'use strict';
// s.cjs: Ultra-compact 1-Compile Pure-JS 8-Byte SWAR-STAY CSV-to-JSON Engine.
// - ONLY 1 TurboFan compile in the ENTIRE process (transduceChunk ONLY — zero writeAscii/writeInt compiles!)
// - Zero scalar tail loops inside transduceChunk (2-loop flat CFG -> ~12-16ms single compile, 0 deopts, 0 GC!)
// - Shift-free LSB, 512 KiB L2-hot sliding window, zero-bailout cross-window unterminated_quote recovery!
// Exports: { primeEngine, transduceText, finishCase }

const ERR_STRAY_CR = 0;
const ERR_QUOTE_JUNK = 1;
const ERR_UNTERMINATED = 2;
const ERR_SHORT_ROW = 3;
const ERR_LONG_ROW = 4;

const B_OPEN_HDR = Buffer.from('{"columns":');               // 11 B
const B_ROWS_HDR_PAD = Buffer.from(',"rows":[     ');        // 14 B (11+14 = 25)
const B_OPEN_NOHDR = Buffer.from('{"columns":null,"rows":['); // 24 B
const B_EMPTY_HDR = Buffer.from('{"columns":[],"rows":[');    // 22 B
const B_ERRORS_START = Buffer.from('],"errors":[');
const B_E_STRAY = Buffer.from('{"code":"stray_cr","line":');
const B_E_JUNK = Buffer.from('{"code":"quote_junk","line":');
const B_E_UNTERM = Buffer.from('{"code":"unterminated_quote","line":');
const B_E_SHORT = Buffer.from('{"code":"short_row","line":');
const B_E_LONG = Buffer.from('{"code":"long_row","line":');
const B_ROW_KEY = Buffer.from(',"row":');
const B_NULL = Buffer.from('null');
const B_FIELDS_KEY = Buffer.from(',"fields":');
const B_EXTRA_KEY = Buffer.from(',"extra":[');

// Reusable zero-GC buffers & typed arrays
let errCap = 4096;
let errCode = new Int32Array(errCap);
let errLine = new Int32Array(errCap);
let errRow = new Int32Array(errCap);
let errFields = new Int32Array(errCap);
let errExtraStart = new Int32Array(errCap);
let errExtraLen = new Int32Array(errCap);
let errCount = 0;

let extraBuf = Buffer.allocUnsafe(64 * 1024);
let extraLen = 0;

let firstRecBuf = Buffer.allocUnsafe(8192);
let firstRecLen = 0;
let prefixBuf = Buffer.allocUnsafe(8192);

let untermBuf = Buffer.allocUnsafe(4096);
let untermLen = 0;

// Per-case scalar state
let sLine = 1;
let sBodyRows = 0;
let sWidth = -1;
let sCaseEmpty = false;
let sHoleFilePos = 0;
let sDoneText = false;
let sBailout = false;
let sSegEnd = 0;

function growErrors() {
  const nc = errCap * 2;
  const nCode = new Int32Array(nc); nCode.set(errCode); errCode = nCode;
  const nLine = new Int32Array(nc); nLine.set(errLine); errLine = nLine;
  const nRow = new Int32Array(nc); nRow.set(errRow); errRow = nRow;
  const nFields = new Int32Array(nc); nFields.set(errFields); errFields = nFields;
  const nES = new Int32Array(nc); nES.set(errExtraStart); errExtraStart = nES;
  const nEL = new Int32Array(nc); nEL.set(errExtraLen); errExtraLen = nEL;
  errCap = nc;
}

function pushErr(code, line, recIdx, fields, eStart, eLen) {
  if (errCount >= errCap) growErrors();
  const idx = errCount++;
  errCode[idx] = code;
  errLine[idx] = line;
  errRow[idx] = recIdx;
  errFields[idx] = fields;
  errExtraStart[idx] = eStart;
  errExtraLen[idx] = eLen;
}

function appendExtra(src, start, len) {
  if (extraLen + len > extraBuf.length) {
    let nc = extraBuf.length * 2;
    while (nc < extraLen + len) nc *= 2;
    const nb = Buffer.allocUnsafe(nc);
    extraBuf.copy(nb, 0, 0, extraLen);
    extraBuf = nb;
  }
  const s = extraLen;
  src.copy(extraBuf, s, start, start + len);
  extraLen = s + len;
  return s;
}

function appendUnterm(src, start, end) {
  const len = end - start;
  if (len <= 0) return;
  if (untermLen + len > untermBuf.length) {
    let nc = untermBuf.length * 2;
    while (nc < untermLen + len) nc *= 2;
    const nb = Buffer.allocUnsafe(nc);
    untermBuf.copy(nb, 0, 0, untermLen);
    untermBuf = nb;
  }
  src.copy(untermBuf, untermLen, start, end);
  untermLen += len;
}

function growFirstRec(need) {
  let nc = firstRecBuf.length * 2;
  while (nc < need) nc *= 2;
  const nb = Buffer.allocUnsafe(nc);
  firstRecBuf.copy(nb, 0, 0, firstRecLen);
  firstRecBuf = nb;
}

// Single cold window/headroom sync helper.
// Guarantees while !st.eof: sSegEnd <= st.inEnd - 16 and if p >= st.inEnd - 24 triggers refill!
function syncWindow(st, p, o, capStart) {
  let inEnd = st.inEnd;
  let safeEnd = st.eof ? inEnd : inEnd - 16;
  if (p >= safeEnd - 7) {
    if (!st.eof) {
      if (capStart >= 0) appendUnterm(st.inBuf, capStart, p);
      st.p = p;
      st.refill();
      p = st.p;
      inEnd = st.inEnd;
      safeEnd = st.eof ? inEnd : inEnd - 16;
    } else if (p >= inEnd) {
      sBailout = true;
      return false;
    }
  }
  if (st.outBuf.length - o < 16384) {
    st.o = o;
    st.ensureOut(65536);
  }
  st.p = p;
  st.o = o;
  let seg = p + ((st.outBuf.length - o - 128) >>> 2);
  if (seg > safeEnd) seg = safeEnd;
  sSegEnd = seg;
  return true;
}

// Cold helper for the 0..3 bytes at p >= end4 inside unquoted loop (only runs ~22x in 11 MB or at EOF!)
// Returns: 0 = synced/refilled (continue SWAR loop!), 1 = stopped at '\' or '"', -1 = bailout.
// Updates st.p, st.o, sSegEnd, and returns updated fi / cutO / fieldStartP via scalars!
let sFi = 0;
let sCutO = 0;
let sFieldStartP = 0;

function handleUnqTail(st, p, o, fi, width, cutO, fieldStartP) {
  const inBuf = st.inBuf;
  if (!st.eof || sSegEnd - p > 3) {
    const wasStart = fieldStartP === p;
    if (!syncWindow(st, p, o, -1)) return -1;
    p = st.p; o = st.o;
    if (wasStart) fieldStartP = p; else if (p === 0) fieldStartP = -1;
    if (sSegEnd - p > 3) {
      sFi = fi; sCutO = cutO; sFieldStartP = fieldStartP;
      return 0;
    }
  }
  // st.eof === true and <= 3 bytes remain before inEnd!
  const out = st.outBuf;
  const dvOut = st.dvOut;
  const end = st.inEnd;
  while (p < end) {
    const b = inBuf[p];
    if (b === 0x2C) {
      p += 1; fi += 1;
      if (fi === width) cutO = o + 1;
      dvOut.setUint32(o, 0x00222c22, true);
      o += 3;
      fieldStartP = p;
      continue;
    }
    if (b === 0x5C || b === 0x22) {
      st.p = p; st.o = o; sFi = fi; sCutO = cutO; sFieldStartP = fieldStartP;
      return 1;
    }
    out[o++] = b;
    p += 1;
  }
  sBailout = true;
  return -1;
}

// Cold helper for p >= end4 inside quoted loop (only runs at window boundary or EOF!)
// Returns: 0 = synced/refilled (continue SWAR loop!), 1 = stopped at '\' or '"', -1 = bailout.
let sCapStart = 0;
function handleQuoTail(st, p, o, capStart) {
  const inBuf = st.inBuf;
  if (!st.eof || sSegEnd - p > 3) {
    if (!syncWindow(st, p, o, capStart)) return -1;
    if (st.p === 0) capStart = 0;
    p = st.p; o = st.o;
    if (sSegEnd - p > 3) {
      sCapStart = capStart;
      return 0;
    }
  }
  const out = st.outBuf;
  const end = st.inEnd;
  while (p < end) {
    const b = inBuf[p];
    if (b === 0x5C || b === 0x22) {
      st.p = p; st.o = o; sCapStart = capStart;
      return 1;
    }
    out[o++] = b;
    p += 1;
  }
  sBailout = true;
  return -1;
}

// Cold unquoted scanner over sliding window `st` writing to `st.outBuf`.
// Returns: 1 = ',', 0 = LF/CRLF, 2 = closing '"', -1 = bailout.
function scanUnquotedCold(st, line, o, recordLine, recIdx, mode) {
  const inBuf = st.inBuf;
  const dvIn = st.dvIn;
  let p = st.p;
  let hasJunk = false;

  while (true) {
    if (!syncWindow(st, p, o, -1)) return -1;
    p = st.p;
    const out = st.outBuf;
    const segEnd = sSegEnd;
    const inEnd = st.inEnd;

    const p0 = p;
    while (p < segEnd) {
      const b = inBuf[p];
      if (b === 0x2C || b === 0x5C || b === 0x22) break;
      out[o++] = b;
      p += 1;
    }
    if (mode !== 0 && p > p0) hasJunk = true;
    if (p >= segEnd) continue;

    const b = inBuf[p];
    if (b === 0x2C) {
      p += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      st.p = p; sLine = line; st.o = o;
      return 1;
    }
    if (b === 0x22) {
      p += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      st.p = p; sLine = line; st.o = o;
      sDoneText = true;
      return 2;
    }
    if (p + 4 > inEnd && !st.eof) { st.p = p; st.refill(); p = st.p; }
    const ie = st.inEnd;
    if (p + 1 >= ie) { sBailout = true; return -1; }
    const esc = inBuf[p + 1];
    if (esc === 0x75) { sBailout = true; return -1; }
    if (esc === 0x6E) {
      p += 2; line += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      st.p = p; sLine = line; st.o = o;
      return 0;
    }
    if (esc === 0x72) {
      if (p + 3 < ie && dvIn.getUint16(p + 2, true) === 0x6e5c) {
        p += 4; line += 1;
        if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
        st.p = p; sLine = line; st.o = o;
        return 0;
      }
      pushErr(ERR_STRAY_CR, recordLine, recIdx, 0, 0, 0);
      p += 2;
      continue;
    }
    if (esc === 0x2F) { out[o++] = 0x2F; p += 2; if (mode !== 0) hasJunk = true; continue; }
    out[o++] = 0x5C; out[o++] = esc; p += 2;
    if (mode !== 0) hasJunk = true;
  }
}

function handleAbnormalRow(st, p, fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, bodyRows) {
  if (fi === 1 && o === firstFieldStartO + 1 && !firstQuoted) {
    sBodyRows = bodyRows;
    return rowStartO;
  }
  const recIdx = bodyRows + 1;
  if (fi < width) {
    pushErr(ERR_SHORT_ROW, recordLine, recIdx, fi, 0, 0);
    const pad = width - fi;
    const need = pad * 3 + 256;
    if (st.outBuf.length - o < need) {
      st.o = o;
      st.ensureOut(need + 4096);
    }
    const out = st.outBuf;
    const dvOut = st.dvOut;
    for (let k = 0; k < pad; k++) {
      dvOut.setUint32(o, 0x0022222c, true);
      o += 3;
    }
    out[o++] = 0x5D;
    const safeEnd = st.eof ? st.inEnd : st.inEnd - 16;
    let seg = p + ((out.length - o - 128) >>> 2);
    if (seg > safeEnd) seg = safeEnd;
    sSegEnd = seg;
    sBodyRows = bodyRows + 1;
    return o;
  }
  const out = st.outBuf;
  const eLen = o - (cutO + 1);
  const eStart = appendExtra(out, cutO + 1, eLen);
  pushErr(ERR_LONG_ROW, recordLine, recIdx, 0, eStart, eLen);
  out[cutO] = 0x5D;
  sBodyRows = bodyRows + 1;
  return cutO + 1;
}

function handleUntermInChunk(st, p, openP, openLine, openWin, fieldStartO, rowStartO, firstFieldStartO, firstQuoted, fi, width, cutO, recordLine, bodyRows) {
  if (openWin === st.windowId) {
    pushErr(ERR_UNTERMINATED, recordLine, bodyRows + 1, 0, 0, 0);
    st.dvOut.setUint16(fieldStartO, 0x225c, true);
    st.p = openP + 2;
    const rc = scanUnquotedCold(st, openLine, fieldStartO + 2, recordLine, bodyRows + 1, 0);
    if (rc < 0) return -1;
    syncWindow(st, st.p, st.o, -1);
    return rc;
  }
  appendUnterm(st.inBuf, 0, p + 1);
  st.p = p + 1;
  const buf = untermBuf;
  const len = untermLen;
  const subSt = {
    inFd: -1, inBuf: buf,
    in32: new Int32Array(buf.buffer, buf.byteOffset, buf.byteLength >>> 2),
    dvIn: new DataView(buf.buffer, buf.byteOffset, buf.byteLength),
    p: 0, inEnd: len, eof: true, windowId: 0, refill() { this.eof = true; },
    outFd: st.outFd, outBuf: st.outBuf, dvOut: st.dvOut, o: fieldStartO,
    outFilePos: st.outFilePos, flushThresh: st.flushThresh,
    ensureOut(need) { st.o = this.o; st.ensureOut(need); this.outBuf = st.outBuf; this.dvOut = st.dvOut; },
    flushOut() { st.o = this.o; st.flushOut(); this.o = st.o; this.outFilePos = st.outFilePos; },
    patchAt(fp, sb, l) { st.patchAt(fp, sb, l); },
  };
  if (subSt.outBuf.length - fieldStartO < 64) subSt.ensureOut(4096);
  pushErr(ERR_UNTERMINATED, recordLine, bodyRows + 1, 0, 0, 0);
  subSt.dvOut.setUint16(fieldStartO, 0x225c, true);
  let rc = scanUnquotedCold(subSt, openLine, fieldStartO + 2, recordLine, bodyRows + 1, 0);
  if (rc < 0) return -1;
  let o = subSt.o; let line = sLine;
  fi += 1;
  while (rc === 1) {
    if (fi === width) cutO = o + 1;
    if (subSt.outBuf.length - o < 64) { subSt.o = o; subSt.ensureOut(4096); }
    subSt.dvOut.setUint32(o, 0x00222c22, true);
    o += 3;
    const isQ = subSt.p + 1 < len && subSt.dvIn.getUint16(subSt.p, true) === 0x225c;
    rc = isQ
      ? scanQuotedColdRec(subSt, subSt.p, line, o, recordLine, bodyRows + 1)
      : scanUnquotedCold(subSt, line, o, recordLine, bodyRows + 1, 0);
    if (rc < 0) return -1;
    o = subSt.o; line = sLine;
    fi += 1;
  }
  if (subSt.outBuf.length - o < 64) { subSt.o = o; subSt.ensureOut(4096); }
  subSt.outBuf[o++] = 0x22;
  if (fi === width && (width > 1 || o > firstFieldStartO + 1 || firstQuoted)) {
    subSt.outBuf[o++] = 0x5D;
    bodyRows += 1;
  } else {
    o = handleAbnormalRow(subSt, subSt.p, fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, bodyRows);
    bodyRows = sBodyRows;
  }
  subSt.o = o;
  if (o >= subSt.flushThresh) subSt.flushOut();
  sLine = line; sBodyRows = bodyRows;
  if (rc !== 2) {
    sDoneText = false;
    while (true) {
      const r2 = transduceChunk(subSt, 512);
      if (r2 === 0) return -1;
      if (r2 === 2) break;
    }
  }
  st.o = subSt.o; st.outBuf = subSt.outBuf; st.dvOut = subSt.dvOut; st.outFilePos = subSt.outFilePos;
  sDoneText = true;
  return 3;
}

function scanQuotedColdRec(st, openP, openLine, fieldStartO, recordLine, recIdx) {
  const inBuf = st.inBuf;
  const dvIn = st.dvIn;
  const openWin = st.windowId;
  let p = openP + 2;
  let line = openLine;
  let o = fieldStartO;
  let closed = false;

  while (true) {
    if (!syncWindow(st, p, o, -1)) return -1;
    p = st.p;
    const out = st.outBuf;
    const dvOut = st.dvOut;
    const segEnd = sSegEnd;

    while (p < segEnd) {
      const b = inBuf[p];
      if (b === 0x5C || b === 0x22) break;
      out[o++] = b;
      p += 1;
    }
    if (p >= segEnd) continue;
    if (inBuf[p] === 0x22) break;

    if (p + 4 > st.inEnd && !st.eof) { st.p = p; st.refill(); p = st.p; }
    const inEnd = st.inEnd;
    if (p + 1 >= inEnd) { sBailout = true; return -1; }
    const esc = inBuf[p + 1];
    if (esc === 0x22) {
      if (p + 3 < inEnd && dvIn.getUint16(p + 2, true) === 0x225c) {
        dvOut.setUint16(o, 0x225c, true); o += 2; p += 4; continue;
      }
      p += 2; closed = true; break;
    }
    if (esc === 0x75) { sBailout = true; return -1; }
    if (esc === 0x72) {
      dvOut.setUint16(o, 0x6e5c, true); o += 2; line += 1;
      p += (p + 3 < inEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) ? 4 : 2;
      continue;
    }
    if (esc === 0x6E) { dvOut.setUint16(o, 0x6e5c, true); o += 2; line += 1; p += 2; continue; }
    if (esc === 0x2F) { out[o++] = 0x2F; p += 2; continue; }
    out[o++] = 0x5C; out[o++] = esc; p += 2;
  }

  if (!closed) {
    if (openWin !== st.windowId) { sBailout = true; return -1; }
    pushErr(ERR_UNTERMINATED, recordLine, recIdx, 0, 0, 0);
    st.dvOut.setUint16(fieldStartO, 0x225c, true);
    st.p = openP + 2;
    return scanUnquotedCold(st, openLine, fieldStartO + 2, recordLine, recIdx, 0);
  }
  if (p + 4 > st.inEnd && !st.eof) { st.p = p; st.refill(); p = st.p; }
  const inEnd = st.inEnd;
  if (p >= inEnd) { sBailout = true; return -1; }
  const next = inBuf[p];
  if (next === 0x2C) { st.p = p + 1; sLine = line; st.o = o; return 1; }
  if (next === 0x22) { st.p = p + 1; sLine = line; st.o = o; sDoneText = true; return 2; }
  if (next === 0x5C && p + 1 < inEnd) {
    const esc = inBuf[p + 1];
    if (esc === 0x6E) { st.p = p + 2; sLine = line + 1; st.o = o; return 0; }
    if (esc === 0x72 && p + 3 < inEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) {
      st.p = p + 4; sLine = line + 1; st.o = o; return 0;
    }
  }
  st.p = p;
  return scanUnquotedCold(st, line, o, recordLine, recIdx, 1);
}

function parseFirstRecord(st) {
  const inBuf = st.inBuf;
  const dvIn = st.dvIn;
  const savedO = st.o;
  let line = 1;

  while (true) {
    if (st.inEnd - st.p < 16 && !st.eof) st.refill();
    let p = st.p;
    let inEnd = st.inEnd;
    if (p >= inEnd) { sBailout = true; return false; }

    const b0 = inBuf[p];
    if (b0 === 0x22) {
      st.p = p + 1; sLine = line; sDoneText = true; st.o = savedO;
      return false;
    }
    if (b0 === 0x5C && p + 1 < inEnd) {
      const esc = inBuf[p + 1];
      if (esc === 0x6E) { st.p = p + 2; line += 1; continue; }
      if (esc === 0x72 && p + 3 < inEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) {
        st.p = p + 4; line += 1; continue;
      }
    }

    const recordLine = line;
    let o = savedO;
    if (st.outBuf.length - o < 4096) { st.o = o; st.ensureOut(65536); }
    st.outBuf[o++] = 0x5B;
    let fi = 0; let firstQuoted = false; let firstEmpty = false;

    while (true) {
      if (st.outBuf.length - o < 64) { st.o = o; st.ensureOut(65536); }
      if (fi > 0) st.outBuf[o++] = 0x2C;
      st.outBuf[o++] = 0x22;
      const fieldStartO = o;
      if (st.inEnd - st.p < 16 && !st.eof) st.refill();
      p = st.p; inEnd = st.inEnd;
      const isQuoted = p + 1 < inEnd && dvIn.getUint16(p, true) === 0x225c;
      if (fi === 0) firstQuoted = isQuoted;
      const rc = isQuoted
        ? scanQuotedColdRec(st, p, line, fieldStartO, recordLine, 0)
        : scanUnquotedCold(st, line, fieldStartO, recordLine, 0, 0);
      if (rc < 0) { st.o = savedO; return false; }
      line = sLine; o = st.o;
      if (fi === 0) firstEmpty = o === fieldStartO;
      st.outBuf[o++] = 0x22;
      fi += 1;
      if (rc !== 1) break;
    }

    if (fi === 1 && firstEmpty && !firstQuoted) {
      if (sDoneText) { st.o = savedO; return false; }
      continue;
    }
    st.outBuf[o++] = 0x5D;
    const recLen = o - savedO;
    if (recLen > firstRecBuf.length) growFirstRec(recLen);
    st.outBuf.copy(firstRecBuf, 0, savedO, o);
    firstRecLen = recLen; sWidth = fi; sLine = line; st.o = savedO;
    return true;
  }
}

// ULTRA-COMPACT SINGLE-COMPILE 2-LOOP SWAR KERNEL:
// Zero scalar fallback loops inside! Tiny CFG -> ultra-fast TurboFan compile (~12-16ms), 0 deopts, 0 GC!
function transduceChunk(st, limit) {
  if (!syncWindow(st, st.p, st.o, -1)) return 0;
  const inBuf = st.inBuf;
  const dvIn = st.dvIn;
  let p = st.p;
  let o = st.o;
  let out = st.outBuf;
  let dvOut = st.dvOut;
  let end4 = sSegEnd - 3;
  let line = sLine;
  let bodyRows = sBodyRows;
  const width = sWidth;
  const flushThresh = st.flushThresh;
  let count = 0;

  if (inBuf[p] === 0x22) {
    st.p = p + 1; st.o = o; sLine = line; sBodyRows = bodyRows; sDoneText = true;
    return 2;
  }

  let rowStartO = o;
  if (bodyRows > 0) { dvOut.setUint32(o, 0x00225b2c, true); o += 3; }
  else { dvOut.setUint16(o, 0x225b, true); o += 2; }

  let fi = 0;
  let cutO = 0;
  let firstQuoted = false;
  let firstFieldStartO = o;
  let fieldStartP = p;
  let recordLine = line;

  while (true) {
    // === UNQUOTED 4-BYTE SWAR-STAY + SHIFT-FREE LSB ===
    while (p < end4) {
      let w = dvIn.getInt32(p, true);
      dvOut.setInt32(o, w, true);
      let x1 = w ^ 0x2c2c2c2c;
      let x2 = w ^ 0x5c5c5c5c;
      let x3 = w ^ 0x22222222;
      let h1 = (x1 - 0x01010101) & ~x1;
      let h2 = (x2 - 0x01010101) & ~x2;
      let h3 = (x3 - 0x01010101) & ~x3;
      let hit = (h1 | h2 | h3) & -2139062144;
      if (hit === 0) {
        p += 4; o += 4;
        if (p >= end4) break;
        w = dvIn.getInt32(p, true);
        dvOut.setInt32(o, w, true);
        x1 = w ^ 0x2c2c2c2c;
        x2 = w ^ 0x5c5c5c5c;
        x3 = w ^ 0x22222222;
        h1 = (x1 - 0x01010101) & ~x1;
        h2 = (x2 - 0x01010101) & ~x2;
        h3 = (x3 - 0x01010101) & ~x3;
        hit = (h1 | h2 | h3) & -2139062144;
        if (hit === 0) { p += 4; o += 4; continue; }
      }

      const lsb = hit & -hit;
      const k = (31 - Math.clz32(lsb)) >>> 3;
      p += k; o += k;

      if ((lsb & h1) !== 0) {
        p += 1; fi += 1;
        if (fi === width) cutO = o + 1;
        dvOut.setUint32(o, 0x00222c22, true);
        o += 3;
        fieldStartP = p;
        continue;
      }
      break;
    }

    if (p >= end4) {
      const tr = handleUnqTail(st, p, o, fi, width, cutO, fieldStartP);
      if (tr < 0) return 0;
      p = st.p; o = st.o; out = st.outBuf; dvOut = st.dvOut;
      end4 = sSegEnd - 3; fi = sFi; cutO = sCutO; fieldStartP = sFieldStartP;
      if (tr === 0) continue;
    }

    let hitEof = false;
    if (inBuf[p] === 0x22) {
      p += 1;
      sDoneText = true;
      if (fi === 0 && o === firstFieldStartO && !firstQuoted) {
        st.p = p; st.o = rowStartO; sLine = line; sBodyRows = bodyRows;
        return 2;
      }
      hitEof = true;
    } else {
      const esc = inBuf[p + 1];
      if (esc === 0x6E) {
        p += 2; line += 1;
      } else if (esc === 0x72 && p + 3 < st.inEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) {
        p += 4; line += 1;
      } else if (esc === 0x22 && p === fieldStartP) {
        // === INLINE 4-BYTE SWAR QUOTED FIELD ===
        if (fi === 0) firstQuoted = true;
        const openP = p;
        const openLine = line;
        const openWin = st.windowId;
        const fieldStartO = o;
        p += 2;
        let closed = false;
        let capStart = openP + 2;
        untermLen = 0;

        while (true) {
          while (p < end4) {
            const w0 = dvIn.getInt32(p, true);
            dvOut.setInt32(o, w0, true);
            const x0a = w0 ^ 0x5c5c5c5c;
            const x0b = w0 ^ 0x22222222;
            const h0 = (((x0a - 0x01010101) & ~x0a) | ((x0b - 0x01010101) & ~x0b)) & -2139062144;
            if (h0 !== 0) {
              const k = (31 - Math.clz32(h0 & -h0)) >>> 3;
              p += k; o += k; break;
            }
            p += 4; o += 4;
            if (p >= end4) break;
            const w1 = dvIn.getInt32(p, true);
            dvOut.setInt32(o, w1, true);
            const x1a = w1 ^ 0x5c5c5c5c;
            const x1b = w1 ^ 0x22222222;
            const h1 = (((x1a - 0x01010101) & ~x1a) | ((x1b - 0x01010101) & ~x1b)) & -2139062144;
            if (h1 !== 0) {
              const k = (31 - Math.clz32(h1 & -h1)) >>> 3;
              p += k; o += k; break;
            }
            p += 4; o += 4;
          }
          if (p >= end4) {
            const qr = handleQuoTail(st, p, o, capStart);
            if (qr < 0) return 0;
            p = st.p; o = st.o; out = st.outBuf; dvOut = st.dvOut;
            end4 = sSegEnd - 3; capStart = sCapStart;
            if (qr === 0) continue;
          }
          if (inBuf[p] === 0x22) break;
          const qEsc = inBuf[p + 1];
          if (qEsc === 0x22) {
            if (p + 3 < st.inEnd && dvIn.getUint16(p + 2, true) === 0x225c) {
              dvOut.setUint16(o, 0x225c, true); o += 2; p += 4; continue;
            }
            p += 2; closed = true; break;
          }
          if (qEsc === 0x72) {
            dvOut.setUint16(o, 0x6e5c, true); o += 2; line += 1;
            p += (p + 3 < st.inEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) ? 4 : 2;
            continue;
          }
          if (qEsc === 0x6E) { dvOut.setUint16(o, 0x6e5c, true); o += 2; line += 1; p += 2; continue; }
          if (qEsc === 0x75) { sBailout = true; return 0; }
          if (qEsc === 0x2F) { out[o++] = 0x2F; p += 2; continue; }
          out[o++] = 0x5C; out[o++] = qEsc; p += 2;
        }

        let qrc = 0;
        if (!closed) {
          qrc = handleUntermInChunk(st, p, openP, openLine, openWin, fieldStartO, rowStartO, firstFieldStartO, firstQuoted, fi, width, cutO, recordLine, bodyRows);
          if (qrc < 0) return 0;
          if (qrc === 3) return 2;
          p = st.p; line = sLine; o = st.o; out = st.outBuf; dvOut = st.dvOut; end4 = sSegEnd - 3;
        } else {
          const nb = inBuf[p];
          if (nb === 0x2C) { p += 1; qrc = 1; }
          else if (nb === 0x22) { p += 1; sDoneText = true; qrc = 2; }
          else if (nb === 0x5C && inBuf[p + 1] === 0x6E) { p += 2; line += 1; }
          else if (nb === 0x5C && inBuf[p + 1] === 0x72 && p + 3 < st.inEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) { p += 4; line += 1; }
          else {
            st.p = p;
            qrc = scanUnquotedCold(st, line, o, recordLine, bodyRows + 1, 1);
            if (qrc < 0) return 0;
            p = st.p; line = sLine; o = st.o;
            syncWindow(st, p, o, -1);
            p = st.p; out = st.outBuf; dvOut = st.dvOut; end4 = sSegEnd - 3;
          }
        }

        if (qrc === 1) {
          fi += 1;
          if (fi === width) cutO = o + 1;
          dvOut.setUint32(o, 0x00222c22, true);
          o += 3;
          fieldStartP = p;
          continue;
        }
        if (qrc === 2) hitEof = true;
      } else {
        st.p = p;
        const ec = scanUnquotedCold(st, line, o, recordLine, bodyRows + 1, 0);
        if (ec < 0) return 0;
        p = st.p; line = sLine; o = st.o;
        syncWindow(st, p, o, -1);
        p = st.p; out = st.outBuf; dvOut = st.dvOut; end4 = sSegEnd - 3;
        if (ec === 1) {
          fi += 1;
          if (fi === width) cutO = o + 1;
          dvOut.setUint32(o, 0x00222c22, true);
          o += 3;
          fieldStartP = p;
          continue;
        }
        if (ec === 2) hitEof = true;
      }
    }

    // === ROW END ===
    fi += 1;
    if (fi === width && (width > 1 || o > firstFieldStartO || firstQuoted)) {
      bodyRows += 1;
      count += 1;
      if (hitEof || o >= flushThresh || count >= limit || p >= end4) {
        dvOut.setUint16(o, 0x5d22, true);
        o += 2;
        if (o >= flushThresh) { st.o = o; st.flushOut(); o = st.o; }
        st.p = p; st.o = o; sLine = line; sBodyRows = bodyRows;
        return hitEof ? 2 : 1;
      }
      rowStartO = o + 2;
      dvOut.setUint32(o, 0x5b2c5d22, true);
      out[o + 4] = 0x22;
      o += 5;
      fi = 0; cutO = 0; firstQuoted = false;
      firstFieldStartO = o; fieldStartP = p; recordLine = line;
      continue;
    }

    out[o++] = 0x22;
    o = handleAbnormalRow(st, p, fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, bodyRows);
    bodyRows = sBodyRows;
    out = st.outBuf; dvOut = st.dvOut; end4 = sSegEnd - 3;
    count += 1;
    if (hitEof || o >= flushThresh || count >= limit || p >= end4) {
      if (o >= flushThresh) { st.o = o; st.flushOut(); o = st.o; }
      st.p = p; st.o = o; sLine = line; sBodyRows = bodyRows;
      return hitEof ? 2 : 1;
    }
    rowStartO = o;
    if (bodyRows > 0) { dvOut.setUint32(o, 0x00225b2c, true); o += 3; }
    else { dvOut.setUint16(o, 0x225b, true); o += 2; }
    fi = 0; cutO = 0; firstQuoted = false;
    firstFieldStartO = o; fieldStartP = p; recordLine = line;
  }
}

function transduceText(st) {
  errCount = 0;
  extraLen = 0;
  firstRecLen = 0;
  untermLen = 0;
  sLine = 1;
  sBodyRows = 0;
  sWidth = -1;
  sCaseEmpty = false;
  sDoneText = false;
  sBailout = false;

  if (st.inEnd - st.p < 16 && !st.eof) st.refill();
  const inBuf = st.inBuf;
  if (st.p + 2 < st.inEnd && inBuf[st.p] === 0xEF && inBuf[st.p + 1] === 0xBB && inBuf[st.p + 2] === 0xBF) {
    st.p += 3;
  }

  const found = parseFirstRecord(st);
  if (sBailout) return 0;
  if (!found) {
    sCaseEmpty = true;
    return 1;
  }

  if (st.o >= st.flushThresh) st.flushOut();
  const holeLen = firstRecLen + 25;
  if (st.outBuf.length - st.o < holeLen + 4096) {
    st.ensureOut(holeLen + 65536);
  }
  sHoleFilePos = st.outFilePos + st.o;
  st.o += holeLen;

  if (!sDoneText) {
    while (true) {
      const rc = transduceChunk(st, 512);
      if (rc === 0) return 0;
      if (rc === 2) break;
    }
  }
  return 1;
}

// Inline buffer copy + digit emit inside finishCase -> ZERO TurboFan compiles for writeAscii/writeInt!
function finishCase(st, header) {
  const worstErrBytes = 64 + errCount * 96 + extraLen + 32;
  if (st.outBuf.length - st.o < worstErrBytes) {
    st.ensureOut(worstErrBytes + 4096);
  }
  const out = st.outBuf;
  let o = st.o;

  if (sCaseEmpty) {
    const src = header ? B_EMPTY_HDR : B_OPEN_NOHDR;
    out.set(src, o); o += src.length;
  } else {
    const holeLen = firstRecLen + 25;
    if (holeLen > prefixBuf.length) {
      let nc = prefixBuf.length * 2;
      while (nc < holeLen) nc *= 2;
      prefixBuf = Buffer.allocUnsafe(nc);
    }
    let po = 0;
    if (header) {
      prefixBuf.set(B_OPEN_HDR, po); po += B_OPEN_HDR.length;
      prefixBuf.set(firstRecBuf.subarray(0, firstRecLen), po); po += firstRecLen;
      prefixBuf.set(B_ROWS_HDR_PAD, po); po += B_ROWS_HDR_PAD.length;
    } else {
      prefixBuf.set(B_OPEN_NOHDR, po); po += B_OPEN_NOHDR.length;
      prefixBuf.set(firstRecBuf.subarray(0, firstRecLen), po); po += firstRecLen;
      prefixBuf[po++] = sBodyRows > 0 ? 0x2C : 0x20;
    }
    st.o = o;
    st.patchAt(sHoleFilePos, prefixBuf, po);
  }

  out.set(B_ERRORS_START, o); o += B_ERRORS_START.length;
  for (let i = 0; i < errCount; i++) {
    const code = errCode[i];
    if (i > 0) out[o++] = 0x2C;
    const tag = code === ERR_STRAY_CR ? B_E_STRAY
      : code === ERR_QUOTE_JUNK ? B_E_JUNK
      : code === ERR_UNTERMINATED ? B_E_UNTERM
      : code === ERR_SHORT_ROW ? B_E_SHORT
      : B_E_LONG;
    out.set(tag, o); o += tag.length;

    let n = errLine[i];
    if (n < 10) { out[o++] = 48 + n; }
    else {
      const s0 = o;
      while (n > 0) { const q = (n / 10) | 0; out[o++] = 48 + (n - q * 10); n = q; }
      for (let l = s0, r = o - 1; l < r; l++, r--) { const t = out[l]; out[l] = out[r]; out[r] = t; }
    }

    out.set(B_ROW_KEY, o); o += B_ROW_KEY.length;
    let r = header ? (errRow[i] - 1) : errRow[i];
    if (r < 0) { out[o++] = 110; out[o++] = 117; out[o++] = 108; out[o++] = 108; }
    else if (r < 10) { out[o++] = 48 + r; }
    else {
      const s0 = o;
      while (r > 0) { const q = (r / 10) | 0; out[o++] = 48 + (r - q * 10); r = q; }
      for (let l = s0, rt = o - 1; l < rt; l++, rt--) { const t = out[l]; out[l] = out[rt]; out[rt] = t; }
    }

    if (code === ERR_SHORT_ROW) {
      out.set(B_FIELDS_KEY, o); o += B_FIELDS_KEY.length;
      let f = errFields[i];
      if (f < 10) { out[o++] = 48 + f; }
      else {
        const s0 = o;
        while (f > 0) { const q = (f / 10) | 0; out[o++] = 48 + (f - q * 10); f = q; }
        for (let l = s0, rt = o - 1; l < rt; l++, rt--) { const t = out[l]; out[l] = out[rt]; out[rt] = t; }
      }
    } else if (code === ERR_LONG_ROW) {
      out.set(B_EXTRA_KEY, o); o += B_EXTRA_KEY.length;
      const es = errExtraStart[i];
      const eLen = errExtraLen[i];
      out.set(extraBuf.subarray(es, es + eLen), o); o += eLen;
      out[o++] = 0x5D;
    }
    out[o++] = 0x7D;
  }
  out[o++] = 0x5D;
  out[o++] = 0x7D;
  st.o = o;
  if (o >= st.flushThresh) st.flushOut();
}

function primeEngine(st) {
  const savedInFd = st.inFd;
  const savedOutFd = st.outFd;
  const savedFlushThresh = st.flushThresh;
  const savedEof = st.eof;

  // Break ALL V8 kFieldConst dependencies on st properties BEFORE compiling transduceChunk!
  st.inFd = 0; st.inFd = -1;
  st.outFd = 0; st.outFd = -1;
  st.eof = false; st.eof = true;
  st.flushThresh = 1; st.flushThresh = 0x7fffffff;
  st.windowId = 1; st.windowId = 0;
  st.outFilePos = 1; st.outFilePos = 0;
  st.refill();
  st.flushOut();

  const wSamples = [
    JSON.stringify('\uFEFFalpha,bravo\r\n\r\n,12345678\r\n"","x12345678""y12345678""z1234"\r\n"ok12345678"j,"m12345678\r\n""n56789012"j\r\n"p12345678"j\r1\r\n\r\r\n1\r\n1,2,3,4\r\n1,"q",extra\r\n4\r5,6\r7\r\n\r,9\r\n"unterm').slice(1),
    JSON.stringify('café1234,bravo5678\n\n,12345678\n"","x12345678""y12345678""z1234"\n"ok12345678"j,"m12345678\n\rn56789012\n""k12345678"j\n"q12345678"\rj\n"z12345678"\r,2\n1,\n1\n1,2,3,4\n4\r5,6\r7\n"a12345678\nb45678901"j,1\n"x""y').slice(1),
    JSON.stringify('a\n""\n\r\n\r\r\nb\n1,2,3\n12345678,x\n').slice(1),
    JSON.stringify('a,b\n12345678901234567890,12345678901234567890\n').slice(1),
    JSON.stringify('a,b\n12345678,"hello12345678901234567890",x\n').slice(1),
    JSON.stringify('a,b\n12345678,"hello12345678901234567890"').slice(1),
    'a\\/b,c\\\\d\\t\\b\\f\\n1,2\\u0041"',
    '"',
  ];

  for (let i = 0; i < 2; i++) {
    st.flushThresh = i === 0 ? 1 : 0x7fffffff;
    for (let j = 0; j < wSamples.length; j++) {
      const n = st.inBuf.write(wSamples[j], 0, 'utf8');
      st.p = 0; st.inEnd = n; st.eof = i === 1; st.o = 0; st.outFilePos = 0;
      transduceText(st);
    }
  }

  // Exercise handleUnqTail (tr=0 & tr=1) and handleQuoTail (qr=0 & qr=1) inside transduceChunk!
  st.flushThresh = 0x7fffffff;
  for (const [s, w] of [
    ['12345678901234567890,12345678901234567890\\n"', 2],
    ['12345678,\\"hello12345678901234567890\\",123456\\n"', 3],
    ['\\"a\\",123456789012\\n"', 2],
    ['\\"ab\\""', 1],
    ['12345678,abcdefgh",12345678901234567890', 2],
    ['12345678,abcdefgh\\n",12345678901234567890', 2],
  ]) {
    const n = st.inBuf.write(s, 0, 'utf8');
    errCount = 0; extraLen = 0; sLine = 1; sBodyRows = 1; sWidth = w; sDoneText = false; sBailout = false;
    st.p = 0; st.inEnd = n; st.eof = false; st.o = 0; st.outFilePos = 0;
    transduceChunk(st, 8);
  }

  // Minimal micro-prime for transduceChunk into TurboFan!
  const pStr =
    '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
    '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
    '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
    '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n"';
  const pLen = st.inBuf.write(pStr, 0, 'utf8');
  for (let k = 0; k < 180; k++) {
    errCount = 0; extraLen = 0; sLine = 1; sBodyRows = 1; sWidth = 3; sDoneText = false; sBailout = false;
    st.p = 0; st.inEnd = pLen; st.eof = true; st.o = 0; st.outFilePos = 0;
    transduceChunk(st, 4);
  }

  errCount = 0; extraLen = 0; firstRecLen = 0; untermLen = 0;
  sLine = 1; sBodyRows = 0; sWidth = -1; sCaseEmpty = false; sDoneText = false; sBailout = false;
  st.inFd = savedInFd;
  st.outFd = savedOutFd;
  st.flushThresh = savedFlushThresh;
  st.eof = savedEof;
  st.p = 0; st.inEnd = 0; st.o = 0; st.outFilePos = 0;
}

module.exports = { primeEngine, transduceText, finishCase };
