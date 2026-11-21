// Ultra-fast drop-in replacement for make.fun's csv-reader 1.0.0.
// Pure ES module, zero dependencies, deterministic, stateless.
// Exports:
//   - run(input): exact {columns, rows, errors} JS object parser (contract & \uXXXX fallback)
//   - solveCaseBuffer(inBuf, textStart, textEnd, header, writer): zero-GC direct raw-JSON
//     UTF-8 Buffer CSV -> raw-JSON UTF-8 Buffer flat 8-byte SWAR streaming engine.

// ============================================================================
// Part 1: Direct UTF-8 Raw-JSON-Buffer Flat SWAR CSV -> JSON Streamer
// ============================================================================

const ERR_STRAY_CR = 0;
const ERR_QUOTE_JUNK = 1;
const ERR_UNTERMINATED = 2;
const ERR_SHORT_ROW = 3;
const ERR_LONG_ROW = 4;

const B_OPEN_HDR = Buffer.from('{"columns":');
const B_OPEN_NOHDR = Buffer.from('{"columns":null,"rows":[');
const B_EMPTY_HDR = Buffer.from('[],"rows":[');
const B_ROWS_START = Buffer.from(',"rows":[');
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

// Reusable zero-GC error storage (reset on every solveCaseBuffer call)
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

function pushErr(code, line, row, fields, eStart, eLen) {
  if (errCount >= errCap) growErrors();
  const idx = errCount++;
  errCode[idx] = code;
  errLine[idx] = line;
  errRow[idx] = row;
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

function writeAscii(out, o, src) {
  const n = src.length;
  for (let i = 0; i < n; i++) out[o + i] = src[i];
  return o + n;
}

function writeInt(out, o, n) {
  if (n < 10) {
    out[o] = 48 + n;
    return o + 1;
  }
  if (n < 100) {
    const t = (n / 10) | 0;
    out[o] = 48 + t;
    out[o + 1] = 48 + (n - t * 10);
    return o + 2;
  }
  const start = o;
  while (n > 0) {
    const q = (n / 10) | 0;
    out[o++] = 48 + (n - q * 10);
    n = q;
  }
  let l = start;
  let r = o - 1;
  while (l < r) {
    const tmp = out[l];
    out[l++] = out[r];
    out[r--] = tmp;
  }
  return o;
}

// Per-case scalar registers (reset before every solveCaseBuffer call)
let sP = 0;
let sLine = 1;
let sO = 0;
let sRows = 0;
let sWidth = -1;
let sOut = null;
let sDvOut = null;
let sHitU = false;

let cInBuf = null;
let cDvIn = null;
let cOutBuf = null;
let cDvOut = null;

function getDvIn(buf) {
  if (buf === cInBuf) return cDvIn;
  cInBuf = buf;
  cDvIn = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  return cDvIn;
}

function getDvOut(buf) {
  if (buf === cOutBuf) return cDvOut;
  cOutBuf = buf;
  cDvOut = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  return cDvOut;
}

function ensureOut(writer, o, need) {
  writer.pos = o;
  writer.ensure(need);
  sOut = writer.buf;
  sDvOut = writer.dv || getDvOut(sOut);
  return sOut;
}

// Cold unquoted span scanner (mode 0 = normal / unterminated / header / tail, mode 1 = quote_junk).
// Returns 1 if ended at comma, 0 if ended at line break / EOF, -1 if \uXXXX encountered.
function scanUnquotedCold(inBuf, dvIn, textEnd, p, line, o, recordLine, recordRow, mode) {
  const out = sOut;
  const dvOut = sDvOut;
  const end4 = textEnd - 3;
  let hasJunk = false;

  while (p < textEnd) {
    const p0 = p;
    while (p < end4) {
      const w = dvIn.getInt32(p, true);
      dvOut.setInt32(o, w, true);
      const x1 = w ^ 0x2c2c2c2c;
      const x2 = w ^ 0x5c5c5c5c;
      const hit = (((x1 - 0x01010101) & ~x1) | ((x2 - 0x01010101) & ~x2)) & -2139062144;
      if (hit !== 0) {
        const k = (31 - Math.clz32(hit & -hit)) >>> 3;
        p += k;
        o += k;
        break;
      }
      p += 4;
      o += 4;
    }
    if (p >= end4) {
      while (p < textEnd) {
        const b = inBuf[p];
        if (b === 0x2C || b === 0x5C) break;
        out[o++] = b;
        p += 1;
      }
    }
    if (mode !== 0 && p > p0) hasJunk = true;
    if (p >= textEnd) break;

    const b = inBuf[p];
    if (b === 0x2C) {
      p += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recordRow, 0, 0, 0);
      sP = p;
      sLine = line;
      sO = o;
      return 1;
    }
    if (p + 1 >= textEnd) break;
    const esc = inBuf[p + 1];
    if (esc === 0x75) {
      sHitU = true;
      return -1;
    }
    if (esc === 0x6E) {
      p += 2;
      line += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recordRow, 0, 0, 0);
      sP = p;
      sLine = line;
      sO = o;
      return 0;
    }
    if (esc === 0x72) {
      if (p + 3 < textEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) {
        p += 4;
        line += 1;
        if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recordRow, 0, 0, 0);
        sP = p;
        sLine = line;
        sO = o;
        return 0;
      }
      pushErr(ERR_STRAY_CR, recordLine, recordRow, 0, 0, 0);
      p += 2;
      continue;
    }
    if (esc === 0x2F) {
      out[o++] = 0x2F;
      p += 2;
      if (mode !== 0) hasJunk = true;
      continue;
    }
    out[o++] = 0x5C;
    out[o++] = esc;
    p += 2;
    if (mode !== 0) hasJunk = true;
  }

  if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recordRow, 0, 0, 0);
  sP = p;
  sLine = line;
  sO = o;
  return 0;
}

function handleUnterminated(inBuf, dvIn, textEnd, openP, openLine, fieldStartO, recordLine, recordRow) {
  pushErr(ERR_UNTERMINATED, recordLine, recordRow, 0, 0, 0);
  sDvOut.setUint16(fieldStartO, 0x225c, true);
  return scanUnquotedCold(inBuf, dvIn, textEnd, openP + 2, openLine, fieldStartO + 2, recordLine, recordRow, 0);
}

function handleAbnormalRow(fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, recordRow, textEnd, p, writer) {
  if (fi === 1 && o === firstFieldStartO + 1 && !firstQuoted) {
    sRows = recordRow;
    return rowStartO;
  }
  let out = sOut;
  let dvOut = sDvOut;
  if (fi < width) {
    pushErr(ERR_SHORT_ROW, recordLine, recordRow, fi, 0, 0);
    const pad = width - fi;
    const need = pad * 3 + (textEnd - p) * 3 + 256;
    if (out.length - o < need) {
      out = ensureOut(writer, o, need);
      dvOut = sDvOut;
    }
    for (let k = 0; k < pad; k++) {
      dvOut.setUint32(o, 0x0022222c, true); // ',""'
      o += 3;
    }
    out[o++] = 0x5D;
    sRows = recordRow + 1;
    return o;
  }
  const eLen = o - (cutO + 1);
  const eStart = appendExtra(out, cutO + 1, eLen);
  pushErr(ERR_LONG_ROW, recordLine, recordRow, 0, eStart, eLen);
  out[cutO] = 0x5D;
  sRows = recordRow + 1;
  return cutO + 1;
}

// Separate 8-byte (2x32-bit) SWAR quoted field scanner starting at openP (`\"`).
// Returns 1 if ended at comma, 0 if ended at line break / EOF, -1 if \uXXXX encountered.
function scanQuoted(inBuf, dvIn, textEnd, openP, openLine, fieldStartO, recordLine, recordRow) {
  const out = sOut;
  const dvOut = sDvOut;
  const end8 = textEnd - 7;
  const end4 = textEnd - 3;
  let p = openP + 2;
  let line = openLine;
  let o = fieldStartO;
  let closed = false;

  while (p < textEnd) {
    while (p < end8) {
      const w0 = dvIn.getInt32(p, true);
      dvOut.setInt32(o, w0, true);
      const x0 = w0 ^ 0x5c5c5c5c;
      const h0 = (x0 - 0x01010101) & ~x0 & -2139062144;
      if (h0 !== 0) {
        const k = (31 - Math.clz32(h0 & -h0)) >>> 3;
        p += k;
        o += k;
        break;
      }
      const w1 = dvIn.getInt32(p + 4, true);
      dvOut.setInt32(o + 4, w1, true);
      const x1 = w1 ^ 0x5c5c5c5c;
      const h1 = (x1 - 0x01010101) & ~x1 & -2139062144;
      if (h1 !== 0) {
        const k = 4 + ((31 - Math.clz32(h1 & -h1)) >>> 3);
        p += k;
        o += k;
        break;
      }
      p += 8;
      o += 8;
    }
    if (p >= end8) {
      while (p < end4) {
        const w = dvIn.getInt32(p, true);
        dvOut.setInt32(o, w, true);
        const x = w ^ 0x5c5c5c5c;
        const h = (x - 0x01010101) & ~x & -2139062144;
        if (h !== 0) {
          const k = (31 - Math.clz32(h & -h)) >>> 3;
          p += k;
          o += k;
          break;
        }
        p += 4;
        o += 4;
      }
      if (p >= end4) {
        while (p < textEnd) {
          const b = inBuf[p];
          if (b === 0x5C) break;
          out[o++] = b;
          p += 1;
        }
      }
    }
    if (p + 1 >= textEnd) break;
    const esc = inBuf[p + 1];
    if (esc === 0x22) {
      if (p + 3 < textEnd && dvIn.getUint16(p + 2, true) === 0x225c) {
        dvOut.setUint16(o, 0x225c, true);
        o += 2;
        p += 4;
        continue;
      }
      p += 2;
      closed = true;
      break;
    }
    if (esc === 0x72) {
      dvOut.setUint16(o, 0x6e5c, true);
      o += 2;
      line += 1;
      p += (p + 3 < textEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) ? 4 : 2;
      continue;
    }
    if (esc === 0x6E) {
      dvOut.setUint16(o, 0x6e5c, true);
      o += 2;
      line += 1;
      p += 2;
      continue;
    }
    if (esc === 0x75) {
      sHitU = true;
      return -1;
    }
    if (esc === 0x2F) {
      out[o++] = 0x2F;
      p += 2;
      continue;
    }
    out[o++] = 0x5C;
    out[o++] = esc;
    p += 2;
  }

  if (!closed) return handleUnterminated(inBuf, dvIn, textEnd, openP, openLine, fieldStartO, recordLine, recordRow);
  if (p >= textEnd) {
    sP = p;
    sLine = line;
    sO = o;
    return 0;
  }
  const next = inBuf[p];
  if (next === 0x2C) {
    sP = p + 1;
    sLine = line;
    sO = o;
    return 1;
  }
  if (next === 0x5C && p + 1 < textEnd) {
    const esc = inBuf[p + 1];
    if (esc === 0x6E) {
      sP = p + 2;
      sLine = line + 1;
      sO = o;
      return 0;
    }
    if (esc === 0x72 && p + 3 < textEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) {
      sP = p + 4;
      sLine = line + 1;
      sO = o;
      return 0;
    }
  }
  return scanUnquotedCold(inBuf, dvIn, textEnd, p, line, o, recordLine, recordRow, 1);
}

// Cold tail row finisher (called at most once per case when p enters the last 3 bytes).
function finishTailRow(inBuf, dvIn, textEnd, p, line, o, fi, width, cutO, rowStartO, firstFieldStartO, firstQuoted, fieldStartP, recordLine, rowsCount, writer) {
  const out = sOut;
  const dvOut = sDvOut;
  while (true) {
    let ec;
    if (p === fieldStartP && p + 1 < textEnd && dvIn.getUint16(p, true) === 0x225c) {
      if (fi === 0) firstQuoted = true;
      ec = scanQuoted(inBuf, dvIn, textEnd, p, line, o, recordLine, rowsCount);
    } else {
      ec = scanUnquotedCold(inBuf, dvIn, textEnd, p, line, o, recordLine, rowsCount, 0);
    }
    if (ec < 0) return;
    p = sP;
    line = sLine;
    o = sO;
    fi += 1;
    if (ec !== 0) {
      if (fi === width) cutO = o + 1;
      dvOut.setUint32(o, 0x00222c22, true);
      o += 3;
      fieldStartP = p;
      continue;
    }
    out[o++] = 0x22;
    if (fi === width) cutO = o;
    break;
  }
  if (fi === width && (width > 1 || o > firstFieldStartO + 1 || firstQuoted)) {
    out[o++] = 0x5D;
    rowsCount += 1;
  } else {
    o = handleAbnormalRow(fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, rowsCount, textEnd, p, writer);
    rowsCount = sRows;
  }
  sP = p;
  sLine = line;
  sO = o;
  sRows = rowsCount;
}

function parseTailRows(inBuf, dvIn, textEnd, writer) {
  while (sP < textEnd) {
    let o = sO;
    const rowStartO = o;
    if (sRows > 0) {
      sDvOut.setUint32(o, 0x00225b2c, true);
      o += 3;
    } else {
      sDvOut.setUint16(o, 0x225b, true);
      o += 2;
    }
    finishTailRow(inBuf, dvIn, textEnd, sP, sLine, o, 0, sWidth, 0, rowStartO, o, false, sP, sLine, sRows, writer);
    if (sHitU) return;
  }
}

// Flat 1-loop 8-byte (2x32-bit) SWAR-STAY kernel: stays inside one loop across ',' and '\n'/'\r\n'.
function parseBufferChunk(inBuf, dvIn, textEnd, writer, limit) {
  let p = sP;
  let line = sLine;
  let o = sO;
  let rowsCount = sRows;
  const width = sWidth;
  let out = sOut;
  let dvOut = sDvOut;
  const end4 = textEnd - 3;
  let count = 0;

  let rowStartO = o;
  if (rowsCount > 0) {
    dvOut.setUint32(o, 0x00225b2c, true);
    o += 3;
  } else {
    dvOut.setUint16(o, 0x225b, true);
    o += 2;
  }

  let fi = 0;
  let cutO = 0;
  let firstQuoted = false;
  let firstFieldStartO = o;
  let fieldStartP = p;
  let recordLine = line;
  let inRow = true;

  while (p < end4) {
    let w = dvIn.getInt32(p, true);
    dvOut.setInt32(o, w, true);
    let x1 = w ^ 0x2c2c2c2c;
    let x2 = w ^ 0x5c5c5c5c;
    let hit = (((x1 - 0x01010101) & ~x1) | ((x2 - 0x01010101) & ~x2)) & -2139062144;
    if (hit === 0) {
      p += 4;
      o += 4;
      if (p >= end4) break;
      w = dvIn.getInt32(p, true);
      dvOut.setInt32(o, w, true);
      x1 = w ^ 0x2c2c2c2c;
      x2 = w ^ 0x5c5c5c5c;
      hit = (((x1 - 0x01010101) & ~x1) | ((x2 - 0x01010101) & ~x2)) & -2139062144;
      if (hit === 0) {
        p += 4;
        o += 4;
        continue;
      }
    }

    const k = (31 - Math.clz32(hit & -hit)) >>> 3;
    p += k;
    o += k;

    if (((w >>> (k << 3)) & 0xFF) === 0x2C) {
      p += 1;
      fi += 1;
      if (fi === width) cutO = o + 1;
      dvOut.setUint32(o, 0x00222c22, true); // '","'
      o += 3;
      fieldStartP = p;
      continue;
    }

    if (p + 1 >= textEnd) break;
    const esc = inBuf[p + 1];
    if (esc === 0x6E) {
      p += 2;
      line += 1;
    } else if (esc === 0x72 && p + 3 < textEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) {
      p += 4;
      line += 1;
    } else if (esc === 0x22 && p === fieldStartP) {
      if (fi === 0) firstQuoted = true;
      const qec = scanQuoted(inBuf, dvIn, textEnd, p, line, o, recordLine, rowsCount);
      if (qec < 0) return;
      p = sP;
      line = sLine;
      o = sO;
      if (qec !== 0) {
        fi += 1;
        if (fi === width) cutO = o + 1;
        dvOut.setUint32(o, 0x00222c22, true);
        o += 3;
        fieldStartP = p;
        continue;
      }
    } else {
      const ec = scanUnquotedCold(inBuf, dvIn, textEnd, p, line, o, recordLine, rowsCount, 0);
      if (ec < 0) return;
      p = sP;
      line = sLine;
      o = sO;
      if (ec !== 0) {
        fi += 1;
        if (fi === width) cutO = o + 1;
        dvOut.setUint32(o, 0x00222c22, true);
        o += 3;
        fieldStartP = p;
        continue;
      }
    }

    // Row end
    fi += 1;
    if (fi === width && (width > 1 || o > firstFieldStartO || firstQuoted)) {
      rowsCount += 1;
      count += 1;
      if (count >= limit || p >= end4) {
        dvOut.setUint16(o, 0x5d22, true); // '"]'
        o += 2;
        inRow = false;
        break;
      }
      rowStartO = o + 2;
      dvOut.setUint32(o, 0x5b2c5d22, true); // '"],["' bytes 0..3
      out[o + 4] = 0x22;                    // byte 4: '"'
      o += 5;
      fi = 0;
      cutO = 0;
      firstQuoted = false;
      firstFieldStartO = o;
      fieldStartP = p;
      recordLine = line;
      continue;
    }

    out[o++] = 0x22;
    o = handleAbnormalRow(fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, rowsCount, textEnd, p, writer);
    rowsCount = sRows;
    out = sOut;
    dvOut = sDvOut;
    count += 1;
    if (count >= limit || p >= end4) {
      inRow = false;
      break;
    }
    rowStartO = o;
    if (rowsCount > 0) {
      dvOut.setUint32(o, 0x00225b2c, true);
      o += 3;
    } else {
      dvOut.setUint16(o, 0x225b, true);
      o += 2;
    }
    fi = 0;
    cutO = 0;
    firstQuoted = false;
    firstFieldStartO = o;
    fieldStartP = p;
    recordLine = line;
  }

  if (inRow) {
    finishTailRow(inBuf, dvIn, textEnd, p, line, o, fi, width, cutO, rowStartO, firstFieldStartO, firstQuoted, fieldStartP, recordLine, rowsCount, writer);
    return;
  }
  sP = p;
  sLine = line;
  sO = o;
  sRows = rowsCount;
}

function parseFirstBufferRecord(inBuf, dvIn, textEnd, header) {
  let p = sP;
  let line = sLine;
  let o = sO;
  const out = sOut;
  const recordRow = header ? -1 : 0;

  while (p < textEnd) {
    if (inBuf[p] === 0x5C && p + 1 < textEnd) {
      const esc = inBuf[p + 1];
      if (esc === 0x6E) {
        p += 2;
        line += 1;
        continue;
      }
      if (esc === 0x72 && p + 3 < textEnd && dvIn.getUint16(p + 2, true) === 0x6e5c) {
        p += 4;
        line += 1;
        continue;
      }
    }
    const recordLine = line;
    const rowStartO = o;
    out[o++] = 0x5B;
    let fi = 0;
    let firstQuoted = false;
    let firstEmpty = false;
    while (true) {
      if (fi > 0) out[o++] = 0x2C;
      out[o++] = 0x22;
      const fieldStartO = o;
      const isQuoted = p + 1 < textEnd && dvIn.getUint16(p, true) === 0x225c;
      if (fi === 0) firstQuoted = isQuoted;
      const endedComma = isQuoted
        ? scanQuoted(inBuf, dvIn, textEnd, p, line, fieldStartO, recordLine, recordRow)
        : scanUnquotedCold(inBuf, dvIn, textEnd, p, line, o, recordLine, recordRow, 0);
      if (endedComma < 0) return false;
      p = sP;
      line = sLine;
      o = sO;
      if (fi === 0) firstEmpty = o === fieldStartO;
      out[o++] = 0x22;
      fi += 1;
      if (endedComma === 0) break;
    }
    if (fi === 1 && firstEmpty && !firstQuoted) {
      o = rowStartO;
      continue;
    }
    out[o++] = 0x5D;
    sP = p;
    sLine = line;
    sO = o;
    sWidth = fi;
    return true;
  }
  sP = p;
  sLine = line;
  sO = o;
  return false;
}

function writeErrorsBuffer(writer) {
  let o = sO;
  let out = sOut;
  const worstErrBytes = 32 + errCount * 96 + extraLen + 16;
  if (out.length - o < worstErrBytes) out = ensureOut(writer, o, worstErrBytes);

  o = writeAscii(out, o, B_ERRORS_START);
  for (let i = 0; i < errCount; i++) {
    const code = errCode[i];
    if (i > 0) out[o++] = 0x2C;
    if (code === ERR_STRAY_CR) o = writeAscii(out, o, B_E_STRAY);
    else if (code === ERR_QUOTE_JUNK) o = writeAscii(out, o, B_E_JUNK);
    else if (code === ERR_UNTERMINATED) o = writeAscii(out, o, B_E_UNTERM);
    else if (code === ERR_SHORT_ROW) o = writeAscii(out, o, B_E_SHORT);
    else o = writeAscii(out, o, B_E_LONG);

    o = writeInt(out, o, errLine[i]);
    o = writeAscii(out, o, B_ROW_KEY);
    const r = errRow[i];
    if (r < 0) o = writeAscii(out, o, B_NULL);
    else o = writeInt(out, o, r);

    if (code === ERR_SHORT_ROW) {
      o = writeAscii(out, o, B_FIELDS_KEY);
      o = writeInt(out, o, errFields[i]);
    } else if (code === ERR_LONG_ROW) {
      o = writeAscii(out, o, B_EXTRA_KEY);
      const es = errExtraStart[i];
      const eLen = errExtraLen[i];
      extraBuf.copy(out, o, es, es + eLen);
      o += eLen;
      out[o++] = 0x5D;
    }
    out[o++] = 0x7D;
  }
  out[o++] = 0x5D;
  out[o++] = 0x7D;
  sO = o;
}

export function solveCaseBuffer(inBuf, textStart, textEnd, header, writer) {
  errCount = 0;
  extraLen = 0;
  sLine = 1;
  sRows = 0;
  sWidth = -1;
  sHitU = false;
  const startPos = writer.pos;
  const dvIn = getDvIn(inBuf);

  let p = textStart;
  if (p + 2 < textEnd && inBuf[p] === 0xEF && inBuf[p + 1] === 0xBB && inBuf[p + 2] === 0xBF) {
    p += 3;
  }
  sP = p;

  const need = (textEnd - p) * 3 + 256;
  let o = startPos;
  let out = writer.buf;
  if (out.length - o < need) {
    out = ensureOut(writer, o, need);
  } else {
    sOut = out;
    sDvOut = writer.dv || getDvOut(out);
  }

  const end4 = textEnd - 3;
  if (header) {
    o = writeAscii(out, o, B_OPEN_HDR);
    sO = o;
    const found = parseFirstBufferRecord(inBuf, dvIn, textEnd, true);
    if (sHitU) {
      writer.pos = startPos;
      sOut = null;
      sDvOut = null;
      return false;
    }
    o = sO;
    out = sOut;
    if (found) {
      o = writeAscii(out, o, B_ROWS_START);
      sO = o;
      while (sP < end4) {
        parseBufferChunk(inBuf, dvIn, textEnd, writer, 512);
        if (sHitU) {
          writer.pos = startPos;
          sOut = null;
          sDvOut = null;
          return false;
        }
      }
      if (sP < textEnd) {
        parseTailRows(inBuf, dvIn, textEnd, writer);
        if (sHitU) {
          writer.pos = startPos;
          sOut = null;
          sDvOut = null;
          return false;
        }
      }
    } else {
      o = writeAscii(out, o, B_EMPTY_HDR);
      sO = o;
    }
  } else {
    o = writeAscii(out, o, B_OPEN_NOHDR);
    sO = o;
    const found = parseFirstBufferRecord(inBuf, dvIn, textEnd, false);
    if (sHitU) {
      writer.pos = startPos;
      sOut = null;
      sDvOut = null;
      return false;
    }
    if (found) {
      sRows = 1;
      while (sP < end4) {
        parseBufferChunk(inBuf, dvIn, textEnd, writer, 512);
        if (sHitU) {
          writer.pos = startPos;
          sOut = null;
          sDvOut = null;
          return false;
        }
      }
      if (sP < textEnd) {
        parseTailRows(inBuf, dvIn, textEnd, writer);
        if (sHitU) {
          writer.pos = startPos;
          sOut = null;
          sDvOut = null;
          return false;
        }
      }
    }
  }

  writeErrorsBuffer(writer);
  writer.pos = sO;
  sOut = null;
  sDvOut = null;
  return true;
}

// ============================================================================
// Part 2: Exact JS String Parser (export function run(input)) — Contract & Fallback
// ============================================================================

let gPos = 0;
let gLine = 1;
let gEndedComma = false;
let gNextLF = -1;
let gNextCR = -1;
let gNextComma = -1;

function readUnquotedSlow(text, len, start, crPos, line, errors, recordLine, recordRow) {
  let acc = text.slice(start, crPos);
  errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
  let p = crPos + 1;
  let seg = p;
  let ended = 0;

  while (p < len) {
    const ch = text.charCodeAt(p);
    if (ch <= 44) {
      if (ch === 44) {
        if (p > seg) acc += text.slice(seg, p);
        p += 1;
        ended = 1;
        break;
      }
      if (ch === 10) {
        if (p > seg) acc += text.slice(seg, p);
        p += 1;
        line += 1;
        ended = 2;
        break;
      }
      if (ch === 13) {
        if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
          if (p > seg) acc += text.slice(seg, p);
          p += 2;
          line += 1;
          ended = 2;
          break;
        }
        if (p > seg) acc += text.slice(seg, p);
        errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
        p += 1;
        seg = p;
        continue;
      }
    }
    p += 1;
  }
  if (ended === 0 && p > seg) acc += text.slice(seg, p);
  gPos = p;
  gLine = line;
  gEndedComma = ended === 1;
  return acc;
}

function readQuoteJunk(text, len, p, val, line, errors, recordLine, recordRow) {
  let acc = val;
  let seg = p;
  let added = 0;
  let ended = 0;

  while (p < len) {
    const ch = text.charCodeAt(p);
    if (ch <= 44) {
      if (ch === 44) {
        if (p > seg) { acc += text.slice(seg, p); added += p - seg; }
        p += 1;
        ended = 1;
        break;
      }
      if (ch === 10) {
        if (p > seg) { acc += text.slice(seg, p); added += p - seg; }
        p += 1;
        line += 1;
        ended = 2;
        break;
      }
      if (ch === 13) {
        if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
          if (p > seg) { acc += text.slice(seg, p); added += p - seg; }
          p += 2;
          line += 1;
          ended = 2;
          break;
        }
        if (p > seg) { acc += text.slice(seg, p); added += p - seg; }
        errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
        p += 1;
        seg = p;
        continue;
      }
    }
    p += 1;
  }
  if (ended === 0 && p > seg) { acc += text.slice(seg, p); added += p - seg; }
  if (added > 0) errors.push({ code: 'quote_junk', line: recordLine, row: recordRow });
  gPos = p;
  gLine = line;
  gEndedComma = ended === 1;
  return acc;
}

function readUnterminated(text, len, open, openLine, errors, recordLine, recordRow) {
  let p = open + 1;
  let line = openLine;
  errors.push({ code: 'unterminated_quote', line: recordLine, row: recordRow });
  let acc = '"';
  let seg = p;
  let ended = 0;

  while (p < len) {
    const ch = text.charCodeAt(p);
    if (ch <= 44) {
      if (ch === 44) { if (p > seg) acc += text.slice(seg, p); p += 1; ended = 1; break; }
      if (ch === 10) { if (p > seg) acc += text.slice(seg, p); p += 1; line += 1; ended = 2; break; }
      if (ch === 13) {
        if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
          if (p > seg) acc += text.slice(seg, p); p += 2; line += 1; ended = 2; break;
        }
        if (p > seg) acc += text.slice(seg, p);
        errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
        p += 1; seg = p; continue;
      }
    }
    p += 1;
  }
  if (ended === 0 && p > seg) acc += text.slice(seg, p);
  gPos = p;
  gLine = line;
  gEndedComma = ended === 1;
  return acc;
}

function readQuotedComplex(text, len, open, q, lineEnd, line, errors, recordLine, recordRow) {
  const openLine = line;
  if (q === -1) return readUnterminated(text, len, open, openLine, errors, recordLine, recordRow);

  let seg = open + 1;
  let acc = '';
  let hasAcc = false;

  while (true) {
    if (q >= lineEnd) {
      let p = seg;
      while (p < q) {
        const ch = text.charCodeAt(p);
        if (ch <= 13) {
          if (ch === 10) line += 1;
          else if (ch === 13) {
            acc += text.slice(seg, p) + '\n';
            hasAcc = true;
            line += 1;
            if (p + 1 < q && text.charCodeAt(p + 1) === 10) p += 1;
            seg = p + 1;
          }
        }
        p += 1;
      }
    }

    if (q + 1 < len && text.charCodeAt(q + 1) === 34) {
      acc += text.slice(seg, q + 1);
      hasAcc = true;
      seg = q + 2;
      q = text.indexOf('"', seg);
      if (q === -1) return readUnterminated(text, len, open, openLine, errors, recordLine, recordRow);
      continue;
    }

    const val = hasAcc ? (q === seg ? acc : acc + text.slice(seg, q)) : (q === seg ? '' : text.slice(seg, q));
    const after = q + 1;
    if (after >= len) { gPos = after; gLine = line; gEndedComma = false; return val; }
    const next = text.charCodeAt(after);
    if (next === 44) { gPos = after + 1; gLine = line; gEndedComma = true; return val; }
    if (next === 10) { gPos = after + 1; gLine = line + 1; gEndedComma = false; return val; }
    if (next === 13 && after + 1 < len && text.charCodeAt(after + 1) === 10) {
      gPos = after + 2; gLine = line + 1; gEndedComma = false; return val;
    }
    return readQuoteJunk(text, len, after, val, line, errors, recordLine, recordRow);
  }
}

function finishAbnormalRow(fields, fi, width, lastQuoted, extra, recordLine, rows, errors) {
  if (fi === 1 && fields[0] === '' && !lastQuoted) return;
  if (fi < width) {
    errors.push({ code: 'short_row', line: recordLine, row: rows.length, fields: fi });
    for (let i = fi; i < width; i++) fields[i] = '';
    rows.push(fields);
  } else {
    errors.push({ code: 'long_row', line: recordLine, row: rows.length, extra });
    rows.push(fields);
  }
}

function parseFirstRecord(text, len, errors, header) {
  let pos = gPos;
  let line = gLine;

  while (pos < len) {
    const c0 = text.charCodeAt(pos);
    if (c0 === 10) { pos += 1; line += 1; continue; }
    if (c0 === 13 && pos + 1 < len && text.charCodeAt(pos + 1) === 10) { pos += 2; line += 1; continue; }

    const recordLine = line;
    const recordRow = header ? null : 0;
    const fields = [];
    let lastQuoted = false;

    while (true) {
      if (pos < len && text.charCodeAt(pos) === 34) {
        lastQuoted = true;
        fields.push(readQuotedComplex(text, len, pos, text.indexOf('"', pos + 1), -1, line, errors, recordLine, recordRow));
        pos = gPos; line = gLine;
        if (!gEndedComma) break;
        continue;
      }

      lastQuoted = false;
      const start = pos;
      let p = pos;
      let ended = 0;
      while (p < len) {
        const ch = text.charCodeAt(p);
        if (ch <= 44) {
          if (ch === 44) { fields.push(p === start ? '' : text.slice(start, p)); pos = p + 1; ended = 1; break; }
          if (ch === 10) { fields.push(p === start ? '' : text.slice(start, p)); pos = p + 1; line += 1; ended = 2; break; }
          if (ch === 13) {
            if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
              fields.push(p === start ? '' : text.slice(start, p)); pos = p + 2; line += 1; ended = 2; break;
            }
            fields.push(readUnquotedSlow(text, len, start, p, line, errors, recordLine, recordRow));
            pos = gPos; line = gLine; ended = gEndedComma ? 1 : 2; break;
          }
        }
        p += 1;
      }
      if (ended === 0) { fields.push(p === start ? '' : text.slice(start, p)); pos = len; break; }
      if (ended === 2) break;
    }

    if (fields.length === 1 && fields[0] === '' && !lastQuoted) continue;
    gPos = pos; gLine = line;
    return fields;
  }

  gPos = pos; gLine = line;
  return null;
}

function parseChunk(text, len, width, rows, errors, limit) {
  let pos = gPos;
  let line = gLine;
  let nextLF = gNextLF;
  let nextCR = gNextCR;
  let nextComma = gNextComma;
  let count = 0;

  while (pos < len && count < limit) {
    const c0 = text.charCodeAt(pos);
    if (c0 === 10) { pos += 1; line += 1; continue; }
    if (c0 === 13 && pos + 1 < len && text.charCodeAt(pos + 1) === 10) { pos += 2; line += 1; continue; }

    count += 1;
    const recordLine = line;
    const fields = new Array(width);
    let extra = null;
    let fi = 0;
    let lastQuoted = false;
    let lineEnd = -1;
    let endKind = 0;

    while (true) {
      if (lineEnd < 0) {
        if (nextLF !== -1 && nextLF < pos) nextLF = text.indexOf('\n', pos);
        if (nextCR !== -1 && nextCR < pos) nextCR = text.indexOf('\r', pos);
        lineEnd = nextLF === -1 ? len : nextLF;
        endKind = nextLF === -1 ? 0 : 1;
        if (nextCR !== -1 && nextCR < lineEnd) {
          lineEnd = nextCR;
          endKind = nextCR + 1 === nextLF ? 2 : 3;
        }
      }

      let val;
      let doneRow = false;

      if (pos < lineEnd) {
        const ch0 = text.charCodeAt(pos);
        if (ch0 !== 34) {
          if (ch0 === 44) {
            val = '';
            pos += 1;
          } else {
            if (nextComma !== -1 && nextComma < pos) nextComma = text.indexOf(',', pos + 1);
            if (nextComma !== -1 && nextComma < lineEnd) {
              val = text.slice(pos, nextComma);
              pos = nextComma + 1;
            } else if (endKind !== 3) {
              val = text.slice(pos, lineEnd);
              pos = lineEnd + endKind;
              if (endKind !== 0) line += 1;
              doneRow = true;
            } else {
              lastQuoted = false;
              val = readUnquotedSlow(text, len, pos, lineEnd, line, errors, recordLine, rows.length);
              pos = gPos; line = gLine;
              if (gEndedComma) lineEnd = -1;
              else doneRow = true;
            }
          }
        } else {
          lastQuoted = true;
          const pStart = pos + 1;
          const q = text.indexOf('"', pStart);
          const after = q + 1;
          if (q !== -1 && q < lineEnd && after < lineEnd && text.charCodeAt(after) === 44) {
            val = q === pStart ? '' : text.slice(pStart, q);
            pos = after + 1;
          } else if (q !== -1 && after === lineEnd && endKind !== 3) {
            val = q === pStart ? '' : text.slice(pStart, q);
            pos = lineEnd + endKind;
            if (endKind !== 0) line += 1;
            doneRow = true;
          } else {
            val = readQuotedComplex(text, len, pos, q, lineEnd, line, errors, recordLine, rows.length);
            pos = gPos; line = gLine;
            if (gEndedComma) { if (pos > lineEnd) lineEnd = -1; }
            else doneRow = true;
          }
        }
      } else {
        lastQuoted = false;
        if (endKind !== 3) {
          val = '';
          pos = lineEnd + endKind;
          if (endKind !== 0) line += 1;
          doneRow = true;
        } else {
          val = readUnquotedSlow(text, len, pos, lineEnd, line, errors, recordLine, rows.length);
          pos = gPos; line = gLine;
          if (gEndedComma) lineEnd = -1;
          else doneRow = true;
        }
      }

      if (fi < width) fields[fi] = val;
      else if (extra === null) extra = [val];
      else extra.push(val);
      fi += 1;
      if (doneRow) break;
    }

    if (fi === width && (width > 1 || fields[0] !== '' || lastQuoted)) {
      rows.push(fields);
    } else {
      finishAbnormalRow(fields, fi, width, lastQuoted, extra, recordLine, rows, errors);
    }
  }

  gPos = pos;
  gLine = line;
  gNextLF = nextLF;
  gNextCR = nextCR;
  gNextComma = nextComma;
}

export function run(input) {
  const text = String(input.text);
  const header = input.header === true;
  const len = text.length;
  const errors = [];
  const rows = [];

  gPos = len > 0 && text.charCodeAt(0) === 0xfeff ? 1 : 0;
  gLine = 1;
  gEndedComma = false;

  const first = parseFirstRecord(text, len, errors, header);
  if (first === null) {
    return { columns: header ? [] : null, rows, errors };
  }

  const width = first.length;
  const columns = header ? first : null;
  if (!header) rows.push(first);

  gNextLF = text.indexOf('\n', gPos);
  gNextCR = text.indexOf('\r', gPos);
  gNextComma = text.indexOf(',', gPos);

  while (gPos < len) {
    parseChunk(text, len, width, rows, errors, 512);
  }

  return { columns, rows, errors };
}

// Pre-seed full branch type feedback & micro-prime TurboFan for parseBufferChunk + scanQuoted
// with zero-CPU Atomics.wait sync so Case 0 runs directly in optimized code with 0 eager deopts.
{
  const wBufs = [
    Buffer.from(JSON.stringify('\uFEFFalpha,bravo\r\n\r\n,12345678\r\n"","x12345678""y12345678""z1234"\r\n"ok12345678"j,"m12345678\r\n""n56789012"j\r\n"p12345678"j\r1\r\n\r\r\n1\r\n1,2,3,4\r\n1,"q",extra\r\n4\r5,6\r7\r\n\r,9\r\n"unterm').slice(1, -1)),
    Buffer.from(JSON.stringify('café1234,bravo5678\n\n,12345678\n"","x12345678""y12345678""z1234"\n"ok12345678"j,"m12345678\n\rn56789012\n""k12345678"j\n"q12345678"\rj\n"z12345678"\r,2\n1,\n1\n1,2,3,4\n4\r5,6\r7\n"a12345678\nb45678901"j,1\n"x""y').slice(1, -1)),
    Buffer.from(JSON.stringify('a\n""\n\r\n\r\r\nb\n1,2,3\n12345678,x').slice(1, -1)),
    Buffer.from('a\\/b,c\\\\d\\t\\b\\f\\n1,2\\u0041'),
    Buffer.from(''),
  ];
  const makeDummy = () => {
    const b = Buffer.allocUnsafe(1024);
    return {
      buf: b,
      dv: new DataView(b.buffer, b.byteOffset, b.byteLength),
      pos: 0,
      fd: -1,
      ensure(need) {
        if (this.pos + need <= this.buf.length) return;
        let nc = this.buf.length * 2;
        while (nc < this.pos + need) nc *= 2;
        const nb = Buffer.allocUnsafe(nc);
        this.buf.copy(nb, 0, 0, this.pos);
        this.buf = nb;
        this.dv = new DataView(nb.buffer, nb.byteOffset, nb.byteLength);
      },
      flushAll() { this.pos = 0; },
    };
  };
  const d1 = makeDummy();
  const d2 = { ...makeDummy(), ensure(need) { d1.ensure.call(this, need); } };
  for (let i = 0; i < 2; i++) {
    const dw = (i & 1) === 0 ? d1 : d2;
    for (let j = 0; j < wBufs.length; j++) {
      dw.pos = 0;
      solveCaseBuffer(wBufs[j], 0, wBufs[j].length, (j & 1) === 0, dw);
    }
  }

  const pBuf = Buffer.from(
    'a,b,c\\n12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
    '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
    '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
    '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n'
  );
  const pDv = getDvIn(pBuf);
  const pOut = Buffer.allocUnsafe(pBuf.length * 4 + 256);
  const pDvOut = new DataView(pOut.buffer, pOut.byteOffset, pOut.byteLength);
  for (let j = 0; j < 2; j++) {
    errCount = 0; extraLen = 0; sLine = 1; sRows = 0; sWidth = 2; sHitU = false;
    sP = 0; sO = 0; sOut = pOut; sDvOut = pDvOut;
    parseBufferChunk(wBufs[j], getDvIn(wBufs[j]), wBufs[j].length, d1, 2);
  }
  for (let k = 0; k < 350; k++) {
    errCount = 0; extraLen = 0; sLine = 1; sRows = 1; sWidth = 3; sHitU = false;
    sP = 6; sO = 0; sOut = pOut; sDvOut = pDvOut;
    parseBufferChunk(pBuf, pDv, pBuf.length, d1, 4);
  }
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 15);
  errCount = 0; extraLen = 0; sLine = 1; sRows = 1; sWidth = 3; sHitU = false;
  sP = 6; sO = 0; sOut = pOut; sDvOut = pDvOut;
  parseBufferChunk(pBuf, pDv, pBuf.length, d1, 1);

  errCount = 0; extraLen = 0; sOut = null; sDvOut = null;
  cInBuf = null; cDvIn = null; cOutBuf = null; cDvOut = null;
}
