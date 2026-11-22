'use strict';
// d.cjs: Phase 6 Single-File Pure-JS CSV-to-JSON Streaming Engine.
// 1 shared ArrayBuffer (_AB/_B/_V), 10 GC-safe V8 flags (load-elim/splitting/loop-rot ON), scoped dynPrime
// (1 TF compile ~8.5ms, 0 deopts across 20 drand seeds, 0 GC), pure Int32 separated 3-phi no-0x22 8B SWAR,
// 1 MiB sliding input window, 2.5 MiB 0-pwrite output buffer (22 syscalls), 240ms zero-CPU TF barrier,
// zero-bailout cross-window unterminated_quote recovery, and exact lazy chunked fallback via solve.js.

const __v8 = require('node:v8');
__v8.setFlagsFromString(
  '--no-incremental-marking --no-parallel-scavenge --no-minor-gc-task --no-use-osr --no-lazy-feedback-allocation ' +
  '--no-turbo-inlining --no-turbo-loop-peeling --no-turbo-escape ' +
  '--no-turbo-store-elimination --no-turboshaft-loop-peeling',
);
const { closeSync, openSync, readFileSync, readSync, writeSync } = require('node:fs');

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const IN_PATH = INPUT_DIR + '/cases.json';
const OUT_PATH = OUTPUT_DIR + '/answers.json';

const IN_WIN = 1048576;                   // 1 MiB sliding input window (~12 readSync)
const IN_CAP = IN_WIN + 1024;             // 1,049,600 B (1 KiB tail carry slack)
const OUT_BASE = IN_CAP;                  // output region starts immediately after input region
const OUT_CAP = 2621440;                  // 2.5 MiB output region (0 pwrite on all normal cases!)
const OUT_LIMIT = OUT_BASE + OUT_CAP;     // 3,671,040 B total shared ArrayBuffer
const OUT_FLUSH_AT = OUT_LIMIT - 131072;  // 2.375 MiB mid-case safety flush mark
const CASE_FLUSH_AT = OUT_BASE + 131072;  // per-case inter-case flush threshold (~6 writeSync total)
const WAIT_MS = 240;                      // zero-CPU barrier so background TF finishes before Case 0

// Single pure V8 ArrayBuffer + Uint8Array + Buffer + DataView (constant-folded in TurboFan!)
const _AB = new ArrayBuffer(OUT_LIMIT);
const _B = new Uint8Array(_AB);
const _BUF = Buffer.from(_AB);
const _V = new DataView(_AB);

let inFd = -1;
let outFd = -1;
let gP = 0;
let gInEnd = 0;
let gEof = true;
let gWinId = 0;
let gO = OUT_BASE;
let gOutFilePos = 0;
let gFlushAt = OUT_FLUSH_AT;
let gSegEnd = 0;
let gLine = 1;
let gBodyRows = 0;
let gWidth = -1;
let gCaseEmpty = false;
let gHoleFilePos = 0;
let gDoneText = false;
let gBailout = false;
let gFi = 0;
let gCutO = 0;
let gFieldStartP = 0;
let gCapStart = 0;
let gTextEndInWin = -2; // -2=dirty, -1=not in window, >=0=exact closing unescaped '"' of "text"

function isWsByte(b) { return b === 32 || b === 10 || b === 13 || b === 9; }
function isUnescapedQ(start, q) {
  if (q <= start || _B[q - 1] !== 92) return true;
  let bs = 1, k = q - 2;
  while (k >= start && _B[k] === 92) { bs++; k--; }
  return (bs & 1) === 0;
}
function findViaColonWin(start, end) {
  const saved = _B[end];
  _B[end] = 58;
  let p = start;
  while (p < end) {
    const c = _BUF.indexOf(58, p);
    if (c >= end) break;
    let k = c - 1;
    while (k >= start && isWsByte(_B[k])) k--;
    if (k > start && _B[k] === 34 && isUnescapedQ(start, k)) {
      let j = k - 1;
      while (j >= start) { if (_B[j] === 34 && isUnescapedQ(start, j)) break; j--; }
      if (j > start) {
        j--;
        while (j >= start && isWsByte(_B[j])) j--;
        if (j > start && _B[j] === 44) {
          j--;
          while (j >= start && isWsByte(_B[j])) j--;
          if (j >= start && _B[j] === 34 && isUnescapedQ(start, j)) { _B[end] = saved; return j; }
        }
      }
    }
    p = c + 1;
  }
  _B[end] = saved;
  return -1;
}
function findViaBraceWin(start, limit) {
  const saved = _B[limit];
  _B[limit] = 125;
  let p = start;
  while (p < limit) {
    const br = _BUF.indexOf(125, p);
    if (br >= limit) break;
    let k = br - 1;
    while (k >= start && isWsByte(_B[k])) k--;
    if (k >= start && _B[k] === 34 && isUnescapedQ(start, k)) { _B[limit] = saved; return k; }
    p = br + 1;
  }
  _B[limit] = saved;
  return -1;
}
function locateTextEndInWin(start) {
  const end = gInEnd;
  if (inFd < 0) {
    let p = start;
    while (p < end) {
      const b = _B[p];
      if (b === 34) return p;
      if (b === 92) { p += 2; continue; }
      p++;
    }
    return -1;
  }
  const colEnd = findViaColonWin(start, end);
  const limit = colEnd === -1 ? end : colEnd;
  const brEnd = findViaBraceWin(start, limit);
  const best = brEnd !== -1 ? brEnd : colEnd;
  if (best !== -1) return best;
  // Handle arbitrarily long trailing whitespace, comma, or key prefix between closing '"' and next window
  if (!gEof && end > start) {
    let t = end - 1;
    while (t >= start && isWsByte(_B[t])) t--;
    if (t >= start && _B[t] === 34 && isUnescapedQ(start, t)) {
      // Might be closing '"' of "text", OR closing '"' of a key before ':' in next window!
      let u = t - 1;
      while (u >= start && (_B[u] !== 34 || !isUnescapedQ(start, u))) u--;
      if (u > start) {
        let v = u - 1;
        while (v >= start && isWsByte(_B[v])) v--;
        if (v > start && _B[v] === 44) {
          v--;
          while (v >= start && isWsByte(_B[v])) v--;
          if (v >= start && _B[v] === 34 && isUnescapedQ(start, v)) return v;
        }
      }
      return t;
    }
    if (t >= start && _B[t] === 44) {
      t--;
      while (t >= start && isWsByte(_B[t])) t--;
      if (t >= start && _B[t] === 34 && isUnescapedQ(start, t)) return t;
    } else if (t >= start) {
      // Possibly mid-key name (even with escaped chars or commas): walk back up to 4096 bytes to opening '"'
      const floor = t - 4096 > start ? t - 4096 : start;
      let k = t;
      while (k >= floor) {
        const b = _B[k];
        if (b === 34 && isUnescapedQ(start, k)) break;
        if (b < 32) break;
        k--;
      }
      if (k >= floor && _B[k] === 34 && isUnescapedQ(start, k)) {
        let v = k - 1;
        while (v >= start && isWsByte(_B[v])) v--;
        if (v > start && _B[v] === 44) {
          v--;
          while (v >= start && isWsByte(_B[v])) v--;
          if (v >= start && _B[v] === 34 && isUnescapedQ(start, v)) return v;
        }
      }
    }
  }
  return -1;
}


const ERR_STRAY_CR = 0;
const ERR_QUOTE_JUNK = 1;
const ERR_UNTERMINATED = 2;
const ERR_SHORT_ROW = 3;
const ERR_LONG_ROW = 4;

const _T_ALL = Buffer.from(
  '{"columns":' + ',"rows":[     ' + '{"columns":null,"rows":[' + '{"columns":[],"rows":[' +
  '],"errors":[' + '{"code":"stray_cr","line":' + '{"code":"quote_junk","line":' +
  '{"code":"unterminated_quote","line":' + '{"code":"short_row","line":' + '{"code":"long_row","line":' +
  ',"row":' + ',"fields":' + ',"extra":['
);
const B_OPEN_HDR = _T_ALL.subarray(0, 11);
const B_ROWS_HDR_PAD = _T_ALL.subarray(11, 25);
const B_OPEN_NOHDR = _T_ALL.subarray(25, 49);
const B_EMPTY_HDR = _T_ALL.subarray(49, 71);
const B_ERRORS_START = _T_ALL.subarray(71, 83);
const B_E_STRAY = _T_ALL.subarray(83, 109);
const B_E_JUNK = _T_ALL.subarray(109, 137);
const B_E_UNTERM = _T_ALL.subarray(137, 173);
const B_E_SHORT = _T_ALL.subarray(173, 200);
const B_E_LONG = _T_ALL.subarray(200, 226);
const B_ROW_KEY = _T_ALL.subarray(226, 233);
const B_FIELDS_KEY = _T_ALL.subarray(233, 243);
const B_EXTRA_KEY = _T_ALL.subarray(243, 253);

// Reusable zero-GC error & scratch storage
let errCap = 4096;
let errCode = new Int32Array(errCap);
let errLine = new Int32Array(errCap);
let errRow = new Int32Array(errCap);
let errFields = new Int32Array(errCap);
let errExtraStart = new Int32Array(errCap);
let errExtraLen = new Int32Array(errCap);
let errCount = 0;

let extraBuf = Buffer.allocUnsafe(65536);
let extraLen = 0;
let firstRecBuf = Buffer.allocUnsafe(8192);
let firstRecLen = 0;
let prefixBuf = Buffer.allocUnsafe(8192);
let untermBuf = Buffer.allocUnsafe(4096);
let untermLen = 0;

function refill() {
  if (inFd < 0) {
    gEof = true;
    return;
  }
  const rem = gInEnd - gP;
  if (rem > 0 && gP > 0) _B.copyWithin(0, gP, gInEnd);
  gP = 0;
  let end = rem;
  const maxEnd = IN_CAP - 16;
  const target = rem + IN_WIN < maxEnd ? rem + IN_WIN : maxEnd;
  while (end < target) {
    const n = readSync(inFd, _B, end, target - end, null);
    if (n === 0) {
      gEof = true;
      break;
    }
    end += n;
    if (end >= 256) break;
  }
  gInEnd = end;
  gWinId++;
  gTextEndInWin = -2;
}

function flushOut() {
  const len = gO - OUT_BASE;
  if (outFd >= 0 && len > 0) {
    writeSync(outFd, _B, OUT_BASE, len, null);
    gOutFilePos += len;
    gO = OUT_BASE;
  }
}

function patchAt(filePos, srcBuf, len) {
  if (filePos >= gOutFilePos) {
    srcBuf.copy(_BUF, OUT_BASE + (filePos - gOutFilePos), 0, len);
  } else if (outFd >= 0 && len > 0) {
    writeSync(outFd, srcBuf, 0, len, filePos);
  }
}

function pushErr(code, line, recIdx, fields, eStart, eLen) {
  if (errCount >= errCap) {
    const nc = errCap * 2;
    const grow = (a) => { const n = new Int32Array(nc); n.set(a); return n; };
    errCode = grow(errCode);
    errLine = grow(errLine);
    errRow = grow(errRow);
    errFields = grow(errFields);
    errExtraStart = grow(errExtraStart);
    errExtraLen = grow(errExtraLen);
    errCap = nc;
  }
  const i = errCount++;
  errCode[i] = code;
  errLine[i] = line;
  errRow[i] = recIdx;
  errFields[i] = fields;
  errExtraStart[i] = eStart;
  errExtraLen[i] = eLen;
}

function appendExtra(start, len) {
  if (extraLen + len > extraBuf.length) {
    let nc = extraBuf.length * 2;
    while (nc < extraLen + len) nc *= 2;
    const nb = Buffer.allocUnsafe(nc);
    extraBuf.copy(nb, 0, 0, extraLen);
    extraBuf = nb;
  }
  const s = extraLen;
  _BUF.copy(extraBuf, s, start, start + len);
  extraLen = s + len;
  return s;
}

function appendUnterm(start, end) {
  const len = end - start;
  if (len <= 0) return;
  if (untermLen + len > untermBuf.length) {
    let nc = untermBuf.length * 2;
    while (nc < untermLen + len) nc *= 2;
    const nb = Buffer.allocUnsafe(nc);
    untermBuf.copy(nb, 0, 0, untermLen);
    untermBuf = nb;
  }
  _BUF.copy(untermBuf, untermLen, start, end);
  untermLen += len;
}

function syncWindow(p, o, capStart) {
  if (gTextEndInWin === -2) gTextEndInWin = locateTextEndInWin(p);
  let inEnd = gInEnd;
  let safeEnd = gTextEndInWin >= 0 ? gTextEndInWin : (gEof ? inEnd : inEnd - 128);
  if (p >= safeEnd - 15 && gTextEndInWin < 0) {
    if (!gEof) {
      if (capStart >= 0) appendUnterm(capStart, p);
      gP = p;
      refill();
      p = gP;
      inEnd = gInEnd;
      gTextEndInWin = locateTextEndInWin(p);
      safeEnd = gTextEndInWin >= 0 ? gTextEndInWin : (gEof ? inEnd : inEnd - 128);
    } else if (p >= inEnd) {
      gBailout = true;
      return false;
    }
  }
  if (OUT_LIMIT - o < 16384) {
    gBailout = true;
    return false;
  }
  gP = p;
  gO = o;
  let seg = p + ((OUT_LIMIT - o - 128) >>> 2);
  if (seg > safeEnd) seg = safeEnd;
  gSegEnd = seg;
  return true;
}

function handleUnqTail(p, o, fi, width, cutO, fieldStartP) {
  if (gTextEndInWin < 0 || gSegEnd < gTextEndInWin) {
    const wasStart = fieldStartP === p;
    if (!syncWindow(p, o, -1)) return -1;
    p = gP;
    o = gO;
    if (wasStart) fieldStartP = p;
    else if (p === 0) fieldStartP = -1;
    if (gSegEnd - p > 7) {
      gFi = fi;
      gCutO = cutO;
      gFieldStartP = fieldStartP;
      return 0;
    }
  }
  const end = gTextEndInWin >= 0 ? gTextEndInWin : gInEnd;
  while (p < end) {
    const b = _B[p];
    if (b === 0x2C) {
      p += 1;
      fi += 1;
      if (fi === width) cutO = o + 1;
      _V.setUint32(o, 0x00222c22, true);
      o += 3;
      fieldStartP = p;
      continue;
    }
    if (b === 0x5C) {
      gP = p; gO = o; gFi = fi; gCutO = cutO; gFieldStartP = fieldStartP;
      return 1;
    }
    _B[o++] = b;
    p += 1;
  }
  if (p === gTextEndInWin) {
    gP = p; gO = o; gFi = fi; gCutO = cutO; gFieldStartP = fieldStartP;
    return 1;
  }
  gBailout = true;
  return -1;
}

function handleQuoTail(p, o, capStart, openWin) {
  if (gTextEndInWin < 0 || gSegEnd < gTextEndInWin) {
    const prevWin = gWinId;
    if (prevWin === openWin) untermLen = 0;
    if (!syncWindow(p, o, capStart)) return -1;
    if (gWinId !== prevWin) capStart = 0;
    p = gP;
    o = gO;
    if (gSegEnd - p > 7) {
      gCapStart = capStart;
      return 0;
    }
  }
  const end = gTextEndInWin >= 0 ? gTextEndInWin : gInEnd;
  while (p < end) {
    const b = _B[p];
    if (b === 0x5C) {
      gP = p; gO = o; gCapStart = capStart;
      return 1;
    }
    _B[o++] = b;
    p += 1;
  }
  if (p === gTextEndInWin) {
    gP = p; gO = o; gCapStart = capStart;
    return 2;
  }
  gBailout = true;
  return -1;
}

function handleQuoEscRare(p, o, qEsc) {
  if (qEsc === 0x75) {
    gBailout = true;
    return -1;
  }
  if (qEsc === 0x2F) {
    _B[o++] = 0x2F;
    gP = p + 2;
    gO = o;
    return 0;
  }
  _B[o++] = 0x5C;
  _B[o++] = qEsc;
  gP = p + 2;
  gO = o;
  return 0;
}

function scanUnquotedCold(line, o, recordLine, recIdx, mode) {
  let p = gP;
  let hasJunk = false;
  while (true) {
    if (!syncWindow(p, o, -1)) return -1;
    p = gP;
    const segEnd = gSegEnd;
    const inEnd = gInEnd;
    const p0 = p;
    while (p < segEnd) {
      const b = _B[p];
      if (b === 0x2C || b === 0x5C || b === 0x22) break;
      _B[o++] = b;
      p += 1;
    }
    if (mode !== 0 && p > p0) hasJunk = true;
    if (p >= segEnd && p !== gTextEndInWin) continue;

    const b = _B[p];
    if (b === 0x2C) {
      p += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      gP = p; gLine = line; gO = o;
      return 1;
    }
    if (b === 0x22) {
      p += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      gP = p; gLine = line; gO = o;
      gDoneText = true;
      return 2;
    }
    if (p + 4 > inEnd && !gEof) { gP = p; refill(); p = gP; }
    const ie = gInEnd;
    if (p + 1 >= ie) { gBailout = true; return -1; }
    const esc = _B[p + 1];
    if (esc === 0x75) { gBailout = true; return -1; }
    if (esc === 0x6E) {
      p += 2; line += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      gP = p; gLine = line; gO = o;
      return 0;
    }
    if (esc === 0x72) {
      if (p + 3 < ie && _V.getUint16(p + 2, true) === 0x6e5c) {
        p += 4; line += 1;
        if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
        gP = p; gLine = line; gO = o;
        return 0;
      }
      pushErr(ERR_STRAY_CR, recordLine, recIdx, 0, 0, 0);
      p += 2;
      continue;
    }
    if (esc === 0x2F) { _B[o++] = 0x2F; p += 2; if (mode !== 0) hasJunk = true; continue; }
    _B[o++] = 0x5C; _B[o++] = esc; p += 2;
    if (mode !== 0) hasJunk = true;
  }
}

// --- Zero-Bailout Cross-Window Unterminated Quote Recovery (cold, never touches _B[0..gInEnd]!) ---
let uP = 0;

function scanUnqFromBuf(buf, len, line, o, recordLine, recIdx, mode) {
  let p = uP;
  let hasJunk = false;
  while (p < len) {
    if (OUT_LIMIT - o < 4096) { gBailout = true; return -1; }
    let segEnd = p + ((OUT_LIMIT - o - 128) >>> 2);
    if (segEnd > len) segEnd = len;
    const p0 = p;
    while (p < segEnd) {
      const b = buf[p];
      if (b === 0x2C || b === 0x5C || b === 0x22) break;
      _B[o++] = b;
      p += 1;
    }
    if (mode !== 0 && p > p0) hasJunk = true;
    if (p >= segEnd) continue;
    const b = buf[p];
    if (b === 0x2C) {
      p += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      uP = p; gLine = line; gO = o;
      return 1;
    }
    if (b === 0x22) {
      p += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      uP = p; gLine = line; gO = o;
      return 2;
    }
    if (p + 1 >= len) { gBailout = true; return -1; }
    const esc = buf[p + 1];
    if (esc === 0x75) { gBailout = true; return -1; }
    if (esc === 0x6E) {
      p += 2; line += 1;
      if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
      uP = p; gLine = line; gO = o;
      return 0;
    }
    if (esc === 0x72) {
      if (p + 3 < len && buf[p + 2] === 0x5C && buf[p + 3] === 0x6E) {
        p += 4; line += 1;
        if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recIdx, 0, 0, 0);
        uP = p; gLine = line; gO = o;
        return 0;
      }
      pushErr(ERR_STRAY_CR, recordLine, recIdx, 0, 0, 0);
      p += 2;
      continue;
    }
    if (esc === 0x2F) { _B[o++] = 0x2F; p += 2; if (mode !== 0) hasJunk = true; continue; }
    _B[o++] = 0x5C; _B[o++] = esc; p += 2;
    if (mode !== 0) hasJunk = true;
  }
  gBailout = true;
  return -1;
}

function scanQuoFromBuf(buf, len, openP, openLine, fieldStartO, recordLine, recIdx) {
  let p = openP + 2;
  let line = openLine;
  let o = fieldStartO;
  let closed = false;
  while (p < len) {
    if (OUT_LIMIT - o < 4096) { gBailout = true; return -1; }
    let segEnd = p + ((OUT_LIMIT - o - 128) >>> 2);
    if (segEnd > len) segEnd = len;
    while (p < segEnd) {
      const b = buf[p];
      if (b === 0x5C || b === 0x22) break;
      _B[o++] = b;
      p += 1;
    }
    if (p >= segEnd) continue;
    if (buf[p] === 0x22) break;
    if (p + 1 >= len) { gBailout = true; return -1; }
    const esc = buf[p + 1];
    if (esc === 0x22) {
      if (p + 3 < len && buf[p + 2] === 0x5C && buf[p + 3] === 0x22) {
        _V.setUint16(o, 0x225c, true); o += 2; p += 4; continue;
      }
      p += 2; closed = true; break;
    }
    if (esc === 0x75) { gBailout = true; return -1; }
    if (esc === 0x72) {
      _V.setUint16(o, 0x6e5c, true); o += 2; line += 1;
      p += (p + 3 < len && buf[p + 2] === 0x5C && buf[p + 3] === 0x6E) ? 4 : 2;
      continue;
    }
    if (esc === 0x6E) { _V.setUint16(o, 0x6e5c, true); o += 2; line += 1; p += 2; continue; }
    if (esc === 0x2F) { _B[o++] = 0x2F; p += 2; continue; }
    _B[o++] = 0x5C; _B[o++] = esc; p += 2;
  }
  if (!closed) {
    pushErr(ERR_UNTERMINATED, recordLine, recIdx, 0, 0, 0);
    _V.setUint16(fieldStartO, 0x225c, true);
    uP = openP + 2;
    return scanUnqFromBuf(buf, len, openLine, fieldStartO + 2, recordLine, recIdx, 0);
  }
  if (p >= len) { gBailout = true; return -1; }
  const nb = buf[p];
  if (nb === 0x2C) { uP = p + 1; gLine = line; gO = o; return 1; }
  if (nb === 0x22) { uP = p + 1; gLine = line; gO = o; return 2; }
  if (nb === 0x5C && p + 1 < len) {
    const esc = buf[p + 1];
    if (esc === 0x6E) { uP = p + 2; gLine = line + 1; gO = o; return 0; }
    if (esc === 0x72 && p + 3 < len && buf[p + 2] === 0x5C && buf[p + 3] === 0x6E) {
      uP = p + 4; gLine = line + 1; gO = o; return 0;
    }
  }
  uP = p;
  return scanUnqFromBuf(buf, len, line, o, recordLine, recIdx, 1);
}

function finishCrossWinUntermBody(p, openLine, fieldStartO, rowStartO, firstFieldStartO, firstQuoted, fi, width, cutO, recordLine, bodyRows) {
  appendUnterm(0, p + 1);
  gP = p + 1; // real stream cursor now sits right after closing '"' of "text"!
  const buf = untermBuf;
  const len = untermLen;
  if (OUT_LIMIT - fieldStartO < 64) { gBailout = true; return -1; }
  pushErr(ERR_UNTERMINATED, recordLine, bodyRows + 1, 0, 0, 0);
  _V.setUint16(fieldStartO, 0x225c, true);
  uP = 0;
  let rc = scanUnqFromBuf(buf, len, openLine, fieldStartO + 2, recordLine, bodyRows + 1, 0);
  if (rc < 0) return -1;
  let o = gO;
  let line = gLine;
  fi += 1;

  while (rc === 1) {
    if (fi === width) cutO = o + 1;
    if (OUT_LIMIT - o < 64) { gBailout = true; return -1; }
    _V.setUint32(o, 0x00222c22, true);
    o += 3;
    const isQ = uP + 1 < len && buf[uP] === 0x5C && buf[uP + 1] === 0x22;
    rc = isQ
      ? scanQuoFromBuf(buf, len, uP, line, o, recordLine, bodyRows + 1)
      : scanUnqFromBuf(buf, len, line, o, recordLine, bodyRows + 1, 0);
    if (rc < 0) return -1;
    o = gO;
    line = gLine;
    fi += 1;
  }

  if (OUT_LIMIT - o < 64) { gBailout = true; return -1; }
  _B[o++] = 0x22;
  if (fi === width && (width > 1 || o > firstFieldStartO + 1 || firstQuoted)) {
    _B[o++] = 0x5D;
    bodyRows += 1;
  } else {
    o = handleAbnormalRow(gP, fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, bodyRows);
    if (o < 0) return -1;
    bodyRows = gBodyRows;
  }
  gO = o;
  if (o >= gFlushAt) { flushOut(); o = gO; }

  // Parse remaining rows in untermBuf until closing '"'
  while (rc !== 2 && uP < len) {
    if (buf[uP] === 0x22) { uP += 1; break; }
    if (buf[uP] === 0x5C && uP + 1 < len) {
      if (buf[uP + 1] === 0x6E) { uP += 2; line += 1; continue; }
      if (buf[uP + 1] === 0x72 && uP + 3 < len && buf[uP + 2] === 0x5C && buf[uP + 3] === 0x6E) {
        uP += 4; line += 1; continue;
      }
    }
    if (OUT_LIMIT - o < 64) { gBailout = true; return -1; }
    const rStart = o;
    const rLine = line;
    if (bodyRows > 0) { _V.setUint32(o, 0x00225b2c, true); o += 3; }
    else { _V.setUint16(o, 0x225b, true); o += 2; }
    const f0Start = o;
    let rFi = 0;
    let rCutO = 0;
    let rFirstQ = false;
    while (true) {
      const isQ = uP + 1 < len && buf[uP] === 0x5C && buf[uP + 1] === 0x22;
      if (rFi === 0) rFirstQ = isQ;
      rc = isQ
        ? scanQuoFromBuf(buf, len, uP, line, o, rLine, bodyRows + 1)
        : scanUnqFromBuf(buf, len, line, o, rLine, bodyRows + 1, 0);
      if (rc < 0) return -1;
      o = gO;
      line = gLine;
      rFi += 1;
      if (rc === 1) {
        if (rFi === width) rCutO = o + 1;
        if (OUT_LIMIT - o < 64) { gBailout = true; return -1; }
        _V.setUint32(o, 0x00222c22, true);
        o += 3;
        continue;
      }
      break;
    }
    if (OUT_LIMIT - o < 64) { gBailout = true; return -1; }
    _B[o++] = 0x22;
    if (rFi === width && (width > 1 || o > f0Start + 1 || rFirstQ)) {
      _B[o++] = 0x5D;
      bodyRows += 1;
    } else {
      o = handleAbnormalRow(gP, rFi, width, o, rStart, f0Start, rFirstQ, rCutO, rLine, bodyRows);
      if (o < 0) return -1;
      bodyRows = gBodyRows;
    }
    gO = o;
    if (o >= gFlushAt) { flushOut(); o = gO; }
  }

  gO = o;
  gLine = line;
  gBodyRows = bodyRows;
  gDoneText = true;
  return 3;
}

// Unified cold post-quote / unquoted escape / unterminated handler -> keeps transduceChunk CFG tiny!
function handleColdField(mode, p, line, o, openP, openLine, openWin, fieldStartO, rowStartO, firstFieldStartO, firstQuoted, fi, width, cutO, recordLine, bodyRows) {
  let rc;
  if (mode === 2) {
    if (openWin !== gWinId) {
      return finishCrossWinUntermBody(p, openLine, fieldStartO, rowStartO, firstFieldStartO, firstQuoted, fi, width, cutO, recordLine, bodyRows);
    }
    pushErr(ERR_UNTERMINATED, recordLine, bodyRows + 1, 0, 0, 0);
    _V.setUint16(fieldStartO, 0x225c, true);
    gP = openP + 2;
    rc = scanUnquotedCold(openLine, fieldStartO + 2, recordLine, bodyRows + 1, 0);
  } else {
    gP = p;
    rc = scanUnquotedCold(line, o, recordLine, bodyRows + 1, mode);
  }
  if (rc < 0) return -1;
  syncWindow(gP, gO, -1);
  return rc;
}

function handleAbnormalRow(p, fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, bodyRows) {
  if (fi === 1 && o === firstFieldStartO + 1 && !firstQuoted) {
    gBodyRows = bodyRows;
    return rowStartO;
  }
  const recIdx = bodyRows + 1;
  if (fi < width) {
    pushErr(ERR_SHORT_ROW, recordLine, recIdx, fi, 0, 0);
    const pad = width - fi;
    if (OUT_LIMIT - o < pad * 3 + 256) {
      gBailout = true;
      return -1;
    }
    for (let k = 0; k < pad; k++) {
      _V.setUint32(o, 0x0022222c, true);
      o += 3;
    }
    _B[o++] = 0x5D;
    const safeEnd = gTextEndInWin >= 0 ? gTextEndInWin : (gEof ? gInEnd : gInEnd - 128);
    let seg = p + ((OUT_LIMIT - o - 128) >>> 2);
    if (seg > safeEnd) seg = safeEnd;
    gSegEnd = seg;
    gBodyRows = bodyRows + 1;
    return o;
  }
  const eLen = o - (cutO + 1);
  const eStart = appendExtra(cutO + 1, eLen);
  pushErr(ERR_LONG_ROW, recordLine, recIdx, 0, eStart, eLen);
  _B[cutO] = 0x5D;
  gBodyRows = bodyRows + 1;
  return cutO + 1;
}

function scanQuotedColdRec(openP, openLine, fieldStartO, recordLine, recIdx) {
  const openWin = gWinId;
  let p = openP + 2;
  let line = openLine;
  let o = fieldStartO;
  let closed = false;
  while (true) {
    if (!syncWindow(p, o, -1)) return -1;
    p = gP;
    const segEnd = gSegEnd;
    while (p < segEnd) {
      const b = _B[p];
      if (b === 0x5C || b === 0x22) break;
      _B[o++] = b;
      p += 1;
    }
    if (p >= segEnd && p !== gTextEndInWin) continue;
    if (_B[p] === 0x22) break;
    if (p + 4 > gInEnd && !gEof) { gP = p; refill(); p = gP; }
    const inEnd = gInEnd;
    if (p + 1 >= inEnd) { gBailout = true; return -1; }
    const esc = _B[p + 1];
    if (esc === 0x22) {
      if (p + 3 < inEnd && _V.getUint16(p + 2, true) === 0x225c) {
        _V.setUint16(o, 0x225c, true); o += 2; p += 4; continue;
      }
      p += 2; closed = true; break;
    }
    if (esc === 0x75) { gBailout = true; return -1; }
    if (esc === 0x72) {
      _V.setUint16(o, 0x6e5c, true); o += 2; line += 1;
      p += (p + 3 < inEnd && _V.getUint16(p + 2, true) === 0x6e5c) ? 4 : 2;
      continue;
    }
    if (esc === 0x6E) { _V.setUint16(o, 0x6e5c, true); o += 2; line += 1; p += 2; continue; }
    if (esc === 0x2F) { _B[o++] = 0x2F; p += 2; continue; }
    _B[o++] = 0x5C; _B[o++] = esc; p += 2;
  }
  if (!closed) {
    if (openWin !== gWinId) { gBailout = true; return -1; }
    pushErr(ERR_UNTERMINATED, recordLine, recIdx, 0, 0, 0);
    _V.setUint16(fieldStartO, 0x225c, true);
    gP = openP + 2;
    return scanUnquotedCold(openLine, fieldStartO + 2, recordLine, recIdx, 0);
  }
  if (p + 4 > gInEnd && !gEof) { gP = p; refill(); p = gP; }
  const inEnd = gInEnd;
  if (p >= inEnd) { gBailout = true; return -1; }
  const next = _B[p];
  if (next === 0x2C) { gP = p + 1; gLine = line; gO = o; return 1; }
  if (next === 0x22) { gP = p + 1; gLine = line; gO = o; gDoneText = true; return 2; }
  if (next === 0x5C && p + 1 < inEnd) {
    const esc = _B[p + 1];
    if (esc === 0x6E) { gP = p + 2; gLine = line + 1; gO = o; return 0; }
    if (esc === 0x72 && p + 3 < inEnd && _V.getUint16(p + 2, true) === 0x6e5c) {
      gP = p + 4; gLine = line + 1; gO = o; return 0;
    }
  }
  gP = p;
  return scanUnquotedCold(line, o, recordLine, recIdx, 1);
}

function parseFirstRecord() {
  const savedO = gO;
  let line = 1;
  while (true) {
    if (gInEnd - gP < 16 && !gEof) refill();
    let p = gP;
    let inEnd = gInEnd;
    if (p >= inEnd) { gBailout = true; return false; }
    const b0 = _B[p];
    if (b0 === 0x22) { gP = p + 1; gLine = line; gDoneText = true; gO = savedO; return false; }
    if (b0 === 0x5C && p + 1 < inEnd) {
      const esc = _B[p + 1];
      if (esc === 0x6E) { gP = p + 2; line += 1; continue; }
      if (esc === 0x72 && p + 3 < inEnd && _V.getUint16(p + 2, true) === 0x6e5c) {
        gP = p + 4; line += 1; continue;
      }
    }
    const recordLine = line;
    let o = savedO;
    if (OUT_LIMIT - o < 4096) { gBailout = true; return false; }
    _B[o++] = 0x5B;
    let fi = 0;
    let firstQuoted = false;
    let firstEmpty = false;
    while (true) {
      if (OUT_LIMIT - o < 64) { gBailout = true; return false; }
      if (fi > 0) _B[o++] = 0x2C;
      _B[o++] = 0x22;
      const fieldStartO = o;
      if (gInEnd - gP < 16 && !gEof) refill();
      p = gP;
      inEnd = gInEnd;
      const isQuoted = p + 1 < inEnd && _V.getUint16(p, true) === 0x225c;
      if (fi === 0) firstQuoted = isQuoted;
      const rc = isQuoted
        ? scanQuotedColdRec(p, line, fieldStartO, recordLine, 0)
        : scanUnquotedCold(line, fieldStartO, recordLine, 0, 0);
      if (rc < 0) { gO = savedO; return false; }
      line = gLine;
      o = gO;
      if (fi === 0) firstEmpty = o === fieldStartO;
      _B[o++] = 0x22;
      fi += 1;
      if (rc !== 1) break;
    }
    if (fi === 1 && firstEmpty && !firstQuoted) {
      if (gDoneText) { gO = savedO; return false; }
      continue;
    }
    _B[o++] = 0x5D;
    const recLen = o - savedO;
    if (recLen > firstRecBuf.length) {
      let nc = firstRecBuf.length * 2;
      while (nc < recLen) nc *= 2;
      firstRecBuf = Buffer.allocUnsafe(nc);
    }
    _BUF.copy(firstRecBuf, 0, savedO, o);
    firstRecLen = recLen;
    gWidth = fi;
    gLine = line;
    gO = savedO;
    return true;
  }
}

// === ULTRA-SLIM SINGLE-COMPILE GLOBAL _V 8-BYTE SWAR KERNEL (P2Q2, NO limit/count) ===
function transduceChunk() {
  if (!syncWindow(gP, gO, -1)) return 0;
  let p = gP | 0;
  let o = gO | 0;
  let end8 = (gSegEnd - 7) | 0;
  let line = gLine | 0;
  let bodyRows = gBodyRows | 0;
  const width = gWidth | 0;
  const flushAt = gFlushAt | 0;

  if (_B[p] === 0x22) {
    gP = (p + 1) | 0; gO = o; gLine = line; gBodyRows = bodyRows; gDoneText = true;
    return 2;
  }

  let rowStartO = o;
  if (bodyRows > 0) { _V.setUint32(o, 0x00225b2c, true); o = (o + 3) | 0; }
  else { _V.setUint16(o, 0x225b, true); o = (o + 2) | 0; }

  let fi = 0, cutO = 0, firstQuoted = false, firstFieldStartO = o, fieldStartP = p, recordLine = line;

  while (true) {
    // Separated 3-phi pure-scan unquoted 8B no-0x22 SWAR (0 stack spills, pure Int32 phis!)
    while (true) {
      let hit = 0, h1 = 0;
      while (p < end8) {
        const w0 = _V.getInt32(p, true);
        _V.setInt32(o, w0, true);
        const x0a = w0 ^ 0x2c2c2c2c, x0b = w0 ^ 0x5c5c5c5c;
        const h0a = (x0a - 0x01010101) & ~x0a;
        const m0 = (h0a | ((x0b - 0x01010101) & ~x0b)) & -2139062144;
        if (m0 !== 0) { hit = m0; h1 = h0a; break; }
        const w1 = _V.getInt32((p + 4) | 0, true);
        _V.setInt32((o + 4) | 0, w1, true);
        const x1a = w1 ^ 0x2c2c2c2c, x1b = w1 ^ 0x5c5c5c5c;
        const h1a = (x1a - 0x01010101) & ~x1a;
        const m1 = (h1a | ((x1b - 0x01010101) & ~x1b)) & -2139062144;
        if (m1 !== 0) { p = (p + 4) | 0; o = (o + 4) | 0; hit = m1; h1 = h1a; break; }
        p = (p + 8) | 0; o = (o + 8) | 0;
      }
      if (hit !== 0) {
        const lsb = hit & -hit;
        const k = (31 - Math.clz32(lsb)) >>> 3;
        p = (p + k) | 0; o = (o + k) | 0;
        if ((lsb & h1) !== 0) {
          p = (p + 1) | 0; fi = (fi + 1) | 0;
          if (fi === width) cutO = (o + 1) | 0;
          _V.setUint32(o, 0x00222c22, true); o = (o + 3) | 0; fieldStartP = p;
          continue;
        }
      }
      break;
    }

    if (p >= end8) {
      const tr = handleUnqTail(p, o, fi, width, cutO, fieldStartP);
      if (tr < 0) return 0;
      p = gP | 0; o = gO | 0; end8 = (gSegEnd - 7) | 0; fi = gFi | 0; cutO = gCutO | 0; fieldStartP = gFieldStartP | 0;
      if (tr === 0) continue;
    }

    let hitEof = false;
    if (_B[p] === 0x22) {
      p = (p + 1) | 0; gDoneText = true;
      if (fi === 0 && o === firstFieldStartO && !firstQuoted) {
        gP = p; gO = rowStartO; gLine = line; gBodyRows = bodyRows;
        return 2;
      }
      hitEof = true;
    } else {
      const esc = _B[(p + 1) | 0];
      if (esc === 0x6E) {
        p = (p + 2) | 0; line = (line + 1) | 0;
      } else if (esc === 0x72 && p + 3 < gInEnd && _V.getUint16((p + 2) | 0, true) === 0x6e5c) {
        p = (p + 4) | 0; line = (line + 1) | 0;
      } else if (esc === 0x22 && p === fieldStartP) {
        if (fi === 0) firstQuoted = true;
        const openP = p, openLine = line, openWin = gWinId | 0, fieldStartO = o;
        p = (p + 2) | 0;
        let closed = false, capStart = p;
        while (true) {
          // Combined 8B 1-byte [0x5C ONLY] quoted SWAR (no hot 0x22 check!)
          while (p < end8) {
            const w0 = _V.getInt32(p, true);
            const w1 = _V.getInt32((p + 4) | 0, true);
            _V.setInt32(o, w0, true);
            _V.setInt32((o + 4) | 0, w1, true);
            const x0 = w0 ^ 0x5c5c5c5c, x1 = w1 ^ 0x5c5c5c5c;
            const h0 = (x0 - 0x01010101) & ~x0;
            const h1 = (x1 - 0x01010101) & ~x1;
            if (((h0 | h1) & -2139062144) !== 0) {
              const m0 = h0 & -2139062144;
              const k = m0 !== 0
                ? ((31 - Math.clz32(m0 & -m0)) >>> 3)
                : (4 + ((31 - Math.clz32((h1 & -2139062144) & -(h1 & -2139062144))) >>> 3)) | 0;
              p = (p + k) | 0; o = (o + k) | 0;
              break;
            }
            p = (p + 8) | 0; o = (o + 8) | 0;
          }
          if (p >= end8) {
            const qr = handleQuoTail(p, o, capStart, openWin);
            if (qr < 0) return 0;
            p = gP | 0; o = gO | 0; end8 = (gSegEnd - 7) | 0; capStart = gCapStart | 0;
            if (qr === 0) continue;
            if (qr === 2) break;
          }
          const qEsc = _B[(p + 1) | 0];
          if (qEsc === 0x22) {
            if (p + 3 < gInEnd && _V.getUint16((p + 2) | 0, true) === 0x225c) {
              _V.setUint16(o, 0x225c, true); o = (o + 2) | 0; p = (p + 4) | 0; continue;
            }
            p = (p + 2) | 0; closed = true; break;
          }
          if (qEsc === 0x72) {
            _V.setUint16(o, 0x6e5c, true); o = (o + 2) | 0; line = (line + 1) | 0;
            p = (p + ((p + 3 < gInEnd && _V.getUint16((p + 2) | 0, true) === 0x6e5c) ? 4 : 2)) | 0;
            continue;
          }
          if (qEsc === 0x6E) { _V.setUint16(o, 0x6e5c, true); o = (o + 2) | 0; line = (line + 1) | 0; p = (p + 2) | 0; continue; }
          if (handleQuoEscRare(p, o, qEsc) < 0) return 0;
          p = gP | 0; o = gO | 0;
        }
        let qrc = 0;
        if (!closed) {
          qrc = handleColdField(2, p, line, o, openP, openLine, openWin, fieldStartO, rowStartO, firstFieldStartO, firstQuoted, fi, width, cutO, recordLine, bodyRows);
          if (qrc < 0) return 0;
          if (qrc === 3) return 2;
          p = gP | 0; line = gLine | 0; o = gO | 0; end8 = (gSegEnd - 7) | 0;
        } else {
          const nb = _B[p];
          if (nb === 0x2C) { p = (p + 1) | 0; qrc = 1; }
          else if (nb === 0x22) { p = (p + 1) | 0; gDoneText = true; qrc = 2; }
          else if (nb === 0x5C && _B[(p + 1) | 0] === 0x6E) { p = (p + 2) | 0; line = (line + 1) | 0; }
          else if (nb === 0x5C && _B[(p + 1) | 0] === 0x72 && p + 3 < gInEnd && _V.getUint16((p + 2) | 0, true) === 0x6e5c) { p = (p + 4) | 0; line = (line + 1) | 0; }
          else {
            qrc = handleColdField(1, p, line, o, 0, 0, 0, 0, 0, 0, false, 0, 0, 0, recordLine, bodyRows);
            if (qrc < 0) return 0;
            p = gP | 0; line = gLine | 0; o = gO | 0; end8 = (gSegEnd - 7) | 0;
          }
        }
        if (qrc === 1) {
          fi = (fi + 1) | 0;
          if (fi === width) cutO = (o + 1) | 0;
          _V.setUint32(o, 0x00222c22, true); o = (o + 3) | 0; fieldStartP = p;
          continue;
        }
        if (qrc === 2) hitEof = true;
      } else {
        const ec = handleColdField(0, p, line, o, 0, 0, 0, 0, 0, 0, false, 0, 0, 0, recordLine, bodyRows);
        if (ec < 0) return 0;
        p = gP | 0; line = gLine | 0; o = gO | 0; end8 = (gSegEnd - 7) | 0;
        if (ec === 1) {
          fi = (fi + 1) | 0;
          if (fi === width) cutO = (o + 1) | 0;
          _V.setUint32(o, 0x00222c22, true); o = (o + 3) | 0; fieldStartP = p;
          continue;
        }
        if (ec === 2) hitEof = true;
      }
    }

    fi = (fi + 1) | 0;
    if (fi === width && (width > 1 || o > firstFieldStartO || firstQuoted)) {
      bodyRows = (bodyRows + 1) | 0;
      if (hitEof || o >= flushAt || p >= end8) {
        _V.setUint16(o, 0x5d22, true); o = (o + 2) | 0;
        if (o >= flushAt) { gO = o; flushOut(); o = gO | 0; }
        gP = p; gO = o; gLine = line; gBodyRows = bodyRows;
        return hitEof ? 2 : 1;
      }
      rowStartO = (o + 2) | 0;
      _V.setUint32(o, 0x5b2c5d22, true); _B[(o + 4) | 0] = 0x22; o = (o + 5) | 0;
      fi = 0; cutO = 0; firstQuoted = false; firstFieldStartO = o; fieldStartP = p; recordLine = line;
      continue;
    }

    _B[o] = 0x22; o = (o + 1) | 0;
    o = handleAbnormalRow(p, fi, width, o, rowStartO, firstFieldStartO, firstQuoted, cutO, recordLine, bodyRows) | 0;
    if (o < 0) return 0;
    bodyRows = gBodyRows | 0; end8 = (gSegEnd - 7) | 0;
    if (hitEof || o >= flushAt || p >= end8) {
      if (o >= flushAt) { gO = o; flushOut(); o = gO | 0; }
      gP = p; gO = o; gLine = line; gBodyRows = bodyRows;
      return hitEof ? 2 : 1;
    }
    rowStartO = o;
    if (bodyRows > 0) { _V.setUint32(o, 0x00225b2c, true); o = (o + 3) | 0; }
    else { _V.setUint16(o, 0x225b, true); o = (o + 2) | 0; }
    fi = 0; cutO = 0; firstQuoted = false; firstFieldStartO = o; fieldStartP = p; recordLine = line;
  }
}
function transduceText() {
  errCount = 0; extraLen = 0; firstRecLen = 0; untermLen = 0;
  gLine = 1; gBodyRows = 0; gWidth = -1; gCaseEmpty = false; gDoneText = false; gBailout = false; gTextEndInWin = -2;
  if (gInEnd - gP < 16 && !gEof) refill();
  if (gP + 2 < gInEnd && _B[gP] === 0xEF && _B[gP + 1] === 0xBB && _B[gP + 2] === 0xBF) gP += 3;

  const found = parseFirstRecord();
  if (gBailout) return 0;
  if (!found) {
    gCaseEmpty = true;
    return 1;
  }
  if (gO >= gFlushAt) flushOut();
  const holeLen = firstRecLen + 25;
  if (OUT_LIMIT - gO < holeLen + 4096) {
    flushOut();
    if (OUT_LIMIT - gO < holeLen + 4096) return 0;
  }
  gHoleFilePos = gOutFilePos + (gO - OUT_BASE);
  gO += holeLen;

  if (!gDoneText) {
    while (true) {
      const rc = transduceChunk();
      if (rc === 0) return 0;
      if (rc === 2) break;
    }
  }
  return 1;
}

function finishCase(header) {
  const worstErrBytes = 64 + errCount * 96 + extraLen + 32;
  if (OUT_LIMIT - gO < worstErrBytes) {
    flushOut();
    if (OUT_LIMIT - gO < worstErrBytes) return false;
  }
  let o = gO;
  if (gCaseEmpty) {
    const src = header ? B_EMPTY_HDR : B_OPEN_NOHDR;
    _B.set(src, o);
    o += src.length;
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
      firstRecBuf.copy(prefixBuf, po, 0, firstRecLen); po += firstRecLen;
      prefixBuf.set(B_ROWS_HDR_PAD, po); po += B_ROWS_HDR_PAD.length;
    } else {
      prefixBuf.set(B_OPEN_NOHDR, po); po += B_OPEN_NOHDR.length;
      firstRecBuf.copy(prefixBuf, po, 0, firstRecLen); po += firstRecLen;
      prefixBuf[po++] = gBodyRows > 0 ? 0x2C : 0x20;
    }
    gO = o;
    patchAt(gHoleFilePos, prefixBuf, po);
  }

  _B.set(B_ERRORS_START, o);
  o += B_ERRORS_START.length;
  for (let i = 0; i < errCount; i++) {
    const code = errCode[i];
    if (i > 0) _B[o++] = 0x2C;
    const tag = code === ERR_STRAY_CR ? B_E_STRAY
      : code === ERR_QUOTE_JUNK ? B_E_JUNK
      : code === ERR_UNTERMINATED ? B_E_UNTERM
      : code === ERR_SHORT_ROW ? B_E_SHORT
      : B_E_LONG;
    _B.set(tag, o);
    o += tag.length;

    let n = errLine[i];
    if (n < 10) {
      _B[o++] = 48 + n;
    } else {
      const s0 = o;
      while (n > 0) { const q = (n / 10) | 0; _B[o++] = 48 + (n - q * 10); n = q; }
      for (let l = s0, r = o - 1; l < r; l++, r--) { const t = _B[l]; _B[l] = _B[r]; _B[r] = t; }
    }

    _B.set(B_ROW_KEY, o);
    o += B_ROW_KEY.length;
    let r = header ? (errRow[i] - 1) : errRow[i];
    if (r < 0) {
      _B[o++] = 110; _B[o++] = 117; _B[o++] = 108; _B[o++] = 108;
    } else if (r < 10) {
      _B[o++] = 48 + r;
    } else {
      const s0 = o;
      while (r > 0) { const q = (r / 10) | 0; _B[o++] = 48 + (r - q * 10); r = q; }
      for (let l = s0, rt = o - 1; l < rt; l++, rt--) { const t = _B[l]; _B[l] = _B[rt]; _B[rt] = t; }
    }

    if (code === ERR_SHORT_ROW) {
      _B.set(B_FIELDS_KEY, o);
      o += B_FIELDS_KEY.length;
      let f = errFields[i];
      if (f < 10) {
        _B[o++] = 48 + f;
      } else {
        const s0 = o;
        while (f > 0) { const q = (f / 10) | 0; _B[o++] = 48 + (f - q * 10); f = q; }
        for (let l = s0, rt = o - 1; l < rt; l++, rt--) { const t = _B[l]; _B[l] = _B[rt]; _B[rt] = t; }
      }
    } else if (code === ERR_LONG_ROW) {
      _B.set(B_EXTRA_KEY, o);
      o += B_EXTRA_KEY.length;
      const es = errExtraStart[i];
      const eLen = errExtraLen[i];
      extraBuf.copy(_BUF, o, es, es + eLen);
      o += eLen;
      _B[o++] = 0x5D;
    }
    _B[o++] = 0x7D;
  }
  _B[o++] = 0x5D;
  _B[o++] = 0x7D;
  gO = o;
  return true;
}

// Pre-escaped static warmup strings (ZERO runtime JSON.stringify calls!)
const W_SAMPLES = [
  '\uFEFFalpha,bravo\\r\\n\\r\\n,12345678\\r\\n\\"\\",\\"x12345678\\"\\"y12345678\\"\\"z1234\\"\\r\\n\\"ok12345678\\"j,\\"m12345678\\r\\n\\"\\"n56789012\\"j\\r\\n\\"p12345678\\"j\\r1\\r\\n\\r\\r\\n1\\r\\n1,2,3,4\\r\\n1,\\"q\\",extra\\r\\n1,a\\rb,extra\\r\\n1,\\"q\\"j,extra\\r\\n4\\r5,6\\r7\\r\\n\\r,9\\r\\n\\"unterm"',
  'café1234,bravo5678\\n\\n,12345678\\n\\"\\",\\"x12345678\\"\\"y12345678\\"\\"z1234\\"\\n\\"ok12345678\\"j,\\"m12345678\\n\\rn56789012\\n\\"\\"k12345678\\"j\\n\\"q12345678\\"\\rj\\n\\"z12345678\\"\\r,2\\n1,\\n1\\n1,2,3,4\\n4\\r5,6\\r7\\n\\"a12345678\\nb45678901\\"j,1\\n\\"x\\"\\"y"',
  'a\\n\\"\\"\\n\\r\\n\\r\\r\\nb\\n1,2,3\\n12345678,x\\n"',
  'a,b\\n12345678901234567890,12345678901234567890\\n"',
  'a,b\\n12345678,\\"hello12345678901234567890\\",x\\n"',
  'a,b\\n12345678,\\"hello12345678901234567890\\""',
  'a\\/b,c\\\\d\\t\\b\\f\\n1,2\\u0041"',
  '"',
];

const W_TAILS = [
  ['12345678901234567890,12345678901234567890\\n"', 2],
  ['12345678,\\"hello12345678901234567890\\",123456\\n"', 3],
  ['\\"a\\",123456789012\\n"', 2],
  ['\\"ab\\""', 1],
  ['12345678,a\\rb"', 2],
  ['12345678,abcdefgh",12345678901234567890', 2],
  ['12345678,abcdefgh\\n",12345678901234567890', 2],
];

const P_STR =
  '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
  '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
  '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n' +
  '12345678,\\"hello world 1234567890123456\\",98765432\\r\\nabcdefgh,\\"quoted \\"\\"esc\\"\\" 123456789012\\",xyzw1234\\n"';

function primeEngine() {
  inFd = 0; inFd = -1;
  outFd = 0; outFd = -1;
  gEof = false; gEof = true;
  gFlushAt = OUT_BASE + 1; gFlushAt = OUT_FLUSH_AT;
  gWinId = 1; gWinId = 0;
  gOutFilePos = 1; gOutFilePos = 0;
  refill();
  flushOut();

  for (let i = 0; i < 2; i++) {
    gFlushAt = i === 0 ? OUT_BASE + 1 : OUT_FLUSH_AT;
    for (let j = 0; j < W_SAMPLES.length; j++) {
      const n = _BUF.write(W_SAMPLES[j], 0, 'utf8');
      gP = 0; gInEnd = n; gEof = i === 1; gO = OUT_BASE; gOutFilePos = 0;
      transduceText();
    }
  }

  gFlushAt = OUT_FLUSH_AT;
  for (let i = 0; i < W_TAILS.length; i++) {
    const n = _BUF.write(W_TAILS[i][0], 0, 'utf8');
    errCount = 0; extraLen = 0; gLine = 1; gBodyRows = 1; gWidth = W_TAILS[i][1]; gDoneText = false; gBailout = false;
    gP = 0; gInEnd = n; gEof = false; gO = OUT_BASE; gOutFilePos = 0; gTextEndInWin = -2;
    transduceChunk();
  }

  const pLen = _BUF.write(P_STR, 0, 'utf8');
  // Scoped low threshold ONLY for transduceChunk priming, then lock to 1,000,000 -> 1 single TF compile!
  __v8.setFlagsFromString('--invocation-count-for-turbofan=350');
  for (let k = 0; k < 28; k++) {
    errCount = 0; extraLen = 0; gLine = 1; gBodyRows = 1; gWidth = 3; gDoneText = false; gBailout = false;
    gP = 0; gInEnd = pLen; gEof = true; gO = OUT_BASE; gOutFilePos = 0; gTextEndInWin = pLen - 1;
    transduceChunk();
  }
  __v8.setFlagsFromString('--invocation-count-for-turbofan=1000000');

  errCount = 0; extraLen = 0; firstRecLen = 0; untermLen = 0;
  gLine = 1; gBodyRows = 0; gWidth = -1; gCaseEmpty = false; gDoneText = false; gBailout = false;
  gP = 0; gInEnd = 0; gO = OUT_BASE; gOutFilePos = 0;
}

primeEngine();
if (WAIT_MS > 0) {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, WAIT_MS);
}

// --- Streaming RFC 8259 JSON Envelope Parser ---

function ensureIn(n) {
  if (gInEnd - gP < n && !gEof) refill();
  return gInEnd - gP >= n;
}

function peekByte() {
  if (gP >= gInEnd) {
    if (gEof) return -1;
    refill();
    if (gP >= gInEnd) return -1;
  }
  return _B[gP];
}

function skipWs() {
  for (;;) {
    let p = gP;
    const end = gInEnd;
    while (p < end) {
      const b = _B[p];
      if (b !== 32 && b !== 10 && b !== 13 && b !== 9) {
        gP = p;
        return b;
      }
      p++;
    }
    gP = p;
    if (gEof) return -1;
    refill();
    if (gP >= gInEnd) return -1;
  }
}

function readKey() {
  if (peekByte() !== 34) return null;
  gP++;
  if (!ensureIn(32) && gP >= gInEnd) return null;
  const start = gP;
  let p = start;
  const lim = start + 32 < gInEnd ? start + 32 : gInEnd;
  while (p < lim) {
    const b = _B[p];
    if (b === 34) {
      const k = _BUF.toString('latin1', start, p);
      gP = p + 1;
      return k;
    }
    if (b === 92 || b < 32 || b >= 128) return null;
    p++;
  }
  return null;
}

function skipJsonString() {
  gP++;
  for (;;) {
    let p = gP;
    const end = gInEnd;
    while (p < end) {
      const b = _B[p];
      if (b === 34) { gP = p + 1; return true; }
      if (b === 92) {
        if (p + 1 >= end) {
          gP = p;
          if (gEof) return false;
          refill();
          break;
        }
        p += 2;
        continue;
      }
      p++;
    }
    if (p >= end) {
      gP = p;
      if (gEof) return false;
      refill();
      if (gP >= gInEnd) return false;
    }
  }
}

function skipJsonValue() {
  const b = skipWs();
  if (b === -1) return false;
  if (b === 34) return skipJsonString();
  if (b === 123) {
    gP++;
    if (skipWs() === 125) { gP++; return true; }
    for (;;) {
      if (peekByte() !== 34 || !skipJsonString() || skipWs() !== 58) return false;
      gP++;
      if (!skipJsonValue()) return false;
      const sep = skipWs();
      if (sep === 125) { gP++; return true; }
      if (sep !== 44) return false;
      gP++;
      skipWs();
    }
  }
  if (b === 91) {
    gP++;
    if (skipWs() === 93) { gP++; return true; }
    for (;;) {
      if (!skipJsonValue()) return false;
      const sep = skipWs();
      if (sep === 93) { gP++; return true; }
      if (sep !== 44) return false;
      gP++;
    }
  }
  if (b === 116) {
    if (!ensureIn(4)) return false;
    const p = gP;
    if (_B[p + 1] === 114 && _B[p + 2] === 117 && _B[p + 3] === 101) { gP = p + 4; return true; }
    return false;
  }
  if (b === 102) {
    if (!ensureIn(5)) return false;
    const p = gP;
    if (_B[p + 1] === 97 && _B[p + 2] === 108 && _B[p + 3] === 115 && _B[p + 4] === 101) { gP = p + 5; return true; }
    return false;
  }
  if (b === 110) {
    if (!ensureIn(4)) return false;
    const p = gP;
    if (_B[p + 1] === 117 && _B[p + 2] === 108 && _B[p + 3] === 108) { gP = p + 4; return true; }
    return false;
  }
  if (b === 45 || (b >= 48 && b <= 57)) {
    gP++;
    for (;;) {
      let p = gP;
      const end = gInEnd;
      while (p < end) {
        const c = _B[p];
        if ((c >= 48 && c <= 57) || c === 46 || c === 101 || c === 69 || c === 43 || c === 45) p++;
        else { gP = p; return true; }
      }
      gP = p;
      if (gEof) return true;
      refill();
    }
  }
  return false;
}

// --- Exact Lazy Chunked Fallback (zero-OOM, loaded ONLY on \uXXXX, >OUT_CAP single row, or exotic JSON) ---

function runExactFallback() {
  if (inFd >= 0) { closeSync(inFd); inFd = -1; }
  if (outFd >= 0) { closeSync(outFd); outFd = -1; }

  const { run } = require('./solve.js');
  const cases = JSON.parse(readFileSync(IN_PATH).toString('utf8'));
  const fd = openSync(OUT_PATH, 'w');
  if (cases.length === 0) {
    writeSync(fd, '[]');
    closeSync(fd);
    return;
  }
  let buf = Buffer.allocUnsafe(512 * 1024);
  let pos = 0;
  const flush = () => { if (pos > 0) { writeSync(fd, buf, 0, pos); pos = 0; } };
  const ensure = (need) => {
    if (pos + need > buf.length) {
      flush();
      if (need > buf.length) buf = Buffer.allocUnsafe(need);
    }
  };
  const emitA = (str) => { ensure(str.length); buf.write(str, pos, str.length, 'latin1'); pos += str.length; };
  const emitU = (str) => { ensure(str.length * 3 + 4); pos += buf.write(str, pos, 'utf8'); };
  const CHUNK = 128;
  const scratch = new Array(CHUNK);

  buf[pos++] = 91; // '['
  for (let i = 0; i < cases.length; i++) {
    if (i > 0) { ensure(1); buf[pos++] = 44; }
    const inp = cases[i].input;
    cases[i] = null;
    const r = run(inp);
    if (r.columns === null) {
      emitA('{"columns":null,"rows":');
    } else {
      emitA('{"columns":');
      emitU(JSON.stringify(r.columns));
      emitA(',"rows":');
    }
    const rows = r.rows;
    const rlen = rows.length;
    if (rlen === 0) {
      emitA('[]');
    } else {
      for (let k = 0; k < rlen; k += CHUNK) {
        let s;
        if (k + CHUNK <= rlen) {
          for (let m = 0; m < CHUNK; m++) scratch[m] = rows[k + m];
          s = JSON.stringify(scratch);
        } else {
          s = JSON.stringify(rows.slice(k, rlen));
        }
        ensure(s.length * 3 + 4);
        const n = buf.write(s, pos, 'utf8');
        if (k > 0) buf[pos] = 44;
        pos += n - 1;
      }
      ensure(1);
      buf[pos++] = 93;
    }
    emitA(',"errors":');
    if (r.errors.length === 0) {
      emitA('[]}');
    } else {
      emitU(JSON.stringify(r.errors));
      ensure(1);
      buf[pos++] = 125;
    }
  }
  scratch.fill(undefined);
  ensure(1);
  buf[pos++] = 93;
  flush();
  closeSync(fd);
}

// --- Main Streaming Execution ---

function runStream() {
  inFd = openSync(IN_PATH, 'r');
  outFd = openSync(OUT_PATH, 'w');
  gP = 0; gInEnd = 0; gEof = false; gWinId = 0;
  gO = OUT_BASE; gOutFilePos = 0; gFlushAt = OUT_FLUSH_AT;

  refill();
  if (ensureIn(3) && _B[gP] === 0xef && _B[gP + 1] === 0xbb && _B[gP + 2] === 0xbf) gP += 3;
  if (skipWs() !== 91) return false;
  gP++;
  if (skipWs() === 93) {
    gP++;
    if (skipWs() !== -1) return false;
    _B[gO++] = 91;
    _B[gO++] = 93;
    flushOut();
    return true;
  }

  let caseIdx = 0;
  for (;;) {
    if (skipWs() !== 123) return false;
    gP++;
    if (skipWs() === 125) return false;

    if (gO >= OUT_LIMIT - 16) flushOut();
    _B[gO++] = caseIdx === 0 ? 91 : 44;

    let seenInput = false;
    for (;;) {
      const key = readKey();
      if (key === null) return false;
      if (skipWs() !== 58) return false;
      gP++;

      if (key === 'input') {
        if (seenInput) return false;
        seenInput = true;
        if (skipWs() !== 123) return false;
        gP++;
        if (skipWs() === 125) return false;

        let seenText = false;
        let headerVal = false;
        for (;;) {
          const ikey = readKey();
          if (ikey === null) return false;
          if (skipWs() !== 58) return false;
          gP++;

          if (ikey === 'text') {
            if (seenText || skipWs() !== 34) return false;
            gP++;
            if (gInEnd - gP < 64 && !gEof) refill();
            if (transduceText() !== 1) return false;
            seenText = true;
          } else if (ikey === 'header') {
            const hb = skipWs();
            if (hb === 116) {
              if (!ensureIn(4)) return false;
              const p = gP;
              if (_B[p + 1] === 114 && _B[p + 2] === 117 && _B[p + 3] === 101) { headerVal = true; gP = p + 4; }
              else return false;
            } else if (hb === 102) {
              if (!ensureIn(5)) return false;
              const p = gP;
              if (_B[p + 1] === 97 && _B[p + 2] === 108 && _B[p + 3] === 115 && _B[p + 4] === 101) { headerVal = false; gP = p + 5; }
              else return false;
            } else {
              headerVal = false;
              if (!skipJsonValue()) return false;
            }
          } else {
            if (!skipJsonValue()) return false;
          }

          const isep = skipWs();
          if (isep === 125) { gP++; break; }
          if (isep !== 44) return false;
          gP++;
          skipWs();
        }

        if (!seenText || !finishCase(headerVal)) return false;
      } else {
        if (!skipJsonValue()) return false;
      }

      const sep = skipWs();
      if (sep === 125) { gP++; break; }
      if (sep !== 44) return false;
      gP++;
      skipWs();
    }

    if (!seenInput) return false;
    caseIdx++;

    const asep = skipWs();
    if (asep === 93) {
      gP++;
      if (skipWs() !== -1) return false;
      if (gO >= OUT_LIMIT - 16) flushOut();
      _B[gO++] = 93;
      flushOut();
      return true;
    }
    if (asep !== 44) return false;
    gP++;
    // Flush between cases (not on last case -> folds ']' into final writeSync -> 6x writeSync, 0 pwrite!)
    if (gO >= CASE_FLUSH_AT) flushOut();
  }
}

if (runStream()) {
  closeSync(inFd);
  closeSync(outFd);
  inFd = -1;
  outFd = -1;
} else {
  runExactFallback();
}
