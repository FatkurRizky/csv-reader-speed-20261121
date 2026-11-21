// Ultra-fast drop-in replacement for make.fun's csv-reader 1.0.0.
// Pure ES module, zero dependencies, deterministic, stateless.
// Exports:
//   - run(input): exact {columns, rows, errors} JS object parser (contract & \uXXXX fallback)
//   - solveCaseBuffer(inBuf, textStart, textEnd, header, writer): zero-GC direct raw-JSON
//     UTF-8 Buffer CSV -> raw-JSON UTF-8 Buffer streaming engine.

// ============================================================================
// Part 1: Direct UTF-8 Raw-JSON-Buffer CSV -> JSON Streamer (solveCaseBuffer)
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

function ensureOut(writer, o, need) {
  writer.pos = o;
  writer.ensure(need);
  sOut = writer.buf;
  return sOut;
}

// Unquoted span scanner (mode 0 = normal / unterminated continuation, mode 1 = quote_junk).
// Returns 1 if ended at comma, 0 if ended at line break or EOF.
function scanUnquoted(inBuf, textEnd, p, line, o, writer, recordLine, recordRow, mode) {
  let out = sOut;
  let outLen = out.length;
  let hasJunk = false;

  while (p < textEnd) {
    if (outLen - o < 64) {
      out = ensureOut(writer, o, 4096);
      outLen = out.length;
    }
    let segEnd = p + (outLen - o - 32);
    if (segEnd > textEnd) segEnd = textEnd;

    const p0 = p;
    while (p < segEnd) {
      const b = inBuf[p];
      if (b === 0x2C || b === 0x5C) break;
      out[o++] = b;
      p += 1;
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
    if (b === 0x5C && p + 1 < textEnd) {
      const esc = inBuf[p + 1];
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
        if (p + 3 < textEnd && inBuf[p + 2] === 0x5C && inBuf[p + 3] === 0x6E) {
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
      continue;
    }
  }

  if (mode !== 0 && hasJunk) pushErr(ERR_QUOTE_JUNK, recordLine, recordRow, 0, 0, 0);
  sP = p;
  sLine = line;
  sO = o;
  return 0;
}

// Quoted field scanner starting at openP (`\"`).
// Returns 1 if ended at comma, 0 if ended at line break or EOF.
function scanQuoted(inBuf, textEnd, openP, openLine, fieldStartO, writer, recordLine, recordRow) {
  let out = sOut;
  let outLen = out.length;
  let p = openP + 2;
  let line = openLine;
  let o = fieldStartO;
  let closed = false;

  while (p < textEnd) {
    if (outLen - o < 64) {
      out = ensureOut(writer, o, 4096);
      outLen = out.length;
    }
    let segEnd = p + (outLen - o - 32);
    if (segEnd > textEnd) segEnd = textEnd;

    while (p < segEnd) {
      const b = inBuf[p];
      if (b === 0x5C) break;
      out[o++] = b;
      p += 1;
    }

    if (p >= textEnd) break;
    if (inBuf[p] !== 0x5C) continue;
    if (p + 1 >= textEnd) break;

    const esc = inBuf[p + 1];
    if (esc === 0x22) {
      if (p + 3 < textEnd && inBuf[p + 2] === 0x5C && inBuf[p + 3] === 0x22) {
        out[o++] = 0x5C;
        out[o++] = 0x22;
        p += 4;
        continue;
      }
      p += 2;
      closed = true;
      break;
    }
    if (esc === 0x72) {
      out[o++] = 0x5C;
      out[o++] = 0x6E;
      line += 1;
      if (p + 3 < textEnd && inBuf[p + 2] === 0x5C && inBuf[p + 3] === 0x6E) p += 4;
      else p += 2;
      continue;
    }
    if (esc === 0x6E) {
      out[o++] = 0x5C;
      out[o++] = 0x6E;
      line += 1;
      p += 2;
      continue;
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

  if (!closed) {
    o = fieldStartO;
    line = openLine;
    pushErr(ERR_UNTERMINATED, recordLine, recordRow, 0, 0, 0);
    if (outLen - o < 16) out = ensureOut(writer, o, 4096);
    out[o++] = 0x5C;
    out[o++] = 0x22;
    return scanUnquoted(inBuf, textEnd, openP + 2, line, o, writer, recordLine, recordRow, 0);
  }

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
    if (esc === 0x72 && p + 3 < textEnd && inBuf[p + 2] === 0x5C && inBuf[p + 3] === 0x6E) {
      sP = p + 4;
      sLine = line + 1;
      sO = o;
      return 0;
    }
  }
  return scanUnquoted(inBuf, textEnd, p, line, o, writer, recordLine, recordRow, 1);
}

// Hot body chunk parser (writer-property-free for zero-deopt TurboFan tier-up under --no-use-osr).
function parseBufferChunk(inBuf, textEnd, writer, limit) {
  let p = sP;
  let line = sLine;
  let o = sO;
  let rowsCount = sRows;
  const width = sWidth;
  let out = sOut;
  let outLen = out.length;
  let count = 0;

  while (p < textEnd && count < limit) {
    if (inBuf[p] === 0x5C && p + 1 < textEnd) {
      const esc = inBuf[p + 1];
      if (esc === 0x6E) {
        p += 2;
        line += 1;
        continue;
      }
      if (esc === 0x72 && p + 3 < textEnd && inBuf[p + 2] === 0x5C && inBuf[p + 3] === 0x6E) {
        p += 4;
        line += 1;
        continue;
      }
    }

    count += 1;
    const recordLine = line;
    const recordRow = rowsCount;
    const rowStartO = o;

    if (outLen - o < 256) {
      out = ensureOut(writer, o, 4096);
      outLen = out.length;
    }
    if (rowsCount > 0) out[o++] = 0x2C;
    out[o++] = 0x5B;

    let fi = 0;
    let cutO = 0;
    let firstQuoted = false;
    let firstEmpty = false;

    while (true) {
      if (outLen - o < 64) {
        out = ensureOut(writer, o, 4096);
        outLen = out.length;
      }
      if (fi > 0) out[o++] = 0x2C;
      out[o++] = 0x22;
      const fieldStartO = o;

      let endedComma = 0;
      const isQuoted = p + 1 < textEnd && inBuf[p] === 0x5C && inBuf[p + 1] === 0x22;
      if (fi === 0) firstQuoted = isQuoted;

      if (!isQuoted) {
        let segEnd = p + (outLen - o - 32);
        if (segEnd > textEnd) segEnd = textEnd;
        while (p < segEnd) {
          const b = inBuf[p];
          if (b === 0x2C || b === 0x5C) break;
          out[o++] = b;
          p += 1;
        }
        if (p < textEnd) {
          const b = inBuf[p];
          if (b === 0x2C) {
            p += 1;
            endedComma = 1;
          } else if (b === 0x5C && p + 1 < textEnd) {
            const esc = inBuf[p + 1];
            if (esc === 0x6E) {
              p += 2;
              line += 1;
            } else if (esc === 0x72 && p + 3 < textEnd && inBuf[p + 2] === 0x5C && inBuf[p + 3] === 0x6E) {
              p += 4;
              line += 1;
            } else {
              endedComma = scanUnquoted(inBuf, textEnd, p, line, o, writer, recordLine, recordRow, 0);
              p = sP;
              line = sLine;
              o = sO;
              out = sOut;
              outLen = out.length;
            }
          } else {
            endedComma = scanUnquoted(inBuf, textEnd, p, line, o, writer, recordLine, recordRow, 0);
            p = sP;
            line = sLine;
            o = sO;
            out = sOut;
            outLen = out.length;
          }
        }
      } else {
        endedComma = scanQuoted(inBuf, textEnd, p, line, fieldStartO, writer, recordLine, recordRow);
        p = sP;
        line = sLine;
        o = sO;
        out = sOut;
        outLen = out.length;
      }

      if (fi === 0) firstEmpty = o === fieldStartO;
      if (outLen - o < 16) {
        out = ensureOut(writer, o, 4096);
        outLen = out.length;
      }
      out[o++] = 0x22;
      fi += 1;
      if (fi === width) cutO = o;
      if (endedComma === 0) break;
    }

    if (fi === width) {
      if (width === 1 && firstEmpty && !firstQuoted) {
        o = rowStartO;
        continue;
      }
      out[o++] = 0x5D;
      rowsCount += 1;
    } else if (fi === 1 && firstEmpty && !firstQuoted) {
      o = rowStartO;
      continue;
    } else if (fi < width) {
      pushErr(ERR_SHORT_ROW, recordLine, recordRow, fi, 0, 0);
      const pad = width - fi;
      const need = pad * 3 + 8;
      if (outLen - o < need) {
        out = ensureOut(writer, o, need + 4096);
        outLen = out.length;
      }
      for (let k = 0; k < pad; k++) {
        out[o++] = 0x2C;
        out[o++] = 0x22;
        out[o++] = 0x22;
      }
      out[o++] = 0x5D;
      rowsCount += 1;
    } else {
      const eLen = o - (cutO + 1);
      const eStart = appendExtra(out, cutO + 1, eLen);
      pushErr(ERR_LONG_ROW, recordLine, recordRow, 0, eStart, eLen);
      o = cutO;
      out[o++] = 0x5D;
      rowsCount += 1;
    }
  }

  sP = p;
  sLine = line;
  sO = o;
  sRows = rowsCount;
}

function parseFirstBufferRecord(inBuf, textEnd, writer, header) {
  let p = sP;
  let line = sLine;
  let o = sO;
  let out = sOut;
  let outLen = out.length;
  const recordRow = header ? -1 : 0;

  while (p < textEnd) {
    if (inBuf[p] === 0x5C && p + 1 < textEnd) {
      const esc = inBuf[p + 1];
      if (esc === 0x6E) {
        p += 2;
        line += 1;
        continue;
      }
      if (esc === 0x72 && p + 3 < textEnd && inBuf[p + 2] === 0x5C && inBuf[p + 3] === 0x6E) {
        p += 4;
        line += 1;
        continue;
      }
    }

    const recordLine = line;
    const rowStartO = o;
    if (outLen - o < 64) {
      out = ensureOut(writer, o, 4096);
      outLen = out.length;
    }
    out[o++] = 0x5B;

    let fi = 0;
    let firstQuoted = false;
    let firstEmpty = false;

    while (true) {
      if (outLen - o < 64) {
        out = ensureOut(writer, o, 4096);
        outLen = out.length;
      }
      if (fi > 0) out[o++] = 0x2C;
      out[o++] = 0x22;
      const fieldStartO = o;

      const isQuoted = p + 1 < textEnd && inBuf[p] === 0x5C && inBuf[p + 1] === 0x22;
      if (fi === 0) firstQuoted = isQuoted;

      const endedComma = isQuoted
        ? scanQuoted(inBuf, textEnd, p, line, fieldStartO, writer, recordLine, recordRow)
        : scanUnquoted(inBuf, textEnd, p, line, o, writer, recordLine, recordRow, 0);
      p = sP;
      line = sLine;
      o = sO;
      out = sOut;
      outLen = out.length;

      if (fi === 0) firstEmpty = o === fieldStartO;
      if (outLen - o < 16) {
        out = ensureOut(writer, o, 4096);
        outLen = out.length;
      }
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

function writeErrorsBuffer(writer, flushThreshold) {
  let o = sO;
  let out = sOut;
  let outLen = out.length;

  if (outLen - o < 32) {
    out = ensureOut(writer, o, 4096);
    outLen = out.length;
  }
  o = writeAscii(out, o, B_ERRORS_START);

  for (let i = 0; i < errCount; i++) {
    if (o >= flushThreshold) {
      writer.pos = o;
      writer.flushIfReady();
      o = writer.pos;
      out = writer.buf;
      sOut = out;
      outLen = out.length;
    }
    const code = errCode[i];
    const eLen = code === ERR_LONG_ROW ? errExtraLen[i] : 0;
    const need = 96 + eLen;
    if (outLen - o < need) {
      out = ensureOut(writer, o, need + 4096);
      outLen = out.length;
    }
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
      extraBuf.copy(out, o, es, es + eLen);
      o += eLen;
      out[o++] = 0x5D;
    }
    out[o++] = 0x7D;
  }

  if (outLen - o < 4) out = ensureOut(writer, o, 64);
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
  sOut = writer.buf;
  const flushThreshold = writer.flushThreshold;

  let p = textStart;
  if (p + 2 < textEnd && inBuf[p] === 0xEF && inBuf[p + 1] === 0xBB && inBuf[p + 2] === 0xBF) {
    p += 3;
  }
  sP = p;

  let o = writer.pos;
  let out = sOut;
  if (out.length - o < 64) out = ensureOut(writer, o, 4096);

  if (header) {
    o = writeAscii(out, o, B_OPEN_HDR);
    sO = o;
    const found = parseFirstBufferRecord(inBuf, textEnd, writer, true);
    o = sO;
    out = sOut;
    if (out.length - o < 32) out = ensureOut(writer, o, 4096);
    if (found) {
      o = writeAscii(out, o, B_ROWS_START);
      sO = o;
      while (sP < textEnd) {
        if (sO >= flushThreshold) {
          writer.pos = sO;
          writer.flushIfReady();
          sO = writer.pos;
          sOut = writer.buf;
        }
        parseBufferChunk(inBuf, textEnd, writer, 512);
      }
    } else {
      o = writeAscii(out, o, B_EMPTY_HDR);
      sO = o;
    }
  } else {
    o = writeAscii(out, o, B_OPEN_NOHDR);
    sO = o;
    const found = parseFirstBufferRecord(inBuf, textEnd, writer, false);
    if (found) {
      sRows = 1;
      while (sP < textEnd) {
        if (sO >= flushThreshold) {
          writer.pos = sO;
          writer.flushIfReady();
          sO = writer.pos;
          sOut = writer.buf;
        }
        parseBufferChunk(inBuf, textEnd, writer, 512);
      }
    }
  }

  writeErrorsBuffer(writer, flushThreshold);
  writer.pos = sO;
  sOut = null;
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

// Pre-seed V8 type feedback for solveCaseBuffer with two distinct writer closures so
// no call site monomorphically pins to a warmup closure (0 eager deopts at runtime).
{
  const wBufs = [
    Buffer.from(JSON.stringify('\uFEFFa,b\r\n\r\n,1\r\n"","x""y""z"\r\n"ok"j,"m\r\n""n"j\r\n"p"j\r1\r\n\r\r\n1\r\n1,2,3,4\r\n4\r5,6\r7\r\n\r,9\r\n"u').slice(1, -1)),
    Buffer.from(JSON.stringify('café,b\n\n,1\n"","x""y""z"\n"ok"j,"m\n\rn\n""k"j\n"q"\rj\n"z"\r,2\n1,\n1\n1,2,3,4\n4\r5,6\r7\n"a\nb"j,1\n"x""y').slice(1, -1)),
    Buffer.from(JSON.stringify('a\n""\n\r\n\r\r\nb\n1,2,3\n').slice(1, -1)),
    Buffer.from('a\\/b,c\\\\d\\t\\b\\f\\n1,2'),
    Buffer.from(''),
  ];
  const makeDummy = () => ({
    buf: Buffer.allocUnsafe(128),
    pos: 0,
    fd: -1,
    flushThreshold: 64,
    ensure(need) {
      if (this.pos + need <= this.buf.length) return;
      let nc = this.buf.length * 2;
      while (nc < this.pos + need) nc *= 2;
      const nb = Buffer.allocUnsafe(nc);
      this.buf.copy(nb, 0, 0, this.pos);
      this.buf = nb;
    },
    flushIfReady() { if (this.pos >= this.flushThreshold) this.pos = 0; },
    flushAll() { this.pos = 0; },
  });
  const d1 = makeDummy();
  const d2 = {
    ...makeDummy(),
    ensure(need) { d1.ensure.call(this, need); },
    flushIfReady() { if (this.pos >= this.flushThreshold) this.pos = 0; },
  };
  for (let i = 0; i < 4; i++) {
    const dw = (i & 1) === 0 ? d1 : d2;
    for (let j = 0; j < wBufs.length; j++) {
      dw.pos = 0;
      solveCaseBuffer(wBufs[j], 0, wBufs[j].length, (j & 1) === 0, dw);
    }
  }
}
