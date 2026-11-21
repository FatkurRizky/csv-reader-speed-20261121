import { closeSync, openSync, readFileSync, writeSync } from 'node:fs';
import { run, solveCaseBuffer } from './solve.js';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const CHUNK = 128;

// Monomorphic writer shared with solveCaseBuffer(inBuf, textStart, textEnd, header, writer) -> boolean.
// Guarantees at entry of each case: buf.length - pos >= (textEnd - textStart) * 3 + 65536.
// ensure(need) ONLY grows 2x + refreshes dv (never flushes) so intra-row and inline-\u rewinds are 100% safe.
// flushAll() is called once per case (perCase reused buffer: 6 writeSync syscalls, ~550 PF, L3-hot).
function createWriter(fd, initCap) {
  const buf = Buffer.allocUnsafe(initCap);
  return {
    buf,
    dv: new DataView(buf.buffer, buf.byteOffset, buf.byteLength),
    pos: 0,
    fd,
    flushThreshold: 0x7fffffff,
    ensure(need) {
      const req = this.pos + need;
      if (req <= this.buf.length) return;
      let nextCap = this.buf.length * 2;
      while (nextCap < req) nextCap *= 2;
      const nextBuf = Buffer.allocUnsafe(nextCap);
      if (this.pos > 0) this.buf.copy(nextBuf, 0, 0, this.pos);
      this.buf = nextBuf;
      this.dv = new DataView(nextBuf.buffer, nextBuf.byteOffset, nextBuf.byteLength);
    },
    flushIfReady() {},
    flushAll() {
      if (this.pos > 0) {
        writeSync(this.fd, this.buf, 0, this.pos);
        this.pos = 0;
      }
    },
  };
}

function emitAscii(writer, s) {
  const len = s.length;
  writer.ensure(len);
  writer.buf.write(s, writer.pos, len, 'latin1');
  writer.pos += len;
}

function emitUtf8(writer, s) {
  writer.ensure(s.length * 3 + 4);
  writer.pos += writer.buf.write(s, writer.pos, 'utf8');
}

function writeResultFallback(writer, r) {
  if (r.columns === null) {
    emitAscii(writer, '{"columns":null,"rows":');
  } else {
    emitAscii(writer, '{"columns":');
    emitUtf8(writer, JSON.stringify(r.columns));
    emitAscii(writer, ',"rows":');
  }
  const rows = r.rows;
  const rlen = rows.length;
  if (rlen === 0) {
    emitAscii(writer, '[]');
  } else {
    const scratch = new Array(CHUNK);
    for (let k = 0; k < rlen; k += CHUNK) {
      let s;
      if (k + CHUNK <= rlen) {
        for (let m = 0; m < CHUNK; m++) scratch[m] = rows[k + m];
        s = JSON.stringify(scratch);
      } else {
        s = JSON.stringify(rows.slice(k, rlen));
      }
      writer.ensure(s.length * 3 + 4);
      const n = writer.buf.write(s, writer.pos, 'utf8');
      if (k > 0) writer.buf[writer.pos] = 44;
      writer.pos += n - 1;
    }
    scratch.fill(undefined);
    writer.ensure(1);
    writer.buf[writer.pos++] = 93;
  }
  emitAscii(writer, ',"errors":');
  if (r.errors.length === 0) {
    emitAscii(writer, '[]}');
  } else {
    emitUtf8(writer, JSON.stringify(r.errors));
    writer.ensure(1);
    writer.buf[writer.pos++] = 125;
  }
}

// --- Fast 100%-sound RFC 8259 Raw-Buffer JSON Envelope Parser ---

function isWs(b) {
  return b === 32 || b === 10 || b === 13 || b === 9;
}

function skipWs(buf, p, len) {
  while (p < len) {
    const b = buf[p];
    if (b !== 32 && b !== 10 && b !== 13 && b !== 9) break;
    p++;
  }
  return p;
}

function isUnescaped(buf, start, q) {
  if (q <= start || buf[q - 1] !== 92) return true;
  let bs = 1;
  let k = q - 2;
  while (k >= start && buf[k] === 92) {
    bs++;
    k--;
  }
  return (bs & 1) === 0;
}

function findShortStringEnd(buf, start, len) {
  let p = start;
  while (p < len) {
    const b = buf[p];
    if (b === 34) return p;
    if (b === 92) {
      p += 2;
      continue;
    }
    p++;
  }
  return -1;
}

function findViaColon(buf, start, limit) {
  let p = start;
  while (p < limit) {
    const c = buf.indexOf(58, p); // ':'
    if (c === -1 || c >= limit) return -1;
    let k = c - 1;
    while (k >= start && isWs(buf[k])) k--;
    if (k > start && buf[k] === 34 && isUnescaped(buf, start, k)) {
      let j = k - 1;
      while (j >= start) {
        if (buf[j] === 34 && isUnescaped(buf, start, j)) break;
        j--;
      }
      if (j > start) {
        j--;
        while (j >= start && isWs(buf[j])) j--;
        if (j > start && buf[j] === 44) { // ','
          j--;
          while (j >= start && isWs(buf[j])) j--;
          if (j >= start && buf[j] === 34 && isUnescaped(buf, start, j)) return j;
        }
      }
    }
    p = c + 1;
  }
  return -1;
}

function findViaBrace(buf, start, limit) {
  let p = start;
  while (p < limit) {
    const br = buf.indexOf(125, p); // '}'
    if (br === -1 || br >= limit) return -1;
    let k = br - 1;
    while (k >= start && isWs(buf[k])) k--;
    if (k >= start && buf[k] === 34 && isUnescaped(buf, start, k)) return k;
    p = br + 1;
  }
  return -1;
}

function findObjStringEnd(buf, start, len, preferBrace) {
  if (preferBrace) {
    const brEnd = findViaBrace(buf, start, len);
    const limit = brEnd === -1 ? len : brEnd;
    const colEnd = findViaColon(buf, start, limit);
    return colEnd !== -1 ? colEnd : brEnd;
  }
  const colEnd = findViaColon(buf, start, len);
  const limit = colEnd === -1 ? len : colEnd;
  const brEnd = findViaBrace(buf, start, limit);
  return brEnd !== -1 ? brEnd : colEnd;
}

// Fast inline check for short object strings (<=64B such as "id":"g-0001") before memchr scan.
function findShortOrObjStringEnd(buf, start, len) {
  const lim = start + 64 < len ? start + 64 : len;
  let p = start;
  while (p < lim) {
    const b = buf[p];
    if (b === 34) return p;
    if (b === 92) {
      p += 2;
      continue;
    }
    p++;
  }
  return findObjStringEnd(buf, start, len, false);
}

function matchKey(buf, s, e, expected) {
  const klen = e - s;
  const elen = expected.length;
  let hasBs = false;
  for (let i = s; i < e; i++) {
    if (buf[i] === 92) {
      hasBs = true;
      break;
    }
  }
  if (!hasBs) {
    if (klen !== elen) return false;
    for (let i = 0; i < elen; i++) {
      if (buf[s + i] !== expected.charCodeAt(i)) return false;
    }
    return true;
  }
  try {
    return JSON.parse(buf.subarray(s - 1, e + 1).toString('utf8')) === expected;
  } catch {
    return false;
  }
}

function skipJsonValue(buf, p, len, inObject) {
  p = skipWs(buf, p, len);
  if (p >= len) return -1;
  const b = buf[p];
  if (b === 34) {
    const end = inObject ? findShortOrObjStringEnd(buf, p + 1, len) : findShortStringEnd(buf, p + 1, len);
    return end === -1 ? -1 : end + 1;
  }
  if (b === 123) {
    p = skipWs(buf, p + 1, len);
    if (p >= len) return -1;
    if (buf[p] === 125) return p + 1;
    while (true) {
      if (p >= len || buf[p] !== 34) return -1;
      const ke = findShortStringEnd(buf, p + 1, len);
      if (ke === -1) return -1;
      p = skipWs(buf, ke + 1, len);
      if (p >= len || buf[p] !== 58) return -1;
      p = skipJsonValue(buf, p + 1, len, true);
      if (p === -1) return -1;
      p = skipWs(buf, p, len);
      if (p >= len) return -1;
      if (buf[p] === 125) return p + 1;
      if (buf[p] !== 44) return -1;
      p = skipWs(buf, p + 1, len);
    }
  }
  if (b === 91) {
    p = skipWs(buf, p + 1, len);
    if (p >= len) return -1;
    if (buf[p] === 93) return p + 1;
    while (true) {
      p = skipJsonValue(buf, p, len, false);
      if (p === -1) return -1;
      p = skipWs(buf, p, len);
      if (p >= len) return -1;
      if (buf[p] === 93) return p + 1;
      if (buf[p] !== 44) return -1;
      p = skipWs(buf, p + 1, len);
    }
  }
  if (b === 116) {
    return p + 4 <= len && buf[p + 1] === 114 && buf[p + 2] === 117 && buf[p + 3] === 101 ? p + 4 : -1;
  }
  if (b === 102) {
    return p + 5 <= len && buf[p + 1] === 97 && buf[p + 2] === 108 && buf[p + 3] === 115 && buf[p + 4] === 101 ? p + 5 : -1;
  }
  if (b === 110) {
    return p + 4 <= len && buf[p + 1] === 117 && buf[p + 2] === 108 && buf[p + 3] === 108 ? p + 4 : -1;
  }
  if (b === 45 || (b >= 48 && b <= 57)) {
    p++;
    while (p < len) {
      const c = buf[p];
      if ((c >= 48 && c <= 57) || c === 46 || c === 101 || c === 69 || c === 43 || c === 45) p++;
      else break;
    }
    return p;
  }
  return -1;
}

function parseEnvelope(buf) {
  const len = buf.length;
  let p = 0;
  if (len >= 3 && buf[0] === 0xef && buf[1] === 0xbb && buf[2] === 0xbf) p = 3;
  p = skipWs(buf, p, len);
  if (p >= len || buf[p] !== 91) return null;
  p = skipWs(buf, p + 1, len);
  if (p >= len) return null;

  const list = [];
  if (buf[p] === 93) {
    p = skipWs(buf, p + 1, len);
    return p === len ? list : null;
  }

  while (true) {
    if (p >= len || buf[p] !== 123) return null;
    p = skipWs(buf, p + 1, len);
    if (p >= len || buf[p] === 125) return null;

    let hasInput = false;
    let inputStart = -1;
    let inputEnd = -1;
    let textStart = -1;
    let textEnd = -1;
    let hasText = false;
    let header = false;
    let directOk = false;

    while (true) {
      if (p >= len || buf[p] !== 34) return null;
      const ks = p + 1;
      const ke = findShortStringEnd(buf, ks, len);
      if (ke === -1) return null;
      p = skipWs(buf, ke + 1, len);
      if (p >= len || buf[p] !== 58) return null;
      p = skipWs(buf, p + 1, len);
      if (p >= len) return null;

      if (matchKey(buf, ks, ke, 'input')) {
        if (buf[p] !== 123) return null;
        hasInput = true;
        inputStart = p;
        hasText = false;
        textStart = -1;
        textEnd = -1;
        header = false;
        let seenHeader = false;
        directOk = true;

        p = skipWs(buf, p + 1, len);
        if (p >= len) return null;
        if (buf[p] !== 125) {
          while (true) {
            if (p >= len || buf[p] !== 34) return null;
            const iks = p + 1;
            const ike = findShortStringEnd(buf, iks, len);
            if (ike === -1) return null;
            p = skipWs(buf, ike + 1, len);
            if (p >= len || buf[p] !== 58) return null;
            p = skipWs(buf, p + 1, len);
            if (p >= len) return null;

            if (matchKey(buf, iks, ike, 'text')) {
              if (buf[p] === 34) {
                const ts = p + 1;
                const te = findObjStringEnd(buf, ts, len, seenHeader);
                if (te === -1) return null;
                textStart = ts;
                textEnd = te;
                hasText = true;
                p = te + 1;
              } else {
                directOk = false;
                p = skipJsonValue(buf, p, len, true);
                if (p === -1) return null;
              }
            } else if (matchKey(buf, iks, ike, 'header')) {
              seenHeader = true;
              if (p + 4 <= len && buf[p] === 116 && buf[p + 1] === 114 && buf[p + 2] === 117 && buf[p + 3] === 101) {
                header = true;
                p += 4;
              } else if (p + 5 <= len && buf[p] === 102 && buf[p + 1] === 97 && buf[p + 2] === 108 && buf[p + 3] === 115 && buf[p + 4] === 101) {
                header = false;
                p += 5;
              } else {
                header = false;
                p = skipJsonValue(buf, p, len, true);
                if (p === -1) return null;
              }
            } else {
              p = skipJsonValue(buf, p, len, true);
              if (p === -1) return null;
            }

            p = skipWs(buf, p, len);
            if (p >= len) return null;
            if (buf[p] === 125) {
              inputEnd = p + 1;
              p++;
              break;
            }
            if (buf[p] !== 44) return null;
            p = skipWs(buf, p + 1, len);
          }
        } else {
          inputEnd = p + 1;
          directOk = false;
          p++;
        }
        if (!hasText) directOk = false;
      } else {
        p = skipJsonValue(buf, p, len, true);
        if (p === -1) return null;
      }

      p = skipWs(buf, p, len);
      if (p >= len) return null;
      if (buf[p] === 125) {
        p++;
        break;
      }
      if (buf[p] !== 44) return null;
      p = skipWs(buf, p + 1, len);
    }

    if (!hasInput) return null;
    list.push({ textStart, textEnd, header, inputStart, inputEnd, directOk });

    p = skipWs(buf, p, len);
    if (p >= len) return null;
    if (buf[p] === 93) {
      p = skipWs(buf, p + 1, len);
      return p === len ? list : null;
    }
    if (buf[p] !== 44) return null;
    p = skipWs(buf, p + 1, len);
  }
}

// --- Main Execution ---

const rawBuf = readFileSync(`${INPUT_DIR}/cases.json`);
const fd = openSync(`${OUTPUT_DIR}/answers.json`, 'w');
const parsed = parseEnvelope(rawBuf);

if (parsed === null) {
  const cases = JSON.parse(rawBuf.toString('utf8'));
  if (cases.length === 0) {
    writeSync(fd, '[]');
  } else {
    const writer = createWriter(fd, 4 * 1024 * 1024);
    writer.buf[writer.pos++] = 91; // '['
    for (let i = 0; i < cases.length; i++) {
      if (i > 0) {
        writer.ensure(1);
        writer.buf[writer.pos++] = 44;
      }
      const inp = cases[i].input;
      cases[i] = null;
      writeResultFallback(writer, run(inp));
      if (i < cases.length - 1) writer.flushAll();
    }
    writer.ensure(1);
    writer.buf[writer.pos++] = 93; // ']'
    writer.flushAll();
  }
} else if (parsed.length === 0) {
  writeSync(fd, '[]');
} else {
  const n = parsed.length;
  let maxCaseLen = 0;
  for (let i = 0; i < n; i++) {
    const l = parsed[i].textEnd - parsed[i].textStart;
    if (l > maxCaseLen) maxCaseLen = l;
  }
  const writer = createWriter(fd, Math.max(4 * 1024 * 1024, maxCaseLen * 3 + 65536 + 16));
  const canStream = typeof solveCaseBuffer === 'function';

  for (let i = 0; i < n; i++) {
    const c = parsed[i];
    writer.ensure(1);
    writer.buf[writer.pos++] = i === 0 ? 91 : 44; // '[' or ','
    const caseStartPos = writer.pos;

    if (canStream && c.directOk) {
      const ok = solveCaseBuffer(rawBuf, c.textStart, c.textEnd, c.header, writer);
      if (ok === false) {
        writer.pos = caseStartPos;
        const inp = JSON.parse(rawBuf.subarray(c.inputStart, c.inputEnd).toString('utf8'));
        writeResultFallback(writer, run(inp));
      }
    } else {
      const inp = JSON.parse(rawBuf.subarray(c.inputStart, c.inputEnd).toString('utf8'));
      writeResultFallback(writer, run(inp));
    }
    if (i < n - 1) writer.flushAll();
  }

  writer.ensure(1);
  writer.buf[writer.pos++] = 93; // ']'
  writer.flushAll();
}

closeSync(fd);
