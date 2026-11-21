import { closeSync, openSync, readFileSync, writeSync } from 'node:fs';
import { setFlagsFromString } from 'node:v8';

// 5 verified safe V8 flags (pass forced Major GC in Node v22.23.4; never use --single-threaded-gc).
setFlagsFromString(
  '--no-incremental-marking --no-parallel-scavenge --no-minor-gc-task --no-use-osr --no-lazy-feedback-allocation',
);

const { run, solveCaseBuffer } = await import('./solve.js');

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const BS_U = Buffer.from('\\u');
const CHUNK = 128;

// Monomorphic output writer shared with solveCaseBuffer(inBuf, textStart, textEnd, header, writer).
// Contract: ensure(need) ONLY grows buf (never flushes) so intra-row rewinds stay 100% valid;
// flushIfReady() flushes ONLY at complete row / case boundaries.
function createWriter(fd) {
  return {
    buf: Buffer.allocUnsafe(2 * 1024 * 1024),
    pos: 0,
    fd,
    flushThreshold: 512 * 1024,
    ensure(need) {
      const req = this.pos + need;
      if (req <= this.buf.length) return;
      let nextCap = this.buf.length * 2;
      while (nextCap < req) nextCap *= 2;
      const nextBuf = Buffer.allocUnsafe(nextCap);
      if (this.pos > 0) this.buf.copy(nextBuf, 0, 0, this.pos);
      this.buf = nextBuf;
    },
    flushIfReady() {
      if (this.pos >= this.flushThreshold) {
        writeSync(this.fd, this.buf, 0, this.pos);
        this.pos = 0;
      }
    },
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

// Chunked zero-slice JSON writer for fallback cases (e.g. \uXXXX escapes or exotic JSON envelope).
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
      if (k > 0) writer.buf[writer.pos] = 44; // replace leading '[' with ','
      writer.pos += n - 1; // drop trailing ']'
      writer.flushIfReady();
    }
    scratch.fill(undefined);
    writer.ensure(1);
    writer.buf[writer.pos++] = 93; // ']'
  }
  emitAscii(writer, ',"errors":');
  if (r.errors.length === 0) {
    emitAscii(writer, '[]}');
  } else {
    emitUtf8(writer, JSON.stringify(r.errors));
    writer.ensure(1);
    writer.buf[writer.pos++] = 125; // '}'
  }
}

// --- Fast RFC 8259 Raw-Buffer JSON Envelope Parser ---

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

// Fast short JSON string end scanner (used for keys, "id", and skipped metadata strings).
// Returns index of closing '"', or -1 on error.
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

// 100%-sound RFC 8259 O(1)-hit AVX2 memchr string-end locator for large object string values.
// Inside any valid JSON object, the closing '"' of a string value MUST be followed by either:
//   (1) ws* '}'  -> located via memchr('}')
//   (2) ws* ',' ws* '"' <nextKey> '"' ws* ':' -> located via memchr(':')
// Every '"' inside the string has an odd count of preceding '\', so isUnescaped() has 0 false positives.
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
          if (j >= start && buf[j] === 34 && isUnescaped(buf, start, j)) {
            return j;
          }
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
    if (k >= start && buf[k] === 34 && isUnescaped(buf, start, k)) {
      return k;
    }
    p = br + 1;
  }
  return -1;
}

function findObjStringEnd(buf, start, len) {
  const colEnd = findViaColon(buf, start, len);
  const limit = colEnd === -1 ? len : colEnd;
  const brEnd = findViaBrace(buf, start, limit);
  return brEnd !== -1 ? brEnd : colEnd;
}

// Match JSON key bytes [s, e) against expected ASCII string (handles rare escaped keys via JSON.parse).
function matchKey(buf, s, e, expected) {
  const klen = e - s;
  const elen = expected.length;
  // Fast unescaped path
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

// Skip any arbitrary RFC 8259 JSON value starting at p; returns next offset or -1 on malformed input.
function skipJsonValue(buf, p, len, inObject) {
  p = skipWs(buf, p, len);
  if (p >= len) return -1;
  const b = buf[p];
  if (b === 34) { // string
    const end = inObject ? findObjStringEnd(buf, p + 1, len) : findShortStringEnd(buf, p + 1, len);
    return end === -1 ? -1 : end + 1;
  }
  if (b === 123) { // object
    p = skipWs(buf, p + 1, len);
    if (p >= len) return -1;
    if (buf[p] === 125) return p + 1;
    while (true) {
      if (p >= len || buf[p] !== 34) return -1;
      const ke = findShortStringEnd(buf, p + 1, len);
      if (ke === -1) return -1;
      p = skipWs(buf, ke + 1, len);
      if (p >= len || buf[p] !== 58) return -1; // ':'
      p = skipJsonValue(buf, p + 1, len, true);
      if (p === -1) return -1;
      p = skipWs(buf, p, len);
      if (p >= len) return -1;
      if (buf[p] === 125) return p + 1;
      if (buf[p] !== 44) return -1;
      p = skipWs(buf, p + 1, len);
    }
  }
  if (b === 91) { // array
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
  if (b === 116) { // true
    if (p + 4 <= len && buf[p + 1] === 114 && buf[p + 2] === 117 && buf[p + 3] === 101) return p + 4;
    return -1;
  }
  if (b === 102) { // false
    if (p + 5 <= len && buf[p + 1] === 97 && buf[p + 2] === 108 && buf[p + 3] === 115 && buf[p + 4] === 101) return p + 5;
    return -1;
  }
  if (b === 110) { // null
    if (p + 4 <= len && buf[p + 1] === 117 && buf[p + 2] === 108 && buf[p + 3] === 108) return p + 4;
    return -1;
  }
  if (b === 45 || (b >= 48 && b <= 57)) { // number
    p++;
    while (p < len) {
      const c = buf[p];
      if ((c >= 48 && c <= 57) || c === 46 || c === 101 || c === 69 || c === 43 || c === 45) {
        p++;
      } else {
        break;
      }
    }
    return p;
  }
  return -1;
}

// Parse outer envelope `[{"id":...,"input":{"text":"...","header":...}}, ...]` into case descriptors.
// Returns array of { textStart, textEnd, header, inputStart, inputEnd, directOk }, or null to trigger full fallback.
function parseEnvelope(buf) {
  const len = buf.length;
  let p = 0;
  // Strip optional UTF-8 BOM on cases.json itself if any
  if (len >= 3 && buf[0] === 0xef && buf[1] === 0xbb && buf[2] === 0xbf) p = 3;
  p = skipWs(buf, p, len);
  if (p >= len || buf[p] !== 91) return null; // '['
  p = skipWs(buf, p + 1, len);
  if (p >= len) return null;

  const list = [];
  if (buf[p] === 93) { // ']'
    p = skipWs(buf, p + 1, len);
    return p === len ? list : null;
  }

  while (true) {
    if (p >= len || buf[p] !== 123) return null; // '{'
    p = skipWs(buf, p + 1, len);
    if (p >= len) return null;

    let hasInput = false;
    let inputStart = -1;
    let inputEnd = -1;
    let textStart = -1;
    let textEnd = -1;
    let hasText = false;
    let header = false;
    let directOk = false;

    if (buf[p] === 125) { // empty case object
      return null;
    }

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
        if (buf[p] !== 123) return null; // input must be object
        hasInput = true;
        inputStart = p;
        hasText = false;
        textStart = -1;
        textEnd = -1;
        header = false;
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
                const te = findObjStringEnd(buf, ts, len);
                if (te === -1) return null;
                textStart = ts;
                textEnd = te;
                hasText = true;
                p = te + 1;
              } else {
                // Non-string text (e.g. number/null): skip and use JSON.parse + run() fallback for this case
                directOk = false;
                p = skipJsonValue(buf, p, len, true);
                if (p === -1) return null;
              }
            } else if (matchKey(buf, iks, ike, 'header')) {
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
  // Full safety-net fallback for any exotic/unexpected envelope format
  const cases = JSON.parse(rawBuf.toString('utf8'));
  if (cases.length === 0) {
    writeSync(fd, '[]');
  } else {
    const writer = createWriter(fd);
    writer.buf[writer.pos++] = 91; // '['
    for (let i = 0; i < cases.length; i++) {
      if (i > 0) {
        writer.ensure(1);
        writer.buf[writer.pos++] = 44;
      }
      const inp = cases[i].input;
      cases[i] = null;
      writeResultFallback(writer, run(inp));
      writer.flushIfReady();
    }
    writer.ensure(1);
    writer.buf[writer.pos++] = 93; // ']'
    writer.flushAll();
  }
} else if (parsed.length === 0) {
  writeSync(fd, '[]');
} else {
  const writer = createWriter(fd);
  const canStream = typeof solveCaseBuffer === 'function';
  // Single pass across rawBuf to check if ANY '\u' exists in the entire file (saves ~16ms vs per-case scans to EOF).
  let nextU = canStream ? rawBuf.indexOf(BS_U) : 0;

  for (let i = 0; i < parsed.length; i++) {
    const c = parsed[i];
    writer.ensure(1);
    writer.buf[writer.pos++] = i === 0 ? 91 : 44; // '[' or ','

    let useDirect = canStream && c.directOk;
    if (useDirect && nextU !== -1) {
      if (nextU < c.textStart) nextU = rawBuf.indexOf(BS_U, c.textStart);
      if (nextU !== -1 && nextU < c.textEnd) useDirect = false;
    }

    if (useDirect) {
      solveCaseBuffer(rawBuf, c.textStart, c.textEnd, c.header, writer);
    } else {
      const inp = JSON.parse(rawBuf.subarray(c.inputStart, c.inputEnd).toString('utf8'));
      writeResultFallback(writer, run(inp));
    }
    writer.flushIfReady();
  }

  writer.ensure(1);
  writer.buf[writer.pos++] = 93; // ']'
  writer.flushAll();
}

closeSync(fd);
