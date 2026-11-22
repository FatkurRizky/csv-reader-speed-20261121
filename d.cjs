'use strict';

require('node:v8').setFlagsFromString(
  '--no-incremental-marking --no-parallel-scavenge --no-minor-gc-task --no-use-osr --no-lazy-feedback-allocation --no-turbo-inlining',
);

const { closeSync, openSync, readFileSync, readSync, writeSync } = require('node:fs');
const { primeEngine, transduceText, finishCase } = require('./s.cjs');

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const IN_PATH = `${INPUT_DIR}/cases.json`;
const OUT_PATH = `${OUTPUT_DIR}/answers.json`;

const IN_WIN = 524288;      // 512 KiB L2-hot sliding input window (~131 PF)
const IN_PAD = 1024;        // tail slack for cross-window token carry + SWAR over-read
const OUT_INIT = 1048576;   // 1 MiB output buffer (only ~512 KiB touched = ~131 PF)
const FLUSH_THRESH = 524288;// 512 KiB L2-hot output flush threshold
const WAIT_MS = 40;         // zero-CPU barrier so background TurboFan finishes before Case 0

// Single monomorphic state object shared with s.cjs (primeEngine, transduceText, finishCase).
const inBuf = Buffer.allocUnsafeSlow(IN_WIN + IN_PAD);
const outBuf = Buffer.allocUnsafeSlow(OUT_INIT);

const st = {
  inFd: -1,
  inBuf,
  in32: new Int32Array(inBuf.buffer, inBuf.byteOffset, inBuf.byteLength >>> 2),
  dvIn: new DataView(inBuf.buffer, inBuf.byteOffset, inBuf.byteLength),
  p: 0,
  inEnd: 0,
  eof: true,
  windowId: 0,
  refill() {
    if (this.inFd < 0) {
      this.eof = true;
      return;
    }
    const rem = this.inEnd - this.p;
    if (rem > 0 && this.p > 0) {
      this.inBuf.copyWithin(0, this.p, this.inEnd);
    }
    this.p = 0;
    let end = rem;
    const maxEnd = this.inBuf.length - 16;
    const target = rem + IN_WIN < maxEnd ? rem + IN_WIN : maxEnd;
    while (end < target) {
      const n = readSync(this.inFd, this.inBuf, end, target - end, null);
      if (n === 0) {
        this.eof = true;
        break;
      }
      end += n;
      if (end >= 64) break;
    }
    this.inEnd = end;
    this.windowId++;
  },

  outFd: -1,
  outBuf,
  dvOut: new DataView(outBuf.buffer, outBuf.byteOffset, outBuf.byteLength),
  o: 0,
  outFilePos: 0,
  flushThresh: 0x7fffffff,
  ensureOut(need) {
    const req = this.o + need;
    if (req <= this.outBuf.length) return;
    let nc = this.outBuf.length * 2;
    while (nc < req) nc *= 2;
    const nb = Buffer.allocUnsafeSlow(nc);
    if (this.o > 0) this.outBuf.copy(nb, 0, 0, this.o);
    this.outBuf = nb;
    this.dvOut = new DataView(nb.buffer, nb.byteOffset, nb.byteLength);
  },
  flushOut() {
    if (this.outFd >= 0 && this.o > 0) {
      writeSync(this.outFd, this.outBuf, 0, this.o, this.outFilePos);
      this.outFilePos += this.o;
      this.o = 0;
    }
  },
  patchAt(filePos, srcBuf, len) {
    if (filePos >= this.outFilePos) {
      srcBuf.copy(this.outBuf, filePos - this.outFilePos, 0, len);
    } else if (this.outFd >= 0 && len > 0) {
      writeSync(this.outFd, srcBuf, 0, len, filePos);
    }
  },
  pwrite(buf, len, filePos) {
    if (this.outFd >= 0 && len > 0) {
      writeSync(this.outFd, buf, 0, len, filePos);
    }
  },
};

// Prime TurboFan on the exact monomorphic `st` shape, then sleep 0-CPU while TF finishes compiling.
primeEngine(st);
if (WAIT_MS > 0) {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, WAIT_MS);
}

// --- Streaming RFC 8259 JSON Envelope Helpers (zero readFileSync, zero full-file scan) ---

function ensureIn(s, n) {
  if (s.inEnd - s.p < n && !s.eof) s.refill();
  return s.inEnd - s.p >= n;
}

function peekByte(s) {
  if (s.p >= s.inEnd) {
    if (s.eof) return -1;
    s.refill();
    if (s.p >= s.inEnd) return -1;
  }
  return s.inBuf[s.p];
}

function skipWs(s) {
  for (;;) {
    const buf = s.inBuf;
    let p = s.p;
    const end = s.inEnd;
    while (p < end) {
      const b = buf[p];
      if (b !== 32 && b !== 10 && b !== 13 && b !== 9) {
        s.p = p;
        return b;
      }
      p++;
    }
    s.p = p;
    if (s.eof) return -1;
    s.refill();
    if (s.p >= s.inEnd) return -1;
  }
}

// Read a short unescaped ASCII JSON key `"..."`; returns key string or null (escaped/exotic -> fallback).
function readKey(s) {
  if (peekByte(s) !== 34) return null;
  s.p++;
  if (!ensureIn(s, 32) && s.p >= s.inEnd) return null;
  const buf = s.inBuf;
  const start = s.p;
  let p = start;
  const lim = start + 32 < s.inEnd ? start + 32 : s.inEnd;
  while (p < lim) {
    const b = buf[p];
    if (b === 34) {
      const k = buf.toString('latin1', start, p);
      s.p = p + 1;
      return k;
    }
    if (b === 92 || b < 32 || b >= 128) return null;
    p++;
  }
  return null;
}

function skipJsonString(s) {
  // Entry: s.p is at opening '"'
  s.p++;
  for (;;) {
    const buf = s.inBuf;
    let p = s.p;
    const end = s.inEnd;
    while (p < end) {
      const b = buf[p];
      if (b === 34) {
        s.p = p + 1;
        return true;
      }
      if (b === 92) {
        if (p + 1 >= end) {
          s.p = p;
          if (s.eof) return false;
          s.refill();
          break;
        }
        p += 2;
        continue;
      }
      p++;
    }
    if (p >= end) {
      s.p = p;
      if (s.eof) return false;
      s.refill();
      if (s.p >= s.inEnd) return false;
    }
  }
}

function skipJsonValue(s) {
  const b = skipWs(s);
  if (b === -1) return false;
  if (b === 34) return skipJsonString(s);
  if (b === 123) { // '{'
    s.p++;
    const next = skipWs(s);
    if (next === 125) { s.p++; return true; }
    for (;;) {
      if (peekByte(s) !== 34) return false;
      if (!skipJsonString(s)) return false;
      if (skipWs(s) !== 58) return false;
      s.p++;
      if (!skipJsonValue(s)) return false;
      const sep = skipWs(s);
      if (sep === 125) { s.p++; return true; }
      if (sep !== 44) return false;
      s.p++;
      skipWs(s);
    }
  }
  if (b === 91) { // '['
    s.p++;
    const next = skipWs(s);
    if (next === 93) { s.p++; return true; }
    for (;;) {
      if (!skipJsonValue(s)) return false;
      const sep = skipWs(s);
      if (sep === 93) { s.p++; return true; }
      if (sep !== 44) return false;
      s.p++;
    }
  }
  if (b === 116) { // true
    if (!ensureIn(s, 4)) return false;
    const buf = s.inBuf;
    const p = s.p;
    if (buf[p + 1] === 114 && buf[p + 2] === 117 && buf[p + 3] === 101) {
      s.p = p + 4;
      return true;
    }
    return false;
  }
  if (b === 102) { // false
    if (!ensureIn(s, 5)) return false;
    const buf = s.inBuf;
    const p = s.p;
    if (buf[p + 1] === 97 && buf[p + 2] === 108 && buf[p + 3] === 115 && buf[p + 4] === 101) {
      s.p = p + 5;
      return true;
    }
    return false;
  }
  if (b === 110) { // null
    if (!ensureIn(s, 4)) return false;
    const buf = s.inBuf;
    const p = s.p;
    if (buf[p + 1] === 117 && buf[p + 2] === 108 && buf[p + 3] === 108) {
      s.p = p + 4;
      return true;
    }
    return false;
  }
  if (b === 45 || (b >= 48 && b <= 57)) { // number
    s.p++;
    for (;;) {
      const buf = s.inBuf;
      let p = s.p;
      const end = s.inEnd;
      while (p < end) {
        const c = buf[p];
        if ((c >= 48 && c <= 57) || c === 46 || c === 101 || c === 69 || c === 43 || c === 45) {
          p++;
        } else {
          s.p = p;
          return true;
        }
      }
      s.p = p;
      if (s.eof) return true;
      s.refill();
    }
  }
  return false;
}

// --- 100% Exact Lazy Synchronous Fallback (loaded ONLY on \uXXXX, cross-window unterminated, or exotic envelope) ---

function runExactFallback() {
  if (st.inFd >= 0) { closeSync(st.inFd); st.inFd = -1; }
  if (st.outFd >= 0) { closeSync(st.outFd); st.outFd = -1; }

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
  st.inFd = openSync(IN_PATH, 'r');
  st.outFd = openSync(OUT_PATH, 'w');
  st.p = 0;
  st.inEnd = 0;
  st.eof = false;
  st.windowId = 0;
  st.o = 0;
  st.outFilePos = 0;
  st.flushThresh = FLUSH_THRESH;

  st.refill();

  // Strip optional UTF-8 BOM on cases.json itself
  if (ensureIn(st, 3) && st.inBuf[st.p] === 0xef && st.inBuf[st.p + 1] === 0xbb && st.inBuf[st.p + 2] === 0xbf) {
    st.p += 3;
  }

  if (skipWs(st) !== 91) return false; // '['
  st.p++;

  const firstB = skipWs(st);
  if (firstB === 93) { // empty '[]'
    st.p++;
    if (skipWs(st) !== -1) return false;
    st.outBuf[0] = 91;
    st.outBuf[1] = 93;
    st.o = 2;
    st.flushOut();
    return true;
  }

  let caseIdx = 0;
  for (;;) {
    if (skipWs(st) !== 123) return false; // '{'
    st.p++;
    if (skipWs(st) === 125) return false; // empty case object

    st.ensureOut(1);
    st.outBuf[st.o++] = caseIdx === 0 ? 91 : 44; // '[' or ','

    let seenInput = false;
    for (;;) {
      const key = readKey(st);
      if (key === null) return false;
      if (skipWs(st) !== 58) return false; // ':'
      st.p++;

      if (key === 'input') {
        if (seenInput) return false;
        seenInput = true;
        if (skipWs(st) !== 123) return false; // '{'
        st.p++;
        if (skipWs(st) === 125) return false; // empty input object

        let seenText = false;
        let headerVal = false;
        for (;;) {
          const ikey = readKey(st);
          if (ikey === null) return false;
          if (skipWs(st) !== 58) return false; // ':'
          st.p++;

          if (ikey === 'text') {
            if (seenText) return false;
            if (skipWs(st) !== 34) return false; // non-string text -> fallback
            st.p++; // position right after opening '"'
            if (st.inEnd - st.p < 64 && !st.eof) st.refill();
            const ok = transduceText(st);
            if (ok !== 1) return false; // \uXXXX or cross-window unterminated -> fallback
            seenText = true;
          } else if (ikey === 'header') {
            const hb = skipWs(st);
            if (hb === 116) { // true
              if (!ensureIn(st, 4)) return false;
              const buf = st.inBuf;
              const p = st.p;
              if (buf[p + 1] === 114 && buf[p + 2] === 117 && buf[p + 3] === 101) {
                headerVal = true;
                st.p = p + 4;
              } else {
                return false;
              }
            } else if (hb === 102) { // false
              if (!ensureIn(st, 5)) return false;
              const buf = st.inBuf;
              const p = st.p;
              if (buf[p + 1] === 97 && buf[p + 2] === 108 && buf[p + 3] === 115 && buf[p + 4] === 101) {
                headerVal = false;
                st.p = p + 5;
              } else {
                return false;
              }
            } else {
              headerVal = false;
              if (!skipJsonValue(st)) return false;
            }
          } else {
            if (!skipJsonValue(st)) return false;
          }

          const isep = skipWs(st);
          if (isep === 125) { // '}'
            st.p++;
            break;
          }
          if (isep !== 44) return false; // ','
          st.p++;
          skipWs(st);
        }

        if (!seenText) return false;
        finishCase(st, headerVal);
      } else {
        if (!skipJsonValue(st)) return false;
      }

      const sep = skipWs(st);
      if (sep === 125) { // '}'
        st.p++;
        break;
      }
      if (sep !== 44) return false;
      st.p++;
      skipWs(st);
    }

    if (!seenInput) return false;
    caseIdx++;

    const asep = skipWs(st);
    if (asep === 93) { // ']'
      st.p++;
      if (skipWs(st) !== -1) return false;
      st.ensureOut(1);
      st.outBuf[st.o++] = 93;
      st.flushOut();
      return true;
    }
    if (asep !== 44) return false;
    st.p++;
  }
}

if (runStream()) {
  closeSync(st.inFd);
  closeSync(st.outFd);
  st.inFd = -1;
  st.outFd = -1;
} else {
  runExactFallback();
}
