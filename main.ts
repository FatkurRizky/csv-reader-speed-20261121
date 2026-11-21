import { closeSync, openSync, readFileSync, writeSync } from 'node:fs';
import { setFlagsFromString } from 'node:v8';

// Safe V8 flag matching house baseline (never use --single-threaded-gc via setFlagsFromString:
// crashes V8 CppHeap with exit 133 on Major GC; keep TurboFan enabled).
setFlagsFromString('--no-incremental-marking');

interface CsvResult {
  columns: string[] | null;
  rows: string[][];
  errors: unknown[];
}

const { run } = (await import('./solve.js')) as {
  run: (input: unknown) => CsvResult;
};

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Reading raw Buffer + .toString('utf8') avoids Node's chunked utf8 readFileSync overhead (~10-15ms faster).
const cases = JSON.parse(
  readFileSync(`${INPUT_DIR}/cases.json`).toString('utf8'),
) as { id: string; input: unknown }[];

// Chunked zero-slice UTF-8 Buffer JSON writer:
// Uses V8's C++ SIMD FastJsonStringifier on 128-row L2-hot chunks (~25KB) instead of giant 4MB
// LargeObjectSpace strings, writes UTF-8 directly into a reusable 512KB buffer (16x fewer page faults
// than 8MB), and handles all RFC 8259 edge cases (controls, UTF-8, emoji, lone surrogates, errors)
// byte-for-byte identically to JSON.stringify(answers).
const CHUNK = 128;
let outBuf = Buffer.allocUnsafe(512 * 1024);
let pos = 0;
const fd = openSync(`${OUTPUT_DIR}/answers.json`, 'w');

function flush(): void {
  if (pos > 0) {
    writeSync(fd, outBuf, 0, pos);
    pos = 0;
  }
}

function ensure(need: number): void {
  if (pos + need > outBuf.length) {
    flush();
    if (need > outBuf.length) outBuf = Buffer.allocUnsafe(need);
  }
}

function emitAscii(s: string): void {
  const len = s.length;
  ensure(len);
  outBuf.write(s, pos, len, 'latin1');
  pos += len;
}

function emitUtf8(s: string): void {
  ensure(s.length * 3 + 4);
  pos += outBuf.write(s, pos, 'utf8');
}

function writeCase(r: CsvResult, scratch: string[][], isFirst: boolean): void {
  if (!isFirst) {
    ensure(2);
    outBuf[pos++] = 44; // ','
  }
  if (r.columns === null) {
    emitAscii('{"columns":null,"rows":');
  } else {
    emitAscii('{"columns":');
    emitUtf8(JSON.stringify(r.columns));
    emitAscii(',"rows":');
  }
  const rows = r.rows;
  const rlen = rows.length;
  if (rlen === 0) {
    emitAscii('[]');
  } else {
    for (let k = 0; k < rlen; k += CHUNK) {
      let s: string;
      if (k + CHUNK <= rlen) {
        for (let m = 0; m < CHUNK; m++) scratch[m] = rows[k + m];
        s = JSON.stringify(scratch);
      } else {
        s = JSON.stringify(rows.slice(k, rlen));
      }
      ensure(s.length * 3 + 4);
      const n = outBuf.write(s, pos, 'utf8');
      if (k > 0) outBuf[pos] = 44; // overwrite leading '[' with ','
      pos += n - 1; // drop trailing ']'
    }
    ensure(2);
    outBuf[pos++] = 93; // ']'
  }
  emitAscii(',"errors":');
  if (r.errors.length === 0) {
    emitAscii('[]}');
  } else {
    emitUtf8(JSON.stringify(r.errors));
    ensure(2);
    outBuf[pos++] = 125; // '}'
  }
}

if (cases.length === 0) {
  writeSync(fd, '[]');
} else {
  const scratch: string[][] = new Array(CHUNK);
  outBuf[pos++] = 91; // '['
  for (let i = 0; i < cases.length; i++) {
    const inp = cases[i].input;
    cases[i] = null as unknown as { id: string; input: unknown };
    writeCase(run(inp), scratch, i === 0);
  }
  scratch.fill(undefined as unknown as string[]);
  ensure(2);
  outBuf[pos++] = 93; // ']'
  flush();
}
closeSync(fd);
