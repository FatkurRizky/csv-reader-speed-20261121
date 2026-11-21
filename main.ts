import { closeSync, openSync, readFileSync, writeSync } from 'node:fs';
import { setFlagsFromString } from 'node:v8';

setFlagsFromString(
  '--no-incremental-marking --no-concurrent-marking --no-concurrent-sweeping --single-threaded-gc --max-semi-space-size=64 --no-turbofan --no-concurrent-recompilation',
);

const { run } = (await import('./solve.js')) as {
  run: (input: unknown) => unknown;
};

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(`${INPUT_DIR}/cases.json`, 'utf8')) as {
  id: string;
  input: unknown;
}[];

const fd = openSync(`${OUTPUT_DIR}/answers.json`, 'w');
if (cases.length === 0) {
  writeSync(fd, '[]');
} else {
  let outBuf = Buffer.allocUnsafe(8 * 1024 * 1024);
  for (let i = 0; i < cases.length; i++) {
    const inp = cases[i].input;
    cases[i] = null as unknown as { id: string; input: unknown };
    const s = JSON.stringify(run(inp));
    const need = s.length * 3 + 4;
    if (need > outBuf.length) outBuf = Buffer.allocUnsafe(need);
    outBuf[0] = i === 0 ? 91 : 44; // '[' or ','
    let n = 1 + outBuf.write(s, 1, 'utf8');
    if (i === cases.length - 1) outBuf[n++] = 93; // ']'
    writeSync(fd, outBuf, 0, n);
  }
}
closeSync(fd);
