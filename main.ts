import { setFlagsFromString } from 'node:v8';

setFlagsFromString(
  '--no-incremental-marking --no-parallel-scavenge --no-minor-gc-task --no-use-osr --no-lazy-feedback-allocation',
);

await import('./driver.js');
