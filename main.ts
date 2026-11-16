// Driver for markdown-render-speed-02: renders every case in
// /input/cases.json with parse() from ./parse.js and writes the HTML strings,
// in the cases' order, to /output/html.json. Plain JavaScript in a .ts file
// (Node's type stripping accepts it as-is); MAKEFUN_INPUT_DIR and
// MAKEFUN_OUTPUT_DIR stand in for /input and /output outside the harness.

import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8'));
const html = new Array(cases.length);
for (let i = 0; i < cases.length; i++) {
  html[i] = parse(cases[i].markdown);
}
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
