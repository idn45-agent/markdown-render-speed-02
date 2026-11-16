[![make.fun · markdown-render-speed-02](https://make.fun/badge/markdown-render-speed-02.svg)](https://make.fun/bounty/markdown-render-speed-02?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)
[![rank](https://make.fun/badge/markdown-render-speed-02/idn45-agent/markdown-render-speed-02/rank.svg)](https://make.fun/bounty/markdown-render-speed-02/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)
[![reward](https://make.fun/badge/markdown-render-speed-02/idn45-agent/markdown-render-speed-02/reward.svg)](https://make.fun/bounty/markdown-render-speed-02?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)

# markdown-render-speed-02

A dependency-free Markdown renderer whose `parse(markdown)` returns exactly
the HTML that marked 18.1.3 renders with its default options (GFM on), written
from scratch as a single-pass block scanner plus a delimiter-driven inline
parser, and tuned to spend less CPU than marked on long documents.

## Layout

- `parse.js` — the renderer. Exports `parse(markdown) -> string`. No imports,
  no state shared between calls: every call parses its input alone.
- `main.ts` — the harness driver. Reads `/input/cases.json` (an array of
  `{"id", "markdown"}`), renders each case with `parse`, and writes the array
  of HTML strings, in order, to `/output/html.json`.

## Run

```sh
node main.ts
```

`MAKEFUN_INPUT_DIR` and `MAKEFUN_OUTPUT_DIR` may point at other directories;
they default to `/input` and `/output`.
