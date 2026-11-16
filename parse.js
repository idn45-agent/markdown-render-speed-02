// parse.js — a from-scratch Markdown renderer that returns, for every input,
// exactly the HTML marked 18.1.3 returns with its default options (GFM on),
// while spending less CPU than marked on long documents.
//
// Shape: a line-oriented block scanner (one pass, no whole-document regexes)
// producing a small token tree, then a renderer whose inline stage is a
// hand-written scanner with a delimiter stack for emphasis. No state is kept
// between calls: every parse() starts from a fresh link-definition table
// filled by that call's own block pass.

// ---------------------------------------------------------------- helpers

const ESCAPES = {
  '&': '&amp;',
  '<': '&lt;',
  '>': '&gt;',
  '"': '&quot;',
  "'": '&#39;',
};

// Escape for element content the way marked escapes plain text: the five
// markup characters, except that an "&" which already begins an entity
// reference (&#123; &#x1F; &name;) is left alone.
const TEXT_ESCAPE_RE = /[<>"']|&(?!(?:#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
function escapeText(s) {
  return s.replace(TEXT_ESCAPE_RE, (c) => ESCAPES[c]);
}

// Escape with every "&" escaped (code content, attribute values).
const FULL_ESCAPE_RE = /[&<>"']/g;
function escapeFull(s) {
  return s.replace(FULL_ESCAPE_RE, (c) => ESCAPES[c]);
}

const ASCII_PUNCT = new Set('!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~'.split(''));

// Column width of the leading whitespace of a line, with tab stops of 4.
function leadingCols(line) {
  let col = 0;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (c === ' ') col += 1;
    else if (c === '\t') col += 4 - (col % 4);
    else break;
  }
  return col;
}

// Remove up to n columns of leading whitespace from a line. A tab that
// straddles the cut leaves its remaining width as spaces. Returns the rest
// of the line (the whole line when it has fewer than n columns and is not
// all whitespace: then the columns actually present are removed only when
// the line is blank).
function stripCols(line, n) {
  let col = 0;
  let i = 0;
  while (i < line.length && col < n) {
    const c = line[i];
    if (c === ' ') {
      col += 1;
      i += 1;
    } else if (c === '\t') {
      const w = 4 - (col % 4);
      if (col + w <= n) {
        col += w;
        i += 1;
      } else {
        // partially consumed tab: remainder becomes spaces
        return ' '.repeat(col + w - n) + line.slice(i + 1);
      }
    } else {
      break;
    }
  }
  return line.slice(i);
}

// Remove one leading "tab unit" (whitespace reaching exactly the first
// tab stop, column 4) from a line; if the leading whitespace run does not
// reach column 4 the line is returned unchanged. Used for the first lazy
// line of a blockquote paragraph.
function stripTabUnit(line) {
  let col = 0;
  let i = 0;
  while (i < line.length && col < 4) {
    const c = line[i];
    if (c === ' ') { col += 1; i += 1; continue; }
    if (c === '\t') { col += 4 - (col % 4); i += 1; continue; }
    return line;
  }
  if (col < 4) return line;
  return line.slice(i);
}

function isBlank(line) {
  return /^[ \t]*$/.test(line);
}

// Strip the first `fromCol` columns of a line the way marked's container
// stripping (list items, blockquote markers) behaves: characters before the
// cut are dropped, a tab straddling the cut leaves its remaining width as
// spaces, and any tab inside the leading whitespace beyond the cut is
// expanded to the spaces its original column span covers. The rest of the
// line, from its first non-whitespace character on, is copied raw.
function stripContainer(line, fromCol) {
  let col = 0;
  let out = '';
  let i = 0;
  let leading = true;
  while (i < line.length) {
    const c = line[i];
    if (c === ' ' || c === '\t') {
      const w = c === ' ' ? 1 : 4 - (col % 4);
      if (col + w <= fromCol) {
        // entirely before the cut: contributes nothing
      } else if (col >= fromCol) {
        out += ' '.repeat(w);
      } else {
        out += ' '.repeat(col + w - fromCol);
      }
      col += w;
      i += 1;
      continue;
    }
    if (leading) {
      if (col < fromCol) {
        // a non-whitespace character before the cut (a container marker
        // such as ">" or "-"): it is dropped, whitespace phase continues
        col += 1;
        i += 1;
        continue;
      }
      leading = false;
    }
    out += line.slice(i);
    break;
  }
  return out;
}

// ------------------------------------------------------- link definitions

// The key marked looks a definition up by: whitespace runs collapse to one
// space, the label is trimmed and lower-cased.
function defKey(label) {
  return label.replace(/\s+/g, ' ').trim().toLowerCase();
}

// Try to read a link reference definition starting at lines[i]. On success
// returns {lines: consumedCount, label, href, title} and registers nothing;
// on failure returns null.
function scanDef(lines, i) {
  const first = lines[i];
  const m = /^ {0,3}\[((?:\\.|[^\]\\])*)\]:[ \t]*/.exec(first);
  if (!m) return null;
  const label = m[1];
  if (label.length > 999) return null;
  let rest = first.slice(m[0].length);
  let used = 1;
  // The destination may sit on the next line when this one ends after ":".
  if (rest === '') {
    if (i + 1 >= lines.length) return null;
    rest = lines[i + 1].replace(/^ {0,3}/, '');
    used = 2;
    if (rest === '') return null;
  }
  const dest = scanDest(rest, 0, true);
  if (!dest) return null;
  let tail = rest.slice(dest.end).replace(/^[ \t]+/, '');
  let title = null;
  if (tail === '' && used < 2 && i + 1 < lines.length) {
    // A title may sit alone on the following line.
    const nxt = lines[i + 1].replace(/^ {0,3}/, '');
    const t = scanTitle(nxt, 0);
    if (t && /^[ \t]*$/.test(nxt.slice(t.end))) {
      title = t.title;
      tail = '';
      used = 2;
    }
  }
  if (tail !== '') {
    const t = scanTitle(rest, dest.end + (rest.slice(dest.end).match(/^[ \t]*/)[0].length));
    if (!t) return null;
    title = t.title;
    if (!/^[ \t]*$/.test(rest.slice(t.end))) return null;
  }
  return { lines: used, label, href: dest.href, title };
}

// Scan a link destination at s[pos]: either <...> (no newline, backslash
// escapes allowed) or a bare run of non-space characters with balanced
// parentheses (one level of nesting may itself contain escaped parens).
// Returns {href, end} with end just past the destination.
function scanDest(s, pos, stopAtSpace) {
  if (s[pos] === '<') {
    let j = pos + 1;
    let out = '';
    while (j < s.length) {
      const c = s[j];
      if (c === '\\' && j + 1 < s.length && ASCII_PUNCT.has(s[j + 1])) {
        out += s[j + 1];
        j += 2;
        continue;
      }
      if (c === '>') return { href: out, end: j + 1 };
      if (c === '<' || c === '\n') return null;
      out += c;
      j += 1;
    }
    return null;
  }
  let j = pos;
  let depth = 0;
  let out = '';
  while (j < s.length) {
    const c = s[j];
    if (c === '\\' && j + 1 < s.length && ASCII_PUNCT.has(s[j + 1])) {
      out += s[j + 1];
      j += 2;
      continue;
    }
    if (stopAtSpace && (c === ' ' || c === '\t' || c === '\n')) break;
    if (c === '(') depth += 1;
    else if (c === ')') {
      if (depth === 0) break;
      depth -= 1;
    }
    if (c < ' ') return null;
    out += c;
    j += 1;
  }
  if (j === pos || depth !== 0) return null;
  return { href: out, end: j };
}

function unescapePunct(s) {
  return s.replace(/\\([!"#$%&'()*+,\-./:;<=>?@[\\\]^_`{|}~])/g, '$1');
}

// Scan a link title at s[pos]: "..." or '...' or (...). Returns
// {title, end} or null. Titles may not contain their delimiter unescaped;
// the parenthesised form may not contain an unescaped "(" either.
function scanTitle(s, pos) {
  const open = s[pos];
  if (open !== '"' && open !== "'" && open !== '(') return null;
  const close = open === '(' ? ')' : open;
  let j = pos + 1;
  let out = '';
  while (j < s.length) {
    const c = s[j];
    if (c === '\\' && j + 1 < s.length && ASCII_PUNCT.has(s[j + 1])) {
      out += s[j + 1];
      j += 2;
      continue;
    }
    if (c === close) return { title: out, end: j + 1 };
    if (open === '(' && c === '(') return null;
    if (c === '\n') return null;
    out += c;
    j += 1;
  }
  return null;
}

// ---------------------------------------------------------------- blocks
//
// lexBlocks(lines, ctx) turns an array of source lines into block tokens:
//   { t: 'code', text }            indented code, text ends with "\n"
//   { t: 'fence', lang, text }     fenced code, text ends with "\n" if any
//   { t: 'heading', depth, text }  ATX or setext heading (raw inline text)
//   { t: 'hr' }
//   { t: 'html', text }            raw HTML block, text without trailing \n
//   { t: 'quote', children }       blockquote
//   { t: 'list', ordered, start, loose, items }  items: token arrays
//   { t: 'table', header, align, rows }          raw cell texts
//   { t: 'para', text }            paragraph (raw inline text)
// ctx: { defs: Map, top: boolean }

const FENCE_RE = /^ {0,3}(`{3,}|~{3,})(.*)$/;
const ATX_RE = /^ {0,3}(#{1,6})(?:[ \t]+(.*?)[ \t]*$|[ \t]*$)/;
const HR_RE = /^ {0,3}([-*_])(?:[ \t]*\1){2,}[ \t]*$/;
const QUOTE_RE = /^ {0,3}>[ \t]?/;
const SETEXT_RE = /^ {0,3}(=+|-+)[ \t]*$/;

function matchListStart(line) {
  const m = /^ {0,3}(?:([-+*])|(\d{1,9})([.)]))([ \t]+|$)/.exec(line);
  if (!m) return null;
  const bullet = m[1] || null;
  const num = m[2] !== undefined ? parseInt(m[2], 10) : null;
  const delim = bullet || m[3];
  // column where the marker ends
  const leadSpaces = /^ */.exec(line)[0].length;
  const markerLen = bullet ? 1 : m[2].length + 1;
  const after = line.slice(leadSpaces + markerLen);
  const spaces = /^[ \t]*/.exec(after)[0];
  let spaceCols = 0;
  for (const c of spaces) spaceCols += c === '\t' ? 4 - ((leadSpaces + markerLen + spaceCols) % 4) : 1;
  const contentEmpty = after.trim() === '';
  // content indent: marker + following run when it is 1..4 columns, else +1
  const contentIndent = leadSpaces + markerLen + (spaceCols >= 1 && spaceCols <= 4 && !contentEmpty ? spaceCols : 1);
  return {
    bullet,
    num,
    delim,
    ordered: !bullet,
    markerEnd: leadSpaces + markerLen,
    contentIndent,
    rest: contentEmpty ? '' : stripContainer(line, contentIndent),
    empty: contentEmpty,
  };
}

// The block-level HTML start conditions (CommonMark types 1-6 plus a
// complete tag of any name, type 7), as marked applies them. Returns
// { kind } where kind is 'raw' (script/pre/style/textarea), 'comment',
// 'pi', 'decl', 'cdata', 'block' or 'tag', or null.
const BLOCK_TAGS = new Set(('address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol optgroup option p param section source summary table tbody td tfoot th thead title tr track ul').split(' '));

function htmlBlockStart(line) {
  const m = /^ {0,3}<(\/?)([A-Za-z][A-Za-z0-9-]*)((?:[ \t]+[^ \t<>"'/=]+(?:[ \t]*=[ \t]*(?:[^ \t"'=<>`]+|'[^']*'|"[^"]*"))?)*)[ \t]*(\/?)>/.exec(line);
  const stripped = line.replace(/^ {0,3}/, '');
  if (stripped.startsWith('<!--')) return { kind: 'comment' };
  if (stripped.startsWith('<?')) return { kind: 'pi' };
  if (/^<![A-Z]/.test(stripped)) return { kind: 'decl' };
  if (stripped.startsWith('<![CDATA[')) return { kind: 'cdata' };
  const rawM = /^ {0,3}<(script|pre|style|textarea)(?=[ \t>]|\/>|$)/i.exec(line);
  if (rawM) return { kind: 'raw', tag: rawM[1].toLowerCase() };
  if (m) {
    const name = m[2].toLowerCase();
    const after = line.slice(m[0].length);
    const boundary = after === '' || /^[ \t]/.test(after);
    if (BLOCK_TAGS.has(name) && boundary) return { kind: 'block' };
    if (boundary || m[5] === '/') return { kind: 'tag' };
  }
  return null;
}

// Split a table row line into trimmed cell texts. Pipes escaped as \| or
// inside a code span do not split. Leading/trailing edge pipes drop the
// empty cell they would make.
function splitRow(line) {
  const cells = [];
  let cur = '';
  let i = 0;
  let inCode = 0; // backtick run length currently open, 0 = none
  while (i < line.length) {
    const c = line[i];
    if (c === '\\' && line[i + 1] === '|') {
      cur += '\\|';
      i += 2;
      continue;
    }
    if (c === '`') {
      let run = 0;
      while (line[i] === '`') {
        run += 1;
        i += 1;
      }
      cur += '`'.repeat(run);
      if (inCode === 0) inCode = run;
      else if (inCode === run) inCode = 0;
      continue;
    }
    if (c === '|' && inCode === 0) {
      cells.push(cur);
      cur = '';
      i += 1;
      continue;
    }
    cur += c;
    i += 1;
  }
  cells.push(cur);
  const trimmed = cells.map((c) => c.trim());
  // drop edge empties made by a leading/trailing pipe
  const leadPipe = /^\s*\|/.test(line);
  const trailPipe = /\|\s*$/.test(line.replace(/\\\|/g, ''));
  if (leadPipe && trimmed.length && trimmed[0] === '') trimmed.shift();
  if (trailPipe && trimmed.length && trimmed[trimmed.length - 1] === '') trimmed.pop();
  return trimmed;
}

function parseDelimiterRow(line) {
  if (!line.includes('-')) return null;
  const cells = splitRow(line);
  if (cells.length === 0) return null;
  const align = [];
  for (const cell of cells) {
    const m = /^(:?)-+(:?)$/.exec(cell.replace(/ /g, ''));
    if (!m) return null;
    align.push(m[1] && m[2] ? 'center' : m[2] ? 'right' : m[1] ? 'left' : null);
  }
  return align;
}

// Does lines[i] (a would-be header) plus lines[i+1] (delimiter) open a
// table? Returns the align array or null.
function tableStart(lines, i) {
  if (i + 1 >= lines.length) return null;
  const headerLine = lines[i];
  if (!headerLine.includes('|')) return null;
  const align = parseDelimiterRow(lines[i + 1]);
  if (!align) return null;
  const header = splitRow(headerLine.replace(/^ {0,3}/, ''));
  if (header.length !== align.length) return null;
  return { align, header };
}

// ------------------------------------------------------------- lex loop

function lexBlocks(lines, ctx, prot) {
  const tokens = [];
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    if (isBlank(line)) {
      i += 1;
      continue;
    }
    // fenced code
    const fm = FENCE_RE.exec(line);
    if (fm && (fm[1][0] === '~' || !fm[2].includes('`'))) {
      const ch = fm[1][0];
      const len = fm[1].length;
      const indent = line.indexOf(ch);
      const info = fm[2].trim();
      const body = [];
      let j = i + 1;
      let closed = false;
      while (j < n) {
        const cl = lines[j];
        const cm = /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(cl);
        if (cm && cm[1][0] === ch && cm[1].length >= len) {
          closed = true;
          break;
        }
        body.push(indent > 0 ? stripCols(cl, indent) : cl);
        j += 1;
      }
      tokens.push({ t: 'fence', lang: info === '' ? null : unescapePunct(info.split(/[ \t]+/)[0]), text: body.length ? body.join('\n') + '\n' : '' });
      i = closed ? j + 1 : j;
      continue;
    }
    // indented code
    if (leadingCols(line) >= 4) {
      const body = [];
      let j = i;
      let lastContent = -1;
      while (j < n) {
        const l = lines[j];
        if (isBlank(l)) {
          body.push(stripCols(l, 4));
          j += 1;
          continue;
        }
        if (leadingCols(l) >= 4) {
          body.push(stripCols(l, 4));
          lastContent = body.length - 1;
          j += 1;
          continue;
        }
        break;
      }
      body.length = lastContent + 1;
      tokens.push({ t: 'code', text: body.join('\n') + '\n' });
      i = j;
      continue;
    }
    // ATX heading
    const hm = ATX_RE.exec(line);
    if (hm) {
      let text = hm[2] === undefined ? '' : hm[2];
      if (/^#+$/.test(text)) text = '';
      else text = text.replace(/[ \t]#+$/, '').replace(/[ \t]+$/, '');
      tokens.push({ t: 'heading', depth: hm[1].length, text });
      i += 1;
      continue;
    }
    // thematic break
    if (HR_RE.test(line)) {
      tokens.push({ t: 'hr' });
      i += 1;
      continue;
    }
    // blockquote
    if (QUOTE_RE.test(line)) {
      const q = lexQuote(lines, i, ctx, prot);
      tokens.push(q.token);
      i = q.next;
      continue;
    }
    // list
    if (matchListStart(line)) {
      const l = lexList(lines, i, ctx, prot);
      tokens.push(l.token);
      i = l.next;
      continue;
    }
    // HTML block
    const hb = htmlBlockStart(line);
    if (hb) {
      const h = lexHtmlBlock(lines, i, hb);
      tokens.push(h.token);
      i = h.next;
      continue;
    }
    // link reference definition
    const def = scanDef(lines, i);
    if (def) {
      const key = defKey(def.label);
      if (!ctx.defs.has(key)) ctx.defs.set(key, { href: def.href, title: def.title });
      i += def.lines;
      continue;
    }
    // table
    const ts = tableStart(lines, i);
    if (ts) {
      const rows = [];
      let j = i + 2;
      while (j < n && !isBlank(lines[j]) && lines[j].includes('|')) {
        rows.push(splitRow(lines[j].replace(/^ {0,3}/, '')));
        j += 1;
      }
      tokens.push({ t: 'table', header: ts.header, align: ts.align, rows });
      i = j;
      continue;
    }
    // paragraph or setext heading
    const p = lexParagraph(lines, i, ctx, prot);
    tokens.push(p.token);
    i = p.next;
  }
  return tokens;
}

function lexHtmlBlock(lines, i, hb) {
  const body = [lines[i]];
  let j = i + 1;
  if (hb.kind === 'block' || hb.kind === 'tag') {
    while (j < lines.length && !isBlank(lines[j])) {
      body.push(lines[j]);
      j += 1;
    }
  } else {
    const closer =
      hb.kind === 'raw' ? new RegExp('</' + hb.tag, 'i')
      : hb.kind === 'comment' ? /-->/
      : hb.kind === 'pi' ? /\?>/
      : hb.kind === 'cdata' ? /\]\]>/
      : />/;
    if (!closer.test(lines[i])) {
      while (j < lines.length && !closer.test(lines[j])) {
        body.push(lines[j]);
        j += 1;
      }
      if (j < lines.length) {
        body.push(lines[j]);
        j += 1;
      }
    }
  }
  return { token: { t: 'html', text: body.join('\n') }, next: j };
}

// Collect a blockquote starting at lines[i]: marker lines are stripped,
// lazy paragraph-continuation lines follow marked's quirks (the first
// lazy line of a run loses one tab unit and can never act as a setext
// underline; a later lazy setext-shaped line is re-indented by 4 spaces),
// and a blank line without a marker ends the quote. `prot` holds indices
// of `lines` that an outer container already made setext-proof; the
// returned protection set for the inner lines is built the same way.
function lexQuote(lines, i, ctx, prot) {
  const inner = [];
  const innerProt = new Set();
  let j = i;
  let paraOpen = false;
  let lazyRun = 0;
  while (j < lines.length) {
    const line = lines[j];
    const qm = /^ {0,3}>/.exec(line);
    if (qm) {
      const g = qm[0].length - 1; // index of '>'
      let fromCol = g + 1;
      if (line[g + 1] === ' ' || line[g + 1] === '\t') fromCol += 1;
      const stripped = stripContainer(line, fromCol);
      if (prot && prot.has(j)) innerProt.add(inner.length);
      inner.push(stripped);
      paraOpen = quoteParaState(stripped, paraOpen);
      lazyRun = 0;
      j += 1;
      continue;
    }
    if (isBlank(line)) break;
    if (paraOpen && !startsInterruptingBlock(line, lines, j)) {
      let lazy;
      if (lazyRun === 0) {
        lazy = stripTabUnit(line);
        if (SETEXT_RE.test(lazy)) innerProt.add(inner.length);
      } else if (SETEXT_RE.test(line) && line[0] !== '\t') {
        lazy = '    ' + line.replace(/^ {0,3}/, '');
      } else {
        lazy = line;
      }
      if (prot && prot.has(j)) innerProt.add(inner.length);
      inner.push(lazy);
      lazyRun += 1;
      j += 1;
      continue;
    }
    break;
  }
  const children = lexBlocks(inner, { defs: ctx.defs, top: false }, innerProt);
  return { token: { t: 'quote', children }, next: j };
}

// Rough tracker: after adding `line` to a blockquote's inner lines, is a
// paragraph open at its end? (Used only to decide laziness.)
function quoteParaState(line, wasOpen) {
  return paraOpenAfter(line, wasOpen);
}

// Would `line` interrupt a paragraph? (Setext underlines do not count:
// they continue the paragraph by converting it.)
function startsInterruptingBlock(line, lines, j) {
  if (FENCE_RE.test(line)) return true;
  if (ATX_RE.test(line)) return true;
  if (HR_RE.test(line)) return true;
  if (QUOTE_RE.test(line)) return true;
  const ms = matchListStart(line);
  if (ms && !ms.empty && (!ms.ordered || ms.num === 1)) return true;
  const hb = htmlBlockStart(line);
  if (hb && hb.kind !== 'tag') return true;
  if (tableStart(lines, j)) return true;
  return false;
}

function lexParagraph(lines, i, ctx, prot) {
  const collected = [lines[i]];
  let j = i + 1;
  while (j < lines.length) {
    const line = lines[j];
    if (isBlank(line)) break;
    const sm = SETEXT_RE.exec(line);
    if (sm && !(prot && prot.has(j))) {
      return {
        token: { t: 'heading', depth: sm[1][0] === '=' ? 1 : 2, text: collected.join('\n').trim() },
        next: j + 1,
      };
    }
    if (startsInterruptingBlock(line, lines, j)) break;
    collected.push(line);
    j += 1;
  }
  return { token: { t: 'para', text: collected.join('\n') }, next: j };
}

// ---------------------------------------------------------------- lists

function sameListItem(a, b) {
  if (!a || !b) return false;
  if (a.ordered !== b.ordered) return false;
  return a.ordered ? a.delim === b.delim : a.bullet === b.bullet;
}

// State of an open paragraph after appending a content line: true when a
// paragraph is open at the end of the line. Used for container laziness
// and the extra 4-column strip on list-item paragraph continuations.
function paraOpenAfter(line, wasOpen) {
  if (isBlank(line)) return false;
  if (wasOpen) {
    if (SETEXT_RE.test(line)) return false;
    return !startsInterruptingBlock(line, [line], 0);
  }
  if (leadingCols(line) >= 4) return false;
  return !startsInterruptingBlock(line, [line], 0);
}

function lexList(lines, i, ctx, prot) {
  const first = matchListStart(lines[i]);
  const items = [];
  let loose = false;
  let j = i;
  let start = first.ordered ? first.num : null;
  while (j < lines.length) {
    const ms = matchListStart(lines[j]);
    if (!sameListItem(ms, first)) break;
    const ci = ms.contentIndent;
    const itemLines = [ms.rest];
    const itemSrc = [j];
    let itemParaOpen = ms.rest !== '' && paraOpenAfter(ms.rest, false);
    let itemLoose = false;
    let k = j + 1;
    let end = -1;
    while (k < lines.length) {
      const line = lines[k];
      if (isBlank(line)) {
        // look ahead: more item content, a sibling item, or the end
        let m = k + 1;
        while (m < lines.length && isBlank(lines[m])) m += 1;
        if (m >= lines.length) { end = m; break; }
        const nl = lines[m];
        if (leadingCols(nl) >= ci) {
          for (let b = k; b < m; b += 1) { itemLines.push(''); itemSrc.push(b); }
          itemParaOpen = false;
          itemLoose = true;
          k = m;
          continue;
        }
        const nm = matchListStart(nl);
        if (!HR_RE.test(nl) && sameListItem(nm, first)) {
          loose = true;
          end = m;
          break;
        }
        end = m;
        break;
      }
      if (leadingCols(line) >= ci) {
        let stripped = stripContainer(line, ci);
        if (itemParaOpen && leadingCols(stripped) >= 4 && !startsInterruptingBlock(stripped, [stripped], 0)) {
          stripped = stripCols(stripped, 4);
        }
        itemLines.push(stripped);
        itemSrc.push(k);
        itemParaOpen = paraOpenAfter(stripped, itemParaOpen);
        k += 1;
        continue;
      }
      const lm = matchListStart(line);
      if (!HR_RE.test(line) && sameListItem(lm, first)) { end = k; break; }
      if (itemParaOpen && !startsInterruptingBlock(line, lines, k)) {
        itemLines.push(line); // lazy continuation, verbatim
        itemSrc.push(k);
        k += 1;
        continue;
      }
      end = k;
      break;
    }
    if (end === -1) end = k;
    if (itemLoose) loose = true;
    let itemProt = null;
    if (prot) {
      itemProt = new Set();
      for (let x = 0; x < itemSrc.length; x += 1) {
        if (prot.has(itemSrc[x])) itemProt.add(x);
      }
      if (itemProt.size === 0) itemProt = null;
    }
    items.push(lexBlocks(itemLines, { defs: ctx.defs, top: false }, itemProt));
    j = end;
    // skip blank lines between items (already accounted via lookahead)
    if (j < lines.length && (HR_RE.test(lines[j]) || !sameListItem(matchListStart(lines[j]), first))) break;
  }
  return { token: { t: 'list', ordered: first.ordered, start, loose, items }, next: j };
}

// -------------------------------------------------------------- render

function renderTokens(tokens, ctx) {
  let out = '';
  for (const tok of tokens) out += renderToken(tok, ctx);
  return out;
}

function renderToken(tok, ctx) {
  switch (tok.t) {
    case 'code':
      return '<pre><code>' + escapeFull(tok.text) + '</code></pre>\n';
    case 'fence':
      return '<pre><code' + (tok.lang !== null ? ' class="language-' + escapeText(tok.lang) + '"' : '') + '>' + escapeFull(tok.text) + '</code></pre>\n';
    case 'heading':
      return '<h' + tok.depth + '>' + renderInline(tok.text, ctx, false) + '</h' + tok.depth + '>\n';
    case 'hr':
      return '<hr>\n';
    case 'html':
      return tok.text + '\n';
    case 'quote':
      return '<blockquote>\n' + renderTokens(tok.children, ctx) + '</blockquote>\n';
    case 'para':
      return '<p>' + renderInline(tok.text, ctx, false) + '</p>\n';
    case 'table': {
      let out = '<table>\n<thead>\n<tr>\n';
      for (let c = 0; c < tok.header.length; c += 1) {
        const a = tok.align[c];
        out += '<th' + (a ? ' align="' + a + '"' : '') + '>' + renderInline(tok.header[c], ctx, false) + '</th>\n';
      }
      out += '</tr>\n</thead>\n';
      if (tok.rows.length) {
        out += '<tbody>';
        for (const row of tok.rows) {
          out += '<tr>\n';
          for (let c = 0; c < tok.header.length; c += 1) {
            const a = tok.align[c];
            out += '<td' + (a ? ' align="' + a + '"' : '') + '>' + renderInline(row[c] === undefined ? '' : row[c], ctx, false) + '</td>\n';
          }
          out += '</tr>\n';
        }
        out += '</tbody>';
      }
      return out + '</table>\n';
    }
    case 'list': {
      let out = tok.ordered
        ? '<ol' + (tok.start !== null && tok.start !== 1 ? ' start="' + tok.start + '"' : '') + '>\n'
        : '<ul>\n';
      for (const item of tok.items) out += '<li>' + renderListItem(item, tok.loose, ctx) + '</li>\n';
      return out + (tok.ordered ? '</ol>\n' : '</ul>\n');
    }
    default:
      return '';
  }
}

function renderListItem(tokens, loose, ctx) {
  let prefix = '';
  let toks = tokens;
  if (toks.length && toks[0].t === 'para') {
    const m = /^\[([ xX])\][ \t]+/.exec(toks[0].text);
    if (m) {
      prefix = '<input ' + (m[1] !== ' ' ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
      toks = toks.slice();
      toks[0] = { t: 'para', text: toks[0].text.slice(m[0].length) };
    }
  }
  if (loose) {
    if (!prefix) return renderTokens(toks, ctx);
    let out = '';
    for (let idx = 0; idx < toks.length; idx += 1) {
      if (idx === 0) out += '<p>' + prefix + renderInline(toks[0].text, ctx, false) + '</p>\n';
      else out += renderToken(toks[idx], ctx);
    }
    return out;
  }
  let out = prefix;
  for (const tok of toks) {
    out += tok.t === 'para' ? renderInline(tok.text, ctx, false) : renderToken(tok, ctx);
  }
  return out;
}

// ---------------------------------------------------------------- main

export function parse(src) {
  const text = String(src).replace(/\r\n?/g, '\n');
  const lines = text.split('\n');
  // A trailing newline terminates the last line; it does not add a new
  // empty one (a phantom empty line would leak into fence/code content).
  if (lines.length && lines[lines.length - 1] === '') lines.pop();
  const ctx = { defs: new Map(), top: true };
  const tokens = lexBlocks(lines, ctx, null);
  return renderTokens(tokens, ctx);
}

// --------------------------------------------------------------- inline

const NUM_ENTITY_RE = /&#(\d{1,7});|&#[Xx]([0-9A-Fa-f]{1,6});/g;

function decodeNumericEntities(s) {
  if (!s.includes('&#')) return s;
  return s.replace(NUM_ENTITY_RE, (m, dec, hex) => {
    const cp = dec !== undefined ? parseInt(dec, 10) : parseInt(hex, 16);
    if (cp === 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) return '\uFFFD';
    return String.fromCodePoint(cp);
  });
}

// Text nodes: numeric character references are decoded to their character
// (invalid ones become U+FFFD), then the result is escaped, leaving other
// entity-shaped sequences (&name;, &#...;) untouched.
function escapeTextNode(s) {
  return escapeText(decodeNumericEntities(s));
}

function cleanUrl(href) {
  try {
    return encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
}

function hrefAttr(href) {
  const clean = cleanUrl(href);
  if (clean === null) return null;
  return escapeText(clean);
}

// Scan an inline HTML tag/comment/etc. at the start of s (s[0] === '<').
// Returns the raw matched string or null.
function scanInlineHtml(s) {
  if (s.startsWith('<!--')) {
    if (s.startsWith('<!-->') || s.startsWith('<!--->')) return null;
    const end = s.indexOf('-->', 4);
    if (end === -1) return null;
    return s.slice(0, end + 3);
  }
  if (s.startsWith('<![CDATA[')) {
    const end = s.indexOf(']]>', 9);
    if (end === -1) return null;
    return s.slice(0, end + 3);
  }
  if (s.startsWith('<?')) {
    const end = s.indexOf('?>', 2);
    if (end === -1) return null;
    return s.slice(0, end + 2);
  }
  let m = /^<![A-Z]+(?:[ \t][^>]*)?>/.exec(s);
  if (m) return m[0];
  m = /^<\/[A-Za-z][A-Za-z0-9-]*[ \t]*>/.exec(s);
  if (m) return m[0];
  m = /^<([A-Za-z][A-Za-z0-9-]*)/.exec(s);
  if (!m) return null;
  let p = m[0].length;
  for (;;) {
    let ws = 0;
    while (p < s.length && (s[p] === ' ' || s[p] === '\t' || s[p] === '\n')) { p += 1; ws += 1; }
    if (s[p] === '>') return s.slice(0, p + 1);
    if (s[p] === '/' && s[p + 1] === '>') return s.slice(0, p + 2);
    if (ws === 0) return null;
    const am = /^[A-Za-z_:][A-Za-z0-9_.:-]*/.exec(s.slice(p));
    if (!am) return null;
    p += am[0].length;
    let q = p;
    while (q < s.length && (s[q] === ' ' || s[q] === '\t' || s[q] === '\n')) q += 1;
    if (s[q] === '=') {
      q += 1;
      while (q < s.length && (s[q] === ' ' || s[q] === '\t' || s[q] === '\n')) q += 1;
      const qc = s[q];
      if (qc === '"' || qc === "'") {
        const end = s.indexOf(qc, q + 1);
        if (end === -1) return null;
        p = end + 1;
      } else {
        const vm = /^[^\s"'=<>`]+/.exec(s.slice(q));
        if (!vm) return null;
        p = q + vm[0].length;
      }
    }
  }
}

// Find the ']' closing a link label whose text starts at index `from`.
// Nesting and backslash escapes are honoured; code spans are skipped.
function findClosingBracket(s, from) {
  let depth = 1;
  let i = from;
  while (i < s.length) {
    const c = s[i];
    if (c === '\\') { i += 2; continue; }
    if (c === '`') {
      let run = 1;
      while (s[i + run] === '`') run += 1;
      let j = i + run;
      let closed = false;
      while (j < s.length) {
        if (s[j] === '`') {
          let m2 = 1;
          while (s[j + m2] === '`') m2 += 1;
          if (m2 === run) { j += m2; closed = true; break; }
          j += m2;
        } else j += 1;
      }
      i = closed ? j : i + run;
      continue;
    }
    if (c === '[') depth += 1;
    else if (c === ']') {
      depth -= 1;
      if (depth === 0) return i;
    }
    i += 1;
  }
  return -1;
}

function parseLinkDest(s, openIdx) {
  let p = openIdx + 1;
  const skipWs = () => {
    while (p < s.length && (s[p] === ' ' || s[p] === '\t' || s[p] === '\n')) p += 1;
  };
  skipWs();
  if (s[p] === ')') return { href: '', title: null, end: p + 1 };
  const dest = scanDest(s, p, true);
  if (!dest) return null;
  p = dest.end;
  skipWs();
  if (s[p] === ')') return { href: dest.href, title: null, end: p + 1 };
  const t = scanTitle(s, p);
  if (!t) return null;
  p = t.end;
  skipWs();
  if (s[p] === ')') return { href: dest.href, title: t.title, end: p + 1 };
  return null;
}

const PUNCT_RE = /[\p{P}\p{S}]/u;
function isWsChar(ch) {
  return ch === undefined || ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === '\f' || ch === '\v';
}
function isPunctChar(ch) {
  return ch !== undefined && PUNCT_RE.test(ch);
}

const TRAILING_PUNCT = new Set(['?', '!', '.', ',', ':', '*', '_', '~', ';']);
const ENTITY_TAIL_RE = /&(?:#\d+|#[Xx][0-9A-Fa-f]+|\w+);$/;

function trimAutolink(url) {
  let u = url;
  for (;;) {
    const before = u;
    u = u.replace(ENTITY_TAIL_RE, '');
    while (u.length && TRAILING_PUNCT.has(u[u.length - 1])) u = u.slice(0, -1);
    let opens = 0;
    let closes = 0;
    for (const ch of u) {
      if (ch === '(') opens += 1;
      else if (ch === ')') closes += 1;
    }
    while (u.endsWith(')') && closes > opens) {
      u = u.slice(0, -1);
      closes -= 1;
    }
    if (u === before) return u;
  }
}

// Try a GFM extended autolink at s[i]: returns {raw, href} or null.
function matchAutolink(s, i, prevCh) {
  const rest = s.slice(i);
  let m = /^(?:https?|ftp):\/\/[^\s<>]+/i.exec(rest);
  if (m) {
    const raw = trimAutolink(m[0]);
    if (raw.length <= m[0].indexOf('://') + 3) return null;
    return { raw, href: raw };
  }
  if ((rest.startsWith('www.') || rest.startsWith('WWW.')) && (prevCh === undefined || isWsChar(prevCh) || isPunctChar(prevCh))) {
    m = /^www\.[^\s<>]+/i.exec(rest);
    if (m && m[0].includes('.', 4)) {
      const raw = trimAutolink(m[0]);
      if (raw.length > 4) return { raw, href: 'http://' + raw };
    }
    return null;
  }
  if (prevCh === undefined || !( /[A-Za-z0-9.!#$%&'*+\/=?^_`{|}~@-]/.test(prevCh) )) {
    m = /^[A-Za-z0-9.!#$%&'*+\/=?^_`{|}~-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+/.exec(rest);
    if (m) {
      const raw = trimAutolink(m[0]);
      if (raw.includes('@')) return { raw, href: 'mailto:' + raw };
    }
  }
  return null;
}

function renderInline(src, ctx, inLink) {
  let head = null;
  let tail = null;
  const delims = [];
  const appendNode = (node) => {
    node.prev = tail;
    node.next = null;
    if (tail) tail.next = node;
    else head = node;
    tail = node;
    return node;
  };
  let textBuf = '';
  const flushText = () => {
    if (textBuf === '') return;
    if (tail && tail.kind === 'text' && !tail.delim) tail.text += textBuf;
    else appendNode({ kind: 'text', text: textBuf, delim: false });
    textBuf = '';
  };
  const pushRaw = (html) => {
    flushText();
    appendNode({ kind: 'raw', text: html });
  };

  const n = src.length;
  let i = 0;
  while (i < n) {
    const c = src[i];
    if (c === '\\') {
      const nx = src[i + 1];
      if (nx === '\n') {
        pushRaw('<br>');
        i += 2;
        continue;
      }
      if (nx !== undefined && ASCII_PUNCT.has(nx)) {
        // An escaped punctuation character is inert: it must not start an
        // entity, a delimiter run or a tag, so it becomes its own node.
        pushRaw(escapeFull(nx));
        i += 2;
        continue;
      }
      textBuf += '\\';
      i += 1;
      continue;
    }
    if (c === '`') {
      let run = 1;
      while (src[i + run] === '`') run += 1;
      let j = i + run;
      let found = -1;
      while (j < n) {
        if (src[j] === '`') {
          let m2 = 1;
          while (src[j + m2] === '`') m2 += 1;
          if (m2 === run) { found = j; break; }
          j += m2;
        } else j += 1;
      }
      if (found === -1) {
        textBuf += '`'.repeat(run);
        i += run;
        continue;
      }
      let content = src.slice(i + run, found).replace(/\n/g, ' ');
      if (content.length >= 2 && content[0] === ' ' && content[content.length - 1] === ' ' && /[^ ]/.test(content)) {
        content = content.slice(1, -1);
      }
      pushRaw('<code>' + escapeFull(content) + '</code>');
      i = found + run;
      continue;
    }
    if (c === '<') {
      const rest = src.slice(i);
      let m = /^<([A-Za-z][A-Za-z0-9+.-]{1,31}:[^<>\s]*)>/.exec(rest);
      if (m) {
        const attr = hrefAttr(m[1]);
        pushRaw('<a href="' + (attr === null ? '' : attr) + '">' + escapeFull(m[1]) + '</a>');
        i += m[0].length;
        continue;
      }
      m = /^<([A-Za-z0-9.!#$%&'*+\/=?^_`{|}~-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+)>/.exec(rest);
      if (m) {
        pushRaw('<a href="mailto:' + escapeText(m[1]) + '">' + escapeText(m[1]) + '</a>');
        i += m[0].length;
        continue;
      }
      const html = scanInlineHtml(rest);
      if (html !== null) {
        pushRaw(html);
        i += html.length;
        continue;
      }
      textBuf += '<';
      i += 1;
      continue;
    }
    if (c === '[' || (c === '!' && src[i + 1] === '[')) {
      const isImg = c === '!';
      if (isImg || !inLink) {
        const labelStart = i + (isImg ? 2 : 1);
        const close = findClosingBracket(src, labelStart);
        if (close !== -1) {
          const label = src.slice(labelStart, close);
          let href = null;
          let title = null;
          let consumed = -1;
          let refAttempted = false;
          if (src[close + 1] === '(') {
            const pd = parseLinkDest(src, close + 1);
            if (pd) {
              href = pd.href;
              title = pd.title;
              consumed = pd.end;
            }
          }
          if (consumed === -1 && src[close + 1] === '[') {
            refAttempted = true;
            // full or collapsed reference
            let refEnd = close + 2;
            let refLabel = '';
            let ok = true;
            while (refEnd < n && src[refEnd] !== ']') {
              if (src[refEnd] === '[') { ok = false; break; }
              if (src[refEnd] === '\\' && refEnd + 1 < n) { refLabel += src[refEnd + 1]; refEnd += 2; continue; }
              refLabel += src[refEnd];
              refEnd += 1;
            }
            if (ok && src[refEnd] === ']') {
              const def = ctx.defs.get(defKey(refLabel === '' ? label : refLabel));
              if (def) {
                href = def.href;
                title = def.title;
                consumed = refEnd + 1;
              }
            }
          }
          if (consumed === -1 && !refAttempted) {
            const def = ctx.defs.get(defKey(label));
            if (def) {
              href = def.href;
              title = def.title;
              consumed = close + 1;
            }
          }
          if (consumed !== -1) {
            const attr = hrefAttr(href);
            if (isImg) {
              const alt = renderInline(label, ctx, true).replace(/<[^>]*>/g, '');
              pushRaw('<img src="' + (attr === null ? '' : attr) + '" alt="' + alt + '"' + (title !== null ? ' title="' + escapeText(title) + '"' : '') + '>');
            } else if (attr === null) {
              pushRaw(renderInline(label, ctx, true));
            } else {
              pushRaw('<a href="' + attr + '"' + (title !== null ? ' title="' + escapeText(title) + '"' : '') + '>' + renderInline(label, ctx, true) + '</a>');
            }
            i = consumed;
            continue;
          }
        }
      }
      textBuf += c;
      i += 1;
      continue;
    }
    if (c === '*' || c === '_' || c === '~') {
      let run = 1;
      while (src[i + run] === c) run += 1;
      if (c === '~' && run > 2) {
        textBuf += '~'.repeat(run);
        i += run;
        continue;
      }
      flushText();
      const node = appendNode({ kind: 'text', text: c.repeat(run), delim: true });
      const prevCh = i > 0 ? src[i - 1] : undefined;
      const nextCh = i + run < n ? src[i + run] : undefined;
      let canOpen;
      let canClose;
      if (c === '~') {
        canOpen = nextCh !== undefined && !isWsChar(nextCh);
        canClose = prevCh !== undefined && !isWsChar(prevCh);
      } else {
        const leftFlank = !isWsChar(nextCh) && (!isPunctChar(nextCh) || isWsChar(prevCh) || isPunctChar(prevCh));
        const rightFlank = !isWsChar(prevCh) && (!isPunctChar(prevCh) || isWsChar(nextCh) || isPunctChar(nextCh));
        if (c === '*') {
          canOpen = leftFlank;
          canClose = rightFlank;
        } else {
          canOpen = leftFlank && (!rightFlank || isPunctChar(prevCh));
          canClose = rightFlank && (!leftFlank || isPunctChar(nextCh));
        }
      }
      delims.push({ node, char: c, len: run, canOpen, canClose });
      i += run;
      continue;
    }
    if (c === ' ') {
      const m = /^ {2,}\n/.exec(src.slice(i));
      if (m) {
        pushRaw('<br>');
        i += m[0].length;
        continue;
      }
      textBuf += ' ';
      i += 1;
      continue;
    }
    if (!inLink && (c === 'h' || c === 'H' || c === 'w' || c === 'W' || c === 'f' || c === 'F' || /[A-Za-z0-9.!#$%&'*+\/=?^_`{|}~-]/.test(c))) {
      const prevCh = i > 0 ? src[i - 1] : undefined;
      const al = matchAutolink(src, i, prevCh);
      if (al) {
        const attr = hrefAttr(al.href);
        pushRaw('<a href="' + (attr === null ? '' : attr) + '">' + escapeFull(al.raw) + '</a>');
        i += al.raw.length;
        continue;
      }
    }
    textBuf += c;
    i += 1;
  }
  flushText();

  processDelims(delims);
  return renderNodes(head);
}

function processDelims(delims) {
  const openersBottom = new Map();
  let ci = 0;
  while (ci < delims.length) {
    const closer = delims[ci];
    if (!closer.canClose || closer.len === 0) { ci += 1; continue; }
    const key = closer.char + '|' + (closer.len % 3) + '|' + (closer.canOpen ? '1' : '0');
    const bottom = openersBottom.has(key) ? openersBottom.get(key) : -1;
    let oi = -1;
    for (let k = ci - 1; k > bottom; k -= 1) {
      const op = delims[k];
      if (op.char !== closer.char || !op.canOpen || op.len === 0) continue;
      if (closer.char === '~') {
        if (op.len !== closer.len) continue;
        oi = k;
        break;
      }
      if ((closer.canOpen || op.canClose) && (op.len + closer.len) % 3 === 0 && !(op.len % 3 === 0 && closer.len % 3 === 0)) continue;
      oi = k;
      break;
    }
    if (oi === -1) {
      openersBottom.set(key, ci - 1);
      if (!closer.canOpen) closer.canClose = false;
      ci += 1;
      continue;
    }
    const op = delims[oi];
    const use = closer.char === '~' ? closer.len : (op.len >= 2 && closer.len >= 2 ? 2 : 1);
    op.len -= use;
    closer.len -= use;
    op.node.text = op.node.text.slice(0, op.node.text.length - use);
    closer.node.text = closer.node.text.slice(use);
    const tag = closer.char === '~' ? 'del' : use === 2 ? 'strong' : 'em';
    wrapNodes(op.node, closer.node, tag);
    for (let k = oi + 1; k < ci; k += 1) {
      delims[k].canOpen = false;
      delims[k].canClose = false;
    }
    if (closer.len === 0) ci += 1;
  }
}

function wrapNodes(openNode, closeNode, tag) {
  const wrap = { kind: 'wrap', tag, inner: null, prev: openNode, next: closeNode };
  const first = openNode.next;
  const last = closeNode.prev;
  if (first === closeNode) {
    wrap.inner = null;
  } else {
    wrap.inner = first;
    first.prev = null;
    last.next = null;
  }
  openNode.next = wrap;
  closeNode.prev = wrap;
}

function renderNodes(head) {
  let out = '';
  let node = head;
  while (node) {
    if (node.kind === 'text') out += escapeTextNode(node.text);
    else if (node.kind === 'raw') out += node.text;
    else if (node.kind === 'wrap') out += '<' + node.tag + '>' + renderNodes(node.inner) + '</' + node.tag + '>';
    node = node.next;
  }
  return out;
}
