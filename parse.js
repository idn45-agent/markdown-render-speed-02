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
  if (!s.includes('&') && !s.includes('<') && !s.includes('>') && !s.includes('"') && !s.includes("'")) return s;
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
// straddles the cut is dropped whole. Returns the rest
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
        // A tab straddling the cut is dropped whole (marked's fence
        // content stripping does not leave its remainder as spaces).
        return line.slice(i + 1);
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
// Does the line's leading whitespace contain a tab that ends past
// column n (i.e. the strip of n columns would cut through it or
// leave it in the remainder's indent)?
function isTabIndentedLine(line, n) {
  let col = 0;
  for (let p = 0; p < line.length; p += 1) {
    const ch = line[p];
    if (ch === ' ') { col += 1; continue; }
    if (ch === '\t') {
      const end = col + (4 - (col % 4));
      if (end > n) return true;
      col = end;
      continue;
    }
    return false;
  }
  return false;
}

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
  return label.replace(/\s+/g, ' ').trim().toLowerCase().replace(/ß/g, 'ss');
}

// Try to read a link reference definition starting at lines[i]. On success
// returns {lines: consumedCount, label, href, title} and registers nothing;
// on failure returns null.
function scanDef(lines, i) {
  const first = lines[i];
  const m = /^ {0,3}\[/.exec(first);
  if (!m) return null;
  // The definition is parsed over the first line plus as many following
  // (non-blank) lines as it needs: the label, the destination and the
  // title may each sit on their own line, and a title may span lines.
  let text = first.slice(m[0].length);
  let used = 1;
  const extend = () => {
    if (i + used < lines.length && !isBlank(lines[i + used])) {
      text += '\n' + lines[i + used];
      used += 1;
      return true;
    }
    return false;
  };
  const ensure = (pos) => { while (pos >= text.length && extend()) { /* grow */ } };
  // Label: up to an unescaped ']' (an unescaped '[' is not allowed).
  let pos = 0;
  let label = '';
  let labelEnd = -1;
  for (;;) {
    ensure(pos);
    if (pos >= text.length) return null;
    const c = text[pos];
    if (c === '\\') {
      ensure(pos + 1);
      if (pos + 1 >= text.length) return null;
      label += c + text[pos + 1];
      pos += 2;
      continue;
    }
    if (c === '[') return null;
    if (c === ']') { labelEnd = pos; break; }
    label += c;
    pos += 1;
  }
  if (label.length > 999 || label.trim() === '') return null;
  ensure(labelEnd + 1);
  if (text[labelEnd + 1] !== ':') return null;
  pos = labelEnd + 2;
  // A gap: spaces/tabs and at most one newline.
  const skipGap = (p) => {
    let sawNl = false;
    for (;;) {
      if (p >= text.length) {
        if (!extend()) return p;
        continue;
      }
      const c = text[p];
      if (c === ' ' || c === '\t') { p += 1; continue; }
      if (c === '\n' && !sawNl) { sawNl = true; p += 1; continue; }
      return p;
    }
  };
  const lineRestBlank = (p) => {
    let q = p;
    while (q < text.length && text[q] !== '\n') {
      if (text[q] !== ' ' && text[q] !== '\t') return false;
      q += 1;
    }
    return true;
  };
  const consumed = (p) => text.slice(0, p).split('\n').length;
  pos = skipGap(pos);
  ensure(pos);
  if (pos >= text.length) return null;
  const dest = scanDest(text, pos, true);
  if (!dest) return null;
  const endDest = dest.end;
  // Optional title, but only when at least one whitespace character
  // separates it from the destination.
  const posT = skipGap(endDest);
  if (posT > endDest) {
    while (extend()) { /* a title may span many lines */ }
    if (posT < text.length) {
      const t = scanTitle(text, posT);
      if (t && lineRestBlank(t.end)) {
        return { lines: consumed(t.end), label, href: dest.href, title: t.title };
      }
    }
  }
  if (lineRestBlank(endDest)) {
    return { lines: consumed(endDest), label, href: dest.href, title: null };
  }
  return null;
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
  const fc0 = firstContentChar(line);
  if (fc0 !== '-' && fc0 !== '+' && fc0 !== '*' && !(fc0 >= '0' && fc0 <= '9')) return null;
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

function firstContentChar(line) {
  let p = 0;
  while (line[p] === ' ') p += 1;
  return line[p];
}

function htmlBlockStart(line, lines, i) {
  if (firstContentChar(line) !== '<') return null;
  const m = /^ {0,3}<(\/?)([A-Za-z][A-Za-z0-9-]*)((?:[ \t]+[^ \t<>"'/=]+(?:[ \t]*=[ \t]*(?:[^ \t"'=<>`]+|'[^']*'|"[^"]*"))?)*)[ \t]*(\/?)>/.exec(line);
  const stripped = line.replace(/^ {0,3}/, '');
  if (stripped.startsWith('<!--')) return { kind: 'comment' };
  if (stripped.startsWith('<?')) return { kind: 'pi' };
  if (stripped.startsWith('<![CDATA[')) return { kind: 'cdata' };
  if (/^<![A-Z]/.test(stripped)) return { kind: 'decl' };
  const rawM = /^ {0,3}<(script|pre|style|textarea)(?=[ \t>]|\/>|$)/i.exec(line);
  if (rawM) return { kind: 'raw', tag: rawM[1].toLowerCase() };
  // A block-level tag name followed by whitespace, '>', '/>' or the end of
  // the line opens an HTML block even if the tag is never completed.
  const bm = /^ {0,3}<\/?([A-Za-z][A-Za-z0-9-]*)(?=[ \t>]|\/>|$)/.exec(line);
  if (bm && BLOCK_TAGS.has(bm[1].toLowerCase())) return { kind: 'block' };
  if (m) {
    // Type 7: a complete, well-formed tag with only whitespace after it.
    const tagLen = scanInlineHtml(line.replace(/^ {0,3}/, ''), 0);
    if (tagLen !== -1 && tagLen === m[0].replace(/^ {0,3}/, '').length && /^[ \t]*$/.test(line.slice(m[0].length))) return { kind: 'tag' };
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
  while (i < line.length) {
    const c = line[i];
    if (c === '\\' && i + 1 < line.length) {
      if (line[i + 1] === '|') {
        cur += '|'; // marked unescapes \| to | in cell text
        i += 2;
        continue;
      }
      cur += c + line[i + 1];
      i += 2;
      continue;
    }
    if (c === '`') {
      // A code span protects the pipes inside it. marked's cell
      // splitter finds spans the way its codespan regex does: try
      // opening runs from longest to shortest, the closing string is
      // the next occurrence of the same backtick string, and the
      // content must be non-empty; on failure a single backtick is
      // literal and scanning resumes at the next one.
      let run = 1;
      while (line[i + run] === '`') run += 1;
      let end = -1;
      for (let open = run; open >= 1 && end === -1; open -= 1) {
        const ticks = '`'.repeat(open);
        const close = line.indexOf(ticks, i + open + 1);
        if (close !== -1) end = close + open;
      }
      if (end === -1) {
        cur += '`';
        i += 1;
      } else {
        let seg = '';
        let k = i;
        while (k < end) {
          if (line[k] === '\\' && k + 1 < end) {
            seg += line[k + 1] === '|' ? '|' : line[k] + line[k + 1];
            k += 2;
            continue;
          }
          seg += line[k];
          k += 1;
        }
        cur += seg;
        i = end;
      }
      continue;
    }
    if (c === '|') {
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

// A table body ends at a blank line or at a line that starts another
// block (a heading, list, fence, quote, rule, definition, HTML block or
// indented code).
function tableRowEnds(lines, j, inItem) {
  const line = lines[j];
  if (leadingCols(line) >= 4 && line.trim() !== '') return true;
  if (startsInterruptingBlock(line, lines, j, inItem)) return true;
  if (scanDef(lines, j)) return true;
  if (htmlBlockStart(line, lines, j)) return true;
  return false;
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
  let pendingBlank = false;
  let sepBlank = false;
  const push = (tok) => {
    if (pendingBlank) { sepBlank = true; pendingBlank = false; }
    tokens.push(tok);
  };
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    if (isBlank(line)) {
      if (tokens.length) pendingBlank = true;
      i += 1;
      continue;
    }
    // Lines an outer container collected as lazy paragraph text are
    // forced paragraph content: they never start a block.
    if (prot && prot.has(i)) {
      const p = lexParagraph(lines, i, ctx, prot);
      push(p.token);
      i = p.next;
      continue;
    }
    const fc = firstContentChar(line);
    // fenced code
    const fm = (fc === '`' || fc === '~') ? FENCE_RE.exec(line) : null;
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
        // Marked dedents backtick-fence content by the opener's
        // indent, but leaves tilde-fence content untouched.
        body.push(ch === '`' && indent > 0 ? stripCols(cl, indent) : cl);
        j += 1;
      }
      if (body.length && body[body.length - 1] === '') body.pop();
      push({ t: 'fence', lang: info === '' ? null : unescapePunct(info.split(/[ \t]+/)[0]), text: body.length ? body.join('\n') + '\n' : '' });
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
      push({ t: 'code', text: body.join('\n') + '\n' });
      i += lastContent + 1;
      continue;
    }
    // ATX heading
    const hm = fc === '#' ? ATX_RE.exec(line) : null;
    if (hm) {
      let text = hm[2] === undefined ? '' : hm[2];
      if (/^#+$/.test(text)) text = '';
      else text = text.replace(/[ \t]#+$/, '').replace(/[ \t]+$/, '');
      push({ t: 'heading', depth: hm[1].length, text });
      i += 1;
      continue;
    }
    // thematic break
    if ((fc === '-' || fc === '*' || fc === '_') && HR_RE.test(line)) {
      push({ t: 'hr' });
      i += 1;
      continue;
    }
    // blockquote
    if (fc === '>' && QUOTE_RE.test(line)) {
      const q = lexQuote(lines, i, ctx, prot);
      push(q.token);
      i = q.next;
      continue;
    }
    // list
    if (matchListStart(line)) {
      const l = lexList(lines, i, ctx, prot);
      push(l.token);
      i = l.next;
      continue;
    }
    // HTML block
    const hb = htmlBlockStart(line, lines, i);
    if (hb) {
      const h = lexHtmlBlock(lines, i, hb, ctx);
      push(h.token);
      i = h.next;
      continue;
    }
    // link reference definition
    const def = fc === '[' ? scanDef(lines, i) : null;
    if (def) {
      const key = defKey(def.label);
      if (!ctx.defs.has(key)) ctx.defs.set(key, { href: def.href, title: def.title });
      // Definitions are invisible in the output but still count as a
      // block when a list's looseness is decided.
      if (pendingBlank) { sepBlank = true; pendingBlank = false; }
      i += def.lines;
      continue;
    }
    // table
    const ts = tableStart(lines, i);
    if (ts) {
      const rows = [];
      let j = i + 2;
      while (j < n && !/^ *$/.test(lines[j]) && !tableRowEnds(lines, j, ctx.inItem)) {
        rows.push(splitRow(lines[j].replace(/^ {0,3}/, '')));
        j += 1;
      }
      push({ t: 'table', header: ts.header, align: ts.align, rows });
      i = j;
      continue;
    }
    // paragraph or setext heading
    const p = lexParagraph(lines, i, ctx, prot);
    push(p.token);
    i = p.next;
  }
  tokens.sepBlank = sepBlank;
  return tokens;
}

function lexHtmlBlock(lines, i, hb, ctx) {
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
  // Marked keeps the newline after the block's last line unless the block
  // was terminated by a blank line (or the source simply ends there).
  // Blank-terminated kinds (block/tag) treat any whitespace-only line as
  // the terminator; closer-terminated kinds only lose the newline when
  // the following line is completely empty.
  let text = body.join('\n');
  const lastIdx = j - 1;
  if (lastIdx < lines.length - 1) {
    const closerKind = hb.kind !== 'block' && hb.kind !== 'tag';
    if (closerKind ? lines[j] !== '' : !isBlank(lines[j])) text += '\n';
  } else if (ctx.srcEndsNl) {
    text += '\n';
  }
  return { token: { t: 'html', text }, next: j };
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
  const st = { open: false, fence: null };
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
      advanceTrack(st, stripped, false);
      lazyRun = 0;
      j += 1;
      continue;
    }
    if (isBlank(line)) break;
    if (st.open && !startsInterruptingBlock(line, lines, j)) {
      let lazy;
      if (lazyRun === 0) {
        lazy = stripTabUnit(line);
      } else if (SETEXT_RE.test(line) && line[0] !== '\t') {
        lazy = '    ' + line.replace(/^ {0,3}/, '');
      } else {
        lazy = line;
      }
      // A lazy line is paragraph text by construction: protect it from
      // being re-lexed as a block start (or a setext underline).
      innerProt.add(inner.length);
      if (prot && prot.has(j)) innerProt.add(inner.length);
      inner.push(lazy);
      advanceTrack(st, lazy, false);
      lazyRun += 1;
      j += 1;
      continue;
    }
    break;
  }
  const children = lexBlocks(inner, { defs: ctx.defs, top: false, openEnd: true, inItem: false }, innerProt);
  return { token: { t: 'quote', children }, next: j };
}

// Would `line` interrupt a paragraph? (Setext underlines do not count:
// they continue the paragraph by converting it.)
function isFenceStart(line) {
  const fc0 = firstContentChar(line);
  if (fc0 !== '`' && fc0 !== '~') return false;
  const fm = FENCE_RE.exec(line);
  return fm !== null && (fm[1][0] === '~' || !fm[2].includes('`'));
}

function startsInterruptingBlock(line, lines, j, inItem) {
  const fc0 = firstContentChar(line);
  if (isFenceStart(line)) return true;
  if (fc0 === '#' && ATX_RE.test(line)) return true;
  if ((fc0 === '-' || fc0 === '*' || fc0 === '_') && HR_RE.test(line)) return true;
  if (fc0 === '>' && QUOTE_RE.test(line)) return true;
  const ms = matchListStart(line);
  // Inside a list item, marked lets an ordered list interrupt a
  // paragraph whatever its start number; elsewhere only 1 does.
  if (ms && !ms.empty && (!ms.ordered || ms.num === 1 || inItem)) return true;
  const hb = htmlBlockStart(line, lines, j);
  if (hb && hb.kind !== 'tag') return true;
  if (tableStart(lines, j)) return true;
  return false;
}
function lexParagraph(lines, i, ctx, prot) {
  const collected = [lines[i]];
  let j = i + 1;
  while (j < lines.length) {
    const line = lines[j];
    if (isBlank(line)) {
      // A whitespace-only final line with no terminator of its own is
      // paragraph content in marked, not a blank separator.
      if (j === lines.length - 1 && ctx.openEnd && line.length > 0) {
        collected.push(line);
        j += 1;
      }
      break;
    }
    if (prot && prot.has(j)) {
      collected.push(line);
      j += 1;
      continue;
    }
    const sm = SETEXT_RE.exec(line);
    if (sm && !(prot && prot.has(j))) {
      return {
        token: { t: 'heading', depth: sm[1][0] === '=' ? 1 : 2, text: collected.join('\n').trim() },
        next: j + 1,
      };
    }
    if (startsInterruptingBlock(line, lines, j, ctx.inItem)) break;
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
function paraOpenAfter(line, wasOpen, inItem) {
  if (isBlank(line)) return false;
  const fc = firstContentChar(line);
  if (fc === '>' && QUOTE_RE.test(line)) {
    const g = line.indexOf('>');
    let fromCol = g + 1;
    if (line[g + 1] === ' ' || line[g + 1] === '\t') fromCol += 1;
    return paraOpenAfter(stripContainer(line, fromCol), false, false);
  }
  const ms = matchListStart(line);
  if (ms) return ms.rest !== '' && paraOpenAfter(ms.rest, false, true);
  if (wasOpen) {
    if (SETEXT_RE.test(line)) return false;
    return !startsInterruptingBlock(line, [line], 0, inItem);
  }
  if (leadingCols(line) >= 4) return false;
  if (fc === '[' && scanDef([line], 0)) return false;
  return !startsInterruptingBlock(line, [line], 0, inItem);
}

// Does `line` close the open fence `fence` ({ch, len})?
function isFenceClose(line, fence) {
  const cm = /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(line);
  return cm !== null && cm[1][0] === fence.ch && cm[1].length >= fence.len;
}

// Advance a container-collection state {open, fence} over one content
// line: while a fence is open its content lines leave no paragraph open
// (so they are never mistaken for paragraph text), and a fence start
// records the fence so following lines are tracked as its content.
function advanceTrack(st, line, inItem) {
  if (st.fence) {
    if (!isBlank(line) && isFenceClose(line, st.fence)) st.fence = null;
    st.open = false;
    return;
  }
  const fc = firstContentChar(line);
  const fm = (fc === '`' || fc === '~') ? FENCE_RE.exec(line) : null;
  if (fm && (fm[1][0] === '~' || !fm[2].includes('`'))) {
    st.fence = { ch: fm[1][0], len: fm[1].length };
    st.open = false;
    return;
  }
  st.open = paraOpenAfter(line, st.open, inItem);
}

// Flat paragraph state at one container level (no recursion into nested
// quotes/lists): true when `line` leaves a paragraph of THIS level open.
function paraOpenFlat(line, wasOpen) {
  if (isBlank(line)) return false;
  if (leadingCols(line) >= 4) return false;
  const fc = firstContentChar(line);
  if (fc === '`' || fc === '~') { if (isFenceStart(line)) return false; }
  else if (fc === '#' && ATX_RE.test(line)) return false;
  else if ((fc === '-' || fc === '*' || fc === '_') && HR_RE.test(line)) return false;
  else if (fc === '>' && QUOTE_RE.test(line)) return false;
  if (matchListStart(line)) return false;
  if (htmlBlockStart(line)) return false;
  if (fc === '[' && scanDef([line], 0)) return false;
  if (wasOpen && SETEXT_RE.test(line)) return false;
  return true;
}

// Would the text after an indented line's first 4 columns start a block?
function blockStartAfterIndent(line) {
  const rest = stripCols(line, 4);
  if (isFenceStart(rest) || ATX_RE.test(rest) || HR_RE.test(rest) || QUOTE_RE.test(rest)) return true;
  if (matchListStart(rest)) return true;
  if (htmlBlockStart(rest)) return true;
  return false;
}

// Strip a blockquote marker (for state tracking only).
function quoteStrip(line) {
  const g = line.indexOf('>');
  let fromCol = g + 1;
  if (line[g + 1] === ' ' || line[g + 1] === '\t') fromCol += 1;
  return stripContainer(line, fromCol);
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
    const itemLazy = new Set();
    const itemSt = { open: false, fence: null };
    // Whether the item's open fence is "live": it has already taken
    // a content line, with no blank line since. Only a live fence
    // pulls in following unindented lines as content.
    let itemFenceLive = false;
    // Index in itemLines of the last "tab line" (see the >= ci branch):
    // when a run of tab lines ends, that line's text gains a trailing
    // newline (marked renders a phantom blank inside the paragraph).
    // The rule only applies to the item's own-level paragraph: once a
    // nested list starts, plain lines belong to it, not to this item.
    let tabLineIdx = -1;
    let itemNestedList = false;
    if (ms.rest !== '') advanceTrack(itemSt, ms.rest, true);
    let itemOwnParaOpen = ms.rest !== '' && paraOpenFlat(ms.rest, false);
    let itemQuotePara = QUOTE_RE.test(ms.rest) ? paraOpenAfter(quoteStrip(ms.rest), false, false) : false;
    let itemHasContent = ms.rest !== '';
    let k = j + 1;
    let end = -1;
    let endViaBlank = false;
    while (k < lines.length) {
      const line = lines[k];
      if (isBlank(line)) {
        // look ahead: more item content, a sibling item, or the end
        let m = k + 1;
        while (m < lines.length && isBlank(lines[m])) m += 1;
        if (m >= lines.length) { end = k; endViaBlank = true; break; }
        const nl = lines[m];
        if (itemHasContent && leadingCols(nl) >= ci) {
          for (let b = k; b < m; b += 1) { itemLines.push(''); itemSrc.push(b); advanceTrack(itemSt, '', true); }
          itemOwnParaOpen = false;
          // A nested list survives a blank when the content after it
          // is still indented into the nested list's range; only a
          // return to this item's own level ends it.
          if (leadingCols(stripContainer(nl, ci)) < 2) itemNestedList = false;
          itemQuotePara = false;
          itemFenceLive = false;
          k = m;
          continue;
        }
        const nm = matchListStart(nl);
        if (!HR_RE.test(nl) && sameListItem(nm, first)) {
          loose = true;
          end = k;
          endViaBlank = true;
          break;
        }
        end = k;
        endViaBlank = true;
        break;
      }
      if (leadingCols(line) >= ci) {
        // A "tab line": the line's leading whitespace holds a tab that
        // the content-indent strip does not consume exactly (it ends
        // past the strip), while the item's own paragraph is open.
        // Marked renders such a line with its whole indent removed,
        // and the last line of a tab-line run carries an extra
        // trailing newline in the paragraph text.
        let stripped = stripContainer(line, ci);
        let tabLine = false;
        if (!itemSt.fence && itemOwnParaOpen && !itemNestedList && isTabIndentedLine(line, ci)) {
          const content = line.replace(/^[ \t]+/, '');
          if (!matchListStart(content) && !isFenceStart(content)) {
            tabLine = true;
            stripped = content;
          }
        }
        if (!tabLine && tabLineIdx !== -1) {
          if (itemLines.length - 1 === tabLineIdx) itemLines[tabLineIdx] += '\n';
          tabLineIdx = -1;
        }
        itemLines.push(stripped);
        itemSrc.push(k);
        if (tabLine) tabLineIdx = itemLines.length - 1;
        itemHasContent = true;
        const wasFence = itemSt.fence !== null;
        advanceTrack(itemSt, stripped, true);
        itemFenceLive = itemSt.fence ? wasFence : false;
        itemOwnParaOpen = itemSt.fence ? false : paraOpenFlat(stripped, itemOwnParaOpen);
        if (matchListStart(stripped)) itemNestedList = true;
        if (QUOTE_RE.test(stripped)) itemQuotePara = paraOpenAfter(quoteStrip(stripped), false, false);
        else if (!(itemQuotePara && !startsInterruptingBlock(stripped, [stripped], 0))) itemQuotePara = false;
        k += 1;
        continue;
      }
      if (itemSt.fence) {
        // An unindented line while the item's fence is open is fence
        // content only when the fence is live (it already took a
        // content line with no blank since); a fence-close line is
        // never the item's. Otherwise the item ends here and the
        // fence keeps the content it had.
        if (isFenceClose(line, itemSt.fence)) { end = k; break; }
        if (!itemFenceLive) { end = k; break; }
        itemLines.push(line);
        itemSrc.push(k);
        itemHasContent = true;
        advanceTrack(itemSt, line, true);
        k += 1;
        continue;
      }
      const lm = matchListStart(line);
      if (!HR_RE.test(line) && sameListItem(lm, first)) { end = k; break; }
      if (lm) { end = k; break; } // an item of a different list ends this one
      if (itemQuotePara && QUOTE_RE.test(line)) {
        // a marker line of a blockquote that is open inside the item
        itemLines.push(line);
        itemSrc.push(k);
        itemHasContent = true;
        itemQuotePara = paraOpenAfter(quoteStrip(line), false, false);
        k += 1;
        continue;
      }
      if (itemSt.open && !startsInterruptingBlock(line, lines, k)) {
        if (tabLineIdx !== -1) {
          if (itemLines.length - 1 === tabLineIdx) itemLines[tabLineIdx] += '\n';
          tabLineIdx = -1;
        }
        itemLines.push(stripTabUnit(line)); // lazy continuation
        itemSrc.push(k);
        itemLazy.add(itemLines.length - 1);
        itemHasContent = true;
        k += 1;
        continue;
      }
      end = k;
      break;
    }
    if (end === -1) end = k;
    let itemProt = null;
    if (prot || itemLazy.size) {
      itemProt = new Set(itemLazy);
      if (prot) {
        for (let x = 0; x < itemSrc.length; x += 1) {
          if (prot.has(itemSrc[x])) itemProt.add(x);
        }
      }
      if (itemProt.size === 0) itemProt = null;
    }
    const itemTokens = lexBlocks(itemLines, { defs: ctx.defs, top: false, openEnd: true, inItem: true }, itemProt);
    if (itemTokens.sepBlank) loose = true;
    items.push(itemTokens);
    j = end;
    if (endViaBlank) {
      // The item ended at a blank line: the list only continues if a
      // sibling item follows the blanks. Report the blank position as
      // the end so an enclosing level can see the separator.
      let m = j;
      while (m < lines.length && isBlank(lines[m])) m += 1;
      if (m < lines.length && !HR_RE.test(lines[m]) && sameListItem(matchListStart(lines[m]), first)) {
        j = m;
      } else {
        break;
      }
    } else if (j < lines.length && (HR_RE.test(lines[j]) || !sameListItem(matchListStart(lines[j]), first))) {
      break;
    }
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
      return tok.text;
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
  const ctx = { defs: new Map(), top: true, srcEndsNl: text.endsWith('\n'), openEnd: !text.endsWith('\n'), inItem: false, state: { inLink: false } };
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
  if (!s.includes('&') && !s.includes('<') && !s.includes('>') && !s.includes('"') && !s.includes("'")) return s;
  return escapeText(decodeNumericEntities(s));
}

function cleanUrl(href) {
  try {
    const enc = encodeURI(href);
    return href.includes('%') ? enc.replace(/%25/g, '%') : enc;
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
// Scan an inline HTML tag/comment/etc. at s[off]: returns its length
// or -1. Mirrors the CommonMark tag grammar.
function scanInlineHtml(s, off) {
  if (s.startsWith('<!--', off)) {
    if (s.startsWith('<!-->', off)) return 5;
    if (s.startsWith('<!--->', off)) return 6;
    const end = s.indexOf('-->', off + 4);
    if (end === -1) return -1;
    return end + 3 - off;
  }
  if (s.startsWith('<![CDATA[', off)) {
    const end = s.indexOf(']]>', off + 9);
    if (end === -1) return -1;
    return end + 3 - off;
  }
  if (s.startsWith('<?', off)) {
    const end = s.indexOf('?>', off + 2);
    if (end === -1) return -1;
    return end + 2 - off;
  }
  if (s.startsWith('<!', off)) {
    let p = off + 2;
    if (!(s[p] >= 'A' && s[p] <= 'Z')) return -1;
    while (s[p] >= 'A' && s[p] <= 'Z') p += 1;
    if (s[p] === ' ' || s[p] === '\t') {
      while (p < s.length && s[p] !== '>') p += 1;
    }
    return s[p] === '>' ? p + 1 - off : -1;
  }
  const alphaAt = (idx) => { const c = s[idx]; return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'); };
  const nameAt = (idx) => { const c = s[idx]; return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c === '-'; };
  if (s[off + 1] === '/') {
    let p = off + 2;
    if (!alphaAt(p)) return -1;
    p += 1;
    while (nameAt(p)) p += 1;
    while (s[p] === ' ' || s[p] === '\t') p += 1;
    return s[p] === '>' ? p + 1 - off : -1;
  }
  if (!alphaAt(off + 1)) return -1;
  let p = off + 2;
  while (nameAt(p)) p += 1;
  for (;;) {
    let ws = 0;
    while (p < s.length && (s[p] === ' ' || s[p] === '\t' || s[p] === '\n')) { p += 1; ws += 1; }
    if (s[p] === '>') return p + 1 - off;
    if (s[p] === '/' && s[p + 1] === '>') return p + 2 - off;
    if (ws === 0) return -1;
    const attrStart = s[p];
    if (!((attrStart >= 'A' && attrStart <= 'Z') || (attrStart >= 'a' && attrStart <= 'z') || attrStart === '_' || attrStart === ':')) return -1;
    p += 1;
    for (;;) {
      const c = s[p];
      if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c === '_' || c === '.' || c === ':' || c === '-') { p += 1; continue; }
      break;
    }
    let q = p;
    while (q < s.length && (s[q] === ' ' || s[q] === '\t' || s[q] === '\n')) q += 1;
    if (s[q] === '=') {
      q += 1;
      while (q < s.length && (s[q] === ' ' || s[q] === '\t' || s[q] === '\n')) q += 1;
      const qc = s[q];
      if (qc === '"' || qc === "'") {
        const end = s.indexOf(qc, q + 1);
        if (end === -1) return -1;
        p = end + 1;
      } else {
        const vs = q;
        while (q < s.length && !isWsChar(s[q]) && s[q] !== '"' && s[q] !== "'" && s[q] !== '=' && s[q] !== '<' && s[q] !== '>' && s[q] !== '`') q += 1;
        if (q === vs) return -1;
        p = q;
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
  const beforeGap = p;
  skipWs();
  if (s[p] === ')') return { href: dest.href, title: null, end: p + 1 };
  if (p === beforeGap) return null; // a title needs whitespace before it
  const t = scanTitle(s, p);
  if (!t) return null;
  p = t.end;
  skipWs();
  if (s[p] === ')') return { href: dest.href, title: t.title, end: p + 1 };
  return null;
}

const PUNCT_RE = /[\p{P}\p{S}]/u;
const WS_ASCII_TAB = new Uint8Array(128);
for (const c of [' ', '\t', '\n', '\v', '\f', '\r']) WS_ASCII_TAB[c.charCodeAt(0)] = 1;
const PUNCT_ASCII_TAB = new Uint8Array(128);
for (const c of '!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~') PUNCT_ASCII_TAB[c.charCodeAt(0)] = 1;
function isWsChar(ch) {
  if (ch === undefined) return true;
  const cc = ch.charCodeAt(0);
  return cc < 128 ? WS_ASCII_TAB[cc] === 1 : /\s/.test(ch);
}
function isPunctChar(ch) {
  if (ch === undefined) return false;
  const cc = ch.charCodeAt(0);
  return cc < 128 ? PUNCT_ASCII_TAB[cc] === 1 : PUNCT_RE.test(ch);
}

const TRAILING_PUNCT = new Set(['?', '!', '.', ',', ':', '*', '_', '~', ';']);
const ENTITY_TAIL_RE = /&(?:#\d+|#[Xx][0-9A-Fa-f]+|\w+);$/;

// Cut a bare-autolink run at the start of its final unclosed
// parenthesized group, when that group contains no ')' at all (no
// inner pair ever closed inside it). A group that does close an
// inner pair keeps the whole run.
function cutUnclosedGroup(run) {
  let depth = 0;
  let groupStart = -1;
  let groupHasClose = false;
  for (let i = 0; i < run.length; i += 1) {
    const c = run[i];
    if (c === '(') {
      if (depth === 0) { groupStart = i; groupHasClose = false; }
      depth += 1;
    } else if (c === ')') {
      if (depth > 0) {
        depth -= 1;
        if (depth === 0) groupStart = -1;
        else groupHasClose = true;
      }
    }
  }
  if (groupStart !== -1 && !groupHasClose) return run.slice(0, groupStart);
  return run;
}

function trimAutolink(url) {
  let u = url;
  for (;;) {
    const before = u;
    u = u.replace(ENTITY_TAIL_RE, '');
    while (u.length && TRAILING_PUNCT.has(u[u.length - 1])) u = u.slice(0, -1);
    // A trailing ')' is dropped when it is unmatched, or when the
    // group it closes itself contains a '(' (a nested group).
    while (u.endsWith(')')) {
      let depth = 0;
      let matchPos = -1;
      for (let j = u.length - 2; j >= 0; j -= 1) {
        if (u[j] === ')') depth += 1;
        else if (u[j] === '(') {
          if (depth === 0) { matchPos = j; break; }
          depth -= 1;
        }
      }
      if (matchPos === -1) { u = u.slice(0, -1); continue; }
      if (u.slice(matchPos + 1, -1).includes('(')) { u = u.slice(0, -1); continue; }
      break;
    }
    if (u === before) return u;
  }
}

const EMAIL_LOCAL_TAB = new Uint8Array(128);
for (const c of 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789.!#$%&\'*+/=?^_`{|}~-') EMAIL_LOCAL_TAB[c.charCodeAt(0)] = 1;
const DOMAIN_TAB = new Uint8Array(128);
for (const c of 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_-') DOMAIN_TAB[c.charCodeAt(0)] = 1;
const ALNUM_TAB = new Uint8Array(128);
for (const c of 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789') ALNUM_TAB[c.charCodeAt(0)] = 1;
// Chars that block a bare email when they precede it: the email-local
// set without '_', plus '@' (handled separately by the caller).
const EMAIL_BLOCK_TAB = new Uint8Array(128);
for (const c of 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789.!#$%&\'*+/=?^`{|}~-') EMAIL_BLOCK_TAB[c.charCodeAt(0)] = 1;
function tabAt(tab, s, idx) {
  const cc = s.charCodeAt(idx);
  return cc < 128 && tab[cc] === 1;
}

// Match a bare email address at s[start]: returns its length or 0.
// The domain needs at least one dot, its labels must start and end
// with an alphanumeric, and the address may not be immediately
// followed by another domain-ish character (which would make it a
// longer, invalid address rather than a valid one plus punctuation).
function matchEmailAddress(s, start, delims) {
  let p = start;
  while (p < s.length) {
    const cc = s.charCodeAt(p);
    if (cc >= 128 || EMAIL_LOCAL_TAB[cc] !== 1) break;
    p += 1;
  }
  if (p === start || s[p] !== '@') return 0;
  const domStart = p + 1;
  // Scan the domain as dot-separated labels of [A-Za-z0-9_-].
  const labelEnds = [];
  let q = domStart;
  for (;;) {
    const ls = q;
    while (q < s.length) {
      const cc = s.charCodeAt(q);
      if (cc >= 128 || DOMAIN_TAB[cc] !== 1) break;
      q += 1;
    }
    if (q === ls) break;
    labelEnds.push(q);
    if (s[q] !== '.') break;
    q += 1;
  }
  if (labelEnds.length < 2) return 0;
  const labelOkAt = (a, b) => b - a >= 1 && tabAt(ALNUM_TAB, s, a) && tabAt(ALNUM_TAB, s, b - 1);
  // Candidate domains, longest first: every label-prefix of the full
  // match, and of the full match with trailing [_-] stripped from its
  // last label. A candidate is an end position in s.
  const candEnds = [];
  for (let k = labelEnds.length; k >= 2; k -= 1) candEnds.push(labelEnds[k - 1]);
  const lastEnd = labelEnds[labelEnds.length - 1];
  const lastStart = labelEnds.length >= 2 ? labelEnds[labelEnds.length - 2] + 1 : domStart;
  let trimEnd = lastEnd;
  while (trimEnd > lastStart && (s[trimEnd - 1] === '_' || s[trimEnd - 1] === '-')) trimEnd -= 1;
  if (trimEnd < lastEnd && trimEnd > lastStart) {
    for (let k = labelEnds.length; k >= 2; k -= 1) {
      candEnds.push(k === labelEnds.length ? trimEnd : labelEnds[k - 1]);
    }
  }
  candEnds.sort((a, b) => b - a);
  let underTried = false;
  let prevEnd = -1;
  for (const domEnd of candEnds) {
    if (domEnd === prevEnd) continue;
    prevEnd = domEnd;
    // Validate every label of this candidate.
    let ok = true;
    let ls = domStart;
    for (let k = 0; k < labelEnds.length; k += 1) {
      const le = k === labelEnds.length - 1 && domEnd < labelEnds[k] ? domEnd : labelEnds[k];
      if (le > domEnd) break;
      if (!labelOkAt(ls, le)) { ok = false; break; }
      if (le === domEnd) break;
      ls = labelEnds[k] + 1;
    }
    if (!ok) continue;
    const after = s[domEnd];
    if (after !== undefined && tabAt(DOMAIN_TAB, s, domEnd)) {
      if (!underTried && after === '_' && delims) {
        underTried = true;
        let m = 0;
        while (s[domEnd + m] === '_') m += 1;
        if (m >= 1 && delims.some((e) => e.char === '_' && e.len === m && e.canOpen)) return domEnd - start;
      }
      continue;
    }
    return domEnd - start;
  }
  return 0;
}

// Try a GFM extended autolink at s[i]: returns {raw, href} or null.
// opts.delims: delimiter runs scanned so far (for the __ email rule);
// opts.inBracket: inside an open '[' label, where a bare autolink run
// must stop at a bracket (marked lexes the label atomically).
function matchSchemeAt(s, i) {
  // Returns the length of 'http://', 'https://' or 'ftp://' at s[i]
  // (case-insensitive), or 0.
  const lc = (ch) => (ch >= 'A' && ch <= 'Z' ? ch.toLowerCase() : ch);
  const c0 = s[i];
  if (c0 === 'h' || c0 === 'H') {
    if (lc(s[i + 1]) === 't' && lc(s[i + 2]) === 't' && lc(s[i + 3]) === 'p') {
      if (lc(s[i + 4]) === 's' && s[i + 5] === ':' && s[i + 6] === '/' && s[i + 7] === '/') return 8;
      if (s[i + 4] === ':' && s[i + 5] === '/' && s[i + 6] === '/') return 7;
    }
  } else if (c0 === 'f' || c0 === 'F') {
    if (lc(s[i + 1]) === 't' && lc(s[i + 2]) === 'p' && s[i + 3] === ':' && s[i + 4] === '/' && s[i + 5] === '/') return 6;
  }
  return 0;
}

function scanRunWs(s, from) {
  let j = from;
  while (j < s.length && !isWsChar(s[j]) && s[j] !== '<' && s[j] !== '>') j += 1;
  return j;
}

function capBracketRun(run, inBracket) {
  if (!inBracket) return run;
  const cut = run.search(/[\[\]]/);
  return cut === -1 ? run : run.slice(0, cut);
}

function matchAutolink(s, i, prevCh, delims, inBracket) {
  const pcc = prevCh === undefined ? -1 : prevCh.charCodeAt(0);
  const boundary = prevCh === undefined || (pcc < 128 ? (WS_ASCII_TAB[pcc] === 1 || PUNCT_ASCII_TAB[pcc] === 1) : (isWsChar(prevCh) || isPunctChar(prevCh)));
  if (boundary) {
    const schemeLen = matchSchemeAt(s, i);
    if (schemeLen > 0) {
      const end = scanRunWs(s, i);
      if (end > i + schemeLen) {
        const raw = trimAutolink(cutUnclosedGroup(capBracketRun(s.slice(i, end), inBracket)));
        if (raw.length <= schemeLen) return null;
        return { raw, href: raw };
      }
    }
    if (s.startsWith('www.', i) || s.startsWith('WWW.', i)) {
      if (scanRunWs(s, i) > i + 4) {
        const capped = capBracketRun(s.slice(i, scanRunWs(s, i)), inBracket);
        if (capped.includes('.', 4)) {
          const raw = trimAutolink(cutUnclosedGroup(capped));
          if (raw.length > 4) return { raw, href: 'http://' + raw };
        }
      }
      return null;
    }
    const lcAt = (idx, ch) => { const c = s[idx]; return c === ch || (c >= 'A' && c <= 'Z' && c.toLowerCase() === ch); };
    const schemeMail = (lcAt(i, 'm') && lcAt(i + 1, 'a') && lcAt(i + 2, 'i') && lcAt(i + 3, 'l') && lcAt(i + 4, 't') && lcAt(i + 5, 'o') && s[i + 6] === ':') ? 7
      : (lcAt(i, 'x') && lcAt(i + 1, 'm') && lcAt(i + 2, 'p') && lcAt(i + 3, 'p') && s[i + 4] === ':') ? 5 : 0;
    if (schemeMail > 0) {
      const emLen = matchEmailAddress(s, i + schemeMail, delims);
      if (!emLen) return null;
      let raw = s.slice(i, i + schemeMail + emLen);
      if (schemeMail === 5) {
        let j = i + schemeMail + emLen;
        if (s[j] === '/') {
          j += 1;
          const rs = j;
          while (j < s.length && s[j] !== '/' && !isWsChar(s[j]) && s[j] !== '<' && s[j] !== '>') j += 1;
          if (j > rs) raw += s.slice(rs - 1, j);
        }
      }
      return { raw: trimAutolink(raw), href: raw };
    }
  }
  // A bare email may not be preceded by an email character (it would
  // be the tail of a longer address) — except a '_' run that starts a
  // word, which marked has already claimed as an emphasis delimiter.
  let emailBlocked = (pcc >= 0 && pcc < 128 && EMAIL_BLOCK_TAB[pcc] === 1) || prevCh === '@';
  if (!emailBlocked && prevCh === '_') {
    let j = i - 1;
    while (j >= 0 && s[j] === '_') j -= 1;
    if (j >= 0) {
      const cc = s.charCodeAt(j);
      if (cc < 128 && EMAIL_LOCAL_TAB[cc] === 1) emailBlocked = true;
    }
  }
  if (!emailBlocked) {
    const emLen = matchEmailAddress(s, i, delims);
    if (emLen) {
      const em = s.slice(i, i + emLen);
      return { raw: em, href: 'mailto:' + em };
    }
  }
  return null;
}

// The lengths of the backtick runs in a raw label text, skipping
// backslash-escaped characters.
function backtickRuns(text) {
  const runs = [];
  let i = 0;
  while (i < text.length) {
    if (text[i] === '\\') { i += 2; continue; }
    if (text[i] === '`') {
      let run = 1;
      while (text[i + run] === '`') run += 1;
      runs.push(run);
      i += run;
      continue;
    }
    i += 1;
  }
  return runs;
}

// Whether marked's link extraction accepts a label containing
// backtick runs. Empirically (probed against marked 18.1.3): a label
// is rejected when it contains an odd number of backtick runs and
// either the last run has length 1 or some text follows the last
// run inside the label. A trailing run of length >= 2 at the very
// end of the label is absorbed.
function labelIsValid(label) {
  if (!label.includes('`')) return true;
  const runs = backtickRuns(label);
  if (runs.length % 2 === 0) return true;
  const last = runs[runs.length - 1];
  return last >= 2 && label.endsWith('`');
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
    if (tail && tail.kind === 'text' && !tail.delim && !tail.opener) tail.text += textBuf;
    else appendNode({ kind: 'text', text: textBuf, delim: false });
    textBuf = '';
  };
  const pushRaw = (html) => {
    flushText();
    appendNode({ kind: 'raw', text: html });
  };

  // CommonMark bracket stack: '[' and '![' openers are pushed as literal
  // text nodes first; a ']' tries to form a link/image with the most
  // recent opener. A formed link deactivates all earlier link openers.
  const brackets = [];
  // marked masks the regions between exactly-paired backtick runs
  // over the whole paragraph text (regardless of token boundaries):
  // emphasis/strikethrough delimiters inside such a region are
  // inert. The pairing is greedy: a run opens a region and the next
  // run of exactly the same length closes it.
  const maskRegions = [];
  {
    // Collect the backtick runs first: an opener that finds no
    // exact-length closing run is simply skipped, and pairing resumes
    // at the next run (it does not swallow the rest of the text). A
    // backslash-escaped run can close a pair (marked's span search
    // does not skip escapes) but never open one.
    const runs = [];
    let k = 0;
    while (k < src.length) {
      if (src[k] === '\\') {
        if (src[k + 1] === '`') {
          let run = 1;
          while (src[k + 1 + run] === '`') run += 1;
          runs.push([k + 1, run, true]);
          k += 1 + run;
          continue;
        }
        k += 2;
        continue;
      }
      if (src[k] === '`') {
        let run = 1;
        while (src[k + run] === '`') run += 1;
        runs.push([k, run, false]);
        k += run;
        continue;
      }
      k += 1;
    }
    let ri = 0;
    while (ri < runs.length) {
      if (runs[ri][2]) { ri += 1; continue; }
      const [openPos, openLen] = runs[ri];
      let rj = ri + 1;
      while (rj < runs.length && runs[rj][1] !== openLen) rj += 1;
      if (rj < runs.length) {
        maskRegions.push([openPos, runs[rj][0] + openLen]);
        ri = rj + 1;
      } else {
        ri += 1;
      }
    }
  }
  const inMask = (pos) => {
    for (const [a, b] of maskRegions) {
      if (pos > a && pos < b) return true;
      if (a > pos) break;
    }
    return false;
  };
  const popBracket = () => {
    const popped = brackets.pop();
    if (popped && popped.touched && brackets.length) {
      brackets[brackets.length - 1].lspan = popped.lspan;
      brackets[brackets.length - 1].touched = true;
    }
    return popped;
  };
  // Does the '(' at openIdx start a group that closes (depth returns
  // to 0) somewhere in the rest of the source?
  const parenGroupComplete = (openIdx) => {
    let depth = 1;
    for (let j = openIdx + 1; j < src.length; j += 1) {
      const cj = src[j];
      if (cj === '\\') { j += 1; continue; }
      if (cj === '(') depth += 1;
      else if (cj === ')') {
        depth -= 1;
        if (depth === 0) return true;
      }
    }
    return false;
  };

  const closeBracket = (closeIdx) => {
    if (!brackets.length) return -1;
    const opener = brackets[brackets.length - 1];
    if (!opener.active) {
      popBracket();
      return -1;
    }
    if (!labelIsValid(src.slice(opener.contentStart, closeIdx))) {
      // marked's label extraction rejects this label (see
      // labelIsValid), so the ']' stays literal text. A complete
      // (...)-group after it still mutes the label's emphasis.
      if (src[closeIdx + 1] === '(' && parenGroupComplete(closeIdx + 1)) {
        for (let k = opener.delimIdx; k < delims.length; k += 1) {
          delims[k].canOpen = false;
          delims[k].canClose = false;
        }
      }
      popBracket();
      return -1;
    }
    const label = src.slice(opener.contentStart, closeIdx);
    let href = null;
    let title = null;
    let consumed = -1;
    let refAttempted = false;
    let parenComplete = false;
    if (src[closeIdx + 1] === '(') {
      const pd = parseLinkDest(src, closeIdx + 1);
      if (pd) {
        href = pd.href;
        title = pd.title;
        consumed = pd.end;
      } else {
        // Did the parenthesized group at least close? marked matches
        // the [...](...) shape first and validates the destination
        // second; when validation fails on a complete group, the label
        // renders with its emphasis muted (code spans still form).
        parenComplete = parenGroupComplete(closeIdx + 1);
      }
    }
    if (consumed === -1 && src[closeIdx + 1] === '[') {
      refAttempted = true;
      let refEnd = closeIdx + 2;
      let refLabel = '';
      let ok = true;
      while (refEnd < n && src[refEnd] !== ']') {
        if (src[refEnd] === '[') { ok = false; break; }
        if (src[refEnd] === '\\' && refEnd + 1 < n) { refLabel += src[refEnd] + src[refEnd + 1]; refEnd += 2; continue; }
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
      const def = label.trim() === '' ? undefined : ctx.defs.get(defKey(label));
      if (def) {
        href = def.href;
        title = def.title;
        consumed = closeIdx + 1;
      }
    }
    if (consumed === -1) {
      if (parenComplete) {
        for (let k = opener.delimIdx; k < delims.length; k += 1) {
          delims[k].canOpen = false;
          delims[k].canClose = false;
        }
      }
      popBracket();
      return -1;
    }
    flushText();
    const inside = delims.splice(opener.delimIdx);
    for (const d of inside) d.masked = false;
    processDelims(inside);
    if (!opener.isImage) {
      // Bare autolinks do not form inside link text: unwrap them,
      // including ones nested inside emphasis wraps.
      const unwrap = (nd) => {
        while (nd) {
          if (nd.kind === 'autolink') { nd.kind = 'text'; nd.text = nd.rawText; }
          if (nd.inner) unwrap(nd.inner);
          nd = nd.next;
        }
      };
      unwrap(opener.node.next);
    }
    const innerHead = opener.node.next;
    if (innerHead) innerHead.prev = null;
    if (tail) tail.next = null;
    const before = opener.node.prev;
    if (before) before.next = null;
    else head = null;
    tail = before;
    popBracket();
    const attr = hrefAttr(href);
    if (opener.isImage) {
      const plain = innerHead ? plainTextOfNodes(innerHead) : '';
      appendNode({ kind: 'raw', text: '<img src="' + (attr === null ? '' : attr) + '" alt="' + escapeText(plain) + '"' + (title !== null ? ' title="' + escapeText(title) + '"' : '') + '>', altText: plain });
    } else if (attr === null) {
      if (innerHead) {
        innerHead.prev = tail;
        if (tail) tail.next = innerHead;
        else head = innerHead;
        let last = innerHead;
        while (last.next) last = last.next;
        tail = last;
      }
    } else {
      appendNode({ kind: 'link', hrefAttr: attr, title, inner: innerHead });
      for (const o of brackets) if (!o.isImage) o.active = false;
    }
    return consumed;
  };

  const n = src.length;
  // Run lengths known to have no closing run later in this text: a
  // failed code-span search scans to the end, so any later run of the
  // same length can be emitted as text without searching again.
  const deadRuns = new Set();
  let i = 0;
  while (i < n) {
    const c = src[i];
    if (c === '\\') {
      const nx = src[i + 1];
      if (nx === '\n') {
        pushRaw('<br>');
        i += 2;
        while (src[i] === ' ' || src[i] === '\t') i += 1; // next line's indent is dropped
        continue;
      }
      if (nx !== undefined && ASCII_PUNCT.has(nx)) {
        // An escaped punctuation character is inert: it must not start an
        // entity, a delimiter run or a tag, so it becomes its own node.
        flushText();
        appendNode({ kind: 'raw', text: escapeFull(nx), altText: nx });
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
      const topBr = brackets.length ? brackets[brackets.length - 1] : null;
      const inLabel = topBr !== null && topBr.active;
      // Register this run in the top label's extraction pairing: a
      // run opens a span, and a run of length <= the open run's
      // length closes it. The state decides whether a ']' further
      // along is hidden inside such a span (see closeBracket).
      let lspanAfter = 0;
      if (inLabel) {
        topBr.touched = true;
        if (topBr.lspan === 0) lspanAfter = run;
        else if (run <= topBr.lspan) lspanAfter = 0;
        else lspanAfter = topBr.lspan;
      }
      let j = i + run;
      let found = -1;
      let lstate = lspanAfter;
      if (!deadRuns.has(run)) {
        while (j < n) {
          if (src[j] === '`') {
            let m2 = 1;
            while (src[j + m2] === '`') m2 += 1;
            if (inLabel) {
              if (lstate === 0) lstate = m2;
              else if (m2 <= lstate) lstate = 0;
            }
            if (m2 === run) { found = j; break; }
            j += m2;
          } else if (src[j] === ']' && inLabel && lstate === 0) {
            // The label ends before any span closes: the code span
            // search is confined to the label.
            break;
          } else j += 1;
        }
        if (found === -1 && j >= n) deadRuns.add(run);
      }
      if (found === -1) {
        if (inLabel) topBr.lspan = lspanAfter;
        textBuf += '`'.repeat(run);
        i += run;
        continue;
      }
      if (inLabel) topBr.lspan = lstate;
      let content = src.slice(i + run, found).replace(/\n/g, ' ');
      if (content.length >= 2 && content[0] === ' ' && content[content.length - 1] === ' ' && /[^ ]/.test(content)) {
        content = content.slice(1, -1);
      }
      flushText();
      appendNode({ kind: 'raw', text: '<code>' + escapeFull(content) + '</code>', altText: content });
      i = found + run;
      continue;
    }
    if (c === '<') {
      // Angle autolink with a scheme: <scheme:...>
      {
        let p = i + 1;
        const a0 = src[p];
        if (a0 !== undefined && ((a0 >= 'A' && a0 <= 'Z') || (a0 >= 'a' && a0 <= 'z'))) {
          p += 1;
          const ss = p;
          while (p < n) {
            const c2 = src[p];
            if ((c2 >= 'A' && c2 <= 'Z') || (c2 >= 'a' && c2 <= 'z') || (c2 >= '0' && c2 <= '9') || c2 === '+' || c2 === '.' || c2 === '-') { p += 1; continue; }
            break;
          }
          if (p - ss >= 1 && p - (i + 1) <= 32 && src[p] === ':') {
            let q = p + 1;
            while (q < n && src[q] !== '<' && src[q] !== '>' && !isWsChar(src[q])) q += 1;
            if (src[q] === '>') {
              const text = src.slice(i + 1, q);
              const attr = hrefAttr(text);
              flushText();
              appendNode({ kind: 'raw', text: '<a href="' + (attr === null ? '' : attr) + '">' + escapeFull(text) + '</a>', altText: text });
              i = q + 1;
              continue;
            }
          }
        }
      }
      // Angle autolink with an email address: <user@host.tld>
      {
        let p = i + 1;
        while (p < n && tabAt(EMAIL_LOCAL_TAB, src, p)) p += 1;
        if (p > i + 1 && src[p] === '@') {
          let q = p + 1;
          let dots = 0;
          let ok = true;
          for (;;) {
            const ls = q;
            while (q < n) {
              const c2 = src[q];
              if ((c2 >= 'A' && c2 <= 'Z') || (c2 >= 'a' && c2 <= 'z') || (c2 >= '0' && c2 <= '9') || c2 === '-') { q += 1; continue; }
              break;
            }
            if (q === ls) { ok = false; break; }
            if (src[q] === '.') { dots += 1; q += 1; continue; }
            break;
          }
          if (ok && dots >= 1 && src[q] === '>') {
            const text = src.slice(i + 1, q);
            flushText();
            appendNode({ kind: 'raw', text: '<a href="mailto:' + escapeText(text) + '">' + escapeText(text) + '</a>', altText: text });
            i = q + 1;
            continue;
          }
        }
      }
      const htmlLen = scanInlineHtml(src, i);
      if (htmlLen !== -1) {
        const html = src.slice(i, i + htmlLen);
        pushRaw(html);
        // marked leaks its inLink state across inline runs: an <a …>
        // tag suppresses bare autolinks until an exact </a> appears.
        if (/^<a /i.test(html)) ctx.state.inLink = true;
        else if (/^<\/a>$/i.test(html)) ctx.state.inLink = false;
        i += htmlLen;
        continue;
      }
      textBuf += '<';
      i += 1;
      continue;
    }
    if (c === '[' || (c === '!' && src[i + 1] === '[')) {
      const isImg = c === '!';
      flushText();
      const node = appendNode({ kind: 'text', text: isImg ? '![' : '[', delim: false, opener: true });
      brackets.push({ node, isImage: isImg, contentStart: i + (isImg ? 2 : 1), delimIdx: delims.length, active: true, lspan: 0, touched: false });
      i += isImg ? 2 : 1;
      continue;
    }
    if (c === ']') {
      const ni = closeBracket(i);
      if (ni !== -1) {
        i = ni;
        continue;
      }
      textBuf += ']';
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
      // A run inside a masked backtick region (see maskRegions above)
      // is inert in the paragraph's own delimiter processing — but a
      // link label is lexed by marked on its own, so the flag is
      // cleared for the entries a formed link splices out.
      delims.push({ node, char: c, len: run, fullLen: run, skip: 0, nextCh, canOpen, canClose, dead: 0, pre: 0, done: false, masked: inMask(i) });
      i += run;
      continue;
    }
    if (c === ' ') {
      if (src[i + 1] === ' ') {
        let j = i + 1;
        while (src[j] === ' ') j += 1;
        if (src[j] === '\n') {
          // Two or more spaces before a newline: a hard break, and
          // the next line's leading spaces/tabs are dropped.
          pushRaw('<br>');
          i = j + 1;
          while (src[i] === ' ' || src[i] === '\t') i += 1;
          continue;
        }
        textBuf += src.slice(i, j);
        i = j;
        continue;
      }
      textBuf += ' ';
      i += 1;
      continue;
    }
    if (!inLink && !ctx.state.inLink && tabAt(EMAIL_LOCAL_TAB, src, i)) {
      const prevCh = i > 0 ? src[i - 1] : undefined;
      const al = matchAutolink(src, i, prevCh, delims, brackets.length > 0 && brackets[brackets.length - 1].active);
      if (al) {
        const attr = hrefAttr(al.href);
        flushText();
        appendNode({ kind: 'autolink', text: '<a href="' + (attr === null ? '' : attr) + '">' + escapeFull(al.raw) + '</a>', rawText: al.raw });
        i += al.raw.length;
        continue;
      }
      // No autolink starts here. Consume the following run of plain
      // word characters in bulk: an autolink cannot start inside it,
      // except right after a punctuation character (a scheme, www or
      // mailto start) — the run stops before such a position, and at
      // characters with their own branch above.
      let j = i + 1;
      while (j < n && tabAt(EMAIL_LOCAL_TAB, src, j)) {
        const cj = src[j];
        if (cj === '*' || cj === '_' || cj === '~' || cj === '`') break;
        if ((cj === 'h' || cj === 'H' || cj === 'f' || cj === 'F' || cj === 'w' || cj === 'W' || cj === 'm' || cj === 'M' || cj === 'x' || cj === 'X') && isPunctChar(src[j - 1])) break;
        j += 1;
      }
      textBuf += src.slice(i, j);
      i = j;
      continue;
    }
    // A plain character with no branch of its own: consume a run of
    // such characters at once (not a branch character, and unable to
    // start an autolink).
    {
      let j = i + 1;
      while (j < n) {
        const cc = src.charCodeAt(j);
        if (cc < 128 && EMAIL_LOCAL_TAB[cc] === 1) break;
        const cj = src[j];
        if (cj === '\\' || cj === '<' || cj === '[' || cj === ']' || cj === ' ') break;
        j += 1;
      }
      textBuf += src.slice(i, j);
      i = j;
    }
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
    if (!closer.canClose || closer.len === 0 || closer.dead > 0 || closer.masked) { ci += 1; continue; }
    const key = closer.char + '|' + (closer.len % 3) + '|' + (closer.canOpen ? '1' : '0');
    const bottom = openersBottom.has(key) ? openersBottom.get(key) : -1;
    let oi = -1;
    let blocked = false;
    let glueSeen = false;
    for (let k = ci - 1; k > bottom; k -= 1) {
      const op = delims[k];
      if (op.glue && op.char === closer.char) { glueSeen = true; continue; }
      if (op.dead > 0) {
        // A dead entry: the ghost of a delimiter pair whose closer could
        // also open. A later closer passes it by paying dead-1 stars,
        // provided it can still fully consume the nearest opener below
        // afterwards; otherwise it is blocked and wears the entry down.
        if (op.char !== closer.char) continue;
        let below = null;
        for (let m = k - 1; m > bottom; m -= 1) {
          const q = delims[m];
          if (q.dead === 0 && q.char === closer.char && q.canOpen && q.len > 0 && !q.masked) { below = q; break; }
        }
        let pay = -1;
        if (closer.len > op.dead) pay = op.dead - 1;
        else if (below && below.len <= closer.len && (below.len < closer.len || closer.len < op.dead)) {
          pay = Math.min(op.dead - 1, closer.len - below.len);
        }
        if (pay >= 0) {
          closer.pre += pay;
          closer.len -= pay;
          op.dead = 0;
          continue;
        }
        op.dead -= closer.len;
        blocked = true;
        break;
      }
      if (op.char !== closer.char || !op.canOpen || op.len === 0 || op.masked) continue;
      if (closer.char === '~') {
        if (op.len !== closer.len) continue;
        oi = k;
        break;
      }
      if ((closer.canOpen || op.canClose) && (op.len + closer.len) % 3 === 0 && !(op.len % 3 === 0 && closer.len % 3 === 0)) continue;
      // A strong pair whose closer could also open (against an opener
      // that could not close) poisons a later single-star match across
      // it: marked's scan produces no em there. The search continues
      // past the poisoned opener: a strong match further down still
      // forms.
      if (glueSeen && !(op.len >= 2 && closer.len >= 2)) continue;
      oi = k;
      break;
    }
    if (blocked) {
      closer.canClose = false;
      ci += 1;
      continue;
    }
    if (oi === -1) {
      openersBottom.set(key, ci - 1);
      if (!closer.canOpen) closer.canClose = false;
      ci += 1;
      continue;
    }
    const op = delims[oi];
    const opLenBefore = op.len;
    const closerLenBefore = closer.len + closer.pre;
    const use = closer.char === '~' ? closer.len : (op.len >= 2 && closer.len >= 2 ? 2 : 1);
    op.len -= use;
    closer.len -= use;
    op.node.text = op.node.text.slice(0, op.node.text.length - use);
    if (closer.pre > 0 && use === 2) {
      // Stars spent passing a dead entry render inside a strong wrap;
      // for an em wrap they render after it instead.
      const preNode = { kind: 'text', text: closer.char.repeat(closer.pre), prev: closer.node.prev, next: closer.node };
      if (closer.node.prev) closer.node.prev.next = preNode;
      closer.node.prev = preNode;
    }
    closer.node.text = closer.char.repeat(closer.len + (use === 1 ? closer.pre : 0));
    closer.pre = 0;
    const tag = closer.char === '~' ? 'del' : use === 2 ? 'strong' : 'em';
    wrapNodes(op.node, closer.node, tag);
    if (use === 2 && closer.len === 0 && closer.canOpen && !op.canClose) closer.glue = true;
    if (closer.len === 0 && closer.canOpen && closer.char !== '~' && !op.canClose && use === 1) {
      // A fully consumed single-star closer that could also open,
      // matched against an opener that could not close, leaves a dead
      // entry behind at its position.
      closer.dead = opLenBefore + closerLenBefore;
      closer.canClose = false;
    }
    for (let k = oi + 1; k < ci; k += 1) {
      delims[k].canOpen = false;
      delims[k].canClose = false;
      delims[k].dead = 0;
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

// The plain-text content of a node list, as used for image alt text:
// text is entity-decoded, links and emphasis contribute their contents,
// images contribute their own alt text, code spans their raw content.
function plainTextOfNodes(head) {
  let out = '';
  let node = head;
  while (node) {
    if (node.kind === 'text') out += decodeNumericEntities(node.text);
    else if (node.kind === 'wrap' || node.kind === 'link') out += plainTextOfNodes(node.inner);
    else if (node.kind === 'autolink') out += node.rawText;
    else if (node.kind === 'raw') out += node.altText === undefined ? '' : node.altText;
    node = node.next;
  }
  return out;
}

function renderNodes(head) {
  let out = '';
  let node = head;
  while (node) {
    if (node.kind === 'text') out += escapeTextNode(node.text);
    else if (node.kind === 'raw' || node.kind === 'autolink') out += node.text;
    else if (node.kind === 'link') out += '<a href="' + node.hrefAttr + '"' + (node.title !== null ? ' title="' + escapeText(node.title) + '"' : '') + '>' + renderNodes(node.inner) + '</a>';
    else if (node.kind === 'wrap') out += '<' + node.tag + '>' + renderNodes(node.inner) + '</' + node.tag + '>';
    node = node.next;
  }
  return out;
}
