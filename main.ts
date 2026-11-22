// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone;
// run it as `node main.ts [options] [PATCH]`. It reads a patch in one of four formats
// (unified diff, SEARCH/REPLACE blocks, V4A, JSON edits), finds the lines each edit names
// at the first of three matching tiers, and writes every change or none.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this
// file hands over to runner.ts (the last lines below): keep that hand-over and runner.ts
// as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';
const blankWs = (s: string): boolean => /^[ \t]*$/.test(s);

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** One file's text as lines: its line break, its lines, whether it ends with a break. */
interface FileState {
  br: string;
  lines: string[];
  final: boolean;
}

function parseFile(text: string): FileState {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { br, lines: parts, final };
}

function renderFile(s: FileState): string {
  if (s.lines.length === 0) return '';
  return s.lines.join(s.br) + (s.final ? s.br : '');
}

function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { old: string; new: string }[] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/* ------------------------------------------------------------------ */
/* Section 5: matching lines at three tiers.                           */
/* ------------------------------------------------------------------ */

function normLine(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

function matchesAt(fileLines: string[], pos: number, oldLines: string[], tier: number): boolean {
  for (let k = 0; k < oldLines.length; k++) {
    if (normLine(fileLines[pos + k]!, tier) !== normLine(oldLines[k]!, tier)) return false;
  }
  return true;
}

function occurrences(fileLines: string[], oldLines: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  for (let i = from; i + oldLines.length <= fileLines.length; i++) {
    if (matchesAt(fileLines, i, oldLines, tier)) out.push(i);
  }
  return out;
}

/** The first tier at which O occurs at or after `from`, with its positions, or null. */
function findTier(fileLines: string[], oldLines: string[], from: number, strict: boolean): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrences(fileLines, oldLines, t, from);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/** The first line at or after `from` equal to a single-line anchor, first tier with one. */
function findSingle(fileLines: string[], anchor: string, from: number, strict: boolean): number | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let i = from; i < fileLines.length; i++) {
      if (normLine(fileLines[i]!, t) === normLine(anchor, t)) return i;
    }
  }
  return null;
}

interface BodyItem {
  kind: ' ' | '-' | '+';
  text: string;
  bs: boolean;
}

/**
 * Build the replacement lines for a matched block. `ctxOfN[j]` is the index into O of
 * the context line N[j] repeats, or -1 for an added line. Context lines are written as
 * the file's own matched lines; at tier 2 every other line is re-indented.
 */
function buildNew(oldLines: string[], newLines: string[], ctxOfN: number[], fileLines: string[], pos: number, tier: number): string[] {
  const out: string[] = [];
  const f = oldLines.length > 0 ? leadingWs(fileLines[pos]!) : '';
  const p = oldLines.length > 0 ? leadingWs(oldLines[0]!) : '';
  for (let j = 0; j < newLines.length; j++) {
    const ci = ctxOfN[j]!;
    if (ci >= 0) {
      out.push(fileLines[pos + ci]!);
      continue;
    }
    let line = newLines[j]!;
    if (tier === 2 && line !== '' && !blankWs(line) && line.startsWith(p)) line = f + line.slice(p.length);
    out.push(line);
  }
  return out;
}

/** Split a hunk/chunk body into its old lines, new lines and context mapping. */
function bodyON(body: BodyItem[]): { oldLines: string[]; newLines: string[]; ctxOfN: number[] } {
  const oldLines: string[] = [];
  const newLines: string[] = [];
  const ctxOfN: number[] = [];
  for (const b of body) {
    if (b.kind === ' ') {
      oldLines.push(b.text);
      ctxOfN.push(oldLines.length - 1);
      newLines.push(b.text);
    } else if (b.kind === '-') {
      oldLines.push(b.text);
    } else {
      ctxOfN.push(-1);
      newLines.push(b.text);
    }
  }
  return { oldLines, newLines, ctxOfN };
}

/** Whether a `\` line follows the hunk's last context or `+` line. */
function lastNoNewline(body: BodyItem[]): boolean {
  for (let k = body.length - 1; k >= 0; k--) {
    const b = body[k]!;
    if (b.kind === ' ' || b.kind === '+') return b.bs;
  }
  return false;
}

/* ------------------------------------------------------------------ */
/* Section 4: detecting the format. Section 9: JSON edits.            */
/* ------------------------------------------------------------------ */

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ------------------------------------------------------------------ */
/* Section 6: unified diffs.                                           */
/* ------------------------------------------------------------------ */

interface Hunk {
  a: number;
  body: BodyItem[];
}

interface USection {
  pairOld: string | null | undefined;
  pairNew: string | null | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  diffOld: string | undefined;
  diffNew: string | undefined;
  isCreate: boolean;
  isDelete: boolean;
  hunks: Hunk[];
}

/** A `--- ` / `+++ ` path: text after the four characters, up to the first tab, trimmed. */
function parseDiffPath(line: string): string | null {
  let p = line.slice(4).split('\t')[0]!.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/')) p = p.slice(2);
  else if (p.startsWith('b/')) p = p.slice(2);
  return p;
}

const HUNK_HEAD = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;

/** Parse one hunk starting at lines[i] (an `@@` line); returns it and the next line index. */
function parseHunk(lines: string[], i: number): { hunk: Hunk; next: number } {
  const m = HUNK_HEAD.exec(lines[i]!);
  if (!m) throw new Exit2(`error: parse ${i + 1}`);
  const a = Number(m[1]);
  let j = i + 1;
  const raw: string[] = [];
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\')) {
      raw.push(l);
      j++;
      continue;
    }
    break;
  }
  while (raw.length > 0 && raw[raw.length - 1] === '') raw.pop();
  const body: BodyItem[] = [];
  for (const l of raw) {
    if (l.startsWith('\\')) {
      if (body.length > 0) body[body.length - 1]!.bs = true;
      continue;
    }
    body.push({ kind: l === '' ? ' ' : (l[0] as ' ' | '-' | '+'), text: l === '' ? '' : l.slice(1), bs: false });
  }
  return { hunk: { a, body }, next: j };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: USection[] = [];
  const fresh = (): USection => ({
    pairOld: undefined,
    pairNew: undefined,
    renameFrom: undefined,
    renameTo: undefined,
    diffOld: undefined,
    diffNew: undefined,
    isCreate: false,
    isDelete: false,
    hunks: [],
  });
  let cur: USection | null = null;
  let inHeader = false;
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)\s*$/.exec(l);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = fresh();
      cur.diffOld = m[1]!;
      cur.diffNew = m[2]!;
      sections.push(cur);
      inHeader = true;
      i++;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const oldP = parseDiffPath(l);
      const newP = parseDiffPath(lines[i + 1]!);
      if (cur !== null && inHeader && cur.pairOld === undefined) {
        cur.pairOld = oldP;
        cur.pairNew = newP;
      } else {
        cur = fresh();
        cur.pairOld = oldP;
        cur.pairNew = newP;
        sections.push(cur);
        inHeader = true;
      }
      i += 2;
      continue;
    }
    if (l.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const { hunk, next } = parseHunk(lines, i);
      cur.hunks.push(hunk);
      inHeader = false;
      i = next;
      continue;
    }
    if (l.startsWith('--- ')) {
      if (cur !== null && inHeader) throw new Exit2(`error: parse ${i + 2}`);
      i++;
      continue;
    }
    if (cur !== null && inHeader) {
      if (l.startsWith('+++ ')) {
        if (cur.pairNew === undefined) cur.pairNew = parseDiffPath(l);
        i++;
        continue;
      }
      if (l.startsWith('rename from ')) {
        if (cur.renameFrom === undefined) cur.renameFrom = l.slice(12).trim();
        i++;
        continue;
      }
      if (l.startsWith('rename to ')) {
        if (cur.renameTo === undefined) cur.renameTo = l.slice(10).trim();
        i++;
        continue;
      }
      if (l.startsWith('new file mode')) {
        cur.isCreate = true;
        i++;
        continue;
      }
      if (l.startsWith('deleted file mode')) {
        cur.isDelete = true;
        i++;
        continue;
      }
      i++;
      continue;
    }
    i++;
  }
  return sections.map((sec) => unifiedSectionEdit(sec, strict));
}

/** Apply a section's hunks in order to a file's text. */
function applyUnifiedHunks(before: string, hunks: Hunk[], strict: boolean, path: string): string {
  const st = parseFile(before);
  let d = 0;
  for (const h of hunks) {
    const { oldLines, newLines, ctxOfN } = bodyON(h.body);
    const noNl = lastNoNewline(h.body);
    if (oldLines.length === 0) {
      const at = Math.min(h.a + d, st.lines.length);
      const atEnd = at === st.lines.length;
      st.lines.splice(at, 0, ...newLines);
      if (atEnd) st.final = !noNl;
    } else {
      const found = findTier(st.lines, oldLines, 0, strict);
      if (!found) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let best = found.occ[0]!;
      for (const pos of found.occ) {
        if (Math.abs(pos - target) < Math.abs(best - target)) best = pos;
      }
      const atEnd = best + oldLines.length === st.lines.length;
      const built = buildNew(oldLines, newLines, ctxOfN, st.lines, best, found.tier);
      st.lines.splice(best, oldLines.length, ...built);
      if (atEnd) st.final = !noNl;
    }
    d += newLines.length - oldLines.length;
  }
  return renderFile(st);
}

function unifiedSectionEdit(sec: USection, strict: boolean): Edit {
  const oldP = sec.pairOld !== undefined ? sec.pairOld : (sec.renameFrom ?? sec.diffOld ?? null);
  const newP = sec.pairNew !== undefined ? sec.pairNew : (sec.renameTo ?? sec.diffNew ?? null);
  const isCreate = oldP === null || sec.isCreate;
  const isDelete = newP === null || sec.isDelete;
  if (isCreate) {
    const p = newP ?? '';
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      const plus: { text: string; bs: boolean }[] = [];
      for (const h of sec.hunks) for (const b of h.body) if (b.kind === '+') plus.push({ text: b.text, bs: b.bs });
      const content = plus.length === 0 ? '' : plus.map((x) => x.text).join('\n') + (plus[plus.length - 1]!.bs ? '' : '\n');
      tree.now.set(p, content);
    };
  }
  if (isDelete) {
    const p = oldP ?? '';
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
    };
  }
  if (oldP !== newP) {
    const from = oldP ?? '';
    const to = newP ?? '';
    return (tree) => {
      if (!safe(from)) throw new Fail('unsafe', from);
      if (!safe(to)) throw new Fail('unsafe', to);
      const before = tree.get(from);
      if (before === null) throw new Fail('missing', from);
      if (tree.get(to) !== null) throw new Fail('exists', to);
      const out = applyUnifiedHunks(before, sec.hunks, strict, from);
      tree.now.set(from, null);
      tree.now.set(to, out);
      tree.moves.push({ old: from, new: to });
    };
  }
  const p = oldP ?? '';
  return (tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const before = tree.get(p);
    if (before === null) throw new Fail('missing', p);
    tree.now.set(p, applyUnifiedHunks(before, sec.hunks, strict, p));
  };
}

/* ------------------------------------------------------------------ */
/* Section 7: SEARCH/REPLACE blocks.                                   */
/* ------------------------------------------------------------------ */

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let i = 0;
  let prevEnd = 0;
  let prevPath: string | null = null;
  while (i < lines.length) {
    let s = -1;
    for (let j = i; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') {
        s = j;
        break;
      }
    }
    if (s === -1) break;
    let path: string | null = null;
    for (let j = s - 1; j >= prevEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '') continue;
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${s + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = s + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq === -1) throw new Exit2(`error: parse ${s + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep === -1) throw new Exit2(`error: parse ${s + 1}`);
    const oldLines = lines.slice(s + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(searchReplaceEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return edits;
}

function searchReplaceEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const st = parseFile(before);
    const found = findTier(st.lines, oldLines, 0, strict);
    if (!found) throw new Fail('no-match', path);
    if (found.occ.length > 1) throw new Fail('ambiguous', path);
    const pos = found.occ[0]!;
    const built = buildNew(oldLines, newLines, newLines.map(() => -1), st.lines, pos, found.tier);
    st.lines.splice(pos, oldLines.length, ...built);
    tree.now.set(path, renderFile(st));
  };
}

/* ------------------------------------------------------------------ */
/* Section 8: V4A patches.                                             */
/* ------------------------------------------------------------------ */

interface VChunk {
  anchor: string;
  eof: boolean;
  body: BodyItem[];
}

interface VRaw {
  text: string;
  no: number;
}

const V_ADD = '*** Add File: ';
const V_DEL = '*** Delete File: ';
const V_UPD = '*** Update File: ';
const V_MOVE = '*** Move to: ';

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    if (blank(lines[i]!)) {
      i++;
      continue;
    }
    const l = lines[i]!;
    let kind: 'add' | 'delete' | 'update';
    let path: string;
    if (l.startsWith(V_ADD)) {
      kind = 'add';
      path = l.slice(V_ADD.length).trim();
    } else if (l.startsWith(V_DEL)) {
      kind = 'delete';
      path = l.slice(V_DEL.length).trim();
    } else if (l.startsWith(V_UPD)) {
      kind = 'update';
      path = l.slice(V_UPD.length).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const headerLine = i + 1;
    let j = i + 1;
    while (j < last) {
      const lj = lines[j]!;
      if (lj.startsWith(V_ADD) || lj.startsWith(V_DEL) || lj.startsWith(V_UPD)) break;
      j++;
    }
    const raw: VRaw[] = [];
    for (let k = i + 1; k < j; k++) raw.push({ text: lines[k]!, no: k + 1 });
    while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
    edits.push(v4aSectionEdit(kind, path, raw, headerLine, strict));
    i = j;
  }
  return edits;
}

function v4aSectionEdit(kind: 'add' | 'delete' | 'update', path: string, raw: VRaw[], headerLine: number, strict: boolean): Edit {
  if (kind === 'add') {
    const fileLines: string[] = [];
    for (const r of raw) {
      if (r.text === '') fileLines.push('');
      else if (r.text.startsWith('+')) fileLines.push(r.text.slice(1));
      else throw new Exit2(`error: parse ${r.no}`);
    }
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
    };
  }
  if (kind === 'delete') {
    for (const r of raw) throw new Exit2(`error: parse ${r.no}`);
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) === null) throw new Fail('missing', path);
      tree.now.set(path, null);
    };
  }
  let moveTo: string | null = null;
  let k = 0;
  if (k < raw.length && raw[k]!.text.startsWith(V_MOVE)) {
    moveTo = raw[k]!.text.slice(V_MOVE.length).trim();
    k++;
  }
  const chunks: VChunk[] = [];
  let cur: VChunk | null = null;
  for (; k < raw.length; k++) {
    const r = raw[k]!;
    const t = r.text;
    if (t.startsWith('@@')) {
      if (cur !== null) chunks.push(cur);
      cur = { anchor: t.slice(2).trim(), eof: false, body: [] };
    } else if (t === '*** End of File') {
      if (cur === null) cur = { anchor: '', eof: false, body: [] };
      cur.eof = true;
      chunks.push(cur);
      cur = null;
    } else if (t === '' || t.startsWith(' ') || t.startsWith('-') || t.startsWith('+')) {
      if (cur === null) cur = { anchor: '', eof: false, body: [] };
      cur.body.push({ kind: t === '' ? ' ' : (t[0] as ' ' | '-' | '+'), text: t === '' ? '' : t.slice(1), bs: false });
    } else {
      throw new Exit2(`error: parse ${r.no}`);
    }
  }
  if (cur !== null) chunks.push(cur);
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${headerLine}`);
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const st = parseFile(before);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== '') {
        const at = findSingle(st.lines, ch.anchor, cursor, strict);
        if (at === null) throw new Fail('no-match', path);
        cursor = at + 1;
      }
      const { oldLines, newLines, ctxOfN } = bodyON(ch.body);
      if (oldLines.length === 0) {
        const at = ch.eof ? st.lines.length : cursor;
        st.lines.splice(at, 0, ...newLines);
        cursor = at + newLines.length;
      } else {
        const found = findTier(st.lines, oldLines, cursor, strict);
        if (!found) throw new Fail('no-match', path);
        let occ = found.occ;
        if (ch.eof) occ = occ.filter((p) => p + oldLines.length === st.lines.length);
        if (occ.length === 0) throw new Fail('no-match', path);
        const pos = occ[0]!;
        const built = buildNew(oldLines, newLines, ctxOfN, st.lines, pos, found.tier);
        st.lines.splice(pos, oldLines.length, ...built);
        cursor = pos + built.length;
      }
    }
    const out = renderFile(st);
    if (moveTo !== null) {
      tree.now.set(path, null);
      tree.now.set(moveTo, out);
      tree.moves.push({ old: path, new: moveTo });
    } else {
      tree.now.set(path, out);
    }
  };
}

/* ------------------------------------------------------------------ */
/* Sections 1, 2 and 10: invocation, output, order and atomicity.      */
/* ------------------------------------------------------------------ */

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // A move that succeeded reports as one R line, sorted by its new path, replacing
  // that pair's D and A lines; every other change reports by its own path.
  const rByNew = new Map<string, string>();
  for (const mv of tree.moves) {
    if (tree.original(mv.old) !== null && tree.now.get(mv.old) === null && tree.original(mv.new) === null && tree.now.get(mv.new) !== null) {
      rByNew.set(mv.new, mv.old);
    }
  }
  const movedOlds = new Set(rByNew.values());
  const rows: { key: string; line: string }[] = [];
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (rByNew.has(p)) {
      rows.push({ key: p, line: `R ${rByNew.get(p)} -> ${p}` });
      continue;
    }
    if (movedOlds.has(p)) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  const out = rows.map((r) => r.line);
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
