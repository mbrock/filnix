// The playground's source editor: CodeMirror 6 with C highlighting in
// the wiki's and dterm's colours. default.nix bundles this into the
// page's editor.js.
import { EditorState, StateEffect, StateField, RangeSet } from "@codemirror/state";
import { EditorView, Decoration, GutterMarker, keymap, lineNumbers, gutterLineClass, gutter, drawSelection, hoverTooltip } from "@codemirror/view";
import { defaultKeymap, history, historyKeymap, indentWithTab } from "@codemirror/commands";
import { StreamLanguage, HighlightStyle, syntaxHighlighting, bracketMatching, indentOnInput, indentUnit } from "@codemirror/language";
import { c } from "@codemirror/legacy-modes/mode/clike";
import { tags as t } from "@lezer/highlight";

// The line a failure names, as its start, kept in place as the text
// changes; null when there is none.
const setBad = StateEffect.define();
const badMarker = new (class extends GutterMarker { elementClass = "cm-bad"; })();
const badLine = Decoration.line({ class: "cm-bad" });
const bad = StateField.define({
  create: () => null,
  update(pos, tr) {
    for (const e of tr.effects) if (e.is(setBad)) return e.value;
    return pos === null ? null : tr.changes.mapPos(pos);
  },
  provide: (f) => [
    EditorView.decorations.from(f, (pos) => (pos === null ? Decoration.none : Decoration.set(badLine.range(pos)))),
    gutterLineClass.from(f, (pos) => (pos === null ? RangeSet.empty : RangeSet.of(badMarker.range(pos)))),
  ],
});

// The lines something outside the editor stands for (an IR function
// under the pointer), tinted.
const setLinked = StateEffect.define();
const linkedLine = Decoration.line({ class: "cm-linked" });
const linked = StateField.define({
  create: () => Decoration.none,
  update(d, tr) {
    for (const e of tr.effects) if (e.is(setLinked)) return e.value;
    return d.map(tr.changes);
  },
  provide: (f) => EditorView.decorations.from(f),
});

// How many IR instructions each line made, in a gutter of its own.
class Count extends GutterMarker {
  constructor(n) { super(); this.n = n; }
  eq(o) { return o.n === this.n; }
  toDOM() { return document.createTextNode(String(this.n)); }
}
const setCounts = StateEffect.define();
const counts = StateField.define({
  create: () => RangeSet.empty,
  update(set, tr) {
    for (const e of tr.effects) if (e.is(setCounts)) return e.value;
    return set.map(tr.changes);
  },
});
const countGutter = gutter({ class: "cm-counts", markers: (v) => v.state.field(counts) });

const colours = HighlightStyle.define([
  { tag: [t.keyword, t.controlKeyword, t.modifier], color: "var(--call)" },
  { tag: [t.typeName, t.standard(t.name)], color: "var(--atom)" },
  { tag: [t.string, t.character], color: "var(--str)" },
  { tag: [t.number, t.atom, t.bool], color: "var(--num)" },
  { tag: t.meta, color: "var(--var)" },
  { tag: t.comment, color: "var(--note)" },
]);

const theme = EditorView.theme({
  "&": { height: "100%", color: "var(--ink)", background: "none" },
  "&.cm-focused": { outline: "none" },
  ".cm-scroller": { font: "0.8rem/1.55 var(--mono-font)" },
  ".cm-content": { padding: "0.4rem 0", caretColor: "var(--ink)" },
  ".cm-line": { padding: "0 0.6rem 0 0.1rem" },
  ".cm-cursor": { borderLeftColor: "var(--ink)" },
  "&.cm-focused > .cm-scroller > .cm-selectionLayer .cm-selectionBackground, .cm-selectionBackground":
    { background: "color-mix(in srgb, var(--accent) 16%, transparent)" },
  ".cm-gutters": { background: "var(--code-bg)", border: "0", color: "color-mix(in srgb, var(--muted) 70%, transparent)" },
  ".cm-lineNumbers .cm-gutterElement": { padding: "0 0.6em 0 0.5em", minWidth: "1.6em" },
  ".cm-gutterElement.cm-bad": { color: "var(--accent)", fontWeight: "700" },
  ".cm-line.cm-bad": { background: "color-mix(in srgb, var(--accent) 9%, transparent)" },
  "&.cm-focused .cm-matchingBracket": { background: "color-mix(in srgb, var(--accent) 14%, transparent)" },
  ".cm-nonmatchingBracket": { color: "var(--accent)" },
  ".cm-counts .cm-gutterElement": { padding: "0 0.3em 0 0.1em", minWidth: "1.4em", textAlign: "right", fontSize: "0.85em", color: "color-mix(in srgb, var(--atom) 55%, transparent)" },
  ".cm-line.cm-linked": { background: "color-mix(in srgb, var(--atom) 9%, transparent)" },
  ".cm-tooltip": {
    border: "1px solid var(--rule)",
    borderRadius: "4px",
    background: "var(--paper)",
    boxShadow: "0 6px 18px rgb(0 0 0 / 0.08)",
  },
});

// editor(parent, {run, update, hover}): an empty editor in parent; Ctrl
// or Cmd+Enter calls run, and every update (an edit, a move of the
// cursor) update. hover(word) answers, with a promise of an element or
// null, what to show over an identifier the pointer rests on. Returns
// {view, state}: state(doc) makes a fresh state holding doc, for
// view.setState, so each example keeps its own text and history.
export function editor(parent, { run, update, hover }) {
  const extensions = [
    lineNumbers(),
    counts,
    countGutter,
    history(),
    drawSelection(),
    indentOnInput(),
    bracketMatching(),
    indentUnit.of("    "),
    StreamLanguage.define(c),
    syntaxHighlighting(colours),
    keymap.of([{ key: "Mod-Enter", run: () => (run(), true) }, ...defaultKeymap, ...historyKeymap, indentWithTab]),
    bad,
    linked,
    theme,
    EditorView.contentAttributes.of({ "aria-label": "C source" }),
    EditorView.updateListener.of(update),
    hoverTooltip(async (view, pos) => {
      const word = view.state.wordAt(pos);
      const dom = word && (await hover(view.state.sliceDoc(word.from, word.to)));
      return dom ? { pos: word.from, end: word.to, above: true, create: () => ({ dom }) } : null;
    }, { hoverTime: 250 }),
  ];
  const state = (doc) => EditorState.create({ doc, extensions });
  return { view: new EditorView({ parent, state: state("") }), state };
}

// link(view, from, to): tint lines from..to (1-based), or none if from is 0.
export function link(view, from, to) {
  const doc = view.state.doc;
  const lines = [];
  for (let n = Math.max(from, 1); from && n <= Math.min(to, doc.lines); n++) lines.push(linkedLine.range(doc.line(n).from));
  view.dispatch({ effects: setLinked.of(Decoration.set(lines)) });
}

// count(view, lines): show lines' instruction counts, lines a list of
// {line, n}; an empty list clears them.
export function count(view, lines) {
  const doc = view.state.doc;
  const marks = lines.filter((c) => c.line >= 1 && c.line <= doc.lines).map((c) => new Count(c.n).range(doc.line(c.line).from));
  view.dispatch({ effects: setCounts.of(RangeSet.of(marks, true)) });
}

// mark(view, n): mark line n (1-based), or none if n is 0 or past the end.
export function mark(view, n) {
  const doc = view.state.doc;
  view.dispatch({ effects: setBad.of(n >= 1 && n <= doc.lines ? doc.line(n).from : null) });
}
