// The playground's source editor: CodeMirror 6 with C highlighting in
// the wiki's and dterm's colours. default.nix bundles this into the
// page's editor.js.
import { EditorState, StateEffect, StateField, RangeSet } from "@codemirror/state";
import { EditorView, Decoration, GutterMarker, keymap, lineNumbers, gutterLineClass, drawSelection } from "@codemirror/view";
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

const colours = HighlightStyle.define([
  { tag: [t.keyword, t.controlKeyword, t.modifier], color: "var(--call)" },
  { tag: [t.typeName, t.standard(t.name)], color: "var(--atom)" },
  { tag: [t.string, t.character], color: "var(--str)" },
  { tag: [t.number, t.atom, t.bool], color: "var(--num)" },
  { tag: t.meta, color: "var(--var)" },
  { tag: t.comment, color: "var(--note)", fontStyle: "italic" },
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
});

// editor(parent, run, update): an empty editor in parent; Ctrl or
// Cmd+Enter calls run, and every update (an edit, a move of the cursor)
// update. Returns {view, state}: state(doc) makes a fresh state holding
// doc, for view.setState, so each example keeps its own text and history.
export function editor(parent, run, update) {
  const extensions = [
    lineNumbers(),
    history(),
    drawSelection(),
    indentOnInput(),
    bracketMatching(),
    indentUnit.of("    "),
    StreamLanguage.define(c),
    syntaxHighlighting(colours),
    keymap.of([{ key: "Mod-Enter", run: () => (run(), true) }, ...defaultKeymap, ...historyKeymap, indentWithTab]),
    bad,
    theme,
    EditorView.contentAttributes.of({ "aria-label": "C source" }),
    EditorView.updateListener.of(update),
  ];
  const state = (doc) => EditorState.create({ doc, extensions });
  return { view: new EditorView({ parent, state: state("") }), state };
}

// mark(view, n): mark line n (1-based), or none if n is 0 or past the end.
export function mark(view, n) {
  const doc = view.state.doc;
  view.dispatch({ effects: setBad.of(n >= 1 && n <= doc.lines ? doc.line(n).from : null) });
}
