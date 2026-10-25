// The shared IR interaction contract, without browser/runtime dependencies.
// Browser layout and source-editor interactions are checked separately.
import test from "node:test";
import assert from "node:assert/strict";
import { gloss, highlightValues } from "./ir.js";

function value(raw) {
  const classes = new Set();
  return {
    dataset: { tmp: raw }, title: "IR class: w · C expression type: int",
    // Subscripts and pretty source names must never be read as identities.
    get textContent() { throw new Error("display text is not an identity"); },
    classList: { add: (c) => classes.add(c), remove: (c) => classes.delete(c) },
    classes,
  };
}

function interaction(scopes) {
  const handlers = new Map(), all = scopes.flat();
  for (const values of scopes) {
    const scope = { querySelectorAll: () => values };
    for (const v of values) v.closest = () => scope;
  }
  const root = {
    querySelectorAll: () => all.filter((v) => v.classes.has("lit")),
    addEventListener: (event, fn) => handlers.set(event, fn),
  };
  highlightValues(root);
  return {
    over: (v) => handlers.get("pointerover")({ target: { closest: () => v } }),
    leave: () => handlers.get("pointerleave")(),
  };
}

test("hover follows raw identity, including unusual and generated names", () => {
  const definition = value('pr.1"'), use = value('pr.1"'), other = value("pr.2");
  const ui = interaction([[definition, use, other]]);
  ui.over(use);
  assert.ok(definition.classes.has("lit"));
  assert.ok(use.classes.has("lit"));
  assert.ok(!other.classes.has("lit"));
});

test("identities are scoped to one function/stage and clear on leave", () => {
  const a = value("v0"), b = value("v0");
  const ui = interaction([[a], [b]]);
  ui.over(a);
  assert.ok(a.classes.has("lit"));
  assert.ok(!b.classes.has("lit"));
  ui.over(b);
  assert.ok(!a.classes.has("lit"));
  assert.ok(b.classes.has("lit"));
  ui.leave();
  assert.ok(!b.classes.has("lit"));
});

test("gloss preserves provenance tooltip and raw identity", () => {
  const v = value("v91");
  const word = { dataset: { key: "tmp/1", role: "value", tip: "generic temporary" } };
  const unused = { dataset: { key: "load/1", role: "memory", tip: "read" } };
  const root = {
    querySelectorAll: (selector) => {
      if (selector === ".legend .word") return [word, unused];
      if (selector === "[data-tmp]") return [v];
      return [];
    },
  };
  gloss(root);
  assert.equal(v.dataset.tmp, "v91");
  assert.equal(v.title, "IR class: w · C expression type: int");
  assert.ok(v.classes.has("w-value"));
  assert.equal(word.hidden, false);
  assert.equal(unused.hidden, true);
});
