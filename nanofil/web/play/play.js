// The playground page: send the source to the worker and put each
// section of the article it returns into its place (data-slot).
import { editor, mark, link, count } from "./editor.js";

const $ = (id) => document.getElementById(id);
const worker = new Worker("worker.js");
const fmt = (ms) => (ms < 1000 ? `${ms.toFixed(0)} ms` : `${(ms / 1000).toFixed(2)} s`);
const state = (s) => (document.body.dataset.state = s);

// The source, in a CodeMirror editor (editor/editor.js). Each example
// keeps its own state, so edits survive a look at another; one that
// differs from its file is marked in the menu and can be reverted.
const ed = editor($("code"), { run: () => $("run").disabled || compile(), update: changed, hover: symbol });
const source = ed.view;
const files = new Map(); // name -> the example's text
const states = new Map(); // name -> its editor state
let current = null;

async function open(name) {
  if (!files.has(name)) {
    const text = await (await fetch(`examples/${name}.c`, { cache: "no-cache" })).text();
    files.set(name, text);
    states.set(name, ed.state(text));
  }
  if (current) states.set(current, source.state);
  current = name;
  $("example").value = name;
  source.setState(states.get(name));
  changed();
}

function changed() {
  const doc = source.state.doc;
  const edited = current && doc.toString() !== files.get(current);
  $("revert").hidden = !edited;
  const option = $("example").selectedOptions[0];
  if (option) option.textContent = `${option.value}.c${edited ? " •" : ""}`;
  const head = source.state.selection.main.head;
  const line = doc.lineAt(head);
  $("pos").textContent = `${line.number}:${head - line.from + 1}`;
  follow(line.number);
}

// Questions about the last compile, answered by Prolog in the worker
// (play_view.pl): ask(goal, input) is a promise of the goal's bindings,
// or null if it fails.
const asked = new Map();
let asks = 0;
const ask = (goal, input) =>
  new Promise((resolve) => {
    asked.set(++asks, resolve);
    worker.postMessage({ ask: asks, goal, input });
  });

// The file's top-level items and their lines, from play_outline/1. The
// item the cursor is in is "here" in the C and IR panes, and an item
// under the pointer in either pane tints its lines in the editor.
//
// Without -O the IR's rows carry the line they come from (data-line),
// so the cursor's line is "at" in the IR, a row under the pointer tints
// just its line, and the editor counts each line's instructions.
let outline = [];
let here = null;
let atLine = 0;
const itemAt = (n) => outline.find((o) => o.from <= n && n <= o.to);
function follow(n) {
  if (n !== atLine) {
    atLine = n;
    for (const el of document.querySelectorAll(".goal.at")) el.classList.remove("at");
    for (const el of document.querySelectorAll(`.pane .goal[data-line="${n}"]`)) el.classList.add("at");
    document.querySelector(`[data-slot="${tab}"] .goal[data-line="${n}"]`)?.scrollIntoView({ block: "nearest", behavior: "smooth" });
  }
  const item = itemAt(n) ?? null;
  if (item?.name === here?.name && item?.from === here?.from) return;
  here = item;
  for (const el of document.querySelectorAll(".here")) el.classList.remove("here");
  if (!item) return;
  for (const ir of document.querySelectorAll(`details.clause[data-name="${CSS.escape(item.name)}"]`)) ir.classList.add("here");
  document.querySelector(`[data-slot="c"] [data-line="${item.from}"]`)?.classList.add("here");
  const pane = document.querySelector(`[data-slot="${tab}"] .here`);
  pane?.scrollIntoView({ block: "nearest", behavior: "smooth" });
}
function lines(el) {
  const row = el.closest(".goal[data-line]");
  if (row) return outline.lines?.get(+row.dataset.line);
  const ir = el.closest("details.clause[data-name]");
  if (ir) return outline.find((o) => o.name === ir.dataset.name);
  const c = el.closest(".clause.item[data-line]");
  return c && itemAt(+c.dataset.line);
}
let linkedTo = null;
document.querySelector(".panes").addEventListener("pointerover", (e) => {
  const item = lines(e.target) ?? null;
  if (item === linkedTo) return;
  linkedTo = item;
  link(source, item?.from ?? 0, item?.to ?? 0);
});
document.querySelector(".panes").addEventListener("pointerleave", () => {
  linkedTo = null;
  link(source, 0, 0);
});
// A click on a C item puts the cursor at its start.
document.querySelector('[data-slot="c"]').addEventListener("click", (e) => {
  const c = e.target.closest(".clause.item[data-line]");
  if (!c) return;
  const line = source.state.doc.line(Math.min(+c.dataset.line, source.state.doc.lines));
  source.dispatch({ selection: { anchor: line.from }, scrollIntoView: true });
  source.focus();
});

// What the editor shows over an identifier: play_symbol/2's answer.
async function symbol(name) {
  const r = await ask("play_view:play_symbol(Name, Info)", { Name: name });
  if (!r) return null;
  const i = r.Info;
  const dom = document.createElement("div");
  dom.className = "symbol";
  const facts = [i.kind, i.sig, i.size !== undefined && `${i.size} bytes`, i.linkage,
    i.blocks !== undefined && `${i.blocks} blocks, ${i.insts} instructions`,
    i.calls !== undefined && `${i.calls} call${i.calls === 1 ? "" : "s"}`,
    i.line && `line ${i.line}`].filter(Boolean);
  dom.innerHTML = (i.html ? `<div class="head">${i.html}</div>` : "") + `<div class="facts"></div>`;
  dom.lastChild.textContent = facts.join(" · ");
  return dom;
}

const opened = open(location.hash.slice(1) || "hello").catch(() => open("hello"));
$("example").onchange = async () => {
  await open($("example").value);
  history.replaceState(null, "", "#" + current);
  if (!$("run").disabled) compile();
  source.focus();
};
$("revert").onclick = () => {
  states.set(current, ed.state(files.get(current)));
  source.setState(states.get(current));
  changed();
  if (!$("run").disabled) compile();
  source.focus();
};
if (/Mac|iP(hone|ad)/.test(navigator.platform)) $("keys").textContent = "⌘ ↵";

// -O is the all-passes shortcut. A partial selection is mixed; changing
// either control takes effect on Compile, just as the old -O did.
const passInputs = [...$("passes").querySelectorAll("input")];
$("opt").onchange = () => {
  for (const input of passInputs) input.checked = $("opt").checked;
  $("opt").indeterminate = false;
};
$("passes").onchange = () => {
  const n = passInputs.filter((input) => input.checked).length;
  $("opt").checked = n === passInputs.length;
  $("opt").indeterminate = n > 0 && n < passInputs.length;
};

// Tabs: each pass's output (play_view.pl's pipeline, which replaces the
// bar's buttons on every compile). The one chosen stays chosen across
// compiles; if its pass is no longer selected, the checked IR shows instead.
let tab = "ir";
const tabs = () => $("tabs").querySelectorAll("button[data-tab]");
const has = (name) => document.querySelector(`[data-slot="${name}"]`)?.hasChildNodes();
function show(name) {
  tab = name;
  for (const b of tabs()) b.classList.toggle("selected", b.dataset.tab === name);
  const bar = $("tabs"), sel = bar.querySelector(".selected");
  if (sel) bar.scrollLeft = Math.max(0, sel.offsetLeft - bar.offsetLeft - bar.clientWidth / 2 + sel.offsetWidth / 2);
  for (const p of document.querySelectorAll(".pane")) p.hidden = p.dataset.slot !== name;
}
$("tabs").onclick = (e) => {
  const b = e.target.closest("button[data-tab]");
  if (b && !b.disabled) show(b.dataset.tab);
};
show(tab);
const irTabs = ["lowered", ...passInputs.map((input) => input.value), "ir"];

// A link to an IR item (from Data or Symbols) opens the IR tab there.
document.addEventListener("click", (e) => {
  const a = e.target.closest('a[href^="#ir-"]');
  if (!a) return;
  e.preventDefault();
  if (!irTabs.includes(tab)) show("ir");
  const name = decodeURIComponent(a.hash.slice(4));
  const el = document.querySelector(`[data-slot="${tab}"] details.clause[data-name="${CSS.escape(name)}"]`);
  if (el) {
    el.open = true;
    el.scrollIntoView({ block: "start", behavior: "smooth" });
  }
});

// The IR's words, from the legend over it (play_view.pl's gloss/4): each
// word gets its role's colour and its meaning as hover text, and so does
// an atom whose meaning depends on its place (a class, an op), by the
// word's data-slots. Entries the module does not use are hidden.
function gloss(ir) {
  const words = new Map([...ir.querySelectorAll(".legend .word")].map((w) => [w.dataset.key, w]));
  const used = new Set();
  const note = (el, key, target = el) => {
    const w = words.get(key);
    if (!w) return false;
    target.title = w.dataset.tip;
    target.classList.add("w-" + w.dataset.role);
    used.add(w);
    return true;
  };
  for (const c of ir.querySelectorAll(".c")) {
    const f = c.firstElementChild;
    const args = [...(c.querySelector(":scope > .args")?.children ?? [])].filter((a) => a.matches(".arg"));
    const key = `${f.textContent}/${args.length}`;
    note(f, key, c);
    if (key === "tmp/1") c.dataset.tmp = args[0].textContent;
    for (const s of words.get(key)?.dataset.slots.split(" ").filter(Boolean) ?? []) {
      const [i, kind] = s.split(":");
      const a = args[i - 1]?.firstElementChild;
      if (a?.matches(".a")) note(a, `${kind}:${a.textContent}`) ||
        (kind === "type" && note(a, `class:${a.textContent}`));
    }
  }
  for (const a of ir.querySelectorAll(".goal > .a")) note(a, `${a.textContent}/0`);
  for (const w of words.values()) w.hidden = !used.has(w);
  for (const r of ir.querySelectorAll(".legend .role")) r.hidden = !r.querySelector(".word:not([hidden])");
}
// Hovering a temporary lights up its definition and uses in the function.
document.querySelector(".panes").addEventListener("pointerover", (e) => {
  for (const el of document.querySelectorAll(".c.lit")) el.classList.remove("lit");
  const t = e.target.closest(".c[data-tmp]");
  if (!t) return;
  const fn = t.closest("details.clause") ?? document;
  for (const el of fn.querySelectorAll(`.c[data-tmp="${CSS.escape(t.dataset.tmp)}"]`)) el.classList.add("lit");
});

function compile() {
  $("run").disabled = true;
  state("busy");
  worker.postMessage({ source: source.state.doc.toString(),
    passes: passInputs.filter((input) => input.checked).map((input) => input.value) });
}

worker.onmessage = ({ data }) => {
  $("run").disabled = false;
  if (data.type === "ready") return opened.then(compile);
  if (data.type === "answer") {
    asked.get(data.ask)?.(data.value);
    return asked.delete(data.ask);
  }
  const slots = document.querySelectorAll("[data-slot]");
  for (const s of slots) s.innerHTML = "";
  if (data.type === "result") {
    const article = document.createElement("article");
    article.innerHTML = data.html.replaceAll("/work/input.c:", "line ");
    const failed = article.querySelector("#failure .name")?.textContent;
    mark(source, +(article.querySelector("#failure .why")?.textContent.match(/^line (\d+)/)?.[1] ?? 0));
    for (const sec of article.querySelectorAll("section[id]")) {
      const slot = document.querySelector(`[data-slot="${sec.id}"]`);
      if (slot) slot.append(...sec.childNodes);
    }
    for (const t of irTabs) gloss(document.querySelector(`[data-slot="${t}"]`));
    $("status").textContent = failed ?? fmt(data.ms);
    $("memory").textContent = `${fmt(data.ms)} · ${data.mb.toFixed(0)} MB`;
    for (const b of tabs()) b.disabled = !has(b.dataset.tab);
    show(has(tab) ? tab : has("ir") ? "ir" : [...tabs()].findLast((b) => !b.disabled)?.dataset.tab ?? "c");
    state(failed ? "failed" : "ok");
    Promise.all([ask("play_view:play_outline(O)"), ask("play_view:play_lines(C)")]).then(([r, c]) => {
      outline = r?.O ?? [];
      // One item per line, so the same line is the same object to hover.
      outline.lines = new Map((c?.C ?? []).map((l) => [l.line, { from: l.line, to: l.line }]));
      count(source, c?.C ?? []);
      here = null;
      atLine = 0;
      follow(source.state.doc.lineAt(source.state.selection.main.head).number);
    });
  } else {
    $("status").textContent = "error";
    const pre = document.createElement("pre");
    pre.className = "why";
    pre.textContent = data.message;
    document.querySelector('[data-slot="failure"]').append(pre);
    state("failed");
  }
};

$("form").onsubmit = (e) => {
  e.preventDefault();
  compile();
};
// Ctrl/Cmd+Enter compiles from anywhere on the page, not only the editor.
document.addEventListener("keydown", (e) => {
  if (e.key === "Enter" && (e.ctrlKey || e.metaKey) && !e.defaultPrevented && !$("run").disabled) {
    e.preventDefault();
    compile();
  }
});
