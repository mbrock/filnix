// The playground page: send the source to the worker and put each
// section of the article it returns into its place (data-slot).
import { editor, mark, link } from "./editor.js";

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
    const text = await (await fetch(`examples/${name}.c`)).text();
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
let outline = [];
let here = null;
const itemAt = (n) => outline.find((o) => o.from <= n && n <= o.to);
function follow(n) {
  const item = itemAt(n) ?? null;
  if (item?.name === here?.name && item?.from === here?.from) return;
  here = item;
  for (const el of document.querySelectorAll(".here")) el.classList.remove("here");
  if (!item) return;
  const ir = document.getElementById("ir-" + item.name);
  ir?.classList.add("here");
  document.querySelector(`[data-slot="c"] [data-line="${item.from}"]`)?.classList.add("here");
  const pane = document.querySelector(`[data-slot="${tab}"] .here`);
  pane?.scrollIntoView({ block: "nearest", behavior: "smooth" });
}
function lines(el) {
  const ir = el.closest('details.clause[id^="ir-"]');
  if (ir) return outline.find((o) => "ir-" + o.name === ir.id);
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

// Tabs: the one chosen stays chosen across compiles.
let tab = "ir";
function show(name) {
  tab = name;
  for (const b of $("tabs").children) b.classList.toggle("selected", b.dataset.tab === name);
  for (const p of document.querySelectorAll(".pane")) p.hidden = p.dataset.slot !== name;
}
$("tabs").onclick = (e) => e.target.dataset.tab && show(e.target.dataset.tab);
show(tab);

// A link to an IR item (from Data or Symbols) opens the IR tab there.
document.addEventListener("click", (e) => {
  const a = e.target.closest('a[href^="#ir-"]');
  if (!a) return;
  e.preventDefault();
  show("ir");
  const el = document.getElementById(decodeURIComponent(a.hash.slice(1)));
  if (el) {
    el.open = true;
    el.scrollIntoView({ block: "start", behavior: "smooth" });
  }
});

function compile() {
  $("run").disabled = true;
  state("busy");
  worker.postMessage({ source: source.state.doc.toString(), opt: $("opt").checked ? "o1" : "o0" });
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
    $("status").textContent = failed ?? fmt(data.ms);
    $("memory").textContent = `${fmt(data.ms)} · ${data.mb.toFixed(0)} MB`;
    for (const b of $("tabs").children)
      b.disabled = !document.querySelector(`[data-slot="${b.dataset.tab}"]`).hasChildNodes();
    state(failed ? "failed" : "ok");
    ask("play_view:play_outline(O)").then((r) => {
      outline = r?.O ?? [];
      here = null;
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
