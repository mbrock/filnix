// The playground page: send the source to the worker and put each
// section of the article it returns into its place (data-slot).
import { editor, mark } from "./editor.js";

const $ = (id) => document.getElementById(id);
const worker = new Worker("worker.js");
const fmt = (ms) => (ms < 1000 ? `${ms.toFixed(0)} ms` : `${(ms / 1000).toFixed(2)} s`);
const state = (s) => (document.body.dataset.state = s);

// The source, in a CodeMirror editor (editor/editor.js). Each example
// keeps its own state, so edits survive a look at another; one that
// differs from its file is marked in the menu and can be reverted.
const ed = editor($("code"), () => $("run").disabled || compile(), changed);
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
