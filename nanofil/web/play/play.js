// The playground page: send the source to the worker and put each
// section of the article it returns into its place (data-slot).
import { editor, mark } from "./editor.js";

const $ = (id) => document.getElementById(id);
const worker = new Worker("worker.js");
const fmt = (ms) => (ms < 1000 ? `${ms.toFixed(0)} ms` : `${(ms / 1000).toFixed(2)} s`);
const state = (s) => (document.body.dataset.state = s);

// The source, in a CodeMirror editor (editor/editor.js) that takes the
// textarea's place and text; a failure's line is marked in it.
const textarea = $("source");
const source = editor(textarea.parentNode, textarea.value, () => $("run").disabled || compile());
textarea.remove();

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
  if (data.type === "ready") return compile();
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
