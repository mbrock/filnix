// The playground page: send the source to the worker, show its article.
const $ = (id) => document.getElementById(id);
const worker = new Worker("worker.js");
const status = (text, bad = false) => {
  $("status").textContent = text;
  $("status").classList.toggle("bad", bad);
};
const fmt = (ms) => (ms < 1000 ? `${ms.toFixed(0)} ms` : `${(ms / 1000).toFixed(2)} s`);

function compile() {
  $("run").disabled = true;
  status("compiling");
  worker.postMessage({ source: $("source").value, opt: $("opt").checked ? "o1" : "o0" });
}

worker.onmessage = ({ data }) => {
  $("run").disabled = false;
  if (data.type === "ready") {
    compile();
  } else if (data.type === "result") {
    $("out").innerHTML = data.html;
    const bad = $("out").querySelector(".stages .bad .name");
    status(`${bad ? bad.textContent + " failed · " : ""}${fmt(data.ms)} · ${data.mb.toFixed(0)} MB`, !!bad);
    $("sections").innerHTML =
      "<ul>" +
      [...$("out").querySelectorAll("section[id]")]
        .map((s) => `<li><a href="#${s.id}">${s.querySelector("h2").textContent}</a></li>`)
        .join("") +
      "</ul>";
  } else {
    status("error", true);
    $("out").innerHTML = "";
    const pre = document.createElement("pre");
    pre.className = "error";
    pre.textContent = data.message;
    $("out").append(pre);
  }
};

$("form").onsubmit = (e) => {
  e.preventDefault();
  compile();
};
$("source").onkeydown = (e) => {
  if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) {
    e.preventDefault();
    if (!$("run").disabled) compile();
  }
};
