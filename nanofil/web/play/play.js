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
  status("Compiling…");
  worker.postMessage({ source: $("source").value, opt: $("opt").checked ? "o1" : "o0" });
}

worker.onmessage = ({ data }) => {
  $("run").disabled = false;
  if (data.type === "ready") {
    status(`Loaded in ${fmt(data.ms)}, ${data.mb.toFixed(0)} MB.`);
    compile();
  } else if (data.type === "result") {
    $("out").innerHTML = data.html;
    const bad = $("out").querySelector("table.stages tr.bad td.name");
    const what = bad ? `Stopped at ${bad.textContent} after` : "Compiled in";
    status(`${what} ${fmt(data.ms)}; WebAssembly memory ${data.mb.toFixed(0)} MB.`, !!bad);
    $("sections").innerHTML = [...$("out").querySelectorAll("section[id]")]
      .map((s) => `<a href="#${s.id}">${s.querySelector("h2").textContent}</a>`)
      .join("");
  } else {
    status("Error", true);
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
