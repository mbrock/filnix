// nanofil in a Web Worker: SWI-Prolog (swipl-wasm) with nanofil's
// sources, the frozen preprocessor profile and the headers (fs.json, from
// build.sh) in its file system. Messages:
//   in:  {source, opt}            opt "o0" or "o1"
//        {ask, goal, input}       a question about the last compile
//                                 (play_view.pl), input its bindings
//   out: {type: "ready", ms, mb}  once loaded
//        {type: "result", html, ms, mb} | {type: "error", message}
//        {type: "answer", ask, value}  the goal's bindings, or null
importScripts("swipl/swipl-web.js");

// Emscripten keeps its memory private; catch it as it is made.
let memory = null;
for (const name of ["instantiate", "instantiateStreaming"]) {
  const orig = WebAssembly[name];
  WebAssembly[name] = async (...args) => {
    const r = await orig.apply(WebAssembly, args);
    for (const v of Object.values((r.instance ?? r).exports)) if (v instanceof WebAssembly.Memory) memory = v;
    return r;
  };
}
const mb = () => (memory ? memory.buffer.byteLength / 2 ** 20 : 0);

let log = [];
const ready = (async () => {
  const t0 = performance.now();
  const [swipl, files] = await Promise.all([
    SWIPL({
      arguments: ["-q"],
      locateFile: (p) => "swipl/" + p,
      print: (s) => log.push(s),
      printErr: (s) => log.push(s),
    }),
    fetch("fs.json").then((r) => r.json()),
  ]);
  const FS = swipl.FS;
  for (const [path, text] of Object.entries(files)) {
    const dir = path.slice(0, path.lastIndexOf("/"));
    FS.mkdirTree(dir);
    FS.writeFile(path, text);
  }
  FS.mkdirTree("/work");
  const r = swipl.prolog.query("working_directory(_, '/nanofil/src/'), consult(load_swi)").once();
  if (r.error) throw new Error("loading nanofil: " + JSON.stringify(r) + "\n" + log.join("\n"));
  postMessage({ type: "ready", ms: performance.now() - t0, mb: mb() });
  return swipl;
})();
ready.catch((e) => postMessage({ type: "error", message: String(e.stack ?? e) }));

// swipl-wasm turns dicts into objects and strings into String objects;
// JSON makes them plain for postMessage.
const plain = (v) => JSON.parse(JSON.stringify(v, (k, x) => (typeof x === "bigint" ? Number(x) : x)));

onmessage = async ({ data: { source, opt, ask, goal, input } }) => {
  if (ask !== undefined) {
    const swipl = await ready;
    let value = null;
    try {
      const r = swipl.prolog.query(goal, input).once();
      if (r?.$tag === "bindings") value = plain(r);
    } catch {}
    return postMessage({ type: "answer", ask, value });
  }
  try {
    const swipl = await ready;
    swipl.FS.writeFile("/work/input.c", source);
    log = [];
    const t0 = performance.now();
    const r = swipl.prolog.query(`play_html('/work/input.c', ${opt === "o1" ? "o1" : "o0"}, Html)`).once();
    const ms = performance.now() - t0;
    // A solution is {$tag: "bindings", Html}; Html is a Prolog string object.
    if (r?.$tag !== "bindings") {
      postMessage({ type: "error", message: JSON.stringify(r) + "\n" + log.join("\n") });
    } else {
      postMessage({ type: "result", html: String(r.Html), ms, mb: mb() });
    }
  } catch (e) {
    postMessage({ type: "error", message: String(e.stack ?? e) + "\n" + log.join("\n") });
  }
};
