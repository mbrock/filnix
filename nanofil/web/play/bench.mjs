// Run the playground's pipeline under Node on swipl-wasm or trealla-js,
// as the page does, and report wall time and WebAssembly memory.
//
//   node bench.mjs swi|trealla-js|tpl-wasi FS.JSON FILE.c [o0|o1] [REPEAT]
//
// swi is swipl-wasm and trealla-js the trealla npm package (NODE_PATH
// must reach them); tpl-wasi is TPL_WASM (trealla-wasm.nix's tpl.wasm)
// run as a WASI command, once per REPEAT, as a page would.
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname } from "node:path";
import { pathToFileURL } from "node:url";

const require = createRequire(import.meta.url);
const [host, fsJson, cFile, opt = "o0", repeat = "1"] = process.argv.slice(2);
const files = JSON.parse(readFileSync(fsJson, "utf8"));
const source = readFileSync(cFile, "utf8");
const goal = process.env.GOAL ?? `play_report('/work/input.c', ${opt})`;
// Capture each WebAssembly instance's memory, whichever host made it.
const memories = [];
for (const name of ["instantiate", "instantiateStreaming"]) {
  const orig = WebAssembly[name];
  WebAssembly[name] = async (...args) => {
    const r = await orig.apply(WebAssembly, args);
    const inst = r.instance ?? r;
    for (const v of Object.values(inst.exports ?? {})) if (v instanceof WebAssembly.Memory) memories.push(v);
    return r;
  };
}
const wasmBytes = () => memories.reduce((n, m) => n + m.buffer.byteLength, 0);
const mb = (n) => (n / 2 ** 20).toFixed(0) + " MB";
const t0 = performance.now();
const ms = () => (performance.now() - t0).toFixed(0) + " ms";

function mkdirs(mkdir, exists, path) {
  let p = "";
  for (const part of dirname(path).split("/").filter(Boolean)) {
    p += "/" + part;
    if (!exists(p)) mkdir(p);
  }
}

if (host === "swi") {
  const SWIPL = require("swipl-wasm");
  let out = "";
  const swipl = await SWIPL({
    arguments: ["-q"],
    print: (s) => (out += s + "\n"),
    printErr: (s) => process.stderr.write(s + "\n"),
  });
  const FS = swipl.FS;
  for (const [path, text] of Object.entries({ ...files, "/work/input.c": source })) {
    mkdirs((p) => FS.mkdir(p), (p) => FS.analyzePath(p).exists, path);
    FS.writeFile(path, text);
  }
  console.error(`swi: started ${ms()}`);
  swipl.prolog.query("working_directory(_, '/nanofil/src/'), consult('swi/compat.pl'), asserta(user:file_search_path(library, '/nanofil/play-lib')), use_module(play)").once();
  console.error(`swi: loaded ${ms()}, heap ${mb(wasmBytes())}`);
  for (let i = 0; i < +repeat; i++) {
    out = "";
    const t = performance.now();
    const r = swipl.prolog.query(goal).once();
    console.error(`swi: run ${i} ${(performance.now() - t).toFixed(0)} ms, heap ${mb(wasmBytes())}${r.error ? " " + JSON.stringify(r) : ""}`);
  }
  process.stdout.write(out);
} else if (host === "tpl-wasi") {
  const { WASI } = await import("node:wasi");
  const { mkdtempSync, mkdirSync, writeFileSync, rmSync } = await import("node:fs");
  const root = mkdtempSync("/tmp/play-wasi-");
  const all = { ...files, "/work/input.c": source,
    "/usr/local/share/trealla/library/process.pl": files["/nanofil/play-lib/process.pl"] };
  for (const [path, text] of Object.entries(all)) {
    mkdirSync(root + dirname(path), { recursive: true });
    writeFileSync(root + path, text);
  }
  const mod = await WebAssembly.compile(readFileSync(process.env.TPL_WASM));
  console.error(`tpl-wasi: compiled ${ms()}`);
  let out = "";
  for (let i = 0; i < +repeat; i++) {
    const t = performance.now();
    const outFile = root + "/work/out.txt";
    const wasi = new WASI({ version: "preview1", returnOnExit: true, preopens: { "/": root },
      args: ["tpl", "-q", "-g", `working_directory(_, '/nanofil/src/'), use_module(play), tell('/work/out.txt'), ${goal}, told`, "-g", "halt"] });
    const inst = await WebAssembly.instantiate(mod, wasi.getImportObject());
    const code = wasi.start(inst);
    out = readFileSync(outFile, "utf8");
    console.error(`tpl-wasi: run ${i} ${(performance.now() - t).toFixed(0)} ms (load included), memory ${mb(inst.exports.memory.buffer.byteLength)}, exit ${code}`);
  }
  rmSync(root, { recursive: true });
  process.stdout.write(out);
} else {
  const { Prolog, load } = await import(pathToFileURL(require.resolve("trealla")).href);
  await load();
  const pl = new Prolog();
  await pl.init();
  const fs = pl.fs;
  const tplFiles = { ...files, "/work/input.c": source,
    "/usr/local/share/trealla/library/process.pl": files["/nanofil/play-lib/process.pl"] };
  for (const [path, text] of Object.entries(tplFiles)) {
    mkdirs((p) => fs.createDir(p), (p) => { try { return fs.metadata(p) !== null; } catch { return false; } }, path);
    const f = fs.open(path, { create: true, write: true, truncate: true });
    f.writeString(text);
    f.flush();
  }
  const mem = () => mb(wasmBytes());
  console.error(`tpl: started ${ms()}`);
  // Trealla resolves relative module names from the working directory.
  const loaded = await pl.queryOnce("working_directory(_, '/nanofil/src/'), use_module(play)");
  if (loaded.status !== "success" || loaded.stderr) console.error("tpl: load", JSON.stringify(loaded).slice(0, 600));
  console.error(`tpl: loaded ${ms()}, memory ${mem()}`);
  let out = "";
  for (let i = 0; i < +repeat; i++) {
    const t = performance.now();
    const a = await pl.queryOnce(goal);
    if (a.status !== "success") console.error("tpl:", JSON.stringify(a).slice(0, 600));
    out = a.stdout ?? "";
    console.error(`tpl: run ${i} ${(performance.now() - t).toFixed(0)} ms, memory ${mem()}${a.stderr ? " stderr: " + a.stderr.slice(0, 400) : ""}`);
  }
  process.stdout.write(out);
}
