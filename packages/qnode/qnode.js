// qnode: run small Node.js CLI scripts on QuickJS.
//
// Usage: qjs --std qnode.js SCRIPT [ARGS...]
//
// Provides just enough of Node for self-contained CLIs: CommonJS require
// with relative modules and JSON, the process object, console.error/warn,
// Buffer-free fs (utf-8 strings only), path and assert. ES module scripts
// are imported directly; their imports must be relative paths.
import * as std from "std";
import * as os from "os";

function fail(msg) {
  std.err.puts("qnode: " + msg + "\n");
  std.exit(70);
}

function show(v) {
  if (typeof v === "string") return v;
  if (v instanceof Error) return v.stack ? v + "\n" + v.stack : String(v);
  try {
    return JSON.stringify(v);
  } catch {
    return String(v);
  }
}
const toStderr = (...a) => std.err.puts(a.map(show).join(" ") + "\n");
console.error = toStderr;
console.warn = toStderr;
console.info = console.log;
console.debug = console.log;

// ── path ──
const path = {
  sep: "/",
  delimiter: ":",
  isAbsolute: (p) => p.startsWith("/"),
  normalize(p) {
    const abs = p.startsWith("/");
    const out = [];
    for (const part of p.split("/")) {
      if (part === "" || part === ".") continue;
      if (part === ".." && out.length && out[out.length - 1] !== "..") out.pop();
      else if (part !== ".." || !abs) out.push(part);
    }
    const s = (abs ? "/" : "") + out.join("/");
    return s || (abs ? "/" : ".");
  },
  join: (...ps) => path.normalize(ps.filter((p) => p !== "").join("/")),
  resolve(...ps) {
    let r = "";
    for (const p of ps) r = p.startsWith("/") || r === "" ? p : r + "/" + p;
    if (!r.startsWith("/")) r = process.cwd() + "/" + r;
    return path.normalize(r);
  },
  dirname(p) {
    const i = p.replace(/\/+$/, "").lastIndexOf("/");
    return i < 0 ? "." : i === 0 ? "/" : p.slice(0, i);
  },
  basename(p, ext) {
    let b = p.replace(/\/+$/, "").split("/").pop();
    if (ext && b.endsWith(ext)) b = b.slice(0, -ext.length);
    return b;
  },
  extname(p) {
    const b = path.basename(p);
    const i = b.lastIndexOf(".");
    return i <= 0 ? "" : b.slice(i);
  },
};
path.posix = path;

// ── fs (utf-8 text only) ──
function errno(code, p) {
  const e = new Error(code + ": " + std.strerror(-code) + ", '" + p + "'");
  e.code = { 2: "ENOENT", 13: "EACCES", 17: "EEXIST", 21: "EISDIR" }[-code];
  return e;
}
const fs = {
  existsSync: (p) => os.stat(p)[1] === 0,
  readFileSync(p, opts) {
    const s = std.loadFile(p);
    if (s === null) throw errno(-2, p);
    return s; // always a string: no Buffer on QuickJS
  },
  writeFileSync(p, data) {
    const f = std.open(p, "w");
    if (!f) throw errno(-13, p);
    f.puts(String(data));
    f.close();
  },
  copyFileSync(a, b) {
    fs.writeFileSync(b, fs.readFileSync(a));
  },
  readdirSync(p) {
    const [names, err] = os.readdir(p);
    if (err) throw errno(-err, p);
    return names.filter((n) => n !== "." && n !== "..").sort();
  },
  statSync(p) {
    const [st, err] = os.stat(p);
    if (err) throw errno(-err, p);
    const type = st.mode & os.S_IFMT;
    return {
      size: st.size,
      mtimeMs: st.mtime,
      isFile: () => type === os.S_IFREG,
      isDirectory: () => type === os.S_IFDIR,
    };
  },
  mkdirSync(p) {
    const err = os.mkdir(p);
    if (err) throw errno(err, p);
  },
};
const promisify = (f) => async (...a) => f(...a);
// Callback forms: fs.readFile(path[, opts], cb).
for (const n of ["readFile", "writeFile", "copyFile", "readdir", "stat", "mkdir"]) {
  fs[n] = (...a) => {
    const cb = a.pop();
    let r, e = null;
    try {
      r = fs[n + "Sync"](...a);
    } catch (err) {
      e = err;
    }
    os.setTimeout(() => cb(e, r), 0);
  };
}
fs.access = (p, ...a) => fs.stat(p, a.pop());
fs.accessSync = (p) => void fs.statSync(p);
fs.promises = {
  readFile: promisify(fs.readFileSync),
  writeFile: promisify(fs.writeFileSync),
  copyFile: promisify(fs.copyFileSync),
  readdir: promisify(fs.readdirSync),
  stat: promisify(fs.statSync),
  mkdir: promisify(fs.mkdirSync),
};

// ── assert ──
function assert(v, msg) {
  if (!v) throw new Error(msg || "Assertion failed");
}
assert.ok = assert;
assert.equal = (a, b, m) => assert(a == b, m);
assert.strictEqual = (a, b, m) => assert(a === b, m);
assert.default = assert;

// ── process ──
// stdin is read in one piece once a listener or read() asks for it.
function makeStdin() {
  const handlers = {};
  let data = null;
  let scheduled = false;
  const load = () => (data ??= std.in.readAsString());
  const emit = (ev, ...a) => (handlers[ev] || []).forEach((h) => h(...a));
  const stdin = {
    isTTY: os.isatty(0),
    fd: 0,
    setEncoding: () => stdin,
    resume: () => stdin,
    pause: () => stdin,
    on(ev, h) {
      (handlers[ev] ||= []).push(h);
      if (!scheduled && (ev === "data" || ev === "readable" || ev === "end")) {
        scheduled = true;
        os.setTimeout(() => {
          const s = load();
          if (s !== "") {
            emit("data", s);
            emit("readable");
          }
          emit("end");
        }, 0);
      }
      return stdin;
    },
    read() {
      if (data === null) return load() || null;
      const s = data;
      data = "";
      return s === "" ? null : s;
    },
  };
  stdin.once = stdin.on;
  stdin.addListener = stdin.on;
  return stdin;
}
const stream = (f) => ({
  isTTY: os.isatty(f === std.out ? 1 : 2),
  _handle: { setBlocking() {} }, // writes are synchronous already
  write(s) {
    f.puts(String(s));
    return true;
  },
  on() {
    return this;
  },
});
const [script, ...args] = scriptArgs.slice(1);
if (!script) fail("usage: qjs --std qnode.js SCRIPT [ARGS...]");
const process = {
  argv: ["node", script, ...args],
  argv0: "node",
  execArgv: [],
  env: std.getenviron(),
  platform: "linux",
  arch: "x64",
  pid: os.getpid ? os.getpid() : 0,
  version: "v18.0.0",
  // Node 18 is the floor most CLIs check; qnode is not Node, of course.
  versions: { node: "18.0.0" },
  exitCode: undefined,
  cwd: () => os.getcwd()[0],
  chdir: (d) => os.chdir(d),
  exit(code) {
    std.out.flush();
    std.exit(code ?? process.exitCode ?? 0);
  },
  on: () => process,
  once: () => process,
  nextTick: (f, ...a) => Promise.resolve().then(() => f(...a)),
  hrtime: Object.assign(() => [0, 0], { bigint: () => BigInt(Date.now()) * 1000000n }),
  memoryUsage: () => ({ rss: 0, heapUsed: 0 }),
  stdin: makeStdin(),
  stdout: stream(std.out),
  stderr: stream(std.err),
};
globalThis.process = process;
globalThis.global = globalThis;
globalThis.setTimeout = os.setTimeout;
globalThis.clearTimeout = os.clearTimeout;
globalThis.setImmediate = (f, ...a) => os.setTimeout(() => f(...a), 0);
globalThis.queueMicrotask ??= (f) => Promise.resolve().then(f);
const B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
globalThis.btoa ??= (s) => {
  let out = "";
  for (let i = 0; i < s.length; i += 3) {
    const n = (s.charCodeAt(i) << 16) | (s.charCodeAt(i + 1) << 8) | s.charCodeAt(i + 2);
    out += B64[(n >> 18) & 63] + B64[(n >> 12) & 63];
    out += i + 1 < s.length ? B64[(n >> 6) & 63] : "=";
    out += i + 2 < s.length ? B64[n & 63] : "=";
  }
  return out;
};
globalThis.atob ??= (s) => {
  let out = "";
  s = s.replace(/[^A-Za-z0-9+/]/g, "");
  for (let i = 0; i < s.length; i += 4) {
    const n = [0, 1, 2, 3].reduce((a, k) => (a << 6) | Math.max(0, B64.indexOf(s[i + k] ?? "A")), 0);
    out += String.fromCharCode((n >> 16) & 255);
    if (i + 2 < s.length) out += String.fromCharCode((n >> 8) & 255);
    if (i + 3 < s.length) out += String.fromCharCode(n & 255);
  }
  return out;
};

// ── small builtins ──
class EventEmitter {
  get _events() {
    // Old-style subclasses (util.inherits) never call the constructor.
    Object.defineProperty(this, "_events", { value: {}, writable: true });
    return this._events;
  }
  on(ev, h) {
    (this._events[ev] ||= []).push(h);
    return this;
  }
  once(ev, h) {
    const w = (...a) => {
      this.off(ev, w);
      h.apply(this, a);
    };
    return this.on(ev, w);
  }
  off(ev, h) {
    this._events[ev] = (this._events[ev] || []).filter((x) => x !== h);
    return this;
  }
  emit(ev, ...a) {
    const hs = this._events[ev] || [];
    hs.slice().forEach((h) => h.apply(this, a));
    return hs.length > 0;
  }
  listenerCount(ev) {
    return (this._events[ev] || []).length;
  }
}
EventEmitter.prototype.addListener = EventEmitter.prototype.on;
EventEmitter.prototype.removeListener = EventEmitter.prototype.off;
EventEmitter.EventEmitter = EventEmitter;
EventEmitter.default = EventEmitter;

const util = {
  inspect: show,
  format: (f, ...a) =>
    typeof f === "string"
      ? f.replace(/%[sdifjoO%]/g, (m) => (m === "%%" ? "%" : show(a.shift()))) +
        a.map((x) => " " + show(x)).join("")
      : [f, ...a].map(show).join(" "),
  inherits(ctor, superCtor) {
    Object.setPrototypeOf(ctor.prototype, superCtor.prototype);
    Object.setPrototypeOf(ctor, superCtor);
  },
  deprecate: (f) => f,
  promisify: (f) => (...a) =>
    new Promise((res, rej) => f(...a, (e, v) => (e ? rej(e) : res(v)))),
  isDeepStrictEqual: (a, b) => JSON.stringify(a) === JSON.stringify(b),
};

const nodeOs = {
  EOL: "\n",
  platform: () => "linux",
  type: () => "Linux",
  arch: () => "x64",
  homedir: () => std.getenv("HOME") || "/",
  tmpdir: () => std.getenv("TMPDIR") || "/tmp",
  hostname: () => "localhost",
  cpus: () => [{ model: "unknown", speed: 0 }],
  totalmem: () => 0,
  freemem: () => 0,
};

// Modules that CLIs often load eagerly but rarely use: loading works,
// calling anything reports what is missing.
function unsupported(name) {
  return new Proxy(
    {},
    {
      get(_, prop) {
        if (prop === "__esModule" || typeof prop === "symbol") return undefined;
        return function () {
          throw new Error("qnode: " + name + "." + String(prop) + " is not supported");
        };
      },
    },
  );
}

// ── CommonJS ──
const builtins = {
  fs,
  path,
  assert,
  process,
  events: EventEmitter,
  util,
  os: nodeOs,
  tty: { isatty: (fd) => os.isatty(fd) },
  url: {
    fileURLToPath: (u) => decodeURIComponent(String(u.href ?? u).replace(/^file:\/\//, "")),
    pathToFileURL: (p) => ({ href: "file://" + path.resolve(p) }),
  },
};
for (const name of [
  "child_process",
  "crypto",
  "http",
  "https",
  "net",
  "readline",
  "stream",
  "vm",
  "worker_threads",
  "zlib",
])
  builtins[name] = unsupported(name);
const cache = {};
function resolveFile(p) {
  for (const c of [p, p + ".js", p + ".cjs", p + ".json", p + "/index.js"]) {
    const [st, err] = os.stat(c);
    if (!err && (st.mode & os.S_IFMT) === os.S_IFREG) return c;
  }
  const pkg = p + "/package.json";
  if (fs.existsSync(pkg)) {
    const meta = JSON.parse(std.loadFile(pkg));
    // Prefer the CommonJS entry of an "exports" map.
    let e = meta.exports;
    if (e && typeof e === "object" && "." in e) e = e["."];
    while (e && typeof e === "object")
      e = Array.isArray(e)
        ? e.find((x) => typeof x === "string" || x.require || x.default)
        : (e.require ?? e.node ?? e.default);
    const main = typeof e === "string" ? e : meta.main;
    if (main) return resolveFile(path.join(p, main));
  }
  return null;
}
function resolveModule(spec, dir) {
  if (spec.startsWith("./") || spec.startsWith("../") || spec.startsWith("/"))
    return resolveFile(path.resolve(dir, spec));
  for (let d = dir; ; d = path.dirname(d)) {
    const f = resolveFile(path.join(d, "node_modules", spec));
    if (f) return f;
    if (d === "/") return null;
  }
}
function makeRequire(dir) {
  const resolve = (spec) => {
    const file = resolveModule(spec, dir);
    if (!file) throw new Error("qnode: cannot find module '" + spec + "'");
    return file;
  };
  function require(spec) {
    const name = spec.replace(/^node:/, "");
    if (name in builtins) return builtins[name];
    return loadCommonJS(resolve(spec));
  }
  require.resolve = (spec) => (spec.replace(/^node:/, "") in builtins ? spec : resolve(spec));
  require.cache = cache;
  return require;
}
function loadCommonJS(file) {
  if (cache[file]) return cache[file].exports;
  const module = { exports: {}, filename: file, loaded: false };
  cache[file] = module;
  const src = std.loadFile(file);
  if (file.endsWith(".json")) {
    module.exports = JSON.parse(src);
  } else {
    const body = src.replace(/^#!.*/, "");
    let fn;
    try {
      fn = std.evalScript(
        "(function (exports, require, module, __filename, __dirname) {" +
          body +
          "\n})",
      );
    } catch (e) {
      e.message += " (in " + file + ")";
      throw e;
    }
    fn.call(module.exports, module.exports, makeRequire(path.dirname(file)), module, file, path.dirname(file));
  }
  module.loaded = true;
  return module.exports;
}

const main = path.resolve(script);
const text = std.loadFile(main);
if (text === null) fail("cannot read " + main);
const isModule = main.endsWith(".mjs") || /^\s*(import|export)\s/m.test(text.replace(/^#!.*/, ""));
if (isModule) {
  import(main).catch((e) => {
    toStderr(e);
    std.exit(1);
  });
} else {
  try {
    loadCommonJS(main);
  } catch (e) {
    toStderr(e);
    std.exit(1);
  }
}
