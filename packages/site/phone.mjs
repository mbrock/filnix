// No page of the built site scrolls sideways on a phone.
//
//   node packages/site/phone.mjs SITE [--all | PAGE.html...] [WIDTH...]
//
// Serves SITE (the output of `nix build .#site`) and opens each page in
// an iframe WIDTH pixels wide (default 320), in one agent-browser page,
// after its fonts and dterm.js's layout; a page whose document is wider
// than the frame fails, with its width and the outermost elements that
// stick out. Without --all it checks SAMPLE, the pages that were widest
// before their fixes, in well under a minute (CI's Pages job); --all
// checks every page of the site but the forwarding stubs: the explainers,
// pandoc's docs and every page drawn by dterm, dterm-rocq and dterm-nix
// (about 5 minutes; run it by hand after changing how pages lay out), and
// PAGEs, paths under SITE, check just those.
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { createServer } from "node:http";
import { readFileSync, readdirSync, statSync } from "node:fs";
import { extname, join, normalize } from "node:path";

const SAMPLE = [
  "index.html", "nanofil/index.html", "nanofil/src.html",
  "nanofil/main.html", "nanofil/filc_amd64.html", "nanofil/c_lower.html",
  "nanofil/c_types.html", "nanofil/ir.html", "nanofil/amd64_regs_check.html",
  "nanofil/rocq/index.html", "nanofil/rocq/rocq-theories-Machine.html",
  "nix/index.html", "nix/options.html", "nix/flake.html",
  "nix/compiler-libcxx.html", "nix/ports-overlay.html",
  "nix/ports-determinate-nix.html", "nix/build-filc.html",
  "nix/bench-php-default.html", "nix/lib-filc-system.html",
  "nanofil/docs/abi-findings.html", "docs/php-port-notes.html",
  "frame-coloring-o0/index.html", "glibc-memcmp-noalloc/index.html",
];

const [site, ...rest] = process.argv.slice(2);
if (!site) throw new Error("Pass the built site's directory");
const all = rest.includes("--all");
const named = rest.filter((a) => a.endsWith(".html"));
const widths = rest.filter((a) => /^\d+$/.test(a)).map(Number);
if (!widths.length) widths.push(320);

// A forwarding stub (build.sh writes one per moved document) is not a page.
const page = (path) => !readFileSync(join(site, path), "utf8").includes('http-equiv="refresh"');
const html = (dir) => readdirSync(join(site, dir)).filter((f) => f.endsWith(".html"))
  .filter((f) => statSync(join(site, dir, f)).isFile()).sort().map((f) => `${dir}/${f}`);
const explainers = readdirSync(site).filter((d) => statSync(join(site, d)).isDirectory())
  .map((d) => `${d}/index.html`).filter((f) => { try { return statSync(join(site, f)).isFile(); } catch { return false; } })
  .filter((f) => !/^(docs|nanofil|nix)\//.test(f));
const pages = all ? ["index.html", ...explainers, ...html("docs"), ...html("nanofil"), ...html("nanofil/docs"),
    ...html("nanofil/rocq"), ...html("nix")].filter(page)
  : named.length ? named : SAMPLE;

const types = { ".html": "text/html", ".css": "text/css", ".js": "text/javascript",
  ".json": "application/json", ".png": "image/png", ".svg": "image/svg+xml", ".woff2": "font/woff2" };
const server = createServer((req, res) => {
  let path = normalize(decodeURIComponent(new URL(req.url, "http://x").pathname)).replace(/^\/+/, "");
  if (path === "" || path.endsWith("/")) path += "index.html";
  try {
    const body = readFileSync(join(site, path));
    res.writeHead(200, { "content-type": types[extname(path)] ?? "application/octet-stream" });
    res.end(body);
  } catch {
    res.writeHead(404); res.end();
  }
});
await new Promise((ok) => server.listen(0, "127.0.0.1", ok));
const base = `http://127.0.0.1:${server.address().port}`;

const session = `phone-${process.pid}`;
// Asynchronously, so this process can serve the pages the browser asks for.
const browser = async (...args) => (await promisify(execFile)("agent-browser", ["--session", session, ...args],
  { encoding: "utf8", maxBuffer: 1 << 26 })).stdout;
let failed = 0;
try {
  await browser("open", `${base}/`);
  await browser("set", "viewport", "1280", "800");
  for (const width of widths) {
    const started = Date.now();
    // The run goes on in the page; short evaluations read its progress,
    // since one evaluation may last at most 30 seconds.
    await browser("eval", `(() => {
      const state = window.phone = { done: 0, page: "", results: [], finished: false };
      // A page that never finishes loading (a stalled video, say) is
      // measured as it stands after 10 seconds.
      const within = (p) => Promise.race([p, new Promise((ok) => setTimeout(ok, 10000))]);
      (async () => {
        for (const page of ${JSON.stringify(pages)}) {
          const frame = document.createElement("iframe");
          frame.style.cssText = "width:${width}px;height:700px;border:0;position:fixed;top:0;left:0";
          const loaded = new Promise((ok) => { frame.onload = ok; });
          state.page = page;
          frame.src = "/" + page;
          document.body.append(frame);
          await within(loaded);
          const doc = frame.contentDocument, win = frame.contentWindow;
          await within(doc.fonts.ready);
          for (let i = 0; i < 4; i++) await within(new Promise((ok) => win.requestAnimationFrame(ok)));
          const w = doc.documentElement.clientWidth, sw = doc.documentElement.scrollWidth;
          if (sw > w + 1) {
            const clipped = (e) => { for (let p = e.parentElement; p; p = p.parentElement)
              if (win.getComputedStyle(p).overflowX !== "visible") return true; return false; };
            const wide = new Set([...doc.body.querySelectorAll("*")]
              .filter((e) => e.getBoundingClientRect().right > w + 1 && !clipped(e)));
            const outer = [...wide].filter((e) => !wide.has(e.parentElement)).slice(0, 3)
              .map((e) => e.tagName.toLowerCase() + (e.className ? "." + String(e.className).split(" ").join(".") : "")
                + " in " + e.parentElement.tagName.toLowerCase() + "." + String(e.parentElement.className).split(" ").join("."));
            state.results.push(page + " " + sw + "px: " + (outer.join(", ") || "text in a box"));
          }
          frame.remove();
          state.done++;
        }
      })().catch((e) => state.results.push("error: " + e)).finally(() => { state.finished = true; });
      return 1;
    })()`);
    let state, shown = 0;
    do {
      await new Promise((ok) => setTimeout(ok, 1000));
      state = JSON.parse(JSON.parse(await browser("eval", "JSON.stringify(window.phone)")));
      if (state.done - shown >= 50) { shown = state.done; console.log(`${width}px: ${shown} of ${pages.length}, at ${state.page}`); }
    } while (!state.finished);
    const out = state.results.join("\n");
    const seconds = ((Date.now() - started) / 1000).toFixed(1);
    if (out) {
      failed += out.split("\n").length;
      console.log(`FAIL at ${width}px (${seconds} s):\n${out}`);
    } else {
      console.log(`ok ${pages.length} pages fit ${width}px (${seconds} s)`);
    }
  }
} finally {
  try { await browser("close"); } catch {}
  server.close();
}
process.exit(failed ? 1 : 0);
