import { test } from "node:test";
import assert from "node:assert/strict";
import worker from "./worker.mjs";

const sha = "a".repeat(40), next = "b".repeat(40);
const prefix = `/__releases/${sha}`;
const uploaded = new Date("2026-11-10T09:00:00Z");
// Test the public HTTP interface against R2-shaped objects. Live validation
// additionally exercises real R2, streaming, TLS and the edge cache.
function site() {
  let current = sha;
  const files = new Map([
    [`releases/${sha}/index.html`, "<h1>first</h1>"],
    [`releases/${sha}/commit.txt`, sha],
    [`releases/${sha}/docs/index.html`, "docs"],
    [`releases/${sha}/large.bin`, "0123456789abcdef"],
    [`releases/${next}/index.html`, "<h1>next</h1>"],
    [`releases/${next}/large.bin`, "next release"],
    [`releases/${next}/commit.txt`, next],
  ]);
  globalThis.caches = { default: { async match() {}, async put() {} } };
  const env = { SITE: {
    async head(key) {
      const body = files.get(key);
      if (body === undefined) return null;
      return { size: Buffer.byteLength(body), uploaded, httpEtag: '"test-etag"',
        writeHttpMetadata(h) { h.set("content-type", key.endsWith(".html") ? "text/html" : "application/octet-stream"); } };
    },
    async get(key, options) {
      if (key === "current.json") return current && { async json() { return { sha: current }; } };
      let body = files.get(key);
      if (body === undefined) return null;
      if (options?.range) body = body.slice(options.range.offset, options.range.offset + options.range.length);
      return { body };
    },
  } };
  return {
    promote(value) { current = value; },
    add(path, body) { files.set(`releases/${current}${path}`, body); },
    expire(value) {
      for (const key of files.keys()) if (key.startsWith(`releases/${value}/`)) files.delete(key);
    },
    fetch(path, options) { return worker.fetch(new Request(`https://filnix.org${path}`, options), env, { waitUntil() {} }); },
  };
}

test("canonical pages stay clean and fresh, while pinned resources survive promotion", async () => {
  const s = site();
  const first = await s.fetch("/?q=hello");
  assert.equal(first.status, 200);
  assert.equal(first.headers.get("location"), null);
  assert.equal(first.headers.get("cache-control"), "no-store");
  assert.equal(await first.text(), "<h1>first</h1>");
  assert.equal(await (await s.fetch("/docs/")).text(), "docs");
  assert.equal((await s.fetch("/docs")).headers.get("location"), "https://filnix.org/docs/");
  const head = await s.fetch("/docs/", { method: "HEAD" });
  assert.equal(head.status, 200);
  assert.equal(await head.text(), "");
  s.promote(next);
  assert.equal(await (await s.fetch("/")).text(), "<h1>next</h1>");
  assert.equal((await s.fetch("/docs/")).status, 404);
  assert.equal(await (await s.fetch("/large.bin")).text(), "next release");
  const asset = await s.fetch(`${prefix}/large.bin`);
  assert.equal(await asset.text(), "0123456789abcdef");
  assert.match(asset.headers.get("cache-control"), /immutable/);
  assert.equal(await (await s.fetch(`${prefix}/`)).text(), "<h1>first</h1>");
  assert.equal(await (await s.fetch("/commit.txt")).text(), `${next}\n`);
  assert.equal((await s.fetch(`${prefix}/docs`)).status, 308);
  assert.equal((await s.fetch(`${prefix}/absent.html`)).status, 404);
  s.promote(null);
  assert.equal((await s.fetch("/")).status, 503);
  assert.equal((await s.fetch(`${prefix}/`)).status, 200);
});

test("expired bookmarks redirect to canonical paths, without masking real missing pages", async () => {
  const s = site();
  s.promote(next);
  assert.equal((await s.fetch(`${prefix}/absent.html`)).status, 404);
  s.expire(sha);
  const expired = await s.fetch(`${prefix}/docs/?search=hello`);
  assert.equal(expired.status, 302);
  assert.equal(expired.headers.get("location"), "https://filnix.org/docs/?search=hello");
  assert.equal(expired.headers.get("cache-control"), "no-store");
  assert.equal((await s.fetch(`${prefix}/large.bin`)).status, 404);
  assert.equal((await s.fetch(`/__releases/${next}/absent.html`)).status, 404);
  s.expire(next);
  assert.equal((await s.fetch(`/__releases/${next}/absent.html`)).status, 404);
});

test("binary downloads retain exact bytes, HEAD metadata and range semantics", async () => {
  const s = site(), path = `${prefix}/large.bin`;
  const full = await s.fetch(path);
  assert.equal(full.status, 200);
  assert.equal(full.headers.get("content-length"), "16");
  assert.equal(await full.text(), "0123456789abcdef");
  const head = await s.fetch(path, { method: "HEAD" });
  assert.equal(head.headers.get("content-length"), "16");
  assert.equal(await head.text(), "");
  for (const [range, body, contentRange] of [
    ["bytes=3-8", "345678", "bytes 3-8/16"],
    ["bytes=-5", "bcdef", "bytes 11-15/16"],
    ["bytes=13-999", "def", "bytes 13-15/16"],
  ]) {
    const r = await s.fetch(path, { headers: { range } });
    assert.equal(r.status, 206);
    assert.equal(r.headers.get("content-range"), contentRange);
    assert.equal(await r.text(), body);
  }
  for (const range of ["bytes=16-", "bytes=-0", "bytes=8-3", "bytes=999999999999999999999-"]) {
    const r = await s.fetch(path, { headers: { range } });
    assert.equal(r.status, 416);
    assert.equal(r.headers.get("content-range"), "bytes */16");
  }
  const stale = await s.fetch(path, { headers: { range: "bytes=3-8", "if-range": '"old"' } });
  assert.equal(stale.status, 200);
  assert.equal(await stale.text(), "0123456789abcdef");
});

test("conditional requests distinguish not-modified from failed preconditions", async () => {
  const s = site(), path = `${prefix}/index.html`;
  assert.equal((await s.fetch(path, { headers: { "if-none-match": '"other", W/"test-etag"' } })).status, 304);
  assert.equal((await s.fetch(path, { headers: { "if-none-match": '"other"' } })).status, 200);
  assert.equal((await s.fetch(path, { headers: { "if-match": 'W/"test-etag"' } })).status, 412);
  assert.equal((await s.fetch(path, { headers: { "if-modified-since": uploaded.toUTCString() } })).status, 304);
  assert.equal((await s.fetch(path, { headers: { "if-unmodified-since": "Tue, 10 Nov 2026 08:00:00 GMT" } })).status, 412);
  assert.equal((await s.fetch(path, { method: "PUT", body: "no" })).status, 405);
  assert.equal((await s.fetch("/%00")).status, 400);
});

test("a page a restructuring moved redirects to where it lives now", async () => {
  const s = site(), rocq = "/nanofil/rocq/";
  s.add(`${rocq}rocq-theories-soundness-Machine.html`, "machine");
  const old = await s.fetch(`${rocq}rocq-theories-Machine.html?x=1`);
  assert.equal(old.status, 301);
  assert.equal(old.headers.get("location"), `https://filnix.org${rocq}rocq-theories-soundness-Machine.html?x=1`);
  assert.equal((await s.fetch(`${rocq}rocq-theories-HelloMain.html`)).headers.get("location"),
    `https://filnix.org${rocq}rocq-theories-hello_contracts-HelloMain.html`);
  // A page that exists again under its old name is served, not moved.
  s.add(`${rocq}rocq-theories-Syntax.html`, "flat");
  assert.equal(await (await s.fetch(`${rocq}rocq-theories-Syntax.html`)).text(), "flat");
  for (const path of [`${rocq}rocq-theories-Nowhere.html`, `${rocq}rocq-theories-soundness-Walk.html`,
    `${rocq}rocq-glibc-Machine.html`, `${prefix}${rocq}rocq-theories-Machine.html`]) {
    assert.equal((await s.fetch(path)).status, 404, path);
  }
  // A superseded page redirects even while the site still publishes it,
  // but its pinned copy is served as published.
  s.add(`${rocq}rocq-glibc-ZsysWrite.html`, "zsys");
  const zsys = await s.fetch(`${rocq}rocq-glibc-ZsysWrite.html?x=1`);
  assert.equal(zsys.status, 301);
  assert.equal(zsys.headers.get("location"), `https://filnix.org${rocq}rocq-glibc-zsys-OsWrite.html?x=1`);
  assert.equal(await (await s.fetch(`${prefix}${rocq}rocq-glibc-ZsysWrite.html`)).text(), "zsys");
});
