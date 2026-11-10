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
    [`releases/${sha}/docs/index.html`, "docs"],
    [`releases/${sha}/large.bin`, "0123456789abcdef"],
    [`releases/${next}/index.html`, "<h1>next</h1>"],
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
    fetch(path, options) { return worker.fetch(new Request(`https://filnix.org${path}`, options), env, { waitUntil() {} }); },
  };
}

test("promotion redirects new visitors, without changing existing release URLs", async () => {
  const s = site();
  assert.equal((await s.fetch("/?q=hello")).headers.get("location"), `https://filnix.org${prefix}/?q=hello`);
  s.promote(next);
  assert.equal((await s.fetch("/docs/")).headers.get("location"), `https://filnix.org/__releases/${next}/docs/`);
  assert.equal(await (await s.fetch(`${prefix}/`)).text(), "<h1>first</h1>");
  assert.equal(await (await s.fetch("/commit.txt")).text(), `${next}\n`);
  assert.equal((await s.fetch(`${prefix}/docs`)).status, 308);
  assert.equal((await s.fetch(`${prefix}/absent.html`)).status, 404);
  s.promote(null);
  assert.equal((await s.fetch("/")).status, 503);
  assert.equal((await s.fetch(`${prefix}/`)).status, 200);
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
