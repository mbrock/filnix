import { moved } from "./moves.mjs";

// R2 holds immutable releases/<sha>/manifest.json files referencing
// content-addressed blobs/<sha256> objects (plus legacy releases/<sha>/<path>
// trees during migration). Only current.json is mutable.
// Canonical pages resolve current.json once and revalidate with strong ETags
// (cache-control: no-cache) on manifest releases; pinned /__releases/<sha>/…
// URLs remain immutable for edge caching and browser checks.
async function loadManifest(env, ctx, sha) {
  const key = `releases/${sha}/manifest.json`;
  const cacheReq = new Request(`https://filnix.org/__internal/${key}`);
  const cached = await caches.default.match(cacheReq);
  if (cached) {
    try { return await cached.json(); } catch { /* fall through to R2 */ }
  }
  const obj = await env.SITE.get(key);
  if (!obj) return null;
  const text = await obj.text();
  let data;
  try { data = JSON.parse(text); } catch { return null; }
  if (!data || typeof data.files !== "object") return null;
  ctx.waitUntil(caches.default.put(cacheReq, new Response(text, {
    headers: { "content-type": "application/json", "cache-control": "public, max-age=60" },
  })));
  return data;
}

function serveObject({ request, ctx, etag, uploaded, size, contentType, cacheControl, cacheable, cacheRequest, fetchBody }) {
  const headers = new Headers();
  if (contentType) headers.set("content-type", contentType);
  headers.set("etag", etag);
  headers.set("last-modified", uploaded.toUTCString());
  headers.set("accept-ranges", "bytes");
  headers.set("cache-control", cacheControl);
  headers.set("x-content-type-options", "nosniff");
  const matches = (value, weak) => value.split(",").some(tag => {
    tag = tag.trim();
    return tag === "*" || (weak ? tag.replace(/^W\//, "") : tag) === etag;
  });
  const modified = Math.floor(uploaded.getTime() / 1000) * 1000;
  const ifMatch = request.headers.get("if-match");
  const unmodified = request.headers.get("if-unmodified-since");
  if ((ifMatch && !matches(ifMatch, false)) ||
      (!ifMatch && unmodified && modified > Date.parse(unmodified))) {
    return new Response(null, { status: 412, headers });
  }
  const noneMatch = request.headers.get("if-none-match");
  const since = request.headers.get("if-modified-since");
  if ((noneMatch && matches(noneMatch, true)) ||
      (!noneMatch && since && modified <= Date.parse(since))) {
    return new Response(null, { status: 304, headers });
  }
  let range;
  const ifRange = request.headers.get("if-range");
  const mayRange = request.method === "GET" &&
    (!ifRange || ifRange === etag || modified <= Date.parse(ifRange));
  // Unsupported/malformed/multiple ranges are ignored, as HTTP permits.
  const part = mayRange && request.headers.get("range")?.match(/^bytes=(\d*)-(\d*)$/);
  if (part && (part[1] || part[2])) {
    const total = BigInt(size);
    let start = part[1] ? BigInt(part[1]) : total - BigInt(part[2]);
    let end = part[1] && part[2] ? BigInt(part[2]) : total - 1n;
    if (start < 0n) start = 0n;
    if (end >= total) end = total - 1n;
    if (start >= total || start > end) {
      headers.set("content-range", `bytes */${size}`);
      return new Response(null, { status: 416, headers });
    }
    range = { offset: Number(start), length: Number(end - start + 1n) };
    headers.set("content-range", `bytes ${start}-${end}/${size}`);
  }
  headers.set("content-length", String(range ? range.length : size));
  if (request.method === "HEAD") return new Response(null, { headers });
  return fetchBody(range).then(object => {
    if (!object) return new Response("Not found", { status: 404, headers: { "cache-control": "no-store" } });
    const response = new Response(object.body, { status: range ? 206 : 200, headers });
    // Cloudflare's ordinary cache cannot store objects larger than 512 MiB.
    // Larger downloads still stream directly from R2 without buffering.
    if (cacheable && size <= 512 * 1024 * 1024) {
      ctx.waitUntil(caches.default.put(cacheRequest, response.clone()));
    }
    return response;
  });
}

export default {
  async fetch(request, env, ctx) {
    const url = new URL(request.url);
    const reply = (body, status, headers = {}) => new Response(
      request.method === "HEAD" ? null : body,
      { status, headers: { "cache-control": "no-store", ...headers } },
    );
    if (!["GET", "HEAD"].includes(request.method)) {
      return reply("Method not allowed", 405, { allow: "GET, HEAD" });
    }
    if (url.protocol !== "https:") {
      url.protocol = "https:";
      return reply(null, 308, { location: url.href });
    }
    let path;
    try { path = decodeURIComponent(url.pathname); }
    catch { return reply("Invalid path", 400); }
    if (/[\\\0]/.test(path) || path.split("/").some(p => p === "." || p === "..")) {
      return reply("Invalid path", 400);
    }
    const pinned = path.match(/^\/__releases\/([0-9a-f]{40})(\/.*)?$/);
    let sha, tail;
    if (!pinned) {
      const current = await env.SITE.get("current.json");
      if (!current) return reply("First deployment is not ready", 503);
      ({ sha } = await current.json());
      if (!/^[0-9a-f]{40}$/.test(sha)) return reply("Invalid deployment", 503);
      if (path === "/commit.txt") {
        return reply(`${sha}\n`, 200, { "content-type": "text/plain; charset=utf-8" });
      }
      tail = path;
    } else {
      [, sha, tail = "/"] = pinned;
      if (!pinned[2]) {
        url.pathname += "/";
        return reply(null, 308, { location: url.href });
      }
    }
    // A query string cannot select different immutable bytes.
    const cacheURL = new URL(url);
    cacheURL.search = "";
    const cacheRequest = new Request(cacheURL);
    const cacheable = Boolean(pinned) && request.method === "GET" &&
      !["range", "if-match", "if-none-match", "if-modified-since", "if-unmodified-since"]
        .some(h => request.headers.has(h));
    if (cacheable) {
      const cached = await caches.default.match(cacheRequest);
      if (cached) return cached;
    }

    // Content-addressed manifest path: one cached manifest lookup replaces
    // R2 HEAD calls and provides strong SHA-256 ETags for 304 revalidation.
    const manifest = await loadManifest(env, ctx, sha);
    if (manifest) {
      const lookup = tail.endsWith("/") ? `${tail}index.html` : tail;
      const entry = Object.hasOwn(manifest.files, lookup) ? manifest.files[lookup] : null;
      if (!entry) {
        if (!tail.endsWith("/") && Object.hasOwn(manifest.files, `${tail}/index.html`)) {
          url.pathname += "/";
          return reply(null, 308, { location: url.href });
        }
        const now = !pinned && moved(tail);
        if (now) {
          url.pathname = now;
          return reply(null, 301, { location: url.href });
        }
        return reply("Not found", 404);
      }
      const [hash, size, contentType] = entry;
      return serveObject({
        request,
        ctx,
        etag: `"${hash}"`,
        uploaded: new Date(manifest.created || 0),
        size,
        contentType,
        cacheControl: pinned ? "public, max-age=31536000, immutable" : "no-cache",
        cacheable,
        cacheRequest,
        fetchBody: (range) => env.SITE.get(`blobs/${hash}`, range ? { range } : undefined),
      });
    }

    // Legacy tree path: releases/<sha>/<path> objects.
    let key = `releases/${sha}${tail}`;
    if (tail.endsWith("/")) key += "index.html";
    const meta = await env.SITE.head(key);
    if (!meta) {
      // Expired page bookmarks may move forward, but an expired asset must
      // never silently become a different release's JS, WASM, CSS or data.
      const page = tail.endsWith("/") || tail.endsWith(".html") || !tail.split("/").at(-1).includes(".");
      if (pinned && page && !await env.SITE.head(`releases/${sha}/commit.txt`)) {
        const current = await env.SITE.get("current.json");
        if (current && (await current.json()).sha !== sha) {
          url.pathname = url.pathname.replace(/^\/__releases\/[0-9a-f]{40}/, "");
          return reply(null, 302, { location: url.href });
        }
      }
      if (!tail.endsWith("/") && await env.SITE.head(`${key}/index.html`)) {
        url.pathname += "/";
        return reply(null, 308, { location: url.href });
      }
      // A page a restructuring moved (moves.mjs), so old links still work.
      const now = !pinned && moved(tail);
      if (now) {
        url.pathname = now;
        return reply(null, 301, { location: url.href });
      }
      return reply("Not found", 404);
    }
    const metaHeaders = new Headers();
    meta.writeHttpMetadata(metaHeaders);
    return serveObject({
      request,
      ctx,
      etag: meta.httpEtag,
      uploaded: meta.uploaded,
      size: meta.size,
      contentType: metaHeaders.get("content-type"),
      cacheControl: pinned ? "public, max-age=31536000, immutable" : "no-store",
      cacheable,
      cacheRequest,
      fetchBody: (range) => env.SITE.get(key, range ? { range } : undefined),
    });
  },
};
