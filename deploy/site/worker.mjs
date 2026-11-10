// R2 holds immutable releases/<sha>/ trees. Only current.json is mutable.
// Canonical URLs redirect into a complete release, so relative links keep
// using that release even if another build is promoted during navigation.
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
    if (!pinned) {
      const current = await env.SITE.get("current.json");
      if (!current) return reply("First deployment is not ready", 503);
      const { sha } = await current.json();
      if (!/^[0-9a-f]{40}$/.test(sha)) return reply("Invalid deployment", 503);
      if (path === "/commit.txt") {
        return reply(`${sha}\n`, 200, { "content-type": "text/plain; charset=utf-8" });
      }
      url.pathname = `/__releases/${sha}${url.pathname}`;
      return reply(null, 302, { location: url.href });
    }
    const [, sha, tail = "/"] = pinned;
    if (!pinned[2]) {
      url.pathname += "/";
      return reply(null, 308, { location: url.href });
    }
    // A query string cannot select different immutable bytes.
    const cacheURL = new URL(url);
    cacheURL.search = "";
    const cacheRequest = new Request(cacheURL);
    const cacheable = request.method === "GET" &&
      !["range", "if-match", "if-none-match", "if-modified-since", "if-unmodified-since"]
        .some(h => request.headers.has(h));
    if (cacheable) {
      const cached = await caches.default.match(cacheRequest);
      if (cached) return cached;
    }
    let key = `releases/${sha}${tail}`;
    if (tail.endsWith("/")) key += "index.html";
    const meta = await env.SITE.head(key);
    if (!meta) {
      if (!tail.endsWith("/") && await env.SITE.head(`${key}/index.html`)) {
        url.pathname += "/";
        return reply(null, 308, { location: url.href });
      }
      return reply("Not found", 404);
    }
    const headers = new Headers();
    meta.writeHttpMetadata(headers);
    headers.set("etag", meta.httpEtag);
    headers.set("last-modified", meta.uploaded.toUTCString());
    headers.set("accept-ranges", "bytes");
    headers.set("cache-control", "public, max-age=31536000, immutable");
    headers.set("x-content-type-options", "nosniff");
    const matches = (value, weak) => value.split(",").some(tag => {
      tag = tag.trim();
      return tag === "*" || (weak ? tag.replace(/^W\//, "") : tag) === meta.httpEtag;
    });
    const modified = Math.floor(meta.uploaded.getTime() / 1000) * 1000;
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
      (!ifRange || ifRange === meta.httpEtag || modified <= Date.parse(ifRange));
    // Unsupported/malformed/multiple ranges are ignored, as HTTP permits.
    const part = mayRange && request.headers.get("range")?.match(/^bytes=(\d*)-(\d*)$/);
    if (part && (part[1] || part[2])) {
      const size = BigInt(meta.size);
      let start = part[1] ? BigInt(part[1]) : size - BigInt(part[2]);
      let end = part[1] && part[2] ? BigInt(part[2]) : size - 1n;
      if (start < 0n) start = 0n;
      if (end >= size) end = size - 1n;
      if (start >= size || start > end) {
        headers.set("content-range", `bytes */${meta.size}`);
        return new Response(null, { status: 416, headers });
      }
      range = { offset: Number(start), length: Number(end - start + 1n) };
      headers.set("content-range", `bytes ${start}-${end}/${meta.size}`);
    }
    headers.set("content-length", String(range ? range.length : meta.size));
    if (request.method === "HEAD") return new Response(null, { headers });
    const object = await env.SITE.get(key, range ? { range } : undefined);
    if (!object) return reply("Not found", 404);
    const response = new Response(object.body, { status: range ? 206 : 200, headers });
    // Cloudflare's ordinary cache cannot store objects larger than 512 MiB.
    // Larger downloads still stream directly from R2 without buffering.
    if (cacheable && meta.size <= 512 * 1024 * 1024) {
      ctx.waitUntil(caches.default.put(cacheRequest, response.clone()));
    }
    return response;
  },
};
