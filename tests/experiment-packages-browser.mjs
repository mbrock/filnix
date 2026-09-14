// Run against an installed dashboard and Chromium's loopback debugging endpoint.
// node tests/experiment-browser.mjs http://127.0.0.1:8777 results/experiment-packages-ui
import { mkdir, writeFile } from "node:fs/promises";
import assert from "node:assert/strict";
const base = process.argv[2] || "http://127.0.0.1:8777",
  out = process.argv[3] || "results/experiment-packages-ui";
await mkdir(out, { recursive: true });
const tab = await (
  await fetch("http://127.0.0.1:9228/json/new?about:blank", { method: "PUT" })
).json();
const ws = new WebSocket(tab.webSocketDebuggerUrl);
await new Promise((r) => ws.addEventListener("open", r, { once: true }));
let serial = 0;
const pending = new Map(),
  errors = [];
ws.addEventListener("message", (event) => {
  const m = JSON.parse(event.data);
  if (m.id) {
    const p = pending.get(m.id);
    pending.delete(m.id);
    m.error ? p.reject(m.error) : p.resolve(m.result);
  } else if (m.method === "Runtime.exceptionThrown") errors.push(m.params);
});
const call = (method, params = {}) =>
  new Promise((resolve, reject) => {
    const id = ++serial;
    pending.set(id, { resolve, reject });
    ws.send(JSON.stringify({ id, method, params }));
  });
const evaluate = async (expression) =>
  (
    await call("Runtime.evaluate", {
      expression,
      returnByValue: true,
      awaitPromise: true,
    })
  ).result.value;
const wait = (ms) => new Promise((r) => setTimeout(r, ms));
async function until(expression) {
  for (let n = 0; n < 100; n++) {
    if (await evaluate(expression)) return;
    await wait(100);
  }
  assert.fail("Timed out: " + expression);
}
await call("Runtime.enable");
await call("Page.enable");
await call("Emulation.setDeviceMetricsOverride", {
  width: 1440,
  height: 1000,
  deviceScaleFactor: 1,
  mobile: false,
});
const cid = "eaaa75f8-2149-452d-8c0e-e76d6c584029";
await call("Page.navigate", { url: base + "/?campaign=" + cid + "#inventory" });
await until("document.querySelectorAll('.package-row').length > 2000");
let count = await evaluate("document.querySelectorAll('.package-row').length");
const controls = (id, value, event = "change") =>
  evaluate(
    `document.getElementById(${JSON.stringify(id)}).value=${JSON.stringify(value)};document.getElementById(${JSON.stringify(id)}).dispatchEvent(new Event(${JSON.stringify(event)}))`,
  );
const screenshot = async (name) => {
  const shot = await call("Page.captureScreenshot", { format: "png" });
  await writeFile(out + "/" + name + ".png", Buffer.from(shot.data, "base64"));
};
await screenshot("packages-desktop");
assert.equal(
  await evaluate("document.querySelectorAll('.pagination').length"),
  0,
);
assert.ok(
  await evaluate(
    "document.querySelector('.package-description').textContent.length > 5",
  ),
);
await controls("search", "ambisonics", "input");
await until(
  "document.querySelectorAll('.package-row').length > 0 && document.querySelectorAll('.package-row').length < 100",
);
assert.ok(
  await evaluate(
    "document.querySelector('#packages').textContent.includes('AMB-plugins')",
  ),
  "Description-only search",
);
await evaluate("document.getElementById('package-paths').click()");
assert.match(
  await evaluate("document.querySelector('.package-path').href"),
  /github.com\/lessrest\/filnixpkgs\/blob\/400439/,
);
await screenshot("packages-search");
await controls("search", "", "input");
await until(`document.querySelectorAll('.package-row').length === ${count}`);
// CSV includes the full filtered set, not just the visible viewport.
await evaluate(
  `window.__blob=null;window.__createURL=URL.createObjectURL;window.__anchorClick=HTMLAnchorElement.prototype.click;URL.createObjectURL=(b)=>{window.__blob=b;return window.__createURL(b)};HTMLAnchorElement.prototype.click=function(){};document.getElementById('package-export').click();URL.createObjectURL=window.__createURL;HTMLAnchorElement.prototype.click=window.__anchorClick`,
);
assert.ok(
  await evaluate(
    `window.__blob.text().then(s=>s.includes('"Package","Version","Description"') && s.includes('"AMB-plugins"'))`,
  ),
);
await controls("filter", "all");
await until("document.querySelectorAll('.package-row').length === 13772");
assert.match(
  await evaluate("document.getElementById('matches').textContent"),
  /13,772/,
);
await controls("package-sort", "name-desc");
const descending = await evaluate(
  "document.querySelector('.package-name').textContent",
);
await controls("package-sort", "name");
assert.notEqual(
  await evaluate("document.querySelector('.package-name').textContent"),
  descending,
);
await controls("filter", "failed");
await until("document.querySelectorAll('.package-row').length > 500");
assert.equal(
  await evaluate(
    "[...document.querySelectorAll('.package-state')].every(n=>n.textContent==='Failed')",
  ),
  true,
);
assert.ok(
  await evaluate("document.querySelectorAll('.package-reason').length > 500"),
);
await controls("package-sort", "duration");
await screenshot("packages-failures");
// Refresh preserves reading position; routine dashboard polling never replaces the list.
await evaluate(
  "window.scrollTo(0,3500); window.__firstRow=document.querySelector('.package-row');window.__scroll=scrollY",
);
await wait(5500);
assert.equal(
  await evaluate("window.__firstRow===document.querySelector('.package-row')"),
  true,
);
await evaluate("document.getElementById('package-refresh').click()");
await until("!document.getElementById('package-refresh').disabled");
assert.ok(await evaluate("Math.abs(window.__scroll-scrollY)<5"));
await controls("filter", "available");
await controls("package-sort", "name");
count = await evaluate("document.querySelectorAll('.package-row').length");
await controls("search", "hello", "input");
await until(
  "[...document.querySelectorAll('.package-name')].some(n=>n.textContent==='hello')",
);
await evaluate(
  "[...document.querySelectorAll('.package-name')].find(n=>n.textContent==='hello').click()",
);
await until("document.getElementById('detail').open");
assert.ok(
  await evaluate(
    "document.querySelector('#detail .package-source').href.includes('/blob/400439')",
  ),
);
assert.ok(
  await evaluate(
    "document.querySelector('#detail .package-description').textContent.length>10",
  ),
);
await screenshot("package-detail");
await evaluate("document.getElementById('close-detail').click()");
await controls("search", "", "input");
await until(`document.querySelectorAll('.package-row').length === ${count}`);
await evaluate("window.scrollTo(0,0)");
await call("Emulation.setTouchEmulationEnabled", {
  enabled: true,
  maxTouchPoints: 5,
});
for (const width of [390, 320]) {
  await call("Emulation.setDeviceMetricsOverride", {
    width,
    height: 900,
    deviceScaleFactor: 1,
    mobile: true,
  });
  await wait(200);
  assert.ok(
    await evaluate("document.documentElement.scrollWidth<=innerWidth"),
    "No horizontal overflow at " + width,
  );
  assert.equal(
    await evaluate(
      "getComputedStyle(document.getElementById('search')).fontSize",
    ),
    "16px",
  );
  await screenshot("packages-mobile-" + width);
}
await call("Network.enable");
await call("Network.emulateNetworkConditions", {
  offline: true,
  latency: 0,
  downloadThroughput: 0,
  uploadThroughput: 0,
});
await evaluate("document.getElementById('package-refresh').click()");
await until(
  "document.getElementById('package-freshness').textContent.includes('retained')",
);
assert.equal(
  await evaluate("document.querySelectorAll('.package-row').length"),
  count,
);
await controls("search", "library", "input");
await until(
  "document.querySelectorAll('.package-row').length>0 && document.querySelectorAll('.package-row').length<1000",
);
await call("Network.emulateNetworkConditions", {
  offline: false,
  latency: 0,
  downloadThroughput: -1,
  uploadThroughput: -1,
});
// A quick campaign switch cannot publish an obsolete request into the current list.
await controls("search", "", "input");
await evaluate(
  `const select=document.getElementById('campaign-select');select.selectedIndex=1;select.dispatchEvent(new Event('change'));select.value=${JSON.stringify(cid)};select.dispatchEvent(new Event('change'))`,
);
await until(
  "document.querySelectorAll('.package-row').length > 2000 && !document.getElementById('package-refresh').disabled",
);
assert.equal(
  await evaluate("new URLSearchParams(location.search).get('campaign')"),
  cid,
);
assert.deepEqual(errors, []);
await writeFile(
  out + "/checks.json",
  JSON.stringify({ available: count, fullInventory: 13772, errors }, null, 2),
);
await call("Page.close");
ws.close();
console.log("Package browser checks passed", {
  available: count,
  fullInventory: 13772,
});
