// Run against an installed dashboard and Chromium's loopback debugging endpoint.
// node tests/experiment-browser.mjs http://127.0.0.1:8777 results/experiment-ui
import { mkdir, writeFile } from "node:fs/promises";
import assert from "node:assert/strict";
const base = process.argv[2] || "http://127.0.0.1:8777",
  out = process.argv[3] || "results/experiment-ui";
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
await call("Runtime.enable");
await call("Page.enable");
await call("Emulation.setDeviceMetricsOverride", {
  width: 1440,
  height: 1100,
  deviceScaleFactor: 1,
  mobile: false,
});
await call("Page.navigate", { url: base });
await wait(1500);
assert.equal(
  await evaluate("document.getElementById('selected').textContent"),
  "13,772",
);
assert.match(
  await evaluate("document.getElementById('connection').textContent"),
  /connected/,
);
let shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/desktop.png", Buffer.from(shot.data, "base64"));
await evaluate(
  "document.getElementById('search').value='hello';document.getElementById('search').dispatchEvent(new Event('input'))",
);
await wait(600);
assert.ok(
  await evaluate(
    "document.querySelectorAll('.pkg').length > 0 && document.querySelectorAll('.pkg').length < 50",
  ),
);
await evaluate(
  "[...document.querySelectorAll('.pkg')].find(n=>n.querySelector('.pkg-name').firstChild.textContent==='hello').click()",
);
await wait(300);
assert.equal(await evaluate("document.getElementById('detail').open"), true);
assert.match(
  await evaluate("document.getElementById('detail-content').textContent"),
  /Fil-C compiler/,
);
shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/package.png", Buffer.from(shot.data, "base64"));
await evaluate(
  "document.getElementById('close-detail').click();document.getElementById('search').value='';document.getElementById('search').dispatchEvent(new Event('input'))",
);
await wait(600);
await call("Emulation.setDeviceMetricsOverride", {
  width: 390,
  height: 1000,
  deviceScaleFactor: 1,
  mobile: true,
});
await wait(100);
assert.equal(
  await evaluate("document.documentElement.scrollWidth <= innerWidth"),
  true,
);
shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/mobile.png", Buffer.from(shot.data, "base64"));
await call("Network.enable");
await call("Network.emulateNetworkConditions", {
  offline: true,
  latency: 0,
  downloadThroughput: 0,
  uploadThroughput: 0,
});
await wait(5500);
assert.match(
  await evaluate("document.getElementById('connection').textContent"),
  /lost/,
);
await call("Network.emulateNetworkConditions", {
  offline: false,
  latency: 0,
  downloadThroughput: -1,
  uploadThroughput: -1,
});
await wait(5500);
assert.match(
  await evaluate("document.getElementById('connection').textContent"),
  /connected/,
);
assert.deepEqual(errors, []);
console.log(
  "Browser checks passed: real inventory, search, recipe detail, mobile width, disconnect/reconnect, no JS exceptions.",
);
ws.close();
await fetch("http://127.0.0.1:9228/json/close/" + tab.id);
