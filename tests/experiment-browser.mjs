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
  /Connected/,
);
let shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/desktop.png", Buffer.from(shot.data, "base64"));
assert.equal(
  await evaluate("document.querySelector('#history-record').open"),
  false,
);
await evaluate("document.querySelector('[data-tab=dependencies]').click()");
assert.equal(await evaluate("location.hash"), "#dependency-map");
await evaluate("history.back()");
await wait(150);
assert.equal(
  await evaluate("document.querySelector('#history').hidden"),
  false,
);
await evaluate("history.forward()");
await wait(150);
assert.equal(
  await evaluate("document.querySelector('#dependency-map').hidden"),
  false,
);
assert.ok(
  await evaluate("document.querySelector('#graph-focus [data-drv]') !== null"),
);
await evaluate(
  "document.getElementById('graph-available').checked=true;document.getElementById('graph-available').dispatchEvent(new Event('change'))",
);
await wait(400);
assert.ok(
  await evaluate("document.querySelectorAll('#graph-edges > path').length > 0"),
);
const originalFocus = await evaluate(
  "document.querySelector('#graph-focus [data-drv]').dataset.drv",
);
const inputFocus = await evaluate(
  "document.querySelector('#graph-inputs [data-drv]').dataset.drv",
);
await evaluate("document.querySelector('#graph-inputs [data-drv]').click()");
await until(
  `document.querySelector('#graph-focus [data-drv]')?.dataset.drv === ${JSON.stringify(inputFocus)}`,
);
assert.notEqual(
  await evaluate(
    "document.querySelector('#graph-focus [data-drv]').dataset.drv",
  ),
  originalFocus,
);
assert.equal(
  await evaluate(
    "document.getElementById('graph-follow').getAttribute('aria-pressed')",
  ),
  "false",
);
await evaluate("document.getElementById('graph-back').click()");
await until(
  `document.querySelector('#graph-focus [data-drv]')?.dataset.drv === ${JSON.stringify(originalFocus)}`,
);
assert.equal(
  await evaluate(
    "document.querySelector('#graph-focus [data-drv]').dataset.drv",
  ),
  originalFocus,
);
await evaluate("document.querySelector('[data-tab=dependencies]').click()");
await wait(100);
shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/graph-desktop.png", Buffer.from(shot.data, "base64"));
await evaluate("document.querySelector('[data-tab=packages]').click()");
await until("document.querySelectorAll('.package-name').length > 2000");
await evaluate(
  "[...document.querySelectorAll('.package-name')].find(n=>n.textContent==='hello').click()",
);
await until(
  "document.getElementById('detail').open && document.querySelector('#detail .package-description') !== null",
);
assert.equal(await evaluate("document.getElementById('detail').open"), true);
assert.match(
  await evaluate("document.getElementById('detail-content').textContent"),
  /Fil-C compiler/,
);
shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/package.png", Buffer.from(shot.data, "base64"));
await evaluate("document.getElementById('close-detail').click()");
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
await call("Emulation.setTouchEmulationEnabled", {
  enabled: true,
  maxTouchPoints: 5,
});
shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/mobile.png", Buffer.from(shot.data, "base64"));
await call("Emulation.setDeviceMetricsOverride", {
  width: 320,
  height: 740,
  deviceScaleFactor: 1,
  mobile: true,
});
await evaluate("document.querySelector('#campaign-options summary').click()");
assert.ok(
  await evaluate(
    "document.querySelector('#campaign-options .menu-body').getBoundingClientRect().left >= 0 && document.documentElement.scrollWidth<=innerWidth",
  ),
  "Campaign menu fits a narrow phone",
);
shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/mobile-campaign.png", Buffer.from(shot.data, "base64"));
await evaluate("document.querySelector('#campaign-options summary').click()");
await call("Emulation.setDeviceMetricsOverride", {
  width: 390,
  height: 1000,
  deviceScaleFactor: 1,
  mobile: true,
});
await evaluate("document.querySelector('[data-tab=dependencies]').click()");
await wait(100);
shot = await call("Page.captureScreenshot", { format: "png" });
await writeFile(out + "/graph-mobile.png", Buffer.from(shot.data, "base64"));
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
assert.match(
  await evaluate("document.getElementById('graph-freshness').textContent"),
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
  /Connected/,
);
assert.deepEqual(errors, []);
console.log(
  "Browser checks passed: live dependency arrows, navigation/back, pinned focus, full inventory, recipe detail, mobile width, disconnect/reconnect, no JS exceptions.",
);
ws.close();
await fetch("http://127.0.0.1:9228/json/close/" + tab.id);
