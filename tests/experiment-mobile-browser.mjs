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
  for (let n = 0; n < 200; n++) {
    if (await evaluate(expression)) return;
    await wait(100);
  }
  assert.fail("Timed out: " + expression);
}
await call("Runtime.enable");
await call("Page.enable");
await call("Network.enable");
const cid = "eaaa75f8-2149-452d-8c0e-e76d6c584029";
const screenshot = async (name) => {
  const s = await call("Page.captureScreenshot", { format: "png" });
  await writeFile(out + "/" + name + ".png", Buffer.from(s.data, "base64"));
};
const change = (id, value) =>
  evaluate(
    `document.getElementById(${JSON.stringify(id)}).value=${JSON.stringify(value)};document.getElementById(${JSON.stringify(id)}).dispatchEvent(new Event('change'))`,
  );
await call("Emulation.setDeviceMetricsOverride", {
  width: 390,
  height: 844,
  deviceScaleFactor: 1,
  mobile: true,
});
await call("Emulation.setTouchEmulationEnabled", {
  enabled: true,
  maxTouchPoints: 5,
});
await call("Page.navigate", { url: base + "/?campaign=" + cid + "#inventory" });
await until("document.querySelectorAll('.package-row').length>2000");
assert.equal(await evaluate("document.querySelector('#search')"), null);
const firstTop = await evaluate(
  "document.querySelector('.package-row').getBoundingClientRect().top",
);
assert.ok(firstTop < 130, "Content begins near the top");
const fonts = await evaluate(
  "['.package-name','.package-description','.package-state','.package-version'].map(s=>({size:getComputedStyle(document.querySelector(s)).fontSize,family:getComputedStyle(document.querySelector(s)).fontFamily}))",
);
assert.ok(
  fonts.every((f) => f.size === fonts[0].size && f.family === fonts[0].family),
);
await screenshot("mobile-initial");
await evaluate("scrollTo(0,2000)");
await wait(100);
assert.ok(
  await evaluate(
    "document.querySelector('.app-chrome').getBoundingClientRect().bottom<0 && document.querySelector('.catalog-controls').getBoundingClientRect().bottom<0",
  ),
);
assert.ok(
  await evaluate(
    "document.querySelector('.package-table thead').getBoundingClientRect().height<35",
  ),
);
await screenshot("mobile-scrolled");
// Package -> log -> Back -> package -> Back -> exact place in the list.
const selected = await evaluate(
  `(()=>{const n=[...document.querySelectorAll('.package-name')].find(n=>{const r=n.getBoundingClientRect();return r.top>30 && r.bottom<innerHeight});window.__listY=scrollY;window.__package=n.dataset.package;n.click();return n.dataset.package})()`,
);
await until(
  "document.querySelector('#detail').open && document.querySelector('#detail .package-description')",
);
assert.equal(
  await evaluate("new URLSearchParams(location.search).get('package')"),
  selected,
);
await until(
  "[...document.querySelectorAll('#detail button')].some(n=>n.textContent.includes('recorded build log'))",
);
await evaluate(
  "[...document.querySelectorAll('#detail button')].find(n=>n.textContent.includes('recorded build log')).click()",
);
await until(
  "document.querySelector('#log-view').open && document.querySelector('#log-lines').children.length>0",
);
const logURL = await evaluate("location.href");
await evaluate("history.back()");
await until(
  "!document.querySelector('#log-view').open && document.querySelector('#detail').open",
);
await evaluate("history.back()");
await until(
  "!document.querySelector('#detail').open && Math.abs(scrollY-window.__listY)<3",
);
await evaluate("history.forward()");
await until(
  "document.querySelector('#detail').open && document.querySelector('#detail .package-description')",
);
await evaluate("history.forward()");
await until("document.querySelector('#log-view').open");
assert.equal(await evaluate("location.href"), logURL);
await evaluate("document.querySelector('#log-close').click()");
await until(
  "!document.querySelector('#log-view').open && document.querySelector('#detail').open",
);
await evaluate("document.querySelector('#close-detail').click()");
await until(
  "!document.querySelector('#detail').open && Math.abs(scrollY-window.__listY)<3",
);
// Reload of a deep URL can close its overlay without leaving the site.
await call("Page.navigate", { url: logURL });
await until(
  "document.querySelector('#log-view').open && document.querySelector('#detail').open",
);
await evaluate("document.querySelector('#log-close').click()");
await until(
  "!document.querySelector('#log-view').open && document.querySelector('#detail').open",
);
await evaluate("document.querySelector('#close-detail').click()");
await until(
  "!document.querySelector('#detail').open && document.querySelectorAll('.package-row').length>2000",
);
assert.equal(
  await evaluate("new URLSearchParams(location.search).has('package')"),
  false,
);
// The full unpaginated list remains available to native browser Find.
await change("filter", "all");
await until("document.querySelectorAll('.package-row').length===13772");
assert.ok(
  await evaluate(
    "window.find(document.querySelector('.package-row:last-child .package-name').textContent)",
  ),
);
await evaluate("getSelection().removeAllRanges();scrollTo(0,0)");
await change("filter", "failed");
await until(
  "document.querySelectorAll('.package-row').length>900 && [...document.querySelectorAll('.package-state')].every(n=>n.textContent==='Failed')",
);
await screenshot("mobile-failures");
await evaluate("history.back()");
await until(
  "document.getElementById('filter').value==='all' && document.querySelectorAll('.package-row').length===13772",
);
await evaluate("history.back()");
await until(
  "document.getElementById('filter').value==='available' && document.querySelectorAll('.package-row').length>2000",
);
// Switching views and refreshing do not lose the reading position.
await evaluate("scrollTo(0,2300)");
await wait(100);
await evaluate(
  "window.__listY=scrollY;document.querySelector('[data-tab=activity]').click()",
);
await until("document.body.dataset.view==='activity'");
await evaluate("history.back()");
await until(
  "document.body.dataset.view==='packages' && Math.abs(scrollY-window.__listY)<3",
);
await evaluate("document.querySelector('#package-refresh').click()");
await until("!document.querySelector('#package-refresh').disabled");
assert.ok(await evaluate("Math.abs(scrollY-window.__listY)<3"));
// A delayed package response cannot reopen a detail after Back.
await call("Network.emulateNetworkConditions", {
  offline: false,
  latency: 700,
  downloadThroughput: -1,
  uploadThroughput: -1,
});
await evaluate(
  "document.querySelector('.package-name').click();history.back()",
);
await until("!document.querySelector('#detail').open");
await wait(1000);
assert.equal(await evaluate("document.querySelector('#detail').open"), false);
await call("Network.emulateNetworkConditions", {
  offline: false,
  latency: 0,
  downloadThroughput: -1,
  uploadThroughput: -1,
});
// Campaign changes participate in browser history too.
await evaluate(
  "const s=document.getElementById('campaign-select');s.selectedIndex=1;s.dispatchEvent(new Event('change'))",
);
await until(
  "new URLSearchParams(location.search).get('campaign')!=='" +
    cid +
    "' && !document.querySelector('#package-refresh').disabled",
);
await evaluate("history.back()");
await until(
  "document.querySelectorAll('.package-row').length>2000 && new URLSearchParams(location.search).get('campaign')==='" +
    cid +
    "'",
);
await evaluate("scrollTo(0,0)");
await call("Emulation.setDeviceMetricsOverride", {
  width: 320,
  height: 740,
  deviceScaleFactor: 1,
  mobile: true,
});
await wait(100);
assert.ok(await evaluate("document.documentElement.scrollWidth<=innerWidth"));
await screenshot("mobile-320");
await evaluate("document.querySelector('#package-options summary').click()");
assert.ok(
  await evaluate(
    "document.querySelector('#package-options .menu-body').getBoundingClientRect().left>=0",
  ),
);
await screenshot("mobile-options");
await evaluate("document.querySelector('#package-options summary').click()");
await call("Emulation.setDeviceMetricsOverride", {
  width: 1440,
  height: 1000,
  deviceScaleFactor: 1,
  mobile: false,
});
await call("Emulation.setTouchEmulationEnabled", { enabled: false });
await wait(100);
await screenshot("desktop");
// Batch -> package -> Back -> batch, and Escape follows the same history.
await evaluate("document.querySelector('[data-tab=activity]').click()");
await until("document.querySelector('#history-rows tr') !== null");
await evaluate("document.querySelector('#history-rows tr').click()");
await until(
  "document.querySelector('#history-record').open && document.querySelector('.record-targets button')",
);
const batchURL = await evaluate("location.href");
await evaluate("document.querySelector('.record-targets button').click()");
await until(
  "document.querySelector('#detail').open && document.querySelector('#detail .package-description')",
);
await call("Input.dispatchKeyEvent", {
  type: "keyDown",
  key: "Escape",
  code: "Escape",
  windowsVirtualKeyCode: 27,
});
await call("Input.dispatchKeyEvent", {
  type: "keyUp",
  key: "Escape",
  code: "Escape",
  windowsVirtualKeyCode: 27,
});
await until(
  "!document.querySelector('#detail').open && document.querySelector('#history-record').open",
);
assert.equal(await evaluate("location.href"), batchURL);
await evaluate("document.querySelector('#history-close').click()");
await until("!document.querySelector('#history-record').open");
// Evaluation rows lead with the fatal diagnostic and retain the raw trace.
await evaluate("document.querySelector('[data-tab=packages]').click()");
await change("filter", "evaluation-error");
await until("document.querySelectorAll('.package-row').length>3000");
assert.ok(
  await evaluate(
    "document.querySelector('.package-reason').textContent.includes('marked as broken')",
  ),
);
assert.ok(
  await evaluate(
    "!document.querySelector('.package-reason').textContent.includes('GC Warning')",
  ),
);
await evaluate("scrollTo(0,0)");
await screenshot("evaluation-errors-desktop");
await call("Emulation.setDeviceMetricsOverride", {
  width: 390,
  height: 844,
  deviceScaleFactor: 1,
  mobile: true,
});
await wait(100);
await screenshot("evaluation-errors-mobile");
await evaluate("document.querySelector('.package-name').click()");
await until(
  "document.querySelector('#detail .package-error-summary') !== null",
);
assert.ok(
  await evaluate(
    "document.querySelector('.package-error-summary').textContent.includes('marked as broken')",
  ),
);
assert.equal(
  await evaluate("document.querySelector('.package-diagnostic').open"),
  false,
);
await screenshot("evaluation-error-detail");
await evaluate("document.querySelector('.package-diagnostic summary').click()");
assert.ok(
  await evaluate(
    "document.querySelector('.package-diagnostic pre').textContent.includes('GC Warning: Failed to expand heap')",
  ),
);
await evaluate("document.querySelector('#close-detail').click()");
await until("!document.querySelector('#detail').open");
assert.deepEqual(errors, []);
await writeFile(
  out + "/checks.json",
  JSON.stringify(
    { firstRowTop: firstTop, font: fonts[0], allRows: 13772, errors },
    null,
    2,
  ),
);
await call("Page.close");
ws.close();
console.log("Dense list and browser-history checks passed");
