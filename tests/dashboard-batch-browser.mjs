// Run against an installed dashboard and Chromium's loopback debugging endpoint.
// node tests/dashboard-browser.mjs http://127.0.0.1:8777 results/tagflow
import { mkdir, writeFile } from "node:fs/promises";
import assert from "node:assert/strict";
const base = process.argv[2] || "http://127.0.0.1:8777",
  out = process.argv[3] || "results/tagflow";
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
    if (await evaluate("Boolean(" + expression + ")")) return;
    await wait(100);
  }
  assert.fail("Timed out: " + expression);
}
await call("Runtime.enable");
await call("Page.enable");
await call("Network.enable");
const requests = [];
ws.addEventListener("message", (event) => {
  const m = JSON.parse(event.data);
  if (m.method === "Network.requestWillBeSent") requests.push(m.params.request.url);
});
const cid = "3eaf2f72-7c12-4bf2-9934-9646ea9dab4d";
const old = "eaaa75f8-2149-452d-8c0e-e76d6c584029";
const url = (id, suffix) => base + "/campaigns/" + id + suffix;
const screenshot = async (name) => {
  const s = await call("Page.captureScreenshot", { format: "png" });
  await writeFile(out + "/" + name + ".png", Buffer.from(s.data, "base64"));
};
const go = async (url, condition) => {
  await call("Page.navigate", {url}); await until(condition); await wait(250);
};
try {
await call("Emulation.setDeviceMetricsOverride", {width:390,height:844,deviceScaleFactor:1,mobile:true});
const active='fcc0ac77-1099-4ea5-8ec8-0460ab541e4a';
const finished='4187b2a7-d943-4894-80c3-f275d6b1d95f';
await go(url(cid,'/batches/'+active),"document.querySelector('#batch-heading')");
assert.ok(await evaluate("document.querySelectorAll('[data-build-status]').length > 100"));
assert.ok(!(await evaluate("document.querySelector('#batch-status').innerText")).includes('Stopped'));
await screenshot('batch-mobile');
await evaluate('window.scrollTo(0,1200)'); await wait(300);
assert.ok(Math.abs(await evaluate("document.querySelector('#batch-heading').getBoundingClientRect().top")) < 2);
await screenshot('batch-scrolled-mobile');
await go(url(cid,'/batches/'+finished),"document.querySelector('#batch-heading')");
assert.ok(await evaluate("document.querySelector('#batch-heading [data-status=finished-errors]')"));
assert.ok(await evaluate("document.querySelector('[data-build-status=failed]')"));
assert.ok(await evaluate("document.querySelector('[data-build-status=built]')"));
assert.ok(await evaluate("document.querySelector('[data-build-status=tested]')"));
assert.ok(!(await evaluate("document.querySelector('#batch-status').innerText")).includes('Awaiting result'));
await screenshot('finished-batch-mobile');
await evaluate("document.querySelector('[data-build-status=failed] a').click()");
await until("document.querySelector('#log-reader')");
await until("!document.querySelector('#log-search') && document.querySelector('[data-offset]')");
assert.match(await evaluate("document.querySelector('#log-tools').innerText"),/Finished · errors/);
await screenshot('batch-failure-log-mobile');
await go(url(cid,'/batches'),"document.querySelector('#batch-"+finished+"')");
assert.ok(await evaluate("document.querySelector('#batch-"+finished+" [data-status=finished-errors]')"));
await screenshot('batch-list-mobile');
await call('Emulation.setDeviceMetricsOverride',{width:1280,height:900,deviceScaleFactor:1,mobile:false});
await go(url(cid,'/batches/'+finished),"document.querySelector('#batch-heading')");
await screenshot('finished-batch-desktop');
await call('Emulation.setScriptExecutionDisabled',{value:true});
await go(url(cid,'/batches/'+finished),"document.querySelector('#batch-heading')");
assert.ok(await evaluate("document.querySelectorAll('[data-build-status]').length > 100"));
await screenshot('batch-no-js');
assert.equal(errors.length,0,JSON.stringify(errors));
console.log(JSON.stringify({passed:true,requests:requests.length,jsonRequests:requests.filter(u=>u.includes('/api/')).length}));
} finally {
ws.close(); await fetch("http://127.0.0.1:9228/json/close/"+tab.id);
}
