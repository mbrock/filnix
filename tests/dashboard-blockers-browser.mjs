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
await go(url(cid,"/packages/13789"), "document.querySelector('#package-detail')");
assert.match(await evaluate("document.querySelector('#package-scheduling').textContent"), /not queued/);
await screenshot("blocked-package-mobile");
const failure = await evaluate("[...document.querySelectorAll('#package-detail a')].find(a=>a.textContent==='Failure log').href");
const failureDrv = new URL(failure).searchParams.get("drv");
await evaluate("[...document.querySelectorAll('#package-detail a')].find(a=>a.textContent==='Failure log').click()");
await until("document.querySelector('#log-reader')");
await until("!document.querySelector('#log-search') && document.querySelector('[data-offset]')");
await screenshot("failure-log-mobile");
assert.equal(new URL(await evaluate("location.href")).searchParams.get("drv"), failureDrv);
assert.ok(await evaluate("document.querySelector('#log-scroll').innerText.length > 100"));
await call("Page.navigateToHistoryEntry", {entryId:(await call("Page.getNavigationHistory")).entries.at(-2).id});
await until("document.querySelector('#package-detail')");
await evaluate("[...document.querySelectorAll('#package-detail a')].find(a=>a.textContent==='Planning log').click()");
await until("document.querySelector('#log-reader')");
assert.equal(new URL(await evaluate("location.href")).searchParams.get("drv"),null);
assert.match(await evaluate("document.querySelector('select[name=drv]').innerText"),/Planning output/);
await screenshot("planning-log-mobile");
// A real stopped dependency whose output ended long before the batch's tail.
await go(url(cid,'/dependencies?focus='+encodeURIComponent(failureDrv)),"document.querySelector('#focus-node')");
assert.match(await evaluate("document.querySelector('#focus-node').innerText"),/Not queued/);
await screenshot("failed-dependency-mobile");
// A native dependency has exactly the same derivation in both campaigns.
const reused = "/nix/store/mv1dir1wb7v4wphxw6lqiikxx8l0mlrz-qtsvg-5.15.17.drv";
await go(url(cid,"/dependencies?focus="+encodeURIComponent(reused)),"document.querySelector('#focus-node')");
assert.match(await evaluate("document.querySelector('#focus-node').innerText"),/From The first Filnix inventory/);
const earlier = await evaluate("[...document.querySelectorAll('#focus-node a')].find(a=>a.textContent==='Failure log').href");
assert.ok(earlier.includes('/campaigns/'+old+'/batches/'));
await screenshot("reused-failure-mobile");
await evaluate("[...document.querySelectorAll('#focus-node a')].find(a=>a.textContent==='Failure log').click()");
await until("document.querySelector('#log-reader')");
await until("!document.querySelector('#log-search') && document.querySelector('[data-offset]')");
assert.ok((await evaluate("location.pathname")).includes('/campaigns/'+old+'/'));
await screenshot("earlier-campaign-log-mobile");
assert.equal(errors.length,0,JSON.stringify(errors));
console.log(JSON.stringify({passed:true,requests:requests.length,failureDrv}));
} finally {
ws.close(); await fetch("http://127.0.0.1:9228/json/close/"+tab.id);
}
