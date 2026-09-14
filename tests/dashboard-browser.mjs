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
await go(base + "/", "document.querySelector('#summary') && window.htmx");
assert.equal(await evaluate("document.querySelector('#workspace').dataset.campaign"),cid);
assert.equal(await evaluate("document.documentElement.scrollWidth"),390);
await screenshot("activity-mobile");
const initialSample = await evaluate("Number(document.querySelector('#activity-feed').dataset.sampled)");
await wait(6200);
assert.ok(await evaluate("Number(document.querySelector('#activity-feed').dataset.sampled)") > initialSample, 'Timeline and recent batches refresh');
await evaluate("document.querySelector('#activity-toggle').click()");
await until("document.querySelector('#activity-feed').dataset.watch === '0'");
const heldSample = await evaluate("document.querySelector('#activity-feed').dataset.sampled");
await wait(6200);
assert.equal(await evaluate("document.querySelector('#activity-feed').dataset.sampled"),heldSample,'Paused history stays still');
assert.equal(await evaluate("document.querySelector('#summary').getAttribute('hx-trigger').includes('every')"),true);
await evaluate("document.querySelector('#activity-toggle').click()");
await until("document.querySelector('#activity-feed').dataset.watch === '1'");

await go(url(old,"/packages"), "document.querySelectorAll('#package-list tbody tr').length > 3000");
const fonts=await evaluate("[...document.querySelector('#package-list tbody tr').querySelectorAll('a,span,div')].map(e=>({size:getComputedStyle(e).fontSize,family:getComputedStyle(e).fontFamily}))");
assert.ok(fonts.every(f=>f.size==='14px' && !f.family.includes('mono')));
assert.ok(await evaluate("document.querySelector('#package-list tbody').getBoundingClientRect().top < 205"));
await screenshot("packages-mobile");
await evaluate("scrollTo(0,2500)"); await wait(150);
const before=await evaluate("scrollY");
await evaluate("[...document.querySelectorAll('#package-list tbody a')].find(e=>{const r=e.getBoundingClientRect(); return r.top>100 && r.top<600}).click()");
await until("!document.querySelector('#package-list') && document.querySelector('#content h1')");
await until("scrollY < 10");
await screenshot("package-mobile");
await evaluate("history.back()");
await until("document.querySelector('#package-list')");
await wait(600);
const back=await evaluate("scrollY");
assert.ok(Math.abs(before-back)<30,`Back restores scroll: ${before} -> ${back}`);
await evaluate("history.forward()");await until("!document.querySelector('#package-list') && document.querySelector('#content h1')");
await go(url(old,"/batches?sort=longest&kind=build"), "document.querySelectorAll('tbody tr').length > 100");
assert.equal(await evaluate("document.querySelector('select[name=sort]').value"),'longest');
await screenshot("batches-mobile");
await go(url(cid,"/dependencies"), "document.querySelector('#dependency-region')");
await screenshot("dependencies-mobile");
await go(url(cid,"/log"), "document.querySelectorAll('[data-offset]').length > 0");
await wait(800);
console.log('log',await evaluate("({attempt:document.querySelector('#log-reader').dataset.attempt, follow:document.querySelector('#log-reader').dataset.follow,lines:document.querySelectorAll('[data-offset]').length,fonts:[...new Set([...document.querySelectorAll('#log-scroll pre')].map(e=>getComputedStyle(e).fontSize))],width:document.documentElement.scrollWidth})"));
assert.equal(await evaluate("document.documentElement.scrollWidth"),390);
assert.deepEqual(await evaluate("[...new Set([...document.querySelectorAll('#log-scroll pre')].map(e=>getComputedStyle(e).fontSize))]"),['12px']);
await screenshot("log-mobile");
await evaluate("document.querySelector('#log-tools details').open=true");
await wait(4500);
assert.equal(await evaluate("document.querySelector('#log-tools details').open"),true,'Log options remain open across refreshes');
await screenshot("log-options-mobile");
await evaluate("document.querySelector('#log-tools details').open=false");

// Fail one cursor request and hold the next beyond its polling interval.
let cursorRequests = 0, delayedFinished = false, interruptionVisible = false;
await call("Fetch.enable", {patterns:[{urlPattern:"*part=chunk*",requestStage:"Request"}]});
const intercept = async (event) => {
  const m=JSON.parse(event.data);
  if(m.method!=="Fetch.requestPaused") return;
  const requestId=m.params.requestId;
  cursorRequests++;
  try {
    if(cursorRequests===1) await call("Fetch.failRequest",{requestId,errorReason:"Failed"});
    else {
      if(cursorRequests===2) {
        interruptionVisible = await evaluate("!document.querySelector('#connection-status').hidden");
        await wait(4500);
      }
      await call("Fetch.continueRequest",{requestId});
      if(cursorRequests===2) delayedFinished=true;
    }
  } catch(error) { errors.push(error); }
};
ws.addEventListener("message",intercept);
await wait(13500);
await call("Fetch.disable");ws.removeEventListener("message",intercept);
assert.ok(cursorRequests>=3 && delayedFinished,`Cursor recovers from failure and slowness: ${cursorRequests}`);
assert.equal(interruptionVisible, true, 'A failed live request is visible');
await wait(1000);
assert.equal(await evaluate("document.querySelector('#connection-status').hidden"),true,'The error clears when that reader recovers');
assert.equal(await evaluate("new Set([...document.querySelectorAll('[data-offset]')].map(e=>e.dataset.offset)).size === document.querySelectorAll('[data-offset]').length"),true);
await evaluate("document.querySelector('#log-toggle').click()");
await until("document.querySelector('#log-reader').dataset.follow==='0' && !document.querySelector('#log-reader').dataset.pausing");
await wait(300);
assert.equal(await evaluate("document.querySelector('#log-cursor')?.getAttribute('hx-trigger') || 'click'"),'click');
await evaluate("document.querySelector('#log-toggle').click()");
await until("document.querySelector('#log-reader').dataset.follow==='1'");
await wait(800);
await evaluate("document.querySelector('#log-scroll').scrollTop-=250");
await until("document.querySelector('#log-reader').dataset.follow==='0' && !document.querySelector('#log-reader').dataset.pausing");
await screenshot("log-paused-mobile");
await call("Emulation.setDeviceMetricsOverride", {width:1440,height:1000,deviceScaleFactor:1,mobile:false});
await go(url(cid,"/packages?state=all"), "document.querySelectorAll('#package-list tbody tr').length === 13772");
await screenshot("inventory-desktop");
assert.ok(await evaluate("document.documentElement.scrollWidth <= 1440"));
await go(url(cid,"/log"), "document.querySelectorAll('[data-offset]').length > 0");
await wait(400);await screenshot("log-desktop");
await call("Emulation.setScriptExecutionDisabled",{value:true});
await go(url(old,"/packages?state=tested"), "document.querySelector('#package-list')");
await screenshot("packages-no-js");
await call("Emulation.setScriptExecutionDisabled",{value:false});
assert.equal(requests.filter(u=>u.includes('/api/')&&!u.includes('/download')).length,0,'UI never fetches JSON');
assert.deepEqual(errors,[]);
console.log(JSON.stringify({passed:true,requests:requests.length,jsonRequests:0,backScroll:[before,back]},null,2));
} finally {
ws.close(); await fetch("http://127.0.0.1:9228/json/close/"+tab.id);
}
