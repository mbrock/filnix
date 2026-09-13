// Exercise the read-only history viewer against a real campaign, without builds.
// Requires Chromium --remote-debugging-port=9228 and the first Filnix inventory.
import { mkdir, writeFile } from "node:fs/promises";
import assert from "node:assert/strict";
const base = process.argv[2] || "http://127.0.0.1:8778";
const out = process.argv[3] || "results/experiment-history-ui";
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
const evaluate = async (expression) => {
  const r = await call("Runtime.evaluate", {
    expression,
    returnByValue: true,
    awaitPromise: true,
  });
  if (r.exceptionDetails) throw Error(JSON.stringify(r.exceptionDetails));
  return r.result.value;
};
const wait = (ms) => new Promise((r) => setTimeout(r, ms));
async function until(expression) {
  for (let n = 0; n < 150; n++) {
    if (await evaluate(expression)) return;
    await wait(100);
  }
  assert.fail("Timed out: " + expression);
}
async function capture(name) {
  const shot = await call("Page.captureScreenshot", { format: "png" });
  await writeFile(out + "/" + name + ".png", Buffer.from(shot.data, "base64"));
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
await until(
  "document.querySelectorAll('#history-rows tr').length===24 && !document.querySelector('#history-record').open",
);
assert.ok(
  await evaluate(
    "document.querySelectorAll('#timeline-build button').length>12",
  ),
);
assert.ok(
  await evaluate("document.querySelectorAll('#timeline-plan button').length>1"),
);
assert.match(
  await evaluate("document.getElementById('history-page').textContent"),
  /1–24/,
);
await capture("desktop");
await evaluate("document.querySelector('.ledger-scroll').scrollTop=100");
await until(
  "document.getElementById('history-follow').getAttribute('aria-pressed')==='false'",
);
await evaluate("document.getElementById('history-follow').click()");
await until(
  "document.getElementById('history-follow').getAttribute('aria-pressed')==='true'",
);
const first = await evaluate(
  "document.querySelector('#history-rows tr').dataset.attempt",
);
await evaluate("document.getElementById('history-older').click()");
await until(
  "document.getElementById('history-page').textContent.includes('25–')",
);
assert.equal(
  await evaluate(
    "document.getElementById('history-follow').getAttribute('aria-pressed')",
  ),
  "false",
);
const old = await evaluate(
  "document.querySelector('#history-rows tr').dataset.attempt",
);
assert.notEqual(old, first);
await evaluate(
  "document.querySelector('#history-rows .history-inspect').click()",
);
await until(
  `document.getElementById('history-selection').textContent===${JSON.stringify(old.slice(0, 8))}`,
);
await evaluate(
  "document.querySelector('#history-close').click();document.querySelector('#history-rows .history-inspect').focus();document.querySelector('.ledger-scroll').scrollTop=120",
);
const scroll = await evaluate(
  "document.querySelector('.ledger-scroll').scrollTop",
);
await wait(5400);
assert.equal(
  await evaluate("document.querySelector('#history-rows tr').dataset.attempt"),
  old,
);
assert.equal(
  await evaluate("document.activeElement.className"),
  "history-inspect",
);
assert.equal(
  await evaluate("document.querySelector('.ledger-scroll').scrollTop"),
  scroll,
);
await evaluate("document.querySelector('#history-rows .history-log').click()");
await until(
  "document.getElementById('log-view').open && document.getElementById('log-lines').children.length>0",
);
assert.equal(
  await evaluate("document.getElementById('log-attempt').value"),
  old,
);
await capture("historical-log");
await evaluate(
  "document.getElementById('log-close').click();document.getElementById('history-follow').click()",
);
await until(
  "document.getElementById('history-page').textContent.includes('1–24')",
);
await evaluate(
  "document.getElementById('history-search').value='hello';document.getElementById('history-search').dispatchEvent(new Event('input'))",
);
await until(
  "document.querySelectorAll('#history-rows tr').length<24 && document.querySelectorAll('#history-rows tr').length>0",
);
assert.ok(
  await evaluate(
    "[...document.querySelectorAll('.history-targets')].every(n=>n.title.includes('hello'))",
  ),
);
await capture("search");
await evaluate(
  "document.getElementById('history-search').value='';document.getElementById('history-search').dispatchEvent(new Event('input'))",
);
await wait(400);
await evaluate(
  "document.getElementById('history-outcome').value='error';document.getElementById('history-outcome').dispatchEvent(new Event('change'))",
);
await until(
  "document.querySelector('#history-rows tr') && [...document.querySelectorAll('#history-rows .history-result')].every(n=>n.classList.contains('error'))",
);
await evaluate(
  "document.getElementById('history-window').value='3600';document.getElementById('history-window').dispatchEvent(new Event('change'))",
);
await wait(350);
assert.ok(
  await evaluate(
    "document.querySelectorAll('#timeline-build button').length>0",
  ),
);
await evaluate("document.querySelector('#timeline-build button').click()");
await until(
  "document.querySelector('#timeline-build button.selected') && document.querySelector('.record-facts')",
);
assert.equal(
  await evaluate(
    "document.querySelector('#timeline-build button.selected').dataset.attempt.slice(0,8)",
  ),
  await evaluate("document.getElementById('history-selection').textContent"),
);
await capture("timeline-selection");
await evaluate("document.querySelector('#history-close').click()");
// The new-admission badge is a browser-only fixture; cursor consistency is also
// verified against actual SQLite inserts in test_experiment_history.py.
await evaluate(
  `window.historyOriginalFetch=window.fetch;window.fetch=async (...args)=>{const r=await window.historyOriginalFetch(...args);if(String(args[0]).startsWith('/api/history?')){const d=await r.json();d.newer=7;return new Response(JSON.stringify(d),{status:200,headers:{'Content-Type':'application/json'}});}return r;}`,
);
await until(
  "document.getElementById('history-follow').textContent.includes('7 new')",
);
await evaluate(
  "window.fetch=window.historyOriginalFetch;delete window.historyOriginalFetch;document.getElementById('history-follow').click()",
);
await until(
  "document.getElementById('history-follow').getAttribute('aria-pressed')==='true'",
);
await call("Network.enable");
await call("Network.emulateNetworkConditions", {
  offline: true,
  latency: 0,
  downloadThroughput: 0,
  uploadThroughput: 0,
});
await until(
  "document.getElementById('history-freshness').textContent.includes('Connection lost')",
);
assert.ok(
  await evaluate("document.querySelectorAll('#history-rows tr').length>0"),
);
await call("Network.emulateNetworkConditions", {
  offline: false,
  latency: 0,
  downloadThroughput: -1,
  uploadThroughput: -1,
});
await until(
  "document.getElementById('history-freshness').textContent.startsWith('Live')",
);
await evaluate(
  "document.getElementById('history-window').value='0';document.getElementById('history-window').dispatchEvent(new Event('change'));document.getElementById('history-outcome').value='';document.getElementById('history-outcome').dispatchEvent(new Event('change'));window.scrollTo(0,0)",
);
await call("Emulation.setDeviceMetricsOverride", {
  width: 390,
  height: 1000,
  deviceScaleFactor: 1,
  mobile: true,
});
await call("Emulation.setTouchEmulationEnabled", {
  enabled: true,
  maxTouchPoints: 5,
});
await wait(400);
assert.equal(
  await evaluate("document.documentElement.scrollWidth<=innerWidth"),
  true,
);
await capture("mobile");
await evaluate(
  "document.getElementById('history').scrollIntoView({block:'start'})",
);
await capture("mobile-history");
assert.ok(
  await evaluate(
    "document.querySelector('.ledger-scroll').scrollWidth<=document.querySelector('.ledger-scroll').clientWidth",
  ),
);
await evaluate("window.scrollTo(0,750)");
await until(
  "document.querySelector('#history-follow').getAttribute('aria-pressed')==='false'",
);
await evaluate("document.querySelector('#history-older').click()");
await until(
  "document.querySelector('#history-page').textContent.includes('25–')",
);
assert.ok(
  await evaluate(
    "document.querySelector('.ledger-scroll').getBoundingClientRect().top >= document.querySelector('.app-chrome').getBoundingClientRect().bottom",
  ),
  "Pagination returns to the first row",
);
await capture("mobile-results");
await evaluate(
  "document.querySelector('#history-rows .history-inspect').click()",
);
await until(
  "document.querySelector('#history-record').open && document.querySelector('.record-facts')",
);
await capture("mobile-record");
await evaluate("document.querySelector('#history-close').click()");
// Rapid campaign changes must not let an old response repopulate the new view.
await evaluate(
  "document.getElementById('campaign-select').selectedIndex=1;document.getElementById('campaign-select').dispatchEvent(new Event('change'))",
);
await until(
  "document.getElementById('campaign-name').textContent.includes('calibration') && document.querySelectorAll('#history-rows tr').length<24",
);
await evaluate(
  "document.getElementById('campaign-select').selectedIndex=0;document.getElementById('campaign-select').dispatchEvent(new Event('change'))",
);
await until(
  "document.getElementById('history-page').textContent.includes('1–24')",
);
assert.deepEqual(errors, []);
console.log(
  "History browser checks passed: complete timeline, stable pagination/focus/scroll, attempt inspection and log opening, target search, outcome filters, timeline range/selection, new-admission notice, offline recovery, mobile ledger without horizontal scrolling, campaign switch.",
);
ws.close();
await fetch("http://127.0.0.1:9228/json/close/" + tab.id);
