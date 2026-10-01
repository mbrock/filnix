// Read-only design walk. Chromium must listen on 127.0.0.1:9228.
// node tests/dashboard-design-browser.mjs BASE OUTPUT [audit]
import { mkdir, writeFile } from "node:fs/promises";
import assert from "node:assert/strict";
const [base = "http://127.0.0.1:8777", out = ".amp/in/artifacts/design-tightening", mode] = process.argv.slice(2);
await mkdir(out, { recursive: true });
const tab = await (await fetch("http://127.0.0.1:9228/json/new?about:blank", { method: "PUT" })).json();
const ws = new WebSocket(tab.webSocketDebuggerUrl);
await new Promise(resolve => ws.addEventListener("open", resolve, { once: true }));
let serial = 0;
const pending = new Map(), errors = [], report = [];
ws.addEventListener("message", event => {
  const message = JSON.parse(event.data);
  if (message.id) {
    const request = pending.get(message.id);
    pending.delete(message.id);
    message.error ? request.reject(message.error) : request.resolve(message.result);
  } else if (message.method === "Runtime.exceptionThrown") errors.push(message.params);
});
const call = (method, params = {}) => new Promise((resolve, reject) => {
  const id = ++serial;
  pending.set(id, { resolve, reject });
  ws.send(JSON.stringify({ id, method, params }));
});
const evaluate = async expression => {
  const result = await call("Runtime.evaluate", { expression, returnByValue: true, awaitPromise: true });
  if (result.exceptionDetails) throw new Error(JSON.stringify(result.exceptionDetails));
  return result.result.value;
};
const wait = ms => new Promise(resolve => setTimeout(resolve, ms));
async function until(expression) {
  for (let n = 0; n < 200; n++) {
    if (await evaluate(`Boolean(${expression})`)) return;
    await wait(100);
  }
  throw new Error("Timed out: " + expression);
}
async function go(url, selector) {
  await call("Page.navigate", { url });
  await until(`location.pathname === ${JSON.stringify(new URL(url).pathname)} && document.readyState !== 'loading' && document.querySelector(${JSON.stringify(selector)})`);
  await wait(400);
}
async function capture(name) {
  const screenshot = await call("Page.captureScreenshot", { format: "png" });
  await writeFile(`${out}/${name}.png`, Buffer.from(screenshot.data, "base64"));
}
async function select(name, value) {
  await evaluate(`(() => { const s = document.querySelector('select[name=${name}]'); s.value = ${JSON.stringify(value)}; s.dispatchEvent(new Event('change', {bubbles:true})); })()`);
  await until(`new URL(location.href).searchParams.get(${JSON.stringify(name)}) === ${JSON.stringify(value)}`);
  await wait(350);
}
try {
  await call("Runtime.enable");
  await call("Page.enable");
  await call("Emulation.setDeviceMetricsOverride", { width: 1440, height: 1000, deviceScaleFactor: 2, mobile: false });
  const home = await fetch(base);
  const prefix = new URL(home.url).pathname;
  const page = suffix => base + prefix + suffix;
  for (const [name, suffix, selector] of [
    ["activity", "", "#summary"],
    ["packages", "/packages?state=all", "#package-list"],
    ["batches", "/batches", "#timeline"],
    ["blockers", "/blockers", "#blockers"],
    ["dependencies", "/dependencies?available=1", "#dependency-region"],
  ]) {
    await go(page(suffix), selector);
    const response = await fetch(page(suffix));
    const htmlBytes = (await response.arrayBuffer()).byteLength;
    const metrics = await evaluate(`({url:location.href, title:document.title, rows:document.querySelectorAll('#content tbody tr').length, width:document.documentElement.scrollWidth, fonts:[...new Set([...document.querySelectorAll('#content a, #content td, #content p, header a')].map(e=>getComputedStyle(e).fontSize))]})`);
    report.push({ name, htmlBytes, ...metrics });
    await capture(name);
    if (mode !== "audit") {
      assert.ok(await evaluate("document.querySelector('#controller-heartbeat')?.textContent.includes('Controller')"));
      assert.ok(metrics.width <= 1440, name + " overflows");
      assert.ok(metrics.fonts.every(size => ["12px", "14px", "16px"].includes(size)), JSON.stringify(metrics));
      if (["packages", "batches"].includes(name)) assert.ok(htmlBytes < 300000, name + " HTML budget");
      if (name === "packages") {
        assert.equal(metrics.rows, 100);
        await select("state", "built");
        assert.match(await evaluate("document.title"), /Packages · Built/);
        await evaluate("document.querySelector('nav[aria-label=\"Result pages\"] a').click()");
        await until("new URL(location.href).searchParams.get('page') === '1'");
        await capture("packages-page-2");
        await select("state", "failed");
        assert.ok(!new URL(await evaluate("location.href")).searchParams.has("page"), "filter resets page");
        await capture("packages-failed");
        await evaluate("document.querySelector('#semantic-facet-note').open = true");
        await capture("packages-notes");
      }
      if (name === "batches") {
        assert.ok(metrics.rows <= 50);
        assert.ok(await evaluate("[...document.querySelectorAll('tbody td:first-child > a')].every(a => !a.textContent.includes(', '))"));
        await evaluate("document.documentElement.style.filter = 'grayscale(1)'");
        await capture("batches-grayscale");
        await evaluate("document.documentElement.style.filter = ''");
        await select("kind", "plan");
        await select("sort", "oldest");
        await capture("batches-filtered");
      }
    }
  }
  await go(page("/batches?kind=build&outcome=error"), "tbody tr");
  const batchURL = await evaluate("document.querySelector('tbody td a').href");
  await go(batchURL, "#batch-heading");
  await capture("batch-detail");
  const logURL = await evaluate("[...document.querySelectorAll('#batch-heading a')].find(a => a.textContent === 'Batch log').href");
  await go(logURL, "#log-reader");
  await capture("batch-log");
  if (mode !== "audit") {
    assert.ok(await evaluate("!document.querySelector('#log-tools details')"));
    await select("size", "16");
    await select("wrap", "0");
    await evaluate("document.querySelector('#log-toggle').click()");
    await until("document.querySelector('#log-reader').dataset.follow === '0'");
    await capture("log-paused-unwrapped");
    assert.equal(await evaluate("document.querySelector('select[name=size]').value"), "16");
    assert.equal(await evaluate("document.querySelector('select[name=wrap]').value"), "0");
  }
  await go(page("/log"), "#log-reader");
  await capture("current-batch-log");
  report.push({ name: "current-batch-log", text: await evaluate("document.querySelector('#log-tools')?.innerText || document.querySelector('#log-reader').innerText") });
  if (mode !== "audit") {
    await evaluate("document.querySelector('#log-toggle').click()");
    await until("document.querySelector('#log-reader').dataset.follow === '0'");
    assert.equal(await evaluate("new URL(location.href).searchParams.get('follow')"), "0");
    await capture("current-batch-paused");
    await call("Emulation.setScriptExecutionDisabled", { value: true });
    await go(page("/packages?state=built&page=1"), "#package-list");
    assert.equal(await evaluate("document.querySelectorAll('#package-list tbody tr').length"), 100);
    await capture("packages-no-js");
    await call("Emulation.setScriptExecutionDisabled", { value: false });
  }
  await call("Emulation.setDeviceMetricsOverride", { width: 390, height: 844, deviceScaleFactor: 2, mobile: false });
  for (const [name, suffix, selector] of [["packages-narrow", "/packages?state=all", "#package-list"], ["log-narrow", "/log?follow=0&wrap=0&size=16", "#log-reader"], ["dependencies-narrow", "/dependencies?available=1", "#dependency-region"]]) {
    await go(page(suffix), selector);
    await capture(name);
    if (mode !== "audit") assert.ok(await evaluate("document.documentElement.scrollWidth <= 390"), name + " overflows");
  }
  assert.deepEqual(errors, []);
  await writeFile(`${out}/report.json`, JSON.stringify(report, null, 2));
  console.log(JSON.stringify({ passed: true, report }, null, 2));
} finally {
  ws.close();
  await fetch("http://127.0.0.1:9228/json/close/" + tab.id);
}
