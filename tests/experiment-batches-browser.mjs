// Run against an installed dashboard and Chromium's loopback debugging endpoint.
// node tests/experiment-batches-browser.mjs http://127.0.0.1:8777 results/experiment-batches-ui
import { mkdir, writeFile } from "node:fs/promises";
import assert from "node:assert/strict";
const base = process.argv[2] || "http://127.0.0.1:8777",
  out = process.argv[3] || "results/experiment-batches-ui";
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
  console.error(
    "Browser state",
    await evaluate(
      "({url:location.href,dialogs:[...document.querySelectorAll('dialog')].map(d=>[d.id,d.open]),view:document.body.dataset.view, text:document.body.innerText.slice(0,1200)})",
    ),
    errors,
  );
  assert.fail("Timed out: " + expression);
}
await call("Runtime.enable");
await call("Page.enable");
await call("Network.enable");
const cid = "eaaa75f8-2149-452d-8c0e-e76d6c584029";
const controls = (id, value, event = "change") =>
  evaluate(
    `document.getElementById(${JSON.stringify(id)}).value=${JSON.stringify(value)};document.getElementById(${JSON.stringify(id)}).dispatchEvent(new Event(${JSON.stringify(event)}))`,
  );
const screenshot = async (name) => {
  const shot = await call("Page.captureScreenshot", { format: "png" });
  await writeFile(out + "/" + name + ".png", Buffer.from(shot.data, "base64"));
};
try {
  await call("Emulation.setDeviceMetricsOverride", {
    width: 1440,
    height: 1000,
    deviceScaleFactor: 1,
    mobile: false,
  });
  await call("Page.navigate", {
    url: base + "/?campaign=" + cid + "#batch-timings",
  });
  await until("document.querySelectorAll('.batch-row').length>100");
  const sorted = (direction) =>
    evaluate(
      `(()=>{const times=[...document.querySelectorAll('.batch-row')].map(n=>n.dataset.duration).filter(n=>n!=='').map(Number);return times.every((t,i)=>i===0||${direction}*(t-times[i-1])>=0)})()`,
    );
  assert.ok(await sorted(-1), "Longest first by default");
  assert.equal(
    await evaluate("document.querySelector('.overview').hidden"),
    true,
  );
  const count = await evaluate(
    "document.querySelectorAll('.batch-row').length",
  );
  assert.ok(
    await evaluate(
      `document.querySelectorAll('.batch-interval').length === ${count}`,
    ),
  );
  await screenshot("batches-desktop");
  // Search finds transitive build names and keeps one history entry while typing.
  const baseline = await evaluate("history.length");
  await controls("batch-search", "aws", "input");
  await controls("batch-search", "aws-sdk", "input");
  assert.equal(await evaluate("history.length"), baseline + 1);
  assert.ok(
    await evaluate(
      "document.querySelectorAll('.batch-row').length > 0 && document.querySelectorAll('.batch-row').length < 100",
    ),
  );
  assert.ok(
    await evaluate(
      "[...document.querySelectorAll('.batch-matched')].some(n=>n.textContent.includes('aws-sdk'))",
    ),
  );
  await screenshot("batches-sdk");
  await evaluate("history.back()");
  await until(
    `document.querySelector('#batch-search').value === '' && document.querySelectorAll('.batch-row').length === ${count}`,
  );
  await controls("batch-sort", "shortest");
  assert.ok(await sorted(1));
  await controls("batch-result", "error");
  assert.ok(
    await evaluate(
      "[...document.querySelectorAll('.batch-outcome')].every(n=>n.classList.contains('error'))",
    ),
  );
  await controls("batch-result", "all");
  await controls("batch-kind", "all");
  assert.ok(
    await evaluate("document.querySelectorAll('.batch-row').length>1000"),
  );
  await controls("batch-kind", "build");
  await controls("batch-sort", "longest");
  // Batch -> package -> Escape -> batch -> log -> Back -> batch -> Back -> list.
  await evaluate("scrollTo(0,900)");
  await wait(100);
  await evaluate(
    "window.__batchY=scrollY;const n=[...document.querySelectorAll('.batch-duration a')].find(n=>n.getBoundingClientRect().top>40);window.__aid=n.dataset.batch;n.click()",
  );
  await until(
    "document.querySelector('#history-record').open && document.querySelector('.record-targets button')",
  );
  await screenshot("batch-detail");
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
    "!document.querySelector('#detail').open && document.querySelector('#history-record').open && !new URLSearchParams(location.search).has('package')",
  );
  await wait(200);
  await evaluate("document.querySelector('.record-heading button').click()");
  await until("document.querySelector('#log-view').open");
  const deep = await evaluate("location.href");
  await evaluate("history.back()");
  await until(
    "!document.querySelector('#log-view').open && document.querySelector('#history-record').open",
  );
  await evaluate("history.back()");
  await until(
    "!document.querySelector('#history-record').open && Math.abs(scrollY-window.__batchY)<3",
  );
  await evaluate("history.forward()");
  await until("document.querySelector('#history-record').open");
  await evaluate("document.querySelector('#history-close').click()");
  await until("!document.querySelector('#history-record').open");
  // Status polling never reorders the loaded snapshot.
  await evaluate("window.__row=document.querySelector('.batch-row')");
  await wait(5500);
  assert.ok(
    await evaluate("window.__row === document.querySelector('.batch-row')"),
  );
  await evaluate("document.querySelector('#batch-refresh').click()");
  await until("!document.querySelector('#batch-refresh').disabled");
  assert.ok(await evaluate("Math.abs(scrollY-window.__batchY)<3"));
  // Direct links survive reload and close to the timing browser.
  await call("Page.navigate", { url: deep });
  await until(
    "document.querySelector('#log-view').open && document.querySelector('#history-record').open",
  );
  await evaluate("document.querySelector('#log-close').click()");
  await until("!document.querySelector('#log-view').open");
  await evaluate("document.querySelector('#history-close').click()");
  await until(
    "!document.querySelector('#history-record').open && document.querySelectorAll('.batch-row').length>100",
  );
  await evaluate("scrollTo(0,0)");
  await call("Emulation.setTouchEmulationEnabled", {
    enabled: true,
    maxTouchPoints: 5,
  });
  for (const width of [390, 320]) {
    await call("Emulation.setDeviceMetricsOverride", {
      width,
      height: 844,
      deviceScaleFactor: 1,
      mobile: true,
    });
    await wait(200);
    assert.ok(
      await evaluate("document.documentElement.scrollWidth<=innerWidth"),
      "No horizontal overflow at " + width,
    );
    await screenshot("batches-mobile-" + width);
  }
  await call("Network.emulateNetworkConditions", {
    offline: true,
    latency: 0,
    downloadThroughput: 0,
    uploadThroughput: 0,
  });
  const loaded = await evaluate(
    "document.querySelectorAll('.batch-row').length",
  );
  await evaluate("document.querySelector('#batch-refresh').click()");
  await until(
    "document.querySelector('#batch-freshness').textContent.includes('retained')",
  );
  assert.equal(
    await evaluate("document.querySelectorAll('.batch-row').length"),
    loaded,
  );
  await controls("batch-sort", "shortest");
  assert.ok(await sorted(1));
  await call("Network.emulateNetworkConditions", {
    offline: false,
    latency: 0,
    downloadThroughput: -1,
    uploadThroughput: -1,
  });
  // Switching campaigns cannot leave a previous campaign's batches on screen.
  await evaluate(
    "const s=document.querySelector('#campaign-select');s.selectedIndex=1;s.dispatchEvent(new Event('change'))",
  );
  await until(
    "document.querySelectorAll('.batch-row').length < 100 && !document.querySelector('#batch-refresh').disabled",
  );
  await controls("campaign-select", cid);
  await until(
    "document.querySelectorAll('.batch-row').length > 100 && !document.querySelector('#batch-refresh').disabled",
  );
  assert.deepEqual(errors, []);
  await writeFile(
    out + "/checks.json",
    JSON.stringify({ buildBatches: count, errors }, null, 2),
  );
  console.log("Batch browser checks passed", { buildBatches: count });
} finally {
  await call("Page.close");
  ws.close();
}
