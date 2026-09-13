// Real captured logs, desktop/mobile interaction, and reconnect checks through CDP.
import { mkdir, writeFile } from "node:fs/promises";
import assert from "node:assert/strict";
const base = process.argv[2] || "http://127.0.0.1:8778";
const out = process.argv[3] || "/home/mbrock/filnix/results/experiment-log-ui";
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
  if (r.exceptionDetails) throw new Error(JSON.stringify(r.exceptionDetails));
  return r.result.value;
};
const wait = (ms) => new Promise((r) => setTimeout(r, ms));
const until = async (expression) => {
  for (let i = 0; i < 80; i++) {
    if (await evaluate(expression)) return;
    await wait(100);
  }
  throw new Error("Timed out: " + expression);
};
const screenshot = async (file) => {
  const shot = await call("Page.captureScreenshot", { format: "png" });
  await writeFile(out + "/" + file, Buffer.from(shot.data, "base64"));
};
try {
  await call("Runtime.enable");
  await call("Page.enable");
  await call("Network.enable");
  await call("Emulation.setDeviceMetricsOverride", {
    width: 1440,
    height: 1000,
    deviceScaleFactor: 1,
    mobile: false,
  });
  await call("Page.navigate", { url: base });
  await until(
    "window.buildLogs && document.querySelector('#selected').textContent === '13,772'",
  );
  const aid = "ea14ba14-da7c-4ee1-8f13-429cdee27b62"; // Real completed multi-build batch.
  await evaluate(`showLog(${JSON.stringify(aid)})`);
  await until(
    "document.querySelectorAll('.log-row').length > 0 && !document.querySelector('#log-earlier').disabled",
  );
  assert.equal(
    await evaluate("document.querySelector('#log-view').open"),
    true,
  );
  assert.ok(
    await evaluate("+document.querySelector('.log-row').dataset.offset > 0"),
  );
  assert.equal(
    await evaluate(
      "document.querySelector('#log-lines').textContent.includes('@nix {')",
    ),
    false,
  );
  await wait(300);
  assert.ok(
    await evaluate(
      "Math.abs(document.querySelector('#log-scroll').scrollHeight - document.querySelector('#log-scroll').clientHeight - document.querySelector('#log-scroll').scrollTop) < 3",
    ),
  );
  await screenshot("logs-desktop.png");
  await evaluate(
    "document.querySelector('#log-scroll').dispatchEvent(new WheelEvent('wheel',{deltaY:-200}));document.querySelector('#log-scroll').scrollTop=140",
  );
  await wait(200);
  const paused = await evaluate(
    "[document.querySelector('#log-scroll').scrollTop, document.querySelector('#log-lines').textContent]",
  );
  await wait(1700);
  assert.deepEqual(
    await evaluate(
      "[document.querySelector('#log-scroll').scrollTop, document.querySelector('#log-lines').textContent]",
    ),
    paused,
  );
  assert.equal(
    await evaluate(
      "document.querySelector('#log-follow').getAttribute('aria-pressed')",
    ),
    "false",
  );
  const anchor = await evaluate(`(() => {
    const top = document.querySelector('#log-scroll').getBoundingClientRect().top;
    const n = [...document.querySelectorAll('.log-row')].find(n=>n.getBoundingClientRect().bottom > top);
    return [n.dataset.offset,n.getBoundingClientRect().top];
  })()`);
  const first = await evaluate(
    "+document.querySelector('.log-row').dataset.offset",
  );
  await evaluate("document.querySelector('#log-earlier').click()");
  await until(`+document.querySelector('.log-row').dataset.offset < ${first}`);
  const anchorAfter = await evaluate(
    `[...document.querySelectorAll('.log-row')].find(n=>n.dataset.offset===${JSON.stringify(anchor[0])})?.getBoundingClientRect().top`,
  );
  assert.ok(
    Math.abs(anchorAfter - anchor[1]) < 3,
    "History insertion preserves the visible row",
  );
  await evaluate(
    "document.querySelector('#log-search').value='error';document.querySelector('#log-search').dispatchEvent(new Event('input'))",
  );
  assert.ok(
    await evaluate("document.querySelectorAll('#log-lines mark').length > 0"),
  );
  await evaluate("document.querySelector('#log-next-match').click()");
  assert.ok(
    await evaluate(
      "document.querySelector('#log-lines mark.current') !== null",
    ),
  );
  await screenshot("logs-search.png");
  // Scope by a real output owner, with the full derivation passed through the map API.
  const drv =
    "/nix/store/vbrvash4lq7vgalq2mrix6i6cs4vw6pn-libopus-x86_64-unknown-linux-gnufilc0-1.5.2.drv";
  await evaluate(`showLog(${JSON.stringify(aid)}, ${JSON.stringify(drv)})`);
  await until(
    "document.querySelectorAll('.log-row').length > 0 && document.querySelector('#log-status').textContent.includes('ended')",
  );
  assert.ok(
    await evaluate(
      "[...document.querySelectorAll('.log-owner')].every(n=>n.title.includes('libopus-'))",
    ),
  );
  assert.match(
    await evaluate("document.querySelector('#log-title').textContent"),
    /libopus/,
  );
  // Back-to-back requests for the same attempt must not mix their filtered output.
  await evaluate(
    `showLog(${JSON.stringify(aid)});showLog(${JSON.stringify(aid)}, ${JSON.stringify(drv)})`,
  );
  await until("document.querySelectorAll('.log-row').length > 0");
  assert.ok(
    await evaluate(
      "[...document.querySelectorAll('.log-owner')].every(n=>n.title.includes('libopus-'))",
    ),
  );
  await evaluate(
    "document.querySelector('#log-wrap').checked=true;document.querySelector('#log-wrap').dispatchEvent(new Event('change'))",
  );
  await screenshot("logs-build.png");
  await call("Emulation.setDeviceMetricsOverride", {
    width: 390,
    height: 844,
    deviceScaleFactor: 1,
    mobile: true,
  });
  await wait(250);
  assert.ok(
    await evaluate(
      "document.querySelector('#log-view').scrollWidth <= innerWidth",
    ),
  );
  await screenshot("logs-mobile.png");
  await call("Network.emulateNetworkConditions", {
    offline: true,
    latency: 0,
    downloadThroughput: 0,
    uploadThroughput: 0,
  });
  await until(
    "document.querySelector('#log-status').textContent.includes('Connection lost')",
  );
  const before = await evaluate(
    "document.querySelector('#log-lines').textContent",
  );
  await call("Network.emulateNetworkConditions", {
    offline: false,
    latency: 0,
    downloadThroughput: -1,
    uploadThroughput: -1,
  });
  await until(
    "!document.querySelector('#log-status').textContent.includes('Connection lost')",
  );
  assert.equal(
    await evaluate("document.querySelector('#log-lines').textContent"),
    before,
  );
  const raw = await fetch(base + "/api/log/download?attempt=" + aid);
  assert.equal(raw.status, 200);
  assert.match(raw.headers.get("content-disposition"), /attachment/);
  assert.ok((await raw.text()).includes('@nix {"action"'));
  // Drive batch transitions using real historical attempts; only this tab's
  // snapshot callback is controlled. The running experiment is never mutated.
  await evaluate(`window.restoreLogUpdate = window.buildLogs.update;
    window.buildLogs.update = () => {};
    window.buildLogs.open(${JSON.stringify(aid)}, "", true)`);
  await until(
    "document.querySelectorAll('.log-row').length > 0 && document.querySelector('#log-status').textContent.includes('ended')",
  );
  await evaluate("document.querySelector('#log-follow').click()");
  const next = "6e1ee130-399a-4f83-a98d-42ce24e8e28a";
  await evaluate(`(async () => { window.testSnapshot = await (await fetch('/api/snapshot')).json();
    window.testSnapshot.attempts = [{id:${JSON.stringify(next)},kind:'build',state:'finished'}];
    window.restoreLogUpdate(window.testSnapshot); })()`);
  assert.equal(
    await evaluate("document.querySelector('#log-attempt').value"),
    aid,
  );
  await evaluate("document.querySelector('#log-follow').click()");
  await until(
    "document.querySelectorAll('.log-row').length > 0 && document.querySelector('#log-status').textContent.includes('ended')",
  );
  await evaluate("window.restoreLogUpdate(window.testSnapshot)");
  await until(
    `document.querySelector('#log-attempt').value === ${JSON.stringify(next)}`,
  );
  await evaluate(
    "window.buildLogs.update = window.restoreLogUpdate;document.querySelector('#log-close').click();document.querySelector('#watch-builds').click()",
  );
  await until(
    "document.querySelector('#log-view').open && document.querySelector('#log-watch').getAttribute('aria-pressed')==='true'",
  );
  await until("document.querySelectorAll('.log-row').length > 0");
  await call("Emulation.setDeviceMetricsOverride", {
    width: 1440,
    height: 1000,
    deviceScaleFactor: 1,
    mobile: false,
  });
  await wait(300);
  await screenshot("logs-live.png");
  assert.deepEqual(errors, []);
  console.log(
    "Log browser checks passed: tail, readable output, scoped builds, request switching, scroll pause, history, search, mobile, reconnect, download, watch mode.",
  );
} catch (error) {
  console.error(JSON.stringify(errors));
  console.error(await evaluate("document.body.innerText.slice(-1500)"));
  throw error;
} finally {
  ws.close();
  await fetch("http://127.0.0.1:9228/json/close/" + tab.id);
}
