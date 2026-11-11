// Exercise the public layout checker with a real navigation exceeding
// agent-browser 0.38.1's 25s load wait, including a late overflow.
import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { createServer } from "node:http";
import { once } from "node:events";
import { fileURLToPath } from "node:url";

async function checkNavigation(overflow) {
  let delayed = false;
  const server = createServer((request, response) => {
    response.writeHead(200, { "Content-Type": "text/html" });
    response.write('<!doctype html><meta name="viewport" content="width=device-width"><body>');
    if (request.url.endsWith("index.html")) {
      response.end('<a href="rocq-theories-soundness-Machine.html">Machine</a>');
      return;
    }
    const finish = () => response.end(overflow ? '<div style="width:669px">late overflow</div>' : "fits");
    if (!delayed && request.url.endsWith("Machine.html")) {
      delayed = true;
      // Commit the narrow document immediately, but hold its end (and
      // the offending element) beyond the browser's load deadline.
      setTimeout(finish, 28000);
    } else {
      finish();
    }
  });
  server.listen(0, "127.0.0.1");
  await once(server, "listening");
  try {
    const base = `http://127.0.0.1:${server.address().port}`;
    console.log(`${new Date().toISOString()} delayed navigation, overflow=${overflow}`);
    const child = spawn(process.execPath, [fileURLToPath(new URL("./layout.mjs", import.meta.url)),
      base, "--pages-only", "320"], { stdio: ["ignore", "pipe", "pipe"] });
    let output = "";
    for (const stream of [child.stdout, child.stderr]) {
      stream.on("data", chunk => { output += chunk; process.stdout.write(chunk); });
    }
    const [code] = await once(child, "close");
    assert.equal(code, overflow ? 1 : 0, output);
    if (overflow) assert.match(output, /page overflows:/, "must fail on overflow, not navigation");
    console.log(`${new Date().toISOString()} ok delayed ${overflow ? "overflow rejected" : "page checked"}`);
  } finally {
    server.closeAllConnections();
    await new Promise(resolve => server.close(resolve));
  }
}

// Independent HTTP servers and browser sessions; don't pay the 28s delay twice.
await Promise.all([false, true].map(checkNavigation));
