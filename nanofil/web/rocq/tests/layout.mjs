// Browser regression check against the generated site, served over HTTP.
// node nanofil/web/rocq/tests/layout.mjs http://localhost:8765
// Requires agent-browser; uses the real model, not simplified UI fixtures.
import { execFileSync } from "node:child_process";

const base = process.argv[2];
if (!base) throw new Error("Pass the generated site's HTTP base URL");
const session = `rocq-test-${process.pid}`;
function browser(...args) {
  return execFileSync("agent-browser", ["--session", session, ...args], { encoding: "utf8" });
}
function check(body) {
  browser("eval", `(async () => {
    const assert = (ok, message) => { if (!ok) throw new Error(message); };
    await document.fonts.ready;
    await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
    ${body}
    return "ok";
  })()`);
}
const source = (name) => `${base}/nanofil/rocq/rocq-theories-${name}.html`;
const fitsPage = `assert(document.documentElement.scrollWidth <= innerWidth + 1, "page overflows");`;

try {
  browser("open", source("Ops"));
  browser("eval", 'localStorage.removeItem("dterm-rocq-layout")');
  for (const width of [320, 390, 768, 1280]) {
    browser("set", "viewport", String(width), "900", "2");
    for (const file of ["Syntax", "Memory", "Ops", "Run", "Semantics", "Validate"]) {
      browser("open", source(file));
      check(`${fitsPage}
        assert(document.querySelector("#rq-layout").value === "auto", "default is not adaptive");
        for (const aside of document.querySelectorAll(".ctor-aside, .field-aside"))
          if (aside.textContent.trim()) assert(aside.getClientRects().length, "comment hidden");
      `);
      console.log(`ok adaptive ${file} at ${width}px`);
    }
    browser("open", `${base}/nanofil/formal.html`);
    check(`${fitsPage}
      const table = [...document.querySelectorAll(".rq-comparison")].find(t => t.querySelector("th")?.textContent === "Rocq definition");
      const cell = table.querySelector("td");
      if (innerWidth <= 700) {
        assert(table.scrollWidth <= table.clientWidth + 1, "Rocq comparison overflows");
        assert(getComputedStyle(cell, "::before").display !== "none", "card label hidden");
        assert(getComputedStyle(cell, "::before").content.includes("Rocq definition"), "card label missing");
      }
    `);
    console.log(`ok formal comparison at ${width}px`);

    browser("open", source("Runtime"));
    const proof = "#object_region_remove + .rq-captured";
    browser("click", `${proof} > summary`);
    check(`${fitsPage}
      const proof = document.querySelector(${JSON.stringify(proof)});
      assert(proof.querySelector('[data-move="-1"]').disabled, "initial previous enabled");
      assert(proof.querySelectorAll('.rq-snapshot:not([hidden])').length === 1, "multiple selected states");
    `);
    browser("click", `${proof} [data-move="1"]`);
    check(`${fitsPage}
      const state = document.querySelector(${JSON.stringify(proof)}).querySelector('.rq-snapshot:not([hidden])');
      assert(state.querySelector('.rq-conclusion').dataset.raw === 'object_region b (remove_region base rs) = object_region b rs', "wrong intros goal");
      assert(state.querySelectorAll('.rq-hyp[data-change="added"]').length === 3, "missing introduced context");
      assert(state.querySelector('.rq-conclusion .f'), "goal not typeset by dterm");
    `);
    browser("click", `${proof} .rq-compare`);
    check(`assert(document.querySelector(${JSON.stringify(proof)}).querySelectorAll('.rq-snapshot:not([hidden])').length === 2, "before/after unavailable");`);
    browser("click", `${proof} .rq-compare`);
    browser("scrollintoview", `${proof} .rq-step-link:nth-child(5)`);
    browser("click", `${proof} .rq-step-link:nth-child(5)`);
    check(`${fitsPage}
      const state = document.querySelector(${JSON.stringify(proof)}).querySelector('.rq-snapshot:not([hidden])');
      assert(state.querySelector('h3').textContent.includes('apply Z.eqb_eq in E.'), "wrong selected tactic");
      assert(state.querySelector('[data-role="deferred"]'), "pending branch lost");
      assert(state.querySelector('.rq-hyp[data-change="changed"]'), "rewrite in hypothesis not highlighted");
    `);
    browser("press", "End");
    check(`${fitsPage}
      const proof = document.querySelector(${JSON.stringify(proof)});
      assert(proof.querySelector('[data-move="1"]').disabled, "next enabled after Qed");
      assert(proof.querySelector('.rq-snapshot:not([hidden])').textContent.includes('checked and closed'), "closure not distinguished");
    `);
    browser("press", "Home");
    browser("press", "ArrowDown");
    check(`assert(document.activeElement.getAttribute('aria-current') === 'step', "keyboard selection loses focus");`);
    console.log(`ok proof navigation, context changes, pending goals and comparison at ${width}px`);
  }
  for (const width of [320, 1280]) {
    browser("set", "viewport", String(width), "900", "2");
    browser("open", source("Ops"));
    for (const layout of ["stack", "table", "auto"]) {
      browser("select", "#rq-layout", layout);
      check(`${fitsPage}
        const row = document.querySelector("#extension .case");
        const pattern = row.querySelector(".cond .goal").getBoundingClientRect();
        const result = row.querySelector(".then .goal").getBoundingClientRect();
        if (${JSON.stringify(layout)} === "stack") assert(result.top >= pattern.bottom - 1, "result not below pattern");
        if (${JSON.stringify(layout)} === "table") assert(Math.abs(result.top - pattern.top) < 2, "columns not aligned");
      `);
      browser("open", `${base}/nanofil/formal.html`);
      check(`${fitsPage}
        assert(document.querySelector("#rq-layout").value === ${JSON.stringify(layout)}, "choice not remembered");
      `);
      browser("open", source("Ops"));
      console.log(`ok ${layout} selection and persistence at ${width}px`);
    }
  }
} finally {
  browser("close");
}
