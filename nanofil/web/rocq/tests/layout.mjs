// Browser regression check against the generated site, served over HTTP.
// node nanofil/web/rocq/tests/layout.mjs http://localhost:8765 [--pages-only | --declarations-only] [320 390 768 1280]
// Requires agent-browser; uses the real model, not simplified UI fixtures.
import { execFileSync } from "node:child_process";

const base = process.argv[2];
if (!base) throw new Error("Pass the generated site's HTTP base URL");
const pagesOnly = process.argv.includes("--pages-only");
const declarationsOnly = process.argv.includes("--declarations-only");
const args = process.argv.slice(3).filter(a => !["--pages-only", "--declarations-only"].includes(a));
const widths = args.length ? args.map(Number) : [320, 390, 768, 1280];
if (widths.some(w => ![320, 390, 768, 1280].includes(w))) throw new Error("Unknown test width");
const detailWidths = pagesOnly || declarationsOnly ? [] : widths;
const sweepWidths = declarationsOnly ? [] : widths;
let session = `rocq-test-${process.pid}`;
function browser(...args) {
  try {
    return execFileSync("agent-browser", ["--session", session, ...args], { encoding: "utf8" });
  } catch (error) {
    // agent-browser 0.38.1's navigation load wait is fixed at 25s,
    // independently of AGENT_BROWSER_DEFAULT_TIMEOUT. Keep waiting for
    // this navigation, not a second GET or an assertion on the old page.
    if (args[0] !== "open" || !String(error.stderr).includes("Operation timed out.")) throw error;
    console.log(`${new Date().toISOString()} waiting for navigation to finish: ${args[1]}`);
    return execFileSync("agent-browser", ["--session", session, "wait", "--fn",
      `location.href === ${JSON.stringify(args[1])} && document.readyState === "complete"`,
      "--timeout", "60000"], { encoding: "utf8" });
  }
}
function check(body) {
  browser("eval", `(async () => {
    const assert = (ok, message) => { if (!ok) throw new Error(message); };
    await document.fonts.ready;
    for (let i = 0; i < 4; i++) await new Promise(requestAnimationFrame);
    ${body}
    return "ok";
  })()`);
}
const source = (name) => `${base}/nanofil/rocq/rocq-theories-${name}.html`;
const fitsPage = `assert(document.documentElement.scrollWidth <= innerWidth + 1,
    'page overflows: ' + document.documentElement.scrollWidth + 'px at ' + innerWidth + 'px');
  for (const dialog of document.querySelectorAll('dialog[open]'))
    assert(dialog.scrollWidth <= dialog.clientWidth + 1, "proof dialog overflows");`;
const contextRows = `
  for (const row of document.querySelectorAll('.rq-snapshot:not([hidden]) .rq-hyp')) {
    const name = row.querySelector('.rq-hyp-names').getBoundingClientRect();
    const type = row.querySelector('.rq-hyp-type').getBoundingClientRect();
    assert(type.left >= name.right - 1, "hypothesis type not beside its name");
    assert(Math.abs(type.top - name.top) < 4, "hypothesis row not aligned");
  }
`;

try {
  browser("open", `${base}/nanofil/rocq/index.html`);
  browser("eval", 'localStorage.removeItem("dterm-rocq-layout")');
  for (const width of widths) {
    browser("set", "viewport", String(width), "900", "2");
    for (const page of ["nanofil/poison.html", "nanofil/rocq/rocq-spikes-Poison.html"]) {
      browser("open", `${base}/${page}`);
      for (const layout of ["auto", "stack"]) {
        browser("select", "#rq-layout", layout);
        check(`
          for (const id of ['taint', 'word_taint', 'poison_policy']) {
            const declaration = document.querySelector('#' + id);
            assert(declaration.getBoundingClientRect().right <= innerWidth + 1,
              'declaration extends past the viewport: ' + id);
            assert(declaration.scrollWidth <= declaration.clientWidth + 1,
              'declaration content overflows: ' + id);
          }
          const beside = (row, nameSelector, typeSelector) => {
            assert(row, 'missing declaration');
            const name = row.querySelector(nameSelector).getBoundingClientRect();
            const type = row.querySelector(typeSelector).getBoundingClientRect();
            assert(type.left >= name.right - 1 && Math.abs(type.top - name.top) < 4,
              'short declaration split after its name: ' + row.textContent);
          };
          for (const name of ['t_branch', 't_index', 't_vartime', 'pol_check_branches'])
            beside(document.querySelector('#' + name), '.field-name', '.field-type > .goal');
          beside(document.querySelector('#WTInt'), '.ctor', '.ctor-args > .goal');
          assert(document.querySelector('#taint .rq-fields').getBoundingClientRect().height < 100,
            'three boolean fields take more than compact rows');
          if (innerWidth >= 1280) {
            const binders = [...document.querySelectorAll('#WTLimit .binder')];
            assert(Math.abs(binders[0].getBoundingClientRect().top - binders[1].getBoundingClientRect().top) < 4,
              'constructor arguments wrap despite fitting on desktop');
          }
        `);
      }
      browser("select", "#rq-layout", "auto");
    }
    for (const file of ["Memory", "Syntax"]) {
      browser("open", `${base}/nanofil/rocq/rocq-theories-core-${file}.html`);
      check(`${fitsPage}
        for (const cell of document.querySelectorAll('.field-aside, .ctor-aside'))
          if (cell.textContent.trim()) assert(cell.getClientRects().length, 'declaration comment hidden');
        const args = document.querySelector('#Phi .ctor-args');
        if (args && innerWidth <= 390) {
          const binders = [...args.querySelectorAll('.binder')];
          assert(binders.at(-1).getBoundingClientRect().top >= binders[0].getBoundingClientRect().bottom - 1,
            'long constructor arguments must wrap');
          assert(args.scrollWidth <= args.clientWidth + 1, 'wrapped constructor arguments overflow');
          for (const binder of binders)
            assert(binder.getClientRects().length === 1, 'short binder split instead of wrapping between binders');
        }
      `);
    }
    console.log(`ok compact declarations, wrapping and comments at ${width}px`);
  }
  browser("open", `${base}/nanofil/rocq/index.html`);
  // Discover from the generated index: new theories join the phone gate
  // automatically, instead of silently falling outside a fixed file list.
  const pages = JSON.parse(browser("eval", `[...new Set([...document.querySelectorAll('a[href]')]
    .map(a => a.getAttribute('href')).filter(h => /^[^/]+[.]html$/.test(h) && h !== 'index.html'))]`));
  if (!pages.some(p => p.includes("Machine"))) throw new Error("missing Machine page in index");
  for (const width of sweepWidths.filter(w => w <= 390)) {
    browser("set", "viewport", String(width), "900", "2");
    for (const page of ["index.html", ...pages]) {
      console.log(`${new Date().toISOString()} checking ${page}${pagesOnly ? "" : " and its proof steps"} at ${width}px`);
      browser("open", `${base}/nanofil/rocq/${page}`);
      check(fitsPage);
      if (page === "rocq-theories-soundness-Evidence.html") check(`
        assert(document.querySelector('#phis_env_agree a[href="rocq-theories-core-Term.html#lookup"]'),
          "Evidence regression needs the full cross-link index");
      `);
      // A fresh narrow load can wrap differently from dterm's resize plan.
      // Exercise both, including returning from a desktop-sized viewport.
      browser("set", "viewport", "1280", "900", "2");
      check("");
      browser("set", "viewport", String(width), "900", "2");
      check(fitsPage);
      // A crashed planner can leave an apparently fitting CSS fallback.
      // Reject that too, rather than passing an unexercised printer.
      const errors = JSON.parse(browser("--json", "errors")).data.errors;
      if (errors.length) throw new Error(`${page}: ${errors.map(e => e.text).join("\n")}`);
      if (pagesOnly) {
        console.log(`ok no overflow ${page} at ${width}px, on load and after desktop reflow`);
        continue;
      }
      const count = JSON.parse(browser("eval", "document.querySelectorAll('.rq-proof').length"));
      // Bound each command to four snapshots: large captured states can
      // spend real time in layout, even in a short proof.
      for (let i = 0; i < count; i++) {
        check(`
          const proof = document.querySelectorAll('.rq-proof')[${i}];
          proof.open = true;
          const script = proof.querySelector('.rq-script');
          if (script) script.open = true;
          for (let i = 0; i < 4; i++) await new Promise(requestAnimationFrame);
          ${fitsPage}
        `);
        const steps = JSON.parse(browser("eval", `document.querySelectorAll('.rq-proof')[${i}].querySelectorAll('.rq-step-link').length`));
        for (let start = 0; start < steps; start += 4) {
          check(`
            const links = [...document.querySelectorAll('.rq-proof')[${i}].querySelectorAll('.rq-step-link')];
            for (const link of links.slice(${start}, ${start + 4})) {
              link.click();
              for (let i = 0; i < 4; i++) await new Promise(requestAnimationFrame);
              assert(document.documentElement.scrollWidth <= innerWidth + 1,
                ${JSON.stringify(page)} + ' overflows at ' + link.getAttribute('aria-label'));
              ${fitsPage}
            }
          `);
        }
        browser("eval", `document.querySelectorAll('.rq-proof')[${i}].open = false`);
        console.log(`${new Date().toISOString()} ok ${page} proof ${i + 1}/${count}, ${steps} steps at ${width}px`);
      }
      console.log(`ok no overflow ${page}, including all proof steps, at ${width}px`);
    }
  }
  for (const width of detailWidths) {
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
    check(fitsPage);
    browser("scrollintoview", `${proof} > summary`);
    browser("click", `${proof} > summary`);
    check(`${fitsPage}
      const proof = document.querySelector(${JSON.stringify(proof)});
      assert(proof.open, "proof did not open");
      assert(proof.querySelector('[data-move="-1"]').disabled, "initial previous enabled");
      assert(proof.querySelectorAll('.rq-snapshot:not([hidden])').length === 1, "multiple selected states");
    `);
    browser("click", `${proof} [data-move="1"]`);
    check(`${fitsPage} ${contextRows}
      const state = document.querySelector(${JSON.stringify(proof)}).querySelector('.rq-snapshot:not([hidden])');
      assert(state.querySelector('.rq-conclusion').dataset.raw === 'object_region b (remove_region base rs) = object_region b rs', "wrong intros goal");
      assert(state.querySelectorAll('.rq-hyp[data-change="added"]').length === 3, "missing introduced context");
      assert(state.querySelector('.rq-conclusion .f'), "goal not typeset by dterm");
    `);
    browser("click", `${proof} .rq-compare`);
    check(`assert(document.querySelector(${JSON.stringify(proof)}).querySelectorAll('.rq-snapshot:not([hidden])').length === 2, "before/after unavailable");`);
    browser("click", `${proof} .rq-compare`);
    browser("scrollintoview", `${proof} .rq-step-link[aria-label="apply Z.eqb_eq in E."]`);
    browser("click", `${proof} .rq-step-link[aria-label="apply Z.eqb_eq in E."]`);
    check(`${fitsPage}
      const state = document.querySelector(${JSON.stringify(proof)}).querySelector('.rq-snapshot:not([hidden])');
      assert(state.querySelector('h3 .tactic').title === 'apply Z.eqb_eq in E.', "wrong selected tactic");
      assert(state.querySelector('h3 .tactic [data-d]'), "selected tactic not typeset");
      assert(document.querySelector(${JSON.stringify(proof)}).querySelector('.rq-step-link .tactic [data-d]'), "timeline tactic not typeset");
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
  for (const width of detailWidths.filter(w => w === 320 || w === 1280)) {
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
      browser("open", source("Runtime"));
      check(fitsPage);
      browser("scrollintoview", "#object_region_remove + .rq-captured > summary");
      browser("click", "#object_region_remove + .rq-captured > summary");
      check(`assert(document.querySelector('#object_region_remove + .rq-captured').open, "proof did not open");`);
      browser("click", '#object_region_remove + .rq-captured [data-move="1"]');
      browser("click", "#object_region_remove + .rq-captured .rq-compare");
      check(`${fitsPage} ${contextRows}
        assert(document.querySelector('#object_region_remove + .rq-captured').querySelectorAll('.rq-snapshot:not([hidden])').length === 2, "comparison missing in selected layout");
      `);
      browser("open", source("Machine"));
      check(`${fitsPage}
        assert(document.querySelectorAll('.rq-ltac').length === 3, "Ltac definitions not parsed");
        assert(document.querySelector('#cases .rq-tac-match [data-d]'), "Ltac pattern not typeset");
        const proof = document.querySelector('#store_res_kept + .rq-captured');
        proof.open = true;
        const step = proof.querySelector('.rq-step-link:has(.rq-tac-match)');
        assert(step && !step.querySelector('a'), "compound tactic missing or nested interactive link");
        step.click();
        for (let i = 0; i < 4; i++) await new Promise(requestAnimationFrame);
        ${fitsPage}
        assert(proof.querySelector('.rq-snapshot:not([hidden]) h3 .rq-tac-match'), "selected match not typeset");
        assert(proof.querySelector('dialog:modal'), "proof did not open modally");
        // A phone reads the proof as one flow; desktop gives the script
        // and the selected state a pane each.
        assert(getComputedStyle(proof.querySelector('.rq-timeline')).overflowY === (innerWidth <= 720 ? 'visible' : 'auto'),
          "timeline scrolling does not match the width");
      `);
      browser("open", source("Ops"));
      console.log(`ok ${layout} selection and persistence at ${width}px`);
    }
    browser("open", source("Machine"));
    browser("scrollintoview", '#kept_trans + .rq-captured > summary');
    const pageY = JSON.parse(browser('eval', 'scrollY'));
    browser("click", '#kept_trans + .rq-captured > summary');
    check(`${fitsPage}
      const proof = document.querySelector('#kept_trans + .rq-captured');
      assert(proof.querySelector('dialog:modal'), "dialog not modal");
      assert(proof.querySelector('.rq-position').textContent === 'Initial goal', "initial state counted as tactic");
      const link = [...proof.querySelectorAll('.rq-step-link')].find(e => e.getAttribute('aria-label').startsWith('intros (b & reg2'));
      link.click();
      for (let i=0; i<4; i++) await new Promise(requestAnimationFrame);
      assert(link.querySelector('.rq-pattern').getClientRects().length === 1, "short intro pattern breaks across lines");
      assert(link.querySelector('[data-v="reg2"] sub')?.textContent === '2', "tactic local not subscripted");
      assert(proof.querySelector('.rq-position').textContent.endsWith('/ 20'), "tactic count disagrees with source");
      const dialog = proof.querySelector('dialog');
      const panes = innerWidth <= 720 ? '.rq-explorer' : '.rq-timeline, .rq-states, .rq-script';
      for (const el of dialog.querySelectorAll('*'))
        if (!el.matches(panes) && el.getClientRects().length && ['auto','scroll'].includes(getComputedStyle(el).overflowY))
          assert(el.scrollHeight <= el.clientHeight + 1, "nested vertical scrolling in proof");
      if (innerWidth === 320) {
        const row = link.getBoundingClientRect(), state = proof.querySelector('.rq-states').getBoundingClientRect();
        assert(state.top >= row.bottom - 1 && state.top <= row.bottom + 10, "phone goal not beside selected tactic in flow");
      }
    `);
    browser('eval', `document.querySelector('#kept_trans + .rq-captured dialog select').focus()`);
    browser('press', 'Shift+Tab');
    check(`assert(document.querySelector('dialog:modal').contains(document.activeElement), "modal focus escaped");`);
    browser('press', 'Escape');
    check(`assert(!document.querySelector('dialog[open]'), "Escape did not close proof");
      assert(document.activeElement === document.querySelector('#kept_trans + .rq-captured > summary'), "close did not restore focus");
      assert(Math.abs(scrollY - ${pageY}) < 2, "modal moved underlying page");`);
    browser('click', '#kept_trans + .rq-captured > summary');
    browser('select', '#kept_trans + .rq-captured dialog select', 'stack');
    check(`assert(document.documentElement.dataset.caseLayout === 'stack', "dialog layout selector disconnected");`);
    browser('click', '#kept_trans + .rq-captured [aria-label="Close proof"]');
    check(`assert(!document.querySelector('dialog[open]'), "close button did not close proof");`);
    console.log(`ok modal, intro patterns, local typography, counts, single scroll and close at ${width}px`);

    // A short viewport makes this real proof scroll on desktop too.
    // At 900px high its compact script and context can fit entirely.
    browser('set', 'viewport', String(width), '600', '2');
    browser('open', source('Runtime'));
    check(`
      const proof = document.getElementById('InterpRuntime.ready_kept').nextElementSibling;
      proof.open = true;
      for (let i=0; i<4; i++) await new Promise(requestAnimationFrame);
      const links = [...proof.querySelectorAll('.rq-step-link')];
      const rewrite = links.find(e => e.getAttribute('aria-label').startsWith('destruct Hr as'));
      rewrite.click();
      for (let i=0; i<4; i++) await new Promise(requestAnimationFrame);
      ${fitsPage}
      assert(rewrite.querySelector('.rq-intro-or .rq-intro-and'), "nested sum/product intro pattern lost");
      assert([...rewrite.querySelectorAll('[title="->"]')].map(e => e.textContent).join('') === '→→', "rewrite pattern printed as loose source tokens");
      const short = links.find(e => e.getAttribute('aria-label') === 'intros a Ha.');
      const bullet = short.querySelector('.bullet').getBoundingClientRect();
      const tactic = short.querySelector('.tactic').getBoundingClientRect();
      assert(Math.abs(bullet.top - tactic.top) < 2, "bullet isolated from its tactic");
      assert(short.getBoundingClientRect().height < 30, "short tactic row too tall");
      const brace = links.find(e => e.getAttribute('aria-label').startsWith('intros (b & reg & E & Hr)'));
      assert(brace.closest('.rq-braced'), "braced proof lost its focus group");
      if (innerWidth > 720)
        assert(brace.getBoundingClientRect().left > short.getBoundingClientRect().left + 3, "focus group not indented");
      // The chain closes the focused branch; its preceding state has
      // the large context that must scroll without obscuring the header.
      links[links.indexOf(rewrite) - 1].click();
      for (let i=0; i<4; i++) await new Promise(requestAnimationFrame);
      const header = proof.querySelector('.rq-dialog-head');
      const narrow = innerWidth <= 720;
      const content = proof.querySelector(narrow ? '.rq-explorer' : '.rq-states');
      const top = header.getBoundingClientRect().top;
      content.scrollTop = 500;
      await new Promise(requestAnimationFrame);
      assert(content.scrollTop > 0, "long proof content not scrollable");
      assert(content.getBoundingClientRect().top >= header.getBoundingClientRect().bottom - 1,
        "scrolling context slides underneath header");
      assert(Math.abs(header.getBoundingClientRect().top - top) < 1, "header scrolled away");
      const scrollers = [...proof.querySelectorAll('dialog *')].filter(e =>
        e.getClientRects().length && ['auto','scroll'].includes(getComputedStyle(e).overflowY) && e.scrollHeight > e.clientHeight + 1);
      if (narrow) assert(scrollers.length === 1 && scrollers[0] === content, "phone proof has multiple vertical scroll areas");
      else assert(scrollers.every(e => e.matches('.rq-timeline, .rq-states')), "desktop proof scrolls outside its two panes");
      // The selected tactic stays in view in its own pane.
      if (!narrow) {
        const pane = proof.querySelector('.rq-timeline').getBoundingClientRect();
        const row = links[links.indexOf(rewrite) - 1].getBoundingClientRect();
        assert(row.top >= pane.top - 1 && row.bottom <= pane.bottom + 1, "selected tactic scrolled out of its pane");
      }
    `);
    console.log(`ok nested patterns, compact bullets, braced focus and non-overlapping header at ${width}px`);
  }
  // Use a fresh browser so cached scripts cannot bypass request blocking.
  browser("close");
  session = `rocq-static-${process.pid}`;
  browser("open", "about:blank");
  browser("network", "route", "*", "--abort", "--resource-type", "script");
  for (const width of sweepWidths.filter(w => w <= 390)) {
    browser("set", "viewport", String(width), "900", "2");
    for (const page of ["index.html", ...pages]) {
      console.log(`${new Date().toISOString()} checking ${page} without scripts at ${width}px`);
      browser("open", `${base}/nanofil/rocq/${page}`);
      check(`
        if (!${pagesOnly})
          for (const proof of document.querySelectorAll('.rq-proof, .rq-script')) proof.open = true;
        ${fitsPage}
        assert(!document.querySelector('.rq-snapshot[hidden]'), "static states hidden");
      `);
      browser("set", "viewport", "1280", "900", "2");
      check("");
      browser("set", "viewport", String(width), "900", "2");
      check(fitsPage);
      console.log(`ok no-script overflow ${page} at ${width}px, on load and after desktop reflow`);
    }
  }
  for (const width of detailWidths.filter(w => w === 320 || w === 1280)) {
    browser("set", "viewport", String(width), "900", "2");
    browser("open", source("Runtime"));
    check(fitsPage);
    browser("scrollintoview", "#object_region_remove + .rq-captured > summary");
    browser("click", "#object_region_remove + .rq-captured > summary");
    check(`${fitsPage} ${contextRows}
      const proof = document.querySelector('#object_region_remove + .rq-captured');
      assert(proof.open, "static proof did not open");
      assert(proof.querySelector('.rq-proof-controls').hidden, "nonfunctional controls shown");
      assert(proof.querySelectorAll('.rq-snapshot:not([hidden])').length === 11, "static proof states lost");
      assert(proof.textContent.includes('No remaining goals.') && proof.textContent.includes('checked and closed'), "closure distinction lost");
    `);
    console.log(`ok all snapshots readable without scripts at ${width}px`);
  }
} finally {
  browser("close");
}
