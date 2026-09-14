const $ = (id) => document.getElementById(id);
const el = (tag, text, cls) => {
  const n = document.createElement(tag);
  if (text != null) n.textContent = text;
  if (cls) n.className = cls;
  return n;
};
const fmt = (x) => Number(x || 0).toLocaleString();
let data = JSON.parse($("initial").textContent),
  generation = 0,
  detailGeneration = 0;
function replace(id, nodes) {
  $(id).replaceChildren(...nodes);
}
const viewIds = {
  activity: "history",
  packages: "inventory",
  timings: "batch-timings",
  dependencies: "dependency-map",
};
window.showView = (view, updateURL = true) => {
  if (window.dashboardNavigation && updateURL)
    return window.dashboardNavigation.view(view);
  if (!viewIds[view]) view = "activity";
  document.body.dataset.view = view;
  document.querySelector(".overview").hidden = ["packages", "timings"].includes(
    view,
  );
  for (const panel of document.querySelectorAll("[data-view]"))
    panel.hidden = panel.dataset.view !== view;
  for (const link of document.querySelectorAll("[data-tab]")) {
    if (link.dataset.tab === view) link.setAttribute("aria-current", "page");
    else link.removeAttribute("aria-current");
  }
  window.dispatchEvent(new Event("resize"));
  window.dispatchEvent(new Event("viewchange"));
};
window.changeCampaign = (id) => {
  if (!id || data.campaign?.id === id) return;
  data.campaign.id = id;
  $("campaign-select").value = id;
  $("campaign-name").textContent =
    data.campaigns.find((c) => c.id === id)?.name || "Campaign";
  $("mode").textContent = "Loading";
  $("notice").hidden = true;
  window.packageBrowser?.changeCampaign(id);
  window.batchBrowser?.changeCampaign(id);
  window.dependencyMap?.updateCampaign(id);
  window.attemptHistory?.updateCampaign(id);
  refresh();
};
for (const link of document.querySelectorAll("[data-tab]"))
  link.onclick = (event) => {
    if (
      event.button ||
      event.metaKey ||
      event.ctrlKey ||
      event.shiftKey ||
      event.altKey
    )
      return;
    event.preventDefault();
    window.showView(link.dataset.tab);
  };
window.showView(
  Object.keys(viewIds).find((k) => "#" + viewIds[k] === location.hash) ||
    "activity",
  false,
);
new ResizeObserver(([entry]) =>
  document.documentElement.style.setProperty(
    "--chrome-height",
    entry.target.getBoundingClientRect().height + "px",
  ),
).observe(document.querySelector(".app-chrome"));
document.addEventListener("pointerdown", (event) => {
  for (const menu of document.querySelectorAll(".menu[open]"))
    if (!menu.contains(event.target)) menu.open = false;
});
window.lastPhase = (phase) =>
  phase
    ? "Last: " +
      phase
        .replace(/Phase$/, "")
        .replace(/([a-z])([A-Z])/g, "$1 $2")
        .toLowerCase()
    : "No phase recorded";
window.phaseName = (phase) =>
  ({
    buildPhase: "Building",
    checkPhase: "Testing",
    pytestCheckPhase: "Testing",
    installCheckPhase: "Install tests",
    configurePhase: "Configuring",
    autoreconfPhase: "Configuring",
    unpackPhase: "Unpacking",
    patchPhase: "Patching",
    installPhase: "Installing",
    fixupPhase: "Finishing",
  })[phase] ||
  (phase
    ? phase.replace(/Phase$/, "").replace(/([a-z])([A-Z])/g, "$1 $2")
    : "Starting");
function render(d) {
  data = d;
  if (!d.campaign) {
    $("notice").textContent = "No campaigns imported.";
    $("notice").hidden = false;
    return;
  }
  const c = d.campaign,
    counts = d.counts;
  window.dependencyMap?.updateCampaign(c.id);
  window.buildLogs?.update(d);
  window.attemptHistory?.updateCampaign(c.id);
  window.packageBrowser?.update(d);
  window.batchBrowser?.update(d);
  if ($("campaign-select").options.length !== d.campaigns.length) {
    $("campaign-select").replaceChildren(
      ...d.campaigns.map((c) => {
        const o = el("option", c.name);
        o.value = c.id;
        return o;
      }),
    );
  }
  $("campaign-select").value = c.id;
  $("campaign-name").textContent = c.name;
  $("revision").textContent = "SOURCE " + c.revision.slice(0, 12);
  $("mode").textContent = c.mode.toUpperCase();
  $("mode").className = c.mode;
  const fresh = c.heartbeat && Date.now() / 1000 - c.heartbeat < 30;
  $("connection").textContent = fresh ? "● Connected" : "○ Offline";
  $("notice").textContent =
    c.hold ||
    (!fresh ? "Controller offline · showing the last observation." : "") ||
    (c.mode === "paused"
      ? "Campaign paused · no new batches will be admitted."
      : "");
  $("notice").hidden = !$("notice").textContent;
  const total = Object.values(counts).reduce((a, b) => a + b, 0);
  $("selected").textContent = fmt(total);
  $("planned").textContent = fmt(
    total - (counts.unplanned || 0) - (counts["evaluation-error"] || 0),
  );
  $("unique").textContent = fmt(d.unique_derivations);
  $("available").textContent = fmt(counts.available);
  $("tested").textContent = fmt(d.tested);
  $("evaluated").textContent = fmt(total - (counts.unplanned || 0));
  $("failed").textContent = fmt(counts.failed);
  $("blocked").textContent = fmt(counts.blocked);
  $("eval-errors").textContent = fmt(counts["evaluation-error"]);
  $("excluded-count").textContent = counts.excluded
    ? ` · ${fmt(counts.excluded)} excluded`
    : "";
  $("remaining").textContent = fmt(counts.unplanned);
  replace(
    "inventory-progress",
    Object.entries(counts)
      .filter(([, n]) => n)
      .map(([state, n]) => {
        const segment = el("span", null, state);
        segment.style.width = (100 * n) / Math.max(1, total) + "%";
        segment.title = `${state}: ${fmt(n)} inputs`;
        return segment;
      }),
  );
  $("inventory-progress-label").textContent =
    `${((100 * (total - (counts.unplanned || 0))) / Math.max(1, total)).toFixed(1)}% of the inventory`;
  const r = d.resources,
    resources = [];
  const line = el("div", null, "resource-line");
  line.append(
    el("span", "Workload memory"),
    el(
      "span",
      r.memory
        ? `${(r.memory / 2 ** 30).toFixed(1)} / ${(r.maximum / 2 ** 30).toFixed(0)} GiB`
        : "Not configured",
    ),
  );
  resources.push(line);
  const meter = el("div", null, "meter"),
    fill = el("div", null, "meter-fill");
  fill.style.width =
    Math.min(100, (100 * (r.memory || 0)) / (r.maximum || 1)) + "%";
  meter.append(fill);
  resources.push(meter);
  resources.push(
    el(
      "p",
      r.verified
        ? `Limits verified · CPUs ${r.cpus}`
        : "Build admission held until daemon containment is verified.",
    ),
  );
  replace("resources", resources);
  const activeAttempt = d.attempts.find(
    (a) => a.kind === "build" && a.state !== "finished",
  );
  const planning = d.attempts.some(
    (a) => a.kind === "plan" && a.state !== "finished",
  );
  $("now-summary").textContent =
    `${d.active.length ? `${fmt(d.active.length)} building` : activeAttempt ? "Preparing build" : c.mode === "paused" ? "Paused" : "Preparing"}${planning ? " · planning" : ""} · ${fmt(counts.queued)} queued`;
  const oldActive = new Map(
    [...$("active").children].map((n) => [n.dataset.drv, n]),
  );
  const activeNodes = d.active.slice(0, 4).map((a) => {
    const n = oldActive.get(a.drv) || el("button", null, "active-build");
    n.dataset.drv = a.drv;
    if (!n.children.length) n.append(el("span"), el("small"));
    n.children[0].textContent = a.drv
      .split("/")
      .pop()
      .slice(33, -4)
      .replace("-x86_64-unknown-linux-gnufilc0", "");
    n.children[1].textContent = window.phaseName(a.phase);
    n.onclick = () => showLog(a.attempt, a.drv);
    return n;
  });
  if (!activeNodes.length)
    activeNodes.push(
      el(
        "p",
        planning && !activeAttempt
          ? "Evaluating the next packages…"
          : c.mode === "paused"
            ? "No new batches will start."
            : "Resolving dependencies…",
        "idle-work",
      ),
    );
  if (d.active.length > 4) {
    const more = el("button", `+${d.active.length - 4} more`, "active-more");
    more.onclick = () => $("watch-builds").click();
    activeNodes.push(more);
  }
  for (const n of [...$("active").children])
    if (!activeNodes.includes(n)) n.remove();
  activeNodes.forEach((n, i) => {
    if ($("active").children[i] !== n)
      $("active").insertBefore(n, $("active").children[i] || null);
  });
  replace(
    "blockers",
    d.blockers.length
      ? d.blockers.map((b) => {
          const n = el(
            "button",
            `${b.name.replace("-x86_64-unknown-linux-gnufilc0", "")} · ${b.affected} dependents`,
            "attempt",
          );
          n.onclick = () => showDerivation(b.drv);
          return n;
        })
      : [el("p", "No shared blockers.")],
  );
  $("footer-version").textContent = `filnix ${d.version} · ${c.nix_version}`;
}
async function refresh() {
  const g = ++generation;
  try {
    const q = new URLSearchParams({
      campaign: data.campaign?.id || "",
    });
    const response = await fetch("/api/snapshot?" + q);
    if (!response.ok) throw new Error("snapshot unavailable");
    const d = await response.json();
    if (g === generation) render(d);
  } catch (e) {
    if (g === generation) {
      $("connection").textContent = "○ Connection lost · retrying";
      $("notice").textContent = "Connection lost · retrying";
      $("notice").hidden = false;
    }
  }
}
async function showPackage(id, fromRoute = false) {
  if (window.dashboardNavigation && !fromRoute)
    return window.dashboardNavigation.package(id);
  const g = ++detailGeneration;
  replace("detail-content", [el("p", "Loading package…")]);
  if (!$("detail").open) $("detail").showModal();
  let p;
  try {
    const response = await fetch("/api/package?id=" + id);
    if (!response.ok) throw new Error("Package unavailable");
    p = await response.json();
  } catch {
    if (g === detailGeneration)
      replace("detail-content", [
        el("p", "Package unavailable. Close and reopen to retry."),
      ]);
    return;
  }
  if (g !== detailGeneration) return;
  const nodes = [
    el("h2", p.label),
    el("span", p.state === "available" ? "Built" : p.state, "badge " + p.state),
    el(
      "p",
      p.selection?.metadata?.description || "No description recorded.",
      "package-description",
    ),
    el("p", p.selection?.metadata?.version || ""),
  ];
  if (p.source_url) {
    const source = el(
      "a",
      (p.selection?.sourceFile || "Nixpkgs source") + " ↗",
      "package-source",
    );
    source.href = p.source_url;
    source.target = "_blank";
    source.rel = "noopener";
    nodes.push(source);
  }
  if (p.error) nodes.push(el("h3", "Observation"), el("pre", p.error));
  if (p.recipe) {
    const locate = el("button", "Explore on dependency map ↗", "graph-log");
    locate.onclick = () => window.dependencyMap?.locate(p.drv);
    nodes.push(locate);
    nodes.push(
      el("h3", "Recipe and provenance"),
      el("p", `${p.recipe.name} · ${p.recipe.hostPlatform}`),
      el(
        "p",
        p.recipe.compiler === p.recipe.expectedCompiler
          ? "Configured with the Fil-C compiler. Artifact instrumentation has not been independently verified."
          : "Compiler differs from the Fil-C default; provenance needs review.",
      ),
      el(
        "p",
        `Checks configured: ${p.recipe.doCheck}. Install checks configured: ${p.recipe.doInstallCheck}.`,
      ),
      el("pre", p.drv),
    );
  }
  if (p.realization?.evidence_attempt) {
    const log = el("button", "Open recorded build log ↗", "graph-log");
    log.onclick = () => showLog(p.realization.evidence_attempt, p.drv);
    nodes.push(log);
  }
  if (p.realization)
    nodes.push(
      el(
        "p",
        `Output availability: ${p.realization.available ? "observed available" : "not observed"}. Origin: ${p.realization.origin}.`,
      ),
    );
  nodes.push(
    el("h3", "Test evidence"),
    el(
      "p",
      p.tests.length
        ? p.tests
            .map((t) => t.phase + " passed · " + t.attempt.slice(0, 8))
            .join("\n")
        : "No executed test phase has been observed. Recipe flags and cached outputs do not establish a test pass.",
    ),
  );
  if (p.blockers.length)
    nodes.push(
      el("h3", "Blockers"),
      el(
        "pre",
        p.blockers
          .map((b) => b.failure + ": " + b.chain.join("\n  → "))
          .join("\n\n"),
      ),
    );
  nodes.push(
    el("h3", "Direct build dependencies"),
    el(
      "p",
      "Role annotations describe evaluated package inputs. Unannotated edges remain unknown. Showing up to 100.",
    ),
  );
  for (const dep of p.dependencies) {
    const b = el(
      "button",
      `${dep.name} · ${dep.roles || "unknown role"} ↗`,
      "attempt",
    );
    b.onclick = () => showDerivation(dep.drv);
    nodes.push(b);
  }
  if (p.dependents.length) {
    nodes.push(el("h3", "Planned dependents (up to 100)"));
    for (const d of p.dependents) {
      const b = el("button", d.label + " · " + d.state, "attempt");
      b.onclick = () => showPackage(d.id);
      nodes.push(b);
    }
  }
  nodes.push(
    el("h3", "Downstream checks on known host dependency paths"),
    el(
      "p",
      p.downstream_tests.length
        ? p.downstream_tests.map((t) => t.label + " · " + t.phase).join("\n")
        : "No downstream test evidence yet. This view follows only recorded host dependency edges.",
    ),
  );
  replace("detail-content", nodes);
  if (!$("detail").open) $("detail").showModal();
}
async function showDerivation(drv, offset = 0, fromRoute = false) {
  if (window.dashboardNavigation && !fromRoute)
    return window.dashboardNavigation.derivation(drv, offset);
  const g = ++detailGeneration;
  const q = new URLSearchParams({ drv, campaign: data.campaign.id, offset });
  replace("detail-content", [el("p", "Loading derivation…")]);
  if (!$("detail").open) $("detail").showModal();
  let d;
  try {
    const response = await fetch("/api/derivation?" + q);
    if (!response.ok) throw new Error("Derivation unavailable");
    d = await response.json();
  } catch {
    if (g === detailGeneration)
      replace("detail-content", [
        el("p", "Derivation unavailable. Close and reopen to retry."),
      ]);
    return;
  }
  if (g !== detailGeneration) return;
  const nodes = [
    el("h2", d.derivation.name),
    el("pre", drv),
    el(
      "p",
      `Availability: ${d.derivation.available ? "observed available" : "not observed"} · Origin: ${d.derivation.origin}`,
    ),
  ];
  const locate = el("button", "Explore on dependency map ↗", "graph-log");
  locate.onclick = () => window.dependencyMap?.locate(drv);
  nodes.push(locate);
  if (d.derivation.evidence_attempt) {
    const log = el("button", "Open recorded build log ↗", "graph-log");
    log.onclick = () => showLog(d.derivation.evidence_attempt, drv);
    nodes.push(log);
  }
  if (d.derivation.failure)
    nodes.push(el("p", "Failure: " + d.derivation.failure));
  for (const t of d.tests) {
    const b = el("button", t.phase + " passed · open attempt log", "attempt");
    b.onclick = () => showLog(t.attempt, drv);
    nodes.push(b);
  }
  nodes.push(el("h3", "Build dependencies (up to 100)"));
  for (const dep of d.dependencies) {
    const b = el(
      "button",
      dep.name + " · " + (dep.roles || "unknown role") + " ↗",
      "attempt",
    );
    b.onclick = () => showDerivation(dep.drv);
    nodes.push(b);
  }
  nodes.push(el("h3", "Selected packages depending on this derivation"));
  for (const p of d.dependents) {
    const b = el("button", p.label + " · " + p.state, "attempt");
    b.onclick = () => showPackage(p.id);
    nodes.push(b);
  }
  if (offset) {
    const b = el("button", "Previous dependents", "attempt");
    b.onclick = () => showDerivation(drv, Math.max(0, offset - 50));
    nodes.push(b);
  }
  if (d.dependents.length === 50) {
    const b = el("button", "More dependents", "attempt");
    b.onclick = () => showDerivation(drv, offset + 50);
    nodes.push(b);
  }
  replace("detail-content", nodes);
  if (!$("detail").open) $("detail").showModal();
}
function showLog(id, drv = "") {
  window.buildLogs?.open(id, drv);
}
window.closeDetails = () => {
  detailGeneration++;
  $("detail").close();
};
$("close-detail").onclick = () => window.dashboardNavigation.close("detail");
$("detail").addEventListener("close", () => {
  if (!$("detail").open) detailGeneration++;
});
$("campaign-select").onchange = () => {
  $("campaign-options").open = false;
  window.dashboardNavigation.campaign($("campaign-select").value);
};
render(data);
setInterval(refresh, 5000);
