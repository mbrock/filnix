const $ = (id) => document.getElementById(id);
const el = (tag, text, cls) => {
  const n = document.createElement(tag);
  if (text != null) n.textContent = text;
  if (cls) n.className = cls;
  return n;
};
const fmt = (x) => Number(x || 0).toLocaleString();
let data = JSON.parse($("initial").textContent),
  offset = 0,
  generation = 0,
  logAttempt = null,
  logOffset = 0,
  logText = "",
  detailGeneration = 0;
function replace(id, nodes) {
  $(id).replaceChildren(...nodes);
}
function render(d) {
  data = d;
  if (!d.campaign) {
    $("notice").textContent =
      "No campaigns imported. Importing an inventory creates a paused campaign.";
    return;
  }
  const c = d.campaign,
    counts = d.counts;
  window.dependencyMap?.updateCampaign(c.id);
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
  $("mode").className = "badge " + c.mode;
  const fresh = c.heartbeat && Date.now() / 1000 - c.heartbeat < 30;
  $("connection").textContent = fresh
    ? "● Controller connected"
    : "○ Controller offline / stale";
  $("notice").textContent =
    c.hold ||
    c.manifest.purpose ||
    (c.mode === "paused"
      ? "Campaign paused. The input set is frozen; planning and calibration can be inspected here. No new package batches will be admitted."
      : "Campaign running. Small batches share dependencies through Nix. Test evidence is recorded separately from output availability.");
  const total = Object.values(counts).reduce((a, b) => a + b, 0);
  $("selected").textContent = fmt(total);
  $("planned").textContent = fmt(
    total - (counts.unplanned || 0) - (counts["evaluation-error"] || 0),
  );
  $("unique").textContent =
    fmt(d.unique_derivations) + " unique root derivations";
  $("available").textContent = fmt(counts.available);
  $("tested").textContent = fmt(d.tested);
  $("matches").textContent = fmt(d.filtered) + " packages";
  replace(
    "packages",
    d.candidates.length
      ? d.candidates.map((p) => {
          const row = el("button", null, "pkg"),
            name = el("span", p.label, "pkg-name");
          name.append(
            el("span", [p.decision, ...p.tags].join(" · "), "pkg-tags"),
          );
          row.append(
            name,
            el("span", p.state, "badge " + p.state),
            el("span", "↗", "arrow"),
          );
          row.onclick = () => showPackage(p.id);
          return row;
        })
      : [el("p", "No packages match this filter.", "empty")],
  );
  $("page").textContent = d.filtered
    ? `${fmt(offset + 1)}–${fmt(Math.min(offset + 50, d.filtered))}`
    : "0";
  $("previous").disabled = offset === 0;
  $("next").disabled = offset + 50 >= d.filtered;
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
  replace(
    "active",
    d.active.length
      ? d.active.map((a) =>
          el(
            "p",
            `${a.drv.split("/").pop().slice(33, -4)} · ${a.phase || "starting"}`,
          ),
        )
      : [el("p", "No builds in flight. Planning does not compile packages.")],
  );
  replace(
    "blockers",
    d.blockers.length
      ? d.blockers.map((b) => {
          const n = el(
            "button",
            `${b.name} · ${b.failure} · ${b.affected} planned inputs affected`,
            "attempt",
          );
          n.onclick = () => showDerivation(b.drv);
          return n;
        })
      : [
          el(
            "p",
            "No proven dependency failures yet. Unplanned packages remain unknown.",
          ),
        ],
  );
  replace(
    "attempts",
    d.attempts.length
      ? d.attempts.map((a) => {
          const b = el(
            "button",
            `${a.kind} · ${a.result ? JSON.parse(a.result).reason : a.state}\n${a.id.slice(0, 8)}`,
            "attempt",
          );
          b.onclick = () => showLog(a.id);
          return b;
        })
      : [el("p", "No attempts recorded.")],
  );
  $("footer-version").textContent = `filnix ${d.version} · ${c.nix_version}`;
}
async function refresh() {
  const g = ++generation;
  try {
    const q = new URLSearchParams({
      campaign: data.campaign?.id || "",
      q: $("search").value,
      state: $("filter").value,
      offset,
    });
    const response = await fetch("/api/snapshot?" + q);
    if (!response.ok) throw new Error("snapshot unavailable");
    const d = await response.json();
    if (g === generation) render(d);
  } catch (e) {
    if (g === generation)
      $("connection").textContent = "○ Connection lost · retrying";
  }
}
async function showPackage(id) {
  const g = ++detailGeneration;
  logAttempt = null;
  const response = await fetch("/api/package?id=" + id);
  if (!response.ok) return;
  const p = await response.json();
  if (g !== detailGeneration) return;
  const nodes = [
    el("h2", p.label),
    el("span", p.state, "badge " + p.state),
    el("p", (p.selection?.reasons || []).join(" · ")),
  ];
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
async function showDerivation(drv, offset = 0) {
  const g = ++detailGeneration;
  logAttempt = null;
  const q = new URLSearchParams({ drv, campaign: data.campaign.id, offset });
  const response = await fetch("/api/derivation?" + q);
  if (!response.ok) return;
  const d = await response.json();
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
  if (d.derivation.failure)
    nodes.push(el("p", "Failure: " + d.derivation.failure));
  for (const t of d.tests) {
    const b = el("button", t.phase + " passed · open attempt log", "attempt");
    b.onclick = () => showLog(t.attempt);
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
async function showLog(id) {
  detailGeneration++;
  logAttempt = id;
  logOffset = 0;
  logText = "";
  replace("detail-content", [
    el("h2", "Attempt log"),
    el("p", id),
    el("pre", "", "log"),
  ]);
  if (!$("detail").open) $("detail").showModal();
  await pollLog();
}
async function pollLog() {
  if (!logAttempt || !$("detail").open) return;
  const id = logAttempt;
  try {
    const response = await fetch(`/api/log?attempt=${id}&offset=${logOffset}`);
    if (!response.ok) return;
    const r = await response.json();
    if (id !== logAttempt) return;
    logOffset = r.offset;
    logText = (logText + r.text).slice(-200000);
    $("detail-content").querySelector("pre").textContent =
      logText || "Waiting for captured stderr…";
  } catch (e) {}
}
$("close-detail").onclick = () => {
  $("detail").close();
  logAttempt = null;
  detailGeneration++;
};
$("detail").addEventListener("close", () => {
  logAttempt = null;
  detailGeneration++;
});
let timer;
$("search").oninput = () => {
  clearTimeout(timer);
  offset = 0;
  timer = setTimeout(refresh, 250);
};
$("filter").onchange = () => {
  offset = 0;
  refresh();
};
$("previous").onclick = () => {
  offset = Math.max(0, offset - 50);
  refresh();
};
$("next").onclick = () => {
  offset += 50;
  refresh();
};
$("campaign-select").onchange = () => {
  const id = $("campaign-select").value;
  data.campaign.id = id;
  offset = 0;
  history.replaceState(null, "", "/?campaign=" + id);
  refresh();
};
render(data);
setInterval(refresh, 5000);
setInterval(pollLog, 1500);
