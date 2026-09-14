/* A stable, keyboard-accessible neighborhood, with dependency arrows behind it. */
(() => {
  const states = {
    building: "Building",
    excluded: "Excluded",
    available: "Available",
    failed: "Failed",
    blocked: "Blocked",
    waiting: "Waiting / not started",
    settling: "Awaiting result",
    unknown: "Not observed",
  };
  const phases = {
    configurePhase: "Configuring",
    buildPhase: "Building",
    checkPhase: "Running checks",
    installCheckPhase: "Running install checks",
    installPhase: "Installing",
    fixupPhase: "Finalizing",
    unpackPhase: "Unpacking",
    patchPhase: "Patching",
  };
  let campaign = null,
    focus = null,
    page = 0,
    generation = 0,
    current = null,
    signature = null;
  const name = (n) =>
    n.labels[0]?.label ||
    n.name.replaceAll("-x86_64-unknown-linux-gnufilc0", "");
  const phase = (n) =>
    n.state === "building"
      ? phases[n.phase] || n.phase || states[n.state]
      : states[n.state];
  function choose(drv, fromRoute = false) {
    if (window.dashboardNavigation && !fromRoute)
      return window.dashboardNavigation.focus(drv);
    focus = drv;
    page = 0;
    signature = null;
    refreshGraph();
  }
  function node(n, center = false) {
    const b = el(
      "button",
      null,
      "graph-node " + n.state + (center ? " focal" : ""),
    );
    b.dataset.drv = n.drv;
    b.title = n.name + "\n" + n.drv;
    if (n.availability_evidence === "consumer-phase")
      b.title +=
        "\nAvailability inferred from a consumer reaching a build phase. Build/test origin remains unknown.";
    b.append(
      el("span", name(n), "graph-node-name"),
      el("span", phase(n), "graph-node-state"),
    );
    if (n.roles?.length)
      b.append(el("small", n.roles.join(" · "), "graph-role"));
    if (n.failure) b.append(el("small", n.failure, "graph-role"));
    b.setAttribute(
      "aria-label",
      `${name(n)}: ${phase(n)}. ${center ? "Open details" : "Explore dependencies"}`,
    );
    b.onclick = () => (center ? showDerivation(n.drv) : choose(n.drv));
    return b;
  }
  function chip(n) {
    const b = el(
      "button",
      name(n),
      "graph-chip " +
        n.state +
        (current?.focus?.drv === n.drv ? " selected" : ""),
    );
    b.title = n.name + " · " + states[n.state];
    b.onclick = () => choose(n.drv);
    return b;
  }
  function drawEdges() {
    const svg = $("graph-edges"),
      stage = $("graph-stage"),
      bounds = stage.getBoundingClientRect();
    svg.replaceChildren();
    svg.setAttribute("viewBox", `0 0 ${bounds.width} ${bounds.height}`);
    const ns = "http://www.w3.org/2000/svg";
    const defs = document.createElementNS(ns, "defs"),
      marker = document.createElementNS(ns, "marker");
    for (const [k, v] of Object.entries({
      id: "graph-arrow",
      viewBox: "0 0 10 10",
      refX: "9",
      refY: "5",
      markerWidth: "5",
      markerHeight: "5",
      orient: "auto-start-reverse",
    }))
      marker.setAttribute(k, v);
    const tip = document.createElementNS(ns, "path");
    tip.setAttribute("d", "M 0 0 L 10 5 L 0 10 z");
    tip.setAttribute("fill", "#93a38d");
    marker.append(tip);
    defs.append(marker);
    svg.append(defs);
    const nodes = [...stage.querySelectorAll("[data-drv]")];
    const edges = [...(current?.edges || [])];
    if (nodes.some((n) => n.dataset.drv === "available-inputs"))
      edges.push({ source: "available-inputs", target: current.focus.drv });
    for (const e of edges) {
      const a = nodes.find((n) => n.dataset.drv === e.source),
        b = nodes.find((n) => n.dataset.drv === e.target);
      if (!a || !b) continue;
      const ra = a.getBoundingClientRect(),
        rb = b.getBoundingClientRect(),
        mobile = innerWidth <= 650;
      const x1 = (mobile ? ra.left + ra.width / 2 : ra.right) - bounds.left,
        y1 = (mobile ? ra.bottom : ra.top + ra.height / 2) - bounds.top;
      const x2 = (mobile ? rb.left + rb.width / 2 : rb.left) - bounds.left,
        y2 = (mobile ? rb.top : rb.top + rb.height / 2) - bounds.top;
      const left1 = ra.left - bounds.left,
        left2 = rb.left - bounds.left;
      const middle1 = ra.top + ra.height / 2 - bounds.top,
        middle2 = rb.top + rb.height / 2 - bounds.top;
      const bus = Math.max(2, Math.min(left1, left2) - 14);
      const d = mobile
        ? `M${left1},${middle1} H${bus} V${middle2} H${left2}`
        : `M${x1},${y1} C${(x1 + x2) / 2},${y1} ${(x1 + x2) / 2},${y2} ${x2},${y2}`;
      const path = document.createElementNS(ns, "path");
      path.setAttribute("d", d);
      path.setAttribute("marker-end", "url(#graph-arrow)");
      svg.append(path);
    }
  }
  function renderGraph(g) {
    current = g;
    const fresh = g.heartbeat && Date.now() / 1000 - g.heartbeat < 30;
    $("graph-freshness").textContent = fresh
      ? "Updated just now"
      : "Controller stale · last known state";
    const w = g.work;
    $("graph-work-status").textContent =
      w.kind === "plan"
        ? `Evaluating recipes · ${w.completed} of ${w.total} complete`
        : w.kind === "build"
          ? w.stage === "preflight"
            ? "Checking which outputs are already in the store…"
            : g.building.length
              ? `${g.building.length} build${g.building.length === 1 ? "" : "s"} running in Nix`
              : "Nix is resolving dependencies or fetching outputs"
          : g.mode === "paused"
            ? "Campaign paused"
            : "Between batches";
    if (g.planning && w.kind === "build")
      $("graph-work-status").textContent +=
        ` · planning ${g.planning.completed}/${g.planning.total}`;
    $("graph-batch-label").textContent =
      g.batches?.length > 1
        ? `${g.batches.length} active batches`
        : g.batch?.state === "finished"
          ? "Last build batch"
          : "Batch";
    $("graph-follow").textContent = focus ? "Follow live" : "● Live";
    $("graph-follow").setAttribute("aria-pressed", String(!focus));
    $("graph-back").disabled = !focus;
    const nextSignature = JSON.stringify([
      g.focus,
      g.inputs,
      g.consumers,
      g.roots,
      g.building,
      g.totals,
      g.selected_dependents,
      g.affected_roots,
      g.page,
      focus,
    ]);
    if (nextSignature === signature) return;
    signature = nextSignature;
    const focused = document.activeElement?.dataset?.drv;
    replace(
      "graph-running",
      g.building.map((n) => {
        const b = el("button", name(n) + " · " + phase(n), "graph-live-build");
        b.onclick = () => choose(n.drv);
        return b;
      }),
    );
    replace("graph-roots", g.roots.map(chip));
    $("graph-input-label").textContent = `DEPENDS ON · ${g.totals.inputs || 0}`;
    $("graph-consumer-label").textContent =
      `NEEDED BY · ${g.totals.consumers || 0}`;
    const emptyInputs =
      g.totals.hidden_available === g.totals.inputs && g.totals.inputs
        ? `${g.totals.inputs} available inputs hidden`
        : "No inputs on this page";
    replace(
      "graph-inputs",
      g.inputs.length
        ? g.inputs.map((n) => node(n))
        : [el("p", emptyInputs, "graph-empty")],
    );
    if (g.totals.hidden_available) {
      const ready = el("button", null, "graph-node available graph-collapsed");
      ready.dataset.drv = "available-inputs";
      ready.append(
        el(
          "span",
          `${g.totals.hidden_available} available inputs`,
          "graph-node-name",
        ),
        el("span", "Expand dependencies ↗", "graph-node-state"),
      );
      ready.onclick = () => {
        $("graph-available").checked = true;
        page = 0;
        signature = null;
        refreshGraph();
      };
      if (!g.inputs.length) $("graph-inputs").replaceChildren(ready);
      else $("graph-inputs").append(ready);
    }
    replace(
      "graph-consumers",
      g.consumers.length
        ? g.consumers.map((n) => node(n))
        : [el("p", "No recorded consumers here.", "graph-empty")],
    );
    const center = g.focus
      ? [node(g.focus, true)]
      : [
          el(
            "p",
            "The map will appear as recipes are evaluated.",
            "graph-empty",
          ),
        ];
    if (g.focus) {
      center.push(
        el(
          "p",
          `${g.selected_dependents} selected package${g.selected_dependents === 1 ? " depends" : "s depend"} on this`,
          "graph-impact",
        ),
      );
      if (g.affected_roots.length) {
        center.push(
          el("span", "Leads to these batch targets", "graph-target-label"),
        );
        const list = el("div", null, "graph-roots graph-affected");
        list.append(...g.affected_roots.map(chip));
        center.push(list);
      }
      if (g.focus.attempt) {
        const log = el("button", "Open build log ↗", "graph-log");
        log.onclick = () => showLog(g.focus.attempt, g.focus.drv);
        center.push(log);
      }
    }
    replace("graph-focus", center);
    $("graph-previous").hidden = g.page === 0;
    $("graph-next").hidden = !g.totals.more;
    $("graph-explanation").textContent = g.totals.hidden_available
      ? `${g.totals.hidden_available} ready inputs hidden`
      : "";
    if (focused)
      [...$("graph-stage").querySelectorAll("[data-drv]")]
        .find((n) => n.dataset.drv === focused)
        ?.focus({ preventScroll: true });
    requestAnimationFrame(drawEdges);
  }
  async function refreshGraph() {
    if (!campaign) return;
    const g = ++generation;
    try {
      const q = new URLSearchParams({
        campaign,
        focus: focus || "",
        available: $("graph-available").checked ? "1" : "0",
        page,
      });
      const response = await fetch("/api/graph?" + q);
      if (!response.ok) throw new Error("Graph unavailable");
      const value = await response.json();
      if (g !== generation) return;
      page = value.page;
      renderGraph(value);
    } catch (e) {
      if (g === generation)
        $("graph-freshness").textContent =
          "Connection lost · showing last observation";
    }
  }
  window.dependencyMap = {
    updateCampaign(id) {
      if (id === campaign) return;
      campaign = id;
      focus = null;
      page = 0;
      signature = null;
      refreshGraph();
    },
    focus: (drv) => {
      if (focus !== drv) choose(drv, true);
    },
    locate(drv) {
      window.dashboardNavigation.focus(drv);
    },
  };
  $("graph-follow").onclick = () => window.dashboardNavigation.focus(null);
  $("graph-back").onclick = () => window.dashboardNavigation.backGraph();
  $("graph-available").onchange = () => {
    page = 0;
    signature = null;
    refreshGraph();
  };
  $("graph-previous").onclick = () => {
    page = Math.max(0, page - 1);
    refreshGraph();
  };
  $("graph-next").onclick = () => {
    page++;
    refreshGraph();
  };
  new ResizeObserver(drawEdges).observe($("graph-stage"));
  window.addEventListener("resize", drawEdges);
  window.dependencyMap.updateCampaign(data.campaign?.id);
  setInterval(refreshGraph, 5000);
})();
