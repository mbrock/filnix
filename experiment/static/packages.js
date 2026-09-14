/* One complete snapshot; filtering never fetches pages or interrupts reading. */
(() => {
  const $ = (id) => document.getElementById(id);
  const node = (tag, text, cls) => {
    const n = document.createElement(tag);
    if (text != null) n.textContent = text;
    if (cls) n.className = cls;
    return n;
  };
  const number = (n) => n.toLocaleString();
  const states = {
    available: "Available",
    failed: "Failed",
    blocked: "Blocked",
    "evaluation-error": "Eval error",
    inconclusive: "Inconclusive",
    excluded: "Excluded",
    running: "Running",
    queued: "Queued",
    unplanned: "Not evaluated",
  };
  const duration = (s) =>
    s == null
      ? "—"
      : s < 60
        ? `${Math.floor(s)}s`
        : s < 3600
          ? `${Math.floor(s / 60)}m ${Math.floor(s % 60)}s`
          : `${Math.floor(s / 3600)}h ${Math.floor((s % 3600) / 60)}m`;
  const timeKind = (p) =>
    ({
      build: "build",
      building: "building",
      batch: "batch",
      "eval-batch": "eval batch",
    })[p.timing] || "";
  const collator = new Intl.Collator(undefined, {
    numeric: true,
    sensitivity: "base",
  });
  const date = new Intl.DateTimeFormat(undefined, {
    month: "short",
    day: "numeric",
    hour: "2-digit",
    minute: "2-digit",
  });
  const initial = JSON.parse($("initial").textContent);
  let campaign = initial.campaign?.id,
    snapshot = null,
    rows = [],
    shown = [],
    request = 0,
    controller,
    loading = false,
    timer;
  function readURL() {
    const q = new URLSearchParams(location.search);
    $("search").value = q.get("q") || "";
    $("filter").value = q.get("result") || "available";
    if (!$("filter").value) $("filter").value = "available";
    $("package-sort").value = q.get("sort") || "name";
    if (!$("package-sort").value) $("package-sort").value = "name";
    $("package-paths").checked = q.get("paths") === "1";
  }
  function saveURL() {
    const u = new URL(location.href);
    for (const [key, value] of [
      ["q", $("search").value],
      ["result", $("filter").value === "available" ? "" : $("filter").value],
      [
        "sort",
        $("package-sort").value === "name" ? "" : $("package-sort").value,
      ],
      ["paths", $("package-paths").checked ? "1" : ""],
    ]) {
      if (value) u.searchParams.set(key, value);
      else u.searchParams.delete(key);
    }
    history.replaceState(null, "", u);
  }
  function matches(p, state) {
    if (state === "all") return true;
    if (state === "checked") return p.checks.length > 0;
    if (state === "tried") return !["unplanned", "queued"].includes(p.state);
    return p.state === state;
  }
  function render(keepPosition = false) {
    if (!snapshot) return;
    // Locate the first visible row, even when the toolbar has become sticky.
    const visible = keepPosition
      ? [...$("packages").children].find(
          (n) =>
            n.getBoundingClientRect().bottom >
            $("inventory")
              .querySelector(".catalog-controls")
              .getBoundingClientRect().bottom +
              30,
        )
      : null;
    const oldTop = visible?.getBoundingClientRect().top,
      oldId = visible?.dataset.id,
      oldScroll = scrollY;
    const query = $("search")
        .value.trim()
        .toLocaleLowerCase()
        .split(/\s+/)
        .filter(Boolean),
      state = $("filter").value;
    shown = rows.filter(
      (p) =>
        matches(p, state) && query.every((term) => p.search.includes(term)),
    );
    const order = $("package-sort").value;
    shown.sort((a, b) => {
      if (order === "recent" || order === "duration" || order === "shortest") {
        const key = order === "recent" ? "last" : "duration",
          x = a[key],
          y = b[key];
        if (x == null && y != null) return 1;
        if (x != null && y == null) return -1;
        if (x !== y) return (order === "shortest" ? 1 : -1) * (x - y);
      }
      return (
        (order === "name-desc" ? -1 : 1) * collator.compare(a.label, b.label)
      );
    });
    const fragment = document.createDocumentFragment();
    for (const p of shown) {
      const tr = node("tr", null, "package-row");
      tr.dataset.id = p.id;
      const name = node("td", null, "package-identity");
      const open = node("button", p.label, "package-name");
      open.dataset.package = p.id;
      name.append(open, node("span", p.version, "package-version"));
      const description = node("td", null, "package-info");
      const text = node(
        "span",
        p.description || "Description unavailable",
        "package-description",
      );
      text.title = p.description;
      description.append(text);
      if (p.reason && !["available", "queued", "unplanned"].includes(p.state)) {
        const reason = node(
          "span",
          p.reason.replace(/\s+/g, " "),
          "package-reason",
        );
        reason.title = p.reason;
        description.append(reason);
      }
      if (p.source) {
        const path = node(
          p.source_url ? "a" : "span",
          p.source,
          "package-path",
        );
        if (p.source_url) {
          path.href = p.source_url;
          path.target = "_blank";
          path.rel = "noopener";
        }
        description.append(path);
      }
      const result = node("td", null, "package-result");
      result.append(
        node("span", states[p.state] || p.state, "package-state " + p.state),
      );
      const checks = node(
        "span",
        p.checks.length ? "✓ Checks passed" : "— No check evidence",
        "package-checks",
      );
      checks.title = p.checks.length
        ? p.checks.join(", ") + " completed successfully in this campaign"
        : "No recorded successful checks in this campaign";
      if (p.checks.length) checks.classList.add("checked");
      result.append(checks);
      const elapsed = node("td", null, "package-time");
      elapsed.append(
        node("span", duration(p.duration)),
        node("small", timeKind(p)),
      );
      elapsed.title =
        p.duration == null
          ? "Individual build time was not recorded"
          : (p.timing?.includes("batch")
              ? "Duration of the entire job, including other packages and dependencies."
              : "Worker-observed Nix build activity, including its build phases.") +
            (p.time_attempt ? " Job " + p.time_attempt.slice(0, 8) : "");
      const last = node(
        "td",
        p.last ? date.format(p.last * 1000) : "—",
        "package-last",
      );
      if (p.last)
        last.title =
          new Date(p.last * 1000).toLocaleString() + " · " + p.attempt;
      const log = node("td", null, "package-log");
      if (p.attempt) {
        const b = node("button", "Log ↗");
        b.dataset.log = p.attempt;
        b.dataset.drv = p.log_drv || "";
        b.setAttribute("aria-label", "Build or evaluation log for " + p.label);
        log.append(b);
      }
      tr.append(name, description, result, elapsed, last, log);
      fragment.append(tr);
    }
    $("packages").replaceChildren(fragment);
    $("inventory").classList.toggle("show-paths", $("package-paths").checked);
    $("matches").textContent =
      `${number(shown.length)} ${query.length ? "matches" : "packages"} · ${number(new Set(shown.map((p) => p.drv).filter(Boolean)).size)} derivations`;
    $("package-empty").hidden = shown.length !== 0;
    $("package-export").disabled = shown.length === 0;
    for (const b of $("package-tabs").children) {
      b.setAttribute("aria-pressed", String(b.dataset.result === state));
      b.querySelector("b").textContent = number(
        rows.filter((p) => matches(p, b.dataset.result)).length,
      );
    }
    if (keepPosition) {
      const newAnchor =
        oldId &&
        [...$("packages").children].find((n) => n.dataset.id === oldId);
      scrollTo(
        0,
        newAnchor
          ? oldScroll + newAnchor.getBoundingClientRect().top - oldTop
          : oldScroll,
      );
    }
  }
  async function load() {
    if (!campaign || $("inventory").hidden || loading) return;
    const generation = ++request,
      requestedCampaign = campaign;
    controller?.abort();
    controller = new AbortController();
    loading = true;
    $("package-refresh").disabled = true;
    $("package-freshness").textContent = snapshot
      ? "Refreshing…"
      : "Loading the full inventory…";
    try {
      const response = await fetch(
        "/api/packages?" + new URLSearchParams({ campaign }),
        { signal: controller.signal },
      );
      if (!response.ok) throw new Error("Inventory unavailable");
      const result = await response.json();
      if (generation !== request || requestedCampaign !== campaign) return;
      const preserve = !!snapshot;
      snapshot = result;
      rows = result.rows.map((p) => ({
        ...p,
        search: [p.label, p.description, p.version, p.source, p.reason, p.drv]
          .join(" ")
          .toLocaleLowerCase(),
      }));
      render(preserve);
      $("package-freshness").textContent =
        "Loaded " +
        new Date(result.now * 1000).toLocaleTimeString([], {
          hour: "2-digit",
          minute: "2-digit",
        }) +
        " · full list";
      $("package-refresh").textContent = "Refresh";
    } catch (e) {
      if (generation !== request) return;
      $("package-freshness").textContent = snapshot
        ? "Connection lost · loaded list retained"
        : "Could not load the inventory. Retry with Refresh.";
    } finally {
      if (generation === request) {
        loading = false;
        $("package-refresh").disabled = false;
      }
    }
  }
  function changeCampaign(id) {
    if (campaign === id) return;
    campaign = id;
    request++;
    controller?.abort();
    loading = false;
    snapshot = null;
    rows = [];
    shown = [];
    $("packages").replaceChildren();
    $("matches").textContent = "Loading inventory…";
    $("package-export").disabled = true;
    $("package-refresh").disabled = false;
    $("package-empty").hidden = true;
    for (const b of $("package-tabs").children)
      b.querySelector("b").textContent = "";
    load();
  }
  window.packageBrowser = {
    changeCampaign,
    update(d) {
      if (!d.campaign) return;
      changeCampaign(d.campaign.id);
      if (!snapshot) {
        load();
        return;
      }
      if (d.cursor > snapshot.cursor && !loading) {
        $("package-refresh").textContent = "Update list";
        $("package-freshness").textContent = "New activity · update when ready";
      }
    },
  };
  $("packages").onclick = (event) => {
    const p = event.target.closest("[data-package]"),
      log = event.target.closest("[data-log]");
    if (p) window.showPackage(Number(p.dataset.package));
    if (log) window.showLog(log.dataset.log, log.dataset.drv);
  };
  function filterChanged() {
    saveURL();
    render();
  }
  $("search").oninput = () => {
    clearTimeout(timer);
    timer = setTimeout(filterChanged, 120);
  };
  $("filter").onchange = filterChanged;
  $("package-sort").onchange = filterChanged;
  $("package-paths").onchange = () => {
    saveURL();
    $("inventory").classList.toggle("show-paths", $("package-paths").checked);
  };
  $("package-tabs").onclick = (event) => {
    const b = event.target.closest("[data-result]");
    if (b) {
      $("filter").value = b.dataset.result;
      filterChanged();
    }
  };
  $("package-refresh").onclick = load;
  $("package-export").onclick = () => {
    const cell = (v) =>
      '"' +
      String(v ?? "")
        .replace(/^[=+@\-\t\r]/, "'$&")
        .replaceAll('"', '""') +
      '"';
    const columns = [
      "Package",
      "Version",
      "Description",
      "Result",
      "Checks",
      "Seconds",
      "Timing kind",
      "Last attempt",
      "Source",
      "Derivation",
      "Observation",
    ];
    const csv = [
      columns,
      ...shown.map((p) => [
        p.label,
        p.version,
        p.description,
        p.state,
        p.checks.join("; "),
        p.duration,
        p.timing,
        p.last ? new Date(p.last * 1000).toISOString() : "",
        p.source_url || p.source,
        p.drv,
        p.reason,
      ]),
    ]
      .map((r) => r.map(cell).join(","))
      .join("\r\n");
    const url = URL.createObjectURL(
        new Blob(["\ufeff" + csv], { type: "text/csv;charset=utf-8" }),
      ),
      a = node("a");
    a.href = url;
    a.download = `filnix-${$("filter").value}.csv`;
    a.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  };
  window.addEventListener("viewchange", () => {
    if (!snapshot) load();
  });
  window.addEventListener("popstate", () => {
    readURL();
    render();
  });
  new ResizeObserver(([entry]) =>
    $("inventory").style.setProperty(
      "--catalog-height",
      entry.target.getBoundingClientRect().height + "px",
    ),
  ).observe(document.querySelector(".catalog-controls"));
  readURL();
  load();
})();
