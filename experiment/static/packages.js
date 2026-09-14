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
          ? `${Math.floor(s / 60)}m`
          : `${(s / 3600).toFixed(1)}h`;
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
    filterSignature = "";
  function readURL() {
    const q = new URLSearchParams(location.search);

    $("filter").value = q.get("result") || "available";
    if (!$("filter").value) $("filter").value = "available";
    $("package-sort").value = q.get("sort") || "name";
    if (!$("package-sort").value) $("package-sort").value = "name";
    $("package-paths").checked = q.get("paths") === "1";
    $("package-dates").checked = q.get("dates") === "1";
  }
  function saveURL() {
    const u = new URL(location.href);
    for (const [key, value] of [
      ["result", $("filter").value === "available" ? "" : $("filter").value],
      [
        "sort",
        $("package-sort").value === "name" ? "" : $("package-sort").value,
      ],
      ["paths", $("package-paths").checked ? "1" : ""],
      ["dates", $("package-dates").checked ? "1" : ""],
    ]) {
      if (value) u.searchParams.set(key, value);
      else u.searchParams.delete(key);
    }
    u.searchParams.delete("q");
    window.dashboardNavigation.go(u, { scroll: "keep" });
  }
  function matches(p, state) {
    if (state === "all") return true;
    if (state === "checked") return p.checks.length > 0;
    if (state === "tried") return !["unplanned", "queued"].includes(p.state);
    return p.state === state;
  }
  function render(keepPosition = false) {
    if (!snapshot) return;
    const visible = keepPosition
      ? [...$("packages").children].find(
          (n) => n.getBoundingClientRect().bottom > 30,
        )
      : null;
    const oldTop = visible?.getBoundingClientRect().top,
      oldId = visible?.dataset.id,
      oldScroll = scrollY;
    const state = $("filter").value;
    shown = rows.filter((p) => matches(p, state));
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
      const open = node("a", p.label, "package-name");
      open.href = window.dashboardNavigation.packageURL(p.id);
      open.dataset.package = p.id;
      name.append(
        open,
        document.createTextNode(" "),
        node("span", p.version, "package-version"),
      );
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
      const status = node(
        "span",
        p.checks.length && p.state === "available"
          ? "Checked"
          : states[p.state] || p.state,
        "package-state " + p.state,
      );
      status.title = p.checks.length
        ? p.checks.join(", ") + " passed in this campaign"
        : "No successful check evidence recorded";
      result.append(status);
      const elapsed = node("td", null, "package-time");
      const timeText =
        p.duration == null
          ? p.attempt
            ? "Log"
            : "—"
          : duration(p.duration) + " " + timeKind(p);
      const time = node(p.attempt ? "a" : "span", timeText);
      if (p.attempt) {
        const aid = p.time_attempt || p.attempt;
        const drv =
          p.timing === "build" || p.timing === "building"
            ? p.drv
            : p.log_drv || "";
        time.href = window.dashboardNavigation.logURL(aid, drv);
        time.dataset.log = aid;
        time.dataset.drv = drv;
        time.setAttribute("aria-label", timeText + ": log for " + p.label);
      }
      elapsed.title =
        p.duration == null
          ? "Open recorded attempt log"
          : (p.timing?.includes("batch")
              ? "Whole job duration, including other packages and dependencies."
              : "Individual build activity duration.") +
            " " +
            Math.round(p.duration) +
            " seconds. Job " +
            p.time_attempt;
      elapsed.append(time);
      const last = node(
        "td",
        p.last ? date.format(p.last * 1000) : "—",
        "package-last",
      );
      if (p.last)
        last.title =
          new Date(p.last * 1000).toLocaleString() + " · " + p.attempt;
      tr.append(name, description, result, elapsed, last);
      fragment.append(tr);
    }
    $("packages").replaceChildren(fragment);
    $("inventory").classList.toggle("show-paths", $("package-paths").checked);
    $("inventory").classList.toggle("show-dates", $("package-dates").checked);
    $("matches").textContent = number(shown.length);
    $("matches").title =
      number(new Set(shown.map((p) => p.drv).filter(Boolean)).size) +
      " distinct derivations";
    $("package-empty").hidden = shown.length !== 0;
    $("package-export").disabled = shown.length === 0;
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
      rows = result.rows;
      render(preserve);
      window.dispatchEvent(new Event("contentready"));
      $("package-freshness").textContent =
        "Loaded " +
        new Date(result.now * 1000).toLocaleTimeString([], {
          hour: "2-digit",
          minute: "2-digit",
        }) +
        " · full list";
      $("package-refresh").textContent = "Refresh list";
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

    load();
  }
  window.packageBrowser = {
    ready: () => !!snapshot,
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
    if (
      event.button ||
      event.ctrlKey ||
      event.metaKey ||
      event.shiftKey ||
      event.altKey
    )
      return;
    if (p || log) event.preventDefault();
    if (p) window.showPackage(Number(p.dataset.package));
    if (log) window.showLog(log.dataset.log, log.dataset.drv);
  };
  $("filter").onchange = saveURL;
  $("package-sort").onchange = saveURL;
  $("package-paths").onchange = saveURL;
  $("package-dates").onchange = saveURL;
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
  window.addEventListener("routechange", () => {
    readURL();
    const signature = [
      $("filter").value,
      $("package-sort").value,
      $("package-paths").checked,
      $("package-dates").checked,
    ].join("/");
    if (signature !== filterSignature) {
      filterSignature = signature;
      render();
    }
  });
  readURL();
  // Navigation initializes after all view modules have registered.
})();
