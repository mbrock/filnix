/* A complete batch snapshot; sorting and searching never fetch another page. */
(() => {
  const $ = (id) => document.getElementById(id);
  const node = (tag, text, cls) => {
    const n = document.createElement(tag);
    if (text != null) n.textContent = text;
    if (cls) n.className = cls;
    return n;
  };
  const initial = JSON.parse($("initial").textContent);
  const fields = {
    batchQ: "batch-search",
    batchKind: "batch-kind",
    batchSort: "batch-sort",
    batchResult: "batch-result",
  };
  const defaults = {
    batchQ: "",
    batchKind: "build",
    batchSort: "longest",
    batchResult: "all",
  };
  const date = new Intl.DateTimeFormat(undefined, {
    month: "short",
    day: "numeric",
    hour: "2-digit",
    minute: "2-digit",
  });
  const duration = (s) =>
    s == null
      ? "—"
      : s < 60
        ? `${Math.floor(s)}s`
        : s < 3600
          ? `${Math.floor(s / 60)}m ${Math.floor(s % 60)}s`
          : `${Math.floor(s / 3600)}h ${Math.floor(s / 60) % 60}m`;
  const result = (b) =>
    b.outcome === "active"
      ? "Running"
      : b.outcome === "complete"
        ? "Completed"
        : b.outcome === "unknown"
          ? "Unknown"
          : (b.reason || "Error").replaceAll("-", " ");
  let campaign = initial.campaign?.id,
    snapshot,
    rows = [],
    controller,
    loading = false,
    request = 0,
    signature = "",
    editingSearch = false;
  function readURL() {
    const q = new URLSearchParams(location.search);
    for (const [key, id] of Object.entries(fields)) {
      $(id).value = q.get(key) || defaults[key];
      if (!$(id).value) $(id).value = defaults[key];
    }
  }
  function saveURL(replace = false) {
    const u = new URL(location.href);
    for (const [key, id] of Object.entries(fields)) {
      const value = $(id).value;
      if (value !== defaults[key]) u.searchParams.set(key, value);
      else u.searchParams.delete(key);
    }
    window.dashboardNavigation.go(u, { replace, scroll: "keep" });
  }
  function attemptURL(id) {
    const u = new URL(location.href);
    for (const k of [
      "package",
      "derivation",
      "depPage",
      "log",
      "logDrv",
      "follow",
    ])
      u.searchParams.delete(k);
    u.searchParams.set("attempt", id);
    return u.href;
  }
  function timeline(shown) {
    const known = shown
      .filter((b) => b.duration != null)
      .sort((a, b) => a.created - b.created || a.id.localeCompare(b.id));
    const track = $("batch-timeline"),
      axis = $("batch-axis");
    track.replaceChildren();
    axis.replaceChildren();
    if (!known.length) return;
    const start = known[0].created,
      end = Math.max(...known.map((b) => b.created + b.duration)),
      width = Math.max(1, end - start),
      lanes = [];
    const fragment = document.createDocumentFragment();
    for (const b of known) {
      let lane = lanes.findIndex((end) => end <= b.created);
      if (lane < 0) lane = lanes.length;
      lanes[lane] = b.created + b.duration;
      const bar = node("a", null, "batch-interval " + b.outcome);
      bar.href = attemptURL(b.id);
      bar.dataset.batch = b.id;
      bar.style.left = `${(100 * (b.created - start)) / width}%`;
      bar.style.width = `${(100 * b.duration) / width}%`;
      bar.style.top = `${lane * 14 + 4}px`;
      bar.title = `${b.kind === "plan" ? "Planning" : "Build"} ${b.id.slice(0, 8)} · ${date.format(b.created * 1000)} · ${duration(b.duration)}${b.outcome === "active" ? " elapsed" : ""} · ${result(b)}\n${b.roots.join(", ")}`;
      bar.setAttribute("aria-label", bar.title);
      // The same batch has a full-size keyboard/touch link in the table.
      bar.tabIndex = -1;
      fragment.append(bar);
    }
    track.style.height = `${Math.max(1, lanes.length) * 14 + 8}px`;
    track.append(fragment);
    axis.append(
      node("span", date.format(start * 1000)),
      node("span", date.format(end * 1000)),
    );
  }
  function render(preserve = false) {
    if (!snapshot) return;
    const anchor = preserve
        ? [...$("batches").children].find(
            (n) => n.getBoundingClientRect().bottom > 30,
          )
        : null,
      top = anchor?.getBoundingClientRect().top,
      y = scrollY;
    const q = $("batch-search").value.trim().toLocaleLowerCase(),
      kind = $("batch-kind").value,
      outcome = $("batch-result").value,
      sort = $("batch-sort").value;
    const shown = rows.filter(
      (b) =>
        (kind === "all" || b.kind === kind) &&
        (outcome === "all" || b.outcome === outcome) &&
        (!q || b.search.includes(q)),
    );
    shown.sort((a, b) => {
      if (sort === "newest" || sort === "oldest")
        return (
          (sort === "newest" ? -1 : 1) * (a.created - b.created) ||
          a.id.localeCompare(b.id)
        );
      if (a.duration == null && b.duration != null) return 1;
      if (b.duration == null && a.duration != null) return -1;
      return (
        (sort === "shortest" ? 1 : -1) * (a.duration - b.duration) ||
        b.created - a.created ||
        a.id.localeCompare(b.id)
      );
    });
    const max = Math.max(1, ...shown.map((b) => b.duration || 0));
    const fragment = document.createDocumentFragment();
    for (const b of shown) {
      const tr = node("tr", null, "batch-row");
      tr.dataset.batch = b.id;
      tr.dataset.duration = b.duration ?? "";
      const elapsed = node("td", null, "batch-duration");
      const open = node("a", duration(b.duration));
      open.href = attemptURL(b.id);
      open.dataset.batch = b.id;
      open.setAttribute(
        "aria-label",
        `${duration(b.duration)}: ${b.kind} batch ${b.id.slice(0, 8)}`,
      );
      elapsed.append(open);
      if (b.outcome === "active")
        elapsed.append(node("span", " elapsed", "batch-elapsed"));
      const bar = node("span", null, "duration-bar " + b.outcome);
      bar.style.width = `${(100 * (b.duration || 0)) / max}%`;
      elapsed.append(bar);
      const packages = node("td", null, "batch-packages");
      const names = node(
        "a",
        b.roots.join(", ") || "No requested packages",
        "batch-roots",
      );
      names.href = attemptURL(b.id);
      names.dataset.batch = b.id;
      names.title = b.roots.join(", ");
      const note = [b.kind === "plan" ? "Planning" : "Build", b.id.slice(0, 8)];
      if (b.builds) note.push(`${b.builds} builds`);
      if (b.tested) note.push(`${b.tested} tested`);
      packages.append(names, node("span", note.join(" · "), "batch-meta"));
      if (q) {
        const matches = b.names.filter(
          (n) => n.toLocaleLowerCase().includes(q) && !b.roots.includes(n),
        );
        if (matches.length)
          packages.append(node("span", matches.join(", "), "batch-matched"));
      }
      const started = node("td", date.format(b.created * 1000), "batch-start");
      started.title = new Date(b.created * 1000).toLocaleString();
      const status = node("td", result(b), "batch-outcome " + b.outcome);
      tr.append(elapsed, packages, started, status);
      fragment.append(tr);
    }
    $("batches").replaceChildren(fragment);
    $("batch-count").textContent =
      `${shown.length.toLocaleString()}${shown.length === rows.length ? "" : " / " + rows.length.toLocaleString()}`;
    $("batch-empty").hidden = !!shown.length;
    timeline(shown);
    if (anchor) {
      const next = [...$("batches").children].find(
        (n) => n.dataset.batch === anchor.dataset.batch,
      );
      if (next) scrollTo(0, y + next.getBoundingClientRect().top - top);
    }
  }
  async function load() {
    if (!campaign || $("batch-timings").hidden || loading) return;
    const generation = ++request,
      requestedCampaign = campaign;
    controller?.abort();
    controller = new AbortController();
    loading = true;
    $("batch-refresh").disabled = true;
    $("batch-freshness").textContent = snapshot
      ? "Refreshing…"
      : "Loading batches…";
    try {
      const response = await fetch(
        "/api/batches?" + new URLSearchParams({ campaign }),
        { signal: controller.signal },
      );
      if (!response.ok) throw new Error("Batches unavailable");
      const value = await response.json();
      if (generation !== request || requestedCampaign !== campaign) return;
      const preserve = !!snapshot;
      snapshot = value;
      rows = value.rows.map((b) => ({
        ...b,
        search: [b.id, ...b.names].join("\n").toLocaleLowerCase(),
      }));
      render(preserve);
      $("batch-freshness").textContent =
        "As of " +
        new Date(value.now * 1000).toLocaleTimeString([], {
          hour: "2-digit",
          minute: "2-digit",
        });
      $("batch-refresh").textContent = "Refresh";
      window.dispatchEvent(new Event("contentready"));
    } catch (e) {
      if (generation !== request) return;
      $("batch-freshness").textContent = snapshot
        ? "Connection lost · loaded batches retained"
        : "Could not load batches. Retry with Refresh.";
    } finally {
      if (generation === request) {
        loading = false;
        $("batch-refresh").disabled = false;
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
    $("batches").replaceChildren();
    $("batch-timeline").replaceChildren();
    $("batch-axis").replaceChildren();
    $("batch-count").textContent = "";
    $("batch-empty").hidden = true;
    $("batch-refresh").disabled = false;
    load();
  }
  window.batchBrowser = {
    ready: () => !!snapshot,
    changeCampaign,
    update(d) {
      if (!d.campaign) return;
      changeCampaign(d.campaign.id);
      if (!snapshot) load();
      else if (d.cursor > snapshot.cursor && !loading)
        $("batch-refresh").textContent = "Update";
    },
  };
  for (const id of ["batch-kind", "batch-sort", "batch-result"])
    $(id).onchange = () => {
      editingSearch = false;
      saveURL();
    };
  $("batch-search").oninput = () => {
    saveURL(editingSearch);
    editingSearch = true;
  };
  $("batch-search").onblur = () => {
    editingSearch = false;
  };
  $("batch-refresh").onclick = load;
  $("batch-timings").onclick = (event) => {
    const link = event.target.closest("a[data-batch]");
    if (
      !link ||
      event.button ||
      event.ctrlKey ||
      event.metaKey ||
      event.shiftKey ||
      event.altKey
    )
      return;
    event.preventDefault();
    window.dashboardNavigation.attempt(link.dataset.batch);
  };
  window.addEventListener("viewchange", () => {
    if (!snapshot) load();
  });
  window.addEventListener("popstate", () => {
    editingSearch = false;
  });
  window.addEventListener("routechange", () => {
    readURL();
    const next = JSON.stringify(Object.values(fields).map((id) => $(id).value));
    if (next !== signature) {
      signature = next;
      render();
    }
  });
  readURL();
})();
