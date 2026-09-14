/* URL-backed views and overlays, with one history entry per user navigation. */
(() => {
  const $ = (id) => document.getElementById(id);
  const views = {
    activity: "history",
    packages: "inventory",
    dependencies: "dependency-map",
  };
  const overlayKeys = [
    "package",
    "derivation",
    "depPage",
    "attempt",
    "log",
    "logDrv",
    "follow",
  ];
  const initial = JSON.parse($("initial").textContent);
  let applied = "",
    serial = 0,
    restoration = null;
  const url = () => new URL(location.href);
  const state = () => history.state?.filnix || {};
  const key = () => crypto.randomUUID();
  history.scrollRestoration = "manual";
  if (!state().key)
    history.replaceState(
      { filnix: { key: key(), y: scrollY, parent: null } },
      "",
      location.href,
    );
  function save() {
    const s = { ...state(), y: scrollY };
    s.focus =
      document.activeElement?.closest("[data-package]")?.dataset.package ||
      null;
    s.detailScroll = $("detail").scrollTop;
    s.attemptScroll = $("history-record").scrollTop;
    history.replaceState({ filnix: s }, "", location.href);
  }
  function restore() {
    if (!restoration) return;
    const { token, s } = restoration;
    requestAnimationFrame(() => {
      if (token !== serial) return;
      const ready =
        document.body.dataset.view !== "packages" ||
        window.packageBrowser.ready();
      if (!ready) return;
      scrollTo(0, s.y || 0);
      $("detail").scrollTop = s.detailScroll || 0;
      $("history-record").scrollTop = s.attemptScroll || 0;
      if ((s.y || 0) <= document.documentElement.scrollHeight - innerHeight + 1)
        restoration = null;
      if (
        s.focus &&
        !$("detail").open &&
        !$("log-view").open &&
        !$("history-record").open
      )
        document
          .querySelector(`[data-package="${CSS.escape(s.focus)}"]`)
          ?.focus({ preventScroll: true });
    });
  }
  async function apply() {
    const token = ++serial,
      u = url(),
      q = u.searchParams;
    restoration = { token, s: state() };
    const campaign = q.get("campaign") || initial.campaigns?.[0]?.id;
    const view =
      Object.keys(views).find((k) => "#" + views[k] === u.hash) || "activity";
    const old = new URL(applied || u.href);
    const campaignChanged =
      old.searchParams.get("campaign") !== q.get("campaign");
    window.showView(view, false);
    window.changeCampaign(campaign);
    window.dispatchEvent(new Event("routechange"));
    window.dependencyMap.focus(q.get("focus") || null);
    for (const menu of document.querySelectorAll(".menu[open]"))
      menu.open = false;
    if (!q.has("log")) $("log-view").close();
    if (!q.has("package") && !q.has("derivation")) window.closeDetails();
    if (!q.has("attempt")) $("history-record").close();
    applied = u.href;
    const changed = (keys) =>
      !old ||
      !keys.every((k) => old.searchParams.get(k) === q.get(k)) ||
      campaignChanged;
    if (
      q.has("attempt") &&
      (!$("history-record").open || changed(["attempt"]))
    ) {
      await window.attemptHistory.open(q.get("attempt"));
      if (token !== serial) return;
    }
    if (
      q.has("package") &&
      (!$("detail").open || changed(["package", "derivation"]))
    ) {
      await window.showPackage(Number(q.get("package")), true);
      if (token !== serial) return;
    } else if (
      q.has("derivation") &&
      (!$("detail").open || changed(["package", "derivation", "depPage"]))
    ) {
      await window.showDerivation(
        q.get("derivation"),
        Number(q.get("depPage") || 0),
        true,
      );
      if (token !== serial) return;
    }
    if (
      q.has("log") &&
      (!$("log-view").open || changed(["log", "logDrv", "follow"]))
    )
      window.buildLogs.open(
        q.get("log"),
        q.get("logDrv") || "",
        q.get("follow") === "1",
        true,
      );
    restore();
  }
  function go(next, { replace = false, scroll = "top" } = {}) {
    next = new URL(next, location.href);
    if (next.href === location.href) return;
    save();
    const current = state(),
      parent = { url: location.href, key: current.key };
    const nextState = replace ? { ...current } : { key: key(), parent };
    if (scroll === "keep")
      Object.assign(nextState, {
        y: scrollY,
        focus: current.focus,
        detailScroll: current.detailScroll,
        attemptScroll: current.attemptScroll,
      });
    else
      Object.assign(nextState, {
        y: 0,
        focus: null,
        detailScroll: 0,
        attemptScroll: 0,
      });
    history[replace ? "replaceState" : "pushState"](
      { filnix: nextState },
      "",
      next,
    );
    apply();
  }
  function clearOverlays(u) {
    for (const k of overlayKeys) u.searchParams.delete(k);
    return u;
  }
  function packageURL(id) {
    const u = url();
    for (const k of ["derivation", "depPage", "log", "logDrv", "follow"])
      u.searchParams.delete(k);
    u.searchParams.set("package", id);
    return u.href;
  }
  function logURL(id, drv = "", continuous = false) {
    const u = url();
    u.searchParams.set("log", id);
    for (const [k, v] of [
      ["logDrv", drv],
      ["follow", continuous ? "1" : ""],
    ]) {
      if (v) u.searchParams.set(k, v);
      else u.searchParams.delete(k);
    }
    return u.href;
  }
  window.dashboardNavigation = {
    go,
    packageURL,
    logURL,
    view(view) {
      const u = clearOverlays(url());
      u.hash = views[view] || views.activity;
      go(u);
    },
    campaign(id) {
      const u = clearOverlays(url());
      u.searchParams.set("campaign", id);
      u.searchParams.delete("focus");
      go(u);
    },
    package(id) {
      go(packageURL(id), { scroll: "keep" });
    },
    derivation(drv, page = 0) {
      const u = url();
      for (const k of ["package", "log", "logDrv", "follow"])
        u.searchParams.delete(k);
      u.searchParams.set("derivation", drv);
      u.searchParams.set("depPage", page);
      go(u, { scroll: "keep" });
    },
    attempt(id) {
      const u = clearOverlays(url());
      u.searchParams.set("attempt", id);
      go(u, { scroll: "keep" });
    },
    log(id, drv = "", continuous = false) {
      if (!id) return;
      const next = logURL(id, drv, continuous);
      if (next === location.href)
        return window.buildLogs.open(id, drv, continuous, true);
      go(next, { replace: url().searchParams.has("log"), scroll: "keep" });
    },
    logFollowing(value) {
      const u = url();
      if (!u.searchParams.has("log")) return;
      if (value) u.searchParams.set("follow", "1");
      else u.searchParams.delete("follow");
      history.replaceState(history.state, "", u);
      applied = u.href;
    },
    focus(drv) {
      const u = clearOverlays(url());
      u.hash = views.dependencies;
      if (drv) u.searchParams.set("focus", drv);
      else u.searchParams.delete("focus");
      go(u, {
        scroll: location.hash === "#" + views.dependencies ? "keep" : "top",
      });
    },
    backGraph() {
      if (
        state().parent &&
        new URL(state().parent.url).hash === "#" + views.dependencies
      )
        history.back();
      else this.focus(null);
    },
    close(kind) {
      if (state().parent) {
        history.back();
        return;
      }
      const u = url();
      const keys =
        kind === "log"
          ? ["log", "logDrv", "follow"]
          : kind === "detail"
            ? ["package", "derivation", "depPage", "log", "logDrv", "follow"]
            : overlayKeys;
      for (const k of keys) u.searchParams.delete(k);
      go(u, { replace: true, scroll: "keep" });
    },
  };
  for (const [id, kind] of [
    ["detail", "detail"],
    ["history-record", "attempt"],
    ["log-view", "log"],
  ])
    $(id).addEventListener("cancel", (event) => {
      if (event.defaultPrevented) return;
      event.preventDefault();
      window.dashboardNavigation.close(kind);
    });
  window.addEventListener("popstate", apply);
  window.addEventListener("hashchange", () => {
    if (location.href !== applied) apply();
  });
  window.addEventListener("contentready", restore);
  // Keep the current entry accurate for browser Back, reload, and native links.
  let saveFrame;
  window.addEventListener(
    "scroll",
    () => {
      if (saveFrame) return;
      saveFrame = requestAnimationFrame(() => {
        saveFrame = null;
        save();
      });
    },
    { passive: true },
  );
  window.addEventListener("pagehide", save);
  apply();
})();
