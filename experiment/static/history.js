/* Recorded attempts, with a stable reading position independent of live work. */
(() => {
  const $ = (id) => document.getElementById(id);
  const el = (tag, text, cls) => {
    const n = document.createElement(tag);
    if (text != null) n.textContent = text;
    if (cls) n.className = cls;
    return n;
  };
  const fmt = (n) => Number(n || 0).toLocaleString();
  const time = (t) => new Date(t * 1000).toISOString().slice(11, 19);
  const date = (t) => new Date(t * 1000).toISOString().slice(0, 10);
  const elapsed = (s) => {
    s = Math.max(0, Math.floor(s));
    return (
      (s >= 3600 ? Math.floor(s / 3600) + ":" : "") +
      String(Math.floor(s / 60) % 60).padStart(2, "0") +
      ":" +
      String(s % 60).padStart(2, "0")
    );
  };
  const status = (a) =>
    a.state !== "finished"
      ? "active"
      : a.reason === "completed"
        ? "complete"
        : a.reason
          ? "error"
          : "unknown";
  const label = (a) =>
    a.state !== "finished"
      ? a.cancel_requested
        ? "Cancelling"
        : a.state === "intended"
          ? "Starting"
          : "Running"
      : a.reason === "completed"
        ? a.kind === "plan"
          ? "Plan finished"
          : "Completed"
        : {
            excluded: "Kernel excluded",
            "build-error": "With errors",
            timeout: "Timed out",
            "log-limit": "Log limit",
            "resource-interruption": "Resource limit",
          }[a.reason] ||
          a.reason ||
          "Unknown";
  let campaign = "",
    snapshot = null,
    following = true,
    anchor = "",
    pages = [""],
    selected = "",
    selectedInfo = null;
  let request = null,
    detailRequest = null,
    generation = 0,
    detailGeneration = 0,
    busy = false,
    scrollPage = false;
  $("history-zone").textContent = "UTC";

  function hold() {
    if (!following) return;
    request?.abort();
    ++generation;
    busy = false;
    following = false;
    anchor = snapshot?.anchor || "";
    followButton();
  }
  function followButton() {
    $("history-follow").setAttribute("aria-pressed", String(following));
    $("history-follow").textContent = following
      ? "● Live"
      : snapshot?.newer
        ? `↑ ${fmt(snapshot.newer)} new`
        : "↑ Latest";
  }
  function pageTop() {
    document.querySelector(".ledger-scroll").scrollTop = 0;
    if (
      !$("history").hidden &&
      matchMedia("(max-width:650px)").matches &&
      scrollY > document.querySelector(".ledger").offsetTop
    ) {
      window.scrollTo(
        0,
        document.querySelector(".ledger").getBoundingClientRect().top +
          scrollY -
          document.querySelector(".app-chrome").offsetHeight,
      );
    }
  }
  function reset() {
    pages = [""];
    anchor = "";
    following = true;
    $("history-rows").replaceChildren();
    pageTop();
    load(true);
  }
  function renderTimeline(o, now) {
    const span = Math.max(1, o.end - o.start);
    const left = (t) => 100 * Math.max(0, Math.min(1, (t - o.start) / span));
    $("history-span").textContent =
      `${date(o.start)}${date(o.start) !== date(o.end) ? " – " + date(o.end) : ""} / UTC`;
    $("history-summary").textContent =
      `${fmt((o.kinds.build || 0) + (o.kinds.plan || 0))} batches · ${elapsed(o.end - o.created)}`;
    const ticks = [];
    for (let i = 0; i <= 4; i++)
      ticks.push(el("span", time(o.start + (span * i) / 4)));
    $("timeline-axis").replaceChildren(...ticks);
    for (const kind of ["build", "plan"]) {
      const track = $("timeline-" + kind);
      const existing = new Map(
        [...track.children].map((n) => [n.dataset.key, n]),
      );
      const records = o.intervals
        .filter((a) => a.kind === kind)
        .sort((a, b) => a.created - b.created || a.id.localeCompare(b.id));
      const nodes = [],
        ends = [];
      for (const a of records) {
        let row = ends.findIndex((end) => end <= a.created);
        if (row < 0) row = ends.length;
        ends[row] = a.finished || now;
        const n = existing.get(a.id) || el("button", null, "timeline-interval");
        n.dataset.key = a.id;
        n.dataset.attempt = a.id;
        n.className = `timeline-interval ${a.outcome}${selected === a.id ? " selected" : ""}`;
        n.style.top = 2 + row * 18 + "px";
        n.style.left = left(a.created) + "%";
        const w = Math.max(0, left(a.finished || now) - left(a.created));
        n.style.width = `max(3px, ${w}%)`;
        n.textContent = w > 7 ? elapsed((a.finished || now) - a.created) : "";
        const description = `${kind} ${a.id.slice(0, 8)} · ${time(a.created)}–${a.finished ? time(a.finished) : "now"} UTC · ${elapsed((a.finished || now) - a.created)} · ${a.targets} requested · ${label(a)}`;
        n.title = description;
        n.setAttribute("aria-label", description);
        n.setAttribute("aria-pressed", String(selected === a.id));
        n.onmouseenter = n.onfocus = () => {
          $("timeline-readout").textContent = description;
        };
        n.onclick = () => selectAttempt(a.id);
        nodes.push(n);
      }
      track.style.height = 20 + Math.max(0, ends.length - 1) * 18 + "px";
      // At large scales show duration occupancy for every interval, not a recent sample.
      const buckets = new Map();
      for (const b of o.buckets.filter((b) => b.kind === kind)) {
        if (!buckets.has(b.n)) buckets.set(b.n, []);
        buckets.get(b.n).push(b);
      }
      for (const [i, group] of buckets) {
        const n = el("span", "", "timeline-bucket");
        const sum = group.reduce((v, b) => v + b.count, 0);
        const desc = `${kind} · ${time(o.start + (i * span) / o.bucket_count)} UTC · ${group.map((b) => `${b.count} ${b.outcome}`).join(", ")} attempts touching this interval`;
        n.style.left = (100 * i) / o.bucket_count + "%";
        n.style.width = 100 / o.bucket_count + "%";
        n.title = desc;
        n.tabIndex = 0;
        n.setAttribute("aria-label", desc);
        n.onmouseenter = n.onfocus = () => {
          $("timeline-readout").textContent = desc;
        };
        for (const b of group) {
          const part = el("span", null, b.outcome);
          part.style.height = (100 * b.count) / sum + "%";
          n.append(part);
        }
        nodes.push(n);
      }
      if (!nodes.length)
        nodes.push(el("span", "No attempts in this range", "timeline-empty"));
      // Keep buttons in place so keyboard focus survives live updates.
      for (const n of [...track.children]) if (!nodes.includes(n)) n.remove();
      nodes.forEach((n, i) => {
        if (track.children[i] !== n)
          track.insertBefore(n, track.children[i] || null);
      });
    }
    $("timeline").classList.toggle("aggregated", o.buckets.length > 0);
    if (o.buckets.length && !$("timeline-readout").matches(":hover"))
      $("timeline-readout").textContent =
        "Dense range: each column shows attempts touching that time interval. Use a shorter range for individual batches.";
  }
  function renderRows(d) {
    const body = $("history-rows");
    const old = new Map([...body.children].map((n) => [n.dataset.attempt, n]));
    const nodes = [];
    for (const a of d.rows) {
      let tr = old.get(a.id);
      if (!tr) {
        tr = el("tr");
        tr.dataset.attempt = a.id;
        tr.onclick = () => selectAttempt(a.id);
        for (let i = 0; i < 7; i++) tr.append(el("td"));
        const inspect = el("button", time(a.created), "history-inspect");
        inspect.setAttribute(
          "aria-label",
          `Inspect ${a.kind} attempt ${a.id.slice(0, 8)}`,
        );
        inspect.title = `${date(a.created)} ${time(a.created)} UTC`;
        tr.children[0].append(el("small", date(a.created)), inspect);
        tr.children[2].append(el("span", a.kind === "plan" ? "Plan" : "Build"));
        tr.children[2].title = a.id;
        const packages = el(
          "span",
          a.targets.map((t) => t.label).join(", "),
          "history-targets",
        );
        packages.title = a.targets.map((t) => t.label).join(", ");
        tr.children[3].append(
          el("b", fmt(a.targets.length), "target-count"),
          packages,
        );
        const logs = el("button", "↗", "history-log");
        logs.setAttribute(
          "aria-label",
          `Open log for ${a.kind} attempt ${a.id.slice(0, 8)}`,
        );
        logs.onclick = (event) => {
          event.stopPropagation();
          window.buildLogs.open(a.id);
        };
        tr.children[6].append(logs);
      }
      tr.classList.toggle("selected", selected === a.id);
      tr.children[0]
        .querySelector("button")
        .setAttribute("aria-pressed", String(selected === a.id));
      tr.children[1].textContent = elapsed((a.finished || d.now) - a.created);
      tr.children[4].textContent = a.checks ? fmt(a.checks) : "—";
      tr.children[4].title =
        "Derivations with recorded successful checks in this batch";
      tr.children[5].textContent = label(a);
      tr.children[5].className = "history-result " + status(a);
      nodes.push(tr);
    }
    for (const n of [...body.children]) if (!nodes.includes(n)) n.remove();
    nodes.forEach((n, i) => {
      if (body.children[i] !== n)
        body.insertBefore(n, body.children[i] || null);
    });
    $("history-empty").hidden = !!nodes.length;
    $("history-older").disabled = !d.more;
    $("history-newer").disabled = pages.length === 1;
    const first = (pages.length - 1) * 24;
    $("history-page").textContent =
      `${nodes.length ? first + 1 : 0}–${first + nodes.length} / ${fmt(d.total)} attempts${following ? "" : " · paused"}`;
    followButton();
  }
  function renderDetail(a) {
    selectedInfo = a;
    $("history-selection").textContent = a.id.slice(0, 8);
    const state = el("span", label(a), "history-result " + status(a));
    const top = el("div", null, "record-heading");
    const log = el("button", "Open log ↗");
    log.onclick = () => window.buildLogs.open(a.id);
    top.append(state, log);
    const facts = el("dl", null, "record-facts");
    const pairs = [
      ["Job", a.kind === "build" ? "Build batch" : "Recipe evaluation"],
      ["Started", `${date(a.created)} ${time(a.created)} UTC`],
      [
        "Finished",
        a.finished
          ? time(a.finished) + " UTC"
          : a.state === "finished"
            ? "Unknown"
            : "In progress",
      ],
      [
        "Elapsed",
        a.finished == null && a.state === "finished"
          ? "—"
          : elapsed((a.finished ?? Date.now() / 1000) - a.created),
      ],
      ["Build activity", `${fmt(a.builds)} derivations`],
      ["Successful checks", `${fmt(a.checks)} derivations`],
    ];
    for (const [key, value] of pairs)
      facts.append(el("dt", key), el("dd", value));
    const targets = el("div", null, "record-targets");
    for (const t of a.targets) {
      const n = el("button", t.label);
      n.title = "Inspect current package record";
      n.onclick = () =>
        t.id || t.aliases?.length
          ? window.showPackage(t.id || t.aliases[0].id)
          : window.showDerivation(t.drv);
      targets.append(n);
    }
    const nodes = [
      top,
      facts,
      el(
        "h3",
        `${fmt(a.targets.length)} requested ${a.kind === "plan" ? "inputs" : "derivations"}`,
      ),
      targets,
    ];
    if (a.error) nodes.push(el("p", a.error, "record-note error"));
    if (a.activities.length) {
      nodes.push(el("h3", "Builds"));
      const list = el("div", null, "record-activities");
      for (const b of a.activities) {
        const n = el("button");
        n.append(
          el("span", b.name.replace("-x86_64-unknown-linux-gnufilc0", "")),
          el(
            "small",
            b.checked
              ? "Checks passed"
              : a.state === "finished" || b.stopped
                ? window.lastPhase(b.phase)
                : window.phaseName(b.phase),
          ),
        );
        n.onclick = () => window.buildLogs.open(a.id, b.drv);
        list.append(n);
      }
      nodes.push(list);
      if (a.builds > a.activities.length)
        nodes.push(
          el(
            "p",
            `Showing the first ${a.activities.length} activities. See the log for the full batch.`,
            "record-note",
          ),
        );
    }
    $("history-detail").replaceChildren(...nodes);
  }
  async function selectAttempt(id, pin = true, fromRoute = false) {
    if (window.dashboardNavigation && !fromRoute)
      return window.dashboardNavigation.attempt(id);
    if (pin) hold();
    selected = id;
    selectedInfo = null;
    if (snapshot) {
      renderRows(snapshot);
      renderTimeline(snapshot.overview, snapshot.now);
    }
    $("history-detail").textContent = "Loading…";
    if (!$("history-record").open) $("history-record").showModal();
    await loadDetail();
  }
  async function loadDetail() {
    detailRequest?.abort();
    const controller = new AbortController();
    detailRequest = controller;
    const token = ++detailGeneration;
    const timer = setTimeout(() => controller.abort(), 10000);
    try {
      const response = await fetch(
        "/api/history/attempt?" +
          new URLSearchParams({ campaign, id: selected }),
        { signal: controller.signal },
      );
      if (!response.ok) throw Error("attempt unavailable");
      const info = await response.json();
      if (token === detailGeneration) renderDetail(info);
    } catch (e) {
      if (token === detailGeneration)
        $("history-detail").textContent =
          "Attempt record unavailable. Select it to retry.";
    } finally {
      clearTimeout(timer);
    }
  }
  async function load(force = false) {
    if (!campaign || (busy && !force)) return;
    request?.abort();
    const controller = new AbortController();
    request = controller;
    const token = ++generation;
    busy = true;
    const timer = setTimeout(() => controller.abort(), 10000);
    try {
      const q = new URLSearchParams({
        campaign,
        anchor: following ? "" : anchor,
        before: pages.at(-1),
        kind: $("history-kind").value,
        outcome: $("history-outcome").value,
        q: $("history-search").value,
        window: $("history-window").value,
      });
      const response = await fetch("/api/history?" + q, {
        signal: controller.signal,
      });
      if (!response.ok) throw Error("history unavailable");
      const d = await response.json();
      if (token !== generation) return;
      snapshot = d;
      if (!following && !anchor) anchor = d.anchor;
      renderTimeline(d.overview, d.now);
      renderRows(d);
      window.dispatchEvent(new Event("contentready"));
      if (scrollPage) {
        pageTop();
        scrollPage = false;
      }
      $("history-freshness").textContent = `Live · ${time(d.now)} UTC`;
      if (
        $("history-record").open &&
        selectedInfo &&
        selectedInfo.state !== "finished"
      )
        loadDetail();
    } catch (e) {
      if (token === generation)
        $("history-freshness").textContent = "Connection lost · retrying";
    } finally {
      clearTimeout(timer);
      if (token === generation) busy = false;
    }
  }
  document
    .querySelector(".ledger-scroll")
    .addEventListener("scroll", (event) => {
      if (following && event.currentTarget.scrollTop > 8) hold();
    });
  $("history-close").onclick = () =>
    window.dashboardNavigation.close("attempt");
  $("history-record").addEventListener("close", () => {
    if ($("history-record").open) return;
    detailRequest?.abort();
    ++detailGeneration;
  });
  window.addEventListener(
    "scroll",
    () => {
      if (
        following &&
        !$("history").hidden &&
        matchMedia("(max-width: 650px)").matches &&
        document.querySelector(".ledger-scroll")?.getBoundingClientRect().top <
          -50
      )
        hold();
    },
    { passive: true },
  );
  $("history-follow").onclick = () => (following ? hold() : reset());
  $("history-older").onclick = () => {
    if (!snapshot?.more) return;
    hold();
    pages.push(snapshot.rows.at(-1).id);
    scrollPage = true;
    load(true);
  };
  $("history-newer").onclick = () => {
    if (pages.length > 1) {
      pages.pop();
      scrollPage = true;
      load(true);
    }
  };
  $("history-kind").onchange = $("history-outcome").onchange = reset;
  $("history-window").onchange = () => load(true);
  let debounce;
  $("history-search").oninput = () => {
    clearTimeout(debounce);
    debounce = setTimeout(reset, 200);
  };
  window.attemptHistory = {
    open: (id) => selectAttempt(id, true, true),
    updateCampaign(id) {
      if (campaign === id) return;
      campaign = id;
      $("history-record").close();
      selected = "";
      selectedInfo = null;
      snapshot = null;
      detailRequest?.abort();
      ++detailGeneration;
      $("history-selection").textContent = "";
      $("history-detail").textContent = "Select a batch to inspect its record.";
      $("history-search").value =
        $("history-kind").value =
        $("history-outcome").value =
          "";
      reset();
    },
  };
  const initial = JSON.parse($("initial").textContent);
  if (initial.campaign)
    window.attemptHistory.updateCampaign(initial.campaign.id);
  setInterval(() => load(), 5000);
})();
