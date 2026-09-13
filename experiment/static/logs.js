(() => {
  const $ = (id) => document.getElementById(id);
  const node = (tag, text, cls = "") => {
    const n = document.createElement(tag);
    n.textContent = text;
    n.className = cls;
    return n;
  };
  const name = (drv) =>
    drv
      ? drv
          .split("/")
          .pop()
          .slice(33, -4)
          .replace("-x86_64-unknown-linux-gnufilc0", "")
      : "nix";
  const bytes = (n) =>
    n > 1024 ** 2
      ? (n / 1024 ** 2).toFixed(1) + " MiB"
      : Math.ceil(n / 1024) + " KiB";
  const dialog = $("log-view"),
    scroll = $("log-scroll"),
    lines = $("log-lines");
  let id = null,
    drv = "",
    snapshot = null,
    watch = false,
    following = true;
  let entries = [],
    start = 0,
    end = 0,
    info = null,
    epoch = 0,
    busy = false;
  let timer,
    controller,
    suppressScroll = 0,
    disconnected = false,
    matchIndex = -1;
  let campaignId = null,
    seeking = false;
  let sourceSignature = "",
    attemptSignature = "",
    skipped = false;

  function stop() {
    epoch++;
    clearTimeout(timer);
    controller?.abort();
    busy = false;
  }
  function bottom() {
    suppressScroll = performance.now() + 250;
    requestAnimationFrame(() => {
      scroll.scrollTop = scroll.scrollHeight;
    });
  }
  function follow(value) {
    following = value;
    $("log-follow").setAttribute("aria-pressed", String(value));
    status();
  }
  function status() {
    const a = info?.attempt;
    const lag = info ? Math.max(0, info.size - end) : 0;
    $("log-follow").textContent = following
      ? "● Following output"
      : lag
        ? `↓ ${bytes(lag)} new · Jump to live`
        : "↓ Jump to live";
    $("log-watch").setAttribute("aria-pressed", String(watch));
    $("log-watch").textContent = watch
      ? "● Following batches"
      : "Follow batches";
    $("log-status").textContent = disconnected
      ? "Connection lost · retrying…"
      : busy
        ? "Reading output…"
        : !following
          ? "Paused scrolling · your place is saved"
          : info?.finished
            ? `Attempt ended · ${a.result?.reason || a.state}`
            : lag
              ? "Catching up…"
              : "Live · waiting for output";
    $("log-status").classList.toggle("disconnected", disconnected);
    $("log-range").textContent = info
      ? `${entries.length.toLocaleString()} records loaded · ${bytes(info.captured)} captured${skipped ? " · oversized record omitted; available in raw log" : ""}`
      : "Opening log…";
    $("log-earlier").disabled = busy || start === 0;
    $("log-earlier").textContent =
      start > 0 ? "↑ Load earlier output" : "Beginning of captured output";
    $("log-empty").hidden = entries.length !== 0;
    $("log-empty").textContent = busy
      ? "Looking for captured output…"
      : disconnected
        ? "Could not reach the log server. Reconnecting automatically…"
        : drv
          ? "No output from this build in this window. Load earlier output or choose All builds."
          : "No build output in this window. Nix may be preparing inputs.";
    if (a) {
      const when = new Date(a.created * 1000).toLocaleTimeString();
      $("log-title").textContent = drv ? name(drv) : "All builds in this batch";
      $("log-subtitle").textContent =
        `${a.kind === "plan" ? "Planning" : "Build batch"} ${id.slice(0, 8)} · started ${when}`;
      $("log-evidence").textContent = info.finished
        ? `Attempt result: ${a.result?.reason || a.state}${a.result?.exit_code != null ? " · exit " + a.result.exit_code : ""}`
        : "Build activity ending is not proof of success.";
    }
  }
  function attemptOptions() {
    const attempts = [...(snapshot?.attempts || [])];
    if (id && !attempts.some((a) => a.id === id))
      attempts.unshift(info?.attempt || { id, kind: "build", created: 0 });
    const signature = JSON.stringify(attempts.map((a) => [a.id, a.state]));
    if (signature === attemptSignature) return;
    attemptSignature = signature;
    $("log-attempt").replaceChildren(
      ...attempts.map((a) => {
        const option = node(
          "option",
          `${a.kind} · ${a.id.slice(0, 8)} · ${a.state || "recorded"}`,
        );
        option.value = a.id;
        return option;
      }),
    );
    $("log-attempt").value = id;
  }
  function sourceOptions() {
    const nav = $("log-sources");
    const selectedBefore = nav.querySelector(".selected")?.title;
    const oldTop = nav.scrollTop,
      oldLeft = nav.scrollLeft;
    const sources = [
      ...new Map((info?.sources || []).map((a) => [a.drv, a])).values(),
    ];
    sources.sort(
      (a, b) => a.stopped - b.stopped || name(a.drv).localeCompare(name(b.drv)),
    );
    if (drv && !sources.some((a) => a.drv === drv))
      sources.unshift({ drv, phase: "No activity recorded", stopped: true });
    const signature = JSON.stringify([drv, sources]);
    if (signature === sourceSignature) return;
    sourceSignature = signature;
    const all = node(
      "button",
      `All builds (${sources.length})`,
      "log-source" + (!drv ? " selected" : ""),
    );
    all.onclick = () => open(id, "", watch);
    all.setAttribute("aria-pressed", String(!drv));
    nav.replaceChildren(
      all,
      ...sources.map((a) => {
        const b = node(
          "button",
          "",
          "log-source" + (drv === a.drv ? " selected" : ""),
        );
        b.title = a.drv;
        b.setAttribute("aria-pressed", String(drv === a.drv));
        b.append(
          node("span", name(a.drv)),
          node(
            "small",
            `${!a.stopped && !info.finished ? "● " : ""}${a.phase || "starting"}${a.stopped ? " · output ended" : ""}`,
          ),
        );
        b.onclick = () => open(id, a.drv, watch);
        return b;
      }),
    );
    nav.scrollTop = oldTop;
    nav.scrollLeft = oldLeft;
    if (drv && selectedBefore !== drv)
      nav
        .querySelector(".selected")
        ?.scrollIntoView({ block: "nearest", inline: "nearest" });
  }
  function renderEntries() {
    const q = $("log-search").value.toLowerCase();
    const fragment = document.createDocumentFragment();
    for (const e of entries) {
      const row = node("div", "", "log-row " + e.kind);
      row.dataset.offset = e.offset;
      const label = node("button", name(e.drv), "log-owner");
      label.title = e.drv || "Nix / evaluator output";
      label.disabled = !e.drv;
      label.onclick = () => open(id, e.drv, watch);
      const text = node("span", "", "log-text");
      if (q) {
        let from = 0,
          at;
        const lower = e.text.toLowerCase();
        while ((at = lower.indexOf(q, from)) >= 0) {
          text.append(
            document.createTextNode(e.text.slice(from, at)),
            node("mark", e.text.slice(at, at + q.length)),
          );
          from = at + q.length;
          if (text.childNodes.length > 200) break;
        }
        text.append(document.createTextNode(e.text.slice(from)));
      } else text.textContent = e.text;
      row.append(label, text);
      fragment.append(row);
    }
    suppressScroll = performance.now() + 250;
    lines.replaceChildren(fragment);
    const count = lines.querySelectorAll("mark").length;
    $("log-matches").textContent = q ? `${count} matches` : "";
    $("log-prev-match").disabled = $("log-next-match").disabled = count === 0;
    matchIndex = -1;
    if (following) bottom();
  }
  function merge(incoming, prepend) {
    const seen = new Set(entries.map((e) => e.offset));
    const fresh = incoming.filter((e) => !seen.has(e.offset));
    if (!fresh.length) return;
    entries = prepend ? [...fresh, ...entries] : [...entries, ...fresh];
    let chars = entries.reduce((n, e) => n + e.text.length, 0);
    while (entries.length > 2000 || (chars > 1024 ** 2 && entries.length > 1)) {
      const removed = prepend ? entries.pop() : entries.shift();
      chars -= removed.text.length;
      if (prepend) end = Math.min(end, removed.offset);
      else start = entries[0].offset;
    }
    const top = scroll.getBoundingClientRect().top;
    const anchor = prepend
      ? [...lines.children].find((n) => n.getBoundingClientRect().bottom > top)
      : null;
    const anchorOffset = anchor?.dataset.offset,
      anchorY = anchor?.getBoundingClientRect().top;
    renderEntries();
    if (anchor) {
      const next = [...lines.children].find(
        (n) => n.dataset.offset === anchorOffset,
      );
      if (next) scroll.scrollTop += next.getBoundingClientRect().top - anchorY;
    }
  }
  async function read(direction = following ? "after" : "status") {
    if (busy || !id || !dialog.open) return;
    busy = true;
    status();
    const g = epoch;
    controller = new AbortController();
    const requestController = controller;
    const timeout = setTimeout(() => requestController.abort(), 12000);
    try {
      // Empty filtered windows are traversed promptly, with a bounded amount of work.
      for (let pages = 0; pages < 8; pages++) {
        const q = new URLSearchParams({
          attempt: id,
          drv,
          direction,
          cursor: direction === "before" ? start : end,
        });
        const response = await fetch("/api/build-log?" + q, {
          signal: controller.signal,
        });
        if (!response.ok) throw new Error("log unavailable");
        const r = await response.json();
        if (g !== epoch) return;
        disconnected = false;
        info = r;
        skipped ||= r.skipped;
        if (r.reset && direction !== "tail") {
          open(id, drv, watch);
          return;
        }
        if (direction === "after" && !following) {
          sourceOptions();
          break;
        }
        if (direction === "tail") {
          start = r.start;
          end = r.end;
        } else if (direction === "before") start = r.start;
        else if (direction === "after") end = r.end;
        if (direction !== "status") merge(r.entries, direction === "before");
        sourceOptions();
        attemptOptions();
        if (
          (direction === "tail" || direction === "before") &&
          r.before &&
          ((seeking && entries.length < (drv ? 100 : 1)) || !r.entries.length)
        )
          direction = "before";
        else if (
          direction === "after" &&
          r.more &&
          r.end > Number(q.get("cursor"))
        )
          continue;
        else break;
      }
    } catch (e) {
      if (g === epoch) disconnected = true;
    } finally {
      clearTimeout(timeout);
      if (g === epoch) {
        busy = false;
        status();
        clearTimeout(timer);
        if (entries.length >= (drv ? 100 : 1) || start === 0) seeking = false;
        timer = setTimeout(
          () => read(seeking && following ? "before" : undefined),
          (seeking && following) || (following && info?.more && !info?.finished)
            ? 100
            : 1200,
        );
      }
    }
  }
  function open(attempt, selected = "", continuous = false) {
    if (!attempt) return;
    stop();
    id = attempt;
    drv = selected;
    watch = continuous;
    entries = [];
    seeking = true;
    start = end = 0;
    info = null;
    skipped = disconnected = false;
    sourceSignature = attemptSignature = "";
    $("log-sources").replaceChildren(
      node("p", "Reading builds…", "log-source"),
    );
    scroll.classList.toggle("scoped", Boolean(drv));
    $("log-search").value = "";
    $("log-title").textContent = selected
      ? name(selected)
      : "All builds in this batch";
    $("log-subtitle").textContent = attempt;
    $("log-download").href = "/api/log/download?attempt=" + id;
    follow(true);
    renderEntries();
    attemptOptions();
    if (!dialog.open) dialog.showModal();
    read("tail");
  }
  function newest() {
    return snapshot?.attempts.find((a) => a.kind === "build");
  }
  window.buildLogs = {
    open,
    update(d) {
      const changed = campaignId && campaignId !== d.campaign?.id;
      campaignId = d.campaign?.id;
      snapshot = d;
      $("watch-builds").disabled = !newest();
      if (changed && dialog.open) {
        dialog.close();
        return;
      }
      if (!dialog.open) return;
      attemptOptions();
      const next = newest();
      if (
        watch &&
        following &&
        !busy &&
        info?.finished &&
        end >= info.size &&
        !seeking &&
        next &&
        next.id !== id
      )
        open(next.id, "", true);
    },
  };
  $("watch-builds").onclick = () => open(newest()?.id, "", true);
  $("log-close").onclick = () => dialog.close();
  dialog.addEventListener("close", () => {
    // A queued close event can arrive after the viewer has already reopened.
    if (dialog.open) return;
    stop();
    id = null;
  });
  $("log-attempt").onchange = () => open($("log-attempt").value);
  $("log-watch").onclick = () => {
    watch = !watch;
    if (watch && newest()) open(newest().id, "", true);
    else status();
  };
  $("log-follow").onclick = () => {
    if (following) follow(false);
    else open(id, drv, watch);
  };
  $("log-earlier").onclick = () => {
    follow(false);
    read("before");
  };
  scroll.addEventListener("scroll", () => {
    if (
      following &&
      performance.now() > suppressScroll &&
      scroll.scrollHeight - scroll.clientHeight - scroll.scrollTop > 70
    )
      follow(false);
  });
  // Pause before the browser moves the viewport, even when new output is arriving.
  scroll.addEventListener(
    "wheel",
    (e) => {
      if (e.deltaY < 0) follow(false);
    },
    { passive: true },
  );
  scroll.addEventListener("touchstart", () => follow(false), { passive: true });
  scroll.addEventListener("keydown", (e) => {
    if (["PageUp", "Home", "ArrowUp"].includes(e.key)) follow(false);
  });
  $("log-wrap").onchange = () => {
    scroll.classList.toggle("wrapped", $("log-wrap").checked);
    if (following) bottom();
  };
  $("log-search").oninput = () => {
    follow(false);
    renderEntries();
  };
  function match(step) {
    const marks = [...lines.querySelectorAll("mark")];
    if (!marks.length) return;
    matchIndex = (matchIndex + step + marks.length) % marks.length;
    marks.forEach((m, i) => m.classList.toggle("current", i === matchIndex));
    marks[matchIndex].scrollIntoView({ block: "center", inline: "nearest" });
    $("log-matches").textContent = `${matchIndex + 1} / ${marks.length}`;
  }
  $("log-next-match").onclick = () => match(1);
  $("log-prev-match").onclick = () => match(-1);
  $("log-search").onkeydown = (e) => {
    if (e.key === "Enter") {
      e.preventDefault();
      match(e.shiftKey ? -1 : 1);
    }
  };
  window.addEventListener("resize", () => {
    if (dialog.open && drv)
      requestAnimationFrame(() => {
        $("log-sources")
          .querySelector(".selected")
          ?.scrollIntoView({ block: "nearest", inline: "nearest" });
      });
  });
})();
