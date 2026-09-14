/* Reading behavior only. Every content node arrives as server-rendered HTML. */
(() => {
  const bound = new WeakSet(), navigations = new WeakSet();
  let anchor = null, adjusting = false;
  const failedReaders = new Set();
  const busy = (reader) => !!reader?.querySelector('#log-tools details[open], #log-tools form[data-editing], #log-tools form:focus-within');
  const readerKey = (ctx) => ctx?.sourceElement?.id || ctx?.target?.id || "workspace";
  function connectionStatus() {
    const status = document.querySelector("#connection-status");
    if (status) status.hidden = failedReaders.size === 0;
  }
  function loadFailed(event) {
    const ctx = event.detail.ctx;
    if (event.detail.error?.name === "AbortError" || (ctx && !ctx.sourceElement?.isConnected)) return;
    failedReaders.add(readerKey(ctx));
    connectionStatus();
  }
  document.addEventListener("htmx:error", loadFailed);
  document.addEventListener("htmx:response:error", loadFailed);
  document.addEventListener("htmx:after:request", (event) => {
    const ctx = event.detail.ctx;
    if (ctx?.response?.status < 400) failedReaders.delete(readerKey(ctx));
    connectionStatus();
  });
  document.addEventListener("input", (event) => {
    const form = event.target.closest?.("#log-tools form");
    if (form) form.dataset.editing = "1";
  });
  document.addEventListener("htmx:before:morph:attr", (event) => {
    // Open diagnostic sections belong to the reader, not to refreshed data.
    if (event.target.tagName === "DETAILS" && event.detail.attrName === "open") event.preventDefault();
  });
  document.addEventListener("htmx:before:swap", (event) => {
    const ctx = event.detail.ctx, source = ctx?.sourceElement;
    const reader = source?.closest("#log-reader");
    if (busy(reader) && (source?.id === "log-tools" || (source?.id === "log-cursor" && ctx.target === reader))) event.preventDefault();
  });

  function pauseAt(scroll, reader) {
    const toggle = reader.querySelector("#log-toggle");
    if (!toggle || reader.dataset.pausing) return;
    const top = scroll.getBoundingClientRect().top;
    const row = [...scroll.querySelectorAll("[data-offset]")].find(
      (node) => node.getBoundingClientRect().bottom > top,
    );
    if (!row) return;
    anchor = { offset: row.dataset.offset, delta: row.getBoundingClientRect().top - top };
    const url = new URL(toggle.href);
    url.searchParams.set("follow", "0");
    url.searchParams.set("direction", "after");
    url.searchParams.set("cursor", row.dataset.offset);
    toggle.href = url.href;
    toggle.setAttribute("hx-get", url.href);
    reader.dataset.pausing = "1";
    reader.dataset.follow = "0";
    reader.querySelector("#log-cursor")?.dispatchEvent(new Event("htmx:abort"));
    // A click handler cannot synchronously click the same anchor again.
    queueMicrotask(() => toggle.click());
  }

  function settle() {
    const reader = document.querySelector("#log-reader");
    const scroll = reader?.querySelector("#log-scroll");
    if (!scroll) return;
    if (!bound.has(scroll)) {
      bound.add(scroll);
      scroll.addEventListener("scroll", () => {
        if (!adjusting && reader.dataset.follow === "1" &&
            scroll.scrollHeight - scroll.scrollTop - scroll.clientHeight > 60)
          pauseAt(scroll, reader);
      }, { passive: true });
    }
    adjusting = true;
    if (anchor && !reader.dataset.pausing) {
      const row = scroll.querySelector(`[data-offset="${CSS.escape(anchor.offset)}"]`);
      if (row) scroll.scrollTop += row.getBoundingClientRect().top - scroll.getBoundingClientRect().top - anchor.delta;
      anchor = null;
    } else if (reader.dataset.follow === "1") {
      scroll.scrollTop = scroll.scrollHeight;
    }
    requestAnimationFrame(() => { adjusting = false; });
  }

  document.addEventListener("click", (event) => {
    const toggle = event.target.closest?.("#log-toggle");
    const reader = toggle?.closest("#log-reader");
    if (reader?.dataset.follow === "1" && !reader.dataset.pausing &&
        !event.metaKey && !event.ctrlKey && !event.shiftKey && !event.altKey) {
      event.preventDefault();
      event.stopImmediatePropagation();
      pauseAt(reader.querySelector("#log-scroll"), reader);
    }
  }, true);

  document.addEventListener("htmx:before:request", (event) => {
    const ctx = event.detail.ctx, source = ctx?.sourceElement;
    if (source?.getAttribute("hx-push-url") === "true") navigations.add(ctx);
    if ((source?.id === "log-tools" || source?.id === "log-cursor") && busy(source.closest("#log-reader"))) event.preventDefault();
    if (source?.id === "log-cursor" && source.closest("#log-reader")?.dataset.pausing)
      event.preventDefault();
  });
  document.addEventListener("htmx:after:swap", (event) => {
    if (event.detail.ctx && navigations.has(event.detail.ctx)) {
      window.scrollTo(0, 0);
      failedReaders.clear();
      connectionStatus();
    }
    requestAnimationFrame(settle);
  });
  document.addEventListener("htmx:after:settle", () => requestAnimationFrame(settle));
  document.addEventListener("DOMContentLoaded", () => {
    // Preserve bookmarked view fragments from the former single-page viewer.
    const oldViews = { "#inventory": "/packages", "#batch-timings": "/batches", "#dependency-map": "/dependencies" };
    const suffix = oldViews[location.hash];
    if (suffix && /^\/campaigns\/[^/]+$/.test(location.pathname)) {
      const url = new URL(location.href); url.pathname += suffix; url.hash = "";
      location.replace(url); return;
    }
    requestAnimationFrame(settle);
  });
})();
