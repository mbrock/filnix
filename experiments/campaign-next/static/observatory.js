/* HTMX owns index/inspector/graph HTML. The console owns its bounded log window. */
document.addEventListener('DOMContentLoaded', () => {
  const byId = id => document.getElementById(id);
  const params = new URL(location.href).searchParams;
  document.addEventListener('htmx:before:request', e => {
    if (document.hidden) e.preventDefault();
  });
  if (byId('overview-summary')) {
    function railState() {
      byId('rail-after').value = '0';
      byId('session-results').scrollTop = 0;
      const u = new URL(location.href);
      u.searchParams.set('filter', byId('session-filter').value);
      u.searchParams.set('find', byId('session-find').value);
      history.replaceState(null, '', u);
    }
    byId('session-filter').value = params.get('filter') || 'all';
    byId('session-find').value = params.get('find') || '';
    if (params.has('filter') || params.has('find')) htmx.trigger(byId('rail-controls'), 'change');
    byId('rail-controls').addEventListener('change', railState);
    byId('session-filter').addEventListener('input', railState);
    byId('session-find').addEventListener('input', () => { railState(); htmx.trigger(byId('rail-controls'), 'change'); });
    document.addEventListener('click', e => {
      const filter = e.target.closest('[data-filter]');
      if (filter) { byId('session-filter').value = filter.dataset.filter; railState(); htmx.trigger(byId('rail-controls'), 'change'); }
    });
    document.addEventListener('htmx:before:request', e => {
      const action = new URL(e.detail.ctx.request.action, location.href);
      if (action.pathname.endsWith('/sessions') && e.detail.ctx.sourceElement.matches('button')) {
        byId('rail-after').value = action.searchParams.get('after') || '0';
        byId('session-results').scrollTop = 0;
      }
    });
    document.addEventListener('htmx:before:swap', e => {
      const action = new URL(e.detail.ctx.request.action, location.href);
      if (action.pathname.endsWith('/sessions')) {
        const q = action.searchParams;
        if (q.get('after') !== byId('rail-after').value ||
            q.get('filter') !== byId('session-filter').value ||
            q.get('find') !== byId('session-find').value) e.preventDefault();
      }
    });
    document.addEventListener('htmx:after:swap', e => {
      const action = new URL(e.detail.ctx.request.action, location.href);
      if (action.pathname.endsWith('/sessions')) byId('rail-after').value = document.querySelector('.rail-count').dataset.after;
      const summary = byId('overview-summary');
      const form = byId('rail-controls');
      if (summary?.dataset.watch === '0' && form.getAttribute('hx-trigger').includes('every')) {
        form.setAttribute('hx-trigger', 'change, submit');
        htmx.process(form, true);
        htmx.trigger(form, 'change'); // One final settled list, then no idle polling.
      }
    });
    // The overview has no selected session, graph, console or log polling.
    return;
  }
  const back = new URL('./', location.href);
  for (const key of ['filter', 'find']) if (params.has(key)) back.searchParams.set(key, params.get(key));
  byId('sessions-back').href = back;
  const initialRun = byId('state').dataset.run;
  const cursor = byId('log-cursor');
  const rows = byId('log-rows');
  // The console is part of the page; the document is its scroller.
  const page = document.scrollingElement;
  const atBottom = () => page.scrollHeight - page.scrollTop - innerHeight <= 40;
  const toBottom = () => { page.scrollTop = page.scrollHeight; };
  let following = byId('state').dataset.live === '1', pending = null, epoch = 0;
  let timer, wasLive = following;
  const searched = new WeakMap();
  let stateView;
  const message = value => { byId('console-state').textContent = value; };
  function saveStateView() {
    const selected = byId('selected-node');
    return {
      scroll: ['#state', '#graph-scroll'].map(selector => {
        const element = document.querySelector(selector);
        return {selector, top: element?.scrollTop || 0, left: element?.scrollLeft || 0, focused: element === document.activeElement};
      }),
      disclosures: ['.native-result', '.output-paths', '.reported-errors', '[data-static]'].map(selector => ({selector, open: document.querySelector(selector)?.open || false})),
      selected: selected ? {text: selected.textContent, hidden: selected.hidden} : null
    };
  }
  function restoreStateView(view) {
    for (const saved of view.disclosures) {
      const element = document.querySelector(saved.selector);
      if (element) element.open = saved.open;
    }
    if (view.selected && byId('selected-node')) {
      byId('selected-node').textContent = view.selected.text;
      byId('selected-node').hidden = view.selected.hidden;
    }
    for (const saved of view.scroll) {
      const element = document.querySelector(saved.selector);
      if (!element) continue;
      if (saved.focused) element.focus({preventScroll: true});
      element.scrollTop = saved.top;
      element.scrollLeft = saved.left;
    }
  }
  const pin = () => {
    const u = new URL(location.href);
    u.searchParams.set('run', initialRun);
    u.searchParams.delete('follow');
    history.replaceState(null, '', u);
    byId('state').setAttribute('hx-get', './state?' + new URLSearchParams({run: initialRun, activity: cursor.dataset.activity}));
  };
  function setFollow(value) {
    following = value;
    byId('log-follow').textContent = value ? 'Pause' : 'Follow';
    if (!value) { epoch++; pending?.abort(); pin(); }
    schedule();
  }
  function find() {
    const term = byId('log-find').value;
    const pattern = term ? new RegExp(term.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'giu') : null;
    let matches = 0;
    const lines = rows.querySelectorAll('.log-row');
    for (const row of lines) {
      const pre = row.querySelector('pre');
      const saved = searched.get(row);
      if (saved?.term === term) { matches += saved.matches; continue; }
      // Remove only our highlights. Keep the server's SGR spans and styles.
      if (saved?.term) {
        for (const mark of pre.querySelectorAll('mark')) mark.replaceWith(document.createTextNode(mark.textContent));
        pre.normalize();
      }
      const ranges = pattern ? [...pre.textContent.matchAll(pattern)].map(m => [m.index, m.index + m[0].length]) : [];
      if (ranges.length) {
        const walker = document.createTreeWalker(pre, NodeFilter.SHOW_TEXT);
        const nodes = [];
        while (walker.nextNode()) nodes.push(walker.currentNode);
        let offset = 0;
        for (const node of nodes) {
          const text = node.nodeValue, end = offset + text.length;
          const fragment = document.createDocumentFragment();
          let pos = 0, changed = false;
          for (const [start, stop] of ranges) {
            if (start >= end || stop <= offset) continue;
            const from = Math.max(start - offset, 0), to = Math.min(stop - offset, text.length);
            fragment.append(document.createTextNode(text.slice(pos, from)));
            const mark = document.createElement('mark');
            mark.textContent = text.slice(from, to); fragment.append(mark);
            pos = to; changed = true;
          }
          if (changed) { fragment.append(document.createTextNode(text.slice(pos))); node.replaceWith(fragment); }
          offset = end;
        }
      }
      row.hidden = !!term && !ranges.length;
      searched.set(row, {term, matches: ranges.length});
      matches += ranges.length;
    }
    byId('find-count').textContent = (term ? matches + ' matches · ' : '') + lines.length + ' loaded';
  }
  // Show a row's source only where it changes from the row above.
  function sources() {
    let previous = null;
    for (const row of rows.querySelectorAll('.log-row')) {
      row.classList.toggle('same', row.dataset.source === previous);
      previous = row.dataset.source;
    }
  }
  function earlierState(doc) {
    const marker = doc.getElementById('log-earlier'), button = byId('log-earlier');
    if (!marker) return;
    button.dataset.first = marker.dataset.first;
    button.hidden = marker.hidden;
  }
  async function loadEarlier() {
    const button = byId('log-earlier');
    if (pending || button.hidden) return;
    pending = new AbortController();
    const generation = epoch;
    button.disabled = true;
    try {
      const q = new URLSearchParams({run: initialRun, activity: cursor.dataset.activity, before: button.dataset.first});
      const response = await fetch('./logs?' + q, {signal: pending.signal});
      if (!response.ok) throw new Error('HTTP ' + response.status);
      const doc = new DOMParser().parseFromString(await response.text(), 'text/html');
      if (generation !== epoch) return;
      const fragment = document.createDocumentFragment();
      for (const row of doc.querySelectorAll('.log-row')) fragment.append(row);
      // Keep the reader's place: the row that was first stays where it was.
      const anchor = rows.querySelector('.log-row'), top = anchor?.getBoundingClientRect().top;
      rows.prepend(fragment);
      earlierState(doc);
      sources(); find(); message('');
      if (anchor) page.scrollTop += anchor.getBoundingClientRect().top - top;
    } catch (e) { if (e.name !== 'AbortError') message('Output unavailable · ' + e.message); }
    finally { pending = null; button.disabled = false; }
  }
  async function load({tail = false, after = cursor.dataset.after, activity = cursor.dataset.activity, replace = false} = {}) {
    if (pending) return;
    const generation = epoch;
    pending = new AbortController();
    const q = new URLSearchParams({run: initialRun, activity, after});
    if (tail) q.set('tail', '1');
    try {
      const response = await fetch('./logs?' + q, {signal: pending.signal});
      if (!response.ok) throw new Error('HTTP ' + response.status);
      const doc = new DOMParser().parseFromString(await response.text(), 'text/html');
      if (generation !== epoch) return;
      const stick = following && atBottom();
      if (replace) { rows.replaceChildren(); earlierState(doc); }
      const added = doc.querySelectorAll('.log-row');
      const fragment = document.createDocumentFragment();
      for (const row of added) fragment.append(row);
      rows.append(fragment);
      const next = doc.getElementById('log-cursor');
      cursor.dataset.after = next.dataset.after;
      cursor.dataset.activity = activity;
      if (added.length) rows.querySelector('.log-empty')?.remove();
      // A long live follow keeps a bounded window; earlier output stays loadable.
      if (rows.children.length > 20000) {
        while (rows.children.length > 20000) rows.firstElementChild.remove();
        byId('log-earlier').dataset.first = rows.firstElementChild.dataset.seq;
        byId('log-earlier').hidden = false;
      }
      if (!rows.children.length) { const p = document.createElement('p'); p.className = 'log-empty'; p.textContent = 'No captured output'; rows.append(p); }
      sources(); find();
      if (stick || tail) toBottom();
      message('');
    } catch (e) { if (e.name !== 'AbortError') message('Output unavailable · ' + e.message); }
    finally { pending = null; }
  }
  async function jumpPhase(seq, activity) {
    setFollow(false);
    const command = epoch;
    // Wait for the aborted poll to settle before replacing its cursor/window.
    while (pending) await new Promise(resolve => setTimeout(resolve, 10));
    if (command !== epoch) return;
    const u = new URL(location.href); u.searchParams.set('activity', activity); history.replaceState(null, '', u);
    await load({after: String(BigInt(seq)-1n), activity, replace: true});
    rows.firstElementChild?.scrollIntoView({block: 'start'});
  }
  async function end() {
    const command = ++epoch;
    pending?.abort();
    while (pending) await new Promise(resolve => setTimeout(resolve,10));
    if (command === epoch) await load({tail:true,replace:true});
  }
  async function selectNode() {
    const hash = location.hash.slice(1);
    if (!hash.startsWith('drv-')) return;
    let node = byId(hash);
    if (!node) {
      const details = document.querySelector('[data-static]');
      if (!details || !/^drv-(?:[0-9a-f]{2})+$/.test(hash)) return;
      details.open = true;
      const bytes = hash.slice(4).match(/../g).map(x => parseInt(x,16));
      const drv = new TextDecoder().decode(new Uint8Array(bytes));
      const response = await fetch('./graph?' + new URLSearchParams({run: initialRun,node: drv}));
      if (!response.ok) { message('Graph unavailable · HTTP ' + response.status); return; }
      byId('static-rows').innerHTML = await response.text();
      htmx.process(byId('static-rows'));
      node = byId(hash);
    }
    if (node) {
      byId('selected-node').textContent = 'Selected · ' + node.dataset.name;
      byId('selected-node').hidden = node.classList.contains('root-anchor');
      node.scrollIntoView({block: 'center'});
      const name = node.querySelector('.node-name'), graph = byId('graph-scroll');
      if (name) graph.scrollLeft += name.getBoundingClientRect().left - graph.getBoundingClientRect().left;
    }
  }
  byId('log-find').addEventListener('input', () => { setFollow(false); find(); });
  byId('log-follow').addEventListener('click', () => { if (following) setFollow(false); else { setFollow(true); end(); } });
  byId('log-earlier').addEventListener('click', loadEarlier);
  byId('log-end').addEventListener('click', end);
  byId('log-wrap').addEventListener('change', e => {
    byId('log-scroll').closest('.log-panel').classList.toggle('nowrap', !e.target.checked);
  });
  document.addEventListener('click', async e => {
    const phase = e.target.closest('[data-phase-seq]');
    if (phase) jumpPhase(phase.dataset.phaseSeq,phase.dataset.phaseActivity);
    const copy = e.target.closest('[data-copy]');
    if (copy) { try { await navigator.clipboard.writeText(copy.dataset.copy); message('Copied'); } catch { message('Copy unavailable'); } }
  });
  document.addEventListener('htmx:before:swap', e => {
    const action = new URL(e.detail.ctx.request.action, location.href);
    if (!action.pathname.endsWith('/state')) return;
    const pinned = new URL(location.href).searchParams.get('run');
    if (pinned && action.searchParams.get('run') !== pinned) { e.preventDefault(); return; }
    stateView = saveStateView();
  });
  document.addEventListener('htmx:after:swap', e => {
    if (!new URL(location.href).searchParams.has('run') && byId('state').dataset.run !== initialRun) { location.reload(); return; }
    const action = new URL(e.detail.ctx.request.action, location.href);
    if (action.pathname.endsWith('/state')) restoreStateView(stateView);
    const graph = byId('graph-scroll');
    if (graph) {
      const summary = document.querySelector('[data-static] summary');
      if (summary) summary.textContent = graph.dataset.staticCount + ' static inputs';
    }
    if (!action.pathname.endsWith('/state')) return;
    byId('log-mode').textContent = byId('state').dataset.live === '1' ? 'Live' : 'Captured';
    const live = byId('state').dataset.live === '1';
    if (following && wasLive && !live) load(); // Drain the final committed tail.
    wasLive = live;
    schedule();
  });
  window.addEventListener('hashchange', selectNode);
  function schedule() {
    clearTimeout(timer);
    if (following && !document.hidden && byId('state').dataset.live === '1')
      timer = setTimeout(async () => { await load(); schedule(); }, 1000);
  }
  document.addEventListener('visibilitychange', schedule);
  schedule();
  sources();
  find();
  selectNode();
});
