/* HTMX owns state/rail/graph HTML. This console owns its bounded log window. */
document.addEventListener('DOMContentLoaded', () => {
  const byId = id => document.getElementById(id);
  const initialRun = byId('state').dataset.run;
  const cursor = byId('log-cursor');
  const rows = byId('log-rows');
  const box = byId('log-scroll');
  let following = true, pending = null, epoch = 0, graphScroll = 0, exhausted = false;
  const message = value => { byId('console-state').textContent = value; };
  const pin = () => {
    const u = new URL(location.href);
    u.searchParams.set('run', initialRun);
    history.replaceState(null, '', u);
    // Reprocess a fresh element: do not leave an old implicit-latest timer.
    const old = byId('state'), replacement = old.cloneNode(true);
    replacement.setAttribute('hx-get', './state?' + new URLSearchParams({run: initialRun, activity: cursor.dataset.activity}));
    old.replaceWith(replacement);
    htmx.process(replacement);
  };
  function setFollow(value) {
    following = value;
    exhausted = false;
    byId('log-follow').textContent = value ? 'Pause' : 'Follow';
    if (!value) { epoch++; pending?.abort(); pin(); }
  }
  function find() {
    const term = byId('log-find').value.toLowerCase();
    let matches = 0;
    for (const row of rows.querySelectorAll('.log-row')) {
      const pre = row.querySelector('pre');
      const text = pre.textContent;
      pre.replaceChildren();
      let pos = 0, next;
      while (term && (next = text.toLowerCase().indexOf(term, pos)) >= 0) {
        pre.append(document.createTextNode(text.slice(pos, next)));
        const mark = document.createElement('mark');
        mark.textContent = text.slice(next, next + term.length);
        pre.append(mark); pos = next + term.length; matches++;
      }
      pre.append(document.createTextNode(text.slice(pos)));
      row.hidden = !!term && !text.toLowerCase().includes(term);
    }
    byId('find-count').textContent = (term ? matches + ' matches · ' : '') + rows.querySelectorAll('.log-row').length + ' loaded';
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
      exhausted = doc.querySelectorAll('.log-row').length === 0;
      if (replace) rows.replaceChildren();
      for (const row of doc.querySelectorAll('.log-row')) rows.append(row);
      const next = doc.getElementById('log-cursor');
      cursor.dataset.after = next.dataset.after;
      cursor.dataset.activity = activity;
      while (rows.querySelectorAll('.log-row').length > 256) rows.firstElementChild.remove();
      if (rows.querySelector('.log-row')) rows.querySelector('.log-empty')?.remove();
      if (!rows.children.length) { const p = document.createElement('p'); p.className = 'log-empty'; p.textContent = 'No captured output'; rows.append(p); }
      find();
      if (following || tail) box.scrollTop = box.scrollHeight;
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
    box.scrollTop = 0;
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
      byId('selected-node').hidden = node.id === document.querySelector('.graph-node')?.id;
      byId('graph-scroll').scrollTop += node.getBoundingClientRect().top - byId('graph-scroll').getBoundingClientRect().top;
      byId('graph-scroll').scrollLeft += node.querySelector('.node-name').getBoundingClientRect().left - byId('graph-scroll').getBoundingClientRect().left;
    }
  }
  function railState() {
    byId('rail-after').value = '0';
    const u = new URL(location.href);
    u.searchParams.set('filter', byId('session-filter').value);
    u.searchParams.set('find', byId('session-find').value);
    history.replaceState(null, '', u);
  }
  const params = new URL(location.href).searchParams;
  byId('session-filter').value = params.get('filter') || 'all';
  byId('session-find').value = params.get('find') || '';
  if (params.has('filter') || params.has('find')) htmx.trigger(byId('rail-controls'), 'change');
  byId('rail-controls').addEventListener('change', railState);
  byId('session-filter').addEventListener('input', railState);
  byId('session-find').addEventListener('input', () => { railState(); htmx.trigger(byId('rail-controls'), 'change'); });
  byId('log-find').addEventListener('input', () => { if (following) setFollow(false); find(); });
  byId('log-follow').addEventListener('click', () => { if (following) setFollow(false); else { setFollow(true); end(); } });
  byId('log-end').addEventListener('click', end);
  box.addEventListener('scroll', () => { if (following && box.scrollHeight-box.scrollTop-box.clientHeight > 40) setFollow(false); });
  byId('log-phase').addEventListener('change', e => { const o = e.target.selectedOptions[0]; if (o.value) jumpPhase(o.value,o.dataset.activity); });
  document.addEventListener('click', async e => {
    const filter = e.target.closest('[data-filter]');
    if (filter) { byId('session-filter').value = filter.dataset.filter; railState(); htmx.trigger(byId('rail-controls'), 'change'); }
    const phase = e.target.closest('[data-phase-seq]');
    if (phase) jumpPhase(phase.dataset.phaseSeq,phase.dataset.phaseActivity);
    const copy = e.target.closest('[data-copy]');
    if (copy) { try { await navigator.clipboard.writeText(copy.dataset.copy); message('Copied'); } catch { message('Copy unavailable'); } }
  });
  document.addEventListener('htmx:before:swap', () => { graphScroll = byId('graph-scroll')?.scrollTop || 0; });
  document.addEventListener('htmx:after:swap', e => {
    if (!new URL(location.href).searchParams.has('run') && byId('state').dataset.run !== initialRun) { location.reload(); return; }
    const graph = byId('graph-scroll');
    if (graph) {
      graph.scrollTop = graphScroll;
      const action = new URL(e.detail.ctx.request.action, location.href);
      if (action.pathname.endsWith('/graph')) graph.scrollTop += byId('static-rows').getBoundingClientRect().top - graph.getBoundingClientRect().top;
      const summary = document.querySelector('[data-static] summary');
      if (summary) summary.textContent = graph.dataset.staticCount + ' static inputs';
    }
    byId('rail-after').value = document.querySelector('.rail-count').dataset.after;
    const phase = byId('log-phase'), choice = phase.value;
    if (document.activeElement !== phase && byId('phase-options')) {
      phase.replaceChildren(byId('phase-options').content.cloneNode(true));
      phase.value = choice;
    }
    byId('log-mode').textContent = byId('state').dataset.live === '1' ? 'Live' : 'Captured';
    if (following) box.scrollTop = box.scrollHeight;
    if (location.hash) selectNode();
  });
  window.addEventListener('hashchange', selectNode);
  const poll = async () => { if (following && (!exhausted || byId('state').dataset.live === '1')) await load(); setTimeout(poll,1000); };
  setTimeout(poll,1000);
  box.scrollTop = box.scrollHeight;
  find(); selectNode();
});
