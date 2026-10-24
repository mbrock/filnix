// Hovering a variable lights up its other occurrences in the same clause
// or documentation.
document.addEventListener("mouseover", (event) => {
  const v = event.target.closest(".v[data-v]");
  for (const lit of document.querySelectorAll(".v.lit")) lit.classList.remove("lit");
  if (!v) return;
  const scope = v.closest(".clause, .doc, tr") || document;
  for (const w of scope.querySelectorAll(".v[data-v]")) {
    if (w.dataset.v === v.dataset.v) w.classList.add("lit");
  }
});

// The line planner: where a head or goal breaks, chosen at the width the
// browser gives it, after Zoot (mbrock/zoot) and "A Pretty Expressive
// Printer" (Porncharoenwase, Pombrio and Torlak 2023), cut to dterm.
//
// dterm.pl draws each term once, as inline text, and marks the terms too
// long for 80 or 40 characters (class long, long-n), which is the layout
// without this script. Here each head and goal becomes a document of
// groups, read from the HTML itself. A group breaks at all of its
// separators or at none, so its parts keep the same footing:
//
// - the arguments of a compound or list: each after the first starts a
//   line, one step deeper than the line the term opened on; arguments
//   that are all atoms, numbers and variables instead fill their lines;
// - a chain of one operator, A, B, C or C → T ; E: a comma ends its line
//   and the next goal aligns under the first, and any other operator
//   starts its line, under the first operand, with its operand after it.
//
// A term that fits on its line therefore never breaks inside, and every
// continuation line sits deeper than the line that holds its parent.
//
// Every token is measured with canvas in its own font, paddings and
// borders included, so the plan is in pixels. The evaluator keeps, for
// each piece of document at each column, the Pareto frontier of where its
// last line ends against its cost: overflow past the width (squared),
// then the breaks, each costing 8^depth, so a term breaks between its
// big pieces before it breaks inside small ones, then lines.
//
// The plan is written back after kpre (mbrock/kpre): a chosen break is a
// <br class="zbr"> and an indent, and every other separator becomes a
// no-break space, so the browser's own line breaker draws exactly the plan.
(() => {
  const TERMS = ".clause > .head, div.goal, .clause.item, details.clause > summary";
  const SAFETY = 3; // canvas and the page disagree by a pixel or so
  const CAP = 12; // the most candidates a frontier keeps
  const MAX_NODES = 6000; // bigger terms keep dterm.pl's breaks
  const LOOSE = 1e12; // a space outside any group: only to avoid overflow
  const NBSP = "\u00a0";
  const root = document.documentElement;
  const ctx = document.createElement("canvas").getContext("2d");
  let widths = new Map(); // font → text → px
  let styles = new Map(); // element context → measures
  let styleWidth = innerWidth;
  const original = new Map(); // what this script changed → how it was
  const sizes = new WeakMap();
  const pending = new Set();
  const clauses = new Set();

  const px = (v) => parseFloat(v) || 0;
  const fontOf = (cs) => `${cs.fontStyle} ${cs.fontWeight} ${cs.fontSize} ${cs.fontFamily}`;
  function textWidth(font, text) {
    let m = widths.get(font);
    if (!m) widths.set(font, (m = new Map()));
    let w = m.get(text);
    if (w === undefined) {
      ctx.font = font;
      m.set(text, (w = ctx.measureText(text).width));
    }
    return w;
  }

  // Documents: text, a line break, concatenation, choice, an indent one
  // step in, and an alignment at the current column.
  let nid = 0, nodes = 0;
  const T = (w) => (nodes++, { k: 0, w, id: nid++ });
  const NL = (cost, at) => (nodes++, { k: 1, cost, at, id: nid++ });
  const CAT = (kids) => (kids.length === 1 ? kids[0] : (nodes++, { k: 2, kids, id: nid++ }));
  const OR = (a, b) => (nodes++, { k: 3, a, b, id: nid++ });
  const NEST = (n, kid) => (nodes++, { k: 4, n, kid, id: nid++ });
  const ALIGN = (kid) => (nodes++, { k: 5, kid, id: nid++ });

  function pseudo(el, which) {
    const cs = getComputedStyle(el, which), c = cs.content;
    if (!c || c[0] !== '"' || c.length < 3) return 0;
    return textWidth(fontOf(cs), c.slice(1, -1)) + px(cs.marginLeft) + px(cs.marginRight) +
      px(cs.paddingLeft) + px(cs.paddingRight);
  }

  function style(el, pkey) {
    const key = pkey + ">" + el.tagName + "." + el.className;
    let s = styles.get(key);
    if (s) return s;
    const cs = getComputedStyle(el);
    s = {
      key,
      skip: cs.display === "none" || cs.position === "absolute",
      font: fontOf(cs),
      left: px(cs.marginLeft) + px(cs.borderLeftWidth) + px(cs.paddingLeft),
      right: px(cs.marginRight) + px(cs.borderRightWidth) + px(cs.paddingRight),
      before: 0, after: 0, indent: 0,
    };
    // An argument's pseudo-elements are dterm.pl's broken layout, which
    // the plan replaces.
    if (!el.classList.contains("arg")) {
      s.before = pseudo(el, "::before");
      s.after = pseudo(el, "::after");
    }
    const ind = cs.getPropertyValue("--indent").trim();
    s.indent = ind.endsWith("em") ? px(ind) * px(cs.fontSize) : px(ind);
    styles.set(key, s);
    return s;
  }

  const cost = (depth) => 8 ** depth;
  const isSpace = (n) => n && n.nodeType === 3 && (n.data === " " || n.data === NBSP);

  // A separator: a space that is a space or, when its group breaks, a
  // line break.
  function sep(n, s, st) {
    st.seps.push(n);
    return T(textWidth(s.font, " "));
  }
  function brk(n, depth, st) {
    st.seps.push(n);
    return NL(cost(depth), n);
  }

  function node(n, s, depth, st) {
    if (n.nodeType === 3) {
      if (isSpace(n)) return OR(sep(n, s, st), NL(LOOSE, n));
      return n.data ? T(textWidth(s.font, n.data.replace(/\s+/g, " "))) : null;
    }
    if (n.nodeType !== 1 || n.nodeName === "BR" || n.classList.contains("zin")) return null;
    const e = style(n, s.key);
    if (e.skip) return null;
    const cl = n.classList, kids = [];
    if (e.left + e.before) kids.push(T(e.left + e.before));
    if (cl.contains("args") || (cl.contains("l") && !cl.contains("empty"))) kids.push(boxDoc(n, e, depth + 1, st));
    else if (cl.contains("o") && !cl.contains("pre") && opOf(n)) kids.push(chainDoc(n, e, depth, st));
    else {
      const d = cl.contains("paren") || cl.contains("braces") ? depth + 1 : depth;
      for (const c of n.childNodes) { const k = node(c, e, d, st); if (k) kids.push(k); }
    }
    if (e.right + e.after) kids.push(T(e.right + e.after));
    return kids.length ? CAT(kids) : null;
  }

  // Arguments: all on the line, each after the first on a line of its
  // own, or, when none of them has parts, filling the lines.
  function boxDoc(el, e, depth, st) {
    const parts = [];
    for (const c of el.childNodes) {
      if (isSpace(c)) parts.push(c);
      else { const d = node(c, e, depth, st); if (d) parts.push(d); }
    }
    const nargs = parts.filter((p) => !p.nodeType).length;
    const flat = [], broken = [];
    if (nargs < 2) {
      for (const p of parts) flat.push(p.nodeType ? OR(sep(p, e, st), NL(LOOSE, p)) : p);
      return CAT(flat);
    }
    if (!el.querySelector(".args, .l:not(.empty), .paren, .braces, .o:not(.pre), .s")) {
      for (const p of parts) flat.push(p.nodeType ? OR(sep(p, e, st), brk(p, depth, st)) : p);
      return NEST(e.indent, CAT(flat));
    }
    for (const p of parts) {
      flat.push(p.nodeType ? sep(p, e, st) : p);
      broken.push(p.nodeType ? brk(p, depth, st) : p);
    }
    return OR(CAT(flat), NEST(e.indent, CAT(broken)));
  }

  // Operator chains. An operator's family: the operators that chain
  // together, as the arms of a conditional do.
  function opOf(o) {
    for (const c of o.children) if (c.classList.contains("op")) return c.classList.contains("tight") ? null : c;
    return null;
  }
  const family = (op) => (["->", ";", "*->", "|"].includes(op.title) ? "if" : op.title);
  function links(o, fam, out) {
    const op = opOf(o), kids = [...o.childNodes];
    const i = kids.indexOf(op);
    const els = (a) => a.filter((k) => k.nodeType === 1 && !k.matches(".zbr, .zin"));
    const [left] = els(kids.slice(0, i)), [right] = els(kids.slice(i + 1));
    const inner = (x) => x && x.classList.contains("o") && !x.classList.contains("pre") && opOf(x) && family(opOf(x)) === fam;
    if (inner(left)) links(left, fam, out); else out.push(left);
    // The space before an operator, past any break this script made there.
    let b = op.previousSibling;
    while (b && b.nodeType === 1 && b.matches(".zbr, .zin")) b = b.previousSibling;
    if (b && b.nodeType === 1 && b.matches(".wb-nbsp")) b = b.firstChild; // the workbench's samples
    out.push({ before: isSpace(b) ? b : null, op,
      after: isSpace(op.nextSibling) ? op.nextSibling : null });
    if (inner(right)) links(right, fam, out); else out.push(right);
  }
  function chainDoc(o, e, depth, st) {
    const fam = family(opOf(o)), parts = [];
    links(o, fam, parts);
    const flat = [], broken = [];
    for (let i = 0; i < parts.length; i++) {
      const p = parts[i];
      if (!p.op) {
        const d = node(p, e, depth, st);
        if (!d) continue;
        flat.push(d);
        broken.push(i && fam !== "," ? ALIGN(d) : d);
        continue;
      }
      const op = node(p.op, e, depth, st);
      const sp = (n) => (n ? sep(n, e, st) : null);
      flat.push(...[sp(p.before), op, sp(p.after)].filter(Boolean));
      // A comma ends its line; any other operator starts one.
      if (fam === ",") broken.push(...[sp(p.before), op, p.after ? brk(p.after, depth, st) : null].filter(Boolean));
      else broken.push(...[p.before ? brk(p.before, depth, st) : null, op, sp(p.after)].filter(Boolean));
    }
    return OR(CAT(flat), ALIGN(CAT(broken)));
  }

  // Evaluation. A candidate is {last, ov, bad, h, dec}: the column its
  // last line ends at, its cost, and the breaks that make it.
  function better(a, b) {
    const ao = Math.round(a.ov), bo = Math.round(b.ov);
    if (ao !== bo) return ao < bo;
    if (a.bad !== b.bad) return a.bad < b.bad;
    return a.h < b.h;
  }
  function prune(cs) {
    cs.sort((a, b) => a.last - b.last || (better(a, b) ? -1 : better(b, a) ? 1 : 0));
    const out = [];
    for (const c of cs) if (!out.length || better(c, out[out.length - 1])) out.push(c);
    if (out.length <= CAP) return out;
    return Array.from({ length: CAP }, (_, i) => out[Math.round((i * (out.length - 1)) / (CAP - 1))]);
  }
  const join = (c, d) => ({
    last: d.last, ov: c.ov + d.ov, bad: c.bad + d.bad, h: c.h + d.h,
    dec: c.dec && d.dec ? [c.dec, d.dec] : c.dec || d.dec,
  });
  function overflow(W, last, w) {
    const old = Math.max(0, last - W), nw = Math.max(0, last + w - Math.max(W, last));
    return nw * (2 * old + nw);
  }
  function evaluate(n, last, base, E) {
    const key = n.id + ":" + Math.round(last * 2) + ":" + Math.round(base * 2);
    let r = E.memo.get(key);
    if (!r) E.memo.set(key, (r = step(n, last, base, E)));
    return r;
  }
  function step(n, last, base, E) {
    switch (n.k) {
      case 0: return [{ last: last + n.w, ov: overflow(E.W, last, n.w), bad: 0, h: 0, dec: null }];
      case 1: return [{ last: base, ov: 0, bad: n.cost, h: 1, dec: { at: n.at, to: base } }];
      case 2: {
        let F = [{ last, ov: 0, bad: 0, h: 0, dec: null }];
        for (const kid of n.kids) {
          const G = [];
          for (const c of F) for (const d of evaluate(kid, c.last, base, E)) G.push(join(c, d));
          F = prune(G);
        }
        return F;
      }
      case 3: return prune(evaluate(n.a, last, base, E).concat(evaluate(n.b, last, base, E)));
      case 4: return evaluate(n.kid, last, base + n.n, E);
      // Never left of the hang: there a continuation would read as the
      // next goal.
      case 5: return evaluate(n.kid, last, Math.max(last, E.hang), E);
    }
  }
  function decisions(dec, breaks) {
    if (!dec) return;
    if (Array.isArray(dec)) { decisions(dec[0], breaks); decisions(dec[1], breaks); }
    else breaks.set(dec.at, dec.to);
  }

  // A term: where it starts, how wide it may run, its document.
  function measure(el, clause) {
    if (!el.getClientRects().length || el.querySelector("div")) return null;
    // A short chain set as a table shares its width between columns.
    const c = el.closest(".case");
    if (c && getComputedStyle(c).display === "contents") return null;
    const cs = getComputedStyle(el), r = el.getBoundingClientRect();
    const origin = r.left + el.clientLeft;
    // The goals are columns as wide as their content, so the measure is the
    // clause's: its content edge, less what each box between takes.
    const cc = getComputedStyle(clause), cr = clause.getBoundingClientRect();
    let right = cr.left + clause.clientLeft + clause.clientWidth - px(cc.paddingRight);
    for (let a = el.parentElement; a && a !== clause && clause.contains(a); a = a.parentElement) {
      const as = getComputedStyle(a);
      right -= px(as.marginRight) + px(as.borderRightWidth) + px(as.paddingRight);
    }
    if (el !== clause) right -= px(cs.paddingRight);
    let start = 0;
    for (const n of el.childNodes) {
      if (n.nodeType === 1) {
        const ns = getComputedStyle(n);
        if (ns.position === "absolute" || ns.display === "none") continue;
        start = n.getBoundingClientRect().left - origin - px(ns.marginLeft);
        break;
      }
      if (n.nodeType === 3 && n.data) {
        const rg = document.createRange();
        rg.selectNodeContents(n);
        start = rg.getBoundingClientRect().left - origin;
        break;
      }
    }
    const st = { seps: [] };
    const top = { key: "R" + fontOf(cs), font: fontOf(cs) };
    const hang = px(cs.paddingLeft), indent = style(el, "S").indent || px(cs.fontSize);
    nodes = 0;
    const kids = [];
    for (const n of el.childNodes) { const d = node(n, top, 0, st); if (d) kids.push(d); }
    if (nodes > MAX_NODES) return null;
    // The first step in from the line's start is the hang.
    return { el, st, doc: CAT(kids), start, W: right - origin - SAFETY, hang, base: hang - indent };
  }

  function plan(t) {
    const E = { W: t.W, hang: t.hang, memo: new Map() };
    const F = evaluate(t.doc, t.start, t.base, E);
    let best = F[0];
    for (const c of F) if (better(c, best)) best = c;
    const breaks = new Map();
    decisions(best.dec, breaks);
    return breaks;
  }

  function remember(n) {
    if (original.has(n)) return;
    original.set(n, n.nodeType === 3 ? n.data : n.className);
  }

  function write(t, breaks) {
    // dterm.pl's own breaks give way to the plan.
    for (const b of [t.el, ...t.el.querySelectorAll(".long, .long-n")]) {
      if (!b.classList.contains("long") && !b.classList.contains("long-n")) continue;
      remember(b);
      b.classList.remove("long", "long-n");
    }
    for (const n of t.st.seps) {
      remember(n);
      unbreak(n);
      const to = breaks.get(n);
      n.data = to === undefined ? NBSP : " ";
      if (to === undefined) continue;
      // The break, and the indent past the hang the line continues at.
      const b = document.createElement("br"), i = document.createElement("span");
      b.className = "zbr";
      i.className = "zin";
      i.style.width = Math.max(0, to - t.hang) + "px";
      n.after(b, i);
    }
  }

  function unbreak(n) {
    const br = n.nextSibling;
    if (!br || br.nodeName !== "BR" || !br.classList.contains("zbr")) return;
    if (br.nextSibling?.classList?.contains("zin")) br.nextSibling.remove();
    br.remove();
  }

  // Without the planner, the page is as dterm.pl drew it.
  function restore() {
    for (const [n, was] of original) {
      if (n.nodeType === 3) { unbreak(n); n.data = was; }
      else n.className = was;
    }
    original.clear();
  }

  let raf = null;
  function schedule() {
    if (raf === null) raf = requestAnimationFrame(run);
  }
  function run() {
    raf = null;
    if (root.dataset.planner === "off") { pending.clear(); restore(); return; }
    if (innerWidth !== styleWidth) { styles = new Map(); styleWidth = innerWidth; }
    const work = [];
    // All reading first, then all writing: one layout for the lot.
    for (const clause of pending) {
      if (!clause.isConnected) { clauses.delete(clause); continue; }
      const terms = clause.matches(".clause.item") ? [clause]
        : [...clause.querySelectorAll(TERMS)].filter((e) => e.closest(".clause") === clause);
      for (const el of terms) { const t = measure(el, clause); if (t) work.push(t); }
    }
    pending.clear();
    const plans = work.map(plan);
    work.forEach((t, i) => write(t, plans[i]));
  }

  const resized = new ResizeObserver((entries) => {
    for (const e of entries) {
      const w = e.contentRect.width;
      if (Math.abs((sizes.get(e.target) ?? -1) - w) < 0.5) continue;
      sizes.set(e.target, w);
      pending.add(e.target);
    }
    schedule();
  });
  function scan(top) {
    const found = top.matches?.(".clause") ? [top] : [];
    for (const c of top.querySelectorAll?.(".clause") ?? []) found.push(c);
    for (const c of found) if (!clauses.has(c)) { clauses.add(c); resized.observe(c); }
  }
  function all() {
    for (const c of clauses) pending.add(c);
    schedule();
  }

  // The playground draws its terms after loading; the workbench changes
  // the type on the root element.
  new MutationObserver((records) => {
    for (const r of records) for (const n of r.addedNodes) if (n.nodeType === 1 && !n.matches(".zbr, .zin")) scan(n);
  }).observe(document.body, { childList: true, subtree: true });
  new MutationObserver(() => { styles = new Map(); all(); })
    .observe(root, { attributes: true, attributeFilter: ["style", "class", "data-planner", "data-parens", "data-brackets", "data-layout", "data-long"] });
  document.fonts?.addEventListener("loadingdone", () => { widths = new Map(); styles = new Map(); all(); });
  (document.fonts?.ready ?? Promise.resolve()).then(() => scan(document));
})();
