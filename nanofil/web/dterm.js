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

// The printer: where a head or goal breaks, chosen at the width the page
// gives it. After Bernardy, "A Pretty But Not Greedy Printer" (ICFP 2017),
// with his ribbon, and after Zoot (mbrock/zoot).
//
// dterm.pl draws each term once, as inline text, and marks its groups:
// data-d=args on a compound or list, whose .arg children are its items,
// and data-d=op on an operator a line may break at. A head or goal is
// read from that markup as a document in Bernardy's four operators:
//
//   text      a token, measured with canvas in its own font;
//   a <> b    b set after a, its later lines aligned where it began;
//   flush a   a, then a new line at the start of a's box;
//   a <|> b   either.
//
// The layouts each group offers are its legibility; what the printer
// optimises is only fitting and frugality. A group on one line has all
// its parts on that line, as a group either fits or breaks:
//
// - arguments: all on one line; or the first (and any simple ones after
//   it) on the opening line and each of the rest on a line of its own,
//   aligned under the first or hung --indent past the term's start; when
//   or, as Lisp is set, all from the next line, a step past the functor;
//   when all after the first are simple (atoms, numbers, variables, t(Q)) they
//   fill their lines instead, aligned or hung; a list of two or more
//   compound terms is on one line only within half the ribbon;
// - a chain of one operator: on one line, or a line per operand, aligned
//   under the first: a comma ends its line, → and ; start theirs, and any
//   other operator ends its line.
//
// Each document gets the Pareto frontier of its layouts by height, width,
// width of the last line and badness (a hung layout is a little worse than
// an aligned one). A layout wider than the width, or a single line longer
// than --ribbon (the measure: how much one line may hold however wide the
// page), is dropped as soon as it is made. The printer takes the shortest
// layout left, then the least bad, then the narrowest; when none fits it
// lets the ribbon go, then the width.
//
// The plan is written as kpre (mbrock/kpre) writes a paragraph: a break
// is a <br class="zbr"> and an indent, every other separator a no-break
// space, so the browser draws exactly the plan. A conditional set as a
// table stays one only while it fits; otherwise it is stacked.
(() => {
  const TERMS = ".clause > .head, div.goal, .clause.item, details.clause > summary";
  const SAFETY = 3; // canvas and the page disagree by a pixel or so
  const EPS = 0.5; // widths this close are the same width
  const MAX_NODES = 8000; // bigger terms flow as text
  const NBSP = "\u00a0";
  const root = document.documentElement;
  const ctx = document.createElement("canvas").getContext("2d");
  let widths = new Map(); // font → text → px
  let styles = new Map(); // element context → measures
  let styleWidth = innerWidth;
  const seps = new WeakSet(); // the spaces dterm.pl wrote between parts
  const original = new Map(); // what this script changed → how it was
  const planned = new Map(); // a term → the separators its plan wrote
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
  const ems = (v, size) => (v.trim().endsWith("em") ? px(v) * size : px(v));

  // Documents.
  let nid = 0, nodes = 0;
  const T = (w, unit = false, bad = 0) => (nodes++, { k: 0, w, unit, bad, id: nid++ });
  const STEP = (w) => (nodes++, { k: 0, w, sp: true, bad: 0, id: nid++ });
  const CAT = (kids) => {
    kids = kids.filter(Boolean);
    if (kids.length < 2) return kids[0] ?? null;
    return (nodes++, { k: 1, kids, id: nid++ });
  };
  const FLUSH = (a, at) => (nodes++, { k: 2, a, at, id: nid++ });
  const OR = (a, b) => (nodes++, { k: 3, a, b, id: nid++ });
  // a on one line, at most max wide (a fraction of the ribbon)
  const ONE = (a, max = 1) => a && (nodes++, { k: 4, a, max, id: nid++ });
  const vcat = (lines) => CAT(lines.map(([d, at], i) => (i < lines.length - 1 ? FLUSH(d, at) : d)));

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
      left: px(cs.marginLeft) + px(cs.borderLeftWidth) + px(cs.paddingLeft) + pseudo(el, "::before"),
      right: px(cs.marginRight) + px(cs.borderRightWidth) + px(cs.paddingRight) + pseudo(el, "::after"),
    };
    s.space = textWidth(s.font, " ") + px(cs.wordSpacing);
    styles.set(key, s);
    return s;
  }

  // A separator: a space on the line; where its group breaks, the break.
  function sep(n, s, st) {
    st.seps.push(n);
    return T(s.space);
  }

  function doc(n, s, st) {
    if (n.nodeType === 3) {
      if (seps.has(n)) return sep(n, s, st); // between parts of no group
      return n.data ? T(textWidth(s.font, n.data.replace(/\s+/g, " ")), true) : null;
    }
    if (n.nodeType !== 1 || n.nodeName === "BR" || n.classList.contains("zin")) return null;
    const e = style(n, s.key);
    if (e.skip) return null;
    const d = n.dataset.d === "args" ? argsDoc(n, e, st)
      : n.dataset.d === "op" && opOf(n) ? chainDoc(n, e, st)
      : CAT([...n.childNodes].map((c) => doc(c, e, st)));
    return CAT([e.left && T(e.left), d, e.right && T(e.right)]);
  }

  // A simple item: no group inside, or one as short as t(Q) or [A].
  const simple = (el) => !el.querySelector("[data-d]") || el.textContent.length <= 6;

  // A compound or list: its opening (functor and parenthesis, or bracket),
  // its items, and the separators between them.
  function argsDoc(el, e, st) {
    const box = el.classList.contains("l") ? el : [...el.children].find((c) => c.classList.contains("args"));
    if (!box) return CAT([...el.childNodes].map((c) => doc(c, e, st)));
    const open = [], items = [];
    let be = e, close = null;
    if (box !== el) {
      for (const c of el.childNodes) { if (c === box) break; open.push(doc(c, e, st)); }
      be = style(box, e.key);
      open.push(be.left && T(be.left));
      close = be.right && T(be.right);
    }
    let at = null;
    for (const c of box.childNodes) {
      if (seps.has(c)) { at = c; st.seps.push(c); continue; }
      const d = doc(c, be, st);
      if (!d) continue;
      // An item with no space before it (a list's |Tail) is one with the last.
      if (items.length && !at) { const p = items[items.length - 1]; p.d = CAT([p.d, d]); p.simple &&= simple(c); }
      else items.push({ d, at, el: c, simple: c.nodeType !== 1 || simple(c) });
      at = null;
    }
    const O = CAT(open), sp = T(be.space), step = STEP(st.indent);
    const n = items.length;
    const line = (a, b) => CAT(items.slice(a, b).flatMap((it, i) => (i ? [sp, it.d] : [it.d])));
    // Lisp's layout: the arguments from the next line, a step past the
    // functor, so a deep term comes back to the left. The break is before
    // the first argument, where there is no space to write it in.
    const lisp = (body) => {
      st.marks.push(items[0].el);
      return CAT([FLUSH(O, items[0].el), step, body, close, T(0, false, 2)]);
    };
    const deep = box !== el && items.some((it) => !it.simple) && items[0].el.nodeType === 1;
    if (n < 2) return deep ? OR(CAT([O, line(0, n), close]), lisp(items[0].d)) : CAT([O, line(0, n), close]);
    // A group set on one line is all on one line.
    // A list of terms (instructions, say) is a column once it is longer
    // than a phrase: half the ribbon.
    const column = box === el && items.filter((it) => !it.simple).length > 1;
    const alts = [ONE(CAT([O, line(0, n), close]), column ? 0.5 : 1)];
    if (items.slice(1).every((it) => it.simple)) {
      // Filled: aligned under the first item, or hung.
      let L = items[0].d, H = CAT([O, items[0].d]);
      for (const it of items.slice(1)) {
        L = OR(CAT([L, sp, it.d]), CAT([FLUSH(L, it.at), it.d]));
        H = OR(CAT([H, sp, it.d]), CAT([FLUSH(H, it.at), step, it.d]));
      }
      alts.push(CAT([O, L, close]), CAT([H, close, T(0, false, 1)]));
    } else {
      for (let k = 1; k < n; k++) {
        const rest = vcat(items.slice(k).map((it, i) => [it.d, items[k + i + 1]?.at]));
        const at = items[k].at, first = k > 1 ? ONE(line(0, k)) : line(0, k);
        alts.push(CAT([O, FLUSH(first, at), rest, close]));
        alts.push(CAT([FLUSH(CAT([O, first]), at), step, rest, close, T(0, false, 1)]));
        if (!items[k].simple) break; // only simple items join the first line
      }
    }
    if (deep) alts.push(lisp(vcat(items.map((it, i) => [it.d, items[i + 1]?.at]))));
    return alts.reduce((a, b) => OR(a, b));
  }

  // Operator chains: the operands of one operator, or of the operators of
  // a conditional, with the spaces around each operator.
  function opOf(o) {
    for (const c of o.children) if (c.classList.contains("op")) return c.classList.contains("tight") ? null : c;
    return null;
  }
  const family = (op) => (["->", ";", "*->", "|"].includes(op.title) ? "if" : op.title);
  const skipMarks = (n, dir) => {
    while (n && n.nodeType === 1 && n.matches(".zbr, .zin, .wb-nbsp:empty")) n = n[dir];
    if (n && n.nodeType === 1 && n.matches(".wb-nbsp")) n = n.firstChild; // the workbench's samples
    return n;
  };
  const isSpace = (n) => n && n.nodeType === 3 && /^[ \u00a0]?$/.test(n.data) && (seps.has(n) || n.data === NBSP || original.has(n));
  function links(o, fam, out) {
    const op = opOf(o), kids = [...o.childNodes];
    const i = kids.indexOf(op);
    const els = (a) => a.filter((k) => k.nodeType === 1 && !k.matches(".zbr, .zin, .wb-nbsp"));
    const [left] = els(kids.slice(0, i)), [right] = els(kids.slice(i + 1));
    const inner = (x) => x && x.dataset.d === "op" && opOf(x) && family(opOf(x)) === fam;
    if (inner(left)) links(left, fam, out); else out.push(left);
    const b = skipMarks(op.previousSibling, "previousSibling"), a = skipMarks(op.nextSibling, "nextSibling");
    out.push({ before: isSpace(b) ? b : null, op, after: isSpace(a) ? a : null });
    if (inner(right)) links(right, fam, out); else out.push(right);
  }
  function chainDoc(o, e, st) {
    const fam = family(opOf(o)), parts = [];
    links(o, fam, parts);
    const space = (n) => n && sep(n, e, st);
    const flat = [], lines = [];
    let cur = [];
    for (let i = 0; i < parts.length; i++) {
      const p = parts[i];
      if (!p.op) {
        const d = doc(p, e, st);
        flat.push(d);
        cur.push(d);
        continue;
      }
      const op = doc(p.op, e, st), b = space(p.before), a = space(p.after);
      flat.push(b, op, a);
      // → and ; start their lines; any other operator ends its line.
      const lead = fam === "if" && p.before;
      const at = lead ? p.before : p.after;
      if (!at) { cur.push(b, op, a); continue; }
      if (lead) { lines.push([CAT(cur), at]); cur = [op, a]; }
      else { cur.push(b, op); lines.push([CAT(cur), at]); cur = []; }
    }
    lines.push([CAT(cur), null]);
    if (lines.length < 2) return CAT(flat);
    const bad = fam === "if" || fam === "," ? 0 : 2;
    return OR(ONE(CAT(flat)), CAT([vcat(lines), bad && T(0, false, bad)]));
  }

  // Evaluation: each document's frontier, computed once (a layout's
  // measures do not depend on where it starts). A candidate is {h, mw, lw,
  // b, u, r}: lines after the first, widest line, last line, badness,
  // whether it is one token, and how it was made.
  function dominates(a, b) {
    return a.h <= b.h && a.b <= b.b && a.mw <= b.mw + EPS && a.lw <= b.lw + EPS;
  }
  function pareto(cs) {
    cs.sort((a, b) => a.h - b.h || a.b - b.b || a.mw - b.mw || a.lw - b.lw);
    const out = [];
    for (const c of cs) if (!out.some((o) => dominates(o, c))) out.push(c);
    return out;
  }
  function evaluate(n, E) {
    let r = E.memo.get(n.id);
    if (!r) E.memo.set(n.id, (r = step(n, E)));
    return r;
  }
  const valid = (m, E) => m.mw <= E.W && (m.h > 0 || m.u || m.mw <= E.R);
  function step(n, E) {
    switch (n.k) {
      case 0: {
        const m = { h: 0, mw: n.w, lw: n.w, b: n.bad, u: n.unit, r: n };
        return valid(m, E) ? [m] : [];
      }
      case 1: {
        let F = evaluate(n.kids[0], E);
        for (const kid of n.kids.slice(1)) {
          if (!F.length) return F;
          const G = [], K = evaluate(kid, E);
          for (const x of F) for (const y of K) {
            const m = { h: x.h + y.h, mw: Math.max(x.mw, x.lw + y.mw), lw: x.lw + y.lw, b: x.b + y.b, u: false, r: [x.r, y.r] };
            if (valid(m, E)) G.push(m);
          }
          F = pareto(G);
        }
        return F;
      }
      case 2: return pareto(evaluate(n.a, E).map((x) => ({ h: x.h + 1, mw: x.mw, lw: 0, b: x.b, u: false, r: { f: x.r, at: n.at } })));
      case 3: return pareto(evaluate(n.a, E).concat(evaluate(n.b, E)));
      case 4: return evaluate(n.a, E).filter((x) => x.h === 0 && (x.u || x.mw <= n.max * E.R));
    }
  }

  // The breaks a layout makes: where, and at what column the next line
  // starts. A box's later lines start where the box began.
  function walk(r, col, out) {
    if (Array.isArray(r)) return walk(r[1], walk(r[0], col, out), out);
    if (r.f) {
      walk(r.f, col, out);
      out.open = { at: r.at, to: col };
      out.breaks.set(r.at, out.open);
      return col;
    }
    if (r.sp && out.open) out.open.to += r.w;
    else if (r.w) out.open = null;
    return col + r.w;
  }

  function plan(t) {
    const tries = [[t.W, t.R], [t.W, Infinity], [Infinity, Infinity]];
    for (const [W, R] of tries) {
      const F = evaluate(t.doc, { W, R, memo: new Map() });
      if (!F.length) continue;
      const wide = W === Infinity;
      let best = F[0];
      for (const c of F) {
        const key = wide ? [c.mw, c.h, c.b] : [c.h, c.b, c.mw];
        const bk = wide ? [best.mw, best.h, best.b] : [best.h, best.b, best.mw];
        if (key[0] < bk[0] || (key[0] === bk[0] && (key[1] < bk[1] || (key[1] === bk[1] && key[2] < bk[2])))) best = c;
      }
      const out = { breaks: new Map(), open: null };
      walk(best.r, t.start, out);
      return out.breaks;
    }
    return new Map();
  }

  // Where a thing in a clause may reach: the clause's content edge, less
  // what each box between takes on its right.
  function rightEdge(el, clause) {
    const cc = getComputedStyle(clause), cr = clause.getBoundingClientRect();
    let right = cr.left + clause.clientLeft + clause.clientWidth - px(cc.paddingRight);
    for (let a = el.parentElement; a && a !== clause && clause.contains(a); a = a.parentElement) {
      const as = getComputedStyle(a);
      right -= px(as.marginRight) + px(as.borderRightWidth) + px(as.paddingRight);
    }
    return right;
  }

  // A term: where it starts, how wide it may run, its document.
  function measure(el, clause) {
    if (!el.getClientRects().length || el.querySelector("div")) return null;
    const cs = getComputedStyle(el), r = el.getBoundingClientRect();
    const origin = r.left + el.clientLeft;
    let right = rightEdge(el, clause);
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
    const size = px(cs.fontSize);
    const st = { seps: [], marks: [], indent: ems(cs.getPropertyValue("--indent"), size) || size };
    const top = { key: "R" + fontOf(cs), font: fontOf(cs), space: textWidth(fontOf(cs), " ") };
    nodes = 0;
    const d = CAT([...el.childNodes].map((n) => doc(n, top, st)));
    if (!d || nodes > MAX_NODES) return null;
    const W = right - origin - SAFETY - start;
    const R = ems(cs.getPropertyValue("--ribbon"), size) || Infinity;
    return { el, st, doc: d, start, W, R: Math.min(R, W) };
  }

  function remember(n) {
    if (!original.has(n)) original.set(n, n.nodeType === 3 ? n.data : n.className);
  }

  function unbreak(n) {
    if (n.nodeType === 1) {
      const i = n.previousSibling, br = i?.previousSibling;
      if (i?.classList?.contains("zin") && br?.classList?.contains("zbr")) { i.remove(); br.remove(); }
      return;
    }
    let br = n.nextSibling;
    if (!br || br.nodeName !== "BR" || !br.classList.contains("zbr")) return;
    if (br.nextSibling?.classList?.contains("zin")) br.nextSibling.remove();
    br.remove();
  }

  // A term as dterm.pl drew it.
  function unplan(el) {
    for (const n of planned.get(el) ?? []) { unbreak(n); if (n.nodeType === 3) n.data = original.get(n); }
    planned.delete(el);
    if (el.classList.contains("zt")) el.classList.remove("zt");
  }

  function write(t, breaks) {
    for (const n of planned.get(t.el) ?? []) unbreak(n);
    for (const m of t.st.marks) {
      const b = breaks.get(m);
      if (!b) continue;
      const br = document.createElement("br"), i = document.createElement("span");
      br.className = "zbr";
      i.className = "zin";
      i.style.width = b.to + "px";
      m.before(br, i);
    }
    for (const n of t.st.seps) {
      remember(n);
      const b = breaks.get(n);
      n.data = b ? "" : NBSP;
      if (!b) continue;
      const br = document.createElement("br"), i = document.createElement("span");
      br.className = "zbr";
      i.className = "zin";
      i.style.width = b.to + "px";
      n.after(br, i);
    }
    planned.set(t.el, t.st.seps.concat(t.st.marks));
  }

  // Without the printer, the page is as dterm.pl drew it.
  function restore() {
    for (const el of [...planned.keys()]) unplan(el);
    for (const [n, was] of original) if (n.nodeType === 1) n.className = was;
    original.clear();
    root.classList.remove("zp");
  }

  let raf = null;
  function schedule() {
    if (raf === null) raf = requestAnimationFrame(run);
  }
  const inTable = (el) => { const c = el.closest(".cases"); return c && !c.classList.contains("stack"); };
  function run() {
    raf = null;
    if (root.dataset.planner === "off") { pending.clear(); restore(); return; }
    root.classList.add("zp");
    if (innerWidth !== styleWidth) { styles = new Map(); styleWidth = innerWidth; }
    const todo = [];
    for (const clause of pending) {
      if (!clause.isConnected) { clauses.delete(clause); continue; }
      const terms = clause.matches(".clause.item") ? [clause]
        : [...clause.querySelectorAll(TERMS)].filter((e) => e.closest(".clause") === clause);
      const tables = [...clause.querySelectorAll(".cases")].filter((c) => {
        if (!original.has(c)) remember(c);
        return !original.get(c).split(" ").includes("stack");
      });
      todo.push({ clause, terms, tables });
    }
    pending.clear();
    // Tables first: each is set as a table, on one line per goal, to see
    // whether it fits.
    for (const { terms, tables } of todo) {
      for (const c of tables) { c.classList.remove("stack"); c.classList.add("ztry"); }
      for (const el of terms) if (tables.some((c) => c.contains(el))) unplan(el);
    }
    const fits = todo.map(({ clause, tables }) => tables.map((c) => {
      const r = c.getBoundingClientRect(), cs = getComputedStyle(c);
      return r.width <= rightEdge(c, clause) - px(cs.marginRight) - r.left - SAFETY;
    }));
    todo.forEach(({ tables }, i) => tables.forEach((c, j) => {
      c.classList.remove("ztry");
      if (!fits[i][j]) c.classList.add("stack");
    }));
    // Then the terms, all read, then all written: one layout for the lot.
    for (const { terms } of todo) for (const el of terms) {
      if (inTable(el)) { unplan(el); continue; }
      if (!el.dataset.zt) {
        el.dataset.zt = "1";
        const w = document.createTreeWalker(el, NodeFilter.SHOW_TEXT);
        for (let t; (t = w.nextNode()); ) if (t.data === " ") seps.add(t);
      }
      el.classList.add("zt");
    }
    const work = [], loose = [];
    for (const { clause, terms } of todo) for (const el of terms) {
      if (!el.classList.contains("zt")) continue;
      const t = measure(el, clause);
      if (t) work.push(t); else loose.push(el);
    }
    loose.forEach(unplan);
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
    .observe(root, { attributes: true, attributeFilter: ["style", "data-planner", "data-parens", "data-brackets", "data-layout"] });
  document.fonts?.addEventListener("loadingdone", () => { widths = new Map(); styles = new Map(); all(); });
  (document.fonts?.ready ?? Promise.resolve()).then(() => scan(document));
})();
