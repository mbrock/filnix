// A dterm page, laid out by the browser at a PDF's measure, written as
// Typst (typeset.py). Prose (headings, paragraphs, lists, prose tables,
// quotes) becomes Typst markup, for Typst to set and justify in the
// paper's own type. Everything dterm draws (clauses, Rocq and C fences,
// diagrams, fact tables) becomes what the browser drew: each run of glyphs
// at the place dterm.js's printer put it, and each parenthesis, bracket,
// rule and fill as a shape. Typst runs no layout search; the Pareto
// printer has already chosen every line break for this width.
//
// dtermTypst(opts) resolves to { title, typst }. opts.base is the page's
// URL on the wiki, for links; opts.maxHeight is the page's text height
// in CSS px, the tallest strip a drawing may be cut into.

(() => {
  const PT = 0.75; // pt per CSS px
  // Typst may break a line at #h; a word joiner after it keeps a term's
  // own spacing from becoming a break the browser's printer never chose.
  const WJ = "\u2060";
  const f2 = (v) => (Math.round(v * PT * 100) / 100).toString();
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const frame = () => Promise.race([new Promise((r) => requestAnimationFrame(() => r())), sleep(100)]);

  // Typst string literal.
  const tstr = (s) => '"' + s.replace(/[\\"]/g, (c) => "\\" + c)
    .replace(/[\u0000-\u001f]/g, (c) => `\\u{${c.charCodeAt(0).toString(16)}}`) + '"';
  // Typst markup text: every markup character escaped, except quotes,
  // which Typst sets as smart quotes.
  const markup = (s) => s.replace(/[\\#*_`$<>@\[\]~\/\-+=.:]/g, (c) => "\\" + c);

  // Colours: rgb(), rgba() and color(srgb …) as Typst rgb with alpha.
  function colour(c, opacity = 1) {
    let m = c.match(/^rgba?\(([\d.]+),\s*([\d.]+),\s*([\d.]+)(?:,\s*([\d.]+))?\)/), r, g, b, a;
    if (m) [r, g, b, a] = [+m[1], +m[2], +m[3], m[4] === undefined ? 1 : +m[4]];
    else if ((m = c.match(/^color\(srgb ([\d.e-]+) ([\d.e-]+) ([\d.e-]+)(?: \/ ([\d.]+))?\)/)))
      [r, g, b, a] = [m[1] * 255, m[2] * 255, m[3] * 255, m[4] === undefined ? 1 : +m[4]];
    else return null;
    a *= opacity;
    if (a <= 0.004) return null;
    const h = (v) => Math.max(0, Math.min(255, Math.round(v))).toString(16).padStart(2, "0");
    return `rgb("#${h(r)}${h(g)}${h(b)}${a < 0.996 ? h(a * 255) : ""}")`;
  }

  const opacities = new WeakMap();
  function opacity(el) {
    if (!el || el.nodeType !== 1) return 1;
    let o = opacities.get(el);
    if (o === undefined) opacities.set(el, (o = parseFloat(getComputedStyle(el).opacity) * opacity(el.parentElement)));
    return o;
  }

  // The paper's families: what each CSS family list is set in.
  function family(cs) {
    const first = cs.fontFamily.split(",")[0].trim().replace(/^["']|["']$/g, "");
    if (/mono|consol|menlo|courier/i.test(first)) return "DM Mono";
    return "Public Sans";
  }

  // Where the baseline sits below the top of a text rect, per font.
  const ascents = new Map();
  function ascent(cs) {
    const font = `${cs.fontStyle} ${cs.fontWeight} ${cs.fontSize} ${cs.fontFamily}`;
    let a = ascents.get(font);
    if (a !== undefined) return a;
    const probe = document.createElement("span"), mark = document.createElement("span");
    probe.style.cssText = `position:absolute;left:0;top:0;white-space:nowrap;line-height:normal;font:${font}`;
    probe.textContent = "Hg";
    mark.style.cssText = "display:inline-block;width:0;height:0;vertical-align:baseline";
    probe.append(mark);
    document.body.append(probe);
    const rg = document.createRange();
    rg.selectNodeContents(probe.firstChild);
    a = mark.getBoundingClientRect().top - rg.getBoundingClientRect().top;
    probe.remove();
    ascents.set(font, a);
    return a;
  }

  // ::before and ::after strings as real spans, so their glyphs have
  // rects like any other text. Done after the printer has planned, with
  // the pseudo-element's own computed style, so nothing moves.
  function materialize(root) {
    const sheet = document.createElement("style");
    sheet.textContent = "[data-tp-before]::before, [data-tp-after]::after { content: none !important; }";
    document.head.append(sheet);
    const jobs = [], counters = new Map();
    // CSS counters, in document order, without nested scopes: enough for
    // numbered clauses.
    const count = (v, set) => {
      if (!v || v === "none") return;
      const t = v.split(/\s+/);
      for (let i = 0; i < t.length; i += 2) counters.set(t[i], (set ? 0 : counters.get(t[i]) ?? 0) + (+t[i + 1] || 0));
    };
    for (const el of root.querySelectorAll("*")) {
      const ecs = getComputedStyle(el);
      count(ecs.counterReset, true);
      count(ecs.counterIncrement, false);
      for (const which of ["before", "after"]) {
        const cs = getComputedStyle(el, "::" + which);
        let c = cs.content;
        if (!c || c === "none" || c === "normal" || cs.display === "none") continue;
        c = c.replace(/counter\((\w[\w-]*)\)/g, (_, n) => JSON.stringify(String(counters.get(n) ?? 0)));
        c = c.replace(/"\s+"/g, "");
        const m = c.match(/^"((?:[^"\\]|\\.)*)"$/);
        if (!m) { console.log(`typeset: unsupported ${which} content ${c} on ${el.className}`); continue; }
        const span = document.createElement("span");
        for (const p of cs) if (p !== "content") span.style.setProperty(p, cs.getPropertyValue(p));
        span.textContent = m[1].replace(/\\(.)/g, "$1");
        span.dataset.tpPseudo = which;
        jobs.push([el, which, span]);
      }
    }
    for (const [el, which, span] of jobs) {
      el.setAttribute("data-tp-" + which, "");
      if (which === "before") el.prepend(span); else el.append(span);
    }
  }

  // ---------------------------------------------------------------- drawings

  // Styles of placed text, written once each as #let sN.
  const styles = new Map();
  function styleOf(cs, el) {
    const fill = colour(cs.color, opacity(el)) ?? "rgb(\"#00000000\")";
    const parts = [`font: (${tstr(family(cs))}, "DejaVu Sans")`, `size: ${f2(parseFloat(cs.fontSize))}pt`,
      `weight: ${Math.round(parseFloat(cs.fontWeight) || 400)}`, `fill: ${fill}`];
    if (cs.fontStyle !== "normal") parts.push(`style: "italic"`);
    const ls = parseFloat(cs.letterSpacing);
    if (ls) parts.push(`tracking: ${f2(ls)}pt`);
    if (/tabular/.test(cs.fontVariantNumeric)) parts.push(`number-width: "tabular"`);
    const key = parts.join(", ");
    let name = styles.get(key);
    if (!name) styles.set(key, (name = "s" + styles.size));
    return name;
  }

  const transform = (s, cs) => cs.textTransform === "uppercase" ? s.toUpperCase()
    : cs.textTransform === "lowercase" ? s.toLowerCase() : s;

  // The runs of a text node: maximal stretches of ink on one line.
  function textItems(t, items, rg) {
    const el = t.parentElement, cs = getComputedStyle(el);
    if (cs.visibility === "hidden" || !t.data) return;
    const data = t.data, style = styleOf(cs, el), asc = ascent(cs);
    let run = null;
    const flush = () => {
      if (!run) return;
      const r = run, text = transform(r.text, cs);
      items.push({ y0: r.top, y1: r.bottom, line: true,
        out: (o) => `#R(${f2(r.left - o.x)}, ${f2(r.top + asc - o.y)}, ${f2(r.right - r.left)}, ${style}, ${tstr(text)})` });
      run = null;
    };
    for (let i = 0; i < data.length; ) {
      const cp = data.codePointAt(i), n = cp > 0xffff ? 2 : 1, ch = data.slice(i, i + n);
      if (/\s/.test(ch) || ch === "\u00ad" || ch === "\u200b") { flush(); i += n; continue; }
      rg.setStart(t, i);
      rg.setEnd(t, i + n);
      const r = rg.getClientRects()[0];
      i += n;
      if (!r || (!r.width && !r.height)) { flush(); continue; }
      if (run && Math.abs(r.top - run.top) < 0.5 && Math.abs(r.left - run.right) < 0.75) {
        run.text += ch;
        run.right = r.right;
        run.bottom = Math.max(run.bottom, r.bottom);
      } else {
        flush();
        run = { text: ch, left: r.left, right: r.right, top: r.top, bottom: r.bottom };
      }
    }
    flush();
  }

  // Lengths of a computed border radius: "3px" or "3.4px 50%".
  function radius(v, w, h) {
    const [a, b = a] = v.split(" ");
    const len = (s, base) => (s.endsWith("%") ? (parseFloat(s) / 100) * base : parseFloat(s) || 0);
    return [len(a, w), len(b, h)];
  }

  function boxItems(el, cs, items) {
    const rects = [...el.getClientRects()];
    if (!rects.length) return;
    const o = opacity(el);
    const side = (s) => ({ w: parseFloat(cs[`border${s}Width`]) || 0, style: cs[`border${s}Style`], c: colour(cs[`border${s}Color`], o) });
    const L = side("Left"), R = side("Right"), T = side("Top"), B = side("Bottom");
    const bg = colour(cs.backgroundColor, o);
    const shown = (s) => s.w > 0 && s.c && s.style !== "none" && s.style !== "hidden";
    // A block's background and rules may be cut at a page break and drawn
    // on both sides; an inline box (a term's bows) holds its lines together.
    const soft = !cs.display.startsWith("inline");
    const add = (y0, y1, out) => items.push({ y0, y1, out, soft });
    rects.forEach((r, i) => {
      if (r.width <= 0 || r.height <= 0) return;
      const first = i === 0, last = i === rects.length - 1;
      const [rx] = radius(cs.borderTopLeftRadius, r.width, r.height);
      const [rxr] = radius(cs.borderTopRightRadius, r.width, r.height);
      const rad = Math.min(rx, r.width / 2, r.height / 2);
      if (bg) add(r.top, r.bottom, (p) => `#F(${f2(r.left - p.x)}, ${f2(r.top - p.y)}, ${f2(r.width)}, ${f2(r.height)}, ${bg}, r: ${f2(rad)})`);
      const all = [L, R, T, B].every((s) => shown(s) && s.w === L.w && s.c === L.c && s.style === L.style);
      if (all && rects.length === 1) {
        add(r.top, r.bottom, (p) => `#S(${f2(r.left - p.x)}, ${f2(r.top - p.y)}, ${f2(r.width)}, ${f2(r.height)}, ${f2(L.w)}, ${L.c}, r: ${f2(rad)}, dash: ${tstr(L.style)})`);
        return;
      }
      // A side border with a bow is a parenthesis: a crescent, thickest
      // at its middle, its ends curving in by the horizontal radius.
      const vertical = (s, x, dir, rr) => {
        if (!shown(s)) return;
        if (s.style === "dotted" || s.style === "dashed")
          add(r.top, r.bottom, (p) => `#V(${f2(x + (dir * s.w) / 2 - p.x)}, ${f2(r.top - p.y)}, ${f2(r.height)}, ${f2(s.w)}, ${s.c}, dash: ${tstr(s.style)})`);
        else if (rr > s.w && !shown(T) && !shown(B))
          add(r.top, r.bottom, (p) => `#P(${f2(x - p.x)}, ${f2(r.top - p.y)}, ${f2(r.height)}, ${f2(Math.min(rr, r.width / 2))}, ${f2(s.w)}, ${dir}, ${s.c})`);
        else add(r.top, r.bottom, (p) => `#F(${f2((dir > 0 ? x : x - s.w) - p.x)}, ${f2(r.top - p.y)}, ${f2(s.w)}, ${f2(r.height)}, ${s.c})`);
      };
      if (first) vertical(L, r.left, 1, rx);
      if (last) vertical(R, r.right, -1, rxr);
      const horizontal = (s, y) => {
        if (!shown(s)) return;
        if (s.style === "dotted" || s.style === "dashed")
          add(y, y + s.w, (p) => `#H(${f2(r.left - p.x)}, ${f2(y + s.w / 2 - p.y)}, ${f2(r.width)}, ${f2(s.w)}, ${s.c}, dash: ${tstr(s.style)})`);
        else add(y, y + s.w, (p) => `#F(${f2(r.left - p.x)}, ${f2(y - p.y)}, ${f2(r.width)}, ${f2(s.w)}, ${s.c})`);
      };
      horizontal(T, r.top);
      horizontal(B, r.bottom - B.w);
      // A list's square brackets: arms drawn as background gradients.
      if (cs.backgroundImage.includes("linear-gradient") && shown(L)) {
        const size = parseFloat(cs.fontSize), armv = cs.getPropertyValue("--bracket-arm").trim();
        const arm = armv.endsWith("em") ? parseFloat(armv) * size : parseFloat(armv) || 0.2 * size;
        const h = L.w, c = L.c;
        const arms = [];
        if (first) arms.push([r.left, r.top], [r.left, r.bottom - h]);
        if (last) arms.push([r.right - arm, r.top], [r.right - arm, r.bottom - h]);
        for (const [x, y] of arms) add(y, y + h, (p) => `#F(${f2(x - p.x)}, ${f2(y - p.y)}, ${f2(arm)}, ${f2(h)}, ${c})`);
      }
    });
  }

  function imageItems(el, items) {
    const r = el.getBoundingClientRect();
    if (!r.width || !r.height || !el.currentSrc.startsWith("file:")) return;
    const path = decodeURIComponent(new URL(el.currentSrc).pathname);
    items.push({ y0: r.top, y1: r.bottom, out: (p) => `#I(${f2(r.left - p.x)}, ${f2(r.top - p.y)}, ${f2(r.width)}, ${f2(r.height)}, ${tstr(path)})` });
  }

  function linkItems(el, items) {
    const url = href(el);
    if (!url || url.startsWith("#")) return;
    for (const r of el.getClientRects()) {
      if (!r.width || !r.height) continue;
      items.push({ y0: r.top, y1: r.bottom, out: (p) => `#A(${f2(r.left - p.x)}, ${f2(r.top - p.y)}, ${f2(r.width)}, ${f2(r.height)}, ${tstr(url)})` });
    }
  }

  function collect(el, items, rg) {
    if (el.nodeType === 3) return textItems(el, items, rg);
    if (el.nodeType !== 1) return;
    const cs = getComputedStyle(el);
    if (cs.display === "none") return;
    if (el.tagName === "IMG") return imageItems(el, items);
    if (el.tagName === "SVG" || el.tagName === "svg") console.log("typeset: an svg is not drawn");
    if (cs.visibility !== "hidden") boxItems(el, cs, items);
    if (el.tagName === "A") linkItems(el, items);
    for (const c of el.childNodes) collect(c, items, rg);
  }

  // A run of drawn blocks as strips Typst may break a page between. A
  // strip ends where nothing drawn crosses from one line to the next;
  // when a strip would be taller than a page, it is cut at a line anyway
  // and what crosses the cut is drawn, clipped, on both sides.
  function drawing(els, origin) {
    const items = [], rg = document.createRange();
    for (const el of els) collect(el, items, rg);
    if (!items.length) return "";
    items.sort((a, b) => a.y0 - b.y0);
    const top = Math.min(...items.map((i) => i.y0)), bottom = Math.max(...items.map((i) => i.y1));
    const gaps = [];
    let reach = -Infinity;
    for (const it of items.filter((i) => !i.soft)) {
      if (reach > -Infinity && it.y0 >= reach - 0.25) gaps.push((reach + it.y0) / 2);
      reach = Math.max(reach, it.y1);
    }
    const lines = [...new Set(items.filter((i) => i.line).map((i) => Math.floor(i.y0)))].sort((a, b) => a - b);
    const max = opts.maxHeight;
    const minStrip = 2.6 * parseFloat(getComputedStyle(document.documentElement).fontSize);
    // A diagram that fits on a page stays whole: its arrows run between
    // its parts.
    if (els.every((e) => e.matches?.(".dg")) && bottom - top <= max) gaps.length = 0;
    const cuts = [top];
    let at = top;
    while (bottom - at > max) {
      const fit = gaps.filter((g) => g > at + minStrip && g <= at + max);
      const forced = lines.filter((l) => l > at + minStrip && l <= at + max);
      const cut = fit.length ? fit[fit.length - 1] : forced.length ? forced[forced.length - 1] : at + max;
      cuts.push(cut);
      at = cut;
    }
    // Within a page's height, every gap is a place to break, but no
    // strip is shorter than two lines or so.
    const all = [top];
    for (let k = 1; k <= cuts.length; k++) {
      const lo = cuts[k - 1], hi = cuts[k] ?? bottom;
      for (const g of gaps) if (g > lo && g < hi && g - all[all.length - 1] >= minStrip && hi - g >= minStrip) all.push(g);
      if (k < cuts.length) all.push(cuts[k]);
    }
    all.push(bottom);
    const strips = [];
    for (let k = 0; k + 1 < all.length; k++) {
      const y0 = all[k], y1 = all[k + 1];
      const inside = items.filter((i) => i.y1 > y0 + 0.01 && i.y0 < y1 - 0.01 || (i.y0 === i.y1 && i.y0 >= y0 && i.y0 < y1));
      const crosses = inside.some((i) => i.y0 < y0 - 0.25 || i.y1 > y1 + 0.25);
      const p = { x: origin, y: y0 };
      strips.push(`  (${f2(y1 - y0)}, ${crosses}, [${inside.map((i) => i.out(p)).join("")}]),`);
    }
    const right = Math.max(...els.map((e) => e.getBoundingClientRect().right));
    if (right - origin > opts.width + 1) console.log(`typeset: a drawing is ${f2(right - origin - opts.width)}pt too wide: ${els[0].className}`);
    return `#drawing((\n${strips.join("\n")}\n))\n\n`;
  }

  // ------------------------------------------------------------------ prose

  let opts, ids;
  function href(a) {
    const h = a.getAttribute("href");
    if (!h) return null;
    if (h.startsWith("#")) return ids.has(h.slice(1)) ? h : null;
    try { return new URL(h, opts.base).href; } catch { return null; }
  }

  const label = (id) => id.replace(/[^A-Za-z0-9_\-:.]/g, "-");

  // Inline content, relative to the block it is in: text in the block's
  // own type is left to the paper's; code, terms and anything coloured or
  // weighted differently keeps its look.
  function inline(n, base, inCode = false) {
    if (n.nodeType === 3) {
      const cs = getComputedStyle(n.parentElement);
      const pre = /^pre/.test(cs.whiteSpace);
      let s = transform(n.data, cs);
      if (!pre) s = s.replace(/[ \t\n\r]+/g, " ");
      if (!s) return "";
      const look = [];
      const fill = colour(cs.color, opacity(n.parentElement));
      // Links in prose are set in the text's colour; code keeps its own.
      if (fill && fill !== base.fill && (inCode || !n.parentElement.closest("a"))) look.push(`fill: ${fill}`);
      if (inCode) {
        look.push(`font: (${tstr(family(cs))}, "DejaVu Sans")`);
        // Sans and mono beside the prose serif are scaled to its x-height
        // (dterm.typ's sans-x and mono-x).
        const ratio = parseFloat(cs.fontSize) / base.size;
        look.push(`size: ${ratio.toFixed(3)}em * ${family(cs) === "DM Mono" ? "mono-x" : "sans-x"}`, "hyphenate: false");
      }
      const w = Math.round(parseFloat(cs.fontWeight));
      if (w !== base.weight) look.push(`weight: ${w}`);
      if (cs.fontStyle !== base.style) look.push(`style: ${tstr(cs.fontStyle === "normal" ? "normal" : "italic")}`);
      if (!look.length && !inCode) return markup(s);
      return `#text(${look.join(", ")}, ${tstr(s)});`;
    }
    if (n.nodeType !== 1) return "";
    const cs = getComputedStyle(n);
    if (cs.display === "none" || cs.visibility === "hidden") return "";
    const tag = n.tagName;
    if (tag === "BR") return "#linebreak();";
    if (tag === "IMG") return "";
    const code = inCode || tag === "CODE" || tag === "KBD" || tag === "SAMP" || n.classList.contains("term");
    let body = [...n.childNodes].map((c) => inline(c, base, code)).join("");
    // A term's parentheses and brackets are its box's side borders.
    const o = opacity(n);
    const side = (s) => (parseFloat(cs[`border${s}Width`]) || 0) > 0 && cs[`border${s}Style`] !== "none" && colour(cs[`border${s}Color`], o);
    if (code && n.parentElement && (side("Left") || side("Right"))) {
      const sq = cs.backgroundImage.includes("linear-gradient") || n.classList.contains("l");
      const glyph = (g, s) => `#text(fill: ${colour(cs[`border${s}Color`], o)}, font: ("Public Sans", "DejaVu Sans"), size: sans-x * 1em, weight: 300, ${tstr(g)});`;
      const pad = `${WJ}#h(${((parseFloat(cs.paddingLeft) || 0) / base.size).toFixed(3)}em);${WJ}`;
      body = (side("Left") ? glyph(sq ? "[" : "(", "Left") + pad : "") + body + (side("Right") ? pad + glyph(sq ? "]" : ")", "Right") : "");
    }
    // Margins (a Rocq application's gap after its head) and the padding of
    // a box drawn as glyphs, in the paragraph's em.
    const em = (v) => (parseFloat(v) || 0) / base.size;
    if (code) {
      const glyphs = n.parentElement && (side("Left") || side("Right"));
      const l = em(cs.marginLeft) + (glyphs ? 0 : em(cs.paddingLeft)), r = em(cs.marginRight) + (glyphs ? 0 : em(cs.paddingRight));
      if (l > 0.01) body = `${WJ}#h(${l.toFixed(3)}em);${WJ}` + body;
      if (r > 0.01) body += `${WJ}#h(${r.toFixed(3)}em);${WJ}`;
    }
    const bg = code && !inCode && colour(cs.backgroundColor, o);
    if (bg) body = `#highlight(fill: ${bg}, radius: 1.5pt, extent: 0.8pt)[${body}];`;
    if (tag === "SUB") body = `#sub[${body}];`;
    if (tag === "SUP") body = `#super[${body}];`;
    if (tag === "A") {
      const h = href(n);
      if (h) body = h.startsWith("#") ? `#link(<${label(h.slice(1))}>)[${body}];` : `#link(${tstr(h)})[${body}];`;
    }
    return body;
  }

  function baseOf(el) {
    const cs = getComputedStyle(el);
    return { fill: colour(cs.color), size: parseFloat(cs.fontSize), weight: Math.round(parseFloat(cs.fontWeight)), style: cs.fontStyle };
  }
  const inlineOf = (el) => [...el.childNodes].map((c) => inline(c, baseOf(el))).join("").trim();

  const PROSE = new Set(["H1", "H2", "H3", "H4", "H5", "H6", "P", "UL", "OL", "BLOCKQUOTE", "HR"]);
  const isProse = (el) => PROSE.has(el.tagName) || el.matches("table.prose-table, aside.sidebar");
  // An element is split into its parts when prose is among them;
  // otherwise it is drawn whole.
  const container = (el) => !isProse(el) && [...el.children].some((c) => isProse(c) || (container(c) && getComputedStyle(c).display !== "none"));

  let title = null;
  function blocks(el, origin) {
    let out = "", pending = [];
    const flush = () => { if (pending.length) out += drawing(pending, origin); pending = []; };
    for (const n of el.childNodes) {
      if (n.nodeType === 3) {
        if (n.data.trim()) { flush(); out += markup(n.data.trim().replace(/\s+/g, " ")) + "\n\n"; }
        continue;
      }
      if (n.nodeType !== 1) continue;
      const cs = getComputedStyle(n);
      if (cs.display === "none" || n.tagName === "SCRIPT" || n.tagName === "STYLE" || n.tagName === "LINK") continue;
      if (!isProse(n) && !container(n)) { if (n.getClientRects().length || cs.display === "contents") pending.push(n); continue; }
      flush();
      out += prose(n, origin);
    }
    flush();
    return out;
  }

  function prose(n, origin) {
    const tag = n.tagName;
    if (/^H[1-6]$/.test(tag)) {
      if (n.classList.contains("source-title") || (tag === "H1" && !title)) { title = n.textContent.trim(); return ""; }
      const level = Math.max(1, +tag[1] - 1);
      return `#heading(level: ${level})[${inlineOf(n)}]${n.id ? ` <${label(n.id)}>` : ""}\n\n`;
    }
    if (tag === "P") { const s = inlineOf(n); return s ? s + "\n\n" : ""; }
    if (tag === "HR") return "#line(length: 100%, stroke: 0.4pt + luma(60%))\n\n";
    if (tag === "UL" || tag === "OL") {
      const items = [...n.children].filter((li) => li.tagName === "LI").map((li) => `[${item(li)}]`);
      const start = tag === "OL" && n.start > 1 ? `start: ${n.start}, ` : "";
      return `#${tag === "OL" ? "enum" : "list"}(${start}${items.join(", ")})\n\n`;
    }
    if (tag === "BLOCKQUOTE") return `#quote(block: true)[${blocks(n, n.getBoundingClientRect().left)}]\n\n`;
    if (n.matches("aside.sidebar")) return `#sidebar[${blocks(n, n.getBoundingClientRect().left)}]\n\n`;
    if (n.matches("table.prose-table")) return table(n);
    return blocks(n, origin);
  }

  // A list item: its text, and any blocks in it.
  function item(li) {
    const blocky = [...li.children].some((c) => isProse(c) || !/^inline/.test(getComputedStyle(c).display));
    if (!blocky) return inlineOf(li);
    let out = "", run = [];
    const flushRun = () => {
      const s = run.map((c) => inline(c, baseOf(li))).join("").trim();
      if (s) out += s + "\n\n";
      run = [];
    };
    const origin = li.getBoundingClientRect().left;
    let draw = [];
    const flushDraw = () => { if (draw.length) out += drawing(draw, origin); draw = []; };
    for (const c of li.childNodes) {
      const inl = c.nodeType !== 1 || /^inline/.test(getComputedStyle(c).display);
      if (inl) { flushDraw(); run.push(c); continue; }
      flushRun();
      if (isProse(c) || container(c)) { flushDraw(); out += prose(c, origin); } else draw.push(c);
    }
    flushRun();
    flushDraw();
    return out.trim();
  }

  function table(t) {
    const rows = [...t.rows];
    const cols = Math.max(...rows.map((r) => [...r.cells].reduce((s, c) => s + c.colSpan, 0)));
    const head = t.tHead ? [...t.tHead.rows] : rows.filter((r) => [...r.cells].every((c) => c.tagName === "TH"));
    const align = [];
    const first = rows.find((r) => !head.includes(r)) ?? rows[0];
    for (const c of first?.cells ?? []) {
      const a = getComputedStyle(c).textAlign;
      align.push(a === "right" || a === "end" ? "right" : a === "center" ? "center" : "left");
    }
    while (align.length < cols) align.push("left");
    const cell = (c) => {
      const s = inlineOf(c);
      return c.colSpan > 1 ? `table.cell(colspan: ${c.colSpan})[${s}]` : `[${s}]`;
    };
    const line = (r) => [...r.cells].map(cell).join(", ");
    const body = rows.filter((r) => !head.includes(r));
    const header = head.length ? `table.header(${head.map(line).join(", ")}),\n` : "";
    return `#prose-table(columns: ${cols}, align: (${align.join(", ")}),\n${header}${body.map((r) => line(r) + ",").join("\n")}\n)\n\n`;
  }

  window.dtermTypst = async (o) => {
    opts = o;
    await document.fonts.ready;
    // dterm.js plans after the fonts load, on a frame; wait until it has
    // and the page has stopped changing.
    for (let i = 0; i < 100 && !document.documentElement.classList.contains("zp"); i++) await sleep(50);
    let last = -1;
    for (let i = 0; i < 40; i++) {
      for (let k = 0; k < 3; k++) await frame();
      const h = document.body.scrollHeight + document.querySelectorAll("br.zbr").length * 1e6;
      if (h === last) break;
      last = h;
      await sleep(100);
    }
    const main = document.querySelector("main") ?? document.body;
    materialize(main);
    ids = new Set([...main.querySelectorAll("h2[id], h3[id], h4[id], h5[id], h6[id]")].map((h) => h.id));
    const origin = main.getBoundingClientRect().left;
    const body = blocks(main, origin);
    const lets = [...styles].map(([k, v]) => `#let ${v} = (${k})`).join("\n");
    return { title: title ?? document.title, typst: lets + "\n\n" + body };
  };
})();
