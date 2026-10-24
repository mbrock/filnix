// The dterm workbench: two frames of samples.html, each with its own type.
// A knob is a CSS custom property or a data attribute on the frame's root
// element; a preset is a set of knob values, and anything a preset leaves
// out is what dterm.css says.

const knobs = [
  { group: "Layout" },
  { id: "layout", label: "Terms", attr: "layout", options: [["text", "flow as text"], ["flex", "v2: boxes that wrap"]] },
  { id: "planner", label: "Line breaks", attr: "planner", options: [["on", "planned to fit (dterm.js)"], ["off", "dterm.pl's: by length"]] },
  { id: "long", label: "By length: break a term longer than", attr: "long", options: [["48", "48 characters"], ["60", "60 characters"], ["72", "72 characters"], ["80", "80 characters"], ["90", "90 characters"], ["0", "never"]], initial: "80" },
  { id: "hang", label: "Hanging indent", prop: "--hang", min: 0, max: 3, step: 0.1, unit: "em" },
  { id: "size", label: "Size of clauses", prop: "--wb-size", min: 0.8, max: 1.15, step: 0.01, unit: "rem", initial: 0.95 },
  { group: "Parentheses" },
  { id: "parens", label: "Drawn as", attr: "parens", options: [["border", "hairline borders"], ["glyph", "the font's glyphs"]] },
  { id: "paren-ink", label: "Ink", prop: "--paren-ink", min: 5, max: 100, step: 1, unit: "%" },
  { id: "paren-stroke", label: "Stroke", prop: "--paren-stroke", min: 0.03, max: 0.15, step: 0.005, unit: "em" },
  { id: "paren-curve", label: "Bow", prop: "--paren-curve", min: 0, max: 0.6, step: 0.01, unit: "em" },
  { id: "paren-inside", label: "Space inside", prop: "--paren-inside", min: 0, max: 0.45, step: 0.01, unit: "em" },
  { id: "paren-outside", label: "Space after the functor", prop: "--paren-outside", min: 0, max: 0.25, step: 0.01, unit: "em" },
  { id: "paren-grow", label: "Growth per level inside", prop: "--paren-grow", min: 0, max: 0.12, step: 0.005, unit: "em" },
  { group: "Brackets and bars" },
  { id: "brackets", label: "Brackets", attr: "brackets", options: [["arms", "square, with arms"], ["box", "v2: rounded boxes"], ["paren", "like parentheses"]] },
  { id: "bracket-arm", label: "Arm", prop: "--bracket-arm", min: 0, max: 0.45, step: 0.01, unit: "em" },
  { id: "bracket-ink", label: "Bracket ink", prop: "--bracket-ink", min: 10, max: 100, step: 1, unit: "%" },
  { id: "bar-space", label: "Space around |", prop: "--bar-space", min: 0, max: 0.35, step: 0.01, unit: "em" },
  { group: "Commas and operators" },
  { id: "sep-ink", label: "Comma ink", prop: "--sep-ink", min: 10, max: 100, step: 1, unit: "%" },
  { id: "sep-weight", label: "Comma weight", prop: "--wb-sep-weight", min: 300, max: 800, step: 50, unit: "", initial: 400 },
  { id: "arg-space", label: "Space after a comma (± word space)", prop: "--wb-arg-space", min: -0.15, max: 0.3, step: 0.01, unit: "em", initial: 0 },
  { id: "op-space", label: "Space around operators (± word space)", prop: "--wb-op-space", min: -0.15, max: 0.3, step: 0.01, unit: "em", initial: 0 },
];

// Presets: what each changes from dterm.css.
const presets = {
  dterm: { name: "dterm (as published)", values: {} },
  v2: { name: "v2, before this", values: { layout: "flex", planner: "off", long: "0", brackets: "box" } },
  quiet: { name: "quieter", values: { "paren-ink": 22, "paren-stroke": 0.055, "sep-ink": 38, "bracket-ink": 45 } },
  firm: { name: "firmer", values: { "paren-ink": 52, "paren-stroke": 0.085, "sep-ink": 72, "sep-weight": 500 } },
  glyph: { name: "glyph parentheses", values: { parens: "glyph", "paren-ink": 48, "paren-inside": 0.02 } },
  loose: { name: "loose, as the mockup", values: { "paren-inside": 0.3, "arg-space": 0.1, "paren-grow": 0, "sep-ink": 60 } },
  tight: { name: "tight", values: { "paren-inside": 0.06, "paren-outside": 0, "arg-space": -0.05, "op-space": -0.06 } },
  flat: { name: "no growth, no bow", values: { "paren-grow": 0, "paren-curve": 0.12 } },
};

const state = { a: { preset: "v2", values: {} }, b: { preset: "dterm", values: {} } };
const frames = {};
let which = "b";

function frameDoc(f) { return frames[f]?.contentDocument; }

// The value dterm.css gives a knob, read from a frame.
function base(k, f) {
  const doc = frameDoc(f);
  if (k.initial !== undefined) return String(k.initial);
  if (k.attr) return k.options[0][0];
  if (!doc) return "";
  return parseFloat(getComputedStyle(doc.documentElement).getPropertyValue(k.prop)) + "";
}

function value(k, f) {
  const s = state[f];
  if (k.id in s.values) return String(s.values[k.id]);
  const p = presets[s.preset].values;
  if (k.id in p) return String(p[k.id]);
  return base(k, f);
}

function apply(f) {
  const doc = frameDoc(f);
  if (!doc || !doc.documentElement) return;
  const root = doc.documentElement;
  for (const k of knobs) {
    if (!k.id) continue;
    const v = value(k, f);
    if (k.attr) root.dataset[k.attr] = v;
    else if (v !== "" && (k.id in state[f].values || k.id in presets[state[f].preset].values || k.initial !== undefined)) root.style.setProperty(k.prop, v + k.unit);
    else root.style.removeProperty(k.prop);
  }
  document.querySelector(`.wb-frame[data-frame="${f}"] .wb-name`).textContent =
    presets[state[f].preset].name + (Object.keys(state[f].values).length ? ", tuned" : "");
  if (f === which) showCss();
}

function showCss() {
  const lines = [];
  for (const k of knobs) {
    if (!k.id) continue;
    const v = value(k, which);
    if (v === base(k, which)) continue;
    lines.push(k.attr ? `/* ${k.label.toLowerCase()}: ${v} */` : `  ${k.prop}: ${v}${k.unit};`);
  }
  document.getElementById("css").textContent =
    lines.length ? `:root {\n${lines.filter((l) => l.startsWith("  ")).join("\n")}\n}\n${lines.filter((l) => !l.startsWith("  ")).join("\n")}`.trim()
                 : "/* dterm.css as published */";
}

function render() {
  const box = document.getElementById("knobs");
  box.replaceChildren();
  for (const k of knobs) {
    if (k.group) {
      const h = document.createElement("h3");
      h.textContent = k.group;
      box.append(h);
      continue;
    }
    const row = document.createElement("label");
    row.className = "wb-row";
    row.append(k.label);
    let input;
    if (k.options) {
      input = document.createElement("select");
      for (const [v, t] of k.options) input.append(new Option(t, v));
    } else {
      input = document.createElement("input");
      Object.assign(input, { type: "range", min: k.min, max: k.max, step: k.step });
      const out = document.createElement("output");
      row.append(out);
      input.addEventListener("input", () => { out.textContent = input.value + k.unit; });
      input.output = out;
    }
    input.value = value(k, which);
    if (input.output) input.output.textContent = input.value + k.unit;
    input.addEventListener("input", () => {
      state[which].values[k.id] = input.value;
      apply(which);
    });
    row.append(input);
    box.append(row);
  }
  document.getElementById("preset").value = state[which].preset;
  showCss();
}

function setupPresets() {
  const sel = document.getElementById("preset");
  for (const [id, p] of Object.entries(presets)) sel.append(new Option(p.name, id));
  sel.addEventListener("change", () => {
    state[which] = { preset: sel.value, values: {} };
    apply(which);
    render();
  });
  for (const r of document.querySelectorAll('input[name="which"]')) {
    r.addEventListener("change", () => { which = r.value; markWhich(); render(); });
  }
  document.getElementById("copy").addEventListener("click", () => {
    navigator.clipboard?.writeText(document.getElementById("css").textContent);
  });
}

function markWhich() {
  for (const fig of document.querySelectorAll(".wb-frame")) fig.classList.toggle("tuning", fig.dataset.frame === which);
}

// The visible variant of each sample in a frame, for jumping and for
// scrolling the two frames together sample by sample.
function blocks(f) {
  const doc = frameDoc(f);
  return doc ? [...doc.querySelectorAll(".wb-v")].filter((e) => e.offsetParent !== null || e.getClientRects().length) : [];
}

function headings(f) {
  const doc = frameDoc(f);
  return doc ? [...doc.querySelectorAll("article.wb > h2")] : [];
}

let syncing = false;
function follow(from, to) {
  if (syncing || !document.getElementById("sync").checked) return;
  const a = blocks(from), b = blocks(to);
  const win = frames[from].contentWindow, y = win.scrollY;
  let i = 0;
  while (i + 1 < a.length && a[i + 1].offsetTop - 40 <= y) i++;
  if (!a[i] || !b[i]) return;
  const frac = Math.min(1, Math.max(0, (y - a[i].offsetTop + 40) / Math.max(1, a[i].offsetHeight)));
  syncing = true;
  frames[to].contentWindow.scrollTo(0, b[i].offsetTop - 40 + frac * b[i].offsetHeight);
  requestAnimationFrame(() => { syncing = false; });
}

function setWidth() {
  const v = document.getElementById("width").value;
  document.querySelector(".wb-frames").dataset.width = v;
  for (const fig of document.querySelectorAll(".wb-frame")) fig.style.setProperty("--w", v === "fill" ? "" : v + "px");
}

function setupJump() {
  const sel = document.getElementById("jump");
  headings("a").forEach((h, i) => sel.append(new Option(h.textContent, i)));
  sel.addEventListener("change", () => {
    for (const f of ["a", "b"]) {
      const h = headings(f)[sel.value];
      if (h) frames[f].contentWindow.scrollTo(0, h.offsetTop - 8);
    }
  });
}

let loaded = 0;
function ready(f) {
  apply(f);
  frames[f].contentWindow.addEventListener("scroll", () => follow(f, f === "a" ? "b" : "a"), { passive: true });
  if (++loaded === 2) { setupJump(); render(); }
}
for (const fig of document.querySelectorAll(".wb-frame")) {
  const f = fig.dataset.frame;
  frames[f] = fig.querySelector("iframe");
  const doc = frames[f].contentDocument;
  if (doc && doc.readyState === "complete" && doc.querySelector("article.wb")) ready(f);
  else frames[f].addEventListener("load", () => ready(f), { once: true });
}
document.getElementById("width").addEventListener("change", setWidth);
setupPresets();
markWhich();
setWidth();
