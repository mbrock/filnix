// Shared by the playground and the workbench. The renderer owns raw
// temporary identities; pretty text (including SSA subscripts) is display only.
export function gloss(ir) {
  if (!ir) return;
  const words = new Map([...ir.querySelectorAll(".legend .word")].map((w) => [w.dataset.key, w]));
  const used = new Set();
  const note = (el, key, target = el) => {
    const w = words.get(key);
    if (!w) return false;
    if (!target.title) target.title = w.dataset.tip;
    target.classList.add("w-" + w.dataset.role);
    used.add(w);
    return true;
  };
  for (const c of ir.querySelectorAll(".c")) {
    const f = c.firstElementChild;
    const args = [...(c.querySelector(":scope > .args")?.children ?? [])].filter((a) => a.matches(".arg"));
    const key = `${f.textContent}/${args.length}`;
    note(f, key, c);
    for (const s of words.get(key)?.dataset.slots.split(" ").filter(Boolean) ?? []) {
      const [i, kind] = s.split(":");
      const a = args[i - 1]?.firstElementChild;
      if (a?.matches(".a")) note(a, `${kind}:${a.textContent}`) ||
        (kind === "type" && note(a, `class:${a.textContent}`));
    }
  }
  for (const value of ir.querySelectorAll("[data-tmp]")) note(value, "tmp/1");
  for (const a of ir.querySelectorAll(".goal > .a")) note(a, `${a.textContent}/0`);
  for (const w of words.values()) w.hidden = !used.has(w);
  for (const r of ir.querySelectorAll(".legend .role")) r.hidden = !r.querySelector(".word:not([hidden])");
}

export function highlightValues(root) {
  const clear = () => {
    for (const el of root.querySelectorAll("[data-tmp].lit")) el.classList.remove("lit");
  };
  root.addEventListener("pointerover", (e) => {
    clear();
    const t = e.target.closest("[data-tmp]");
    if (!t) return;
    const fn = t.closest("details.clause.func");
    if (!fn) return;
    for (const el of fn.querySelectorAll("[data-tmp]")) {
      if (el.dataset.tmp === t.dataset.tmp) el.classList.add("lit");
    }
  });
  root.addEventListener("pointerleave", clear);
}
