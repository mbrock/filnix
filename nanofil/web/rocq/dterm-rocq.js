// On a narrow screen the sidebar comes before the page, so its blocks
// start folded. (dterm.js lights up a variable's uses in its clause.)
if (matchMedia("(max-width: 900px)").matches)
  for (const d of document.querySelectorAll(".rq-nav .nav-block")) d.open = false;

(() => {
  const select = document.querySelector("#rq-layout");
  if (!select) return;
  const root = document.documentElement;
  // Label the Rocq comparison tables when their columns become cards.
  for (const table of document.querySelectorAll(".prose-table:has(code.rq)")) {
    table.classList.add("rq-comparison");
    const labels = [...table.querySelectorAll("th")].map((th) => th.textContent);
    for (const row of table.querySelectorAll("tbody tr"))
      [...row.cells].forEach((cell, i) => { cell.dataset.label = labels[i] || ""; });
  }
  function apply(layout) {
    select.value = layout;
    // dterm.js owns match fitting and term breaking, including after a
    // preference change. No second printer in the Rocq enhancement.
    root.dataset.caseLayout = layout;
  }
  let saved;
  try { saved = localStorage.getItem("dterm-rocq-layout"); } catch { /* private/blocked storage */ }
  apply(["auto", "stack", "table"].includes(saved) ? saved : "auto");
  select.addEventListener("change", () => {
    apply(select.value);
    try { localStorage.setItem("dterm-rocq-layout", select.value); } catch { /* still works this page */ }
  });
  select.closest(".rq-layout").hidden = false;
})();

// Progressive enhancement over build-time, dterm-rendered proof states.
// Without JavaScript every snapshot remains readable in source order.
for (const proof of document.querySelectorAll(".rq-captured")) {
  const links = [...proof.querySelectorAll(".rq-step-link")];
  const states = [...proof.querySelectorAll(".rq-snapshot")];
  const controls = proof.querySelector(".rq-proof-controls");
  const previous = controls.querySelector('[data-move="-1"]');
  const next = controls.querySelector('[data-move="1"]');
  const timeline = proof.querySelector(".rq-timeline");
  const compare = document.createElement("button");
  compare.type = "button";
  compare.className = "rq-compare";
  compare.textContent = "Compare before";
  compare.setAttribute("aria-pressed", "false");
  controls.append(compare);
  let selected = 0;
  let comparing = false;
  let dialog;
  const explorer = proof.querySelector('.rq-explorer');
  const stateList = proof.querySelector('.rq-states');
  // On narrow screens the chosen state follows its tactic in the same
  // scroll flow. display:contents promotes the timeline's ordered rows.
  links.forEach((link, i) => { link.style.order = i * 2; });

  function open() {
    if (!dialog) {
      dialog = document.createElement('dialog');
      dialog.className = 'rq-dialog';
      const heading = document.createElement('header');
      heading.className = 'rq-dialog-head';
      const title = document.createElement('h2');
      title.id = `${proof.id}-title`;
      title.textContent = proof.previousElementSibling?.querySelector('.def')?.textContent || 'Proof';
      title.title = title.textContent;
      dialog.setAttribute('aria-labelledby', title.id);
      heading.append(title);
      if (selectLayout) {
        const layout = selectLayout.cloneNode(true);
        layout.removeAttribute('id');
        layout.setAttribute('aria-label', 'Rocq layout');
        layout.addEventListener('change', () => {
          selectLayout.value = layout.value;
          selectLayout.dispatchEvent(new Event('change'));
        });
        heading.append(layout);
      }
      const close = document.createElement('button');
      close.type = 'button';
      close.textContent = '×';
      close.setAttribute('aria-label', 'Close proof');
      close.addEventListener('click', () => dialog.close());
      heading.append(close, controls);
      dialog.append(heading, explorer);
      proof.append(dialog);
      dialog.addEventListener('click', event => {
        if (event.target.closest('a[href]')) dialog.close();
      });
      dialog.addEventListener('close', () => {
        proof.open = false;
        proof.querySelector(':scope > summary').focus({ preventScroll: true });
      });
    }
    const layout = dialog.querySelector('select');
    if (layout) layout.value = selectLayout.value;
    if (!dialog.open) dialog.showModal();
    show(selected);
    links[selected].focus({ preventScroll: true });
  }
  const selectLayout = document.querySelector('#rq-layout');

  // Compare against the preceding source step, not the last one clicked.
  // These are textual changes in Rocq's output, not semantic equivalence.
  for (let i = 1; i < states.length; i++) {
    const before = states[i - 1].querySelector('.rq-proof-goal[data-role="focused"]');
    const after = states[i].querySelector('.rq-proof-goal[data-role="focused"]');
    if (!before || !after) continue;
    const oldHyps = new Map([...before.querySelectorAll(".rq-hyp")].map(h => [h.dataset.hyp, h.dataset.raw]));
    for (const h of after.querySelectorAll(".rq-hyp")) {
      if (oldHyps.get(h.dataset.hyp) !== h.dataset.raw) {
        const isNew = !oldHyps.has(h.dataset.hyp);
        h.dataset.change = isNew ? "added" : "changed";
        h.title = isNew ? "Added since preceding step" : "Changed since preceding step";
      }
      oldHyps.delete(h.dataset.hyp);
    }
    const conclusion = after.querySelector(".rq-conclusion");
    const goalChanged = conclusion.dataset.raw !== before.querySelector(".rq-conclusion").dataset.raw;
    if (goalChanged) {
      conclusion.dataset.change = "changed";
      conclusion.title = "Changed since preceding step";
    }
    // Additions and rewrites are marked in place; only removals need prose.
    if (oldHyps.size) states[i].querySelector(".rq-changes").textContent =
      `${oldHyps.size} context ${oldHyps.size === 1 ? "entry" : "entries"} removed`;
  }

  function show(index, focus = false) {
    selected = Math.max(0, Math.min(index, states.length - 1));
    for (let i = 0; i < states.length; i++) {
      states[i].hidden = i !== selected && !(comparing && i === selected - 1);
      states[i].classList.toggle("rq-before", comparing && i === selected - 1);
      links[i].setAttribute("aria-current", i === selected ? "step" : "false");
    }
    previous.disabled = selected === 0;
    next.disabled = selected === states.length - 1;
    compare.disabled = selected === 0;
    const position = selected === 0 ? 'Initial goal' : selected === states.length - 1
      ? links[selected].getAttribute('aria-label') : `${selected} / ${states.length - 2}`;
    controls.querySelector(".rq-position").textContent = position;
    controls.querySelector(".rq-position").setAttribute("aria-label", selected > 0 && selected < states.length - 1
      ? `Tactic ${selected} of ${states.length - 2}` : position);
    stateList.style.order = selected * 2 + 1;
    if (focus) links[selected].focus({ preventScroll: true });
    // dterm.js's ResizeObserver remeasures newly visible clauses.
    // Only the dialog scrolls; the underlying source stays where it was.
    if (dialog?.open) requestAnimationFrame(() => requestAnimationFrame(() => {
      links[selected].scrollIntoView({ block: getComputedStyle(timeline).display === 'contents' ? 'start' : 'nearest' });
    }));
  }
  links.forEach((link, i) => link.addEventListener("click", () => show(i)));
  controls.addEventListener("click", event => {
    const move = event.target.closest("[data-move]");
    if (move) show(selected + Number(move.dataset.move));
  });
  compare.addEventListener("click", () => {
    comparing = !comparing;
    compare.setAttribute("aria-pressed", String(comparing));
    show(selected);
  });
  timeline.addEventListener("keydown", event => {
    const move = { ArrowDown: 1, ArrowRight: 1, ArrowUp: -1, ArrowLeft: -1 }[event.key];
    if (!move && event.key !== "Home" && event.key !== "End") return;
    event.preventDefault();
    show(event.key === "Home" ? 0 : event.key === "End" ? states.length - 1 : selected + move, true);
  });
  controls.hidden = false;
  timeline.hidden = false;
  show(0);
  proof.addEventListener("toggle", () => {
    if (proof.open) open();
    else if (dialog?.open) dialog.close();
  });
}
