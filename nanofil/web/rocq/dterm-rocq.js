// On a narrow screen the sidebar comes before the page, so its blocks
// start folded. (dterm.js lights up a variable's uses in its clause.)
if (matchMedia("(max-width: 900px)").matches)
  for (const d of document.querySelectorAll(".rq-nav .nav-block")) d.open = false;

(() => {
  const select = document.querySelector("#rq-layout");
  if (!select) return;
  const root = document.documentElement;
  const help = document.querySelector("#rq-layout-help");
  const descriptions = {
    auto: "Fits each block to its available width.",
    stack: "Patterns above results; comments below code.",
    table: "Aligned columns; wide blocks scroll locally.",
  };
  // Label the Rocq comparison tables when their columns become cards.
  for (const table of document.querySelectorAll(".prose-table:has(code.rq)")) {
    table.classList.add("rq-comparison");
    const labels = [...table.querySelectorAll("th")].map((th) => th.textContent);
    for (const row of table.querySelectorAll("tbody tr"))
      [...row.cells].forEach((cell, i) => { cell.dataset.label = labels[i] || ""; });
  }
  function apply(layout) {
    select.value = layout;
    help.textContent = descriptions[layout];
    // dterm.js owns match fitting and term breaking, including after a
    // preference change. No second printer in the Rocq enhancement.
    root.dataset.caseLayout = layout;
  }
  let saved;
  try { saved = localStorage.getItem("dterm-rocq-layout"); } catch { /* private/blocked storage */ }
  apply(Object.hasOwn(descriptions, saved) ? saved : "auto");
  select.addEventListener("change", () => {
    apply(select.value);
    try { localStorage.setItem("dterm-rocq-layout", select.value); } catch { /* still works this page */ }
  });
  select.closest(".rq-layout").hidden = false;
})();
