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
