// Hovering a name lights up the binding it refers to and every other use
// of that binding on the page (dterm_nix.pl marks them data-b).
document.addEventListener("mouseover", (event) => {
  const b = event.target.closest("[data-b]");
  for (const lit of document.querySelectorAll(".lit-b")) lit.classList.remove("lit-b");
  if (!b) return;
  for (const w of document.querySelectorAll(`[data-b="${b.dataset.b}"]`)) w.classList.add("lit-b");
});
