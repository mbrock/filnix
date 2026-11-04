// Hovering a name lights up the binding it refers to and every other use
// of that binding on the page (dterm_nix.pl marks them data-b).
document.addEventListener("mouseover", (event) => {
  const b = event.target.closest("[data-b]");
  for (const lit of document.querySelectorAll(".lit-b")) lit.classList.remove("lit-b");
  if (!b) return;
  for (const w of document.querySelectorAll(`[data-b="${b.dataset.b}"]`)) w.classList.add("lit-b");
});

// A port list's filter: show the ports whose name, package or verbs
// contain every word typed.
const portFilter = document.getElementById("port-filter");
if (portFilter) {
  const apply = () => {
    const words = portFilter.value.toLowerCase().split(/\s+/).filter(Boolean);
    const shows = (text) => words.every((w) => text.toLowerCase().includes(w));
    for (const row of document.querySelectorAll("tr.port-row"))
      row.classList.toggle("port-hidden", !shows(row.dataset.find));
    for (const group of document.querySelectorAll(".index-group"))
      group.classList.toggle("port-hidden", !group.querySelector("tr.port-row:not(.port-hidden)"));
  };
  portFilter.addEventListener("input", apply);
}
