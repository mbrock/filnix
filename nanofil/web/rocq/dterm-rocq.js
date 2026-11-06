// On a narrow screen the sidebar comes before the page, so its blocks
// start folded. (dterm.js lights up a variable's uses in its clause.)
if (matchMedia("(max-width: 900px)").matches)
  for (const d of document.querySelectorAll(".rq-nav .nav-block")) d.open = false;
