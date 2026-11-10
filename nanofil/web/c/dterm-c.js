// A function's IR link opens the playground on the file, at that
// function's IR (play.js reads #src= and &ir=).
document.addEventListener("click", (event) => {
  const a = event.target.closest("a.c-ir[data-ir]");
  if (!a) return;
  a.href = a.href.replace(/&ir=[^&]*$/, "") + "&ir=" + encodeURIComponent(a.dataset.ir);
});
