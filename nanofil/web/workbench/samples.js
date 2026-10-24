// The no-break spaces dterm.pl writes before wide operators and necks are
// text; v2's flex layout (samples.css) would draw each as an item, so each
// gets a span that layout can hide.
for (const box of document.querySelectorAll(".o, .clause > .head")) {
  for (const n of [...box.childNodes]) {
    if (n.nodeType === Node.TEXT_NODE && n.data === "\u00a0") {
      const s = document.createElement("span");
      s.className = "wb-nbsp";
      n.replaceWith(s);
      s.append(n);
    }
  }
}
