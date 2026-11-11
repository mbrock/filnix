// The paper for a dterm page (typeset.py, extract.js). Prose arrives as
// Typst markup and is set here; drawings arrive already laid out, as
// strips of glyph runs and shapes at the positions the browser's printer
// chose, and are only placed. Every length is in pt.

#let ink = rgb("#1b1b1b")
#let muted = rgb("#5f666c")
#let accent = rgb("#9a3248")
#let rule = rgb("#cfc8bc")

// Public Sans terms and DM Mono code set inside prose, scaled so their
// x-height sits with the serif's rather than towering over it.
#let sans-x = 0.86
#let mono-x = 0.9

// A run of glyphs, its baseline at (x, y). w is the width the browser
// measured; the box is a little wider so the same font never wraps it.
#let R(x, y, w, s, t) = place(top + left, dx: x * 1pt, dy: y * 1pt,
  box(width: w * 1pt + 8pt, text(..s, top-edge: "baseline", bottom-edge: "baseline",
    hyphenate: false, t)))

// A filled rectangle, and a stroked one.
#let F(x, y, w, h, c, r: 0) = place(top + left, dx: x * 1pt, dy: y * 1pt,
  rect(width: w * 1pt, height: h * 1pt, fill: c, stroke: none, radius: r * 1pt))
#let S(x, y, w, h, sw, c, r: 0, dash: "solid") = place(top + left,
  dx: (x + sw / 2) * 1pt, dy: (y + sw / 2) * 1pt,
  rect(width: (w - sw) * 1pt, height: (h - sw) * 1pt, radius: r * 1pt,
    stroke: (paint: c, thickness: sw * 1pt, dash: if dash == "solid" { none } else { dash })))

// Dotted or dashed rules.
#let V(x, y, h, sw, c, dash: "dotted") = place(top + left, dx: x * 1pt, dy: y * 1pt,
  line(start: (0pt, 0pt), end: (0pt, h * 1pt), stroke: (paint: c, thickness: sw * 1pt, dash: dash)))
#let H(x, y, w, sw, c, dash: "dotted") = place(top + left, dx: x * 1pt, dy: y * 1pt,
  line(start: (0pt, 0pt), end: (w * 1pt, 0pt), stroke: (paint: c, thickness: sw * 1pt, dash: dash)))

// A parenthesis: the crescent a side border with an elliptical radius
// draws. x is the border's outer edge, dir 1 for an opening one and -1
// for a closing one, rr how far its ends bow in, sw its stroke at the
// middle.
#let P(x, y, h, rr, sw, dir, c) = {
  let k = 0.5523
  let m = h / 2
  let ri = calc.max(rr - sw, 0)
  let pt(a, b) = ((x + dir * a) * 1pt, (y + b) * 1pt)
  place(top + left, curve(fill: c, stroke: none,
    curve.move(pt(rr, 0)),
    curve.cubic(pt(rr - k * rr, 0), pt(0, m - k * m), pt(0, m)),
    curve.cubic(pt(0, m + k * m), pt(rr - k * rr, h), pt(rr, h)),
    curve.line(pt(rr, h)),
    curve.cubic(pt(rr - k * ri, h), pt(sw, m + k * m), pt(sw, m)),
    curve.cubic(pt(sw, m - k * m), pt(rr - k * ri, 0), pt(rr, 0)),
    curve.close()))
}

#let I(x, y, w, h, path) = place(top + left, dx: x * 1pt, dy: y * 1pt,
  image(path, width: w * 1pt, height: h * 1pt))
#let A(x, y, w, h, url) = place(top + left, dx: x * 1pt, dy: y * 1pt,
  link(url, box(width: w * 1pt, height: h * 1pt)))

// A drawing: strips of (height, clipped, content), between which a page
// may break.
#let drawing(strips) = {
  let n = strips.len()
  for (i, (h, clip, body)) in strips.enumerate() {
    block(width: 100%, height: h * 1pt, breakable: false, clip: clip,
      above: if i == 0 { 0.55em } else { 0pt },
      below: if i == n - 1 { 0.7em } else { 0pt }, body)
  }
}

#let sidebar(body) = block(width: 100%, inset: (left: 0.9em, y: 0.2em),
  stroke: (left: 1.2pt + rule), above: 0.9em, below: 0.9em, body)

#let prose-table(columns: 1, align: left, ..cells) = {
  set text(size: 0.84em)
  set par(justify: false, leading: 0.45em)
  block(width: 100%, above: 0.9em, below: 1em, table(
    columns: columns,
    align: align,
    inset: (x: 0.35em, y: 0.36em),
    stroke: (x, y) => if y == 0 { (top: 0.8pt + ink, bottom: 0.5pt + ink) },
    ..cells.pos(),
    table.hline(stroke: 0.8pt + ink),
  ))
}

#let dterm-paper(
  title: none, source: none, url: none,
  paper: (width: 157.8mm, height: 210.4mm),
  margin: (top: 13mm, right: 12mm, bottom: 15mm, left: 12mm),
  body-size: 11pt, prose-font: ("Source Serif 4",), grey: false, body,
) = {
  let hue = if grey { ink } else { accent }
  set document(title: title)
  set page(width: paper.width, height: paper.height, margin: margin,
    header: context {
      if here().page() > 1 {
        set text(font: ("Public Sans", "DejaVu Sans"), size: 6.8pt, fill: muted, weight: 500)
        title.split(":").first()
        h(1fr)
        let hs = query(selector(heading.where(level: 1)).before(here()))
        if hs.len() > 0 { hs.last().body }
      }
    },
    footer: context {
      set text(font: ("Public Sans", "DejaVu Sans"), size: 6.8pt, fill: muted, weight: 500)
      h(1fr)
      counter(page).display()
      h(1fr)
    })
  set text(font: (..prose-font, "DejaVu Sans"), size: body-size, fill: ink,
    lang: "en", number-width: "proportional", hyphenate: true)
  set par(justify: true, leading: 0.6em, spacing: 1.05em, linebreaks: "optimized")
  show link: set text(fill: if grey { ink } else { hue.darken(10%) })
  set list(indent: 0.4em, body-indent: 0.5em, spacing: 0.75em, marker: text(fill: muted, [•]))
  set enum(indent: 0.2em, body-indent: 0.5em, spacing: 0.75em)
  show heading: set text(font: ("Public Sans", "DejaVu Sans"), fill: ink, hyphenate: false)
  show heading: set par(justify: false)
  show heading.where(level: 1): it => {
    set text(size: body-size * 1.3, weight: 800, tracking: -0.02em)
    block(above: 1.9em, below: 0.75em, sticky: true, it.body)
  }
  show heading.where(level: 2): it => {
    set text(size: body-size * 1.08, weight: 700)
    block(above: 1.4em, below: 0.6em, sticky: true, it.body)
  }
  show heading.where(level: 3): it => {
    set text(size: body-size * 0.98, weight: 700, fill: muted)
    block(above: 1.1em, below: 0.5em, sticky: true, it.body)
  }
  show quote.where(block: true): it => block(inset: (left: 0.9em), stroke: (left: 1.2pt + rule), it.body)

  // Title block.
  block(below: 1.4em, {
    set par(justify: false)
    if source != none {
      text(font: ("Public Sans", "DejaVu Sans"), size: 7pt, weight: 700, fill: hue, tracking: 0.06em, source)
      v(0.3em)
    }
    text(font: ("Public Sans", "DejaVu Sans"), size: body-size * 1.9, weight: 800, tracking: -0.035em, hyphenate: false, title)
    if url != none {
      v(0.15em)
      text(font: ("Public Sans", "DejaVu Sans"), size: 7pt, fill: muted, link(url, url))
    }
  })
  body
}
