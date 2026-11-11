# dterm on paper

A PDF of any page the wiki draws: a nanofil document, a Prolog module, a
Rocq file or a Nix file, typeset with Typst.

```sh
nix build --impure -o /tmp/dterm-pdf --expr \
  'import ./nanofil/web/typst/typeset.nix { pkgs = import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }; }'
/tmp/dterm-pdf/bin/dterm-pdf nanofil/docs/lambda-anf.md -o lambda-anf.pdf
/tmp/dterm-pdf/bin/dterm-pdf nanofil/src/ir.pl --profile a4
/tmp/dterm-pdf/bin/dterm-pdf nanofil/rocq/backend/Nfb.v
/tmp/dterm-pdf/bin/dterm-pdf lib/filc-system.nix
```

Run it from the repository root. `--profile` is `remarkable` (the
default: the reMarkable's 157.8 × 210.4 mm screen, grey links), `a5` or
`a4`; `--typ FILE` keeps the Typst source.

Prose is set in Equity when `EQUITY_FONTS` names a directory holding
`EquityOTA-{Regular,Italic,Bold}.otf`, and in Source Serif 4 otherwise;
headings and drawn terms are Public Sans, code DM Mono. Equity is
mbrock's licensed typeface and is never committed:
[deploy/site/equity.sh](../../../deploy/site/equity.sh) fetches it from
the private R2 bucket when the site is published, and puts each
document's PDF beside its page on filnix.org. A document takes about 30 s,
since dterm.pl reads every module to resolve its references; a Rocq or
Nix file takes about a second.

## How

1. `pdf.sh` draws the page as the site build does, into a scratch copy
   of the wiki's layout.
2. `typeset.py` opens it in headless Chromium at the PDF's text width,
   with `print.css`, which hides the web chrome and sets the paper's
   fonts. dterm.js's printer then chooses every term's line breaks for
   that width, exactly as it does for a phone.
3. `extract.js` writes the laid-out page as Typst. Prose (headings,
   paragraphs, lists, prose tables, asides) becomes Typst markup, which
   Typst sets and justifies in Equity, and inline terms keep
   their colours and bows. Everything dterm draws (clauses, Rocq,
   C, diagrams, fact tables) becomes what the browser drew: glyph runs
   at the positions the printer chose, and parentheses, brackets, rules
   and fills as shapes, cut into strips at the gaps between lines so a
   page may break between them. A diagram that fits on one page stays
   whole.
4. `dterm.typ` is the paper: page, running heads, headings, and the
   primitives the strips use. Typst only places what it is given.

The layout search stays out of Typst. Typst's evaluator memoizes every
function call, which made a Pareto frontier search written in Typst
intractable (mbrock/luv's `wiki/typst-prty.typ`, then a WebAssembly
plugin). Here the printer that already runs on every wiki page does the
search, in the browser, and Typst receives its result. That keeps one
printer and one set of layouts for the web and for paper.
