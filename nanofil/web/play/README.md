# nanofil in the browser

nanofil compiles C in a web page, on SWI-Prolog 10.1.19 in WebAssembly,
and the page draws what it made with dterm. It is published with the wiki
at [nanofil/play/](https://mbrock.github.io/filnix/nanofil/play/), in the
wiki's palette and stylesheets. Paste C, press Compile (or Ctrl+Enter),
and the page shows, from one `<article>` whose sections it puts in place:

- beside the source, a dot and the time; it opens on the stages
  (profile, preprocess, parse, lower, validate, each selected optimization,
  pizlonate, print IR, backend, print assembly) with their times and the memory. A stage that
  fails names itself there, says why above the tabs, and marks the line
  in the gutter;
- the output as a pipeline: each pass's output is a tab, and before it
  stands the pass that made it, with its time: parse → **C syntax**
  (`c_parse/2`, the input's own items, not the header declarations) →
  lower → **IR** (as `c_lower.pl` made it) → promote → **promoted IR**
  → copy → **copies folded** → local_storage → **local storage**
  → pizlonate → **checked IR** (after
  `pizlonate.pl` has made Fil-C's checks and pollchecks explicit, the
  module the backend compiles; see
  [docs/pizlonation.md](../../docs/pizlonation.md)) → amd64 →
  **assembly** (each `asm.pl` line term beside the AT&T line it prints
  as; the first 1500 lines, longer listings follow as text), and at
  the end **text**, the checked IR as the clauses `nanofil print` and
  `compile` read (`src/ir_text.pl`). In the checked IR the rows
  pizlonation wrote are marked at the left.
  An IR is a function as its head over its blocks, a block as its label
  over one row per phi, instruction and jump, each function and data
  object folding under its head, and a run of text bytes drawn as the
  one `item(b, str(S))` it means. Over each IR, "How to read the IR"
  explains each word the module uses (`play_view.pl`'s `gloss/4`), and
  every word in the IR is coloured by its role (instruction, memory,
  Fil-C check, jump, value) and says what it means on hover, a class or
  op atom by its place (`slot/2`); hovering a temporary lights up its
  definition and uses. Without -O each row's source line is beside it;
  the editor tints the numbers of the lines that made IR, and the
  cursor's line rules its rows in every IR;
- **Data**, each data object's bytes as hex and text, pointers as the
  symbols they point at;
- **Symbols**, what the module defines (name, kind, IR signature or size,
  linkage) and what it calls or uses without defining. A name opens the
  IR tab at its definition.

The three **Optimization passes** checkboxes select promotion, copy
elimination and local storage independently; **-O** selects all or none
and shows a mixed state for a partial selection. Press **Compile** to
apply the selection. Only selected passes add output tabs. If the tab
being read disappears, the page returns to checked IR. The order stays
promotion → copy → local storage, with pizlonation always afterwards.

**Check evidence → Check reuse** runs `check_reuse:reuse_checks/2` after
pizlonation ([docs/m7.md](../../docs/m7.md)) and adds a **reused checks**
tab after checked IR: the module the backend then compiles, accepted by
`reuse_refines/2` and `valid_module/1` as `cc --checks=reuse` accepts it.
Accesses there may read an earlier proof in their block; the text and
assembly tabs show that module.

The page and compiler share `opt:optimization_passes/2` and
`opt:optimize_pass/3`; the page records the actual intermediate modules,
not separately reconstructed examples. `optimize(passes([copy]), M0, M)`
runs copy elimination alone; `o0` and `o1` retain their existing outputs.
Each playground pass also validates its output (included in its time).
Checked and already-local modules keep the optimizer's identity bypass.
Pass algorithms and the one-check-per-access safety contract are unchanged.

The [semantic campaign](../../docs/campaign.md) gives this view a longer-term
role: inspect an access's requirements and the evidence that discharges
them. A future check-reuse pass should expose its real result and reasons
here, including obligations left to runtime checks. That evidence must be
a compiler product, not an analysis independently reconstructed by the UI.
The reused checks tab shows which proof each access reads, but not yet
why a remaining check was kept; it does not certify transformations.

```sh
nix build .#site -o /tmp/site
python3 -m http.server -d /tmp/site    # then open /nanofil/play/
```

The page loads `../../style.css` and `../dterm.css` from the wiki, so it
is served from the site build; `nix build -f nanofil/web/play` builds its
own files alone.

## One SWI-Prolog

The npm package `swipl-wasm` 8.2.5 is SWI-Prolog 10.1.19 (its
`build-config.json`; `current_prolog_flag(version, V)` gives 100119).
`swipl.nix` builds the same release natively from swipl-devel, so the
frozen profile, the bundle and the browser run one SWI, and
`packages/site` draws the dterm pages with it too. Nixpkgs has 9.2.9.

Nothing here changes nanofil: the bundle copies `src/` and adds the
driver beside it.

## How it fits together

| file | role |
|---|---|
| `play.pl` | `play/3`: one file through the pipeline, each stage timed and caught. Both hosts. |
| `play_view.pl` | `play_html/3`: the article, drawn with dterm's `term//4`. SWI only, like dterm. |
| `load_swi.pl` | loads dterm and the view, then `src/swi/compat.pl`, nanofil and `play.pl`. |
| `profile.pl` | freezes `pp_profile/2`'s answer for filcc (macros, include path, feature answers). |
| `headers.c` | the headers the page ships: whatever these 26 standard includes reach, by `clang -M` (155 files, 0.7 MB). |
| `wasm/process.pl` | a `library(process)` stub: `c_pp.pl` loads the library for `pp_profile/2`, which a browser cannot run. |
| `build.sh` | assembles the site; `fs.json` maps each virtual path to its text. |
| `worker.js`, `play.js`, `index.html`, `play.css` | swipl-wasm in a Web Worker, and the page. |
| `bench.mjs` | the pipeline under Node on swipl-wasm, trealla-js or `tpl.wasm`, with time and wasm memory. |
| `trealla-wasm.nix` | Trealla as a WASI command, at nanofil's pinned revision with filnix's patches. |

The preprocessor is the only part of nanofil that talks to the outside
world (it asks clang for its macros, search path and `__has_*`
answers), so the browser gets that answer frozen. A `__has_*` query
outside the frozen batch would call clang and fails with the stub's
error; none of the shipped headers makes one. A header outside the
bundle fails as `include_not_found`.

## Which Prolog

All four hosts give byte-identical IR text and assembly, also identical
to `bin/nanofil cc`, on every input where they finish. Hello world is
`#include <stdio.h>` and a `printf`. `more.c` is `tests/c/more.c`
(153 lines, no includes). "26 headers" is `headers.c` with an empty
`main`, which is mostly preprocessing. Wasm numbers are under Node 26
(V8); swipl-wasm's are the steady state after loading, while
`tpl.wasm` includes loading nanofil each run (about 0.5 s).

| input | native SWI 9.2.9 | native Trealla | swipl-wasm (SWI 10.1.19) | Trealla `tpl.wasm` |
|---|---|---|---|---|
| hello world | 0.64 s, 55 MB | 1.76 s, 488 MB | 0.36 s, 106 MB | 2.7 s, 1066 MB |
| more.c `-O0` | 0.41 s, 37 MB | 0.89 s, 274 MB | 0.15 s, 44 MB | 1.3 s, 298 MB |
| more.c `-O1` | 0.46 s, 29 MB | 0.86 s, 228 MB | 0.15 s, 27 MB | 1.1 s, 298 MB |
| 26 headers | 3.1 s, 317 MB | 11.6 s, 3.4 GB | 2.6 s, 628 MB | 14.3 s, 3.77 GB, no output |

Native times include process start and loading; memory is peak RSS
natively and the WebAssembly memory size in wasm, which never shrinks.

- **swipl-wasm** (npm `swipl-wasm`, 2.3 MB wasm and a 1.7 MB library
  image) runs the whole pipeline after one change: a stub for
  `library(process)`, which the build lacks. Loading nanofil takes about
  0.6 s. Preprocessing dominates (hello world spends 0.3 to 0.45 s
  reading the 29 headers that `stdio.h` reaches).
- **trealla-js 0.30.1** (npm `trealla`) loads nanofil but traps with
  "RuntimeError: function signature mismatch" as soon as a goal such as
  `catch((call(c_parse(T, I)), R = ok), E, R = error(E))` runs over real tokens; each
  stage alone succeeds. It is also built without filnix's Trealla
  patches, one of which (`trealla-runtime-atom-arity-unify`) fixes
  unification that nanofil relies on.
- **Trealla `tpl.wasm`** at nanofil's pinned revision with the patches
  (`trealla-wasm.nix`, 2.1 MB) runs everything correctly, at 5 to 10x
  swipl-wasm's time and 3 to 10x its memory. Hello world needs a 1 GB
  heap. On the 26-header input it reaches 3.77 GB of the 4 GB that
  32-bit wasm allows and produces nothing, so in a browser it would
  fail outright.

So the page runs on swipl-wasm, which also lets it use dterm: dterm is
SWI-only for reading source, but drawing terms that have no source text
needs only its term layer (`term//4`, `esc//1`), called with unbound
positions.

## In a browser

Chromium (headless, this orb), served by the Nix build:

- opening the page until the first hello world is drawn, including
  compiling the wasm and loading nanofil (assets from the local server):
  about 1.5 s; the status line then reads "Compiled in 536 ms;
  WebAssembly memory 103 MB";
- a loop with `-O`: 74 ms; a parse error: 5 ms;
- `more.c -O`: 1.0 s, of which the pipeline is 0.23 s and the rest is
  drawing. Drawing all 5747 assembly lines took 2.2 s and 3.9 MB of
  HTML, hence the 1500-line cap.

## Next

- Draw the C syntax with source positions: the tokens carry `File:Line`,
  so each item could sit beside its source lines, and each IR block
  beside the statement it came from.
- Cache the preprocessed headers. Preprocessing `stdio.h` is most of a
  hello world, and it is the same every time.
- Lazy sections: draw a function's assembly when it is opened, instead
  of the cap.
- Run the interpreter (`interp.pl`) on `main` and show the outcome; it
  needs CLP(Z), which swipl-wasm has.
