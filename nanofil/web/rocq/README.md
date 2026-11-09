# dterm-rocq: Rocq drawn as structure

dterm-rocq draws nanofil's Rocq the way [dterm](../../docs/dterm.md)
draws its Prolog and [dterm-nix](../../../dterm-nix/README.md) draws
filnix's Nix: by what the code is, not how it was typed. The pages are on
the Filnix wiki at
[mbrock.github.io/filnix/nanofil/rocq](https://mbrock.github.io/filnix/nanofil/rocq/),
one per file of the model in [nanofil/rocq](../../rocq/), and the Rocq
written in [formal.md](../../docs/formal.md) is drawn the same way on
`nanofil/formal.html`.

| File | What it does |
|---|---|
| [rocq_syntax.pl](rocq_syntax.pl) | A lexer and DCG for the vernacular and Gallina: every node keeps its span, comments come back beside the sentences, a file's own infix notations become operators |
| [rocq_draw.pl](rocq_draw.pl) | Draws the terms: sentences for the pages, and inline Rocq and ```` ```rocq ```` fences for the documents (dterm_guide.pl) |
| [dterm_rocq.pl](dterm_rocq.pl) | One page per `.v` file, with its contents, and an index |
| [dterm-rocq.css](dterm-rocq.css), [dterm-rocq.js](dterm-rocq.js) | The Rocq layouts, over nanofil's `dterm.css` |
| [tests/parse.sh](tests/parse.sh) | Checks the grammar against Rocq itself |

Shared with dterm and dterm-nix: `dterm.js`, the printer that breaks
inline terms at the width they get (it reads only `data-d=args` and
`data-d=op`), `dterm.css`, which sets the terms, and `dterm_html.pl`, the
HTML DCGs and the Markdown of comments. The shared printer also accepts
`data-case-layout="stack"` or `"table"` on the root to override its automatic
case fitting. It measures nested terms against their grid or table cell,
not just the enclosing clause, so a deeply nested result breaks in the room
it actually has. Other pages keep automatic case fitting.

## Layout choices

The **Rocq layout** selector appears on source pages and on Rocq documents
such as `formal.html`. Its choice is remembered across those pages:

- **Adaptive** (default): matches use columns only when they fit; constructor
  and record tables become rows with their comments underneath when their
  container is narrower than 40rem. The Rocq comparison table in the formal
  campaign becomes labeled cards on narrow screens.
- **Stacked**: patterns above results, constructor and record comments below
  their code, and comparison tables as cards, even on desktop.
- **Side by side**: preserve aligned columns, with local horizontal scrolling
  for wide blocks. This is useful for comparing cases; it is deliberately
  not the phone default.

Signatures and quantified expressions expose breaks between binders, and
constructor arguments and field types use the same term printer as definition
bodies. Nested matches spend less of a narrow screen on indentation. Comments
remain visible in every layout. Without JavaScript, source tables still adapt
to their container and the nonfunctional selector stays hidden.

## Reading Rocq

The grammar is a Prolog DCG, as dterm-nix's is, rather than SerAPI or
`coqdoc`'s output: the drawer matches the terms directly in clause heads,
and Rocq's own printers either drop comments and spelling (`Print`) or
give HTML of tokens without structure (`coqdoc`). It reads what the
formal campaign writes: `Inductive` (with `with`), `Record`,
`Definition`, `Fixpoint`, theorems, `Axiom` and `Parameter`, `Module`,
`Module Type` and `Section`, `Notation`, and Gallina terms with `forall`,
`fun`, `exists`, `let` (with `let fix`, `let '(a, b)` and the development's
`let*`), `if`, `match` (several scrutinees, `|` alternatives,
or-patterns `(W | L)` and `as` patterns, which bind tighter than any
operator: `Const c as a :: rest`), records `{| … |}`, sigma types, scopes,
chained comparisons `a <= b < c` and Rocq's standard operator levels. It
also reads what Rocq prints in proof states: an unfolded fixpoint
`(fix f (x : T) {struct x} : U := …) a`, named arguments `(elt:=A)`,
pattern binders `fun '(a, b) => …` and a positive's binary digits
`p~0~1`; and `Module M := F A`, a functor applied, drawn as one line. A proof keeps
its focus bullets and tactic sentences. Ltac definitions and scripts parse
sequencing, choice, dispatch, `first`/`solve`, prefixes such as `try` and
`repeat`, counted `do N`, goal selectors, and `match`/`lazymatch`/`multimatch`.
Match patterns, parenthesized expressions, assertions and `ltac:(…)` use the Gallina grammar;
intro patterns remain distinct from terms. Atomic tactic extensions keep
their tokens; an unsupported control form stays verbatim, never disappears.

It reads Iris (rocq/spikes) at Iris's levels: `∗` (80, right), `-∗`,
`==∗` and `⊢` (99, right), `▷ □ ◇ ● ◯ ✓` as tight prefixes, `|==>`,
`|={E1,E2}=>` and `P ={E}=∗ Q`, `⌜φ⌝`, `WP e @ s; E {{ v, Φ v }}`,
Texan triples `{{{ P }}} e {{{ x, RET v; Q }}}`, big operators
`[∗ list] k ↦ x ∈ l, Φ`, points-to `ℓ ↦{#q} v`, `k ↪[γ]□ v`, step-indexed
relations `≡{n}≡ ≼{n} ✓{n}`, and std++'s `!! <$> <[k:=v]> .*1 λ`. A file's
`Infix "**" := star` folds as a Notation does, also in the files that
`Require` it. The proof mode's strings are read as intro, selection and
specialization patterns (`iIntros (x) "[H1 #H2]"`, `iApply ("H" $! x with
"[$HP]")`), not as opaque text.

`tests/parse.sh` compiles each `.v` file, then reprints its tree with
every subterm in parentheses (`tests/reprint.pl`) and compiles that: if
the definitions still type-check and the proofs still go through, every
operator was read at Rocq's precedence and every binder where Rocq puts
it. The reprint also groups Ltac control flow and embedded terms, and a
temporary proof fixture distinguishes choice from sequencing and exercises
dispatch, match patterns and assertions. All files in the development are
compiled with their `_RocqProject`'s flags in its order. Unparsed definitions
or tactics fail this check. Making `->` left-associative fails four Campaign
1 files and `::` left-associative fails Semantics.v.

## Drawing rules

- An inductive type is a table of its constructors and their arguments.
  A relation whose constructors have premises, such as a step relation,
  is a column of inference rules: the quantified variables, the premises
  over a line, the conclusion under it, the constructor's name on the
  line.
- A record is a table of its fields; a comment after a field or a
  constructor sits beside it.
- A theorem, lemma or axiom is its statement drawn as a rule, and its
  proof folds under it, a row per tactic indented by its bullets.
- Ltac matches use the same adaptive pattern/result layout as Gallina.
  Dispatch and choice have one branch per row; atomic tactics and their
  embedded terms use dterm's application/operator printer. Source scripts,
  timeline buttons and selected-step headings share that drawing. Buttons
  keep the original command as their accessible name; typeset steps expose
  it in their tooltip. Unknown syntax remains monospace.
- A definition is its signature over its body. `match` is a table of
  patterns and results, `if` a table of conditions, `let` a binding over
  its body; anything else is one term, broken by dterm.js.
- Inline, an application is its function and arguments without
  parentheses, `forall`, `fun` and `exists` are `∀`, `λ` and `∃`, and the
  ASCII operators are their glyphs (`→ ∧ ∨ ≠ ≤ ≥ ×`). A file's own infix
  notation (`Notation "c ⟶ r" := (step c r)`) folds the application back
  into it, as Rocq prints it.
- A bound variable is a variable (digits as a subscript, `'` as a prime);
  a name the drawn files define links to its definition; constructors,
  types, definitions and lemmas each have their colour.
- `(** … *)` comments are prose in dterm's little Markdown, with
  coqdoc's `[term]` drawn as Rocq and `(** * Title *)` or
  `(** ## Title *)` as a section heading (the page's contents follow them). The first is the page's
  lede, and its first sentence the file's line on the index. A link
  `[text](../../docs/formal.md#…)` is written relative to the `.v` file,
  as GitHub reads it, and drawn to the site's page for that document.
  `(* … *)` comments are notes, or asides at the end of a line.
  `name/N`, `module:name/N` and `module.pl` link to nanofil's Prolog.
- Iris is drawn as its papers write it: `−∗`, `|⇛` with its masks as
  scripts, `WP` with the postcondition's binder, triples in ⦃ ⦄, a big
  operator with its binders and list under it, `ℓ ↦` with its fraction
  above. A proof-mode tactic's hypotheses are names, its marks operators.

## Rocq in documents

In a nanofil document that names Rocq (formal.md), inline code that only
Rocq writes is drawn as Rocq: a sentence (`Theorem t : …`), a type's
constructors (`cap := None | Obj base`), a record's fields
(`ptr := { addr : Z; cap : cap }`), a typed name
(`step : config -> outcome`), or a term whose head is a constructor
(`Trap r`) or that is a proposition (`f x = true`). Prolog terms keep
dterm's drawing. A ```` ```rocq ```` fence is drawn as a page draws its
sentences.

## Running it

```sh
swipl nanofil/web/rocq/dterm_rocq.pl OUT . --prolog=nanofil/src $(find nanofil -name '*.v')
nanofil/web/rocq/tests/parse.sh        # every .v file under nanofil
node nanofil/web/rocq/tests/layout.mjs http://localhost:8765
```

The site build ([packages/site](../../../packages/site/build.sh)) draws
every `.v` file under `nanofil/` into `nanofil/rocq/`.
The browser check takes the HTTP base URL of a served site build and needs
`agent-browser`. It exercises the real model and formal campaign at 320,
390, 768 and 1280px, including the layout selector and its saved preference.
Pass one or more widths after the URL to split the run into bounded jobs;
the default still covers all four. For example, run 320 and 390 separately,
then 768 and 1280 together, each under the usual watchdog.
At 320 and 390px it discovers every Rocq page from the generated index and
checks for document overflow, including expanded scripts and every captured
proof step, in the page and the open dialog. It also checks modal navigation,
focus restoration, local typography, tactic counts and the single vertical
scroll flow. New theories join this check without editing a file list.

Pages runs `layout.mjs URL --pages-only 320 390` on the actual full site
before deploying. This bounded sweep checks every source page with and
without JavaScript, both on narrow loads and after desktop-to-phone reflow;
the default command retains the exhaustive proof checks above. It must use
the full cross-link index: Evidence's linked names expose an overflow that
rendering Evidence alone misses. A fresh narrow load can also fit when the
resize plan does not. The browser check was previously manual, so adding a
theory did not automatically run it in CI.

The planner keeps the available width as a hard constraint. When even its
least ribbon-constrained plan cannot fit a deeply nested term, it restores
the ordinary wrapping markup rather than forcing wide indents and no-break
spaces. The browser sweep also rejects JavaScript exceptions: a crashed
planner can leave a fitting but unplanned page and conceal a reflow bug.

Closed captured proofs hide their explorer subtree with `display: none`,
not only the browser's native disclosure hiding. This keeps large snapshot
trees out of style work until opened; the modal moves the explorer out of
that direct-child rule. The shared printer also leaves clauses without a
rendered box alone: its ResizeObserver queues them when they become visible.
All snapshots remain inline and readable without scripts. The phone gate
keeps the same pages, states, parallel widths and deadlines.

Proof capture schedules the project as a dependency graph (`coqdep`) on the
build's cores: compiling an imported file and replaying any file in its own
RocqIDE session each start once that file's imports are compiled, the longest
chain of compiles first. A file nothing imports is only replayed, since the
replay already executes every command and checks every closure. It keeps
every command, source hash, active goal and proof-closure check; concurrency
changes neither the snapshots nor the capture/build deadlines. At 4 cores
this took the capture from 279s to 148s with byte-identical output; the
remaining critical path is Prefix.v's own replay.

The pinned agent-browser 0.38.1 has a fixed 25-second navigation load wait,
independent of its advertised default timeout. If only that wait expires,
the checker waits up to another 60 seconds for the same URL to finish
loading, then runs all assertions normally. It neither repeats navigation
nor accepts the old document as a loaded page. Other errors still fail,
and the watchdog's 300-second deadline is unchanged. Pages also runs
`node nanofil/web/rocq/tests/navigation.mjs`: a real delayed HTTP response
must pass when narrow and fail on overflow inserted at the end of loading,
after the initial navigation timeout.

Rendering streams completed declarations, timeline entries, hypotheses,
goals and snapshots instead of retaining a page-sized list of HTML codes.
`write_streamed_page/3` resumes the existing DCG after each `html_flush/2`
checkpoint with a fresh difference list; enclosing elements and module/local
environments survive the checkpoint. Ordinary `phrase/2` users, including
Rocq snippets in the guide, still receive the same pure code list.

SWI 10's adaptive GC can also accumulate discarded fragments almost to the
stack limit. The writer collects after another eighth of the actual limit
has been allocated since the preceding collection (128 MiB at the default
1 GiB), rather than collecting every hypothesis. It also collects between
pages. The source/index/capture and an individual fragment must still fit;
no snapshots, hypotheses or pending goals are truncated or skipped, and
the cross-file name index is built once, not once per output page.

Each page logs UTC completion time, elapsed seconds, sampled maximum total
stack usage against the actual limit, and global usage before/after final
collection. Samples run every 50ms and before fragments are released, so
the maximum is observed, not an exact high-water mark. A UTC warning names
the page the first time a sample reaches 60% of the limit. The site keeps
the default 1 GiB limit. `tests/capture.py` checks 200 coqc-verified lemmas
and all 1,600 snapshots on one page under 64 MiB; the whole-page writer at
517909a exhausts that limit on the same input.

## Reading proofs, not just tactics

The source pages offer **Explore proof**, opening a wide native dialog
(full-screen on narrow screens). The source disclosure stays a single row.
A tactic timeline sits beside the current context and conclusion on desktop;
on narrow screens the selected context follows its tactic in the script.
Previous/Next, arrow keys and Home/End navigate the proof. **Compare before**
keeps the preceding source state visible. Added/changed context entries and
changed conclusions have both a green accent and a symbol (+ or ↻);
only removed context entries need a separate count. These are textual
differences in Rocq's output, not claims of semantic equivalence. Pending
branches and shelved goals remain available; solving the focused goal is
not the same as closing the proof. Initial goals and checked closure are
named separately from the tactic count. Escape or the close button returns
focus to the source disclosure without moving the page. The source script
and name links remain. Without JavaScript, all snapshots are readable inline
in order, with no dialog or nonfunctional controls.

The explorer uses dterm's compact rows and rules rather than nested cards:
hypothesis names and types share aligned rows even on narrow screens, and
⊢ separates the conclusion from its context. The name, navigation, layout
choice and close button share one header row on desktop, outside the
scrollers, so nothing slides underneath it. On desktop the script and the
selected state are two panes that scroll on their own: the script pane
keeps the selected tactic in view, and the state pane keeps its position
from step to step. A wide state pane sets short hypotheses (34 characters
or fewer, as Rocq prints them) two to four to a row, in columns whose names
and types align, in Rocq's order; long ones and local definitions keep a
whole row. The selected tactic is highlighted beside its state, so the state
repeats no heading; it counts open goals only when there are several. On a
phone the explorer is one vertical flow with no nested scrolling, and the
selected state follows its tactic. All three layouts still use the same printer.
Tactic locals come from captured contexts before and after each command,
so newly introduced and consumed names share the goals' variable typography.
Intro patterns keep their delimiters inline, rather than looking like nested
tactic blocks. Controls, comparison states and source disclosure use a small gutter.
Empty contexts and repeated explanatory hints are omitted. “No remaining
goals” is still distinct from a checked closure, without a reminder to type
`Qed` at every solved state.

### Patterns and tactic control flow

Intro patterns are trees of alternatives, sequences and pairs, with bound
names, wildcards and rewrite arrows, rather than generic bracket tokens.
`as`, `in`, `with`, `using`, `eqn:` and `by` own their arguments. Parenthesized
expressions and assertions still use the same Gallina grammar and printer
as goals. `context […]` in a match hypothesis or goal is a tactic pattern,
not a Gallina application; the reprint must not parenthesize it as one.
`do N` owns its count and one tactic, before sequencing or choice. The
coqc fixture checks both zero and multiple repetitions and explicit grouping.

Short tactic chains, prefixes and choices use dterm's operator and argument
groups: they stay a phrase when they fit and break at tree boundaries when
they do not. Tactic arguments do not acquire Gallina's application brackets.
Chains containing match arms become indented control flow; their separators
stay beside the continuation, not alone on a line. Match arms use the shared
Adaptive/Stacked/Side-by-side fitting. Focus bullets start sibling groups and
braces nest groups, with compact rows and the bullet beside its first tactic.
The source parser and capture planner share `rocq_focus_tokens/4`, so
`2: { tac. … }` opens a selected focus group and captures `tac.` separately,
even on one line. Nested braces always open another group, unlike repeated
bullets, which start siblings. Capture fixtures use the first tactic's new
hypothesis later in the proof, so silently dropping it fails the check.
On narrow screens the selected state still follows the actual compound
command; the renderer never invents intermediate execution states.

### Prior art and the choice

- [Alectryon](https://github.com/cpitclaudel/alectryon) is the closest model:
  static documents with actual per-sentence contexts, goals and messages.
  Its 2.0 drivers support Rocq 9 through VsRocq and experimental coq-lsp;
  its minimal `coqc_time` driver does **not** capture goals. Borrow the
  snapshot model, not its HTML/CSS or a second typesetter.
- [jsCoq](https://jscoq.github.io/) offers a real browser prover, editing,
  step navigation and a goal panel. Useful for experiments, but the prover
  download and editor are unnecessary for reading checked source pages.
- [rocq-lsp's protocol](https://github.com/ejgallego/coq-lsp/blob/main/etc/doc/PROTOCOL.md)
  exposes `proof/goals`: structured contexts, conclusions, focus stacks,
  shelf and given-up goals at document positions. A good future capture
  backend, but the pinned toolchain already ships RocqIDE's equivalent
  XML `Add`/`Status`/`Goal` interface, so no new server/version is needed.
- [Proof General](https://proofgeneral.github.io/) supplies the familiar
  script-plus-goals mental model. We retain explicit step selection,
  without editor chrome or an obligation to execute the script yourself.
- [Lean's infoview](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md)
  makes the local context and remaining goals first-class. Its companion
  [Verso](https://github.com/leanprover/verso) annotates published tactic
  proofs with proof states, explicitly inspired by Alectryon. Borrow that
  reading experience while keeping dterm's typography and name links.

### Real states at build time

`capture_plan.pl` uses the renderer's lexer for character-offset command
boundaries, separating focus bullets/braces from sentences. `capture.py`
compiles the `_RocqProject` in dependency order in a writable temporary
copy, then replays proof-bearing files through the pinned `coqidetop` with
asynchronous proofs disabled. `Status true` forces each accepted command
to execute; `Goal` records focused, deferred, shelved and given-up goals.
Initial states, each tactic sentence's result, and proof closure are saved.
A compound tactic (`…; …`) is one step, not a fabricated sub-tactic trace.
Errors fail the build; `Admitted`/`Abort` never receive a checked badge.

The renderer validates each source's SHA-256 before using its offsets.
Goals, grouped hypotheses and local definitions use the same Gallina
grammar and term printer as source code. Unsupported notation is shown
verbatim with an explanatory tooltip, never silently dropped or guessed.
The existing Adaptive/Stacked/Side-by-side selector is unchanged.

`capture.nix` caches execution independently of CSS/JS. The site requires
its output and embeds the rendered states in HTML; the reader needs
neither a server nor a running prover. To preview with local tools:

```sh
python3 nanofil/tests/watch.py --label 'Proof capture' -- \
  python3 nanofil/web/rocq/capture.py nanofil/rocq /tmp/proof-states.json
swipl nanofil/web/rocq/dterm_rocq.pl OUT . --prolog=nanofil/src \
  --states=/tmp/proof-states.json $(find nanofil/rocq -name '*.v')
python3 nanofil/web/rocq/tests/capture.py
```

The capture regression exercises real rewrites, grouped context, local
definitions, focus, shelved goals, checked/aborted/admitted closure,
Unicode offsets, failed tactics and stale-source rejection. The browser
regression exercises navigation, comparison and context-change markers at
all four widths as well as the existing layout checks.
