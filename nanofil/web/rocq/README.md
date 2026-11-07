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
`let*`), `if`, `match` (several scrutinees, `|` alternatives and
or-patterns `(W | L)`), records `{| … |}`, sigma types, scopes, chained
comparisons `a <= b < c` and Rocq's standard operator levels. A proof is kept as its tactics, each with the bullets
that focus it; tactics are not parsed. A sentence it does not read is
drawn as its text.

`tests/parse.sh` compiles each `.v` file, then reprints its tree with
every subterm in parentheses (`tests/reprint.pl`) and compiles that: if
the definitions still type-check and the proofs still go through, every
operator was read at Rocq's precedence and every binder where Rocq puts
it. It passes on the nine files of the Campaign 1 development
([nanofil/rocq/theories](../../rocq/theories)), compiled with their
`_RocqProject`'s flags in its order. Making `->` left-associative fails
four of them and `::` left-associative fails Semantics.v.

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
  lede. `(* … *)` comments are notes, or asides at the end of a line.
  `name/N`, `module:name/N` and `module.pl` link to nanofil's Prolog.

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

## Reading proofs, not just tactics

The source pages offer **Explore proof**. A tactic timeline sits beside
the current context and conclusion; on narrow screens it sits above them.
Previous/Next, arrow keys and Home/End navigate the proof. **Compare before**
keeps the preceding source state visible. Added/changed context entries and
changed conclusions have both a green accent and a symbol (+ or ↻);
only removed context entries need a separate count. These are textual
differences in Rocq's output, not claims of semantic equivalence. Pending
branches and shelved goals remain available; solving the focused goal is
not the same as closing the proof. The source script and name links remain.
Without JavaScript, all snapshots are readable in order.

The explorer uses dterm's compact rows and rules rather than nested cards:
hypothesis names and types share aligned rows even on narrow screens, and
⊢ separates the conclusion from its context. The timeline scrolls locally;
controls, comparison states and source disclosure use only a small gutter.
Empty contexts and repeated explanatory hints are omitted. “No remaining
goals” is still distinct from a checked closure, without a reminder to type
`Qed` at every solved state.

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
