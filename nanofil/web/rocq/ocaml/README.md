# OCaml `dterm-rocq`

This directory contains an OCaml 5 translation of the Prolog `dterm-rocq` pipeline in the parent directory. It uses only `Stdlib` and `Unix`, compiles to one native binary, and renders the site's Rocq pages in parallel across OCaml 5 domains.

## Layout

### Parser and reprinter
- [ast.ml](ast.ml) — typed ASTs for tokens, expressions, binders, Iris forms, `IRNotation`, tactics, vernacular items, and inline fragments.
- [lexer.ml](lexer.ml) — UTF-8 scanner using `Stdlib.String.get_utf_8_uchar`, nested comment scanner, and sentence chunker.
- [parser_core.ml](parser_core.ml) — cursor `state`, O(1) `try_`/`first` backtracking, contextual flags, and operator and notation-fold tables.
- [parse_term.ml](parse_term.ml) — Pratt `expr`, binders, Iris, `FrameNotation`, `IRNotation`, and `cap_*` fixtures.
- [parse_tactic.ml](parse_tactic.ml) — Ltac, intro patterns, and Iris Proof Mode tactics.
- [parse_vernac.ml](parse_vernac.ml) — vernacular sentences, dynamic `Notation`/`Infix` + sibling-file cache, `Module`/`Section`/`Proof` tree builder, and inline prose fragments.
- [reprint.ml](reprint.ml) — 1-to-1 port of `tests/reprint.pl` via `Buffer.t`.

### HTML renderer
- [html.ml](html.ml) — direct-to-`Buffer.t` HTML builder, RFC 3986 fragment URI encoder, and site header.
- [markdown.ml](markdown.ml) — port of `dterm_html.pl` block Markdown parser (`blocks`, `dedent`, `trim_blank_ends`, tables).
- [concepts.ml](concepts.ml) — port of `concepts.pl` (`[[concept]]` links, hover cards, `![[embed]]`).
- [draw_env.ml](draw_env.ml) — immutable cross-domain `corpus` index and per-page mutable `ctx`.
- [draw_hooks.ml](draw_hooks.ml) — forward hooks breaking mutual recursion across the draw modules.
- [draw_ir.ml](draw_ir.ml) — `IRNotation` renderer (functions, blocks, phis, instructions, jumps, `Flight`/`Touch` escapes, glosses).
- [draw_tactic.ml](draw_tactic.ml) — proof, Ltac, intro-pattern, and IPM renderer (`focus_tree`, `proof_env`).
- [draw_prose.ml](draw_prose.ml) — comment sections and asides, inline prose, concept cards and embeds, Prolog links, inline Rocq fragments, and `rocq_fence`.
- [draw_term.ml](draw_term.ml) — inline terms, subscript/prime variables, operator glyphs, binders, block layouts, inference rules, and vernacular declarations.
- [c_batch.ml](c_batch.ml) — collects unique ```` ```c ```` fences and inline C spans across the corpus and renders them in one invocation of [c_batch.pl](../../c/c_batch.pl).
- [blurbs.ml](blurbs.ml) — curated `file_blurb` summaries from `dterm_rocq.pl`.
- [draw_page.ml](draw_page.ml) — page shell, TOC and siblings navigation, `index.html`, and two-pass OCaml 5 domain-parallel site renderer.
- [main.ml](main.ml) — CLI for `--reprint`, `--reprint-all`, and `--render`.

## Building and running

```sh
nix build .#site.dtermRocq

# Render Rocq pages with Prolog links, concept cards, and batched c_draw
./result/bin/dterm-rocq --render /tmp/out . \
  --prolog=nanofil/src --concepts=nanofil/docs/concepts \
  --c-batch=nanofil/web/c/c_batch.pl nanofil/rocq/.../*.v
```
