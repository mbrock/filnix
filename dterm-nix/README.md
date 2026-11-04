# dterm-nix: Nix drawn as structure

dterm-nix draws Nix files as web pages the way nanofil's
[dterm](../nanofil/docs/dterm.md) draws Prolog: by what the code is, not
how it was typed. The pages are on the Filnix wiki at
[mbrock.github.io/filnix/nix](https://mbrock.github.io/filnix/nix/).

| File | What it does |
|---|---|
| [nix_syntax.pl](nix_syntax.pl) | A lexer and DCG for Nix: every node keeps its span, strings keep their spelling, comments come back beside the tree |
| [dterm_nix.pl](dterm_nix.pl) | Resolves names to their bindings and draws each file as a page |
| [dterm-nix.css](dterm-nix.css), [dterm-nix.js](dterm-nix.js) | The Nix layouts, over nanofil's `dterm.css`; hovering a name lights up its binding and its other uses |
| [tests/parse.sh](tests/parse.sh) | Checks the grammar against Nix's own parser |

Shared with nanofil's dterm: `dterm.js`, the printer that breaks inline
terms at the width they get (it reads only `data-d=args` and `data-d=op`
markup), `dterm.css`, which sets the terms, and
`nanofil/web/dterm_html.pl`, the HTML DCGs and the Markdown of comments.

## Reading Nix

The grammar is a Prolog DCG rather than tree-sitter-nix or
`nix-instantiate --parse`:

- `nix-instantiate --parse` drops comments and desugars (`a.b = 1;`
  becomes nested sets, `-x` becomes `__sub 0 x`), so it cannot show the
  source as written.
- tree-sitter-nix keeps both, but it is a concrete syntax tree in a
  separate tool, read through JSON.
- A DCG makes Nix into Prolog terms the drawer can match on directly,
  in clause heads as dterm matches Prolog, and it is small:
  about 400 lines with the lexer.

`tests/parse.sh` prints each file's tree back as Nix with every
subexpression in parentheses, and checks that `nix-instantiate --parse`
gives the same output for the reprint as for the original. That holds
for every `.nix` file in this repository and for 1,929 files of the
pinned Nixpkgs (all of `lib`, `nixos/lib`, `pkgs/stdenv` and
`pkgs/top-level`, and a sample of modules and packages). Making `++`
left-associative fails 8 of this repository's files.

## Drawing rules

- An attribute set is a table of its bindings: a name column and a
  value column shared by the rows. A value that is itself a block (a
  set, a function, a `let`) goes under its name. A set of up to three
  bindings written on one line stays inline, in braces.
- `let … in` is its bindings over its body; `with` and `assert` are a
  line over their body.
- A function is a signature: `λ` and its parameters, curried ones on one
  line, and a table of the defaults of an argument set.
- `if` chains and `mkIf c x` are dterm's case tables; a chain of one
  operator over blocks (`//`, `++`) is a column of operands.
- An application is its function and arguments, set as dterm sets a
  compound but without parentheses; when an argument is a block it goes
  under the function, so `mkOption { … }` is the option's table.
- `description` is prose, `lib.literalExpression "…"` shows the
  expression as Nix, an indented string is the text it means.
- Comments are where they were written: the header is the page's lede,
  comments between bindings are notes, a comment at the end of a line
  sits beside its row. Indented examples in comments are drawn as the
  bindings they are; backquoted Nix in prose is drawn as Nix.
- A name links to where it is bound (`let`, `rec`, parameters,
  `inherit`); each `let` binding and each binding of the set the file
  returns lists what it uses and what uses it. Paths link to their files.

## Running it

```sh
swipl dterm-nix/dterm_nix.pl OUT . nixos/filc.nix finix/userland.nix
dterm-nix/tests/parse.sh               # every .nix file in the repository
```

The pages expect `../nanofil/dterm.css`, `../nanofil/dterm.js` and
`dterm-nix.css`/`.js` beside them. The site build
([packages/site](../packages/site/default.nix)) lists the files it draws
in `nixPages`.
