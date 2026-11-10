# dterm-c: C drawn from nanofil's own parse

dterm-c draws C written into nanofil's prose, as
[dterm](../../docs/dterm.md) draws Prolog and [dterm-rocq](../rocq/README.md)
Rocq: by what the code is, as nanofil's frontend reads it, not by a
regex highlighter. It draws ```` ```c ```` fences and `` `c: EXPR` ``
inline code in the documents dterm draws, in module headers and comments
on the Prolog pages, and in Rocq comments. [docs/dterm.md](../../docs/dterm.md)
(C in prose) says how to write them.

| File | What it does |
|---|---|
| [c_read.pl](c_read.pl) | Reads C with [c_lex.pl](../../src/c_lex.pl) and [c_parse.pl](../../src/c_parse.pl): a fence one external declaration at a time, with the comments, directives and integer spellings the lexer drops (`c_read_text/3`); inline code as an expression, type, statement or declaration (`c_snippet/2`) |
| [c_draw.pl](c_draw.pl) | Draws them: `c_fence//1`, `c_inline//1` for `` `c: …` ``, `c_inline_auto//1` for unmarked code that is C beyond doubt |

The styles are in nanofil's [dterm.css](../dterm.css) (`.dterm-c` for
fences, `code.cx` inline), so every page that sets terms sets C. The
drawers load the lexer and parser from nanofil's src (with
`src/swi/compat.pl`, as bin/nanofil does) the first time they draw C:
dterm.pl from the source directory it reads, dterm_rocq.pl from
`--prolog=DIR`. Without this directory, or without the src, C stays
plain code.

## Reading C

Fences are not preprocessed: macros stay as written, so a function-like
macro is a call and an object macro a name. The grammar needs to know
which names are typedefs; c_read starts from the standard library's and
POSIX's and learns the fence's own as it reads them. A declaration the
grammar refuses is read again with the names that stand where a type
would as typedefs, then, for a function, a statement at a time; what is
still refused is kept as its tokens with the parser's reason. Nothing is
dropped.

c_read calls c_parse's nonterminals directly (`external_decl//4`,
`block_item//3`, `decl_specs//2`, `full_declarator//3`, `type_name//2`,
`conditional//2`, `expr//2`) and its helpers (`typedef_declared/3`,
`typedefs_hidden/3`, `params_env/3`, `c_operator/4`). Renaming one breaks
the drawing, not the compiler, which does not load these files.

## Drawing rules

- A function is its signature over its body: a column of statements set
  in from a hairline, a compound statement its keyword line over its
  own column, without braces or semicolons. `if`/`else if`/`else` is one
  flat chain, `switch` a table of its labels beside their statements.
- A struct or union is a table of its fields, types then names; an enum
  a table of its constants and values; `typedef struct {…} T` is headed
  by `T`. Inline, a struct's members are in braces.
- Expressions use dterm's term markup (`data-d=args`, `data-d=op`), so
  dterm.js breaks them at the width they get; the tree decides the
  parentheses. Assignment is `←`, an initializer `≔`, equality `=`.
- In a fence, a local is a variable (hovering it lights up its uses) and
  a name the fence defines links to its definition, under anchors only
  that fence uses (`#c1-sum`). Inline, a name is a variable unless it is
  called or in capitals.
- Comments in a fence are prose before an item, notes inside a body and
  asides after code on its line; directives sit among the items.
