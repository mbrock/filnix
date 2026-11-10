# dterm-c: C drawn from nanofil's own parse

dterm-c draws the C under `nanofil/` the way [dterm](../../docs/dterm.md)
draws its Prolog and [dterm-rocq](../rocq/README.md) its Rocq: by what the
code is, as nanofil's frontend reads it, not by a regex highlighter. The
pages go in the site's `nanofil/c/`, one per `.c` or `.h` file, with an
index.

| File | What it does |
|---|---|
| [c_read.pl](c_read.pl) | Reads a file with [c_lex.pl](../../src/c_lex.pl) and [c_parse.pl](../../src/c_parse.pl), one external declaration at a time, and collects the comments, directives and integer spellings the lexer drops |
| [c_draw.pl](c_draw.pl) | Draws the items: for the pages, and for ```` ```c ```` fences in the documents dterm draws (dterm_guide.pl) |
| [dterm_c.pl](dterm_c.pl) | One page per file, with its contents, and an index |
| [dterm-c.css](dterm-c.css), [dterm-c.js](dterm-c.js) | The C layouts, over nanofil's `dterm.css`; the IR link |

## Reading C

The file is not preprocessed: macros stay as written, so a function-like
macro is a call and an object macro a name. The grammar needs to know
which names are typedefs. c_read starts with the standard library's and
POSIX's typedefs and learns the file's own as it reads them. A
declaration the grammar refuses is read again with the names that stand
where a type would treated as typedefs. If it still fails and it is a
function, its body is read a statement at a time. A statement the
grammar refuses (a macro used as a statement, an unsupported asm) is
kept as its tokens with the parser's reason, and so is an external
declaration. Nothing is dropped. Of the 527 files, all draw. The index
counts each file's unread parts.

c_read calls c_parse's nonterminals directly (`external_decl//4`,
`block_item//3`, `decl_specs//2`, `full_declarator//3`, `conditional//2`,
`expr//2`) and its helpers (`typedef_declared/3`, `typedefs_hidden/3`,
`params_env/3`, `c_operator/4`). Renaming one of these breaks the pages,
not the compiler. The compiler is unchanged and does not load these files.

## Drawing rules

- A function is its signature over its body. A body is a column of
  statements set in from a hairline. A compound statement is its keyword
  line over its own column, so braces and semicolons are not drawn.
  `if`/`else if`/`else` is one flat chain, and `switch` is a table of its
  labels beside the statements under each.
- A struct or union is a table of its fields, types then names. An enum
  is a table of its constants and values. `typedef struct {…} T` is
  headed by `T`.
- Expressions are set as dterm sets terms (`data-d=args`, `data-d=op`), so
  dterm.js breaks them at the width they get. Parentheses come from the
  tree, so only the needed ones are drawn. Assignment is `←`, an
  initializer `≔`, equality `=`, and `≠ ≤ ≥ ∧ ∨ ¬ × − ≪ ≫ →` are glyphs.
  Each keeps its C spelling as its title. Integers keep their spelling
  (`0x1F`, `10UL`).
- A local or parameter is a variable (hovering it lights up its uses). A
  name the file defines links to its definition: functions, globals,
  typedefs, enumeration constants, macros, struct tags as
  `#struct-TAG`. A field links to its struct when only one struct has it,
  and a goto links to its label.
- Comments before an item are its prose, inside a body they are notes,
  and after code on its line they are asides. A file's first comment is
  the page's lede. A comment of `key: value` lines (a test's `run:`
  lines) is a list. Directives sit among the items. A `#define` body
  that reads as an expression is drawn as one, its parameters as
  variables.
- Each function has an **IR** link that opens the
  [playground](../play/) on the file (`#src=BASE64URL&name=FILE&ir=FN`).
  The playground compiles it in the browser and opens that function's
  checked IR. Files over 24 KB have no link, since the URL would be too
  long.

## Links from documents

dterm_guide.pl's `c_page/2` sends a link to a `.c` or `.h` file to its
page, and draws ```` ```c ```` fences with c_draw (without anchors or
cross-links). If `web/c` is missing from the sources dterm reads, C
fences stay text and C links go to GitHub. Pandoc-rendered documents use
`packages/site/pages.lua`'s rule for the same names.

## Running it

```sh
swipl nanofil/web/c/dterm_c.pl OUT . $(find nanofil \( -name '*.c' -o -name '*.h' \) | sort)
```

OUT gets `index.html`, `dterm-c.css`, `dterm-c.js`, and one page per file
named by its path without `nanofil/`, with `/` as `-`, and `.c` dropped
or `.h` as `-h`: `nanofil/tests/c/basic.c` is `tests-c-basic.html`. The
pages expect `../dterm.css`, `../dterm.js`, `../../style.css` and
`../play/`, as in the site's `nanofil/c/`. `--src=DIR` names nanofil's
src (default `ROOT/nanofil/src`). It takes about 5 s for all 527 files
and exits 1 if any page is not drawn.
