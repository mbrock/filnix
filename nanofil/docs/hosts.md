# Prolog hosts

nanofil runs on SWI-Prolog (the default, through `src/swi/`) and, while
Trealla is paused, keeps to Trealla's dialect (AGENTS.md). This file
records what was measured on other hosts, so the next attempt starts from
the numbers.

## Scryer Prolog: not worth supporting yet (October 2026)

Scryer 0.10.0 (nixpkgs `scryer-prolog`) ran a scratch copy of `src/` on
Lua 5.4.7's files. The output was identical to SWI's: `cc-ir` and `-O cc`
of `lvm.c` (76,757 lines of assembly) and `lapi.c`, and the
preprocessor's tokens of `lvm.c` matched `filcc -E`'s. It was slower and
larger everywhere:

| `lvm.c` | SWI 9.2.9 | Scryer 0.10.0 |
| --- | --- | --- |
| startup (empty file) | 0.3 s | 2.0–2.4 s |
| `tokens` of the `.i` | 0.8 s | 4.5 s |
| preprocess + `tokens` | 3.0 s, 314 MB | 12.5 s, 536 MB |
| `cc-ir` | 1.7 s, 133 MB | 7.6 s, 367 MB |
| `-O cc` | 3.5 s, 216 MB | 14.5 s, 737 MB |

Scryer's packed strings did not make the character-list preprocessor
cheaper: text it builds (spliced lines, spellings) is ordinary list
cells again. Scryer also compiles all of `src/` on every run.

Running there took, besides one real fix (an operator atom as an operand
must be bracketed, `Op == (=)`, not `Op == '='`; now in `c_lower.pl`):

- no `:- if/else/endif`: choose the non-SWI branches by script;
- argv from `os:argv/1`; `forall/2` from `library(iso_ext)`;
- missing: `msort/2`, `sort/4`, `atomic_list_concat/2,3`, `atom_number/2`,
  `is_list/1`, `include/3`, `exclude/3`, `foldl/6`, `last/2`,
  `max_list/2`, `min_list/2`, `numlist/3`, `subtract/3`;
- char lists, not atoms, for `format/2,3` and `format_//2` format
  strings (and no `format(atom(A), ...)`), `getenv/2`,
  `process_create/3`, and file names (`path_canonical/2`,
  `file_exists/1` stand in for `absolute_file_name/2`, `exists_file/1`);
- `write_canonical/1` prints lists as `'.'(H, T)`, so `tokens` output
  differs in form.

So "Trealla's dialect" also leans on Trealla's SWI-like extras. A
`src/scryer/` layer would be about 60 lines plus a `format` wrapper, but
at 4x SWI's time it buys only a strictness check. Revisit when Scryer
is faster or caches compiled code.
