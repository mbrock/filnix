# name map

**nanofil**

A name map is a finite map keyed by IR names, the model's counterpart of SWI-Prolog's library(assoc), which ir.pl and cfg.pl use for every table indexed by a label or a [[temporary]]: the single-definition map, the evidence indexes, dominator intervals.

- Maps.v: [nmap], with [nm_empty], [nm_find], [nm_add], [nm_remove] and [nm_mem]; the lemmas [nm_find_add], [nm_find_remove] and [nm_find_fold_add] say what each operation does to a lookup.
- A name is hashed to an integer, and each hash keeps an association list of the names that share it, in the stdlib's AVL tree keyed by integers.

The subtlety: the hash decides only speed, never an answer. A lookup compares names with [name_eqb] within its bucket, so two names with one hash stay apart, and the proofs never reason about the hash.

Why not simpler: Term.v's association lists are linear, and a function of a thousand blocks asks millions of questions; a tree keyed by positives was thirty times slower once extracted.

Defined in [Maps.v](../../rocq/theories/core/Maps.v).
