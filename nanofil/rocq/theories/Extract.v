(** Extraction of the model to OCaml: the decoder, the interpreter's
    instance of the semantics, and `judge`, which the driver
    (extraction/main.ml) applies to every line `nanofil outcomes`
    prints, and `judge_valid`, which it applies to rocq/mutants.pl's
    verdicts. Integers become zarith's, strings OCaml's, and `nat`
    OCaml's `int`: the model's `nat`s count list elements and rounds,
    and a unary one as large as the square of a function's block count
    (`dominators`'s bound, a million for Lua's `luaV_execute`)
    overflowed the stack. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt
  ExtrOcamlNatInt.
From Nanofil Require Import Term Transport.

Set Extraction Output Directory "extraction".
Extraction "nanofil_model.ml" term_eqb decode_module judge judge_valid.
