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
From Nanofil Require Import Term Maps Transport.

(** Maps.v's `string_hash` decides which bucket a name goes in, never
    an answer: a lookup compares the names in its bucket with
    `name_eqb`. So the extraction may use OCaml's own string hash; the
    Gallina one goes through eight integer operations per character,
    which made the validator twice as slow on small functions. *)
Extract Constant Maps.string_hash =>
  "(fun s h -> Big_int_Z.big_int_of_int
     ((Hashtbl.hash s + 31 * Big_int_Z.int_of_big_int h) land 0xFFFFF))".

Set Extraction Output Directory "extraction".
Extraction "nanofil_model.ml" term_eqb decode_module judge judge_valid.
