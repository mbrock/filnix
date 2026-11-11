(** Checking compiler output against the Rocq model requires an
    executable program, rather than evaluating every test inside the proof assistant.
    This module selects the decoder, execution judge, and
    [[validator]] functions for [[extraction]] to OCaml, producing the model used by the test driver.
    The driver compares [[interpreter]] outcomes and [[mutant]]
    verdicts through the judgments defined in [Transport](Transport.v).

    Extracted integers use Zarith, strings use native OCaml strings,
    and natural-number counters use machine integers rather than unary lists of successors.
    Large traversal and execution budgets would otherwise create deep
    recursive values and overflow the OCaml stack before useful work could finish.
    The extracted entry points include the original validator and the
    faster implementation whose identical answers are proved in [ValidFast](ValidFast.v). *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt
  ExtrOcamlNatInt.
From Nanofil Require Import Term Maps Validate ValidFast Transport.

(** A hash collision cannot change a map's answer because bucket
    lookup still compares complete names before returning their values.
    Extraction can therefore replace [string_hash] with OCaml's native
    string hash, avoiding repeated arbitrary-precision arithmetic for each character. *)
Extract Constant Maps.string_hash =>
  "(fun s h -> Big_int_Z.big_int_of_int
     ((Hashtbl.hash s + 31 * Big_int_Z.int_of_big_int h) land 0xFFFFF))".

Set Extraction Output Directory "extraction".
Extraction "nanofil_model.ml" term_eqb decode_module judge judge_valid
  valid_items valid_func valid_items_fast valid_func_fast valid_fast.
