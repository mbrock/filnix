(** This file extracts the regex compiler of Rx.v to OCaml, for the
    gate's program rx-gallina, whose driver is main.ml. The program
    computes the outcome of each pattern of a text of terms and prints
    the lines rx.pl prints for them. It also reads each function back
    with IrText.v's reader and compares the term it reads with the term
    built.

    The constants are extracted as the backend's own extraction in
    rocq/backend/Extract.v extracts them. Integers become zarith's,
    strings become OCaml's, and a [nat] becomes OCaml's `int`. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatInt.
From Stdlib Require Import ZArith.
From Nanofil Require Import Term Maps.
From Backend Require Import IrText.
From Rx Require Import Rx.

(** The hash that picks a label's bucket in [reachable]'s maps becomes
    OCaml's string hash, as in the backend's extraction: a lookup
    compares the names in the bucket, so the hash decides no answer. *)
Extract Constant Maps.string_hash =>
  "(fun s h -> Big_int_Z.big_int_of_int
     ((Hashtbl.hash s + 31 * Big_int_Z.int_of_big_int h) land 0xFFFFF))".

(** A [nat] is OCaml's `int`, so the conversions between [nat] and [Z]
    are zarith's. *)
Extract Constant Z.to_nat =>
  "(fun z -> if Big_int_Z.sign_big_int z <= 0 then 0 else Big_int_Z.int_of_big_int z)".
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".

(** A list's length is OCaml's, which is tail-recursive. *)
Extract Inlined Constant length => "List.length".

(** IrText.v's three character functions, which Rx.v uses too, are
    OCaml's: the code of a character, the character of a code, and a
    string filled from its characters, last first, in one pass. *)
Extract Constant IrText.code => "Char.code".
Extract Constant IrText.byte => "Char.chr".
Extract Constant IrText.string_of_rev =>
  "(fun cs ->
     let n = List.length cs in
     let b = Bytes.create n in
     let rec fill i = function
       | [] -> ()
       | c :: r -> Bytes.unsafe_set b i c; fill (i - 1) r in
     fill (n - 1) cs;
     Bytes.unsafe_to_string b)".

Set Extraction Output Directory "extraction".
Extraction "rx.ml" rx_outcomes outcome_lines rx_file_text writeq_text read_clauses term_eqb.
