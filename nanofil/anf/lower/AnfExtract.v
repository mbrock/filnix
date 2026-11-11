(** Extraction of the λANF lowering (AnfLower.v) and of IrText.v's
    reader to OCaml, for the driver main.ml. The constants are
    extracted as the backend's extraction (rocq/backend/Extract.v)
    extracts them. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatInt.
From Stdlib Require Import ZArith.
From Nanofil Require Import Term Maps.
From Backend Require Import IrText.
From Anf Require Import AnfLower.

Extract Constant Maps.string_hash =>
  "(fun s h -> Big_int_Z.big_int_of_int
     ((Hashtbl.hash s + 31 * Big_int_Z.int_of_big_int h) land 0xFFFFF))".
Extract Constant Z.to_nat =>
  "(fun z -> if Big_int_Z.sign_big_int z <= 0 then 0 else Big_int_Z.int_of_big_int z)".
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".
Extract Inlined Constant length => "List.length".
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
Extraction "anf_lower.ml" lower text_clauses.
