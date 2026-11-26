(** Extraction of the Gallina C frontend to OCaml.

    Integers become Zarith big integers so 64-bit and 128-bit C constants keep
    exact values; [nat] fuel and lengths become OCaml [int]; character and
    string-building primitives map directly to OCaml [Char] and [Bytes]. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatInt.
From Stdlib Require Import ZArith List String Ascii.
From Frontend Require Import CAst CAttrs CLex CParse CCanon.

Extract Inlined Constant Ascii.eqb => "(=)".
Extract Inlined Constant String.eqb => "String.equal".
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant String.length => "String.length".
Extract Constant String.get =>
  "(fun i s -> if i >= 0 && i < String.length s then Some (String.unsafe_get s i) else None)".
Extract Constant String.substring =>
  "(fun start len s ->
     let n = String.length s in
     if start >= n then """"
     else
       let k = min len (n - start) in
       if k <= 0 then """" else String.sub s start k)".

Extract Constant CAttrs.z_to_string => "Big_int_Z.string_of_big_int".

Extract Constant CLex.code => "Char.code".
Extract Constant CLex.byte => "Char.chr".
Extract Constant CLex.string_of_rev =>
  "(fun cs ->
     let n = List.length cs in
     let b = Bytes.create n in
     let rec fill i = function
       | [] -> ()
       | c :: r -> Bytes.unsafe_set b i c; fill (i - 1) r in
     fill (n - 1) cs;
     Bytes.unsafe_to_string b)".

Extract Constant CParse.env_string_hash =>
  "(fun s h -> Big_int_Z.big_int_of_int
     ((Hashtbl.hash s + 31 * Big_int_Z.int_of_big_int h) land 0xFFFFF))".

Extract Constant Z.to_nat =>
  "(fun z -> if Big_int_Z.sign_big_int z <= 0 then 0 else Big_int_Z.int_of_big_int z)".
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".

Extract Inlined Constant List.length => "List.length".

Set Extraction Output Directory "extraction".
Extraction "nanofil_frontend.ml"
  CLex.lex_chars CLex.c23_tokens
  CParse.c_parse CParse.c_constant_expression
  CCanon.emit_token CCanon.emit_item.
