(** Extraction of the Gallina C frontend and lowering passes to OCaml.

    Integers become Zarith big integers so 64-bit and 128-bit C constants keep
    exact values; [nat] fuel and lengths become OCaml [int]; character,
    hashing, ordering, and string-building primitives map directly to OCaml
    primitives without pulling in [String] or [Ascii] internals. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatInt.
From Stdlib Require Import ZArith List String Ascii.
From Nanofil Require Import Term Maps.
From Backend Require Import Text Order Asm Compile.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp
  CTypeAst CTypeTables CTypes CTypeCanon CLaunder CLowerState CLowerInit
  CLowerAsm CLowerBuiltins CLower CLayouts.

Extract Inlined Constant Ascii.eqb => "(=)".
Extract Inlined Constant String.eqb => "String.equal".
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant String.concat => "String.concat".
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

Extract Constant Maps.string_hash =>
  "(fun s h -> Big_int_Z.big_int_of_int
     ((Hashtbl.hash s + 31 * Big_int_Z.int_of_big_int h) land 0xFFFFF))".

Extract Inlined Constant Order.atom_compare =>
  "(fun a b -> let c = Stdlib.compare (a : string) b in if c < 0 then Lt else if c = 0 then Eq else Gt)".

Extract Constant Z.to_nat =>
  "(fun z -> if Big_int_Z.sign_big_int z <= 0 then 0 else Big_int_Z.int_of_big_int z)".
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".

Extract Inlined Constant List.length => "List.length".

Set Extraction Output Directory "extraction".
Extraction "nanofil_frontend.ml"
  CLex.lex_chars CLex.c23_tokens
  CIeee.ieee_binary CIeee.ieee_neg CIeee.ieee_sqrt CIeee.ieee_convert
  CIeee.ieee_from_int CIeee.ieee_to_int CIeee.ieee_compare
  CIeee.ieee_parse CIeee.ieee_decimal
  CParse.c_parse CParse.c_constant_expression
  CCanon.emit_token CCanon.emit_item
  CPp.preprocess_file CPp.make_pp_env CPp.parse_include_dirs
  CPp.default_feature_queries CPp.add_cli_define CPp.prepend_include_dirs
  CPp.pp_value
  CTypeAst.default_type_opts CTypeAst.mkCTypeOpts
  CTypeCanon.check_tu_items
  CLaunder.launder_module
  CLowerState.default_lower_opts CLowerState.mkCLowerOpts
  CLowerState.ir_module_lines CLowerState.ir_item_line
  CLowerState.l_tr_msg CLowerState.unknown_loc
  CLowerAsm.c_toplevel_asm CLowerAsm.without_symver_aliases
  CLower.c_module_opts CLower.c_module
  CLayouts.module_layouts_canon
  Compile.compile Compile.compile_promoted Compile.compile_allocated
  Asm.rev_lines_parts.
