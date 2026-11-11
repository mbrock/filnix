(** The stdlib's constants that the λANF lowering realizes itself
    (docs/lambda-anf.md, M3): CertiRocq leaves each as a primitive
    (`Eprim`), and AnfLower.v's [prim_table] lowers its target, inline
    or as a call of anf_prims.c, on the represented integers,
    characters and strings. A program whose λANF is tapped imports this
    file; Rocq's extraction to OCaml, the reference, does not, so the
    same Gallina runs there.

    Each target computes exactly what the constant's Gallina definition
    does, on every input: `nf_sub0` is the truncated subtraction of `N`
    and `nat`, `nf_sub1` and `nf_pred1` those of `positive`, and the
    divisions of `Z` round down and give 0 and the dividend for a
    divisor of 0. anf/lower/tests/SelfTest.v holds them to [vm_compute]
    on values across 2^30, 2^31, 2^32 and 2^64. *)

From Stdlib Require Import ZArith NArith Ascii String List.
From CertiRocq.Plugin Require Import CertiRocq.

CertiRocq Register [
  Z.add => "nf_add", Z.sub => "nf_sub", Z.mul => "nf_mul", Z.opp => "nf_neg",
  Z.succ => "nf_succ", Z.pred => "nf_pred", Z.abs => "nf_abs",
  Z.compare => "nf_compare", Z.eqb => "nf_eqb", Z.ltb => "nf_ltb", Z.leb => "nf_leb",
  Z.max => "nf_max", Z.min => "nf_min",
  Z.div => "nf_div", Z.modulo => "nf_mod", Z.quot => "nf_quot", Z.rem => "nf_rem",
  Z.div_eucl => "nf_div_eucl", Z.pow => "nf_pow",
  Z.shiftl => "nf_shiftl", Z.shiftr => "nf_shiftr",
  Z.land => "nf_land", Z.lor => "nf_lor", Z.lxor => "nf_lxor",
  Z.testbit => "nf_testbit", Z.even => "nf_even", Z.odd => "nf_odd",
  Z.of_nat => "nf_id", Z.to_nat => "nf_max0", Z.of_N => "nf_id", Z.to_N => "nf_max0",
  Z.abs_nat => "nf_abs", Z.abs_N => "nf_abs",
  Pos.add => "nf_add", Pos.mul => "nf_mul", Pos.sub => "nf_sub1", Pos.pred => "nf_pred1",
  Pos.succ => "nf_succ", Pos.compare => "nf_compare", Pos.eqb => "nf_eqb",
  Pos.ltb => "nf_ltb", Pos.leb => "nf_leb", Pos.max => "nf_max", Pos.min => "nf_min",
  Pos.to_nat => "nf_id", Pos.of_succ_nat => "nf_succ",
  N.add => "nf_add", N.sub => "nf_sub0", N.mul => "nf_mul", N.pred => "nf_pred0",
  N.succ => "nf_succ", N.compare => "nf_compare", N.eqb => "nf_eqb",
  N.ltb => "nf_ltb", N.leb => "nf_leb", N.max => "nf_max", N.min => "nf_min",
  N.div => "nf_div", N.modulo => "nf_mod", N.div_eucl => "nf_div_eucl", N.pow => "nf_pow",
  N.shiftl => "nf_shiftl", N.shiftr => "nf_shiftr",
  N.land => "nf_land", N.lor => "nf_lor", N.lxor => "nf_lxor", N.testbit => "nf_testbit",
  N.of_nat => "nf_id", N.to_nat => "nf_id",
  Nat.add => "nf_add", Nat.sub => "nf_sub0", Nat.mul => "nf_mul", Nat.pred => "nf_pred0",
  Nat.succ => "nf_succ", Nat.compare => "nf_compare", Nat.eqb => "nf_eqb",
  Nat.ltb => "nf_ltb", Nat.leb => "nf_leb", Nat.max => "nf_max", Nat.min => "nf_min",
  Nat.div => "nf_div", Nat.modulo => "nf_mod", Nat.pow => "nf_pow",
  Nat.even => "nf_even", Nat.odd => "nf_odd",
  List.length => "nf_list_length",
  nat_of_ascii => "nf_id", N_of_ascii => "nf_id",
  ascii_of_nat => "nf_ascii_of_nat", ascii_of_N => "nf_ascii_of_nat",
  ascii_of_byte => "nf_id", byte_of_ascii => "nf_id",
  Ascii.eqb => "nf_ascii_eqb", Ascii.compare => "nf_ascii_compare",
  String.eqb => "nf_str_eqb", String.compare => "nf_str_compare",
  String.append => "nf_str_append", String.length => "nf_str_length",
  String.concat => "nf_str_concat", String.substring => "nf_substring",
  string_of_list_ascii => "nf_str_of_list", list_ascii_of_string => "nf_list_of_str"
] Include [ "anf_prims.h" ].
