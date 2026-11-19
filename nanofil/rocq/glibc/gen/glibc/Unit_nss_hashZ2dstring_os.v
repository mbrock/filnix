(** This file defines checked IR from glibc’s `nss/hash-string.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___hash_string : func :=
  ir_fn{ "export" "__hash_string"(P %"v0") -> (RClass L) {
  @"start":
    => goto "L6";
  @"L6" [%"pr.3" : P = phi("start" => %"v0", "L25" => %"v16", "L7" => %"v16"); %"pr.2" : L = phi("start" => #0, "L25" => %"v37", "L7" => %"v20")]:
    %"chk0" : A = (Check 0 1 Read 1) %"pr.3";
    %"v10" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v11" : W = (Cmp Ne W) %"v10", #0
    => br %"v11" ? "L7" : "L8";
  @"L7":
    %"v13" : L = Shl %"pr.2", #4;
    %"v16" = %"pr.3" +p #1;
    %"v17" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v18" : W = (Ext Ub) %"v17";
    %"v19" : L = (Ext Uw) %"v18";
    %"v20" : L = Add %"v13", %"v19";
    %"v24" : L = And %"v20", #4026531840;
    %"v29" : W = (Cmp Ne L) %"v24", #0
    => br %"v29" ? "L25" : poll "L6";
  @"L25":
    %"v33" : L = Shr %"v24", #24;
    %"v34" : L = Xor %"v20", %"v33";
    %"v37" : L = Xor %"v34", %"v24"
    => goto poll "L6";
  @"L8":
    => ret %"pr.2"
} }.
