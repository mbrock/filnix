(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_fn___strlen : func :=
  ir_fn{ "export" "__strlen"(P %"v0") -> (RClass L) {
  @"start":
    %"v4" : L = Ptoi %"v0";
    %"v9" : L = And %"v4", #18446744073709551608;
    %"lc.2" : L = Sub %"v9", %"v4";
    %"v10" = %"v0" +p %"lc.2";
    %"chk0" : A = (Check 0 8 Read 1) %"v10";
    %"v13" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v6" : L = And %"v13", #9187201950435737471;
    %"iw_1.v8" : L = Add %"iw_1.v6", #9187201950435737471;
    %"iw_1.v10" : L = Or %"iw_1.v8", %"v13";
    %"iw_1.v12" : L = Or %"iw_1.v10", #9187201950435737471;
    %"iw_1.v13" : L = Xor %"iw_1.v12", #(-1);
    %"iw_2.v10" : L = And %"v4", #7;
    %"iw_2.v11" : L = Shl %"iw_2.v10", #3;
    %"iw_2.v12" : L = Shr %"iw_1.v13", %"iw_2.v11";
    %"v23" : W = (Cmp Ne L) %"iw_2.v12", #0
    => br %"v23" ? "iw_3.start" : "L28";
  @"iw_3.start":
    %"iw_3.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_2.v12", #0
    => br %"iw_3.iw_1.iw_1.v6" ? "iw_3.iw_1.iw_1.L4" : "iw_3.iw_1.iw_1.L3";
  @"iw_3.iw_1.iw_1.L3":
    %"iw_3.iw_1.iw_1.v8" : L = Neg %"iw_2.v12";
    %"iw_3.iw_1.iw_1.v9" : L = And %"iw_2.v12", %"iw_3.iw_1.iw_1.v8";
    %"iw_3.iw_1.iw_1.v10" : L = Sub %"iw_3.iw_1.iw_1.v9", #1;
    %"iw_3.iw_1.iw_1.v11" : L = Shr %"iw_3.iw_1.iw_1.v10", #1;
    %"iw_3.iw_1.iw_1.v12" : L = And %"iw_3.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_3.iw_1.iw_1.v13" : L = Sub %"iw_3.iw_1.iw_1.v10", %"iw_3.iw_1.iw_1.v12";
    %"iw_3.iw_1.iw_1.v14" : L = And %"iw_3.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_3.iw_1.iw_1.v15" : L = Shr %"iw_3.iw_1.iw_1.v13", #2;
    %"iw_3.iw_1.iw_1.v16" : L = And %"iw_3.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_3.iw_1.iw_1.v17" : L = Add %"iw_3.iw_1.iw_1.v14", %"iw_3.iw_1.iw_1.v16";
    %"iw_3.iw_1.iw_1.v18" : L = Shr %"iw_3.iw_1.iw_1.v17", #4;
    %"iw_3.iw_1.iw_1.v19" : L = Add %"iw_3.iw_1.iw_1.v17", %"iw_3.iw_1.iw_1.v18";
    %"iw_3.iw_1.iw_1.v20" : L = And %"iw_3.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_3.iw_1.iw_1.v21" : L = Mul %"iw_3.iw_1.iw_1.v20", #72340172838076673;
    %"iw_3.iw_1.iw_1.v22" : L = Shr %"iw_3.iw_1.iw_1.v21", #56
    => goto "iw_3.iw_1.iw_1.L4";
  @"iw_3.iw_1.iw_1.L4" [%"iw_3.iw_1.iw_1.v23" : W = phi("iw_3.iw_1.iw_1.L3" => %"iw_3.iw_1.iw_1.v22", "iw_3.start" => #64)]:
    %"iw_3.iw_1.v27" : W = Shr %"iw_3.iw_1.iw_1.v23", #3;
    %"v26" : L = (Ext Uw) %"iw_3.iw_1.v27"
    => ret %"v26";
  @"L28" [%"pr.1" : P = phi("L28" => %"v32", "start" => %"v10")]:
    %"v32" = %"pr.1" +p #8;
    %"chk1" : A = (Check 0 8 Read 1) %"v32";
    %"v33" : L = (RawLoad LdL 0) %"chk1";
    %"iw_4.iw_1.v8" : L = Sub %"v33", #72340172838076673;
    %"iw_4.iw_1.v10" : L = Xor %"v33", #(-1);
    %"iw_4.iw_1.v11" : L = And %"iw_4.iw_1.v8", %"iw_4.iw_1.v10";
    %"iw_4.iw_1.v13" : L = And %"iw_4.iw_1.v11", #9259542123273814144;
    %"v37" : W = (Cmp Eq L) %"iw_4.iw_1.v13", #0
    => br %"v37" ? poll "L28" : "iw_5.start";
  @"iw_5.start":
    => br %"v37" ? "iw_5.iw_3.iw_1.iw_1.L4" : "iw_5.iw_3.iw_1.iw_1.L3";
  @"iw_5.iw_3.iw_1.iw_1.L3":
    %"iw_5.iw_3.iw_1.iw_1.v8" : L = Neg %"iw_4.iw_1.v13";
    %"iw_5.iw_3.iw_1.iw_1.v9" : L = And %"iw_4.iw_1.v13", %"iw_5.iw_3.iw_1.iw_1.v8";
    %"iw_5.iw_3.iw_1.iw_1.v10" : L = Sub %"iw_5.iw_3.iw_1.iw_1.v9", #1;
    %"iw_5.iw_3.iw_1.iw_1.v11" : L = Shr %"iw_5.iw_3.iw_1.iw_1.v10", #1;
    %"iw_5.iw_3.iw_1.iw_1.v12" : L = And %"iw_5.iw_3.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_5.iw_3.iw_1.iw_1.v13" : L = Sub %"iw_5.iw_3.iw_1.iw_1.v10", %"iw_5.iw_3.iw_1.iw_1.v12";
    %"iw_5.iw_3.iw_1.iw_1.v14" : L = And %"iw_5.iw_3.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_5.iw_3.iw_1.iw_1.v15" : L = Shr %"iw_5.iw_3.iw_1.iw_1.v13", #2;
    %"iw_5.iw_3.iw_1.iw_1.v16" : L = And %"iw_5.iw_3.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_5.iw_3.iw_1.iw_1.v17" : L = Add %"iw_5.iw_3.iw_1.iw_1.v14", %"iw_5.iw_3.iw_1.iw_1.v16";
    %"iw_5.iw_3.iw_1.iw_1.v18" : L = Shr %"iw_5.iw_3.iw_1.iw_1.v17", #4;
    %"iw_5.iw_3.iw_1.iw_1.v19" : L = Add %"iw_5.iw_3.iw_1.iw_1.v17", %"iw_5.iw_3.iw_1.iw_1.v18";
    %"iw_5.iw_3.iw_1.iw_1.v20" : L = And %"iw_5.iw_3.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_5.iw_3.iw_1.iw_1.v21" : L = Mul %"iw_5.iw_3.iw_1.iw_1.v20", #72340172838076673;
    %"iw_5.iw_3.iw_1.iw_1.v22" : L = Shr %"iw_5.iw_3.iw_1.iw_1.v21", #56
    => goto "iw_5.iw_3.iw_1.iw_1.L4";
  @"iw_5.iw_3.iw_1.iw_1.L4" [%"iw_5.iw_3.iw_1.iw_1.v23" : W = phi("iw_5.iw_3.iw_1.iw_1.L3" => %"iw_5.iw_3.iw_1.iw_1.v22", "iw_5.start" => #64)]:
    %"iw_5.iw_3.iw_1.v27" : W = Shr %"iw_5.iw_3.iw_1.iw_1.v23", #3;
    %"v41" : L = (Ext Uw) %"iw_5.iw_3.iw_1.v27";
    %"v42" = %"v32" +p %"v41";
    %"v44" : L = Ptoi %"v42";
    %"v46" : L = Sub %"v44", %"v4"
    => ret %"v46"
} }.

Definition hi_fn___GI_strrchr : func :=
  ir_fn{ "export" "__GI_strrchr"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    call %"v7" : L = $"__GI_strlen"(P %"v0");
    %"v8" : L = Add %"v7", #1;
    call %"v9" : P = $"__GI___memrchr"(P %"v0", W %"v2", L %"v8")
    => ret %"v9"
} }.
