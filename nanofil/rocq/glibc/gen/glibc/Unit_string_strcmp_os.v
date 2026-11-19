(** This file defines checked IR from glibc’s `string/strcmp.os` object.
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

Definition fn___GI_strcmp : func :=
  ir_fn{ "export" "__GI_strcmp"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v6" : L = Ptoi %"v0";
    %"v7" : L = Neg %"v6";
    %"v8" : L = And %"v7", #7
    => goto "L10";
  @"L10" [%"pr.3" : W = phi("L12" => %"v46", "start" => #0); %"pr.2" : P = phi("L12" => %"v25", "start" => %"v2"); %"pr.1" : P = phi("L12" => %"v20", "start" => %"v0")]:
    %"v16" : L = (Ext Sw) %"pr.3";
    %"v17" : W = (Cmp Ult L) %"v16", %"v8"
    => br %"v17" ? "L11" : "L13";
  @"L11":
    %"v20" = %"pr.1" +p #1;
    %"chk0" : A = (Check 0 1 Read 1) %"pr.1";
    %"v21" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v22" : W = (Ext Ub) %"v21";
    %"v25" = %"pr.2" +p #1;
    %"chk1" : A = (Check 0 1 Read 1) %"pr.2";
    %"v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v27" : W = (Ext Ub) %"v26";
    %"v31" : W = Sub %"v22", %"v27";
    %"v36" : W = (Cmp Eq W) %"v22", #0
    => br %"v36" ? "L38" : "L37";
  @"L37":
    %"v40" : W = (Cmp Ne W) %"v31", #0
    => goto "L38";
  @"L38" [%"v42" : W = phi("L11" => #1, "L37" => %"v40")]:
    => br %"v42" ? "L32" : "L12";
  @"L32":
    => ret %"v31";
  @"L12":
    %"v46" : W = Add %"pr.3", #1
    => goto poll "L10";
  @"L13":
    %"v51" = %"pr.1" +p #8;
    %"chk2" : A = (Check 0 8 Read 1) %"pr.1";
    %"v52" : L = (RawLoad LdL 0) %"chk2";
    %"v55" : L = Ptoi %"pr.2";
    %"v56" : L = And %"v55", #7;
    %"v61" : W = (Cmp Eq L) %"v56", #0
    => br %"v61" ? "iw_1.start" : "L58";
  @"iw_1.start":
    %"iw_1.v8" = %"pr.2" +p #8;
    %"chk3" : A = (Check 0 8 Read 1) %"pr.2";
    %"iw_1.v9" : L = (RawLoad LdL 0) %"chk3"
    => goto "iw_1.L10";
  @"iw_1.L10" [%"iw_1.pr.4" : L = phi("iw_1.L18" => %"iw_1.v28", "iw_1.start" => %"iw_1.v9"); %"iw_1.pr.3" : L = phi("iw_1.L18" => %"iw_1.v25", "iw_1.start" => %"v52"); %"iw_1.pr.2" : P = phi("iw_1.L18" => %"iw_1.v27", "iw_1.start" => %"iw_1.v8"); %"iw_1.pr.1" : P = phi("iw_1.L18" => %"iw_1.v24", "iw_1.start" => %"v51")]:
    %"iw_1.v15" : W = (Cmp Eq L) %"iw_1.pr.3", %"iw_1.pr.4"
    => br %"iw_1.v15" ? "iw_1.iw_1.start" : "iw_1.iw_2.start";
  @"iw_1.iw_1.start":
    %"iw_1.iw_1.iw_1.v8" : L = Sub %"iw_1.pr.3", #72340172838076673;
    %"iw_1.iw_1.iw_1.v10" : L = Xor %"iw_1.pr.3", #(-1);
    %"iw_1.iw_1.iw_1.v11" : L = And %"iw_1.iw_1.iw_1.v8", %"iw_1.iw_1.iw_1.v10";
    %"iw_1.iw_1.iw_1.v13" : L = And %"iw_1.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_1.iw_1.v4" : W = (Cmp Ne L) %"iw_1.iw_1.iw_1.v13", #0
    => br %"iw_1.iw_1.v4" ? "L59" : "iw_1.L18";
  @"iw_1.L18":
    %"iw_1.v24" = %"iw_1.pr.1" +p #8;
    %"chk4" : A = (Check 0 8 Read 1) %"iw_1.pr.1";
    %"iw_1.v25" : L = (RawLoad LdL 0) %"chk4";
    %"iw_1.v27" = %"iw_1.pr.2" +p #8;
    %"chk5" : A = (Check 0 8 Read 1) %"iw_1.pr.2";
    %"iw_1.v28" : L = (RawLoad LdL 0) %"chk5"
    => goto poll "iw_1.L10";
  @"iw_1.iw_2.start":
    %"iw_1.iw_2.iw_1.iw_1.v9" : L = Xor %"iw_1.pr.3", %"iw_1.pr.4";
    %"iw_1.iw_2.iw_1.iw_1.v13" : L = And %"iw_1.pr.3", #9187201950435737471;
    %"iw_1.iw_2.iw_1.iw_1.v15" : L = Add %"iw_1.iw_2.iw_1.iw_1.v13", #9187201950435737471;
    %"iw_1.iw_2.iw_1.iw_1.v17" : L = Or %"iw_1.iw_2.iw_1.iw_1.v15", %"iw_1.pr.3";
    %"iw_1.iw_2.iw_1.iw_1.v21" : L = And %"iw_1.iw_2.iw_1.iw_1.v9", #9187201950435737471;
    %"iw_1.iw_2.iw_1.iw_1.v23" : L = Add %"iw_1.iw_2.iw_1.iw_1.v21", #9187201950435737471;
    %"iw_1.iw_2.iw_1.iw_1.v25" : L = Or %"iw_1.iw_2.iw_1.iw_1.v23", %"iw_1.iw_2.iw_1.iw_1.v9";
    %"iw_1.iw_2.iw_1.iw_1.v28" : L = Xor %"iw_1.iw_2.iw_1.iw_1.v17", #(-1);
    %"iw_1.iw_2.iw_1.iw_1.v29" : L = Or %"iw_1.iw_2.iw_1.iw_1.v25", %"iw_1.iw_2.iw_1.iw_1.v28";
    %"iw_1.iw_2.iw_1.iw_1.v32" : L = And %"iw_1.iw_2.iw_1.iw_1.v29", #9259542123273814144;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_1.iw_2.iw_1.iw_1.v32", #0
    => br %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v6" ? "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4" : "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3";
  @"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3":
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v8" : L = Neg %"iw_1.iw_2.iw_1.iw_1.v32";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v9" : L = And %"iw_1.iw_2.iw_1.iw_1.v32", %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v8";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v10" : L = Sub %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v9", #1;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v11" : L = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v10", #1;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v12" : L = And %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v13" : L = Sub %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v10", %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v12";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v14" : L = And %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v15" : L = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v13", #2;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v16" : L = And %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v17" : L = Add %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v14", %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v16";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v18" : L = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v17", #4;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v19" : L = Add %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v17", %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v18";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v20" : L = And %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v21" : L = Mul %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v20", #72340172838076673;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v22" : L = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v21", #56
    => goto "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4";
  @"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4" [%"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v23" : W = phi("iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3" => %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v22", "iw_1.iw_2.start" => #64)]:
    %"iw_1.iw_2.iw_1.iw_2.iw_1.v27" : W = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v23", #3;
    %"iw_1.iw_2.iw_2.v10" : W = Shl %"iw_1.iw_2.iw_1.iw_2.iw_1.v27", #3;
    %"iw_1.iw_2.iw_2.v11" : L = Shr %"iw_1.pr.3", %"iw_1.iw_2.iw_2.v10";
    %"iw_1.iw_2.iw_2.v12" : W = (Ext Ub) %"iw_1.iw_2.iw_2.v11";
    %"iw_1.iw_2.iw_3.v11" : L = Shr %"iw_1.pr.4", %"iw_1.iw_2.iw_2.v10";
    %"iw_1.iw_2.iw_3.v12" : W = (Ext Ub) %"iw_1.iw_2.iw_3.v11";
    %"iw_1.iw_2.v16" : W = Sub %"iw_1.iw_2.iw_2.v12", %"iw_1.iw_2.iw_3.v12"
    => goto "L59";
  @"L58":
    (Flight (a "v69") Sub [(FAddress (t "pr.2")); (FValue (t "v56"))] (LowerOf (t "pr.2")));
    %"iw_2.v10" = %"v69" +p #8;
    %"chk6" : A = (Check 0 8 Read 1) %"v69";
    %"iw_2.v11" : L = (RawLoad LdL 0) %"chk6";
    %"iw_2.v14" : L = Shl %"v56", #3;
    %"iw_2.v18" : L = Sub #64, %"iw_2.v14";
    %"iw_2.v22" : L = Shr %"iw_2.v11", %"iw_2.v14";
    %"iw_2.v26" : L = Shl #18446744073709551615, %"iw_2.v18";
    %"iw_2.v27" : L = Or %"iw_2.v22", %"iw_2.v26";
    %"iw_2.iw_1.iw_1.v8" : L = Sub %"iw_2.v27", #72340172838076673;
    %"iw_2.iw_1.iw_1.v10" : L = Xor %"iw_2.v27", #(-1);
    %"iw_2.iw_1.iw_1.v11" : L = And %"iw_2.iw_1.iw_1.v8", %"iw_2.iw_1.iw_1.v10";
    %"iw_2.iw_1.iw_1.v13" : L = And %"iw_2.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_2.v34" : W = (Cmp Eq L) %"iw_2.iw_1.iw_1.v13", #0
    => br %"iw_2.v34" ? "iw_2.L36" : "iw_2.L30";
  @"iw_2.L36" [%"iw_2.pr.5" : L = phi("iw_2.L61" => %"iw_2.v41", "L58" => %"iw_2.v11"); %"iw_2.pr.4" : L = phi("iw_2.L61" => %"iw_2.v68", "L58" => %"v52"); %"iw_2.pr.2" : P = phi("iw_2.L61" => %"iw_2.v40", "L58" => %"iw_2.v10"); %"iw_2.pr.1" : P = phi("iw_2.L61" => %"iw_2.v67", "L58" => %"v51")]:
    %"iw_2.v40" = %"iw_2.pr.2" +p #8;
    %"chk7" : A = (Check 0 8 Read 1) %"iw_2.pr.2";
    %"iw_2.v41" : L = (RawLoad LdL 0) %"chk7";
    %"iw_2.v44" : L = Shr %"iw_2.pr.5", %"iw_2.v14";
    %"iw_2.v47" : L = Shl %"iw_2.v41", %"iw_2.v18";
    %"iw_2.v48" : L = Or %"iw_2.v44", %"iw_2.v47";
    %"iw_2.v54" : W = (Cmp Ne L) %"iw_2.pr.4", %"iw_2.v48"
    => br %"iw_2.v54" ? "iw_2.iw_2.start" : "iw_2.iw_3.start";
  @"iw_2.iw_2.start":
    %"iw_2.iw_2.iw_1.iw_1.v9" : L = Xor %"iw_2.pr.4", %"iw_2.v48";
    %"iw_2.iw_2.iw_1.iw_1.v13" : L = And %"iw_2.pr.4", #9187201950435737471;
    %"iw_2.iw_2.iw_1.iw_1.v15" : L = Add %"iw_2.iw_2.iw_1.iw_1.v13", #9187201950435737471;
    %"iw_2.iw_2.iw_1.iw_1.v17" : L = Or %"iw_2.iw_2.iw_1.iw_1.v15", %"iw_2.pr.4";
    %"iw_2.iw_2.iw_1.iw_1.v21" : L = And %"iw_2.iw_2.iw_1.iw_1.v9", #9187201950435737471;
    %"iw_2.iw_2.iw_1.iw_1.v23" : L = Add %"iw_2.iw_2.iw_1.iw_1.v21", #9187201950435737471;
    %"iw_2.iw_2.iw_1.iw_1.v25" : L = Or %"iw_2.iw_2.iw_1.iw_1.v23", %"iw_2.iw_2.iw_1.iw_1.v9";
    %"iw_2.iw_2.iw_1.iw_1.v28" : L = Xor %"iw_2.iw_2.iw_1.iw_1.v17", #(-1);
    %"iw_2.iw_2.iw_1.iw_1.v29" : L = Or %"iw_2.iw_2.iw_1.iw_1.v25", %"iw_2.iw_2.iw_1.iw_1.v28";
    %"iw_2.iw_2.iw_1.iw_1.v32" : L = And %"iw_2.iw_2.iw_1.iw_1.v29", #9259542123273814144;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_2.iw_2.iw_1.iw_1.v32", #0
    => br %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v6" ? "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4" : "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3";
  @"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3":
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v8" : L = Neg %"iw_2.iw_2.iw_1.iw_1.v32";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v9" : L = And %"iw_2.iw_2.iw_1.iw_1.v32", %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v8";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v10" : L = Sub %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v9", #1;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v11" : L = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v10", #1;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v12" : L = And %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v13" : L = Sub %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v10", %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v12";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v14" : L = And %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v15" : L = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v13", #2;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v16" : L = And %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v17" : L = Add %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v14", %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v16";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v18" : L = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v17", #4;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v19" : L = Add %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v17", %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v18";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v20" : L = And %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v21" : L = Mul %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v20", #72340172838076673;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v22" : L = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v21", #56
    => goto "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4";
  @"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4" [%"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v23" : W = phi("iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3" => %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v22", "iw_2.iw_2.start" => #64)]:
    %"iw_2.iw_2.iw_1.iw_2.iw_1.v27" : W = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v23", #3;
    %"iw_2.iw_2.iw_2.v10" : W = Shl %"iw_2.iw_2.iw_1.iw_2.iw_1.v27", #3;
    %"iw_2.iw_2.iw_2.v11" : L = Shr %"iw_2.pr.4", %"iw_2.iw_2.iw_2.v10";
    %"iw_2.iw_2.iw_2.v12" : W = (Ext Ub) %"iw_2.iw_2.iw_2.v11";
    %"iw_2.iw_2.iw_3.v11" : L = Shr %"iw_2.v48", %"iw_2.iw_2.iw_2.v10";
    %"iw_2.iw_2.iw_3.v12" : W = (Ext Ub) %"iw_2.iw_2.iw_3.v11";
    %"iw_2.iw_2.v16" : W = Sub %"iw_2.iw_2.iw_2.v12", %"iw_2.iw_2.iw_3.v12"
    => goto "L59";
  @"iw_2.iw_3.start":
    %"iw_2.iw_3.iw_1.v8" : L = Sub %"iw_2.v41", #72340172838076673;
    %"iw_2.iw_3.iw_1.v10" : L = Xor %"iw_2.v41", #(-1);
    %"iw_2.iw_3.iw_1.v11" : L = And %"iw_2.iw_3.iw_1.v8", %"iw_2.iw_3.iw_1.v10";
    %"iw_2.iw_3.iw_1.v13" : L = And %"iw_2.iw_3.iw_1.v11", #9259542123273814144;
    %"iw_2.iw_3.v4" : W = (Cmp Ne L) %"iw_2.iw_3.iw_1.v13", #0
    => br %"iw_2.iw_3.v4" ? "iw_2.iw_4.start" : "iw_2.L61";
  @"iw_2.L61":
    %"iw_2.v67" = %"iw_2.pr.1" +p #8;
    %"chk8" : A = (Check 0 8 Read 1) %"iw_2.pr.1";
    %"iw_2.v68" : L = (RawLoad LdL 0) %"chk8"
    => goto poll "iw_2.L36";
  @"iw_2.iw_4.start":
    %"iw_2.iw_4.iw_1.v8" : L = Sub %"iw_2.pr.4", #72340172838076673;
    %"iw_2.iw_4.iw_1.v10" : L = Xor %"iw_2.pr.4", #(-1);
    %"iw_2.iw_4.iw_1.v11" : L = And %"iw_2.iw_4.iw_1.v8", %"iw_2.iw_4.iw_1.v10";
    %"iw_2.iw_4.iw_1.v13" : L = And %"iw_2.iw_4.iw_1.v11", #9259542123273814144;
    %"iw_2.iw_4.v4" : W = (Cmp Ne L) %"iw_2.iw_4.iw_1.v13", #0
    => br %"iw_2.iw_4.v4" ? "L59" : "iw_2.L72";
  @"iw_2.L72":
    %"chk9" : A = (Check 0 8 Read 1) %"iw_2.pr.1";
    %"iw_2.v79" : L = (RawLoad LdL 0) %"chk9";
    %"iw_2.v82" : L = Shr %"iw_2.v41", %"iw_2.v14";
    %"iw_2.v84" : W = Shl #0, %"iw_2.v18";
    %"iw_2.v85" : L = (Ext Sw) %"iw_2.v84";
    %"iw_2.v86" : L = Or %"iw_2.v82", %"iw_2.v85"
    => goto "iw_2.L30";
  @"iw_2.L30" [%"iw_2.pr.6" : L = phi("iw_2.L72" => %"iw_2.v86", "L58" => %"iw_2.v27"); %"iw_2.pr.3" : L = phi("iw_2.L72" => %"iw_2.v79", "L58" => %"v52")]:
    %"iw_2.iw_5.iw_1.iw_1.v9" : L = Xor %"iw_2.pr.3", %"iw_2.pr.6";
    %"iw_2.iw_5.iw_1.iw_1.v13" : L = And %"iw_2.pr.3", #9187201950435737471;
    %"iw_2.iw_5.iw_1.iw_1.v15" : L = Add %"iw_2.iw_5.iw_1.iw_1.v13", #9187201950435737471;
    %"iw_2.iw_5.iw_1.iw_1.v17" : L = Or %"iw_2.iw_5.iw_1.iw_1.v15", %"iw_2.pr.3";
    %"iw_2.iw_5.iw_1.iw_1.v21" : L = And %"iw_2.iw_5.iw_1.iw_1.v9", #9187201950435737471;
    %"iw_2.iw_5.iw_1.iw_1.v23" : L = Add %"iw_2.iw_5.iw_1.iw_1.v21", #9187201950435737471;
    %"iw_2.iw_5.iw_1.iw_1.v25" : L = Or %"iw_2.iw_5.iw_1.iw_1.v23", %"iw_2.iw_5.iw_1.iw_1.v9";
    %"iw_2.iw_5.iw_1.iw_1.v28" : L = Xor %"iw_2.iw_5.iw_1.iw_1.v17", #(-1);
    %"iw_2.iw_5.iw_1.iw_1.v29" : L = Or %"iw_2.iw_5.iw_1.iw_1.v25", %"iw_2.iw_5.iw_1.iw_1.v28";
    %"iw_2.iw_5.iw_1.iw_1.v32" : L = And %"iw_2.iw_5.iw_1.iw_1.v29", #9259542123273814144;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_2.iw_5.iw_1.iw_1.v32", #0
    => br %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v6" ? "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4" : "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3";
  @"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3":
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v8" : L = Neg %"iw_2.iw_5.iw_1.iw_1.v32";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v9" : L = And %"iw_2.iw_5.iw_1.iw_1.v32", %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v8";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v10" : L = Sub %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v9", #1;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v11" : L = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v10", #1;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v12" : L = And %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v13" : L = Sub %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v10", %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v12";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v14" : L = And %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v15" : L = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v13", #2;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v16" : L = And %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v17" : L = Add %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v14", %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v16";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v18" : L = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v17", #4;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v19" : L = Add %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v17", %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v18";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v20" : L = And %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v21" : L = Mul %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v20", #72340172838076673;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v22" : L = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v21", #56
    => goto "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4";
  @"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4" [%"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v23" : W = phi("iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3" => %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v22", "iw_2.L30" => #64)]:
    %"iw_2.iw_5.iw_1.iw_2.iw_1.v27" : W = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v23", #3;
    %"iw_2.iw_5.iw_2.v10" : W = Shl %"iw_2.iw_5.iw_1.iw_2.iw_1.v27", #3;
    %"iw_2.iw_5.iw_2.v11" : L = Shr %"iw_2.pr.3", %"iw_2.iw_5.iw_2.v10";
    %"iw_2.iw_5.iw_2.v12" : W = (Ext Ub) %"iw_2.iw_5.iw_2.v11";
    %"iw_2.iw_5.iw_3.v11" : L = Shr %"iw_2.pr.6", %"iw_2.iw_5.iw_2.v10";
    %"iw_2.iw_5.iw_3.v12" : W = (Ext Ub) %"iw_2.iw_5.iw_3.v11";
    %"iw_2.iw_5.v16" : W = Sub %"iw_2.iw_5.iw_2.v12", %"iw_2.iw_5.iw_3.v12"
    => goto "L59";
  @"L59" [%"v73" : W = phi("iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4" => %"iw_1.iw_2.v16", "iw_1.iw_1.start" => #0, "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4" => %"iw_2.iw_2.v16", "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4" => %"iw_2.iw_5.v16", "iw_2.iw_4.start" => #0)]:
    => ret %"v73"
} }.

Definition item_strcmp : item :=
  (IAlias (a "strcmp") (a "export") (a "__GI_strcmp")).
