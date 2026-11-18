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

Definition hello_image_fn___GI_strcmp : func :=
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

Definition hello_image_fn___GI_strcpy : func :=
  ir_fn{ "export" "__GI_strcpy"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"__GI___stpcpy"(P %"v0", P %"v2")
    => ret %"v0"
} }.

Definition hello_image_fn___GI_strcspn : func :=
  ir_fn{ "export" "__GI_strcspn"(P %"v0", P %"v2") -> (RClass L) {
  @"start":
    %"v33" : P = (Alloc 4) #256;
    %"chk0" : A = (Check 0 1 Read 1) %"v2";
    %"v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => br %"v10" ? "L14" : "L13";
  @"L13":
    %"v16" = %"v2" +p #1;
    %"chk1" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v18" : W = (Cmp Eq W) %"v17", #0
    => goto "L14";
  @"L14" [%"v22" : W = phi("start" => #1, "L13" => %"v18")]:
    => br %"v22" ? "L4" : "L6";
  @"L4":
    %"v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    call %"v27" : P = $"__GI___strchrnul"(P %"v0", W %"v26");
    %"v29" : L = Ptoi %"v27";
    %"v30" : L = Ptoi %"v0";
    %"v31" : L = Sub %"v29", %"v30"
    => ret %"v31";
  @"L6":
    call %"v35" : P = $"__GI_memset"(P %"v33", W #0, L #64);
    %"v37" = %"v35" +p #64;
    call %"v38" : P = $"__GI_memset"(P %"v37", W #0, L #64);
    %"v40" = %"v35" +p #128;
    call %"v41" : P = $"__GI_memset"(P %"v40", W #0, L #64);
    %"v43" = %"v35" +p #192;
    call %"v44" : P = $"__GI_memset"(P %"v43", W #0, L #64)
    => goto "L48";
  @"L48" [%"pr.2" : P = phi("L48" => %"v53", "L6" => %"v2")]:
    %"v53" = %"pr.2" +p #1;
    %"chk3" : A = (Check 0 1 Read 1) %"pr.2";
    %"v54" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"v55" : L = (Ext Uw) %"v54";
    %"v56" = %"v35" +p %"v55";
    %"chk4" : A = (Check 0 1 Write 1) %"v56";
    store Wb [%"chk4" + 0] <- #1
    => br %"v54" ? poll "L48" : "L50";
  @"L50":
    %"chk5" : A = (Check 0 1 Read 1) %"v0";
    %"v65" : W = (RawLoad (LdNarrow Ub) 0) %"chk5";
    %"v66" : L = (Ext Uw) %"v65";
    %"v67" = %"v35" +p %"v66";
    %"chk6" : A = (Check 0 1 Read 1) %"v67";
    %"v68" : W = (RawLoad (LdNarrow Ub) 0) %"chk6"
    => br %"v68" ? "L59" : "L61";
  @"L59":
    => ret #0;
  @"L61":
    %"v75" = %"v0" +p #1;
    %"chk7" : A = (HalfCheck Upper 0 1 Read 1) %"chk5", %"v75";
    %"v76" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v77" : L = (Ext Uw) %"v76";
    %"v78" = %"v35" +p %"v77";
    %"chk8" : A = (Check 0 1 Read 1) %"v78";
    %"v79" : W = (RawLoad (LdNarrow Ub) 0) %"chk8"
    => br %"v79" ? "L70" : "L72";
  @"L70":
    => ret #1;
  @"L72":
    %"v86" = %"v0" +p #2;
    %"chk9" : A = (HalfCheck Upper 0 1 Read 1) %"chk5", %"v86";
    %"v87" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"v88" : L = (Ext Uw) %"v87";
    %"v89" = %"v35" +p %"v88";
    %"chk10" : A = (Check 0 1 Read 1) %"v89";
    %"v90" : W = (RawLoad (LdNarrow Ub) 0) %"chk10"
    => br %"v90" ? "L81" : "L83";
  @"L81":
    => ret #2;
  @"L83":
    %"v97" = %"v0" +p #3;
    %"chk11" : A = (HalfCheck Upper 0 1 Read 1) %"chk5", %"v97";
    %"v98" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"v99" : L = (Ext Uw) %"v98";
    %"v100" = %"v35" +p %"v99";
    %"chk12" : A = (Check 0 1 Read 1) %"v100";
    %"v101" : W = (RawLoad (LdNarrow Ub) 0) %"chk12"
    => br %"v101" ? "L92" : "L94";
  @"L92":
    => ret #3;
  @"L94":
    %"v104" : L = Ptoi %"v0";
    %"v106" : L = And %"v104", #18446744073709551612;
    %"lc.2" : L = Sub %"v106", %"v104";
    %"v107" = %"v0" +p %"lc.2"
    => goto "L112";
  @"L112" [%"pr.1" : P = phi("L112" => %"v116", "L94" => %"v107")]:
    %"v116" = %"pr.1" +p #4;
    %"chk13" : A = (Check 0 1 Read 1) %"v116";
    %"v120" : W = (RawLoad (LdNarrow Ub) 0) %"chk13";
    %"v121" : L = (Ext Uw) %"v120";
    %"v122" = %"v35" +p %"v121";
    %"chk14" : A = (Check 0 1 Read 1) %"v122";
    %"v123" : W = (RawLoad (LdNarrow Ub) 0) %"chk14";
    %"v126" = %"v116" +p #1;
    %"chk15" : A = (HalfCheck Upper 0 1 Read 1) %"chk13", %"v126";
    %"v127" : W = (RawLoad (LdNarrow Ub) 0) %"chk15";
    %"v128" : L = (Ext Uw) %"v127";
    %"v129" = %"v35" +p %"v128";
    %"chk16" : A = (Check 0 1 Read 1) %"v129";
    %"v130" : W = (RawLoad (LdNarrow Ub) 0) %"chk16";
    %"v133" = %"v116" +p #2;
    %"chk17" : A = (HalfCheck Upper 0 1 Read 1) %"chk13", %"v133";
    %"v134" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v135" : L = (Ext Uw) %"v134";
    %"v136" = %"v35" +p %"v135";
    %"chk18" : A = (Check 0 1 Read 1) %"v136";
    %"v137" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"v140" = %"v116" +p #3;
    %"chk19" : A = (HalfCheck Upper 0 1 Read 1) %"chk13", %"v140";
    %"v141" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"v142" : L = (Ext Uw) %"v141";
    %"v143" = %"v35" +p %"v142";
    %"chk20" : A = (Check 0 1 Read 1) %"v143";
    %"v144" : W = (RawLoad (LdNarrow Ub) 0) %"chk20";
    %"v147" : W = Or %"v123", %"v130";
    %"v149" : W = Or %"v147", %"v137";
    %"v151" : W = Or %"v149", %"v144";
    %"v152" : W = (Cmp Eq W) %"v151", #0
    => br %"v152" ? poll "L112" : "L114";
  @"L114":
    %"v156" : L = Ptoi %"v116";
    %"v158" : L = Sub %"v156", %"v104";
    %"v165" : W = (Cmp Ne W) %"v147", #0
    => br %"v165" ? "L159" : "L160";
  @"L159":
    %"v168" : L = (Ext Uw) %"v123";
    %"v169" : L = Sub %"v158", %"v168";
    %"v170" : L = Add %"v169", #1
    => goto "L161";
  @"L160":
    %"v173" : L = (Ext Uw) %"v137";
    %"v174" : L = Sub %"v158", %"v173";
    %"v175" : L = Add %"v174", #3
    => goto "L161";
  @"L161" [%"v176" : L = phi("L159" => %"v170", "L160" => %"v175")]:
    => ret %"v176"
} }.

Definition hello_image_fn___GI___strdup : func :=
  ir_fn{ "export" "__GI___strdup"(P %"v0") -> (RClass P) {
  @"start":
    call %"v4" : L = $"__GI_strlen"(P %"v0");
    %"v5" : L = Add %"v4", #1;
    call %"v8" : P = $"malloc"(L %"v5");
    %"v13" : L = Ptoi %"v8";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L9" : "L11";
  @"L9":
    => ret #0;
  @"L11":
    call %"v20" : P = $"__GI_memcpy"(P %"v8", P %"v0", L %"v5")
    => ret %"v20"
} }.

Definition hello_image_fn___strlen : func :=
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

Definition hello_image_fn___GI_strncmp : func :=
  ir_fn{ "export" "__GI_strncmp"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v11" : L = Ptoi %"v0";
    %"v12" : L = Neg %"v11";
    %"v13" : L = And %"v12", #7;
    %"v15" : W = (Cmp Ult L) %"v13", %"v4"
    => br %"v15" ? "L9" : "L8";
  @"L8":
    => goto "L9";
  @"L9" [%"v21" : L = phi("L8" => %"v4", "start" => %"v13")]:
    => goto "L24";
  @"L24" [%"pr.3" : W = phi("L26" => %"v59", "L9" => #0); %"pr.2" : P = phi("L26" => %"v39", "L9" => %"v2"); %"pr.1" : P = phi("L26" => %"v34", "L9" => %"v0")]:
    %"v30" : L = (Ext Sw) %"pr.3";
    %"v31" : W = (Cmp Ult L) %"v30", %"v21"
    => br %"v31" ? "L25" : "L27";
  @"L25":
    %"v34" = %"pr.1" +p #1;
    %"chk0" : A = (Check 0 1 Read 1) %"pr.1";
    %"v35" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v36" : W = (Ext Ub) %"v35";
    %"v39" = %"pr.2" +p #1;
    %"chk1" : A = (Check 0 1 Read 1) %"pr.2";
    %"v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v41" : W = (Ext Ub) %"v40";
    %"v44" : W = Sub %"v36", %"v41";
    %"v49" : W = (Cmp Eq W) %"v36", #0
    => br %"v49" ? "L51" : "L50";
  @"L50":
    %"v53" : W = (Cmp Ne W) %"v44", #0
    => goto "L51";
  @"L51" [%"v55" : W = phi("L25" => #1, "L50" => %"v53")]:
    => br %"v55" ? "L45" : "L26";
  @"L45":
    => ret %"v44";
  @"L26":
    %"v59" : W = Add %"pr.3", #1
    => goto poll "L24";
  @"L27":
    %"v65" : W = (Cmp Eq L) %"v21", %"v4"
    => br %"v65" ? "L60" : "L62";
  @"L60":
    => ret #0;
  @"L62":
    %"v71" = %"pr.1" +p #8;
    %"chk2" : A = (Check 0 8 Read 1) %"pr.1";
    %"v72" : L = (RawLoad LdL 0) %"chk2";
    %"v75" : L = Ptoi %"pr.2";
    %"v76" : L = And %"v75", #7;
    %"v81" : W = (Cmp Eq L) %"v76", #0
    => br %"v81" ? "L77" : "L78";
  @"L77":
    %"v87" : L = Sub %"v4", %"v21";
    %"iw_1.v10" = %"pr.2" +p #8;
    %"chk3" : A = (Check 0 8 Read 1) %"pr.2";
    %"iw_1.v11" : L = (RawLoad LdL 0) %"chk3"
    => goto "iw_1.L12";
  @"iw_1.L12" [%"iw_1.pr.5" : L = phi("iw_1.L28" => %"iw_1.v38", "L77" => %"iw_1.v11"); %"iw_1.pr.4" : L = phi("iw_1.L28" => %"iw_1.v25", "L77" => %"v87"); %"iw_1.pr.3" : L = phi("iw_1.L28" => %"iw_1.v35", "L77" => %"v72"); %"iw_1.pr.2" : P = phi("iw_1.L28" => %"iw_1.v37", "L77" => %"iw_1.v10"); %"iw_1.pr.1" : P = phi("iw_1.L28" => %"iw_1.v34", "L77" => %"v71")]:
    %"iw_1.v17" : W = (Cmp Eq L) %"iw_1.pr.3", %"iw_1.pr.5"
    => br %"iw_1.v17" ? "iw_1.L13" : "iw_1.iw_2.start";
  @"iw_1.L13":
    %"iw_1.v22" : W = (Cmp Ule L) %"iw_1.pr.4", #8
    => br %"iw_1.v22" ? "iw_1.iw_2.start" : "iw_1.L20";
  @"iw_1.L20":
    %"iw_1.v25" : L = Sub %"iw_1.pr.4", #8;
    %"iw_1.iw_1.iw_1.v8" : L = Sub %"iw_1.pr.3", #72340172838076673;
    %"iw_1.iw_1.iw_1.v10" : L = Xor %"iw_1.pr.3", #(-1);
    %"iw_1.iw_1.iw_1.v11" : L = And %"iw_1.iw_1.iw_1.v8", %"iw_1.iw_1.iw_1.v10";
    %"iw_1.iw_1.iw_1.v13" : L = And %"iw_1.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_1.iw_1.v4" : W = (Cmp Ne L) %"iw_1.iw_1.iw_1.v13", #0
    => br %"iw_1.iw_1.v4" ? "L79" : "iw_1.L28";
  @"iw_1.L28":
    %"iw_1.v34" = %"iw_1.pr.1" +p #8;
    %"chk4" : A = (Check 0 8 Read 1) %"iw_1.pr.1";
    %"iw_1.v35" : L = (RawLoad LdL 0) %"chk4";
    %"iw_1.v37" = %"iw_1.pr.2" +p #8;
    %"chk5" : A = (Check 0 8 Read 1) %"iw_1.pr.2";
    %"iw_1.v38" : L = (RawLoad LdL 0) %"chk5"
    => goto poll "iw_1.L12";
  @"iw_1.iw_2.start":
    %"iw_1.iw_2.iw_1.iw_1.v9" : L = Xor %"iw_1.pr.3", %"iw_1.pr.5";
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
    %"iw_1.iw_2.v15" : L = (Ext Uw) %"iw_1.iw_2.iw_1.iw_2.iw_1.v27";
    %"iw_1.iw_2.v16" : W = (Cmp Ule L) %"iw_1.pr.4", %"iw_1.iw_2.v15"
    => br %"iw_1.iw_2.v16" ? "L79" : "iw_1.iw_2.iw_2.start";
  @"iw_1.iw_2.iw_2.start":
    %"iw_1.iw_2.iw_2.v10" : W = Shl %"iw_1.iw_2.iw_1.iw_2.iw_1.v27", #3;
    %"iw_1.iw_2.iw_2.v11" : L = Shr %"iw_1.pr.3", %"iw_1.iw_2.iw_2.v10";
    %"iw_1.iw_2.iw_2.v12" : W = (Ext Ub) %"iw_1.iw_2.iw_2.v11";
    %"iw_1.iw_2.iw_3.v11" : L = Shr %"iw_1.pr.5", %"iw_1.iw_2.iw_2.v10";
    %"iw_1.iw_2.iw_3.v12" : W = (Ext Ub) %"iw_1.iw_2.iw_3.v11";
    %"iw_1.iw_2.v26" : W = Sub %"iw_1.iw_2.iw_2.v12", %"iw_1.iw_2.iw_3.v12"
    => goto "L79";
  @"L78":
    (Flight (a "v92") Sub [(FAddress (t "pr.2")); (FValue (t "v76"))] (LowerOf (t "pr.2")));
    %"v97" : L = Sub %"v4", %"v21";
    %"iw_2.v12" = %"v92" +p #8;
    %"chk6" : A = (Check 0 8 Read 1) %"v92";
    %"iw_2.v13" : L = (RawLoad LdL 0) %"chk6";
    %"iw_2.v16" : L = Shl %"v76", #3;
    %"iw_2.v20" : L = Sub #64, %"iw_2.v16";
    %"iw_2.v24" : L = Shr %"iw_2.v13", %"iw_2.v16";
    %"iw_2.v28" : L = Shl #18446744073709551615, %"iw_2.v20";
    %"iw_2.v29" : L = Or %"iw_2.v24", %"iw_2.v28";
    %"iw_2.iw_1.iw_1.v8" : L = Sub %"iw_2.v29", #72340172838076673;
    %"iw_2.iw_1.iw_1.v10" : L = Xor %"iw_2.v29", #(-1);
    %"iw_2.iw_1.iw_1.v11" : L = And %"iw_2.iw_1.iw_1.v8", %"iw_2.iw_1.iw_1.v10";
    %"iw_2.iw_1.iw_1.v13" : L = And %"iw_2.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_2.v36" : W = (Cmp Eq L) %"iw_2.iw_1.iw_1.v13", #0
    => br %"iw_2.v36" ? "iw_2.L37" : "iw_2.L38";
  @"iw_2.L37":
    %"iw_2.v41" : L = Sub #8, %"v76";
    %"iw_2.v42" : W = (Cmp Ugt L) %"v97", %"iw_2.v41"
    => goto "iw_2.L38";
  @"iw_2.L38" [%"iw_2.v44" : W = phi("L78" => #0, "iw_2.L37" => %"iw_2.v42")]:
    => br %"iw_2.v44" ? "iw_2.L46" : "iw_2.L32";
  @"iw_2.L46" [%"iw_2.pr.8" : L = phi("iw_2.L80" => %"iw_2.v51", "iw_2.L38" => %"iw_2.v13"); %"iw_2.pr.6" : L = phi("iw_2.L80" => %"iw_2.v77", "iw_2.L38" => %"v97"); %"iw_2.pr.4" : L = phi("iw_2.L80" => %"iw_2.v95", "iw_2.L38" => %"v72"); %"iw_2.pr.2" : P = phi("iw_2.L80" => %"iw_2.v50", "iw_2.L38" => %"iw_2.v12"); %"iw_2.pr.1" : P = phi("iw_2.L80" => %"iw_2.v94", "iw_2.L38" => %"v71")]:
    %"iw_2.v50" = %"iw_2.pr.2" +p #8;
    %"chk7" : A = (Check 0 8 Read 1) %"iw_2.pr.2";
    %"iw_2.v51" : L = (RawLoad LdL 0) %"chk7";
    %"iw_2.v54" : L = Shr %"iw_2.pr.8", %"iw_2.v16";
    %"iw_2.v57" : L = Shl %"iw_2.v51", %"iw_2.v20";
    %"iw_2.v58" : L = Or %"iw_2.v54", %"iw_2.v57";
    %"iw_2.v63" : W = (Cmp Ule L) %"iw_2.pr.6", #8
    => br %"iw_2.v63" ? "iw_2.L65" : "iw_2.L64";
  @"iw_2.L64":
    %"iw_2.v68" : W = (Cmp Ne L) %"iw_2.pr.4", %"iw_2.v58"
    => goto "iw_2.L65";
  @"iw_2.L65" [%"iw_2.v70" : W = phi("iw_2.L46" => #1, "iw_2.L64" => %"iw_2.v68")]:
    => br %"iw_2.v70" ? "iw_2.iw_2.start" : "iw_2.L61";
  @"iw_2.iw_2.start":
    %"iw_2.iw_2.iw_1.iw_1.v9" : L = Xor %"iw_2.pr.4", %"iw_2.v58";
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
    %"iw_2.iw_2.v15" : L = (Ext Uw) %"iw_2.iw_2.iw_1.iw_2.iw_1.v27";
    %"iw_2.iw_2.v16" : W = (Cmp Ule L) %"iw_2.pr.6", %"iw_2.iw_2.v15"
    => br %"iw_2.iw_2.v16" ? "L79" : "iw_2.iw_2.iw_2.start";
  @"iw_2.iw_2.iw_2.start":
    %"iw_2.iw_2.iw_2.v10" : W = Shl %"iw_2.iw_2.iw_1.iw_2.iw_1.v27", #3;
    %"iw_2.iw_2.iw_2.v11" : L = Shr %"iw_2.pr.4", %"iw_2.iw_2.iw_2.v10";
    %"iw_2.iw_2.iw_2.v12" : W = (Ext Ub) %"iw_2.iw_2.iw_2.v11";
    %"iw_2.iw_2.iw_3.v11" : L = Shr %"iw_2.v58", %"iw_2.iw_2.iw_2.v10";
    %"iw_2.iw_2.iw_3.v12" : W = (Ext Ub) %"iw_2.iw_2.iw_3.v11";
    %"iw_2.iw_2.v26" : W = Sub %"iw_2.iw_2.iw_2.v12", %"iw_2.iw_2.iw_3.v12"
    => goto "L79";
  @"iw_2.L61":
    %"iw_2.v77" : L = Sub %"iw_2.pr.6", #8;
    %"iw_2.iw_3.iw_1.v8" : L = Sub %"iw_2.v51", #72340172838076673;
    %"iw_2.iw_3.iw_1.v10" : L = Xor %"iw_2.v51", #(-1);
    %"iw_2.iw_3.iw_1.v11" : L = And %"iw_2.iw_3.iw_1.v8", %"iw_2.iw_3.iw_1.v10";
    %"iw_2.iw_3.iw_1.v13" : L = And %"iw_2.iw_3.iw_1.v11", #9259542123273814144;
    %"iw_2.iw_3.v4" : W = (Cmp Ne L) %"iw_2.iw_3.iw_1.v13", #0
    => br %"iw_2.iw_3.v4" ? "iw_2.L85" : "iw_2.L84";
  @"iw_2.L84":
    %"iw_2.v88" : L = Sub #8, %"v76";
    %"iw_2.v89" : W = (Cmp Ule L) %"iw_2.v77", %"iw_2.v88"
    => goto "iw_2.L85";
  @"iw_2.L85" [%"iw_2.v91" : W = phi("iw_2.L61" => #1, "iw_2.L84" => %"iw_2.v89")]:
    => br %"iw_2.v91" ? "iw_2.iw_4.start" : "iw_2.L80";
  @"iw_2.L80":
    %"iw_2.v94" = %"iw_2.pr.1" +p #8;
    %"chk8" : A = (Check 0 8 Read 1) %"iw_2.pr.1";
    %"iw_2.v95" : L = (RawLoad LdL 0) %"chk8"
    => goto poll "iw_2.L46";
  @"iw_2.iw_4.start":
    %"iw_2.iw_4.iw_1.v8" : L = Sub %"iw_2.pr.4", #72340172838076673;
    %"iw_2.iw_4.iw_1.v10" : L = Xor %"iw_2.pr.4", #(-1);
    %"iw_2.iw_4.iw_1.v11" : L = And %"iw_2.iw_4.iw_1.v8", %"iw_2.iw_4.iw_1.v10";
    %"iw_2.iw_4.iw_1.v13" : L = And %"iw_2.iw_4.iw_1.v11", #9259542123273814144;
    %"iw_2.iw_4.v4" : W = (Cmp Ne L) %"iw_2.iw_4.iw_1.v13", #0
    => br %"iw_2.iw_4.v4" ? "L79" : "iw_2.L99";
  @"iw_2.L99":
    %"chk9" : A = (Check 0 8 Read 1) %"iw_2.pr.1";
    %"iw_2.v106" : L = (RawLoad LdL 0) %"chk9";
    %"iw_2.v109" : L = Shr %"iw_2.v51", %"iw_2.v16";
    %"iw_2.v111" : W = Shl #0, %"iw_2.v20";
    %"iw_2.v112" : L = (Ext Sw) %"iw_2.v111";
    %"iw_2.v113" : L = Or %"iw_2.v109", %"iw_2.v112"
    => goto "iw_2.L32";
  @"iw_2.L32" [%"iw_2.pr.9" : L = phi("iw_2.L99" => %"iw_2.v113", "iw_2.L38" => %"iw_2.v29"); %"iw_2.pr.5" : L = phi("iw_2.L99" => %"iw_2.v77", "iw_2.L38" => %"v97"); %"iw_2.pr.3" : L = phi("iw_2.L99" => %"iw_2.v106", "iw_2.L38" => %"v72")]:
    %"iw_2.iw_5.iw_1.iw_1.v9" : L = Xor %"iw_2.pr.3", %"iw_2.pr.9";
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
  @"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4" [%"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v23" : W = phi("iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3" => %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v22", "iw_2.L32" => #64)]:
    %"iw_2.iw_5.iw_1.iw_2.iw_1.v27" : W = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v23", #3;
    %"iw_2.iw_5.v15" : L = (Ext Uw) %"iw_2.iw_5.iw_1.iw_2.iw_1.v27";
    %"iw_2.iw_5.v16" : W = (Cmp Ule L) %"iw_2.pr.5", %"iw_2.iw_5.v15"
    => br %"iw_2.iw_5.v16" ? "L79" : "iw_2.iw_5.iw_2.start";
  @"iw_2.iw_5.iw_2.start":
    %"iw_2.iw_5.iw_2.v10" : W = Shl %"iw_2.iw_5.iw_1.iw_2.iw_1.v27", #3;
    %"iw_2.iw_5.iw_2.v11" : L = Shr %"iw_2.pr.3", %"iw_2.iw_5.iw_2.v10";
    %"iw_2.iw_5.iw_2.v12" : W = (Ext Ub) %"iw_2.iw_5.iw_2.v11";
    %"iw_2.iw_5.iw_3.v11" : L = Shr %"iw_2.pr.9", %"iw_2.iw_5.iw_2.v10";
    %"iw_2.iw_5.iw_3.v12" : W = (Ext Ub) %"iw_2.iw_5.iw_3.v11";
    %"iw_2.iw_5.v26" : W = Sub %"iw_2.iw_5.iw_2.v12", %"iw_2.iw_5.iw_3.v12"
    => goto "L79";
  @"L79" [%"v99" : W = phi("iw_1.L20" => #0, "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4" => #0, "iw_1.iw_2.iw_2.start" => %"iw_1.iw_2.v26", "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4" => #0, "iw_2.iw_2.iw_2.start" => %"iw_2.iw_2.v26", "iw_2.iw_4.start" => #0, "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4" => #0, "iw_2.iw_5.iw_2.start" => %"iw_2.iw_5.v26")]:
    => ret %"v99"
} }.

Definition hello_image_fn___GI___strndup : func :=
  ir_fn{ "export" "__GI___strndup"(P %"v0", L %"v2") -> (RClass P) {
  @"start":
    call %"v7" : L = $"__GI___strnlen"(P %"v0", L %"v2");
    %"v10" : L = Add %"v7", #1;
    call %"v11" : P = $"malloc"(L %"v10");
    %"v16" : L = Ptoi %"v11";
    %"v17" : L = Ptoi #0;
    %"v18" : W = (Cmp Eq L) %"v16", %"v17"
    => br %"v18" ? "L12" : "L14";
  @"L12":
    => ret #0;
  @"L14":
    %"v22" = %"v11" +p %"v7";
    %"chk0" : A = (Check 0 1 Write 1) %"v22";
    store Wb [%"chk0" + 0] <- #0;
    call %"v26" : P = $"__GI_memcpy"(P %"v11", P %"v0", L %"v7")
    => ret %"v26"
} }.

Definition hello_image_fn___GI___strnlen : func :=
  ir_fn{ "export" "__GI___strnlen"(P %"v0", L %"v2") -> (RClass L) {
  @"start":
    call %"v7" : P = $"__GI_memchr"(P %"v0", W #0, L %"v2");
    %"v12" : L = Ptoi %"v7";
    %"v13" : W = (Cmp Ne L) %"v12", #0
    => br %"v13" ? "L8" : "L10";
  @"L8":
    %"v17" : L = Ptoi %"v0";
    %"v18" : L = Sub %"v12", %"v17"
    => goto "L10";
  @"L10" [%"v20" : L = phi("L8" => %"v18", "start" => %"v2")]:
    => ret %"v20"
} }.

Definition hello_image_fn___GI_strrchr : func :=
  ir_fn{ "export" "__GI_strrchr"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    call %"v7" : L = $"__GI_strlen"(P %"v0");
    %"v8" : L = Add %"v7", #1;
    call %"v9" : P = $"__GI___memrchr"(P %"v0", W %"v2", L %"v8")
    => ret %"v9"
} }.

Definition hello_image_fn___GI_strspn : func :=
  ir_fn{ "export" "__GI_strspn"(P %"v0", P %"v2") -> (RClass L) {
  @"start":
    %"v40" : P = (Alloc 4) #256;
    %"chk0" : A = (Check 0 1 Read 1) %"v2";
    %"v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => br %"v10" ? "L4" : "L6";
  @"L4":
    => ret #0;
  @"L6":
    %"v16" = %"v2" +p #1;
    %"chk1" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v18" : W = (Cmp Eq W) %"v17", #0
    => br %"v18" ? "L23" : "L14";
  @"L23" [%"pr.1" : P = phi("L25" => %"v33", "L6" => %"v0")]:
    %"chk2" : A = (Check 0 1 Read 1) %"pr.1";
    %"v28" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"chk3" : A = (Renew 0 1 Read 1) %"chk0", %"v2";
    %"v30" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v31" : W = (Cmp Eq W) %"v28", %"v30"
    => br %"v31" ? "L25" : "L26";
  @"L25":
    %"v33" = %"pr.1" +p #1
    => goto poll "L23";
  @"L26":
    %"v36" : L = Ptoi %"pr.1";
    %"v37" : L = Ptoi %"v0";
    %"v38" : L = Sub %"v36", %"v37"
    => ret %"v38";
  @"L14":
    call %"v42" : P = $"__GI_memset"(P %"v40", W #0, L #64);
    %"v44" = %"v42" +p #64;
    call %"v45" : P = $"__GI_memset"(P %"v44", W #0, L #64);
    %"v47" = %"v42" +p #128;
    call %"v48" : P = $"__GI_memset"(P %"v47", W #0, L #64);
    %"v50" = %"v42" +p #192;
    call %"v51" : P = $"__GI_memset"(P %"v50", W #0, L #64)
    => goto "L54";
  @"L54" [%"pr.3" : P = phi("L14" => %"v2", "L54" => %"v59")]:
    %"v59" = %"pr.3" +p #1;
    %"chk4" : A = (Check 0 1 Read 1) %"pr.3";
    %"v60" : W = (RawLoad (LdNarrow Ub) 0) %"chk4";
    %"v61" : L = (Ext Uw) %"v60";
    %"v62" = %"v42" +p %"v61";
    %"chk5" : A = (Check 0 1 Write 1) %"v62";
    store Wb [%"chk5" + 0] <- #1;
    %"chk6" : A = (HalfCheck Upper 0 1 Read 1) %"chk4", %"v59";
    %"v64" : W = (RawLoad (LdNarrow Ub) 0) %"chk6"
    => br %"v64" ? poll "L54" : "L56";
  @"L56":
    %"chk7" : A = (Check 0 1 Read 1) %"v0";
    %"v72" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v73" : L = (Ext Uw) %"v72";
    %"v74" = %"v42" +p %"v73";
    %"chk8" : A = (Check 0 1 Read 1) %"v74";
    %"v75" : W = (RawLoad (LdNarrow Ub) 0) %"chk8";
    %"v76" : W = (Cmp Eq W) %"v75", #0
    => br %"v76" ? "L66" : "L68";
  @"L66":
    => ret #0;
  @"L68":
    %"v83" = %"v0" +p #1;
    %"chk9" : A = (HalfCheck Upper 0 1 Read 1) %"chk7", %"v83";
    %"v84" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"v85" : L = (Ext Uw) %"v84";
    %"v86" = %"v42" +p %"v85";
    %"chk10" : A = (Check 0 1 Read 1) %"v86";
    %"v87" : W = (RawLoad (LdNarrow Ub) 0) %"chk10";
    %"v88" : W = (Cmp Eq W) %"v87", #0
    => br %"v88" ? "L78" : "L80";
  @"L78":
    => ret #1;
  @"L80":
    %"v95" = %"v0" +p #2;
    %"chk11" : A = (HalfCheck Upper 0 1 Read 1) %"chk7", %"v95";
    %"v96" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"v97" : L = (Ext Uw) %"v96";
    %"v98" = %"v42" +p %"v97";
    %"chk12" : A = (Check 0 1 Read 1) %"v98";
    %"v99" : W = (RawLoad (LdNarrow Ub) 0) %"chk12";
    %"v100" : W = (Cmp Eq W) %"v99", #0
    => br %"v100" ? "L90" : "L92";
  @"L90":
    => ret #2;
  @"L92":
    %"v107" = %"v0" +p #3;
    %"chk13" : A = (HalfCheck Upper 0 1 Read 1) %"chk7", %"v107";
    %"v108" : W = (RawLoad (LdNarrow Ub) 0) %"chk13";
    %"v109" : L = (Ext Uw) %"v108";
    %"v110" = %"v42" +p %"v109";
    %"chk14" : A = (Check 0 1 Read 1) %"v110";
    %"v111" : W = (RawLoad (LdNarrow Ub) 0) %"chk14";
    %"v112" : W = (Cmp Eq W) %"v111", #0
    => br %"v112" ? "L102" : "L104";
  @"L102":
    => ret #3;
  @"L104":
    %"v115" : L = Ptoi %"v0";
    %"v117" : L = And %"v115", #18446744073709551612;
    %"lc.2" : L = Sub %"v117", %"v115";
    %"v118" = %"v0" +p %"lc.2"
    => goto "L123";
  @"L123" [%"pr.2" : P = phi("L104" => %"v118", "L123" => %"v127")]:
    %"v127" = %"pr.2" +p #4;
    %"chk15" : A = (Check 0 1 Read 1) %"v127";
    %"v131" : W = (RawLoad (LdNarrow Ub) 0) %"chk15";
    %"v132" : L = (Ext Uw) %"v131";
    %"v133" = %"v42" +p %"v132";
    %"chk16" : A = (Check 0 1 Read 1) %"v133";
    %"v134" : W = (RawLoad (LdNarrow Ub) 0) %"chk16";
    %"v137" = %"v127" +p #1;
    %"chk17" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"v137";
    %"v138" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v139" : L = (Ext Uw) %"v138";
    %"v140" = %"v42" +p %"v139";
    %"chk18" : A = (Check 0 1 Read 1) %"v140";
    %"v141" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"v144" = %"v127" +p #2;
    %"chk19" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"v144";
    %"v145" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"v146" : L = (Ext Uw) %"v145";
    %"v147" = %"v42" +p %"v146";
    %"chk20" : A = (Check 0 1 Read 1) %"v147";
    %"v148" : W = (RawLoad (LdNarrow Ub) 0) %"chk20";
    %"v151" = %"v127" +p #3;
    %"chk21" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"v151";
    %"v152" : W = (RawLoad (LdNarrow Ub) 0) %"chk21";
    %"v153" : L = (Ext Uw) %"v152";
    %"v154" = %"v42" +p %"v153";
    %"chk22" : A = (Check 0 1 Read 1) %"v154";
    %"v155" : W = (RawLoad (LdNarrow Ub) 0) %"chk22";
    %"v158" : W = And %"v134", %"v141";
    %"v160" : W = And %"v158", %"v148";
    %"v162" : W = And %"v160", %"v155";
    %"v163" : W = (Cmp Ne W) %"v162", #0
    => br %"v163" ? poll "L123" : "L125";
  @"L125":
    %"v167" : L = Ptoi %"v127";
    %"v169" : L = Sub %"v167", %"v115";
    %"v176" : W = (Cmp Eq W) %"v158", #0
    => br %"v176" ? "L170" : "L171";
  @"L170":
    %"v179" : L = (Ext Uw) %"v134";
    %"v180" : L = Add %"v169", %"v179"
    => goto "L172";
  @"L171":
    %"v183" : L = (Ext Uw) %"v148";
    %"v184" : L = Add %"v169", %"v183";
    %"v185" : L = Add %"v184", #2
    => goto "L172";
  @"L172" [%"v186" : L = phi("L170" => %"v180", "L171" => %"v185")]:
    => ret %"v186"
} }.
