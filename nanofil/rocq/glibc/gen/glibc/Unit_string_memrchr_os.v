(** This file defines checked IR from glibc’s `string/memrchr.os` object.
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

Definition fn___GI___memrchr : func :=
  ir_fn{ "export" "__GI___memrchr"(P %"v0", W %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v10" : W = (Cmp Eq L) %"v4", #0
    => br %"v10" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"v17" = %"v0" +p %"v4";
    %"v18" : L = Ptoi %"v17";
    %"v19" : L = Add %"v18", #8;
    %"v20" : L = Sub %"v19", #1;
    %"v22" : L = And %"v20", #18446744073709551608;
    %"lc.2" : L = Sub %"v22", %"v18";
    %"v23" = %"v17" +p %"lc.2";
    %"v26" : L = Ptoi %"v0";
    %"v28" : L = Add %"v26", %"v4";
    (Flight (a "v31") Sub [(FAddress (t "v23")); (FValue (Const 8))] (LowerOf (t "v23")));
    %"chk0" : A = (Check 0 8 Read 1) %"v31";
    %"v32" : L = (RawLoad LdL 0) %"chk0";
    %"v35" : W = (Ext Ub) %"v2";
    %"iw_1.v6" : L = (Ext Uw) %"v35";
    %"iw_1.v7" : L = Mul %"iw_1.v6", #72340172838076673;
    %"v41" : L = And %"v26", #18446744073709551608;
    %"lc.4" : L = Sub %"v41", %"v26";
    %"v42" = %"v0" +p %"lc.4";
    %"iw_2.v6" : L = Xor %"v32", %"iw_1.v7";
    %"iw_2.iw_1.v6" : L = And %"iw_2.v6", #9187201950435737471;
    %"iw_2.iw_1.v8" : L = Add %"iw_2.iw_1.v6", #9187201950435737471;
    %"iw_2.iw_1.v10" : L = Or %"iw_2.iw_1.v8", %"iw_2.v6";
    %"iw_2.iw_1.v12" : L = Or %"iw_2.iw_1.v10", #9187201950435737471;
    %"iw_2.iw_1.v13" : L = Xor %"iw_2.iw_1.v12", #(-1);
    %"iw_3.v5" : L = And %"v28", #7;
    %"iw_3.v10" : W = (Cmp Eq L) %"iw_3.v5", #0
    => br %"iw_3.v10" ? "iw_3.join" : "iw_3.L13";
  @"iw_3.L13":
    %"iw_3.v21" : L = Shl %"iw_3.v5", #3;
    %"iw_3.v22" : L = Shl #18446744073709551615, %"iw_3.v21";
    %"iw_3.v23" : L = Xor %"iw_3.v22", #(-1);
    %"iw_3.v24" : L = And %"iw_2.iw_1.v13", %"iw_3.v23"
    => goto "iw_3.join";
  @"iw_3.join" [%"v48" : L = phi("iw_3.L13" => %"iw_3.v24", "L8" => %"iw_2.iw_1.v13")]:
    %"v53" : W = (Cmp Ne L) %"v48", #0
    => br %"v53" ? "iw_4.start" : "L51";
  @"iw_4.start":
    %"iw_4.iw_1.iw_1.v6" : W = (Cmp Eq L) %"v48", #0
    => br %"iw_4.iw_1.iw_1.v6" ? "iw_4.iw_1.iw_1.L4" : "iw_4.iw_1.iw_1.L3";
  @"iw_4.iw_1.iw_1.L3":
    %"iw_4.iw_1.iw_1.v8" : L = Shr %"v48", #1;
    %"iw_4.iw_1.iw_1.v9" : L = Or %"v48", %"iw_4.iw_1.iw_1.v8";
    %"iw_4.iw_1.iw_1.v10" : L = Shr %"iw_4.iw_1.iw_1.v9", #2;
    %"iw_4.iw_1.iw_1.v11" : L = Or %"iw_4.iw_1.iw_1.v9", %"iw_4.iw_1.iw_1.v10";
    %"iw_4.iw_1.iw_1.v12" : L = Shr %"iw_4.iw_1.iw_1.v11", #4;
    %"iw_4.iw_1.iw_1.v13" : L = Or %"iw_4.iw_1.iw_1.v11", %"iw_4.iw_1.iw_1.v12";
    %"iw_4.iw_1.iw_1.v14" : L = Shr %"iw_4.iw_1.iw_1.v13", #8;
    %"iw_4.iw_1.iw_1.v15" : L = Or %"iw_4.iw_1.iw_1.v13", %"iw_4.iw_1.iw_1.v14";
    %"iw_4.iw_1.iw_1.v16" : L = Shr %"iw_4.iw_1.iw_1.v15", #16;
    %"iw_4.iw_1.iw_1.v17" : L = Or %"iw_4.iw_1.iw_1.v15", %"iw_4.iw_1.iw_1.v16";
    %"iw_4.iw_1.iw_1.v18" : L = Shr %"iw_4.iw_1.iw_1.v17", #32;
    %"iw_4.iw_1.iw_1.v19" : L = Or %"iw_4.iw_1.iw_1.v17", %"iw_4.iw_1.iw_1.v18";
    %"iw_4.iw_1.iw_1.v20" : L = Shr %"iw_4.iw_1.iw_1.v19", #1;
    %"iw_4.iw_1.iw_1.v21" : L = And %"iw_4.iw_1.iw_1.v20", #6148914691236517205;
    %"iw_4.iw_1.iw_1.v22" : L = Sub %"iw_4.iw_1.iw_1.v19", %"iw_4.iw_1.iw_1.v21";
    %"iw_4.iw_1.iw_1.v23" : L = And %"iw_4.iw_1.iw_1.v22", #3689348814741910323;
    %"iw_4.iw_1.iw_1.v24" : L = Shr %"iw_4.iw_1.iw_1.v22", #2;
    %"iw_4.iw_1.iw_1.v25" : L = And %"iw_4.iw_1.iw_1.v24", #3689348814741910323;
    %"iw_4.iw_1.iw_1.v26" : L = Add %"iw_4.iw_1.iw_1.v23", %"iw_4.iw_1.iw_1.v25";
    %"iw_4.iw_1.iw_1.v27" : L = Shr %"iw_4.iw_1.iw_1.v26", #4;
    %"iw_4.iw_1.iw_1.v28" : L = Add %"iw_4.iw_1.iw_1.v26", %"iw_4.iw_1.iw_1.v27";
    %"iw_4.iw_1.iw_1.v29" : L = And %"iw_4.iw_1.iw_1.v28", #1085102592571150095;
    %"iw_4.iw_1.iw_1.v30" : L = Mul %"iw_4.iw_1.iw_1.v29", #72340172838076673;
    %"iw_4.iw_1.iw_1.v31" : L = Shr %"iw_4.iw_1.iw_1.v30", #56;
    %"iw_4.iw_1.iw_1.v32" : L = Sub %"iw_4.iw_1.iw_1.v31", #64;
    %"iw_4.iw_1.iw_1.v33" : L = Neg %"iw_4.iw_1.iw_1.v32"
    => goto "iw_4.iw_1.iw_1.L4";
  @"iw_4.iw_1.iw_1.L4" [%"iw_4.iw_1.iw_1.v34" : W = phi("iw_4.iw_1.iw_1.L3" => %"iw_4.iw_1.iw_1.v33", "iw_4.start" => #64)]:
    %"iw_4.iw_1.v7" : W = Shr %"iw_4.iw_1.iw_1.v34", #3;
    %"iw_4.v13" : L = (Ext Uw) %"iw_4.iw_1.v7";
    %"iw_4.v14" : L = Sub #7, %"iw_4.v13"
    => goto "iw_4.join";
  @"iw_4.join" [%"v57" : W = phi("iw_4.iw_1.iw_1.L4" => %"iw_4.v14")]:
    %"v58" : L = (Ext Uw) %"v57";
    %"v59" = %"v31" +p %"v58";
    %"v65" : L = Ptoi %"v59";
    %"v67" : W = (Cmp Uge L) %"v65", %"v26"
    => br %"v67" ? "L62" : "L61";
  @"L61":
    => goto "L62";
  @"L62" [%"v69" : P = phi("L61" => #0, "iw_4.join" => %"v59")]:
    => ret %"v69";
  @"L51":
    %"v76" : L = Ptoi %"v31";
    %"v77" : L = Ptoi %"v42";
    %"v78" : W = (Cmp Eq L) %"v76", %"v77"
    => br %"v78" ? "L71" : "L73";
  @"L71":
    => ret #0;
  @"L73":
    (Flight (a "v81") Sub [(FAddress (t "v31")); (FValue (Const 8))] (LowerOf (t "v31")));
    %"chk1" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v81";
    %"v82" : L = (RawLoad LdL 0) %"chk1"
    => goto "L83";
  @"L83" [%"pr.2" : L = phi("L73" => %"v82", "L93" => %"v107"); %"pr.1" : P = phi("L73" => %"v81", "L93" => %"v106")]:
    %"v88" : L = Ptoi %"pr.1";
    %"v90" : W = (Cmp Ne L) %"v88", %"v77"
    => br %"v90" ? "iw_5.start" : "iw_7.start";
  @"iw_5.start":
    %"iw_5.iw_1.v6" : L = Xor %"pr.2", %"iw_1.v7";
    %"iw_5.iw_1.iw_1.v8" : L = Sub %"iw_5.iw_1.v6", #72340172838076673;
    %"iw_5.iw_1.iw_1.v10" : L = Xor %"iw_5.iw_1.v6", #(-1);
    %"iw_5.iw_1.iw_1.v11" : L = And %"iw_5.iw_1.iw_1.v8", %"iw_5.iw_1.iw_1.v10";
    %"iw_5.iw_1.iw_1.v13" : L = And %"iw_5.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_5.v7" : W = (Cmp Ne L) %"iw_5.iw_1.iw_1.v13", #0
    => br %"iw_5.v7" ? "iw_6.start" : "L93";
  @"iw_6.start":
    %"iw_6.iw_1.iw_1.v6" : L = And %"iw_5.iw_1.v6", #9187201950435737471;
    %"iw_6.iw_1.iw_1.v8" : L = Add %"iw_6.iw_1.iw_1.v6", #9187201950435737471;
    %"iw_6.iw_1.iw_1.v10" : L = Or %"iw_6.iw_1.iw_1.v8", %"iw_5.iw_1.v6";
    %"iw_6.iw_1.iw_1.v12" : L = Or %"iw_6.iw_1.iw_1.v10", #9187201950435737471;
    %"iw_6.iw_1.iw_1.v13" : L = Xor %"iw_6.iw_1.iw_1.v12", #(-1);
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_6.iw_1.iw_1.v13", #0
    => br %"iw_6.iw_1.iw_3.iw_1.iw_1.v6" ? "iw_6.iw_1.iw_3.iw_1.iw_1.L4" : "iw_6.iw_1.iw_3.iw_1.iw_1.L3";
  @"iw_6.iw_1.iw_3.iw_1.iw_1.L3":
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v8" : L = Shr %"iw_6.iw_1.iw_1.v13", #1;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v9" : L = Or %"iw_6.iw_1.iw_1.v13", %"iw_6.iw_1.iw_3.iw_1.iw_1.v8";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v10" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v9", #2;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v11" : L = Or %"iw_6.iw_1.iw_3.iw_1.iw_1.v9", %"iw_6.iw_1.iw_3.iw_1.iw_1.v10";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v12" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v11", #4;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v13" : L = Or %"iw_6.iw_1.iw_3.iw_1.iw_1.v11", %"iw_6.iw_1.iw_3.iw_1.iw_1.v12";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v14" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v13", #8;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v15" : L = Or %"iw_6.iw_1.iw_3.iw_1.iw_1.v13", %"iw_6.iw_1.iw_3.iw_1.iw_1.v14";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v16" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v15", #16;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v17" : L = Or %"iw_6.iw_1.iw_3.iw_1.iw_1.v15", %"iw_6.iw_1.iw_3.iw_1.iw_1.v16";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v18" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v17", #32;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v19" : L = Or %"iw_6.iw_1.iw_3.iw_1.iw_1.v17", %"iw_6.iw_1.iw_3.iw_1.iw_1.v18";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v20" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v19", #1;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v21" : L = And %"iw_6.iw_1.iw_3.iw_1.iw_1.v20", #6148914691236517205;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v22" : L = Sub %"iw_6.iw_1.iw_3.iw_1.iw_1.v19", %"iw_6.iw_1.iw_3.iw_1.iw_1.v21";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v23" : L = And %"iw_6.iw_1.iw_3.iw_1.iw_1.v22", #3689348814741910323;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v24" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v22", #2;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v25" : L = And %"iw_6.iw_1.iw_3.iw_1.iw_1.v24", #3689348814741910323;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v26" : L = Add %"iw_6.iw_1.iw_3.iw_1.iw_1.v23", %"iw_6.iw_1.iw_3.iw_1.iw_1.v25";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v27" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v26", #4;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v28" : L = Add %"iw_6.iw_1.iw_3.iw_1.iw_1.v26", %"iw_6.iw_1.iw_3.iw_1.iw_1.v27";
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v29" : L = And %"iw_6.iw_1.iw_3.iw_1.iw_1.v28", #1085102592571150095;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v30" : L = Mul %"iw_6.iw_1.iw_3.iw_1.iw_1.v29", #72340172838076673;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v31" : L = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v30", #56;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v32" : L = Sub %"iw_6.iw_1.iw_3.iw_1.iw_1.v31", #64;
    %"iw_6.iw_1.iw_3.iw_1.iw_1.v33" : L = Neg %"iw_6.iw_1.iw_3.iw_1.iw_1.v32"
    => goto "iw_6.iw_1.iw_3.iw_1.iw_1.L4";
  @"iw_6.iw_1.iw_3.iw_1.iw_1.L4" [%"iw_6.iw_1.iw_3.iw_1.iw_1.v34" : W = phi("iw_6.iw_1.iw_3.iw_1.iw_1.L3" => %"iw_6.iw_1.iw_3.iw_1.iw_1.v33", "iw_6.start" => #64)]:
    %"iw_6.iw_1.iw_3.iw_1.v7" : W = Shr %"iw_6.iw_1.iw_3.iw_1.iw_1.v34", #3;
    %"iw_6.iw_1.iw_3.v13" : L = (Ext Uw) %"iw_6.iw_1.iw_3.iw_1.v7";
    %"iw_6.iw_1.iw_3.v14" : L = Sub #7, %"iw_6.iw_1.iw_3.v13"
    => goto "iw_6.iw_1.iw_3.join";
  @"iw_6.iw_1.iw_3.join" [%"iw_6.iw_1.v11" : W = phi("iw_6.iw_1.iw_3.iw_1.iw_1.L4" => %"iw_6.iw_1.iw_3.v14")]:
    %"v102" : L = (Ext Uw) %"iw_6.iw_1.v11";
    %"v103" = %"pr.1" +p %"v102"
    => ret %"v103";
  @"L93":
    (Flight (a "v106") Sub [(FAddress (t "pr.1")); (FValue (Const 8))] (LowerOf (t "pr.1")));
    %"chk2" : A = (Check 0 8 Read 1) %"v106";
    %"v107" : L = (RawLoad LdL 0) %"chk2"
    => goto poll "L83";
  @"iw_7.start":
    %"iw_7.iw_1.v6" : L = Xor %"pr.2", %"iw_1.v7";
    %"iw_7.iw_1.iw_1.v8" : L = Sub %"iw_7.iw_1.v6", #72340172838076673;
    %"iw_7.iw_1.iw_1.v10" : L = Xor %"iw_7.iw_1.v6", #(-1);
    %"iw_7.iw_1.iw_1.v11" : L = And %"iw_7.iw_1.iw_1.v8", %"iw_7.iw_1.iw_1.v10";
    %"iw_7.iw_1.iw_1.v13" : L = And %"iw_7.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_7.v7" : W = (Cmp Ne L) %"iw_7.iw_1.iw_1.v13", #0
    => br %"iw_7.v7" ? "iw_8.start" : "L110";
  @"iw_8.start":
    %"iw_8.iw_1.iw_1.v6" : L = And %"iw_7.iw_1.v6", #9187201950435737471;
    %"iw_8.iw_1.iw_1.v8" : L = Add %"iw_8.iw_1.iw_1.v6", #9187201950435737471;
    %"iw_8.iw_1.iw_1.v10" : L = Or %"iw_8.iw_1.iw_1.v8", %"iw_7.iw_1.v6";
    %"iw_8.iw_1.iw_1.v12" : L = Or %"iw_8.iw_1.iw_1.v10", #9187201950435737471;
    %"iw_8.iw_1.iw_1.v13" : L = Xor %"iw_8.iw_1.iw_1.v12", #(-1);
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_8.iw_1.iw_1.v13", #0
    => br %"iw_8.iw_1.iw_3.iw_1.iw_1.v6" ? "iw_8.iw_1.iw_3.iw_1.iw_1.L4" : "iw_8.iw_1.iw_3.iw_1.iw_1.L3";
  @"iw_8.iw_1.iw_3.iw_1.iw_1.L3":
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v8" : L = Shr %"iw_8.iw_1.iw_1.v13", #1;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v9" : L = Or %"iw_8.iw_1.iw_1.v13", %"iw_8.iw_1.iw_3.iw_1.iw_1.v8";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v10" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v9", #2;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v11" : L = Or %"iw_8.iw_1.iw_3.iw_1.iw_1.v9", %"iw_8.iw_1.iw_3.iw_1.iw_1.v10";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v12" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v11", #4;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v13" : L = Or %"iw_8.iw_1.iw_3.iw_1.iw_1.v11", %"iw_8.iw_1.iw_3.iw_1.iw_1.v12";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v14" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v13", #8;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v15" : L = Or %"iw_8.iw_1.iw_3.iw_1.iw_1.v13", %"iw_8.iw_1.iw_3.iw_1.iw_1.v14";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v16" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v15", #16;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v17" : L = Or %"iw_8.iw_1.iw_3.iw_1.iw_1.v15", %"iw_8.iw_1.iw_3.iw_1.iw_1.v16";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v18" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v17", #32;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v19" : L = Or %"iw_8.iw_1.iw_3.iw_1.iw_1.v17", %"iw_8.iw_1.iw_3.iw_1.iw_1.v18";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v20" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v19", #1;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v21" : L = And %"iw_8.iw_1.iw_3.iw_1.iw_1.v20", #6148914691236517205;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v22" : L = Sub %"iw_8.iw_1.iw_3.iw_1.iw_1.v19", %"iw_8.iw_1.iw_3.iw_1.iw_1.v21";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v23" : L = And %"iw_8.iw_1.iw_3.iw_1.iw_1.v22", #3689348814741910323;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v24" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v22", #2;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v25" : L = And %"iw_8.iw_1.iw_3.iw_1.iw_1.v24", #3689348814741910323;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v26" : L = Add %"iw_8.iw_1.iw_3.iw_1.iw_1.v23", %"iw_8.iw_1.iw_3.iw_1.iw_1.v25";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v27" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v26", #4;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v28" : L = Add %"iw_8.iw_1.iw_3.iw_1.iw_1.v26", %"iw_8.iw_1.iw_3.iw_1.iw_1.v27";
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v29" : L = And %"iw_8.iw_1.iw_3.iw_1.iw_1.v28", #1085102592571150095;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v30" : L = Mul %"iw_8.iw_1.iw_3.iw_1.iw_1.v29", #72340172838076673;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v31" : L = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v30", #56;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v32" : L = Sub %"iw_8.iw_1.iw_3.iw_1.iw_1.v31", #64;
    %"iw_8.iw_1.iw_3.iw_1.iw_1.v33" : L = Neg %"iw_8.iw_1.iw_3.iw_1.iw_1.v32"
    => goto "iw_8.iw_1.iw_3.iw_1.iw_1.L4";
  @"iw_8.iw_1.iw_3.iw_1.iw_1.L4" [%"iw_8.iw_1.iw_3.iw_1.iw_1.v34" : W = phi("iw_8.iw_1.iw_3.iw_1.iw_1.L3" => %"iw_8.iw_1.iw_3.iw_1.iw_1.v33", "iw_8.start" => #64)]:
    %"iw_8.iw_1.iw_3.iw_1.v7" : W = Shr %"iw_8.iw_1.iw_3.iw_1.iw_1.v34", #3;
    %"iw_8.iw_1.iw_3.v13" : L = (Ext Uw) %"iw_8.iw_1.iw_3.iw_1.v7";
    %"iw_8.iw_1.iw_3.v14" : L = Sub #7, %"iw_8.iw_1.iw_3.v13"
    => goto "iw_8.iw_1.iw_3.join";
  @"iw_8.iw_1.iw_3.join" [%"iw_8.iw_1.v11" : W = phi("iw_8.iw_1.iw_3.iw_1.iw_1.L4" => %"iw_8.iw_1.iw_3.v14")]:
    %"v120" : L = (Ext Uw) %"iw_8.iw_1.v11";
    %"v121" = %"pr.1" +p %"v120";
    %"v127" : L = Ptoi %"v121";
    %"v129" : W = (Cmp Uge L) %"v127", %"v26"
    => br %"v129" ? "L122" : "L110";
  @"L122":
    => ret %"v121";
  @"L110":
    => ret #0
} }.

Definition item_memrchr : item :=
  (IAlias (a "memrchr") (a "weak") (a "__GI___memrchr")).
