(** This file defines checked IR from glibc’s `string/memchr.os` object.
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

Definition item___GI_memchr : item :=
  (IAlias (a "__GI_memchr") (a "weak") (a "__memchr")).

Definition fn___memchr : func :=
  ir_fn{ "export" "__memchr"(P %"v0", W %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v10" : W = (Cmp Eq L) %"v4", #0
    => br %"v10" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"v16" : L = Ptoi %"v0";
    %"v18" : L = And %"v16", #18446744073709551608;
    %"lc.2" : L = Sub %"v18", %"v16";
    %"v19" = %"v0" +p %"lc.2";
    %"chk0" : A = (Check 0 8 Read 1) %"v19";
    %"v25" : L = (RawLoad LdL 0) %"chk0";
    %"v28" : W = (Ext Ub) %"v2";
    %"iw_1.v6" : L = (Ext Uw) %"v28";
    %"iw_1.v7" : L = Mul %"iw_1.v6", #72340172838076673;
    %"v34" : L = Sub %"v4", #1;
    %"iw_2.v9" : L = Sub #18446744073709551615, %"v16";
    %"iw_2.v10" : W = (Cmp Ugt L) %"v34", %"iw_2.v9"
    => br %"iw_2.v10" ? "iw_2.L6" : "iw_2.L5";
  @"iw_2.L5":
    %"iw_2.v13" : L = Add %"v16", %"v34"
    => goto "iw_2.L6";
  @"iw_2.L6" [%"iw_2.v14" : L = phi("iw_2.L5" => %"iw_2.v13", "L8" => #18446744073709551615)]:
    (Flight (a "iw_2.v15") Copy [(FValue (t "iw_2.v14"))] LowerNone);
    %"v36" : L = Ptoi %"iw_2.v15";
    (Flight (a "iw_3.v9") Sub [(FAddress (t "v0")); (FValue (t "v16"))] (LowerOf (t "v0")));
    %"iw_3.v12" = %"iw_3.v9" +p %"v36";
    %"v40" : L = Ptoi %"iw_3.v12";
    %"v42" : L = And %"v40", #18446744073709551608;
    %"lc.4" : L = Sub %"v42", %"v40";
    %"v43" = %"iw_3.v12" +p %"lc.4";
    %"iw_4.v6" : L = Xor %"v25", %"iw_1.v7";
    %"iw_4.iw_1.v6" : L = And %"iw_4.v6", #9187201950435737471;
    %"iw_4.iw_1.v8" : L = Add %"iw_4.iw_1.v6", #9187201950435737471;
    %"iw_4.iw_1.v10" : L = Or %"iw_4.iw_1.v8", %"iw_4.v6";
    %"iw_4.iw_1.v12" : L = Or %"iw_4.iw_1.v10", #9187201950435737471;
    %"iw_4.iw_1.v13" : L = Xor %"iw_4.iw_1.v12", #(-1);
    %"iw_5.v10" : L = And %"v16", #7;
    %"iw_5.v11" : L = Shl %"iw_5.v10", #3;
    %"iw_5.v12" : L = Shr %"iw_4.iw_1.v13", %"iw_5.v11";
    %"v54" : W = (Cmp Ne L) %"iw_5.v12", #0
    => br %"v54" ? "iw_6.start" : "L52";
  @"iw_6.start":
    %"iw_6.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_5.v12", #0
    => br %"iw_6.iw_1.iw_1.v6" ? "iw_6.iw_1.iw_1.L4" : "iw_6.iw_1.iw_1.L3";
  @"iw_6.iw_1.iw_1.L3":
    %"iw_6.iw_1.iw_1.v8" : L = Neg %"iw_5.v12";
    %"iw_6.iw_1.iw_1.v9" : L = And %"iw_5.v12", %"iw_6.iw_1.iw_1.v8";
    %"iw_6.iw_1.iw_1.v10" : L = Sub %"iw_6.iw_1.iw_1.v9", #1;
    %"iw_6.iw_1.iw_1.v11" : L = Shr %"iw_6.iw_1.iw_1.v10", #1;
    %"iw_6.iw_1.iw_1.v12" : L = And %"iw_6.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_6.iw_1.iw_1.v13" : L = Sub %"iw_6.iw_1.iw_1.v10", %"iw_6.iw_1.iw_1.v12";
    %"iw_6.iw_1.iw_1.v14" : L = And %"iw_6.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_6.iw_1.iw_1.v15" : L = Shr %"iw_6.iw_1.iw_1.v13", #2;
    %"iw_6.iw_1.iw_1.v16" : L = And %"iw_6.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_6.iw_1.iw_1.v17" : L = Add %"iw_6.iw_1.iw_1.v14", %"iw_6.iw_1.iw_1.v16";
    %"iw_6.iw_1.iw_1.v18" : L = Shr %"iw_6.iw_1.iw_1.v17", #4;
    %"iw_6.iw_1.iw_1.v19" : L = Add %"iw_6.iw_1.iw_1.v17", %"iw_6.iw_1.iw_1.v18";
    %"iw_6.iw_1.iw_1.v20" : L = And %"iw_6.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_6.iw_1.iw_1.v21" : L = Mul %"iw_6.iw_1.iw_1.v20", #72340172838076673;
    %"iw_6.iw_1.iw_1.v22" : L = Shr %"iw_6.iw_1.iw_1.v21", #56
    => goto "iw_6.iw_1.iw_1.L4";
  @"iw_6.iw_1.iw_1.L4" [%"iw_6.iw_1.iw_1.v23" : W = phi("iw_6.iw_1.iw_1.L3" => %"iw_6.iw_1.iw_1.v22", "iw_6.start" => #64)]:
    %"iw_6.iw_1.v27" : W = Shr %"iw_6.iw_1.iw_1.v23", #3;
    %"v59" : L = (Ext Uw) %"iw_6.iw_1.v27";
    %"v60" = %"v0" +p %"v59";
    %"v66" : L = Ptoi %"v60";
    %"v68" : W = (Cmp Ule L) %"v66", %"v40"
    => br %"v68" ? "L63" : "L62";
  @"L62":
    => goto "L63";
  @"L63" [%"v70" : P = phi("L62" => #0, "iw_6.iw_1.iw_1.L4" => %"v60")]:
    => ret %"v70";
  @"L52":
    %"v77" : L = Ptoi %"v19";
    %"v78" : L = Ptoi %"v43";
    %"v79" : W = (Cmp Eq L) %"v77", %"v78"
    => br %"v79" ? "L72" : "L74";
  @"L72":
    => ret #0;
  @"L74":
    %"v82" = %"v19" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v82";
    %"v83" : L = (RawLoad LdL 0) %"chk1"
    => goto "L84";
  @"L84" [%"pr.2" : L = phi("L74" => %"v83", "L94" => %"v108"); %"pr.1" : P = phi("L74" => %"v82", "L94" => %"v107")]:
    %"v89" : L = Ptoi %"pr.1";
    %"v91" : W = (Cmp Ne L) %"v89", %"v78"
    => br %"v91" ? "iw_7.start" : "iw_9.start";
  @"iw_7.start":
    %"iw_7.iw_1.v6" : L = Xor %"pr.2", %"iw_1.v7";
    %"iw_7.iw_1.iw_1.v8" : L = Sub %"iw_7.iw_1.v6", #72340172838076673;
    %"iw_7.iw_1.iw_1.v10" : L = Xor %"iw_7.iw_1.v6", #(-1);
    %"iw_7.iw_1.iw_1.v11" : L = And %"iw_7.iw_1.iw_1.v8", %"iw_7.iw_1.iw_1.v10";
    %"iw_7.iw_1.iw_1.v13" : L = And %"iw_7.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_7.v7" : W = (Cmp Ne L) %"iw_7.iw_1.iw_1.v13", #0
    => br %"iw_7.v7" ? "iw_8.start" : "L94";
  @"iw_8.start":
    %"iw_8.iw_3.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_7.iw_1.iw_1.v13", #0
    => br %"iw_8.iw_3.iw_1.iw_1.v6" ? "iw_8.iw_3.iw_1.iw_1.L4" : "iw_8.iw_3.iw_1.iw_1.L3";
  @"iw_8.iw_3.iw_1.iw_1.L3":
    %"iw_8.iw_3.iw_1.iw_1.v8" : L = Neg %"iw_7.iw_1.iw_1.v13";
    %"iw_8.iw_3.iw_1.iw_1.v9" : L = And %"iw_7.iw_1.iw_1.v13", %"iw_8.iw_3.iw_1.iw_1.v8";
    %"iw_8.iw_3.iw_1.iw_1.v10" : L = Sub %"iw_8.iw_3.iw_1.iw_1.v9", #1;
    %"iw_8.iw_3.iw_1.iw_1.v11" : L = Shr %"iw_8.iw_3.iw_1.iw_1.v10", #1;
    %"iw_8.iw_3.iw_1.iw_1.v12" : L = And %"iw_8.iw_3.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_8.iw_3.iw_1.iw_1.v13" : L = Sub %"iw_8.iw_3.iw_1.iw_1.v10", %"iw_8.iw_3.iw_1.iw_1.v12";
    %"iw_8.iw_3.iw_1.iw_1.v14" : L = And %"iw_8.iw_3.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_8.iw_3.iw_1.iw_1.v15" : L = Shr %"iw_8.iw_3.iw_1.iw_1.v13", #2;
    %"iw_8.iw_3.iw_1.iw_1.v16" : L = And %"iw_8.iw_3.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_8.iw_3.iw_1.iw_1.v17" : L = Add %"iw_8.iw_3.iw_1.iw_1.v14", %"iw_8.iw_3.iw_1.iw_1.v16";
    %"iw_8.iw_3.iw_1.iw_1.v18" : L = Shr %"iw_8.iw_3.iw_1.iw_1.v17", #4;
    %"iw_8.iw_3.iw_1.iw_1.v19" : L = Add %"iw_8.iw_3.iw_1.iw_1.v17", %"iw_8.iw_3.iw_1.iw_1.v18";
    %"iw_8.iw_3.iw_1.iw_1.v20" : L = And %"iw_8.iw_3.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_8.iw_3.iw_1.iw_1.v21" : L = Mul %"iw_8.iw_3.iw_1.iw_1.v20", #72340172838076673;
    %"iw_8.iw_3.iw_1.iw_1.v22" : L = Shr %"iw_8.iw_3.iw_1.iw_1.v21", #56
    => goto "iw_8.iw_3.iw_1.iw_1.L4";
  @"iw_8.iw_3.iw_1.iw_1.L4" [%"iw_8.iw_3.iw_1.iw_1.v23" : W = phi("iw_8.iw_3.iw_1.iw_1.L3" => %"iw_8.iw_3.iw_1.iw_1.v22", "iw_8.start" => #64)]:
    %"iw_8.iw_3.iw_1.v27" : W = Shr %"iw_8.iw_3.iw_1.iw_1.v23", #3;
    %"v103" : L = (Ext Uw) %"iw_8.iw_3.iw_1.v27";
    %"v104" = %"pr.1" +p %"v103"
    => ret %"v104";
  @"L94":
    %"v107" = %"pr.1" +p #8;
    %"chk2" : A = (Check 0 8 Read 1) %"v107";
    %"v108" : L = (RawLoad LdL 0) %"chk2"
    => goto poll "L84";
  @"iw_9.start":
    %"iw_9.iw_1.v6" : L = Xor %"pr.2", %"iw_1.v7";
    %"iw_9.iw_1.iw_1.v8" : L = Sub %"iw_9.iw_1.v6", #72340172838076673;
    %"iw_9.iw_1.iw_1.v10" : L = Xor %"iw_9.iw_1.v6", #(-1);
    %"iw_9.iw_1.iw_1.v11" : L = And %"iw_9.iw_1.iw_1.v8", %"iw_9.iw_1.iw_1.v10";
    %"iw_9.iw_1.iw_1.v13" : L = And %"iw_9.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_9.v7" : W = (Cmp Ne L) %"iw_9.iw_1.iw_1.v13", #0
    => br %"iw_9.v7" ? "iw_10.start" : "L111";
  @"iw_10.start":
    %"iw_10.iw_3.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_9.iw_1.iw_1.v13", #0
    => br %"iw_10.iw_3.iw_1.iw_1.v6" ? "iw_10.iw_3.iw_1.iw_1.L4" : "iw_10.iw_3.iw_1.iw_1.L3";
  @"iw_10.iw_3.iw_1.iw_1.L3":
    %"iw_10.iw_3.iw_1.iw_1.v8" : L = Neg %"iw_9.iw_1.iw_1.v13";
    %"iw_10.iw_3.iw_1.iw_1.v9" : L = And %"iw_9.iw_1.iw_1.v13", %"iw_10.iw_3.iw_1.iw_1.v8";
    %"iw_10.iw_3.iw_1.iw_1.v10" : L = Sub %"iw_10.iw_3.iw_1.iw_1.v9", #1;
    %"iw_10.iw_3.iw_1.iw_1.v11" : L = Shr %"iw_10.iw_3.iw_1.iw_1.v10", #1;
    %"iw_10.iw_3.iw_1.iw_1.v12" : L = And %"iw_10.iw_3.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_10.iw_3.iw_1.iw_1.v13" : L = Sub %"iw_10.iw_3.iw_1.iw_1.v10", %"iw_10.iw_3.iw_1.iw_1.v12";
    %"iw_10.iw_3.iw_1.iw_1.v14" : L = And %"iw_10.iw_3.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_10.iw_3.iw_1.iw_1.v15" : L = Shr %"iw_10.iw_3.iw_1.iw_1.v13", #2;
    %"iw_10.iw_3.iw_1.iw_1.v16" : L = And %"iw_10.iw_3.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_10.iw_3.iw_1.iw_1.v17" : L = Add %"iw_10.iw_3.iw_1.iw_1.v14", %"iw_10.iw_3.iw_1.iw_1.v16";
    %"iw_10.iw_3.iw_1.iw_1.v18" : L = Shr %"iw_10.iw_3.iw_1.iw_1.v17", #4;
    %"iw_10.iw_3.iw_1.iw_1.v19" : L = Add %"iw_10.iw_3.iw_1.iw_1.v17", %"iw_10.iw_3.iw_1.iw_1.v18";
    %"iw_10.iw_3.iw_1.iw_1.v20" : L = And %"iw_10.iw_3.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_10.iw_3.iw_1.iw_1.v21" : L = Mul %"iw_10.iw_3.iw_1.iw_1.v20", #72340172838076673;
    %"iw_10.iw_3.iw_1.iw_1.v22" : L = Shr %"iw_10.iw_3.iw_1.iw_1.v21", #56
    => goto "iw_10.iw_3.iw_1.iw_1.L4";
  @"iw_10.iw_3.iw_1.iw_1.L4" [%"iw_10.iw_3.iw_1.iw_1.v23" : W = phi("iw_10.iw_3.iw_1.iw_1.L3" => %"iw_10.iw_3.iw_1.iw_1.v22", "iw_10.start" => #64)]:
    %"iw_10.iw_3.iw_1.v27" : W = Shr %"iw_10.iw_3.iw_1.iw_1.v23", #3;
    %"v121" : L = (Ext Uw) %"iw_10.iw_3.iw_1.v27";
    %"v122" = %"pr.1" +p %"v121";
    %"v128" : L = Ptoi %"v122";
    %"v130" : W = (Cmp Ule L) %"v128", %"v40"
    => br %"v130" ? "L123" : "L111";
  @"L123":
    => ret %"v122";
  @"L111":
    => ret #0
} }.

Definition item_memchr : item :=
  (IAlias (a "memchr") (a "export") (a "__memchr")).
