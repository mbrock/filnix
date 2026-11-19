(** This file defines checked IR from glibc’s `string/strchrnul.os` object.
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

Definition fn___GI___strchrnul : func :=
  ir_fn{ "export" "__GI___strchrnul"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    %"v6" : L = Ptoi %"v0";
    %"v11" : L = And %"v6", #18446744073709551608;
    %"lc.2" : L = Sub %"v11", %"v6";
    %"v12" = %"v0" +p %"lc.2";
    %"v15" : W = (Ext Ub) %"v2";
    %"iw_1.v6" : L = (Ext Uw) %"v15";
    %"iw_1.v7" : L = Mul %"iw_1.v6", #72340172838076673;
    %"chk0" : A = (Check 0 8 Read 1) %"v12";
    %"v19" : L = (RawLoad LdL 0) %"chk0";
    %"iw_2.iw_1.v6" : L = And %"v19", #9187201950435737471;
    %"iw_2.iw_1.v8" : L = Add %"iw_2.iw_1.v6", #9187201950435737471;
    %"iw_2.iw_1.v10" : L = Or %"iw_2.iw_1.v8", %"v19";
    %"iw_2.iw_1.v12" : L = Or %"iw_2.iw_1.v10", #9187201950435737471;
    %"iw_2.iw_1.v13" : L = Xor %"iw_2.iw_1.v12", #(-1);
    %"iw_2.v8" : L = Xor %"v19", %"iw_1.v7";
    %"iw_2.iw_2.v6" : L = And %"iw_2.v8", #9187201950435737471;
    %"iw_2.iw_2.v8" : L = Add %"iw_2.iw_2.v6", #9187201950435737471;
    %"iw_2.iw_2.v10" : L = Or %"iw_2.iw_2.v8", %"iw_2.v8";
    %"iw_2.iw_2.v12" : L = Or %"iw_2.iw_2.v10", #9187201950435737471;
    %"iw_2.iw_2.v13" : L = Xor %"iw_2.iw_2.v12", #(-1);
    %"iw_2.v10" : L = Or %"iw_2.iw_1.v13", %"iw_2.iw_2.v13";
    %"iw_3.v10" : L = And %"v6", #7;
    %"iw_3.v11" : L = Shl %"iw_3.v10", #3;
    %"iw_3.v12" : L = Shr %"iw_2.v10", %"iw_3.v11";
    %"v30" : W = (Cmp Ne L) %"iw_3.v12", #0
    => br %"v30" ? "iw_4.start" : "L37";
  @"iw_4.start":
    %"iw_4.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_3.v12", #0
    => br %"iw_4.iw_1.iw_1.v6" ? "iw_4.iw_1.iw_1.L4" : "iw_4.iw_1.iw_1.L3";
  @"iw_4.iw_1.iw_1.L3":
    %"iw_4.iw_1.iw_1.v8" : L = Neg %"iw_3.v12";
    %"iw_4.iw_1.iw_1.v9" : L = And %"iw_3.v12", %"iw_4.iw_1.iw_1.v8";
    %"iw_4.iw_1.iw_1.v10" : L = Sub %"iw_4.iw_1.iw_1.v9", #1;
    %"iw_4.iw_1.iw_1.v11" : L = Shr %"iw_4.iw_1.iw_1.v10", #1;
    %"iw_4.iw_1.iw_1.v12" : L = And %"iw_4.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_4.iw_1.iw_1.v13" : L = Sub %"iw_4.iw_1.iw_1.v10", %"iw_4.iw_1.iw_1.v12";
    %"iw_4.iw_1.iw_1.v14" : L = And %"iw_4.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_4.iw_1.iw_1.v15" : L = Shr %"iw_4.iw_1.iw_1.v13", #2;
    %"iw_4.iw_1.iw_1.v16" : L = And %"iw_4.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_4.iw_1.iw_1.v17" : L = Add %"iw_4.iw_1.iw_1.v14", %"iw_4.iw_1.iw_1.v16";
    %"iw_4.iw_1.iw_1.v18" : L = Shr %"iw_4.iw_1.iw_1.v17", #4;
    %"iw_4.iw_1.iw_1.v19" : L = Add %"iw_4.iw_1.iw_1.v17", %"iw_4.iw_1.iw_1.v18";
    %"iw_4.iw_1.iw_1.v20" : L = And %"iw_4.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_4.iw_1.iw_1.v21" : L = Mul %"iw_4.iw_1.iw_1.v20", #72340172838076673;
    %"iw_4.iw_1.iw_1.v22" : L = Shr %"iw_4.iw_1.iw_1.v21", #56
    => goto "iw_4.iw_1.iw_1.L4";
  @"iw_4.iw_1.iw_1.L4" [%"iw_4.iw_1.iw_1.v23" : W = phi("iw_4.iw_1.iw_1.L3" => %"iw_4.iw_1.iw_1.v22", "iw_4.start" => #64)]:
    %"iw_4.iw_1.v27" : W = Shr %"iw_4.iw_1.iw_1.v23", #3;
    %"v34" : L = (Ext Uw) %"iw_4.iw_1.v27";
    %"v35" = %"v0" +p %"v34"
    => ret %"v35";
  @"L37" [%"pr.1" : P = phi("L37" => %"v41", "start" => %"v12")]:
    %"v41" = %"pr.1" +p #8;
    %"chk1" : A = (Check 0 8 Read 1) %"v41";
    %"v42" : L = (RawLoad LdL 0) %"chk1";
    %"iw_5.iw_1.iw_1.v8" : L = Sub %"v42", #72340172838076673;
    %"iw_5.iw_1.iw_1.v10" : L = Xor %"v42", #(-1);
    %"iw_5.iw_1.iw_1.v11" : L = And %"iw_5.iw_1.iw_1.v8", %"iw_5.iw_1.iw_1.v10";
    %"iw_5.iw_1.iw_1.v13" : L = And %"iw_5.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_5.iw_1.v8" : L = Xor %"v42", %"iw_1.v7";
    %"iw_5.iw_1.iw_2.v8" : L = Sub %"iw_5.iw_1.v8", #72340172838076673;
    %"iw_5.iw_1.iw_2.v10" : L = Xor %"iw_5.iw_1.v8", #(-1);
    %"iw_5.iw_1.iw_2.v11" : L = And %"iw_5.iw_1.iw_2.v8", %"iw_5.iw_1.iw_2.v10";
    %"iw_5.iw_1.iw_2.v13" : L = And %"iw_5.iw_1.iw_2.v11", #9259542123273814144;
    %"iw_5.iw_1.v10" : L = Or %"iw_5.iw_1.iw_1.v13", %"iw_5.iw_1.iw_2.v13";
    %"v47" : W = (Cmp Eq L) %"iw_5.iw_1.v10", #0
    => br %"v47" ? poll "L37" : "iw_6.start";
  @"iw_6.start":
    => br %"v47" ? "iw_6.iw_3.iw_1.iw_1.L4" : "iw_6.iw_3.iw_1.iw_1.L3";
  @"iw_6.iw_3.iw_1.iw_1.L3":
    %"iw_6.iw_3.iw_1.iw_1.v8" : L = Neg %"iw_5.iw_1.v10";
    %"iw_6.iw_3.iw_1.iw_1.v9" : L = And %"iw_5.iw_1.v10", %"iw_6.iw_3.iw_1.iw_1.v8";
    %"iw_6.iw_3.iw_1.iw_1.v10" : L = Sub %"iw_6.iw_3.iw_1.iw_1.v9", #1;
    %"iw_6.iw_3.iw_1.iw_1.v11" : L = Shr %"iw_6.iw_3.iw_1.iw_1.v10", #1;
    %"iw_6.iw_3.iw_1.iw_1.v12" : L = And %"iw_6.iw_3.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_6.iw_3.iw_1.iw_1.v13" : L = Sub %"iw_6.iw_3.iw_1.iw_1.v10", %"iw_6.iw_3.iw_1.iw_1.v12";
    %"iw_6.iw_3.iw_1.iw_1.v14" : L = And %"iw_6.iw_3.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_6.iw_3.iw_1.iw_1.v15" : L = Shr %"iw_6.iw_3.iw_1.iw_1.v13", #2;
    %"iw_6.iw_3.iw_1.iw_1.v16" : L = And %"iw_6.iw_3.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_6.iw_3.iw_1.iw_1.v17" : L = Add %"iw_6.iw_3.iw_1.iw_1.v14", %"iw_6.iw_3.iw_1.iw_1.v16";
    %"iw_6.iw_3.iw_1.iw_1.v18" : L = Shr %"iw_6.iw_3.iw_1.iw_1.v17", #4;
    %"iw_6.iw_3.iw_1.iw_1.v19" : L = Add %"iw_6.iw_3.iw_1.iw_1.v17", %"iw_6.iw_3.iw_1.iw_1.v18";
    %"iw_6.iw_3.iw_1.iw_1.v20" : L = And %"iw_6.iw_3.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_6.iw_3.iw_1.iw_1.v21" : L = Mul %"iw_6.iw_3.iw_1.iw_1.v20", #72340172838076673;
    %"iw_6.iw_3.iw_1.iw_1.v22" : L = Shr %"iw_6.iw_3.iw_1.iw_1.v21", #56
    => goto "iw_6.iw_3.iw_1.iw_1.L4";
  @"iw_6.iw_3.iw_1.iw_1.L4" [%"iw_6.iw_3.iw_1.iw_1.v23" : W = phi("iw_6.iw_3.iw_1.iw_1.L3" => %"iw_6.iw_3.iw_1.iw_1.v22", "iw_6.start" => #64)]:
    %"iw_6.iw_3.iw_1.v27" : W = Shr %"iw_6.iw_3.iw_1.iw_1.v23", #3;
    %"v52" : L = (Ext Uw) %"iw_6.iw_3.iw_1.v27";
    %"v53" = %"v41" +p %"v52"
    => ret %"v53"
} }.

Definition item_strchrnul : item :=
  (IAlias (a "strchrnul") (a "weak") (a "__GI___strchrnul")).
