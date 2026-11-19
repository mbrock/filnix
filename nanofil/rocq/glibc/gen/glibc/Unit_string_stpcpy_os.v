(** This file defines checked IR from glibc’s `string/stpcpy.os` object.
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

Definition fn___GI___stpcpy : func :=
  ir_fn{ "export" "__GI___stpcpy"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    %"v6" : L = Ptoi %"v0";
    %"v7" : L = Neg %"v6";
    %"v8" : L = And %"v7", #7
    => goto "L9";
  @"L9" [%"pr.3" : L = phi("L11" => %"v29", "start" => %"v8"); %"pr.2" : P = phi("L11" => %"v17", "start" => %"v2"); %"pr.1" : P = phi("L11" => %"v31", "start" => %"v0")]:
    %"v14" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v14" ? "L10" : "L12";
  @"L10":
    %"v17" = %"pr.2" +p #1;
    %"chk0" : A = (Check 0 1 Read 1) %"pr.2";
    %"v18" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"chk1" : A = (Check 0 1 Write 1) %"pr.1";
    store Wb [%"chk1" + 0] <- %"v18";
    %"v25" : W = (Cmp Eq W) %"v18", #0
    => br %"v25" ? "L21" : "L11";
  @"L21":
    => ret %"pr.1";
  @"L11":
    %"v29" : L = Sub %"pr.3", #1;
    %"v31" = %"pr.1" +p #1
    => goto poll "L9";
  @"L12":
    %"v34" : L = Ptoi %"pr.2";
    %"v35" : L = And %"v34", #7;
    %"v40" : W = (Cmp Eq L) %"v35", #0
    => br %"v40" ? "iw_1.L5" : "L37";
  @"iw_1.L5" [%"iw_1.pr.2" : P = phi("iw_1.L13" => %"iw_1.v9", "L12" => %"pr.2"); %"iw_1.pr.1" : P = phi("iw_1.L13" => %"iw_1.v19", "L12" => %"pr.1")]:
    %"iw_1.v9" = %"iw_1.pr.2" +p #8;
    %"chk2" : A = (Check 0 8 Read 1) %"iw_1.pr.2";
    %"iw_1.v10" : L = (RawLoad LdL 0) %"chk2";
    %"iw_1.iw_1.iw_1.v8" : L = Sub %"iw_1.v10", #72340172838076673;
    %"iw_1.iw_1.iw_1.v10" : L = Xor %"iw_1.v10", #(-1);
    %"iw_1.iw_1.iw_1.v11" : L = And %"iw_1.iw_1.iw_1.v8", %"iw_1.iw_1.iw_1.v10";
    %"iw_1.iw_1.iw_1.v13" : L = And %"iw_1.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_1.iw_1.v4" : W = (Cmp Ne L) %"iw_1.iw_1.iw_1.v13", #0
    => br %"iw_1.iw_1.v4" ? "iw_1.iw_2.L7" : "iw_1.L13";
  @"iw_1.L13":
    %"iw_1.v19" = %"iw_1.pr.1" +p #8;
    %"chk3" : A = (Check 0 8 Write 1) %"iw_1.pr.1";
    store Wl [%"chk3" + 0] <- %"iw_1.v10"
    => goto poll "iw_1.L5";
  @"iw_1.iw_2.L7" [%"iw_1.iw_2.pr.2" : L = phi("iw_1.iw_2.L9" => %"iw_1.iw_2.v28", "iw_1.L5" => #0); %"iw_1.iw_2.pr.1" : P = phi("iw_1.iw_2.L9" => %"iw_1.iw_2.v30", "iw_1.L5" => %"iw_1.pr.1")]:
    %"iw_1.iw_2.v12" : W = (Cmp Ult L) %"iw_1.iw_2.pr.2", #8
    => br %"iw_1.iw_2.v12" ? "iw_1.iw_2.L8" : "L38";
  @"iw_1.iw_2.L8":
    %"iw_1.iw_2.iw_1.v2" : W = Copy %"iw_1.iw_2.pr.2";
    %"iw_1.iw_2.iw_1.v10" : W = Shl %"iw_1.iw_2.iw_1.v2", #3;
    %"iw_1.iw_2.iw_1.v11" : L = Shr %"iw_1.v10", %"iw_1.iw_2.iw_1.v10";
    %"iw_1.iw_2.iw_1.v12" : W = (Ext Ub) %"iw_1.iw_2.iw_1.v11";
    %"iw_1.iw_2.v18" : W = (Ext Sb) %"iw_1.iw_2.iw_1.v12";
    %"chk4" : A = (Check 0 1 Write 1) %"iw_1.iw_2.pr.1";
    store Wb [%"chk4" + 0] <- %"iw_1.iw_2.v18";
    %"iw_1.iw_2.v25" : W = (Cmp Eq W) %"iw_1.iw_2.v18", #0
    => br %"iw_1.iw_2.v25" ? "L38" : "iw_1.iw_2.L9";
  @"iw_1.iw_2.L9":
    %"iw_1.iw_2.v28" : L = Add %"iw_1.iw_2.pr.2", #1;
    %"iw_1.iw_2.v30" = %"iw_1.iw_2.pr.1" +p #1
    => goto poll "iw_1.iw_2.L7";
  @"L37":
    (Flight (a "v47") Sub [(FAddress (t "pr.2")); (FValue (t "v35"))] (LowerOf (t "pr.2")));
    %"iw_2.v8" = %"v47" +p #8;
    %"chk5" : A = (Check 0 8 Read 1) %"v47";
    %"iw_2.v9" : L = (RawLoad LdL 0) %"chk5";
    %"iw_2.v12" : L = Shl %"v35", #3;
    %"iw_2.v16" : L = Sub #64, %"iw_2.v12";
    %"iw_2.v20" : L = Shr %"iw_2.v9", %"iw_2.v12";
    %"iw_2.v24" : L = Shl #18446744073709551615, %"iw_2.v16";
    %"iw_2.v25" : L = Or %"iw_2.v20", %"iw_2.v24";
    %"iw_2.iw_1.iw_1.v8" : L = Sub %"iw_2.v25", #72340172838076673;
    %"iw_2.iw_1.iw_1.v10" : L = Xor %"iw_2.v25", #(-1);
    %"iw_2.iw_1.iw_1.v11" : L = And %"iw_2.iw_1.iw_1.v8", %"iw_2.iw_1.iw_1.v10";
    %"iw_2.iw_1.iw_1.v13" : L = And %"iw_2.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_2.v32" : W = (Cmp Eq L) %"iw_2.iw_1.iw_1.v13", #0
    => br %"iw_2.v32" ? "iw_2.L34" : "iw_2.L53";
  @"iw_2.L34" [%"iw_2.pr.6" : L = phi("L37" => %"iw_2.v9", "iw_2.L49" => %"iw_2.v39"); %"iw_2.pr.5" : P = phi("L37" => %"iw_2.v8", "iw_2.L49" => %"iw_2.v38"); %"iw_2.pr.2" : P = phi("L37" => %"pr.1", "iw_2.L49" => %"iw_2.v56")]:
    %"iw_2.v38" = %"iw_2.pr.5" +p #8;
    %"chk6" : A = (Check 0 8 Read 1) %"iw_2.pr.5";
    %"iw_2.v39" : L = (RawLoad LdL 0) %"chk6";
    %"iw_2.v42" : L = Shr %"iw_2.pr.6", %"iw_2.v12";
    %"iw_2.v45" : L = Shl %"iw_2.v39", %"iw_2.v16";
    %"iw_2.v46" : L = Or %"iw_2.v42", %"iw_2.v45";
    %"iw_2.iw_2.iw_1.v8" : L = Sub %"iw_2.v46", #72340172838076673;
    %"iw_2.iw_2.iw_1.v10" : L = Xor %"iw_2.v46", #(-1);
    %"iw_2.iw_2.iw_1.v11" : L = And %"iw_2.iw_2.iw_1.v8", %"iw_2.iw_2.iw_1.v10";
    %"iw_2.iw_2.iw_1.v13" : L = And %"iw_2.iw_2.iw_1.v11", #9259542123273814144;
    %"iw_2.iw_2.v4" : W = (Cmp Ne L) %"iw_2.iw_2.iw_1.v13", #0
    => br %"iw_2.iw_2.v4" ? "iw_2.L53" : "iw_2.L49";
  @"iw_2.L49":
    %"iw_2.v56" = %"iw_2.pr.2" +p #8;
    %"chk7" : A = (Check 0 8 Write 1) %"iw_2.pr.2";
    store Wl [%"chk7" + 0] <- %"iw_2.v46";
    %"iw_2.iw_3.iw_1.v8" : L = Sub %"iw_2.v39", #72340172838076673;
    %"iw_2.iw_3.iw_1.v10" : L = Xor %"iw_2.v39", #(-1);
    %"iw_2.iw_3.iw_1.v11" : L = And %"iw_2.iw_3.iw_1.v8", %"iw_2.iw_3.iw_1.v10";
    %"iw_2.iw_3.iw_1.v13" : L = And %"iw_2.iw_3.iw_1.v11", #9259542123273814144;
    %"iw_2.iw_3.v4" : W = (Cmp Ne L) %"iw_2.iw_3.iw_1.v13", #0
    => br %"iw_2.iw_3.v4" ? "iw_2.L36" : poll "iw_2.L34";
  @"iw_2.L36":
    %"iw_2.v68" : L = Shr %"iw_2.v39", %"iw_2.v12";
    %"iw_2.v70" : W = Shl #0, %"iw_2.v16";
    %"iw_2.v71" : L = (Ext Sw) %"iw_2.v70";
    %"iw_2.v72" : L = Or %"iw_2.v68", %"iw_2.v71"
    => goto "iw_2.L53";
  @"iw_2.L53" [%"iw_2.pr.8" : L = phi("iw_2.L34" => %"iw_2.v46", "iw_2.L36" => %"iw_2.v72", "L37" => %"iw_2.v25"); %"iw_2.pr.4" : P = phi("iw_2.L34" => %"iw_2.pr.2", "iw_2.L36" => %"iw_2.v56", "L37" => %"pr.1")]:
    => goto "iw_2.iw_4.L7";
  @"iw_2.iw_4.L7" [%"iw_2.iw_4.pr.2" : L = phi("iw_2.iw_4.L9" => %"iw_2.iw_4.v28", "iw_2.L53" => #0); %"iw_2.iw_4.pr.1" : P = phi("iw_2.iw_4.L9" => %"iw_2.iw_4.v30", "iw_2.L53" => %"iw_2.pr.4")]:
    %"iw_2.iw_4.v12" : W = (Cmp Ult L) %"iw_2.iw_4.pr.2", #8
    => br %"iw_2.iw_4.v12" ? "iw_2.iw_4.L8" : "L38";
  @"iw_2.iw_4.L8":
    %"iw_2.iw_4.iw_1.v2" : W = Copy %"iw_2.iw_4.pr.2";
    %"iw_2.iw_4.iw_1.v10" : W = Shl %"iw_2.iw_4.iw_1.v2", #3;
    %"iw_2.iw_4.iw_1.v11" : L = Shr %"iw_2.pr.8", %"iw_2.iw_4.iw_1.v10";
    %"iw_2.iw_4.iw_1.v12" : W = (Ext Ub) %"iw_2.iw_4.iw_1.v11";
    %"iw_2.iw_4.v18" : W = (Ext Sb) %"iw_2.iw_4.iw_1.v12";
    %"chk8" : A = (Check 0 1 Write 1) %"iw_2.iw_4.pr.1";
    store Wb [%"chk8" + 0] <- %"iw_2.iw_4.v18";
    %"iw_2.iw_4.v25" : W = (Cmp Eq W) %"iw_2.iw_4.v18", #0
    => br %"iw_2.iw_4.v25" ? "L38" : "iw_2.iw_4.L9";
  @"iw_2.iw_4.L9":
    %"iw_2.iw_4.v28" : L = Add %"iw_2.iw_4.pr.2", #1;
    %"iw_2.iw_4.v30" = %"iw_2.iw_4.pr.1" +p #1
    => goto poll "iw_2.iw_4.L7";
  @"L38" [%"v50" : P = phi("iw_1.iw_2.L7" => %"iw_1.iw_2.pr.1", "iw_1.iw_2.L8" => %"iw_1.iw_2.pr.1", "iw_2.iw_4.L7" => %"iw_2.iw_4.pr.1", "iw_2.iw_4.L8" => %"iw_2.iw_4.pr.1")]:
    => ret %"v50"
} }.

Definition item___GI_stpcpy : item :=
  (IAlias (a "__GI_stpcpy") (a "weak") (a "__GI___stpcpy")).

Definition item_stpcpy : item :=
  (IAlias (a "stpcpy") (a "export") (a "__GI___stpcpy")).
