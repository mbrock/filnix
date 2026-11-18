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

Definition hello_image_fn__itoa_word : func :=
  ir_fn{ "export" "_itoa_word"(L %"v0", P %"v2", W %"v4", W %"v6") -> (RClass P) {
  @"start":
    => br %"v6" ? "L9" : "L10";
  @"L9":
    %"v13" : P = Copy $"__GI__itoa_upper_digits"
    => goto "L11";
  @"L10":
    %"v14" : P = Copy $"__GI__itoa_lower_digits"
    => goto "L11";
  @"L11" [%"v15" : P = phi("L9" => %"v13", "L10" => %"v14")]:
    %"v79" : W = (Cmp Eq W) %"v4", #10
    => br %"v79" ? "L20" : "L80";
  @"L20" [%"pr.6" : P = phi("L20" => %"v24", "L11" => %"v2"); %"pr.1" : L = phi("L20" => %"v31", "L11" => %"v0")]:
    (Flight (a "v24") Sub [(FAddress (t "pr.6")); (FValue (Const 1))] (LowerOf (t "pr.6")));
    %"v27" : L = Urem %"pr.1", #10;
    %"v28" = %"v15" +p %"v27";
    %"chk0" : A = (Check 0 1 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"chk1" : A = (Check 0 1 Write 1) %"v24";
    store Wb [%"chk1" + 0] <- %"v29";
    %"v31" : L = Udiv %"pr.1", #10;
    %"v32" : W = (Cmp Ne L) %"v31", #0
    => br %"v32" ? poll "L20" : "L18";
  @"L34" [%"pr.7" : P = phi("L34" => %"v38", "L80" => %"v2"); %"pr.2" : L = phi("L34" => %"v45", "L80" => %"v0")]:
    (Flight (a "v38") Sub [(FAddress (t "pr.7")); (FValue (Const 1))] (LowerOf (t "pr.7")));
    %"v41" : L = And %"pr.2", #15;
    %"v42" = %"v15" +p %"v41";
    %"chk2" : A = (Check 0 1 Read 1) %"v42";
    %"v43" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"chk3" : A = (Check 0 1 Write 1) %"v38";
    store Wb [%"chk3" + 0] <- %"v43";
    %"v45" : L = Shr %"pr.2", #4;
    %"v46" : W = (Cmp Ne L) %"v45", #0
    => br %"v46" ? poll "L34" : "L18";
  @"L48" [%"pr.8" : P = phi("L48" => %"v52", "L82" => %"v2"); %"pr.3" : L = phi("L48" => %"v59", "L82" => %"v0")]:
    (Flight (a "v52") Sub [(FAddress (t "pr.8")); (FValue (Const 1))] (LowerOf (t "pr.8")));
    %"v55" : L = And %"pr.3", #7;
    %"v56" = %"v15" +p %"v55";
    %"chk4" : A = (Check 0 1 Read 1) %"v56";
    %"v57" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"chk5" : A = (Check 0 1 Write 1) %"v52";
    store Wb [%"chk5" + 0] <- %"v57";
    %"v59" : L = Shr %"pr.3", #3;
    %"v60" : W = (Cmp Ne L) %"v59", #0
    => br %"v60" ? poll "L48" : "L18";
  @"L62" [%"pr.9" : P = phi("L62" => %"v66", "L82" => %"v2"); %"pr.4" : L = phi("L62" => %"v77", "L82" => %"v0")]:
    (Flight (a "v66") Sub [(FAddress (t "pr.9")); (FValue (Const 1))] (LowerOf (t "pr.9")));
    %"v70" : L = (Ext Uw) %"v4";
    %"v71" : L = Urem %"pr.4", %"v70";
    %"v72" = %"v15" +p %"v71";
    %"chk6" : A = (Check 0 1 Read 1) %"v72";
    %"v73" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"chk7" : A = (Check 0 1 Write 1) %"v66";
    store Wb [%"chk7" + 0] <- %"v73";
    %"v77" : L = Udiv %"pr.4", %"v70";
    %"v78" : W = (Cmp Ne L) %"v77", #0
    => br %"v78" ? poll "L62" : "L18";
  @"L80":
    %"v81" : W = (Cmp Eq W) %"v4", #16
    => br %"v81" ? poll "L34" : "L82";
  @"L82":
    %"v83" : W = (Cmp Eq W) %"v4", #8
    => br %"v83" ? poll "L48" : poll "L62";
  @"L18" [%"pr.5" : P = phi("L20" => %"v24", "L34" => %"v38", "L48" => %"v52", "L62" => %"v66")]:
    => ret %"pr.5"
} }.
