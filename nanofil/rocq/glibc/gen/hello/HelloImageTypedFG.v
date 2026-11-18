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

Definition hello_image_fn___GI___fgets_unlocked : func :=
  ir_fn{ "export" "__GI___fgets_unlocked"(P %"v0", W %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v16" : W = (Cmp Sle W) %"v2", #0
    => br %"v16" ? "L12" : "L14";
  @"L12":
    => ret #0;
  @"L14":
    %"v22" : W = (Cmp Eq W) %"v2", #1
    => br %"v22" ? "L18" : "L20";
  @"L18":
    %"chk0" : A = (Check 0 1 Write 1) %"v0";
    store Wb [%"chk0" + 0] <- #0
    => ret %"v0";
  @"L20":
    %"chk1" : A = (Check 0 4 Read 1) %"v4";
    %"v30" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v31" : W = And %"v30", #32;
    %"v33" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v35" : W = And %"v33", #4294967263;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk1", %"v4";
    store Ww [%"chk3" + 0] <- %"v35";
    %"v39" : W = Sub %"v2", #1;
    %"v40" : L = (Ext Sw) %"v39";
    call %"v41" : L = $"__GI__IO_getline"(P %"v4", P %"v0", L %"v40", W #10, W #1);
    %"v46" : W = (Cmp Eq L) %"v41", #0
    => br %"v46" ? "L48" : "L47";
  @"L47":
    %"chk4" : A = (Renew 0 4 Read 1) %"chk1", %"v4";
    %"v50" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v51" : W = And %"v50", #32
    => br %"v51" ? "L52" : "L48";
  @"L52":
    %"v54" : P = Copy $"__libc_errno";
    %"chk5" : A = (Check 0 4 Read 1) %"v54";
    %"v55" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v56" : W = (Cmp Ne W) %"v55", #11
    => goto "L48";
  @"L48" [%"v60" : W = phi("L20" => #1, "L47" => #0, "L52" => %"v56")]:
    => br %"v60" ? "L44" : "L43";
  @"L43":
    %"v63" = %"v0" +p %"v41";
    %"chk6" : A = (Check 0 1 Write 1) %"v63";
    store Wb [%"chk6" + 0] <- #0
    => goto "L44";
  @"L44" [%"pr.1" : P = phi("L43" => %"v0", "L48" => #0)]:
    %"chk7" : A = (Renew 0 4 Read 1) %"chk1", %"v4";
    %"v66" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v68" : W = Or %"v66", %"v31";
    %"chk8" : A = (Renew 0 4 Write 1) %"chk1", %"v4";
    store Ww [%"chk8" + 0] <- %"v68"
    => ret %"pr.1"
} }.
