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

Definition hello_image_fn___opendir : func :=
  ir_fn{ "export" "__opendir"(P %"v0") -> (RClass P) {
  @"start":
    %"chk0" : A = (Check 0 1 Read 1) %"v0";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"iw_1.v8" : W = (Cmp Eq W) %"iw_1.v7", #0
    => br %"iw_1.v8" ? "iw_1.L2" : "iw_1.join";
  @"iw_1.L2":
    %"iw_1.v11" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.v11";
    store Ww [%"chk1" + 0] <- #2
    => goto "iw_1.join";
  @"iw_1.join" [%"v6" : W = phi("iw_1.L2" => #1, "start" => #0)]:
    => br %"v6" ? "L2" : "L4";
  @"L2":
    => ret #0;
  @"L4":
    call %"v12" : W = $"__GI___open_nocancel"(P %"v0", W #591872);
    %"iw_2.v10" : P = (Alloc 8) #144;
    %"iw_2.v6" : W = (Cmp Slt W) %"v12", #0
    => br %"iw_2.v6" ? "iw_2.join" : "iw_2.L4";
  @"iw_2.L4":
    call %"iw_2.v15" : W = $"__GI___fstat64"(W %"v12", P %"iw_2.v10");
    %"iw_2.v16" : W = (Cmp Slt W) %"iw_2.v15", #0
    => br %"iw_2.v16" ? "iw_2.L19" : "iw_2.L13";
  @"iw_2.L13":
    %"iw_2.v24" = %"iw_2.v10" +p #24;
    %"chk2" : A = (Check 0 4 Read 1) %"iw_2.v24";
    %"iw_2.v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"iw_2.v26" : W = And %"iw_2.v25", #61440;
    %"iw_2.v28" : W = (Cmp Ne W) %"iw_2.v26", #16384
    => br %"iw_2.v28" ? "iw_2.L21" : "iw_2.L23";
  @"iw_2.L21":
    %"iw_2.v31" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"iw_2.v31";
    store Ww [%"chk3" + 0] <- #20
    => goto "iw_2.L19";
  @"iw_2.L19":
    call void $"__GI___close_nocancel_nostatus"(W %"v12")
    => goto "iw_2.join";
  @"iw_2.L23":
    call %"iw_2.v36" : P = $"__alloc_dir"(W %"v12", W #1, W #0, P %"iw_2.v10")
    => goto "iw_2.join";
  @"iw_2.join" [%"v13" : P = phi("iw_2.L19" => #0, "iw_2.L23" => %"iw_2.v36", "L4" => #0)]:
    => ret %"v13"
} }.

Definition hello_image_fn___GI___open64_nocancel : func :=
  ir_fn{ "export" "__GI___open64_nocancel"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"va_args" : P = VaArgs #16;
    %"v4" : P = Copy $"zsys_open";
    %"v5" : P = VaArgs #0;
    call %"v6" : P = $"zcall"(P %"v4", P %"v5");
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret %"v7"
} }.
