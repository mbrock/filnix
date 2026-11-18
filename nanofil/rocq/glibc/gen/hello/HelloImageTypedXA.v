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

Definition hello_image_fn_xalloc_die : func :=
  ir_fn{ "export" "xalloc_die"() -> RVoid {
  @"start":
    %"v16" : P = Copy $"exit_failure";
    %"chk0" : A = (Check 0 4 Read 1) %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v19" : P = Copy $"xalloc-die#str.41";
    %"v20" : P = Copy $"xalloc-die#str.42";
    %"v21" : P = Copy $"xalloc-die#str.43";
    call void $"error"(W %"v17", W #0, P %"v19", P %"v21");
    %"v26" : W = (Cmp Ne W) %"v17", #0
    => br %"v26" ? "L22" : "L2";
  @"L22":
    => unreachable;
  @"L2":
    call void $"abort"()
    => ret void
} }.
