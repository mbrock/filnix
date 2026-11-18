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

Definition hi_fn_glibc_libc_start'23futex_wake : func :=
  ir_fn{ "local" "glibc_libc_start#futex_wake"(P %"v0", W %"v2", W %"v4") -> RVoid {
  @"start":
    %"v16" : W = (Cmp Eq W) %"v4", #0
    => br %"v16" ? "L18" : "L17";
  @"L17":
    %"v20" : W = (Cmp Eq W) %"v4", #128
    => goto "L18";
  @"L18" [%"v22" : W = phi("start" => #1, "L17" => %"v20")]:
    => br %"v22" ? "L11" : "L14";
  @"L14":
    %"v24" : P = Copy $"glibc_libc_start#str.322";
    %"v25" : P = Copy $"glibc_libc_start#str.323";
    %"v26" : P = Copy $"glibc_libc_start#str.324";
    %"v27" : P = Copy $"glibc_libc_start#str.325";
    call void $"zerrorf"(P %"v24", P %"v25", W #173, P %"v26", P %"v27")
    => goto "L11";
  @"L11":
    => br %"v16" ? "L30" : "L29";
  @"L29":
    => goto "L30";
  @"L30" [%"v33" : W = phi("L29" => #0, "L11" => #1)]:
    call void $"zsys_futex_wake"(P %"v0", W %"v2", W %"v33")
    => ret void
} }.
