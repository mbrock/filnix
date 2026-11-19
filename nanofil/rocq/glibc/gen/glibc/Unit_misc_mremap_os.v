(** This file defines checked IR from glibc’s `misc/mremap.os` object.
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

Definition fn___GI___mremap : func :=
  ir_fn{ "export" "__GI___mremap"(P %"v0", L %"v2", L %"v4", W %"v6") -> (RClass P) {
  @"start":
    %"v8" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #32;
    %"v17" : W = And %"v6", #4294967288
    => br %"v17" ? "L10" : "L12";
  @"L10":
    %"v18" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v18";
    store Ww [%"chk0" + 0] <- #22;
    (Flight (a "v21") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v21";
  @"L12":
    %"v28" : W = And %"v6", #6
    => br %"v28" ? "L23" : "L25";
  @"L23":
    %"chk1" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk1" + 0] <- %"va_args";
    %"v29" : P = VaArg %"v8"
    => goto "L25";
  @"L25" [%"pr.1" : P = phi("L23" => %"v29", "L12" => #0)]:
    call %"v35" : P = $"zsys_mremap"(P %"v0", L %"v2", L %"v4", W %"v6", P %"pr.1")
    => ret %"v35"
} }.
