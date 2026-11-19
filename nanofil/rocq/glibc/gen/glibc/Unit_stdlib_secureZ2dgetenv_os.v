(** This file defines checked IR from glibc’s `stdlib/secure-getenv.os` object.
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

Definition fn___GI___libc_secure_getenv : func :=
  ir_fn{ "export" "__GI___libc_secure_getenv"(P %"v0") -> (RClass P) {
  @"start":
    %"v5" : P = Copy $"__libc_enable_secure";
    %"chk0" : A = (Check 0 4 Read 1) %"v5";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => br %"v6" ? "L4" : "L3";
  @"L3":
    call %"v8" : P = $"__GI_getenv"(P %"v0")
    => goto "L4";
  @"L4" [%"v9" : P = phi("L3" => %"v8", "start" => #0)]:
    => ret %"v9"
} }.

Definition item_secure_getenv : item :=
  (IAlias (a "secure_getenv") (a "weak") (a "__GI___libc_secure_getenv")).
