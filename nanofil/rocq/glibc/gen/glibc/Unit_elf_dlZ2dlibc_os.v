(** This file defines checked IR from glibc’s `elf/dl-libc.os` object.
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

Definition fn___libc_dlclose : func :=
  ir_fn{ "export" "__libc_dlclose"(P %"v0") -> (RClass W) {
  @"start":
    => ret #0
} }.

Definition fn___libc_dlopen_mode : func :=
  ir_fn{ "export" "__libc_dlopen_mode"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"zsys_dlopen"(P %"v0", W %"v2")
    => ret %"v6"
} }.

Definition fn___libc_dlsym : func :=
  ir_fn{ "export" "__libc_dlsym"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"zsys_dlsym"(P %"v0", P %"v2")
    => ret %"v6"
} }.
