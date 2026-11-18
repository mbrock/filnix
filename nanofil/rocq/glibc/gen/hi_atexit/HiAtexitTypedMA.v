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

Definition hi_fn_main : func :=
  ir_fn{ "export" "main"() -> (RClass W) {
  @"start":
    %"v0" : P = Copy $"hi_atexit#close_stdout_hi";
    call %"v1" : W = $"atexit"(P %"v0");
    %"v2" : P = Copy $"hi_atexit#str.0";
    call %"v3" : W = $"puts"(P %"v2");
    call void $"exit"(W #0)
    => ret #0
} }.

Definition hi_fn_glibc_malloc'23malloc_printerr : func :=
  ir_fn{ "local" "glibc_malloc#malloc_printerr"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_malloc#str.407";
    %"v3" : P = Copy $"glibc_malloc#str.408";
    call void $"__libc_message_impl"(P %"v2", P %"v3", P %"v0")
    => unreachable
} }.
