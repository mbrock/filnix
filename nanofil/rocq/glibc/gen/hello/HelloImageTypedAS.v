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

Definition hello_image_fn____asprintf : func :=
  ir_fn{ "export" "___asprintf"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #16;
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- %"va_args";
    call %"v8" : W = $"__vasprintf_internal"(P %"v0", P %"v2", P %"v4", W #0)
    => ret %"v8"
} }.
