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

Definition hello_image_fn___vsnprintf_internal : func :=
  ir_fn{ "export" "__vsnprintf_internal"(P %"v0", L %"v2", P %"v4", P %"v6", W %"v8") -> (RClass W) {
  @"start":
    %"v10" : P = (Alloc 8) #168;
    call void $"__printf_buffer_snprintf_init"(P %"v10", P %"v0", L %"v2");
    call void $"__printf_buffer"(P %"v10", P %"v4", P %"v6", W %"v8");
    call %"v16" : W = $"__printf_buffer_snprintf_done"(P %"v10")
    => ret %"v16"
} }.
