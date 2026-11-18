(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___vsnprintf_internal : func :=
  mkFunc (a "__vsnprintf_internal") (a "export") (RClass W) [(P, (a "v0")); (L, (a "v2")); (P, (a "v4")); (P, (a "v6")); (W, (a "v8"))] [(mkBlock (a "start") [] [(Let (a "v10") P (Alloc 8) [(Const 168)]);
      (Call CVoid (Global (a "__printf_buffer_snprintf_init")) [(Arg P (t "v10")); (Arg P (t "v0")); (Arg L (t "v2"))]);
      (Call CVoid (Global (a "__printf_buffer")) [(Arg P (t "v10")); (Arg P (t "v4")); (Arg P (t "v6")); (Arg W (t "v8"))]);
      (Call (CResult (a "v16") W) (Global (a "__printf_buffer_snprintf_done")) [(Arg P (t "v10"))])] (JRet (t "v16")))].
