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

Definition hello_image_fn_atexit : func :=
  mkFunc (a "atexit") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") W) (Global (a "__cxa_atexit")) [(Arg P (t "v0")); (Arg P (Const 0)); (Arg P (Const 0))])] (JRet (t "v3")))].
