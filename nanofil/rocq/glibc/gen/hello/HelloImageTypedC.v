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

Definition hello_image_fn_c32isprint : func :=
  mkFunc (a "c32isprint") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") W) (Global (a "iswprint")) [(Arg W (t "v0"))])] (JRet (t "v3")))].
