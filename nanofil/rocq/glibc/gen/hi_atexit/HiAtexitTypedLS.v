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

Definition hi_fn___lseek64 : func :=
  mkFunc (a "__lseek64") (a "export") (RClass L) [(W, (a "v0")); (L, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [(Call (CResult (a "v9") L) (Global (a "zsys_lseek")) [(Arg W (t "v0")); (Arg L (t "v2")); (Arg W (t "v4"))])] (JRet (t "v9")))].
