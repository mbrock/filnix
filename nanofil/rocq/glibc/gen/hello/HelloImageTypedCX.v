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

Definition hello_image_fn___GI___cxa_atexit : func :=
  mkFunc (a "__GI___cxa_atexit") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v9") P Copy [(Global (a "__exit_funcs"))]);
      (Call (CResult (a "v10") W) (Global (a "__internal_atexit")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg P (t "v4")); (Arg P (t "v9"))])] (JRet (t "v10")))].
