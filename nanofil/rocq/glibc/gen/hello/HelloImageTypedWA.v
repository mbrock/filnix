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

Definition hello_image_fn___GI___wait4 : func :=
  mkFunc (a "__GI___wait4") (a "export") (RClass W) [(W, (a "v0")); (P, (a "v2")); (W, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Call (CResult (a "v12") W) (Global (a "zsys_wait4")) [(Arg W (t "v0")); (Arg P (t "v2")); (Arg W (t "v4")); (Arg P (t "v6"))])] (JRet (t "v12")))].

Definition hello_image_fn___GI___waitpid : func :=
  mkFunc (a "__GI___waitpid") (a "export") (RClass W) [(W, (a "v0")); (P, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [(Call (CResult (a "v9") W) (Global (a "__GI___wait4")) [(Arg W (t "v0")); (Arg P (t "v2")); (Arg W (t "v4")); (Arg P (Const 0))])] (JRet (t "v9")))].
