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

Definition hi_fn___GI__exit : func :=
  mkFunc (a "__GI__exit") (a "export") RVoid [(W, (a "v0"))] [(mkBlock (a "start") [] [(Call CVoid (Global (a "zsys_exit_hard")) [(Arg W (t "v0"))])] JRetVoid)].

Definition hi_fn___GI_exit : func :=
  mkFunc (a "__GI_exit") (a "export") RVoid [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v3") P Copy [(Global (a "__exit_funcs"))]);
      (Call CVoid (Global (a "__run_exit_handlers")) [(Arg W (t "v0")); (Arg P (t "v3")); (Arg W (Const 1)); (Arg W (Const 1))])] JRetVoid)].
