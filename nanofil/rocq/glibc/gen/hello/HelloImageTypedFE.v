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

Definition hello_image_fn___feof_unlocked : func :=
  mkFunc (a "__feof_unlocked") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 4 Read 1) [(t "v0")]);
      (Let (a "v6") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v7") W And [(t "v6"); (Const 16)]);
      (Let (a "v8") W (Cmp Ne W) [(t "v7"); (Const 0)])] (JRet (t "v8")))].
