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

Definition hi_fn___isatty_nostatus : func :=
  mkFunc (a "__isatty_nostatus") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P (Alloc 4) [(Const 44)]);
      (Call (CResult (a "v18") W) (Global (a "zsys_ioctl")) [(Arg W (t "v0")); (Arg W (Const 2150388778)); (Arg P (t "v2"))]);
      (Let (a "v19") W (Cmp Eq W) [(t "v18"); (Const 0)])] (JRet (t "v19")))].
