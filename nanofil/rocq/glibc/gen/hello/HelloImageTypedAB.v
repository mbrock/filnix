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

Definition hello_image_fn___GI_abort : func :=
  mkFunc (a "__GI_abort") (a "export") RVoid [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "glibc_abort#str.268"))]);
      (Call CVoid (Global (a "zerror")) [(Arg P (t "v0"))])] (JGoto (To (a "L2"))));
  (mkBlock (a "L2") [] [(Let (a "v4") P Copy [(Global (a "glibc_abort#str.269"))]);
      (Call CVoid (Global (a "zsafety_error")) [(Arg P (t "v4"))])] (JGoto (Poll (a "L2"))))].

Definition hello_image_fn_abs : func :=
  mkFunc (a "abs") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v6") W (Cmp Slt W) [(t "v0"); (Const 0)])] (JBranch (t "v6") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [(Let (a "v8") W Neg [(t "v0")])] (JGoto (To (a "L4"))));
  (mkBlock (a "L4") [(Phi (a "v10") W [((a "L2"), (t "v8")); ((a "start"), (t "v0"))])] [] (JRet (t "v10")))].
