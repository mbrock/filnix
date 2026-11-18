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

Definition hello_image_fn___GI___snprintf : func :=
  mkFunc (a "__GI___snprintf") (a "export") (RClass W) [(P, (a "v0")); (L, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v6") P (Alloc 8) [(Const 24)]);
      (Let (a "va_args") P VaArgs [(Const 24)]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v6")]);
      (RawStorePointer 0 (t "va_args") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Call (CResult (a "v11") W) (Global (a "__vsnprintf_internal")) [(Arg P (t "v0")); (Arg L (t "v2")); (Arg P (t "v4")); (Arg P (t "v6")); (Arg W (Const 0))])] (JRet (t "v11")))].
