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

Definition hello_image_fn____asprintf : func :=
  mkFunc (a "___asprintf") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v4") P (Alloc 8) [(Const 24)]);
      (Let (a "va_args") P VaArgs [(Const 16)]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v4")]);
      (RawStorePointer 0 (t "va_args") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Call (CResult (a "v8") W) (Global (a "__vasprintf_internal")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg P (t "v4")); (Arg W (Const 0))])] (JRet (t "v8")))].
