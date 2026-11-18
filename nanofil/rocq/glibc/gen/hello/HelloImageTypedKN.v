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

Definition hello_image_fn_glibc_gconv_dl'23known_compare : func :=
  mkFunc (a "glibc_gconv_dl#known_compare") (a "local") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v9") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v11") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Call (CResult (a "v12") W) (Global (a "__GI_strcmp")) [(Arg P (t "v9")); (Arg P (t "v11"))])] (JRet (t "v12")))].
