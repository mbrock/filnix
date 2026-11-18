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

Definition hello_image_fn_emit_bug_reporting_address : func :=
  mkFunc (a "emit_bug_reporting_address") (a "export") RVoid [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "version-etc#str.45"))]);
      (Let (a "v1") P Copy [(Global (a "stdout"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v1")]);
      (Let (a "v2") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call (CResult (a "v3") W) (Global (a "fputs")) [(Arg P (t "v0")); (Arg P (t "v2"))]);
      (Let (a "v4") P Copy [(Global (a "version-etc#str.43"))]);
      (Let (a "v5") P Copy [(Global (a "version-etc#str.58"))]);
      (Let (a "v6") P Copy [(Global (a "version-etc#str.59"))]);
      (Call (CResult (a "v7") W) (Global (a "printf")) [(Arg P (t "v5")); (Arg P (t "v6"))]);
      (Let (a "v8") P Copy [(Global (a "version-etc#str.43"))]);
      (Let (a "v9") P Copy [(Global (a "version-etc#str.60"))]);
      (Let (a "v10") P Copy [(Global (a "version-etc#str.61"))]);
      (Let (a "v11") P Copy [(Global (a "version-etc#str.62"))]);
      (Call (CResult (a "v12") W) (Global (a "printf")) [(Arg P (t "v9")); (Arg P (t "v10")); (Arg P (t "v11"))]);
      (Let (a "v13") P Copy [(Global (a "version-etc#str.43"))]);
      (Let (a "v14") P Copy [(Global (a "version-etc#str.63"))]);
      (Let (a "v15") P Copy [(Global (a "version-etc#str.64"))]);
      (Call (CResult (a "v16") W) (Global (a "printf")) [(Arg P (t "v14")); (Arg P (t "v15"))])] JRetVoid)].
