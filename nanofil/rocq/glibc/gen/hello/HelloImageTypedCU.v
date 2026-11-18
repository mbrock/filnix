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

Definition hello_image_fn___current_locale_name : func :=
  mkFunc (a "__current_locale_name") (a "export") (RClass P) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v3") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v4") Add [(FAddress (t "v3")); (FValue (Const 128))] (LowerOf (t "v3")));
      (Let (a "v6") L (Ext Sw) [(t "v0")]);
      (Let (a "v7") L Shl [(t "v6"); (Const 3)]);
      (Flight (a "v8") Add [(FAddress (t "v4")); (FValue (t "v7"))] (LowerOf (t "v4")));
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v8")]);
      (Let (a "v9") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")])] (JRet (t "v9")))].
