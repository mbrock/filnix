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

Definition hello_image_fn___gnu_dev_major : func :=
  mkFunc (a "__gnu_dev_major") (a "export") (RClass W) [(L, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v4") L And [(t "v0"); (Const 1048320)]);
      (Let (a "v5") L Shr [(t "v4"); (Const 8)]);
      (Let (a "v6") W Copy [(t "v5")]);
      (Let (a "v8") L And [(t "v0"); (Const 18446726481523507200)]);
      (Let (a "v9") L Shr [(t "v8"); (Const 32)]);
      (Let (a "v10") L (Ext Uw) [(t "v6")]);
      (Let (a "v11") L Or [(t "v10"); (t "v9")]);
      (Let (a "v12") W Copy [(t "v11")])] (JRet (t "v12")))].
