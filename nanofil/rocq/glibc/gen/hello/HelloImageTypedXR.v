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

Definition hello_image_fn_xrealloc : func :=
  mkFunc (a "xrealloc") (a "export") (RClass P) [(P, (a "v0")); (L, (a "v2"))] [(mkBlock (a "start") [] [(Call (CResult (a "v6") P) (Global (a "realloc")) [(Arg P (t "v0")); (Arg L (t "v2"))]);
      (Let (a "iw_1.v6") L Ptoi [(t "v6")]);
      (Let (a "iw_1.v8") W (Cmp Eq L) [(t "iw_1.v6"); (Const 0)])] (JBranch (t "iw_1.v8") (To (a "iw_1.L2")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L2") [] [(Call CVoid (Global (a "xalloc_die")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [] (JRet (t "v6")))].
