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

Definition hello_image_fn_xmalloc : func :=
  mkFunc (a "xmalloc") (a "export") (RClass P) [(L, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") P) (Global (a "malloc")) [(Arg L (t "v0"))]);
      (Let (a "iw_1.v6") L Ptoi [(t "v3")]);
      (Let (a "iw_1.v8") W (Cmp Eq L) [(t "iw_1.v6"); (Const 0)])] (JBranch (t "iw_1.v8") (To (a "iw_1.L2")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L2") [] [(Call CVoid (Global (a "xalloc_die")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [] (JRet (t "v3")))].
