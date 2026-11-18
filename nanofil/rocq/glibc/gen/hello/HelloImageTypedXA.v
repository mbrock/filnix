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

Definition hello_image_fn_xalloc_die : func :=
  mkFunc (a "xalloc_die") (a "export") RVoid [] [(mkBlock (a "start") [] [(Let (a "v16") P Copy [(Global (a "exit_failure"))]);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v16")]);
      (Let (a "v17") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v19") P Copy [(Global (a "xalloc-die#str.41"))]);
      (Let (a "v20") P Copy [(Global (a "xalloc-die#str.42"))]);
      (Let (a "v21") P Copy [(Global (a "xalloc-die#str.43"))]);
      (Call CVoid (Global (a "error")) [(Arg W (t "v17")); (Arg W (Const 0)); (Arg P (t "v19")); (Arg P (t "v21"))]);
      (Let (a "v26") W (Cmp Ne W) [(t "v17"); (Const 0)])] (JBranch (t "v26") (To (a "L22")) (To (a "L2"))));
  (mkBlock (a "L22") [] [] JUnreachable);
  (mkBlock (a "L2") [] [(Call CVoid (Global (a "abort")) [])] JRetVoid)].
