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

Definition hello_image_fn___GI___lll_lock_wait_private : func :=
  mkFunc (a "__GI___lll_lock_wait_private") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 4 Read 1) [(t "v0")]);
      (Let (a "v6") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v7") W (Cmp Eq W) [(t "v6"); (Const 2)])] (JBranch (t "v7") (To (a "iw_1.L29")) (To (a "L10"))));
  (mkBlock (a "L10") [] [(Let (a "chk1") A (Renew 0 4 Read 1) [(t "chk0"); (t "v0")]);
      (Let (a "v14") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")])] (JGoto (To (a "L15"))));
  (mkBlock (a "L15") [(Phi (a "v17") W [((a "L10"), (t "v14")); ((a "L15"), (t "v18"))])] [(Let (a "chk2") A (HalfCheck Lower 0 4 Write 4) [(t "chk0"); (t "v0")]);
      (Let (a "v18") W (RawCas (CasNarrow Sw) 0) [(t "chk2"); (t "v17"); (Const 2)]);
      (Let (a "v19") W (Cmp Eq W) [(t "v18"); (t "v17")])] (JBranch (t "v19") (To (a "L16")) (Poll (a "L15"))));
  (mkBlock (a "L16") [] [(Let (a "v20") W (Cmp Ne W) [(t "v17"); (Const 0)])] (JBranch (t "v20") (To (a "iw_1.L29")) (To (a "L12"))));
  (mkBlock (a "iw_1.L29") [] [(Call CVoid (Global (a "zsys_futex_wait")) [(Arg P (t "v0")); (Arg W (Const 2)); (Arg W (Const 1))])] (JGoto (Poll (a "L10"))));
  (mkBlock (a "L12") [] [] JRetVoid)].

Definition hello_image_fn___GI___lll_lock_wake_private : func :=
  mkFunc (a "__GI___lll_lock_wake_private") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call CVoid (Global (a "zsys_futex_wake")) [(Arg P (t "v0")); (Arg W (Const 1)); (Arg W (Const 1))])] JRetVoid)].
