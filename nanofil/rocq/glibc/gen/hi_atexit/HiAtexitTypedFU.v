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

Definition hi_fn_glibc_libc_start'23futex_wake : func :=
  mkFunc (a "glibc_libc_start#futex_wake") (a "local") RVoid [(P, (a "v0")); (W, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v16") W (Cmp Eq W) [(t "v4"); (Const 0)])] (JBranch (t "v16") (To (a "L18")) (To (a "L17"))));
  (mkBlock (a "L17") [] [(Let (a "v20") W (Cmp Eq W) [(t "v4"); (Const 128)])] (JGoto (To (a "L18"))));
  (mkBlock (a "L18") [(Phi (a "v22") W [((a "start"), (Const 1)); ((a "L17"), (t "v20"))])] [] (JBranch (t "v22") (To (a "L11")) (To (a "L14"))));
  (mkBlock (a "L14") [] [(Let (a "v24") P Copy [(Global (a "glibc_libc_start#str.322"))]);
      (Let (a "v25") P Copy [(Global (a "glibc_libc_start#str.323"))]);
      (Let (a "v26") P Copy [(Global (a "glibc_libc_start#str.324"))]);
      (Let (a "v27") P Copy [(Global (a "glibc_libc_start#str.325"))]);
      (Call CVoid (Global (a "zerrorf")) [(Arg P (t "v24")); (Arg P (t "v25")); (Arg W (Const 173)); (Arg P (t "v26")); (Arg P (t "v27"))])] (JGoto (To (a "L11"))));
  (mkBlock (a "L11") [] [] (JBranch (t "v16") (To (a "L30")) (To (a "L29"))));
  (mkBlock (a "L29") [] [] (JGoto (To (a "L30"))));
  (mkBlock (a "L30") [(Phi (a "v33") W [((a "L29"), (Const 0)); ((a "L11"), (Const 1))])] [(Call CVoid (Global (a "zsys_futex_wake")) [(Arg P (t "v0")); (Arg W (t "v2")); (Arg W (t "v33"))])] JRetVoid)].
