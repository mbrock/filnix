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

Definition hello_image_fn___opendir : func :=
  mkFunc (a "__opendir") (a "export") (RClass P) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 1 Read 1) [(t "v0")]);
      (Let (a "iw_1.v7") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "iw_1.v8") W (Cmp Eq W) [(t "iw_1.v7"); (Const 0)])] (JBranch (t "iw_1.v8") (To (a "iw_1.L2")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L2") [] [(Let (a "iw_1.v11") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk1") A (Check 0 4 Write 1) [(t "iw_1.v11")]);
      (RawStore Ww 0 (Const 2) (t "chk1"))] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [(Phi (a "v6") W [((a "iw_1.L2"), (Const 1)); ((a "start"), (Const 0))])] [] (JBranch (t "v6") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [] (JRet (Const 0)));
  (mkBlock (a "L4") [] [(Call (CResult (a "v12") W) (Global (a "__GI___open_nocancel")) [(Arg P (t "v0")); (Arg W (Const 591872))]);
      (Let (a "iw_2.v10") P (Alloc 8) [(Const 144)]);
      (Let (a "iw_2.v6") W (Cmp Slt W) [(t "v12"); (Const 0)])] (JBranch (t "iw_2.v6") (To (a "iw_2.join")) (To (a "iw_2.L4"))));
  (mkBlock (a "iw_2.L4") [] [(Call (CResult (a "iw_2.v15") W) (Global (a "__GI___fstat64")) [(Arg W (t "v12")); (Arg P (t "iw_2.v10"))]);
      (Let (a "iw_2.v16") W (Cmp Slt W) [(t "iw_2.v15"); (Const 0)])] (JBranch (t "iw_2.v16") (To (a "iw_2.L19")) (To (a "iw_2.L13"))));
  (mkBlock (a "iw_2.L13") [] [(Flight (a "iw_2.v24") Add [(FAddress (t "iw_2.v10")); (FValue (Const 24))] (LowerOf (t "iw_2.v10")));
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "iw_2.v24")]);
      (Let (a "iw_2.v25") W (RawLoad (LdNarrow Uw) 0) [(t "chk2")]);
      (Let (a "iw_2.v26") W And [(t "iw_2.v25"); (Const 61440)]);
      (Let (a "iw_2.v28") W (Cmp Ne W) [(t "iw_2.v26"); (Const 16384)])] (JBranch (t "iw_2.v28") (To (a "iw_2.L21")) (To (a "iw_2.L23"))));
  (mkBlock (a "iw_2.L21") [] [(Let (a "iw_2.v31") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk3") A (Check 0 4 Write 1) [(t "iw_2.v31")]);
      (RawStore Ww 0 (Const 20) (t "chk3"))] (JGoto (To (a "iw_2.L19"))));
  (mkBlock (a "iw_2.L19") [] [(Call CVoid (Global (a "__GI___close_nocancel_nostatus")) [(Arg W (t "v12"))])] (JGoto (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.L23") [] [(Call (CResult (a "iw_2.v36") P) (Global (a "__alloc_dir")) [(Arg W (t "v12")); (Arg W (Const 1)); (Arg W (Const 0)); (Arg P (t "iw_2.v10"))])] (JGoto (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.join") [(Phi (a "v13") P [((a "iw_2.L19"), (Const 0)); ((a "iw_2.L23"), (t "iw_2.v36")); ((a "L4"), (Const 0))])] [] (JRet (t "v13")))].

Definition hello_image_fn___GI___open64_nocancel : func :=
  mkFunc (a "__GI___open64_nocancel") (a "export") (RClass W) [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "va_args") P VaArgs [(Const 16)]);
      (Let (a "v4") P Copy [(Global (a "zsys_open"))]);
      (Let (a "v5") P VaArgs [(Const 0)]);
      (Call (CResult (a "v6") P) (Global (a "zcall")) [(Arg P (t "v4")); (Arg P (t "v5"))]);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v6")]);
      (Let (a "v7") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")])] (JRet (t "v7")))].
