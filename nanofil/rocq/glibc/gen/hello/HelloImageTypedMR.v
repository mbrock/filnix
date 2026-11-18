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

Definition hello_image_fn___GI___mremap : func :=
  mkFunc (a "__GI___mremap") (a "export") (RClass P) [(P, (a "v0")); (L, (a "v2")); (L, (a "v4")); (W, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v8") P (Alloc 8) [(Const 24)]);
      (Let (a "va_args") P VaArgs [(Const 32)]);
      (Let (a "v17") W And [(t "v6"); (Const 4294967288)])] (JBranch (t "v17") (To (a "L10")) (To (a "L12"))));
  (mkBlock (a "L10") [] [(Let (a "v18") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk0") A (Check 0 4 Write 1) [(t "v18")]);
      (RawStore Ww 0 (Const 22) (t "chk0"));
      (Flight (a "v21") Copy [(FValue (Const 18446744073709551615))] LowerNone)] (JRet (t "v21")));
  (mkBlock (a "L12") [] [(Let (a "v28") W And [(t "v6"); (Const 6)])] (JBranch (t "v28") (To (a "L23")) (To (a "L25"))));
  (mkBlock (a "L23") [] [(Let (a "chk1") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (t "va_args") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v29") P VaArg [(t "v8")])] (JGoto (To (a "L25"))));
  (mkBlock (a "L25") [(Phi (a "pr.1") P [((a "L23"), (t "v29")); ((a "L12"), (Const 0))])] [(Call (CResult (a "v35") P) (Global (a "zsys_mremap")) [(Arg P (t "v0")); (Arg L (t "v2")); (Arg L (t "v4")); (Arg W (t "v6")); (Arg P (t "pr.1"))])] (JRet (t "v35")))].
