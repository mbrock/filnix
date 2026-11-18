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

Definition hello_image_fn___GI___fortify_fail : func :=
  mkFunc (a "__GI___fortify_fail") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P Copy [(Global (a "glibc_fortify_fail#str.19"))]);
      (Let (a "v3") P Copy [(Global (a "glibc_fortify_fail#str.20"))]);
      (Call CVoid (Global (a "__libc_message_impl")) [(Arg P (t "v2")); (Arg P (t "v3")); (Arg P (t "v0"))])] JRetVoid)].

Definition hello_image_fn___fopen_maybe_mmap : func :=
  mkFunc (a "__fopen_maybe_mmap") (a "export") (RClass P) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v6") Add [(FAddress (t "v0")); (FValue (Const 116))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v6")]);
      (Let (a "v7") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v8") W Shl [(t "v7"); (Const 8)]);
      (Let (a "v9") W Sar [(t "v8"); (Const 8)]);
      (Let (a "v10") W And [(t "v9"); (Const 1)])] (JBranch (t "v10") (To (a "L11")) (To (a "L12"))));
  (mkBlock (a "L11") [] [(Let (a "chk1") A (HalfCheck Lower 0 4 Read 1) [(t "chk0"); (t "v0")]);
      (Let (a "v14") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")]);
      (Let (a "v15") W And [(t "v14"); (Const 8)]);
      (Let (a "v16") W (Cmp Ne W) [(t "v15"); (Const 0)])] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [(Phi (a "v17") W [((a "start"), (Const 0)); ((a "L11"), (t "v16"))])] [] (JBranch (t "v17") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [(Flight (a "v22") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk2") A (HalfCheck Upper 0 4 Read 1) [(t "chk0"); (t "v22")]);
      (Let (a "v23") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v24") W (Cmp Sle W) [(t "v23"); (Const 0)])] (JBranch (t "v24") (To (a "L18")) (To (a "L19"))));
  (mkBlock (a "L18") [] [(Flight (a "v26") Add [(FAddress (t "v0")); (FValue (Const 216))] (LowerOf (t "v0")));
      (Let (a "v27") P Copy [(Global (a "__io_vtables"))]);
      (Flight (a "v28") Add [(FAddress (t "v27")); (FValue (Const 672))] (LowerOf (t "v27")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v26")]);
      (RawStorePointer 0 (t "v28") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L20"))));
  (mkBlock (a "L19") [] [(Flight (a "v30") Add [(FAddress (t "v0")); (FValue (Const 216))] (LowerOf (t "v0")));
      (Let (a "v31") P Copy [(Global (a "__io_vtables"))]);
      (Flight (a "v32") Add [(FAddress (t "v31")); (FValue (Const 1176))] (LowerOf (t "v31")));
      (Let (a "chk4") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v30")]);
      (RawStorePointer 0 (t "v32") (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L20"))));
  (mkBlock (a "L20") [] [(Flight (a "v34") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "chk5") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v34")]);
      (Let (a "v35") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v36") Add [(FAddress (t "v35")); (FValue (Const 224))] (LowerOf (t "v35")));
      (Let (a "v37") P Copy [(Global (a "__io_vtables"))]);
      (Flight (a "v38") Add [(FAddress (t "v37")); (FValue (Const 1176))] (LowerOf (t "v37")));
      (Let (a "chk6") A (Check 0 8 Write 8) [(t "v36")]);
      (RawStorePointer 0 (t "v38") (t "chk6") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L4"))));
  (mkBlock (a "L4") [] [] (JRet (t "v0")))].

Definition hello_image_fn___fopen_internal : func :=
  mkFunc (a "__fopen_internal") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [(Call (CResult (a "v7") P) (Global (a "malloc")) [(Arg L (Const 472))]);
      (Let (a "v12") L Ptoi [(t "v7")]);
      (Let (a "v13") L Ptoi [(Const 0)]);
      (Let (a "v14") W (Cmp Eq L) [(t "v12"); (t "v13")])] (JBranch (t "v14") (To (a "L8")) (To (a "L10"))));
  (mkBlock (a "L8") [] [] (JRet (Const 0)));
  (mkBlock (a "L10") [] [(Flight (a "v17") Add [(FAddress (t "v7")); (FValue (Const 136))] (LowerOf (t "v7")));
      (Flight (a "v19") Add [(FAddress (t "v7")); (FValue (Const 224))] (LowerOf (t "v7")));
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v17")]);
      (RawStorePointer 0 (t "v19") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v22") Add [(FAddress (t "v7")); (FValue (Const 240))] (LowerOf (t "v7")));
      (Let (a "v23") P Copy [(Global (a "__io_vtables"))]);
      (Flight (a "v24") Add [(FAddress (t "v23")); (FValue (Const 840))] (LowerOf (t "v23")));
      (Call CVoid (Global (a "_IO_no_init")) [(Arg P (t "v7")); (Arg W (Const 0)); (Arg W (Const 0)); (Arg P (t "v22")); (Arg P (t "v24"))]);
      (Flight (a "v26") Add [(FAddress (t "v7")); (FValue (Const 216))] (LowerOf (t "v7")));
      (Let (a "v27") P Copy [(Global (a "__io_vtables"))]);
      (Flight (a "v28") Add [(FAddress (t "v27")); (FValue (Const 336))] (LowerOf (t "v27")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v26")]);
      (RawStorePointer 0 (t "v28") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Call CVoid (Global (a "_IO_new_file_init_internal")) [(Arg P (t "v7"))]);
      (Call (CResult (a "v37") P) (Global (a "__GI__IO_file_fopen")) [(Arg P (t "v7")); (Arg P (t "v0")); (Arg P (t "v2")); (Arg W (t "v4"))]);
      (Let (a "v38") L Ptoi [(t "v37")]);
      (Let (a "v40") W (Cmp Ne L) [(t "v38"); (t "v13")])] (JBranch (t "v40") (To (a "L30")) (To (a "L32"))));
  (mkBlock (a "L30") [] [(Call (CResult (a "v42") P) (Global (a "__fopen_maybe_mmap")) [(Arg P (t "v7"))])] (JRet (t "v42")));
  (mkBlock (a "L32") [] [(Call CVoid (Global (a "__GI__IO_un_link")) [(Arg P (t "v7"))]);
      (Call CVoid (Global (a "free")) [(Arg P (t "v7"))])] (JRet (Const 0)))].
