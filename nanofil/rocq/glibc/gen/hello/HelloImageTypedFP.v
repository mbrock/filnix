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

Definition hello_image_fn___fpending : func :=
  mkFunc (a "__fpending") (a "export") (RClass L) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v6") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v6")]);
      (Let (a "v7") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v8") W (Cmp Sgt W) [(t "v7"); (Const 0)])] (JBranch (t "v8") (To (a "L2")) (To (a "L3"))));
  (mkBlock (a "L2") [] [(Flight (a "v10") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v10")]);
      (Let (a "v11") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v12") Add [(FAddress (t "v11")); (FValue (Const 32))] (LowerOf (t "v11")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v12")]);
      (Let (a "v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v16") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v17") Add [(FAddress (t "v16")); (FValue (Const 24))] (LowerOf (t "v16")));
      (Let (a "chk4") A (Check 0 8 Read 8) [(t "v17")]);
      (Let (a "v18") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "v19") L Ptoi [(t "v13")]);
      (Let (a "v20") L Ptoi [(t "v18")]);
      (Let (a "v21") L Sub [(t "v19"); (t "v20")]);
      (Let (a "v22") L Div [(t "v21"); (Const 4)])] (JRet (t "v22")));
  (mkBlock (a "L3") [] [(Flight (a "v25") Add [(FAddress (t "v0")); (FValue (Const 40))] (LowerOf (t "v0")));
      (Let (a "chk5") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v25")]);
      (Let (a "v26") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v28") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk6") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v28")]);
      (Let (a "v29") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v30") L Ptoi [(t "v26")]);
      (Let (a "v31") L Ptoi [(t "v29")]);
      (Let (a "v32") L Sub [(t "v30"); (t "v31")])] (JRet (t "v32")))].

Definition hello_image_fn___fprintf : func :=
  mkFunc (a "__fprintf") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v4") P (Alloc 8) [(Const 24)]);
      (Let (a "va_args") P VaArgs [(Const 16)]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v4")]);
      (RawStorePointer 0 (t "va_args") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Call (CResult (a "v8") W) (Global (a "__vfprintf_internal")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg P (t "v4")); (Arg W (Const 0))])] (JRet (t "v8")))].

Definition hello_image_fn___GI_fputws_unlocked : func :=
  mkFunc (a "__GI_fputws_unlocked") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Call (CResult (a "v6") L) (Global (a "__wcslen")) [(Arg P (t "v0"))]);
      (Call (CResult (a "v57") W) (Global (a "_IO_fwide")) [(Arg P (t "v2")); (Arg W (Const 1))]);
      (Let (a "v59") W (Cmp Eq W) [(t "v57"); (Const 1)])] (JBranch (t "v59") (To (a "L60")) (To (a "L61"))));
  (mkBlock (a "L60") [] [(Flight (a "v63") Add [(FAddress (t "v2")); (FValue (Const 216))] (LowerOf (t "v2")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v63")]);
      (Let (a "v64") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "iw_1.v4") L Ptoi [(t "v64")]);
      (Let (a "iw_1.v7") P Copy [(Global (a "__io_vtables"))]);
      (Let (a "iw_1.v8") L Ptoi [(t "iw_1.v7")]);
      (Let (a "iw_1.v9") L Sub [(t "iw_1.v4"); (t "iw_1.v8")]);
      (Let (a "iw_1.v15") W (Cmp Uge L) [(t "iw_1.v9"); (Const 2352)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L10")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Call CVoid (Global (a "_IO_vtable_check")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v66") Add [(FAddress (t "v64")); (FValue (Const 56))] (LowerOf (t "v64")));
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v66")]);
      (Let (a "v67") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "chk2") F CheckFunction [(t "v67")]);
      (RawCall (CResult (a "v71") L) (t "chk2") [(Arg P (t "v2")); (Arg P (t "v0")); (Arg L (t "v6"))]);
      (Let (a "v73") W (Cmp Eq L) [(t "v71"); (t "v6")])] (JGoto (To (a "L61"))));
  (mkBlock (a "L61") [(Phi (a "v75") W [((a "start"), (Const 0)); ((a "iw_1.join"), (t "v73"))])] [] (JBranch (t "v75") (To (a "L14")) (To (a "L13"))));
  (mkBlock (a "L13") [] [] (JGoto (To (a "L14"))));
  (mkBlock (a "L14") [(Phi (a "pr.1") W [((a "L13"), (Const 4294967295)); ((a "L61"), (Const 1))])] [] (JRet (t "pr.1")))].
