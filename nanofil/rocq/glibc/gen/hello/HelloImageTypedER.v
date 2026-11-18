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

Definition hello_image_fn___GI___errno_location : func :=
  mkFunc (a "__GI___errno_location") (a "export") (RClass P) [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "__libc_errno"))])] (JRet (t "v0")))].

Definition hello_image_fn___error_internal : func :=
  mkFunc (a "__error_internal") (a "export") RVoid [(W, (a "v0")); (W, (a "v2")); (P, (a "v4")); (P, (a "v6")); (W, (a "v8"))] [(mkBlock (a "start") [] [(Let (a "v10") P (Alloc 4) [(Const 4)]);
      (Let (a "chk0") A (Check 0 4 Write 1) [(t "v10")]);
      (RawStore Ww 0 (Const 0) (t "chk0"));
      (Call (CResult (a "v11") W) (Global (a "__GI___pthread_setcancelstate")) [(Arg W (Const 1)); (Arg P (t "v10"))]);
      (Let (a "iw_1.v0") P Copy [(Global (a "stdout"))]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "iw_1.v0")]);
      (Let (a "iw_1.v1") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Call (CResult (a "iw_1.v2") W) (Global (a "__GI__IO_fflush")) [(Arg P (t "iw_1.v1"))]);
      (Let (a "v15") P Copy [(Global (a "error_print_progname"))]);
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v15")]);
      (Let (a "v16") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v17") L Ptoi [(t "v16")]);
      (Let (a "v18") W (Cmp Ne L) [(t "v17"); (Const 0)])] (JBranch (t "v18") (To (a "L12")) (To (a "L13"))));
  (mkBlock (a "L12") [] [(Let (a "v19") P Copy [(Global (a "error_print_progname"))]);
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v19")]);
      (Let (a "v20") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Let (a "chk4") F CheckFunction [(t "v20")]);
      (RawCall CVoid (t "chk4") [])] (JGoto (To (a "iw_2.start"))));
  (mkBlock (a "L13") [] [(Let (a "v21") P Copy [(Global (a "glibc_error#str.255"))]);
      (Let (a "v22") P Copy [(Global (a "program_invocation_name"))]);
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v22")]);
      (Let (a "v23") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Call (CResult (a "v24") W) (Global (a "__fxprintf")) [(Arg P (Const 0)); (Arg P (t "v21")); (Arg P (t "v23"))])] (JGoto (To (a "iw_2.start"))));
  (mkBlock (a "iw_2.start") [] [(Let (a "iw_2.v11") P Copy [(Global (a "stderr"))]);
      (Let (a "chk6") A (Check 0 8 Read 8) [(t "iw_2.v11")]);
      (Let (a "iw_2.v12") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Call (CResult (a "iw_2.v16") W) (Global (a "__vfxprintf")) [(Arg P (t "iw_2.v12")); (Arg P (t "v4")); (Arg P (t "v6")); (Arg W (t "v8"))]);
      (Let (a "iw_2.v21") W (Cmp Slt W) [(t "iw_2.v16"); (Const 0)])] (JBranch (t "iw_2.v21") (To (a "iw_2.L22")) (To (a "iw_2.L23"))));
  (mkBlock (a "iw_2.L22") [] [(Let (a "iw_2.v24") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk7") A (Check 0 4 Read 1) [(t "iw_2.v24")]);
      (Let (a "iw_2.v25") W (RawLoad (LdNarrow Sw) 0) [(t "chk7")]);
      (Let (a "iw_2.v26") W (Cmp Eq W) [(t "iw_2.v25"); (Const 12)])] (JGoto (To (a "iw_2.L23"))));
  (mkBlock (a "iw_2.L23") [(Phi (a "iw_2.v28") W [((a "iw_2.start"), (Const 0)); ((a "iw_2.L22"), (t "iw_2.v26"))])] [] (JBranch (t "iw_2.v28") (To (a "iw_2.L67")) (To (a "iw_2.L30"))));
  (mkBlock (a "iw_2.L67") [] [(Let (a "iw_2.v70") P Copy [(Global (a "stderr"))]);
      (Let (a "chk8") A (Check 0 8 Read 8) [(t "iw_2.v70")]);
      (Let (a "iw_2.v71") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Flight (a "iw_2.v72") Add [(FAddress (t "iw_2.v71")); (FValue (Const 192))] (LowerOf (t "iw_2.v71")));
      (Let (a "chk9") A (Check 0 4 Read 1) [(t "iw_2.v72")]);
      (Let (a "iw_2.v73") W (RawLoad (LdNarrow Sw) 0) [(t "chk9")]);
      (Let (a "iw_2.v80") W (Cmp Sgt W) [(t "iw_2.v73"); (Const 0)])] (JGoto (To (a "iw_2.L30"))));
  (mkBlock (a "iw_2.L30") [(Phi (a "iw_2.v82") W [((a "iw_2.L23"), (Const 0)); ((a "iw_2.L67"), (t "iw_2.v80"))])] [] (JBranch (t "iw_2.v82") (To (a "iw_2.L17")) (To (a "iw_2.L19"))));
  (mkBlock (a "iw_2.L17") [] [(Let (a "iw_2.v83") P Copy [(Global (a "glibc_error#str.253"))]);
      (Let (a "iw_2.v84") P Copy [(Global (a "stderr"))]);
      (Let (a "chk10") A (Check 0 8 Read 8) [(t "iw_2.v84")]);
      (Let (a "iw_2.v85") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")]);
      (Call (CResult (a "iw_2.v86") W) (Global (a "__GI_fputws_unlocked")) [(Arg P (t "iw_2.v83")); (Arg P (t "iw_2.v85"))])] (JGoto (To (a "iw_2.L19"))));
  (mkBlock (a "iw_2.L19") [] [(Let (a "iw_2.v87") P Copy [(Global (a "error_message_count"))]);
      (Let (a "chk11") A (Check 0 4 Read 1) [(t "iw_2.v87")]);
      (Let (a "iw_2.v88") W (RawLoad (LdNarrow Uw) 0) [(t "chk11")]);
      (Let (a "iw_2.v89") W Add [(t "iw_2.v88"); (Const 1)]);
      (Let (a "chk12") A (Renew 0 4 Write 1) [(t "chk11"); (t "iw_2.v87")]);
      (RawStore Ww 0 (t "iw_2.v89") (t "chk12"))] (JBranch (t "v2") (To (a "iw_2.iw_1.start")) (To (a "iw_2.L92"))));
  (mkBlock (a "iw_2.iw_1.start") [] [(Let (a "iw_2.iw_1.v3") P (Alloc 4) [(Const 1024)]);
      (Call (CResult (a "iw_2.iw_1.v5") P) (Global (a "__GI___strerror_r")) [(Arg W (t "v2")); (Arg P (t "iw_2.iw_1.v3")); (Arg L (Const 1024))]);
      (Let (a "iw_2.iw_1.v6") P Copy [(Global (a "glibc_error#str.252"))]);
      (Call (CResult (a "iw_2.iw_1.v8") W) (Global (a "__fxprintf")) [(Arg P (Const 0)); (Arg P (t "iw_2.iw_1.v6")); (Arg P (t "iw_2.iw_1.v5"))])] (JGoto (To (a "iw_2.L92"))));
  (mkBlock (a "iw_2.L92") [] [(Let (a "iw_2.v95") P Copy [(Global (a "glibc_error#str.254"))]);
      (Call (CResult (a "iw_2.v96") W) (Global (a "__fxprintf")) [(Arg P (Const 0)); (Arg P (t "iw_2.v95"))]);
      (Let (a "iw_2.v97") P Copy [(Global (a "stderr"))]);
      (Let (a "chk13") A (Check 0 8 Read 8) [(t "iw_2.v97")]);
      (Let (a "iw_2.v98") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk13")]);
      (Call (CResult (a "iw_2.v99") W) (Global (a "__GI__IO_fflush")) [(Arg P (t "iw_2.v98"))])] (JBranch (t "v0") (To (a "iw_2.L100")) (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.L100") [] [(Call CVoid (Global (a "__GI_exit")) [(Arg W (t "v0"))])] (JGoto (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.join") [] [(Let (a "chk14") A (Renew 0 4 Read 1) [(t "chk0"); (t "v10")]);
      (Let (a "v30") W (RawLoad (LdNarrow Sw) 0) [(t "chk14")]);
      (Call (CResult (a "v31") W) (Global (a "__GI___pthread_setcancelstate")) [(Arg W (t "v30")); (Arg P (Const 0))])] JRetVoid)].

Definition hello_image_fn___error : func :=
  mkFunc (a "__error") (a "export") RVoid [(W, (a "v0")); (W, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v6") P (Alloc 8) [(Const 24)]);
      (Let (a "va_args") P VaArgs [(Const 24)]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v6")]);
      (RawStorePointer 0 (t "va_args") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Call CVoid (Global (a "__error_internal")) [(Arg W (t "v0")); (Arg W (t "v2")); (Arg P (t "v4")); (Arg P (t "v6")); (Arg W (Const 0))])] JRetVoid)].

Definition hello_image_fn_glibc_libc_start'23errno_handler : func :=
  mkFunc (a "glibc_libc_start#errno_handler") (a "local") RVoid [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk0") A (Check 0 4 Write 1) [(t "v2")]);
      (RawStore Ww 0 (t "v0") (t "chk0"))] JRetVoid)].
