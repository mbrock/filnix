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

Definition hello_image_fn___libc_assert_fail : func :=
  mkFunc (a "__libc_assert_fail") (a "export") RVoid [(P, (a "v0")); (P, (a "v2")); (W, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v8") P (Alloc 4) [(Const 11)]);
      (Flight (a "v12") Add [(FAddress (t "v8")); (FValue (Const 11))] (LowerOf (t "v8")));
      (Flight (a "v15") Add [(FAddress (t "v12")); (FValue (Const 18446744073709551615))] (LowerOf (t "v12")));
      (Let (a "chk0") A (Check 0 1 Write 1) [(t "v15")]);
      (RawStore Wb 0 (Const 0) (t "chk0"));
      (Let (a "v18") L (Ext Uw) [(t "v4")]);
      (Flight (a "v23") Sub [(FAddress (t "v12")); (FValue (Const 1))] (LowerOf (t "v12")));
      (Call (CResult (a "v24") P) (Global (a "_itoa_word")) [(Arg L (t "v18")); (Arg P (t "v23")); (Arg W (Const 10)); (Arg W (Const 0))]);
      (Let (a "v25") P Copy [(Global (a "glibc___libc_assert_fail#str.21"))]);
      (Let (a "v26") P Copy [(Global (a "glibc___libc_assert_fail#str.22"))]);
      (Call CVoid (Global (a "__libc_message_impl")) [(Arg P (t "v25")); (Arg P (t "v26")); (Arg P (t "v2")); (Arg P (t "v24")); (Arg P (t "v6")); (Arg P (t "v0"))])] JRetVoid)].

Definition hello_image_fn___libc_dlopen_mode : func :=
  mkFunc (a "__libc_dlopen_mode") (a "export") (RClass P) [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Call (CResult (a "v6") P) (Global (a "zsys_dlopen")) [(Arg P (t "v0")); (Arg W (t "v2"))])] (JRet (t "v6")))].

Definition hello_image_fn___libc_dlsym : func :=
  mkFunc (a "__libc_dlsym") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Call (CResult (a "v6") P) (Global (a "zsys_dlsym")) [(Arg P (t "v0")); (Arg P (t "v2"))])] (JRet (t "v6")))].

Definition hello_image_fn___libc_dlclose : func :=
  mkFunc (a "__libc_dlclose") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [] (JRet (Const 0)))].

Definition hello_image_fn___libc_open64 : func :=
  mkFunc (a "__libc_open64") (a "export") (RClass W) [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "va_args") P VaArgs [(Const 16)]);
      (Let (a "v4") P Copy [(Global (a "zsys_open"))]);
      (Let (a "v5") P VaArgs [(Const 0)]);
      (Call (CResult (a "v6") P) (Global (a "zcall")) [(Arg P (t "v4")); (Arg P (t "v5"))]);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v6")]);
      (Let (a "v7") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")])] (JRet (t "v7")))].

Definition hello_image_fn___GI___libc_read : func :=
  mkFunc (a "__GI___libc_read") (a "export") (RClass L) [(W, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Call (CResult (a "v9") L) (Global (a "zsys_read")) [(Arg W (t "v0")); (Arg P (t "v2")); (Arg L (t "v4"))])] (JRet (t "v9")))].

Definition hello_image_fn___GI___libc_write : func :=
  mkFunc (a "__GI___libc_write") (a "export") (RClass L) [(W, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Call (CResult (a "v9") L) (Global (a "zsys_write")) [(Arg W (t "v0")); (Arg P (t "v2")); (Arg L (t "v4"))])] (JRet (t "v9")))].

Definition hello_image_fn___libio_codecvt_out : func :=
  mkFunc (a "__libio_codecvt_out") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6")); (P, (a "v8")); (P, (a "v10")); (P, (a "v12")); (P, (a "v14"))] [(mkBlock (a "start") [] [(Let (a "v22") P (Alloc 8) [(Const 8)]);
      (Let (a "v23") P (Alloc 8) [(Const 8)]);
      (Flight (a "v19") Add [(FAddress (t "v0")); (FValue (Const 56))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v19")]);
      (Let (a "v20") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Write 8) [(t "v23")]);
      (RawStorePointer 0 (t "v4") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v27") Add [(FAddress (t "v19")); (FValue (Const 8))] (LowerOf (t "v19")));
      (Let (a "chk2") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v27")]);
      (RawStorePointer 0 (t "v10") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v32") Add [(FAddress (t "v27")); (FValue (Const 8))] (LowerOf (t "v27")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Write 8) [(t "chk2"); (t "v32")]);
      (RawStorePointer 0 (t "v12") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v37") Add [(FAddress (t "v27")); (FValue (Const 32))] (LowerOf (t "v27")));
      (Let (a "chk4") A (HalfCheck Upper 0 8 Write 8) [(t "chk2"); (t "v37")]);
      (RawStorePointer 0 (t "v2") (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v41") Add [(FAddress (t "v20")); (FValue (Const 40))] (LowerOf (t "v20")));
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v41")]);
      (Let (a "v42") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk6") A (HalfCheck Lower 0 8 Read 8) [(t "chk5"); (t "v20")]);
      (Let (a "v47") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v48") L Ptoi [(t "v47")]);
      (Let (a "v49") L Ptoi [(Const 0)]);
      (Let (a "v50") W (Cmp Ne L) [(t "v48"); (t "v49")])] (JBranch (t "v50") (To (a "iw_1.join")) (To (a "L44"))));
  (mkBlock (a "L44") [] [] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v56") Add [(FAddress (t "v0")); (FValue (Const 56))] (LowerOf (t "v0")));
      (Flight (a "v57") Add [(FAddress (t "v56")); (FValue (Const 8))] (LowerOf (t "v56")));
      (Let (a "chk7") F CheckFunction [(t "v42")]);
      (RawCall (CResult (a "v59") W) (t "chk7") [(Arg P (t "v20")); (Arg P (t "v57")); (Arg P (t "v23")); (Arg P (t "v6")); (Arg P (Const 0)); (Arg P (t "v22")); (Arg W (Const 0)); (Arg W (Const 0))]);
      (Let (a "chk8") A (Renew 0 8 Read 8) [(t "chk1"); (t "v23")]);
      (Let (a "v61") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk9") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (t "v61") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk10") A (Renew 0 8 Read 8) [(t "chk2"); (t "v57")]);
      (Let (a "v66") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")]);
      (Let (a "chk11") A (Check 0 8 Write 8) [(t "v14")]);
      (RawStorePointer 0 (t "v66") (t "chk11") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v76") W (Cmp Eq W) [(t "v59"); (Const 0)])] (JBranch (t "v76") (To (a "L69")) (To (a "L77"))));
  (mkBlock (a "L77") [] [(Let (a "v78") W (Cmp Eq W) [(t "v59"); (Const 4)])] (JBranch (t "v78") (To (a "L69")) (To (a "L79"))));
  (mkBlock (a "L79") [] [(Let (a "v80") W (Cmp Eq W) [(t "v59"); (Const 5)])] (JBranch (t "v80") (To (a "L69")) (To (a "L81"))));
  (mkBlock (a "L81") [] [(Let (a "v82") W (Cmp Eq W) [(t "v59"); (Const 7)])] (JBranch (t "v82") (To (a "L69")) (To (a "L83"))));
  (mkBlock (a "L83") [] [] (JGoto (To (a "L69"))));
  (mkBlock (a "L69") [(Phi (a "pr.1") W [((a "L77"), (Const 0)); ((a "iw_1.join"), (Const 0)); ((a "L81"), (Const 1)); ((a "L79"), (Const 1)); ((a "L83"), (Const 2))])] [] (JRet (t "pr.1")))].

Definition hello_image_fn___libio_codecvt_in : func :=
  mkFunc (a "__libio_codecvt_in") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6")); (P, (a "v8")); (P, (a "v10")); (P, (a "v12")); (P, (a "v14"))] [(mkBlock (a "start") [] [(Let (a "v21") P (Alloc 8) [(Const 8)]);
      (Let (a "v22") P (Alloc 8) [(Const 8)]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v19") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Write 8) [(t "v22")]);
      (RawStorePointer 0 (t "v4") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v25") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk2") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v25")]);
      (RawStorePointer 0 (t "v10") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v29") Add [(FAddress (t "v25")); (FValue (Const 8))] (LowerOf (t "v25")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Write 8) [(t "chk2"); (t "v29")]);
      (RawStorePointer 0 (t "v12") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v33") Add [(FAddress (t "v25")); (FValue (Const 32))] (LowerOf (t "v25")));
      (Let (a "chk4") A (HalfCheck Upper 0 8 Write 8) [(t "chk2"); (t "v33")]);
      (RawStorePointer 0 (t "v2") (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v37") Add [(FAddress (t "v19")); (FValue (Const 40))] (LowerOf (t "v19")));
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v37")]);
      (Let (a "v38") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk6") A (HalfCheck Lower 0 8 Read 8) [(t "chk5"); (t "v19")]);
      (Let (a "v43") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v44") L Ptoi [(t "v43")]);
      (Let (a "v45") L Ptoi [(Const 0)]);
      (Let (a "v46") W (Cmp Ne L) [(t "v44"); (t "v45")])] (JBranch (t "v46") (To (a "iw_1.join")) (To (a "L40"))));
  (mkBlock (a "L40") [] [] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v52") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk7") F CheckFunction [(t "v38")]);
      (RawCall (CResult (a "v54") W) (t "chk7") [(Arg P (t "v19")); (Arg P (t "v52")); (Arg P (t "v22")); (Arg P (t "v6")); (Arg P (Const 0)); (Arg P (t "v21")); (Arg W (Const 0)); (Arg W (Const 0))]);
      (Let (a "chk8") A (Renew 0 8 Read 8) [(t "chk1"); (t "v22")]);
      (Let (a "v56") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk9") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (t "v56") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk10") A (Renew 0 8 Read 8) [(t "chk2"); (t "v52")]);
      (Let (a "v60") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")]);
      (Let (a "chk11") A (Check 0 8 Write 8) [(t "v14")]);
      (RawStorePointer 0 (t "v60") (t "chk11") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v70") W (Cmp Eq W) [(t "v54"); (Const 0)])] (JBranch (t "v70") (To (a "L63")) (To (a "L71"))));
  (mkBlock (a "L71") [] [(Let (a "v72") W (Cmp Eq W) [(t "v54"); (Const 4)])] (JBranch (t "v72") (To (a "L63")) (To (a "L73"))));
  (mkBlock (a "L73") [] [(Let (a "v74") W (Cmp Eq W) [(t "v54"); (Const 5)])] (JBranch (t "v74") (To (a "L63")) (To (a "L75"))));
  (mkBlock (a "L75") [] [(Let (a "v76") W (Cmp Eq W) [(t "v54"); (Const 7)])] (JBranch (t "v76") (To (a "L63")) (To (a "L77"))));
  (mkBlock (a "L77") [] [] (JGoto (To (a "L63"))));
  (mkBlock (a "L63") [(Phi (a "pr.1") W [((a "L71"), (Const 0)); ((a "iw_1.join"), (Const 0)); ((a "L75"), (Const 1)); ((a "L73"), (Const 1)); ((a "L77"), (Const 2))])] [] (JRet (t "pr.1")))].

Definition hello_image_fn___libio_codecvt_encoding : func :=
  mkFunc (a "__libio_codecvt_encoding") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v6") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v7") Add [(FAddress (t "v6")); (FValue (Const 88))] (LowerOf (t "v6")));
      (Let (a "chk1") A (Check 0 4 Read 1) [(t "v7")]);
      (Let (a "v8") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")])] (JBranch (t "v8") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L4") [] [(Let (a "v15") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v16") Add [(FAddress (t "v15")); (FValue (Const 72))] (LowerOf (t "v15")));
      (Let (a "chk3") A (Check 0 4 Read 1) [(t "v16")]);
      (Let (a "v17") W (RawLoad (LdNarrow Sw) 0) [(t "chk3")]);
      (Let (a "v19") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v20") Add [(FAddress (t "v19")); (FValue (Const 76))] (LowerOf (t "v19")));
      (Let (a "chk5") A (Check 0 4 Read 1) [(t "v20")]);
      (Let (a "v21") W (RawLoad (LdNarrow Sw) 0) [(t "chk5")]);
      (Let (a "v22") W (Cmp Ne W) [(t "v17"); (t "v21")])] (JBranch (t "v22") (To (a "L11")) (To (a "L13"))));
  (mkBlock (a "L11") [] [] (JRet (Const 0)));
  (mkBlock (a "L13") [] [(Let (a "v25") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v26") Add [(FAddress (t "v25")); (FValue (Const 72))] (LowerOf (t "v25")));
      (Let (a "chk7") A (Check 0 4 Read 1) [(t "v26")]);
      (Let (a "v27") W (RawLoad (LdNarrow Sw) 0) [(t "chk7")])] (JRet (t "v27")))].

Definition hello_image_fn___libio_codecvt_length : func :=
  mkFunc (a "__libio_codecvt_length") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6")); (L, (a "v8"))] [(mkBlock (a "start") [] [(Let (a "v11") P (Alloc 8) [(Const 8)]);
      (Let (a "v19") P (Alloc 8) [(Const 8)]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v11")]);
      (RawStorePointer 0 (t "v4") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v14") L Shl [(t "v8"); (Const 2)]);
      (Let (a "v15") P (Alloc 4) [(t "v14")]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v18") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v21") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk2") A (HalfCheck Upper 0 8 Write 8) [(t "chk1"); (t "v21")]);
      (RawStorePointer 0 (t "v15") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v24") Add [(FAddress (t "v21")); (FValue (Const 8))] (LowerOf (t "v21")));
      (Flight (a "v27") Add [(FAddress (t "v15")); (FValue (t "v14"))] (LowerOf (t "v15")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Write 8) [(t "chk2"); (t "v24")]);
      (RawStorePointer 0 (t "v27") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v30") Add [(FAddress (t "v21")); (FValue (Const 32))] (LowerOf (t "v21")));
      (Let (a "chk4") A (HalfCheck Upper 0 8 Write 8) [(t "chk2"); (t "v30")]);
      (RawStorePointer 0 (t "v2") (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v34") Add [(FAddress (t "v18")); (FValue (Const 40))] (LowerOf (t "v18")));
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v34")]);
      (Let (a "v35") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk6") A (HalfCheck Lower 0 8 Read 8) [(t "chk5"); (t "v18")]);
      (Let (a "v40") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v41") L Ptoi [(t "v40")]);
      (Let (a "v42") L Ptoi [(Const 0)]);
      (Let (a "v43") W (Cmp Ne L) [(t "v41"); (t "v42")])] (JBranch (t "v43") (To (a "iw_1.join")) (To (a "L37"))));
  (mkBlock (a "L37") [] [] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v49") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk7") F CheckFunction [(t "v35")]);
      (RawCall (CResult (a "v51") W) (t "chk7") [(Arg P (t "v18")); (Arg P (t "v49")); (Arg P (t "v11")); (Arg P (t "v6")); (Arg P (Const 0)); (Arg P (t "v19")); (Arg W (Const 0)); (Arg W (Const 0))]);
      (Let (a "chk8") A (Renew 0 8 Read 8) [(t "chk0"); (t "v11")]);
      (Let (a "v52") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "v54") L Ptoi [(t "v52")]);
      (Let (a "v55") L Ptoi [(t "v4")]);
      (Let (a "v56") L Sub [(t "v54"); (t "v55")]);
      (Let (a "v57") W Copy [(t "v56")])] (JRet (t "v57")))].

Definition hello_image_fn___libc_message_impl : func :=
  mkFunc (a "__libc_message_impl") (a "export") RVoid [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v4") P (Alloc 8) [(Const 24)]);
      (Let (a "v13") P (Alloc 8) [(Const 240)]);
      (Let (a "va_args") P VaArgs [(Const 16)]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v4")]);
      (RawStorePointer 0 (t "va_args") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L18"))));
  (mkBlock (a "L18") [(Phi (a "pr.8") P [((a "start"), (t "v2")); ((a "L56"), (t "pr.9"))]); (Phi (a "pr.4") L [((a "start"), (Const 0)); ((a "L56"), (t "v94"))]); (Phi (a "pr.2") W [((a "start"), (Const 0)); ((a "L56"), (t "v96"))])] [(Let (a "chk1") A (Check 0 1 Read 1) [(t "pr.8")]);
      (Let (a "v22") W (RawLoad (LdNarrow Sb) 0) [(t "chk1")]);
      (Let (a "v23") W (Cmp Ne W) [(t "v22"); (Const 0)])] (JBranch (t "v23") (To (a "L26")) (To (a "L20"))));
  (mkBlock (a "L26") [(Phi (a "pr.10") P [((a "L18"), (t "pr.8")); ((a "L27"), (t "v43"))])] [(Let (a "chk2") A (Check 0 1 Read 1) [(t "pr.10")]);
      (Let (a "v31") W (RawLoad (LdNarrow Sb) 0) [(t "chk2")]);
      (Let (a "v32") W (Cmp Ne W) [(t "v31"); (Const 37)])] (JBranch (t "v32") (To (a "L34")) (To (a "L33"))));
  (mkBlock (a "L33") [] [(Flight (a "v36") Add [(FAddress (t "pr.10")); (FValue (Const 1))] (LowerOf (t "pr.10")));
      (Let (a "chk3") A (HalfCheck Upper 0 1 Read 1) [(t "chk2"); (t "v36")]);
      (Let (a "v37") W (RawLoad (LdNarrow Sb) 0) [(t "chk3")]);
      (Let (a "v38") W (Cmp Ne W) [(t "v37"); (Const 115)])] (JGoto (To (a "L34"))));
  (mkBlock (a "L34") [(Phi (a "v40") W [((a "L26"), (Const 1)); ((a "L33"), (t "v38"))])] [] (JBranch (t "v40") (To (a "L27")) (To (a "L28"))));
  (mkBlock (a "L27") [] [(Flight (a "v42") Add [(FAddress (t "pr.10")); (FValue (Const 1))] (LowerOf (t "pr.10")));
      (Call (CResult (a "v43") P) (Global (a "__GI___strchrnul")) [(Arg P (t "v42")); (Arg W (Const 37))]);
      (Let (a "chk4") A (Check 0 1 Read 1) [(t "v43")]);
      (Let (a "v49") W (RawLoad (LdNarrow Sb) 0) [(t "chk4")]);
      (Let (a "v50") W (Cmp Eq W) [(t "v49"); (Const 0)])] (JBranch (t "v50") (To (a "L28")) (Poll (a "L26"))));
  (mkBlock (a "L28") [(Phi (a "pr.11") P [((a "L34"), (t "pr.10")); ((a "L27"), (t "v43"))])] [(Let (a "chk5") A (Renew 0 1 Read 1) [(t "chk1"); (t "pr.8")]);
      (Let (a "v59") W (RawLoad (LdNarrow Sb) 0) [(t "chk5")]);
      (Let (a "v60") W (Cmp Eq W) [(t "v59"); (Const 37)])] (JBranch (t "v60") (To (a "L61")) (To (a "L62"))));
  (mkBlock (a "L61") [] [(Flight (a "v64") Add [(FAddress (t "pr.8")); (FValue (Const 1))] (LowerOf (t "pr.8")));
      (Let (a "chk6") A (HalfCheck Upper 0 1 Read 1) [(t "chk1"); (t "v64")]);
      (Let (a "v65") W (RawLoad (LdNarrow Sb) 0) [(t "chk6")]);
      (Let (a "v66") W (Cmp Eq W) [(t "v65"); (Const 115)])] (JGoto (To (a "L62"))));
  (mkBlock (a "L62") [(Phi (a "v68") W [((a "L28"), (Const 0)); ((a "L61"), (t "v66"))])] [] (JBranch (t "v68") (To (a "L54")) (To (a "L55"))));
  (mkBlock (a "L54") [] [(Let (a "v69") P VaArg [(t "v4")]);
      (Call (CResult (a "v71") L) (Global (a "__GI_strlen")) [(Arg P (t "v69"))]);
      (Flight (a "v73") Add [(FAddress (t "pr.8")); (FValue (Const 2))] (LowerOf (t "pr.8")))] (JGoto (To (a "L56"))));
  (mkBlock (a "L55") [] [(Let (a "v77") L Ptoi [(t "pr.11")]);
      (Let (a "v78") L Ptoi [(t "pr.8")]);
      (Let (a "v79") L Sub [(t "v77"); (t "v78")])] (JGoto (To (a "L56"))));
  (mkBlock (a "L56") [(Phi (a "pr.13") L [((a "L54"), (t "v71")); ((a "L55"), (t "v79"))]); (Phi (a "pr.12") P [((a "L54"), (t "v69")); ((a "L55"), (t "pr.8"))]); (Phi (a "pr.9") P [((a "L54"), (t "v73")); ((a "L55"), (t "pr.11"))])] [(Let (a "v82") L (Ext Sw) [(t "pr.2")]);
      (Let (a "v83") L Shl [(t "v82"); (Const 4)]);
      (Flight (a "v84") Add [(FAddress (t "v13")); (FValue (t "v83"))] (LowerOf (t "v13")));
      (Let (a "chk7") A (Check 0 8 Write 8) [(t "v84")]);
      (RawStorePointer 0 (t "pr.12") (t "chk7") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v90") Add [(FAddress (t "v84")); (FValue (Const 8))] (LowerOf (t "v84")));
      (Let (a "chk8") A (HalfCheck Upper 0 8 Write 1) [(t "chk7"); (t "v90")]);
      (RawStore Wl 0 (t "pr.13") (t "chk8"));
      (Let (a "v94") L Add [(t "pr.4"); (t "pr.13")]);
      (Let (a "v96") W Add [(t "pr.2"); (Const 1)]);
      (Let (a "v103") W (Cmp Sgt W) [(t "v96"); (Const 15)])] (JBranch (t "v103") (To (a "L97")) (Poll (a "L18"))));
  (mkBlock (a "L97") [] [(Let (a "v108") P Copy [(Global (a "glibc_libc_fatal#str.298"))]);
      (Let (a "chk9") A (Check 0 8 Write 8) [(t "v13")]);
      (RawStorePointer 0 (t "v108") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v110") Add [(FAddress (t "v13")); (FValue (Const 8))] (LowerOf (t "v13")));
      (Let (a "chk10") A (HalfCheck Upper 0 8 Write 1) [(t "chk9"); (t "v110")]);
      (RawStore Wl 0 (Const 70) (t "chk10"))] (JGoto (To (a "L20"))));
  (mkBlock (a "L20") [(Phi (a "pr.5") L [((a "L18"), (t "pr.4")); ((a "L97"), (Const 70))]); (Phi (a "pr.3") W [((a "L18"), (t "pr.2")); ((a "L97"), (Const 1))])] [(Let (a "v118") W (Cmp Sgt W) [(t "pr.3"); (Const 0)])] (JBranch (t "v118") (To (a "L114")) (To (a "L116"))));
  (mkBlock (a "L114") [] [(Let (a "v121") L (Ext Sw) [(t "pr.3")])] (JGoto (To (a "iw_1.L9"))));
  (mkBlock (a "iw_1.L9") [] [(Call (CResult (a "iw_1.v15") L) (Global (a "zsys_writev")) [(Arg W (Const 2)); (Arg P (t "v13")); (Arg W (t "v121"))]);
      (Let (a "iw_1.v17") W (Cmp Slt L) [(t "iw_1.v15"); (Const 0)])] (JBranch (t "iw_1.v17") (To (a "iw_1.L18")) (To (a "iw_1.L19"))));
  (mkBlock (a "iw_1.L18") [] [(Let (a "iw_1.v20") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk11") A (Check 0 4 Read 1) [(t "iw_1.v20")]);
      (Let (a "iw_1.v21") W (RawLoad (LdNarrow Sw) 0) [(t "chk11")]);
      (Let (a "iw_1.v22") W (Cmp Eq W) [(t "iw_1.v21"); (Const 4)])] (JGoto (To (a "iw_1.L19"))));
  (mkBlock (a "iw_1.L19") [(Phi (a "iw_1.v24") W [((a "iw_1.L9"), (Const 0)); ((a "iw_1.L18"), (t "iw_1.v22"))])] [] (JBranch (t "iw_1.v24") (Poll (a "iw_1.L9")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Let (a "v126") L Add [(t "pr.5"); (Const 4)]);
      (Let (a "v127") L Add [(t "v126"); (Const 1)]);
      (Let (a "v128") P Copy [(Global (a "_dl_pagesize"))]);
      (Let (a "chk12") A (Check 0 8 Read 1) [(t "v128")]);
      (Let (a "v129") L (RawLoad LdL 0) [(t "chk12")]);
      (Let (a "v130") L Add [(t "v127"); (t "v129")]);
      (Let (a "v131") L Sub [(t "v130"); (Const 1)]);
      (Let (a "v132") P Copy [(Global (a "_dl_pagesize"))]);
      (Let (a "chk13") A (Check 0 8 Read 1) [(t "v132")]);
      (Let (a "v133") L (RawLoad LdL 0) [(t "chk13")]);
      (Let (a "v134") L Neg [(t "v133")]);
      (Let (a "v135") L And [(t "v131"); (t "v134")]);
      (Call (CResult (a "v141") P) (Global (a "__GI___mmap")) [(Arg P (Const 0)); (Arg L (t "v135")); (Arg W (Const 3)); (Arg W (Const 34)); (Arg W (Const 4294967295)); (Arg L (Const 0))]);
      (Flight (a "v148") Copy [(FValue (Const 18446744073709551615))] LowerNone);
      (Let (a "v149") L Ptoi [(t "v141")]);
      (Let (a "v150") L Ptoi [(t "v148")]);
      (Let (a "v151") W (Cmp Ne L) [(t "v149"); (t "v150")])] (JBranch (t "v151") (To (a "L142")) (To (a "L116"))));
  (mkBlock (a "L142") [] [(Let (a "chk14") A (Check 0 4 Write 1) [(t "v141")]);
      (RawStore Ww 0 (t "v135") (t "chk14"));
      (Flight (a "v158") Add [(FAddress (t "v141")); (FValue (Const 4))] (LowerOf (t "v141")))] (JGoto (To (a "L160"))));
  (mkBlock (a "L160") [(Phi (a "pr.15") W [((a "L142"), (Const 0)); ((a "L161"), (t "v181"))]); (Phi (a "pr.14") P [((a "L142"), (t "v158")); ((a "L161"), (t "v179"))])] [(Let (a "v166") W (Cmp Slt W) [(t "pr.15"); (t "pr.3")])] (JBranch (t "v166") (To (a "L161")) (To (a "L163"))));
  (mkBlock (a "L161") [] [(Let (a "v169") L (Ext Sw) [(t "pr.15")]);
      (Let (a "v170") L Shl [(t "v169"); (Const 4)]);
      (Flight (a "v171") Add [(FAddress (t "v13")); (FValue (t "v170"))] (LowerOf (t "v13")));
      (Let (a "chk15") A (Check 0 8 Read 8) [(t "v171")]);
      (Let (a "v172") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk15")]);
      (Flight (a "v177") Add [(FAddress (t "v171")); (FValue (Const 8))] (LowerOf (t "v171")));
      (Let (a "chk16") A (HalfCheck Upper 0 8 Read 1) [(t "chk15"); (t "v177")]);
      (Let (a "v178") L (RawLoad LdL 0) [(t "chk16")]);
      (Call (CResult (a "v179") P) (Global (a "__GI_mempcpy")) [(Arg P (t "pr.14")); (Arg P (t "v172")); (Arg L (t "v178"))]);
      (Let (a "v181") W Add [(t "pr.15"); (Const 1)])] (JGoto (Poll (a "L160"))));
  (mkBlock (a "L163") [] [(Let (a "chk17") A (Check 0 1 Write 1) [(t "pr.14")]);
      (RawStore Wb 0 (Const 0) (t "chk17"));
      (Call CVoid (Global (a "__set_vma_name")) [(Arg P (t "v141")); (Arg L (t "v135")); (Arg P (t "v0"))]);
      (Let (a "v187") P Copy [(Global (a "__GI___abort_msg"))]);
      (Let (a "chk18") A (Check 0 8 Read 8) [(t "v187")]);
      (Let (a "v189") P (RawLoadPointer 0 [AtomicRead]) [(t "chk18")])] (JGoto (To (a "L190"))));
  (mkBlock (a "L190") [(Phi (a "v192") P [((a "L163"), (t "v189")); ((a "L190"), (t "v193"))])] [(Let (a "chk19") A (HalfCheck Lower 0 8 Write 8) [(t "chk18"); (t "v187")]);
      (Let (a "v193") P (RawCas CasP 0) [(t "chk19"); (t "v192"); (t "v141")]);
      (Let (a "v194") L Ptoi [(t "v193")]);
      (Let (a "v195") L Ptoi [(t "v192")]);
      (Let (a "v196") W (Cmp Eq L) [(t "v194"); (t "v195")])] (JBranch (t "v196") (To (a "L191")) (Poll (a "L190"))));
  (mkBlock (a "L191") [] [(Let (a "v202") L Ptoi [(Const 0)]);
      (Let (a "v203") W (Cmp Ne L) [(t "v195"); (t "v202")])] (JBranch (t "v203") (To (a "L197")) (To (a "L116"))));
  (mkBlock (a "L197") [] [(Let (a "chk20") A (Check 0 4 Read 1) [(t "v192")]);
      (Let (a "v206") W (RawLoad (LdNarrow Uw) 0) [(t "chk20")]);
      (Let (a "v207") L (Ext Uw) [(t "v206")]);
      (Call (CResult (a "v208") W) (Global (a "__GI___munmap")) [(Arg P (t "v192")); (Arg L (t "v207"))])] (JGoto (To (a "L116"))));
  (mkBlock (a "L116") [] [(Call CVoid (Global (a "__GI_abort")) [])] JRetVoid)].

Definition hello_image_fn___GI___libc_fatal : func :=
  mkFunc (a "__GI___libc_fatal") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [] (JGoto (To (a "L3"))));
  (mkBlock (a "L3") [] [(Let (a "v5") P Copy [(Global (a "glibc_libc_fatal#str.299"))]);
      (Let (a "v6") P Copy [(Global (a "glibc_libc_fatal#str.300"))]);
      (Call CVoid (Global (a "__libc_message_impl")) [(Arg P (t "v5")); (Arg P (t "v6")); (Arg P (t "v0"))])] (JGoto (Poll (a "L3"))))].

Definition hello_image_fn_glibc_malloc'23__libc_malloc2 : func :=
  mkFunc (a "glibc_malloc#__libc_malloc2") (a "local") (RClass P) [(L, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v6") P (Alloc 16) [(t "v0")])] (JRet (t "v6")))].

Definition hello_image_fn___GI___libc_malloc : func :=
  mkFunc (a "__GI___libc_malloc") (a "export") (RClass P) [(L, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "iw_1.v6") W (Cmp Ugt L) [(t "v0"); (Const 9223372036854775807)])] (JBranch (t "iw_1.v6") (To (a "iw_1.join")) (To (a "iw_1.L4"))));
  (mkBlock (a "iw_1.L4") [] [(Let (a "iw_1.v14") L Add [(t "v0"); (Const 8)]);
      (Let (a "iw_1.v23") L Add [(t "iw_1.v14"); (Const 15)]);
      (Let (a "iw_1.v43") W (Cmp Ult L) [(t "iw_1.v23"); (Const 32)])] (JBranch (t "iw_1.v43") (To (a "iw_1.join")) (To (a "iw_1.L76"))));
  (mkBlock (a "iw_1.L76") [] [(Let (a "iw_1.v83") L And [(t "iw_1.v23"); (Const 18446744073709551600)])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [(Phi (a "v4") L [((a "start"), (Const 18446744073709551615)); ((a "iw_1.L4"), (Const 32)); ((a "iw_1.L76"), (t "iw_1.v83"))])] [(Let (a "v9") P Copy [(Global (a "glibc_malloc#mp_"))]);
      (Flight (a "v10") Add [(FAddress (t "v9")); (FValue (Const 120))] (LowerOf (t "v9")));
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v10")]);
      (Let (a "v11") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v12") W (Cmp Ult L) [(t "v4"); (t "v11")])] (JBranch (t "v12") (To (a "L26")) (To (a "L7"))));
  (mkBlock (a "L26") [] [(Let (a "v34") L Sub [(t "v4"); (Const 32)]);
      (Let (a "v42") L Shr [(t "v34"); (Const 4)]);
      (Let (a "v47") W (Cmp Ult L) [(t "v42"); (Const 64)])] (JBranch (t "v47") (To (a "L43")) (To (a "iw_3.start"))));
  (mkBlock (a "L43") [] [(Let (a "v53") P Copy [(Global (a "tcache"))]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v53")]);
      (Let (a "v54") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v55") Add [(FAddress (t "v54")); (FValue (Const 152))] (LowerOf (t "v54")));
      (Let (a "v57") L Shl [(t "v42"); (Const 3)]);
      (Flight (a "v58") Add [(FAddress (t "v55")); (FValue (t "v57"))] (LowerOf (t "v55")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v58")]);
      (Let (a "v59") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v60") L Ptoi [(t "v59")]);
      (Let (a "v61") L Ptoi [(Const 0)]);
      (Let (a "v62") W (Cmp Ne L) [(t "v60"); (t "v61")])] (JBranch (t "v62") (To (a "iw_2.start")) (To (a "L7"))));
  (mkBlock (a "iw_2.start") [] [(Let (a "iw_2.v3") P Copy [(Global (a "tcache"))]);
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "iw_2.v3")]);
      (Let (a "iw_2.v4") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "iw_2.v5") Add [(FAddress (t "iw_2.v4")); (FValue (Const 152))] (LowerOf (t "iw_2.v4")));
      (Flight (a "iw_2.v8") Add [(FAddress (t "iw_2.v5")); (FValue (t "v57"))] (LowerOf (t "iw_2.v5")));
      (Let (a "chk4") A (Check 0 8 Read 8) [(t "iw_2.v8")]);
      (Let (a "iw_2.iw_1.v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "iw_2.iw_1.v26") L Ptoi [(t "iw_2.iw_1.v13")]);
      (Let (a "iw_2.iw_1.v35") L And [(t "iw_2.iw_1.v26"); (Const 15)]);
      (Let (a "iw_2.iw_1.v36") W (Cmp Ne L) [(t "iw_2.iw_1.v35"); (Const 0)])] (JBranch (t "iw_2.iw_1.v36") (To (a "iw_2.iw_1.L22")) (To (a "iw_2.iw_1.L38"))));
  (mkBlock (a "iw_2.iw_1.L22") [] [(Let (a "iw_2.iw_1.v37") P Copy [(Global (a "glibc_malloc#str.421"))]);
      (Call CVoid (Global (a "glibc_malloc#malloc_printerr")) [(Arg P (t "iw_2.iw_1.v37"))])] (JGoto (To (a "iw_2.iw_1.L38"))));
  (mkBlock (a "iw_2.iw_1.L38") [] [(Let (a "iw_2.iw_1.v46") L Shr [(t "iw_2.iw_1.v26"); (Const 12)]);
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "iw_2.iw_1.v13")]);
      (Let (a "iw_2.iw_1.v48") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "iw_2.iw_1.v49") L Ptoi [(t "iw_2.iw_1.v48")]);
      (Let (a "iw_2.iw_1.v50") L Xor [(t "iw_2.iw_1.v46"); (t "iw_2.iw_1.v49")]);
      (Flight (a "iw_2.iw_1.v51") Copy [(FValue (t "iw_2.iw_1.v50"))] LowerNone);
      (Let (a "chk6") A (Renew 0 8 Write 8) [(t "chk4"); (t "iw_2.v8")]);
      (RawStorePointer 0 (t "iw_2.iw_1.v51") (t "chk6") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "iw_2.iw_1.v67") P Copy [(Global (a "tcache"))]);
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "iw_2.iw_1.v67")]);
      (Let (a "iw_2.iw_1.v68") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Let (a "iw_2.iw_1.v70") L Shl [(t "v42"); (Const 1)]);
      (Flight (a "iw_2.iw_1.v71") Add [(FAddress (t "iw_2.iw_1.v68")); (FValue (t "iw_2.iw_1.v70"))] (LowerOf (t "iw_2.iw_1.v68")));
      (Let (a "chk8") A (Check 0 2 Read 1) [(t "iw_2.iw_1.v71")]);
      (Let (a "iw_2.iw_1.v72") W (RawLoad (LdNarrow Uh) 0) [(t "chk8")]);
      (Let (a "iw_2.iw_1.v73") W Add [(t "iw_2.iw_1.v72"); (Const 1)]);
      (Let (a "iw_2.iw_1.v74") W (Ext Uh) [(t "iw_2.iw_1.v73")]);
      (Let (a "chk9") A (Renew 0 2 Write 1) [(t "chk8"); (t "iw_2.iw_1.v71")]);
      (RawStore Wh 0 (t "iw_2.iw_1.v74") (t "chk9"));
      (Flight (a "iw_2.iw_1.v76") Add [(FAddress (t "iw_2.iw_1.v13")); (FValue (Const 8))] (LowerOf (t "iw_2.iw_1.v13")));
      (Let (a "chk10") A (HalfCheck Upper 0 8 Write 1) [(t "chk5"); (t "iw_2.iw_1.v76")]);
      (RawStore Wl 0 (Const 0) (t "chk10"))] (JRet (t "iw_2.iw_1.v13")));
  (mkBlock (a "iw_3.start") [] [(Let (a "iw_3.iw_1.iw_1.v6") W (Cmp Eq L) [(t "v4"); (Const 0)])] (JBranch (t "iw_3.iw_1.iw_1.v6") (To (a "iw_3.iw_1.iw_1.L4")) (To (a "iw_3.iw_1.iw_1.L3"))));
  (mkBlock (a "iw_3.iw_1.iw_1.L3") [] [(Let (a "iw_3.iw_1.iw_1.v8") L Shr [(t "v4"); (Const 1)]);
      (Let (a "iw_3.iw_1.iw_1.v9") L Or [(t "v4"); (t "iw_3.iw_1.iw_1.v8")]);
      (Let (a "iw_3.iw_1.iw_1.v10") L Shr [(t "iw_3.iw_1.iw_1.v9"); (Const 2)]);
      (Let (a "iw_3.iw_1.iw_1.v11") L Or [(t "iw_3.iw_1.iw_1.v9"); (t "iw_3.iw_1.iw_1.v10")]);
      (Let (a "iw_3.iw_1.iw_1.v12") L Shr [(t "iw_3.iw_1.iw_1.v11"); (Const 4)]);
      (Let (a "iw_3.iw_1.iw_1.v13") L Or [(t "iw_3.iw_1.iw_1.v11"); (t "iw_3.iw_1.iw_1.v12")]);
      (Let (a "iw_3.iw_1.iw_1.v14") L Shr [(t "iw_3.iw_1.iw_1.v13"); (Const 8)]);
      (Let (a "iw_3.iw_1.iw_1.v15") L Or [(t "iw_3.iw_1.iw_1.v13"); (t "iw_3.iw_1.iw_1.v14")]);
      (Let (a "iw_3.iw_1.iw_1.v16") L Shr [(t "iw_3.iw_1.iw_1.v15"); (Const 16)]);
      (Let (a "iw_3.iw_1.iw_1.v17") L Or [(t "iw_3.iw_1.iw_1.v15"); (t "iw_3.iw_1.iw_1.v16")]);
      (Let (a "iw_3.iw_1.iw_1.v18") L Shr [(t "iw_3.iw_1.iw_1.v17"); (Const 32)]);
      (Let (a "iw_3.iw_1.iw_1.v19") L Or [(t "iw_3.iw_1.iw_1.v17"); (t "iw_3.iw_1.iw_1.v18")]);
      (Let (a "iw_3.iw_1.iw_1.v20") L Shr [(t "iw_3.iw_1.iw_1.v19"); (Const 1)]);
      (Let (a "iw_3.iw_1.iw_1.v21") L And [(t "iw_3.iw_1.iw_1.v20"); (Const 6148914691236517205)]);
      (Let (a "iw_3.iw_1.iw_1.v22") L Sub [(t "iw_3.iw_1.iw_1.v19"); (t "iw_3.iw_1.iw_1.v21")]);
      (Let (a "iw_3.iw_1.iw_1.v23") L And [(t "iw_3.iw_1.iw_1.v22"); (Const 3689348814741910323)]);
      (Let (a "iw_3.iw_1.iw_1.v24") L Shr [(t "iw_3.iw_1.iw_1.v22"); (Const 2)]);
      (Let (a "iw_3.iw_1.iw_1.v25") L And [(t "iw_3.iw_1.iw_1.v24"); (Const 3689348814741910323)]);
      (Let (a "iw_3.iw_1.iw_1.v26") L Add [(t "iw_3.iw_1.iw_1.v23"); (t "iw_3.iw_1.iw_1.v25")]);
      (Let (a "iw_3.iw_1.iw_1.v27") L Shr [(t "iw_3.iw_1.iw_1.v26"); (Const 4)]);
      (Let (a "iw_3.iw_1.iw_1.v28") L Add [(t "iw_3.iw_1.iw_1.v26"); (t "iw_3.iw_1.iw_1.v27")]);
      (Let (a "iw_3.iw_1.iw_1.v29") L And [(t "iw_3.iw_1.iw_1.v28"); (Const 1085102592571150095)]);
      (Let (a "iw_3.iw_1.iw_1.v30") L Mul [(t "iw_3.iw_1.iw_1.v29"); (Const 72340172838076673)]);
      (Let (a "iw_3.iw_1.iw_1.v31") L Shr [(t "iw_3.iw_1.iw_1.v30"); (Const 56)]);
      (Let (a "iw_3.iw_1.iw_1.v32") L Sub [(t "iw_3.iw_1.iw_1.v31"); (Const 64)]);
      (Let (a "iw_3.iw_1.iw_1.v33") L Neg [(t "iw_3.iw_1.iw_1.v32")])] (JGoto (To (a "iw_3.iw_1.iw_1.L4"))));
  (mkBlock (a "iw_3.iw_1.iw_1.L4") [(Phi (a "iw_3.iw_1.iw_1.v34") W [((a "iw_3.iw_1.iw_1.L3"), (t "iw_3.iw_1.iw_1.v33")); ((a "iw_3.start"), (Const 64))])] [(Let (a "iw_3.iw_1.v4") W Sub [(Const 64); (t "iw_3.iw_1.iw_1.v34")]);
      (Let (a "iw_3.v35") W Sub [(t "iw_3.iw_1.v4"); (Const 11)]);
      (Let (a "iw_3.v36") L (Ext Uw) [(t "iw_3.v35")]);
      (Let (a "iw_3.v38") L Add [(t "iw_3.v36"); (Const 64)]);
      (Let (a "iw_4.iw_1.v9") P Copy [(Global (a "tcache"))]);
      (Let (a "chk11") A (Check 0 8 Read 8) [(t "iw_4.iw_1.v9")]);
      (Let (a "iw_4.iw_1.v10") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk11")]);
      (Flight (a "iw_4.iw_1.v11") Add [(FAddress (t "iw_4.iw_1.v10")); (FValue (Const 152))] (LowerOf (t "iw_4.iw_1.v10")));
      (Let (a "iw_4.iw_1.v13") L Shl [(t "iw_3.v38"); (Const 3)]);
      (Flight (a "iw_4.iw_1.v14") Add [(FAddress (t "iw_4.iw_1.v11")); (FValue (t "iw_4.iw_1.v13"))] (LowerOf (t "iw_4.iw_1.v11")));
      (Let (a "chk12") A (Check 0 8 Read 8) [(t "iw_4.iw_1.v14")]);
      (Let (a "iw_4.iw_1.v17") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk12")])] (JGoto (To (a "iw_4.iw_1.L18"))));
  (mkBlock (a "iw_4.iw_1.L18") [(Phi (a "iw_4.iw_1.pr.2") P [((a "iw_4.iw_1.L19"), (t "iw_4.iw_1.v51")); ((a "iw_3.iw_1.iw_1.L4"), (t "iw_4.iw_1.v17"))]); (Phi (a "iw_4.iw_1.pr.1") P [((a "iw_4.iw_1.L19"), (t "iw_4.iw_1.pr.2")); ((a "iw_3.iw_1.iw_1.L4"), (t "iw_4.iw_1.v14"))]); (Phi (a "iw_4.pr.1") W [((a "iw_4.iw_1.L19"), (Const 1)); ((a "iw_3.iw_1.iw_1.L4"), (Const 0))])] [(Let (a "iw_4.iw_1.v22") L Ptoi [(t "iw_4.iw_1.pr.2")]);
      (Let (a "iw_4.iw_1.v23") L Ptoi [(Const 0)]);
      (Let (a "iw_4.iw_1.v24") W (Cmp Ne L) [(t "iw_4.iw_1.v22"); (t "iw_4.iw_1.v23")])] (JBranch (t "iw_4.iw_1.v24") (To (a "iw_4.iw_1.L25")) (To (a "iw_4.iw_1.L26"))));
  (mkBlock (a "iw_4.iw_1.L25") [] [(Flight (a "iw_4.iw_1.v29") Sub [(FAddress (t "iw_4.iw_1.pr.2")); (FValue (Const 16))] (LowerOf (t "iw_4.iw_1.pr.2")));
      (Flight (a "iw_4.iw_1.v30") Add [(FAddress (t "iw_4.iw_1.v29")); (FValue (Const 8))] (LowerOf (t "iw_4.iw_1.v29")));
      (Let (a "chk13") A (Check 0 8 Read 1) [(t "iw_4.iw_1.v30")]);
      (Let (a "iw_4.iw_1.v31") L (RawLoad LdL 0) [(t "chk13")]);
      (Let (a "iw_4.iw_1.v36") L And [(t "iw_4.iw_1.v31"); (Const 18446744073709551608)]);
      (Let (a "iw_4.iw_1.v38") W (Cmp Ult L) [(t "iw_4.iw_1.v36"); (t "v4")])] (JGoto (To (a "iw_4.iw_1.L26"))));
  (mkBlock (a "iw_4.iw_1.L26") [(Phi (a "iw_4.iw_1.v42") W [((a "iw_4.iw_1.L18"), (Const 0)); ((a "iw_4.iw_1.L25"), (t "iw_4.iw_1.v38"))])] [] (JBranch (t "iw_4.iw_1.v42") (To (a "iw_4.iw_1.L19")) (To (a "iw_4.iw_1.join"))));
  (mkBlock (a "iw_4.iw_1.L19") [] [(Let (a "iw_4.iw_1.v46") L Shr [(t "iw_4.iw_1.v22"); (Const 12)]);
      (Let (a "chk14") A (Check 0 8 Read 8) [(t "iw_4.iw_1.pr.2")]);
      (Let (a "iw_4.iw_1.v48") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Let (a "iw_4.iw_1.v49") L Ptoi [(t "iw_4.iw_1.v48")]);
      (Let (a "iw_4.iw_1.v50") L Xor [(t "iw_4.iw_1.v46"); (t "iw_4.iw_1.v49")]);
      (Flight (a "iw_4.iw_1.v51") Copy [(FValue (t "iw_4.iw_1.v50"))] LowerNone)] (JGoto (Poll (a "iw_4.iw_1.L18"))));
  (mkBlock (a "iw_4.iw_1.join") [] [(Let (a "iw_4.v17") W (Cmp Eq L) [(t "iw_4.iw_1.v22"); (t "iw_4.iw_1.v23")])] (JBranch (t "iw_4.v17") (To (a "iw_4.L19")) (To (a "iw_4.L18"))));
  (mkBlock (a "iw_4.L18") [] [(Flight (a "iw_4.v23") Sub [(FAddress (t "iw_4.iw_1.pr.2")); (FValue (Const 16))] (LowerOf (t "iw_4.iw_1.pr.2")));
      (Flight (a "iw_4.v24") Add [(FAddress (t "iw_4.v23")); (FValue (Const 8))] (LowerOf (t "iw_4.v23")));
      (Let (a "chk15") A (Check 0 8 Read 1) [(t "iw_4.v24")]);
      (Let (a "iw_4.v25") L (RawLoad LdL 0) [(t "chk15")]);
      (Let (a "iw_4.v30") L And [(t "iw_4.v25"); (Const 18446744073709551608)]);
      (Let (a "iw_4.v31") W (Cmp Ne L) [(t "v4"); (t "iw_4.v30")])] (JGoto (To (a "iw_4.L19"))));
  (mkBlock (a "iw_4.L19") [(Phi (a "iw_4.v33") W [((a "iw_4.iw_1.join"), (Const 1)); ((a "iw_4.L18"), (t "iw_4.v31"))])] [] (JBranch (t "iw_4.v33") (To (a "iw_4.join")) (To (a "iw_4.iw_2.start"))));
  (mkBlock (a "iw_4.iw_2.start") [] [] (JBranch (t "iw_4.pr.1") (To (a "iw_4.iw_2.L8")) (To (a "iw_4.iw_2.L7"))));
  (mkBlock (a "iw_4.iw_2.L7") [] [(Let (a "chk16") A (Check 0 8 Read 8) [(t "iw_4.iw_1.pr.1")]);
      (Let (a "iw_4.iw_2.v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk16")])] (JGoto (To (a "iw_4.iw_2.L9"))));
  (mkBlock (a "iw_4.iw_2.L8") [] [(Let (a "iw_4.iw_2.v15") L Ptoi [(t "iw_4.iw_1.pr.1")]);
      (Let (a "iw_4.iw_2.v16") L Shr [(t "iw_4.iw_2.v15"); (Const 12)]);
      (Let (a "chk17") A (Check 0 8 Read 8) [(t "iw_4.iw_1.pr.1")]);
      (Let (a "iw_4.iw_2.v18") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Let (a "iw_4.iw_2.v19") L Ptoi [(t "iw_4.iw_2.v18")]);
      (Let (a "iw_4.iw_2.v20") L Xor [(t "iw_4.iw_2.v16"); (t "iw_4.iw_2.v19")]);
      (Flight (a "iw_4.iw_2.v21") Copy [(FValue (t "iw_4.iw_2.v20"))] LowerNone)] (JGoto (To (a "iw_4.iw_2.L9"))));
  (mkBlock (a "iw_4.iw_2.L9") [(Phi (a "iw_4.iw_2.pr.1") P [((a "iw_4.iw_2.L7"), (t "iw_4.iw_2.v13")); ((a "iw_4.iw_2.L8"), (t "iw_4.iw_2.v21"))])] [(Let (a "iw_4.iw_2.v26") L Ptoi [(t "iw_4.iw_2.pr.1")]);
      (Let (a "iw_4.iw_2.v35") L And [(t "iw_4.iw_2.v26"); (Const 15)]);
      (Let (a "iw_4.iw_2.v36") W (Cmp Ne L) [(t "iw_4.iw_2.v35"); (Const 0)])] (JBranch (t "iw_4.iw_2.v36") (To (a "iw_4.iw_2.L22")) (To (a "iw_4.iw_2.L24"))));
  (mkBlock (a "iw_4.iw_2.L22") [] [(Let (a "iw_4.iw_2.v37") P Copy [(Global (a "glibc_malloc#str.421"))]);
      (Call CVoid (Global (a "glibc_malloc#malloc_printerr")) [(Arg P (t "iw_4.iw_2.v37"))])] (JGoto (To (a "iw_4.iw_2.L24"))));
  (mkBlock (a "iw_4.iw_2.L24") [] [] (JBranch (t "iw_4.pr.1") (To (a "iw_4.iw_2.L39")) (To (a "iw_4.iw_2.L38"))));
  (mkBlock (a "iw_4.iw_2.L38") [] [(Let (a "iw_4.iw_2.v46") L Shr [(t "iw_4.iw_2.v26"); (Const 12)]);
      (Let (a "chk18") A (Check 0 8 Read 8) [(t "iw_4.iw_2.pr.1")]);
      (Let (a "iw_4.iw_2.v48") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk18")]);
      (Let (a "iw_4.iw_2.v49") L Ptoi [(t "iw_4.iw_2.v48")]);
      (Let (a "iw_4.iw_2.v50") L Xor [(t "iw_4.iw_2.v46"); (t "iw_4.iw_2.v49")]);
      (Flight (a "iw_4.iw_2.v51") Copy [(FValue (t "iw_4.iw_2.v50"))] LowerNone);
      (Let (a "chk19") A (Check 0 8 Write 8) [(t "iw_4.iw_1.pr.1")]);
      (RawStorePointer 0 (t "iw_4.iw_2.v51") (t "chk19") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "iw_4.iw_2.L40"))));
  (mkBlock (a "iw_4.iw_2.L39") [] [(Let (a "iw_4.iw_2.v54") L Ptoi [(t "iw_4.iw_1.pr.1")]);
      (Let (a "iw_4.iw_2.v55") L Shr [(t "iw_4.iw_2.v54"); (Const 12)]);
      (Let (a "iw_4.iw_2.v58") L Shr [(t "iw_4.iw_2.v26"); (Const 12)]);
      (Let (a "chk20") A (Check 0 8 Read 8) [(t "iw_4.iw_2.pr.1")]);
      (Let (a "iw_4.iw_2.v60") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk20")]);
      (Let (a "iw_4.iw_2.v61") L Ptoi [(t "iw_4.iw_2.v60")]);
      (Let (a "iw_4.iw_2.v62") L Xor [(t "iw_4.iw_2.v58"); (t "iw_4.iw_2.v61")]);
      (Flight (a "iw_4.iw_2.v63") Copy [(FValue (t "iw_4.iw_2.v62"))] LowerNone);
      (Let (a "iw_4.iw_2.v64") L Ptoi [(t "iw_4.iw_2.v63")]);
      (Let (a "iw_4.iw_2.v65") L Xor [(t "iw_4.iw_2.v55"); (t "iw_4.iw_2.v64")]);
      (Flight (a "iw_4.iw_2.v66") Copy [(FValue (t "iw_4.iw_2.v65"))] LowerNone);
      (Let (a "chk21") A (Check 0 8 Write 8) [(t "iw_4.iw_1.pr.1")]);
      (RawStorePointer 0 (t "iw_4.iw_2.v66") (t "chk21") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "iw_4.iw_2.L40"))));
  (mkBlock (a "iw_4.iw_2.L40") [] [(Let (a "iw_4.iw_2.v67") P Copy [(Global (a "tcache"))]);
      (Let (a "chk22") A (Check 0 8 Read 8) [(t "iw_4.iw_2.v67")]);
      (Let (a "iw_4.iw_2.v68") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk22")]);
      (Let (a "iw_4.iw_2.v70") L Shl [(t "iw_3.v38"); (Const 1)]);
      (Flight (a "iw_4.iw_2.v71") Add [(FAddress (t "iw_4.iw_2.v68")); (FValue (t "iw_4.iw_2.v70"))] (LowerOf (t "iw_4.iw_2.v68")));
      (Let (a "chk23") A (Check 0 2 Read 1) [(t "iw_4.iw_2.v71")]);
      (Let (a "iw_4.iw_2.v72") W (RawLoad (LdNarrow Uh) 0) [(t "chk23")]);
      (Let (a "iw_4.iw_2.v73") W Add [(t "iw_4.iw_2.v72"); (Const 1)]);
      (Let (a "iw_4.iw_2.v74") W (Ext Uh) [(t "iw_4.iw_2.v73")]);
      (Let (a "chk24") A (Renew 0 2 Write 1) [(t "chk23"); (t "iw_4.iw_2.v71")]);
      (RawStore Wh 0 (t "iw_4.iw_2.v74") (t "chk24"));
      (Flight (a "iw_4.iw_2.v76") Add [(FAddress (t "iw_4.iw_2.pr.1")); (FValue (Const 8))] (LowerOf (t "iw_4.iw_2.pr.1")));
      (Let (a "chk25") A (Check 0 8 Write 1) [(t "iw_4.iw_2.v76")]);
      (RawStore Wl 0 (Const 0) (t "chk25"))] (JGoto (To (a "iw_4.join"))));
  (mkBlock (a "iw_4.join") [(Phi (a "v71") P [((a "iw_4.iw_2.L40"), (t "iw_4.iw_2.pr.1")); ((a "iw_4.L19"), (Const 0))])] [(Let (a "v76") L Ptoi [(t "v71")]);
      (Let (a "v78") W (Cmp Ne L) [(t "v76"); (t "iw_4.iw_1.v23")])] (JBranch (t "v78") (To (a "L72")) (To (a "L7"))));
  (mkBlock (a "L72") [] [] (JRet (t "v71")));
  (mkBlock (a "L7") [] [(Call (CResult (a "v82") P) (Global (a "glibc_malloc#__libc_malloc2")) [(Arg L (t "v0"))])] (JRet (t "v82")))].

Definition hello_image_fn___GI___libc_free : func :=
  mkFunc (a "__GI___libc_free") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call CVoid (Global (a "zgc_free")) [(Arg P (t "v0"))])] JRetVoid)].

Definition hello_image_fn___GI___libc_realloc : func :=
  mkFunc (a "__GI___libc_realloc") (a "export") (RClass P) [(P, (a "v0")); (L, (a "v2"))] [(mkBlock (a "start") [] [(Call (CResult (a "v9") P) (Global (a "zgc_realloc")) [(Arg P (t "v0")); (Arg L (t "v2"))])] (JRet (t "v9")))].

Definition hello_image_fn___libc_calloc : func :=
  mkFunc (a "__libc_calloc") (a "export") (RClass P) [(L, (a "v0")); (L, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v10") L Mul [(t "v0"); (t "v2")]);
      (Let (a "v11") L And [(t "v0"); (Const 4294967295)]);
      (Let (a "v12") L Shr [(t "v0"); (Const 32)]);
      (Let (a "v13") L And [(t "v2"); (Const 4294967295)]);
      (Let (a "v14") L Shr [(t "v2"); (Const 32)]);
      (Let (a "v15") L Mul [(t "v11"); (t "v13")]);
      (Let (a "v16") L Mul [(t "v12"); (t "v13")]);
      (Let (a "v17") L Mul [(t "v11"); (t "v14")]);
      (Let (a "v18") L Mul [(t "v12"); (t "v14")]);
      (Let (a "v19") L Shr [(t "v15"); (Const 32)]);
      (Let (a "v20") L And [(t "v16"); (Const 4294967295)]);
      (Let (a "v21") L And [(t "v17"); (Const 4294967295)]);
      (Let (a "v22") L Add [(t "v19"); (t "v20")]);
      (Let (a "v23") L Add [(t "v22"); (t "v21")]);
      (Let (a "v24") L Shr [(t "v23"); (Const 32)]);
      (Let (a "v25") L Shr [(t "v16"); (Const 32)]);
      (Let (a "v26") L Shr [(t "v17"); (Const 32)]);
      (Let (a "v27") L Add [(t "v18"); (t "v25")]);
      (Let (a "v28") L Add [(t "v27"); (t "v26")]);
      (Let (a "v29") L Add [(t "v28"); (t "v24")]);
      (Let (a "v35") W (Cmp Ne L) [(t "v29"); (Const 0)])] (JBranch (t "v35") (To (a "L5")) (To (a "L41"))));
  (mkBlock (a "L5") [] [(Let (a "v39") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk0") A (Check 0 4 Write 1) [(t "v39")]);
      (RawStore Ww 0 (Const 12) (t "chk0"))] (JRet (Const 0)));
  (mkBlock (a "L41") [] [(Let (a "v45") P (Alloc 16) [(t "v10")])] (JRet (t "v45")))].

Definition hello_image_fn___GI___libc_scratch_buffer_grow_preserve : func :=
  mkFunc (a "__GI___libc_scratch_buffer_grow_preserve") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v4") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v4")]);
      (Let (a "v5") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v6") L Shl [(t "v5"); (Const 1)]);
      (Let (a "chk1") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v0")]);
      (Let (a "v12") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v14") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "v15") L Ptoi [(t "v12")]);
      (Let (a "v16") L Ptoi [(t "v14")]);
      (Let (a "v17") W (Cmp Eq L) [(t "v15"); (t "v16")])] (JBranch (t "v17") (To (a "L8")) (To (a "L9"))));
  (mkBlock (a "L8") [] [(Call (CResult (a "v19") P) (Global (a "malloc")) [(Arg L (t "v6"))]);
      (Let (a "v24") L Ptoi [(t "v19")]);
      (Let (a "v25") L Ptoi [(Const 0)]);
      (Let (a "v26") W (Cmp Eq L) [(t "v24"); (t "v25")])] (JBranch (t "v26") (To (a "L20")) (To (a "L22"))));
  (mkBlock (a "L20") [] [] (JRet (Const 0)));
  (mkBlock (a "L22") [] [(Flight (a "v31") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Flight (a "v33") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk2") A (Renew 0 8 Read 1) [(t "chk0"); (t "v33")]);
      (Let (a "v34") L (RawLoad LdL 0) [(t "chk2")]);
      (Call (CResult (a "v35") P) (Global (a "__GI_memcpy")) [(Arg P (t "v19")); (Arg P (t "v31")); (Arg L (t "v34"))])] (JGoto (To (a "L10"))));
  (mkBlock (a "L9") [] [(Flight (a "v41") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v42") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v43") W (Cmp Uge L) [(t "v6"); (t "v42")])] (JBranch (t "v43") (To (a "L36")) (To (a "L37"))));
  (mkBlock (a "L36") [] [(Let (a "v47") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Call (CResult (a "v49") P) (Global (a "realloc")) [(Arg P (t "v47")); (Arg L (t "v6"))])] (JGoto (To (a "L38"))));
  (mkBlock (a "L37") [] [(Let (a "v50") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk5") A (Check 0 4 Write 1) [(t "v50")]);
      (RawStore Ww 0 (Const 12) (t "chk5"))] (JGoto (To (a "L38"))));
  (mkBlock (a "L38") [(Phi (a "pr.2") P [((a "L36"), (t "v49")); ((a "L37"), (Const 0))])] [(Let (a "v55") L Ptoi [(t "pr.2")]);
      (Let (a "v56") L Ptoi [(Const 0)]);
      (Let (a "v57") W (Cmp Eq L) [(t "v55"); (t "v56")])] (JBranch (t "v57") (To (a "L51")) (To (a "L10"))));
  (mkBlock (a "L51") [] [(Let (a "chk6") A (Renew 0 8 Read 8) [(t "chk1"); (t "v0")]);
      (Let (a "v61") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "v61"))]);
      (Flight (a "iw_1.v4") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk7") A (Renew 0 8 Write 8) [(t "chk1"); (t "v0")]);
      (RawStorePointer 0 (t "iw_1.v4") (t "chk7") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_1.v6") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk8") A (Renew 0 8 Write 1) [(t "chk0"); (t "iw_1.v6")]);
      (RawStore Wl 0 (Const 1024) (t "chk8"))] (JRet (Const 0)));
  (mkBlock (a "L10") [(Phi (a "pr.1") P [((a "L22"), (t "v19")); ((a "L38"), (t "pr.2"))])] [(Let (a "chk9") A (Renew 0 8 Write 8) [(t "chk1"); (t "v0")]);
      (RawStorePointer 0 (t "pr.1") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v68") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk10") A (Renew 0 8 Write 1) [(t "chk0"); (t "v68")]);
      (RawStore Wl 0 (t "v6") (t "chk10"))] (JRet (Const 1)))].

Definition hello_image_fn___GI___libc_scratch_buffer_set_array_size : func :=
  mkFunc (a "__GI___libc_scratch_buffer_set_array_size") (a "export") (RClass W) [(P, (a "v0")); (L, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v9") L Mul [(t "v2"); (t "v4")]);
      (Let (a "v15") L Or [(t "v2"); (t "v4")]);
      (Let (a "v18") L Shr [(t "v15"); (Const 32)]);
      (Let (a "v19") W (Cmp Ne L) [(t "v18"); (Const 0)])] (JBranch (t "v19") (To (a "L20")) (To (a "L21"))));
  (mkBlock (a "L20") [] [(Let (a "v23") W (Cmp Ne L) [(t "v2"); (Const 0)])] (JGoto (To (a "L21"))));
  (mkBlock (a "L21") [(Phi (a "v25") W [((a "start"), (Const 0)); ((a "L20"), (t "v23"))])] [] (JBranch (t "v25") (To (a "L26")) (To (a "L27"))));
  (mkBlock (a "L26") [] [(Let (a "v31") L Udiv [(t "v9"); (t "v2")]);
      (Let (a "v32") W (Cmp Ne L) [(t "v4"); (t "v31")])] (JGoto (To (a "L27"))));
  (mkBlock (a "L27") [(Phi (a "v34") W [((a "L21"), (Const 0)); ((a "L26"), (t "v32"))])] [] (JBranch (t "v34") (To (a "iw_1.start")) (To (a "L12"))));
  (mkBlock (a "iw_1.start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "iw_1.v6") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "iw_1.v8") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "iw_1.v9") L Ptoi [(t "iw_1.v6")]);
      (Let (a "iw_1.v10") L Ptoi [(t "iw_1.v8")]);
      (Let (a "iw_1.v11") W (Cmp Ne L) [(t "iw_1.v9"); (t "iw_1.v10")])] (JBranch (t "iw_1.v11") (To (a "iw_1.L2")) (To (a "iw_2.start"))));
  (mkBlock (a "iw_1.L2") [] [(Let (a "iw_1.v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "iw_1.v13"))])] (JGoto (To (a "iw_2.start"))));
  (mkBlock (a "iw_2.start") [] [(Flight (a "iw_2.v4") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk2") A (Renew 0 8 Write 8) [(t "chk0"); (t "v0")]);
      (RawStorePointer 0 (t "iw_2.v4") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_2.v6") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Write 1) [(t "chk0"); (t "iw_2.v6")]);
      (RawStore Wl 0 (Const 1024) (t "chk3"));
      (Let (a "v37") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk4") A (Check 0 4 Write 1) [(t "v37")]);
      (RawStore Ww 0 (Const 12) (t "chk4"))] (JRet (Const 0)));
  (mkBlock (a "L12") [] [(Flight (a "v45") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk5") A (Check 0 8 Read 1) [(t "v45")]);
      (Let (a "v46") L (RawLoad LdL 0) [(t "chk5")]);
      (Let (a "v47") W (Cmp Ule L) [(t "v9"); (t "v46")])] (JBranch (t "v47") (To (a "L40")) (To (a "iw_3.start"))));
  (mkBlock (a "L40") [] [] (JRet (Const 1)));
  (mkBlock (a "iw_3.start") [] [(Let (a "chk6") A (HalfCheck Lower 0 8 Read 8) [(t "chk5"); (t "v0")]);
      (Let (a "iw_3.v6") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "iw_3.v8") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "iw_3.v9") L Ptoi [(t "iw_3.v6")]);
      (Let (a "iw_3.v10") L Ptoi [(t "iw_3.v8")]);
      (Let (a "iw_3.v11") W (Cmp Ne L) [(t "iw_3.v9"); (t "iw_3.v10")])] (JBranch (t "iw_3.v11") (To (a "iw_3.L2")) (To (a "iw_3.join"))));
  (mkBlock (a "iw_3.L2") [] [(Let (a "iw_3.v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "iw_3.v13"))])] (JGoto (To (a "iw_3.join"))));
  (mkBlock (a "iw_3.join") [] [(Call (CResult (a "v53") P) (Global (a "malloc")) [(Arg L (t "v9"))]);
      (Let (a "v58") L Ptoi [(t "v53")]);
      (Let (a "v59") L Ptoi [(Const 0)]);
      (Let (a "v60") W (Cmp Eq L) [(t "v58"); (t "v59")])] (JBranch (t "v60") (To (a "iw_4.start")) (To (a "L56"))));
  (mkBlock (a "iw_4.start") [] [(Flight (a "iw_4.v4") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk8") A (Renew 0 8 Write 8) [(t "chk6"); (t "v0")]);
      (RawStorePointer 0 (t "iw_4.v4") (t "chk8") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_4.v6") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk9") A (Renew 0 8 Write 1) [(t "chk5"); (t "iw_4.v6")]);
      (RawStore Wl 0 (Const 1024) (t "chk9"))] (JRet (Const 0)));
  (mkBlock (a "L56") [] [(Let (a "chk10") A (Renew 0 8 Write 8) [(t "chk6"); (t "v0")]);
      (RawStorePointer 0 (t "v53") (t "chk10") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v67") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk11") A (Renew 0 8 Write 1) [(t "chk5"); (t "v67")]);
      (RawStore Wl 0 (t "v9") (t "chk11"))] (JRet (Const 1)))].

Definition hello_image_fn___GI___libc_cleanup_push_defer : func :=
  mkFunc (a "__GI___libc_cleanup_push_defer") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "v5") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Flight (a "v7") Add [(FAddress (t "v3")); (FValue (Const 776))] (LowerOf (t "v3")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v7")]);
      (Let (a "v8") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Write 8) [(t "v5")]);
      (RawStorePointer 0 (t "v8") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v11") Add [(FAddress (t "v3")); (FValue (Const 792))] (LowerOf (t "v3")));
      (Let (a "chk2") A (HalfCheck Upper 0 4 Read 1) [(t "chk0"); (t "v11")]);
      (Let (a "v12") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v18") W And [(t "v12"); (Const 2)]);
      (Let (a "v19") L (Ext Sw) [(t "v18")]);
      (Let (a "v20") W (Cmp Ne L) [(t "v19"); (Const 0)])] (JBranch (t "v20") (To (a "L22")) (To (a "L15"))));
  (mkBlock (a "L22") [(Phi (a "pr.2") W [((a "L36"), (t "pr.3")); ((a "start"), (t "v12"))])] [(Let (a "v28") W And [(t "pr.2"); (Const 4294967293)]);
      (Flight (a "v30") Add [(FAddress (t "v3")); (FValue (Const 792))] (LowerOf (t "v3")));
      (Let (a "chk3") A (HalfCheck Upper 0 4 Write 4) [(t "chk0"); (t "v30")]);
      (Let (a "v33") W (RawCas (CasNarrow Sw) 0) [(t "chk3"); (t "pr.2"); (t "v28")]);
      (Let (a "v34") W (Cmp Eq W) [(t "v33"); (t "pr.2")])] (JBranch (t "v34") (To (a "L36")) (To (a "L35"))));
  (mkBlock (a "L35") [] [] (JGoto (To (a "L36"))));
  (mkBlock (a "L36") [(Phi (a "pr.3") W [((a "L22"), (t "pr.2")); ((a "L35"), (t "v33"))])] [(Let (a "v37") W (Cmp Ne W) [(t "v33"); (t "pr.2")])] (JBranch (t "v37") (Poll (a "L22")) (To (a "L15"))));
  (mkBlock (a "L15") [(Phi (a "pr.1") W [((a "L36"), (t "pr.3")); ((a "start"), (t "v12"))])] [(Flight (a "v39") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "v45") W And [(t "pr.1"); (Const 2)])] (JBranch (t "v45") (To (a "L42")) (To (a "L41"))));
  (mkBlock (a "L41") [] [] (JGoto (To (a "L42"))));
  (mkBlock (a "L42") [(Phi (a "v46") W [((a "L41"), (Const 0)); ((a "L15"), (Const 1))])] [(Let (a "chk4") A (HalfCheck Lower 0 4 Write 1) [(t "chk1"); (t "v39")]);
      (RawStore Ww 0 (t "v46") (t "chk4"));
      (Flight (a "v48") Add [(FAddress (t "v3")); (FValue (Const 776))] (LowerOf (t "v3")));
      (Let (a "chk5") A (Renew 0 8 Write 8) [(t "chk0"); (t "v48")]);
      (RawStorePointer 0 (t "v0") (t "chk5") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] JRetVoid)].

Definition hello_image_fn___GI___libc_cleanup_pop_restore : func :=
  mkFunc (a "__GI___libc_cleanup_pop_restore") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "v5") Add [(FAddress (t "v3")); (FValue (Const 776))] (LowerOf (t "v3")));
      (Flight (a "v7") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v7")]);
      (Let (a "v8") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Write 8) [(t "v5")]);
      (RawStorePointer 0 (t "v8") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v11") Add [(FAddress (t "v3")); (FValue (Const 792))] (LowerOf (t "v3")));
      (Let (a "chk2") A (HalfCheck Upper 0 4 Read 1) [(t "chk1"); (t "v11")]);
      (Let (a "v12") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Flight (a "v17") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk3") A (HalfCheck Lower 0 4 Read 1) [(t "chk0"); (t "v17")]);
      (Let (a "v18") W (RawLoad (LdNarrow Sw) 0) [(t "chk3")]);
      (Let (a "v19") W (Cmp Ne W) [(t "v18"); (Const 0)])] (JBranch (t "v19") (To (a "L20")) (To (a "L21"))));
  (mkBlock (a "L20") [] [(Let (a "v24") W And [(t "v12"); (Const 2)]);
      (Let (a "v25") W (Cmp Eq W) [(t "v24"); (Const 0)])] (JGoto (To (a "L21"))));
  (mkBlock (a "L21") [(Phi (a "v27") W [((a "start"), (Const 0)); ((a "L20"), (t "v25"))])] [] (JBranch (t "v27") (To (a "L29")) (To (a "L15"))));
  (mkBlock (a "L29") [(Phi (a "pr.1") W [((a "L42"), (t "pr.2")); ((a "L21"), (t "v12"))])] [(Let (a "v34") W Or [(t "pr.1"); (Const 2)]);
      (Flight (a "v36") Add [(FAddress (t "v3")); (FValue (Const 792))] (LowerOf (t "v3")));
      (Let (a "chk4") A (HalfCheck Upper 0 4 Write 4) [(t "chk1"); (t "v36")]);
      (Let (a "v39") W (RawCas (CasNarrow Sw) 0) [(t "chk4"); (t "pr.1"); (t "v34")]);
      (Let (a "v40") W (Cmp Eq W) [(t "v39"); (t "pr.1")])] (JBranch (t "v40") (To (a "L42")) (To (a "L41"))));
  (mkBlock (a "L41") [] [] (JGoto (To (a "L42"))));
  (mkBlock (a "L42") [(Phi (a "pr.2") W [((a "L29"), (t "pr.1")); ((a "L41"), (t "v39"))])] [(Let (a "v43") W (Cmp Ne W) [(t "v39"); (t "pr.1")])] (JBranch (t "v43") (Poll (a "L29")) (To (a "iw_1.start"))));
  (mkBlock (a "iw_1.start") [] [(Let (a "iw_1.v10") W And [(t "pr.2"); (Const 57)]);
      (Let (a "iw_1.v12") W (Cmp Eq W) [(t "iw_1.v10"); (Const 8)])] (JBranch (t "iw_1.v12") (To (a "L44")) (To (a "L15"))));
  (mkBlock (a "L44") [] [(Flight (a "v52") Copy [(FValue (Const 18446744073709551615))] LowerNone);
      (Call (CResult (a "iw_2.v3") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "iw_2.v5") Add [(FAddress (t "iw_2.v3")); (FValue (Const 1608))] (LowerOf (t "iw_2.v3")));
      (Let (a "chk5") A (Check 0 8 Write 8) [(t "iw_2.v5")]);
      (RawStorePointer 0 (t "v52") (t "chk5") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_2.v9") Add [(FAddress (t "iw_2.v3")); (FValue (Const 792))] (LowerOf (t "iw_2.v3")));
      (Let (a "chk6") A (HalfCheck Lower 0 4 Read 1) [(t "chk5"); (t "iw_2.v9")]);
      (Let (a "iw_2.v10") W (RawLoad (LdNarrow Sw) 0) [(t "chk6")])] (JGoto (To (a "iw_2.L12"))));
  (mkBlock (a "iw_2.L12") [(Phi (a "iw_2.pr.1") W [((a "iw_2.L38"), (t "iw_2.pr.2")); ((a "L44"), (t "iw_2.v10"))])] [(Let (a "iw_2.v17") W Or [(t "iw_2.pr.1"); (Const 1)]);
      (Let (a "iw_2.v19") W Or [(t "iw_2.v17"); (Const 16)]);
      (Let (a "iw_2.v23") W And [(t "iw_2.v19"); (Const 4294967293)]);
      (Let (a "iw_2.v29") W (Cmp Eq W) [(t "iw_2.pr.1"); (t "iw_2.v23")])] (JBranch (t "iw_2.v29") (To (a "iw_2.L14")) (To (a "iw_2.L13"))));
  (mkBlock (a "iw_2.L13") [] [(Flight (a "iw_2.v32") Add [(FAddress (t "iw_2.v3")); (FValue (Const 792))] (LowerOf (t "iw_2.v3")));
      (Let (a "chk7") A (HalfCheck Lower 0 4 Write 4) [(t "chk5"); (t "iw_2.v32")]);
      (Let (a "iw_2.v35") W (RawCas (CasNarrow Sw) 0) [(t "chk7"); (t "iw_2.pr.1"); (t "iw_2.v23")]);
      (Let (a "iw_2.v36") W (Cmp Eq W) [(t "iw_2.v35"); (t "iw_2.pr.1")])] (JBranch (t "iw_2.v36") (To (a "iw_2.L38")) (To (a "iw_2.L37"))));
  (mkBlock (a "iw_2.L37") [] [] (JGoto (To (a "iw_2.L38"))));
  (mkBlock (a "iw_2.L38") [(Phi (a "iw_2.pr.2") W [((a "iw_2.L13"), (t "iw_2.pr.1")); ((a "iw_2.L37"), (t "iw_2.v35"))])] [(Let (a "iw_2.v39") W (Cmp Ne W) [(t "iw_2.v35"); (t "iw_2.pr.1")])] (JBranch (t "iw_2.v39") (Poll (a "iw_2.L12")) (To (a "iw_2.L14"))));
  (mkBlock (a "iw_2.L14") [] [(Flight (a "iw_2.v41") Add [(FAddress (t "iw_2.v3")); (FValue (Const 784))] (LowerOf (t "iw_2.v3")));
      (Let (a "chk8") A (HalfCheck Lower 0 8 Read 8) [(t "chk5"); (t "iw_2.v41")]);
      (Let (a "iw_2.v42") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Call CVoid (Global (a "__GI___pthread_unwind")) [(Arg P (t "iw_2.v42"))])] (JGoto (To (a "L15"))));
  (mkBlock (a "L15") [] [] JRetVoid)].

Definition hello_image_fn___libc_siglongjmp : func :=
  mkFunc (a "__libc_siglongjmp") (a "export") RVoid [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v5") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call CVoid (Global (a "zlongjmp")) [(Arg P (t "v5")); (Arg W (t "v2"))])] JRetVoid)].
