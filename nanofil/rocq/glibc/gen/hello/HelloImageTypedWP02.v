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

Definition hello_image_fn___wprintf_buffer_pad_1 : func :=
  mkFunc (a "__wprintf_buffer_pad_1") (a "export") RVoid [(P, (a "v0")); (W, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Flight (a "iw_1.v3") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "iw_1.v3")]);
      (Let (a "iw_1.v4") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "iw_1.v5") W (Cmp Eq W) [(t "iw_1.v4"); (Const 0)])] (JBranch (t "iw_1.v5") (To (a "L6")) (To (a "L15"))));
  (mkBlock (a "L6") [] [] JRetVoid);
  (mkBlock (a "L15") [(Phi (a "pr.1") L [((a "L67"), (t "v86")); ((a "start"), (t "v4"))])] [(Flight (a "v22") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v22")]);
      (Let (a "v23") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v25") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk2") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v25")]);
      (Let (a "v26") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v27") L Ptoi [(t "v23")]);
      (Let (a "v28") L Ptoi [(t "v26")]);
      (Let (a "v29") W (Cmp Eq L) [(t "v27"); (t "v28")])] (JBranch (t "v29") (To (a "L30")) (To (a "L31"))));
  (mkBlock (a "L30") [] [(Call (CResult (a "v33") W) (Global (a "__wprintf_buffer_flush")) [(Arg P (t "v0"))]);
      (Let (a "v34") W (Ext Ub) [(t "v33")]);
      (Let (a "v35") W (Cmp Eq W) [(t "v34"); (Const 0)])] (JGoto (To (a "L31"))));
  (mkBlock (a "L31") [(Phi (a "v37") W [((a "L15"), (Const 0)); ((a "L30"), (t "v35"))])] [] (JBranch (t "v37") (To (a "L18")) (To (a "L20"))));
  (mkBlock (a "L18") [] [] JRetVoid);
  (mkBlock (a "L20") [] [(Flight (a "v43") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk3") A (Renew 0 8 Read 8) [(t "chk1"); (t "v43")]);
      (Let (a "v44") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "v46") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk4") A (Renew 0 8 Read 8) [(t "chk2"); (t "v46")]);
      (Let (a "v47") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "v48") L Ptoi [(t "v44")]);
      (Let (a "v49") L Ptoi [(t "v47")]);
      (Let (a "v50") W (Cmp Ne L) [(t "v48"); (t "v49")])] (JBranch (t "v50") (To (a "L41")) (To (a "L40"))));
  (mkBlock (a "L40") [] [(Let (a "v51") P Copy [(Global (a "glibc_wprintf_buffer_pad_1#str.41"))]);
      (Let (a "v52") P Copy [(Global (a "glibc_wprintf_buffer_pad_1#str.42"))]);
      (Let (a "v53") P Copy [(Global (a "glibc_wprintf_buffer_pad_1#str.43"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v51")); (Arg P (t "v52")); (Arg W (Const 35)); (Arg P (t "v53"))])] (JGoto (To (a "L41"))));
  (mkBlock (a "L41") [] [(Flight (a "v56") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk5") A (Renew 0 8 Read 8) [(t "chk2"); (t "v56")]);
      (Let (a "v57") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v59") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk6") A (Renew 0 8 Read 8) [(t "chk1"); (t "v59")]);
      (Let (a "v60") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v61") L Ptoi [(t "v57")]);
      (Let (a "v62") L Ptoi [(t "v60")]);
      (Let (a "v63") L Sub [(t "v61"); (t "v62")]);
      (Let (a "v64") L Div [(t "v63"); (Const 4)]);
      (Let (a "v70") W (Cmp Ugt L) [(t "v64"); (t "pr.1")])] (JBranch (t "v70") (To (a "L67")) (To (a "L66"))));
  (mkBlock (a "L66") [] [] (JGoto (To (a "L67"))));
  (mkBlock (a "L67") [(Phi (a "pr.2") L [((a "L66"), (t "v64")); ((a "L41"), (t "pr.1"))])] [(Flight (a "v73") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v74") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Call (CResult (a "v77") P) (Global (a "__GI___wmemset")) [(Arg P (t "v74")); (Arg W (t "v2")); (Arg L (t "pr.2"))]);
      (Let (a "chk8") A (Renew 0 8 Read 8) [(t "chk1"); (t "v73")]);
      (Let (a "v80") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "v82") L Shl [(t "pr.2"); (Const 2)]);
      (Flight (a "v83") Add [(FAddress (t "v80")); (FValue (t "v82"))] (LowerOf (t "v80")));
      (Let (a "chk9") A (Renew 0 8 Write 8) [(t "chk1"); (t "v73")]);
      (RawStorePointer 0 (t "v83") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v86") L Sub [(t "pr.1"); (t "pr.2")]);
      (Let (a "v88") W (Cmp Ugt L) [(t "v86"); (Const 0)])] (JBranch (t "v88") (Poll (a "L15")) (To (a "L17"))));
  (mkBlock (a "L17") [] [] JRetVoid)].

Definition hello_image_fn___wprintf_buffer_putc_1 : func :=
  mkFunc (a "__wprintf_buffer_putc_1") (a "export") RVoid [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Flight (a "iw_1.v3") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "iw_1.v3")]);
      (Let (a "iw_1.v4") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "iw_1.v5") W (Cmp Eq W) [(t "iw_1.v4"); (Const 0)])] (JBranch (t "iw_1.v5") (To (a "L13")) (To (a "L12"))));
  (mkBlock (a "L12") [] [(Call (CResult (a "v15") W) (Global (a "__wprintf_buffer_flush")) [(Arg P (t "v0"))]);
      (Let (a "v16") W (Ext Ub) [(t "v15")]);
      (Let (a "v17") W (Cmp Eq W) [(t "v16"); (Const 0)])] (JGoto (To (a "L13"))));
  (mkBlock (a "L13") [(Phi (a "v19") W [((a "start"), (Const 1)); ((a "L12"), (t "v17"))])] [] (JBranch (t "v19") (To (a "L4")) (To (a "L6"))));
  (mkBlock (a "L4") [] [] JRetVoid);
  (mkBlock (a "L6") [] [(Flight (a "v25") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v25")]);
      (Let (a "v26") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v28") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk2") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v28")]);
      (Let (a "v29") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v30") L Ptoi [(t "v26")]);
      (Let (a "v31") L Ptoi [(t "v29")]);
      (Let (a "v32") W (Cmp Ult L) [(t "v30"); (t "v31")])] (JBranch (t "v32") (To (a "L23")) (To (a "L22"))));
  (mkBlock (a "L22") [] [(Let (a "v33") P Copy [(Global (a "glibc_wprintf_buffer_putc_1#str.39"))]);
      (Let (a "v34") P Copy [(Global (a "glibc_wprintf_buffer_putc_1#str.40"))]);
      (Let (a "v35") P Copy [(Global (a "glibc_wprintf_buffer_putc_1#str.41"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v33")); (Arg P (t "v34")); (Arg W (Const 27)); (Arg P (t "v35"))])] (JGoto (To (a "L23"))));
  (mkBlock (a "L23") [] [(Flight (a "v37") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk3") A (Renew 0 8 Read 8) [(t "chk1"); (t "v37")]);
      (Let (a "v38") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "v39") Add [(FAddress (t "v38")); (FValue (Const 4))] (LowerOf (t "v38")));
      (Let (a "chk4") A (Renew 0 8 Write 8) [(t "chk1"); (t "v37")]);
      (RawStorePointer 0 (t "v39") (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk5") A (Check 0 4 Write 1) [(t "v38")]);
      (RawStore Ww 0 (t "v2") (t "chk5"))] JRetVoid)].

Definition hello_image_fn___wprintf_buffer_flush_to_file : func :=
  mkFunc (a "__wprintf_buffer_flush_to_file") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v4") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v4")]);
      (Let (a "v5") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v7") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Let (a "v8") L Ptoi [(t "v5")]);
      (Let (a "v9") L Ptoi [(t "v7")]);
      (Let (a "v10") L Sub [(t "v8"); (t "v9")]);
      (Let (a "v11") L Div [(t "v10"); (Const 4)]);
      (Flight (a "v16") Add [(FAddress (t "v0")); (FValue (Const 40))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v16")]);
      (Let (a "v17") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v18") Add [(FAddress (t "v17")); (FValue (Const 216))] (LowerOf (t "v17")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v18")]);
      (Let (a "v19") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "iw_1.v4") L Ptoi [(t "v19")]);
      (Let (a "iw_1.v7") P Copy [(Global (a "__io_vtables"))]);
      (Let (a "iw_1.v8") L Ptoi [(t "iw_1.v7")]);
      (Let (a "iw_1.v9") L Sub [(t "iw_1.v4"); (t "iw_1.v8")]);
      (Let (a "iw_1.v15") W (Cmp Uge L) [(t "iw_1.v9"); (Const 2352)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L10")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Call CVoid (Global (a "_IO_vtable_check")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v21") Add [(FAddress (t "v19")); (FValue (Const 56))] (LowerOf (t "v19")));
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v21")]);
      (Let (a "v22") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "v24") Add [(FAddress (t "v0")); (FValue (Const 40))] (LowerOf (t "v0")));
      (Let (a "chk4") A (Renew 0 8 Read 8) [(t "chk1"); (t "v24")]);
      (Let (a "v25") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Flight (a "v27") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Let (a "chk5") F CheckFunction [(t "v22")]);
      (RawCall (CResult (a "v29") L) (t "chk5") [(Arg P (t "v25")); (Arg P (t "v27")); (Arg L (t "v11"))]);
      (Let (a "v31") W (Cmp Ne L) [(t "v29"); (t "v11")])] (JBranch (t "v31") (To (a "iw_2.start")) (To (a "L14"))));
  (mkBlock (a "iw_2.start") [] [(Flight (a "iw_2.v3") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk6") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "iw_2.v3")]);
      (RawStore Ww 0 (Const 0) (t "chk6"))] JRetVoid);
  (mkBlock (a "L14") [] [(Flight (a "v35") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk7") A (HalfCheck Upper 0 8 Read 1) [(t "chk0"); (t "v35")]);
      (Let (a "v36") L (RawLoad LdL 0) [(t "chk7")]);
      (Let (a "v38") L Add [(t "v36"); (t "v11")]);
      (Let (a "chk8") A (Renew 0 8 Write 1) [(t "chk7"); (t "v35")]);
      (RawStore Wl 0 (t "v38") (t "chk8"));
      (Flight (a "v40") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Flight (a "v42") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Let (a "chk9") A (Renew 0 8 Write 8) [(t "chk0"); (t "v40")]);
      (RawStorePointer 0 (t "v42") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] JRetVoid)].

Definition hello_image_fn___wprintf_buffer_to_file_init : func :=
  mkFunc (a "__wprintf_buffer_to_file_init") (a "export") RVoid [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Flight (a "v6") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v0")]);
      (RawStorePointer 0 (t "v6") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_1.v11") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "iw_1.v11")]);
      (RawStorePointer 0 (t "v6") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_1.v14") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Flight (a "iw_1.v18") Add [(FAddress (t "v6")); (FValue (Const 512))] (LowerOf (t "v6")));
      (Let (a "chk2") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "iw_1.v14")]);
      (RawStorePointer 0 (t "iw_1.v18") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_1.v20") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Write 1) [(t "chk0"); (t "iw_1.v20")]);
      (RawStore Wl 0 (Const 0) (t "chk3"));
      (Flight (a "iw_1.v22") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk4") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "iw_1.v22")]);
      (RawStore Ww 0 (Const 2) (t "chk4"));
      (Flight (a "v11") Add [(FAddress (t "v0")); (FValue (Const 40))] (LowerOf (t "v0")));
      (Let (a "chk5") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v11")]);
      (RawStorePointer 0 (t "v2") (t "chk5") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] JRetVoid)].

Definition hello_image_fn___wprintf_buffer_to_file_done : func :=
  mkFunc (a "__wprintf_buffer_to_file_done") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "iw_1.v3") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "iw_1.v3")]);
      (Let (a "iw_1.v4") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "iw_1.v5") W (Cmp Eq W) [(t "iw_1.v4"); (Const 0)])] (JBranch (t "iw_1.v5") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L4") [] [(Call CVoid (Global (a "__wprintf_buffer_flush_to_file")) [(Arg P (t "v0"))]);
      (Call (CResult (a "v12") W) (Global (a "__wprintf_buffer_done")) [(Arg P (t "v0"))])] (JRet (t "v12")))].

Definition hello_image_fn___wprintf_buffer_write : func :=
  mkFunc (a "__wprintf_buffer_write") (a "export") RVoid [(P, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Flight (a "iw_1.v3") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "iw_1.v3")]);
      (Let (a "iw_1.v4") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "iw_1.v5") W (Cmp Eq W) [(t "iw_1.v4"); (Const 0)])] (JBranch (t "iw_1.v5") (To (a "L6")) (To (a "L15"))));
  (mkBlock (a "L6") [] [] JRetVoid);
  (mkBlock (a "L15") [(Phi (a "pr.2") L [((a "L69"), (t "v92")); ((a "start"), (t "v4"))]); (Phi (a "pr.1") P [((a "L69"), (t "v89")); ((a "start"), (t "v2"))])] [(Let (a "v19") W (Cmp Ugt L) [(t "pr.2"); (Const 0)])] (JBranch (t "v19") (To (a "L16")) (To (a "L17"))));
  (mkBlock (a "L16") [] [(Flight (a "v24") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v24")]);
      (Let (a "v25") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v27") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk2") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v27")]);
      (Let (a "v28") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v29") L Ptoi [(t "v25")]);
      (Let (a "v30") L Ptoi [(t "v28")]);
      (Let (a "v31") W (Cmp Eq L) [(t "v29"); (t "v30")])] (JBranch (t "v31") (To (a "L32")) (To (a "L33"))));
  (mkBlock (a "L32") [] [(Call (CResult (a "v35") W) (Global (a "__wprintf_buffer_flush")) [(Arg P (t "v0"))]);
      (Let (a "v36") W (Ext Ub) [(t "v35")]);
      (Let (a "v37") W (Cmp Eq W) [(t "v36"); (Const 0)])] (JGoto (To (a "L33"))));
  (mkBlock (a "L33") [(Phi (a "v39") W [((a "L16"), (Const 0)); ((a "L32"), (t "v37"))])] [] (JBranch (t "v39") (To (a "L20")) (To (a "L22"))));
  (mkBlock (a "L20") [] [] JRetVoid);
  (mkBlock (a "L22") [] [(Flight (a "v45") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk3") A (Renew 0 8 Read 8) [(t "chk1"); (t "v45")]);
      (Let (a "v46") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "v48") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk4") A (Renew 0 8 Read 8) [(t "chk2"); (t "v48")]);
      (Let (a "v49") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "v50") L Ptoi [(t "v46")]);
      (Let (a "v51") L Ptoi [(t "v49")]);
      (Let (a "v52") W (Cmp Ne L) [(t "v50"); (t "v51")])] (JBranch (t "v52") (To (a "L43")) (To (a "L42"))));
  (mkBlock (a "L42") [] [(Let (a "v53") P Copy [(Global (a "glibc_wprintf_buffer_write#str.41"))]);
      (Let (a "v54") P Copy [(Global (a "glibc_wprintf_buffer_write#str.42"))]);
      (Let (a "v55") P Copy [(Global (a "glibc_wprintf_buffer_write#str.43"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v53")); (Arg P (t "v54")); (Arg W (Const 35)); (Arg P (t "v55"))])] (JGoto (To (a "L43"))));
  (mkBlock (a "L43") [] [(Flight (a "v58") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk5") A (Renew 0 8 Read 8) [(t "chk2"); (t "v58")]);
      (Let (a "v59") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v61") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk6") A (Renew 0 8 Read 8) [(t "chk1"); (t "v61")]);
      (Let (a "v62") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v63") L Ptoi [(t "v59")]);
      (Let (a "v64") L Ptoi [(t "v62")]);
      (Let (a "v65") L Sub [(t "v63"); (t "v64")]);
      (Let (a "v66") L Div [(t "v65"); (Const 4)]);
      (Let (a "v72") W (Cmp Ugt L) [(t "v66"); (t "pr.2")])] (JBranch (t "v72") (To (a "L69")) (To (a "L68"))));
  (mkBlock (a "L68") [] [] (JGoto (To (a "L69"))));
  (mkBlock (a "L69") [(Phi (a "pr.3") L [((a "L68"), (t "v66")); ((a "L43"), (t "pr.2"))])] [(Flight (a "v75") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v76") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Call (CResult (a "v79") P) (Global (a "__wmemcpy")) [(Arg P (t "v76")); (Arg P (t "pr.1")); (Arg L (t "pr.3"))]);
      (Let (a "chk8") A (Renew 0 8 Read 8) [(t "chk1"); (t "v75")]);
      (Let (a "v82") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "v84") L Shl [(t "pr.3"); (Const 2)]);
      (Flight (a "v85") Add [(FAddress (t "v82")); (FValue (t "v84"))] (LowerOf (t "v82")));
      (Let (a "chk9") A (Renew 0 8 Write 8) [(t "chk1"); (t "v75")]);
      (RawStorePointer 0 (t "v85") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v89") Add [(FAddress (t "pr.1")); (FValue (t "v84"))] (LowerOf (t "pr.1")));
      (Let (a "v92") L Sub [(t "pr.2"); (t "pr.3")])] (JGoto (Poll (a "L15"))));
  (mkBlock (a "L17") [] [] JRetVoid)].

Definition hello_image_fn___wprintf_function_invoke : func :=
  mkFunc (a "__wprintf_function_invoke") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (L, (a "v6")); (P, (a "v8"))] [(mkBlock (a "start") [] [(Let (a "v10") P (Alloc 8) [(Const 32)]);
      (Let (a "v52") P (Alloc 8) [(Const 464)]);
      (Let (a "v19") W (Cmp Ule L) [(t "v6"); (Const 4)])] (JBranch (t "v19") (To (a "L14")) (To (a "L13"))));
  (mkBlock (a "L13") [] [(Call (CResult (a "v21") P) (Global (a "calloc")) [(Arg L (t "v6")); (Arg L (Const 8))]);
      (Let (a "v26") L Ptoi [(t "v21")]);
      (Let (a "v27") L Ptoi [(Const 0)]);
      (Let (a "v28") W (Cmp Eq L) [(t "v26"); (t "v27")])] (JBranch (t "v28") (To (a "L22")) (To (a "L14"))));
  (mkBlock (a "L22") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L14") [(Phi (a "pr.1") P [((a "start"), (t "v10")); ((a "L13"), (t "v21"))])] [] (JGoto (To (a "L32"))));
  (mkBlock (a "L32") [(Phi (a "pr.2") W [((a "L14"), (Const 0)); ((a "L33"), (t "v51"))])] [(Let (a "v38") L (Ext Uw) [(t "pr.2")]);
      (Let (a "v39") W (Cmp Ult L) [(t "v38"); (t "v6")])] (JBranch (t "v39") (To (a "L33")) (To (a "L35"))));
  (mkBlock (a "L33") [] [(Let (a "v43") L Shl [(t "v38"); (Const 3)]);
      (Flight (a "v44") Add [(FAddress (t "pr.1")); (FValue (t "v43"))] (LowerOf (t "pr.1")));
      (Let (a "v48") L Shl [(t "v38"); (Const 4)]);
      (Flight (a "v49") Add [(FAddress (t "v4")); (FValue (t "v48"))] (LowerOf (t "v4")));
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v44")]);
      (RawStorePointer 0 (t "v49") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v51") W Add [(t "pr.2"); (Const 1)])] (JGoto (Poll (a "L32"))));
  (mkBlock (a "L35") [] [(Call CVoid (Global (a "__wprintf_buffer_as_file_init")) [(Arg P (t "v52")); (Arg P (t "v0"))]);
      (Let (a "chk1") F CheckFunction [(t "v2")]);
      (RawCall (CResult (a "v59") W) (t "chk1") [(Arg P (t "v52")); (Arg P (t "v8")); (Arg P (t "pr.1"))]);
      (Call (CResult (a "v63") W) (Global (a "__wprintf_buffer_as_file_terminate")) [(Arg P (t "v52"))]);
      (Let (a "v64") W (Ext Ub) [(t "v63")]);
      (Let (a "v65") W (Cmp Eq W) [(t "v64"); (Const 0)])] (JBranch (t "v65") (To (a "L62")) (To (a "L61"))));
  (mkBlock (a "L61") [] [] (JGoto (To (a "L62"))));
  (mkBlock (a "L62") [(Phi (a "pr.3") W [((a "L61"), (t "v59")); ((a "L35"), (Const 4294967295))])] [(Let (a "v71") L Ptoi [(t "pr.1")]);
      (Let (a "v72") L Ptoi [(t "v10")]);
      (Let (a "v73") W (Cmp Ne L) [(t "v71"); (t "v72")])] (JBranch (t "v73") (To (a "L67")) (To (a "L69"))));
  (mkBlock (a "L67") [] [(Call CVoid (Global (a "free")) [(Arg P (t "pr.1"))])] (JGoto (To (a "L69"))));
  (mkBlock (a "L69") [] [] (JRet (t "pr.3")))].
