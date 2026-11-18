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

Definition hello_image_fn_glibc_printf_fp'23__libc_use_alloca'2egnu_inline : func :=
  mkFunc (a "glibc_printf_fp#__libc_use_alloca.gnu_inline") (a "local") (RClass W) [(L, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") W) (Global (a "__GI___libc_alloca_cutoff")) [(Arg L (t "v0"))]);
      (Let (a "v4") L (Ext Sw) [(t "v3")]);
      (Let (a "v5") W (Cmp Ne L) [(t "v4"); (Const 0)])] (JBranch (t "v5") (To (a "L7")) (To (a "L6"))));
  (mkBlock (a "L6") [] [(Let (a "v11") W (Cmp Ule L) [(t "v0"); (Const 4096)])] (JGoto (To (a "L7"))));
  (mkBlock (a "L7") [(Phi (a "v15") W [((a "start"), (Const 1)); ((a "L6"), (t "v11"))])] [] (JRet (t "v15")))].

Definition hello_image_fn___GI___libc_secure_getenv : func :=
  mkFunc (a "__GI___libc_secure_getenv") (a "export") (RClass P) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v5") P Copy [(Global (a "__libc_enable_secure"))]);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v5")]);
      (Let (a "v6") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")])] (JBranch (t "v6") (To (a "L4")) (To (a "L3"))));
  (mkBlock (a "L3") [] [(Call (CResult (a "v8") P) (Global (a "__GI_getenv")) [(Arg P (t "v0"))])] (JGoto (To (a "L4"))));
  (mkBlock (a "L4") [(Phi (a "v9") P [((a "L3"), (t "v8")); ((a "start"), (Const 0))])] [] (JRet (t "v9")))].

Definition hello_image_fn___GI___libc_alloca_cutoff : func :=
  mkFunc (a "__GI___libc_alloca_cutoff") (a "export") (RClass W) [(L, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v6") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "v7") Add [(FAddress (t "v6")); (FValue (Const 1720))] (LowerOf (t "v6")));
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v7")]);
      (Let (a "v8") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v9") L Shr [(t "v8"); (Const 2)]);
      (Let (a "v10") W (Cmp Ne L) [(t "v9"); (Const 0)])] (JBranch (t "v10") (To (a "L13")) (To (a "L12"))));
  (mkBlock (a "L12") [] [] (JGoto (To (a "L13"))));
  (mkBlock (a "L13") [(Phi (a "v16") L [((a "L12"), (Const 262144)); ((a "start"), (t "v9"))])] [(Let (a "v17") W (Cmp Ugt L) [(t "v16"); (Const 65536)])] (JBranch (t "v17") (To (a "L5")) (To (a "L4"))));
  (mkBlock (a "L4") [] [(Call (CResult (a "v18") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "v19") Add [(FAddress (t "v18")); (FValue (Const 1720))] (LowerOf (t "v18")));
      (Let (a "chk1") A (Check 0 8 Read 1) [(t "v19")]);
      (Let (a "v20") L (RawLoad LdL 0) [(t "chk1")]);
      (Let (a "v21") L Shr [(t "v20"); (Const 2)]);
      (Let (a "v22") W (Cmp Ne L) [(t "v21"); (Const 0)])] (JBranch (t "v22") (To (a "L5")) (To (a "L24"))));
  (mkBlock (a "L24") [] [] (JGoto (To (a "L5"))));
  (mkBlock (a "L5") [(Phi (a "v29") L [((a "L13"), (Const 65536)); ((a "L24"), (Const 262144)); ((a "L4"), (t "v21"))])] [(Let (a "v30") W (Cmp Ule L) [(t "v0"); (t "v29")])] (JRet (t "v30")))].

Definition hello_image_fn_glibc_libc_start'23__libc_start_call_main : func :=
  mkFunc (a "glibc_libc_start#__libc_start_call_main") (a "local") RVoid [(P, (a "v0")); (W, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v1") P (Alloc 8) [(Const 8)]);
      (Let (a "v3") P (Alloc 4) [(Const 4)]);
      (Let (a "v5") P (Alloc 8) [(Const 8)]);
      (Let (a "v6") P (Alloc 4) [(Const 4)]);
      (Let (a "v7") P (Alloc 8) [(Const 104)]);
      (Let (a "v8") P (Alloc 4) [(Const 4)]);
      (Let (a "v17") P (Alloc 8) [(Const 8)]);
      (Let (a "v36") P (Alloc 8) [(Const 128)]);
      (Let (a "v37") P (Alloc 8) [(Const 8)]);
      (Let (a "v62") P (Alloc 8) [(Const 8)]);
      (Let (a "v63") P (Alloc 4) [(Const 4)]);
      (Let (a "v64") P (Alloc 4) [(Const 4)]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v1")]);
      (RawStorePointer 0 (t "v0") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk1") A (Check 0 4 Write 1) [(t "v3")]);
      (RawStore Ww 0 (t "v2") (t "chk1"));
      (Let (a "chk2") A (Check 0 8 Write 8) [(t "v5")]);
      (RawStorePointer 0 (t "v4") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v9") W (Setjmp SjUnderscore) [(t "v7"); (Const 0)]);
      (Let (a "chk3") A (Check 0 4 Write 1) [(t "v8")]);
      (RawStore Ww 0 (t "v9") (t "chk3"));
      (Let (a "v13") W (RawLoad (LdNarrow Sw) 0) [(t "chk3")]);
      (Let (a "v14") W (Cmp Eq W) [(t "v13"); (Const 0)]);
      (Let (a "v15") L (Ext Sw) [(t "v14")]);
      (Let (a "v16") W (Cmp Ne L) [(t "v15"); (Const 0)])] (JBranch (t "v16") (To (a "L10")) (To (a "L11"))));
  (mkBlock (a "L10") [] [(Call (CResult (a "v18") P) (Global (a "zthread_self_cookie")) []);
      (Let (a "chk5") A (Check 0 8 Write 8) [(t "v17")]);
      (RawStorePointer 0 (t "v18") (t "chk5") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v19") Add [(FAddress (t "v7")); (FValue (Const 72))] (LowerOf (t "v7")));
      (Let (a "chk6") A (Check 0 8 Read 8) [(t "v17")]);
      (Let (a "v20") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v21") Add [(FAddress (t "v20")); (FValue (Const 784))] (LowerOf (t "v20")));
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v21")]);
      (Let (a "v22") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Let (a "chk8") A (Check 0 8 Write 8) [(t "v19")]);
      (RawStorePointer 0 (t "v22") (t "chk8") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v23") Add [(FAddress (t "v7")); (FValue (Const 72))] (LowerOf (t "v7")));
      (Flight (a "v24") Add [(FAddress (t "v23")); (FValue (Const 8))] (LowerOf (t "v23")));
      (Let (a "chk9") A (Check 0 8 Read 8) [(t "v17")]);
      (Let (a "v25") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Flight (a "v26") Add [(FAddress (t "v25")); (FValue (Const 776))] (LowerOf (t "v25")));
      (Let (a "chk10") A (Check 0 8 Read 8) [(t "v26")]);
      (Let (a "v27") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")]);
      (Let (a "chk11") A (Check 0 8 Write 8) [(t "v24")]);
      (RawStorePointer 0 (t "v27") (t "chk11") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk12") A (Check 0 8 Read 8) [(t "v17")]);
      (Let (a "v28") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk12")]);
      (Flight (a "v29") Add [(FAddress (t "v28")); (FValue (Const 784))] (LowerOf (t "v28")));
      (Let (a "chk13") A (Check 0 8 Write 8) [(t "v29")]);
      (RawStorePointer 0 (t "v7") (t "chk13") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk14") A (Check 0 8 Read 8) [(t "v1")]);
      (Let (a "v30") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Let (a "chk15") A (Check 0 4 Read 1) [(t "v3")]);
      (Let (a "v31") W (RawLoad (LdNarrow Sw) 0) [(t "chk15")]);
      (Let (a "chk16") A (Check 0 8 Read 8) [(t "v5")]);
      (Let (a "v32") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk16")]);
      (Let (a "v33") P Copy [(Global (a "__environ"))]);
      (Let (a "chk17") A (Check 0 8 Read 8) [(t "v33")]);
      (Let (a "v34") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Let (a "chk18") F CheckFunction [(t "v30")]);
      (RawCall (CResult (a "v35") W) (t "chk18") [(Arg W (t "v31")); (Arg P (t "v32")); (Arg P (t "v34"))]);
      (Let (a "chk19") A (Check 0 4 Write 1) [(t "v6")]);
      (RawStore Ww 0 (t "v35") (t "chk19"))] (JGoto (To (a "L12"))));
  (mkBlock (a "L11") [] [(Call CVoid (Global (a "__GI___nptl_deallocate_tsd")) []);
      (Let (a "chk20") A (Check 0 4 Write 1) [(t "v6")]);
      (RawStore Ww 0 (Const 0) (t "chk20"));
      (Call CVoid (Global (a "glibc_libc_start#internal_signal_block_all")) [(Arg P (t "v36"))]);
      (Call (CResult (a "v38") P) (Global (a "zthread_self_cookie")) []);
      (Let (a "chk21") A (Check 0 8 Write 8) [(t "v37")]);
      (RawStorePointer 0 (t "v38") (t "chk21") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L39"))));
  (mkBlock (a "L39") [] [(Let (a "chk22") A (Check 0 8 Read 8) [(t "v37")]);
      (Let (a "v42") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk22")]);
      (Flight (a "v43") Add [(FAddress (t "v42")); (FValue (Const 1592))] (LowerOf (t "v42")));
      (Let (a "chk23") A (Check 0 4 Write 1) [(t "v43")]);
      (RawStore Ww 0 (Const 0) (t "chk23"))] (JGoto (To (a "L40"))));
  (mkBlock (a "L40") [] [] (JBranch (Const 0) (Poll (a "L39")) (To (a "L41"))));
  (mkBlock (a "L41") [] [(Let (a "v44") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk22")]);
      (Flight (a "v45") Add [(FAddress (t "v44")); (FValue (Const 1592))] (LowerOf (t "v44")));
      (Call CVoid (Global (a "glibc_libc_start#futex_wake")) [(Arg P (t "v45")); (Arg W (Const 1)); (Arg W (Const 128))]);
      (Let (a "v49") P Copy [(Global (a "__GI___nptl_nthreads"))]);
      (Let (a "v50") W Neg [(Const 1)]);
      (Let (a "chk25") A (Check 0 4 Read 1) [(t "v49")]);
      (Let (a "v51") W (RawLoad (LdNarrow Uw) 0) [(t "chk25")])] (JGoto (To (a "L52"))));
  (mkBlock (a "L52") [(Phi (a "v54") W [((a "L41"), (t "v51")); ((a "L52"), (t "v56"))])] [(Let (a "v55") W Add [(t "v54"); (t "v50")]);
      (Let (a "chk26") A (Check 0 4 Write 4) [(t "v49")]);
      (Let (a "v56") W (RawCas (CasNarrow Uw) 0) [(t "chk26"); (t "v54"); (t "v55")]);
      (Let (a "v57") W (Cmp Eq W) [(t "v56"); (t "v54")])] (JBranch (t "v57") (To (a "L53")) (Poll (a "L52"))));
  (mkBlock (a "L53") [] [(Let (a "v58") W (Cmp Ne W) [(t "v54"); (Const 1)])] (JBranch (t "v58") (To (a "L46")) (To (a "L47"))));
  (mkBlock (a "L46") [] [] (JGoto (To (a "L59"))));
  (mkBlock (a "L59") [] [] (JBranch (Const 1) (To (a "L60")) (To (a "L61"))));
  (mkBlock (a "L60") [] [(Let (a "chk27") A (Check 0 4 Write 1) [(t "v63")]);
      (RawStore Ww 0 (Const 0) (t "chk27"));
      (Let (a "v65") W (RawLoad (LdNarrow Sw) 0) [(t "chk27")]);
      (Let (a "chk29") A (Check 0 4 Write 1) [(t "v64")]);
      (RawStore Ww 0 (t "v65") (t "chk29"));
      (Let (a "v66") W (RawLoad (LdNarrow Sw) 0) [(t "chk29")]);
      (Let (a "v67") P Copy [(Global (a "glibc_libc_start#str.319"))]);
      (Call CVoid (Global (a "zsafety_error")) [(Arg P (t "v67"))]);
      (Let (a "chk31") A (Check 0 8 Read 1) [(t "v62")]);
      (Let (a "v68") L (RawLoad LdL 0) [(t "chk31")])] (JGoto (Poll (a "L59"))));
  (mkBlock (a "L61") [] [] (JGoto (To (a "L48"))));
  (mkBlock (a "L47") [] [] (JGoto (To (a "L48"))));
  (mkBlock (a "L48") [] [] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [] [(Let (a "chk32") A (Check 0 4 Read 1) [(t "v6")]);
      (Let (a "v69") W (RawLoad (LdNarrow Sw) 0) [(t "chk32")]);
      (Call CVoid (Global (a "__GI_exit")) [(Arg W (t "v69"))])] JRetVoid)].

Definition hello_image_fn___libc_start_main : func :=
  mkFunc (a "__libc_start_main") (a "export") (RClass W) [(P, (a "v0")); (W, (a "v2")); (P, (a "v4")); (P, (a "v6")); (P, (a "v8"))] [(mkBlock (a "start") [] [(Call CVoid (Global (a "zmake_setjmp_save_sigmask")) [(Arg W (Const 1))]);
      (Let (a "v11") P Copy [(Global (a "__environ"))]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v11")]);
      (RawStorePointer 0 (t "v6") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v13") P Copy [(Global (a "_dl_auxv"))]);
      (Let (a "chk1") A (Check 0 8 Write 8) [(t "v13")]);
      (RawStorePointer 0 (t "v8") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L17"))));
  (mkBlock (a "L17") [(Phi (a "pr.1") P [((a "L19"), (t "v36")); ((a "start"), (t "v8"))])] [(Let (a "chk2") A (Check 0 8 Read 1) [(t "pr.1")]);
      (Let (a "v22") L (RawLoad LdL 0) [(t "chk2")]);
      (Let (a "v23") W (Cmp Ne L) [(t "v22"); (Const 0)])] (JBranch (t "v23") (To (a "L18")) (To (a "L20"))));
  (mkBlock (a "L18") [] [(Let (a "v28") L (RawLoad LdL 0) [(t "chk2")]);
      (Let (a "v29") W (Cmp Eq L) [(t "v28"); (Const 23)])] (JBranch (t "v29") (To (a "L24")) (To (a "L19"))));
  (mkBlock (a "L24") [] [(Let (a "v30") P Copy [(Global (a "__libc_enable_secure"))]);
      (Flight (a "v32") Add [(FAddress (t "pr.1")); (FValue (Const 8))] (LowerOf (t "pr.1")));
      (Let (a "chk4") A (HalfCheck Upper 0 8 Read 1) [(t "chk2"); (t "v32")]);
      (Let (a "v33") L (RawLoad LdL 0) [(t "chk4")]);
      (Let (a "chk5") A (Check 0 4 Write 1) [(t "v30")]);
      (RawStore Ww 0 (t "v33") (t "chk5"))] (JGoto (To (a "L20"))));
  (mkBlock (a "L19") [] [(Flight (a "v36") Add [(FAddress (t "pr.1")); (FValue (Const 16))] (LowerOf (t "pr.1")))] (JGoto (Poll (a "L17"))));
  (mkBlock (a "L20") [] [(Let (a "v40") P Copy [(Global (a "__pthread_initialize_minimal"))]);
      (Let (a "v41") L Ptoi [(t "v40")]);
      (Let (a "v42") L Ptoi [(Const 0)]);
      (Let (a "v43") W (Cmp Ne L) [(t "v41"); (t "v42")])] (JBranch (t "v43") (To (a "L37")) (To (a "L39"))));
  (mkBlock (a "L37") [] [(Call CVoid (Global (a "__pthread_initialize_minimal")) [])] (JGoto (To (a "L39"))));
  (mkBlock (a "L39") [] [(Let (a "v44") P Copy [(Global (a "_dl_x86_cpu_features"))]);
      (Call CVoid (Global (a "glibc_libc_start#init_cpu_features")) [(Arg P (t "v44"))]);
      (Call CVoid (Global (a "__libc_setup_tls")) []);
      (Let (a "v45") P Copy [(Global (a "glibc_libc_start#errno_handler"))]);
      (Call CVoid (Global (a "zregister_sys_errno_handler")) [(Arg P (t "v45"))]);
      (Let (a "v46") P Copy [(Global (a "glibc_libc_start#dlerror_handler"))]);
      (Call CVoid (Global (a "zregister_sys_dlerror_handler")) [(Arg P (t "v46"))]);
      (Call CVoid (Global (a "__libc_early_init")) [(Arg W (Const 1))]);
      (Let (a "v51") P Copy [(Global (a "_dl_debug_mask"))]);
      (Let (a "chk6") A (Check 0 4 Read 1) [(t "v51")]);
      (Let (a "v52") W (RawLoad (LdNarrow Sw) 0) [(t "chk6")]);
      (Let (a "v54") W And [(t "v52"); (Const 2)]);
      (Let (a "v55") L (Ext Sw) [(t "v54")]);
      (Let (a "v56") W (Cmp Ne L) [(t "v55"); (Const 0)])] (JBranch (t "v56") (To (a "L48")) (To (a "L50"))));
  (mkBlock (a "L48") [] [(Let (a "v57") P Copy [(Global (a "glibc_libc_start#str.320"))]);
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v4")]);
      (Let (a "v60") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Call CVoid (Global (a "zprintf")) [(Arg P (t "v57")); (Arg P (t "v60"))])] (JGoto (To (a "L50"))));
  (mkBlock (a "L50") [] [(Call CVoid (Global (a "zrun_deferred_global_ctors")) []);
      (Let (a "v64") P Copy [(Global (a "_dl_debug_mask"))]);
      (Let (a "chk8") A (Check 0 4 Read 1) [(t "v64")]);
      (Let (a "v65") W (RawLoad (LdNarrow Sw) 0) [(t "chk8")]);
      (Let (a "v67") W And [(t "v65"); (Const 2)]);
      (Let (a "v68") L (Ext Sw) [(t "v67")]);
      (Let (a "v69") W (Cmp Ne L) [(t "v68"); (Const 0)])] (JBranch (t "v69") (To (a "L61")) (To (a "L63"))));
  (mkBlock (a "L61") [] [(Let (a "v70") P Copy [(Global (a "glibc_libc_start#str.321"))]);
      (Let (a "chk9") A (Check 0 8 Read 8) [(t "v4")]);
      (Let (a "v73") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Call CVoid (Global (a "zprintf")) [(Arg P (t "v70")); (Arg P (t "v73"))])] (JGoto (To (a "L63"))));
  (mkBlock (a "L63") [] [(Call CVoid (Global (a "glibc_libc_start#__libc_start_call_main")) [(Arg P (t "v0")); (Arg W (t "v2")); (Arg P (t "v4"))])] (JRet (Const 0)))].

Definition hello_image_fn___libc_setup_tls : func :=
  mkFunc (a "__libc_setup_tls") (a "export") RVoid [] [(mkBlock (a "start") [] [(Let (a "v1") P (Alloc 16) [(Const 2496)]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v1")]);
      (RawStorePointer 0 (t "v1") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_1.v12") Add [(FAddress (t "v1")); (FValue (Const 16))] (LowerOf (t "v1")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "iw_1.v12")]);
      (RawStorePointer 0 (t "v1") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Call CVoid (Global (a "zthread_set_self_cookie")) [(Arg P (t "v1"))]);
      (Call CVoid (Global (a "__tls_init_tp")) [])] JRetVoid)].

Definition hello_image_fn___libc_early_init : func :=
  mkFunc (a "__libc_early_init") (a "export") RVoid [(W, (a "v0"))] [(mkBlock (a "start") [] [(Call CVoid (Global (a "__GI___ctype_init")) []);
      (Let (a "v2") P Copy [(Global (a "__libc_single_threaded"))]);
      (Let (a "v3") W (Ext Ub) [(t "v0")]);
      (Let (a "v4") W (Ext Sb) [(t "v3")]);
      (Let (a "chk0") A (Check 0 1 Write 1) [(t "v2")]);
      (RawStore Wb 0 (t "v4") (t "chk0"));
      (Let (a "v5") P Copy [(Global (a "__libc_single_threaded_internal"))]);
      (Let (a "v6") P Copy [(Global (a "__libc_initial"))]);
      (Let (a "chk1") A (Check 0 1 Write 1) [(t "v6")]);
      (RawStore Wb 0 (t "v3") (t "chk1"));
      (Let (a "chk2") A (Check 0 1 Write 1) [(t "v5")]);
      (RawStore Wb 0 (t "v4") (t "chk2"));
      (Let (a "iw_1.v0") P (Alloc 8) [(Const 16)]);
      (Call (CResult (a "iw_1.v4") W) (Global (a "__GI___getrlimit")) [(Arg W (Const 3)); (Arg P (t "iw_1.v0"))]);
      (Let (a "iw_1.v5") W (Cmp Ne W) [(t "iw_1.v4"); (Const 0)])] (JBranch (t "iw_1.v5") (To (a "iw_1.L7")) (To (a "iw_1.L6"))));
  (mkBlock (a "iw_1.L6") [] [(Let (a "chk3") A (Check 0 8 Read 1) [(t "iw_1.v0")]);
      (Let (a "iw_1.v8") L (RawLoad LdL 0) [(t "chk3")]);
      (Let (a "iw_1.v11") W (Cmp Eq L) [(t "iw_1.v8"); (Const 18446744073709551615)])] (JGoto (To (a "iw_1.L7"))));
  (mkBlock (a "iw_1.L7") [(Phi (a "iw_1.v13") W [((a "start"), (Const 1)); ((a "iw_1.L6"), (t "iw_1.v11"))])] [] (JBranch (t "iw_1.v13") (To (a "iw_1.L1")) (To (a "iw_1.L2"))));
  (mkBlock (a "iw_1.L1") [] [(Let (a "chk4") A (Check 0 8 Write 1) [(t "iw_1.v0")]);
      (RawStore Wl 0 (Const 2097152) (t "chk4"))] (JGoto (To (a "iw_1.L3"))));
  (mkBlock (a "iw_1.L2") [] [(Let (a "chk5") A (Check 0 8 Read 1) [(t "iw_1.v0")]);
      (Let (a "iw_1.v20") L (RawLoad LdL 0) [(t "chk5")]);
      (Let (a "iw_1.v21") W (Cmp Ult L) [(t "iw_1.v20"); (Const 16384)])] (JBranch (t "iw_1.v21") (To (a "iw_1.L17")) (To (a "iw_1.L3"))));
  (mkBlock (a "iw_1.L17") [] [(Let (a "chk6") A (Renew 0 8 Write 1) [(t "chk5"); (t "iw_1.v0")]);
      (RawStore Wl 0 (Const 16384) (t "chk6"))] (JGoto (To (a "iw_1.L3"))));
  (mkBlock (a "iw_1.L3") [] [(Let (a "iw_1.v23") P Copy [(Global (a "_dl_pagesize"))]);
      (Let (a "chk7") A (Check 0 8 Read 1) [(t "iw_1.v23")]);
      (Let (a "iw_1.v24") L (RawLoad LdL 0) [(t "chk7")]);
      (Let (a "iw_1.v29") L Add [(t "iw_1.v24"); (Const 2048)]);
      (Let (a "chk8") A (Check 0 8 Read 1) [(t "iw_1.v0")]);
      (Let (a "iw_1.v33") L (RawLoad LdL 0) [(t "chk8")]);
      (Let (a "iw_1.v35") W (Cmp Ult L) [(t "iw_1.v33"); (t "iw_1.v29")])] (JBranch (t "iw_1.v35") (To (a "iw_1.L30")) (To (a "iw_1.L32"))));
  (mkBlock (a "iw_1.L30") [] [(Let (a "chk9") A (Renew 0 8 Write 1) [(t "chk8"); (t "iw_1.v0")]);
      (RawStore Wl 0 (t "iw_1.v29") (t "chk9"))] (JGoto (To (a "iw_1.L32"))));
  (mkBlock (a "iw_1.L32") [] [(Let (a "iw_1.v37") L (RawLoad LdL 0) [(t "chk8")]);
      (Let (a "iw_1.v39") L Add [(t "iw_1.v37"); (t "iw_1.v24")]);
      (Let (a "iw_1.v40") L Sub [(t "iw_1.v39"); (Const 1)]);
      (Let (a "iw_1.v42") L Neg [(t "iw_1.v24")]);
      (Let (a "iw_1.v43") L And [(t "iw_1.v40"); (t "iw_1.v42")]);
      (Let (a "chk11") A (Renew 0 8 Write 1) [(t "chk8"); (t "iw_1.v0")]);
      (RawStore Wl 0 (t "iw_1.v43") (t "chk11"));
      (Let (a "iw_1.v44") P Copy [(Global (a "__GI___default_pthread_attr"))]);
      (Flight (a "iw_1.v45") Add [(FAddress (t "iw_1.v44")); (FValue (Const 32))] (LowerOf (t "iw_1.v44")));
      (Let (a "chk12") A (Renew 0 8 Read 1) [(t "chk8"); (t "iw_1.v0")]);
      (Let (a "iw_1.v46") L (RawLoad LdL 0) [(t "chk12")]);
      (Let (a "chk13") A (Check 0 8 Write 1) [(t "iw_1.v45")]);
      (RawStore Wl 0 (t "iw_1.v46") (t "chk13"));
      (Let (a "iw_1.v47") P Copy [(Global (a "__GI___default_pthread_attr"))]);
      (Flight (a "iw_1.v48") Add [(FAddress (t "iw_1.v47")); (FValue (Const 16))] (LowerOf (t "iw_1.v47")));
      (Let (a "iw_1.v49") P Copy [(Global (a "_dl_pagesize"))]);
      (Let (a "chk14") A (Check 0 8 Read 1) [(t "iw_1.v49")]);
      (Let (a "iw_1.v50") L (RawLoad LdL 0) [(t "chk14")]);
      (Let (a "chk15") A (Check 0 8 Write 1) [(t "iw_1.v48")]);
      (RawStore Wl 0 (t "iw_1.v50") (t "chk15"));
      (Call CVoid (Global (a "__pthread_tunables_init")) []);
      (Call CVoid (Global (a "__getrandom_early_init")) [(Arg W (t "v3"))]);
      (Call CVoid (Global (a "__ptmalloc_init")) [])] JRetVoid)].
