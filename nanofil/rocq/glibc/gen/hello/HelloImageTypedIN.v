(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedINBlocks1663x1 HelloImageTypedINBlocks1663x2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___init_misc : func :=
  mkFunc (a "__init_misc") (a "export") RVoid [(W, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v10") L Ptoi [(t "v2")]);
      (Let (a "v11") W (Cmp Ne L) [(t "v10"); (Const 0)])] (JBranch (t "v11") (To (a "L12")) (To (a "L13"))));
  (mkBlock (a "L12") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v16") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v17") L Ptoi [(t "v16")]);
      (Let (a "v18") W (Cmp Ne L) [(t "v17"); (Const 0)])] (JGoto (To (a "L13"))));
  (mkBlock (a "L13") [(Phi (a "v20") W [((a "start"), (Const 0)); ((a "L12"), (t "v18"))])] [] (JBranch (t "v20") (To (a "L6")) (To (a "L8"))));
  (mkBlock (a "L6") [] [(Let (a "chk1") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v24") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Call (CResult (a "v25") P) (Global (a "__GI_strrchr")) [(Arg P (t "v24")); (Arg W (Const 47))]);
      (Let (a "v30") L Ptoi [(t "v25")]);
      (Let (a "v31") L Ptoi [(Const 0)]);
      (Let (a "v32") W (Cmp Eq L) [(t "v30"); (t "v31")])] (JBranch (t "v32") (To (a "L26")) (To (a "L27"))));
  (mkBlock (a "L26") [] [(Let (a "v33") P Copy [(Global (a "__progname"))]);
      (Let (a "chk2") A (Renew 0 8 Read 8) [(t "chk1"); (t "v2")]);
      (Let (a "v36") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "chk3") A (Check 0 8 Write 8) [(t "v33")]);
      (RawStorePointer 0 (t "v36") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L28"))));
  (mkBlock (a "L27") [] [(Let (a "v37") P Copy [(Global (a "__progname"))]);
      (Flight (a "v39") Add [(FAddress (t "v25")); (FValue (Const 1))] (LowerOf (t "v25")));
      (Let (a "chk4") A (Check 0 8 Write 8) [(t "v37")]);
      (RawStorePointer 0 (t "v39") (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L28"))));
  (mkBlock (a "L28") [] [(Let (a "v40") P Copy [(Global (a "__progname_full"))]);
      (Let (a "chk5") A (Renew 0 8 Read 8) [(t "chk1"); (t "v2")]);
      (Let (a "v43") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk6") A (Check 0 8 Write 8) [(t "v40")]);
      (RawStorePointer 0 (t "v43") (t "chk6") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L8"))));
  (mkBlock (a "L8") [] [] JRetVoid)].

Definition hello_image_fn___internal_atexit : func :=
  mkFunc (a "__internal_atexit") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v13") L Ptoi [(t "v0")]);
      (Let (a "v14") L Ptoi [(Const 0)]);
      (Let (a "v15") W (Cmp Ne L) [(t "v13"); (t "v14")])] (JBranch (t "v15") (To (a "L11")) (To (a "L10"))));
  (mkBlock (a "L10") [] [(Let (a "v16") P Copy [(Global (a "glibc_cxa_atexit#str.233"))]);
      (Let (a "v17") P Copy [(Global (a "glibc_cxa_atexit#str.234"))]);
      (Let (a "v18") P Copy [(Global (a "glibc_cxa_atexit#str.235"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v16")); (Arg P (t "v17")); (Arg W (Const 41)); (Arg P (t "v18"))])] (JGoto (To (a "L11"))));
  (mkBlock (a "L11") [] [(Let (a "v20") P Copy [(Global (a "__exit_funcs_lock"))]);
      (Let (a "chk0") A (Check 0 4 Write 4) [(t "v20")]);
      (Let (a "v27") W (RawCas (CasNarrow Sw) 0) [(t "chk0"); (Const 0); (Const 1)]);
      (Let (a "v28") W (Cmp Eq W) [(t "v27"); (Const 0)])] (JBranch (t "v28") (To (a "L30")) (To (a "L29"))));
  (mkBlock (a "L29") [] [] (JGoto (To (a "L30"))));
  (mkBlock (a "L30") [] [(Let (a "v31") W (Cmp Ne W) [(t "v27"); (Const 0)])] (JBranch (t "v31") (To (a "L34")) (To (a "L23"))));
  (mkBlock (a "L34") [] [(Call CVoid (Global (a "__GI___lll_lock_wait_private")) [(Arg P (t "v20"))])] (JGoto (To (a "L23"))));
  (mkBlock (a "L23") [] [(Call (CResult (a "v45") P) (Global (a "__new_exitfn")) [(Arg P (t "v6"))]);
      (Let (a "v50") L Ptoi [(t "v45")]);
      (Let (a "v52") W (Cmp Eq L) [(t "v50"); (t "v14")])] (JBranch (t "v52") (To (a "L46")) (To (a "L48"))));
  (mkBlock (a "L46") [] [(Let (a "v54") P Copy [(Global (a "__exit_funcs_lock"))]);
      (Let (a "chk1") A (Check 0 4 Read 1) [(t "v54")]);
      (Let (a "v58") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")])] (JGoto (To (a "L59"))));
  (mkBlock (a "L59") [(Phi (a "v61") W [((a "L46"), (t "v58")); ((a "L59"), (t "v62"))])] [(Let (a "chk2") A (HalfCheck Lower 0 4 Write 4) [(t "chk1"); (t "v54")]);
      (Let (a "v62") W (RawCas (CasNarrow Sw) 0) [(t "chk2"); (t "v61"); (Const 0)]);
      (Let (a "v63") W (Cmp Eq W) [(t "v62"); (t "v61")])] (JBranch (t "v63") (To (a "L60")) (Poll (a "L59"))));
  (mkBlock (a "L60") [] [(Let (a "v68") W (Cmp Sgt W) [(t "v61"); (Const 1)])] (JBranch (t "v68") (To (a "L71")) (To (a "L66"))));
  (mkBlock (a "L71") [] [(Call CVoid (Global (a "__GI___lll_lock_wake_private")) [(Arg P (t "v54"))])] (JGoto (To (a "L66"))));
  (mkBlock (a "L66") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L48") [] [(Flight (a "v86") Add [(FAddress (t "v45")); (FValue (Const 8))] (LowerOf (t "v45")));
      (Let (a "chk3") A (Check 0 8 Write 8) [(t "v86")]);
      (RawStorePointer 0 (t "v0") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v90") Add [(FAddress (t "v86")); (FValue (Const 8))] (LowerOf (t "v86")));
      (Let (a "chk4") A (HalfCheck Upper 0 8 Write 8) [(t "chk3"); (t "v90")]);
      (RawStorePointer 0 (t "v2") (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v94") Add [(FAddress (t "v86")); (FValue (Const 16))] (LowerOf (t "v86")));
      (Let (a "chk5") A (HalfCheck Upper 0 8 Write 8) [(t "chk3"); (t "v94")]);
      (RawStorePointer 0 (t "v4") (t "chk5") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk6") A (HalfCheck Lower 0 8 Write 1) [(t "chk3"); (t "v45")]);
      (RawStore Wl 0 (Const 4) (t "chk6"));
      (Let (a "v98") P Copy [(Global (a "__exit_funcs_lock"))]);
      (Let (a "chk7") A (Check 0 4 Read 1) [(t "v98")]);
      (Let (a "v102") W (RawLoad (LdNarrow Sw) 0) [(t "chk7")])] (JGoto (To (a "L103"))));
  (mkBlock (a "L103") [(Phi (a "v105") W [((a "L48"), (t "v102")); ((a "L103"), (t "v106"))])] [(Let (a "chk8") A (HalfCheck Lower 0 4 Write 4) [(t "chk7"); (t "v98")]);
      (Let (a "v106") W (RawCas (CasNarrow Sw) 0) [(t "chk8"); (t "v105"); (Const 0)]);
      (Let (a "v107") W (Cmp Eq W) [(t "v106"); (t "v105")])] (JBranch (t "v107") (To (a "L104")) (Poll (a "L103"))));
  (mkBlock (a "L104") [] [(Let (a "v112") W (Cmp Sgt W) [(t "v105"); (Const 1)])] (JBranch (t "v112") (To (a "L115")) (To (a "L110"))));
  (mkBlock (a "L115") [] [(Call CVoid (Global (a "__GI___lll_lock_wake_private")) [(Arg P (t "v98"))])] (JGoto (To (a "L110"))));
  (mkBlock (a "L110") [] [] (JRet (Const 0)))].

Definition hello_image_fn_glibc_libc_start'23intel_02_known_compare : func :=
  mkFunc (a "glibc_libc_start#intel_02_known_compare") (a "local") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 1 Read 1) [(t "v0")]);
      (Let (a "v12") W (RawLoad (LdNarrow Ub) 0) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 1 Read 1) [(t "v2")]);
      (Let (a "v14") W (RawLoad (LdNarrow Ub) 0) [(t "chk1")]);
      (Let (a "v15") W (Cmp Eq W) [(t "v12"); (t "v14")])] (JBranch (t "v15") (To (a "L8")) (To (a "L10"))));
  (mkBlock (a "L8") [] [] (JRet (Const 0)));
  (mkBlock (a "L10") [] [(Let (a "v21") W (RawLoad (LdNarrow Ub) 0) [(t "chk0")]);
      (Let (a "v23") W (RawLoad (LdNarrow Ub) 0) [(t "chk1")]);
      (Let (a "v24") W (Cmp Slt W) [(t "v21"); (t "v23")])] (JBranch (t "v24") (To (a "L19")) (To (a "L18"))));
  (mkBlock (a "L18") [] [] (JGoto (To (a "L19"))));
  (mkBlock (a "L19") [(Phi (a "v26") W [((a "L18"), (Const 1)); ((a "L10"), (Const 4294967295))])] [] (JRet (t "v26")))].

Definition hello_image_fn_glibc_libc_start'23intel_check_word : func :=
  mkFunc (a "glibc_libc_start#intel_check_word") (a "local") (RClass L) [(W, (a "v0")); (W, (a "v2")); (P, (a "v4")); (P, (a "v6")); (P, (a "v8")); (P, (a "v10"))] (app [(mkBlock (a "start") [] [(Let (a "v51") P (Alloc 4) [(Const 4)]);
      (Let (a "v52") P (Alloc 4) [(Const 4)]);
      (Let (a "v53") P (Alloc 4) [(Const 4)]);
      (Let (a "v54") P (Alloc 4) [(Const 4)]);
      (Let (a "v334") P (Alloc 4) [(Const 8)]);
      (Let (a "v16") W And [(t "v2"); (Const 2147483648)]);
      (Let (a "v17") W (Cmp Ne W) [(t "v16"); (Const 0)])] (JBranch (t "v17") (To (a "L12")) (To (a "L14"))));
  (mkBlock (a "L12") [] [] (JRet (Const 0)));
  (mkBlock (a "L14") [] [(Let (a "v21") W Sub [(t "v0"); (Const 185)]);
      (Let (a "v22") W Div [(t "v21"); (Const 3)]);
      (Let (a "v23") W Mul [(t "v22"); (Const 3)])] (JGoto (To (a "L24"))));
  (mkBlock (a "L24") [(Phi (a "pr.6") W [((a "L14"), (t "v23")); ((a "L34"), (t "pr.9"))]); (Phi (a "pr.5") W [((a "L14"), (t "v2")); ((a "L34"), (t "v405"))]); (Phi (a "pr.1") W [((a "L14"), (t "v0")); ((a "L34"), (t "pr.4"))])] [(Let (a "v28") W (Cmp Ne W) [(t "pr.5"); (Const 0)])] (JBranch (t "v28") (To (a "L25")) (To (a "L26"))));
  (mkBlock (a "L25") [] [(Let (a "v31") W And [(t "pr.5"); (Const 255)]);
      (Let (a "v36") W (Cmp Eq W) [(t "v31"); (Const 64)])] (JBranch (t "v36") (To (a "L32")) (To (a "L33"))));
  (mkBlock (a "L32") [] [(Let (a "chk0") A (Check 0 1 Write 1) [(t "v6")]);
      (RawStore Wb 0 (Const 1) (t "chk0"));
      (Let (a "v44") W (Cmp Eq W) [(t "pr.6"); (Const 9)])] (JBranch (t "v44") (To (a "L26")) (To (a "L34"))));
  (mkBlock (a "L33") [] [(Let (a "v50") W (Cmp Eq W) [(t "v31"); (Const 255)])] (JBranch (t "v50") (To (a "L56")) (To (a "L47"))));
  (mkBlock (a "L56") [(Phi (a "pr.10") W [((a "L169"), (t "v294")); ((a "L33"), (Const 0))])] [(Flight (a "v64") Add [(FAddress (t "v10")); (FValue (Const 1))] (LowerOf (t "v10")));
      (Let (a "chk1") A (Check 0 1 Read 1) [(t "v64")]);
      (Let (a "v65") W (RawLoad (LdNarrow Ub) 0) [(t "chk1")]);
      (Let (a "v66") W (Cmp Ult W) [(t "pr.10"); (t "v65")])] (JBranch (t "v66") (To (a "L59")) (To (a "L60"))));
  (mkBlock (a "L59") [] [(Flight (a "v68") Add [(FAddress (t "v10")); (FValue (Const 20))] (LowerOf (t "v10")));
      (Let (a "v70") L (Ext Uw) [(t "pr.10")]);
      (Let (a "v71") L Shl [(t "v70"); (Const 4)]);
      (Flight (a "v72") Add [(FAddress (t "v68")); (FValue (t "v71"))] (LowerOf (t "v68")));
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "v72")]);
      (Let (a "v74") W (RawLoad (LdNarrow Uw) 0) [(t "chk2")]);
      (Let (a "chk3") A (Check 0 4 Write 1) [(t "v51")]);
      (RawStore Ww 0 (t "v74") (t "chk3"));
      (Flight (a "v81") Add [(FAddress (t "v72")); (FValue (Const 4))] (LowerOf (t "v72")));
      (Let (a "chk4") A (HalfCheck Upper 0 4 Read 1) [(t "chk2"); (t "v81")]);
      (Let (a "v82") W (RawLoad (LdNarrow Uw) 0) [(t "chk4")]);
      (Let (a "chk5") A (Check 0 4 Write 1) [(t "v52")]);
      (RawStore Ww 0 (t "v82") (t "chk5"));
      (Flight (a "v89") Add [(FAddress (t "v72")); (FValue (Const 8))] (LowerOf (t "v72")));
      (Let (a "chk6") A (HalfCheck Upper 0 4 Read 1) [(t "chk2"); (t "v89")]);
      (Let (a "v90") W (RawLoad (LdNarrow Uw) 0) [(t "chk6")]);
      (Let (a "chk7") A (Check 0 4 Write 1) [(t "v53")]);
      (RawStore Ww 0 (t "v90") (t "chk7"));
      (Flight (a "v97") Add [(FAddress (t "v72")); (FValue (Const 12))] (LowerOf (t "v72")));
      (Let (a "chk8") A (HalfCheck Upper 0 4 Read 1) [(t "chk2"); (t "v97")]);
      (Let (a "v98") W (RawLoad (LdNarrow Uw) 0) [(t "chk8")]);
      (Let (a "chk9") A (Check 0 4 Write 1) [(t "v54")]);
      (RawStore Ww 0 (t "v98") (t "chk9"))] (JGoto (To (a "L61"))));
  (mkBlock (a "L60") [] [(Flight (a "v104") Add [(FAddress (t "v10")); (FValue (Const 1))] (LowerOf (t "v10")));
      (Let (a "v105") W (RawLoad (LdNarrow Ub) 0) [(t "chk1")]);
      (Let (a "v106") W (Cmp Eq W) [(t "pr.10"); (t "v105")])] (JBranch (t "v106") (To (a "L107")) (To (a "L108"))));
  (mkBlock (a "L107") [] [(Let (a "v111") L (Ext Uw) [(t "pr.10")]);
      (Let (a "v112") W (Cmp Ult L) [(t "v111"); (Const 16)])] (JGoto (To (a "L108"))));
  (mkBlock (a "L108") [(Phi (a "v114") W [((a "L60"), (Const 0)); ((a "L107"), (t "v112"))])] [] (JBranch (t "v114") (To (a "L99")) (To (a "L100"))));
  (mkBlock (a "L99") [] [(Call CVoid (Global (a "zcpuid_count")) [(Arg W (Const 4)); (Arg W (t "pr.10")); (Arg P (t "v51")); (Arg P (t "v52")); (Arg P (t "v53")); (Arg P (t "v54"))]);
      (Flight (a "v117") Add [(FAddress (t "v10")); (FValue (Const 20))] (LowerOf (t "v10")));
      (Let (a "v119") L (Ext Uw) [(t "pr.10")]);
      (Let (a "v120") L Shl [(t "v119"); (Const 4)]);
      (Flight (a "v121") Add [(FAddress (t "v117")); (FValue (t "v120"))] (LowerOf (t "v117")));
      (Let (a "chk11") A (Check 0 4 Read 1) [(t "v51")]);
      (Let (a "v123") W (RawLoad (LdNarrow Uw) 0) [(t "chk11")]);
      (Let (a "chk12") A (Check 0 4 Write 1) [(t "v121")]);
      (RawStore Ww 0 (t "v123") (t "chk12"));
      (Flight (a "v130") Add [(FAddress (t "v121")); (FValue (Const 4))] (LowerOf (t "v121")));
      (Let (a "chk13") A (Check 0 4 Read 1) [(t "v52")]);
      (Let (a "v131") W (RawLoad (LdNarrow Uw) 0) [(t "chk13")]);
      (Let (a "chk14") A (HalfCheck Upper 0 4 Write 1) [(t "chk12"); (t "v130")]);
      (RawStore Ww 0 (t "v131") (t "chk14"));
      (Flight (a "v138") Add [(FAddress (t "v121")); (FValue (Const 8))] (LowerOf (t "v121")));
      (Let (a "chk15") A (Check 0 4 Read 1) [(t "v53")]);
      (Let (a "v139") W (RawLoad (LdNarrow Uw) 0) [(t "chk15")]);
      (Let (a "chk16") A (HalfCheck Upper 0 4 Write 1) [(t "chk12"); (t "v138")]);
      (RawStore Ww 0 (t "v139") (t "chk16"));
      (Flight (a "v146") Add [(FAddress (t "v121")); (FValue (Const 12))] (LowerOf (t "v121")));
      (Let (a "chk17") A (Check 0 4 Read 1) [(t "v54")]);
      (Let (a "v147") W (RawLoad (LdNarrow Uw) 0) [(t "chk17")]);
      (Let (a "chk18") A (HalfCheck Upper 0 4 Write 1) [(t "chk12"); (t "v146")]);
      (RawStore Ww 0 (t "v147") (t "chk18"));
      (Flight (a "v149") Add [(FAddress (t "v10")); (FValue (Const 1))] (LowerOf (t "v10")));
      (Let (a "chk19") A (Renew 0 1 Read 1) [(t "chk1"); (t "v149")]);
      (Let (a "v150") W (RawLoad (LdNarrow Ub) 0) [(t "chk19")]);
      (Let (a "v151") W Add [(t "v150"); (Const 1)]);
      (Let (a "v152") W (Ext Ub) [(t "v151")]);
      (Let (a "chk20") A (Renew 0 1 Write 1) [(t "chk1"); (t "v149")]);
      (RawStore Wb 0 (t "v152") (t "chk20"))] (JGoto (To (a "L61"))));
  (mkBlock (a "L100") [] [(Call CVoid (Global (a "zcpuid_count")) [(Arg W (Const 4)); (Arg W (t "pr.10")); (Arg P (t "v51")); (Arg P (t "v52")); (Arg P (t "v53")); (Arg P (t "v54"))])] (JGoto (To (a "L61"))));
  (mkBlock (a "L61") [] [(Let (a "chk21") A (Check 0 4 Read 1) [(t "v51")]);
      (Let (a "v155") W (RawLoad (LdNarrow Uw) 0) [(t "chk21")]);
      (Let (a "v156") W And [(t "v155"); (Const 31)]);
      (Let (a "v161") W (Cmp Eq W) [(t "v156"); (Const 0)])] (JBranch (t "v161") (To (a "L58")) (To (a "L159"))));
  (mkBlock (a "L159") [] [(Let (a "v164") W (RawLoad (LdNarrow Uw) 0) [(t "chk21")]);
      (Let (a "v165") W Shr [(t "v164"); (Const 5)]);
      (Let (a "v166") W And [(t "v165"); (Const 7)]);
      (Let (a "v171") W (Cmp Eq W) [(t "v166"); (Const 1)])] (JBranch (t "v171") (To (a "L172")) (To (a "L173"))));
  (mkBlock (a "L172") [] [(Let (a "v175") W (Cmp Eq W) [(t "v156"); (Const 1)])] (JGoto (To (a "L173"))));
  (mkBlock (a "L173") [(Phi (a "v177") W [((a "L159"), (Const 0)); ((a "L172"), (t "v175"))])] [] (JBranch (t "v177") (To (a "L178")) (To (a "L179"))));
  (mkBlock (a "L178") [] [(Let (a "v182") W (Cmp Eq W) [(t "pr.6"); (Const 3)])] (JGoto (To (a "L179"))));
  (mkBlock (a "L179") [(Phi (a "v184") W [((a "L173"), (Const 0)); ((a "L178"), (t "v182"))])] [] (JBranch (t "v184") (To (a "L186")) (To (a "L185"))));
  (mkBlock (a "L185") [] [] (JBranch (t "v171") (To (a "L189")) (To (a "L190"))));
  (mkBlock (a "L189") [] [(Let (a "v192") W (Cmp Eq W) [(t "v156"); (Const 2)])] (JGoto (To (a "L190"))));
  (mkBlock (a "L190") [(Phi (a "v194") W [((a "L185"), (Const 0)); ((a "L189"), (t "v192"))])] [] (JBranch (t "v194") (To (a "L195")) (To (a "L186"))));
  (mkBlock (a "L195") [] [(Let (a "v199") W (Cmp Eq W) [(t "pr.6"); (Const 0)])] (JGoto (To (a "L186"))));
  (mkBlock (a "L186") [(Phi (a "v203") W [((a "L179"), (Const 1)); ((a "L190"), (Const 0)); ((a "L195"), (t "v199"))])] [] (JBranch (t "v203") (To (a "L205")) (To (a "L204"))));
  (mkBlock (a "L204") [] [(Let (a "v207") W (Cmp Eq W) [(t "v166"); (Const 2)])] (JBranch (t "v207") (To (a "L208")) (To (a "L205"))));
  (mkBlock (a "L208") [] [(Let (a "v212") W (Cmp Eq W) [(t "pr.6"); (Const 6)])] (JGoto (To (a "L205"))));
  (mkBlock (a "L205") [(Phi (a "v216") W [((a "L186"), (Const 1)); ((a "L204"), (Const 0)); ((a "L208"), (t "v212"))])] [] (JBranch (t "v216") (To (a "L218")) (To (a "L217"))));
  (mkBlock (a "L217") [] [(Let (a "v220") W (Cmp Eq W) [(t "v166"); (Const 3)])] (JBranch (t "v220") (To (a "L221")) (To (a "L218"))));
  (mkBlock (a "L221") [] [(Let (a "v225") W (Cmp Eq W) [(t "pr.6"); (Const 9)])] (JGoto (To (a "L218"))));
  (mkBlock (a "L218") [(Phi (a "v229") W [((a "L205"), (Const 1)); ((a "L217"), (Const 0)); ((a "L221"), (t "v225"))])] [] (JBranch (t "v229") (To (a "L231")) (To (a "L230"))));
  (mkBlock (a "L230") [] [(Let (a "v233") W (Cmp Eq W) [(t "v166"); (Const 4)])] (JBranch (t "v233") (To (a "L234")) (To (a "L231"))));
  (mkBlock (a "L234") [] [(Let (a "v238") W (Cmp Eq W) [(t "pr.6"); (Const 12)])] (JGoto (To (a "L231"))));
  (mkBlock (a "L231") [(Phi (a "v242") W [((a "L218"), (Const 1)); ((a "L230"), (Const 0)); ((a "L234"), (t "v238"))])] [] (JBranch (t "v242") (To (a "L167")) (To (a "L169"))))] [(mkBlock (a "L167") [] [(Let (a "v245") W Sub [(t "pr.1"); (Const 185)]);
      (Let (a "v247") W Sub [(t "v245"); (t "pr.6")]);
      (Let (a "v252") W (Cmp Eq W) [(t "v247"); (Const 0)])] (JBranch (t "v252") (To (a "L248")) (To (a "L250"))));
  (mkBlock (a "L248") [] [(Let (a "chk23") A (Check 0 4 Read 1) [(t "v52")]);
      (Let (a "v253") W (RawLoad (LdNarrow Uw) 0) [(t "chk23")]);
      (Let (a "v254") W Shr [(t "v253"); (Const 22)]);
      (Let (a "v255") W Add [(t "v254"); (Const 1)]);
      (Let (a "v256") W (RawLoad (LdNarrow Uw) 0) [(t "chk23")]);
      (Let (a "v257") W Shr [(t "v256"); (Const 12)]);
      (Let (a "v258") W And [(t "v257"); (Const 1023)]);
      (Let (a "v259") W Add [(t "v258"); (Const 1)]);
      (Let (a "v260") W Mul [(t "v255"); (t "v259")]);
      (Let (a "v261") W (RawLoad (LdNarrow Uw) 0) [(t "chk23")]);
      (Let (a "v262") W And [(t "v261"); (Const 4095)]);
      (Let (a "v263") W Add [(t "v262"); (Const 1)]);
      (Let (a "v264") W Mul [(t "v260"); (t "v263")]);
      (Let (a "chk26") A (Check 0 4 Read 1) [(t "v53")]);
      (Let (a "v265") W (RawLoad (LdNarrow Uw) 0) [(t "chk26")]);
      (Let (a "v266") W Add [(t "v265"); (Const 1)]);
      (Let (a "v267") W Mul [(t "v264"); (t "v266")]);
      (Let (a "v268") L (Ext Uw) [(t "v267")])] (JRet (t "v268")));
  (mkBlock (a "L250") [] [(Let (a "v274") W (Cmp Eq W) [(t "v247"); (Const 1)])] (JBranch (t "v274") (To (a "L270")) (To (a "L272"))));
  (mkBlock (a "L270") [] [(Let (a "chk27") A (Check 0 4 Read 1) [(t "v52")]);
      (Let (a "v275") W (RawLoad (LdNarrow Uw) 0) [(t "chk27")]);
      (Let (a "v276") W Shr [(t "v275"); (Const 22)]);
      (Let (a "v277") W Add [(t "v276"); (Const 1)]);
      (Let (a "v278") L (Ext Uw) [(t "v277")])] (JRet (t "v278")));
  (mkBlock (a "L272") [] [(Let (a "v284") W (Cmp Eq W) [(t "v247"); (Const 2)])] (JBranch (t "v284") (To (a "L282")) (To (a "L281"))));
  (mkBlock (a "L281") [] [(Let (a "v285") P Copy [(Global (a "glibc_libc_start#str.301"))]);
      (Let (a "v286") P Copy [(Global (a "glibc_libc_start#str.302"))]);
      (Let (a "v287") P Copy [(Global (a "glibc_libc_start#str.303"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v285")); (Arg P (t "v286")); (Arg W (Const 217)); (Arg P (t "v287"))])] (JGoto (To (a "L282"))));
  (mkBlock (a "L282") [] [(Let (a "chk28") A (Check 0 4 Read 1) [(t "v52")]);
      (Let (a "v288") W (RawLoad (LdNarrow Uw) 0) [(t "chk28")]);
      (Let (a "v289") W And [(t "v288"); (Const 4095)]);
      (Let (a "v290") W Add [(t "v289"); (Const 1)]);
      (Let (a "v291") L (Ext Uw) [(t "v290")])] (JRet (t "v291")));
  (mkBlock (a "L169") [] [(Let (a "v294") W Add [(t "pr.10"); (Const 1)])] (JGoto (Poll (a "L56"))));
  (mkBlock (a "L58") [] [] (JRet (Const 18446744073709551615)));
  (mkBlock (a "L47") [] [(Let (a "v302") W (Cmp Eq W) [(t "v31"); (Const 73)])] (JBranch (t "v302") (To (a "L303")) (To (a "L304"))));
  (mkBlock (a "L303") [] [(Let (a "v307") W (Cmp Eq W) [(t "pr.6"); (Const 9)])] (JGoto (To (a "L304"))));
  (mkBlock (a "L304") [(Phi (a "v309") W [((a "L47"), (Const 0)); ((a "L303"), (t "v307"))])] [] (JBranch (t "v309") (To (a "L298")) (To (a "L300"))));
  (mkBlock (a "L298") [] [(Flight (a "v312") Add [(FAddress (t "v8")); (FValue (Const 8))] (LowerOf (t "v8")));
      (Let (a "chk29") A (Check 0 4 Read 1) [(t "v312")]);
      (Let (a "v313") W (RawLoad (LdNarrow Uw) 0) [(t "chk29")]);
      (Flight (a "v316") Add [(FAddress (t "v8")); (FValue (Const 12))] (LowerOf (t "v8")));
      (Let (a "chk30") A (HalfCheck Upper 0 4 Read 1) [(t "chk29"); (t "v316")]);
      (Let (a "v317") W (RawLoad (LdNarrow Uw) 0) [(t "chk30")]);
      (Let (a "v322") W (Cmp Eq W) [(t "v313"); (Const 15)])] (JBranch (t "v322") (To (a "L323")) (To (a "L324"))));
  (mkBlock (a "L323") [] [(Let (a "v326") W (Cmp Eq W) [(t "v317"); (Const 6)])] (JGoto (To (a "L324"))));
  (mkBlock (a "L324") [(Phi (a "v328") W [((a "L298"), (Const 0)); ((a "L323"), (t "v326"))])] [] (JBranch (t "v328") (To (a "L318")) (To (a "L300"))));
  (mkBlock (a "L318") [] [(Let (a "v330") W Sub [(t "pr.1"); (Const 194)]);
      (Let (a "v331") W Add [(t "v330"); (Const 191)])] (JGoto (To (a "L300"))));
  (mkBlock (a "L300") [(Phi (a "pr.7") W [((a "L318"), (Const 6)); ((a "L324"), (t "pr.6")); ((a "L304"), (t "pr.6"))]); (Phi (a "pr.2") W [((a "L318"), (t "v331")); ((a "L324"), (t "pr.1")); ((a "L304"), (t "pr.1"))])] [(Let (a "v336") W (Ext Ub) [(t "v31")]);
      (Let (a "chk31") A (Check 0 1 Write 1) [(t "v334")]);
      (RawStore Wb 0 (t "v336") (t "chk31"));
      (Let (a "v337") P Copy [(Global (a "glibc_libc_start#intel_02_known"))]);
      (Let (a "v339") P Copy [(Global (a "glibc_libc_start#intel_02_known_compare"))])] (JGoto (To (a "iw_1.L12"))));
  (mkBlock (a "iw_1.L12") [(Phi (a "iw_1.pr.3") L [((a "iw_1.L36"), (t "iw_1.v45")); ((a "L300"), (Const 68))]); (Phi (a "iw_1.pr.1") P [((a "iw_1.L36"), (t "iw_1.pr.2")); ((a "L300"), (t "v337"))])] [(Let (a "iw_1.v16") W (Cmp Ne L) [(t "iw_1.pr.3"); (Const 0)])] (JBranch (t "iw_1.v16") (To (a "iw_1.L13")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L13") [] [(Let (a "iw_1.v19") L Shr [(t "iw_1.pr.3"); (Const 1)]);
      (Let (a "iw_1.v21") L Shl [(t "iw_1.v19"); (Const 3)]);
      (Flight (a "iw_1.v22") Add [(FAddress (t "iw_1.pr.1")); (FValue (t "iw_1.v21"))] (LowerOf (t "iw_1.pr.1")));
      (Let (a "chk32") F CheckFunction [(t "v339")]);
      (RawCall (CResult (a "iw_1.v26") W) (t "chk32") [(Arg P (t "v334")); (Arg P (t "iw_1.v22"))]);
      (Let (a "iw_1.v31") W (Cmp Eq W) [(t "iw_1.v26"); (Const 0)])] (JBranch (t "iw_1.v31") (To (a "iw_1.join")) (To (a "iw_1.L29"))));
  (mkBlock (a "iw_1.L29") [] [(Let (a "iw_1.v38") W (Cmp Sgt W) [(t "iw_1.v26"); (Const 0)])] (JBranch (t "iw_1.v38") (To (a "iw_1.L34")) (To (a "iw_1.L36"))));
  (mkBlock (a "iw_1.L34") [] [(Flight (a "iw_1.v41") Add [(FAddress (t "iw_1.v22")); (FValue (Const 8))] (LowerOf (t "iw_1.v22")));
      (Let (a "iw_1.v43") L Sub [(t "iw_1.pr.3"); (Const 1)])] (JGoto (To (a "iw_1.L36"))));
  (mkBlock (a "iw_1.L36") [(Phi (a "iw_1.pr.4") L [((a "iw_1.L34"), (t "iw_1.v43")); ((a "iw_1.L29"), (t "iw_1.pr.3"))]); (Phi (a "iw_1.pr.2") P [((a "iw_1.L34"), (t "iw_1.v41")); ((a "iw_1.L29"), (t "iw_1.pr.1"))])] [(Let (a "iw_1.v45") L Shr [(t "iw_1.pr.4"); (Const 1)])] (JGoto (Poll (a "iw_1.L12"))));
  (mkBlock (a "iw_1.join") [(Phi (a "v340") P [((a "iw_1.L13"), (t "iw_1.v22")); ((a "iw_1.L12"), (Const 0))])] [(Let (a "v345") L Ptoi [(t "v340")]);
      (Let (a "v346") L Ptoi [(Const 0)]);
      (Let (a "v347") W (Cmp Ne L) [(t "v345"); (t "v346")])] (JBranch (t "v347") (To (a "L341")) (To (a "L34"))));
  (mkBlock (a "L341") [] [(Flight (a "v352") Add [(FAddress (t "v340")); (FValue (Const 3))] (LowerOf (t "v340")));
      (Let (a "chk33") A (Check 0 1 Read 1) [(t "v352")]);
      (Let (a "v353") W (RawLoad (LdNarrow Ub) 0) [(t "chk33")]);
      (Let (a "v355") W (Cmp Eq W) [(t "v353"); (t "pr.7")])] (JBranch (t "v355") (To (a "L348")) (To (a "L350"))));
  (mkBlock (a "L348") [] [(Let (a "v358") W Sub [(t "pr.2"); (Const 185)]);
      (Let (a "v360") W Sub [(t "v358"); (t "pr.7")]);
      (Let (a "v365") W (Cmp Eq W) [(t "v360"); (Const 0)])] (JBranch (t "v365") (To (a "L361")) (To (a "L363"))));
  (mkBlock (a "L361") [] [(Flight (a "v367") Add [(FAddress (t "v340")); (FValue (Const 4))] (LowerOf (t "v340")));
      (Let (a "chk34") A (HalfCheck Upper 0 4 Read 1) [(t "chk33"); (t "v367")]);
      (Let (a "v368") W (RawLoad (LdNarrow Uw) 0) [(t "chk34")]);
      (Let (a "v369") L (Ext Uw) [(t "v368")])] (JRet (t "v369")));
  (mkBlock (a "L363") [] [(Let (a "v375") W (Cmp Eq W) [(t "v360"); (Const 1)])] (JBranch (t "v375") (To (a "L371")) (To (a "L373"))));
  (mkBlock (a "L371") [] [(Flight (a "v377") Add [(FAddress (t "v340")); (FValue (Const 1))] (LowerOf (t "v340")));
      (Let (a "chk35") A (HalfCheck Lower 0 1 Read 1) [(t "chk33"); (t "v377")]);
      (Let (a "v378") W (RawLoad (LdNarrow Ub) 0) [(t "chk35")]);
      (Let (a "v379") L (Ext Uw) [(t "v378")])] (JRet (t "v379")));
  (mkBlock (a "L373") [] [(Let (a "v385") W (Cmp Eq W) [(t "v360"); (Const 2)])] (JBranch (t "v385") (To (a "L383")) (To (a "L382"))));
  (mkBlock (a "L382") [] [(Let (a "v386") P Copy [(Global (a "glibc_libc_start#str.301"))]);
      (Let (a "v387") P Copy [(Global (a "glibc_libc_start#str.302"))]);
      (Let (a "v388") P Copy [(Global (a "glibc_libc_start#str.303"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v386")); (Arg P (t "v387")); (Arg W (Const 266)); (Arg P (t "v388"))])] (JGoto (To (a "L383"))));
  (mkBlock (a "L383") [] [(Flight (a "v390") Add [(FAddress (t "v340")); (FValue (Const 2))] (LowerOf (t "v340")));
      (Let (a "chk36") A (HalfCheck Lower 0 1 Read 1) [(t "chk33"); (t "v390")]);
      (Let (a "v391") W (RawLoad (LdNarrow Ub) 0) [(t "chk36")]);
      (Let (a "v392") L (Ext Uw) [(t "v391")])] (JRet (t "v392")));
  (mkBlock (a "L350") [] [(Flight (a "v398") Add [(FAddress (t "v340")); (FValue (Const 3))] (LowerOf (t "v340")));
      (Let (a "v399") W (RawLoad (LdNarrow Ub) 0) [(t "chk33")]);
      (Let (a "v401") W (Cmp Eq W) [(t "v399"); (Const 6)])] (JBranch (t "v401") (To (a "L394")) (To (a "L34"))));
  (mkBlock (a "L394") [] [(Let (a "chk38") A (Check 0 1 Write 1) [(t "v4")]);
      (RawStore Wb 0 (Const 1) (t "chk38"))] (JGoto (To (a "L34"))));
  (mkBlock (a "L34") [(Phi (a "pr.9") W [((a "L32"), (t "pr.6")); ((a "L394"), (t "pr.7")); ((a "L350"), (t "pr.7")); ((a "iw_1.join"), (t "pr.7"))]); (Phi (a "pr.4") W [((a "L32"), (t "pr.1")); ((a "L394"), (t "pr.2")); ((a "L350"), (t "pr.2")); ((a "iw_1.join"), (t "pr.2"))])] [(Let (a "v405") W Shr [(t "pr.5"); (Const 8)])] (JGoto (Poll (a "L24"))));
  (mkBlock (a "L26") [] [] (JRet (Const 0)))]).

Definition hello_image_fn_glibc_libc_start'23init_cpu_features : func :=
  mkFunc (a "glibc_libc_start#init_cpu_features") (a "local") RVoid [(P, (a "v0"))] (hello_image_fn_glibc_libc_start'23init_cpu_features'blocks1 ++ hello_image_fn_glibc_libc_start'23init_cpu_features'blocks2).

Definition hello_image_fn_glibc_libc_start'23internal_signal_block_all : func :=
  mkFunc (a "glibc_libc_start#internal_signal_block_all") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P Copy [(Global (a "glibc_libc_start#sigall_set"))]);
      (Call (CResult (a "v4") W) (Global (a "zsys_sigprocmask")) [(Arg W (Const 0)); (Arg P (t "v2")); (Arg P (t "v0"))])] JRetVoid)].

Definition hello_image_fn_glibc_init_first'23_init_first : func :=
  mkFunc (a "glibc_init_first#_init_first") (a "local") RVoid [(W, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v6") P Copy [(Global (a "__libc_argc"))]);
      (Let (a "chk0") A (Check 0 4 Write 1) [(t "v6")]);
      (RawStore Ww 0 (t "v0") (t "chk0"));
      (Let (a "v8") P Copy [(Global (a "__libc_argv"))]);
      (Let (a "chk1") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (t "v2") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v10") P Copy [(Global (a "__environ"))]);
      (Let (a "chk2") A (Check 0 8 Write 8) [(t "v10")]);
      (RawStorePointer 0 (t "v4") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Call CVoid (Global (a "__init_misc")) [(Arg W (t "v0")); (Arg P (t "v2")); (Arg P (t "v4"))])] JRetVoid)].
