(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedFIBlocks260x1 HelloImageTypedFIBlocks260x2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn_glibc_gconv_cache'23find_module_idx : func :=
  mkFunc (a "glibc_gconv_cache#find_module_idx") (a "local") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v11") P Copy [(Global (a "glibc_gconv_cache#gconv_cache"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v11")]);
      (Let (a "v12") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v13") P Copy [(Global (a "glibc_gconv_cache#gconv_cache"))]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v13")]);
      (Let (a "v14") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v16") Add [(FAddress (t "v12")); (FValue (Const 4))] (LowerOf (t "v12")));
      (Let (a "chk2") A (Check 0 2 Read 1) [(t "v16")]);
      (Let (a "v17") W (RawLoad (LdNarrow Uh) 0) [(t "chk2")]);
      (Let (a "v18") L (Ext Uw) [(t "v17")]);
      (Flight (a "v19") Add [(FAddress (t "v14")); (FValue (t "v18"))] (LowerOf (t "v14")));
      (Let (a "v20") P Copy [(Global (a "glibc_gconv_cache#gconv_cache"))]);
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v20")]);
      (Let (a "v21") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "v23") Add [(FAddress (t "v12")); (FValue (Const 6))] (LowerOf (t "v12")));
      (Let (a "chk4") A (HalfCheck Upper 0 2 Read 1) [(t "chk2"); (t "v23")]);
      (Let (a "v24") W (RawLoad (LdNarrow Uh) 0) [(t "chk4")]);
      (Let (a "v25") L (Ext Uw) [(t "v24")]);
      (Flight (a "v26") Add [(FAddress (t "v21")); (FValue (t "v25"))] (LowerOf (t "v21")));
      (Call (CResult (a "v28") L) (Global (a "__hash_string")) [(Arg P (t "v0"))]);
      (Let (a "v29") W Copy [(t "v28")]);
      (Flight (a "v31") Add [(FAddress (t "v12")); (FValue (Const 8))] (LowerOf (t "v12")));
      (Let (a "chk5") A (HalfCheck Upper 0 2 Read 1) [(t "chk2"); (t "v31")]);
      (Let (a "v32") W (RawLoad (LdNarrow Uh) 0) [(t "chk5")]);
      (Let (a "v33") W Urem [(t "v29"); (t "v32")]);
      (Let (a "v34") W Copy [(t "v28")]);
      (Let (a "v37") W (RawLoad (LdNarrow Uh) 0) [(t "chk5")]);
      (Let (a "v38") W Sub [(t "v37"); (Const 2)]);
      (Let (a "v39") W Urem [(t "v34"); (t "v38")]);
      (Let (a "v40") W Add [(t "v39"); (Const 1)]);
      (Let (a "v41") P Copy [(Global (a "glibc_gconv_cache#cache_size"))]);
      (Let (a "chk7") A (Check 0 8 Read 1) [(t "v41")]);
      (Let (a "v42") L (RawLoad LdL 0) [(t "chk7")]);
      (Let (a "chk8") A (Renew 0 2 Read 1) [(t "chk2"); (t "v16")]);
      (Let (a "v45") W (RawLoad (LdNarrow Uh) 0) [(t "chk8")]);
      (Let (a "v46") L (Ext Uw) [(t "v45")]);
      (Let (a "v47") L Sub [(t "v42"); (t "v46")])] (JGoto (To (a "L48"))));
  (mkBlock (a "L48") [(Phi (a "pr.1") W [((a "start"), (t "v33")); ((a "L59"), (t "v100")); ((a "L95"), (t "v109"))])] [(Let (a "v53") L (Ext Uw) [(t "pr.1")]);
      (Let (a "v54") L Shl [(t "v53"); (Const 2)]);
      (Flight (a "v55") Add [(FAddress (t "v26")); (FValue (t "v54"))] (LowerOf (t "v26")));
      (Let (a "chk9") A (Check 0 2 Read 1) [(t "v55")]);
      (Let (a "v56") W (RawLoad (LdNarrow Uh) 0) [(t "chk9")]);
      (Let (a "v57") W (Cmp Ne W) [(t "v56"); (Const 0)])] (JBranch (t "v57") (To (a "L49")) (To (a "L50"))));
  (mkBlock (a "L49") [] [(Let (a "v66") W (RawLoad (LdNarrow Uh) 0) [(t "chk9")]);
      (Let (a "v67") W Copy [(t "v47")]);
      (Let (a "v68") W (Cmp Ult W) [(t "v66"); (t "v67")])] (JBranch (t "v68") (To (a "L69")) (To (a "L70"))));
  (mkBlock (a "L69") [] [(Let (a "v78") W (RawLoad (LdNarrow Uh) 0) [(t "chk9")]);
      (Let (a "v79") L (Ext Uw) [(t "v78")]);
      (Flight (a "v80") Add [(FAddress (t "v19")); (FValue (t "v79"))] (LowerOf (t "v19")));
      (Call (CResult (a "v81") W) (Global (a "__GI_strcmp")) [(Arg P (t "v0")); (Arg P (t "v80"))]);
      (Let (a "v82") W (Cmp Eq W) [(t "v81"); (Const 0)])] (JGoto (To (a "L70"))));
  (mkBlock (a "L70") [(Phi (a "v84") W [((a "L49"), (Const 0)); ((a "L69"), (t "v82"))])] [] (JBranch (t "v84") (To (a "L58")) (To (a "L59"))));
  (mkBlock (a "L58") [] [(Flight (a "v91") Add [(FAddress (t "v55")); (FValue (Const 2))] (LowerOf (t "v55")));
      (Let (a "chk12") A (HalfCheck Upper 0 2 Read 1) [(t "chk9"); (t "v91")]);
      (Let (a "v92") W (RawLoad (LdNarrow Uh) 0) [(t "chk12")]);
      (Let (a "v93") L (Ext Uw) [(t "v92")]);
      (Let (a "chk13") A (Check 0 8 Write 1) [(t "v2")]);
      (RawStore Wl 0 (t "v93") (t "chk13"))] (JRet (Const 0)));
  (mkBlock (a "L59") [] [(Let (a "v100") W Add [(t "pr.1"); (t "v40")]);
      (Flight (a "v102") Add [(FAddress (t "v12")); (FValue (Const 8))] (LowerOf (t "v12")));
      (Let (a "chk14") A (Renew 0 2 Read 1) [(t "chk5"); (t "v102")]);
      (Let (a "v103") W (RawLoad (LdNarrow Uh) 0) [(t "chk14")]);
      (Let (a "v104") W (Cmp Uge W) [(t "v100"); (t "v103")])] (JBranch (t "v104") (To (a "L95")) (Poll (a "L48"))));
  (mkBlock (a "L95") [] [(Flight (a "v107") Add [(FAddress (t "v12")); (FValue (Const 8))] (LowerOf (t "v12")));
      (Let (a "v108") W (RawLoad (LdNarrow Uh) 0) [(t "chk14")]);
      (Let (a "v109") W Sub [(t "v100"); (t "v108")])] (JGoto (Poll (a "L48"))));
  (mkBlock (a "L50") [] [] (JRet (Const 4294967295)))].

Definition hello_image_fn_glibc_gconv_cache'23find_module : func :=
  mkFunc (a "glibc_gconv_cache#find_module") (a "local") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Call (CResult (a "v8") L) (Global (a "__GI_strlen")) [(Arg P (t "v0"))]);
      (Call (CResult (a "v11") L) (Global (a "__GI_strlen")) [(Arg P (t "v2"))]);
      (Let (a "v12") L Add [(t "v11"); (Const 1)]);
      (Let (a "v15") L Add [(t "v8"); (t "v12")]);
      (Let (a "v16") P (Alloc 4) [(t "v15")]);
      (Call (CResult (a "v20") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v16")); (Arg P (t "v0")); (Arg L (t "v8"))]);
      (Call (CResult (a "v23") P) (Global (a "__GI_memcpy")) [(Arg P (t "v20")); (Arg P (t "v2")); (Arg L (t "v12"))]);
      (Call (CResult (a "v25") P) (Global (a "__gconv_find_shlib")) [(Arg P (t "v16"))]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v4")]);
      (RawStorePointer 0 (t "v25") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk1") A (Renew 0 8 Read 8) [(t "chk0"); (t "v4")]);
      (Let (a "v30") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "v31") L Ptoi [(t "v30")]);
      (Let (a "v32") L Ptoi [(Const 0)]);
      (Let (a "v33") W (Cmp Ne L) [(t "v31"); (t "v32")])] (JBranch (t "v33") (To (a "L26")) (To (a "L28"))));
  (mkBlock (a "L26") [] [(Flight (a "v35") Add [(FAddress (t "v4")); (FValue (Const 8))] (LowerOf (t "v4")));
      (Let (a "chk2") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v35")]);
      (RawStorePointer 0 (Const 0) (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v37") Add [(FAddress (t "v4")); (FValue (Const 40))] (LowerOf (t "v4")));
      (Let (a "chk3") A (Renew 0 8 Read 8) [(t "chk0"); (t "v4")]);
      (Let (a "v39") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "v40") Add [(FAddress (t "v39")); (FValue (Const 24))] (LowerOf (t "v39")));
      (Let (a "chk4") A (Check 0 8 Read 8) [(t "v40")]);
      (Let (a "v41") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "chk5") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v37")]);
      (RawStorePointer 0 (t "v41") (t "chk5") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v43") Add [(FAddress (t "v4")); (FValue (Const 56))] (LowerOf (t "v4")));
      (Let (a "chk6") A (Renew 0 8 Read 8) [(t "chk0"); (t "v4")]);
      (Let (a "v45") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v46") Add [(FAddress (t "v45")); (FValue (Const 32))] (LowerOf (t "v45")));
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v46")]);
      (Let (a "v47") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Let (a "chk8") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v43")]);
      (RawStorePointer 0 (t "v47") (t "chk8") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v49") Add [(FAddress (t "v4")); (FValue (Const 64))] (LowerOf (t "v4")));
      (Let (a "chk9") A (Renew 0 8 Read 8) [(t "chk0"); (t "v4")]);
      (Let (a "v51") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Flight (a "v52") Add [(FAddress (t "v51")); (FValue (Const 40))] (LowerOf (t "v51")));
      (Let (a "chk10") A (Check 0 8 Read 8) [(t "v52")]);
      (Let (a "v53") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")]);
      (Let (a "chk11") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v49")]);
      (RawStorePointer 0 (t "v53") (t "chk11") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v55") Add [(FAddress (t "v4")); (FValue (Const 48))] (LowerOf (t "v4")));
      (Let (a "chk12") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v55")]);
      (RawStorePointer 0 (Const 0) (t "chk12") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v57") Add [(FAddress (t "v4")); (FValue (Const 96))] (LowerOf (t "v4")));
      (Let (a "chk13") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v57")]);
      (RawStorePointer 0 (Const 0) (t "chk13") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk14") A (Renew 0 8 Read 8) [(t "chk8"); (t "v43")]);
      (Let (a "v61") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Let (a "v67") L Ptoi [(t "v61")]);
      (Let (a "v69") W (Cmp Ne L) [(t "v67"); (t "v32")])] (JBranch (t "v69") (To (a "iw_1.join")) (To (a "L28"))));
  (mkBlock (a "iw_1.join") [] [(Let (a "chk15") F CheckFunction [(t "v61")]);
      (RawCall (CResult (a "v73") W) (t "chk15") [(Arg P (t "v4"))]);
      (Flight (a "v75") Add [(FAddress (t "v4")); (FValue (Const 48))] (LowerOf (t "v4")));
      (Let (a "chk16") A (Renew 0 8 Read 8) [(t "chk12"); (t "v75")]);
      (Let (a "v76") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk16")])] (JGoto (To (a "L28"))));
  (mkBlock (a "L28") [(Phi (a "pr.1") W [((a "iw_1.join"), (t "v73")); ((a "L26"), (Const 0)); ((a "start"), (Const 1))])] [] (JRet (t "pr.1")))].

Definition hello_image_fn_glibc_gconv_db'23find_derivation : func :=
  mkFunc (a "glibc_gconv_db#find_derivation") (a "local") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6")); (P, (a "v8")); (P, (a "v10"))] (hello_image_fn_glibc_gconv_db'23find_derivation'blocks1 ++ hello_image_fn_glibc_gconv_db'23find_derivation'blocks2).

Definition hello_image_fn_glibc_vfprintf_internal'23__find_specmb'2egnu_inline : func :=
  mkFunc (a "glibc_vfprintf_internal#__find_specmb.gnu_inline") (a "local") (RClass P) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") P) (Global (a "__GI___strchrnul")) [(Arg P (t "v0")); (Arg W (Const 37))])] (JRet (t "v3")))].

Definition hello_image_fn_glibc_vfwprintf_internal'23__find_specwc'2egnu_inline : func :=
  mkFunc (a "glibc_vfwprintf_internal#__find_specwc.gnu_inline") (a "local") (RClass P) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") P) (Global (a "__wcschrnul")) [(Arg P (t "v0")); (Arg W (Const 37))])] (JRet (t "v3")))].
