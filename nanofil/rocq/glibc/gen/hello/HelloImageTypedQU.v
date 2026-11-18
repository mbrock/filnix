(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedQUBlocks28x1 HelloImageTypedQUBlocks28x2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn_quotearg'23quotearg_buffer_restyled : func :=
  mkFunc (a "quotearg#quotearg_buffer_restyled") (a "local") (RClass L) [(P, (a "v0")); (L, (a "v2")); (P, (a "v4")); (L, (a "v6")); (W, (a "v8")); (W, (a "v10")); (P, (a "v12")); (P, (a "v14")); (P, (a "v16"))] (hello_image_fn_quotearg'23quotearg_buffer_restyled'blocks1 ++ hello_image_fn_quotearg'23quotearg_buffer_restyled'blocks2).

Definition hello_image_fn_quotearg_char_mem : func :=
  mkFunc (a "quotearg_char_mem") (a "export") (RClass P) [(P, (a "v0")); (L, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v6") P (Alloc 8) [(Const 56)]);
      (Let (a "v7") P Copy [(Global (a "quotearg#default_quoting_options"))]);
      (Call CVoid (Global (a "zmemmove")) [(Arg P (t "v6")); (Arg P (t "v7")); (Arg L (Const 56))]);
      (Let (a "v8") W (Ext Sb) [(t "v4")]);
      (Call (CResult (a "v9") W) (Global (a "set_char_quoting")) [(Arg P (t "v6")); (Arg W (t "v8")); (Arg W (Const 1))]);
      (Let (a "iw_1.v47") P (Alloc 8) [(Const 8)]);
      (Call (CResult (a "iw_1.v9") P) (Global (a "__errno_location")) []);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "iw_1.v9")]);
      (Let (a "iw_1.v10") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "iw_1.v12") P Copy [(Global (a "quotearg#slotvec"))]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "iw_1.v12")]);
      (Let (a "iw_1.v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "iw_1.v36") P Copy [(Global (a "quotearg#nslots"))]);
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "iw_1.v36")]);
      (Let (a "iw_1.v37") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "iw_1.v39") W (Cmp Sle W) [(t "iw_1.v37"); (Const 0)])] (JBranch (t "iw_1.v39") (To (a "iw_1.L33")) (To (a "iw_1.L35"))));
  (mkBlock (a "iw_1.L33") [] [(Let (a "iw_1.v42") P Copy [(Global (a "quotearg#slotvec0"))]);
      (Let (a "iw_1.v43") L Ptoi [(t "iw_1.v13")]);
      (Let (a "iw_1.v44") L Ptoi [(t "iw_1.v42")]);
      (Let (a "iw_1.v45") W (Cmp Eq L) [(t "iw_1.v43"); (t "iw_1.v44")]);
      (Let (a "iw_1.v48") P Copy [(Global (a "quotearg#nslots"))]);
      (Let (a "chk3") A (Check 0 4 Read 1) [(t "iw_1.v48")]);
      (Let (a "iw_1.v49") W (RawLoad (LdNarrow Sw) 0) [(t "chk3")]);
      (Let (a "iw_1.v50") L (Ext Sw) [(t "iw_1.v49")]);
      (Let (a "chk4") A (Check 0 8 Write 1) [(t "iw_1.v47")]);
      (RawStore Wl 0 (t "iw_1.v50") (t "chk4"));
      (Let (a "iw_1.v51") P Copy [(Global (a "quotearg#slotvec"))])] (JBranch (t "iw_1.v45") (To (a "iw_1.L54")) (To (a "iw_1.L53"))));
  (mkBlock (a "iw_1.L53") [] [] (JGoto (To (a "iw_1.L54"))));
  (mkBlock (a "iw_1.L54") [(Phi (a "iw_1.v57") P [((a "iw_1.L53"), (t "iw_1.v13")); ((a "iw_1.L33"), (Const 0))])] [(Let (a "iw_1.v59") P Copy [(Global (a "quotearg#nslots"))]);
      (Let (a "chk5") A (Check 0 4 Read 1) [(t "iw_1.v59")]);
      (Let (a "iw_1.v60") W (RawLoad (LdNarrow Sw) 0) [(t "chk5")]);
      (Let (a "iw_1.v61") W Sub [(Const 0); (t "iw_1.v60")]);
      (Let (a "iw_1.v62") W Add [(t "iw_1.v61"); (Const 1)]);
      (Let (a "iw_1.v63") L (Ext Sw) [(t "iw_1.v62")]);
      (Call (CResult (a "iw_1.v66") P) (Global (a "xpalloc")) [(Arg P (t "iw_1.v57")); (Arg P (t "iw_1.v47")); (Arg L (t "iw_1.v63")); (Arg L (Const 2147483647)); (Arg L (Const 16))]);
      (Let (a "chk6") A (Check 0 8 Write 8) [(t "iw_1.v51")]);
      (RawStorePointer 0 (t "iw_1.v66") (t "chk6") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JBranch (t "iw_1.v45") (To (a "iw_1.L67")) (To (a "iw_1.L69"))));
  (mkBlock (a "iw_1.L67") [] [(Let (a "iw_1.v72") P Copy [(Global (a "quotearg#slotvec0"))]);
      (Let (a "chk7") A (Check 0 8 Read 1) [(t "iw_1.v72")]);
      (Let (a "iw_1.v73") L (RawLoad LdL 0) [(t "chk7")]);
      (Let (a "chk8") A (Check 0 8 Write 1) [(t "iw_1.v66")]);
      (RawStore Wl 0 (t "iw_1.v73") (t "chk8"));
      (Flight (a "iw_1.v74") Add [(FAddress (t "iw_1.v72")); (FValue (Const 8))] (LowerOf (t "iw_1.v72")));
      (Flight (a "iw_1.v75") Add [(FAddress (t "iw_1.v66")); (FValue (Const 8))] (LowerOf (t "iw_1.v66")));
      (Let (a "chk9") A (HalfCheck Upper 0 8 Read 8) [(t "chk7"); (t "iw_1.v74")]);
      (Let (a "iw_1.v76") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Let (a "chk10") A (HalfCheck Upper 0 8 Write 8) [(t "chk8"); (t "iw_1.v75")]);
      (RawStorePointer 0 (t "iw_1.v76") (t "chk10") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "iw_1.L69"))));
  (mkBlock (a "iw_1.L69") [] [(Let (a "iw_1.v78") P Copy [(Global (a "quotearg#nslots"))]);
      (Let (a "chk11") A (Check 0 4 Read 1) [(t "iw_1.v78")]);
      (Let (a "iw_1.v79") W (RawLoad (LdNarrow Sw) 0) [(t "chk11")]);
      (Let (a "iw_1.v80") L (Ext Sw) [(t "iw_1.v79")]);
      (Let (a "iw_1.v81") L Shl [(t "iw_1.v80"); (Const 4)]);
      (Flight (a "iw_1.v82") Add [(FAddress (t "iw_1.v66")); (FValue (t "iw_1.v81"))] (LowerOf (t "iw_1.v66")));
      (Let (a "chk12") A (Renew 0 8 Read 1) [(t "chk4"); (t "iw_1.v47")]);
      (Let (a "iw_1.v83") L (RawLoad LdL 0) [(t "chk12")]);
      (Let (a "iw_1.v84") P Copy [(Global (a "quotearg#nslots"))]);
      (Let (a "chk13") A (Check 0 4 Read 1) [(t "iw_1.v84")]);
      (Let (a "iw_1.v85") W (RawLoad (LdNarrow Sw) 0) [(t "chk13")]);
      (Let (a "iw_1.v86") L (Ext Sw) [(t "iw_1.v85")]);
      (Let (a "iw_1.v87") L Sub [(t "iw_1.v83"); (t "iw_1.v86")]);
      (Let (a "iw_1.v88") L Shl [(t "iw_1.v87"); (Const 4)]);
      (Call (CResult (a "iw_1.v89") P) (Global (a "memset")) [(Arg P (t "iw_1.v82")); (Arg W (Const 0)); (Arg L (t "iw_1.v88"))]);
      (Let (a "iw_1.v90") P Copy [(Global (a "quotearg#nslots"))]);
      (Let (a "chk14") A (Renew 0 8 Read 1) [(t "chk4"); (t "iw_1.v47")]);
      (Let (a "iw_1.v91") L (RawLoad LdL 0) [(t "chk14")]);
      (Let (a "chk15") A (Check 0 4 Write 1) [(t "iw_1.v90")]);
      (RawStore Ww 0 (t "iw_1.v91") (t "chk15"))] (JGoto (To (a "iw_1.L35"))));
  (mkBlock (a "iw_1.L35") [(Phi (a "iw_1.pr.1") P [((a "iw_1.L69"), (t "iw_1.v66")); ((a "start"), (t "iw_1.v13"))])] [(Let (a "chk16") A (Check 0 8 Read 1) [(t "iw_1.pr.1")]);
      (Let (a "iw_1.v98") L (RawLoad LdL 0) [(t "chk16")]);
      (Flight (a "iw_1.v105") Add [(FAddress (t "iw_1.pr.1")); (FValue (Const 8))] (LowerOf (t "iw_1.pr.1")));
      (Let (a "chk17") A (HalfCheck Upper 0 8 Read 8) [(t "chk16"); (t "iw_1.v105")]);
      (Let (a "iw_1.v106") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Flight (a "iw_1.v109") Add [(FAddress (t "v6")); (FValue (Const 4))] (LowerOf (t "v6")));
      (Let (a "chk18") A (Check 0 4 Read 1) [(t "iw_1.v109")]);
      (Let (a "iw_1.v110") W (RawLoad (LdNarrow Sw) 0) [(t "chk18")]);
      (Let (a "iw_1.v111") W Or [(t "iw_1.v110"); (Const 1)]);
      (Let (a "chk19") A (HalfCheck Lower 0 4 Read 1) [(t "chk18"); (t "v6")]);
      (Let (a "iw_1.v118") W (RawLoad (LdNarrow Uw) 0) [(t "chk19")]);
      (Flight (a "iw_1.v121") Add [(FAddress (t "v6")); (FValue (Const 8))] (LowerOf (t "v6")));
      (Flight (a "iw_1.v123") Add [(FAddress (t "v6")); (FValue (Const 40))] (LowerOf (t "v6")));
      (Let (a "chk20") A (HalfCheck Upper 0 8 Read 8) [(t "chk18"); (t "iw_1.v123")]);
      (Let (a "iw_1.v124") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk20")]);
      (Flight (a "iw_1.v126") Add [(FAddress (t "v6")); (FValue (Const 48))] (LowerOf (t "v6")));
      (Let (a "chk21") A (HalfCheck Upper 0 8 Read 8) [(t "chk18"); (t "iw_1.v126")]);
      (Let (a "iw_1.v127") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Call (CResult (a "iw_1.v128") L) (Global (a "quotearg#quotearg_buffer_restyled")) [(Arg P (t "iw_1.v106")); (Arg L (t "iw_1.v98")); (Arg P (t "v0")); (Arg L (t "v2")); (Arg W (t "iw_1.v118")); (Arg W (t "iw_1.v111")); (Arg P (t "iw_1.v121")); (Arg P (t "iw_1.v124")); (Arg P (t "iw_1.v127"))]);
      (Let (a "iw_1.v134") W (Cmp Ule L) [(t "iw_1.v98"); (t "iw_1.v128")])] (JBranch (t "iw_1.v134") (To (a "iw_1.L129")) (To (a "iw_1.L131"))));
  (mkBlock (a "iw_1.L129") [] [(Let (a "iw_1.v141") L Add [(t "iw_1.v128"); (Const 1)]);
      (Let (a "chk22") A (Renew 0 8 Write 1) [(t "chk16"); (t "iw_1.pr.1")]);
      (RawStore Wl 0 (t "iw_1.v141") (t "chk22"));
      (Let (a "iw_1.v146") P Copy [(Global (a "quotearg#slot0"))]);
      (Let (a "iw_1.v147") L Ptoi [(t "iw_1.v106")]);
      (Let (a "iw_1.v148") L Ptoi [(t "iw_1.v146")]);
      (Let (a "iw_1.v149") W (Cmp Ne L) [(t "iw_1.v147"); (t "iw_1.v148")])] (JBranch (t "iw_1.v149") (To (a "iw_1.L142")) (To (a "iw_1.L144"))));
  (mkBlock (a "iw_1.L142") [] [(Call CVoid (Global (a "free")) [(Arg P (t "iw_1.v106"))])] (JGoto (To (a "iw_1.L144"))));
  (mkBlock (a "iw_1.L144") [] [(Flight (a "iw_1.v156") Add [(FAddress (t "iw_1.pr.1")); (FValue (Const 8))] (LowerOf (t "iw_1.pr.1")));
      (Call (CResult (a "iw_1.v158") P) (Global (a "xcharalloc")) [(Arg L (t "iw_1.v141"))]);
      (Let (a "chk23") A (Renew 0 8 Write 8) [(t "chk17"); (t "iw_1.v156")]);
      (RawStorePointer 0 (t "iw_1.v158") (t "chk23") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk24") A (Renew 0 4 Read 1) [(t "chk19"); (t "v6")]);
      (Let (a "iw_1.v164") W (RawLoad (LdNarrow Uw) 0) [(t "chk24")]);
      (Flight (a "iw_1.v167") Add [(FAddress (t "v6")); (FValue (Const 8))] (LowerOf (t "v6")));
      (Flight (a "iw_1.v169") Add [(FAddress (t "v6")); (FValue (Const 40))] (LowerOf (t "v6")));
      (Let (a "chk25") A (Renew 0 8 Read 8) [(t "chk20"); (t "iw_1.v169")]);
      (Let (a "iw_1.v170") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk25")]);
      (Flight (a "iw_1.v172") Add [(FAddress (t "v6")); (FValue (Const 48))] (LowerOf (t "v6")));
      (Let (a "chk26") A (Renew 0 8 Read 8) [(t "chk21"); (t "iw_1.v172")]);
      (Let (a "iw_1.v173") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk26")]);
      (Call (CResult (a "iw_1.v174") L) (Global (a "quotearg#quotearg_buffer_restyled")) [(Arg P (t "iw_1.v158")); (Arg L (t "iw_1.v141")); (Arg P (t "v0")); (Arg L (t "v2")); (Arg W (t "iw_1.v164")); (Arg W (t "iw_1.v111")); (Arg P (t "iw_1.v167")); (Arg P (t "iw_1.v170")); (Arg P (t "iw_1.v173"))])] (JGoto (To (a "iw_1.L131"))));
  (mkBlock (a "iw_1.L131") [(Phi (a "iw_1.pr.2") P [((a "iw_1.L144"), (t "iw_1.v158")); ((a "iw_1.L35"), (t "iw_1.v106"))])] [(Call (CResult (a "iw_1.v175") P) (Global (a "__errno_location")) []);
      (Let (a "chk27") A (Check 0 4 Write 1) [(t "iw_1.v175")]);
      (RawStore Ww 0 (t "iw_1.v10") (t "chk27"))] (JRet (t "iw_1.pr.2")))].

Definition hello_image_fn_quotearg_char : func :=
  mkFunc (a "quotearg_char") (a "export") (RClass P) [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v5") W (Ext Sb) [(t "v2")]);
      (Call (CResult (a "v6") P) (Global (a "quotearg_char_mem")) [(Arg P (t "v0")); (Arg L (Const 18446744073709551615)); (Arg W (t "v5"))])] (JRet (t "v6")))].

Definition hello_image_fn_quotearg_colon : func :=
  mkFunc (a "quotearg_colon") (a "export") (RClass P) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") P) (Global (a "quotearg_char")) [(Arg P (t "v0")); (Arg W (Const 58))])] (JRet (t "v3")))].
