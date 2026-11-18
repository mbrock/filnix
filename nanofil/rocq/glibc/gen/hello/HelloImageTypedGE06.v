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

Definition hello_image_fn_glibc_libc_start'23get_common_indices : func :=
  mkFunc (a "glibc_libc_start#get_common_indices") (a "local") RVoid [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6")); (P, (a "v8"))] [(mkBlock (a "start") [] [(Let (a "v16") P (Alloc 4) [(Const 4)]);
      (Let (a "v14") L Ptoi [(t "v2")]);
      (Let (a "v15") W (Cmp Ne L) [(t "v14"); (Const 0)])] (JBranch (t "v15") (To (a "L10")) (To (a "L12"))));
  (mkBlock (a "L10") [] [(Flight (a "v18") Add [(FAddress (t "v0")); (FValue (Const 20))] (LowerOf (t "v0")));
      (Flight (a "v20") Add [(FAddress (t "v18")); (FValue (Const 4))] (LowerOf (t "v18")));
      (Flight (a "v24") Add [(FAddress (t "v18")); (FValue (Const 8))] (LowerOf (t "v18")));
      (Flight (a "v28") Add [(FAddress (t "v18")); (FValue (Const 12))] (LowerOf (t "v18")));
      (Call CVoid (Global (a "zcpuid")) [(Arg W (Const 1)); (Arg P (t "v16")); (Arg P (t "v20")); (Arg P (t "v24")); (Arg P (t "v28"))]);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v16")]);
      (Let (a "v32") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 4 Write 1) [(t "v18")]);
      (RawStore Ww 0 (t "v32") (t "chk1"));
      (Let (a "v34") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "v35") W Shr [(t "v34"); (Const 8)]);
      (Let (a "v36") W And [(t "v35"); (Const 15)]);
      (Let (a "chk3") A (Check 0 4 Write 1) [(t "v2")]);
      (RawStore Ww 0 (t "v36") (t "chk3"));
      (Let (a "v38") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "v39") W Shr [(t "v38"); (Const 4)]);
      (Let (a "v40") W And [(t "v39"); (Const 15)]);
      (Let (a "chk5") A (Check 0 4 Write 1) [(t "v4")]);
      (RawStore Ww 0 (t "v40") (t "chk5"));
      (Let (a "v42") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "v43") W Shr [(t "v42"); (Const 12)]);
      (Let (a "v44") W And [(t "v43"); (Const 240)]);
      (Let (a "chk7") A (Check 0 4 Write 1) [(t "v6")]);
      (RawStore Ww 0 (t "v44") (t "chk7"));
      (Let (a "v46") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "v47") W And [(t "v46"); (Const 15)]);
      (Let (a "chk9") A (Check 0 4 Write 1) [(t "v8")]);
      (RawStore Ww 0 (t "v47") (t "chk9"));
      (Let (a "v52") W (RawLoad (LdNarrow Uw) 0) [(t "chk3")]);
      (Let (a "v53") W (Cmp Eq W) [(t "v52"); (Const 15)])] (JBranch (t "v53") (To (a "L48")) (To (a "L12"))));
  (mkBlock (a "L48") [] [(Let (a "v55") W (RawLoad (LdNarrow Uw) 0) [(t "chk3")]);
      (Let (a "v56") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "v57") W Shr [(t "v56"); (Const 20)]);
      (Let (a "v58") W And [(t "v57"); (Const 255)]);
      (Let (a "v59") W Add [(t "v55"); (t "v58")]);
      (RawStore Ww 0 (t "v59") (t "chk3"));
      (Let (a "v61") W (RawLoad (LdNarrow Uw) 0) [(t "chk5")]);
      (Let (a "v63") W (RawLoad (LdNarrow Uw) 0) [(t "chk7")]);
      (Let (a "v64") W Add [(t "v61"); (t "v63")]);
      (RawStore Ww 0 (t "v64") (t "chk5"))] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [] [(Flight (a "v69") Add [(FAddress (t "v0")); (FValue (Const 4))] (LowerOf (t "v0")));
      (Let (a "chk17") A (Check 0 4 Read 1) [(t "v69")]);
      (Let (a "v70") W (RawLoad (LdNarrow Sw) 0) [(t "chk17")]);
      (Let (a "v71") W (Cmp Sge W) [(t "v70"); (Const 7)])] (JBranch (t "v71") (To (a "L65")) (To (a "L67"))));
  (mkBlock (a "L65") [] [(Flight (a "v73") Add [(FAddress (t "v0")); (FValue (Const 20))] (LowerOf (t "v0")));
      (Flight (a "v74") Add [(FAddress (t "v73")); (FValue (Const 32))] (LowerOf (t "v73")));
      (Flight (a "v78") Add [(FAddress (t "v74")); (FValue (Const 4))] (LowerOf (t "v74")));
      (Flight (a "v82") Add [(FAddress (t "v74")); (FValue (Const 8))] (LowerOf (t "v74")));
      (Flight (a "v86") Add [(FAddress (t "v74")); (FValue (Const 12))] (LowerOf (t "v74")));
      (Call CVoid (Global (a "zcpuid_count")) [(Arg W (Const 7)); (Arg W (Const 0)); (Arg P (t "v74")); (Arg P (t "v78")); (Arg P (t "v82")); (Arg P (t "v86"))]);
      (Flight (a "v89") Add [(FAddress (t "v73")); (FValue (Const 192))] (LowerOf (t "v73")));
      (Flight (a "v93") Add [(FAddress (t "v89")); (FValue (Const 4))] (LowerOf (t "v89")));
      (Flight (a "v97") Add [(FAddress (t "v89")); (FValue (Const 8))] (LowerOf (t "v89")));
      (Flight (a "v101") Add [(FAddress (t "v89")); (FValue (Const 12))] (LowerOf (t "v89")));
      (Call CVoid (Global (a "zcpuid_count")) [(Arg W (Const 7)); (Arg W (Const 1)); (Arg P (t "v89")); (Arg P (t "v93")); (Arg P (t "v97")); (Arg P (t "v101"))])] (JGoto (To (a "L67"))));
  (mkBlock (a "L67") [] [(Flight (a "v106") Add [(FAddress (t "v0")); (FValue (Const 4))] (LowerOf (t "v0")));
      (Let (a "chk18") A (Renew 0 4 Read 1) [(t "chk17"); (t "v106")]);
      (Let (a "v107") W (RawLoad (LdNarrow Sw) 0) [(t "chk18")]);
      (Let (a "v108") W (Cmp Sge W) [(t "v107"); (Const 13)])] (JBranch (t "v108") (To (a "L102")) (To (a "L104"))));
  (mkBlock (a "L102") [] [(Flight (a "v110") Add [(FAddress (t "v0")); (FValue (Const 20))] (LowerOf (t "v0")));
      (Flight (a "v111") Add [(FAddress (t "v110")); (FValue (Const 96))] (LowerOf (t "v110")));
      (Flight (a "v115") Add [(FAddress (t "v111")); (FValue (Const 4))] (LowerOf (t "v111")));
      (Flight (a "v119") Add [(FAddress (t "v111")); (FValue (Const 8))] (LowerOf (t "v111")));
      (Flight (a "v123") Add [(FAddress (t "v111")); (FValue (Const 12))] (LowerOf (t "v111")));
      (Call CVoid (Global (a "zcpuid_count")) [(Arg W (Const 13)); (Arg W (Const 1)); (Arg P (t "v111")); (Arg P (t "v115")); (Arg P (t "v119")); (Arg P (t "v123"))])] (JGoto (To (a "L104"))));
  (mkBlock (a "L104") [] [(Flight (a "v128") Add [(FAddress (t "v0")); (FValue (Const 4))] (LowerOf (t "v0")));
      (Let (a "chk19") A (Renew 0 4 Read 1) [(t "chk17"); (t "v128")]);
      (Let (a "v129") W (RawLoad (LdNarrow Sw) 0) [(t "chk19")]);
      (Let (a "v130") W (Cmp Sge W) [(t "v129"); (Const 20)])] (JBranch (t "v130") (To (a "L124")) (To (a "L126"))));
  (mkBlock (a "L124") [] [(Flight (a "v132") Add [(FAddress (t "v0")); (FValue (Const 20))] (LowerOf (t "v0")));
      (Flight (a "v133") Add [(FAddress (t "v132")); (FValue (Const 256))] (LowerOf (t "v132")));
      (Flight (a "v137") Add [(FAddress (t "v133")); (FValue (Const 4))] (LowerOf (t "v133")));
      (Flight (a "v141") Add [(FAddress (t "v133")); (FValue (Const 8))] (LowerOf (t "v133")));
      (Flight (a "v145") Add [(FAddress (t "v133")); (FValue (Const 12))] (LowerOf (t "v133")));
      (Call CVoid (Global (a "zcpuid_count")) [(Arg W (Const 20)); (Arg W (Const 0)); (Arg P (t "v133")); (Arg P (t "v137")); (Arg P (t "v141")); (Arg P (t "v145"))])] (JGoto (To (a "L126"))));
  (mkBlock (a "L126") [] [(Flight (a "v150") Add [(FAddress (t "v0")); (FValue (Const 4))] (LowerOf (t "v0")));
      (Let (a "chk20") A (Renew 0 4 Read 1) [(t "chk17"); (t "v150")]);
      (Let (a "v151") W (RawLoad (LdNarrow Sw) 0) [(t "chk20")]);
      (Let (a "v152") W (Cmp Sge W) [(t "v151"); (Const 25)])] (JBranch (t "v152") (To (a "L146")) (To (a "iw_1.start"))));
  (mkBlock (a "L146") [] [(Flight (a "v154") Add [(FAddress (t "v0")); (FValue (Const 20))] (LowerOf (t "v0")));
      (Flight (a "v155") Add [(FAddress (t "v154")); (FValue (Const 224))] (LowerOf (t "v154")));
      (Flight (a "v159") Add [(FAddress (t "v155")); (FValue (Const 4))] (LowerOf (t "v155")));
      (Flight (a "v163") Add [(FAddress (t "v155")); (FValue (Const 8))] (LowerOf (t "v155")));
      (Flight (a "v167") Add [(FAddress (t "v155")); (FValue (Const 12))] (LowerOf (t "v155")));
      (Call CVoid (Global (a "zcpuid_count")) [(Arg W (Const 25)); (Arg W (Const 0)); (Arg P (t "v155")); (Arg P (t "v159")); (Arg P (t "v163")); (Arg P (t "v167"))])] (JGoto (To (a "iw_1.start"))));
  (mkBlock (a "iw_1.start") [] [(Let (a "iw_1.v40") P (Alloc 4) [(Const 4)]);
      (Let (a "iw_1.v41") P (Alloc 4) [(Const 4)]);
      (Let (a "iw_1.v42") P (Alloc 4) [(Const 4)]);
      (Let (a "iw_1.v43") P (Alloc 4) [(Const 4)]);
      (Let (a "iw_1.v5") P Copy [(Global (a "_dl_minsigstacksize"))]);
      (Let (a "chk21") A (Check 0 8 Read 1) [(t "iw_1.v5")]);
      (Let (a "iw_1.v6") L (RawLoad LdL 0) [(t "chk21")]);
      (Let (a "iw_1.v7") W (Cmp Ne L) [(t "iw_1.v6"); (Const 0)])] (JBranch (t "iw_1.v7") (To (a "iw_1.join")) (To (a "iw_1.L4"))));
  (mkBlock (a "iw_1.L4") [] [(Flight (a "iw_1.v13") Add [(FAddress (t "v0")); (FValue (Const 4))] (LowerOf (t "v0")));
      (Let (a "chk22") A (Renew 0 4 Read 1) [(t "chk17"); (t "iw_1.v13")]);
      (Let (a "iw_1.v14") W (RawLoad (LdNarrow Sw) 0) [(t "chk22")]);
      (Let (a "iw_1.v15") W (Cmp Sge W) [(t "iw_1.v14"); (Const 13)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L16")) (To (a "iw_1.L17"))));
  (mkBlock (a "iw_1.L16") [] [(Flight (a "iw_1.v19") Add [(FAddress (t "v0")); (FValue (Const 20))] (LowerOf (t "v0")));
      (Flight (a "iw_1.v21") Add [(FAddress (t "iw_1.v19")); (FValue (Const 8))] (LowerOf (t "iw_1.v19")));
      (Let (a "chk23") A (HalfCheck Upper 0 4 Read 1) [(t "chk17"); (t "iw_1.v21")]);
      (Let (a "iw_1.v22") W (RawLoad (LdNarrow Uw) 0) [(t "chk23")]);
      (Let (a "iw_1.v24") W And [(t "iw_1.v22"); (Const 134217728)]);
      (Let (a "iw_1.v25") W (Cmp Ne W) [(t "iw_1.v24"); (Const 0)])] (JGoto (To (a "iw_1.L17"))));
  (mkBlock (a "iw_1.L17") [(Phi (a "iw_1.v27") W [((a "iw_1.L4"), (Const 0)); ((a "iw_1.L16"), (t "iw_1.v25"))])] [] (JBranch (t "iw_1.v27") (To (a "iw_1.L9")) (To (a "iw_1.L10"))));
  (mkBlock (a "iw_1.L9") [] [(Call CVoid (Global (a "zcpuid_count")) [(Arg W (Const 13)); (Arg W (Const 0)); (Arg P (t "iw_1.v40")); (Arg P (t "iw_1.v41")); (Arg P (t "iw_1.v42")); (Arg P (t "iw_1.v43"))]);
      (Let (a "chk24") A (Check 0 4 Read 1) [(t "iw_1.v41")]);
      (Let (a "iw_1.v45") W (RawLoad (LdNarrow Uw) 0) [(t "chk24")]);
      (Let (a "iw_1.v46") W Add [(t "iw_1.v45"); (Const 512)]);
      (Let (a "iw_1.v48") L (Ext Uw) [(t "iw_1.v46")]);
      (Let (a "iw_1.v49") L Add [(t "iw_1.v48"); (Const 4)]);
      (Let (a "iw_1.v50") P Copy [(Global (a "_dl_minsigstacksize"))]);
      (Let (a "iw_1.v51") W Copy [(t "iw_1.v49")]);
      (Let (a "iw_1.v52") L (Ext Uw) [(t "iw_1.v51")]);
      (Let (a "chk25") A (Check 0 8 Write 1) [(t "iw_1.v50")]);
      (RawStore Wl 0 (t "iw_1.v52") (t "chk25"))] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Let (a "iw_1.v53") P Copy [(Global (a "_dl_minsigstacksize"))]);
      (Let (a "chk26") A (Check 0 8 Write 1) [(t "iw_1.v53")]);
      (RawStore Wl 0 (Const 2048) (t "chk26"))] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [] JRetVoid)].

Definition hello_image_fn___getrandom_early_init : func :=
  mkFunc (a "__getrandom_early_init") (a "export") RVoid [(W, (a "v0"))] [(mkBlock (a "start") [] [] JRetVoid)].
