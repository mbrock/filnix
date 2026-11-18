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

Definition hello_image_fn_glibc_qsort'23msort_with_tmp : func :=
  mkFunc (a "glibc_qsort#msort_with_tmp") (a "local") RVoid [(P, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v14") W (Cmp Ule L) [(t "v4"); (Const 1)])] (JBranch (t "v14") (To (a "L10")) (To (a "L12"))));
  (mkBlock (a "L10") [] [] JRetVoid);
  (mkBlock (a "L12") [] [(Let (a "v17") L Shr [(t "v4"); (Const 1)]);
      (Let (a "v20") L Sub [(t "v4"); (t "v17")]);
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v0")]);
      (Let (a "v25") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v26") L Mul [(t "v17"); (t "v25")]);
      (Flight (a "v27") Add [(FAddress (t "v2")); (FValue (t "v26"))] (LowerOf (t "v2")));
      (Call CVoid (Global (a "glibc_qsort#msort_with_tmp")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg L (t "v17"))]);
      (Call CVoid (Global (a "glibc_qsort#msort_with_tmp")) [(Arg P (t "v0")); (Arg P (t "v27")); (Arg L (t "v20"))]);
      (Flight (a "v36") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v36")]);
      (Let (a "v37") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "chk2") A (Renew 0 8 Read 1) [(t "chk0"); (t "v0")]);
      (Let (a "v40") L (RawLoad LdL 0) [(t "chk2")]);
      (Flight (a "v43") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "v44") P (RawLoadPointer (-16) [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v47") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "v48") P (RawLoadPointer (-8) [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v50") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v51") W (RawLoad (LdNarrow Uw) 8) [(t "chk2")]);
      (Let (a "v207") W (Cmp Eq W) [(t "v51"); (Const 1)])] (JBranch (t "v207") (To (a "L55")) (To (a "L208"))));
  (mkBlock (a "L55") [(Phi (a "pr.40") P [((a "L68"), (t "v90")); ((a "L12"), (t "v37"))]); (Phi (a "pr.33") L [((a "L68"), (t "pr.34")); ((a "L12"), (t "v20"))]); (Phi (a "pr.24") L [((a "L68"), (t "pr.25")); ((a "L12"), (t "v17"))]); (Phi (a "pr.15") P [((a "L68"), (t "pr.16")); ((a "L12"), (t "v27"))]); (Phi (a "pr.7") P [((a "L68"), (t "pr.8")); ((a "L12"), (t "v2"))])] [(Let (a "v59") W (Cmp Ugt L) [(t "pr.24"); (Const 0)])] (JBranch (t "v59") (To (a "L60")) (To (a "L61"))));
  (mkBlock (a "L60") [] [(Let (a "v63") W (Cmp Ugt L) [(t "pr.33"); (Const 0)])] (JGoto (To (a "L61"))));
  (mkBlock (a "L61") [(Phi (a "v65") W [((a "L55"), (Const 0)); ((a "L60"), (t "v63"))])] [] (JBranch (t "v65") (To (a "L56")) (To (a "L53"))));
  (mkBlock (a "L56") [] [(Let (a "chk6") F CheckFunction [(t "v44")]);
      (RawCall (CResult (a "v73") W) (t "chk6") [(Arg P (t "pr.7")); (Arg P (t "pr.15")); (Arg P (t "v48"))]);
      (Let (a "v74") W (Cmp Sle W) [(t "v73"); (Const 0)])] (JBranch (t "v74") (To (a "L66")) (To (a "L67"))));
  (mkBlock (a "L66") [] [(Let (a "chk7") A (Check 0 4 Read 1) [(t "pr.7")]);
      (Let (a "v77") W (RawLoad (LdNarrow Uw) 0) [(t "chk7")]);
      (Let (a "chk8") A (Check 0 4 Write 1) [(t "pr.40")]);
      (RawStore Ww 0 (t "v77") (t "chk8"));
      (Flight (a "v79") Add [(FAddress (t "pr.7")); (FValue (Const 4))] (LowerOf (t "pr.7")));
      (Let (a "v81") L Sub [(t "pr.24"); (Const 1)])] (JGoto (To (a "L68"))));
  (mkBlock (a "L67") [] [(Let (a "chk9") A (Check 0 4 Read 1) [(t "pr.15")]);
      (Let (a "v84") W (RawLoad (LdNarrow Uw) 0) [(t "chk9")]);
      (Let (a "chk10") A (Check 0 4 Write 1) [(t "pr.40")]);
      (RawStore Ww 0 (t "v84") (t "chk10"));
      (Flight (a "v86") Add [(FAddress (t "pr.15")); (FValue (Const 4))] (LowerOf (t "pr.15")));
      (Let (a "v88") L Sub [(t "pr.33"); (Const 1)])] (JGoto (To (a "L68"))));
  (mkBlock (a "L68") [(Phi (a "pr.34") L [((a "L66"), (t "pr.33")); ((a "L67"), (t "v88"))]); (Phi (a "pr.25") L [((a "L66"), (t "v81")); ((a "L67"), (t "pr.24"))]); (Phi (a "pr.16") P [((a "L66"), (t "pr.15")); ((a "L67"), (t "v86"))]); (Phi (a "pr.8") P [((a "L66"), (t "v79")); ((a "L67"), (t "pr.7"))])] [(Flight (a "v90") Add [(FAddress (t "pr.40")); (FValue (Const 4))] (LowerOf (t "pr.40")))] (JGoto (Poll (a "L55"))));
  (mkBlock (a "L92") [(Phi (a "pr.41") P [((a "L105"), (t "v127")); ((a "L208"), (t "v37"))]); (Phi (a "pr.35") L [((a "L105"), (t "pr.27")); ((a "L208"), (t "v20"))]); (Phi (a "pr.26") L [((a "L105"), (t "pr.18")); ((a "L208"), (t "v17"))]); (Phi (a "pr.17") P [((a "L105"), (t "pr.10")); ((a "L208"), (t "v27"))]); (Phi (a "pr.9") P [((a "L105"), (t "pr.1")); ((a "L208"), (t "v2"))])] [(Let (a "v96") W (Cmp Ugt L) [(t "pr.26"); (Const 0)])] (JBranch (t "v96") (To (a "L97")) (To (a "L98"))));
  (mkBlock (a "L97") [] [(Let (a "v100") W (Cmp Ugt L) [(t "pr.35"); (Const 0)])] (JGoto (To (a "L98"))));
  (mkBlock (a "L98") [(Phi (a "v102") W [((a "L92"), (Const 0)); ((a "L97"), (t "v100"))])] [] (JBranch (t "v102") (To (a "L93")) (To (a "L53"))));
  (mkBlock (a "L93") [] [(Let (a "chk11") F CheckFunction [(t "v44")]);
      (RawCall (CResult (a "v110") W) (t "chk11") [(Arg P (t "pr.9")); (Arg P (t "pr.17")); (Arg P (t "v48"))]);
      (Let (a "v111") W (Cmp Sle W) [(t "v110"); (Const 0)])] (JBranch (t "v111") (To (a "L103")) (To (a "L104"))));
  (mkBlock (a "L103") [] [(Let (a "chk12") A (Check 0 8 Read 1) [(t "pr.9")]);
      (Let (a "v114") L (RawLoad LdL 0) [(t "chk12")]);
      (Let (a "chk13") A (Check 0 8 Write 1) [(t "pr.41")]);
      (RawStore Wl 0 (t "v114") (t "chk13"));
      (Flight (a "v116") Add [(FAddress (t "pr.9")); (FValue (Const 8))] (LowerOf (t "pr.9")));
      (Let (a "v118") L Sub [(t "pr.26"); (Const 1)])] (JGoto (To (a "L105"))));
  (mkBlock (a "L104") [] [(Let (a "chk14") A (Check 0 8 Read 1) [(t "pr.17")]);
      (Let (a "v121") L (RawLoad LdL 0) [(t "chk14")]);
      (Let (a "chk15") A (Check 0 8 Write 1) [(t "pr.41")]);
      (RawStore Wl 0 (t "v121") (t "chk15"));
      (Flight (a "v123") Add [(FAddress (t "pr.17")); (FValue (Const 8))] (LowerOf (t "pr.17")));
      (Let (a "v125") L Sub [(t "pr.35"); (Const 1)])] (JGoto (To (a "L105"))));
  (mkBlock (a "L105") [(Phi (a "pr.27") L [((a "L103"), (t "pr.35")); ((a "L104"), (t "v125"))]); (Phi (a "pr.18") L [((a "L103"), (t "v118")); ((a "L104"), (t "pr.26"))]); (Phi (a "pr.10") P [((a "L103"), (t "pr.17")); ((a "L104"), (t "v123"))]); (Phi (a "pr.1") P [((a "L103"), (t "v116")); ((a "L104"), (t "pr.9"))])] [(Flight (a "v127") Add [(FAddress (t "pr.41")); (FValue (Const 8))] (LowerOf (t "pr.41")))] (JGoto (Poll (a "L92"))));
  (mkBlock (a "L129") [(Phi (a "pr.36") P [((a "L142"), (t "v166")); ((a "L210"), (t "v37"))]); (Phi (a "pr.28") L [((a "L142"), (t "pr.29")); ((a "L210"), (t "v20"))]); (Phi (a "pr.19") L [((a "L142"), (t "pr.20")); ((a "L210"), (t "v17"))]); (Phi (a "pr.11") P [((a "L142"), (t "pr.12")); ((a "L210"), (t "v27"))]); (Phi (a "pr.2") P [((a "L142"), (t "pr.3")); ((a "L210"), (t "v2"))])] [(Let (a "v133") W (Cmp Ugt L) [(t "pr.19"); (Const 0)])] (JBranch (t "v133") (To (a "L134")) (To (a "L135"))));
  (mkBlock (a "L134") [] [(Let (a "v137") W (Cmp Ugt L) [(t "pr.28"); (Const 0)])] (JGoto (To (a "L135"))));
  (mkBlock (a "L135") [(Phi (a "v139") W [((a "L129"), (Const 0)); ((a "L134"), (t "v137"))])] [] (JBranch (t "v139") (To (a "L130")) (To (a "L53"))));
  (mkBlock (a "L130") [] [(Let (a "chk16") A (Check 0 8 Read 8) [(t "pr.2")]);
      (Let (a "v145") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk16")]);
      (Let (a "chk17") A (Check 0 8 Read 8) [(t "pr.11")]);
      (Let (a "v147") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Let (a "chk18") F CheckFunction [(t "v44")]);
      (RawCall (CResult (a "v149") W) (t "chk18") [(Arg P (t "v145")); (Arg P (t "v147")); (Arg P (t "v48"))]);
      (Let (a "v150") W (Cmp Sle W) [(t "v149"); (Const 0)])] (JBranch (t "v150") (To (a "L140")) (To (a "L141"))));
  (mkBlock (a "L140") [] [(Let (a "chk19") A (Renew 0 8 Read 8) [(t "chk16"); (t "pr.2")]);
      (Let (a "v153") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk19")]);
      (Let (a "chk20") A (Check 0 8 Write 8) [(t "pr.36")]);
      (RawStorePointer 0 (t "v153") (t "chk20") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v155") Add [(FAddress (t "pr.2")); (FValue (Const 8))] (LowerOf (t "pr.2")));
      (Let (a "v157") L Sub [(t "pr.19"); (Const 1)])] (JGoto (To (a "L142"))));
  (mkBlock (a "L141") [] [(Let (a "chk21") A (Renew 0 8 Read 8) [(t "chk17"); (t "pr.11")]);
      (Let (a "v160") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Let (a "chk22") A (Check 0 8 Write 8) [(t "pr.36")]);
      (RawStorePointer 0 (t "v160") (t "chk22") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v162") Add [(FAddress (t "pr.11")); (FValue (Const 8))] (LowerOf (t "pr.11")));
      (Let (a "v164") L Sub [(t "pr.28"); (Const 1)])] (JGoto (To (a "L142"))));
  (mkBlock (a "L142") [(Phi (a "pr.29") L [((a "L140"), (t "pr.28")); ((a "L141"), (t "v164"))]); (Phi (a "pr.20") L [((a "L140"), (t "v157")); ((a "L141"), (t "pr.19"))]); (Phi (a "pr.12") P [((a "L140"), (t "pr.11")); ((a "L141"), (t "v162"))]); (Phi (a "pr.3") P [((a "L140"), (t "v155")); ((a "L141"), (t "pr.2"))])] [(Flight (a "v166") Add [(FAddress (t "pr.36")); (FValue (Const 8))] (LowerOf (t "pr.36")))] (JGoto (Poll (a "L129"))));
  (mkBlock (a "L168") [(Phi (a "pr.37") P [((a "L179"), (t "v191")); ((a "L180"), (t "v200")); ((a "L210"), (t "v37"))]); (Phi (a "pr.30") L [((a "L179"), (t "pr.30")); ((a "L180"), (t "v205")); ((a "L210"), (t "v20"))]); (Phi (a "pr.21") L [((a "L179"), (t "v196")); ((a "L180"), (t "pr.21")); ((a "L210"), (t "v17"))]); (Phi (a "pr.13") P [((a "L179"), (t "pr.13")); ((a "L180"), (t "v203")); ((a "L210"), (t "v27"))]); (Phi (a "pr.4") P [((a "L179"), (t "v194")); ((a "L180"), (t "pr.4")); ((a "L210"), (t "v2"))])] [(Let (a "v172") W (Cmp Ugt L) [(t "pr.21"); (Const 0)])] (JBranch (t "v172") (To (a "L173")) (To (a "L174"))));
  (mkBlock (a "L173") [] [(Let (a "v176") W (Cmp Ugt L) [(t "pr.30"); (Const 0)])] (JGoto (To (a "L174"))));
  (mkBlock (a "L174") [(Phi (a "v178") W [((a "L168"), (Const 0)); ((a "L173"), (t "v176"))])] [] (JBranch (t "v178") (To (a "L169")) (To (a "L53"))));
  (mkBlock (a "L169") [] [(Let (a "chk23") F CheckFunction [(t "v44")]);
      (RawCall (CResult (a "v186") W) (t "chk23") [(Arg P (t "pr.4")); (Arg P (t "pr.13")); (Arg P (t "v48"))]);
      (Let (a "v187") W (Cmp Sle W) [(t "v186"); (Const 0)])] (JBranch (t "v187") (To (a "L179")) (To (a "L180"))));
  (mkBlock (a "L179") [] [(Call (CResult (a "v191") P) (Global (a "__GI_mempcpy")) [(Arg P (t "pr.37")); (Arg P (t "pr.4")); (Arg L (t "v40"))]);
      (Flight (a "v194") Add [(FAddress (t "pr.4")); (FValue (t "v40"))] (LowerOf (t "pr.4")));
      (Let (a "v196") L Sub [(t "pr.21"); (Const 1)])] (JGoto (Poll (a "L168"))));
  (mkBlock (a "L180") [] [(Call (CResult (a "v200") P) (Global (a "__GI_mempcpy")) [(Arg P (t "pr.37")); (Arg P (t "pr.13")); (Arg L (t "v40"))]);
      (Flight (a "v203") Add [(FAddress (t "pr.13")); (FValue (t "v40"))] (LowerOf (t "pr.13")));
      (Let (a "v205") L Sub [(t "pr.30"); (Const 1)])] (JGoto (Poll (a "L168"))));
  (mkBlock (a "L208") [] [(Let (a "v209") W (Cmp Eq W) [(t "v51"); (Const 0)])] (JBranch (t "v209") (Poll (a "L92")) (To (a "L210"))));
  (mkBlock (a "L210") [] [(Let (a "v211") W (Cmp Eq W) [(t "v51"); (Const 2)])] (JBranch (t "v211") (Poll (a "L129")) (Poll (a "L168"))));
  (mkBlock (a "L53") [(Phi (a "pr.39") P [((a "L61"), (t "pr.40")); ((a "L98"), (t "pr.41")); ((a "L135"), (t "pr.36")); ((a "L174"), (t "pr.37"))]); (Phi (a "pr.32") L [((a "L61"), (t "pr.33")); ((a "L98"), (t "pr.35")); ((a "L135"), (t "pr.28")); ((a "L174"), (t "pr.30"))]); (Phi (a "pr.23") L [((a "L61"), (t "pr.24")); ((a "L98"), (t "pr.26")); ((a "L135"), (t "pr.19")); ((a "L174"), (t "pr.21"))]); (Phi (a "pr.6") P [((a "L61"), (t "pr.7")); ((a "L98"), (t "pr.9")); ((a "L135"), (t "pr.2")); ((a "L174"), (t "pr.4"))])] [(Let (a "v217") W (Cmp Ugt L) [(t "pr.23"); (Const 0)])] (JBranch (t "v217") (To (a "L213")) (To (a "L215"))));
  (mkBlock (a "L213") [] [(Let (a "v222") L Mul [(t "pr.23"); (t "v40")]);
      (Call (CResult (a "v223") P) (Global (a "__GI_memcpy")) [(Arg P (t "pr.39")); (Arg P (t "pr.6")); (Arg L (t "v222"))])] (JGoto (To (a "L215"))));
  (mkBlock (a "L215") [] [(Flight (a "v226") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk24") A (Renew 0 8 Read 8) [(t "chk1"); (t "v226")]);
      (Let (a "v227") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk24")]);
      (Let (a "v230") L Sub [(t "v4"); (t "pr.32")]);
      (Let (a "v232") L Mul [(t "v230"); (t "v40")]);
      (Call (CResult (a "v233") P) (Global (a "__GI_memcpy")) [(Arg P (t "v2")); (Arg P (t "v227")); (Arg L (t "v232"))])] JRetVoid)].
