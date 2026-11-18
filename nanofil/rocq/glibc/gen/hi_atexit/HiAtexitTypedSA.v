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

Definition hi_fn_glibc_genops'23save_for_backup : func :=
  mkFunc (a "glibc_genops#save_for_backup") (a "local") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Flight (a "iw_1.v7") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "iw_1.v7")]);
      (Let (a "iw_1.v8") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "iw_1.v9") L Ptoi [(t "v2")]);
      (Let (a "iw_1.v10") L Ptoi [(t "iw_1.v8")]);
      (Let (a "iw_1.v11") L Sub [(t "iw_1.v9"); (t "iw_1.v10")]);
      (Flight (a "iw_1.v14") Add [(FAddress (t "v0")); (FValue (Const 96))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "iw_1.v14")]);
      (Let (a "iw_1.v15") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")])] (JGoto (To (a "iw_1.L16"))));
  (mkBlock (a "iw_1.L16") [(Phi (a "iw_1.pr.3") P [((a "iw_1.L26"), (t "iw_1.v38")); ((a "start"), (t "iw_1.v15"))]); (Phi (a "iw_1.pr.1") L [((a "iw_1.L26"), (t "iw_1.pr.2")); ((a "start"), (t "iw_1.v11"))])] [(Let (a "iw_1.v21") L Ptoi [(t "iw_1.pr.3")]);
      (Let (a "iw_1.v22") L Ptoi [(Const 0)]);
      (Let (a "iw_1.v23") W (Cmp Ne L) [(t "iw_1.v21"); (t "iw_1.v22")])] (JBranch (t "iw_1.v23") (To (a "iw_1.L17")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L17") [] [(Flight (a "iw_1.v28") Add [(FAddress (t "iw_1.pr.3")); (FValue (Const 16))] (LowerOf (t "iw_1.pr.3")));
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "iw_1.v28")]);
      (Let (a "iw_1.v29") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "iw_1.v31") L (Ext Sw) [(t "iw_1.v29")]);
      (Let (a "iw_1.v32") W (Cmp Slt L) [(t "iw_1.v31"); (t "iw_1.pr.1")])] (JBranch (t "iw_1.v32") (To (a "iw_1.L24")) (To (a "iw_1.L26"))));
  (mkBlock (a "iw_1.L24") [] [(Flight (a "iw_1.v34") Add [(FAddress (t "iw_1.pr.3")); (FValue (Const 16))] (LowerOf (t "iw_1.pr.3")));
      (Let (a "iw_1.v35") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "iw_1.v36") L (Ext Sw) [(t "iw_1.v35")])] (JGoto (To (a "iw_1.L26"))));
  (mkBlock (a "iw_1.L26") [(Phi (a "iw_1.pr.2") L [((a "iw_1.L24"), (t "iw_1.v36")); ((a "iw_1.L17"), (t "iw_1.pr.1"))])] [(Let (a "chk4") A (HalfCheck Lower 0 8 Read 8) [(t "chk2"); (t "iw_1.pr.3")]);
      (Let (a "iw_1.v38") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")])] (JGoto (Poll (a "iw_1.L16"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v11") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk5") A (Renew 0 8 Read 8) [(t "chk0"); (t "v11")]);
      (Let (a "v12") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "v14") L Ptoi [(t "v12")]);
      (Let (a "v15") L Sub [(t "iw_1.v9"); (t "v14")]);
      (Let (a "v17") L Sub [(t "v15"); (t "iw_1.pr.1")]);
      (Flight (a "v20") Add [(FAddress (t "v0")); (FValue (Const 88))] (LowerOf (t "v0")));
      (Let (a "chk6") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v20")]);
      (Let (a "v21") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v23") Add [(FAddress (t "v0")); (FValue (Const 72))] (LowerOf (t "v0")));
      (Let (a "v24") P (RawLoadPointer (-16) [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v25") L Ptoi [(t "v21")]);
      (Let (a "v26") L Ptoi [(t "v24")]);
      (Let (a "v27") L Sub [(t "v25"); (t "v26")]);
      (Let (a "v36") W (Cmp Ugt L) [(t "v17"); (t "v27")])] (JBranch (t "v36") (To (a "L31")) (To (a "L32"))));
  (mkBlock (a "L31") [] [(Let (a "v40") L Add [(t "v17"); (Const 100)]);
      (Call (CResult (a "v41") P) (Global (a "malloc")) [(Arg L (t "v40"))]);
      (Let (a "v46") L Ptoi [(t "v41")]);
      (Let (a "v48") W (Cmp Eq L) [(t "v46"); (t "iw_1.v22")])] (JBranch (t "v48") (To (a "L42")) (To (a "L44"))));
  (mkBlock (a "L42") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L44") [] [(Let (a "v55") W (Cmp Slt L) [(t "iw_1.pr.1"); (Const 0)])] (JBranch (t "v55") (To (a "L51")) (To (a "L52"))));
  (mkBlock (a "L51") [] [(Flight (a "v58") Add [(FAddress (t "v41")); (FValue (Const 100))] (LowerOf (t "v41")));
      (Flight (a "v60") Add [(FAddress (t "v0")); (FValue (Const 88))] (LowerOf (t "v0")));
      (Let (a "chk8") A (Renew 0 8 Read 8) [(t "chk6"); (t "v60")]);
      (Let (a "v61") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Flight (a "v63") Add [(FAddress (t "v61")); (FValue (t "iw_1.pr.1"))] (LowerOf (t "v61")));
      (Let (a "v65") L Neg [(t "iw_1.pr.1")]);
      (Call (CResult (a "v66") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v58")); (Arg P (t "v63")); (Arg L (t "v65"))]);
      (Flight (a "v68") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk9") A (Renew 0 8 Read 8) [(t "chk0"); (t "v68")]);
      (Let (a "v69") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Let (a "v73") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Let (a "v75") L Ptoi [(t "v73")]);
      (Let (a "v76") L Sub [(t "iw_1.v9"); (t "v75")]);
      (Call (CResult (a "v77") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v66")); (Arg P (t "v69")); (Arg L (t "v76"))])] (JGoto (To (a "L53"))));
  (mkBlock (a "L52") [] [(Flight (a "v80") Add [(FAddress (t "v41")); (FValue (Const 100))] (LowerOf (t "v41")));
      (Flight (a "v82") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk11") A (Renew 0 8 Read 8) [(t "chk0"); (t "v82")]);
      (Let (a "v83") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk11")]);
      (Flight (a "v85") Add [(FAddress (t "v83")); (FValue (t "iw_1.pr.1"))] (LowerOf (t "v83")));
      (Call (CResult (a "v87") P) (Global (a "__GI_memcpy")) [(Arg P (t "v80")); (Arg P (t "v85")); (Arg L (t "v17"))])] (JGoto (To (a "L53"))));
  (mkBlock (a "L53") [] [(Flight (a "v90") Add [(FAddress (t "v0")); (FValue (Const 72))] (LowerOf (t "v0")));
      (Let (a "chk12") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v90")]);
      (Let (a "v91") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk12")]);
      (Flight (a "iw_2.v9") Add [(FAddress (t "v0")); (FValue (Const 119))] (LowerOf (t "v0")));
      (Let (a "iw_2.v10") L Ptoi [(t "v91")]);
      (Let (a "iw_2.v11") L Ptoi [(t "iw_2.v9")]);
      (Let (a "iw_2.v12") W (Cmp Ne L) [(t "iw_2.v10"); (t "iw_2.v11")])] (JBranch (t "iw_2.v12") (To (a "iw_2.L4")) (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.L4") [] [(Call CVoid (Global (a "free")) [(Arg P (t "v91"))])] (JGoto (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.join") [] [(Flight (a "v93") Add [(FAddress (t "v0")); (FValue (Const 72))] (LowerOf (t "v0")));
      (Let (a "chk13") A (Renew 0 8 Write 8) [(t "chk12"); (t "v93")]);
      (RawStorePointer 0 (t "v41") (t "chk13") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v96") Add [(FAddress (t "v0")); (FValue (Const 88))] (LowerOf (t "v0")));
      (Flight (a "v99") Add [(FAddress (t "v41")); (FValue (Const 100))] (LowerOf (t "v41")));
      (Flight (a "v101") Add [(FAddress (t "v99")); (FValue (t "v17"))] (LowerOf (t "v99")));
      (Let (a "chk14") A (Renew 0 8 Write 8) [(t "chk6"); (t "v96")]);
      (RawStorePointer 0 (t "v101") (t "chk14") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L33"))));
  (mkBlock (a "L32") [] [(Let (a "v104") L Sub [(t "v27"); (t "v17")]);
      (Let (a "v109") W (Cmp Slt L) [(t "iw_1.pr.1"); (Const 0)])] (JBranch (t "v109") (To (a "L105")) (To (a "L106"))));
  (mkBlock (a "L105") [] [(Flight (a "v111") Add [(FAddress (t "v0")); (FValue (Const 72))] (LowerOf (t "v0")));
      (Let (a "v112") P (RawLoadPointer (-16) [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v114") Add [(FAddress (t "v112")); (FValue (t "v104"))] (LowerOf (t "v112")));
      (Flight (a "v116") Add [(FAddress (t "v0")); (FValue (Const 88))] (LowerOf (t "v0")));
      (Let (a "v117") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v119") Add [(FAddress (t "v117")); (FValue (t "iw_1.pr.1"))] (LowerOf (t "v117")));
      (Let (a "v121") L Neg [(t "iw_1.pr.1")]);
      (Call (CResult (a "v122") P) (Global (a "__GI_memmove")) [(Arg P (t "v114")); (Arg P (t "v119")); (Arg L (t "v121"))]);
      (Let (a "chk17") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v111")]);
      (Let (a "v125") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Flight (a "v127") Add [(FAddress (t "v125")); (FValue (t "v104"))] (LowerOf (t "v125")));
      (Flight (a "v129") Sub [(FAddress (t "v127")); (FValue (t "iw_1.pr.1"))] (LowerOf (t "v127")));
      (Flight (a "v131") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk18") A (Renew 0 8 Read 8) [(t "chk0"); (t "v131")]);
      (Let (a "v132") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk18")]);
      (Let (a "v136") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk18")]);
      (Let (a "v138") L Ptoi [(t "v136")]);
      (Let (a "v139") L Sub [(t "iw_1.v9"); (t "v138")]);
      (Call (CResult (a "v140") P) (Global (a "__GI_memcpy")) [(Arg P (t "v129")); (Arg P (t "v132")); (Arg L (t "v139"))])] (JGoto (To (a "L33"))));
  (mkBlock (a "L106") [] [(Let (a "v145") W (Cmp Ugt L) [(t "v17"); (Const 0)])] (JBranch (t "v145") (To (a "L141")) (To (a "L33"))));
  (mkBlock (a "L141") [] [(Flight (a "v147") Add [(FAddress (t "v0")); (FValue (Const 72))] (LowerOf (t "v0")));
      (Let (a "v148") P (RawLoadPointer (-16) [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v150") Add [(FAddress (t "v148")); (FValue (t "v104"))] (LowerOf (t "v148")));
      (Flight (a "v152") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "v153") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v155") Add [(FAddress (t "v153")); (FValue (t "iw_1.pr.1"))] (LowerOf (t "v153")));
      (Call (CResult (a "v157") P) (Global (a "__GI_memcpy")) [(Arg P (t "v150")); (Arg P (t "v155")); (Arg L (t "v17"))])] (JGoto (To (a "L33"))));
  (mkBlock (a "L33") [(Phi (a "pr.1") L [((a "iw_2.join"), (Const 100)); ((a "L105"), (t "v104")); ((a "L141"), (t "v104")); ((a "L106"), (t "v104"))])] [(Flight (a "v159") Add [(FAddress (t "v0")); (FValue (Const 80))] (LowerOf (t "v0")));
      (Flight (a "v161") Add [(FAddress (t "v0")); (FValue (Const 72))] (LowerOf (t "v0")));
      (Let (a "chk22") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v161")]);
      (Let (a "v162") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk22")]);
      (Flight (a "v164") Add [(FAddress (t "v162")); (FValue (t "pr.1"))] (LowerOf (t "v162")));
      (Let (a "chk23") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v159")]);
      (RawStorePointer 0 (t "v164") (t "chk23") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v167") Add [(FAddress (t "v0")); (FValue (Const 24))] (LowerOf (t "v0")));
      (Let (a "chk24") A (Renew 0 8 Read 8) [(t "chk0"); (t "v167")]);
      (Let (a "v168") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk24")]);
      (Let (a "v170") L Ptoi [(t "v168")]);
      (Let (a "v171") L Sub [(t "iw_1.v9"); (t "v170")]);
      (Flight (a "v173") Add [(FAddress (t "v0")); (FValue (Const 96))] (LowerOf (t "v0")));
      (Let (a "chk25") A (Renew 0 8 Read 8) [(t "chk1"); (t "v173")]);
      (Let (a "v174") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk25")])] (JGoto (To (a "L175"))));
  (mkBlock (a "L175") [(Phi (a "pr.2") P [((a "L176"), (t "v190")); ((a "L33"), (t "v174"))])] [(Let (a "v180") L Ptoi [(t "pr.2")]);
      (Let (a "v182") W (Cmp Ne L) [(t "v180"); (t "iw_1.v22")])] (JBranch (t "v182") (To (a "L176")) (To (a "L178"))));
  (mkBlock (a "L176") [] [(Flight (a "v184") Add [(FAddress (t "pr.2")); (FValue (Const 16))] (LowerOf (t "pr.2")));
      (Let (a "chk26") A (Check 0 4 Read 1) [(t "v184")]);
      (Let (a "v185") W (RawLoad (LdNarrow Sw) 0) [(t "chk26")]);
      (Let (a "v187") L (Ext Sw) [(t "v185")]);
      (Let (a "v188") L Sub [(t "v187"); (t "v171")]);
      (Let (a "chk27") A (Renew 0 4 Write 1) [(t "chk26"); (t "v184")]);
      (RawStore Ww 0 (t "v188") (t "chk27"));
      (Let (a "chk28") A (HalfCheck Lower 0 8 Read 8) [(t "chk26"); (t "pr.2")]);
      (Let (a "v190") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk28")])] (JGoto (Poll (a "L175"))));
  (mkBlock (a "L178") [] [] (JRet (Const 0)))].
