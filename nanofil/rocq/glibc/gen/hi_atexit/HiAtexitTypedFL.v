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

Definition hi_fn_glibc_genops'23flush_cleanup : func :=
  mkFunc (a "glibc_genops#flush_cleanup") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v5") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v5")]);
      (Let (a "v6") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v7") L Ptoi [(t "v6")]);
      (Let (a "v8") L Ptoi [(Const 0)]);
      (Let (a "v9") W (Cmp Ne L) [(t "v7"); (t "v8")])] (JBranch (t "v9") (To (a "L2")) (To (a "L101"))));
  (mkBlock (a "L2") [] [(Let (a "v13") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v13")]);
      (Let (a "v14") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "v14")]);
      (Let (a "v15") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v16") W And [(t "v15"); (Const 32768)]);
      (Let (a "v17") W (Cmp Eq W) [(t "v16"); (Const 0)])] (JBranch (t "v17") (To (a "L18")) (To (a "L101"))));
  (mkBlock (a "L18") [] [(Let (a "v24") P Copy [(Global (a "__libc_single_threaded_internal"))]);
      (Let (a "chk3") A (Check 0 1 Read 1) [(t "v24")]);
      (Let (a "v25") W (RawLoad (LdNarrow Sb) 0) [(t "chk3")]);
      (Let (a "v26") W (Cmp Ne W) [(t "v25"); (Const 0)])] (JBranch (t "v26") (To (a "L27")) (To (a "L28"))));
  (mkBlock (a "L27") [] [(Let (a "v29") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk4") A (Check 0 8 Read 8) [(t "v29")]);
      (Let (a "v30") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Flight (a "v31") Add [(FAddress (t "v30")); (FValue (Const 136))] (LowerOf (t "v30")));
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v31")]);
      (Let (a "v32") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v33") Add [(FAddress (t "v32")); (FValue (Const 4))] (LowerOf (t "v32")));
      (Let (a "chk6") A (Check 0 4 Read 1) [(t "v33")]);
      (Let (a "v34") W (RawLoad (LdNarrow Sw) 0) [(t "chk6")]);
      (Let (a "v35") W (Cmp Eq W) [(t "v34"); (Const 0)])] (JGoto (To (a "L28"))));
  (mkBlock (a "L28") [(Phi (a "v37") W [((a "L18"), (Const 0)); ((a "L27"), (t "v35"))])] [] (JBranch (t "v37") (To (a "L21")) (To (a "L22"))));
  (mkBlock (a "L21") [] [(Let (a "v38") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v38")]);
      (Let (a "v39") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Flight (a "v40") Add [(FAddress (t "v39")); (FValue (Const 136))] (LowerOf (t "v39")));
      (Let (a "chk8") A (Check 0 8 Read 8) [(t "v40")]);
      (Let (a "v41") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Flight (a "v42") Add [(FAddress (t "v41")); (FValue (Const 8))] (LowerOf (t "v41")));
      (Let (a "chk9") A (Check 0 8 Write 8) [(t "v42")]);
      (RawStorePointer 0 (Const 0) (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v43") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk10") A (Check 0 8 Read 8) [(t "v43")]);
      (Let (a "v44") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")]);
      (Flight (a "v45") Add [(FAddress (t "v44")); (FValue (Const 136))] (LowerOf (t "v44")));
      (Let (a "chk11") A (Check 0 8 Read 8) [(t "v45")]);
      (Let (a "v46") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk11")]);
      (Let (a "chk12") A (Check 0 4 Write 1) [(t "v46")]);
      (RawStore Ww 0 (Const 0) (t "chk12"))] (JGoto (To (a "L101"))));
  (mkBlock (a "L22") [] [(Let (a "v50") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk13") A (Check 0 8 Read 8) [(t "v50")]);
      (Let (a "v51") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk13")]);
      (Flight (a "v52") Add [(FAddress (t "v51")); (FValue (Const 136))] (LowerOf (t "v51")));
      (Let (a "chk14") A (Check 0 8 Read 8) [(t "v52")]);
      (Let (a "v53") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Flight (a "v54") Add [(FAddress (t "v53")); (FValue (Const 4))] (LowerOf (t "v53")));
      (Let (a "chk15") A (Check 0 4 Read 1) [(t "v54")]);
      (Let (a "v55") W (RawLoad (LdNarrow Sw) 0) [(t "chk15")]);
      (Let (a "v56") W (Cmp Eq W) [(t "v55"); (Const 0)])] (JBranch (t "v56") (To (a "L47")) (To (a "L48"))));
  (mkBlock (a "L47") [] [(Let (a "v57") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk16") A (Check 0 8 Read 8) [(t "v57")]);
      (Let (a "v58") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk16")]);
      (Flight (a "v59") Add [(FAddress (t "v58")); (FValue (Const 136))] (LowerOf (t "v58")));
      (Let (a "chk17") A (Check 0 8 Read 8) [(t "v59")]);
      (Let (a "v60") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Flight (a "v61") Add [(FAddress (t "v60")); (FValue (Const 8))] (LowerOf (t "v60")));
      (Let (a "chk18") A (Check 0 8 Write 8) [(t "v61")]);
      (RawStorePointer 0 (Const 0) (t "chk18") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v63") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk19") A (Check 0 8 Read 8) [(t "v63")]);
      (Let (a "v64") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk19")]);
      (Flight (a "v65") Add [(FAddress (t "v64")); (FValue (Const 136))] (LowerOf (t "v64")));
      (Let (a "chk20") A (Check 0 8 Read 8) [(t "v65")]);
      (Let (a "v66") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk20")]);
      (Let (a "chk21") A (Check 0 4 Read 1) [(t "v66")]);
      (Let (a "v70") W (RawLoad (LdNarrow Sw) 0) [(t "chk21")])] (JGoto (To (a "L71"))));
  (mkBlock (a "L71") [(Phi (a "v73") W [((a "L47"), (t "v70")); ((a "L71"), (t "v74"))])] [(Let (a "chk22") A (HalfCheck Lower 0 4 Write 4) [(t "chk21"); (t "v66")]);
      (Let (a "v74") W (RawCas (CasNarrow Sw) 0) [(t "chk22"); (t "v73"); (Const 0)]);
      (Let (a "v75") W (Cmp Eq W) [(t "v74"); (t "v73")])] (JBranch (t "v75") (To (a "L72")) (Poll (a "L71"))));
  (mkBlock (a "L72") [] [(Let (a "v80") W (Cmp Sgt W) [(t "v73"); (Const 1)])] (JBranch (t "v80") (To (a "L83")) (To (a "L101"))));
  (mkBlock (a "L83") [] [(Call CVoid (Global (a "__GI___lll_lock_wake_private")) [(Arg P (t "v66"))])] (JGoto (To (a "L101"))));
  (mkBlock (a "L48") [] [(Let (a "v94") P Copy [(Global (a "glibc_genops#run_fp"))]);
      (Let (a "chk23") A (Check 0 8 Read 8) [(t "v94")]);
      (Let (a "v95") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk23")]);
      (Flight (a "v96") Add [(FAddress (t "v95")); (FValue (Const 136))] (LowerOf (t "v95")));
      (Let (a "chk24") A (Check 0 8 Read 8) [(t "v96")]);
      (Let (a "v97") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk24")]);
      (Flight (a "v98") Add [(FAddress (t "v97")); (FValue (Const 4))] (LowerOf (t "v97")));
      (Let (a "chk25") A (Check 0 4 Read 1) [(t "v98")]);
      (Let (a "v99") W (RawLoad (LdNarrow Sw) 0) [(t "chk25")]);
      (Let (a "v100") W Sub [(t "v99"); (Const 1)]);
      (Let (a "chk26") A (Renew 0 4 Write 1) [(t "chk25"); (t "v98")]);
      (RawStore Ww 0 (t "v100") (t "chk26"))] (JGoto (To (a "L101"))));
  (mkBlock (a "L101") [] [(Let (a "v107") P Copy [(Global (a "__libc_single_threaded_internal"))]);
      (Let (a "chk27") A (Check 0 1 Read 1) [(t "v107")]);
      (Let (a "v108") W (RawLoad (LdNarrow Sb) 0) [(t "chk27")]);
      (Let (a "v109") W (Cmp Ne W) [(t "v108"); (Const 0)])] (JBranch (t "v109") (To (a "L110")) (To (a "L111"))));
  (mkBlock (a "L110") [] [(Let (a "v112") P Copy [(Global (a "glibc_genops#list_all_lock"))]);
      (Flight (a "v113") Add [(FAddress (t "v112")); (FValue (Const 4))] (LowerOf (t "v112")));
      (Let (a "chk28") A (Check 0 4 Read 1) [(t "v113")]);
      (Let (a "v114") W (RawLoad (LdNarrow Sw) 0) [(t "chk28")]);
      (Let (a "v115") W (Cmp Eq W) [(t "v114"); (Const 0)])] (JGoto (To (a "L111"))));
  (mkBlock (a "L111") [(Phi (a "v117") W [((a "L101"), (Const 0)); ((a "L110"), (t "v115"))])] [] (JBranch (t "v117") (To (a "L104")) (To (a "L105"))));
  (mkBlock (a "L104") [] [(Let (a "v118") P Copy [(Global (a "glibc_genops#list_all_lock"))]);
      (Flight (a "v119") Add [(FAddress (t "v118")); (FValue (Const 8))] (LowerOf (t "v118")));
      (Let (a "chk29") A (Check 0 8 Write 8) [(t "v119")]);
      (RawStorePointer 0 (Const 0) (t "chk29") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v120") P Copy [(Global (a "glibc_genops#list_all_lock"))]);
      (Let (a "chk30") A (Check 0 4 Write 1) [(t "v120")]);
      (RawStore Ww 0 (Const 0) (t "chk30"))] (JGoto (To (a "L103"))));
  (mkBlock (a "L105") [] [(Let (a "v124") P Copy [(Global (a "glibc_genops#list_all_lock"))]);
      (Flight (a "v125") Add [(FAddress (t "v124")); (FValue (Const 4))] (LowerOf (t "v124")));
      (Let (a "chk31") A (Check 0 4 Read 1) [(t "v125")]);
      (Let (a "v126") W (RawLoad (LdNarrow Sw) 0) [(t "chk31")]);
      (Let (a "v127") W (Cmp Eq W) [(t "v126"); (Const 0)])] (JBranch (t "v127") (To (a "L121")) (To (a "L122"))));
  (mkBlock (a "L121") [] [(Let (a "v128") P Copy [(Global (a "glibc_genops#list_all_lock"))]);
      (Flight (a "v129") Add [(FAddress (t "v128")); (FValue (Const 8))] (LowerOf (t "v128")));
      (Let (a "chk32") A (Check 0 8 Write 8) [(t "v129")]);
      (RawStorePointer 0 (Const 0) (t "chk32") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v131") P Copy [(Global (a "glibc_genops#list_all_lock"))]);
      (Let (a "chk33") A (Check 0 4 Read 1) [(t "v131")]);
      (Let (a "v135") W (RawLoad (LdNarrow Sw) 0) [(t "chk33")])] (JGoto (To (a "L136"))));
  (mkBlock (a "L136") [(Phi (a "v138") W [((a "L121"), (t "v135")); ((a "L136"), (t "v139"))])] [(Let (a "chk34") A (HalfCheck Lower 0 4 Write 4) [(t "chk33"); (t "v131")]);
      (Let (a "v139") W (RawCas (CasNarrow Sw) 0) [(t "chk34"); (t "v138"); (Const 0)]);
      (Let (a "v140") W (Cmp Eq W) [(t "v139"); (t "v138")])] (JBranch (t "v140") (To (a "L137")) (Poll (a "L136"))));
  (mkBlock (a "L137") [] [(Let (a "v145") W (Cmp Sgt W) [(t "v138"); (Const 1)])] (JBranch (t "v145") (To (a "L148")) (To (a "L103"))));
  (mkBlock (a "L148") [] [(Call CVoid (Global (a "__GI___lll_lock_wake_private")) [(Arg P (t "v131"))])] (JGoto (To (a "L103"))));
  (mkBlock (a "L122") [] [(Let (a "v159") P Copy [(Global (a "glibc_genops#list_all_lock"))]);
      (Flight (a "v160") Add [(FAddress (t "v159")); (FValue (Const 4))] (LowerOf (t "v159")));
      (Let (a "chk35") A (Check 0 4 Read 1) [(t "v160")]);
      (Let (a "v161") W (RawLoad (LdNarrow Sw) 0) [(t "chk35")]);
      (Let (a "v162") W Sub [(t "v161"); (Const 1)]);
      (Let (a "chk36") A (Renew 0 4 Write 1) [(t "chk35"); (t "v160")]);
      (RawStore Ww 0 (t "v162") (t "chk36"))] (JGoto (To (a "L103"))));
  (mkBlock (a "L103") [] [] JRetVoid)].
