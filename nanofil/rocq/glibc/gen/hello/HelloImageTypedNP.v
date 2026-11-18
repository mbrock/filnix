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

Definition hello_image_fn___GI___nptl_deallocate_tsd : func :=
  mkFunc (a "__GI___nptl_deallocate_tsd") (a "export") RVoid [] [(mkBlock (a "start") [] [(Call (CResult (a "v1") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "v6") Add [(FAddress (t "v1")); (FValue (Const 1568))] (LowerOf (t "v1")));
      (Let (a "chk0") A (Check 0 1 Read 1) [(t "v6")]);
      (Let (a "v7") W (RawLoad (LdNarrow Ub) 0) [(t "chk0")])] (JBranch (t "v7") (To (a "L10")) (To (a "L4"))));
  (mkBlock (a "L10") [(Phi (a "pr.1") L [((a "L11"), (t "v123")); ((a "start"), (Const 0))])] [(Flight (a "v15") Add [(FAddress (t "v1")); (FValue (Const 1568))] (LowerOf (t "v1")));
      (Let (a "chk1") A (Renew 0 1 Write 1) [(t "chk0"); (t "v15")]);
      (RawStore Wb 0 (Const 0) (t "chk1"))] (JGoto (To (a "L17"))));
  (mkBlock (a "L17") [(Phi (a "pr.4") L [((a "L10"), (Const 0)); ((a "L36"), (t "pr.5"))]); (Phi (a "pr.3") L [((a "L10"), (Const 0)); ((a "L36"), (t "v112"))])] [(Let (a "v26") W (Cmp Ult L) [(t "pr.3"); (Const 32)])] (JBranch (t "v26") (To (a "L18")) (To (a "L20"))));
  (mkBlock (a "L18") [] [(Flight (a "v29") Add [(FAddress (t "v1")); (FValue (Const 1312))] (LowerOf (t "v1")));
      (Let (a "v31") L Shl [(t "pr.3"); (Const 3)]);
      (Flight (a "v32") Add [(FAddress (t "v29")); (FValue (t "v31"))] (LowerOf (t "v29")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v32")]);
      (Let (a "v33") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v38") L Ptoi [(t "v33")]);
      (Let (a "v39") L Ptoi [(Const 0)]);
      (Let (a "v40") W (Cmp Ne L) [(t "v38"); (t "v39")])] (JBranch (t "v40") (To (a "L42")) (To (a "L35"))));
  (mkBlock (a "L42") [(Phi (a "pr.7") L [((a "L44"), (t "v102")); ((a "L18"), (Const 0))]); (Phi (a "pr.6") L [((a "L44"), (t "v104")); ((a "L18"), (t "pr.4"))])] [(Let (a "v47") W (Cmp Ult L) [(t "pr.7"); (Const 32)])] (JBranch (t "v47") (To (a "L43")) (To (a "L36"))));
  (mkBlock (a "L43") [] [(Let (a "v51") L Shl [(t "pr.7"); (Const 4)]);
      (Flight (a "v52") Add [(FAddress (t "v33")); (FValue (t "v51"))] (LowerOf (t "v33")));
      (Flight (a "v53") Add [(FAddress (t "v52")); (FValue (Const 8))] (LowerOf (t "v52")));
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v53")]);
      (Let (a "v54") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Let (a "v59") L Ptoi [(t "v54")]);
      (Let (a "v61") W (Cmp Ne L) [(t "v59"); (t "v39")])] (JBranch (t "v61") (To (a "L55")) (To (a "L44"))));
  (mkBlock (a "L55") [] [(Flight (a "v66") Add [(FAddress (t "v52")); (FValue (Const 8))] (LowerOf (t "v52")));
      (Let (a "chk4") A (Renew 0 8 Write 8) [(t "chk3"); (t "v66")]);
      (RawStorePointer 0 (Const 0) (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk5") A (HalfCheck Lower 0 8 Read 1) [(t "chk3"); (t "v52")]);
      (Let (a "v74") L (RawLoad LdL 0) [(t "chk5")]);
      (Let (a "v75") P Copy [(Global (a "__GI___pthread_keys"))]);
      (Let (a "v77") L Shl [(t "pr.6"); (Const 4)]);
      (Flight (a "v78") Add [(FAddress (t "v75")); (FValue (t "v77"))] (LowerOf (t "v75")));
      (Let (a "chk6") A (Check 0 8 Read 1) [(t "v78")]);
      (Let (a "v79") L (RawLoad LdL 0) [(t "chk6")]);
      (Let (a "v80") W (Cmp Eq L) [(t "v74"); (t "v79")])] (JBranch (t "v80") (To (a "L81")) (To (a "L82"))));
  (mkBlock (a "L81") [] [(Let (a "v83") P Copy [(Global (a "__GI___pthread_keys"))]);
      (Flight (a "v86") Add [(FAddress (t "v83")); (FValue (t "v77"))] (LowerOf (t "v83")));
      (Flight (a "v87") Add [(FAddress (t "v86")); (FValue (Const 8))] (LowerOf (t "v86")));
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v87")]);
      (Let (a "v88") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Let (a "v89") L Ptoi [(t "v88")]);
      (Let (a "v91") W (Cmp Ne L) [(t "v89"); (t "v39")])] (JGoto (To (a "L82"))));
  (mkBlock (a "L82") [(Phi (a "v93") W [((a "L55"), (Const 0)); ((a "L81"), (t "v91"))])] [] (JBranch (t "v93") (To (a "L67")) (To (a "L44"))));
  (mkBlock (a "L67") [] [(Let (a "v94") P Copy [(Global (a "__GI___pthread_keys"))]);
      (Flight (a "v97") Add [(FAddress (t "v94")); (FValue (t "v77"))] (LowerOf (t "v94")));
      (Flight (a "v98") Add [(FAddress (t "v97")); (FValue (Const 8))] (LowerOf (t "v97")));
      (Let (a "chk8") A (Check 0 8 Read 8) [(t "v98")]);
      (Let (a "v99") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk9") F CheckFunction [(t "v99")]);
      (RawCall CVoid (t "chk9") [(Arg P (t "v54"))])] (JGoto (To (a "L44"))));
  (mkBlock (a "L44") [] [(Let (a "v102") L Add [(t "pr.7"); (Const 1)]);
      (Let (a "v104") L Add [(t "pr.6"); (Const 1)])] (JGoto (Poll (a "L42"))));
  (mkBlock (a "L35") [] [(Let (a "v110") L Add [(t "pr.4"); (Const 32)])] (JGoto (To (a "L36"))));
  (mkBlock (a "L36") [(Phi (a "pr.5") L [((a "L35"), (t "v110")); ((a "L42"), (t "pr.6"))])] [(Let (a "v112") L Add [(t "pr.3"); (Const 1)])] (JGoto (Poll (a "L17"))));
  (mkBlock (a "L20") [] [(Flight (a "v117") Add [(FAddress (t "v1")); (FValue (Const 1568))] (LowerOf (t "v1")));
      (Let (a "chk10") A (Renew 0 1 Read 1) [(t "chk0"); (t "v117")]);
      (Let (a "v118") W (RawLoad (LdNarrow Ub) 0) [(t "chk10")]);
      (Let (a "v119") W (Cmp Eq W) [(t "v118"); (Const 0)])] (JBranch (t "v119") (To (a "L130")) (To (a "L11"))));
  (mkBlock (a "L11") [] [(Let (a "v123") L Add [(t "pr.1"); (Const 1)]);
      (Let (a "v124") W (Cmp Ult L) [(t "v123"); (Const 4)])] (JBranch (t "v124") (Poll (a "L10")) (To (a "L12"))));
  (mkBlock (a "L12") [] [(Call (CResult (a "v127") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "v128") Add [(FAddress (t "v127")); (FValue (Const 800))] (LowerOf (t "v127")));
      (Call (CResult (a "v129") P) (Global (a "__GI_memset")) [(Arg P (t "v128")); (Arg W (Const 0)); (Arg L (Const 512))])] (JGoto (To (a "L130"))));
  (mkBlock (a "L130") [(Phi (a "pr.2") L [((a "L132"), (t "v161")); ((a "L12"), (Const 1)); ((a "L20"), (Const 1))])] [(Let (a "v139") W (Cmp Ult L) [(t "pr.2"); (Const 32)])] (JBranch (t "v139") (To (a "L131")) (To (a "L133"))));
  (mkBlock (a "L131") [] [(Flight (a "v142") Add [(FAddress (t "v1")); (FValue (Const 1312))] (LowerOf (t "v1")));
      (Let (a "v144") L Shl [(t "pr.2"); (Const 3)]);
      (Flight (a "v145") Add [(FAddress (t "v142")); (FValue (t "v144"))] (LowerOf (t "v142")));
      (Let (a "chk11") A (Check 0 8 Read 8) [(t "v145")]);
      (Let (a "v146") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk11")]);
      (Let (a "v151") L Ptoi [(t "v146")]);
      (Let (a "v152") L Ptoi [(Const 0)]);
      (Let (a "v153") W (Cmp Ne L) [(t "v151"); (t "v152")])] (JBranch (t "v153") (To (a "L147")) (To (a "L132"))));
  (mkBlock (a "L147") [] [(Call CVoid (Global (a "free")) [(Arg P (t "v146"))]);
      (Flight (a "v156") Add [(FAddress (t "v1")); (FValue (Const 1312))] (LowerOf (t "v1")));
      (Flight (a "v159") Add [(FAddress (t "v156")); (FValue (t "v144"))] (LowerOf (t "v156")));
      (Let (a "chk12") A (Check 0 8 Write 8) [(t "v159")]);
      (RawStorePointer 0 (Const 0) (t "chk12") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L132"))));
  (mkBlock (a "L132") [] [(Let (a "v161") L Add [(t "pr.2"); (Const 1)])] (JGoto (Poll (a "L130"))));
  (mkBlock (a "L133") [] [(Flight (a "v163") Add [(FAddress (t "v1")); (FValue (Const 1568))] (LowerOf (t "v1")));
      (Let (a "chk13") A (Renew 0 1 Write 1) [(t "chk0"); (t "v163")]);
      (RawStore Wb 0 (Const 0) (t "chk13"))] (JGoto (To (a "L4"))));
  (mkBlock (a "L4") [] [] JRetVoid)].
