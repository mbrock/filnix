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

Definition hello_image_fn___btowc : func :=
  mkFunc (a "__btowc") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v82") P (Alloc 4) [(Const 4)]);
      (Let (a "v83") P (Alloc 8) [(Const 48)]);
      (Let (a "v84") P (Alloc 4) [(Const 1)]);
      (Let (a "v85") P (Alloc 8) [(Const 8)]);
      (Let (a "v86") P (Alloc 8) [(Const 8)]);
      (Let (a "v9") W (Cmp Slt W) [(t "v0"); (Const 4294967168)])] (JBranch (t "v9") (To (a "L11")) (To (a "L10"))));
  (mkBlock (a "L10") [] [(Let (a "v15") W (Cmp Sgt W) [(t "v0"); (Const 255)])] (JGoto (To (a "L11"))));
  (mkBlock (a "L11") [(Phi (a "v17") W [((a "start"), (Const 1)); ((a "L10"), (t "v15"))])] [] (JBranch (t "v17") (To (a "L19")) (To (a "L18"))));
  (mkBlock (a "L18") [] [(Let (a "v22") W (Cmp Eq W) [(t "v0"); (Const 4294967295)])] (JGoto (To (a "L19"))));
  (mkBlock (a "L19") [(Phi (a "v24") W [((a "L11"), (Const 1)); ((a "L18"), (t "v22"))])] [] (JBranch (t "v24") (To (a "L3")) (To (a "L5"))));
  (mkBlock (a "L3") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L5") [] [(Let (a "v31") W And [(t "v0"); (Const 4294967168)]);
      (Let (a "v32") W (Cmp Eq W) [(t "v31"); (Const 0)])] (JBranch (t "v32") (To (a "L26")) (To (a "L28"))));
  (mkBlock (a "L26") [] [] (JRet (t "v0")));
  (mkBlock (a "L28") [] [(Let (a "v35") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v35")]);
      (Let (a "v36") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v36")]);
      (Let (a "v38") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "iw_1.v4") Add [(FAddress (t "v38")); (FValue (Const 32))] (LowerOf (t "v38")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "iw_1.v4")]);
      (Let (a "iw_1.v5") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "iw_1.v5")]);
      (Let (a "iw_1.v10") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Let (a "iw_1.v11") L Ptoi [(t "iw_1.v10")]);
      (Let (a "iw_1.v12") L Ptoi [(Const 0)]);
      (Let (a "iw_1.v13") W (Cmp Eq L) [(t "iw_1.v11"); (t "iw_1.v12")])] (JBranch (t "iw_1.v13") (To (a "iw_1.L6")) (To (a "iw_1.L8"))));
  (mkBlock (a "iw_1.L6") [] [(Call CVoid (Global (a "__wcsmbs_load_conv")) [(Arg P (t "v38"))])] (JGoto (To (a "iw_1.L8"))));
  (mkBlock (a "iw_1.L8") [] [(Let (a "chk4") A (Renew 0 8 Read 8) [(t "chk3"); (t "iw_1.v5")]);
      (Let (a "iw_1.v16") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "iw_1.v16")]);
      (Let (a "v42") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v43") Add [(FAddress (t "v42")); (FValue (Const 48))] (LowerOf (t "v42")));
      (Let (a "chk6") A (Check 0 8 Read 8) [(t "v43")]);
      (Let (a "v44") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v49") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk8") A (Check 0 8 Read 8) [(t "v49")]);
      (Let (a "v50") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "v51") L Ptoi [(t "v50")]);
      (Let (a "v53") W (Cmp Ne L) [(t "v51"); (t "iw_1.v12")])] (JBranch (t "v53") (To (a "L47")) (To (a "L46"))));
  (mkBlock (a "L46") [] [] (JGoto (To (a "L47"))));
  (mkBlock (a "L47") [] [(Flight (a "v59") Add [(FAddress (t "iw_1.v16")); (FValue (Const 8))] (LowerOf (t "iw_1.v16")));
      (Let (a "chk9") A (HalfCheck Upper 0 8 Read 1) [(t "chk5"); (t "v59")]);
      (Let (a "v60") L (RawLoad LdL 0) [(t "chk9")]);
      (Let (a "v61") W (Cmp Eq L) [(t "v60"); (Const 1)])] (JBranch (t "v61") (To (a "L64")) (To (a "L65"))));
  (mkBlock (a "L64") [] [(Let (a "v67") L Ptoi [(t "v44")]);
      (Let (a "v69") W (Cmp Ne L) [(t "v67"); (t "iw_1.v12")])] (JGoto (To (a "L65"))));
  (mkBlock (a "L65") [(Phi (a "v73") W [((a "L47"), (Const 0)); ((a "L64"), (t "v69"))])] [] (JBranch (t "v73") (To (a "iw_2.join")) (To (a "L56"))));
  (mkBlock (a "iw_2.join") [] [(Let (a "v77") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "v79") W (Ext Ub) [(t "v0")]);
      (Let (a "chk11") F CheckFunction [(t "v44")]);
      (RawCall (CResult (a "v80") W) (t "chk11") [(Arg P (t "v77")); (Arg W (t "v79"))])] (JRet (t "v80")));
  (mkBlock (a "L56") [] [(Let (a "chk12") A (Check 0 8 Write 8) [(t "v85")]);
      (RawStorePointer 0 (t "v84") (t "chk12") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk13") A (Check 0 8 Write 8) [(t "v83")]);
      (RawStorePointer 0 (t "v82") (t "chk13") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v88") Add [(FAddress (t "v83")); (FValue (Const 8))] (LowerOf (t "v83")));
      (Let (a "chk14") A (Renew 0 8 Read 8) [(t "chk13"); (t "v83")]);
      (Let (a "v89") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Flight (a "v90") Add [(FAddress (t "v89")); (FValue (Const 4))] (LowerOf (t "v89")));
      (Let (a "chk15") A (HalfCheck Upper 0 8 Write 8) [(t "chk13"); (t "v88")]);
      (RawStorePointer 0 (t "v90") (t "chk15") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v91") Add [(FAddress (t "v83")); (FValue (Const 20))] (LowerOf (t "v83")));
      (Let (a "chk16") A (HalfCheck Upper 0 4 Write 1) [(t "chk13"); (t "v91")]);
      (RawStore Ww 0 (Const 0) (t "chk16"));
      (Flight (a "v92") Add [(FAddress (t "v83")); (FValue (Const 24))] (LowerOf (t "v83")));
      (Let (a "chk17") A (HalfCheck Upper 0 4 Write 1) [(t "chk13"); (t "v92")]);
      (RawStore Ww 0 (Const 1) (t "chk17"));
      (Flight (a "v93") Add [(FAddress (t "v83")); (FValue (Const 16))] (LowerOf (t "v83")));
      (Let (a "chk18") A (HalfCheck Upper 0 4 Write 1) [(t "chk13"); (t "v93")]);
      (RawStore Ww 0 (Const 1) (t "chk18"));
      (Flight (a "v94") Add [(FAddress (t "v83")); (FValue (Const 32))] (LowerOf (t "v83")));
      (Flight (a "v95") Add [(FAddress (t "v83")); (FValue (Const 40))] (LowerOf (t "v83")));
      (Let (a "chk19") A (HalfCheck Upper 0 8 Write 8) [(t "chk13"); (t "v94")]);
      (RawStorePointer 0 (t "v95") (t "chk19") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Call (CResult (a "v97") P) (Global (a "__GI_memset")) [(Arg P (t "v95")); (Arg W (Const 0)); (Arg L (Const 8))]);
      (Let (a "v100") W (Ext Ub) [(t "v0")]);
      (Let (a "chk20") A (Check 0 1 Write 1) [(t "v84")]);
      (RawStore Wb 0 (t "v100") (t "chk20"));
      (Let (a "chk21") A (Renew 0 8 Read 8) [(t "chk5"); (t "iw_1.v16")]);
      (Let (a "v103") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Flight (a "v104") Add [(FAddress (t "v103")); (FValue (Const 40))] (LowerOf (t "v103")));
      (Let (a "chk22") A (Check 0 8 Read 8) [(t "v104")]);
      (Let (a "v105") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk22")]);
      (Let (a "v110") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Let (a "chk24") A (Check 0 8 Read 8) [(t "v110")]);
      (Let (a "v111") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk24")]);
      (Let (a "v112") L Ptoi [(t "v111")]);
      (Let (a "v114") W (Cmp Ne L) [(t "v112"); (t "iw_1.v12")])] (JBranch (t "v114") (To (a "iw_3.join")) (To (a "L107"))));
  (mkBlock (a "L107") [] [] (JGoto (To (a "iw_3.join"))));
  (mkBlock (a "iw_3.join") [] [(Let (a "v119") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Let (a "chk26") A (Renew 0 8 Read 8) [(t "chk12"); (t "v85")]);
      (Let (a "v120") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk26")]);
      (Flight (a "v121") Add [(FAddress (t "v120")); (FValue (Const 1))] (LowerOf (t "v120")));
      (Let (a "chk27") F CheckFunction [(t "v105")]);
      (RawCall (CResult (a "v122") W) (t "chk27") [(Arg P (t "v119")); (Arg P (t "v83")); (Arg P (t "v85")); (Arg P (t "v121")); (Arg P (Const 0)); (Arg P (t "v86")); (Arg W (Const 0)); (Arg W (Const 1))]);
      (Let (a "v127") W (Cmp Ne W) [(t "v122"); (Const 0)])] (JBranch (t "v127") (To (a "L128")) (To (a "L129"))));
  (mkBlock (a "L128") [] [(Let (a "v131") W (Cmp Ne W) [(t "v122"); (Const 5)])] (JGoto (To (a "L129"))));
  (mkBlock (a "L129") [(Phi (a "v133") W [((a "iw_3.join"), (Const 0)); ((a "L128"), (t "v131"))])] [] (JBranch (t "v133") (To (a "L134")) (To (a "L135"))));
  (mkBlock (a "L134") [] [(Let (a "v137") W (Cmp Ne W) [(t "v122"); (Const 4)])] (JGoto (To (a "L135"))));
  (mkBlock (a "L135") [(Phi (a "v139") W [((a "L129"), (Const 0)); ((a "L134"), (t "v137"))])] [] (JBranch (t "v139") (To (a "L123")) (To (a "L125"))));
  (mkBlock (a "L123") [] [(Let (a "chk28") A (Check 0 4 Write 1) [(t "v82")]);
      (RawStore Ww 0 (Const (-1)) (t "chk28"))] (JGoto (To (a "L125"))));
  (mkBlock (a "L125") [] [(Let (a "chk29") A (Check 0 4 Read 1) [(t "v82")]);
      (Let (a "v140") W (RawLoad (LdNarrow Sw) 0) [(t "chk29")])] (JRet (t "v140")))].
