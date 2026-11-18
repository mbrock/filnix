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

Definition hello_image_fn___vasprintf_internal : func :=
  mkFunc (a "__vasprintf_internal") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (W, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v8") P (Alloc 8) [(Const 240)]);
      (Flight (a "v9") Add [(FAddress (t "v8")); (FValue (Const 40))] (LowerOf (t "v8")));
      (Flight (a "iw_1.v12") Add [(FAddress (t "v9")); (FValue (Const 200))] (LowerOf (t "v9")));
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (t "v9") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_1.iw_1.v11") Add [(FAddress (t "v8")); (FValue (Const 8))] (LowerOf (t "v8")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "iw_1.iw_1.v11")]);
      (RawStorePointer 0 (t "v9") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_1.iw_1.v14") Add [(FAddress (t "v8")); (FValue (Const 16))] (LowerOf (t "v8")));
      (Let (a "chk2") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "iw_1.iw_1.v14")]);
      (RawStorePointer 0 (t "iw_1.v12") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_1.iw_1.v17") Add [(FAddress (t "v8")); (FValue (Const 24))] (LowerOf (t "v8")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Write 1) [(t "chk0"); (t "iw_1.iw_1.v17")]);
      (RawStore Wl 0 (Const 0) (t "chk3"));
      (Flight (a "iw_1.iw_1.v19") Add [(FAddress (t "v8")); (FValue (Const 32))] (LowerOf (t "v8")));
      (Let (a "chk4") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "iw_1.iw_1.v19")]);
      (RawStore Ww 0 (Const 5) (t "chk4"));
      (Call CVoid (Global (a "__printf_buffer")) [(Arg P (t "v8")); (Arg P (t "v2")); (Arg P (t "v4")); (Arg W (t "v6"))]);
      (Call (CResult (a "v17") W) (Global (a "__printf_buffer_done")) [(Arg P (t "v8"))]);
      (Let (a "v22") W (Cmp Slt W) [(t "v17"); (Const 0)])] (JBranch (t "v22") (To (a "L18")) (To (a "L20"))));
  (mkBlock (a "L18") [] [(Let (a "chk5") A (Renew 0 8 Read 8) [(t "chk0"); (t "v8")]);
      (Let (a "v26") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v27") Add [(FAddress (t "v8")); (FValue (Const 40))] (LowerOf (t "v8")));
      (Let (a "v28") L Ptoi [(t "v26")]);
      (Let (a "v29") L Ptoi [(t "v27")]);
      (Let (a "v30") W (Cmp Ne L) [(t "v28"); (t "v29")])] (JBranch (t "v30") (To (a "L23")) (To (a "L25"))));
  (mkBlock (a "L23") [] [(Let (a "v31") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "v31"))])] (JGoto (To (a "L25"))));
  (mkBlock (a "L25") [] [(Let (a "chk7") A (Check 0 8 Write 8) [(t "v0")]);
      (RawStorePointer 0 (Const 0) (t "chk7") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JRet (t "v17")));
  (mkBlock (a "L20") [] [(Flight (a "v36") Add [(FAddress (t "v8")); (FValue (Const 8))] (LowerOf (t "v8")));
      (Let (a "chk8") A (Renew 0 8 Read 8) [(t "chk1"); (t "v36")]);
      (Let (a "v37") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk9") A (Renew 0 8 Read 8) [(t "chk0"); (t "v8")]);
      (Let (a "v38") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Let (a "v39") L Ptoi [(t "v37")]);
      (Let (a "v40") L Ptoi [(t "v38")]);
      (Let (a "v41") L Sub [(t "v39"); (t "v40")]);
      (Let (a "v45") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Flight (a "v46") Add [(FAddress (t "v8")); (FValue (Const 40))] (LowerOf (t "v8")));
      (Let (a "v47") L Ptoi [(t "v45")]);
      (Let (a "v48") L Ptoi [(t "v46")]);
      (Let (a "v49") W (Cmp Eq L) [(t "v47"); (t "v48")])] (JBranch (t "v49") (To (a "L42")) (To (a "L43"))));
  (mkBlock (a "L42") [] [(Let (a "v52") L Add [(t "v41"); (Const 1)]);
      (Call (CResult (a "v53") P) (Global (a "malloc")) [(Arg L (t "v52"))]);
      (Let (a "chk11") A (Check 0 8 Write 8) [(t "v0")]);
      (RawStorePointer 0 (t "v53") (t "chk11") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk12") A (Renew 0 8 Read 8) [(t "chk11"); (t "v0")]);
      (Let (a "v58") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk12")]);
      (Let (a "v59") L Ptoi [(t "v58")]);
      (Let (a "v60") L Ptoi [(Const 0)]);
      (Let (a "v61") W (Cmp Eq L) [(t "v59"); (t "v60")])] (JBranch (t "v61") (To (a "L54")) (To (a "L56"))));
  (mkBlock (a "L54") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L56") [] [(Let (a "v65") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk12")]);
      (Flight (a "v66") Add [(FAddress (t "v8")); (FValue (Const 40))] (LowerOf (t "v8")));
      (Call (CResult (a "v68") P) (Global (a "__GI_memcpy")) [(Arg P (t "v65")); (Arg P (t "v66")); (Arg L (t "v41"))])] (JGoto (To (a "L44"))));
  (mkBlock (a "L43") [] [(Let (a "v70") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Let (a "v72") L Add [(t "v41"); (Const 1)]);
      (Call (CResult (a "v73") P) (Global (a "realloc")) [(Arg P (t "v70")); (Arg L (t "v72"))]);
      (Let (a "chk15") A (Check 0 8 Write 8) [(t "v0")]);
      (RawStorePointer 0 (t "v73") (t "chk15") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk16") A (Renew 0 8 Read 8) [(t "chk15"); (t "v0")]);
      (Let (a "v78") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk16")]);
      (Let (a "v79") L Ptoi [(t "v78")]);
      (Let (a "v80") L Ptoi [(Const 0)]);
      (Let (a "v81") W (Cmp Eq L) [(t "v79"); (t "v80")])] (JBranch (t "v81") (To (a "L74")) (To (a "L44"))));
  (mkBlock (a "L74") [] [(Let (a "chk17") A (Renew 0 8 Read 8) [(t "chk0"); (t "v8")]);
      (Let (a "v82") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "v82"))])] (JRet (Const 4294967295)));
  (mkBlock (a "L44") [] [(Let (a "chk18") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v86") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk18")]);
      (Flight (a "v88") Add [(FAddress (t "v86")); (FValue (t "v41"))] (LowerOf (t "v86")));
      (Let (a "chk19") A (Check 0 1 Write 1) [(t "v88")]);
      (RawStore Wb 0 (Const 0) (t "chk19"))] (JRet (t "v17")))].
