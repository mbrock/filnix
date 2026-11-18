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

Definition hello_image_fn___GI___futex_abstimed_wait64 : func :=
  mkFunc (a "__GI___futex_abstimed_wait64") (a "export") (RClass W) [(P, (a "v0")); (W, (a "v2")); (W, (a "v4")); (P, (a "v6")); (W, (a "v8"))] [(mkBlock (a "start") [] [(Let (a "v21") W (Cmp Eq W) [(t "v8"); (Const 0)])] (JBranch (t "v21") (To (a "L23")) (To (a "L22"))));
  (mkBlock (a "L22") [] [(Let (a "v25") W (Cmp Eq W) [(t "v8"); (Const 128)])] (JGoto (To (a "L23"))));
  (mkBlock (a "L23") [(Phi (a "v27") W [((a "start"), (Const 1)); ((a "L22"), (t "v25"))])] [] (JBranch (t "v27") (To (a "L16")) (To (a "L19"))));
  (mkBlock (a "L19") [] [(Let (a "v29") P Copy [(Global (a "glibc_futex_internal#str.244"))]);
      (Let (a "v30") P Copy [(Global (a "glibc_futex_internal#str.245"))]);
      (Let (a "v31") P Copy [(Global (a "glibc_futex_internal#str.246"))]);
      (Let (a "v32") P Copy [(Global (a "glibc_futex_internal#str.247"))]);
      (Call CVoid (Global (a "zerrorf")) [(Arg P (t "v29")); (Arg P (t "v30")); (Arg W (Const 31)); (Arg P (t "v31")); (Arg P (t "v32"))])] (JGoto (To (a "L16"))));
  (mkBlock (a "L16") [] [] (JBranch (t "v21") (To (a "L35")) (To (a "L34"))));
  (mkBlock (a "L34") [] [] (JGoto (To (a "L35"))));
  (mkBlock (a "L35") [(Phi (a "v38") W [((a "L34"), (Const 0)); ((a "L16"), (Const 1))])] [(Call (CResult (a "v39") W) (Global (a "zsys_futex_timedwait")) [(Arg P (t "v0")); (Arg W (t "v2")); (Arg W (t "v4")); (Arg P (t "v6")); (Arg W (t "v38"))])] (JRet (t "v39")))].

Definition hello_image_fn___GI___funlockfile : func :=
  mkFunc (a "__GI___funlockfile") (a "export") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v8") P Copy [(Global (a "__libc_single_threaded_internal"))]);
      (Let (a "chk0") A (Check 0 1 Read 1) [(t "v8")]);
      (Let (a "v9") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "v10") W (Cmp Ne W) [(t "v9"); (Const 0)])] (JBranch (t "v10") (To (a "L11")) (To (a "L12"))));
  (mkBlock (a "L11") [] [(Flight (a "v14") Add [(FAddress (t "v0")); (FValue (Const 136))] (LowerOf (t "v0")));
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v14")]);
      (Let (a "v15") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v16") Add [(FAddress (t "v15")); (FValue (Const 4))] (LowerOf (t "v15")));
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "v16")]);
      (Let (a "v17") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v18") W (Cmp Eq W) [(t "v17"); (Const 0)])] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [(Phi (a "v20") W [((a "start"), (Const 0)); ((a "L11"), (t "v18"))])] [] (JBranch (t "v20") (To (a "L5")) (To (a "L6"))));
  (mkBlock (a "L5") [] [(Flight (a "v22") Add [(FAddress (t "v0")); (FValue (Const 136))] (LowerOf (t "v0")));
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v22")]);
      (Let (a "v23") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "v24") Add [(FAddress (t "v23")); (FValue (Const 8))] (LowerOf (t "v23")));
      (Let (a "chk4") A (Check 0 8 Write 8) [(t "v24")]);
      (RawStorePointer 0 (Const 0) (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk5") A (Renew 0 8 Read 8) [(t "chk3"); (t "v22")]);
      (Let (a "v27") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk6") A (Check 0 4 Write 1) [(t "v27")]);
      (RawStore Ww 0 (Const 0) (t "chk6"))] (JGoto (To (a "L4"))));
  (mkBlock (a "L6") [] [(Flight (a "v32") Add [(FAddress (t "v0")); (FValue (Const 136))] (LowerOf (t "v0")));
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v32")]);
      (Let (a "v33") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Flight (a "v34") Add [(FAddress (t "v33")); (FValue (Const 4))] (LowerOf (t "v33")));
      (Let (a "chk8") A (Check 0 4 Read 1) [(t "v34")]);
      (Let (a "v35") W (RawLoad (LdNarrow Sw) 0) [(t "chk8")]);
      (Let (a "v36") W (Cmp Eq W) [(t "v35"); (Const 0)])] (JBranch (t "v36") (To (a "L28")) (To (a "L29"))));
  (mkBlock (a "L28") [] [(Flight (a "v38") Add [(FAddress (t "v0")); (FValue (Const 136))] (LowerOf (t "v0")));
      (Let (a "v39") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Flight (a "v40") Add [(FAddress (t "v39")); (FValue (Const 8))] (LowerOf (t "v39")));
      (Let (a "chk10") A (Check 0 8 Write 8) [(t "v40")]);
      (RawStorePointer 0 (Const 0) (t "chk10") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk11") A (Renew 0 8 Read 8) [(t "chk7"); (t "v38")]);
      (Let (a "v44") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk11")]);
      (Let (a "chk12") A (Check 0 4 Read 1) [(t "v44")]);
      (Let (a "v48") W (RawLoad (LdNarrow Sw) 0) [(t "chk12")])] (JGoto (To (a "L49"))));
  (mkBlock (a "L49") [(Phi (a "v51") W [((a "L28"), (t "v48")); ((a "L49"), (t "v52"))])] [(Let (a "chk13") A (HalfCheck Lower 0 4 Write 4) [(t "chk12"); (t "v44")]);
      (Let (a "v52") W (RawCas (CasNarrow Sw) 0) [(t "chk13"); (t "v51"); (Const 0)]);
      (Let (a "v53") W (Cmp Eq W) [(t "v52"); (t "v51")])] (JBranch (t "v53") (To (a "L50")) (Poll (a "L49"))));
  (mkBlock (a "L50") [] [(Let (a "v58") W (Cmp Sgt W) [(t "v51"); (Const 1)])] (JBranch (t "v58") (To (a "L61")) (To (a "L4"))));
  (mkBlock (a "L61") [] [(Call CVoid (Global (a "__GI___lll_lock_wake_private")) [(Arg P (t "v44"))])] (JGoto (To (a "L4"))));
  (mkBlock (a "L29") [] [(Flight (a "v73") Add [(FAddress (t "v0")); (FValue (Const 136))] (LowerOf (t "v0")));
      (Let (a "v74") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Flight (a "v75") Add [(FAddress (t "v74")); (FValue (Const 4))] (LowerOf (t "v74")));
      (Let (a "chk15") A (Check 0 4 Read 1) [(t "v75")]);
      (Let (a "v76") W (RawLoad (LdNarrow Sw) 0) [(t "chk15")]);
      (Let (a "v77") W Sub [(t "v76"); (Const 1)]);
      (Let (a "chk16") A (Renew 0 4 Write 1) [(t "chk15"); (t "v75")]);
      (RawStore Ww 0 (t "v77") (t "chk16"))] (JGoto (To (a "L4"))));
  (mkBlock (a "L4") [] [] JRetVoid)].

Definition hello_image_fn_glibc_libc_start'23futex_wake : func :=
  mkFunc (a "glibc_libc_start#futex_wake") (a "local") RVoid [(P, (a "v0")); (W, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v16") W (Cmp Eq W) [(t "v4"); (Const 0)])] (JBranch (t "v16") (To (a "L18")) (To (a "L17"))));
  (mkBlock (a "L17") [] [(Let (a "v20") W (Cmp Eq W) [(t "v4"); (Const 128)])] (JGoto (To (a "L18"))));
  (mkBlock (a "L18") [(Phi (a "v22") W [((a "start"), (Const 1)); ((a "L17"), (t "v20"))])] [] (JBranch (t "v22") (To (a "L11")) (To (a "L14"))));
  (mkBlock (a "L14") [] [(Let (a "v24") P Copy [(Global (a "glibc_libc_start#str.322"))]);
      (Let (a "v25") P Copy [(Global (a "glibc_libc_start#str.323"))]);
      (Let (a "v26") P Copy [(Global (a "glibc_libc_start#str.324"))]);
      (Let (a "v27") P Copy [(Global (a "glibc_libc_start#str.325"))]);
      (Call CVoid (Global (a "zerrorf")) [(Arg P (t "v24")); (Arg P (t "v25")); (Arg W (Const 173)); (Arg P (t "v26")); (Arg P (t "v27"))])] (JGoto (To (a "L11"))));
  (mkBlock (a "L11") [] [] (JBranch (t "v16") (To (a "L30")) (To (a "L29"))));
  (mkBlock (a "L29") [] [] (JGoto (To (a "L30"))));
  (mkBlock (a "L30") [(Phi (a "v33") W [((a "L29"), (Const 0)); ((a "L11"), (Const 1))])] [(Call CVoid (Global (a "zsys_futex_wake")) [(Arg P (t "v0")); (Arg W (t "v2")); (Arg W (t "v33"))])] JRetVoid)].
