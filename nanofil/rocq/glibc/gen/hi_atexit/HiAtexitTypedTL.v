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

Definition hi_fn___tls_init_tp : func :=
  mkFunc (a "__tls_init_tp") (a "export") RVoid [] [(mkBlock (a "start") [] [(Call (CResult (a "v1") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "v3") Add [(FAddress (t "v1")); (FValue (Const 720))] (LowerOf (t "v1")));
      (Call (CResult (a "v4") W) (Global (a "zthread_self_id")) []);
      (Let (a "chk0") A (Check 0 4 Write 1) [(t "v3")]);
      (RawStore Ww 0 (t "v4") (t "chk0"));
      (Flight (a "v6") Add [(FAddress (t "v1")); (FValue (Const 728))] (LowerOf (t "v1")));
      (Call (CResult (a "v7") P) (Global (a "zthread_self")) []);
      (Let (a "chk1") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v6")]);
      (RawStorePointer 0 (t "v7") (t "chk1") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v9") Add [(FAddress (t "v1")); (FValue (Const 736))] (LowerOf (t "v1")));
      (Let (a "chk2") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "v9")]);
      (RawStore Ww 0 (Const 0) (t "chk2"));
      (Flight (a "v11") Add [(FAddress (t "v1")); (FValue (Const 1312))] (LowerOf (t "v1")));
      (Flight (a "v14") Add [(FAddress (t "v1")); (FValue (Const 800))] (LowerOf (t "v1")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v11")]);
      (RawStorePointer 0 (t "v14") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v17") Add [(FAddress (t "v1")); (FValue (Const 1572))] (LowerOf (t "v1")));
      (Let (a "chk4") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "v17")]);
      (RawStore Ww 0 (Const 2) (t "chk4"));
      (Flight (a "v19") Add [(FAddress (t "v1")); (FValue (Const 1592))] (LowerOf (t "v1")));
      (Let (a "chk5") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "v19")]);
      (RawStore Ww 0 (Const 2) (t "chk5"));
      (Flight (a "v21") Add [(FAddress (t "v1")); (FValue (Const 1569))] (LowerOf (t "v1")));
      (Let (a "v22") P Copy [(Global (a "__nptl_initial_report_events"))]);
      (Let (a "chk6") A (Check 0 1 Read 1) [(t "v22")]);
      (Let (a "v23") W (RawLoad (LdNarrow Ub) 0) [(t "chk6")]);
      (Let (a "chk7") A (HalfCheck Upper 0 1 Write 1) [(t "chk0"); (t "v21")]);
      (RawStore Wb 0 (t "v23") (t "chk7"));
      (Flight (a "v25") Add [(FAddress (t "v1")); (FValue (Const 744))] (LowerOf (t "v1")));
      (Flight (a "v27") Add [(FAddress (t "v1")); (FValue (Const 752))] (LowerOf (t "v1")));
      (Let (a "chk8") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v25")]);
      (RawStorePointer 0 (t "v27") (t "chk8") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk9") A (HalfCheck Upper 0 8 Write 8) [(t "chk0"); (t "v27")]);
      (RawStorePointer 0 (t "v27") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v34") Add [(FAddress (t "v27")); (FValue (Const 8))] (LowerOf (t "v27")));
      (Let (a "chk10") A (HalfCheck Upper 0 8 Write 1) [(t "chk9"); (t "v34")]);
      (RawStore Wl 0 (Const 18446744073709551584) (t "chk10"));
      (Flight (a "v37") Add [(FAddress (t "v1")); (FValue (Const 1720))] (LowerOf (t "v1")));
      (Let (a "v38") P Copy [(Global (a "__libc_stack_end"))]);
      (Let (a "chk11") A (Check 0 8 Read 8) [(t "v38")]);
      (Let (a "v39") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk11")]);
      (Let (a "v40") L Ptoi [(t "v39")]);
      (Let (a "chk12") A (HalfCheck Upper 0 8 Write 1) [(t "chk0"); (t "v37")]);
      (RawStore Wl 0 (t "v40") (t "chk12"))] JRetVoid)].
