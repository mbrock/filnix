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

Definition hello_image_fn_glibc_vfprintf_internal'23scratch_buffer_free : func :=
  mkFunc (a "glibc_vfprintf_internal#scratch_buffer_free") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v6") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v8") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "v9") L Ptoi [(t "v6")]);
      (Let (a "v10") L Ptoi [(t "v8")]);
      (Let (a "v11") W (Cmp Ne L) [(t "v9"); (t "v10")])] (JBranch (t "v11") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [(Let (a "v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "v13"))])] (JGoto (To (a "L4"))));
  (mkBlock (a "L4") [] [] JRetVoid)].

Definition hello_image_fn_glibc_vfprintf_internal'23scratch_buffer_init : func :=
  mkFunc (a "glibc_vfprintf_internal#scratch_buffer_init") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v4") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v0")]);
      (RawStorePointer 0 (t "v4") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v6") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Write 1) [(t "chk0"); (t "v6")]);
      (RawStore Wl 0 (Const 1024) (t "chk1"))] JRetVoid)].

Definition hello_image_fn_glibc_vfwprintf_internal'23scratch_buffer_free : func :=
  mkFunc (a "glibc_vfwprintf_internal#scratch_buffer_free") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v6") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v8") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "v9") L Ptoi [(t "v6")]);
      (Let (a "v10") L Ptoi [(t "v8")]);
      (Let (a "v11") W (Cmp Ne L) [(t "v9"); (t "v10")])] (JBranch (t "v11") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [(Let (a "v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "v13"))])] (JGoto (To (a "L4"))));
  (mkBlock (a "L4") [] [] JRetVoid)].

Definition hello_image_fn_glibc_vfwprintf_internal'23scratch_buffer_init : func :=
  mkFunc (a "glibc_vfwprintf_internal#scratch_buffer_init") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v4") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v0")]);
      (RawStorePointer 0 (t "v4") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v6") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Write 1) [(t "chk0"); (t "v6")]);
      (RawStore Wl 0 (Const 1024) (t "chk1"))] JRetVoid)].

Definition hello_image_fn___GI___sched_cpucount : func :=
  mkFunc (a "__GI___sched_cpucount") (a "export") (RClass W) [(L, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [] (JGoto (To (a "L6"))));
  (mkBlock (a "L6") [(Phi (a "pr.2") W [((a "iw_1.join"), (t "v25")); ((a "start"), (Const 0))]); (Phi (a "pr.1") W [((a "iw_1.join"), (t "v23")); ((a "start"), (Const 0))])] [(Let (a "v12") L Shr [(t "v0"); (Const 3)]);
      (Let (a "v13") L (Ext Sw) [(t "pr.2")]);
      (Let (a "v14") W (Cmp Ult L) [(t "v13"); (t "v12")])] (JBranch (t "v14") (To (a "L7")) (To (a "L9"))));
  (mkBlock (a "L7") [] [(Let (a "v19") L Shl [(t "v13"); (Const 3)]);
      (Flight (a "v20") Add [(FAddress (t "v2")); (FValue (t "v19"))] (LowerOf (t "v2")));
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v20")]);
      (Let (a "v21") L (RawLoad LdL 0) [(t "chk0")])] (JGoto (To (a "iw_1.L3"))));
  (mkBlock (a "iw_1.L3") [(Phi (a "iw_1.pr.2") W [((a "iw_1.L4"), (t "iw_1.v14")); ((a "L7"), (Const 0))]); (Phi (a "iw_1.pr.1") L [((a "iw_1.L4"), (t "iw_1.v12")); ((a "L7"), (t "v21"))])] [(Let (a "iw_1.v8") W (Cmp Ne L) [(t "iw_1.pr.1"); (Const 0)])] (JBranch (t "iw_1.v8") (To (a "iw_1.L4")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L4") [] [(Let (a "iw_1.v11") L Sub [(t "iw_1.pr.1"); (Const 1)]);
      (Let (a "iw_1.v12") L And [(t "iw_1.pr.1"); (t "iw_1.v11")]);
      (Let (a "iw_1.v14") W Add [(t "iw_1.pr.2"); (Const 1)])] (JGoto (Poll (a "iw_1.L3"))));
  (mkBlock (a "iw_1.join") [] [(Let (a "v23") W Add [(t "pr.1"); (t "iw_1.pr.2")]);
      (Let (a "v25") W Add [(t "pr.2"); (Const 1)])] (JGoto (Poll (a "L6"))));
  (mkBlock (a "L9") [] [] (JRet (t "pr.1")))].
