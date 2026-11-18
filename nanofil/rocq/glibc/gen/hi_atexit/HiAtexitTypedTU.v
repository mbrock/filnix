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

Definition hi_fn___tunable_is_initialized : func :=
  mkFunc (a "__tunable_is_initialized") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P Copy [(Global (a "glibc_dl_tunables#tunable_list"))]);
      (Let (a "v4") L (Ext Uw) [(t "v0")]);
      (Let (a "v5") L Mul [(t "v4"); (Const 136)]);
      (Flight (a "v6") Add [(FAddress (t "v2")); (FValue (t "v5"))] (LowerOf (t "v2")));
      (Flight (a "v7") Add [(FAddress (t "v6")); (FValue (Const 104))] (LowerOf (t "v6")));
      (Let (a "chk0") A (Check 0 1 Read 1) [(t "v7")]);
      (Let (a "v8") W (RawLoad (LdNarrow Ub) 0) [(t "chk0")])] (JRet (t "v8")))].

Definition hi_fn___tunable_set_val : func :=
  mkFunc (a "__tunable_set_val") (a "export") RVoid [(W, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v9") P Copy [(Global (a "glibc_dl_tunables#tunable_list"))]);
      (Let (a "v11") L (Ext Uw) [(t "v0")]);
      (Let (a "v12") L Mul [(t "v11"); (Const 136)]);
      (Flight (a "v13") Add [(FAddress (t "v9")); (FValue (t "v12"))] (LowerOf (t "v9")));
      (Call CVoid (Global (a "glibc_dl_tunables#do_tunable_update_val")) [(Arg P (t "v13")); (Arg P (t "v2")); (Arg P (t "v4")); (Arg P (t "v6"))])] JRetVoid)].

Definition hi_fn___tunable_get_val : func :=
  mkFunc (a "__tunable_get_val") (a "export") RVoid [(W, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v7") P Copy [(Global (a "glibc_dl_tunables#tunable_list"))]);
      (Let (a "v9") L (Ext Uw) [(t "v0")]);
      (Let (a "v10") L Mul [(t "v9"); (Const 136)]);
      (Flight (a "v11") Add [(FAddress (t "v7")); (FValue (t "v10"))] (LowerOf (t "v7")));
      (Flight (a "v13") Add [(FAddress (t "v11")); (FValue (Const 48))] (LowerOf (t "v11")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v13")]);
      (Let (a "v14") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "v38") W (Cmp Eq W) [(t "v14"); (Const 1)])] (JBranch (t "v38") (To (a "L17")) (To (a "L39"))));
  (mkBlock (a "L17") [] [(Flight (a "v20") Add [(FAddress (t "v11")); (FValue (Const 88))] (LowerOf (t "v11")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Read 1) [(t "chk0"); (t "v20")]);
      (Let (a "v21") L (RawLoad LdL 0) [(t "chk1")]);
      (Let (a "chk2") A (Check 0 8 Write 1) [(t "v2")]);
      (RawStore Wl 0 (t "v21") (t "chk2"))] (JGoto (To (a "L16"))));
  (mkBlock (a "L22") [] [(Flight (a "v25") Add [(FAddress (t "v11")); (FValue (Const 88))] (LowerOf (t "v11")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Read 1) [(t "chk0"); (t "v25")]);
      (Let (a "v26") L (RawLoad LdL 0) [(t "chk3")]);
      (Let (a "chk4") A (Check 0 4 Write 1) [(t "v2")]);
      (RawStore Ww 0 (t "v26") (t "chk4"))] (JGoto (To (a "L16"))));
  (mkBlock (a "L27") [] [(Flight (a "v30") Add [(FAddress (t "v11")); (FValue (Const 88))] (LowerOf (t "v11")));
      (Let (a "chk5") A (HalfCheck Upper 0 8 Read 1) [(t "chk0"); (t "v30")]);
      (Let (a "v31") L (RawLoad LdL 0) [(t "chk5")]);
      (Let (a "chk6") A (Check 0 8 Write 1) [(t "v2")]);
      (RawStore Wl 0 (t "v31") (t "chk6"))] (JGoto (To (a "L16"))));
  (mkBlock (a "L32") [] [(Flight (a "v35") Add [(FAddress (t "v11")); (FValue (Const 88))] (LowerOf (t "v11")));
      (Let (a "chk7") A (Check 0 8 Write 8) [(t "v2")]);
      (RawStorePointer 0 (t "v35") (t "chk7") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L16"))));
  (mkBlock (a "L36") [] [] JUnreachable);
  (mkBlock (a "L39") [] [(Let (a "v40") W (Cmp Eq W) [(t "v14"); (Const 0)])] (JBranch (t "v40") (Poll (a "L22")) (To (a "L41"))));
  (mkBlock (a "L41") [] [(Let (a "v42") W (Cmp Eq W) [(t "v14"); (Const 2)])] (JBranch (t "v42") (Poll (a "L27")) (To (a "L43"))));
  (mkBlock (a "L43") [] [(Let (a "v44") W (Cmp Eq W) [(t "v14"); (Const 3)])] (JBranch (t "v44") (Poll (a "L32")) (Poll (a "L36"))));
  (mkBlock (a "L16") [] [(Flight (a "v50") Add [(FAddress (t "v11")); (FValue (Const 104))] (LowerOf (t "v11")));
      (Let (a "chk8") A (HalfCheck Upper 0 1 Read 1) [(t "chk0"); (t "v50")]);
      (Let (a "v51") W (RawLoad (LdNarrow Ub) 0) [(t "chk8")])] (JBranch (t "v51") (To (a "L52")) (To (a "L53"))));
  (mkBlock (a "L52") [] [(Let (a "v55") L Ptoi [(t "v4")]);
      (Let (a "v56") L Ptoi [(Const 0)]);
      (Let (a "v57") W (Cmp Ne L) [(t "v55"); (t "v56")])] (JGoto (To (a "L53"))));
  (mkBlock (a "L53") [(Phi (a "v59") W [((a "L16"), (Const 0)); ((a "L52"), (t "v57"))])] [] (JBranch (t "v59") (To (a "L46")) (To (a "L48"))));
  (mkBlock (a "L46") [] [(Flight (a "v62") Add [(FAddress (t "v11")); (FValue (Const 88))] (LowerOf (t "v11")));
      (Let (a "chk9") F CheckFunction [(t "v4")]);
      (RawCall CVoid (t "chk9") [(Arg P (t "v62"))])] (JGoto (To (a "L48"))));
  (mkBlock (a "L48") [] [] JRetVoid)].
