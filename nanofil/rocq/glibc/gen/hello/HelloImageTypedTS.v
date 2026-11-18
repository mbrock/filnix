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

Definition hello_image_fn___GI___tsearch : func :=
  mkFunc (a "__GI___tsearch") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v20") L Ptoi [(t "v2")]);
      (Let (a "v21") L Ptoi [(Const 0)]);
      (Let (a "v22") W (Cmp Eq L) [(t "v20"); (t "v21")])] (JBranch (t "v22") (To (a "L16")) (To (a "L18"))));
  (mkBlock (a "L16") [] [] (JRet (Const 0)));
  (mkBlock (a "L18") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v25") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v30") L Ptoi [(t "v25")]);
      (Let (a "v32") W (Cmp Ne L) [(t "v30"); (t "v21")])] (JBranch (t "v32") (To (a "L26")) (To (a "L42"))));
  (mkBlock (a "L26") [] [(Flight (a "v34") Add [(FAddress (t "v25")); (FValue (Const 24))] (LowerOf (t "v25")));
      (Let (a "chk1") A (Check 0 4 Read 1) [(t "v34")]);
      (Let (a "v35") W (RawLoad (LdNarrow Uw) 0) [(t "chk1")]);
      (Let (a "v36") W And [(t "v35"); (Const 4294967294)]);
      (Let (a "chk2") A (Renew 0 4 Write 1) [(t "chk1"); (t "v34")]);
      (RawStore Ww 0 (t "v36") (t "chk2"))] (JGoto (To (a "L42"))));
  (mkBlock (a "L42") [(Phi (a "pr.9") W [((a "L26"), (Const 0)); ((a "L18"), (Const 0)); ((a "L71"), (t "pr.8"))]); (Phi (a "pr.8") W [((a "L26"), (Const 0)); ((a "L18"), (Const 0)); ((a "L71"), (t "v56"))]); (Phi (a "pr.6") W [((a "L26"), (Const 0)); ((a "L18"), (Const 0)); ((a "L71"), (t "v56"))]); (Phi (a "pr.4") P [((a "L26"), (t "v2")); ((a "L18"), (t "v2")); ((a "L71"), (t "v78"))]); (Phi (a "pr.3") P [((a "L26"), (t "v2")); ((a "L18"), (t "v2")); ((a "L71"), (t "v78"))]); (Phi (a "pr.2") P [((a "L26"), (Const 0)); ((a "L18"), (Const 0)); ((a "L71"), (t "pr.1"))]); (Phi (a "pr.1") P [((a "L26"), (Const 0)); ((a "L18"), (Const 0)); ((a "L71"), (t "pr.3"))])] [(Let (a "chk3") A (Check 0 8 Read 8) [(t "pr.4")]);
      (Let (a "v46") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Let (a "v47") L Ptoi [(t "v46")]);
      (Let (a "v49") W (Cmp Ne L) [(t "v47"); (t "v21")])] (JBranch (t "v49") (To (a "L43")) (To (a "L44"))));
  (mkBlock (a "L43") [] [(Let (a "chk4") A (Check 0 8 Read 8) [(t "pr.3")]);
      (Let (a "v51") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v51")]);
      (Let (a "v55") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk6") F CheckFunction [(t "v4")]);
      (RawCall (CResult (a "v56") W) (t "chk6") [(Arg P (t "v0")); (Arg P (t "v55"))]);
      (Let (a "v61") W (Cmp Eq W) [(t "v56"); (Const 0)])] (JBranch (t "v61") (To (a "L57")) (To (a "L59"))));
  (mkBlock (a "L57") [] [] (JRet (t "v51")));
  (mkBlock (a "L59") [] [(Call CVoid (Global (a "glibc_tsearch#maybe_split_for_insert")) [(Arg P (t "pr.3")); (Arg P (t "pr.1")); (Arg P (t "pr.2")); (Arg W (t "pr.8")); (Arg W (t "pr.9")); (Arg W (Const 0))]);
      (Let (a "v73") W (Cmp Slt W) [(t "v56"); (Const 0)])] (JBranch (t "v73") (To (a "L69")) (To (a "L70"))));
  (mkBlock (a "L69") [] [(Flight (a "v75") Add [(FAddress (t "v51")); (FValue (Const 8))] (LowerOf (t "v51")))] (JGoto (To (a "L71"))));
  (mkBlock (a "L70") [] [(Flight (a "v77") Add [(FAddress (t "v51")); (FValue (Const 16))] (LowerOf (t "v51")))] (JGoto (To (a "L71"))));
  (mkBlock (a "L71") [(Phi (a "v78") P [((a "L69"), (t "v75")); ((a "L70"), (t "v77"))])] [(Let (a "chk7") A (Check 0 8 Read 8) [(t "v78")]);
      (Let (a "v83") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Let (a "v84") L Ptoi [(t "v83")]);
      (Let (a "v86") W (Cmp Eq L) [(t "v84"); (t "v21")])] (JBranch (t "v86") (To (a "L44")) (Poll (a "L42"))));
  (mkBlock (a "L44") [(Phi (a "pr.7") W [((a "L42"), (t "pr.6")); ((a "L71"), (t "v56"))]); (Phi (a "pr.5") P [((a "L42"), (t "pr.4")); ((a "L71"), (t "v78"))])] [(Call (CResult (a "v93") P) (Global (a "malloc")) [(Arg L (Const 32))]);
      (Let (a "v98") L Ptoi [(t "v93")]);
      (Let (a "v100") W (Cmp Ne L) [(t "v98"); (t "v21")])] (JBranch (t "v100") (To (a "L94")) (To (a "L96"))));
  (mkBlock (a "L94") [] [(Let (a "chk8") A (Check 0 8 Write 8) [(t "pr.5")]);
      (RawStorePointer 0 (t "v93") (t "chk8") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk9") A (Check 0 8 Write 8) [(t "v93")]);
      (RawStorePointer 0 (t "v0") (t "chk9") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v106") Add [(FAddress (t "v93")); (FValue (Const 24))] (LowerOf (t "v93")));
      (Let (a "chk10") A (HalfCheck Upper 0 4 Read 1) [(t "chk9"); (t "v106")]);
      (Let (a "v107") W (RawLoad (LdNarrow Uw) 0) [(t "chk10")]);
      (Let (a "v108") W And [(t "v107"); (Const 4294967294)]);
      (Let (a "v110") W Or [(t "v108"); (Const 1)]);
      (Let (a "chk11") A (Renew 0 4 Write 1) [(t "chk10"); (t "v106")]);
      (RawStore Ww 0 (t "v110") (t "chk11"));
      (Flight (a "v114") Add [(FAddress (t "v93")); (FValue (Const 8))] (LowerOf (t "v93")));
      (Let (a "chk12") A (HalfCheck Upper 0 8 Write 8) [(t "chk9"); (t "v114")]);
      (RawStorePointer 0 (Const 0) (t "chk12") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v116") Add [(FAddress (t "v93")); (FValue (Const 16))] (LowerOf (t "v93")));
      (Let (a "chk13") A (HalfCheck Upper 0 8 Write 8) [(t "chk9"); (t "v116")]);
      (RawStorePointer 0 (Const 0) (t "chk13") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v122") L Ptoi [(t "pr.5")]);
      (Let (a "v123") L Ptoi [(t "pr.3")]);
      (Let (a "v124") W (Cmp Ne L) [(t "v122"); (t "v123")])] (JBranch (t "v124") (To (a "L117")) (To (a "L96"))));
  (mkBlock (a "L117") [] [(Call CVoid (Global (a "glibc_tsearch#maybe_split_for_insert")) [(Arg P (t "pr.5")); (Arg P (t "pr.3")); (Arg P (t "pr.1")); (Arg W (t "pr.7")); (Arg W (t "pr.8")); (Arg W (Const 1))])] (JGoto (To (a "L96"))));
  (mkBlock (a "L96") [] [] (JRet (t "v93")))].
