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

Definition hello_image_fn___GI___wmemchr : func :=
  mkFunc (a "__GI___wmemchr") (a "export") (RClass P) [(P, (a "v0")); (W, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [] (JGoto (To (a "L6"))));
  (mkBlock (a "L6") [(Phi (a "pr.4") L [((a "L45"), (t "v57")); ((a "start"), (t "v4"))]); (Phi (a "pr.1") P [((a "L45"), (t "v55")); ((a "start"), (t "v0"))])] [(Let (a "v10") W (Cmp Uge L) [(t "pr.4"); (Const 4)])] (JBranch (t "v10") (To (a "L7")) (To (a "L8"))));
  (mkBlock (a "L7") [] [(Let (a "chk0") A (Check 0 4 Read 1) [(t "pr.1")]);
      (Let (a "v16") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v18") W (Cmp Eq W) [(t "v16"); (t "v2")])] (JBranch (t "v18") (To (a "L11")) (To (a "L13"))));
  (mkBlock (a "L11") [] [] (JRet (t "pr.1")));
  (mkBlock (a "L13") [] [(Flight (a "v25") Add [(FAddress (t "pr.1")); (FValue (Const 4))] (LowerOf (t "pr.1")));
      (Let (a "chk1") A (HalfCheck Upper 0 4 Read 1) [(t "chk0"); (t "v25")]);
      (Let (a "v26") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")]);
      (Let (a "v28") W (Cmp Eq W) [(t "v26"); (t "v2")])] (JBranch (t "v28") (To (a "L21")) (To (a "L23"))));
  (mkBlock (a "L21") [] [(Flight (a "v30") Add [(FAddress (t "pr.1")); (FValue (Const 4))] (LowerOf (t "pr.1")))] (JRet (t "v30")));
  (mkBlock (a "L23") [] [(Flight (a "v36") Add [(FAddress (t "pr.1")); (FValue (Const 8))] (LowerOf (t "pr.1")));
      (Let (a "chk2") A (HalfCheck Upper 0 4 Read 1) [(t "chk0"); (t "v36")]);
      (Let (a "v37") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v39") W (Cmp Eq W) [(t "v37"); (t "v2")])] (JBranch (t "v39") (To (a "L32")) (To (a "L34"))));
  (mkBlock (a "L32") [] [(Flight (a "v41") Add [(FAddress (t "pr.1")); (FValue (Const 8))] (LowerOf (t "pr.1")))] (JRet (t "v41")));
  (mkBlock (a "L34") [] [(Flight (a "v47") Add [(FAddress (t "pr.1")); (FValue (Const 12))] (LowerOf (t "pr.1")));
      (Let (a "chk3") A (HalfCheck Upper 0 4 Read 1) [(t "chk0"); (t "v47")]);
      (Let (a "v48") W (RawLoad (LdNarrow Sw) 0) [(t "chk3")]);
      (Let (a "v50") W (Cmp Eq W) [(t "v48"); (t "v2")])] (JBranch (t "v50") (To (a "L43")) (To (a "L45"))));
  (mkBlock (a "L43") [] [(Flight (a "v52") Add [(FAddress (t "pr.1")); (FValue (Const 12))] (LowerOf (t "pr.1")))] (JRet (t "v52")));
  (mkBlock (a "L45") [] [(Flight (a "v55") Add [(FAddress (t "pr.1")); (FValue (Const 16))] (LowerOf (t "pr.1")));
      (Let (a "v57") L Sub [(t "pr.4"); (Const 4)])] (JGoto (Poll (a "L6"))));
  (mkBlock (a "L8") [] [(Let (a "v62") W (Cmp Ugt L) [(t "pr.4"); (Const 0)])] (JBranch (t "v62") (To (a "L58")) (To (a "L60"))));
  (mkBlock (a "L58") [] [(Let (a "chk4") A (Check 0 4 Read 1) [(t "pr.1")]);
      (Let (a "v67") W (RawLoad (LdNarrow Sw) 0) [(t "chk4")]);
      (Let (a "v69") W (Cmp Eq W) [(t "v67"); (t "v2")])] (JBranch (t "v69") (To (a "L63")) (To (a "L65"))));
  (mkBlock (a "L63") [] [] (JRet (t "pr.1")));
  (mkBlock (a "L65") [] [(Flight (a "v73") Add [(FAddress (t "pr.1")); (FValue (Const 4))] (LowerOf (t "pr.1")));
      (Let (a "v75") L Sub [(t "pr.4"); (Const 1)])] (JGoto (To (a "L60"))));
  (mkBlock (a "L60") [(Phi (a "pr.5") L [((a "L65"), (t "v75")); ((a "L8"), (t "pr.4"))]); (Phi (a "pr.2") P [((a "L65"), (t "v73")); ((a "L8"), (t "pr.1"))])] [(Let (a "v80") W (Cmp Ugt L) [(t "pr.5"); (Const 0)])] (JBranch (t "v80") (To (a "L76")) (To (a "L78"))));
  (mkBlock (a "L76") [] [(Let (a "chk5") A (Check 0 4 Read 1) [(t "pr.2")]);
      (Let (a "v85") W (RawLoad (LdNarrow Sw) 0) [(t "chk5")]);
      (Let (a "v87") W (Cmp Eq W) [(t "v85"); (t "v2")])] (JBranch (t "v87") (To (a "L81")) (To (a "L83"))));
  (mkBlock (a "L81") [] [] (JRet (t "pr.2")));
  (mkBlock (a "L83") [] [(Flight (a "v91") Add [(FAddress (t "pr.2")); (FValue (Const 4))] (LowerOf (t "pr.2")));
      (Let (a "v93") L Sub [(t "pr.5"); (Const 1)])] (JGoto (To (a "L78"))));
  (mkBlock (a "L78") [(Phi (a "pr.6") L [((a "L83"), (t "v93")); ((a "L60"), (t "pr.5"))]); (Phi (a "pr.3") P [((a "L83"), (t "v91")); ((a "L60"), (t "pr.2"))])] [(Let (a "v98") W (Cmp Ugt L) [(t "pr.6"); (Const 0)])] (JBranch (t "v98") (To (a "L94")) (To (a "L96"))));
  (mkBlock (a "L94") [] [(Let (a "chk6") A (Check 0 4 Read 1) [(t "pr.3")]);
      (Let (a "v103") W (RawLoad (LdNarrow Sw) 0) [(t "chk6")]);
      (Let (a "v105") W (Cmp Eq W) [(t "v103"); (t "v2")])] (JBranch (t "v105") (To (a "L99")) (To (a "L96"))));
  (mkBlock (a "L99") [] [] (JRet (t "pr.3")));
  (mkBlock (a "L96") [] [] (JRet (Const 0)))].

Definition hello_image_fn___wmemcpy : func :=
  mkFunc (a "__wmemcpy") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v9") L Shl [(t "v4"); (Const 2)]);
      (Call (CResult (a "v10") P) (Global (a "__GI_memcpy")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg L (t "v9"))])] (JRet (t "v10")))].

Definition hello_image_fn___wmempcpy : func :=
  mkFunc (a "__wmempcpy") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v9") L Shl [(t "v4"); (Const 2)]);
      (Call (CResult (a "v10") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg L (t "v9"))])] (JRet (t "v10")))].

Definition hello_image_fn___GI___wmemset : func :=
  mkFunc (a "__GI___wmemset") (a "export") (RClass P) [(P, (a "v0")); (W, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [] (JGoto (To (a "L8"))));
  (mkBlock (a "L8") [(Phi (a "pr.2") P [((a "L9"), (t "v26")); ((a "start"), (t "v0"))]); (Phi (a "pr.1") L [((a "L9"), (t "v28")); ((a "start"), (t "v4"))])] [(Let (a "v12") W (Cmp Uge L) [(t "pr.1"); (Const 4)])] (JBranch (t "v12") (To (a "L9")) (To (a "L10"))));
  (mkBlock (a "L9") [] [(Let (a "chk0") A (Check 0 4 Write 1) [(t "pr.2")]);
      (RawStore Ww 0 (t "v2") (t "chk0"));
      (Flight (a "v17") Add [(FAddress (t "pr.2")); (FValue (Const 4))] (LowerOf (t "pr.2")));
      (Let (a "chk1") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "v17")]);
      (RawStore Ww 0 (t "v2") (t "chk1"));
      (Flight (a "v20") Add [(FAddress (t "pr.2")); (FValue (Const 8))] (LowerOf (t "pr.2")));
      (Let (a "chk2") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "v20")]);
      (RawStore Ww 0 (t "v2") (t "chk2"));
      (Flight (a "v23") Add [(FAddress (t "pr.2")); (FValue (Const 12))] (LowerOf (t "pr.2")));
      (Let (a "chk3") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "v23")]);
      (RawStore Ww 0 (t "v2") (t "chk3"));
      (Flight (a "v26") Add [(FAddress (t "pr.2")); (FValue (Const 16))] (LowerOf (t "pr.2")));
      (Let (a "v28") L Sub [(t "pr.1"); (Const 4)])] (JGoto (Poll (a "L8"))));
  (mkBlock (a "L10") [] [(Let (a "v33") W (Cmp Ugt L) [(t "pr.1"); (Const 0)])] (JBranch (t "v33") (To (a "L29")) (To (a "L31"))));
  (mkBlock (a "L29") [] [(Let (a "chk4") A (Check 0 4 Write 1) [(t "pr.2")]);
      (RawStore Ww 0 (t "v2") (t "chk4"));
      (Let (a "v41") W (Cmp Ugt L) [(t "pr.1"); (Const 1)])] (JBranch (t "v41") (To (a "L37")) (To (a "L31"))));
  (mkBlock (a "L37") [] [(Flight (a "v43") Add [(FAddress (t "pr.2")); (FValue (Const 4))] (LowerOf (t "pr.2")));
      (Let (a "chk5") A (HalfCheck Upper 0 4 Write 1) [(t "chk4"); (t "v43")]);
      (RawStore Ww 0 (t "v2") (t "chk5"));
      (Let (a "v49") W (Cmp Ugt L) [(t "pr.1"); (Const 2)])] (JBranch (t "v49") (To (a "L45")) (To (a "L31"))));
  (mkBlock (a "L45") [] [(Flight (a "v51") Add [(FAddress (t "pr.2")); (FValue (Const 8))] (LowerOf (t "pr.2")));
      (Let (a "chk6") A (HalfCheck Upper 0 4 Write 1) [(t "chk4"); (t "v51")]);
      (RawStore Ww 0 (t "v2") (t "chk6"))] (JGoto (To (a "L31"))));
  (mkBlock (a "L31") [] [] (JRet (t "v0")))].

Definition hello_image_fn___wmemmove : func :=
  mkFunc (a "__wmemmove") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v9") L Shl [(t "v4"); (Const 2)]);
      (Call (CResult (a "v10") P) (Global (a "__GI_memmove")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg L (t "v9"))])] (JRet (t "v10")))].
