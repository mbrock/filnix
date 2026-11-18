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

Definition hello_image_fn__itoa_word : func :=
  mkFunc (a "_itoa_word") (a "export") (RClass P) [(L, (a "v0")); (P, (a "v2")); (W, (a "v4")); (W, (a "v6"))] [(mkBlock (a "start") [] [] (JBranch (t "v6") (To (a "L9")) (To (a "L10"))));
  (mkBlock (a "L9") [] [(Let (a "v13") P Copy [(Global (a "__GI__itoa_upper_digits"))])] (JGoto (To (a "L11"))));
  (mkBlock (a "L10") [] [(Let (a "v14") P Copy [(Global (a "__GI__itoa_lower_digits"))])] (JGoto (To (a "L11"))));
  (mkBlock (a "L11") [(Phi (a "v15") P [((a "L9"), (t "v13")); ((a "L10"), (t "v14"))])] [(Let (a "v79") W (Cmp Eq W) [(t "v4"); (Const 10)])] (JBranch (t "v79") (To (a "L20")) (To (a "L80"))));
  (mkBlock (a "L20") [(Phi (a "pr.6") P [((a "L20"), (t "v24")); ((a "L11"), (t "v2"))]); (Phi (a "pr.1") L [((a "L20"), (t "v31")); ((a "L11"), (t "v0"))])] [(Flight (a "v24") Sub [(FAddress (t "pr.6")); (FValue (Const 1))] (LowerOf (t "pr.6")));
      (Let (a "v27") L Urem [(t "pr.1"); (Const 10)]);
      (Flight (a "v28") Add [(FAddress (t "v15")); (FValue (t "v27"))] (LowerOf (t "v15")));
      (Let (a "chk0") A (Check 0 1 Read 1) [(t "v28")]);
      (Let (a "v29") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 1 Write 1) [(t "v24")]);
      (RawStore Wb 0 (t "v29") (t "chk1"));
      (Let (a "v31") L Udiv [(t "pr.1"); (Const 10)]);
      (Let (a "v32") W (Cmp Ne L) [(t "v31"); (Const 0)])] (JBranch (t "v32") (Poll (a "L20")) (To (a "L18"))));
  (mkBlock (a "L34") [(Phi (a "pr.7") P [((a "L34"), (t "v38")); ((a "L80"), (t "v2"))]); (Phi (a "pr.2") L [((a "L34"), (t "v45")); ((a "L80"), (t "v0"))])] [(Flight (a "v38") Sub [(FAddress (t "pr.7")); (FValue (Const 1))] (LowerOf (t "pr.7")));
      (Let (a "v41") L And [(t "pr.2"); (Const 15)]);
      (Flight (a "v42") Add [(FAddress (t "v15")); (FValue (t "v41"))] (LowerOf (t "v15")));
      (Let (a "chk2") A (Check 0 1 Read 1) [(t "v42")]);
      (Let (a "v43") W (RawLoad (LdNarrow Sb) 0) [(t "chk2")]);
      (Let (a "chk3") A (Check 0 1 Write 1) [(t "v38")]);
      (RawStore Wb 0 (t "v43") (t "chk3"));
      (Let (a "v45") L Shr [(t "pr.2"); (Const 4)]);
      (Let (a "v46") W (Cmp Ne L) [(t "v45"); (Const 0)])] (JBranch (t "v46") (Poll (a "L34")) (To (a "L18"))));
  (mkBlock (a "L48") [(Phi (a "pr.8") P [((a "L48"), (t "v52")); ((a "L82"), (t "v2"))]); (Phi (a "pr.3") L [((a "L48"), (t "v59")); ((a "L82"), (t "v0"))])] [(Flight (a "v52") Sub [(FAddress (t "pr.8")); (FValue (Const 1))] (LowerOf (t "pr.8")));
      (Let (a "v55") L And [(t "pr.3"); (Const 7)]);
      (Flight (a "v56") Add [(FAddress (t "v15")); (FValue (t "v55"))] (LowerOf (t "v15")));
      (Let (a "chk4") A (Check 0 1 Read 1) [(t "v56")]);
      (Let (a "v57") W (RawLoad (LdNarrow Sb) 0) [(t "chk4")]);
      (Let (a "chk5") A (Check 0 1 Write 1) [(t "v52")]);
      (RawStore Wb 0 (t "v57") (t "chk5"));
      (Let (a "v59") L Shr [(t "pr.3"); (Const 3)]);
      (Let (a "v60") W (Cmp Ne L) [(t "v59"); (Const 0)])] (JBranch (t "v60") (Poll (a "L48")) (To (a "L18"))));
  (mkBlock (a "L62") [(Phi (a "pr.9") P [((a "L62"), (t "v66")); ((a "L82"), (t "v2"))]); (Phi (a "pr.4") L [((a "L62"), (t "v77")); ((a "L82"), (t "v0"))])] [(Flight (a "v66") Sub [(FAddress (t "pr.9")); (FValue (Const 1))] (LowerOf (t "pr.9")));
      (Let (a "v70") L (Ext Uw) [(t "v4")]);
      (Let (a "v71") L Urem [(t "pr.4"); (t "v70")]);
      (Flight (a "v72") Add [(FAddress (t "v15")); (FValue (t "v71"))] (LowerOf (t "v15")));
      (Let (a "chk6") A (Check 0 1 Read 1) [(t "v72")]);
      (Let (a "v73") W (RawLoad (LdNarrow Sb) 0) [(t "chk6")]);
      (Let (a "chk7") A (Check 0 1 Write 1) [(t "v66")]);
      (RawStore Wb 0 (t "v73") (t "chk7"));
      (Let (a "v77") L Udiv [(t "pr.4"); (t "v70")]);
      (Let (a "v78") W (Cmp Ne L) [(t "v77"); (Const 0)])] (JBranch (t "v78") (Poll (a "L62")) (To (a "L18"))));
  (mkBlock (a "L80") [] [(Let (a "v81") W (Cmp Eq W) [(t "v4"); (Const 16)])] (JBranch (t "v81") (Poll (a "L34")) (To (a "L82"))));
  (mkBlock (a "L82") [] [(Let (a "v83") W (Cmp Eq W) [(t "v4"); (Const 8)])] (JBranch (t "v83") (Poll (a "L48")) (Poll (a "L62"))));
  (mkBlock (a "L18") [(Phi (a "pr.5") P [((a "L20"), (t "v24")); ((a "L34"), (t "v38")); ((a "L48"), (t "v52")); ((a "L62"), (t "v66"))])] [] (JRet (t "pr.5")))].
