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

Definition hello_image_fn___GI___fgets_unlocked : func :=
  mkFunc (a "__GI___fgets_unlocked") (a "export") (RClass P) [(P, (a "v0")); (W, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v16") W (Cmp Sle W) [(t "v2"); (Const 0)])] (JBranch (t "v16") (To (a "L12")) (To (a "L14"))));
  (mkBlock (a "L12") [] [] (JRet (Const 0)));
  (mkBlock (a "L14") [] [(Let (a "v22") W (Cmp Eq W) [(t "v2"); (Const 1)])] (JBranch (t "v22") (To (a "L18")) (To (a "L20"))));
  (mkBlock (a "L18") [] [(Let (a "chk0") A (Check 0 1 Write 1) [(t "v0")]);
      (RawStore Wb 0 (Const 0) (t "chk0"))] (JRet (t "v0")));
  (mkBlock (a "L20") [] [(Let (a "chk1") A (Check 0 4 Read 1) [(t "v4")]);
      (Let (a "v30") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")]);
      (Let (a "v31") W And [(t "v30"); (Const 32)]);
      (Let (a "v33") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")]);
      (Let (a "v35") W And [(t "v33"); (Const 4294967263)]);
      (Let (a "chk3") A (Renew 0 4 Write 1) [(t "chk1"); (t "v4")]);
      (RawStore Ww 0 (t "v35") (t "chk3"));
      (Let (a "v39") W Sub [(t "v2"); (Const 1)]);
      (Let (a "v40") L (Ext Sw) [(t "v39")]);
      (Call (CResult (a "v41") L) (Global (a "__GI__IO_getline")) [(Arg P (t "v4")); (Arg P (t "v0")); (Arg L (t "v40")); (Arg W (Const 10)); (Arg W (Const 1))]);
      (Let (a "v46") W (Cmp Eq L) [(t "v41"); (Const 0)])] (JBranch (t "v46") (To (a "L48")) (To (a "L47"))));
  (mkBlock (a "L47") [] [(Let (a "chk4") A (Renew 0 4 Read 1) [(t "chk1"); (t "v4")]);
      (Let (a "v50") W (RawLoad (LdNarrow Sw) 0) [(t "chk4")]);
      (Let (a "v51") W And [(t "v50"); (Const 32)])] (JBranch (t "v51") (To (a "L52")) (To (a "L48"))));
  (mkBlock (a "L52") [] [(Let (a "v54") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk5") A (Check 0 4 Read 1) [(t "v54")]);
      (Let (a "v55") W (RawLoad (LdNarrow Sw) 0) [(t "chk5")]);
      (Let (a "v56") W (Cmp Ne W) [(t "v55"); (Const 11)])] (JGoto (To (a "L48"))));
  (mkBlock (a "L48") [(Phi (a "v60") W [((a "L20"), (Const 1)); ((a "L47"), (Const 0)); ((a "L52"), (t "v56"))])] [] (JBranch (t "v60") (To (a "L44")) (To (a "L43"))));
  (mkBlock (a "L43") [] [(Flight (a "v63") Add [(FAddress (t "v0")); (FValue (t "v41"))] (LowerOf (t "v0")));
      (Let (a "chk6") A (Check 0 1 Write 1) [(t "v63")]);
      (RawStore Wb 0 (Const 0) (t "chk6"))] (JGoto (To (a "L44"))));
  (mkBlock (a "L44") [(Phi (a "pr.1") P [((a "L43"), (t "v0")); ((a "L48"), (Const 0))])] [(Let (a "chk7") A (Renew 0 4 Read 1) [(t "chk1"); (t "v4")]);
      (Let (a "v66") W (RawLoad (LdNarrow Sw) 0) [(t "chk7")]);
      (Let (a "v68") W Or [(t "v66"); (t "v31")]);
      (Let (a "chk8") A (Renew 0 4 Write 1) [(t "chk1"); (t "v4")]);
      (RawStore Ww 0 (t "v68") (t "chk8"))] (JRet (t "pr.1")))].
