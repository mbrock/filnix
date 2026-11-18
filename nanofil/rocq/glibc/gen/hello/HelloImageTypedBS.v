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

Definition hello_image_fn_glibc_dcigettext'23__bswap_32 : func :=
  mkFunc (a "glibc_dcigettext#__bswap_32") (a "local") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v3") W And [(t "v0"); (Const 4278190080)]);
      (Let (a "v4") W Shr [(t "v3"); (Const 24)]);
      (Let (a "v6") W And [(t "v0"); (Const 16711680)]);
      (Let (a "v7") W Shr [(t "v6"); (Const 8)]);
      (Let (a "v8") W Or [(t "v4"); (t "v7")]);
      (Let (a "v10") W And [(t "v0"); (Const 65280)]);
      (Let (a "v11") W Shl [(t "v10"); (Const 8)]);
      (Let (a "v12") W Or [(t "v8"); (t "v11")]);
      (Let (a "v14") W And [(t "v0"); (Const 255)]);
      (Let (a "v15") W Shl [(t "v14"); (Const 24)]);
      (Let (a "v16") W Or [(t "v12"); (t "v15")])] (JRet (t "v16")))].

Definition hello_image_fn___GI_bsearch : func :=
  mkFunc (a "__GI_bsearch") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4")); (L, (a "v6")); (P, (a "v8"))] [(mkBlock (a "start") [] [] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [(Phi (a "pr.3") L [((a "L36"), (t "v45")); ((a "start"), (t "v4"))]); (Phi (a "pr.1") P [((a "L36"), (t "pr.2")); ((a "start"), (t "v2"))])] [(Let (a "v16") W (Cmp Ne L) [(t "pr.3"); (Const 0)])] (JBranch (t "v16") (To (a "L13")) (To (a "L14"))));
  (mkBlock (a "L13") [] [(Let (a "v19") L Shr [(t "pr.3"); (Const 1)]);
      (Let (a "v21") L Mul [(t "v19"); (t "v6")]);
      (Flight (a "v22") Add [(FAddress (t "pr.1")); (FValue (t "v21"))] (LowerOf (t "pr.1")));
      (Let (a "chk0") F CheckFunction [(t "v8")]);
      (RawCall (CResult (a "v26") W) (t "chk0") [(Arg P (t "v0")); (Arg P (t "v22"))]);
      (Let (a "v31") W (Cmp Eq W) [(t "v26"); (Const 0)])] (JBranch (t "v31") (To (a "L27")) (To (a "L29"))));
  (mkBlock (a "L27") [] [] (JRet (t "v22")));
  (mkBlock (a "L29") [] [(Let (a "v38") W (Cmp Sgt W) [(t "v26"); (Const 0)])] (JBranch (t "v38") (To (a "L34")) (To (a "L36"))));
  (mkBlock (a "L34") [] [(Flight (a "v41") Add [(FAddress (t "v22")); (FValue (t "v6"))] (LowerOf (t "v22")));
      (Let (a "v43") L Sub [(t "pr.3"); (Const 1)])] (JGoto (To (a "L36"))));
  (mkBlock (a "L36") [(Phi (a "pr.4") L [((a "L34"), (t "v43")); ((a "L29"), (t "pr.3"))]); (Phi (a "pr.2") P [((a "L34"), (t "v41")); ((a "L29"), (t "pr.1"))])] [(Let (a "v45") L Shr [(t "pr.4"); (Const 1)])] (JGoto (Poll (a "L12"))));
  (mkBlock (a "L14") [] [] (JRet (Const 0)))].
