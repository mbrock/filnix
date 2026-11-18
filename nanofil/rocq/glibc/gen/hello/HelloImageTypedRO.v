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

Definition hello_image_fn_glibc_printf_fp'23round_away : func :=
  mkFunc (a "glibc_printf_fp#round_away") (a "local") (RClass W) [(W, (a "v0")); (W, (a "v2")); (W, (a "v4")); (W, (a "v6")); (W, (a "v8"))] [(mkBlock (a "start") [] [(Let (a "v56") W (Cmp Eq W) [(t "v8"); (Const 1024)])] (JBranch (t "v56") (To (a "L13")) (To (a "L57"))));
  (mkBlock (a "L13") [] [(Let (a "v14") W (Ext Ub) [(t "v0")])] (JBranch (t "v14") (To (a "L15")) (To (a "L16"))));
  (mkBlock (a "L15") [] [(Let (a "v17") W (Ext Ub) [(t "v4")])] (JBranch (t "v17") (To (a "L16")) (To (a "L18"))));
  (mkBlock (a "L18") [] [(Let (a "v20") W (Ext Ub) [(t "v6")]);
      (Let (a "v21") W (Cmp Ne W) [(t "v20"); (Const 0)])] (JGoto (To (a "L16"))));
  (mkBlock (a "L16") [(Phi (a "v24") W [((a "L13"), (Const 0)); ((a "L15"), (Const 1)); ((a "L18"), (t "v21"))])] [] (JRet (t "v24")));
  (mkBlock (a "L26") [] [(Let (a "v27") W (Ext Ub) [(t "v4")])] (JBranch (t "v27") (To (a "L28")) (To (a "L29"))));
  (mkBlock (a "L28") [] [(Let (a "v30") W (Ext Ub) [(t "v2")])] (JBranch (t "v30") (To (a "L29")) (To (a "L31"))));
  (mkBlock (a "L31") [] [(Let (a "v33") W (Ext Ub) [(t "v6")]);
      (Let (a "v34") W (Cmp Ne W) [(t "v33"); (Const 0)])] (JGoto (To (a "L29"))));
  (mkBlock (a "L29") [(Phi (a "v37") W [((a "L26"), (Const 0)); ((a "L28"), (Const 1)); ((a "L31"), (t "v34"))])] [] (JRet (t "v37")));
  (mkBlock (a "L39") [] [] (JRet (Const 0)));
  (mkBlock (a "L41") [] [(Let (a "v42") W (Ext Ub) [(t "v0")]);
      (Let (a "v43") W (Cmp Eq W) [(t "v42"); (Const 0)])] (JBranch (t "v43") (To (a "L44")) (To (a "L45"))));
  (mkBlock (a "L44") [] [(Let (a "v46") W (Ext Ub) [(t "v4")])] (JBranch (t "v46") (To (a "L45")) (To (a "L47"))));
  (mkBlock (a "L47") [] [(Let (a "v49") W (Ext Ub) [(t "v6")]);
      (Let (a "v50") W (Cmp Ne W) [(t "v49"); (Const 0)])] (JGoto (To (a "L45"))));
  (mkBlock (a "L45") [(Phi (a "v53") W [((a "L41"), (Const 0)); ((a "L44"), (Const 1)); ((a "L47"), (t "v50"))])] [] (JRet (t "v53")));
  (mkBlock (a "L55") [] [(Call CVoid (Global (a "__GI_abort")) [])] (JRet (Const 0)));
  (mkBlock (a "L57") [] [(Let (a "v58") W (Cmp Eq W) [(t "v8"); (Const 0)])] (JBranch (t "v58") (Poll (a "L26")) (To (a "L59"))));
  (mkBlock (a "L59") [] [(Let (a "v60") W (Cmp Eq W) [(t "v8"); (Const 3072)])] (JBranch (t "v60") (Poll (a "L39")) (To (a "L61"))));
  (mkBlock (a "L61") [] [(Let (a "v62") W (Cmp Eq W) [(t "v8"); (Const 2048)])] (JBranch (t "v62") (Poll (a "L41")) (Poll (a "L55"))))].
