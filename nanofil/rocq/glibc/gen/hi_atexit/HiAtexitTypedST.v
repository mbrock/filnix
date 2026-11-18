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

Definition hi_fn___strlen : func :=
  mkFunc (a "__strlen") (a "export") (RClass L) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v4") L Ptoi [(t "v0")]);
      (Let (a "v9") L And [(t "v4"); (Const 18446744073709551608)]);
      (Let (a "lc.2") L Sub [(t "v9"); (t "v4")]);
      (Flight (a "v10") Add [(FAddress (t "v0")); (FValue (t "lc.2"))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v10")]);
      (Let (a "v13") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "iw_1.v6") L And [(t "v13"); (Const 9187201950435737471)]);
      (Let (a "iw_1.v8") L Add [(t "iw_1.v6"); (Const 9187201950435737471)]);
      (Let (a "iw_1.v10") L Or [(t "iw_1.v8"); (t "v13")]);
      (Let (a "iw_1.v12") L Or [(t "iw_1.v10"); (Const 9187201950435737471)]);
      (Let (a "iw_1.v13") L Xor [(t "iw_1.v12"); (Const (-1))]);
      (Let (a "iw_2.v10") L And [(t "v4"); (Const 7)]);
      (Let (a "iw_2.v11") L Shl [(t "iw_2.v10"); (Const 3)]);
      (Let (a "iw_2.v12") L Shr [(t "iw_1.v13"); (t "iw_2.v11")]);
      (Let (a "v23") W (Cmp Ne L) [(t "iw_2.v12"); (Const 0)])] (JBranch (t "v23") (To (a "iw_3.start")) (To (a "L28"))));
  (mkBlock (a "iw_3.start") [] [(Let (a "iw_3.iw_1.iw_1.v6") W (Cmp Eq L) [(t "iw_2.v12"); (Const 0)])] (JBranch (t "iw_3.iw_1.iw_1.v6") (To (a "iw_3.iw_1.iw_1.L4")) (To (a "iw_3.iw_1.iw_1.L3"))));
  (mkBlock (a "iw_3.iw_1.iw_1.L3") [] [(Let (a "iw_3.iw_1.iw_1.v8") L Neg [(t "iw_2.v12")]);
      (Let (a "iw_3.iw_1.iw_1.v9") L And [(t "iw_2.v12"); (t "iw_3.iw_1.iw_1.v8")]);
      (Let (a "iw_3.iw_1.iw_1.v10") L Sub [(t "iw_3.iw_1.iw_1.v9"); (Const 1)]);
      (Let (a "iw_3.iw_1.iw_1.v11") L Shr [(t "iw_3.iw_1.iw_1.v10"); (Const 1)]);
      (Let (a "iw_3.iw_1.iw_1.v12") L And [(t "iw_3.iw_1.iw_1.v11"); (Const 6148914691236517205)]);
      (Let (a "iw_3.iw_1.iw_1.v13") L Sub [(t "iw_3.iw_1.iw_1.v10"); (t "iw_3.iw_1.iw_1.v12")]);
      (Let (a "iw_3.iw_1.iw_1.v14") L And [(t "iw_3.iw_1.iw_1.v13"); (Const 3689348814741910323)]);
      (Let (a "iw_3.iw_1.iw_1.v15") L Shr [(t "iw_3.iw_1.iw_1.v13"); (Const 2)]);
      (Let (a "iw_3.iw_1.iw_1.v16") L And [(t "iw_3.iw_1.iw_1.v15"); (Const 3689348814741910323)]);
      (Let (a "iw_3.iw_1.iw_1.v17") L Add [(t "iw_3.iw_1.iw_1.v14"); (t "iw_3.iw_1.iw_1.v16")]);
      (Let (a "iw_3.iw_1.iw_1.v18") L Shr [(t "iw_3.iw_1.iw_1.v17"); (Const 4)]);
      (Let (a "iw_3.iw_1.iw_1.v19") L Add [(t "iw_3.iw_1.iw_1.v17"); (t "iw_3.iw_1.iw_1.v18")]);
      (Let (a "iw_3.iw_1.iw_1.v20") L And [(t "iw_3.iw_1.iw_1.v19"); (Const 1085102592571150095)]);
      (Let (a "iw_3.iw_1.iw_1.v21") L Mul [(t "iw_3.iw_1.iw_1.v20"); (Const 72340172838076673)]);
      (Let (a "iw_3.iw_1.iw_1.v22") L Shr [(t "iw_3.iw_1.iw_1.v21"); (Const 56)])] (JGoto (To (a "iw_3.iw_1.iw_1.L4"))));
  (mkBlock (a "iw_3.iw_1.iw_1.L4") [(Phi (a "iw_3.iw_1.iw_1.v23") W [((a "iw_3.iw_1.iw_1.L3"), (t "iw_3.iw_1.iw_1.v22")); ((a "iw_3.start"), (Const 64))])] [(Let (a "iw_3.iw_1.v27") W Shr [(t "iw_3.iw_1.iw_1.v23"); (Const 3)]);
      (Let (a "v26") L (Ext Uw) [(t "iw_3.iw_1.v27")])] (JRet (t "v26")));
  (mkBlock (a "L28") [(Phi (a "pr.1") P [((a "L28"), (t "v32")); ((a "start"), (t "v10"))])] [(Flight (a "v32") Add [(FAddress (t "pr.1")); (FValue (Const 8))] (LowerOf (t "pr.1")));
      (Let (a "chk1") A (Check 0 8 Read 1) [(t "v32")]);
      (Let (a "v33") L (RawLoad LdL 0) [(t "chk1")]);
      (Let (a "iw_4.iw_1.v8") L Sub [(t "v33"); (Const 72340172838076673)]);
      (Let (a "iw_4.iw_1.v10") L Xor [(t "v33"); (Const (-1))]);
      (Let (a "iw_4.iw_1.v11") L And [(t "iw_4.iw_1.v8"); (t "iw_4.iw_1.v10")]);
      (Let (a "iw_4.iw_1.v13") L And [(t "iw_4.iw_1.v11"); (Const 9259542123273814144)]);
      (Let (a "v37") W (Cmp Eq L) [(t "iw_4.iw_1.v13"); (Const 0)])] (JBranch (t "v37") (Poll (a "L28")) (To (a "iw_5.start"))));
  (mkBlock (a "iw_5.start") [] [] (JBranch (t "v37") (To (a "iw_5.iw_3.iw_1.iw_1.L4")) (To (a "iw_5.iw_3.iw_1.iw_1.L3"))));
  (mkBlock (a "iw_5.iw_3.iw_1.iw_1.L3") [] [(Let (a "iw_5.iw_3.iw_1.iw_1.v8") L Neg [(t "iw_4.iw_1.v13")]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v9") L And [(t "iw_4.iw_1.v13"); (t "iw_5.iw_3.iw_1.iw_1.v8")]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v10") L Sub [(t "iw_5.iw_3.iw_1.iw_1.v9"); (Const 1)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v11") L Shr [(t "iw_5.iw_3.iw_1.iw_1.v10"); (Const 1)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v12") L And [(t "iw_5.iw_3.iw_1.iw_1.v11"); (Const 6148914691236517205)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v13") L Sub [(t "iw_5.iw_3.iw_1.iw_1.v10"); (t "iw_5.iw_3.iw_1.iw_1.v12")]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v14") L And [(t "iw_5.iw_3.iw_1.iw_1.v13"); (Const 3689348814741910323)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v15") L Shr [(t "iw_5.iw_3.iw_1.iw_1.v13"); (Const 2)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v16") L And [(t "iw_5.iw_3.iw_1.iw_1.v15"); (Const 3689348814741910323)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v17") L Add [(t "iw_5.iw_3.iw_1.iw_1.v14"); (t "iw_5.iw_3.iw_1.iw_1.v16")]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v18") L Shr [(t "iw_5.iw_3.iw_1.iw_1.v17"); (Const 4)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v19") L Add [(t "iw_5.iw_3.iw_1.iw_1.v17"); (t "iw_5.iw_3.iw_1.iw_1.v18")]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v20") L And [(t "iw_5.iw_3.iw_1.iw_1.v19"); (Const 1085102592571150095)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v21") L Mul [(t "iw_5.iw_3.iw_1.iw_1.v20"); (Const 72340172838076673)]);
      (Let (a "iw_5.iw_3.iw_1.iw_1.v22") L Shr [(t "iw_5.iw_3.iw_1.iw_1.v21"); (Const 56)])] (JGoto (To (a "iw_5.iw_3.iw_1.iw_1.L4"))));
  (mkBlock (a "iw_5.iw_3.iw_1.iw_1.L4") [(Phi (a "iw_5.iw_3.iw_1.iw_1.v23") W [((a "iw_5.iw_3.iw_1.iw_1.L3"), (t "iw_5.iw_3.iw_1.iw_1.v22")); ((a "iw_5.start"), (Const 64))])] [(Let (a "iw_5.iw_3.iw_1.v27") W Shr [(t "iw_5.iw_3.iw_1.iw_1.v23"); (Const 3)]);
      (Let (a "v41") L (Ext Uw) [(t "iw_5.iw_3.iw_1.v27")]);
      (Flight (a "v42") Add [(FAddress (t "v32")); (FValue (t "v41"))] (LowerOf (t "v32")));
      (Let (a "v44") L Ptoi [(t "v42")]);
      (Let (a "v46") L Sub [(t "v44"); (t "v4")])] (JRet (t "v46")))].

Definition hi_fn___GI_strrchr : func :=
  mkFunc (a "__GI_strrchr") (a "export") (RClass P) [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Call (CResult (a "v7") L) (Global (a "__GI_strlen")) [(Arg P (t "v0"))]);
      (Let (a "v8") L Add [(t "v7"); (Const 1)]);
      (Call (CResult (a "v9") P) (Global (a "__GI___memrchr")) [(Arg P (t "v0")); (Arg W (t "v2")); (Arg L (t "v8"))])] (JRet (t "v9")))].
