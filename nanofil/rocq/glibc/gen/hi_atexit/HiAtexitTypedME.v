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

Definition hi_fn___GI___mempcpy : func :=
  mkFunc (a "__GI___mempcpy") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Call (CResult (a "v9") P) (Global (a "__GI_memcpy")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg L (t "v4"))]);
      (Flight (a "v11") Add [(FAddress (t "v9")); (FValue (t "v4"))] (LowerOf (t "v9")))] (JRet (t "v11")))].

Definition hi_fn___GI_memcpy : func :=
  mkFunc (a "__GI_memcpy") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Call CVoid (Global (a "zmemmove")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg L (t "v4"))])] (JRet (t "v0")))].

Definition hi_fn___GI___memrchr : func :=
  mkFunc (a "__GI___memrchr") (a "export") (RClass P) [(P, (a "v0")); (W, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v10") W (Cmp Eq L) [(t "v4"); (Const 0)])] (JBranch (t "v10") (To (a "L6")) (To (a "L8"))));
  (mkBlock (a "L6") [] [] (JRet (Const 0)));
  (mkBlock (a "L8") [] [(Flight (a "v17") Add [(FAddress (t "v0")); (FValue (t "v4"))] (LowerOf (t "v0")));
      (Let (a "v18") L Ptoi [(t "v17")]);
      (Let (a "v19") L Add [(t "v18"); (Const 8)]);
      (Let (a "v20") L Sub [(t "v19"); (Const 1)]);
      (Let (a "v22") L And [(t "v20"); (Const 18446744073709551608)]);
      (Let (a "lc.2") L Sub [(t "v22"); (t "v18")]);
      (Flight (a "v23") Add [(FAddress (t "v17")); (FValue (t "lc.2"))] (LowerOf (t "v17")));
      (Let (a "v26") L Ptoi [(t "v0")]);
      (Let (a "v28") L Add [(t "v26"); (t "v4")]);
      (Flight (a "v31") Sub [(FAddress (t "v23")); (FValue (Const 8))] (LowerOf (t "v23")));
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v31")]);
      (Let (a "v32") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v35") W (Ext Ub) [(t "v2")]);
      (Let (a "iw_1.v6") L (Ext Uw) [(t "v35")]);
      (Let (a "iw_1.v7") L Mul [(t "iw_1.v6"); (Const 72340172838076673)]);
      (Let (a "v41") L And [(t "v26"); (Const 18446744073709551608)]);
      (Let (a "lc.4") L Sub [(t "v41"); (t "v26")]);
      (Flight (a "v42") Add [(FAddress (t "v0")); (FValue (t "lc.4"))] (LowerOf (t "v0")));
      (Let (a "iw_2.v6") L Xor [(t "v32"); (t "iw_1.v7")]);
      (Let (a "iw_2.iw_1.v6") L And [(t "iw_2.v6"); (Const 9187201950435737471)]);
      (Let (a "iw_2.iw_1.v8") L Add [(t "iw_2.iw_1.v6"); (Const 9187201950435737471)]);
      (Let (a "iw_2.iw_1.v10") L Or [(t "iw_2.iw_1.v8"); (t "iw_2.v6")]);
      (Let (a "iw_2.iw_1.v12") L Or [(t "iw_2.iw_1.v10"); (Const 9187201950435737471)]);
      (Let (a "iw_2.iw_1.v13") L Xor [(t "iw_2.iw_1.v12"); (Const (-1))]);
      (Let (a "iw_3.v5") L And [(t "v28"); (Const 7)]);
      (Let (a "iw_3.v10") W (Cmp Eq L) [(t "iw_3.v5"); (Const 0)])] (JBranch (t "iw_3.v10") (To (a "iw_3.join")) (To (a "iw_3.L13"))));
  (mkBlock (a "iw_3.L13") [] [(Let (a "iw_3.v21") L Shl [(t "iw_3.v5"); (Const 3)]);
      (Let (a "iw_3.v22") L Shl [(Const 18446744073709551615); (t "iw_3.v21")]);
      (Let (a "iw_3.v23") L Xor [(t "iw_3.v22"); (Const (-1))]);
      (Let (a "iw_3.v24") L And [(t "iw_2.iw_1.v13"); (t "iw_3.v23")])] (JGoto (To (a "iw_3.join"))));
  (mkBlock (a "iw_3.join") [(Phi (a "v48") L [((a "iw_3.L13"), (t "iw_3.v24")); ((a "L8"), (t "iw_2.iw_1.v13"))])] [(Let (a "v53") W (Cmp Ne L) [(t "v48"); (Const 0)])] (JBranch (t "v53") (To (a "iw_4.start")) (To (a "L51"))));
  (mkBlock (a "iw_4.start") [] [(Let (a "iw_4.iw_1.iw_1.v6") W (Cmp Eq L) [(t "v48"); (Const 0)])] (JBranch (t "iw_4.iw_1.iw_1.v6") (To (a "iw_4.iw_1.iw_1.L4")) (To (a "iw_4.iw_1.iw_1.L3"))));
  (mkBlock (a "iw_4.iw_1.iw_1.L3") [] [(Let (a "iw_4.iw_1.iw_1.v8") L Shr [(t "v48"); (Const 1)]);
      (Let (a "iw_4.iw_1.iw_1.v9") L Or [(t "v48"); (t "iw_4.iw_1.iw_1.v8")]);
      (Let (a "iw_4.iw_1.iw_1.v10") L Shr [(t "iw_4.iw_1.iw_1.v9"); (Const 2)]);
      (Let (a "iw_4.iw_1.iw_1.v11") L Or [(t "iw_4.iw_1.iw_1.v9"); (t "iw_4.iw_1.iw_1.v10")]);
      (Let (a "iw_4.iw_1.iw_1.v12") L Shr [(t "iw_4.iw_1.iw_1.v11"); (Const 4)]);
      (Let (a "iw_4.iw_1.iw_1.v13") L Or [(t "iw_4.iw_1.iw_1.v11"); (t "iw_4.iw_1.iw_1.v12")]);
      (Let (a "iw_4.iw_1.iw_1.v14") L Shr [(t "iw_4.iw_1.iw_1.v13"); (Const 8)]);
      (Let (a "iw_4.iw_1.iw_1.v15") L Or [(t "iw_4.iw_1.iw_1.v13"); (t "iw_4.iw_1.iw_1.v14")]);
      (Let (a "iw_4.iw_1.iw_1.v16") L Shr [(t "iw_4.iw_1.iw_1.v15"); (Const 16)]);
      (Let (a "iw_4.iw_1.iw_1.v17") L Or [(t "iw_4.iw_1.iw_1.v15"); (t "iw_4.iw_1.iw_1.v16")]);
      (Let (a "iw_4.iw_1.iw_1.v18") L Shr [(t "iw_4.iw_1.iw_1.v17"); (Const 32)]);
      (Let (a "iw_4.iw_1.iw_1.v19") L Or [(t "iw_4.iw_1.iw_1.v17"); (t "iw_4.iw_1.iw_1.v18")]);
      (Let (a "iw_4.iw_1.iw_1.v20") L Shr [(t "iw_4.iw_1.iw_1.v19"); (Const 1)]);
      (Let (a "iw_4.iw_1.iw_1.v21") L And [(t "iw_4.iw_1.iw_1.v20"); (Const 6148914691236517205)]);
      (Let (a "iw_4.iw_1.iw_1.v22") L Sub [(t "iw_4.iw_1.iw_1.v19"); (t "iw_4.iw_1.iw_1.v21")]);
      (Let (a "iw_4.iw_1.iw_1.v23") L And [(t "iw_4.iw_1.iw_1.v22"); (Const 3689348814741910323)]);
      (Let (a "iw_4.iw_1.iw_1.v24") L Shr [(t "iw_4.iw_1.iw_1.v22"); (Const 2)]);
      (Let (a "iw_4.iw_1.iw_1.v25") L And [(t "iw_4.iw_1.iw_1.v24"); (Const 3689348814741910323)]);
      (Let (a "iw_4.iw_1.iw_1.v26") L Add [(t "iw_4.iw_1.iw_1.v23"); (t "iw_4.iw_1.iw_1.v25")]);
      (Let (a "iw_4.iw_1.iw_1.v27") L Shr [(t "iw_4.iw_1.iw_1.v26"); (Const 4)]);
      (Let (a "iw_4.iw_1.iw_1.v28") L Add [(t "iw_4.iw_1.iw_1.v26"); (t "iw_4.iw_1.iw_1.v27")]);
      (Let (a "iw_4.iw_1.iw_1.v29") L And [(t "iw_4.iw_1.iw_1.v28"); (Const 1085102592571150095)]);
      (Let (a "iw_4.iw_1.iw_1.v30") L Mul [(t "iw_4.iw_1.iw_1.v29"); (Const 72340172838076673)]);
      (Let (a "iw_4.iw_1.iw_1.v31") L Shr [(t "iw_4.iw_1.iw_1.v30"); (Const 56)]);
      (Let (a "iw_4.iw_1.iw_1.v32") L Sub [(t "iw_4.iw_1.iw_1.v31"); (Const 64)]);
      (Let (a "iw_4.iw_1.iw_1.v33") L Neg [(t "iw_4.iw_1.iw_1.v32")])] (JGoto (To (a "iw_4.iw_1.iw_1.L4"))));
  (mkBlock (a "iw_4.iw_1.iw_1.L4") [(Phi (a "iw_4.iw_1.iw_1.v34") W [((a "iw_4.iw_1.iw_1.L3"), (t "iw_4.iw_1.iw_1.v33")); ((a "iw_4.start"), (Const 64))])] [(Let (a "iw_4.iw_1.v7") W Shr [(t "iw_4.iw_1.iw_1.v34"); (Const 3)]);
      (Let (a "iw_4.v13") L (Ext Uw) [(t "iw_4.iw_1.v7")]);
      (Let (a "iw_4.v14") L Sub [(Const 7); (t "iw_4.v13")])] (JGoto (To (a "iw_4.join"))));
  (mkBlock (a "iw_4.join") [(Phi (a "v57") W [((a "iw_4.iw_1.iw_1.L4"), (t "iw_4.v14"))])] [(Let (a "v58") L (Ext Uw) [(t "v57")]);
      (Flight (a "v59") Add [(FAddress (t "v31")); (FValue (t "v58"))] (LowerOf (t "v31")));
      (Let (a "v65") L Ptoi [(t "v59")]);
      (Let (a "v67") W (Cmp Uge L) [(t "v65"); (t "v26")])] (JBranch (t "v67") (To (a "L62")) (To (a "L61"))));
  (mkBlock (a "L61") [] [] (JGoto (To (a "L62"))));
  (mkBlock (a "L62") [(Phi (a "v69") P [((a "L61"), (Const 0)); ((a "iw_4.join"), (t "v59"))])] [] (JRet (t "v69")));
  (mkBlock (a "L51") [] [(Let (a "v76") L Ptoi [(t "v31")]);
      (Let (a "v77") L Ptoi [(t "v42")]);
      (Let (a "v78") W (Cmp Eq L) [(t "v76"); (t "v77")])] (JBranch (t "v78") (To (a "L71")) (To (a "L73"))));
  (mkBlock (a "L71") [] [] (JRet (Const 0)));
  (mkBlock (a "L73") [] [(Flight (a "v81") Sub [(FAddress (t "v31")); (FValue (Const 8))] (LowerOf (t "v31")));
      (Let (a "chk1") A (HalfCheck Lower 0 8 Read 1) [(t "chk0"); (t "v81")]);
      (Let (a "v82") L (RawLoad LdL 0) [(t "chk1")])] (JGoto (To (a "L83"))));
  (mkBlock (a "L83") [(Phi (a "pr.2") L [((a "L73"), (t "v82")); ((a "L93"), (t "v107"))]); (Phi (a "pr.1") P [((a "L73"), (t "v81")); ((a "L93"), (t "v106"))])] [(Let (a "v88") L Ptoi [(t "pr.1")]);
      (Let (a "v90") W (Cmp Ne L) [(t "v88"); (t "v77")])] (JBranch (t "v90") (To (a "iw_5.start")) (To (a "iw_7.start"))));
  (mkBlock (a "iw_5.start") [] [(Let (a "iw_5.iw_1.v6") L Xor [(t "pr.2"); (t "iw_1.v7")]);
      (Let (a "iw_5.iw_1.iw_1.v8") L Sub [(t "iw_5.iw_1.v6"); (Const 72340172838076673)]);
      (Let (a "iw_5.iw_1.iw_1.v10") L Xor [(t "iw_5.iw_1.v6"); (Const (-1))]);
      (Let (a "iw_5.iw_1.iw_1.v11") L And [(t "iw_5.iw_1.iw_1.v8"); (t "iw_5.iw_1.iw_1.v10")]);
      (Let (a "iw_5.iw_1.iw_1.v13") L And [(t "iw_5.iw_1.iw_1.v11"); (Const 9259542123273814144)]);
      (Let (a "iw_5.v7") W (Cmp Ne L) [(t "iw_5.iw_1.iw_1.v13"); (Const 0)])] (JBranch (t "iw_5.v7") (To (a "iw_6.start")) (To (a "L93"))));
  (mkBlock (a "iw_6.start") [] [(Let (a "iw_6.iw_1.iw_1.v6") L And [(t "iw_5.iw_1.v6"); (Const 9187201950435737471)]);
      (Let (a "iw_6.iw_1.iw_1.v8") L Add [(t "iw_6.iw_1.iw_1.v6"); (Const 9187201950435737471)]);
      (Let (a "iw_6.iw_1.iw_1.v10") L Or [(t "iw_6.iw_1.iw_1.v8"); (t "iw_5.iw_1.v6")]);
      (Let (a "iw_6.iw_1.iw_1.v12") L Or [(t "iw_6.iw_1.iw_1.v10"); (Const 9187201950435737471)]);
      (Let (a "iw_6.iw_1.iw_1.v13") L Xor [(t "iw_6.iw_1.iw_1.v12"); (Const (-1))]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v6") W (Cmp Eq L) [(t "iw_6.iw_1.iw_1.v13"); (Const 0)])] (JBranch (t "iw_6.iw_1.iw_3.iw_1.iw_1.v6") (To (a "iw_6.iw_1.iw_3.iw_1.iw_1.L4")) (To (a "iw_6.iw_1.iw_3.iw_1.iw_1.L3"))));
  (mkBlock (a "iw_6.iw_1.iw_3.iw_1.iw_1.L3") [] [(Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v8") L Shr [(t "iw_6.iw_1.iw_1.v13"); (Const 1)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v9") L Or [(t "iw_6.iw_1.iw_1.v13"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v8")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v10") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v9"); (Const 2)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v11") L Or [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v9"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v10")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v12") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v11"); (Const 4)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v13") L Or [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v11"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v12")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v14") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v13"); (Const 8)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v15") L Or [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v13"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v14")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v16") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v15"); (Const 16)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v17") L Or [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v15"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v16")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v18") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v17"); (Const 32)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v19") L Or [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v17"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v18")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v20") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v19"); (Const 1)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v21") L And [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v20"); (Const 6148914691236517205)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v22") L Sub [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v19"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v21")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v23") L And [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v22"); (Const 3689348814741910323)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v24") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v22"); (Const 2)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v25") L And [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v24"); (Const 3689348814741910323)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v26") L Add [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v23"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v25")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v27") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v26"); (Const 4)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v28") L Add [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v26"); (t "iw_6.iw_1.iw_3.iw_1.iw_1.v27")]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v29") L And [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v28"); (Const 1085102592571150095)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v30") L Mul [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v29"); (Const 72340172838076673)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v31") L Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v30"); (Const 56)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v32") L Sub [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v31"); (Const 64)]);
      (Let (a "iw_6.iw_1.iw_3.iw_1.iw_1.v33") L Neg [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v32")])] (JGoto (To (a "iw_6.iw_1.iw_3.iw_1.iw_1.L4"))));
  (mkBlock (a "iw_6.iw_1.iw_3.iw_1.iw_1.L4") [(Phi (a "iw_6.iw_1.iw_3.iw_1.iw_1.v34") W [((a "iw_6.iw_1.iw_3.iw_1.iw_1.L3"), (t "iw_6.iw_1.iw_3.iw_1.iw_1.v33")); ((a "iw_6.start"), (Const 64))])] [(Let (a "iw_6.iw_1.iw_3.iw_1.v7") W Shr [(t "iw_6.iw_1.iw_3.iw_1.iw_1.v34"); (Const 3)]);
      (Let (a "iw_6.iw_1.iw_3.v13") L (Ext Uw) [(t "iw_6.iw_1.iw_3.iw_1.v7")]);
      (Let (a "iw_6.iw_1.iw_3.v14") L Sub [(Const 7); (t "iw_6.iw_1.iw_3.v13")])] (JGoto (To (a "iw_6.iw_1.iw_3.join"))));
  (mkBlock (a "iw_6.iw_1.iw_3.join") [(Phi (a "iw_6.iw_1.v11") W [((a "iw_6.iw_1.iw_3.iw_1.iw_1.L4"), (t "iw_6.iw_1.iw_3.v14"))])] [(Let (a "v102") L (Ext Uw) [(t "iw_6.iw_1.v11")]);
      (Flight (a "v103") Add [(FAddress (t "pr.1")); (FValue (t "v102"))] (LowerOf (t "pr.1")))] (JRet (t "v103")));
  (mkBlock (a "L93") [] [(Flight (a "v106") Sub [(FAddress (t "pr.1")); (FValue (Const 8))] (LowerOf (t "pr.1")));
      (Let (a "chk2") A (Check 0 8 Read 1) [(t "v106")]);
      (Let (a "v107") L (RawLoad LdL 0) [(t "chk2")])] (JGoto (Poll (a "L83"))));
  (mkBlock (a "iw_7.start") [] [(Let (a "iw_7.iw_1.v6") L Xor [(t "pr.2"); (t "iw_1.v7")]);
      (Let (a "iw_7.iw_1.iw_1.v8") L Sub [(t "iw_7.iw_1.v6"); (Const 72340172838076673)]);
      (Let (a "iw_7.iw_1.iw_1.v10") L Xor [(t "iw_7.iw_1.v6"); (Const (-1))]);
      (Let (a "iw_7.iw_1.iw_1.v11") L And [(t "iw_7.iw_1.iw_1.v8"); (t "iw_7.iw_1.iw_1.v10")]);
      (Let (a "iw_7.iw_1.iw_1.v13") L And [(t "iw_7.iw_1.iw_1.v11"); (Const 9259542123273814144)]);
      (Let (a "iw_7.v7") W (Cmp Ne L) [(t "iw_7.iw_1.iw_1.v13"); (Const 0)])] (JBranch (t "iw_7.v7") (To (a "iw_8.start")) (To (a "L110"))));
  (mkBlock (a "iw_8.start") [] [(Let (a "iw_8.iw_1.iw_1.v6") L And [(t "iw_7.iw_1.v6"); (Const 9187201950435737471)]);
      (Let (a "iw_8.iw_1.iw_1.v8") L Add [(t "iw_8.iw_1.iw_1.v6"); (Const 9187201950435737471)]);
      (Let (a "iw_8.iw_1.iw_1.v10") L Or [(t "iw_8.iw_1.iw_1.v8"); (t "iw_7.iw_1.v6")]);
      (Let (a "iw_8.iw_1.iw_1.v12") L Or [(t "iw_8.iw_1.iw_1.v10"); (Const 9187201950435737471)]);
      (Let (a "iw_8.iw_1.iw_1.v13") L Xor [(t "iw_8.iw_1.iw_1.v12"); (Const (-1))]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v6") W (Cmp Eq L) [(t "iw_8.iw_1.iw_1.v13"); (Const 0)])] (JBranch (t "iw_8.iw_1.iw_3.iw_1.iw_1.v6") (To (a "iw_8.iw_1.iw_3.iw_1.iw_1.L4")) (To (a "iw_8.iw_1.iw_3.iw_1.iw_1.L3"))));
  (mkBlock (a "iw_8.iw_1.iw_3.iw_1.iw_1.L3") [] [(Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v8") L Shr [(t "iw_8.iw_1.iw_1.v13"); (Const 1)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v9") L Or [(t "iw_8.iw_1.iw_1.v13"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v8")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v10") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v9"); (Const 2)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v11") L Or [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v9"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v10")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v12") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v11"); (Const 4)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v13") L Or [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v11"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v12")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v14") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v13"); (Const 8)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v15") L Or [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v13"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v14")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v16") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v15"); (Const 16)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v17") L Or [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v15"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v16")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v18") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v17"); (Const 32)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v19") L Or [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v17"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v18")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v20") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v19"); (Const 1)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v21") L And [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v20"); (Const 6148914691236517205)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v22") L Sub [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v19"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v21")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v23") L And [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v22"); (Const 3689348814741910323)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v24") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v22"); (Const 2)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v25") L And [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v24"); (Const 3689348814741910323)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v26") L Add [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v23"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v25")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v27") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v26"); (Const 4)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v28") L Add [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v26"); (t "iw_8.iw_1.iw_3.iw_1.iw_1.v27")]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v29") L And [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v28"); (Const 1085102592571150095)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v30") L Mul [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v29"); (Const 72340172838076673)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v31") L Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v30"); (Const 56)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v32") L Sub [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v31"); (Const 64)]);
      (Let (a "iw_8.iw_1.iw_3.iw_1.iw_1.v33") L Neg [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v32")])] (JGoto (To (a "iw_8.iw_1.iw_3.iw_1.iw_1.L4"))));
  (mkBlock (a "iw_8.iw_1.iw_3.iw_1.iw_1.L4") [(Phi (a "iw_8.iw_1.iw_3.iw_1.iw_1.v34") W [((a "iw_8.iw_1.iw_3.iw_1.iw_1.L3"), (t "iw_8.iw_1.iw_3.iw_1.iw_1.v33")); ((a "iw_8.start"), (Const 64))])] [(Let (a "iw_8.iw_1.iw_3.iw_1.v7") W Shr [(t "iw_8.iw_1.iw_3.iw_1.iw_1.v34"); (Const 3)]);
      (Let (a "iw_8.iw_1.iw_3.v13") L (Ext Uw) [(t "iw_8.iw_1.iw_3.iw_1.v7")]);
      (Let (a "iw_8.iw_1.iw_3.v14") L Sub [(Const 7); (t "iw_8.iw_1.iw_3.v13")])] (JGoto (To (a "iw_8.iw_1.iw_3.join"))));
  (mkBlock (a "iw_8.iw_1.iw_3.join") [(Phi (a "iw_8.iw_1.v11") W [((a "iw_8.iw_1.iw_3.iw_1.iw_1.L4"), (t "iw_8.iw_1.iw_3.v14"))])] [(Let (a "v120") L (Ext Uw) [(t "iw_8.iw_1.v11")]);
      (Flight (a "v121") Add [(FAddress (t "pr.1")); (FValue (t "v120"))] (LowerOf (t "pr.1")));
      (Let (a "v127") L Ptoi [(t "v121")]);
      (Let (a "v129") W (Cmp Uge L) [(t "v127"); (t "v26")])] (JBranch (t "v129") (To (a "L122")) (To (a "L110"))));
  (mkBlock (a "L122") [] [] (JRet (t "v121")));
  (mkBlock (a "L110") [] [] (JRet (Const 0)))].
