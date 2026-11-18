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

Definition hello_image_fn_rpl_mbrtoc32 : func :=
  mkFunc (a "rpl_mbrtoc32") (a "export") (RClass L) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v12") L Ptoi [(t "v2")]);
      (Let (a "v13") L Ptoi [(Const 0)]);
      (Let (a "v14") W (Cmp Eq L) [(t "v12"); (t "v13")])] (JBranch (t "v14") (To (a "L8")) (To (a "L10"))));
  (mkBlock (a "L8") [] [(Let (a "v15") P Copy [(Global (a "mbrtoc32#str.36"))])] (JGoto (To (a "L10"))));
  (mkBlock (a "L10") [(Phi (a "pr.3") L [((a "L8"), (Const 1)); ((a "start"), (t "v4"))]); (Phi (a "pr.2") P [((a "L8"), (t "v15")); ((a "start"), (t "v2"))]); (Phi (a "pr.1") P [((a "L8"), (Const 0)); ((a "start"), (t "v0"))])] [(Let (a "v20") L Ptoi [(t "v6")]);
      (Let (a "v22") W (Cmp Eq L) [(t "v20"); (t "v13")])] (JBranch (t "v22") (To (a "L16")) (To (a "L18"))));
  (mkBlock (a "L16") [] [(Let (a "v23") P Copy [(Global (a "mbrtoc32#internal_state"))])] (JGoto (To (a "L18"))));
  (mkBlock (a "L18") [(Phi (a "pr.4") P [((a "L16"), (t "v23")); ((a "L10"), (t "v6"))])] [(Call (CResult (a "v29") L) (Global (a "mbrtoc32")) [(Arg P (t "pr.1")); (Arg P (t "pr.2")); (Arg L (t "pr.3")); (Arg P (t "pr.4"))]);
      (Let (a "v36") W (Cmp Uge L) [(t "v29"); (Const 18446744073709551614)])] (JBranch (t "v36") (To (a "L37")) (To (a "L38"))));
  (mkBlock (a "L37") [] [(Let (a "v40") W (Cmp Ne L) [(t "pr.3"); (Const 0)])] (JGoto (To (a "L38"))));
  (mkBlock (a "L38") [(Phi (a "v42") W [((a "L18"), (Const 0)); ((a "L37"), (t "v40"))])] [] (JBranch (t "v42") (To (a "L43")) (To (a "L44"))));
  (mkBlock (a "L43") [] [(Call (CResult (a "v45") W) (Global (a "hard_locale")) [(Arg W (Const 0))]);
      (Let (a "v46") W (Ext Ub) [(t "v45")]);
      (Let (a "v47") W (Cmp Eq W) [(t "v46"); (Const 0)])] (JGoto (To (a "L44"))));
  (mkBlock (a "L44") [(Phi (a "v49") W [((a "L38"), (Const 0)); ((a "L43"), (t "v47"))])] [] (JBranch (t "v49") (To (a "L30")) (To (a "L32"))));
  (mkBlock (a "L30") [] [(Let (a "v54") L Ptoi [(t "pr.1")]);
      (Let (a "v56") W (Cmp Ne L) [(t "v54"); (t "v13")])] (JBranch (t "v56") (To (a "L50")) (To (a "L52"))));
  (mkBlock (a "L50") [] [(Let (a "chk0") A (Check 0 1 Read 1) [(t "pr.2")]);
      (Let (a "v59") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "v60") W (Ext Ub) [(t "v59")]);
      (Let (a "chk1") A (Check 0 4 Write 1) [(t "pr.1")]);
      (RawStore Ww 0 (t "v60") (t "chk1"))] (JGoto (To (a "L52"))));
  (mkBlock (a "L52") [] [] (JRet (Const 1)));
  (mkBlock (a "L32") [] [] (JRet (t "v29")))].

Definition hello_image_fn_rpl_mbrtowc : func :=
  mkFunc (a "rpl_mbrtowc") (a "export") (RClass L) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v8") P (Alloc 4) [(Const 4)]);
      (Let (a "v13") L Ptoi [(t "v0")]);
      (Let (a "v15") W (Cmp Eq L) [(t "v13"); (Const 0)])] (JBranch (t "v15") (To (a "L11")) (To (a "L10"))));
  (mkBlock (a "L10") [] [] (JGoto (To (a "L11"))));
  (mkBlock (a "L11") [(Phi (a "pr.1") P [((a "L10"), (t "v0")); ((a "start"), (t "v8"))])] [(Call (CResult (a "v21") L) (Global (a "mbrtowc")) [(Arg P (t "pr.1")); (Arg P (t "v2")); (Arg L (t "v4")); (Arg P (t "v6"))]);
      (Let (a "v28") W (Cmp Uge L) [(t "v21"); (Const 18446744073709551614)])] (JBranch (t "v28") (To (a "L29")) (To (a "L30"))));
  (mkBlock (a "L29") [] [(Let (a "v32") W (Cmp Ne L) [(t "v4"); (Const 0)])] (JGoto (To (a "L30"))));
  (mkBlock (a "L30") [(Phi (a "v34") W [((a "L11"), (Const 0)); ((a "L29"), (t "v32"))])] [] (JBranch (t "v34") (To (a "L35")) (To (a "L36"))));
  (mkBlock (a "L35") [] [(Call (CResult (a "v37") W) (Global (a "hard_locale")) [(Arg W (Const 0))]);
      (Let (a "v38") W (Ext Ub) [(t "v37")]);
      (Let (a "v39") W (Cmp Eq W) [(t "v38"); (Const 0)])] (JGoto (To (a "L36"))));
  (mkBlock (a "L36") [(Phi (a "v41") W [((a "L30"), (Const 0)); ((a "L35"), (t "v39"))])] [] (JBranch (t "v41") (To (a "L22")) (To (a "L24"))));
  (mkBlock (a "L22") [] [(Let (a "chk0") A (Check 0 1 Read 1) [(t "v2")]);
      (Let (a "v44") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "v45") W (Ext Ub) [(t "v44")]);
      (Let (a "chk1") A (Check 0 4 Write 1) [(t "pr.1")]);
      (RawStore Ww 0 (t "v45") (t "chk1"))] (JRet (Const 1)));
  (mkBlock (a "L24") [] [] (JRet (t "v21")))].

Definition hello_image_fn_rpl_mbsrtowcs : func :=
  mkFunc (a "rpl_mbsrtowcs") (a "export") (RClass L) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v130") P (Alloc 4) [(Const 8)]);
      (Let (a "v12") L Ptoi [(t "v6")]);
      (Let (a "v13") L Ptoi [(Const 0)]);
      (Let (a "v14") W (Cmp Eq L) [(t "v12"); (t "v13")])] (JBranch (t "v14") (To (a "L8")) (To (a "L10"))));
  (mkBlock (a "L8") [] [(Let (a "v15") P Copy [(Global (a "_gl_mbsrtowcs_state"))])] (JGoto (To (a "L10"))));
  (mkBlock (a "L10") [(Phi (a "pr.2") P [((a "L8"), (t "v15")); ((a "start"), (t "v6"))])] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v18") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v23") L Ptoi [(t "v0")]);
      (Let (a "v25") W (Cmp Ne L) [(t "v23"); (t "v13")])] (JBranch (t "v25") (To (a "L28")) (To (a "L20"))));
  (mkBlock (a "L28") [(Phi (a "pr.7") P [((a "L102"), (t "v118")); ((a "L10"), (t "v0"))]); (Phi (a "pr.5") P [((a "L102"), (t "v116")); ((a "L10"), (t "v18"))]); (Phi (a "pr.1") L [((a "L102"), (t "v120")); ((a "L10"), (t "v4"))])] [(Let (a "v33") W (Cmp Ugt L) [(t "pr.1"); (Const 0)])] (JBranch (t "v33") (To (a "L29")) (To (a "L31"))));
  (mkBlock (a "L29") [] [(Let (a "chk1") A (Check 0 1 Read 1) [(t "pr.5")]);
      (Let (a "v40") W (RawLoad (LdNarrow Sb) 0) [(t "chk1")]);
      (Let (a "v41") W (Cmp Eq W) [(t "v40"); (Const 0)])] (JBranch (t "v41") (To (a "L37")) (To (a "L36"))));
  (mkBlock (a "L36") [] [(Flight (a "v46") Add [(FAddress (t "pr.5")); (FValue (Const 1))] (LowerOf (t "pr.5")));
      (Let (a "chk2") A (HalfCheck Upper 0 1 Read 1) [(t "chk1"); (t "v46")]);
      (Let (a "v47") W (RawLoad (LdNarrow Sb) 0) [(t "chk2")]);
      (Let (a "v48") W (Cmp Eq W) [(t "v47"); (Const 0)])] (JBranch (t "v48") (To (a "L37")) (To (a "L43"))));
  (mkBlock (a "L43") [] [(Flight (a "v53") Add [(FAddress (t "pr.5")); (FValue (Const 2))] (LowerOf (t "pr.5")));
      (Let (a "chk3") A (HalfCheck Upper 0 1 Read 1) [(t "chk1"); (t "v53")]);
      (Let (a "v54") W (RawLoad (LdNarrow Sb) 0) [(t "chk3")]);
      (Let (a "v55") W (Cmp Eq W) [(t "v54"); (Const 0)])] (JBranch (t "v55") (To (a "L37")) (To (a "L60"))));
  (mkBlock (a "L60") [] [(Flight (a "v63") Add [(FAddress (t "pr.5")); (FValue (Const 3))] (LowerOf (t "pr.5")));
      (Let (a "chk4") A (HalfCheck Upper 0 1 Read 1) [(t "chk1"); (t "v63")]);
      (Let (a "v64") W (RawLoad (LdNarrow Sb) 0) [(t "chk4")]);
      (Let (a "v65") W (Cmp Eq W) [(t "v64"); (Const 0)])] (JBranch (t "v65") (To (a "L37")) (To (a "L57"))));
  (mkBlock (a "L57") [] [(Flight (a "v69") Add [(FAddress (t "pr.5")); (FValue (Const 4))] (LowerOf (t "pr.5")));
      (Call (CResult (a "v72") L) (Global (a "strnlen1")) [(Arg P (t "v69")); (Arg L (Const 12))]);
      (Let (a "v73") L Add [(t "v72"); (Const 4)])] (JGoto (To (a "L37"))));
  (mkBlock (a "L37") [(Phi (a "pr.8") L [((a "L29"), (Const 1)); ((a "L36"), (Const 2)); ((a "L43"), (Const 3)); ((a "L57"), (t "v73")); ((a "L60"), (Const 4))])] [(Call (CResult (a "v79") L) (Global (a "rpl_mbrtowc")) [(Arg P (t "pr.7")); (Arg P (t "pr.5")); (Arg L (t "pr.8")); (Arg P (t "pr.2"))]);
      (Let (a "v86") W (Cmp Eq L) [(t "v79"); (Const 18446744073709551614)])] (JBranch (t "v86") (To (a "L80")) (To (a "L82"))));
  (mkBlock (a "L80") [] [(Call CVoid (Global (a "abort")) [])] (JGoto (To (a "L82"))));
  (mkBlock (a "L82") [] [(Let (a "v93") W (Cmp Eq L) [(t "v79"); (Const 18446744073709551615)])] (JBranch (t "v93") (To (a "L94")) (To (a "L89"))));
  (mkBlock (a "L89") [] [(Let (a "v100") W (Cmp Eq L) [(t "v79"); (Const 0)])] (JBranch (t "v100") (To (a "L31")) (To (a "L102"))));
  (mkBlock (a "L102") [] [(Flight (a "v116") Add [(FAddress (t "pr.5")); (FValue (t "v79"))] (LowerOf (t "pr.5")));
      (Flight (a "v118") Add [(FAddress (t "pr.7")); (FValue (Const 4))] (LowerOf (t "pr.7")));
      (Let (a "v120") L Sub [(t "pr.1"); (Const 1)])] (JGoto (Poll (a "L28"))));
  (mkBlock (a "L31") [(Phi (a "pr.6") P [((a "L28"), (t "pr.5")); ((a "L89"), (Const 0))])] [(Let (a "chk5") A (Renew 0 8 Write 8) [(t "chk0"); (t "v2")]);
      (RawStorePointer 0 (t "pr.6") (t "chk5") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v125") L Ptoi [(t "pr.7")]);
      (Let (a "v127") L Sub [(t "v125"); (t "v23")]);
      (Let (a "v128") L Div [(t "v127"); (Const 4)])] (JRet (t "v128")));
  (mkBlock (a "L20") [] [(Let (a "chk6") A (Check 0 8 Read 1) [(t "pr.2")]);
      (Let (a "v132") L (RawLoad LdL 0) [(t "chk6")]);
      (Let (a "chk7") A (Check 0 8 Write 1) [(t "v130")]);
      (RawStore Wl 0 (t "v132") (t "chk7"))] (JGoto (To (a "L134"))));
  (mkBlock (a "L134") [(Phi (a "pr.12") L [((a "L200"), (t "v208")); ((a "L20"), (Const 0))]); (Phi (a "pr.4") P [((a "L200"), (t "v206")); ((a "L20"), (t "v18"))])] [(Let (a "chk8") A (Check 0 1 Read 1) [(t "pr.4")]);
      (Let (a "v144") W (RawLoad (LdNarrow Sb) 0) [(t "chk8")]);
      (Let (a "v145") W (Cmp Eq W) [(t "v144"); (Const 0)])] (JBranch (t "v145") (To (a "L141")) (To (a "L140"))));
  (mkBlock (a "L140") [] [(Flight (a "v150") Add [(FAddress (t "pr.4")); (FValue (Const 1))] (LowerOf (t "pr.4")));
      (Let (a "chk9") A (HalfCheck Upper 0 1 Read 1) [(t "chk8"); (t "v150")]);
      (Let (a "v151") W (RawLoad (LdNarrow Sb) 0) [(t "chk9")]);
      (Let (a "v152") W (Cmp Eq W) [(t "v151"); (Const 0)])] (JBranch (t "v152") (To (a "L141")) (To (a "L147"))));
  (mkBlock (a "L147") [] [(Flight (a "v157") Add [(FAddress (t "pr.4")); (FValue (Const 2))] (LowerOf (t "pr.4")));
      (Let (a "chk10") A (HalfCheck Upper 0 1 Read 1) [(t "chk8"); (t "v157")]);
      (Let (a "v158") W (RawLoad (LdNarrow Sb) 0) [(t "chk10")]);
      (Let (a "v159") W (Cmp Eq W) [(t "v158"); (Const 0)])] (JBranch (t "v159") (To (a "L141")) (To (a "L164"))));
  (mkBlock (a "L164") [] [(Flight (a "v167") Add [(FAddress (t "pr.4")); (FValue (Const 3))] (LowerOf (t "pr.4")));
      (Let (a "chk11") A (HalfCheck Upper 0 1 Read 1) [(t "chk8"); (t "v167")]);
      (Let (a "v168") W (RawLoad (LdNarrow Sb) 0) [(t "chk11")]);
      (Let (a "v169") W (Cmp Eq W) [(t "v168"); (Const 0)])] (JBranch (t "v169") (To (a "L141")) (To (a "L161"))));
  (mkBlock (a "L161") [] [(Flight (a "v173") Add [(FAddress (t "pr.4")); (FValue (Const 4))] (LowerOf (t "pr.4")));
      (Call (CResult (a "v176") L) (Global (a "strnlen1")) [(Arg P (t "v173")); (Arg L (Const 12))]);
      (Let (a "v177") L Add [(t "v176"); (Const 4)])] (JGoto (To (a "L141"))));
  (mkBlock (a "L141") [(Phi (a "pr.13") L [((a "L134"), (Const 1)); ((a "L140"), (Const 2)); ((a "L147"), (Const 3)); ((a "L161"), (t "v177")); ((a "L164"), (Const 4))])] [(Call (CResult (a "v181") L) (Global (a "rpl_mbrtowc")) [(Arg P (Const 0)); (Arg P (t "pr.4")); (Arg L (t "pr.13")); (Arg P (t "v130"))]);
      (Let (a "v188") W (Cmp Eq L) [(t "v181"); (Const 18446744073709551614)])] (JBranch (t "v188") (To (a "L182")) (To (a "L184"))));
  (mkBlock (a "L182") [] [(Call CVoid (Global (a "abort")) [])] (JGoto (To (a "L184"))));
  (mkBlock (a "L184") [] [(Let (a "v195") W (Cmp Eq L) [(t "v181"); (Const 18446744073709551615)])] (JBranch (t "v195") (To (a "L196")) (To (a "L191"))));
  (mkBlock (a "L191") [] [(Let (a "v202") W (Cmp Eq L) [(t "v181"); (Const 0)])] (JBranch (t "v202") (To (a "L137")) (To (a "L200"))));
  (mkBlock (a "L200") [] [(Flight (a "v206") Add [(FAddress (t "pr.4")); (FValue (t "v181"))] (LowerOf (t "pr.4")));
      (Let (a "v208") L Add [(t "pr.12"); (Const 1)])] (JGoto (Poll (a "L134"))));
  (mkBlock (a "L137") [] [] (JRet (t "pr.12")));
  (mkBlock (a "L94") [] [(Let (a "chk12") A (Renew 0 8 Write 8) [(t "chk0"); (t "v2")]);
      (RawStorePointer 0 (t "pr.5") (t "chk12") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L196"))));
  (mkBlock (a "L196") [] [(Call (CResult (a "v212") P) (Global (a "__errno_location")) []);
      (Let (a "chk13") A (Check 0 4 Write 1) [(t "v212")]);
      (RawStore Ww 0 (Const 84) (t "chk13"))] (JRet (Const 18446744073709551615)))].
