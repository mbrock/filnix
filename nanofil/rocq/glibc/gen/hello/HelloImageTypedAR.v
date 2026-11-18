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

Definition hello_image_fn_glibc_l10nflist'23argz_count__ : func :=
  mkFunc (a "glibc_l10nflist#argz_count__") (a "local") (RClass L) [(P, (a "v0")); (L, (a "v2"))] [(mkBlock (a "start") [] [] (JGoto (To (a "L5"))));
  (mkBlock (a "L5") [(Phi (a "pr.3") L [((a "L6"), (t "v22")); ((a "start"), (Const 0))]); (Phi (a "pr.2") L [((a "L6"), (t "v20")); ((a "start"), (t "v2"))]); (Phi (a "pr.1") P [((a "L6"), (t "v16")); ((a "start"), (t "v0"))])] [(Let (a "v9") W (Cmp Ugt L) [(t "pr.2"); (Const 0)])] (JBranch (t "v9") (To (a "L6")) (To (a "L7"))));
  (mkBlock (a "L6") [] [(Call (CResult (a "v12") L) (Global (a "__GI_strlen")) [(Arg P (t "pr.1"))]);
      (Let (a "v15") L Add [(t "v12"); (Const 1)]);
      (Flight (a "v16") Add [(FAddress (t "pr.1")); (FValue (t "v15"))] (LowerOf (t "pr.1")));
      (Let (a "v20") L Sub [(t "pr.2"); (t "v15")]);
      (Let (a "v22") L Add [(t "pr.3"); (Const 1)])] (JGoto (Poll (a "L5"))));
  (mkBlock (a "L7") [] [] (JRet (t "pr.3")))].

Definition hello_image_fn_glibc_l10nflist'23argz_stringify__ : func :=
  mkFunc (a "glibc_l10nflist#argz_stringify__") (a "local") RVoid [(P, (a "v0")); (L, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [] (JGoto (To (a "L6"))));
  (mkBlock (a "L6") [(Phi (a "pr.3") L [((a "start"), (t "v2")); ((a "L21"), (t "v20")); ((a "L7"), (t "v20"))]); (Phi (a "pr.2") P [((a "start"), (t "v0")); ((a "L21"), (t "v27")); ((a "L7"), (t "v16"))])] [(Let (a "v10") W (Cmp Ugt L) [(t "pr.3"); (Const 0)])] (JBranch (t "v10") (To (a "L7")) (To (a "L8"))));
  (mkBlock (a "L7") [] [(Call (CResult (a "v13") L) (Global (a "__GI_strlen")) [(Arg P (t "pr.2"))]);
      (Flight (a "v16") Add [(FAddress (t "pr.2")); (FValue (t "v13"))] (LowerOf (t "pr.2")));
      (Let (a "v19") L Add [(t "v13"); (Const 1)]);
      (Let (a "v20") L Sub [(t "pr.3"); (t "v19")]);
      (Let (a "v25") W (Cmp Ugt L) [(t "v20"); (Const 0)])] (JBranch (t "v25") (To (a "L21")) (Poll (a "L6"))));
  (mkBlock (a "L21") [] [(Flight (a "v27") Add [(FAddress (t "v16")); (FValue (Const 1))] (LowerOf (t "v16")));
      (Let (a "v29") W (Ext Sb) [(t "v4")]);
      (Let (a "chk0") A (Check 0 1 Write 1) [(t "v16")]);
      (RawStore Wb 0 (t "v29") (t "chk0"))] (JGoto (Poll (a "L6"))));
  (mkBlock (a "L8") [] [] JRetVoid)].

Definition hello_image_fn___argz_add_sep : func :=
  mkFunc (a "__argz_add_sep") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (W, (a "v6"))] [(mkBlock (a "start") [] [(Call (CResult (a "v10") L) (Global (a "__GI_strlen")) [(Arg P (t "v4"))]);
      (Let (a "v11") L Add [(t "v10"); (Const 1)]);
      (Let (a "v16") W (Cmp Ugt L) [(t "v11"); (Const 1)])] (JBranch (t "v16") (To (a "L12")) (To (a "L14"))));
  (mkBlock (a "L12") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v21") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Read 1) [(t "v2")]);
      (Let (a "v23") L (RawLoad LdL 0) [(t "chk1")]);
      (Let (a "v25") L Add [(t "v23"); (t "v11")]);
      (Call (CResult (a "v26") P) (Global (a "realloc")) [(Arg P (t "v21")); (Arg L (t "v25"))]);
      (Let (a "v31") L Ptoi [(t "v26")]);
      (Let (a "v32") L Ptoi [(Const 0)]);
      (Let (a "v33") W (Cmp Eq L) [(t "v31"); (t "v32")])] (JBranch (t "v33") (To (a "L27")) (To (a "L29"))));
  (mkBlock (a "L27") [] [] (JRet (Const 12)));
  (mkBlock (a "L29") [] [(Let (a "chk2") A (Renew 0 8 Write 8) [(t "chk0"); (t "v0")]);
      (RawStorePointer 0 (t "v26") (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk3") A (Renew 0 8 Read 8) [(t "chk0"); (t "v0")]);
      (Let (a "v38") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Let (a "chk4") A (Renew 0 8 Read 1) [(t "chk1"); (t "v2")]);
      (Let (a "v40") L (RawLoad LdL 0) [(t "chk4")]);
      (Flight (a "v41") Add [(FAddress (t "v38")); (FValue (t "v40"))] (LowerOf (t "v38")))] (JGoto (To (a "L43"))));
  (mkBlock (a "L43") [(Phi (a "pr.5") P [((a "L29"), (t "v41")); ((a "L48"), (t "pr.6"))]); (Phi (a "pr.4") P [((a "L29"), (t "v4")); ((a "L48"), (t "v81"))]); (Phi (a "pr.1") L [((a "L29"), (t "v11")); ((a "L48"), (t "pr.2"))])] [(Let (a "chk5") A (Check 0 1 Read 1) [(t "pr.4")]);
      (Let (a "v50") W (RawLoad (LdNarrow Sb) 0) [(t "chk5")]);
      (Let (a "v52") W (Cmp Eq W) [(t "v50"); (t "v6")])] (JBranch (t "v52") (To (a "L46")) (To (a "L47"))));
  (mkBlock (a "L46") [] [(Let (a "chk6") A (Renew 0 8 Read 8) [(t "chk0"); (t "v0")]);
      (Let (a "v58") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v59") L Ptoi [(t "pr.5")]);
      (Let (a "v60") L Ptoi [(t "v58")]);
      (Let (a "v61") W (Cmp Ugt L) [(t "v59"); (t "v60")])] (JBranch (t "v61") (To (a "L62")) (To (a "L63"))));
  (mkBlock (a "L62") [] [(Flight (a "v67") Add [(FAddress (t "pr.5")); (FValue (Const 18446744073709551615))] (LowerOf (t "pr.5")));
      (Let (a "chk7") A (Check 0 1 Read 1) [(t "v67")]);
      (Let (a "v68") W (RawLoad (LdNarrow Sb) 0) [(t "chk7")]);
      (Let (a "v69") W (Cmp Ne W) [(t "v68"); (Const 0)])] (JGoto (To (a "L63"))));
  (mkBlock (a "L63") [(Phi (a "v71") W [((a "L46"), (Const 0)); ((a "L62"), (t "v69"))])] [] (JBranch (t "v71") (To (a "L53")) (To (a "L54"))));
  (mkBlock (a "L53") [] [(Flight (a "v73") Add [(FAddress (t "pr.5")); (FValue (Const 1))] (LowerOf (t "pr.5")));
      (Let (a "chk8") A (Check 0 1 Write 1) [(t "pr.5")]);
      (RawStore Wb 0 (Const 0) (t "chk8"))] (JGoto (To (a "L48"))));
  (mkBlock (a "L54") [] [(Let (a "v75") L Sub [(t "pr.1"); (Const 1)])] (JGoto (To (a "L48"))));
  (mkBlock (a "L47") [] [(Flight (a "v77") Add [(FAddress (t "pr.5")); (FValue (Const 1))] (LowerOf (t "pr.5")));
      (Let (a "v79") W (RawLoad (LdNarrow Sb) 0) [(t "chk5")]);
      (Let (a "chk10") A (Check 0 1 Write 1) [(t "pr.5")]);
      (RawStore Wb 0 (t "v79") (t "chk10"))] (JGoto (To (a "L48"))));
  (mkBlock (a "L48") [(Phi (a "pr.6") P [((a "L47"), (t "v77")); ((a "L53"), (t "v73")); ((a "L54"), (t "pr.5"))]); (Phi (a "pr.2") L [((a "L47"), (t "pr.1")); ((a "L53"), (t "pr.1")); ((a "L54"), (t "v75"))])] [(Flight (a "v81") Add [(FAddress (t "pr.4")); (FValue (Const 1))] (LowerOf (t "pr.4")));
      (Let (a "v82") W (RawLoad (LdNarrow Sb) 0) [(t "chk5")]);
      (Let (a "v83") W (Cmp Ne W) [(t "v82"); (Const 0)])] (JBranch (t "v83") (Poll (a "L43")) (To (a "L45"))));
  (mkBlock (a "L45") [] [(Let (a "chk12") A (Renew 0 8 Read 1) [(t "chk1"); (t "v2")]);
      (Let (a "v85") L (RawLoad LdL 0) [(t "chk12")]);
      (Let (a "v87") L Add [(t "v85"); (t "pr.2")]);
      (Let (a "chk13") A (Renew 0 8 Write 1) [(t "chk1"); (t "v2")]);
      (RawStore Wl 0 (t "v87") (t "chk13"))] (JGoto (To (a "L14"))));
  (mkBlock (a "L14") [] [] (JRet (Const 0)))].

Definition hello_image_fn___argz_create_sep : func :=
  mkFunc (a "__argz_create_sep") (a "export") (RClass W) [(P, (a "v0")); (W, (a "v2")); (P, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Call (CResult (a "v10") L) (Global (a "__GI_strlen")) [(Arg P (t "v0"))]);
      (Let (a "v11") L Add [(t "v10"); (Const 1)]);
      (Let (a "v16") W (Cmp Ugt L) [(t "v11"); (Const 1)])] (JBranch (t "v16") (To (a "L12")) (To (a "L13"))));
  (mkBlock (a "L12") [] [(Call (CResult (a "v21") P) (Global (a "malloc")) [(Arg L (t "v11"))]);
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v4")]);
      (RawStorePointer 0 (t "v21") (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk1") A (Renew 0 8 Read 8) [(t "chk0"); (t "v4")]);
      (Let (a "v26") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "v27") L Ptoi [(t "v26")]);
      (Let (a "v28") L Ptoi [(Const 0)]);
      (Let (a "v29") W (Cmp Eq L) [(t "v27"); (t "v28")])] (JBranch (t "v29") (To (a "L22")) (To (a "L24"))));
  (mkBlock (a "L22") [] [] (JRet (Const 12)));
  (mkBlock (a "L24") [] [(Let (a "v33") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")])] (JGoto (To (a "L34"))));
  (mkBlock (a "L34") [(Phi (a "pr.5") P [((a "L24"), (t "v33")); ((a "L39"), (t "pr.6"))]); (Phi (a "pr.4") P [((a "L24"), (t "v0")); ((a "L39"), (t "v72"))]); (Phi (a "pr.1") L [((a "L24"), (t "v11")); ((a "L39"), (t "pr.2"))])] [(Let (a "chk3") A (Check 0 1 Read 1) [(t "pr.4")]);
      (Let (a "v41") W (RawLoad (LdNarrow Sb) 0) [(t "chk3")]);
      (Let (a "v43") W (Cmp Eq W) [(t "v41"); (t "v2")])] (JBranch (t "v43") (To (a "L37")) (To (a "L38"))));
  (mkBlock (a "L37") [] [(Let (a "chk4") A (Renew 0 8 Read 8) [(t "chk0"); (t "v4")]);
      (Let (a "v49") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "v50") L Ptoi [(t "pr.5")]);
      (Let (a "v51") L Ptoi [(t "v49")]);
      (Let (a "v52") W (Cmp Ugt L) [(t "v50"); (t "v51")])] (JBranch (t "v52") (To (a "L53")) (To (a "L54"))));
  (mkBlock (a "L53") [] [(Flight (a "v58") Add [(FAddress (t "pr.5")); (FValue (Const 18446744073709551615))] (LowerOf (t "pr.5")));
      (Let (a "chk5") A (Check 0 1 Read 1) [(t "v58")]);
      (Let (a "v59") W (RawLoad (LdNarrow Sb) 0) [(t "chk5")]);
      (Let (a "v60") W (Cmp Ne W) [(t "v59"); (Const 0)])] (JGoto (To (a "L54"))));
  (mkBlock (a "L54") [(Phi (a "v62") W [((a "L37"), (Const 0)); ((a "L53"), (t "v60"))])] [] (JBranch (t "v62") (To (a "L44")) (To (a "L45"))));
  (mkBlock (a "L44") [] [(Flight (a "v64") Add [(FAddress (t "pr.5")); (FValue (Const 1))] (LowerOf (t "pr.5")));
      (Let (a "chk6") A (Check 0 1 Write 1) [(t "pr.5")]);
      (RawStore Wb 0 (Const 0) (t "chk6"))] (JGoto (To (a "L39"))));
  (mkBlock (a "L45") [] [(Let (a "v66") L Sub [(t "pr.1"); (Const 1)])] (JGoto (To (a "L39"))));
  (mkBlock (a "L38") [] [(Flight (a "v68") Add [(FAddress (t "pr.5")); (FValue (Const 1))] (LowerOf (t "pr.5")));
      (Let (a "v70") W (RawLoad (LdNarrow Sb) 0) [(t "chk3")]);
      (Let (a "chk8") A (Check 0 1 Write 1) [(t "pr.5")]);
      (RawStore Wb 0 (t "v70") (t "chk8"))] (JGoto (To (a "L39"))));
  (mkBlock (a "L39") [(Phi (a "pr.6") P [((a "L38"), (t "v68")); ((a "L44"), (t "v64")); ((a "L45"), (t "pr.5"))]); (Phi (a "pr.2") L [((a "L38"), (t "pr.1")); ((a "L44"), (t "pr.1")); ((a "L45"), (t "v66"))])] [(Flight (a "v72") Add [(FAddress (t "pr.4")); (FValue (Const 1))] (LowerOf (t "pr.4")));
      (Let (a "v73") W (RawLoad (LdNarrow Sb) 0) [(t "chk3")]);
      (Let (a "v74") W (Cmp Ne W) [(t "v73"); (Const 0)])] (JBranch (t "v74") (Poll (a "L34")) (To (a "L36"))));
  (mkBlock (a "L36") [] [(Let (a "v79") W (Cmp Eq L) [(t "pr.2"); (Const 0)])] (JBranch (t "v79") (To (a "L75")) (To (a "L77"))));
  (mkBlock (a "L75") [] [(Let (a "chk10") A (Renew 0 8 Read 8) [(t "chk0"); (t "v4")]);
      (Let (a "v81") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "v81"))]);
      (Let (a "chk11") A (Renew 0 8 Write 8) [(t "chk0"); (t "v4")]);
      (RawStorePointer 0 (Const 0) (t "chk11") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk12") A (Check 0 8 Write 1) [(t "v6")]);
      (RawStore Wl 0 (Const 0) (t "chk12"))] (JGoto (To (a "L77"))));
  (mkBlock (a "L77") [] [(Let (a "chk13") A (Check 0 8 Write 1) [(t "v6")]);
      (RawStore Wl 0 (t "pr.2") (t "chk13"))] (JGoto (To (a "L14"))));
  (mkBlock (a "L13") [] [(Let (a "chk14") A (Check 0 8 Write 8) [(t "v4")]);
      (RawStorePointer 0 (Const 0) (t "chk14") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk15") A (Check 0 8 Write 1) [(t "v6")]);
      (RawStore Wl 0 (Const 0) (t "chk15"))] (JGoto (To (a "L14"))));
  (mkBlock (a "L14") [] [] (JRet (Const 0)))].

Definition hello_image_fn___GI___argz_next : func :=
  mkFunc (a "__GI___argz_next") (a "export") (RClass P) [(P, (a "v0")); (L, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v10") L Ptoi [(t "v4")]);
      (Let (a "v11") W (Cmp Ne L) [(t "v10"); (Const 0)])] (JBranch (t "v11") (To (a "L6")) (To (a "L7"))));
  (mkBlock (a "L6") [] [(Flight (a "v18") Add [(FAddress (t "v0")); (FValue (t "v2"))] (LowerOf (t "v0")));
      (Let (a "v20") L Ptoi [(t "v18")]);
      (Let (a "v21") W (Cmp Ult L) [(t "v10"); (t "v20")])] (JBranch (t "v21") (To (a "L12")) (To (a "L14"))));
  (mkBlock (a "L12") [] [(Call (CResult (a "v23") P) (Global (a "__GI_strchr")) [(Arg P (t "v4")); (Arg W (Const 0))]);
      (Flight (a "v24") Add [(FAddress (t "v23")); (FValue (Const 1))] (LowerOf (t "v23")))] (JGoto (To (a "L14"))));
  (mkBlock (a "L14") [(Phi (a "pr.1") P [((a "L12"), (t "v24")); ((a "L6"), (t "v4"))])] [(Let (a "v32") L Ptoi [(t "pr.1")]);
      (Let (a "v34") W (Cmp Uge L) [(t "v32"); (t "v20")])] (JBranch (t "v34") (To (a "L27")) (To (a "L26"))));
  (mkBlock (a "L26") [] [] (JGoto (To (a "L27"))));
  (mkBlock (a "L27") [(Phi (a "v36") P [((a "L26"), (t "pr.1")); ((a "L14"), (Const 0))])] [] (JRet (t "v36")));
  (mkBlock (a "L7") [] [(Let (a "v42") W (Cmp Ugt L) [(t "v2"); (Const 0)])] (JBranch (t "v42") (To (a "L38")) (To (a "L39"))));
  (mkBlock (a "L38") [] [] (JRet (t "v0")));
  (mkBlock (a "L39") [] [] (JRet (Const 0)))].
