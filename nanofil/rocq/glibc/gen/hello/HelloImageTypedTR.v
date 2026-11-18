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

Definition hello_image_fn_glibc_dcigettext'23transcmp : func :=
  mkFunc (a "glibc_dcigettext#transcmp") (a "local") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Flight (a "v13") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v13")]);
      (Let (a "v14") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v15") L Ptoi [(t "v14")]);
      (Let (a "v16") L Ptoi [(Const 0)]);
      (Let (a "v17") W (Cmp Ne L) [(t "v15"); (t "v16")])] (JBranch (t "v17") (To (a "L9")) (To (a "L10"))));
  (mkBlock (a "L9") [] [(Flight (a "v19") Add [(FAddress (t "v0")); (FValue (Const 56))] (LowerOf (t "v0")))] (JGoto (To (a "L11"))));
  (mkBlock (a "L10") [] [(Flight (a "v21") Add [(FAddress (t "v0")); (FValue (Const 56))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v21")]);
      (Let (a "v22") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")])] (JGoto (To (a "L11"))));
  (mkBlock (a "L11") [(Phi (a "v23") P [((a "L9"), (t "v19")); ((a "L10"), (t "v22"))])] [(Flight (a "v28") Add [(FAddress (t "v2")); (FValue (Const 32))] (LowerOf (t "v2")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v28")]);
      (Let (a "v29") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v30") L Ptoi [(t "v29")]);
      (Let (a "v32") W (Cmp Ne L) [(t "v30"); (t "v16")])] (JBranch (t "v32") (To (a "L24")) (To (a "L25"))));
  (mkBlock (a "L24") [] [(Flight (a "v34") Add [(FAddress (t "v2")); (FValue (Const 56))] (LowerOf (t "v2")))] (JGoto (To (a "L26"))));
  (mkBlock (a "L25") [] [(Flight (a "v36") Add [(FAddress (t "v2")); (FValue (Const 56))] (LowerOf (t "v2")));
      (Let (a "chk3") A (HalfCheck Upper 0 8 Read 8) [(t "chk2"); (t "v36")]);
      (Let (a "v37") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")])] (JGoto (To (a "L26"))));
  (mkBlock (a "L26") [(Phi (a "v38") P [((a "L24"), (t "v34")); ((a "L25"), (t "v37"))])] [(Call (CResult (a "v39") W) (Global (a "__GI_strcmp")) [(Arg P (t "v23")); (Arg P (t "v38"))]);
      (Let (a "v44") W (Cmp Eq W) [(t "v39"); (Const 0)])] (JBranch (t "v44") (To (a "L40")) (To (a "L42"))));
  (mkBlock (a "L40") [] [(Let (a "chk4") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v0")]);
      (Let (a "v46") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "chk5") A (HalfCheck Lower 0 8 Read 8) [(t "chk2"); (t "v2")]);
      (Let (a "v48") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Call (CResult (a "v49") W) (Global (a "__GI_strcmp")) [(Arg P (t "v46")); (Arg P (t "v48"))]);
      (Let (a "v54") W (Cmp Eq W) [(t "v49"); (Const 0)])] (JBranch (t "v54") (To (a "L50")) (To (a "L42"))));
  (mkBlock (a "L50") [] [(Flight (a "v56") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk6") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v56")]);
      (Let (a "v57") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v59") Add [(FAddress (t "v2")); (FValue (Const 16))] (LowerOf (t "v2")));
      (Let (a "chk7") A (HalfCheck Lower 0 8 Read 8) [(t "chk2"); (t "v59")]);
      (Let (a "v60") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Call (CResult (a "v61") W) (Global (a "__GI_strcmp")) [(Arg P (t "v57")); (Arg P (t "v60"))]);
      (Let (a "v66") W (Cmp Eq W) [(t "v61"); (Const 0)])] (JBranch (t "v66") (To (a "L62")) (To (a "L42"))));
  (mkBlock (a "L62") [] [(Flight (a "v68") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk8") A (HalfCheck Lower 0 4 Read 1) [(t "chk0"); (t "v68")]);
      (Let (a "v69") W (RawLoad (LdNarrow Sw) 0) [(t "chk8")]);
      (Flight (a "v71") Add [(FAddress (t "v2")); (FValue (Const 8))] (LowerOf (t "v2")));
      (Let (a "chk9") A (HalfCheck Lower 0 4 Read 1) [(t "chk2"); (t "v71")]);
      (Let (a "v72") W (RawLoad (LdNarrow Sw) 0) [(t "chk9")]);
      (Let (a "v73") W Sub [(t "v69"); (t "v72")])] (JGoto (To (a "L42"))));
  (mkBlock (a "L42") [(Phi (a "pr.1") W [((a "L62"), (t "v73")); ((a "L50"), (t "v61")); ((a "L40"), (t "v49")); ((a "L26"), (t "v39"))])] [] (JRet (t "pr.1")))].

Definition hello_image_fn_glibc_tsearch'23trecurse_r : func :=
  mkFunc (a "glibc_tsearch#trecurse_r") (a "local") RVoid [(P, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Flight (a "v12") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v12")]);
      (Let (a "v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v14") L Ptoi [(t "v13")]);
      (Let (a "v15") L Ptoi [(Const 0)]);
      (Let (a "v16") W (Cmp Eq L) [(t "v14"); (t "v15")])] (JBranch (t "v16") (To (a "L17")) (To (a "L18"))));
  (mkBlock (a "L17") [] [(Flight (a "v20") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v20")]);
      (Let (a "v21") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "v22") L Ptoi [(t "v21")]);
      (Let (a "v24") W (Cmp Eq L) [(t "v22"); (t "v15")])] (JGoto (To (a "L18"))));
  (mkBlock (a "L18") [(Phi (a "v26") W [((a "start"), (Const 0)); ((a "L17"), (t "v24"))])] [] (JBranch (t "v26") (To (a "L8")) (To (a "L9"))));
  (mkBlock (a "L8") [] [(Let (a "chk2") F CheckFunction [(t "v2")]);
      (RawCall CVoid (t "chk2") [(Arg P (t "v0")); (Arg W (Const 3)); (Arg P (t "v4"))])] (JGoto (To (a "L10"))));
  (mkBlock (a "L9") [] [(Let (a "chk3") F CheckFunction [(t "v2")]);
      (RawCall CVoid (t "chk3") [(Arg P (t "v0")); (Arg W (Const 0)); (Arg P (t "v4"))]);
      (Flight (a "v37") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk4") A (Renew 0 8 Read 8) [(t "chk0"); (t "v37")]);
      (Let (a "v38") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "v39") L Ptoi [(t "v38")]);
      (Let (a "v41") W (Cmp Ne L) [(t "v39"); (t "v15")])] (JBranch (t "v41") (To (a "L33")) (To (a "L35"))));
  (mkBlock (a "L33") [] [(Flight (a "v43") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v44") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Call CVoid (Global (a "glibc_tsearch#trecurse_r")) [(Arg P (t "v44")); (Arg P (t "v2")); (Arg P (t "v4"))])] (JGoto (To (a "L35"))));
  (mkBlock (a "L35") [] [(Let (a "chk6") F CheckFunction [(t "v2")]);
      (RawCall CVoid (t "chk6") [(Arg P (t "v0")); (Arg W (Const 1)); (Arg P (t "v4"))]);
      (Flight (a "v54") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk7") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v54")]);
      (Let (a "v55") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Let (a "v56") L Ptoi [(t "v55")]);
      (Let (a "v58") W (Cmp Ne L) [(t "v56"); (t "v15")])] (JBranch (t "v58") (To (a "L50")) (To (a "L52"))));
  (mkBlock (a "L50") [] [(Flight (a "v60") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "v61") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Call CVoid (Global (a "glibc_tsearch#trecurse_r")) [(Arg P (t "v61")); (Arg P (t "v2")); (Arg P (t "v4"))])] (JGoto (To (a "L52"))));
  (mkBlock (a "L52") [] [(Let (a "chk9") F CheckFunction [(t "v2")]);
      (RawCall CVoid (t "chk9") [(Arg P (t "v0")); (Arg W (Const 2)); (Arg P (t "v4"))])] (JGoto (To (a "L10"))));
  (mkBlock (a "L10") [] [] JRetVoid)].

Definition hello_image_fn___translated_number_width : func :=
  mkFunc (a "__translated_number_width") (a "export") (RClass W) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v9") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v10") Add [(FAddress (t "v9")); (FValue (Const 32))] (LowerOf (t "v9")));
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v10")]);
      (Let (a "v11") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v16") Add [(FAddress (t "v11")); (FValue (Const 19))] (LowerOf (t "v11")));
      (Let (a "chk2") A (Check 0 1 Read 1) [(t "v16")]);
      (Let (a "v17") W (RawLoad (LdNarrow Ub) 0) [(t "chk2")]);
      (Let (a "v18") W (Cmp Sgt W) [(t "v17"); (Const 0)])] (JBranch (t "v18") (To (a "L12")) (To (a "L33"))));
  (mkBlock (a "L12") [] [(Let (a "v21") L Ptoi [(t "v4")]);
      (Let (a "v22") L Ptoi [(t "v2")]);
      (Let (a "v23") L Sub [(t "v21"); (t "v22")]);
      (Flight (a "v25") Add [(FAddress (t "v11")); (FValue (Const 19))] (LowerOf (t "v11")));
      (Let (a "v26") W (RawLoad (LdNarrow Ub) 0) [(t "chk2")]);
      (Let (a "v27") L (Ext Uw) [(t "v26")]);
      (Let (a "v28") L Mul [(t "v23"); (t "v27")])] (JRet (t "v28")));
  (mkBlock (a "L33") [(Phi (a "pr.2") P [((a "L44"), (t "v69")); ((a "start"), (t "v2"))]); (Phi (a "pr.1") W [((a "L44"), (t "v67")); ((a "start"), (Const 0))])] [(Let (a "v39") L Ptoi [(t "pr.2")]);
      (Let (a "v40") L Ptoi [(t "v4")]);
      (Let (a "v41") W (Cmp Ult L) [(t "v39"); (t "v40")])] (JBranch (t "v41") (To (a "L34")) (To (a "L36"))));
  (mkBlock (a "L34") [] [(Let (a "chk4") A (Check 0 1 Read 1) [(t "pr.2")]);
      (Let (a "v46") W (RawLoad (LdNarrow Sb) 0) [(t "chk4")]);
      (Let (a "v47") W (Cmp Sge W) [(t "v46"); (Const 48)])] (JBranch (t "v47") (To (a "L48")) (To (a "L49"))));
  (mkBlock (a "L48") [] [(Let (a "v51") W (RawLoad (LdNarrow Sb) 0) [(t "chk4")]);
      (Let (a "v52") W (Cmp Sle W) [(t "v51"); (Const 57)])] (JGoto (To (a "L49"))));
  (mkBlock (a "L49") [(Phi (a "v54") W [((a "L34"), (Const 0)); ((a "L48"), (t "v52"))])] [] (JBranch (t "v54") (To (a "L44")) (To (a "L43"))));
  (mkBlock (a "L43") [] [(Let (a "v55") P Copy [(Global (a "glibc_translated_number_width#str.45"))]);
      (Let (a "v56") P Copy [(Global (a "glibc_translated_number_width#str.46"))]);
      (Let (a "v57") P Copy [(Global (a "glibc_translated_number_width#str.47"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v55")); (Arg P (t "v56")); (Arg W (Const 37)); (Arg P (t "v57"))])] (JGoto (To (a "L44"))));
  (mkBlock (a "L44") [] [(Flight (a "v60") Add [(FAddress (t "v11")); (FValue (Const 9))] (LowerOf (t "v11")));
      (Let (a "chk6") A (Renew 0 1 Read 1) [(t "chk4"); (t "pr.2")]);
      (Let (a "v62") W (RawLoad (LdNarrow Sb) 0) [(t "chk6")]);
      (Let (a "v63") W Sub [(t "v62"); (Const 48)]);
      (Let (a "v64") L (Ext Sw) [(t "v63")]);
      (Flight (a "v65") Add [(FAddress (t "v60")); (FValue (t "v64"))] (LowerOf (t "v60")));
      (Let (a "chk7") A (Check 0 1 Read 1) [(t "v65")]);
      (Let (a "v66") W (RawLoad (LdNarrow Ub) 0) [(t "chk7")]);
      (Let (a "v67") W Add [(t "pr.1"); (t "v66")]);
      (Flight (a "v69") Add [(FAddress (t "pr.2")); (FValue (Const 1))] (LowerOf (t "pr.2")))] (JGoto (Poll (a "L33"))));
  (mkBlock (a "L36") [] [] (JRet (t "pr.1")))].
