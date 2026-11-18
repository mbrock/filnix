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

Definition hello_image_fn__nl_load_locale : func :=
  mkFunc (a "_nl_load_locale") (a "export") RVoid [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v6") P (Alloc 8) [(Const 144)]);
      (Flight (a "v11") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Write 8) [(t "v11")]);
      (RawStorePointer 0 (Const 0) (t "chk0") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk1") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v0")]);
      (Let (a "v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Call (CResult (a "v15") W) (Global (a "__GI___open_nocancel")) [(Arg P (t "v13")); (Arg W (Const 524288))]);
      (Let (a "v20") L (Ext Sw) [(t "v15")]);
      (Let (a "v21") W (Cmp Slt L) [(t "v20"); (Const 0)])] (JBranch (t "v21") (To (a "L16")) (To (a "L18"))));
  (mkBlock (a "L16") [] [] JRetVoid);
  (mkBlock (a "L18") [] [(Call (CResult (a "v27") W) (Global (a "__GI___fstat64")) [(Arg W (t "v15")); (Arg P (t "v6"))]);
      (Let (a "v28") W (Cmp Slt W) [(t "v27"); (Const 0)])] (JBranch (t "v28") (To (a "L31")) (To (a "L25"))));
  (mkBlock (a "L31") [(Phi (a "pr.1") W [((a "L18"), (t "v15")); ((a "L82"), (t "v79")); ((a "L153"), (t "pr.2")); ((a "L147"), (t "pr.2"))])] [(Call CVoid (Global (a "__GI___close_nocancel_nostatus")) [(Arg W (t "pr.1"))])] JRetVoid);
  (mkBlock (a "L25") [] [(Flight (a "v37") Add [(FAddress (t "v6")); (FValue (Const 24))] (LowerOf (t "v6")));
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "v37")]);
      (Let (a "v38") W (RawLoad (LdNarrow Uw) 0) [(t "chk2")]);
      (Let (a "v39") W And [(t "v38"); (Const 61440)]);
      (Let (a "v40") W (Cmp Eq W) [(t "v39"); (Const 16384)])] (JBranch (t "v40") (To (a "L34")) (To (a "L36"))));
  (mkBlock (a "L34") [] [(Call CVoid (Global (a "__GI___close_nocancel_nostatus")) [(Arg W (t "v15"))]);
      (Let (a "chk3") A (Renew 0 8 Read 8) [(t "chk1"); (t "v0")]);
      (Let (a "v47") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Call (CResult (a "v48") L) (Global (a "__GI_strlen")) [(Arg P (t "v47"))]);
      (Let (a "v50") L Add [(t "v48"); (Const 5)]);
      (Let (a "v51") P Copy [(Global (a "_nl_category_name_sizes"))]);
      (Let (a "v53") L (Ext Sw) [(t "v2")]);
      (Flight (a "v54") Add [(FAddress (t "v51")); (FValue (t "v53"))] (LowerOf (t "v51")));
      (Let (a "chk4") A (Check 0 1 Read 1) [(t "v54")]);
      (Let (a "v55") W (RawLoad (LdNarrow Ub) 0) [(t "chk4")]);
      (Let (a "v56") L (Ext Uw) [(t "v55")]);
      (Let (a "v57") L Add [(t "v50"); (t "v56")]);
      (Let (a "v58") L Add [(t "v57"); (Const 1)]);
      (Let (a "v59") P (Alloc 16) [(t "v58")]);
      (Let (a "chk5") A (Renew 0 8 Read 8) [(t "chk1"); (t "v0")]);
      (Let (a "v62") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Call (CResult (a "v64") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v59")); (Arg P (t "v62")); (Arg L (t "v48"))]);
      (Let (a "v65") P Copy [(Global (a "glibc_loadlocale#str.243"))]);
      (Call (CResult (a "v66") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v64")); (Arg P (t "v65")); (Arg L (Const 5))]);
      (Let (a "iw_1.v2") P Copy [(Global (a "_nl_category_names"))]);
      (Let (a "iw_1.v3") P Copy [(Global (a "_nl_category_name_idxs"))]);
      (Flight (a "iw_1.v6") Add [(FAddress (t "iw_1.v3")); (FValue (t "v53"))] (LowerOf (t "iw_1.v3")));
      (Let (a "chk6") A (Check 0 1 Read 1) [(t "iw_1.v6")]);
      (Let (a "iw_1.v7") W (RawLoad (LdNarrow Ub) 0) [(t "chk6")]);
      (Let (a "iw_1.v8") L (Ext Uw) [(t "iw_1.v7")]);
      (Flight (a "iw_1.v9") Add [(FAddress (t "iw_1.v2")); (FValue (t "iw_1.v8"))] (LowerOf (t "iw_1.v2")));
      (Let (a "v69") P Copy [(Global (a "_nl_category_name_sizes"))]);
      (Flight (a "v72") Add [(FAddress (t "v69")); (FValue (t "v53"))] (LowerOf (t "v69")));
      (Let (a "chk7") A (Check 0 1 Read 1) [(t "v72")]);
      (Let (a "v73") W (RawLoad (LdNarrow Ub) 0) [(t "chk7")]);
      (Let (a "v74") W Add [(t "v73"); (Const 1)]);
      (Let (a "v75") L (Ext Sw) [(t "v74")]);
      (Call (CResult (a "v76") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v66")); (Arg P (t "iw_1.v9")); (Arg L (t "v75"))]);
      (Call (CResult (a "v79") W) (Global (a "__GI___open_nocancel")) [(Arg P (t "v59")); (Arg W (Const 524288))]);
      (Let (a "v84") L (Ext Sw) [(t "v79")]);
      (Let (a "v85") W (Cmp Slt L) [(t "v84"); (Const 0)])] (JBranch (t "v85") (To (a "L80")) (To (a "L82"))));
  (mkBlock (a "L80") [] [] JRetVoid);
  (mkBlock (a "L82") [] [(Call (CResult (a "v91") W) (Global (a "__GI___fstat64")) [(Arg W (t "v79")); (Arg P (t "v6"))]);
      (Let (a "v92") W (Cmp Slt W) [(t "v91"); (Const 0)])] (JBranch (t "v92") (Poll (a "L31")) (To (a "L36"))));
  (mkBlock (a "L36") [(Phi (a "pr.2") W [((a "L82"), (t "v79")); ((a "L25"), (t "v15"))])] [(Let (a "v96") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk8") A (Check 0 4 Read 1) [(t "v96")]);
      (Let (a "v97") W (RawLoad (LdNarrow Sw) 0) [(t "chk8")]);
      (Flight (a "v98") Add [(FAddress (t "v6")); (FValue (Const 48))] (LowerOf (t "v6")));
      (Let (a "chk9") A (HalfCheck Upper 0 8 Read 1) [(t "chk2"); (t "v98")]);
      (Let (a "v99") L (RawLoad LdL 0) [(t "chk9")]);
      (Call (CResult (a "v102") P) (Global (a "__GI___mmap")) [(Arg P (Const 0)); (Arg L (t "v99")); (Arg W (Const 1)); (Arg W (Const 2)); (Arg W (t "pr.2")); (Arg L (Const 0))]);
      (Flight (a "v109") Copy [(FValue (Const 18446744073709551615))] LowerNone);
      (Let (a "v110") L Ptoi [(t "v102")]);
      (Let (a "v111") L Ptoi [(t "v109")]);
      (Let (a "v112") W (Cmp Eq L) [(t "v110"); (t "v111")])] (JBranch (t "v112") (To (a "L103")) (To (a "L105"))));
  (mkBlock (a "L103") [] [(Let (a "v118") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk10") A (Check 0 4 Read 1) [(t "v118")]);
      (Let (a "v119") W (RawLoad (LdNarrow Sw) 0) [(t "chk10")]);
      (Let (a "v120") L (Ext Sw) [(t "v119")]);
      (Let (a "v121") W (Cmp Eq L) [(t "v120"); (Const 38)])] (JBranch (t "v121") (To (a "L115")) (To (a "L105"))));
  (mkBlock (a "L115") [] [(Flight (a "v122") Add [(FAddress (t "v6")); (FValue (Const 48))] (LowerOf (t "v6")));
      (Let (a "chk11") A (Renew 0 8 Read 1) [(t "chk9"); (t "v122")]);
      (Let (a "v123") L (RawLoad LdL 0) [(t "chk11")]);
      (Call (CResult (a "v124") P) (Global (a "malloc")) [(Arg L (t "v123"))]);
      (Let (a "v129") L Ptoi [(t "v124")]);
      (Let (a "v130") L Ptoi [(Const 0)]);
      (Let (a "v131") W (Cmp Ne L) [(t "v129"); (t "v130")])] (JBranch (t "v131") (To (a "L125")) (To (a "L105"))));
  (mkBlock (a "L125") [] [(Flight (a "v133") Add [(FAddress (t "v6")); (FValue (Const 48))] (LowerOf (t "v6")));
      (Let (a "chk12") A (Renew 0 8 Read 1) [(t "chk9"); (t "v133")]);
      (Let (a "v134") L (RawLoad LdL 0) [(t "chk12")])] (JGoto (To (a "L138"))));
  (mkBlock (a "L138") [(Phi (a "pr.8") P [((a "L125"), (t "v124")); ((a "L149"), (t "v162"))]); (Phi (a "pr.7") L [((a "L125"), (t "v134")); ((a "L149"), (t "v165"))])] [(Let (a "v142") W (Cmp Sgt L) [(t "pr.7"); (Const 0)])] (JBranch (t "v142") (To (a "L139")) (To (a "L140"))));
  (mkBlock (a "L139") [] [(Call (CResult (a "v146") L) (Global (a "__GI___read_nocancel")) [(Arg W (t "pr.2")); (Arg P (t "pr.8")); (Arg L (t "pr.7"))]);
      (Let (a "v151") W (Cmp Sle L) [(t "v146"); (Const 0)])] (JBranch (t "v151") (To (a "L147")) (To (a "L149"))));
  (mkBlock (a "L147") [] [(Call CVoid (Global (a "free")) [(Arg P (t "v124"))]);
      (Let (a "v157") W (Cmp Eq L) [(t "v146"); (Const 0)])] (JBranch (t "v157") (To (a "L153")) (Poll (a "L31"))));
  (mkBlock (a "L153") [] [(Let (a "v158") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk13") A (Check 0 4 Write 1) [(t "v158")]);
      (RawStore Ww 0 (Const 22) (t "chk13"))] (JGoto (Poll (a "L31"))));
  (mkBlock (a "L149") [] [(Flight (a "v162") Add [(FAddress (t "pr.8")); (FValue (t "v146"))] (LowerOf (t "pr.8")));
      (Let (a "v165") L Sub [(t "pr.7"); (t "v146")])] (JGoto (Poll (a "L138"))));
  (mkBlock (a "L140") [] [(Let (a "v166") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk14") A (Check 0 4 Write 1) [(t "v166")]);
      (RawStore Ww 0 (t "v97") (t "chk14"))] (JGoto (To (a "L105"))));
  (mkBlock (a "L105") [(Phi (a "pr.5") W [((a "L140"), (Const 0)); ((a "L115"), (Const 0)); ((a "L103"), (Const 1)); ((a "L36"), (Const 1))]); (Phi (a "pr.3") P [((a "L140"), (t "v124")); ((a "L115"), (t "v124")); ((a "L103"), (Const 0)); ((a "L36"), (t "v102"))])] [(Call CVoid (Global (a "__GI___close_nocancel_nostatus")) [(Arg W (t "pr.2"))]);
      (Let (a "v173") L Ptoi [(t "pr.3")]);
      (Let (a "v174") L Ptoi [(Const 0)]);
      (Let (a "v175") W (Cmp Eq L) [(t "v173"); (t "v174")])] (JBranch (t "v175") (To (a "L169")) (To (a "L171"))));
  (mkBlock (a "L169") [] [] JRetVoid);
  (mkBlock (a "L171") [] [(Flight (a "v181") Add [(FAddress (t "v6")); (FValue (Const 48))] (LowerOf (t "v6")));
      (Let (a "chk15") A (Renew 0 8 Read 1) [(t "chk9"); (t "v181")]);
      (Let (a "v182") L (RawLoad LdL 0) [(t "chk15")]);
      (Call (CResult (a "v183") P) (Global (a "_nl_intern_locale_data")) [(Arg W (t "v2")); (Arg P (t "pr.3")); (Arg L (t "v182"))]);
      (Let (a "v188") L Ptoi [(t "v183")]);
      (Let (a "v190") W (Cmp Eq L) [(t "v188"); (t "v174")])] (JBranch (t "v190") (To (a "L184")) (To (a "L186"))));
  (mkBlock (a "L184") [] [] (JBranch (t "pr.5") (To (a "L193")) (To (a "L195"))));
  (mkBlock (a "L193") [] [(Flight (a "v199") Add [(FAddress (t "v6")); (FValue (Const 48))] (LowerOf (t "v6")));
      (Let (a "chk16") A (Renew 0 8 Read 1) [(t "chk9"); (t "v199")]);
      (Let (a "v200") L (RawLoad LdL 0) [(t "chk16")]);
      (Call (CResult (a "v201") W) (Global (a "__GI___munmap")) [(Arg P (t "pr.3")); (Arg L (t "v200"))])] (JGoto (To (a "L195"))));
  (mkBlock (a "L195") [] [] JRetVoid);
  (mkBlock (a "L186") [] [(Let (a "chk17") A (Check 0 8 Write 8) [(t "v183")]);
      (RawStorePointer 0 (Const 0) (t "chk17") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v205") Add [(FAddress (t "v183")); (FValue (Const 24))] (LowerOf (t "v183")));
      (Let (a "chk18") A (HalfCheck Upper 0 4 Write 1) [(t "chk17"); (t "v205")]);
      (RawStore Ww 0 (t "pr.5") (t "chk18"));
      (Flight (a "v208") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk19") A (Renew 0 8 Write 8) [(t "chk0"); (t "v208")]);
      (RawStorePointer 0 (t "v183") (t "chk19") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v211") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk20") A (HalfCheck Lower 0 4 Write 1) [(t "chk0"); (t "v211")]);
      (RawStore Ww 0 (Const 1) (t "chk20"))] JRetVoid)].
