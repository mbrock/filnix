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

Definition hello_image_fn_xpalloc : func :=
  mkFunc (a "xpalloc") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (L, (a "v4")); (L, (a "v6")); (L, (a "v8"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 1) [(t "v2")]);
      (Let (a "v12") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v19") L Sar [(t "v12"); (Const 1)]);
      (Let (a "v20") L Sar [(t "v12"); (Const 63)]);
      (Let (a "v21") L Sar [(t "v19"); (Const 63)]);
      (Let (a "v22") L Add [(t "v12"); (t "v19")]);
      (Let (a "v23") W (Cmp Ult L) [(t "v22"); (t "v12")]);
      (Let (a "v24") L (Ext Uw) [(t "v23")]);
      (Let (a "v25") L Add [(t "v20"); (t "v21")]);
      (Let (a "v26") L Add [(t "v25"); (t "v24")]);
      (Let (a "v27") L Sar [(t "v22"); (Const 63)]);
      (Let (a "v29") W (Cmp Ne L) [(t "v26"); (t "v27")])] (JBranch (t "v29") (To (a "L16")) (To (a "L15"))));
  (mkBlock (a "L15") [] [] (JGoto (To (a "L16"))));
  (mkBlock (a "L16") [(Phi (a "pr.2") L [((a "L15"), (t "v22")); ((a "start"), (Const 9223372036854775807))])] [(Let (a "v35") W (Cmp Sge L) [(t "v6"); (Const 0)])] (JBranch (t "v35") (To (a "L36")) (To (a "L37"))));
  (mkBlock (a "L36") [] [(Let (a "v40") W (Cmp Slt L) [(t "v6"); (t "pr.2")])] (JGoto (To (a "L37"))));
  (mkBlock (a "L37") [(Phi (a "v42") W [((a "L16"), (Const 0)); ((a "L36"), (t "v40"))])] [] (JBranch (t "v42") (To (a "L33")) (To (a "L32"))));
  (mkBlock (a "L32") [] [] (JGoto (To (a "L33"))));
  (mkBlock (a "L33") [(Phi (a "pr.3") L [((a "L32"), (t "pr.2")); ((a "L37"), (t "v6"))])] [(Let (a "v51") L Sar [(t "pr.3"); (Const 63)]);
      (Let (a "v52") L Sar [(t "v8"); (Const 63)]);
      (Let (a "v53") L Mul [(t "pr.3"); (t "v8")]);
      (Let (a "v54") L And [(t "pr.3"); (Const 4294967295)]);
      (Let (a "v55") L Shr [(t "pr.3"); (Const 32)]);
      (Let (a "v56") L And [(t "v8"); (Const 4294967295)]);
      (Let (a "v57") L Shr [(t "v8"); (Const 32)]);
      (Let (a "v58") L Mul [(t "v54"); (t "v56")]);
      (Let (a "v59") L Mul [(t "v55"); (t "v56")]);
      (Let (a "v60") L Mul [(t "v54"); (t "v57")]);
      (Let (a "v61") L Mul [(t "v55"); (t "v57")]);
      (Let (a "v62") L Shr [(t "v58"); (Const 32)]);
      (Let (a "v63") L And [(t "v59"); (Const 4294967295)]);
      (Let (a "v64") L And [(t "v60"); (Const 4294967295)]);
      (Let (a "v65") L Add [(t "v62"); (t "v63")]);
      (Let (a "v66") L Add [(t "v65"); (t "v64")]);
      (Let (a "v67") L Shr [(t "v66"); (Const 32)]);
      (Let (a "v68") L Shr [(t "v59"); (Const 32)]);
      (Let (a "v69") L Shr [(t "v60"); (Const 32)]);
      (Let (a "v70") L Add [(t "v61"); (t "v68")]);
      (Let (a "v71") L Add [(t "v70"); (t "v69")]);
      (Let (a "v72") L Add [(t "v71"); (t "v67")]);
      (Let (a "v73") L And [(t "v51"); (t "v8")]);
      (Let (a "v74") L And [(t "v52"); (t "pr.3")]);
      (Let (a "v75") L Sub [(t "v72"); (t "v73")]);
      (Let (a "v76") L Sub [(t "v75"); (t "v74")]);
      (Let (a "v77") L Sar [(t "v53"); (Const 63)]);
      (Let (a "v79") W (Cmp Ne L) [(t "v76"); (t "v77")])] (JBranch (t "v79") (To (a "L48")) (To (a "L47"))));
  (mkBlock (a "L47") [] [(Let (a "v90") W (Cmp Slt L) [(t "v53"); (Const 128)])] (JBranch (t "v90") (To (a "L88")) (To (a "L87"))));
  (mkBlock (a "L87") [] [] (JGoto (To (a "L88"))));
  (mkBlock (a "L88") [(Phi (a "v91") W [((a "L87"), (Const 0)); ((a "L47"), (Const 128))])] [(Let (a "v92") L (Ext Sw) [(t "v91")])] (JGoto (To (a "L48"))));
  (mkBlock (a "L48") [(Phi (a "v93") L [((a "L88"), (t "v92")); ((a "L33"), (Const 9223372036854775807))])] [(Let (a "v98") W (Cmp Ne L) [(t "v93"); (Const 0)])] (JBranch (t "v98") (To (a "L94")) (To (a "L96"))));
  (mkBlock (a "L94") [] [(Let (a "v101") L Div [(t "v93"); (t "v8")]);
      (Let (a "v105") L Rem [(t "v93"); (t "v8")]);
      (Let (a "v106") L Sub [(t "v93"); (t "v105")])] (JGoto (To (a "L96"))));
  (mkBlock (a "L96") [(Phi (a "pr.7") L [((a "L94"), (t "v106")); ((a "L48"), (t "v53"))]); (Phi (a "pr.4") L [((a "L94"), (t "v101")); ((a "L48"), (t "pr.3"))])] [(Let (a "v111") L Ptoi [(t "v0")]);
      (Let (a "v113") W (Cmp Eq L) [(t "v111"); (Const 0)])] (JBranch (t "v113") (To (a "L107")) (To (a "L109"))));
  (mkBlock (a "L107") [] [(Let (a "chk1") A (Renew 0 8 Write 1) [(t "chk0"); (t "v2")]);
      (RawStore Wl 0 (Const 0) (t "chk1"))] (JGoto (To (a "L109"))));
  (mkBlock (a "L109") [] [(Let (a "v120") L Sub [(t "pr.4"); (t "v12")]);
      (Let (a "v122") W (Cmp Slt L) [(t "v120"); (t "v4")])] (JBranch (t "v122") (To (a "L123")) (To (a "L124"))));
  (mkBlock (a "L123") [] [(Let (a "v128") L Sar [(t "v4"); (Const 63)]);
      (Let (a "v129") L Add [(t "v12"); (t "v4")]);
      (Let (a "v130") W (Cmp Ult L) [(t "v129"); (t "v12")]);
      (Let (a "v131") L (Ext Uw) [(t "v130")]);
      (Let (a "v132") L Add [(t "v20"); (t "v128")]);
      (Let (a "v133") L Add [(t "v132"); (t "v131")]);
      (Let (a "v134") L Sar [(t "v129"); (Const 63)]);
      (Let (a "v136") W (Cmp Ne L) [(t "v133"); (t "v134")])] (JBranch (t "v136") (To (a "L139")) (To (a "L138"))));
  (mkBlock (a "L138") [] [] (JBranch (t "v35") (To (a "L142")) (To (a "L139"))));
  (mkBlock (a "L142") [] [(Let (a "v146") W (Cmp Slt L) [(t "v6"); (t "v129")])] (JGoto (To (a "L139"))));
  (mkBlock (a "L139") [(Phi (a "v150") W [((a "L123"), (Const 1)); ((a "L138"), (Const 0)); ((a "L142"), (t "v146"))])] [] (JBranch (t "v150") (To (a "L124")) (To (a "L151"))));
  (mkBlock (a "L151") [] [(Let (a "v157") L Mul [(t "v129"); (t "v8")]);
      (Let (a "v158") L And [(t "v129"); (Const 4294967295)]);
      (Let (a "v159") L Shr [(t "v129"); (Const 32)]);
      (Let (a "v162") L Mul [(t "v158"); (t "v56")]);
      (Let (a "v163") L Mul [(t "v159"); (t "v56")]);
      (Let (a "v164") L Mul [(t "v158"); (t "v57")]);
      (Let (a "v165") L Mul [(t "v159"); (t "v57")]);
      (Let (a "v166") L Shr [(t "v162"); (Const 32)]);
      (Let (a "v167") L And [(t "v163"); (Const 4294967295)]);
      (Let (a "v168") L And [(t "v164"); (Const 4294967295)]);
      (Let (a "v169") L Add [(t "v166"); (t "v167")]);
      (Let (a "v170") L Add [(t "v169"); (t "v168")]);
      (Let (a "v171") L Shr [(t "v170"); (Const 32)]);
      (Let (a "v172") L Shr [(t "v163"); (Const 32)]);
      (Let (a "v173") L Shr [(t "v164"); (Const 32)]);
      (Let (a "v174") L Add [(t "v165"); (t "v172")]);
      (Let (a "v175") L Add [(t "v174"); (t "v173")]);
      (Let (a "v176") L Add [(t "v175"); (t "v171")]);
      (Let (a "v177") L And [(t "v134"); (t "v8")]);
      (Let (a "v178") L And [(t "v52"); (t "v129")]);
      (Let (a "v179") L Sub [(t "v176"); (t "v177")]);
      (Let (a "v180") L Sub [(t "v179"); (t "v178")]);
      (Let (a "v181") L Sar [(t "v157"); (Const 63)]);
      (Let (a "v183") W (Cmp Ne L) [(t "v180"); (t "v181")])] (JGoto (To (a "L124"))));
  (mkBlock (a "L124") [(Phi (a "v188") W [((a "L109"), (Const 0)); ((a "L139"), (Const 1)); ((a "L151"), (t "v183"))]); (Phi (a "pr.5") L [((a "L109"), (t "pr.7")); ((a "L139"), (t "pr.7")); ((a "L151"), (t "v157"))]); (Phi (a "pr.1") L [((a "L109"), (t "pr.4")); ((a "L139"), (t "v129")); ((a "L151"), (t "v129"))])] [] (JBranch (t "v188") (To (a "L115")) (To (a "L117"))));
  (mkBlock (a "L115") [] [(Call CVoid (Global (a "xalloc_die")) [])] (JGoto (To (a "L117"))));
  (mkBlock (a "L117") [] [(Call (CResult (a "v191") P) (Global (a "xrealloc")) [(Arg P (t "v0")); (Arg L (t "pr.5"))]);
      (Let (a "chk2") A (Renew 0 8 Write 1) [(t "chk0"); (t "v2")]);
      (RawStore Wl 0 (t "pr.1") (t "chk2"))] (JRet (t "v191")))].
