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

Definition hello_image_fn___correctly_grouped_prefixmb : func :=
  mkFunc (a "__correctly_grouped_prefixmb") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v12") L Ptoi [(t "v6")]);
      (Let (a "v13") L Ptoi [(Const 0)]);
      (Let (a "v14") W (Cmp Eq L) [(t "v12"); (t "v13")])] (JBranch (t "v14") (To (a "L8")) (To (a "L10"))));
  (mkBlock (a "L8") [] [] (JRet (t "v2")));
  (mkBlock (a "L10") [] [(Call (CResult (a "v19") L) (Global (a "__GI_strlen")) [(Arg P (t "v4"))])] (JGoto (To (a "L20"))));
  (mkBlock (a "L20") [(Phi (a "pr.1") P [((a "L10"), (t "v2")); ((a "L204"), (t "pr.7")); ((a "L221"), (t "v241")); ((a "L222"), (t "pr.7"))])] [(Let (a "v25") L Ptoi [(t "pr.1")]);
      (Let (a "v26") L Ptoi [(t "v0")]);
      (Let (a "v27") L Sub [(t "v25"); (t "v26")]);
      (Let (a "v29") W (Cmp Uge L) [(t "v27"); (t "v19")])] (JBranch (t "v29") (To (a "L21")) (To (a "L22"))));
  (mkBlock (a "L21") [] [(Flight (a "v33") Sub [(FAddress (t "pr.1")); (FValue (t "v19"))] (LowerOf (t "pr.1")))] (JGoto (To (a "L36"))));
  (mkBlock (a "L36") [(Phi (a "pr.7") P [((a "L21"), (t "v33")); ((a "L46"), (t "v54"))])] [(Let (a "v41") L Ptoi [(t "pr.7")]);
      (Let (a "v43") W (Cmp Uge L) [(t "v41"); (t "v26")])] (JBranch (t "v43") (To (a "L37")) (To (a "L38"))));
  (mkBlock (a "L37") [] [(Call (CResult (a "v50") W) (Global (a "__GI_memcmp")) [(Arg P (t "pr.7")); (Arg P (t "v4")); (Arg L (t "v19"))]);
      (Let (a "v51") W (Cmp Eq W) [(t "v50"); (Const 0)])] (JBranch (t "v51") (To (a "L38")) (To (a "L46"))));
  (mkBlock (a "L46") [] [(Flight (a "v54") Sub [(FAddress (t "pr.7")); (FValue (Const 1))] (LowerOf (t "pr.7")))] (JGoto (Poll (a "L36"))));
  (mkBlock (a "L38") [] [(Let (a "v62") W (Cmp Ult L) [(t "v41"); (t "v26")])] (JBranch (t "v62") (To (a "L55")) (To (a "L57"))));
  (mkBlock (a "L55") [] [] (JRet (t "pr.1")));
  (mkBlock (a "L57") [] [(Let (a "v72") L Sub [(t "v25"); (t "v41")]);
      (Let (a "chk0") A (Check 0 1 Read 1) [(t "v6")]);
      (Let (a "v74") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "v76") L (Ext Sw) [(t "v74")]);
      (Let (a "v77") L Add [(t "v76"); (t "v19")]);
      (Let (a "v78") W (Cmp Eq L) [(t "v72"); (t "v77")])] (JBranch (t "v78") (To (a "L65")) (To (a "L66"))));
  (mkBlock (a "L65") [] [] (JBranch (t "v62") (To (a "L80")) (To (a "L91"))));
  (mkBlock (a "L80") [] [] (JRet (t "pr.1")));
  (mkBlock (a "L91") [(Phi (a "pr.9") P [((a "L65"), (t "v6")); ((a "L121"), (t "pr.10")); ((a "L204"), (t "pr.10"))]); (Phi (a "pr.8") P [((a "L65"), (t "pr.7")); ((a "L121"), (t "pr.5")); ((a "L204"), (t "pr.6"))])] [(Flight (a "v95") Add [(FAddress (t "pr.9")); (FValue (Const 1))] (LowerOf (t "pr.9")));
      (Let (a "chk1") A (Check 0 1 Read 1) [(t "v95")]);
      (Let (a "v100") W (RawLoad (LdNarrow Sb) 0) [(t "chk1")]);
      (Let (a "v101") W (Cmp Eq W) [(t "v100"); (Const 0)])] (JBranch (t "v101") (To (a "L96")) (To (a "L98"))));
  (mkBlock (a "L96") [] [(Flight (a "v103") Sub [(FAddress (t "v95")); (FValue (Const 1))] (LowerOf (t "v95")))] (JGoto (To (a "L98"))));
  (mkBlock (a "L98") [(Phi (a "pr.10") P [((a "L96"), (t "v103")); ((a "L91"), (t "v95"))])] [(Flight (a "v105") Sub [(FAddress (t "pr.8")); (FValue (Const 1))] (LowerOf (t "pr.8")));
      (Let (a "chk2") A (Check 0 1 Read 1) [(t "pr.10")]);
      (Let (a "v110") W (RawLoad (LdNarrow Sb) 0) [(t "chk2")]);
      (Let (a "v111") W (Cmp Eq W) [(t "v110"); (Const 127)])] (JBranch (t "v111") (To (a "L113")) (To (a "L112"))));
  (mkBlock (a "L112") [] [(Let (a "v115") W (RawLoad (LdNarrow Sb) 0) [(t "chk2")]);
      (Let (a "v116") W (Cmp Slt W) [(t "v115"); (Const 0)])] (JGoto (To (a "L113"))));
  (mkBlock (a "L113") [(Phi (a "v118") W [((a "L98"), (Const 1)); ((a "L112"), (t "v116"))])] [] (JBranch (t "v118") (To (a "L119")) (To (a "L150"))));
  (mkBlock (a "L119") [(Phi (a "pr.5") P [((a "L129"), (t "v137")); ((a "L113"), (t "v105"))])] [(Let (a "v124") L Ptoi [(t "pr.5")]);
      (Let (a "v126") W (Cmp Uge L) [(t "v124"); (t "v26")])] (JBranch (t "v126") (To (a "L120")) (To (a "L121"))));
  (mkBlock (a "L120") [] [(Call (CResult (a "v133") W) (Global (a "__GI_memcmp")) [(Arg P (t "pr.5")); (Arg P (t "v4")); (Arg L (t "v19"))]);
      (Let (a "v134") W (Cmp Eq W) [(t "v133"); (Const 0)])] (JBranch (t "v134") (To (a "L121")) (To (a "L129"))));
  (mkBlock (a "L129") [] [(Flight (a "v137") Sub [(FAddress (t "pr.5")); (FValue (Const 1))] (LowerOf (t "pr.5")))] (JGoto (Poll (a "L119"))));
  (mkBlock (a "L121") [] [(Let (a "v145") W (Cmp Ult L) [(t "v124"); (t "v26")])] (JBranch (t "v145") (To (a "L138")) (Poll (a "L91"))));
  (mkBlock (a "L138") [] [] (JRet (t "pr.1")));
  (mkBlock (a "L150") [(Phi (a "pr.6") P [((a "L160"), (t "v168")); ((a "L113"), (t "v105"))])] [(Let (a "v155") L Ptoi [(t "pr.6")]);
      (Let (a "v157") W (Cmp Uge L) [(t "v155"); (t "v26")])] (JBranch (t "v157") (To (a "L151")) (To (a "L152"))));
  (mkBlock (a "L151") [] [(Call (CResult (a "v164") W) (Global (a "__GI_memcmp")) [(Arg P (t "pr.6")); (Arg P (t "v4")); (Arg L (t "v19"))]);
      (Let (a "v165") W (Cmp Eq W) [(t "v164"); (Const 0)])] (JBranch (t "v165") (To (a "L152")) (To (a "L160"))));
  (mkBlock (a "L160") [] [(Flight (a "v168") Sub [(FAddress (t "pr.6")); (FValue (Const 1))] (LowerOf (t "pr.6")))] (JGoto (Poll (a "L150"))));
  (mkBlock (a "L152") [] [(Let (a "v176") W (Cmp Ult L) [(t "v155"); (t "v26")])] (JBranch (t "v176") (To (a "L177")) (To (a "L178"))));
  (mkBlock (a "L177") [] [(Let (a "v181") L Ptoi [(t "v105")]);
      (Let (a "v183") L Sub [(t "v181"); (t "v155")]);
      (Let (a "chk4") A (Renew 0 1 Read 1) [(t "chk2"); (t "pr.10")]);
      (Let (a "v185") W (RawLoad (LdNarrow Sb) 0) [(t "chk4")]);
      (Let (a "v187") L (Ext Sw) [(t "v185")]);
      (Let (a "v188") L Add [(t "v187"); (t "v19")]);
      (Let (a "v189") L Sub [(t "v188"); (Const 1)]);
      (Let (a "v190") W (Cmp Ule L) [(t "v183"); (t "v189")])] (JGoto (To (a "L178"))));
  (mkBlock (a "L178") [(Phi (a "v192") W [((a "L152"), (Const 0)); ((a "L177"), (t "v190"))])] [] (JBranch (t "v192") (To (a "L169")) (To (a "L171"))));
  (mkBlock (a "L169") [] [] (JRet (t "pr.1")));
  (mkBlock (a "L171") [] [] (JBranch (t "v176") (To (a "L204")) (To (a "L203"))));
  (mkBlock (a "L203") [] [(Let (a "v207") L Ptoi [(t "v105")]);
      (Let (a "v209") L Sub [(t "v207"); (t "v155")]);
      (Let (a "chk5") A (Renew 0 1 Read 1) [(t "chk2"); (t "pr.10")]);
      (Let (a "v211") W (RawLoad (LdNarrow Sb) 0) [(t "chk5")]);
      (Let (a "v213") L (Ext Sw) [(t "v211")]);
      (Let (a "v214") L Add [(t "v213"); (t "v19")]);
      (Let (a "v215") L Sub [(t "v214"); (Const 1)]);
      (Let (a "v216") W (Cmp Ne L) [(t "v209"); (t "v215")])] (JGoto (To (a "L204"))));
  (mkBlock (a "L204") [(Phi (a "v218") W [((a "L171"), (Const 1)); ((a "L203"), (t "v216"))])] [] (JBranch (t "v218") (Poll (a "L20")) (Poll (a "L91"))));
  (mkBlock (a "L66") [] [(Let (a "v230") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "v232") L (Ext Sw) [(t "v230")]);
      (Let (a "v233") L Add [(t "v232"); (t "v19")]);
      (Let (a "v234") W (Cmp Ugt L) [(t "v72"); (t "v233")])] (JBranch (t "v234") (To (a "L221")) (To (a "L222"))));
  (mkBlock (a "L221") [] [(Let (a "v237") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "v238") L (Ext Sw) [(t "v237")]);
      (Flight (a "v239") Add [(FAddress (t "pr.7")); (FValue (t "v238"))] (LowerOf (t "pr.7")));
      (Flight (a "v241") Add [(FAddress (t "v239")); (FValue (t "v19"))] (LowerOf (t "v239")))] (JGoto (Poll (a "L20"))));
  (mkBlock (a "L222") [] [] (JBranch (t "v62") (To (a "L242")) (Poll (a "L20"))));
  (mkBlock (a "L242") [] [] (JRet (t "pr.1")));
  (mkBlock (a "L22") [] [(Let (a "v264") W (Cmp Ugt L) [(t "v26"); (t "v25")])] (JBranch (t "v264") (To (a "L259")) (To (a "L258"))));
  (mkBlock (a "L258") [] [] (JGoto (To (a "L259"))));
  (mkBlock (a "L259") [(Phi (a "v267") P [((a "L258"), (t "pr.1")); ((a "L22"), (t "v0"))])] [] (JRet (t "v267")))].
