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

Definition hello_image_fn_glibc_gconv_db'23find_derivation'blocks2 : list block :=
  [(mkBlock (a "iw_3.L204") [(Phi (a "iw_3.pr.8") W [((a "iw_3.iw_1.join"), (t "iw_3.v215")); ((a "iw_3.L147"), (t "iw_3.pr.12"))])] [(Flight (a "iw_3.v240") Add [(FAddress (t "iw_3.v120")); (FValue (Const 48))] (LowerOf (t "iw_3.v120")));
      (Let (a "chk181") A (Renew 0 8 Read 8) [(t "chk176"); (t "iw_3.v240")]);
      (Let (a "iw_3.v241") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk181")])] (JGoto (To (a "iw_3.L129"))));
  (mkBlock (a "iw_3.L128") [] [(Flight (a "iw_3.v243") Add [(FAddress (t "iw_3.pr.6")); (FValue (Const 24))] (LowerOf (t "iw_3.pr.6")));
      (Let (a "iw_3.v244") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk162")]);
      (Flight (a "iw_3.v245") Add [(FAddress (t "iw_3.v244")); (FValue (Const 24))] (LowerOf (t "iw_3.v244")));
      (Let (a "chk183") A (Check 0 8 Read 8) [(t "iw_3.v245")]);
      (Let (a "iw_3.v246") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk183")]);
      (Call CVoid (Global (a "__gconv_get_builtin_trans")) [(Arg P (t "iw_3.v246")); (Arg P (t "iw_3.v120"))])] (JGoto (To (a "iw_3.L129"))));
  (mkBlock (a "iw_3.L129") [(Phi (a "iw_3.pr.7") W [((a "iw_3.L128"), (t "iw_3.pr.12")); ((a "iw_3.L204"), (t "iw_3.pr.8"))])] [(Flight (a "iw_3.v252") Add [(FAddress (t "iw_3.pr.6")); (FValue (Const 32))] (LowerOf (t "iw_3.pr.6")));
      (Let (a "chk184") A (HalfCheck Upper 0 8 Read 8) [(t "chk162"); (t "iw_3.v252")]);
      (Let (a "iw_3.v253") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk184")])] (JGoto (Poll (a "iw_3.L46"))));
  (mkBlock (a "iw_3.L48") [(Phi (a "iw_3.pr.20") W [((a "iw_3.L216"), (Const 1)); ((a "iw_3.L46"), (Const 0)); ((a "iw_3.L52"), (Const 1)); ((a "iw_3.L81"), (Const 1)); ((a "iw_3.L127"), (Const 1))]); (Phi (a "iw_3.pr.18") P [((a "iw_3.L216"), (t "iw_3.pr.19")); ((a "iw_3.L46"), (t "iw_3.pr.17")); ((a "iw_3.L52"), (t "iw_3.pr.17")); ((a "iw_3.L81"), (t "iw_3.v96")); ((a "iw_3.L127"), (t "iw_3.pr.19"))]); (Phi (a "iw_3.pr.15") P [((a "iw_3.L216"), (t "iw_3.pr.16")); ((a "iw_3.L46"), (t "iw_3.pr.14")); ((a "iw_3.L52"), (t "iw_3.v63")); ((a "iw_3.L81"), (t "iw_3.pr.16")); ((a "iw_3.L127"), (t "iw_3.pr.16"))]); (Phi (a "iw_3.pr.13") W [((a "iw_3.L216"), (t "iw_3.v215")); ((a "iw_3.L46"), (t "iw_3.pr.12")); ((a "iw_3.L52"), (t "iw_3.pr.12")); ((a "iw_3.L81"), (t "iw_3.pr.12")); ((a "iw_3.L127"), (t "iw_3.pr.12"))]); (Phi (a "iw_3.pr.4") L [((a "iw_3.L216"), (t "iw_3.v234")); ((a "iw_3.L46"), (t "iw_3.v50")); ((a "iw_3.L52"), (t "iw_3.v50")); ((a "iw_3.L81"), (t "iw_3.v50")); ((a "iw_3.L127"), (t "iw_3.v50"))])] [] (JBranch (t "iw_3.pr.20") (To (a "iw_3.L260")) (To (a "iw_3.L255"))));
  (mkBlock (a "iw_3.L260") [(Phi (a "iw_3.pr.2") L [((a "iw_3.L261"), (t "iw_3.v264")); ((a "iw_3.L48"), (t "iw_3.pr.4"))])] [(Let (a "iw_3.v264") L Add [(t "iw_3.pr.2"); (Const 1)]);
      (Let (a "chk185") A (Renew 0 8 Read 1) [(t "chk150"); (t "v10")]);
      (Let (a "iw_3.v266") L (RawLoad LdL 0) [(t "chk185")]);
      (Let (a "iw_3.v267") W (Cmp Ult L) [(t "iw_3.v264"); (t "iw_3.v266")])] (JBranch (t "iw_3.v267") (To (a "iw_3.L261")) (To (a "iw_3.L262"))));
  (mkBlock (a "iw_3.L261") [] [(Let (a "iw_3.v270") L Mul [(t "iw_3.v264"); (Const 104)]);
      (Flight (a "iw_3.v271") Add [(FAddress (t "iw_3.v34")); (FValue (t "iw_3.v270"))] (LowerOf (t "iw_3.v34")));
      (Call CVoid (Global (a "__gconv_release_step")) [(Arg P (t "iw_3.v271"))])] (JGoto (Poll (a "iw_3.L260"))));
  (mkBlock (a "iw_3.L262") [] [(Call CVoid (Global (a "free")) [(Arg P (t "iw_3.v34"))]);
      (Call CVoid (Global (a "free")) [(Arg P (t "iw_3.pr.15"))]);
      (Call CVoid (Global (a "free")) [(Arg P (t "iw_3.pr.18"))]);
      (Let (a "chk186") A (Renew 0 8 Write 1) [(t "chk150"); (t "v10")]);
      (RawStore Wl 0 (Const 0) (t "chk186"));
      (Let (a "chk187") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (Const 0) (t "chk187") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "iw_3.v281") W (Cmp Eq W) [(t "iw_3.pr.13"); (Const 0)])] (JBranch (t "iw_3.v281") (To (a "L632")) (To (a "iw_3.L278"))));
  (mkBlock (a "iw_3.L278") [] [] (JGoto (To (a "L632"))));
  (mkBlock (a "iw_3.L255") [] [(Let (a "chk188") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (t "iw_3.v34") (t "chk188") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L632"))));
  (mkBlock (a "iw_3.L36") [] [(Let (a "chk189") A (Check 0 8 Write 1) [(t "v10")]);
      (RawStore Wl 0 (Const 0) (t "chk189"));
      (Let (a "chk190") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (Const 0) (t "chk190") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L632"))));
  (mkBlock (a "L631") [] [(Let (a "chk191") A (Check 0 8 Write 8) [(t "v8")]);
      (RawStorePointer 0 (Const 0) (t "chk191") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk192") A (Check 0 8 Write 1) [(t "v10")]);
      (RawStore Wl 0 (Const 0) (t "chk192"))] (JGoto (To (a "L632"))));
  (mkBlock (a "L632") [(Phi (a "pr.41") W [((a "L631"), (t "v37")); ((a "iw_3.L262"), (Const 1)); ((a "iw_3.L278"), (t "iw_3.pr.13")); ((a "iw_3.L255"), (t "iw_3.pr.13")); ((a "iw_3.L36"), (Const 3))])] [] (JBranch (t "v21") (To (a "L710")) (To (a "L709"))));
  (mkBlock (a "L709") [] [] (JGoto (To (a "L710"))));
  (mkBlock (a "L710") [(Phi (a "v712") P [((a "L709"), (t "v4")); ((a "L632"), (t "v6"))])] [] (JBranch (t "v29") (To (a "L718")) (To (a "L717"))));
  (mkBlock (a "L717") [] [] (JGoto (To (a "L718"))));
  (mkBlock (a "L718") [(Phi (a "v720") P [((a "L717"), (t "v0")); ((a "L710"), (t "v2"))])] [(Let (a "chk193") A (Check 0 8 Read 8) [(t "v8")]);
      (Let (a "v722") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk193")]);
      (Let (a "chk194") A (Check 0 8 Read 1) [(t "v10")]);
      (Let (a "v724") L (RawLoad LdL 0) [(t "chk194")]);
      (Call (CResult (a "iw_4.v11") L) (Global (a "__GI_strlen")) [(Arg P (t "v712"))]);
      (Let (a "iw_4.v12") L Add [(t "iw_4.v11"); (Const 1)]);
      (Call (CResult (a "iw_4.v15") L) (Global (a "__GI_strlen")) [(Arg P (t "v720"))]);
      (Let (a "iw_4.v16") L Add [(t "iw_4.v15"); (Const 1)]);
      (Let (a "iw_4.v18") L Add [(t "iw_4.v12"); (Const 32)]);
      (Let (a "iw_4.v20") L Add [(t "iw_4.v18"); (t "iw_4.v16")]);
      (Call (CResult (a "iw_4.v21") P) (Global (a "malloc")) [(Arg L (t "iw_4.v20"))]);
      (Let (a "iw_4.v26") L Ptoi [(t "iw_4.v21")]);
      (Let (a "iw_4.v28") W (Cmp Ne L) [(t "iw_4.v26"); (t "iw_1.v26")])] (JBranch (t "iw_4.v28") (To (a "iw_4.L22")) (To (a "iw_4.join"))));
  (mkBlock (a "iw_4.L22") [] [(Flight (a "iw_4.v31") Add [(FAddress (t "iw_4.v21")); (FValue (Const 32))] (LowerOf (t "iw_4.v21")));
      (Let (a "chk195") A (Check 0 8 Write 8) [(t "iw_4.v21")]);
      (RawStorePointer 0 (t "iw_4.v31") (t "chk195") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_4.v33") Add [(FAddress (t "iw_4.v21")); (FValue (Const 8))] (LowerOf (t "iw_4.v21")));
      (Call (CResult (a "iw_4.v38") P) (Global (a "__GI_mempcpy")) [(Arg P (t "iw_4.v31")); (Arg P (t "v712")); (Arg L (t "iw_4.v12"))]);
      (Call (CResult (a "iw_4.v41") P) (Global (a "__GI_memcpy")) [(Arg P (t "iw_4.v38")); (Arg P (t "v720")); (Arg L (t "iw_4.v16"))]);
      (Let (a "chk196") A (HalfCheck Upper 0 8 Write 8) [(t "chk195"); (t "iw_4.v33")]);
      (RawStorePointer 0 (t "iw_4.v41") (t "chk196") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_4.v43") Add [(FAddress (t "iw_4.v21")); (FValue (Const 16))] (LowerOf (t "iw_4.v21")));
      (Let (a "chk197") A (HalfCheck Upper 0 8 Write 8) [(t "chk195"); (t "iw_4.v43")]);
      (RawStorePointer 0 (t "v722") (t "chk197") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "iw_4.v46") Add [(FAddress (t "iw_4.v21")); (FValue (Const 24))] (LowerOf (t "iw_4.v21")));
      (Let (a "chk198") A (HalfCheck Upper 0 8 Write 1) [(t "chk195"); (t "iw_4.v46")]);
      (RawStore Wl 0 (t "v724") (t "chk198"));
      (Let (a "iw_4.v52") P Copy [(Global (a "glibc_gconv_db#known_derivations"))]);
      (Let (a "iw_4.v53") P Copy [(Global (a "glibc_gconv_db#derivation_compare"))]);
      (Call (CResult (a "iw_4.v54") P) (Global (a "__GI___tsearch")) [(Arg P (t "iw_4.v21")); (Arg P (t "iw_4.v52")); (Arg P (t "iw_4.v53"))]);
      (Let (a "iw_4.v55") L Ptoi [(t "iw_4.v54")]);
      (Let (a "iw_4.v57") W (Cmp Eq L) [(t "iw_4.v55"); (t "iw_1.v26")])] (JBranch (t "iw_4.v57") (To (a "iw_4.L48")) (To (a "iw_4.join"))));
  (mkBlock (a "iw_4.L48") [] [(Call CVoid (Global (a "free")) [(Arg P (t "iw_4.v21"))])] (JGoto (To (a "iw_4.join"))));
  (mkBlock (a "iw_4.join") [] [] (JRet (t "pr.41")))].
