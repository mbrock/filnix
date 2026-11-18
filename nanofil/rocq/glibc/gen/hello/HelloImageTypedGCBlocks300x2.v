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

Definition hello_image_fn___gconv_transform_internal_ucs2reverse'blocks2 : list block :=
  [(mkBlock (a "iw_6.L205") [] [(Let (a "iw_6.v209") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk147")]);
      (Let (a "iw_6.v212") W (Ext Uh) [(t "iw_6.v85")]);
      (Let (a "iw_6.iw_3.v3") W Sar [(t "iw_6.v212"); (Const 8)]);
      (Let (a "iw_6.iw_3.v4") W And [(t "iw_6.iw_3.v3"); (Const 255)]);
      (Let (a "iw_6.iw_3.v6") W And [(t "iw_6.v212"); (Const 255)]);
      (Let (a "iw_6.iw_3.v7") W Shl [(t "iw_6.iw_3.v6"); (Const 8)]);
      (Let (a "iw_6.iw_3.v8") W Or [(t "iw_6.iw_3.v4"); (t "iw_6.iw_3.v7")]);
      (Let (a "iw_6.iw_3.v9") W (Ext Uh) [(t "iw_6.iw_3.v8")]);
      (Let (a "chk167") A (Check 0 2 Write 1) [(t "iw_6.v209")]);
      (RawStore Wh 0 (t "iw_6.iw_3.v9") (t "chk167"));
      (Let (a "iw_6.v215") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk147")]);
      (Flight (a "iw_6.v216") Add [(FAddress (t "iw_6.v215")); (FValue (Const 2))] (LowerOf (t "iw_6.v215")));
      (Let (a "chk169") A (Renew 0 8 Write 8) [(t "chk144"); (t "iw_6.v22")]);
      (RawStorePointer 0 (t "iw_6.v216") (t "chk169") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk170") A (Renew 0 8 Read 8) [(t "chk143"); (t "iw_6.v19")]);
      (Let (a "iw_6.v217") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk170")]);
      (Flight (a "iw_6.v218") Add [(FAddress (t "iw_6.v217")); (FValue (Const 4))] (LowerOf (t "iw_6.v217")));
      (Let (a "chk171") A (Renew 0 8 Write 8) [(t "chk143"); (t "iw_6.v19")]);
      (RawStorePointer 0 (t "iw_6.v218") (t "chk171") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (Poll (a "iw_6.L25"))));
  (mkBlock (a "iw_6.L27") [(Phi (a "iw_6.pr.3") W [((a "iw_6.L25"), (t "iw_6.pr.2")); ((a "iw_6.L37"), (Const 7)); ((a "iw_6.L67"), (Const 5)); ((a "iw_6.L95"), (Const 6)); ((a "iw_6.L134"), (t "iw_6.pr.1")); ((a "iw_6.L156"), (t "iw_6.pr.1")); ((a "iw_6.iw_2.start"), (Const 6))])] [(Let (a "chk172") A (Renew 0 8 Read 8) [(t "chk143"); (t "iw_6.v19")]);
      (Let (a "iw_6.v220") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk172")]);
      (Let (a "chk173") A (Renew 0 8 Write 8) [(t "chk6"); (t "v4")]);
      (RawStorePointer 0 (t "iw_6.v220") (t "chk173") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk174") A (Renew 0 8 Read 8) [(t "chk144"); (t "iw_6.v22")]);
      (Let (a "iw_6.v222") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk174")]);
      (Let (a "v420") L (Ext Sw) [(t "iw_6.pr.3")]);
      (Let (a "chk175") A (Renew 0 8 Read 8) [(t "chk131"); (t "v266")]);
      (Let (a "v433") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk175")]);
      (Let (a "v434") L Ptoi [(t "iw_6.v222")]);
      (Let (a "v435") L Ptoi [(t "v433")]);
      (Let (a "v436") W (Cmp Eq L) [(t "v434"); (t "v435")])] (JBranch (t "v436") (To (a "L431")) (To (a "L430"))));
  (mkBlock (a "L430") [] [(Let (a "v437") P Copy [(Global (a "glibc_gconv_simple#str.273"))]);
      (Let (a "v438") P Copy [(Global (a "glibc_gconv_simple#str.271"))]);
      (Let (a "v439") P Copy [(Global (a "glibc_gconv_simple#str.287"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v437")); (Arg P (t "v438")); (Arg W (Const 594)); (Arg P (t "v439"))])] (JGoto (To (a "L431"))));
  (mkBlock (a "L431") [] [(Let (a "v444") W (Cmp Eq L) [(t "v420"); (Const 5)])] (JBranch (t "v444") (To (a "L442")) (To (a "L441"))));
  (mkBlock (a "L441") [] [(Let (a "v445") P Copy [(Global (a "glibc_gconv_simple#str.274"))]);
      (Let (a "v446") P Copy [(Global (a "glibc_gconv_simple#str.271"))]);
      (Let (a "v447") P Copy [(Global (a "glibc_gconv_simple#str.287"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v445")); (Arg P (t "v446")); (Arg W (Const 595)); (Arg P (t "v447"))])] (JGoto (To (a "L442"))));
  (mkBlock (a "L442") [] [(Let (a "v455") W (Cmp Eq L) [(t "v434"); (t "v262")])] (JBranch (t "v455") (To (a "L448")) (To (a "L258"))));
  (mkBlock (a "L448") [] [(Flight (a "v459") Add [(FAddress (t "v2")); (FValue (Const 20))] (LowerOf (t "v2")));
      (Let (a "chk176") A (Renew 0 4 Read 1) [(t "chk123"); (t "v459")]);
      (Let (a "v460") W (RawLoad (LdNarrow Sw) 0) [(t "chk176")]);
      (Let (a "v461") W Sub [(t "v460"); (Const 1)]);
      (Let (a "chk177") A (Renew 0 4 Write 1) [(t "chk123"); (t "v459")]);
      (RawStore Ww 0 (t "v461") (t "chk177"))] (JGoto (To (a "L258"))));
  (mkBlock (a "L279") [] [(Let (a "v467") W (Cmp Eq W) [(t "iw_3.pr.3"); (Const 5)])] (JBranch (t "v467") (To (a "L463")) (To (a "L258"))));
  (mkBlock (a "L463") [] [(Let (a "chk178") A (Renew 0 8 Read 8) [(t "chk130"); (t "v2")]);
      (Let (a "v469") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk178")])] (JGoto (To (a "L258"))));
  (mkBlock (a "L258") [(Phi (a "pr.7") W [((a "L312"), (t "v277")); ((a "L448"), (t "v277")); ((a "L442"), (t "v277")); ((a "L278"), (t "v277")); ((a "L463"), (Const 0)); ((a "L279"), (t "iw_3.pr.3")); ((a "L242"), (t "iw_3.pr.3"))])] [(Let (a "v474") W (Cmp Ne W) [(t "pr.7"); (Const 0)])] (JBranch (t "v474") (To (a "L190")) (To (a "L472"))));
  (mkBlock (a "L472") [] [(Let (a "chk179") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v2")]);
      (Let (a "v477") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk179")])] (JGoto (Poll (a "L188"))));
  (mkBlock (a "L190") [(Phi (a "pr.5") W [((a "L240"), (t "iw_3.pr.3")); ((a "L258"), (t "pr.7"))])] [(Let (a "v509") L (Ext Sw) [(t "v14")]);
      (Let (a "v510") W (Cmp Ne L) [(t "v509"); (Const 0)])] (JBranch (t "v510") (To (a "L513")) (To (a "L514"))));
  (mkBlock (a "L513") [] [(Let (a "v516") W (Cmp Eq W) [(t "pr.5"); (Const 7)])] (JGoto (To (a "L514"))));
  (mkBlock (a "L514") [(Phi (a "v518") W [((a "L190"), (Const 0)); ((a "L513"), (t "v516"))])] [] (JBranch (t "v518") (To (a "L478")) (To (a "L46"))));
  (mkBlock (a "L478") [] [(Let (a "chk180") A (Renew 0 8 Read 8) [(t "chk6"); (t "v4")]);
      (Let (a "v522") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk180")]);
      (Let (a "v524") L Ptoi [(t "v522")]);
      (Let (a "v525") L Sub [(t "iw_3.v31"); (t "v524")]);
      (Let (a "v530") W (Cmp Ule L) [(t "v525"); (Const 4)])] (JBranch (t "v530") (To (a "L535")) (To (a "L527"))));
  (mkBlock (a "L527") [] [(Let (a "v531") P Copy [(Global (a "glibc_gconv_simple#str.275"))]);
      (Let (a "v532") P Copy [(Global (a "glibc_gconv_simple#str.271"))]);
      (Let (a "v533") P Copy [(Global (a "glibc_gconv_simple#str.287"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v531")); (Arg P (t "v532")); (Arg W (Const 647)); (Arg P (t "v533"))])] (JGoto (To (a "L535"))));
  (mkBlock (a "L535") [(Phi (a "pr.20") L [((a "L536"), (t "v555")); ((a "L527"), (Const 0)); ((a "L478"), (Const 0))])] [(Let (a "v541") W (Cmp Ult L) [(t "pr.20"); (t "v525")])] (JBranch (t "v541") (To (a "L536")) (To (a "L538"))));
  (mkBlock (a "L536") [] [(Flight (a "v543") Add [(FAddress (t "v2")); (FValue (Const 32))] (LowerOf (t "v2")));
      (Let (a "chk181") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v543")]);
      (Let (a "v544") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk181")]);
      (Flight (a "v545") Add [(FAddress (t "v544")); (FValue (Const 4))] (LowerOf (t "v544")));
      (Flight (a "v547") Add [(FAddress (t "v545")); (FValue (t "pr.20"))] (LowerOf (t "v545")));
      (Let (a "chk182") A (Renew 0 8 Read 8) [(t "chk6"); (t "v4")]);
      (Let (a "v549") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk182")]);
      (Flight (a "v551") Add [(FAddress (t "v549")); (FValue (t "pr.20"))] (LowerOf (t "v549")));
      (Let (a "chk183") A (Check 0 1 Read 1) [(t "v551")]);
      (Let (a "v552") W (RawLoad (LdNarrow Ub) 0) [(t "chk183")]);
      (Let (a "v553") W (Ext Sb) [(t "v552")]);
      (Let (a "chk184") A (Check 0 1 Write 1) [(t "v547")]);
      (RawStore Wb 0 (t "v553") (t "chk184"));
      (Let (a "v555") L Add [(t "pr.20"); (Const 1)])] (JGoto (Poll (a "L535"))));
  (mkBlock (a "L538") [] [(Let (a "chk185") A (Renew 0 8 Write 8) [(t "chk6"); (t "v4")]);
      (RawStorePointer 0 (t "v6") (t "chk185") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v559") Add [(FAddress (t "v2")); (FValue (Const 32))] (LowerOf (t "v2")));
      (Let (a "chk186") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v559")]);
      (Let (a "v560") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk186")]);
      (Let (a "chk187") A (Check 0 4 Read 1) [(t "v560")]);
      (Let (a "v561") W (RawLoad (LdNarrow Sw) 0) [(t "chk187")]);
      (Let (a "v563") W And [(t "v561"); (Const 4294967288)]);
      (Let (a "chk188") A (Renew 0 4 Write 1) [(t "chk187"); (t "v560")]);
      (RawStore Ww 0 (t "v563") (t "chk188"));
      (Let (a "v566") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk186")]);
      (Let (a "chk190") A (Check 0 4 Read 1) [(t "v566")]);
      (Let (a "v567") W (RawLoad (LdNarrow Sw) 0) [(t "chk190")]);
      (Let (a "v569") L (Ext Sw) [(t "v567")]);
      (Let (a "v570") L Or [(t "v569"); (t "pr.20")]);
      (Let (a "chk191") A (Renew 0 4 Write 1) [(t "chk190"); (t "v566")]);
      (RawStore Ww 0 (t "v570") (t "chk191"))] (JGoto (To (a "L46"))));
  (mkBlock (a "L46") [(Phi (a "pr.9") W [((a "iw_1.join"), (t "v79")); ((a "L52"), (Const 0)); ((a "L538"), (t "pr.5")); ((a "L514"), (t "pr.5"))])] [] (JRet (t "pr.9")))].
