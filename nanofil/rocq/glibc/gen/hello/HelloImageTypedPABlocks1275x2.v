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

Definition hello_image_fn___parse_one_specmb'blocks2 : list block :=
  [(mkBlock (a "L859") [] [(Flight (a "v874") Add [(FAddress (t "v4")); (FValue (Const 12))] (LowerOf (t "v4")));
      (Let (a "v875") W (RawLoad (LdNarrow Uw) 0) [(t "chk221")]);
      (Let (a "v876") W Shl [(t "v875"); (Const 30)]);
      (Let (a "v877") W Shr [(t "v876"); (Const 31)])] (JBranch (t "v877") (To (a "L870")) (To (a "L871"))));
  (mkBlock (a "L870") [] [(Flight (a "v879") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk224") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v879")]);
      (RawStore Ww 0 (Const 1024) (t "chk224"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L871") [] [(Flight (a "v886") Add [(FAddress (t "v4")); (FValue (Const 12))] (LowerOf (t "v4")));
      (Let (a "v887") W (RawLoad (LdNarrow Uw) 0) [(t "chk221")]);
      (Let (a "v888") W Shl [(t "v887"); (Const 22)]);
      (Let (a "v889") W Shr [(t "v888"); (Const 31)])] (JBranch (t "v889") (To (a "L882")) (To (a "L883"))));
  (mkBlock (a "L882") [] [(Flight (a "v891") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk226") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v891")]);
      (RawStore Ww 0 (Const 1) (t "chk226"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L883") [] [(Flight (a "v893") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk227") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v893")]);
      (RawStore Ww 0 (Const 0) (t "chk227"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L901") [] [(Flight (a "v906") Add [(FAddress (t "v4")); (FValue (Const 12))] (LowerOf (t "v4")));
      (Let (a "chk228") A (Renew 0 4 Read 1) [(t "chk4"); (t "v906")]);
      (Let (a "v907") W (RawLoad (LdNarrow Uw) 0) [(t "chk228")]);
      (Let (a "v908") W Shl [(t "v907"); (Const 31)]);
      (Let (a "v909") W Shr [(t "v908"); (Const 31)])] (JBranch (t "v909") (To (a "L902")) (To (a "L903"))));
  (mkBlock (a "L902") [] [(Flight (a "v911") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk229") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v911")]);
      (RawStore Ww 0 (Const 263) (t "chk229"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L903") [] [(Flight (a "v915") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk230") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v915")]);
      (RawStore Ww 0 (Const 7) (t "chk230"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L916") [] [(Flight (a "v918") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk231") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v918")]);
      (RawStore Ww 0 (Const 1) (t "chk231"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L919") [] [(Flight (a "v921") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk232") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v921")]);
      (RawStore Ww 0 (Const 2) (t "chk232"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L922") [] [(Flight (a "v924") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk233") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v924")]);
      (RawStore Ww 0 (Const 3) (t "chk233"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L925") [] [(Flight (a "v927") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk234") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v927")]);
      (RawStore Ww 0 (Const 4) (t "chk234"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L928") [] [(Flight (a "v930") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk235") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v930")]);
      (RawStore Ww 0 (Const 5) (t "chk235"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L931") [] [(Flight (a "v933") Add [(FAddress (t "v4")); (FValue (Const 52))] (LowerOf (t "v4")));
      (Let (a "chk236") A (HalfCheck Upper 0 4 Write 1) [(t "chk3"); (t "v933")]);
      (RawStore Ww 0 (Const 2048) (t "chk236"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L937") [] [(Flight (a "v939") Add [(FAddress (t "v4")); (FValue (Const 56))] (LowerOf (t "v4")));
      (Let (a "chk237") A (Renew 0 8 Write 1) [(t "chk219"); (t "v939")]);
      (RawStore Wl 0 (Const 0) (t "chk237"))] (JGoto (To (a "L786"))));
  (mkBlock (a "L942") [] [(Let (a "v944") W (Cmp Slt W) [(t "v847"); (Const 71)])] (JBranch (t "v944") (To (a "L945")) (To (a "L946"))));
  (mkBlock (a "L945") [] [(Let (a "v947") W (Cmp Slt W) [(t "v847"); (Const 67)])] (JBranch (t "v947") (To (a "L948")) (To (a "L949"))));
  (mkBlock (a "L948") [] [(Let (a "v950") W (Cmp Eq W) [(t "v847"); (Const 65)])] (JBranch (t "v950") (Poll (a "L901")) (To (a "L951"))));
  (mkBlock (a "L951") [] [(Let (a "v952") W (Cmp Eq W) [(t "v847"); (Const 66)])] (JBranch (t "v952") (Poll (a "L857")) (Poll (a "L937"))));
  (mkBlock (a "L949") [] [(Let (a "v954") W (Cmp Eq W) [(t "v847"); (Const 67)])] (JBranch (t "v954") (Poll (a "L919")) (To (a "L955"))));
  (mkBlock (a "L955") [] [(Let (a "v956") W (Cmp Eq W) [(t "v847"); (Const 69)])] (JBranch (t "v956") (Poll (a "L901")) (To (a "L957"))));
  (mkBlock (a "L957") [] [(Let (a "v958") W (Cmp Eq W) [(t "v847"); (Const 70)])] (JBranch (t "v958") (Poll (a "L901")) (Poll (a "L937"))));
  (mkBlock (a "L946") [] [(Let (a "v960") W (Cmp Slt W) [(t "v847"); (Const 97)])] (JBranch (t "v960") (To (a "L961")) (To (a "L962"))));
  (mkBlock (a "L961") [] [(Let (a "v963") W (Cmp Eq W) [(t "v847"); (Const 71)])] (JBranch (t "v963") (Poll (a "L901")) (To (a "L964"))));
  (mkBlock (a "L964") [] [(Let (a "v965") W (Cmp Eq W) [(t "v847"); (Const 83)])] (JBranch (t "v965") (Poll (a "L925")) (To (a "L966"))));
  (mkBlock (a "L966") [] [(Let (a "v967") W (Cmp Eq W) [(t "v847"); (Const 88)])] (JBranch (t "v967") (Poll (a "L857")) (Poll (a "L937"))));
  (mkBlock (a "L962") [] [(Let (a "v969") W (Cmp Eq W) [(t "v847"); (Const 97)])] (JBranch (t "v969") (Poll (a "L901")) (To (a "L970"))));
  (mkBlock (a "L970") [] [(Let (a "v971") W (Cmp Eq W) [(t "v847"); (Const 98)])] (JBranch (t "v971") (Poll (a "L857")) (To (a "L972"))));
  (mkBlock (a "L972") [] [(Let (a "v973") W (Cmp Eq W) [(t "v847"); (Const 99)])] (JBranch (t "v973") (Poll (a "L916")) (Poll (a "L937"))));
  (mkBlock (a "L943") [] [(Let (a "v975") W (Cmp Slt W) [(t "v847"); (Const 110)])] (JBranch (t "v975") (To (a "L976")) (To (a "L977"))));
  (mkBlock (a "L976") [] [(Let (a "v978") W (Cmp Slt W) [(t "v847"); (Const 103)])] (JBranch (t "v978") (To (a "L979")) (To (a "L980"))));
  (mkBlock (a "L979") [] [(Let (a "v981") W (Cmp Eq W) [(t "v847"); (Const 100)])] (JBranch (t "v981") (Poll (a "L857")) (To (a "L982"))));
  (mkBlock (a "L982") [] [(Let (a "v983") W (Cmp Eq W) [(t "v847"); (Const 101)])] (JBranch (t "v983") (Poll (a "L901")) (To (a "L984"))));
  (mkBlock (a "L984") [] [(Let (a "v985") W (Cmp Eq W) [(t "v847"); (Const 102)])] (JBranch (t "v985") (Poll (a "L901")) (Poll (a "L937"))));
  (mkBlock (a "L980") [] [(Let (a "v987") W (Cmp Eq W) [(t "v847"); (Const 103)])] (JBranch (t "v987") (Poll (a "L901")) (To (a "L988"))));
  (mkBlock (a "L988") [] [(Let (a "v989") W (Cmp Eq W) [(t "v847"); (Const 105)])] (JBranch (t "v989") (Poll (a "L857")) (To (a "L990"))));
  (mkBlock (a "L990") [] [(Let (a "v991") W (Cmp Eq W) [(t "v847"); (Const 109)])] (JBranch (t "v991") (Poll (a "L937")) (To (a "L992"))));
  (mkBlock (a "L992") [] [] (JGoto (Poll (a "L937"))));
  (mkBlock (a "L977") [] [(Let (a "v993") W (Cmp Slt W) [(t "v847"); (Const 115)])] (JBranch (t "v993") (To (a "L994")) (To (a "L995"))));
  (mkBlock (a "L994") [] [(Let (a "v996") W (Cmp Eq W) [(t "v847"); (Const 110)])] (JBranch (t "v996") (Poll (a "L931")) (To (a "L997"))));
  (mkBlock (a "L997") [] [(Let (a "v998") W (Cmp Eq W) [(t "v847"); (Const 111)])] (JBranch (t "v998") (Poll (a "L857")) (To (a "L999"))));
  (mkBlock (a "L999") [] [(Let (a "v1000") W (Cmp Eq W) [(t "v847"); (Const 112)])] (JBranch (t "v1000") (Poll (a "L928")) (Poll (a "L937"))));
  (mkBlock (a "L995") [] [(Let (a "v1002") W (Cmp Eq W) [(t "v847"); (Const 115)])] (JBranch (t "v1002") (Poll (a "L922")) (To (a "L1003"))));
  (mkBlock (a "L1003") [] [(Let (a "v1004") W (Cmp Eq W) [(t "v847"); (Const 117)])] (JBranch (t "v1004") (Poll (a "L857")) (To (a "L1005"))));
  (mkBlock (a "L1005") [] [(Let (a "v1006") W (Cmp Eq W) [(t "v847"); (Const 120)])] (JBranch (t "v1006") (Poll (a "L857")) (Poll (a "L937"))));
  (mkBlock (a "L786") [] [(Flight (a "v1012") Add [(FAddress (t "v4")); (FValue (Const 48))] (LowerOf (t "v4")));
      (Let (a "chk238") A (Renew 0 4 Read 1) [(t "chk3"); (t "v1012")]);
      (Let (a "v1013") W (RawLoad (LdNarrow Sw) 0) [(t "chk238")]);
      (Let (a "v1015") W (Cmp Eq W) [(t "v1013"); (Const 4294967295)])] (JBranch (t "v1015") (To (a "L1016")) (To (a "L1017"))));
  (mkBlock (a "L1016") [] [(Flight (a "v1019") Add [(FAddress (t "v4")); (FValue (Const 56))] (LowerOf (t "v4")));
      (Let (a "chk239") A (HalfCheck Upper 0 8 Read 1) [(t "chk3"); (t "v1019")]);
      (Let (a "v1020") L (RawLoad LdL 0) [(t "chk239")]);
      (Let (a "v1021") W (Cmp Ugt L) [(t "v1020"); (Const 0)])] (JGoto (To (a "L1017"))));
  (mkBlock (a "L1017") [(Phi (a "v1023") W [((a "L786"), (Const 0)); ((a "L1016"), (t "v1021"))])] [] (JBranch (t "v1023") (To (a "L1008")) (To (a "L1010"))));
  (mkBlock (a "L1008") [] [(Flight (a "v1025") Add [(FAddress (t "v4")); (FValue (Const 48))] (LowerOf (t "v4")));
      (Let (a "chk240") A (Renew 0 4 Write 1) [(t "chk3"); (t "v1025")]);
      (RawStore Ww 0 (t "pr.3") (t "chk240"));
      (Flight (a "v1029") Add [(FAddress (t "v4")); (FValue (Const 56))] (LowerOf (t "v4")));
      (Let (a "chk241") A (HalfCheck Upper 0 8 Read 1) [(t "chk3"); (t "v1029")]);
      (Let (a "v1030") L (RawLoad LdL 0) [(t "chk241")]);
      (Let (a "v1031") L Add [(t "pr.9"); (t "v1030")])] (JGoto (To (a "L1010"))));
  (mkBlock (a "L1010") [(Phi (a "pr.6") L [((a "L1008"), (t "v1031")); ((a "L1017"), (t "pr.9"))])] [(Flight (a "v1036") Add [(FAddress (t "v4")); (FValue (Const 8))] (LowerOf (t "v4")));
      (Let (a "chk242") A (Renew 0 4 Read 1) [(t "chk207"); (t "v1036")]);
      (Let (a "v1037") W (RawLoad (LdNarrow Sw) 0) [(t "chk242")]);
      (Let (a "v1038") W (Cmp Eq W) [(t "v1037"); (Const 0)])] (JBranch (t "v1038") (To (a "L1032")) (To (a "L1033"))));
  (mkBlock (a "L1032") [] [(Flight (a "v1040") Add [(FAddress (t "v4")); (FValue (Const 24))] (LowerOf (t "v4")));
      (Flight (a "v1042") Add [(FAddress (t "v4")); (FValue (Const 32))] (LowerOf (t "v4")));
      (Let (a "chk243") A (Renew 0 8 Read 8) [(t "chk0"); (t "v1")]);
      (Let (a "v1043") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk243")]);
      (Flight (a "v1044") Sub [(FAddress (t "v1043")); (FValue (Const 1))] (LowerOf (t "v1043")));
      (Let (a "chk244") A (HalfCheck Lower 0 8 Write 8) [(t "chk3"); (t "v1042")]);
      (RawStorePointer 0 (t "v1044") (t "chk244") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk245") A (HalfCheck Lower 0 8 Write 8) [(t "chk3"); (t "v1040")]);
      (RawStorePointer 0 (t "v1044") (t "chk245") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L1034"))));
  (mkBlock (a "L1033") [] [(Flight (a "v1046") Add [(FAddress (t "v4")); (FValue (Const 24))] (LowerOf (t "v4")));
      (Let (a "chk246") A (Renew 0 8 Read 8) [(t "chk0"); (t "v1")]);
      (Let (a "v1047") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk246")]);
      (Let (a "chk247") A (HalfCheck Lower 0 8 Write 8) [(t "chk3"); (t "v1046")]);
      (RawStorePointer 0 (t "v1047") (t "chk247") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v1049") Add [(FAddress (t "v4")); (FValue (Const 32))] (LowerOf (t "v4")));
      (Let (a "chk248") A (Renew 0 8 Read 8) [(t "chk0"); (t "v1")]);
      (Let (a "v1050") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk248")]);
      (Call (CResult (a "iw_7.v3") P) (Global (a "__GI___strchrnul")) [(Arg P (t "v1050")); (Arg W (Const 37))]);
      (Let (a "chk249") A (HalfCheck Lower 0 8 Write 8) [(t "chk3"); (t "v1049")]);
      (RawStorePointer 0 (t "iw_7.v3") (t "chk249") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L1034"))));
  (mkBlock (a "L1034") [] [] (JRet (t "pr.6")))].
