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

Definition hello_image_fn___gconv_transform_utf8_internal'blocks2 : list block :=
  [(mkBlock (a "L338") [] [(Let (a "chk91") A (Renew 0 8 Read 8) [(t "chk70"); (t "v2")]);
      (Let (a "v344") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk91")])] (JGoto (To (a "L246"))));
  (mkBlock (a "L246") [(Phi (a "pr.7") W [((a "L323"), (t "v265")); ((a "L317"), (t "v265")); ((a "L266"), (t "v265")); ((a "L338"), (Const 0)); ((a "L267"), (t "iw_3.pr.2")); ((a "L230"), (t "iw_3.pr.2"))])] [(Let (a "v349") W (Cmp Ne W) [(t "pr.7"); (Const 0)])] (JBranch (t "v349") (To (a "L190")) (To (a "L347"))));
  (mkBlock (a "L347") [] [(Let (a "chk92") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v2")]);
      (Let (a "v352") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk92")])] (JGoto (Poll (a "L188"))));
  (mkBlock (a "L190") [(Phi (a "pr.5") W [((a "L228"), (t "iw_3.pr.2")); ((a "L246"), (t "pr.7"))])] [(Let (a "v384") L (Ext Sw) [(t "v14")]);
      (Let (a "v385") W (Cmp Ne L) [(t "v384"); (Const 0)])] (JBranch (t "v385") (To (a "L388")) (To (a "L389"))));
  (mkBlock (a "L388") [] [(Let (a "v391") W (Cmp Eq W) [(t "pr.5"); (Const 7)])] (JGoto (To (a "L389"))));
  (mkBlock (a "L389") [(Phi (a "v393") W [((a "L190"), (Const 0)); ((a "L388"), (t "v391"))])] [] (JBranch (t "v393") (To (a "L353")) (To (a "L46"))));
  (mkBlock (a "L353") [] [(Flight (a "v396") Add [(FAddress (t "v2")); (FValue (Const 32))] (LowerOf (t "v2")));
      (Let (a "chk93") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v396")]);
      (Let (a "v397") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk93")]);
      (Let (a "chk94") A (Renew 0 8 Read 8) [(t "chk6"); (t "v4")]);
      (Let (a "v400") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk94")]);
      (Let (a "chk95") A (Check 0 1 Read 1) [(t "v400")]);
      (Let (a "v401") W (RawLoad (LdNarrow Ub) 0) [(t "chk95")]);
      (Let (a "v407") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk94")]);
      (Let (a "v409") L Ptoi [(t "v407")]);
      (Let (a "v410") L Sub [(t "iw_3.v31"); (t "v409")]);
      (Let (a "chk97") A (Check 0 4 Write 1) [(t "v397")]);
      (RawStore Ww 0 (t "v410") (t "chk97"));
      (Let (a "v415") W (Cmp Ne W) [(t "v401"); (Const 192)])] (JBranch (t "v415") (To (a "L416")) (To (a "L417"))));
  (mkBlock (a "L416") [] [(Let (a "v419") W (Cmp Ne W) [(t "v401"); (Const 193)])] (JGoto (To (a "L417"))));
  (mkBlock (a "L417") [(Phi (a "v421") W [((a "L353"), (Const 0)); ((a "L416"), (t "v419"))])] [] (JBranch (t "v421") (To (a "L413")) (To (a "L412"))));
  (mkBlock (a "L412") [] [(Let (a "v422") P Copy [(Global (a "glibc_gconv_simple#str.283"))]);
      (Let (a "v423") P Copy [(Global (a "glibc_gconv_simple#str.271"))]);
      (Let (a "v424") P Copy [(Global (a "glibc_gconv_simple#str.282"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v422")); (Arg P (t "v423")); (Arg W (Const 642)); (Arg P (t "v424"))])] (JGoto (To (a "L413"))));
  (mkBlock (a "L413") [] [(Let (a "v429") W (Cmp Uge W) [(t "v401"); (Const 194)])] (JBranch (t "v429") (To (a "L430")) (To (a "L431"))));
  (mkBlock (a "L430") [] [(Let (a "v433") W (Cmp Ult W) [(t "v401"); (Const 224)])] (JGoto (To (a "L431"))));
  (mkBlock (a "L431") [(Phi (a "v435") W [((a "L413"), (Const 0)); ((a "L430"), (t "v433"))])] [] (JBranch (t "v435") (To (a "L425")) (To (a "L426"))));
  (mkBlock (a "L425") [] [(Let (a "v437") W And [(t "v401"); (Const 31)])] (JGoto (To (a "L427"))));
  (mkBlock (a "L426") [] [(Let (a "v442") W And [(t "v401"); (Const 240)]);
      (Let (a "v443") W (Cmp Eq W) [(t "v442"); (Const 224)])] (JBranch (t "v443") (To (a "L438")) (To (a "L439"))));
  (mkBlock (a "L438") [] [(Let (a "v447") W And [(t "v401"); (Const 15)])] (JGoto (To (a "L427"))));
  (mkBlock (a "L439") [] [(Let (a "v452") W And [(t "v401"); (Const 248)]);
      (Let (a "v453") W (Cmp Eq W) [(t "v452"); (Const 240)])] (JBranch (t "v453") (To (a "L448")) (To (a "L449"))));
  (mkBlock (a "L448") [] [(Let (a "v457") W And [(t "v401"); (Const 7)])] (JGoto (To (a "L427"))));
  (mkBlock (a "L449") [] [(Let (a "v462") W And [(t "v401"); (Const 252)]);
      (Let (a "v463") W (Cmp Eq W) [(t "v462"); (Const 248)])] (JBranch (t "v463") (To (a "L458")) (To (a "L459"))));
  (mkBlock (a "L458") [] [(Let (a "v467") W And [(t "v401"); (Const 3)])] (JGoto (To (a "L427"))));
  (mkBlock (a "L459") [] [(Let (a "v469") W And [(t "v401"); (Const 1)])] (JGoto (To (a "L427"))));
  (mkBlock (a "L427") [(Phi (a "pr.25") L [((a "L425"), (Const 2)); ((a "L438"), (Const 3)); ((a "L448"), (Const 4)); ((a "L458"), (Const 5)); ((a "L459"), (Const 6))]); (Phi (a "pr.20") W [((a "L425"), (t "v437")); ((a "L438"), (t "v447")); ((a "L448"), (t "v457")); ((a "L458"), (t "v467")); ((a "L459"), (t "v469"))])] [(Let (a "v471") L Sub [(t "pr.25"); (Const 1)])] (JGoto (To (a "L472"))));
  (mkBlock (a "L472") [(Phi (a "pr.29") L [((a "L427"), (t "v471")); ((a "L473"), (t "v491"))]); (Phi (a "pr.24") W [((a "L427"), (t "pr.20")); ((a "L473"), (t "v489"))])] [(Let (a "chk98") A (Renew 0 8 Read 8) [(t "chk6"); (t "v4")]);
      (Let (a "v476") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk98")]);
      (Flight (a "v477") Add [(FAddress (t "v476")); (FValue (Const 1))] (LowerOf (t "v476")));
      (Let (a "chk99") A (Renew 0 8 Write 8) [(t "chk6"); (t "v4")]);
      (RawStorePointer 0 (t "v477") (t "chk99") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v479") L Ptoi [(t "v477")]);
      (Let (a "v481") W (Cmp Ult L) [(t "v479"); (t "iw_3.v31")])] (JBranch (t "v481") (To (a "L473")) (To (a "L474"))));
  (mkBlock (a "L473") [] [(Let (a "v483") W Shl [(t "pr.24"); (Const 6)]);
      (Let (a "chk100") A (Renew 0 8 Read 8) [(t "chk6"); (t "v4")]);
      (Let (a "v486") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk100")]);
      (Let (a "chk101") A (Check 0 1 Read 1) [(t "v486")]);
      (Let (a "v487") W (RawLoad (LdNarrow Ub) 0) [(t "chk101")]);
      (Let (a "v488") W And [(t "v487"); (Const 63)]);
      (Let (a "v489") W Or [(t "v483"); (t "v488")]);
      (Let (a "v491") L Sub [(t "pr.29"); (Const 1)])] (JGoto (Poll (a "L472"))));
  (mkBlock (a "L474") [] [(Let (a "v494") L Mul [(t "pr.29"); (Const 6)]);
      (Let (a "v495") W Shl [(t "pr.24"); (t "v494")]);
      (Let (a "chk102") A (Renew 0 4 Read 1) [(t "chk97"); (t "v397")]);
      (Let (a "v497") W (RawLoad (LdNarrow Sw) 0) [(t "chk102")]);
      (Let (a "v499") L Shl [(t "pr.25"); (Const 8)]);
      (Let (a "v500") L (Ext Sw) [(t "v497")]);
      (Let (a "v501") L Or [(t "v500"); (t "v499")]);
      (Let (a "chk103") A (Renew 0 4 Write 1) [(t "chk97"); (t "v397")]);
      (RawStore Ww 0 (t "v501") (t "chk103"));
      (Flight (a "v503") Add [(FAddress (t "v397")); (FValue (Const 4))] (LowerOf (t "v397")));
      (Let (a "chk104") A (HalfCheck Upper 0 4 Write 1) [(t "chk97"); (t "v503")]);
      (RawStore Ww 0 (t "v495") (t "chk104"))] (JGoto (To (a "L46"))));
  (mkBlock (a "L46") [(Phi (a "pr.10") W [((a "iw_1.join"), (t "v79")); ((a "L52"), (Const 0)); ((a "L474"), (t "pr.5")); ((a "L389"), (t "pr.5"))])] [] (JRet (t "pr.10")))].
