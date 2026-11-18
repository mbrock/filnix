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

Definition hello_image_fn___gconv_transform_internal_utf8'blocks2 : list block :=
  [(mkBlock (a "iw_6.L27") [(Phi (a "iw_6.pr.3") W [((a "iw_6.L25"), (t "iw_6.pr.2")); ((a "iw_6.L37"), (Const 7)); ((a "iw_6.L69"), (Const 5)); ((a "iw_6.L121"), (Const 5)); ((a "iw_6.L98"), (Const 6)); ((a "iw_6.L212"), (t "iw_6.pr.1")); ((a "iw_6.L234"), (t "iw_6.pr.1"))])] [(Let (a "chk165") A (Renew 0 8 Read 8) [(t "chk136"); (t "iw_6.v19")]);
      (Let (a "iw_6.v249") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk165")]);
      (Let (a "chk166") A (Renew 0 8 Write 8) [(t "chk6"); (t "v4")]);
      (RawStorePointer 0 (t "iw_6.v249") (t "chk166") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk167") A (Renew 0 8 Read 8) [(t "chk137"); (t "iw_6.v22")]);
      (Let (a "iw_6.v251") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk167")]);
      (Let (a "v295") L (Ext Sw) [(t "iw_6.pr.3")]);
      (Let (a "chk168") A (Renew 0 8 Read 8) [(t "chk129"); (t "v254")]);
      (Let (a "v308") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk168")]);
      (Let (a "v309") L Ptoi [(t "iw_6.v251")]);
      (Let (a "v310") L Ptoi [(t "v308")]);
      (Let (a "v311") W (Cmp Eq L) [(t "v309"); (t "v310")])] (JBranch (t "v311") (To (a "L306")) (To (a "L305"))));
  (mkBlock (a "L305") [] [(Let (a "v312") P Copy [(Global (a "glibc_gconv_simple#str.273"))]);
      (Let (a "v313") P Copy [(Global (a "glibc_gconv_simple#str.271"))]);
      (Let (a "v314") P Copy [(Global (a "glibc_gconv_simple#str.281"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v312")); (Arg P (t "v313")); (Arg W (Const 594)); (Arg P (t "v314"))])] (JGoto (To (a "L306"))));
  (mkBlock (a "L306") [] [(Let (a "v319") W (Cmp Eq L) [(t "v295"); (Const 5)])] (JBranch (t "v319") (To (a "L317")) (To (a "L316"))));
  (mkBlock (a "L316") [] [(Let (a "v320") P Copy [(Global (a "glibc_gconv_simple#str.274"))]);
      (Let (a "v321") P Copy [(Global (a "glibc_gconv_simple#str.271"))]);
      (Let (a "v322") P Copy [(Global (a "glibc_gconv_simple#str.281"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v320")); (Arg P (t "v321")); (Arg W (Const 595)); (Arg P (t "v322"))])] (JGoto (To (a "L317"))));
  (mkBlock (a "L317") [] [(Let (a "v330") W (Cmp Eq L) [(t "v309"); (t "v250")])] (JBranch (t "v330") (To (a "L323")) (To (a "L246"))));
  (mkBlock (a "L323") [] [(Flight (a "v334") Add [(FAddress (t "v2")); (FValue (Const 20))] (LowerOf (t "v2")));
      (Let (a "chk169") A (Renew 0 4 Read 1) [(t "chk121"); (t "v334")]);
      (Let (a "v335") W (RawLoad (LdNarrow Sw) 0) [(t "chk169")]);
      (Let (a "v336") W Sub [(t "v335"); (Const 1)]);
      (Let (a "chk170") A (Renew 0 4 Write 1) [(t "chk121"); (t "v334")]);
      (RawStore Ww 0 (t "v336") (t "chk170"))] (JGoto (To (a "L246"))));
  (mkBlock (a "L267") [] [(Let (a "v342") W (Cmp Eq W) [(t "iw_3.pr.3"); (Const 5)])] (JBranch (t "v342") (To (a "L338")) (To (a "L246"))));
  (mkBlock (a "L338") [] [(Let (a "chk171") A (Renew 0 8 Read 8) [(t "chk128"); (t "v2")]);
      (Let (a "v344") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk171")])] (JGoto (To (a "L246"))));
  (mkBlock (a "L246") [(Phi (a "pr.7") W [((a "L323"), (t "v265")); ((a "L317"), (t "v265")); ((a "L266"), (t "v265")); ((a "L338"), (Const 0)); ((a "L267"), (t "iw_3.pr.3")); ((a "L230"), (t "iw_3.pr.3"))])] [(Let (a "v349") W (Cmp Ne W) [(t "pr.7"); (Const 0)])] (JBranch (t "v349") (To (a "L190")) (To (a "L347"))));
  (mkBlock (a "L347") [] [(Let (a "chk172") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v2")]);
      (Let (a "v352") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk172")])] (JGoto (Poll (a "L188"))));
  (mkBlock (a "L190") [(Phi (a "pr.5") W [((a "L228"), (t "iw_3.pr.3")); ((a "L246"), (t "pr.7"))])] [(Let (a "v384") L (Ext Sw) [(t "v14")]);
      (Let (a "v385") W (Cmp Ne L) [(t "v384"); (Const 0)])] (JBranch (t "v385") (To (a "L388")) (To (a "L389"))));
  (mkBlock (a "L388") [] [(Let (a "v391") W (Cmp Eq W) [(t "pr.5"); (Const 7)])] (JGoto (To (a "L389"))));
  (mkBlock (a "L389") [(Phi (a "v393") W [((a "L190"), (Const 0)); ((a "L388"), (t "v391"))])] [] (JBranch (t "v393") (To (a "L353")) (To (a "L46"))));
  (mkBlock (a "L353") [] [(Let (a "chk173") A (Renew 0 8 Read 8) [(t "chk6"); (t "v4")]);
      (Let (a "v397") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk173")]);
      (Let (a "v399") L Ptoi [(t "v397")]);
      (Let (a "v400") L Sub [(t "iw_3.v31"); (t "v399")]);
      (Let (a "v405") W (Cmp Ule L) [(t "v400"); (Const 4)])] (JBranch (t "v405") (To (a "L410")) (To (a "L402"))));
  (mkBlock (a "L402") [] [(Let (a "v406") P Copy [(Global (a "glibc_gconv_simple#str.275"))]);
      (Let (a "v407") P Copy [(Global (a "glibc_gconv_simple#str.271"))]);
      (Let (a "v408") P Copy [(Global (a "glibc_gconv_simple#str.281"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v406")); (Arg P (t "v407")); (Arg W (Const 647)); (Arg P (t "v408"))])] (JGoto (To (a "L410"))));
  (mkBlock (a "L410") [(Phi (a "pr.20") L [((a "L411"), (t "v430")); ((a "L402"), (Const 0)); ((a "L353"), (Const 0))])] [(Let (a "v416") W (Cmp Ult L) [(t "pr.20"); (t "v400")])] (JBranch (t "v416") (To (a "L411")) (To (a "L413"))));
  (mkBlock (a "L411") [] [(Flight (a "v418") Add [(FAddress (t "v2")); (FValue (Const 32))] (LowerOf (t "v2")));
      (Let (a "chk174") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v418")]);
      (Let (a "v419") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk174")]);
      (Flight (a "v420") Add [(FAddress (t "v419")); (FValue (Const 4))] (LowerOf (t "v419")));
      (Flight (a "v422") Add [(FAddress (t "v420")); (FValue (t "pr.20"))] (LowerOf (t "v420")));
      (Let (a "chk175") A (Renew 0 8 Read 8) [(t "chk6"); (t "v4")]);
      (Let (a "v424") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk175")]);
      (Flight (a "v426") Add [(FAddress (t "v424")); (FValue (t "pr.20"))] (LowerOf (t "v424")));
      (Let (a "chk176") A (Check 0 1 Read 1) [(t "v426")]);
      (Let (a "v427") W (RawLoad (LdNarrow Ub) 0) [(t "chk176")]);
      (Let (a "v428") W (Ext Sb) [(t "v427")]);
      (Let (a "chk177") A (Check 0 1 Write 1) [(t "v422")]);
      (RawStore Wb 0 (t "v428") (t "chk177"));
      (Let (a "v430") L Add [(t "pr.20"); (Const 1)])] (JGoto (Poll (a "L410"))));
  (mkBlock (a "L413") [] [(Let (a "chk178") A (Renew 0 8 Write 8) [(t "chk6"); (t "v4")]);
      (RawStorePointer 0 (t "v6") (t "chk178") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v434") Add [(FAddress (t "v2")); (FValue (Const 32))] (LowerOf (t "v2")));
      (Let (a "chk179") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v434")]);
      (Let (a "v435") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk179")]);
      (Let (a "chk180") A (Check 0 4 Read 1) [(t "v435")]);
      (Let (a "v436") W (RawLoad (LdNarrow Sw) 0) [(t "chk180")]);
      (Let (a "v438") W And [(t "v436"); (Const 4294967288)]);
      (Let (a "chk181") A (Renew 0 4 Write 1) [(t "chk180"); (t "v435")]);
      (RawStore Ww 0 (t "v438") (t "chk181"));
      (Let (a "v441") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk179")]);
      (Let (a "chk183") A (Check 0 4 Read 1) [(t "v441")]);
      (Let (a "v442") W (RawLoad (LdNarrow Sw) 0) [(t "chk183")]);
      (Let (a "v444") L (Ext Sw) [(t "v442")]);
      (Let (a "v445") L Or [(t "v444"); (t "pr.20")]);
      (Let (a "chk184") A (Renew 0 4 Write 1) [(t "chk183"); (t "v441")]);
      (RawStore Ww 0 (t "v445") (t "chk184"))] (JGoto (To (a "L46"))));
  (mkBlock (a "L46") [(Phi (a "pr.10") W [((a "iw_1.join"), (t "v79")); ((a "L52"), (Const 0)); ((a "L413"), (t "pr.5")); ((a "L389"), (t "pr.5"))])] [] (JRet (t "pr.10")))].
