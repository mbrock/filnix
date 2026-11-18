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

Definition hello_image_fn___is_decorate_maps_enabled : func :=
  mkFunc (a "__is_decorate_maps_enabled") (a "export") (RClass W) [] [(mkBlock (a "start") [] [(Let (a "v9") P (Alloc 4) [(Const 4)]);
      (Let (a "v0") P Copy [(Global (a "glibc_setvmaname#decorate_maps"))]);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v0")]);
      (Let (a "v1") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v29") W (Cmp Eq W) [(t "v1"); (Const (-1))])] (JBranch (t "v29") (To (a "L4")) (To (a "L30"))));
  (mkBlock (a "L4") [] [(Call CVoid (Global (a "__tunable_get_val")) [(Arg W (Const 26)); (Arg P (t "v9")); (Arg P (Const 0))]);
      (Let (a "chk1") A (Check 0 4 Read 1) [(t "v9")]);
      (Let (a "v11") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")]);
      (Let (a "v12") W (Cmp Ne W) [(t "v11"); (Const 0)])] (JBranch (t "v12") (To (a "L13")) (To (a "L19"))));
  (mkBlock (a "L13") [] [(Let (a "v16") P Copy [(Global (a "glibc_setvmaname#decorate_maps"))]);
      (Let (a "chk2") A (Check 0 4 Write 1) [(t "v16")]);
      (RawStore Ww 0 (Const 1) (t "chk2"))] (JRet (Const 1)));
  (mkBlock (a "L19") [] [(Let (a "v22") P Copy [(Global (a "glibc_setvmaname#decorate_maps"))]);
      (Let (a "chk3") A (Check 0 4 Write 1) [(t "v22")]);
      (RawStore Ww 0 (Const 0) (t "chk3"))] (JRet (Const 0)));
  (mkBlock (a "L24") [] [] (JRet (Const 0)));
  (mkBlock (a "L26") [] [] (JRet (Const 1)));
  (mkBlock (a "L30") [] [(Let (a "v31") W (Cmp Eq W) [(t "v1"); (Const 0)])] (JBranch (t "v31") (Poll (a "L24")) (To (a "L32"))));
  (mkBlock (a "L32") [] [(Let (a "v33") W (Cmp Eq W) [(t "v1"); (Const 1)])] (JBranch (t "v33") (Poll (a "L26")) (To (a "L3"))));
  (mkBlock (a "L3") [] [] JUnreachable)].

Definition hello_image_fn___GI___isoc23_strtol : func :=
  mkFunc (a "__GI___isoc23_strtol") (a "export") (RClass L) [(P, (a "v0")); (P, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v10") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v10")]);
      (Let (a "v11") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call (CResult (a "v12") L) (Global (a "__GI_____strtol_l_internal")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg W (t "v4")); (Arg W (Const 0)); (Arg W (Const 1)); (Arg P (t "v11"))])] (JRet (t "v12")))].

Definition hello_image_fn___GI___isoc23_strtoul : func :=
  mkFunc (a "__GI___isoc23_strtoul") (a "export") (RClass L) [(P, (a "v0")); (P, (a "v2")); (W, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v10") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v10")]);
      (Let (a "v11") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call (CResult (a "v12") L) (Global (a "__GI_____strtoul_l_internal")) [(Arg P (t "v0")); (Arg P (t "v2")); (Arg W (t "v4")); (Arg W (Const 0)); (Arg W (Const 1)); (Arg P (t "v11"))])] (JRet (t "v12")))].

Definition hello_image_fn___isatty_nostatus : func :=
  mkFunc (a "__isatty_nostatus") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P (Alloc 4) [(Const 44)]);
      (Call (CResult (a "v18") W) (Global (a "zsys_ioctl")) [(Arg W (t "v0")); (Arg W (Const 2150388778)); (Arg P (t "v2"))]);
      (Let (a "v19") W (Cmp Eq W) [(t "v18"); (Const 0)])] (JRet (t "v19")))].

Definition hello_image_fn___iswprint : func :=
  mkFunc (a "__iswprint") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v7") W And [(t "v0"); (Const 4294967168)]);
      (Let (a "v8") W (Cmp Eq W) [(t "v7"); (Const 0)])] (JBranch (t "v8") (To (a "iw_1.start")) (To (a "L4"))));
  (mkBlock (a "iw_1.start") [] [(Let (a "iw_1.v0") P Copy [(Global (a "__libc_tsd_CTYPE_B"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "iw_1.v0")]);
      (Let (a "v10") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v12") L (Ext Sw) [(t "v0")]);
      (Let (a "v13") L Shl [(t "v12"); (Const 1)]);
      (Flight (a "v14") Add [(FAddress (t "v10")); (FValue (t "v13"))] (LowerOf (t "v10")));
      (Let (a "chk1") A (Check 0 2 Read 1) [(t "v14")]);
      (Let (a "v15") W (RawLoad (LdNarrow Uh) 0) [(t "chk1")]);
      (Let (a "v16") W And [(t "v15"); (Const 16384)])] (JRet (t "v16")));
  (mkBlock (a "L4") [] [(Let (a "v19") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v19")]);
      (Let (a "v20") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v20")]);
      (Let (a "v22") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Flight (a "v23") Add [(FAddress (t "v22")); (FValue (Const 56))] (LowerOf (t "v22")));
      (Flight (a "v27") Add [(FAddress (t "v23")); (FValue (Const 136))] (LowerOf (t "v23")));
      (Let (a "chk4") A (Check 0 4 Read 1) [(t "v27")]);
      (Let (a "v28") W (RawLoad (LdNarrow Uw) 0) [(t "chk4")]);
      (Let (a "v29") W Add [(t "v28"); (Const 6)]);
      (Let (a "v30") L (Ext Uw) [(t "v29")]);
      (Let (a "v32") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v32")]);
      (Let (a "v33") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk6") A (Check 0 8 Read 8) [(t "v33")]);
      (Let (a "v35") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v36") Add [(FAddress (t "v35")); (FValue (Const 56))] (LowerOf (t "v35")));
      (Let (a "v38") W And [(t "v30"); (Const 65535)]);
      (Let (a "v39") L (Ext Sw) [(t "v38")]);
      (Let (a "v40") L Shl [(t "v39"); (Const 3)]);
      (Flight (a "v41") Add [(FAddress (t "v36")); (FValue (t "v40"))] (LowerOf (t "v36")));
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v41")]);
      (Let (a "v42") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Let (a "chk8") A (Check 0 4 Read 1) [(t "v42")]);
      (Let (a "iw_2.v7") W (RawLoad (LdNarrow Uw) 0) [(t "chk8")]);
      (Let (a "iw_2.v11") W Shr [(t "v0"); (t "iw_2.v7")]);
      (Flight (a "iw_2.v14") Add [(FAddress (t "v42")); (FValue (Const 4))] (LowerOf (t "v42")));
      (Let (a "chk9") A (HalfCheck Upper 0 4 Read 1) [(t "chk8"); (t "iw_2.v14")]);
      (Let (a "iw_2.v15") W (RawLoad (LdNarrow Uw) 0) [(t "chk9")]);
      (Let (a "iw_2.v21") W (Cmp Ult W) [(t "iw_2.v11"); (t "iw_2.v15")])] (JBranch (t "iw_2.v21") (To (a "iw_2.L16")) (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.L16") [] [(Let (a "iw_2.v25") W Add [(t "iw_2.v11"); (Const 5)]);
      (Let (a "iw_2.v26") L (Ext Uw) [(t "iw_2.v25")]);
      (Let (a "iw_2.v27") L Shl [(t "iw_2.v26"); (Const 2)]);
      (Flight (a "iw_2.v28") Add [(FAddress (t "v42")); (FValue (t "iw_2.v27"))] (LowerOf (t "v42")));
      (Let (a "chk10") A (Check 0 4 Read 1) [(t "iw_2.v28")]);
      (Let (a "iw_2.v29") W (RawLoad (LdNarrow Uw) 0) [(t "chk10")]);
      (Let (a "iw_2.v34") W (Cmp Ne W) [(t "iw_2.v29"); (Const 0)])] (JBranch (t "iw_2.v34") (To (a "iw_2.L30")) (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.L30") [] [(Flight (a "iw_2.v37") Add [(FAddress (t "v42")); (FValue (Const 8))] (LowerOf (t "v42")));
      (Let (a "chk11") A (HalfCheck Upper 0 4 Read 1) [(t "chk8"); (t "iw_2.v37")]);
      (Let (a "iw_2.v38") W (RawLoad (LdNarrow Uw) 0) [(t "chk11")]);
      (Flight (a "iw_2.v41") Add [(FAddress (t "v42")); (FValue (Const 12))] (LowerOf (t "v42")));
      (Let (a "chk12") A (HalfCheck Upper 0 4 Read 1) [(t "chk8"); (t "iw_2.v41")]);
      (Let (a "iw_2.v42") W (RawLoad (LdNarrow Uw) 0) [(t "chk12")]);
      (Let (a "iw_2.v46") W Shr [(t "v0"); (t "iw_2.v38")]);
      (Let (a "iw_2.v48") W And [(t "iw_2.v46"); (t "iw_2.v42")]);
      (Let (a "iw_2.v52") L (Ext Uw) [(t "iw_2.v29")]);
      (Flight (a "iw_2.v53") Add [(FAddress (t "v42")); (FValue (t "iw_2.v52"))] (LowerOf (t "v42")));
      (Let (a "iw_2.v55") L (Ext Uw) [(t "iw_2.v48")]);
      (Let (a "iw_2.v56") L Shl [(t "iw_2.v55"); (Const 2)]);
      (Flight (a "iw_2.v57") Add [(FAddress (t "iw_2.v53")); (FValue (t "iw_2.v56"))] (LowerOf (t "iw_2.v53")));
      (Let (a "chk13") A (Check 0 4 Read 1) [(t "iw_2.v57")]);
      (Let (a "iw_2.v58") W (RawLoad (LdNarrow Uw) 0) [(t "chk13")]);
      (Let (a "iw_2.v63") W (Cmp Ne W) [(t "iw_2.v58"); (Const 0)])] (JBranch (t "iw_2.v63") (To (a "iw_2.L59")) (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.L59") [] [(Flight (a "iw_2.v66") Add [(FAddress (t "v42")); (FValue (Const 16))] (LowerOf (t "v42")));
      (Let (a "chk14") A (HalfCheck Upper 0 4 Read 1) [(t "chk8"); (t "iw_2.v66")]);
      (Let (a "iw_2.v67") W (RawLoad (LdNarrow Uw) 0) [(t "chk14")]);
      (Let (a "iw_2.v70") W Shr [(t "v0"); (Const 5)]);
      (Let (a "iw_2.v72") W And [(t "iw_2.v70"); (t "iw_2.v67")]);
      (Let (a "iw_2.v76") L (Ext Uw) [(t "iw_2.v58")]);
      (Flight (a "iw_2.v77") Add [(FAddress (t "v42")); (FValue (t "iw_2.v76"))] (LowerOf (t "v42")));
      (Let (a "iw_2.v79") L (Ext Uw) [(t "iw_2.v72")]);
      (Let (a "iw_2.v80") L Shl [(t "iw_2.v79"); (Const 2)]);
      (Flight (a "iw_2.v81") Add [(FAddress (t "iw_2.v77")); (FValue (t "iw_2.v80"))] (LowerOf (t "iw_2.v77")));
      (Let (a "chk15") A (Check 0 4 Read 1) [(t "iw_2.v81")]);
      (Let (a "iw_2.v82") W (RawLoad (LdNarrow Uw) 0) [(t "chk15")]);
      (Let (a "iw_2.v85") W And [(t "v0"); (Const 31)]);
      (Let (a "iw_2.v86") W Shr [(t "iw_2.v82"); (t "iw_2.v85")]);
      (Let (a "iw_2.v87") W And [(t "iw_2.v86"); (Const 1)])] (JGoto (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.join") [(Phi (a "v45") W [((a "iw_2.L59"), (t "iw_2.v87")); ((a "L4"), (Const 0)); ((a "iw_2.L16"), (Const 0)); ((a "iw_2.L30"), (Const 0))])] [] (JRet (t "v45")))].
