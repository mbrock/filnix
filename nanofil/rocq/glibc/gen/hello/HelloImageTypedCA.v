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

Definition hello_image_fn___GI___call_tls_dtors : func :=
  mkFunc (a "__GI___call_tls_dtors") (a "export") RVoid [] [(mkBlock (a "start") [] [] JRetVoid)].

Definition hello_image_fn___cache_sysconf : func :=
  mkFunc (a "__cache_sysconf") (a "export") (RClass L) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v3") P Copy [(Global (a "_dl_x86_cpu_features"))]);
      (Let (a "v57") W (Cmp Slt W) [(t "v0"); (Const 192)])] (JBranch (t "v57") (To (a "L58")) (To (a "L59"))));
  (mkBlock (a "L7") [] [(Flight (a "v9") Add [(FAddress (t "v3")); (FValue (Const 424))] (LowerOf (t "v3")));
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v9")]);
      (Let (a "v10") L (RawLoad LdL 0) [(t "chk0")])] (JRet (t "v10")));
  (mkBlock (a "L11") [] [(Flight (a "v13") Add [(FAddress (t "v3")); (FValue (Const 432))] (LowerOf (t "v3")));
      (Let (a "chk1") A (Check 0 8 Read 1) [(t "v13")]);
      (Let (a "v14") L (RawLoad LdL 0) [(t "chk1")])] (JRet (t "v14")));
  (mkBlock (a "L15") [] [(Flight (a "v17") Add [(FAddress (t "v3")); (FValue (Const 440))] (LowerOf (t "v3")));
      (Let (a "chk2") A (Check 0 8 Read 1) [(t "v17")]);
      (Let (a "v18") L (RawLoad LdL 0) [(t "chk2")])] (JRet (t "v18")));
  (mkBlock (a "L19") [] [(Flight (a "v21") Add [(FAddress (t "v3")); (FValue (Const 448))] (LowerOf (t "v3")));
      (Let (a "chk3") A (Check 0 8 Read 1) [(t "v21")]);
      (Let (a "v22") L (RawLoad LdL 0) [(t "chk3")])] (JRet (t "v22")));
  (mkBlock (a "L23") [] [(Flight (a "v25") Add [(FAddress (t "v3")); (FValue (Const 456))] (LowerOf (t "v3")));
      (Let (a "chk4") A (Check 0 8 Read 1) [(t "v25")]);
      (Let (a "v26") L (RawLoad LdL 0) [(t "chk4")])] (JRet (t "v26")));
  (mkBlock (a "L27") [] [(Flight (a "v29") Add [(FAddress (t "v3")); (FValue (Const 464))] (LowerOf (t "v3")));
      (Let (a "chk5") A (Check 0 8 Read 1) [(t "v29")]);
      (Let (a "v30") L (RawLoad LdL 0) [(t "chk5")])] (JRet (t "v30")));
  (mkBlock (a "L31") [] [(Flight (a "v33") Add [(FAddress (t "v3")); (FValue (Const 472))] (LowerOf (t "v3")));
      (Let (a "chk6") A (Check 0 8 Read 1) [(t "v33")]);
      (Let (a "v34") L (RawLoad LdL 0) [(t "chk6")])] (JRet (t "v34")));
  (mkBlock (a "L35") [] [(Flight (a "v37") Add [(FAddress (t "v3")); (FValue (Const 480))] (LowerOf (t "v3")));
      (Let (a "chk7") A (Check 0 8 Read 1) [(t "v37")]);
      (Let (a "v38") L (RawLoad LdL 0) [(t "chk7")])] (JRet (t "v38")));
  (mkBlock (a "L39") [] [(Flight (a "v41") Add [(FAddress (t "v3")); (FValue (Const 488))] (LowerOf (t "v3")));
      (Let (a "chk8") A (Check 0 8 Read 1) [(t "v41")]);
      (Let (a "v42") L (RawLoad LdL 0) [(t "chk8")])] (JRet (t "v42")));
  (mkBlock (a "L43") [] [(Flight (a "v45") Add [(FAddress (t "v3")); (FValue (Const 496))] (LowerOf (t "v3")));
      (Let (a "chk9") A (Check 0 8 Read 1) [(t "v45")]);
      (Let (a "v46") L (RawLoad LdL 0) [(t "chk9")])] (JRet (t "v46")));
  (mkBlock (a "L47") [] [(Flight (a "v49") Add [(FAddress (t "v3")); (FValue (Const 504))] (LowerOf (t "v3")));
      (Let (a "chk10") A (Check 0 8 Read 1) [(t "v49")]);
      (Let (a "v50") L (RawLoad LdL 0) [(t "chk10")])] (JRet (t "v50")));
  (mkBlock (a "L51") [] [(Flight (a "v53") Add [(FAddress (t "v3")); (FValue (Const 512))] (LowerOf (t "v3")));
      (Let (a "chk11") A (Check 0 8 Read 1) [(t "v53")]);
      (Let (a "v54") L (RawLoad LdL 0) [(t "chk11")])] (JRet (t "v54")));
  (mkBlock (a "L58") [] [(Let (a "v60") W (Cmp Slt W) [(t "v0"); (Const 189)])] (JBranch (t "v60") (To (a "L61")) (To (a "L62"))));
  (mkBlock (a "L61") [] [(Let (a "v63") W (Cmp Eq W) [(t "v0"); (Const 185)])] (JBranch (t "v63") (Poll (a "L7")) (To (a "L64"))));
  (mkBlock (a "L64") [] [(Let (a "v65") W (Cmp Eq W) [(t "v0"); (Const 187)])] (JBranch (t "v65") (Poll (a "L11")) (To (a "L66"))));
  (mkBlock (a "L66") [] [(Let (a "v67") W (Cmp Eq W) [(t "v0"); (Const 188)])] (JBranch (t "v67") (Poll (a "L15")) (To (a "L6"))));
  (mkBlock (a "L62") [] [(Let (a "v69") W (Cmp Eq W) [(t "v0"); (Const 189)])] (JBranch (t "v69") (Poll (a "L19")) (To (a "L70"))));
  (mkBlock (a "L70") [] [(Let (a "v71") W (Cmp Eq W) [(t "v0"); (Const 190)])] (JBranch (t "v71") (Poll (a "L23")) (To (a "L72"))));
  (mkBlock (a "L72") [] [(Let (a "v73") W (Cmp Eq W) [(t "v0"); (Const 191)])] (JBranch (t "v73") (Poll (a "L27")) (To (a "L6"))));
  (mkBlock (a "L59") [] [(Let (a "v75") W (Cmp Slt W) [(t "v0"); (Const 195)])] (JBranch (t "v75") (To (a "L76")) (To (a "L77"))));
  (mkBlock (a "L76") [] [(Let (a "v78") W (Cmp Eq W) [(t "v0"); (Const 192)])] (JBranch (t "v78") (Poll (a "L31")) (To (a "L79"))));
  (mkBlock (a "L79") [] [(Let (a "v80") W (Cmp Eq W) [(t "v0"); (Const 193)])] (JBranch (t "v80") (Poll (a "L35")) (To (a "L81"))));
  (mkBlock (a "L81") [] [(Let (a "v82") W (Cmp Eq W) [(t "v0"); (Const 194)])] (JBranch (t "v82") (Poll (a "L39")) (To (a "L6"))));
  (mkBlock (a "L77") [] [(Let (a "v84") W (Cmp Eq W) [(t "v0"); (Const 195)])] (JBranch (t "v84") (Poll (a "L43")) (To (a "L85"))));
  (mkBlock (a "L85") [] [(Let (a "v86") W (Cmp Eq W) [(t "v0"); (Const 196)])] (JBranch (t "v86") (Poll (a "L47")) (To (a "L87"))));
  (mkBlock (a "L87") [] [(Let (a "v88") W (Cmp Eq W) [(t "v0"); (Const 197)])] (JBranch (t "v88") (Poll (a "L51")) (To (a "L6"))));
  (mkBlock (a "L6") [] [] (JRet (Const 18446744073709551615)))].
