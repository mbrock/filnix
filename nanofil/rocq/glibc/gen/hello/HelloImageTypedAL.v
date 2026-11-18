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

Definition hello_image_fn___alloc_dir : func :=
  mkFunc (a "__alloc_dir") (a "export") (RClass P) [(W, (a "v0")); (W, (a "v2")); (W, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Let (a "v11") W (Ext Ub) [(t "v2")]);
      (Let (a "v12") W (Cmp Eq W) [(t "v11"); (Const 0)])] (JBranch (t "v12") (To (a "L13")) (To (a "L14"))));
  (mkBlock (a "L13") [] [(Call (CResult (a "v16") W) (Global (a "__GI___fcntl64_nocancel")) [(Arg W (t "v0")); (Arg W (Const 2)); (Arg W (Const 1))]);
      (Let (a "v17") W (Cmp Slt W) [(t "v16"); (Const 0)])] (JGoto (To (a "L14"))));
  (mkBlock (a "L14") [(Phi (a "v21") W [((a "start"), (Const 0)); ((a "L13"), (t "v17"))])] [] (JBranch (t "v21") (To (a "L8")) (To (a "L10"))));
  (mkBlock (a "L8") [] [] (JRet (Const 0)));
  (mkBlock (a "L10") [] [(Flight (a "v31") Add [(FAddress (t "v6")); (FValue (Const 56))] (LowerOf (t "v6")));
      (Let (a "chk0") A (Check 0 8 Read 1) [(t "v31")]);
      (Let (a "v32") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v33") W (Cmp Ugt L) [(t "v32"); (Const 32768)])] (JBranch (t "v33") (To (a "L27")) (To (a "L29"))));
  (mkBlock (a "L27") [] [(Flight (a "v35") Add [(FAddress (t "v6")); (FValue (Const 56))] (LowerOf (t "v6")));
      (Let (a "v36") L (RawLoad LdL 0) [(t "chk0")])] (JGoto (To (a "L29"))));
  (mkBlock (a "L29") [(Phi (a "v37") L [((a "L27"), (t "v36")); ((a "L10"), (Const 32768))])] [(Let (a "v38") W (Cmp Ult L) [(t "v37"); (Const 1048576)])] (JBranch (t "v38") (To (a "L24")) (To (a "L26"))));
  (mkBlock (a "L24") [] [(Flight (a "v43") Add [(FAddress (t "v6")); (FValue (Const 56))] (LowerOf (t "v6")));
      (Let (a "v44") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "v45") W (Cmp Ugt L) [(t "v44"); (Const 32768)])] (JBranch (t "v45") (To (a "L39")) (To (a "L26"))));
  (mkBlock (a "L39") [] [(Flight (a "v47") Add [(FAddress (t "v6")); (FValue (Const 56))] (LowerOf (t "v6")));
      (Let (a "v48") L (RawLoad LdL 0) [(t "chk0")])] (JGoto (To (a "L26"))));
  (mkBlock (a "L26") [(Phi (a "v50") L [((a "L39"), (t "v48")); ((a "L24"), (Const 32768)); ((a "L29"), (Const 1048576))])] [(Let (a "v53") L Add [(t "v50"); (Const 48)]);
      (Call (CResult (a "v54") P) (Global (a "malloc")) [(Arg L (t "v53"))]);
      (Let (a "v59") L Ptoi [(t "v54")]);
      (Let (a "v60") L Ptoi [(Const 0)]);
      (Let (a "v61") W (Cmp Eq L) [(t "v59"); (t "v60")])] (JBranch (t "v61") (To (a "L55")) (To (a "L57"))));
  (mkBlock (a "L55") [] [] (JBranch (t "v11") (To (a "L62")) (To (a "L64"))));
  (mkBlock (a "L62") [] [(Call CVoid (Global (a "__GI___close_nocancel_nostatus")) [(Arg W (t "v0"))])] (JGoto (To (a "L64"))));
  (mkBlock (a "L64") [] [] (JRet (Const 0)));
  (mkBlock (a "L57") [] [(Let (a "chk4") A (Check 0 4 Write 1) [(t "v54")]);
      (RawStore Ww 0 (t "v0") (t "chk4"));
      (Flight (a "v71") Add [(FAddress (t "v54")); (FValue (Const 4))] (LowerOf (t "v54")));
      (Let (a "chk5") A (HalfCheck Upper 0 4 Write 1) [(t "chk4"); (t "v71")]);
      (RawStore Ww 0 (Const 0) (t "chk5"));
      (Flight (a "v73") Add [(FAddress (t "v54")); (FValue (Const 8))] (LowerOf (t "v54")));
      (Let (a "chk6") A (HalfCheck Upper 0 8 Write 1) [(t "chk4"); (t "v73")]);
      (RawStore Wl 0 (t "v50") (t "chk6"));
      (Flight (a "v76") Add [(FAddress (t "v54")); (FValue (Const 16))] (LowerOf (t "v54")));
      (Let (a "chk7") A (HalfCheck Upper 0 8 Write 1) [(t "chk4"); (t "v76")]);
      (RawStore Wl 0 (Const 0) (t "chk7"));
      (Flight (a "v78") Add [(FAddress (t "v54")); (FValue (Const 24))] (LowerOf (t "v54")));
      (Let (a "chk8") A (HalfCheck Upper 0 8 Write 1) [(t "chk4"); (t "v78")]);
      (RawStore Wl 0 (Const 0) (t "chk8"));
      (Flight (a "v80") Add [(FAddress (t "v54")); (FValue (Const 32))] (LowerOf (t "v54")));
      (Let (a "chk9") A (HalfCheck Upper 0 8 Write 1) [(t "chk4"); (t "v80")]);
      (RawStore Wl 0 (Const 0) (t "chk9"));
      (Flight (a "v82") Add [(FAddress (t "v54")); (FValue (Const 40))] (LowerOf (t "v54")));
      (Let (a "chk10") A (HalfCheck Upper 0 4 Write 1) [(t "chk4"); (t "v82")]);
      (RawStore Ww 0 (Const 0) (t "chk10"))] (JRet (t "v54")))].

Definition hello_image_fn_glibc_localealias'23alias_compare : func :=
  mkFunc (a "glibc_localealias#alias_compare") (a "local") (RClass W) [(P, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v5") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v7") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "v8") P Copy [(Global (a "_nl_C_locobj"))]);
      (Call (CResult (a "v9") W) (Global (a "__GI___strcasecmp_l")) [(Arg P (t "v5")); (Arg P (t "v7")); (Arg P (t "v8"))])] (JRet (t "v9")))].
