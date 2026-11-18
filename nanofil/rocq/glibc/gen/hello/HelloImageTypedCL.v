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

Definition hello_image_fn_close_stream : func :=
  mkFunc (a "close_stream") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v4") L) (Global (a "__fpending")) [(Arg P (t "v0"))]);
      (Let (a "v5") W (Cmp Ne L) [(t "v4"); (Const 0)]);
      (Call (CResult (a "v9") W) (Global (a "ferror")) [(Arg P (t "v0"))]);
      (Let (a "v10") W (Cmp Ne W) [(t "v9"); (Const 0)]);
      (Call (CResult (a "v14") W) (Global (a "fclose")) [(Arg P (t "v0"))]);
      (Let (a "v15") W (Cmp Ne W) [(t "v14"); (Const 0)])] (JBranch (t "v10") (To (a "L22")) (To (a "L21"))));
  (mkBlock (a "L21") [] [] (JBranch (t "v15") (To (a "L24")) (To (a "L22"))));
  (mkBlock (a "L24") [] [] (JBranch (t "v5") (To (a "L22")) (To (a "L27"))));
  (mkBlock (a "L27") [] [(Call (CResult (a "v29") P) (Global (a "__errno_location")) []);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v29")]);
      (Let (a "v30") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v31") W (Cmp Ne W) [(t "v30"); (Const 9)])] (JGoto (To (a "L22"))));
  (mkBlock (a "L22") [(Phi (a "v37") W [((a "start"), (Const 1)); ((a "L21"), (Const 0)); ((a "L24"), (Const 1)); ((a "L27"), (t "v31"))])] [] (JBranch (t "v37") (To (a "L17")) (To (a "L19"))));
  (mkBlock (a "L17") [] [(Let (a "v42") W (Cmp Eq W) [(t "v14"); (Const 0)])] (JBranch (t "v42") (To (a "L38")) (To (a "L40"))));
  (mkBlock (a "L38") [] [(Call (CResult (a "v43") P) (Global (a "__errno_location")) []);
      (Let (a "chk1") A (Check 0 4 Write 1) [(t "v43")]);
      (RawStore Ww 0 (Const 0) (t "chk1"))] (JGoto (To (a "L40"))));
  (mkBlock (a "L40") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L19") [] [] (JRet (Const 0)))].

Definition hello_image_fn_close_stdout : func :=
  mkFunc (a "close_stdout") (a "export") RVoid [] [(mkBlock (a "start") [] [(Let (a "v3") P Copy [(Global (a "stdout"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v3")]);
      (Let (a "v4") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call (CResult (a "v5") W) (Global (a "close_stream")) [(Arg P (t "v4"))]);
      (Let (a "v6") W (Cmp Ne W) [(t "v5"); (Const 0)])] (JBranch (t "v6") (To (a "L7")) (To (a "L8"))));
  (mkBlock (a "L7") [] [(Let (a "v9") P Copy [(Global (a "closeout#ignore_EPIPE"))]);
      (Let (a "chk1") A (Check 0 1 Read 1) [(t "v9")]);
      (Let (a "v10") W (RawLoad (LdNarrow Ub) 0) [(t "chk1")])] (JBranch (t "v10") (To (a "L11")) (To (a "L12"))));
  (mkBlock (a "L11") [] [(Call (CResult (a "v13") P) (Global (a "__errno_location")) []);
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "v13")]);
      (Let (a "v14") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v15") W (Cmp Eq W) [(t "v14"); (Const 32)])] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [(Phi (a "v17") W [((a "L7"), (Const 0)); ((a "L11"), (t "v15"))])] [(Let (a "v18") W (Cmp Eq W) [(t "v17"); (Const 0)])] (JGoto (To (a "L8"))));
  (mkBlock (a "L8") [(Phi (a "v20") W [((a "start"), (Const 0)); ((a "L12"), (t "v18"))])] [] (JBranch (t "v20") (To (a "L0")) (To (a "L91"))));
  (mkBlock (a "L0") [] [(Let (a "v22") P Copy [(Global (a "closeout#str.52"))]);
      (Let (a "v23") P Copy [(Global (a "closeout#str.53"))]);
      (Let (a "v27") P Copy [(Global (a "closeout#file_name"))]);
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v27")]);
      (Let (a "v28") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Let (a "v29") L Ptoi [(t "v28")]);
      (Let (a "v30") W (Cmp Ne L) [(t "v29"); (Const 0)])] (JBranch (t "v30") (To (a "L31")) (To (a "L61"))));
  (mkBlock (a "L31") [] [(Call (CResult (a "v34") P) (Global (a "__errno_location")) []);
      (Let (a "chk4") A (Check 0 4 Read 1) [(t "v34")]);
      (Let (a "v35") W (RawLoad (LdNarrow Sw) 0) [(t "chk4")]);
      (Let (a "v36") P Copy [(Global (a "closeout#str.54"))]);
      (Let (a "v37") P Copy [(Global (a "closeout#file_name"))]);
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v37")]);
      (Let (a "v38") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Call (CResult (a "v39") P) (Global (a "quotearg_colon")) [(Arg P (t "v38"))]);
      (Call CVoid (Global (a "error")) [(Arg W (Const 0)); (Arg W (t "v35")); (Arg P (t "v36")); (Arg P (t "v39")); (Arg P (t "v23"))])] (JGoto (To (a "L26"))));
  (mkBlock (a "L61") [] [(Call (CResult (a "v64") P) (Global (a "__errno_location")) []);
      (Let (a "chk6") A (Check 0 4 Read 1) [(t "v64")]);
      (Let (a "v65") W (RawLoad (LdNarrow Sw) 0) [(t "chk6")]);
      (Let (a "v66") P Copy [(Global (a "closeout#str.55"))]);
      (Call CVoid (Global (a "error")) [(Arg W (Const 0)); (Arg W (t "v65")); (Arg P (t "v66")); (Arg P (t "v23"))])] (JGoto (To (a "L26"))));
  (mkBlock (a "L26") [] [(Let (a "v85") P Copy [(Global (a "exit_failure"))]);
      (Let (a "chk7") A (Check 0 4 Read 1) [(t "v85")]);
      (Let (a "v86") W (RawLoad (LdNarrow Sw) 0) [(t "chk7")]);
      (Call CVoid (Global (a "_exit")) [(Arg W (t "v86"))])] (JGoto (To (a "L91"))));
  (mkBlock (a "L91") [] [(Let (a "v93") P Copy [(Global (a "stderr"))]);
      (Let (a "chk8") A (Check 0 8 Read 8) [(t "v93")]);
      (Let (a "v94") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Call (CResult (a "v95") W) (Global (a "close_stream")) [(Arg P (t "v94"))]);
      (Let (a "v96") W (Cmp Ne W) [(t "v95"); (Const 0)])] (JBranch (t "v96") (To (a "L87")) (To (a "L89"))));
  (mkBlock (a "L87") [] [(Let (a "v99") P Copy [(Global (a "exit_failure"))]);
      (Let (a "chk9") A (Check 0 4 Read 1) [(t "v99")]);
      (Let (a "v100") W (RawLoad (LdNarrow Sw) 0) [(t "chk9")]);
      (Call CVoid (Global (a "_exit")) [(Arg W (t "v100"))])] (JGoto (To (a "L89"))));
  (mkBlock (a "L89") [] [] JRetVoid)].

Definition hello_image_fn___closedir : func :=
  mkFunc (a "__closedir") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v7") L Ptoi [(t "v0")]);
      (Let (a "v8") L Ptoi [(Const 0)]);
      (Let (a "v9") W (Cmp Eq L) [(t "v7"); (t "v8")])] (JBranch (t "v9") (To (a "L3")) (To (a "L5"))));
  (mkBlock (a "L3") [] [(Let (a "v10") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk0") A (Check 0 4 Write 1) [(t "v10")]);
      (RawStore Ww 0 (Const 22) (t "chk0"))] (JRet (Const 4294967295)));
  (mkBlock (a "L5") [] [(Let (a "chk1") A (Check 0 4 Read 1) [(t "v0")]);
      (Let (a "v14") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")]);
      (Call CVoid (Global (a "free")) [(Arg P (t "v0"))]);
      (Call (CResult (a "v17") W) (Global (a "__GI___close_nocancel")) [(Arg W (t "v14"))])] (JRet (t "v17")))].

Definition hello_image_fn___GI___close_nocancel : func :=
  mkFunc (a "__GI___close_nocancel") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") W) (Global (a "zsys_close")) [(Arg W (t "v0"))])] (JRet (t "v3")))].

Definition hello_image_fn___GI___close_nocancel_nostatus : func :=
  mkFunc (a "__GI___close_nocancel_nostatus") (a "export") RVoid [(W, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") W) (Global (a "zsys_close")) [(Arg W (t "v0"))])] JRetVoid)].

Definition hello_image_fn_glibc_pthread_once'23clear_once_control : func :=
  mkFunc (a "glibc_pthread_once#clear_once_control") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 4 Write 1) [(t "v0")]);
      (RawStore Ww 0 (Const 0) (t "chk0"));
      (Call CVoid (Global (a "zsys_futex_wake")) [(Arg P (t "v0")); (Arg W (Const 2147483647)); (Arg W (Const 1))])] JRetVoid)].

Definition hello_image_fn___GI___clock_gettime : func :=
  mkFunc (a "__GI___clock_gettime") (a "export") (RClass W) [(W, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Call (CResult (a "v6") W) (Global (a "zsys_clock_gettime")) [(Arg W (t "v0")); (Arg P (t "v2"))])] (JRet (t "v6")))].
