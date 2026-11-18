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

Definition hi_fn_hi_atexit'23close_stdout_hi : func :=
  mkFunc (a "hi_atexit#close_stdout_hi") (a "local") RVoid [] [(mkBlock (a "start") [] [(Let (a "v1") P Copy [(Global (a "stdout"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v1")]);
      (Let (a "v2") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Call (CResult (a "v3") W) (Global (a "__fpending")) [(Arg P (t "v2"))]);
      (Let (a "v4") W (Cmp Ne W) [(t "v3"); (Const 0)]);
      (Let (a "v6") P Copy [(Global (a "stdout"))]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v6")]);
      (Let (a "v7") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Call (CResult (a "v8") W) (Global (a "ferror")) [(Arg P (t "v7"))]);
      (Let (a "v9") W (Cmp Ne W) [(t "v8"); (Const 0)]);
      (Let (a "v11") P Copy [(Global (a "stdout"))]);
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v11")]);
      (Let (a "v12") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Call (CResult (a "v13") W) (Global (a "fclose")) [(Arg P (t "v12"))]);
      (Let (a "v14") W (Cmp Ne W) [(t "v13"); (Const 0)])] (JBranch (t "v9") (To (a "L20")) (To (a "L19"))));
  (mkBlock (a "L19") [] [] (JGoto (To (a "L20"))));
  (mkBlock (a "L20") [(Phi (a "v23") W [((a "start"), (Const 1)); ((a "L19"), (t "v14"))])] [] (JBranch (t "v23") (To (a "L15")) (To (a "L17"))));
  (mkBlock (a "L15") [] [] (JBranch (t "v4") (To (a "L29")) (To (a "L28"))));
  (mkBlock (a "L28") [] [] (JGoto (To (a "L29"))));
  (mkBlock (a "L29") [(Phi (a "v32") W [((a "L15"), (Const 1)); ((a "L28"), (t "v14"))])] [] (JBranch (t "v32") (To (a "L24")) (To (a "L17"))));
  (mkBlock (a "L24") [] [(Call CVoid (Global (a "_exit")) [(Arg W (Const 1))])] (JGoto (To (a "L17"))));
  (mkBlock (a "L17") [] [] JRetVoid)].

Definition hi_fn___GI___close_nocancel : func :=
  mkFunc (a "__GI___close_nocancel") (a "export") (RClass W) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Call (CResult (a "v3") W) (Global (a "zsys_close")) [(Arg W (t "v0"))])] (JRet (t "v3")))].

Definition hi_fn___GI___clock_gettime : func :=
  mkFunc (a "__GI___clock_gettime") (a "export") (RClass W) [(W, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Call (CResult (a "v6") W) (Global (a "zsys_clock_gettime")) [(Arg W (t "v0")); (Arg P (t "v2"))])] (JRet (t "v6")))].
