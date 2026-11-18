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

Definition hello_image_fn___GI___tfind : func :=
  mkFunc (a "__GI___tfind") (a "export") (RClass P) [(P, (a "v0")); (P, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "v13") L Ptoi [(t "v2")]);
      (Let (a "v14") L Ptoi [(Const 0)]);
      (Let (a "v15") W (Cmp Eq L) [(t "v13"); (t "v14")])] (JBranch (t "v15") (To (a "L9")) (To (a "L11"))));
  (mkBlock (a "L9") [] [] (JRet (Const 0)));
  (mkBlock (a "L11") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v18") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")])] (JGoto (To (a "L19"))));
  (mkBlock (a "L19") [(Phi (a "pr.1") P [((a "L11"), (t "v2")); ((a "L42"), (t "v48")); ((a "L43"), (t "v50"))])] [(Let (a "chk1") A (Check 0 8 Read 8) [(t "pr.1")]);
      (Let (a "v23") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "v24") L Ptoi [(t "v23")]);
      (Let (a "v26") W (Cmp Ne L) [(t "v24"); (t "v14")])] (JBranch (t "v26") (To (a "L20")) (To (a "L21"))));
  (mkBlock (a "L20") [] [(Let (a "v28") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v28")]);
      (Let (a "v33") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Let (a "chk4") F CheckFunction [(t "v4")]);
      (RawCall (CResult (a "v34") W) (t "chk4") [(Arg P (t "v0")); (Arg P (t "v33"))]);
      (Let (a "v39") W (Cmp Eq W) [(t "v34"); (Const 0)])] (JBranch (t "v39") (To (a "L35")) (To (a "L37"))));
  (mkBlock (a "L35") [] [] (JRet (t "v28")));
  (mkBlock (a "L37") [] [(Let (a "v46") W (Cmp Slt W) [(t "v34"); (Const 0)])] (JBranch (t "v46") (To (a "L42")) (To (a "L43"))));
  (mkBlock (a "L42") [] [(Flight (a "v48") Add [(FAddress (t "v28")); (FValue (Const 8))] (LowerOf (t "v28")))] (JGoto (Poll (a "L19"))));
  (mkBlock (a "L43") [] [(Flight (a "v50") Add [(FAddress (t "v28")); (FValue (Const 16))] (LowerOf (t "v28")))] (JGoto (Poll (a "L19"))));
  (mkBlock (a "L21") [] [] (JRet (Const 0)))].
