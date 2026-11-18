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

Definition hi_fn___fpending : func :=
  mkFunc (a "__fpending") (a "export") (RClass L) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v6") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v6")]);
      (Let (a "v7") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v8") W (Cmp Sgt W) [(t "v7"); (Const 0)])] (JBranch (t "v8") (To (a "L2")) (To (a "L3"))));
  (mkBlock (a "L2") [] [(Flight (a "v10") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v10")]);
      (Let (a "v11") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v12") Add [(FAddress (t "v11")); (FValue (Const 32))] (LowerOf (t "v11")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v12")]);
      (Let (a "v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v16") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v17") Add [(FAddress (t "v16")); (FValue (Const 24))] (LowerOf (t "v16")));
      (Let (a "chk4") A (Check 0 8 Read 8) [(t "v17")]);
      (Let (a "v18") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "v19") L Ptoi [(t "v13")]);
      (Let (a "v20") L Ptoi [(t "v18")]);
      (Let (a "v21") L Sub [(t "v19"); (t "v20")]);
      (Let (a "v22") L Div [(t "v21"); (Const 4)])] (JRet (t "v22")));
  (mkBlock (a "L3") [] [(Flight (a "v25") Add [(FAddress (t "v0")); (FValue (Const 40))] (LowerOf (t "v0")));
      (Let (a "chk5") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v25")]);
      (Let (a "v26") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v28") Add [(FAddress (t "v0")); (FValue (Const 32))] (LowerOf (t "v0")));
      (Let (a "chk6") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v28")]);
      (Let (a "v29") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v30") L Ptoi [(t "v26")]);
      (Let (a "v31") L Ptoi [(t "v29")]);
      (Let (a "v32") L Sub [(t "v30"); (t "v31")])] (JRet (t "v32")))].
