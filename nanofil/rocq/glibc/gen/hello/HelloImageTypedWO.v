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

Definition hello_image_fn___GI___woverflow : func :=
  mkFunc (a "__GI___woverflow") (a "export") (RClass W) [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Flight (a "v8") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v8")]);
      (Let (a "v9") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v10") W (Cmp Eq W) [(t "v9"); (Const 0)])] (JBranch (t "v10") (To (a "L36")) (To (a "L6"))));
  (mkBlock (a "L36") [] [(Call (CResult (a "v53") W) (Global (a "_IO_fwide")) [(Arg P (t "v0")); (Arg W (Const 1))])] (JGoto (To (a "L6"))));
  (mkBlock (a "L6") [] [(Flight (a "v56") Add [(FAddress (t "v0")); (FValue (Const 216))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v56")]);
      (Let (a "v57") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "iw_1.v4") L Ptoi [(t "v57")]);
      (Let (a "iw_1.v7") P Copy [(Global (a "__io_vtables"))]);
      (Let (a "iw_1.v8") L Ptoi [(t "iw_1.v7")]);
      (Let (a "iw_1.v9") L Sub [(t "iw_1.v4"); (t "iw_1.v8")]);
      (Let (a "iw_1.v15") W (Cmp Uge L) [(t "iw_1.v9"); (Const 2352)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L10")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Call CVoid (Global (a "_IO_vtable_check")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v59") Add [(FAddress (t "v57")); (FValue (Const 24))] (LowerOf (t "v57")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v59")]);
      (Let (a "v60") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "chk3") F CheckFunction [(t "v60")]);
      (RawCall (CResult (a "v63") W) (t "chk3") [(Arg P (t "v0")); (Arg W (t "v2"))])] (JRet (t "v63")))].
