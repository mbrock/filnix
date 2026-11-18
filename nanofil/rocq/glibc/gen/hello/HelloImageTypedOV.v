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

Definition hello_image_fn___GI___overflow : func :=
  mkFunc (a "__GI___overflow") (a "export") (RClass W) [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Flight (a "v8") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v8")]);
      (Let (a "v9") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v10") W (Cmp Eq W) [(t "v9"); (Const 0)])] (JBranch (t "v10") (To (a "L13")) (To (a "L6"))));
  (mkBlock (a "L13") [] [(Flight (a "v27") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v28") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v29") W (Cmp Eq W) [(t "v28"); (Const 0)])] (JBranch (t "v29") (To (a "L23")) (To (a "L25"))));
  (mkBlock (a "L23") [] [(Flight (a "v31") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk2") A (Renew 0 4 Write 1) [(t "chk0"); (t "v31")]);
      (RawStore Ww 0 (Const 4294967295) (t "chk2"))] (JGoto (To (a "L25"))));
  (mkBlock (a "L25") [] [(Flight (a "v34") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v35") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")])] (JGoto (To (a "L6"))));
  (mkBlock (a "L6") [] [(Flight (a "v58") Add [(FAddress (t "v0")); (FValue (Const 216))] (LowerOf (t "v0")));
      (Let (a "chk4") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v58")]);
      (Let (a "v59") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "iw_1.v4") L Ptoi [(t "v59")]);
      (Let (a "iw_1.v7") P Copy [(Global (a "__io_vtables"))]);
      (Let (a "iw_1.v8") L Ptoi [(t "iw_1.v7")]);
      (Let (a "iw_1.v9") L Sub [(t "iw_1.v4"); (t "iw_1.v8")]);
      (Let (a "iw_1.v15") W (Cmp Uge L) [(t "iw_1.v9"); (Const 2352)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L10")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Call CVoid (Global (a "_IO_vtable_check")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v61") Add [(FAddress (t "v59")); (FValue (Const 24))] (LowerOf (t "v59")));
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v61")]);
      (Let (a "v62") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "chk6") F CheckFunction [(t "v62")]);
      (RawCall (CResult (a "v65") W) (t "chk6") [(Arg P (t "v0")); (Arg W (t "v2"))])] (JRet (t "v65")))].
