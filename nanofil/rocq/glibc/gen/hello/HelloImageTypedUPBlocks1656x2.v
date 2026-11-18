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

Definition hello_image_fn_glibc_libc_start'23update_active'blocks2 : list block :=
  [(mkBlock (a "iw_1.L2") [] [(Flight (a "iw_1.v12") Add [(FAddress (t "v0")); (FValue (Const 20))] (LowerOf (t "v0")));
      (Flight (a "iw_1.v13") Add [(FAddress (t "iw_1.v12")); (FValue (Const 32))] (LowerOf (t "iw_1.v12")));
      (Flight (a "iw_1.v14") Add [(FAddress (t "iw_1.v13")); (FValue (Const 16))] (LowerOf (t "iw_1.v13")));
      (Flight (a "iw_1.v15") Add [(FAddress (t "iw_1.v14")); (FValue (Const 4))] (LowerOf (t "iw_1.v14")));
      (Let (a "chk348") A (Renew 0 4 Read 1) [(t "chk57"); (t "iw_1.v15")]);
      (Let (a "iw_1.v16") W (RawLoad (LdNarrow Uw) 0) [(t "chk348")]);
      (Flight (a "iw_1.v20") Add [(FAddress (t "iw_1.v13")); (FValue (Const 4))] (LowerOf (t "iw_1.v13")));
      (Let (a "chk349") A (HalfCheck Upper 0 4 Read 1) [(t "chk0"); (t "iw_1.v20")]);
      (Let (a "iw_1.v21") W (RawLoad (LdNarrow Uw) 0) [(t "chk349")]);
      (Let (a "iw_1.v23") W And [(t "iw_1.v21"); (Const 1)]);
      (Let (a "iw_1.v24") W Or [(t "iw_1.v16"); (t "iw_1.v23")]);
      (Let (a "chk350") A (Renew 0 4 Write 1) [(t "chk57"); (t "iw_1.v15")]);
      (RawStore Ww 0 (t "iw_1.v24") (t "chk350"))] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v1765") Add [(FAddress (t "v0")); (FValue (Const 344))] (LowerOf (t "v0")));
      (Call (CResult (a "v1767") W) (Global (a "glibc_libc_start#get_isa_level")) [(Arg P (t "v0"))]);
      (Let (a "chk351") A (HalfCheck Upper 0 4 Write 1) [(t "chk0"); (t "v1765")]);
      (RawStore Ww 0 (t "v1767") (t "chk351"))] JRetVoid)].
