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

Definition hello_image_fn_glibc_printf_fphex'23__printf_fphex_buffer'blocks2 : list block :=
  [(mkBlock (a "iw_28.L4") [] [(Flight (a "iw_28.v17") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "iw_28.v18") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk126")]);
      (Flight (a "iw_28.v19") Add [(FAddress (t "iw_28.v18")); (FValue (Const 1))] (LowerOf (t "iw_28.v18")));
      (Let (a "chk129") A (Renew 0 8 Write 8) [(t "chk106"); (t "iw_28.v17")]);
      (RawStorePointer 0 (t "iw_28.v19") (t "chk129") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk130") A (Check 0 1 Write 1) [(t "iw_28.v18")]);
      (RawStore Wb 0 (t "v993") (t "chk130"))] (JGoto (To (a "L983"))));
  (mkBlock (a "iw_28.L5") [] [(Call CVoid (Global (a "__printf_buffer_putc_1")) [(Arg P (t "v0")); (Arg W (t "v993"))])] (JGoto (To (a "L983"))));
  (mkBlock (a "L983") [] [] (JBranch (t "pr.25") (To (a "L1007")) (To (a "L1006"))));
  (mkBlock (a "L1006") [] [] (JGoto (To (a "L1007"))));
  (mkBlock (a "L1007") [(Phi (a "v1009") W [((a "L1006"), (Const 43)); ((a "L983"), (Const 45))])] [(Let (a "v1010") W (Ext Sb) [(t "v1009")]);
      (Flight (a "iw_30.v8") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk131") A (Renew 0 8 Read 8) [(t "chk106"); (t "iw_30.v8")]);
      (Let (a "iw_30.v9") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk131")]);
      (Flight (a "iw_30.v11") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk132") A (Renew 0 8 Read 8) [(t "chk107"); (t "iw_30.v11")]);
      (Let (a "iw_30.v12") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk132")]);
      (Let (a "iw_30.v13") L Ptoi [(t "iw_30.v9")]);
      (Let (a "iw_30.v14") L Ptoi [(t "iw_30.v12")]);
      (Let (a "iw_30.v15") W (Cmp Ne L) [(t "iw_30.v13"); (t "iw_30.v14")])] (JBranch (t "iw_30.v15") (To (a "iw_30.L4")) (To (a "iw_30.L5"))));
  (mkBlock (a "iw_30.L4") [] [(Flight (a "iw_30.v17") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "iw_30.v18") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk131")]);
      (Flight (a "iw_30.v19") Add [(FAddress (t "iw_30.v18")); (FValue (Const 1))] (LowerOf (t "iw_30.v18")));
      (Let (a "chk134") A (Renew 0 8 Write 8) [(t "chk106"); (t "iw_30.v17")]);
      (RawStorePointer 0 (t "iw_30.v19") (t "chk134") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk135") A (Check 0 1 Write 1) [(t "iw_30.v18")]);
      (RawStore Wb 0 (t "v1010") (t "chk135"))] (JGoto (To (a "iw_30.join"))));
  (mkBlock (a "iw_30.L5") [] [(Call CVoid (Global (a "__printf_buffer_putc_1")) [(Arg P (t "v0")); (Arg W (t "v1010"))])] (JGoto (To (a "iw_30.join"))));
  (mkBlock (a "iw_30.join") [] [(Flight (a "v1013") Add [(FAddress (t "v26")); (FValue (Const 5))] (LowerOf (t "v26")));
      (Let (a "v1015") L Ptoi [(t "v1013")]);
      (Let (a "v1017") L Sub [(t "v1015"); (t "v817")]);
      (Call CVoid (Global (a "__printf_buffer_write")) [(Arg P (t "v0")); (Arg P (t "v786")); (Arg L (t "v1017"))]);
      (Flight (a "v1022") Add [(FAddress (t "v4")); (FValue (Const 12))] (LowerOf (t "v4")));
      (Let (a "chk136") A (Renew 0 4 Read 1) [(t "chk0"); (t "v1022")]);
      (Let (a "v1023") W (RawLoad (LdNarrow Uw) 0) [(t "chk136")]);
      (Let (a "v1024") W Shl [(t "v1023"); (Const 26)]);
      (Let (a "v1025") W Shr [(t "v1024"); (Const 31)])] (JBranch (t "v1025") (To (a "L1026")) (To (a "L1027"))));
  (mkBlock (a "L1026") [] [(Flight (a "v1029") Add [(FAddress (t "v4")); (FValue (Const 16))] (LowerOf (t "v4")));
      (Let (a "chk137") A (HalfCheck Upper 0 4 Read 1) [(t "chk0"); (t "v1029")]);
      (Let (a "v1030") W (RawLoad (LdNarrow Sw) 0) [(t "chk137")]);
      (Let (a "v1031") W (Cmp Ne W) [(t "v1030"); (Const 48)])] (JGoto (To (a "L1027"))));
  (mkBlock (a "L1027") [(Phi (a "v1033") W [((a "iw_30.join"), (Const 0)); ((a "L1026"), (t "v1031"))])] [] (JBranch (t "v1033") (To (a "L1018")) (To (a "L1020"))));
  (mkBlock (a "L1018") [] [(Flight (a "v1036") Add [(FAddress (t "v4")); (FValue (Const 16))] (LowerOf (t "v4")));
      (Let (a "chk138") A (HalfCheck Upper 0 4 Read 1) [(t "chk0"); (t "v1036")]);
      (Let (a "v1037") W (RawLoad (LdNarrow Sw) 0) [(t "chk138")]);
      (Let (a "v1038") W (Ext Sb) [(t "v1037")]);
      (Let (a "v1040") L (Ext Sw) [(t "pr.59")]);
      (Let (a "iw_31.v10") W (Cmp Sgt L) [(t "v1040"); (Const 0)])] (JBranch (t "iw_31.v10") (To (a "iw_31.L6")) (To (a "L1020"))));
  (mkBlock (a "iw_31.L6") [] [(Call CVoid (Global (a "__printf_buffer_pad_1")) [(Arg P (t "v0")); (Arg W (t "v1038")); (Arg L (t "v1040"))])] (JGoto (To (a "L1020"))));
  (mkBlock (a "L1020") [] [] JRetVoid)].
