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

Definition hello_image_fn___ctype_b_loc : func :=
  mkFunc (a "__ctype_b_loc") (a "export") (RClass P) [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "__libc_tsd_CTYPE_B"))])] (JRet (t "v0")))].

Definition hello_image_fn___GI___ctype_init : func :=
  mkFunc (a "__GI___ctype_init") (a "export") RVoid [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "__libc_tsd_CTYPE_B"))]);
      (Let (a "v1") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v1")]);
      (Let (a "v2") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v4") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v5") Add [(FAddress (t "v4")); (FValue (Const 56))] (LowerOf (t "v4")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v5")]);
      (Let (a "v10") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Flight (a "v11") Add [(FAddress (t "v10")); (FValue (Const 256))] (LowerOf (t "v10")));
      (Let (a "chk3") A (Check 0 8 Write 8) [(t "v0")]);
      (RawStorePointer 0 (t "v11") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v12") P Copy [(Global (a "__libc_tsd_CTYPE_TOUPPER"))]);
      (Let (a "v13") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk4") A (Check 0 8 Read 8) [(t "v13")]);
      (Let (a "v14") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v14")]);
      (Let (a "v16") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Flight (a "v17") Add [(FAddress (t "v16")); (FValue (Const 56))] (LowerOf (t "v16")));
      (Flight (a "v21") Add [(FAddress (t "v17")); (FValue (Const 8))] (LowerOf (t "v17")));
      (Let (a "chk6") A (Check 0 8 Read 8) [(t "v21")]);
      (Let (a "v22") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Flight (a "v23") Add [(FAddress (t "v22")); (FValue (Const 512))] (LowerOf (t "v22")));
      (Let (a "chk7") A (Check 0 8 Write 8) [(t "v12")]);
      (RawStorePointer 0 (t "v23") (t "chk7") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v24") P Copy [(Global (a "__libc_tsd_CTYPE_TOLOWER"))]);
      (Let (a "v25") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk8") A (Check 0 8 Read 8) [(t "v25")]);
      (Let (a "v26") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk9") A (Check 0 8 Read 8) [(t "v26")]);
      (Let (a "v28") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Flight (a "v29") Add [(FAddress (t "v28")); (FValue (Const 56))] (LowerOf (t "v28")));
      (Flight (a "v33") Add [(FAddress (t "v29")); (FValue (Const 24))] (LowerOf (t "v29")));
      (Let (a "chk10") A (Check 0 8 Read 8) [(t "v33")]);
      (Let (a "v34") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")]);
      (Flight (a "v35") Add [(FAddress (t "v34")); (FValue (Const 512))] (LowerOf (t "v34")));
      (Let (a "chk11") A (Check 0 8 Write 8) [(t "v24")]);
      (RawStorePointer 0 (t "v35") (t "chk11") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] JRetVoid)].

Definition hello_image_fn___ctype_get_mb_cur_max : func :=
  mkFunc (a "__ctype_get_mb_cur_max") (a "weak") (RClass L) [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v1") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v1")]);
      (Let (a "v3") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Flight (a "v4") Add [(FAddress (t "v3")); (FValue (Const 56))] (LowerOf (t "v3")));
      (Flight (a "v8") Add [(FAddress (t "v4")); (FValue (Const 104))] (LowerOf (t "v4")));
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "v8")]);
      (Let (a "v9") W (RawLoad (LdNarrow Uw) 0) [(t "chk2")]);
      (Let (a "v10") L (Ext Uw) [(t "v9")])] (JRet (t "v10")))].

Definition hello_image_fn_glibc_printf_fp'23__ctype_b_loc'2egnu_inline : func :=
  mkFunc (a "glibc_printf_fp#__ctype_b_loc.gnu_inline") (a "local") (RClass P) [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "__libc_tsd_CTYPE_B"))])] (JRet (t "v0")))].

Definition hello_image_fn_glibc_printf_fp'23__ctype_tolower_loc'2egnu_inline : func :=
  mkFunc (a "glibc_printf_fp#__ctype_tolower_loc.gnu_inline") (a "local") (RClass P) [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "__libc_tsd_CTYPE_TOLOWER"))])] (JRet (t "v0")))].
