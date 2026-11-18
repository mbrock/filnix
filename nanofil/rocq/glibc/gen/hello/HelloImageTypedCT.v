(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___ctype_b_loc : func :=
  ir_fn{ "export" "__ctype_b_loc"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_B"
    => ret %"v0"
} }.

Definition hello_image_fn___GI___ctype_init : func :=
  ir_fn{ "export" "__GI___ctype_init"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"v1" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v1";
    %"v2" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v5" = %"v4" +p #56;
    %"chk2" : A = (Check 0 8 Read 8) %"v5";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v11" = %"v10" +p #256;
    %"chk3" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk3" + 0] <- %"v11";
    %"v12" : P = Copy $"__libc_tsd_CTYPE_TOUPPER";
    %"v13" : P = Copy $"__libc_tsd_LOCALE";
    %"chk4" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v14";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v17" = %"v16" +p #56;
    %"v21" = %"v17" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v23" = %"v22" +p #512;
    %"chk7" : A = (Check 0 8 Write 8) %"v12";
    store.ptr [%"chk7" + 0] <- %"v23";
    %"v24" : P = Copy $"__libc_tsd_CTYPE_TOLOWER";
    %"v25" : P = Copy $"__libc_tsd_LOCALE";
    %"chk8" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"v26";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v29" = %"v28" +p #56;
    %"v33" = %"v29" +p #24;
    %"chk10" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v35" = %"v34" +p #512;
    %"chk11" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk11" + 0] <- %"v35"
    => ret void
} }.

Definition hello_image_fn___ctype_get_mb_cur_max : func :=
  ir_fn{ "weak" "__ctype_get_mb_cur_max"() -> (RClass L) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v1" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v1";
    %"v3" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v4" = %"v3" +p #56;
    %"v8" = %"v4" +p #104;
    %"chk2" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v10" : L = (Ext Uw) %"v9"
    => ret %"v10"
} }.

Definition hello_image_fn_glibc_printf_fp'23__ctype_b_loc'2egnu_inline : func :=
  ir_fn{ "local" "glibc_printf_fp#__ctype_b_loc.gnu_inline"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_B"
    => ret %"v0"
} }.

Definition hello_image_fn_glibc_printf_fp'23__ctype_tolower_loc'2egnu_inline : func :=
  ir_fn{ "local" "glibc_printf_fp#__ctype_tolower_loc.gnu_inline"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_TOLOWER"
    => ret %"v0"
} }.
