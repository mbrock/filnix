(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition formatter_module : module :=
  [(IData (a "formatter_roots") (LRo (a "export")) 8 [(Sym (a "__vfprintf_internal") 0)]);
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23read_int;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23outstring_converted_wide_string;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23printf_positional;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23printf_unknown;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23group_number;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___vfprintf_internal;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__find_specmb'2egnu_inline;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_has_failed;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_mark_failed;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_pad;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_putc;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_fp_spec;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23scratch_buffer_free;
  IFunc Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23scratch_buffer_init;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23__printf_buffer'2estep0_jumps'2e277;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23__printf_buffer'2estep1_jumps'2e278;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23__printf_buffer'2estep2_jumps'2e279;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23__printf_buffer'2estep3a_jumps'2e280;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23__printf_buffer'2estep3b_jumps'2e281;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23__printf_buffer'2estep4_jumps'2e282;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23jump_table;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23null;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23printf_positional'2estep4_jumps'2e294;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e284;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e285;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e286;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e289;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e290;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e291;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e292;
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e293].
