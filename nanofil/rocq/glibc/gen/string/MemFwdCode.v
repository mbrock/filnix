(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import MemFwd_roots Unit_csu_errnoZ2dloc_os Unit_csu_errno_os Unit_ctype_ctypeZ2dinfo_os Unit_locale_mb_cur_max_os Unit_string_memcpy_os Unit_string_mempcpy_os Unit_string_memset_os.
From Glibc Require Import Unit_string_strdup_os Unit_wcsmbs_mbsinit_os Unit_wctype_wcfuncs_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition memfwd_module : module :=
  [MemFwd_roots.item_memfwd_roots;
  IFunc Unit_string_memcpy_os.fn___GI_memcpy;
  Unit_string_memcpy_os.item_memcpy;
  IFunc Unit_string_mempcpy_os.fn___GI___mempcpy;
  Unit_string_mempcpy_os.item_mempcpy;
  IFunc Unit_string_memset_os.fn___GI_memset;
  Unit_string_memset_os.item_memset;
  IFunc Unit_string_strdup_os.fn___GI___strdup;
  Unit_string_strdup_os.item_strdup;
  Unit_csu_errno_os.item___libc_errno;
  Unit_csu_errno_os.item_errno;
  IFunc Unit_csu_errnoZ2dloc_os.fn___GI___errno_location;
  Unit_csu_errnoZ2dloc_os.item___errno_location;
  IFunc Unit_wcsmbs_mbsinit_os.fn___mbsinit;
  Unit_wcsmbs_mbsinit_os.item_mbsinit;
  IFunc Unit_wctype_wcfuncs_os.fn___GI___towlower;
  IFunc Unit_wctype_wcfuncs_os.fn___GI___towupper;
  Unit_wctype_wcfuncs_os.item_towupper;
  Unit_wctype_wcfuncs_os.item_towlower;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___ctype_b_loc;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___ctype_toupper_loc;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___ctype_tolower_loc;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___GI___ctype_init;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_B;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_TOLOWER;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_TOUPPER;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype_init;
  IFunc Unit_locale_mb_cur_max_os.fn___ctype_get_mb_cur_max].
