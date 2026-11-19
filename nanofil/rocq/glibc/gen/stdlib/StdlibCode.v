(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Stdlib_roots Unit_csu_errnoZ2dloc_os Unit_csu_errno_os Unit_ctype_ctypeZ2dinfo_os Unit_locale_mb_cur_max_os Unit_malloc_malloc_os Unit_stdlib_atexit_oS Unit_stdlib_cxa_atexit_os.
From Glibc Require Import Unit_wcsmbs_mbsinit_os Unit_wctype_wcfuncs_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition stdlib_module : module :=
  [Stdlib_roots.item_stdlib_root;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23__libc_malloc2;
  IFunc Unit_malloc_malloc_os.fn___GI___libc_malloc;
  IFunc Unit_malloc_malloc_os.fn___GI___libc_free;
  IFunc Unit_malloc_malloc_os.fn___libc_calloc;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23malloc_printerr;
  Unit_malloc_malloc_os.item_malloc;
  Unit_malloc_malloc_os.item_free;
  Unit_malloc_malloc_os.item_calloc;
  Unit_malloc_malloc_os.item_glibc_malloc'23__tcache_dummy;
  Unit_malloc_malloc_os.item_glibc_malloc'23mp_;
  Unit_malloc_malloc_os.item_tcache;
  Unit_malloc_malloc_os.item_glibc_malloc'23str'2e407;
  Unit_malloc_malloc_os.item_glibc_malloc'23str'2e408;
  Unit_malloc_malloc_os.item_glibc_malloc'23str'2e421;
  IFunc Unit_stdlib_cxa_atexit_os.fn___internal_atexit;
  IFunc Unit_stdlib_cxa_atexit_os.fn___GI___cxa_atexit;
  IFunc Unit_stdlib_cxa_atexit_os.fn___new_exitfn;
  Unit_stdlib_cxa_atexit_os.item___exit_funcs;
  Unit_stdlib_cxa_atexit_os.item___exit_funcs_lock;
  Unit_stdlib_cxa_atexit_os.item___new_exitfn_called;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23initial;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e233;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e234;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e235;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e236;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e237;
  Unit_stdlib_cxa_atexit_os.item___cxa_atexit;
  IFunc Unit_stdlib_atexit_oS.fn_atexit;
  Unit_csu_errno_os.item___libc_errno;
  Unit_csu_errno_os.item_errno;
  IFunc Unit_csu_errnoZ2dloc_os.fn___GI___errno_location;
  Unit_csu_errnoZ2dloc_os.item___errno_location;
  IFunc Unit_wcsmbs_mbsinit_os.fn___mbsinit;
  Unit_wcsmbs_mbsinit_os.item_mbsinit;
  IFunc Unit_wctype_wcfuncs_os.fn___iswprint;
  Unit_wctype_wcfuncs_os.item_iswprint;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___ctype_b_loc;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_B;
  IFunc Unit_locale_mb_cur_max_os.fn___ctype_get_mb_cur_max].
