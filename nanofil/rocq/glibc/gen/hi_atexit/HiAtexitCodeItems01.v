(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexit_hi_atexit Unit_csu_errno_os Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_malloc_malloc_os Unit_stdlib_atexit_oS.
From Glibc Require Import Unit_stdlib_cxa_atexit_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_linked_items_01 : module :=
  [IFunc HiAtexit_hi_atexit.fn_hi_atexit'23close_stdout_hi;
  IFunc HiAtexit_hi_atexit.fn_main;
  HiAtexit_hi_atexit.item_hi_atexit'23str'2e0;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_mmap_threshold;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_mmaps_max;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_top_pad;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_perturb_byte;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_trim_threshold;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_arena_max;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_arena_test;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_tcache_max;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_tcache_count;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_hugetlb;
  IFunc Unit_malloc_malloc_os.fn___ptmalloc_init;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23__libc_malloc2;
  IFunc Unit_malloc_malloc_os.fn___GI___libc_malloc;
  IFunc Unit_malloc_malloc_os.fn___GI___libc_free;
  IFunc Unit_malloc_malloc_os.fn___libc_calloc;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23malloc_printerr;
  Unit_malloc_malloc_os.item_malloc;
  Unit_malloc_malloc_os.item_free;
  Unit_malloc_malloc_os.item_calloc;
  Unit_malloc_malloc_os.item_glibc_malloc'23__always_fail_morecore;
  Unit_malloc_malloc_os.item_glibc_malloc'23__tcache_dummy;
  Unit_malloc_malloc_os.item_glibc_malloc'23main_arena;
  Unit_malloc_malloc_os.item_glibc_malloc'23mp_;
  Unit_malloc_malloc_os.item_glibc_malloc'23perturb_byte;
  Unit_malloc_malloc_os.item_tcache;
  Unit_malloc_malloc_os.item_glibc_malloc'23tcache_key;
  Unit_malloc_malloc_os.item_thread_arena;
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
  IFunc Unit_libio___fpending_os.fn___fpending;
  IFunc Unit_libio_ferror_os.fn__IO_ferror;
  Unit_libio_ferror_os.item_ferror;
  IFunc Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate;
  IFunc Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_finish;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_setbuf;
  IFunc Unit_libio_fileops_os.fn__IO_file_setbuf_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_new_do_write;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_underflow;
  IFunc Unit_libio_fileops_os.fn_glibc_fileops'23mmap_remap_check;
  IFunc Unit_libio_fileops_os.fn__IO_file_underflow_mmap;
  IFunc Unit_libio_fileops_os.fn_glibc_fileops'23decide_maybe_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_file_underflow_maybe_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_overflow].
