(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexitTypedAT HiAtexitTypedCL HiAtexitTypedCX HiAtexitTypedDE HiAtexitTypedDL HiAtexitTypedFP HiAtexitTypedIN HiAtexitTypedIO01 HiAtexitTypedIO02 HiAtexitTypedLI HiAtexitTypedMA HiAtexitTypedMM HiAtexitTypedNE HiAtexitTypedObjects01 HiAtexitTypedPT.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_items_01 : module :=
  [IFunc hi_fn_hi_atexit'23close_stdout_hi;
  IFunc hi_fn_main;
  hi_item_hi_atexit'23str'2e0;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_mmap_threshold;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_mmaps_max;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_top_pad;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_perturb_byte;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_trim_threshold;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_arena_max;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_arena_test;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_tcache_max;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_tcache_count;
  IFunc hi_fn_glibc_malloc'23_dl_tunable_set_hugetlb;
  IFunc hi_fn___ptmalloc_init;
  IFunc hi_fn_glibc_malloc'23__libc_malloc2;
  IFunc hi_fn___GI___libc_malloc;
  IFunc hi_fn___GI___libc_free;
  IFunc hi_fn___libc_calloc;
  IFunc hi_fn_glibc_malloc'23malloc_printerr;
  hi_item_malloc;
  hi_item_free;
  hi_item_calloc;
  hi_item_glibc_malloc'23__always_fail_morecore;
  hi_item_glibc_malloc'23__tcache_dummy;
  hi_item_glibc_malloc'23main_arena;
  hi_item_glibc_malloc'23mp_;
  hi_item_glibc_malloc'23perturb_byte;
  hi_item_tcache;
  hi_item_glibc_malloc'23tcache_key;
  hi_item_thread_arena;
  hi_item_glibc_malloc'23str'2e407;
  hi_item_glibc_malloc'23str'2e408;
  hi_item_glibc_malloc'23str'2e421;
  IFunc hi_fn___internal_atexit;
  IFunc hi_fn___GI___cxa_atexit;
  IFunc hi_fn___new_exitfn;
  hi_item___exit_funcs;
  hi_item___exit_funcs_lock;
  hi_item___new_exitfn_called;
  hi_item_glibc_cxa_atexit'23initial;
  hi_item_glibc_cxa_atexit'23str'2e233;
  hi_item_glibc_cxa_atexit'23str'2e234;
  hi_item_glibc_cxa_atexit'23str'2e235;
  hi_item_glibc_cxa_atexit'23str'2e236;
  hi_item_glibc_cxa_atexit'23str'2e237;
  hi_item___cxa_atexit;
  IFunc hi_fn_atexit;
  hi_item___libc_errno;
  hi_item_errno;
  IFunc hi_fn___fpending;
  IFunc hi_fn__IO_ferror;
  hi_item_ferror;
  IFunc hi_fn___GI__IO_file_doallocate;
  IFunc hi_fn__IO_file_close_maybe_unlink;
  IFunc hi_fn__IO_new_file_finish;
  IFunc hi_fn__IO_new_file_setbuf;
  IFunc hi_fn__IO_file_setbuf_mmap;
  IFunc hi_fn__IO_new_do_write;
  IFunc hi_fn__IO_new_file_underflow;
  IFunc hi_fn_glibc_fileops'23mmap_remap_check;
  IFunc hi_fn__IO_file_underflow_mmap;
  IFunc hi_fn_glibc_fileops'23decide_maybe_mmap;
  IFunc hi_fn__IO_file_underflow_maybe_mmap;
  IFunc hi_fn__IO_new_file_overflow].
