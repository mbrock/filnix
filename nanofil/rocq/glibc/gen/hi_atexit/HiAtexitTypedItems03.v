(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexitTypedCA HiAtexitTypedCH HiAtexitTypedCL HiAtexitTypedDL HiAtexitTypedER HiAtexitTypedEX HiAtexitTypedFS HiAtexitTypedFU HiAtexitTypedGE HiAtexitTypedGN HiAtexitTypedHA HiAtexitTypedIN HiAtexitTypedIO05 HiAtexitTypedIS HiAtexitTypedLI HiAtexitTypedLS HiAtexitTypedME HiAtexitTypedObjects01 HiAtexitTypedRU HiAtexitTypedST HiAtexitTypedUP HiAtexitTypedWR.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_items_03 : module :=
  [hi_item_glibc_stdfiles'23_IO_stdfile_0_lock;
  hi_item_glibc_stdfiles'23_IO_stdfile_1_lock;
  hi_item_glibc_stdfiles'23_IO_stdfile_2_lock;
  hi_item_glibc_stdfiles'23_IO_wide_data_0;
  hi_item_glibc_stdfiles'23_IO_wide_data_1;
  hi_item_glibc_stdfiles'23_IO_wide_data_2;
  hi_item___nanofil_ctor__IO_stdfiles_init;
  hi_item_stdout;
  IFunc hi_fn__IO_vtable_check;
  IFunc hi_fn_glibc_vtables'23check_stdfiles_vtables;
  hi_item_IO_accept_foreign_vtables;
  hi_item___io_vtables;
  hi_item_glibc_vtables'23str'2e302;
  hi_item___nanofil_ctor_check_stdfiles_vtables;
  IFunc hi_fn___isatty_nostatus;
  IFunc hi_fn___GI___libc_write;
  hi_item___GI___write;
  IFunc hi_fn___GI___write_nocancel;
  IFunc hi_fn___lseek64;
  IFunc hi_fn___GI___fstat64;
  IFunc hi_fn___GI___close_nocancel;
  IFunc hi_fn___GI__exit;
  hi_item__exit;
  IFunc hi_fn___run_exit_handlers;
  IFunc hi_fn___GI_exit;
  hi_item___exit_funcs_done;
  hi_item_glibc_exit'23__exit_lock;
  hi_item_exit;
  IFunc hi_fn___GI___call_tls_dtors;
  IFunc hi_fn___GI___libc_cleanup_push_defer;
  IFunc hi_fn___GI___libc_cleanup_pop_restore;
  hi_item___libc_single_threaded_internal;
  hi_item___libc_single_threaded;
  IFunc hi_fn___gnu_dev_major;
  IFunc hi_fn___strlen;
  hi_item___GI_strlen;
  IFunc hi_fn___GI___mempcpy;
  hi_item___GI_mempcpy;
  IFunc hi_fn___GI_memcpy;
  IFunc hi_fn_glibc_libc_start'23get_isa_level;
  IFunc hi_fn_glibc_libc_start'23intel_02_known_compare;
  IFunc hi_fn_glibc_libc_start'23intel_check_word;
  IFunc hi_fn_glibc_libc_start'23handle_intel;
  IFunc hi_fn_glibc_libc_start'23handle_amd;
  IFunc hi_fn_glibc_libc_start'23handle_zhaoxin;
  IFunc hi_fn_glibc_libc_start'23handle_hygon;
  IFunc hi_fn_glibc_libc_start'23get_common_cache_info;
  IFunc hi_fn_glibc_libc_start'23dl_init_cacheinfo;
  IFunc hi_fn_glibc_libc_start'23_dl_tunable_set_plt_rewrite;
  IFunc hi_fn_glibc_libc_start'23_dl_tunable_set_prefer_map_32bit_exec;
  IFunc hi_fn_glibc_libc_start'23update_active;
  IFunc hi_fn_glibc_libc_start'23get_common_indices;
  IFunc hi_fn_glibc_libc_start'23__libc_start_call_main;
  IFunc hi_fn_glibc_libc_start'23errno_handler;
  IFunc hi_fn_glibc_libc_start'23dlerror_handler;
  IFunc hi_fn___libc_start_main;
  IFunc hi_fn_glibc_libc_start'23futex_wake;
  IFunc hi_fn_glibc_libc_start'23init_cpu_features;
  IFunc hi_fn_glibc_libc_start'23internal_signal_block_all;
  hi_item___x86_data_cache_size;
  hi_item___x86_data_cache_size_half;
  hi_item___x86_memset_non_temporal_threshold;
  hi_item___x86_rep_movsb_stop_threshold;
  hi_item___x86_rep_movsb_threshold].
