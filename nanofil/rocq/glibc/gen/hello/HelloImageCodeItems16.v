(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_malloc_obstack_os Unit_malloc_scratch_buffer_grow_preserve_os Unit_malloc_scratch_buffer_set_array_size_os Unit_misc_error_os Unit_misc_getclktck_os Unit_misc_getdtsz_os Unit_misc_getpagesize_os.
From Glibc Require Import Unit_misc_getsysstats_os Unit_misc_initZ2dmisc_os Unit_misc_makedev_os Unit_misc_mmap64_os Unit_misc_munmap_os Unit_misc_setvmaname_os Unit_misc_single_threaded_os Unit_misc_sysinfo_os.
From Glibc Require Import Unit_misc_tsearch_os Unit_nptl_cleanup_compat_os Unit_nptl_futexZ2dinternal_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_16 : module :=
  [Unit_malloc_obstack_os.item_obstack_alloc_failed_handler;
  Unit_malloc_obstack_os.item_obstack_exit_failure;
  Unit_malloc_obstack_os.item_glibc_obstack'23str'2e148;
  Unit_malloc_obstack_os.item_glibc_obstack'23str'2e149;
  IFunc Unit_malloc_scratch_buffer_grow_preserve_os.fn___GI___libc_scratch_buffer_grow_preserve;
  IFunc Unit_malloc_scratch_buffer_set_array_size_os.fn___GI___libc_scratch_buffer_set_array_size;
  IFunc Unit_misc_error_os.fn___error_internal;
  IFunc Unit_misc_error_os.fn___error;
  Unit_misc_error_os.item_error;
  Unit_misc_error_os.item_error_message_count;
  Unit_misc_error_os.item_error_print_progname;
  Unit_misc_error_os.item_glibc_error'23str'2e252;
  Unit_misc_error_os.item_glibc_error'23str'2e253;
  Unit_misc_error_os.item_glibc_error'23str'2e254;
  Unit_misc_error_os.item_glibc_error'23str'2e255;
  IFunc Unit_misc_getclktck_os.fn___getclktck;
  IFunc Unit_misc_getdtsz_os.fn___getdtablesize;
  IFunc Unit_misc_getpagesize_os.fn___GI___getpagesize;
  Unit_misc_getpagesize_os.item_glibc_getpagesize'23str'2e279;
  Unit_misc_getpagesize_os.item_glibc_getpagesize'23str'2e280;
  Unit_misc_getpagesize_os.item_glibc_getpagesize'23str'2e281;
  IFunc Unit_misc_getsysstats_os.fn_glibc_getsysstats'23next_line;
  IFunc Unit_misc_getsysstats_os.fn___GI___get_nprocs;
  IFunc Unit_misc_getsysstats_os.fn___GI___get_nprocs_conf;
  IFunc Unit_misc_getsysstats_os.fn___GI___get_phys_pages;
  IFunc Unit_misc_getsysstats_os.fn___GI___get_avphys_pages;
  Unit_misc_getsysstats_os.item_glibc_getsysstats'23str'2e311;
  Unit_misc_getsysstats_os.item_glibc_getsysstats'23str'2e312;
  Unit_misc_getsysstats_os.item_glibc_getsysstats'23str'2e313;
  Unit_misc_getsysstats_os.item_glibc_getsysstats'23str'2e314;
  Unit_misc_getsysstats_os.item_glibc_getsysstats'23str'2e315;
  Unit_misc_getsysstats_os.item_glibc_getsysstats'23str'2e316;
  Unit_misc_getsysstats_os.item_glibc_getsysstats'23str'2e317;
  IFunc Unit_misc_initZ2dmisc_os.fn___init_misc;
  Unit_misc_initZ2dmisc_os.item_program_invocation_name;
  Unit_misc_initZ2dmisc_os.item_program_invocation_short_name;
  Unit_misc_initZ2dmisc_os.item___progname;
  Unit_misc_initZ2dmisc_os.item___progname_full;
  Unit_misc_initZ2dmisc_os.item_glibc_init_misc'23str'2e61;
  IFunc Unit_misc_makedev_os.fn___gnu_dev_major;
  IFunc Unit_misc_mmap64_os.fn___GI___mmap64;
  Unit_misc_mmap64_os.item___GI___mmap;
  Unit_misc_mmap64_os.item_glibc_mmap64'23str'2e279;
  Unit_misc_munmap_os.item___munmap;
  Unit_misc_munmap_os.item___GI___munmap;
  IFunc Unit_misc_setvmaname_os.fn___is_decorate_maps_enabled;
  IFunc Unit_misc_setvmaname_os.fn___set_vma_name;
  Unit_misc_setvmaname_os.item_glibc_setvmaname'23decorate_maps;
  Unit_misc_setvmaname_os.item_glibc_setvmaname'23str'2e282;
  Unit_misc_single_threaded_os.item___libc_single_threaded_internal;
  Unit_misc_single_threaded_os.item___libc_single_threaded;
  Unit_misc_sysinfo_os.item___sysinfo;
  IFunc Unit_misc_tsearch_os.fn_glibc_tsearch'23maybe_split_for_insert;
  IFunc Unit_misc_tsearch_os.fn___GI___tsearch;
  IFunc Unit_misc_tsearch_os.fn___GI___tfind;
  IFunc Unit_misc_tsearch_os.fn_glibc_tsearch'23trecurse_r;
  IFunc Unit_misc_tsearch_os.fn___GI___twalk_r;
  IFunc Unit_nptl_cleanup_compat_os.fn___GI___pthread_cleanup_push;
  IFunc Unit_nptl_cleanup_compat_os.fn___GI___pthread_cleanup_pop;
  IFunc Unit_nptl_futexZ2dinternal_os.fn___GI___futex_abstimed_wait64;
  Unit_nptl_futexZ2dinternal_os.item_glibc_futex_internal'23str'2e244;
  Unit_nptl_futexZ2dinternal_os.item_glibc_futex_internal'23str'2e245;
  Unit_nptl_futexZ2dinternal_os.item_glibc_futex_internal'23str'2e246;
  Unit_nptl_futexZ2dinternal_os.item_glibc_futex_internal'23str'2e247].

Lemma hello_image_linked_items_16_zero : zero_nonneg hello_image_linked_items_16 = true.
Proof. reflexivity. Qed.
