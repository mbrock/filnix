(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_csu_libcZ2dstart_os Unit_io_close_nocancel_os Unit_io_fstat64_os Unit_io_lseek64_os Unit_io_write_nocancel_os Unit_io_write_os Unit_libio_stdfiles_os Unit_libio_stdio_os.
From Glibc Require Import Unit_libio_vtables_os Unit_misc_makedev_os Unit_misc_single_threaded_os Unit_nptl_libcZ2dcleanup_os Unit_posix__exit_os Unit_stdlib_cxa_thread_atexit_impl_os Unit_stdlib_exit_os Unit_string_memcpy_os.
From Glibc Require Import Unit_string_mempcpy_os Unit_string_strlen_os Unit_termios_isatty_nostatus_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_linked_items_03 : module :=
  [Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_0_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_1_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_2_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_0;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_1;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_2;
  Unit_libio_stdfiles_os.item___nanofil_ctor__IO_stdfiles_init;
  Unit_libio_stdio_os.item_stdout;
  IFunc Unit_libio_vtables_os.fn__IO_vtable_check;
  IFunc Unit_libio_vtables_os.fn_glibc_vtables'23check_stdfiles_vtables;
  Unit_libio_vtables_os.item_IO_accept_foreign_vtables;
  Unit_libio_vtables_os.item___io_vtables;
  Unit_libio_vtables_os.item_glibc_vtables'23str'2e302;
  Unit_libio_vtables_os.item___nanofil_ctor_check_stdfiles_vtables;
  IFunc Unit_termios_isatty_nostatus_os.fn___isatty_nostatus;
  IFunc Unit_io_write_os.fn___GI___libc_write;
  Unit_io_write_os.item___GI___write;
  IFunc Unit_io_write_nocancel_os.fn___GI___write_nocancel;
  IFunc Unit_io_lseek64_os.fn___lseek64;
  IFunc Unit_io_fstat64_os.fn___GI___fstat64;
  IFunc Unit_io_close_nocancel_os.fn___GI___close_nocancel;
  IFunc Unit_posix__exit_os.fn___GI__exit;
  Unit_posix__exit_os.item__exit;
  IFunc Unit_stdlib_exit_os.fn___run_exit_handlers;
  IFunc Unit_stdlib_exit_os.fn___GI_exit;
  Unit_stdlib_exit_os.item___exit_funcs_done;
  Unit_stdlib_exit_os.item_glibc_exit'23__exit_lock;
  Unit_stdlib_exit_os.item_exit;
  IFunc Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors;
  IFunc Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer;
  IFunc Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore;
  Unit_misc_single_threaded_os.item___libc_single_threaded_internal;
  Unit_misc_single_threaded_os.item___libc_single_threaded;
  IFunc Unit_misc_makedev_os.fn___gnu_dev_major;
  IFunc Unit_string_strlen_os.fn___strlen;
  Unit_string_strlen_os.item___GI_strlen;
  IFunc Unit_string_mempcpy_os.fn___GI___mempcpy;
  Unit_string_mempcpy_os.item___GI_mempcpy;
  IFunc Unit_string_memcpy_os.fn___GI_memcpy;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23get_isa_level;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23intel_02_known_compare;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23intel_check_word;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23handle_intel;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23handle_amd;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23handle_zhaoxin;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23handle_hygon;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23get_common_cache_info;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23dl_init_cacheinfo;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23_dl_tunable_set_plt_rewrite;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23_dl_tunable_set_prefer_map_32bit_exec;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23update_active;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23get_common_indices;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23__libc_start_call_main;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23errno_handler;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23dlerror_handler;
  IFunc Unit_csu_libcZ2dstart_os.fn___libc_start_main;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23futex_wake;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23init_cpu_features;
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23internal_signal_block_all;
  Unit_csu_libcZ2dstart_os.item___x86_data_cache_size;
  Unit_csu_libcZ2dstart_os.item___x86_data_cache_size_half;
  Unit_csu_libcZ2dstart_os.item___x86_memset_non_temporal_threshold;
  Unit_csu_libcZ2dstart_os.item___x86_rep_movsb_stop_threshold;
  Unit_csu_libcZ2dstart_os.item___x86_rep_movsb_threshold].
