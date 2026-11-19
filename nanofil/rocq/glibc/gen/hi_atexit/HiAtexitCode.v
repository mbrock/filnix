(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexit_hi_atexit Unit_csu_errno_os Unit_csu_initZ2dfirst_os Unit_csu_libcZ2dstart_os Unit_csu_libcZ2dtls_os Unit_ctype_ctypeZ2dinfo_os Unit_dlfcn_libc_dlerror_result_os Unit_elf_dlZ2dsupport_os.
From Glibc Require Import Unit_elf_dlZ2dtls_init_tp_os Unit_elf_dlZ2dtunables_os Unit_elf_enblZ2dsecure_os Unit_elf_libc_early_init_os Unit_io_close_nocancel_os Unit_io_fstat64_os Unit_io_lseek64_os Unit_io_write_nocancel_os.
From Glibc Require Import Unit_io_write_os Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os Unit_libio_iofclose_os Unit_libio_ioputs_os.
From Glibc Require Import Unit_libio_stdfiles_os Unit_libio_stdio_os Unit_libio_vtables_os Unit_locale_CZ2dctype_os Unit_locale_globalZ2dlocale_os Unit_malloc_malloc_os Unit_misc_initZ2dmisc_os Unit_misc_makedev_os.
From Glibc Require Import Unit_misc_single_threaded_os Unit_nptl_libcZ2dcleanup_os Unit_nptl_nptl_deallocate_tsd_os Unit_nptl_nptl_nthreads_os Unit_nptl_pthread_mutex_conf_os Unit_nptl_vars_os Unit_posix__exit_os Unit_posix_environ_os.
From Glibc Require Import Unit_resource_getrlimit64_os Unit_stdlib_atexit_oS Unit_stdlib_cxa_atexit_os Unit_stdlib_cxa_thread_atexit_impl_os Unit_stdlib_exit_os Unit_stdlib_getrandom_os Unit_string_memcpy_os Unit_string_mempcpy_os.
From Glibc Require Import Unit_string_memrchr_os Unit_string_strlen_os Unit_string_strrchr_os Unit_termios_isatty_nostatus_os Unit_time_clock_gettime_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Local Definition hi_linked_items_01 : module :=
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

Local Definition hi_linked_items_02 : module :=
  [IFunc Unit_libio_fileops_os.fn__IO_new_file_sync;
  IFunc Unit_libio_fileops_os.fn__IO_file_sync_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_seekoff;
  IFunc Unit_libio_fileops_os.fn__IO_file_seekoff_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_file_seekoff_maybe_mmap;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_read;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_seek;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_stat;
  IFunc Unit_libio_fileops_os.fn__IO_file_close_mmap;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_close;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_write;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_xsputn;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_xsgetn;
  IFunc Unit_libio_fileops_os.fn__IO_file_xsgetn_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_file_xsgetn_maybe_mmap;
  Unit_libio_fileops_os.item___GI__IO_file_xsputn;
  Unit_libio_fileops_os.item___GI__IO_file_sync;
  Unit_libio_fileops_os.item___GI__IO_file_overflow;
  Unit_libio_fileops_os.item___GI__IO_file_underflow;
  Unit_libio_fileops_os.item___GI__IO_file_setbuf;
  Unit_libio_fileops_os.item___GI__IO_file_finish;
  IFunc Unit_libio_genops_os.fn_glibc_genops'23flush_cleanup;
  IFunc Unit_libio_genops_os.fn___GI__IO_un_link;
  IFunc Unit_libio_genops_os.fn__IO_switch_to_main_get_area;
  IFunc Unit_libio_genops_os.fn__IO_switch_to_backup_area;
  IFunc Unit_libio_genops_os.fn___GI__IO_switch_to_get_mode;
  IFunc Unit_libio_genops_os.fn___GI__IO_free_backup_area;
  IFunc Unit_libio_genops_os.fn___GI___overflow;
  IFunc Unit_libio_genops_os.fn_glibc_genops'23save_for_backup;
  IFunc Unit_libio_genops_os.fn___GI___underflow;
  IFunc Unit_libio_genops_os.fn___GI__IO_setb;
  IFunc Unit_libio_genops_os.fn___GI__IO_doallocbuf;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_uflow;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_xsputn;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_xsgetn;
  IFunc Unit_libio_genops_os.fn__IO_default_setbuf;
  IFunc Unit_libio_genops_os.fn__IO_default_seekpos;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_doallocate;
  IFunc Unit_libio_genops_os.fn__IO_default_sync;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_finish;
  IFunc Unit_libio_genops_os.fn___GI__IO_adjust_column;
  IFunc Unit_libio_genops_os.fn___GI__IO_flush_all;
  IFunc Unit_libio_genops_os.fn__IO_cleanup;
  IFunc Unit_libio_genops_os.fn___GI__IO_unsave_markers;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_pbackfail;
  IFunc Unit_libio_genops_os.fn__IO_default_seek;
  IFunc Unit_libio_genops_os.fn__IO_default_stat;
  IFunc Unit_libio_genops_os.fn__IO_default_read;
  IFunc Unit_libio_genops_os.fn__IO_default_write;
  IFunc Unit_libio_genops_os.fn__IO_default_showmanyc;
  IFunc Unit_libio_genops_os.fn__IO_default_imbue;
  Unit_libio_genops_os.item_glibc_genops'23dealloc_buffers;
  Unit_libio_genops_os.item_glibc_genops'23freeres_list;
  Unit_libio_genops_os.item_glibc_genops'23list_all_lock;
  Unit_libio_genops_os.item_glibc_genops'23run_fp;
  IFunc Unit_libio_iofclose_os.fn__IO_new_fclose;
  Unit_libio_iofclose_os.item_fclose;
  IFunc Unit_libio_ioputs_os.fn___GI__IO_puts;
  Unit_libio_ioputs_os.item_puts;
  IFunc Unit_libio_stdfiles_os.fn_glibc_stdfiles'23_IO_stdfiles_init;
  Unit_libio_stdfiles_os.item__IO_2_1_stderr_;
  Unit_libio_stdfiles_os.item__IO_2_1_stdin_;
  Unit_libio_stdfiles_os.item__IO_2_1_stdout_;
  Unit_libio_stdfiles_os.item___GI__IO_list_all].

Local Definition hi_linked_items_03 : module :=
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

Local Definition hi_linked_items_04 : module :=
  [Unit_csu_libcZ2dstart_os.item___x86_rep_stosb_threshold;
  Unit_csu_libcZ2dstart_os.item___x86_shared_cache_size;
  Unit_csu_libcZ2dstart_os.item___x86_shared_cache_size_half;
  Unit_csu_libcZ2dstart_os.item___x86_shared_non_temporal_threshold;
  Unit_csu_libcZ2dstart_os.item___x86_string_control;
  Unit_csu_libcZ2dstart_os.item__dl_x86_features_tlsdesc_state_size;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23intel_02_known;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23sigall_set;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e301;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e302;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e303;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e304;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e319;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e320;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e321;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e322;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e323;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e324;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e325;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e326;
  Unit_csu_libcZ2dstart_os.item_glibc_libc_start'23str'2e327;
  Unit_csu_libcZ2dstart_os.item___pthread_initialize_minimal;
  IFunc Unit_csu_libcZ2dtls_os.fn___libc_setup_tls;
  IFunc Unit_elf_libc_early_init_os.fn___libc_early_init;
  Unit_elf_libc_early_init_os.item___libc_initial;
  IFunc Unit_elf_dlZ2dtls_init_tp_os.fn___tls_init_tp;
  Unit_elf_dlZ2dtls_init_tp_os.item___nptl_initial_report_events;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___GI___ctype_init;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_B;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_TOLOWER;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_TOUPPER;
  Unit_nptl_vars_os.item___GI___default_pthread_attr;
  IFunc Unit_nptl_nptl_deallocate_tsd_os.fn___GI___nptl_deallocate_tsd;
  Unit_nptl_nptl_nthreads_os.item___GI___nptl_nthreads;
  IFunc Unit_nptl_pthread_mutex_conf_os.fn_glibc_pthread_mutex_conf'23_dl_tunable_set_mutex_spin_count;
  IFunc Unit_nptl_pthread_mutex_conf_os.fn___pthread_tunables_init;
  Unit_nptl_pthread_mutex_conf_os.item___GI___mutex_aconf;
  Unit_posix_environ_os.item___environ;
  IFunc Unit_stdlib_getrandom_os.fn___getrandom_early_init;
  Unit_dlfcn_libc_dlerror_result_os.item___libc_dlerror_result_string;
  Unit_elf_enblZ2dsecure_os.item___libc_enable_secure;
  IFunc Unit_elf_dlZ2dtunables_os.fn_glibc_dl_tunables'23do_tunable_update_val;
  IFunc Unit_elf_dlZ2dtunables_os.fn___tunable_is_initialized;
  IFunc Unit_elf_dlZ2dtunables_os.fn___tunable_set_val;
  IFunc Unit_elf_dlZ2dtunables_os.fn___tunable_get_val;
  Unit_elf_dlZ2dtunables_os.item_glibc_dl_tunables'23tunable_list;
  Unit_elf_dlZ2dsupport_os.item___libc_stack_end;
  Unit_elf_dlZ2dsupport_os.item__dl_auxv;
  Unit_elf_dlZ2dsupport_os.item__dl_debug_mask;
  Unit_elf_dlZ2dsupport_os.item__dl_hwcap;
  Unit_elf_dlZ2dsupport_os.item__dl_hwcap2;
  Unit_elf_dlZ2dsupport_os.item__dl_minsigstacksize;
  Unit_elf_dlZ2dsupport_os.item__dl_pagesize;
  Unit_elf_dlZ2dsupport_os.item__dl_platform;
  Unit_elf_dlZ2dsupport_os.item__dl_thp_mode;
  Unit_elf_dlZ2dsupport_os.item__dl_x86_cpu_features;
  Unit_elf_dlZ2dsupport_os.item__dl_x86_feature_control;
  IFunc Unit_resource_getrlimit64_os.fn___GI___getrlimit64;
  Unit_resource_getrlimit64_os.item___GI___getrlimit;
  IFunc Unit_csu_initZ2dfirst_os.fn_glibc_init_first'23_init_first;
  Unit_csu_initZ2dfirst_os.item___libc_argc;
  Unit_csu_initZ2dfirst_os.item___libc_argv;
  Unit_csu_initZ2dfirst_os.item___nanofil_ctor__init_first;
  IFunc Unit_misc_initZ2dmisc_os.fn___init_misc].

Local Definition hi_linked_items_05 : module :=
  [Unit_misc_initZ2dmisc_os.item___progname;
  Unit_misc_initZ2dmisc_os.item___progname_full;
  Unit_misc_initZ2dmisc_os.item_glibc_init_misc'23str'2e61;
  IFunc Unit_string_strrchr_os.fn___GI_strrchr;
  IFunc Unit_time_clock_gettime_os.fn___GI___clock_gettime;
  IFunc Unit_string_memrchr_os.fn___GI___memrchr;
  Unit_locale_globalZ2dlocale_os.item___libc_tsd_LOCALE;
  Unit_locale_globalZ2dlocale_os.item__nl_global_locale;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_ADDRESS;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_COLLATE;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_IDENTIFICATION;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_MEASUREMENT;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_MESSAGES;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_MONETARY;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_NAME;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_NUMERIC;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_PAPER;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_TELEPHONE;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_TIME;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class32;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_alnum;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_alpha;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_blank;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_cntrl;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_digit;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_graph;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_lower;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_print;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_punct;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_space;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_upper;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_xdigit;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_map_tolower;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_map_toupper;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_tolower;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_toupper;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_width;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23lc_ctype_data;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_from_idx;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_from_tbl;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_to_idx;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_to_tbl;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e258;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e259;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e260;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e261;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e262;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e263;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e264;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e265;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e266;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e267;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e268;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e269;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e270;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e271;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e272;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e273;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e274;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e275;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e276;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e277].

Local Definition hi_linked_items_06 : module :=
  [Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e278;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e279;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e280].

Definition hi_linked : module := hi_linked_items_01 ++ hi_linked_items_02 ++ hi_linked_items_03 ++ hi_linked_items_04 ++ hi_linked_items_05 ++ hi_linked_items_06.
