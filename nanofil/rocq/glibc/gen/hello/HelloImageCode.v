(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageChunks HelloImageEraseMem HelloImage_c32isprint HelloImage_closeZ2dstream HelloImage_closeout HelloImage_exitfail HelloImage_hardZ2dlocale HelloImage_hello.
From Glibc Require Import HelloImage_mbrtoc32 HelloImage_mbrtowc HelloImage_mbsrtowcs HelloImage_mbsrtowcsZ2dstate HelloImage_mbszero HelloImage_memeq HelloImage_progname HelloImage_propername.
From Glibc Require Import HelloImage_quotearg HelloImage_setlocale_null HelloImage_setlocale_nullZ2dunlocked HelloImage_streq HelloImage_strnlen1 HelloImage_versionZ2detc HelloImage_versionZ2detcZ2dfsf HelloImage_xallocZ2ddie.
From Glibc Require Import HelloImage_xmalloc Unit_assert___libc_assert_fail_os Unit_csu_errnoZ2dloc_os Unit_csu_errno_os Unit_csu_initZ2dfirst_os Unit_csu_libcZ2dstart_os Unit_csu_libcZ2dtls_os Unit_ctype_ctypeZ2dinfo_os.
From Glibc Require Import Unit_debug_chk_fail_os Unit_debug_fortify_fail_os Unit_debug_readonlyZ2dareaZ2dfallback_os Unit_debug_readonlyZ2darea_os Unit_dirent_closedir_os Unit_dirent_getdents64_os Unit_dirent_opendir_os Unit_dirent_readdir64_os.
From Glibc Require Import Unit_dlfcn_libc_dlerror_result_os Unit_elf_dlZ2dlibc_os Unit_elf_dlZ2dsupport_os Unit_elf_dlZ2dtls_init_tp_os Unit_elf_dlZ2dtunables_os Unit_elf_enblZ2dsecure_os Unit_elf_libc_early_init_os Unit_iconv_gconv_builtin_os.
From Glibc Require Import Unit_iconv_gconv_cache_os Unit_iconv_gconv_charset_os Unit_iconv_gconv_conf_os Unit_iconv_gconv_db_os Unit_iconv_gconv_dl_os Unit_iconv_gconv_open_os Unit_iconv_gconv_os Unit_iconv_gconv_simple_os.
From Glibc Require Import Unit_iconv_gconv_trans_os Unit_intl_dcgettext_os Unit_intl_dcigettext_os Unit_intl_explodename_os Unit_intl_finddomain_os Unit_intl_l10nflist_os Unit_intl_loadmsgcat_os Unit_intl_localealias_os.
From Glibc Require Import Unit_intl_pluralZ2dexp_os Unit_intl_plural_os Unit_io_close_nocancel_nostatus_os Unit_io_close_nocancel_os Unit_io_fcntl_nocancel_os Unit_io_fstat64_os Unit_io_fstatat64_os Unit_io_getcwd_os.
From Glibc Require Import Unit_io_lseek64_os Unit_io_open64_nocancel_os Unit_io_open64_os Unit_io_read_nocancel_os Unit_io_read_os Unit_io_stat64_os Unit_io_write_nocancel_os Unit_io_write_os.
From Glibc Require Import Unit_libio___fpending_os Unit_libio_feof_u_os Unit_libio_ferror_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os Unit_libio_iofclose_os Unit_libio_iofflush_os.
From Glibc Require Import Unit_libio_iofgets_u_os Unit_libio_iofopen_os Unit_libio_iofopncook_os Unit_libio_iofputs_os Unit_libio_iofputws_u_os Unit_libio_iofwide_os Unit_libio_iogetdelim_os Unit_libio_iogetline_os.
From Glibc Require Import Unit_libio_iopopen_os Unit_libio_iovdprintf_os Unit_libio_libc_fatal_os Unit_libio_memstream_os Unit_libio_obprintf_os Unit_libio_stdfiles_os Unit_libio_stdio_os Unit_libio_strops_os.
From Glibc Require Import Unit_libio_vasprintf_os Unit_libio_vsnprintf_os Unit_libio_vtables_os Unit_libio_wfiledoalloc_os Unit_libio_wfileops_os Unit_libio_wgenops_os Unit_libio_wmemstream_os Unit_libio_wprintf_os.
From Glibc Require Import Unit_libio_wstrops_os Unit_locale_CZ2daddress_os Unit_locale_CZ2dcollate_os Unit_locale_CZ2dctype_os Unit_locale_CZ2didentification_os Unit_locale_CZ2dmeasurement_os Unit_locale_CZ2dmessages_os Unit_locale_CZ2dmonetary_os.
From Glibc Require Import Unit_locale_CZ2dname_os Unit_locale_CZ2dnumeric_os Unit_locale_CZ2dpaper_os Unit_locale_CZ2dtelephone_os Unit_locale_CZ2dtime_os Unit_locale_C_name_os Unit_locale_SYS_libc_os Unit_locale_findlocale_os.
From Glibc Require Import Unit_locale_globalZ2dlocale_os Unit_locale_lcZ2dctype_os Unit_locale_loadarchive_os Unit_locale_loadlocale_os Unit_locale_localename_os Unit_locale_mb_cur_max_os Unit_locale_setlocale_os Unit_locale_xlocale_os.
From Glibc Require Import Unit_malloc_malloc_os Unit_malloc_obstack_os Unit_malloc_scratch_buffer_grow_preserve_os Unit_malloc_scratch_buffer_set_array_size_os Unit_misc_error_os Unit_misc_getclktck_os Unit_misc_getdtsz_os Unit_misc_getpagesize_os.
From Glibc Require Import Unit_misc_getsysstats_os Unit_misc_initZ2dmisc_os Unit_misc_makedev_os Unit_misc_mmap64_os Unit_misc_mremap_os Unit_misc_munmap_os Unit_misc_setvmaname_os Unit_misc_single_threaded_os.
From Glibc Require Import Unit_misc_sysinfo_os Unit_misc_tsearch_os Unit_nptl_alloca_cutoff_os Unit_nptl_cleanup_compat_os Unit_nptl_futexZ2dinternal_os Unit_nptl_libcZ2dcleanup_os Unit_nptl_lowlevellock_os Unit_nptl_nptl_deallocate_tsd_os.
From Glibc Require Import Unit_nptl_nptl_nthreads_os Unit_nptl_pthread_mutex_conf_os Unit_nptl_pthread_once_os Unit_nptl_pthread_rwlock_init_os Unit_nptl_pthread_rwlock_rdlock_os Unit_nptl_pthread_rwlock_unlock_os Unit_nptl_pthread_rwlock_wrlock_os Unit_nptl_pthread_setcancelstate_os.
From Glibc Require Import Unit_nptl_unwind_os Unit_nptl_vars_os Unit_nss_hashZ2dstring_os Unit_posix__exit_os Unit_posix_environ_os Unit_posix_get_child_max_os Unit_posix_getopt1_os Unit_posix_getopt_os.
From Glibc Require Import Unit_posix_sched_cpucount_os Unit_posix_sysconf_os Unit_posix_wait4_os Unit_posix_waitpid_os Unit_resource_getrlimit64_os Unit_setjmp_longjmp_os Unit_stdioZ2dcommon__fitoa_word_os Unit_stdioZ2dcommon_asprintf_os.
From Glibc Require Import Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os Unit_stdioZ2dcommon_errlist_os Unit_stdioZ2dcommon_errname_os Unit_stdioZ2dcommon_fprintf_os Unit_stdioZ2dcommon_funlockfile_os Unit_stdioZ2dcommon_fxprintf_os Unit_stdioZ2dcommon_grouping_iterator_os Unit_stdioZ2dcommon_itoaZ2ddigits_os.
From Glibc Require Import Unit_stdioZ2dcommon_itoaZ2dudigits_os Unit_stdioZ2dcommon_itowaZ2ddigits_os Unit_stdioZ2dcommon_printfZ2dparsemb_os Unit_stdioZ2dcommon_printfZ2dparsewc_os Unit_stdioZ2dcommon_printf_buffer_as_file_os Unit_stdioZ2dcommon_printf_buffer_done_os Unit_stdioZ2dcommon_printf_buffer_flush_os Unit_stdioZ2dcommon_printf_buffer_pad_1_os.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_putc_1_os Unit_stdioZ2dcommon_printf_buffer_puts_1_os Unit_stdioZ2dcommon_printf_buffer_to_file_os Unit_stdioZ2dcommon_printf_buffer_write_os Unit_stdioZ2dcommon_printf_fp_os Unit_stdioZ2dcommon_printf_fphex_os Unit_stdioZ2dcommon_printf_function_invoke_os Unit_stdioZ2dcommon_printf_os.
From Glibc Require Import Unit_stdioZ2dcommon_regZ2dmodifier_os Unit_stdioZ2dcommon_regZ2dprintf_os Unit_stdioZ2dcommon_regZ2dtype_os Unit_stdioZ2dcommon_snprintf_os Unit_stdioZ2dcommon_translated_number_width_os Unit_stdioZ2dcommon_vfprintfZ2dinternal_os Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.
From Glibc Require Import Unit_stdioZ2dcommon_wprintf_buffer_done_os Unit_stdioZ2dcommon_wprintf_buffer_flush_os Unit_stdioZ2dcommon_wprintf_buffer_pad_1_os Unit_stdioZ2dcommon_wprintf_buffer_putc_1_os Unit_stdioZ2dcommon_wprintf_buffer_to_file_os Unit_stdioZ2dcommon_wprintf_buffer_write_os Unit_stdioZ2dcommon_wprintf_function_invoke_os Unit_stdlib_abort_os.
From Glibc Require Import Unit_stdlib_abs_os Unit_stdlib_add_n_os Unit_stdlib_addmul_1_os Unit_stdlib_atexit_oS Unit_stdlib_bsearch_os Unit_stdlib_cmp_os Unit_stdlib_cxa_atexit_os Unit_stdlib_cxa_thread_atexit_impl_os.
From Glibc Require Import Unit_stdlib_dbl2mpn_os Unit_stdlib_divrem_os Unit_stdlib_exit_os Unit_stdlib_fpioconst_os Unit_stdlib_getenv_os Unit_stdlib_getrandom_os Unit_stdlib_grouping_os Unit_stdlib_ldbl2mpn_os.
From Glibc Require Import Unit_stdlib_lshift_os Unit_stdlib_mul_1_os Unit_stdlib_mul_n_os Unit_stdlib_mul_os Unit_stdlib_qsort_os Unit_stdlib_rshift_os Unit_stdlib_secureZ2dgetenv_os Unit_stdlib_strtol_l_os.
From Glibc Require Import Unit_stdlib_strtol_os Unit_stdlib_strtoul_l_os Unit_stdlib_strtoul_os Unit_stdlib_sub_n_os Unit_stdlib_submul_1_os Unit_string__strerror_os Unit_string_argzZ2daddsep_os Unit_string_argzZ2dctsep_os.
From Glibc Require Import Unit_string_argzZ2dnext_os Unit_string_cacheinfo_os Unit_string_memchr_os Unit_string_memcmp_os Unit_string_memcpy_os Unit_string_memmem_os Unit_string_memmove_os Unit_string_mempcpy_os.
From Glibc Require Import Unit_string_memrchr_os Unit_string_memset_os Unit_string_stpcpy_os Unit_string_strcasecmp_l_os Unit_string_strchr_os Unit_string_strchrnul_os Unit_string_strcmp_os Unit_string_strcpy_os.
From Glibc Require Import Unit_string_strcspn_os Unit_string_strdup_os Unit_string_strlen_os Unit_string_strncmp_os Unit_string_strndup_os Unit_string_strnlen_os Unit_string_strrchr_os Unit_string_strspn_os.
From Glibc Require Import Unit_string_strstr_os Unit_string_strtok_r_os Unit_termios_isatty_nostatus_os Unit_time_clock_gettime_os Unit_wcsmbs_btowc_os Unit_wcsmbs_mbrtoc32_os Unit_wcsmbs_mbrtowc_os Unit_wcsmbs_mbsinit_os.
From Glibc Require Import Unit_wcsmbs_mbsrtowcs_l_os Unit_wcsmbs_mbsrtowcs_os Unit_wcsmbs_wcrtomb_os Unit_wcsmbs_wcschrnul_os Unit_wcsmbs_wcslen_os Unit_wcsmbs_wcsmbsload_os Unit_wcsmbs_wcsnlen_os Unit_wcsmbs_wcsrtombs_os.
From Glibc Require Import Unit_wcsmbs_wmemchr_os Unit_wcsmbs_wmemcpy_os Unit_wcsmbs_wmemmove_os Unit_wcsmbs_wmempcpy_os Unit_wcsmbs_wmemset_os Unit_wctype_wcfuncs_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).


(** ## Provenance

    The producer linked GNU Hello's 81 checked objects with 333 user glibc
    units by `rocq/scripts/link.pl --ctors main,__libc_start_main`. The objects come from the
    flake output `checks.x86_64-linux.nanofil-hello-fixture.captured`, and the units come from
    the capture `/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44`.
    These SHA-256 digests identify the inputs and the result:

    - objects, by name and term digest: `5b7ba233e0adedaff060ffdce2b533211d3d360ee7af82a2201a816c261fe53b`
    - units, by name and term digest: `a6dedf5c33d6c177ae56c94ebc438b2ed0ea4ef314de4e22c4faf28d4a61c243`
    - the whole linked image: `d41e2c79f1408cfbb4b74c9b5c980cf5f934f08e940a152cebce3054f146b8b9`

    The extracted module decoder reads the linked term. Its OCaml printer
    writes the resulting constructors as Gallina, and the generator assembles
    the named definitions in link order. Rocq checks these definitions and
    their zero runs. The digests identify the input to the printer.
*)
Local Definition hello_image_linked_items_01 : module :=
  [IFunc HelloImage_c32isprint.fn_c32isprint;
  IFunc HelloImage_closeZ2dstream.fn_close_stream;
  IFunc HelloImage_closeout.fn_close_stdout;
  HelloImage_closeout.item_closeout'23file_name;
  HelloImage_closeout.item_closeout'23ignore_EPIPE;
  HelloImage_closeout.item_closeout'23str'2e52;
  HelloImage_closeout.item_closeout'23str'2e53;
  HelloImage_closeout.item_closeout'23str'2e54;
  HelloImage_closeout.item_closeout'23str'2e55;
  HelloImage_exitfail.item_exit_failure;
  IFunc HelloImage_hardZ2dlocale.fn_hard_locale;
  HelloImage_hardZ2dlocale.item_hard'2dlocale'23str'2e31;
  HelloImage_hardZ2dlocale.item_hard'2dlocale'23str'2e32;
  IFunc HelloImage_mbrtoc32.fn_rpl_mbrtoc32;
  HelloImage_mbrtoc32.item_mbrtoc32'23internal_state;
  HelloImage_mbrtoc32.item_mbrtoc32'23str'2e36;
  IFunc HelloImage_mbrtowc.fn_rpl_mbrtowc;
  HelloImage_mbsrtowcsZ2dstate.item__gl_mbsrtowcs_state;
  IFunc HelloImage_mbsrtowcs.fn_rpl_mbsrtowcs;
  IFunc HelloImage_mbszero.fn_mbszero;
  IFunc HelloImage_memeq.fn_memeq;
  IFunc HelloImage_progname.fn_set_program_name;
  HelloImage_progname.item_program_name;
  HelloImage_progname.item_progname'23str'2e3;
  HelloImage_progname.item_progname'23str'2e4;
  IFunc HelloImage_propername.fn_proper_name;
  IFunc HelloImage_quotearg.fn_set_char_quoting;
  IFunc HelloImage_quotearg.fn_quotearg'23gettext_quote;
  IFunc HelloImage_quotearg.fn_quotearg'23quotearg_buffer_restyled;
  IFunc HelloImage_quotearg.fn_quotearg_char_mem;
  IFunc HelloImage_quotearg.fn_quotearg_char;
  IFunc HelloImage_quotearg.fn_quotearg_colon;
  HelloImage_quotearg.item_quotearg'23default_quoting_options;
  HelloImage_quotearg.item_quotearg'23gettext_quote'2equote'2e83;
  HelloImage_quotearg.item_quotearg'23nslots;
  HelloImage_quotearg.item_quotearg'23slot0;
  HelloImage_quotearg.item_quotearg'23slotvec;
  HelloImage_quotearg.item_quotearg'23slotvec0;
  HelloImage_quotearg.item_quotearg'23str'2e82;
  HelloImage_quotearg.item_quotearg'23str'2e84;
  HelloImage_quotearg.item_quotearg'23str'2e85;
  HelloImage_quotearg.item_quotearg'23str'2e86;
  IFunc HelloImage_setlocale_nullZ2dunlocked.fn_setlocale_null_unlocked;
  IFunc HelloImage_setlocale_nullZ2dunlocked.fn_setlocale_null_r_unlocked;
  IFunc HelloImage_setlocale_null.fn_setlocale_null_r;
  IFunc HelloImage_streq.fn_streq;
  IFunc HelloImage_strnlen1.fn_strnlen1;
  HelloImage_versionZ2detcZ2dfsf.item_version_etc_copyright;
  IFunc HelloImage_versionZ2detc.fn_version_etc_arn;
  IFunc HelloImage_versionZ2detc.fn_version_etc_va;
  IFunc HelloImage_versionZ2detc.fn_version_etc;
  IFunc HelloImage_versionZ2detc.fn_emit_bug_reporting_address;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e41;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e42;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e43;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e44;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e45;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e46;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e47;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e48;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e49;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e50;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e51;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e52].

Local Lemma hello_image_linked_items_01_zero : zero_nonneg hello_image_linked_items_01 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_02 : module :=
  [HelloImage_versionZ2detc.item_version'2detc'23str'2e53;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e54;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e55;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e56;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e57;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e58;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e59;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e60;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e61;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e62;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e63;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e64;
  IFunc HelloImage_xallocZ2ddie.fn_xalloc_die;
  HelloImage_xallocZ2ddie.item_xalloc'2ddie'23str'2e41;
  HelloImage_xallocZ2ddie.item_xalloc'2ddie'23str'2e42;
  HelloImage_xallocZ2ddie.item_xalloc'2ddie'23str'2e43;
  IFunc HelloImage_xmalloc.fn_xmalloc;
  IFunc HelloImage_xmalloc.fn_xcharalloc;
  IFunc HelloImage_xmalloc.fn_xrealloc;
  IFunc HelloImage_xmalloc.fn_xpalloc;
  IFunc HelloImage_hello.fn_main;
  HelloImage_hello.item_hello'23parse_options'2elongopts'2e64;
  HelloImage_hello.item_hello'23str'2e54;
  HelloImage_hello.item_hello'23str'2e55;
  HelloImage_hello.item_hello'23str'2e56;
  HelloImage_hello.item_hello'23str'2e57;
  HelloImage_hello.item_hello'23str'2e58;
  HelloImage_hello.item_hello'23str'2e59;
  HelloImage_hello.item_hello'23str'2e60;
  HelloImage_hello.item_hello'23str'2e61;
  HelloImage_hello.item_hello'23str'2e62;
  HelloImage_hello.item_hello'23str'2e63;
  HelloImage_hello.item_hello'23str'2e65;
  HelloImage_hello.item_hello'23str'2e66;
  HelloImage_hello.item_hello'23str'2e67;
  HelloImage_hello.item_hello'23str'2e68;
  HelloImage_hello.item_hello'23str'2e69;
  HelloImage_hello.item_hello'23str'2e70;
  HelloImage_hello.item_hello'23str'2e71;
  HelloImage_hello.item_hello'23str'2e72;
  HelloImage_hello.item_hello'23str'2e73;
  HelloImage_hello.item_hello'23str'2e74;
  HelloImage_hello.item_hello'23str'2e75;
  HelloImage_hello.item_hello'23str'2e76;
  HelloImage_hello.item_hello'23str'2e77;
  HelloImage_hello.item_hello'23str'2e78;
  HelloImage_hello.item_hello'23str'2e79;
  HelloImage_hello.item_hello'23str'2e80;
  HelloImage_hello.item_hello'23str'2e81;
  HelloImage_hello.item_hello'23str'2e82;
  HelloImage_hello.item_hello'23str'2e83;
  IFunc Unit_assert___libc_assert_fail_os.fn___libc_assert_fail;
  Unit_assert___libc_assert_fail_os.item_glibc___libc_assert_fail'23str'2e21;
  Unit_assert___libc_assert_fail_os.item_glibc___libc_assert_fail'23str'2e22;
  IFunc Unit_csu_errnoZ2dloc_os.fn___GI___errno_location;
  Unit_csu_errnoZ2dloc_os.item___errno_location;
  Unit_csu_errno_os.item___libc_errno;
  Unit_csu_errno_os.item_errno;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___ctype_b_loc;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___GI___ctype_init;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype32_b;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype32_tolower;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype32_toupper;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype_b].

Local Lemma hello_image_linked_items_02_zero : zero_nonneg hello_image_linked_items_02 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_03 : module :=
  [Unit_ctype_ctypeZ2dinfo_os.item___ctype_tolower;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype_toupper;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_B;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_TOLOWER;
  Unit_ctype_ctypeZ2dinfo_os.item___libc_tsd_CTYPE_TOUPPER;
  IFunc Unit_debug_chk_fail_os.fn___GI___chk_fail;
  Unit_debug_chk_fail_os.item_glibc_chk_fail'23str'2e134;
  IFunc Unit_debug_fortify_fail_os.fn___GI___fortify_fail;
  Unit_debug_fortify_fail_os.item_glibc_fortify_fail'23str'2e19;
  Unit_debug_fortify_fail_os.item_glibc_fortify_fail'23str'2e20;
  IFunc Unit_debug_readonlyZ2dareaZ2dfallback_os.fn___readonly_area_fallback;
  Unit_debug_readonlyZ2dareaZ2dfallback_os.item_glibc_readonly_area_fallback'23str'2e252;
  Unit_debug_readonlyZ2dareaZ2dfallback_os.item_glibc_readonly_area_fallback'23str'2e253;
  IFunc Unit_debug_readonlyZ2darea_os.fn___readonly_area;
  IFunc Unit_dirent_closedir_os.fn___closedir;
  IFunc Unit_dirent_getdents64_os.fn___GI___getdents64;
  IFunc Unit_dirent_opendir_os.fn___opendir;
  IFunc Unit_dirent_opendir_os.fn___alloc_dir;
  IFunc Unit_dirent_readdir64_os.fn___GI___readdir64;
  IFunc Unit_elf_dlZ2dlibc_os.fn___libc_dlopen_mode;
  IFunc Unit_elf_dlZ2dlibc_os.fn___libc_dlsym;
  IFunc Unit_elf_dlZ2dlibc_os.fn___libc_dlclose;
  Unit_elf_dlZ2dsupport_os.item___libc_stack_end;
  Unit_elf_dlZ2dsupport_os.item__dl_auxv;
  Unit_elf_dlZ2dsupport_os.item__dl_clktck;
  Unit_elf_dlZ2dsupport_os.item__dl_debug_mask;
  Unit_elf_dlZ2dsupport_os.item__dl_hwcap;
  Unit_elf_dlZ2dsupport_os.item__dl_hwcap2;
  Unit_elf_dlZ2dsupport_os.item__dl_minsigstacksize;
  Unit_elf_dlZ2dsupport_os.item__dl_pagesize;
  Unit_elf_dlZ2dsupport_os.item__dl_platform;
  Unit_elf_dlZ2dsupport_os.item__dl_thp_mode;
  Unit_elf_dlZ2dsupport_os.item__dl_x86_cpu_features;
  Unit_elf_dlZ2dsupport_os.item__dl_x86_feature_control;
  IFunc Unit_elf_dlZ2dtunables_os.fn_glibc_dl_tunables'23do_tunable_update_val;
  IFunc Unit_elf_dlZ2dtunables_os.fn___tunable_is_initialized;
  IFunc Unit_elf_dlZ2dtunables_os.fn___tunable_set_val;
  IFunc Unit_elf_dlZ2dtunables_os.fn___tunable_get_val;
  Unit_elf_dlZ2dtunables_os.item_glibc_dl_tunables'23tunable_list;
  Unit_elf_enblZ2dsecure_os.item___libc_enable_secure;
  IFunc Unit_iconv_gconv_os.fn___gconv;
  Unit_iconv_gconv_os.item_glibc_gconv'23str'2e269;
  Unit_iconv_gconv_os.item_glibc_gconv'23str'2e270;
  Unit_iconv_gconv_os.item_glibc_gconv'23str'2e271;
  Unit_iconv_gconv_os.item_glibc_gconv'23str'2e272;
  IFunc Unit_iconv_gconv_builtin_os.fn___gconv_get_builtin_trans;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23map;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e244;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e245;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e246;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e247;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e248;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e249;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e250;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e251;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e252;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e253;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e254;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e255;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e256;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e257;
  Unit_iconv_gconv_builtin_os.item_glibc_gconv_builtin'23str'2e258;
  IFunc Unit_iconv_gconv_cache_os.fn___gconv_load_cache;
  IFunc Unit_iconv_gconv_cache_os.fn_glibc_gconv_cache'23find_module_idx].

Local Lemma hello_image_linked_items_03_zero : zero_nonneg hello_image_linked_items_03 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_04 : module :=
  [IFunc Unit_iconv_gconv_cache_os.fn_glibc_gconv_cache'23find_module;
  IFunc Unit_iconv_gconv_cache_os.fn___gconv_compare_alias_cache;
  IFunc Unit_iconv_gconv_cache_os.fn___gconv_lookup_cache;
  IFunc Unit_iconv_gconv_cache_os.fn___gconv_release_cache;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23cache_malloced;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23cache_size;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23gconv_cache;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23str'2e281;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23str'2e282;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23str'2e284;
  IFunc Unit_iconv_gconv_charset_os.fn_glibc_gconv_charset'23gconv_parse_code;
  IFunc Unit_iconv_gconv_charset_os.fn___GI___gconv_create_spec;
  IFunc Unit_iconv_gconv_charset_os.fn___GI___gconv_destroy_spec;
  Unit_iconv_gconv_charset_os.item_glibc_gconv_charset'23str'2e244;
  Unit_iconv_gconv_charset_os.item_glibc_gconv_charset'23str'2e245;
  Unit_iconv_gconv_charset_os.item_glibc_gconv_charset'23str'2e246;
  Unit_iconv_gconv_charset_os.item_glibc_gconv_charset'23str'2e247;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23read_conf_file;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23add_alias2;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23add_module;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23__gconv_get_path;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23__gconv_read_conf;
  IFunc Unit_iconv_gconv_conf_os.fn___gconv_load_conf;
  Unit_iconv_gconv_conf_os.item___gconv_max_path_elem_len;
  Unit_iconv_gconv_conf_os.item___gconv_path_elem;
  Unit_iconv_gconv_conf_os.item___gconv_path_envvar;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23builtin_aliases;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23builtin_modules;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23default_gconv_path;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23empty_path_elem;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23gconv_conf_filename;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23gconv_module_ext;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23once;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23read_conf_file'2emodcounter'2e270;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e269;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e271;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e272;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e274;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e275;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e276;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e277;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e278;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e279;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e280;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e281;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e282;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e283;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e284;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e285;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e286;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e287;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e288;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e289;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e290;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e291;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e292;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e293;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e294;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e295;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e296;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e297;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e298;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e299;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e300].

Local Lemma hello_image_linked_items_04_zero : zero_nonneg hello_image_linked_items_04 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_05 : module :=
  [Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e301;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_alias_compare;
  IFunc Unit_iconv_gconv_db_os.fn_glibc_gconv_db'23derivation_compare;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_release_step;
  IFunc Unit_iconv_gconv_db_os.fn_glibc_gconv_db'23find_derivation;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_compare_alias;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_find_transform;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_close_transform;
  Unit_iconv_gconv_db_os.item___gconv_alias_db;
  Unit_iconv_gconv_db_os.item___gconv_lock;
  Unit_iconv_gconv_db_os.item___gconv_modules_db;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23known_derivations;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23str'2e275;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23str'2e276;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23str'2e277;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23str'2e278;
  IFunc Unit_iconv_gconv_dl_os.fn_glibc_gconv_dl'23known_compare;
  IFunc Unit_iconv_gconv_dl_os.fn___gconv_find_shlib;
  IFunc Unit_iconv_gconv_dl_os.fn_glibc_gconv_dl'23do_release_shlib;
  IFunc Unit_iconv_gconv_dl_os.fn___gconv_release_shlib;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23loaded;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e274;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e275;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e276;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e277;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e278;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e279;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e280;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e281;
  IFunc Unit_iconv_gconv_open_os.fn___GI___gconv_open;
  Unit_iconv_gconv_open_os.item_glibc_gconv_open'23str'2e243;
  Unit_iconv_gconv_open_os.item_glibc_gconv_open'23str'2e244;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_btwoc_ascii;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ucs4;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ucs4_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ucs4le;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ucs4le_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ascii_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ascii;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_utf8;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_utf8_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ucs2_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ucs2;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ucs2reverse_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ucs2reverse;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23utf8_internal_loop_single'2einmask'2e318;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e270;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e271;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e272;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e273;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e274;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e275;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e276;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e277;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e278;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e279;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e280;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e281;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e282;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e283;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e284;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e285;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e286;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e287].

Local Lemma hello_image_linked_items_05_zero : zero_nonneg hello_image_linked_items_05 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_06 : module :=
  [Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e288;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e289;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e290;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e291;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e292;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e293;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e294;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e295;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e297;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e300;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e304;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e306;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e309;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e315;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e316;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e317;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e319;
  IFunc Unit_iconv_gconv_trans_os.fn___GI___gconv_transliterate;
  IFunc Unit_intl_dcgettext_os.fn___GI___dcgettext;
  IFunc Unit_intl_dcigettext_os.fn_glibc_dcigettext'23transcmp;
  IFunc Unit_intl_dcigettext_os.fn_glibc_dcigettext'23plural_eval_recurse;
  IFunc Unit_intl_dcigettext_os.fn___dcigettext;
  IFunc Unit_intl_dcigettext_os.fn__nl_find_msg;
  IFunc Unit_intl_dcigettext_os.fn_glibc_dcigettext'23get_output_charset;
  IFunc Unit_intl_dcigettext_os.fn_glibc_dcigettext'23__bswap_32;
  Unit_intl_dcigettext_os.item__nl_current_default_domain;
  Unit_intl_dcigettext_os.item__nl_default_default_domain;
  Unit_intl_dcigettext_os.item___GI__nl_default_dirname;
  Unit_intl_dcigettext_os.item__nl_domain_bindings;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23_nl_find_msg'2efreemem'2e283;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23_nl_find_msg'2efreemem_size'2e284;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23_nl_find_msg'2elock'2e282;
  Unit_intl_dcigettext_os.item__nl_state_lock;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23get_output_charset'2eoutput_charset_cache'2e286;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23get_output_charset'2eoutput_charset_cached'2e287;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23root;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23transmem_list;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23tree_lock;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e275;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e276;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e277;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e278;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e279;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e280;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e281;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e285;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e288;
  IFunc Unit_intl_explodename_os.fn__nl_explode_name;
  IFunc Unit_intl_finddomain_os.fn__nl_find_domain;
  Unit_intl_finddomain_os.item_glibc_finddomain'23_nl_find_domain'2elock'2e265;
  Unit_intl_finddomain_os.item_glibc_finddomain'23_nl_loaded_domains;
  IFunc Unit_intl_l10nflist_os.fn_glibc_l10nflist'23argz_count__;
  IFunc Unit_intl_l10nflist_os.fn_glibc_l10nflist'23argz_stringify__;
  IFunc Unit_intl_l10nflist_os.fn__nl_make_l10nflist;
  IFunc Unit_intl_l10nflist_os.fn__nl_normalize_codeset;
  IFunc Unit_intl_l10nflist_os.fn_glibc_l10nflist'23pop;
  Unit_intl_l10nflist_os.item_glibc_l10nflist'23str'2e130;
  IFunc Unit_intl_loadmsgcat_os.fn_glibc_loadmsgcat'23get_sysdep_segment_value;
  IFunc Unit_intl_loadmsgcat_os.fn__nl_load_domain;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23_nl_load_domain'2elock'2e289;
  Unit_intl_loadmsgcat_os.item__nl_msg_cat_cntr;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e264;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e265;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e266].

Local Lemma hello_image_linked_items_06_zero : zero_nonneg hello_image_linked_items_06 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_07 : module :=
  [Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e267;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e268;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e269;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e270;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e271;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e272;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e273;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e274;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e275;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e276;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e277;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e278;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e279;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e280;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e281;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e282;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e283;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e284;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e285;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e286;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e287;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e288;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e293;
  IFunc Unit_intl_localealias_os.fn__nl_expand_alias;
  IFunc Unit_intl_localealias_os.fn_glibc_localealias'23read_alias_file;
  IFunc Unit_intl_localealias_os.fn_glibc_localealias'23alias_compare;
  Unit_intl_localealias_os.item_glibc_localealias'23_nl_expand_alias'2elocale_alias_path'2e266;
  Unit_intl_localealias_os.item_glibc_localealias'23lock;
  Unit_intl_localealias_os.item_glibc_localealias'23map;
  Unit_intl_localealias_os.item_glibc_localealias'23maxmap;
  Unit_intl_localealias_os.item_glibc_localealias'23nmap;
  Unit_intl_localealias_os.item_glibc_localealias'23read_alias_file'2ealiasfile'2e268;
  Unit_intl_localealias_os.item_glibc_localealias'23string_space;
  Unit_intl_localealias_os.item_glibc_localealias'23string_space_act;
  Unit_intl_localealias_os.item_glibc_localealias'23string_space_max;
  Unit_intl_localealias_os.item_glibc_localealias'23str'2e267;
  Unit_intl_localealias_os.item_glibc_localealias'23str'2e269;
  IFunc Unit_intl_pluralZ2dexp_os.fn___gettext_extract_plural;
  Unit_intl_pluralZ2dexp_os.item___gettext_germanic_plural;
  Unit_intl_pluralZ2dexp_os.item_glibc_plural_exp'23plone;
  Unit_intl_pluralZ2dexp_os.item_glibc_plural_exp'23plvar;
  Unit_intl_pluralZ2dexp_os.item_glibc_plural_exp'23str'2e134;
  Unit_intl_pluralZ2dexp_os.item_glibc_plural_exp'23str'2e135;
  IFunc Unit_intl_plural_os.fn___gettextparse;
  IFunc Unit_intl_plural_os.fn___gettext_free_exp;
  Unit_intl_plural_os.item_glibc_plural'23__gettextparse'2eyyval_default'2e125;
  Unit_intl_plural_os.item_glibc_plural'23yycheck;
  Unit_intl_plural_os.item_glibc_plural'23yydefact;
  Unit_intl_plural_os.item_glibc_plural'23yydefgoto;
  Unit_intl_plural_os.item_glibc_plural'23yypact;
  Unit_intl_plural_os.item_glibc_plural'23yypgoto;
  Unit_intl_plural_os.item_glibc_plural'23yyr1;
  Unit_intl_plural_os.item_glibc_plural'23yyr2;
  Unit_intl_plural_os.item_glibc_plural'23yystos;
  Unit_intl_plural_os.item_glibc_plural'23yytable;
  Unit_intl_plural_os.item_glibc_plural'23yytranslate;
  Unit_intl_plural_os.item_glibc_plural'23str'2e124;
  Unit_intl_plural_os.item_glibc_plural'23str'2e126;
  Unit_intl_plural_os.item_glibc_plural'23str'2e127;
  Unit_intl_plural_os.item_glibc_plural'23str'2e128;
  Unit_intl_plural_os.item_glibc_plural'23str'2e129;
  Unit_intl_plural_os.item_glibc_plural'23str'2e130;
  Unit_intl_plural_os.item_glibc_plural'23str'2e131;
  IFunc Unit_io_close_nocancel_os.fn___GI___close_nocancel].

Local Lemma hello_image_linked_items_07_zero : zero_nonneg hello_image_linked_items_07 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_08 : module :=
  [IFunc Unit_io_close_nocancel_nostatus_os.fn___GI___close_nocancel_nostatus;
  IFunc Unit_io_fstat64_os.fn___GI___fstat64;
  IFunc Unit_io_fstatat64_os.fn___GI___fstatat64;
  IFunc Unit_io_getcwd_os.fn___GI___getcwd;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e242;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e243;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e244;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e245;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e246;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e247;
  IFunc Unit_io_lseek64_os.fn___lseek64;
  IFunc Unit_io_open64_os.fn___libc_open64;
  Unit_io_open64_os.item___GI___open;
  IFunc Unit_io_open64_nocancel_os.fn___GI___open64_nocancel;
  Unit_io_open64_nocancel_os.item___GI___open_nocancel;
  IFunc Unit_io_read_os.fn___GI___libc_read;
  Unit_io_read_os.item___GI___read;
  IFunc Unit_io_read_nocancel_os.fn___GI___read_nocancel;
  IFunc Unit_io_stat64_os.fn___GI___stat64;
  IFunc Unit_io_write_os.fn___GI___libc_write;
  Unit_io_write_os.item___GI___write;
  Unit_io_write_os.item___GI_write;
  IFunc Unit_io_write_nocancel_os.fn___GI___write_nocancel;
  IFunc Unit_libio___fpending_os.fn___fpending;
  IFunc Unit_libio_feof_u_os.fn___feof_unlocked;
  IFunc Unit_libio_ferror_os.fn__IO_ferror;
  Unit_libio_ferror_os.item_ferror;
  IFunc Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_init_internal;
  IFunc Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_close_it;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_finish;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_open;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_fopen;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_setbuf;
  IFunc Unit_libio_fileops_os.fn__IO_file_setbuf_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_new_do_write;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_underflow;
  IFunc Unit_libio_fileops_os.fn_glibc_fileops'23mmap_remap_check;
  IFunc Unit_libio_fileops_os.fn__IO_file_underflow_mmap;
  IFunc Unit_libio_fileops_os.fn_glibc_fileops'23decide_maybe_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_file_underflow_maybe_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_overflow;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_sync;
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
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e265;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e266;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e267;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e268;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e269;
  Unit_libio_fileops_os.item___GI__IO_file_xsputn].

Local Lemma hello_image_linked_items_08_zero : zero_nonneg hello_image_linked_items_08 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_09 : module :=
  [Unit_libio_fileops_os.item___GI__IO_file_seekoff;
  Unit_libio_fileops_os.item___GI__IO_file_sync;
  Unit_libio_fileops_os.item___GI__IO_file_overflow;
  Unit_libio_fileops_os.item___GI__IO_file_underflow;
  Unit_libio_fileops_os.item___GI__IO_do_write;
  Unit_libio_fileops_os.item___GI__IO_file_setbuf;
  Unit_libio_fileops_os.item___GI__IO_file_fopen;
  Unit_libio_fileops_os.item___GI__IO_file_finish;
  IFunc Unit_libio_genops_os.fn_glibc_genops'23flush_cleanup;
  IFunc Unit_libio_genops_os.fn___GI__IO_un_link;
  IFunc Unit_libio_genops_os.fn___GI__IO_link_in;
  IFunc Unit_libio_genops_os.fn__IO_switch_to_main_get_area;
  IFunc Unit_libio_genops_os.fn__IO_switch_to_backup_area;
  IFunc Unit_libio_genops_os.fn___GI__IO_switch_to_get_mode;
  IFunc Unit_libio_genops_os.fn___GI__IO_free_backup_area;
  IFunc Unit_libio_genops_os.fn___GI___overflow;
  IFunc Unit_libio_genops_os.fn_glibc_genops'23save_for_backup;
  IFunc Unit_libio_genops_os.fn___GI___underflow;
  IFunc Unit_libio_genops_os.fn___GI___uflow;
  IFunc Unit_libio_genops_os.fn___GI__IO_setb;
  IFunc Unit_libio_genops_os.fn___GI__IO_doallocbuf;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_uflow;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_xsputn;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_xsgetn;
  IFunc Unit_libio_genops_os.fn__IO_default_setbuf;
  IFunc Unit_libio_genops_os.fn__IO_default_seekpos;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_doallocate;
  IFunc Unit_libio_genops_os.fn__IO_old_init;
  IFunc Unit_libio_genops_os.fn__IO_no_init;
  IFunc Unit_libio_genops_os.fn__IO_default_sync;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_finish;
  IFunc Unit_libio_genops_os.fn___GI__IO_sputbackc;
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
  Unit_libio_genops_os.item_glibc_genops'23stdio_needs_locking;
  IFunc Unit_libio_iofclose_os.fn__IO_new_fclose;
  Unit_libio_iofclose_os.item_fclose;
  IFunc Unit_libio_iofflush_os.fn___GI__IO_fflush;
  IFunc Unit_libio_iofopen_os.fn___fopen_maybe_mmap;
  IFunc Unit_libio_iofopen_os.fn___fopen_internal;
  IFunc Unit_libio_iofopen_os.fn__IO_new_fopen;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_read;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_write;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_seek;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_close;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_seekoff;
  IFunc Unit_libio_iofputs_os.fn___GI__IO_fputs;
  Unit_libio_iofputs_os.item_fputs;
  IFunc Unit_libio_iofwide_os.fn__IO_fwide;
  IFunc Unit_libio_iofwide_os.fn___libio_codecvt_out;
  IFunc Unit_libio_iofwide_os.fn___libio_codecvt_in].

Local Lemma hello_image_linked_items_09_zero : zero_nonneg hello_image_linked_items_09 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_10 : module :=
  [IFunc Unit_libio_iofwide_os.fn___libio_codecvt_encoding;
  IFunc Unit_libio_iofwide_os.fn___libio_codecvt_length;
  Unit_libio_iofwide_os.item_glibc_iofwide'23str'2e288;
  Unit_libio_iofwide_os.item_glibc_iofwide'23str'2e289;
  Unit_libio_iofwide_os.item_glibc_iofwide'23str'2e290;
  Unit_libio_iofwide_os.item_glibc_iofwide'23str'2e291;
  IFunc Unit_libio_iogetdelim_os.fn___GI___getdelim;
  IFunc Unit_libio_iogetline_os.fn___GI__IO_getline;
  IFunc Unit_libio_iogetline_os.fn___GI__IO_getline_info;
  IFunc Unit_libio_iopopen_os.fn_glibc_iopopen'23unlock;
  IFunc Unit_libio_iopopen_os.fn__IO_new_proc_close;
  Unit_libio_iopopen_os.item_glibc_iopopen'23proc_file_chain;
  Unit_libio_iopopen_os.item_glibc_iopopen'23proc_file_chain_lock;
  IFunc Unit_libio_iovdprintf_os.fn___printf_buffer_flush_dprintf;
  IFunc Unit_libio_libc_fatal_os.fn___libc_message_impl;
  IFunc Unit_libio_libc_fatal_os.fn___GI___libc_fatal;
  Unit_libio_libc_fatal_os.item_glibc_libc_fatal'23str'2e298;
  Unit_libio_libc_fatal_os.item_glibc_libc_fatal'23str'2e299;
  Unit_libio_libc_fatal_os.item_glibc_libc_fatal'23str'2e300;
  IFunc Unit_libio_memstream_os.fn__IO_mem_sync;
  IFunc Unit_libio_memstream_os.fn__IO_mem_finish;
  IFunc Unit_libio_memstream_os.fn__IO_mem_setbuf;
  IFunc Unit_libio_memstream_os.fn__IO_mem_doallocate;
  IFunc Unit_libio_obprintf_os.fn___printf_buffer_flush_obstack;
  IFunc Unit_libio_stdfiles_os.fn_glibc_stdfiles'23_IO_stdfiles_init;
  Unit_libio_stdfiles_os.item__IO_2_1_stderr_;
  Unit_libio_stdfiles_os.item__IO_2_1_stdin_;
  Unit_libio_stdfiles_os.item__IO_2_1_stdout_;
  Unit_libio_stdfiles_os.item___GI__IO_list_all;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_0_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_1_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_2_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_0;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_1;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_2;
  Unit_libio_stdfiles_os.item___nanofil_ctor__IO_stdfiles_init;
  Unit_libio_stdio_os.item_stderr;
  Unit_libio_stdio_os.item_stdout;
  IFunc Unit_libio_strops_os.fn___GI__IO_str_overflow;
  IFunc Unit_libio_strops_os.fn___GI__IO_str_underflow;
  IFunc Unit_libio_strops_os.fn__IO_str_count;
  IFunc Unit_libio_strops_os.fn_glibc_strops'23enlarge_userbuf;
  IFunc Unit_libio_strops_os.fn___GI__IO_str_seekoff;
  IFunc Unit_libio_strops_os.fn___GI__IO_str_pbackfail;
  IFunc Unit_libio_strops_os.fn__IO_str_finish;
  Unit_libio_strops_os.item_glibc_strops'23str'2e257;
  Unit_libio_strops_os.item_glibc_strops'23str'2e258;
  Unit_libio_strops_os.item_glibc_strops'23str'2e259;
  IFunc Unit_libio_vasprintf_os.fn___printf_buffer_flush_asprintf;
  IFunc Unit_libio_vasprintf_os.fn___vasprintf_internal;
  IFunc Unit_libio_vsnprintf_os.fn___printf_buffer_flush_snprintf;
  IFunc Unit_libio_vsnprintf_os.fn___printf_buffer_snprintf_init;
  IFunc Unit_libio_vsnprintf_os.fn___printf_buffer_snprintf_done;
  IFunc Unit_libio_vsnprintf_os.fn___vsnprintf_internal;
  IFunc Unit_libio_vtables_os.fn__IO_vtable_check;
  IFunc Unit_libio_vtables_os.fn_glibc_vtables'23check_stdfiles_vtables;
  Unit_libio_vtables_os.item_IO_accept_foreign_vtables;
  Unit_libio_vtables_os.item___io_vtables;
  Unit_libio_vtables_os.item_glibc_vtables'23str'2e302;
  Unit_libio_vtables_os.item___nanofil_ctor_check_stdfiles_vtables;
  IFunc Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wdo_write;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_underflow;
  IFunc Unit_libio_wfileops_os.fn__IO_wfile_underflow_mmap].

Local Lemma hello_image_linked_items_10_zero : zero_nonneg hello_image_linked_items_10 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_11 : module :=
  [IFunc Unit_libio_wfileops_os.fn__IO_wfile_underflow_maybe_mmap;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_overflow;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_sync;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_seekoff;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_xsputn;
  Unit_libio_wfileops_os.item_glibc_wfileops'23str'2e254;
  Unit_libio_wfileops_os.item_glibc_wfileops'23str'2e255;
  Unit_libio_wfileops_os.item_glibc_wfileops'23str'2e256;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_least_wmarker;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_switch_to_main_wget_area;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_switch_to_wbackup_area;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wsetb;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_pbackfail;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_finish;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_uflow;
  IFunc Unit_libio_wgenops_os.fn___GI___woverflow;
  IFunc Unit_libio_wgenops_os.fn___GI___wunderflow;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_xsputn;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_xsgetn;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdoallocbuf;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_doallocate;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_switch_to_wget_mode;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_free_wbackup_area;
  IFunc Unit_libio_wgenops_os.fn_glibc_wgenops'23save_for_wbackup;
  IFunc Unit_libio_wmemstream_os.fn__IO_wmem_sync;
  IFunc Unit_libio_wmemstream_os.fn__IO_wmem_finish;
  IFunc Unit_libio_wmemstream_os.fn__IO_wmem_setbuf;
  IFunc Unit_libio_wmemstream_os.fn__IO_wmem_doallocate;
  IFunc Unit_libio_wprintf_os.fn___wprintf;
  Unit_libio_wprintf_os.item_wprintf;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_overflow;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_underflow;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_count;
  IFunc Unit_libio_wstrops_os.fn_glibc_wstrops'23enlarge_userbuf;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_seekoff;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_pbackfail;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_finish;
  Unit_libio_wstrops_os.item_glibc_wstrops'23str'2e257;
  Unit_libio_wstrops_os.item_glibc_wstrops'23str'2e258;
  Unit_libio_wstrops_os.item_glibc_wstrops'23str'2e259;
  Unit_locale_CZ2daddress_os.item__nl_C_LC_ADDRESS;
  Unit_locale_CZ2daddress_os.item_glibc_C_address'23str'2e40;
  Unit_locale_CZ2daddress_os.item_glibc_C_address'23str'2e41;
  Unit_locale_CZ2dcollate_os.item__nl_C_LC_COLLATE;
  Unit_locale_CZ2dcollate_os.item_glibc_C_collate'23collseqmb;
  Unit_locale_CZ2dcollate_os.item_glibc_C_collate'23collseqwc;
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
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_tolower].

Local Lemma hello_image_linked_items_11_zero : zero_nonneg hello_image_linked_items_11 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_12 : module :=
  [Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_toupper;
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
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e277;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e278;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e279;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e280;
  Unit_locale_CZ2didentification_os.item__nl_C_LC_IDENTIFICATION;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e40;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e41;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e42;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e43;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e44;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e45;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e46;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e47;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e48;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e49;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e50;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e51;
  Unit_locale_CZ2dmeasurement_os.item__nl_C_LC_MEASUREMENT;
  Unit_locale_CZ2dmeasurement_os.item_glibc_C_measurement'23str'2e40;
  Unit_locale_CZ2dmessages_os.item__nl_C_LC_MESSAGES;
  Unit_locale_CZ2dmessages_os.item_glibc_C_messages'23str'2e40;
  Unit_locale_CZ2dmessages_os.item_glibc_C_messages'23str'2e41;
  Unit_locale_CZ2dmessages_os.item_glibc_C_messages'23str'2e42;
  Unit_locale_CZ2dmonetary_os.item__nl_C_LC_MONETARY;
  Unit_locale_CZ2dmonetary_os.item_glibc_C_monetary'23conversion_rate;
  Unit_locale_CZ2dmonetary_os.item_glibc_C_monetary'23not_available;
  Unit_locale_CZ2dmonetary_os.item_glibc_C_monetary'23str'2e40;
  Unit_locale_CZ2dmonetary_os.item_glibc_C_monetary'23str'2e41;
  Unit_locale_CZ2dname_os.item__nl_C_LC_NAME;
  Unit_locale_CZ2dname_os.item_glibc_C_name'23str'2e40;
  Unit_locale_CZ2dname_os.item_glibc_C_name'23str'2e41;
  Unit_locale_CZ2dnumeric_os.item__nl_C_LC_NUMERIC;
  Unit_locale_CZ2dnumeric_os.item_glibc_C_numeric'23str'2e40;
  Unit_locale_CZ2dnumeric_os.item_glibc_C_numeric'23str'2e41;
  Unit_locale_CZ2dpaper_os.item__nl_C_LC_PAPER;
  Unit_locale_CZ2dtelephone_os.item__nl_C_LC_TELEPHONE;
  Unit_locale_CZ2dtelephone_os.item_glibc_C_telephone'23str'2e40;
  Unit_locale_CZ2dtelephone_os.item_glibc_C_telephone'23str'2e41].

Local Lemma hello_image_linked_items_12_zero : zero_nonneg hello_image_linked_items_12 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_13 : module :=
  [Unit_locale_CZ2dtime_os.item__nl_C_LC_TIME;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e100;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e101;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e102;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e103;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e104;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e105;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e106;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e107;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e108;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e109;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e110;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e111;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e112;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e113;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e114;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e115;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e116;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e117;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e118;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e119;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e120;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e121;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e122;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e123;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e124;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e125;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e126;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e127;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e128;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e129;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e130;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e131;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e132;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e133;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e40;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e41;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e42;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e43;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e44;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e45;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e46;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e47;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e48;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e49;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e50;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e51;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e52;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e53;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e54;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e55;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e56;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e57;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e58;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e59;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e60;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e61;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e62;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e63;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e64;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e65;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e66;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e67;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e68].

Local Lemma hello_image_linked_items_13_zero : zero_nonneg hello_image_linked_items_13 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_14 : module :=
  [Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e69;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e70;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e71;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e72;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e73;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e74;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e75;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e76;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e77;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e78;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e79;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e80;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e81;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e82;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e83;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e84;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e85;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e86;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e87;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e88;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e89;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e90;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e91;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e92;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e93;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e94;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e95;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e96;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e97;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e98;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e99;
  Unit_locale_C_name_os.item__nl_C_codeset;
  Unit_locale_C_name_os.item__nl_C_name;
  Unit_locale_C_name_os.item__nl_POSIX_name;
  Unit_locale_SYS_libc_os.item___GI__libc_intl_domainname;
  IFunc Unit_locale_findlocale_os.fn__nl_find_locale;
  Unit_locale_findlocale_os.item__nl_default_locale_path;
  Unit_locale_findlocale_os.item_glibc_findlocale'23_nl_find_locale'2ecodeset_idx'2e245;
  Unit_locale_findlocale_os.item__nl_locale_file_list;
  Unit_locale_findlocale_os.item_glibc_findlocale'23valid_locale_name'2eslashdot'2e250;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e243;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e244;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e246;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e247;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e248;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e249;
  Unit_locale_globalZ2dlocale_os.item___libc_tsd_LOCALE;
  Unit_locale_globalZ2dlocale_os.item__nl_global_locale;
  IFunc Unit_locale_lcZ2dctype_os.fn__nl_postload_ctype;
  IFunc Unit_locale_loadarchive_os.fn__nl_load_locale_from_archive;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23archfname;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23archive_stat;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23archloaded;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23archmapped;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23headmap;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e249;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e250;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e251;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e252;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e254;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e255;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e256;
  IFunc Unit_locale_loadlocale_os.fn__nl_intern_locale_data;
  IFunc Unit_locale_loadlocale_os.fn__nl_load_locale].

Local Lemma hello_image_linked_items_14_zero : zero_nonneg hello_image_linked_items_14 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_15 : module :=
  [Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_category_num_items;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_ADDRESS;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_COLLATE;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_CTYPE;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_IDENTIFICATION;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_MEASUREMENT;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_MESSAGES;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_MONETARY;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_NAME;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_NUMERIC;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_PAPER;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_TELEPHONE;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_TIME;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_types;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23str'2e240;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23str'2e241;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23str'2e242;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23str'2e243;
  IFunc Unit_locale_localename_os.fn___current_locale_name;
  IFunc Unit_locale_mb_cur_max_os.fn___ctype_get_mb_cur_max;
  IFunc Unit_locale_setlocale_os.fn_glibc_setlocale'23new_composite_name;
  IFunc Unit_locale_setlocale_os.fn___GI_setlocale;
  Unit_locale_setlocale_os.item___libc_setlocale_lock;
  Unit_locale_setlocale_os.item__nl_category_name_idxs;
  Unit_locale_setlocale_os.item__nl_category_name_sizes;
  Unit_locale_setlocale_os.item__nl_category_names;
  Unit_locale_setlocale_os.item_glibc_setlocale'23_nl_category_postload;
  Unit_locale_setlocale_os.item_glibc_setlocale'23str'2e234;
  Unit_locale_setlocale_os.item_setlocale;
  Unit_locale_xlocale_os.item__nl_C_locobj;
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
  IFunc Unit_malloc_malloc_os.fn___GI___libc_realloc;
  IFunc Unit_malloc_malloc_os.fn___libc_calloc;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23malloc_printerr;
  Unit_malloc_malloc_os.item_malloc;
  Unit_malloc_malloc_os.item_realloc;
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
  IFunc Unit_malloc_obstack_os.fn___GI__obstack_newchunk;
  IFunc Unit_malloc_obstack_os.fn_glibc_obstack'23print_and_abort].

Local Lemma hello_image_linked_items_15_zero : zero_nonneg hello_image_linked_items_15 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_16 : module :=
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

Local Lemma hello_image_linked_items_16_zero : zero_nonneg hello_image_linked_items_16 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_17 : module :=
  [IFunc Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer;
  IFunc Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore;
  IFunc Unit_nptl_lowlevellock_os.fn___GI___lll_lock_wait_private;
  IFunc Unit_nptl_lowlevellock_os.fn___GI___lll_lock_wake_private;
  IFunc Unit_nptl_pthread_once_os.fn_glibc_pthread_once'23clear_once_control;
  IFunc Unit_nptl_pthread_once_os.fn_glibc_pthread_once'23__pthread_once_slow;
  IFunc Unit_nptl_pthread_once_os.fn____pthread_once;
  IFunc Unit_nptl_pthread_once_os.fn_glibc_pthread_once'23__pthread_cleanup_combined_routine_voidptr;
  Unit_nptl_pthread_once_os.item___fork_generation;
  Unit_nptl_pthread_once_os.item___GI___pthread_once;
  IFunc Unit_nptl_pthread_rwlock_init_os.fn____pthread_rwlock_init;
  Unit_nptl_pthread_rwlock_init_os.item_glibc_pthread_rwlock_init'23default_rwlockattr;
  Unit_nptl_pthread_rwlock_init_os.item___GI___pthread_rwlock_init;
  IFunc Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock;
  Unit_nptl_pthread_rwlock_rdlock_os.item___GI___pthread_rwlock_rdlock;
  Unit_nptl_pthread_rwlock_rdlock_os.item_glibc_pthread_rwlock_rdlock'23str'2e286;
  Unit_nptl_pthread_rwlock_rdlock_os.item_glibc_pthread_rwlock_rdlock'23str'2e287;
  Unit_nptl_pthread_rwlock_rdlock_os.item_glibc_pthread_rwlock_rdlock'23str'2e288;
  Unit_nptl_pthread_rwlock_rdlock_os.item_glibc_pthread_rwlock_rdlock'23str'2e289;
  IFunc Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock;
  Unit_nptl_pthread_rwlock_unlock_os.item___GI___pthread_rwlock_unlock;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e286;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e287;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e288;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e289;
  IFunc Unit_nptl_pthread_rwlock_wrlock_os.fn____pthread_rwlock_wrlock;
  Unit_nptl_pthread_rwlock_wrlock_os.item___GI___pthread_rwlock_wrlock;
  Unit_nptl_pthread_rwlock_wrlock_os.item_glibc_pthread_rwlock_wrlock'23str'2e286;
  Unit_nptl_pthread_rwlock_wrlock_os.item_glibc_pthread_rwlock_wrlock'23str'2e287;
  Unit_nptl_pthread_rwlock_wrlock_os.item_glibc_pthread_rwlock_wrlock'23str'2e288;
  Unit_nptl_pthread_rwlock_wrlock_os.item_glibc_pthread_rwlock_wrlock'23str'2e289;
  IFunc Unit_nptl_pthread_setcancelstate_os.fn___GI___pthread_setcancelstate;
  IFunc Unit_nptl_unwind_os.fn_glibc_unwind'23unwind_stop;
  IFunc Unit_nptl_unwind_os.fn_glibc_unwind'23unwind_cleanup;
  IFunc Unit_nptl_unwind_os.fn___GI___pthread_unwind;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e287;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e288;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e289;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e290;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e291;
  IFunc Unit_nss_hashZ2dstring_os.fn___hash_string;
  IFunc Unit_posix__exit_os.fn___GI__exit;
  Unit_posix__exit_os.item__exit;
  Unit_posix_environ_os.item___environ;
  Unit_posix_environ_os.item___environ_counter;
  IFunc Unit_posix_get_child_max_os.fn___get_child_max;
  IFunc Unit_posix_getopt_os.fn_glibc_getopt'23process_long_option;
  IFunc Unit_posix_getopt_os.fn__getopt_internal_r;
  IFunc Unit_posix_getopt_os.fn__getopt_internal;
  Unit_posix_getopt_os.item_glibc_getopt'23getopt_data;
  Unit_posix_getopt_os.item_optarg;
  Unit_posix_getopt_os.item_opterr;
  Unit_posix_getopt_os.item_optind;
  Unit_posix_getopt_os.item_optopt;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e138;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e139;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e140;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e141;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e142;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e143;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e144;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e145;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e146;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e147].

Local Lemma hello_image_linked_items_17_zero : zero_nonneg hello_image_linked_items_17 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_18 : module :=
  [Unit_posix_getopt_os.item_glibc_getopt'23str'2e148;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e149;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e150;
  IFunc Unit_posix_getopt1_os.fn_getopt_long;
  IFunc Unit_posix_sysconf_os.fn___GI___sysconf;
  IFunc Unit_posix_sysconf_os.fn_glibc_sysconf'23posix_sysconf;
  IFunc Unit_posix_sysconf_os.fn_glibc_sysconf'23__sysconf_check_spec;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e302;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e303;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e304;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e305;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e306;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e307;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e308;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e309;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e348;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e349;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e350;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e351;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e353;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e354;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e355;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e356;
  IFunc Unit_posix_wait4_os.fn___GI___wait4;
  IFunc Unit_posix_waitpid_os.fn___GI___waitpid;
  IFunc Unit_resource_getrlimit64_os.fn___GI___getrlimit64;
  Unit_resource_getrlimit64_os.item___GI___getrlimit;
  IFunc Unit_setjmp_longjmp_os.fn___libc_siglongjmp;
  Unit_setjmp_longjmp_os.item___libc_longjmp;
  IFunc Unit_stdioZ2dcommon__fitoa_word_os.fn__itoa_word;
  IFunc Unit_stdioZ2dcommon_asprintf_os.fn____asprintf;
  Unit_stdioZ2dcommon_asprintf_os.item___GI___asprintf;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item__sys_errlist_internal;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item__sys_errlist_internal_len;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e247;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e248;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e249;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e250;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e251;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e252;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e253;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e254;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e255;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e256;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e257;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e258;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e259;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e260;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e261;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e262;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e263;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e264;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e265;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e266;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e267;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e268;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e269;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e270;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e271;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e272;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e273;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e274;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e275;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e276].

Local Lemma hello_image_linked_items_18_zero : zero_nonneg hello_image_linked_items_18 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_19 : module :=
  [Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e277;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e278;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e279;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e280;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e281;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e282;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e283;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e284;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e285;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e286;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e287;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e288;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e289;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e290;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e291;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e292;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e293;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e294;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e295;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e296;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e297;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e298;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e299;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e300;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e301;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e302;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e303;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e304;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e305;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e306;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e307;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e308;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e309;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e310;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e311;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e312;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e313;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e314;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e315;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e316;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e317;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e318;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e319;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e320;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e321;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e322;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e323;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e324;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e325;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e326;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e327;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e328;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e329;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e330;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e331;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e332;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e333;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e334;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e335;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e336;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e337;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e338;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e339;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e340].

Local Lemma hello_image_linked_items_19_zero : zero_nonneg hello_image_linked_items_19 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_20 : module :=
  [Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e341;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e342;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e343;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e344;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e345;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e346;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e347;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e348;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e349;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e350;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e351;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e352;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e353;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e354;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e355;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e356;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e357;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e358;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e359;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e360;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e361;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e362;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e363;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e364;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e365;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e366;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e367;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e368;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e369;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e370;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e371;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e372;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e373;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e374;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e375;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e376;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e377;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e378;
  IFunc Unit_stdioZ2dcommon_errlist_os.fn___get_errlist;
  IFunc Unit_stdioZ2dcommon_errname_os.fn___get_errname;
  Unit_stdioZ2dcommon_errname_os.item_glibc_errname'23_sys_errname;
  Unit_stdioZ2dcommon_errname_os.item_glibc_errname'23_sys_errnameidx;
  IFunc Unit_stdioZ2dcommon_fprintf_os.fn___fprintf;
  Unit_stdioZ2dcommon_fprintf_os.item_fprintf;
  IFunc Unit_stdioZ2dcommon_funlockfile_os.fn___GI___funlockfile;
  Unit_stdioZ2dcommon_funlockfile_os.item__IO_funlockfile;
  IFunc Unit_stdioZ2dcommon_fxprintf_os.fn___vfxprintf;
  IFunc Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf;
  IFunc Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf_nocancel;
  IFunc Unit_stdioZ2dcommon_grouping_iterator_os.fn___grouping_iterator_init_none;
  IFunc Unit_stdioZ2dcommon_grouping_iterator_os.fn___grouping_iterator_init;
  IFunc Unit_stdioZ2dcommon_grouping_iterator_os.fn___grouping_iterator_next;
  Unit_stdioZ2dcommon_grouping_iterator_os.item_glibc_grouping_iterator'23str'2e41;
  Unit_stdioZ2dcommon_grouping_iterator_os.item_glibc_grouping_iterator'23str'2e42;
  Unit_stdioZ2dcommon_grouping_iterator_os.item_glibc_grouping_iterator'23str'2e43;
  Unit_stdioZ2dcommon_itoaZ2ddigits_os.item___GI__itoa_lower_digits;
  Unit_stdioZ2dcommon_itoaZ2dudigits_os.item___GI__itoa_upper_digits;
  Unit_stdioZ2dcommon_itowaZ2ddigits_os.item__itowa_lower_digits;
  Unit_stdioZ2dcommon_itowaZ2ddigits_os.item__itowa_upper_digits;
  IFunc Unit_stdioZ2dcommon_printfZ2dparsemb_os.fn___parse_one_specmb;
  IFunc Unit_stdioZ2dcommon_printfZ2dparsewc_os.fn___parse_one_specwc;
  IFunc Unit_stdioZ2dcommon_printf_os.fn___printf;
  Unit_stdioZ2dcommon_printf_os.item_printf;
  IFunc Unit_stdioZ2dcommon_printf_buffer_as_file_os.fn___printf_buffer_as_file_overflow].

Local Lemma hello_image_linked_items_20_zero : zero_nonneg hello_image_linked_items_20 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_21 : module :=
  [IFunc Unit_stdioZ2dcommon_printf_buffer_as_file_os.fn___printf_buffer_as_file_xsputn;
  IFunc Unit_stdioZ2dcommon_printf_buffer_as_file_os.fn___printf_buffer_as_file_init;
  IFunc Unit_stdioZ2dcommon_printf_buffer_as_file_os.fn___printf_buffer_as_file_terminate;
  Unit_stdioZ2dcommon_printf_buffer_as_file_os.item_glibc_printf_buffer_as_file'23str'2e266;
  Unit_stdioZ2dcommon_printf_buffer_as_file_os.item_glibc_printf_buffer_as_file'23str'2e267;
  Unit_stdioZ2dcommon_printf_buffer_as_file_os.item_glibc_printf_buffer_as_file'23str'2e268;
  Unit_stdioZ2dcommon_printf_buffer_as_file_os.item_glibc_printf_buffer_as_file'23str'2e269;
  Unit_stdioZ2dcommon_printf_buffer_as_file_os.item_glibc_printf_buffer_as_file'23str'2e270;
  Unit_stdioZ2dcommon_printf_buffer_as_file_os.item_glibc_printf_buffer_as_file'23str'2e271;
  IFunc Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done;
  IFunc Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush;
  Unit_stdioZ2dcommon_printf_buffer_flush_os.item_glibc_printf_buffer_flush'23str'2e39;
  Unit_stdioZ2dcommon_printf_buffer_flush_os.item_glibc_printf_buffer_flush'23str'2e40;
  Unit_stdioZ2dcommon_printf_buffer_flush_os.item_glibc_printf_buffer_flush'23str'2e41;
  IFunc Unit_stdioZ2dcommon_printf_buffer_pad_1_os.fn___printf_buffer_pad_1;
  Unit_stdioZ2dcommon_printf_buffer_pad_1_os.item_glibc_printf_buffer_pad_1'23str'2e41;
  Unit_stdioZ2dcommon_printf_buffer_pad_1_os.item_glibc_printf_buffer_pad_1'23str'2e42;
  Unit_stdioZ2dcommon_printf_buffer_pad_1_os.item_glibc_printf_buffer_pad_1'23str'2e43;
  IFunc Unit_stdioZ2dcommon_printf_buffer_putc_1_os.fn___printf_buffer_putc_1;
  Unit_stdioZ2dcommon_printf_buffer_putc_1_os.item_glibc_printf_buffer_putc_1'23str'2e39;
  Unit_stdioZ2dcommon_printf_buffer_putc_1_os.item_glibc_printf_buffer_putc_1'23str'2e40;
  Unit_stdioZ2dcommon_printf_buffer_putc_1_os.item_glibc_printf_buffer_putc_1'23str'2e41;
  IFunc Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_switch;
  IFunc Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file;
  IFunc Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_init;
  IFunc Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done;
  Unit_stdioZ2dcommon_printf_buffer_to_file_os.item_glibc_printf_buffer_to_file'23str'2e266;
  Unit_stdioZ2dcommon_printf_buffer_to_file_os.item_glibc_printf_buffer_to_file'23str'2e267;
  Unit_stdioZ2dcommon_printf_buffer_to_file_os.item_glibc_printf_buffer_to_file'23str'2e268;
  IFunc Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write;
  Unit_stdioZ2dcommon_printf_buffer_write_os.item_glibc_printf_buffer_write'23str'2e41;
  Unit_stdioZ2dcommon_printf_buffer_write_os.item_glibc_printf_buffer_write'23str'2e42;
  Unit_stdioZ2dcommon_printf_buffer_write_os.item_glibc_printf_buffer_write'23str'2e43;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23round_away;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23hack_digit;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23__printf_fp_buffer_1;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn___printf_buffer_flush_fp;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn___printf_fp_l_buffer;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn___printf_buffer_flush_fp_to_wide;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn___wprintf_fp_l_buffer;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23__ctype_b_loc'2egnu_inline;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23__ctype_tolower_loc'2egnu_inline;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23__libc_use_alloca'2egnu_inline;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23__printf_buffer_mark_failed;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23__printf_buffer_pad;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23__printf_buffer_putc;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23__printf_buffer_puts;
  IFunc Unit_stdioZ2dcommon_printf_fp_os.fn_glibc_printf_fp'23get_rounding_mode;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e295;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e296;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e297;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e298;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e301;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e302;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e303;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e304;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e305;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e306;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e307;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e308;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e309;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e310;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e311;
  Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e312].

Local Lemma hello_image_linked_items_21_zero : zero_nonneg hello_image_linked_items_21 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_22 : module :=
  [Unit_stdioZ2dcommon_printf_fp_os.item_glibc_printf_fp'23str'2e313;
  IFunc Unit_stdioZ2dcommon_printf_fphex_os.fn_glibc_printf_fphex'23__printf_fphex_buffer;
  IFunc Unit_stdioZ2dcommon_printf_fphex_os.fn___printf_fphex_l_buffer;
  IFunc Unit_stdioZ2dcommon_printf_fphex_os.fn___printf_buffer_flush_fphex_to_wide;
  IFunc Unit_stdioZ2dcommon_printf_fphex_os.fn___wprintf_fphex_l_buffer;
  Unit_stdioZ2dcommon_printf_fphex_os.item_glibc_printf_fphex'23str'2e287;
  Unit_stdioZ2dcommon_printf_fphex_os.item_glibc_printf_fphex'23str'2e288;
  Unit_stdioZ2dcommon_printf_fphex_os.item_glibc_printf_fphex'23str'2e289;
  Unit_stdioZ2dcommon_printf_fphex_os.item_glibc_printf_fphex'23str'2e290;
  Unit_stdioZ2dcommon_printf_fphex_os.item_glibc_printf_fphex'23str'2e291;
  Unit_stdioZ2dcommon_printf_fphex_os.item_glibc_printf_fphex'23str'2e292;
  Unit_stdioZ2dcommon_printf_fphex_os.item_glibc_printf_fphex'23str'2e293;
  Unit_stdioZ2dcommon_printf_fphex_os.item_glibc_printf_fphex'23str'2e295;
  IFunc Unit_stdioZ2dcommon_printf_function_invoke_os.fn___printf_function_invoke;
  IFunc Unit_stdioZ2dcommon_regZ2dmodifier_os.fn___handle_registered_modifier_mb;
  IFunc Unit_stdioZ2dcommon_regZ2dmodifier_os.fn___handle_registered_modifier_wc;
  Unit_stdioZ2dcommon_regZ2dmodifier_os.item___printf_modifier_table;
  Unit_stdioZ2dcommon_regZ2dprintf_os.item___printf_arginfo_table;
  Unit_stdioZ2dcommon_regZ2dprintf_os.item___printf_function_table;
  Unit_stdioZ2dcommon_regZ2dtype_os.item___printf_va_arg_table;
  IFunc Unit_stdioZ2dcommon_snprintf_os.fn___GI___snprintf;
  IFunc Unit_stdioZ2dcommon_translated_number_width_os.fn___translated_number_width;
  Unit_stdioZ2dcommon_translated_number_width_os.item_glibc_translated_number_width'23str'2e45;
  Unit_stdioZ2dcommon_translated_number_width_os.item_glibc_translated_number_width'23str'2e46;
  Unit_stdioZ2dcommon_translated_number_width_os.item_glibc_translated_number_width'23str'2e47;
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
  Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.item_glibc_vfprintf_internal'23str'2e293;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23read_int;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23outstring_converted_wide_string;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn___wprintf_buffer;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23printf_positional;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23printf_unknown;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23group_number;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn___vfwprintf_internal].

Local Lemma hello_image_linked_items_22_zero : zero_nonneg hello_image_linked_items_22 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_23 : module :=
  [IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23__find_specwc'2egnu_inline;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23__printf_fp_spec;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23__wprintf_buffer_has_failed;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23__wprintf_buffer_mark_failed;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23__wprintf_buffer_pad;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23__wprintf_buffer_putc;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23scratch_buffer_free;
  IFunc Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23scratch_buffer_init;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep0_jumps'2e278;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep1_jumps'2e279;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep2_jumps'2e280;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep3a_jumps'2e281;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep3b_jumps'2e282;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep4_jumps'2e283;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23jump_table;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23null;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23printf_positional'2estep4_jumps'2e295;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23str'2e285;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23str'2e286;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23str'2e287;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23str'2e290;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23str'2e291;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23str'2e292;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23str'2e293;
  Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.item_glibc_vfwprintf_internal'23str'2e294;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.fn___wprintf_buffer_as_file_overflow;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.fn___wprintf_buffer_as_file_xsputn;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.fn___wprintf_buffer_as_file_init;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.fn___wprintf_buffer_as_file_terminate;
  Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.item_glibc_wprintf_buffer_as_file'23str'2e266;
  Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.item_glibc_wprintf_buffer_as_file'23str'2e267;
  Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.item_glibc_wprintf_buffer_as_file'23str'2e268;
  Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.item_glibc_wprintf_buffer_as_file'23str'2e269;
  Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.item_glibc_wprintf_buffer_as_file'23str'2e270;
  Unit_stdioZ2dcommon_wprintf_buffer_as_file_os.item_glibc_wprintf_buffer_as_file'23str'2e271;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_done_os.fn___wprintf_buffer_done;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_flush_os.fn___wprintf_buffer_flush;
  Unit_stdioZ2dcommon_wprintf_buffer_flush_os.item_glibc_wprintf_buffer_flush'23str'2e39;
  Unit_stdioZ2dcommon_wprintf_buffer_flush_os.item_glibc_wprintf_buffer_flush'23str'2e40;
  Unit_stdioZ2dcommon_wprintf_buffer_flush_os.item_glibc_wprintf_buffer_flush'23str'2e41;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_pad_1_os.fn___wprintf_buffer_pad_1;
  Unit_stdioZ2dcommon_wprintf_buffer_pad_1_os.item_glibc_wprintf_buffer_pad_1'23str'2e41;
  Unit_stdioZ2dcommon_wprintf_buffer_pad_1_os.item_glibc_wprintf_buffer_pad_1'23str'2e42;
  Unit_stdioZ2dcommon_wprintf_buffer_pad_1_os.item_glibc_wprintf_buffer_pad_1'23str'2e43;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_putc_1_os.fn___wprintf_buffer_putc_1;
  Unit_stdioZ2dcommon_wprintf_buffer_putc_1_os.item_glibc_wprintf_buffer_putc_1'23str'2e39;
  Unit_stdioZ2dcommon_wprintf_buffer_putc_1_os.item_glibc_wprintf_buffer_putc_1'23str'2e40;
  Unit_stdioZ2dcommon_wprintf_buffer_putc_1_os.item_glibc_wprintf_buffer_putc_1'23str'2e41;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_to_file_os.fn___wprintf_buffer_flush_to_file;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_to_file_os.fn___wprintf_buffer_to_file_init;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_to_file_os.fn___wprintf_buffer_to_file_done;
  IFunc Unit_stdioZ2dcommon_wprintf_buffer_write_os.fn___wprintf_buffer_write;
  Unit_stdioZ2dcommon_wprintf_buffer_write_os.item_glibc_wprintf_buffer_write'23str'2e41;
  Unit_stdioZ2dcommon_wprintf_buffer_write_os.item_glibc_wprintf_buffer_write'23str'2e42;
  Unit_stdioZ2dcommon_wprintf_buffer_write_os.item_glibc_wprintf_buffer_write'23str'2e43;
  IFunc Unit_stdioZ2dcommon_wprintf_function_invoke_os.fn___wprintf_function_invoke;
  IFunc Unit_stdlib_abort_os.fn___GI_abort;
  Unit_stdlib_abort_os.item___GI___abort_msg;
  Unit_stdlib_abort_os.item_glibc_abort'23str'2e268;
  Unit_stdlib_abort_os.item_glibc_abort'23str'2e269;
  Unit_stdlib_abort_os.item_abort;
  IFunc Unit_stdlib_add_n_os.fn___mpn_add_n;
  IFunc Unit_stdlib_addmul_1_os.fn___mpn_addmul_1;
  IFunc Unit_stdlib_addmul_1_os.fn_glibc_addmul_1'23u128_lshift].

Local Lemma hello_image_linked_items_23_zero : zero_nonneg hello_image_linked_items_23 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_24 : module :=
  [IFunc Unit_stdlib_bsearch_os.fn___GI_bsearch;
  IFunc Unit_stdlib_cmp_os.fn___mpn_cmp;
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
  IFunc Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors;
  IFunc Unit_stdlib_exit_os.fn___run_exit_handlers;
  IFunc Unit_stdlib_exit_os.fn___GI_exit;
  Unit_stdlib_exit_os.item___exit_funcs_done;
  Unit_stdlib_exit_os.item_glibc_exit'23__exit_lock;
  Unit_stdlib_exit_os.item_exit;
  Unit_stdlib_fpioconst_os.item___tens;
  Unit_stdlib_fpioconst_os.item__fpioconst_pow10;
  IFunc Unit_stdlib_getenv_os.fn___GI_getenv;
  IFunc Unit_stdlib_grouping_os.fn___correctly_grouped_prefixmb;
  IFunc Unit_stdlib_lshift_os.fn___mpn_lshift;
  IFunc Unit_stdlib_mul_os.fn___mpn_mul;
  IFunc Unit_stdlib_mul_os.fn_glibc_mul'23__mpn_add_1'2egnu_inline;
  IFunc Unit_stdlib_mul_1_os.fn___mpn_mul_1;
  IFunc Unit_stdlib_mul_1_os.fn_glibc_mul_1'23u128_lshift;
  IFunc Unit_stdlib_mul_n_os.fn___mpn_impn_mul_n_basecase;
  IFunc Unit_stdlib_mul_n_os.fn___mpn_impn_mul_n;
  IFunc Unit_stdlib_mul_n_os.fn_glibc_mul_n'23__mpn_add_1'2egnu_inline;
  IFunc Unit_stdlib_qsort_os.fn_glibc_qsort'23msort_with_tmp;
  IFunc Unit_stdlib_qsort_os.fn___GI___qsort_r;
  IFunc Unit_stdlib_qsort_os.fn___GI_qsort;
  IFunc Unit_stdlib_qsort_os.fn_glibc_qsort'23__pthread_cleanup_combined_routine_voidptr;
  IFunc Unit_stdlib_rshift_os.fn___mpn_rshift;
  Unit_stdlib_rshift_os.item_glibc_rshift'23str'2e62;
  Unit_stdlib_rshift_os.item_glibc_rshift'23str'2e63;
  Unit_stdlib_rshift_os.item_glibc_rshift'23str'2e64;
  IFunc Unit_stdlib_secureZ2dgetenv_os.fn___GI___libc_secure_getenv;
  Unit_stdlib_secureZ2dgetenv_os.item_secure_getenv;
  IFunc Unit_stdlib_strtol_os.fn___GI___isoc23_strtol;
  IFunc Unit_stdlib_strtol_l_os.fn___GI_____strtol_l_internal;
  Unit_stdlib_strtol_l_os.item___strtol_ul_max_tab;
  Unit_stdlib_strtol_l_os.item___strtol_ul_rem_tab;
  IFunc Unit_stdlib_strtoul_os.fn___GI___isoc23_strtoul;
  IFunc Unit_stdlib_strtoul_l_os.fn___GI_____strtoul_l_internal;
  IFunc Unit_stdlib_sub_n_os.fn___mpn_sub_n;
  IFunc Unit_stdlib_submul_1_os.fn___mpn_submul_1;
  IFunc Unit_stdlib_submul_1_os.fn_glibc_submul_1'23u128_lshift;
  IFunc Unit_string__strerror_os.fn___GI___strerror_r;
  Unit_string__strerror_os.item_glibc__strerror'23str'2e136;
  Unit_string__strerror_os.item_glibc__strerror'23str'2e137;
  IFunc Unit_string_argzZ2daddsep_os.fn___argz_add_sep;
  IFunc Unit_string_argzZ2dctsep_os.fn___argz_create_sep;
  IFunc Unit_string_argzZ2dnext_os.fn___GI___argz_next;
  IFunc Unit_string_cacheinfo_os.fn___cache_sysconf;
  IFunc Unit_string_memchr_os.fn___memchr;
  Unit_string_memchr_os.item___GI_memchr;
  Unit_string_memchr_os.item_memchr;
  IFunc Unit_string_memcmp_os.fn___GI_memcmp;
  Unit_string_memcmp_os.item_memcmp].

Local Lemma hello_image_linked_items_24_zero : zero_nonneg hello_image_linked_items_24 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_25 : module :=
  [IFunc Unit_string_memcpy_os.fn___GI_memcpy;
  Unit_string_memcpy_os.item_memcpy;
  IFunc Unit_string_memmem_os.fn_glibc_memmem'23two_way_long_needle;
  IFunc Unit_string_memmem_os.fn___GI___memmem;
  IFunc Unit_string_memmove_os.fn___GI_memmove;
  IFunc Unit_string_mempcpy_os.fn___GI___mempcpy;
  Unit_string_mempcpy_os.item___GI_mempcpy;
  IFunc Unit_string_memrchr_os.fn___GI___memrchr;
  IFunc Unit_string_memset_os.fn___GI_memset;
  Unit_string_memset_os.item_memset;
  IFunc Unit_string_stpcpy_os.fn___GI___stpcpy;
  Unit_string_stpcpy_os.item___GI_stpcpy;
  IFunc Unit_string_strcasecmp_l_os.fn___GI___strcasecmp_l;
  IFunc Unit_string_strchr_os.fn___GI_strchr;
  IFunc Unit_string_strchrnul_os.fn___GI___strchrnul;
  IFunc Unit_string_strcmp_os.fn___GI_strcmp;
  Unit_string_strcmp_os.item_strcmp;
  IFunc Unit_string_strcpy_os.fn___GI_strcpy;
  IFunc Unit_string_strcspn_os.fn___GI_strcspn;
  IFunc Unit_string_strdup_os.fn___GI___strdup;
  IFunc Unit_string_strlen_os.fn___strlen;
  Unit_string_strlen_os.item___GI_strlen;
  Unit_string_strlen_os.item_strlen;
  IFunc Unit_string_strncmp_os.fn___GI_strncmp;
  Unit_string_strncmp_os.item_strncmp;
  IFunc Unit_string_strndup_os.fn___GI___strndup;
  IFunc Unit_string_strnlen_os.fn___GI___strnlen;
  IFunc Unit_string_strrchr_os.fn___GI_strrchr;
  Unit_string_strrchr_os.item_strrchr;
  IFunc Unit_string_strspn_os.fn___GI_strspn;
  IFunc Unit_string_strstr_os.fn_glibc_strstr'23two_way_long_needle;
  IFunc Unit_string_strstr_os.fn___GI_strstr;
  IFunc Unit_string_strtok_r_os.fn___GI___strtok_r;
  IFunc Unit_termios_isatty_nostatus_os.fn___isatty_nostatus;
  IFunc Unit_wcsmbs_btowc_os.fn___btowc;
  IFunc Unit_wcsmbs_mbrtoc32_os.fn_mbrtoc32;
  Unit_wcsmbs_mbrtoc32_os.item_glibc_mbrtoc32'23state;
  IFunc Unit_wcsmbs_mbrtowc_os.fn___GI___mbrtowc;
  Unit_wcsmbs_mbrtowc_os.item___GI_mbrtowc;
  Unit_wcsmbs_mbrtowc_os.item_glibc_mbrtowc'23state;
  Unit_wcsmbs_mbrtowc_os.item_glibc_mbrtowc'23str'2e270;
  Unit_wcsmbs_mbrtowc_os.item_glibc_mbrtowc'23str'2e271;
  Unit_wcsmbs_mbrtowc_os.item_glibc_mbrtowc'23str'2e272;
  Unit_wcsmbs_mbrtowc_os.item_glibc_mbrtowc'23str'2e273;
  Unit_wcsmbs_mbrtowc_os.item_glibc_mbrtowc'23str'2e274;
  Unit_wcsmbs_mbrtowc_os.item_mbrtowc;
  IFunc Unit_wcsmbs_mbsinit_os.fn___mbsinit;
  Unit_wcsmbs_mbsinit_os.item_mbsinit;
  IFunc Unit_wcsmbs_wcrtomb_os.fn___wcrtomb_internal;
  IFunc Unit_wcsmbs_wcrtomb_os.fn___wcrtomb;
  Unit_wcsmbs_wcrtomb_os.item_glibc_wcrtomb'23state;
  Unit_wcsmbs_wcrtomb_os.item_glibc_wcrtomb'23str'2e270;
  Unit_wcsmbs_wcrtomb_os.item_glibc_wcrtomb'23str'2e271;
  Unit_wcsmbs_wcrtomb_os.item_glibc_wcrtomb'23str'2e272;
  IFunc Unit_wcsmbs_wcschrnul_os.fn___wcschrnul;
  IFunc Unit_wcsmbs_wcslen_os.fn___wcslen;
  IFunc Unit_wcsmbs_wcsmbsload_os.fn___wcsmbs_getfct;
  IFunc Unit_wcsmbs_wcsmbsload_os.fn___wcsmbs_load_conv;
  IFunc Unit_wcsmbs_wcsmbsload_os.fn___wcsmbs_clone_conv;
  IFunc Unit_wcsmbs_wcsmbsload_os.fn___wcsmbs_named_conv;
  Unit_wcsmbs_wcsmbsload_os.item___wcsmbs_gconv_fcts_c;
  Unit_wcsmbs_wcsmbsload_os.item_glibc_wcsmbsload'23to_mb;
  Unit_wcsmbs_wcsmbsload_os.item_glibc_wcsmbsload'23to_wc;
  Unit_wcsmbs_wcsmbsload_os.item_glibc_wcsmbsload'23str'2e256].

Local Lemma hello_image_linked_items_25_zero : zero_nonneg hello_image_linked_items_25 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_26 : module :=
  [Unit_wcsmbs_wcsmbsload_os.item_glibc_wcsmbsload'23str'2e257;
  Unit_wcsmbs_wcsmbsload_os.item_glibc_wcsmbsload'23str'2e258;
  Unit_wcsmbs_wcsmbsload_os.item_glibc_wcsmbsload'23str'2e259;
  Unit_wcsmbs_wcsmbsload_os.item_glibc_wcsmbsload'23str'2e260;
  IFunc Unit_wcsmbs_wcsnlen_os.fn___wcsnlen;
  IFunc Unit_wcsmbs_wmemchr_os.fn___GI___wmemchr;
  IFunc Unit_wcsmbs_wmemcpy_os.fn___wmemcpy;
  IFunc Unit_wcsmbs_wmempcpy_os.fn___wmempcpy;
  IFunc Unit_wcsmbs_wmemset_os.fn___GI___wmemset;
  IFunc Unit_wctype_wcfuncs_os.fn___iswprint;
  Unit_wctype_wcfuncs_os.item_iswprint;
  IFunc Unit_io_fcntl_nocancel_os.fn___GI___fcntl64_nocancel;
  IFunc Unit_libio_iofgets_u_os.fn___GI___fgets_unlocked;
  IFunc Unit_libio_iofputws_u_os.fn___GI_fputws_unlocked;
  IFunc Unit_misc_mremap_os.fn___GI___mremap;
  IFunc Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff;
  IFunc Unit_posix_sched_cpucount_os.fn___GI___sched_cpucount;
  IFunc Unit_stdioZ2dcommon_printf_buffer_puts_1_os.fn___printf_buffer_puts_1;
  Unit_stdioZ2dcommon_printf_buffer_puts_1_os.item_glibc_printf_buffer_puts_1'23str'2e41;
  Unit_stdioZ2dcommon_printf_buffer_puts_1_os.item_glibc_printf_buffer_puts_1'23str'2e42;
  Unit_stdioZ2dcommon_printf_buffer_puts_1_os.item_glibc_printf_buffer_puts_1'23str'2e43;
  IFunc Unit_stdlib_abs_os.fn_abs;
  IFunc Unit_stdlib_atexit_oS.fn_atexit;
  IFunc Unit_stdlib_dbl2mpn_os.fn___mpn_extract_double;
  IFunc Unit_stdlib_divrem_os.fn___mpn_divrem;
  IFunc Unit_stdlib_divrem_os.fn_glibc_divrem'23u128_lshift;
  IFunc Unit_stdlib_ldbl2mpn_os.fn___mpn_extract_long_double;
  IFunc Unit_wcsmbs_mbsrtowcs_os.fn___mbsrtowcs;
  Unit_wcsmbs_mbsrtowcs_os.item_glibc_mbsrtowcs'23state;
  IFunc Unit_wcsmbs_mbsrtowcs_l_os.fn___mbsrtowcs_l;
  Unit_wcsmbs_mbsrtowcs_l_os.item_glibc_mbsrtowcs_l'23str'2e270;
  Unit_wcsmbs_mbsrtowcs_l_os.item_glibc_mbsrtowcs_l'23str'2e271;
  Unit_wcsmbs_mbsrtowcs_l_os.item_glibc_mbsrtowcs_l'23str'2e272;
  Unit_wcsmbs_mbsrtowcs_l_os.item_glibc_mbsrtowcs_l'23str'2e273;
  Unit_wcsmbs_mbsrtowcs_l_os.item_glibc_mbsrtowcs_l'23str'2e274;
  Unit_wcsmbs_mbsrtowcs_l_os.item_glibc_mbsrtowcs_l'23str'2e275;
  IFunc Unit_wcsmbs_wcsrtombs_os.fn___wcsrtombs;
  Unit_wcsmbs_wcsrtombs_os.item_glibc_wcsrtombs'23state;
  Unit_wcsmbs_wcsrtombs_os.item_glibc_wcsrtombs'23str'2e270;
  Unit_wcsmbs_wcsrtombs_os.item_glibc_wcsrtombs'23str'2e271;
  Unit_wcsmbs_wcsrtombs_os.item_glibc_wcsrtombs'23str'2e272;
  Unit_wcsmbs_wcsrtombs_os.item_glibc_wcsrtombs'23str'2e273;
  Unit_wcsmbs_wcsrtombs_os.item_glibc_wcsrtombs'23str'2e274;
  Unit_wcsmbs_wcsrtombs_os.item_glibc_wcsrtombs'23str'2e275;
  IFunc Unit_wcsmbs_wmemmove_os.fn___wmemmove;
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
  IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23init_cpu_features].

Local Lemma hello_image_linked_items_26_zero : zero_nonneg hello_image_linked_items_26 = true.
Proof. reflexivity. Qed.

Local Definition hello_image_linked_items_27 : module :=
  [IFunc Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23internal_signal_block_all;
  Unit_csu_libcZ2dstart_os.item___x86_data_cache_size;
  Unit_csu_libcZ2dstart_os.item___x86_data_cache_size_half;
  Unit_csu_libcZ2dstart_os.item___x86_memset_non_temporal_threshold;
  Unit_csu_libcZ2dstart_os.item___x86_rep_movsb_stop_threshold;
  Unit_csu_libcZ2dstart_os.item___x86_rep_movsb_threshold;
  Unit_csu_libcZ2dstart_os.item___x86_rep_stosb_threshold;
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
  Unit_nptl_vars_os.item___GI___default_pthread_attr;
  IFunc Unit_nptl_nptl_deallocate_tsd_os.fn___GI___nptl_deallocate_tsd;
  Unit_nptl_nptl_nthreads_os.item___GI___nptl_nthreads;
  IFunc Unit_nptl_pthread_mutex_conf_os.fn_glibc_pthread_mutex_conf'23_dl_tunable_set_mutex_spin_count;
  IFunc Unit_nptl_pthread_mutex_conf_os.fn___pthread_tunables_init;
  Unit_nptl_pthread_mutex_conf_os.item___GI___mutex_aconf;
  IFunc Unit_stdlib_getrandom_os.fn___getrandom_early_init;
  Unit_dlfcn_libc_dlerror_result_os.item___libc_dlerror_result_string;
  IFunc Unit_csu_initZ2dfirst_os.fn_glibc_init_first'23_init_first;
  Unit_csu_initZ2dfirst_os.item___libc_argc;
  Unit_csu_initZ2dfirst_os.item___libc_argv;
  Unit_csu_initZ2dfirst_os.item___nanofil_ctor__init_first;
  IFunc Unit_time_clock_gettime_os.fn___GI___clock_gettime].

Local Lemma hello_image_linked_items_27_zero : zero_nonneg hello_image_linked_items_27 = true.
Proof. reflexivity. Qed.

Definition hello_image_linked : module := hello_image_linked_items_01 ++ hello_image_linked_items_02 ++ hello_image_linked_items_03 ++ hello_image_linked_items_04 ++ hello_image_linked_items_05 ++ hello_image_linked_items_06 ++ hello_image_linked_items_07 ++ hello_image_linked_items_08 ++ hello_image_linked_items_09 ++ hello_image_linked_items_10 ++ hello_image_linked_items_11 ++ hello_image_linked_items_12 ++ hello_image_linked_items_13 ++ hello_image_linked_items_14 ++ hello_image_linked_items_15 ++ hello_image_linked_items_16 ++ hello_image_linked_items_17 ++ hello_image_linked_items_18 ++ hello_image_linked_items_19 ++ hello_image_linked_items_20 ++ hello_image_linked_items_21 ++ hello_image_linked_items_22 ++ hello_image_linked_items_23 ++ hello_image_linked_items_24 ++ hello_image_linked_items_25 ++ hello_image_linked_items_26 ++ hello_image_linked_items_27.

Lemma hello_image_linked_zero : zero_nonneg hello_image_linked = true.
Proof.
  unfold hello_image_linked. rewrite ?zero_nonneg_app, hello_image_linked_items_01_zero, hello_image_linked_items_02_zero, hello_image_linked_items_03_zero, hello_image_linked_items_04_zero, hello_image_linked_items_05_zero, hello_image_linked_items_06_zero, hello_image_linked_items_07_zero, hello_image_linked_items_08_zero, hello_image_linked_items_09_zero, hello_image_linked_items_10_zero, hello_image_linked_items_11_zero, hello_image_linked_items_12_zero, hello_image_linked_items_13_zero, hello_image_linked_items_14_zero, hello_image_linked_items_15_zero, hello_image_linked_items_16_zero, hello_image_linked_items_17_zero, hello_image_linked_items_18_zero, hello_image_linked_items_19_zero, hello_image_linked_items_20_zero, hello_image_linked_items_21_zero, hello_image_linked_items_22_zero, hello_image_linked_items_23_zero, hello_image_linked_items_24_zero, hello_image_linked_items_25_zero, hello_image_linked_items_26_zero, hello_image_linked_items_27_zero. reflexivity.
Qed.
