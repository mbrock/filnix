(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_csu_libcZ2dstart_os Unit_io_fcntl_nocancel_os Unit_libio_iofgets_u_os Unit_libio_iofputws_u_os Unit_misc_mremap_os Unit_nptl_alloca_cutoff_os Unit_posix_sched_cpucount_os.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_puts_1_os Unit_stdlib_abs_os Unit_stdlib_atexit_oS Unit_stdlib_dbl2mpn_os Unit_stdlib_divrem_os Unit_stdlib_ldbl2mpn_os Unit_wcsmbs_mbsrtowcs_l_os Unit_wcsmbs_mbsrtowcs_os.
From Glibc Require Import Unit_wcsmbs_wcsmbsload_os Unit_wcsmbs_wcsnlen_os Unit_wcsmbs_wcsrtombs_os Unit_wcsmbs_wmemchr_os Unit_wcsmbs_wmemcpy_os Unit_wcsmbs_wmemmove_os Unit_wcsmbs_wmempcpy_os Unit_wcsmbs_wmemset_os.
From Glibc Require Import Unit_wctype_wcfuncs_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_26 : module :=
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

Lemma hello_image_linked_items_26_zero : zero_nonneg hello_image_linked_items_26 = true.
Proof. reflexivity. Qed.
