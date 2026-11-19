(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_csu_initZ2dfirst_os Unit_csu_libcZ2dstart_os Unit_csu_libcZ2dtls_os Unit_ctype_ctypeZ2dinfo_os Unit_dlfcn_libc_dlerror_result_os Unit_elf_dlZ2dsupport_os Unit_elf_dlZ2dtls_init_tp_os Unit_elf_dlZ2dtunables_os.
From Glibc Require Import Unit_elf_enblZ2dsecure_os Unit_elf_libc_early_init_os Unit_misc_initZ2dmisc_os Unit_nptl_nptl_deallocate_tsd_os Unit_nptl_nptl_nthreads_os Unit_nptl_pthread_mutex_conf_os Unit_nptl_vars_os Unit_posix_environ_os.
From Glibc Require Import Unit_resource_getrlimit64_os Unit_stdlib_getrandom_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_linked_items_04 : module :=
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
