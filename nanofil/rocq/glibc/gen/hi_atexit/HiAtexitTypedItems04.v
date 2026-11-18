(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexitTypedCT HiAtexitTypedDL HiAtexitTypedDO HiAtexitTypedGE HiAtexitTypedIN HiAtexitTypedLI HiAtexitTypedNP HiAtexitTypedObjects01 HiAtexitTypedPT HiAtexitTypedTL HiAtexitTypedTU.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_items_04 : module :=
  [hi_item___x86_rep_stosb_threshold;
  hi_item___x86_shared_cache_size;
  hi_item___x86_shared_cache_size_half;
  hi_item___x86_shared_non_temporal_threshold;
  hi_item___x86_string_control;
  hi_item__dl_x86_features_tlsdesc_state_size;
  hi_item_glibc_libc_start'23intel_02_known;
  hi_item_glibc_libc_start'23sigall_set;
  hi_item_glibc_libc_start'23str'2e301;
  hi_item_glibc_libc_start'23str'2e302;
  hi_item_glibc_libc_start'23str'2e303;
  hi_item_glibc_libc_start'23str'2e304;
  hi_item_glibc_libc_start'23str'2e319;
  hi_item_glibc_libc_start'23str'2e320;
  hi_item_glibc_libc_start'23str'2e321;
  hi_item_glibc_libc_start'23str'2e322;
  hi_item_glibc_libc_start'23str'2e323;
  hi_item_glibc_libc_start'23str'2e324;
  hi_item_glibc_libc_start'23str'2e325;
  hi_item_glibc_libc_start'23str'2e326;
  hi_item_glibc_libc_start'23str'2e327;
  hi_item___pthread_initialize_minimal;
  IFunc hi_fn___libc_setup_tls;
  IFunc hi_fn___libc_early_init;
  hi_item___libc_initial;
  IFunc hi_fn___tls_init_tp;
  hi_item___nptl_initial_report_events;
  IFunc hi_fn___GI___ctype_init;
  hi_item___libc_tsd_CTYPE_B;
  hi_item___libc_tsd_CTYPE_TOLOWER;
  hi_item___libc_tsd_CTYPE_TOUPPER;
  hi_item___GI___default_pthread_attr;
  IFunc hi_fn___GI___nptl_deallocate_tsd;
  hi_item___GI___nptl_nthreads;
  IFunc hi_fn_glibc_pthread_mutex_conf'23_dl_tunable_set_mutex_spin_count;
  IFunc hi_fn___pthread_tunables_init;
  hi_item___GI___mutex_aconf;
  hi_item___environ;
  IFunc hi_fn___getrandom_early_init;
  hi_item___libc_dlerror_result_string;
  hi_item___libc_enable_secure;
  IFunc hi_fn_glibc_dl_tunables'23do_tunable_update_val;
  IFunc hi_fn___tunable_is_initialized;
  IFunc hi_fn___tunable_set_val;
  IFunc hi_fn___tunable_get_val;
  hi_item_glibc_dl_tunables'23tunable_list;
  hi_item___libc_stack_end;
  hi_item__dl_auxv;
  hi_item__dl_debug_mask;
  hi_item__dl_hwcap;
  hi_item__dl_hwcap2;
  hi_item__dl_minsigstacksize;
  hi_item__dl_pagesize;
  hi_item__dl_platform;
  hi_item__dl_thp_mode;
  hi_item__dl_x86_cpu_features;
  hi_item__dl_x86_feature_control;
  IFunc hi_fn___GI___getrlimit64;
  hi_item___GI___getrlimit;
  IFunc hi_fn_glibc_init_first'23_init_first;
  hi_item___libc_argc;
  hi_item___libc_argv;
  hi_item___nanofil_ctor__init_first;
  IFunc hi_fn___init_misc].
