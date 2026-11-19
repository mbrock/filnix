(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_ctype_ctypeZ2dinfo_os Unit_debug_chk_fail_os Unit_debug_fortify_fail_os Unit_debug_readonlyZ2dareaZ2dfallback_os Unit_debug_readonlyZ2darea_os Unit_dirent_closedir_os Unit_dirent_getdents64_os.
From Glibc Require Import Unit_dirent_opendir_os Unit_dirent_readdir64_os Unit_elf_dlZ2dlibc_os Unit_elf_dlZ2dsupport_os Unit_elf_dlZ2dtunables_os Unit_elf_enblZ2dsecure_os Unit_iconv_gconv_builtin_os Unit_iconv_gconv_cache_os.
From Glibc Require Import Unit_iconv_gconv_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_03 : module :=
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

Lemma hello_image_linked_items_03_zero : zero_nonneg hello_image_linked_items_03 = true.
Proof. reflexivity. Qed.
