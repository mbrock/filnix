(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedAL HelloImageTypedCH HelloImageTypedCL HelloImageTypedDO HelloImageTypedFI HelloImageTypedFO HelloImageTypedGC01 HelloImageTypedGE01 HelloImageTypedLI HelloImageTypedOP HelloImageTypedObjects01 HelloImageTypedRE HelloImageTypedTU.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_03 : module :=
  [hello_image_item___ctype_tolower;
  hello_image_item___ctype_toupper;
  hello_image_item___libc_tsd_CTYPE_B;
  hello_image_item___libc_tsd_CTYPE_TOLOWER;
  hello_image_item___libc_tsd_CTYPE_TOUPPER;
  IFunc hello_image_fn___GI___chk_fail;
  hello_image_item_glibc_chk_fail'23str'2e134;
  IFunc hello_image_fn___GI___fortify_fail;
  hello_image_item_glibc_fortify_fail'23str'2e19;
  hello_image_item_glibc_fortify_fail'23str'2e20;
  IFunc hello_image_fn___readonly_area_fallback;
  hello_image_item_glibc_readonly_area_fallback'23str'2e252;
  hello_image_item_glibc_readonly_area_fallback'23str'2e253;
  IFunc hello_image_fn___readonly_area;
  IFunc hello_image_fn___closedir;
  IFunc hello_image_fn___GI___getdents64;
  IFunc hello_image_fn___opendir;
  IFunc hello_image_fn___alloc_dir;
  IFunc hello_image_fn___GI___readdir64;
  IFunc hello_image_fn___libc_dlopen_mode;
  IFunc hello_image_fn___libc_dlsym;
  IFunc hello_image_fn___libc_dlclose;
  hello_image_item___libc_stack_end;
  hello_image_item__dl_auxv;
  hello_image_item__dl_clktck;
  hello_image_item__dl_debug_mask;
  hello_image_item__dl_hwcap;
  hello_image_item__dl_hwcap2;
  hello_image_item__dl_minsigstacksize;
  hello_image_item__dl_pagesize;
  hello_image_item__dl_platform;
  hello_image_item__dl_thp_mode;
  hello_image_item__dl_x86_cpu_features;
  hello_image_item__dl_x86_feature_control;
  IFunc hello_image_fn_glibc_dl_tunables'23do_tunable_update_val;
  IFunc hello_image_fn___tunable_is_initialized;
  IFunc hello_image_fn___tunable_set_val;
  IFunc hello_image_fn___tunable_get_val;
  hello_image_item_glibc_dl_tunables'23tunable_list;
  hello_image_item___libc_enable_secure;
  IFunc hello_image_fn___gconv;
  hello_image_item_glibc_gconv'23str'2e269;
  hello_image_item_glibc_gconv'23str'2e270;
  hello_image_item_glibc_gconv'23str'2e271;
  hello_image_item_glibc_gconv'23str'2e272;
  IFunc hello_image_fn___gconv_get_builtin_trans;
  hello_image_item_glibc_gconv_builtin'23map;
  hello_image_item_glibc_gconv_builtin'23str'2e244;
  hello_image_item_glibc_gconv_builtin'23str'2e245;
  hello_image_item_glibc_gconv_builtin'23str'2e246;
  hello_image_item_glibc_gconv_builtin'23str'2e247;
  hello_image_item_glibc_gconv_builtin'23str'2e248;
  hello_image_item_glibc_gconv_builtin'23str'2e249;
  hello_image_item_glibc_gconv_builtin'23str'2e250;
  hello_image_item_glibc_gconv_builtin'23str'2e251;
  hello_image_item_glibc_gconv_builtin'23str'2e252;
  hello_image_item_glibc_gconv_builtin'23str'2e253;
  hello_image_item_glibc_gconv_builtin'23str'2e254;
  hello_image_item_glibc_gconv_builtin'23str'2e255;
  hello_image_item_glibc_gconv_builtin'23str'2e256;
  hello_image_item_glibc_gconv_builtin'23str'2e257;
  hello_image_item_glibc_gconv_builtin'23str'2e258;
  IFunc hello_image_fn___gconv_load_cache;
  IFunc hello_image_fn_glibc_gconv_cache'23find_module_idx].

Lemma hello_image_items_03_zero : zero_nonneg hello_image_items_03 = true.
Proof. reflexivity. Qed.
