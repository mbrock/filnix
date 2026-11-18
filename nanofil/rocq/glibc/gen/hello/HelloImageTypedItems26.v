(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedAB HelloImageTypedAT HelloImageTypedDL HelloImageTypedER HelloImageTypedFC HelloImageTypedFG HelloImageTypedFP HelloImageTypedFU HelloImageTypedGE03 HelloImageTypedGE04 HelloImageTypedHA HelloImageTypedIN HelloImageTypedIS HelloImageTypedLI HelloImageTypedMB HelloImageTypedMP01 HelloImageTypedMP02 HelloImageTypedMR HelloImageTypedObjects12 HelloImageTypedObjects13 HelloImageTypedPR07 HelloImageTypedSC HelloImageTypedU02 HelloImageTypedUP HelloImageTypedWC HelloImageTypedWM.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_26 : module :=
  [hello_image_item_glibc_wcsmbsload'23str'2e257;
  hello_image_item_glibc_wcsmbsload'23str'2e258;
  hello_image_item_glibc_wcsmbsload'23str'2e259;
  hello_image_item_glibc_wcsmbsload'23str'2e260;
  IFunc hello_image_fn___wcsnlen;
  IFunc hello_image_fn___GI___wmemchr;
  IFunc hello_image_fn___wmemcpy;
  IFunc hello_image_fn___wmempcpy;
  IFunc hello_image_fn___GI___wmemset;
  IFunc hello_image_fn___iswprint;
  hello_image_item_iswprint;
  IFunc hello_image_fn___GI___fcntl64_nocancel;
  IFunc hello_image_fn___GI___fgets_unlocked;
  IFunc hello_image_fn___GI_fputws_unlocked;
  IFunc hello_image_fn___GI___mremap;
  IFunc hello_image_fn___GI___libc_alloca_cutoff;
  IFunc hello_image_fn___GI___sched_cpucount;
  IFunc hello_image_fn___printf_buffer_puts_1;
  hello_image_item_glibc_printf_buffer_puts_1'23str'2e41;
  hello_image_item_glibc_printf_buffer_puts_1'23str'2e42;
  hello_image_item_glibc_printf_buffer_puts_1'23str'2e43;
  IFunc hello_image_fn_abs;
  IFunc hello_image_fn_atexit;
  IFunc hello_image_fn___mpn_extract_double;
  IFunc hello_image_fn___mpn_divrem;
  IFunc hello_image_fn_glibc_divrem'23u128_lshift;
  IFunc hello_image_fn___mpn_extract_long_double;
  IFunc hello_image_fn___mbsrtowcs;
  hello_image_item_glibc_mbsrtowcs'23state;
  IFunc hello_image_fn___mbsrtowcs_l;
  hello_image_item_glibc_mbsrtowcs_l'23str'2e270;
  hello_image_item_glibc_mbsrtowcs_l'23str'2e271;
  hello_image_item_glibc_mbsrtowcs_l'23str'2e272;
  hello_image_item_glibc_mbsrtowcs_l'23str'2e273;
  hello_image_item_glibc_mbsrtowcs_l'23str'2e274;
  hello_image_item_glibc_mbsrtowcs_l'23str'2e275;
  IFunc hello_image_fn___wcsrtombs;
  hello_image_item_glibc_wcsrtombs'23state;
  hello_image_item_glibc_wcsrtombs'23str'2e270;
  hello_image_item_glibc_wcsrtombs'23str'2e271;
  hello_image_item_glibc_wcsrtombs'23str'2e272;
  hello_image_item_glibc_wcsrtombs'23str'2e273;
  hello_image_item_glibc_wcsrtombs'23str'2e274;
  hello_image_item_glibc_wcsrtombs'23str'2e275;
  IFunc hello_image_fn___wmemmove;
  IFunc hello_image_fn_glibc_libc_start'23get_isa_level;
  IFunc hello_image_fn_glibc_libc_start'23intel_02_known_compare;
  IFunc hello_image_fn_glibc_libc_start'23intel_check_word;
  IFunc hello_image_fn_glibc_libc_start'23handle_intel;
  IFunc hello_image_fn_glibc_libc_start'23handle_amd;
  IFunc hello_image_fn_glibc_libc_start'23handle_zhaoxin;
  IFunc hello_image_fn_glibc_libc_start'23handle_hygon;
  IFunc hello_image_fn_glibc_libc_start'23get_common_cache_info;
  IFunc hello_image_fn_glibc_libc_start'23dl_init_cacheinfo;
  IFunc hello_image_fn_glibc_libc_start'23_dl_tunable_set_plt_rewrite;
  IFunc hello_image_fn_glibc_libc_start'23_dl_tunable_set_prefer_map_32bit_exec;
  IFunc hello_image_fn_glibc_libc_start'23update_active;
  IFunc hello_image_fn_glibc_libc_start'23get_common_indices;
  IFunc hello_image_fn_glibc_libc_start'23__libc_start_call_main;
  IFunc hello_image_fn_glibc_libc_start'23errno_handler;
  IFunc hello_image_fn_glibc_libc_start'23dlerror_handler;
  IFunc hello_image_fn___libc_start_main;
  IFunc hello_image_fn_glibc_libc_start'23futex_wake;
  IFunc hello_image_fn_glibc_libc_start'23init_cpu_features].

Lemma hello_image_items_26_zero : zero_nonneg hello_image_items_26 = true.
Proof. reflexivity. Qed.
