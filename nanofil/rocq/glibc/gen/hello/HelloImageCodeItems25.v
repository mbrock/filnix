(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_string_memcpy_os Unit_string_memmem_os Unit_string_memmove_os Unit_string_mempcpy_os Unit_string_memrchr_os Unit_string_memset_os Unit_string_stpcpy_os.
From Glibc Require Import Unit_string_strcasecmp_l_os Unit_string_strchr_os Unit_string_strchrnul_os Unit_string_strcmp_os Unit_string_strcpy_os Unit_string_strcspn_os Unit_string_strdup_os Unit_string_strlen_os.
From Glibc Require Import Unit_string_strncmp_os Unit_string_strndup_os Unit_string_strnlen_os Unit_string_strrchr_os Unit_string_strspn_os Unit_string_strstr_os Unit_string_strtok_r_os Unit_termios_isatty_nostatus_os.
From Glibc Require Import Unit_wcsmbs_btowc_os Unit_wcsmbs_mbrtoc32_os Unit_wcsmbs_mbrtowc_os Unit_wcsmbs_mbsinit_os Unit_wcsmbs_wcrtomb_os Unit_wcsmbs_wcschrnul_os Unit_wcsmbs_wcslen_os Unit_wcsmbs_wcsmbsload_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_25 : module :=
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

Lemma hello_image_linked_items_25_zero : zero_nonneg hello_image_linked_items_25 = true.
Proof. reflexivity. Qed.
