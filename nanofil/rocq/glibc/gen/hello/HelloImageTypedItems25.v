(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedBT HelloImageTypedIS HelloImageTypedMB HelloImageTypedME01 HelloImageTypedME02 HelloImageTypedObjects12 HelloImageTypedST01 HelloImageTypedST02 HelloImageTypedST03 HelloImageTypedTW HelloImageTypedWC.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_25 : module :=
  [IFunc hello_image_fn___GI_memcpy;
  hello_image_item_memcpy;
  IFunc hello_image_fn_glibc_memmem'23two_way_long_needle;
  IFunc hello_image_fn___GI___memmem;
  IFunc hello_image_fn___GI_memmove;
  IFunc hello_image_fn___GI___mempcpy;
  hello_image_item___GI_mempcpy;
  IFunc hello_image_fn___GI___memrchr;
  IFunc hello_image_fn___GI_memset;
  hello_image_item_memset;
  IFunc hello_image_fn___GI___stpcpy;
  hello_image_item___GI_stpcpy;
  IFunc hello_image_fn___GI___strcasecmp_l;
  IFunc hello_image_fn___GI_strchr;
  IFunc hello_image_fn___GI___strchrnul;
  IFunc hello_image_fn___GI_strcmp;
  hello_image_item_strcmp;
  IFunc hello_image_fn___GI_strcpy;
  IFunc hello_image_fn___GI_strcspn;
  IFunc hello_image_fn___GI___strdup;
  IFunc hello_image_fn___strlen;
  hello_image_item___GI_strlen;
  hello_image_item_strlen;
  IFunc hello_image_fn___GI_strncmp;
  hello_image_item_strncmp;
  IFunc hello_image_fn___GI___strndup;
  IFunc hello_image_fn___GI___strnlen;
  IFunc hello_image_fn___GI_strrchr;
  hello_image_item_strrchr;
  IFunc hello_image_fn___GI_strspn;
  IFunc hello_image_fn_glibc_strstr'23two_way_long_needle;
  IFunc hello_image_fn___GI_strstr;
  IFunc hello_image_fn___GI___strtok_r;
  IFunc hello_image_fn___isatty_nostatus;
  IFunc hello_image_fn___btowc;
  IFunc hello_image_fn_mbrtoc32;
  hello_image_item_glibc_mbrtoc32'23state;
  IFunc hello_image_fn___GI___mbrtowc;
  hello_image_item___GI_mbrtowc;
  hello_image_item_glibc_mbrtowc'23state;
  hello_image_item_glibc_mbrtowc'23str'2e270;
  hello_image_item_glibc_mbrtowc'23str'2e271;
  hello_image_item_glibc_mbrtowc'23str'2e272;
  hello_image_item_glibc_mbrtowc'23str'2e273;
  hello_image_item_glibc_mbrtowc'23str'2e274;
  hello_image_item_mbrtowc;
  IFunc hello_image_fn___mbsinit;
  hello_image_item_mbsinit;
  IFunc hello_image_fn___wcrtomb_internal;
  IFunc hello_image_fn___wcrtomb;
  hello_image_item_glibc_wcrtomb'23state;
  hello_image_item_glibc_wcrtomb'23str'2e270;
  hello_image_item_glibc_wcrtomb'23str'2e271;
  hello_image_item_glibc_wcrtomb'23str'2e272;
  IFunc hello_image_fn___wcschrnul;
  IFunc hello_image_fn___wcslen;
  IFunc hello_image_fn___wcsmbs_getfct;
  IFunc hello_image_fn___wcsmbs_load_conv;
  IFunc hello_image_fn___wcsmbs_clone_conv;
  IFunc hello_image_fn___wcsmbs_named_conv;
  hello_image_item___wcsmbs_gconv_fcts_c;
  hello_image_item_glibc_wcsmbsload'23to_mb;
  hello_image_item_glibc_wcsmbsload'23to_wc;
  hello_image_item_glibc_wcsmbsload'23str'2e256].

Lemma hello_image_items_25_zero : zero_nonneg hello_image_items_25 = true.
Proof. reflexivity. Qed.
