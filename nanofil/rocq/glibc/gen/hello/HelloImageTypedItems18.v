(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedAS HelloImageTypedGE03 HelloImageTypedIT HelloImageTypedLI HelloImageTypedObjects09 HelloImageTypedObjects10 HelloImageTypedPO HelloImageTypedSY HelloImageTypedWA.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_18 : module :=
  [hello_image_item_glibc_getopt'23str'2e148;
  hello_image_item_glibc_getopt'23str'2e149;
  hello_image_item_glibc_getopt'23str'2e150;
  IFunc hello_image_fn_getopt_long;
  IFunc hello_image_fn___GI___sysconf;
  IFunc hello_image_fn_glibc_sysconf'23posix_sysconf;
  IFunc hello_image_fn_glibc_sysconf'23__sysconf_check_spec;
  hello_image_item_glibc_sysconf'23str'2e302;
  hello_image_item_glibc_sysconf'23str'2e303;
  hello_image_item_glibc_sysconf'23str'2e304;
  hello_image_item_glibc_sysconf'23str'2e305;
  hello_image_item_glibc_sysconf'23str'2e306;
  hello_image_item_glibc_sysconf'23str'2e307;
  hello_image_item_glibc_sysconf'23str'2e308;
  hello_image_item_glibc_sysconf'23str'2e309;
  hello_image_item_glibc_sysconf'23str'2e348;
  hello_image_item_glibc_sysconf'23str'2e349;
  hello_image_item_glibc_sysconf'23str'2e350;
  hello_image_item_glibc_sysconf'23str'2e351;
  hello_image_item_glibc_sysconf'23str'2e353;
  hello_image_item_glibc_sysconf'23str'2e354;
  hello_image_item_glibc_sysconf'23str'2e355;
  hello_image_item_glibc_sysconf'23str'2e356;
  IFunc hello_image_fn___GI___wait4;
  IFunc hello_image_fn___GI___waitpid;
  IFunc hello_image_fn___GI___getrlimit64;
  hello_image_item___GI___getrlimit;
  IFunc hello_image_fn___libc_siglongjmp;
  hello_image_item___libc_longjmp;
  IFunc hello_image_fn__itoa_word;
  IFunc hello_image_fn____asprintf;
  hello_image_item___GI___asprintf;
  hello_image_item__sys_errlist_internal;
  hello_image_item__sys_errlist_internal_len;
  hello_image_item_glibc_errlist_data_gen'23str'2e247;
  hello_image_item_glibc_errlist_data_gen'23str'2e248;
  hello_image_item_glibc_errlist_data_gen'23str'2e249;
  hello_image_item_glibc_errlist_data_gen'23str'2e250;
  hello_image_item_glibc_errlist_data_gen'23str'2e251;
  hello_image_item_glibc_errlist_data_gen'23str'2e252;
  hello_image_item_glibc_errlist_data_gen'23str'2e253;
  hello_image_item_glibc_errlist_data_gen'23str'2e254;
  hello_image_item_glibc_errlist_data_gen'23str'2e255;
  hello_image_item_glibc_errlist_data_gen'23str'2e256;
  hello_image_item_glibc_errlist_data_gen'23str'2e257;
  hello_image_item_glibc_errlist_data_gen'23str'2e258;
  hello_image_item_glibc_errlist_data_gen'23str'2e259;
  hello_image_item_glibc_errlist_data_gen'23str'2e260;
  hello_image_item_glibc_errlist_data_gen'23str'2e261;
  hello_image_item_glibc_errlist_data_gen'23str'2e262;
  hello_image_item_glibc_errlist_data_gen'23str'2e263;
  hello_image_item_glibc_errlist_data_gen'23str'2e264;
  hello_image_item_glibc_errlist_data_gen'23str'2e265;
  hello_image_item_glibc_errlist_data_gen'23str'2e266;
  hello_image_item_glibc_errlist_data_gen'23str'2e267;
  hello_image_item_glibc_errlist_data_gen'23str'2e268;
  hello_image_item_glibc_errlist_data_gen'23str'2e269;
  hello_image_item_glibc_errlist_data_gen'23str'2e270;
  hello_image_item_glibc_errlist_data_gen'23str'2e271;
  hello_image_item_glibc_errlist_data_gen'23str'2e272;
  hello_image_item_glibc_errlist_data_gen'23str'2e273;
  hello_image_item_glibc_errlist_data_gen'23str'2e274;
  hello_image_item_glibc_errlist_data_gen'23str'2e275;
  hello_image_item_glibc_errlist_data_gen'23str'2e276].

Lemma hello_image_items_18_zero : zero_nonneg hello_image_items_18 = true.
Proof. reflexivity. Qed.
