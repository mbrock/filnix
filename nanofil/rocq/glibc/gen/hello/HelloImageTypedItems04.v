(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedAD HelloImageTypedFI HelloImageTypedGC01 HelloImageTypedGC02 HelloImageTypedObjects01 HelloImageTypedObjects02 HelloImageTypedRE.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_04 : module :=
  [IFunc hello_image_fn_glibc_gconv_cache'23find_module;
  IFunc hello_image_fn___gconv_compare_alias_cache;
  IFunc hello_image_fn___gconv_lookup_cache;
  IFunc hello_image_fn___gconv_release_cache;
  hello_image_item_glibc_gconv_cache'23cache_malloced;
  hello_image_item_glibc_gconv_cache'23cache_size;
  hello_image_item_glibc_gconv_cache'23gconv_cache;
  hello_image_item_glibc_gconv_cache'23str'2e281;
  hello_image_item_glibc_gconv_cache'23str'2e282;
  hello_image_item_glibc_gconv_cache'23str'2e284;
  IFunc hello_image_fn_glibc_gconv_charset'23gconv_parse_code;
  IFunc hello_image_fn___GI___gconv_create_spec;
  IFunc hello_image_fn___GI___gconv_destroy_spec;
  hello_image_item_glibc_gconv_charset'23str'2e244;
  hello_image_item_glibc_gconv_charset'23str'2e245;
  hello_image_item_glibc_gconv_charset'23str'2e246;
  hello_image_item_glibc_gconv_charset'23str'2e247;
  IFunc hello_image_fn_glibc_gconv_conf'23read_conf_file;
  IFunc hello_image_fn_glibc_gconv_conf'23add_alias2;
  IFunc hello_image_fn_glibc_gconv_conf'23add_module;
  IFunc hello_image_fn_glibc_gconv_conf'23__gconv_get_path;
  IFunc hello_image_fn_glibc_gconv_conf'23__gconv_read_conf;
  IFunc hello_image_fn___gconv_load_conf;
  hello_image_item___gconv_max_path_elem_len;
  hello_image_item___gconv_path_elem;
  hello_image_item___gconv_path_envvar;
  hello_image_item_glibc_gconv_conf'23builtin_aliases;
  hello_image_item_glibc_gconv_conf'23builtin_modules;
  hello_image_item_glibc_gconv_conf'23default_gconv_path;
  hello_image_item_glibc_gconv_conf'23empty_path_elem;
  hello_image_item_glibc_gconv_conf'23gconv_conf_filename;
  hello_image_item_glibc_gconv_conf'23gconv_module_ext;
  hello_image_item_glibc_gconv_conf'23once;
  hello_image_item_glibc_gconv_conf'23read_conf_file'2emodcounter'2e270;
  hello_image_item_glibc_gconv_conf'23str'2e269;
  hello_image_item_glibc_gconv_conf'23str'2e271;
  hello_image_item_glibc_gconv_conf'23str'2e272;
  hello_image_item_glibc_gconv_conf'23str'2e274;
  hello_image_item_glibc_gconv_conf'23str'2e275;
  hello_image_item_glibc_gconv_conf'23str'2e276;
  hello_image_item_glibc_gconv_conf'23str'2e277;
  hello_image_item_glibc_gconv_conf'23str'2e278;
  hello_image_item_glibc_gconv_conf'23str'2e279;
  hello_image_item_glibc_gconv_conf'23str'2e280;
  hello_image_item_glibc_gconv_conf'23str'2e281;
  hello_image_item_glibc_gconv_conf'23str'2e282;
  hello_image_item_glibc_gconv_conf'23str'2e283;
  hello_image_item_glibc_gconv_conf'23str'2e284;
  hello_image_item_glibc_gconv_conf'23str'2e285;
  hello_image_item_glibc_gconv_conf'23str'2e286;
  hello_image_item_glibc_gconv_conf'23str'2e287;
  hello_image_item_glibc_gconv_conf'23str'2e288;
  hello_image_item_glibc_gconv_conf'23str'2e289;
  hello_image_item_glibc_gconv_conf'23str'2e290;
  hello_image_item_glibc_gconv_conf'23str'2e291;
  hello_image_item_glibc_gconv_conf'23str'2e292;
  hello_image_item_glibc_gconv_conf'23str'2e293;
  hello_image_item_glibc_gconv_conf'23str'2e294;
  hello_image_item_glibc_gconv_conf'23str'2e295;
  hello_image_item_glibc_gconv_conf'23str'2e296;
  hello_image_item_glibc_gconv_conf'23str'2e297;
  hello_image_item_glibc_gconv_conf'23str'2e298;
  hello_image_item_glibc_gconv_conf'23str'2e299;
  hello_image_item_glibc_gconv_conf'23str'2e300].

Lemma hello_image_items_04_zero : zero_nonneg hello_image_items_04 = true.
Proof. reflexivity. Qed.
