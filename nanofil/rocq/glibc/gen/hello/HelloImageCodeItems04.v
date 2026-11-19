(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_iconv_gconv_cache_os Unit_iconv_gconv_charset_os Unit_iconv_gconv_conf_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_04 : module :=
  [IFunc Unit_iconv_gconv_cache_os.fn_glibc_gconv_cache'23find_module;
  IFunc Unit_iconv_gconv_cache_os.fn___gconv_compare_alias_cache;
  IFunc Unit_iconv_gconv_cache_os.fn___gconv_lookup_cache;
  IFunc Unit_iconv_gconv_cache_os.fn___gconv_release_cache;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23cache_malloced;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23cache_size;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23gconv_cache;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23str'2e281;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23str'2e282;
  Unit_iconv_gconv_cache_os.item_glibc_gconv_cache'23str'2e284;
  IFunc Unit_iconv_gconv_charset_os.fn_glibc_gconv_charset'23gconv_parse_code;
  IFunc Unit_iconv_gconv_charset_os.fn___GI___gconv_create_spec;
  IFunc Unit_iconv_gconv_charset_os.fn___GI___gconv_destroy_spec;
  Unit_iconv_gconv_charset_os.item_glibc_gconv_charset'23str'2e244;
  Unit_iconv_gconv_charset_os.item_glibc_gconv_charset'23str'2e245;
  Unit_iconv_gconv_charset_os.item_glibc_gconv_charset'23str'2e246;
  Unit_iconv_gconv_charset_os.item_glibc_gconv_charset'23str'2e247;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23read_conf_file;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23add_alias2;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23add_module;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23__gconv_get_path;
  IFunc Unit_iconv_gconv_conf_os.fn_glibc_gconv_conf'23__gconv_read_conf;
  IFunc Unit_iconv_gconv_conf_os.fn___gconv_load_conf;
  Unit_iconv_gconv_conf_os.item___gconv_max_path_elem_len;
  Unit_iconv_gconv_conf_os.item___gconv_path_elem;
  Unit_iconv_gconv_conf_os.item___gconv_path_envvar;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23builtin_aliases;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23builtin_modules;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23default_gconv_path;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23empty_path_elem;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23gconv_conf_filename;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23gconv_module_ext;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23once;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23read_conf_file'2emodcounter'2e270;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e269;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e271;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e272;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e274;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e275;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e276;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e277;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e278;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e279;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e280;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e281;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e282;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e283;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e284;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e285;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e286;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e287;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e288;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e289;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e290;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e291;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e292;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e293;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e294;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e295;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e296;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e297;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e298;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e299;
  Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e300].

Lemma hello_image_linked_items_04_zero : zero_nonneg hello_image_linked_items_04 = true.
Proof. reflexivity. Qed.
