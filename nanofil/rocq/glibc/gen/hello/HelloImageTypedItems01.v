(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedC HelloImageTypedCL HelloImageTypedEM HelloImageTypedGE01 HelloImageTypedHA01 HelloImageTypedMB HelloImageTypedME01 HelloImageTypedObjects01 HelloImageTypedPR01 HelloImageTypedQU HelloImageTypedRP HelloImageTypedSE HelloImageTypedST01 HelloImageTypedVE.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_01 : module :=
  [IFunc hello_image_fn_c32isprint;
  IFunc hello_image_fn_close_stream;
  IFunc hello_image_fn_close_stdout;
  hello_image_item_closeout'23file_name;
  hello_image_item_closeout'23ignore_EPIPE;
  hello_image_item_closeout'23str'2e52;
  hello_image_item_closeout'23str'2e53;
  hello_image_item_closeout'23str'2e54;
  hello_image_item_closeout'23str'2e55;
  hello_image_item_exit_failure;
  IFunc hello_image_fn_hard_locale;
  hello_image_item_hard'2dlocale'23str'2e31;
  hello_image_item_hard'2dlocale'23str'2e32;
  IFunc hello_image_fn_rpl_mbrtoc32;
  hello_image_item_mbrtoc32'23internal_state;
  hello_image_item_mbrtoc32'23str'2e36;
  IFunc hello_image_fn_rpl_mbrtowc;
  hello_image_item__gl_mbsrtowcs_state;
  IFunc hello_image_fn_rpl_mbsrtowcs;
  IFunc hello_image_fn_mbszero;
  IFunc hello_image_fn_memeq;
  IFunc hello_image_fn_set_program_name;
  hello_image_item_program_name;
  hello_image_item_progname'23str'2e3;
  hello_image_item_progname'23str'2e4;
  IFunc hello_image_fn_proper_name;
  IFunc hello_image_fn_set_char_quoting;
  IFunc hello_image_fn_quotearg'23gettext_quote;
  IFunc hello_image_fn_quotearg'23quotearg_buffer_restyled;
  IFunc hello_image_fn_quotearg_char_mem;
  IFunc hello_image_fn_quotearg_char;
  IFunc hello_image_fn_quotearg_colon;
  hello_image_item_quotearg'23default_quoting_options;
  hello_image_item_quotearg'23gettext_quote'2equote'2e83;
  hello_image_item_quotearg'23nslots;
  hello_image_item_quotearg'23slot0;
  hello_image_item_quotearg'23slotvec;
  hello_image_item_quotearg'23slotvec0;
  hello_image_item_quotearg'23str'2e82;
  hello_image_item_quotearg'23str'2e84;
  hello_image_item_quotearg'23str'2e85;
  hello_image_item_quotearg'23str'2e86;
  IFunc hello_image_fn_setlocale_null_unlocked;
  IFunc hello_image_fn_setlocale_null_r_unlocked;
  IFunc hello_image_fn_setlocale_null_r;
  IFunc hello_image_fn_streq;
  IFunc hello_image_fn_strnlen1;
  hello_image_item_version_etc_copyright;
  IFunc hello_image_fn_version_etc_arn;
  IFunc hello_image_fn_version_etc_va;
  IFunc hello_image_fn_version_etc;
  IFunc hello_image_fn_emit_bug_reporting_address;
  hello_image_item_version'2detc'23str'2e41;
  hello_image_item_version'2detc'23str'2e42;
  hello_image_item_version'2detc'23str'2e43;
  hello_image_item_version'2detc'23str'2e44;
  hello_image_item_version'2detc'23str'2e45;
  hello_image_item_version'2detc'23str'2e46;
  hello_image_item_version'2detc'23str'2e47;
  hello_image_item_version'2detc'23str'2e48;
  hello_image_item_version'2detc'23str'2e49;
  hello_image_item_version'2detc'23str'2e50;
  hello_image_item_version'2detc'23str'2e51;
  hello_image_item_version'2detc'23str'2e52].

Lemma hello_image_items_01_zero : zero_nonneg hello_image_items_01 = true.
Proof. reflexivity. Qed.
