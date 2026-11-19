(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImage_c32isprint HelloImage_closeZ2dstream HelloImage_closeout HelloImage_exitfail HelloImage_hardZ2dlocale HelloImage_mbrtoc32 HelloImage_mbrtowc.
From Glibc Require Import HelloImage_mbsrtowcs HelloImage_mbsrtowcsZ2dstate HelloImage_mbszero HelloImage_memeq HelloImage_progname HelloImage_propername HelloImage_quotearg HelloImage_setlocale_null.
From Glibc Require Import HelloImage_setlocale_nullZ2dunlocked HelloImage_streq HelloImage_strnlen1 HelloImage_versionZ2detc HelloImage_versionZ2detcZ2dfsf.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_01 : module :=
  [IFunc HelloImage_c32isprint.fn_c32isprint;
  IFunc HelloImage_closeZ2dstream.fn_close_stream;
  IFunc HelloImage_closeout.fn_close_stdout;
  HelloImage_closeout.item_closeout'23file_name;
  HelloImage_closeout.item_closeout'23ignore_EPIPE;
  HelloImage_closeout.item_closeout'23str'2e52;
  HelloImage_closeout.item_closeout'23str'2e53;
  HelloImage_closeout.item_closeout'23str'2e54;
  HelloImage_closeout.item_closeout'23str'2e55;
  HelloImage_exitfail.item_exit_failure;
  IFunc HelloImage_hardZ2dlocale.fn_hard_locale;
  HelloImage_hardZ2dlocale.item_hard'2dlocale'23str'2e31;
  HelloImage_hardZ2dlocale.item_hard'2dlocale'23str'2e32;
  IFunc HelloImage_mbrtoc32.fn_rpl_mbrtoc32;
  HelloImage_mbrtoc32.item_mbrtoc32'23internal_state;
  HelloImage_mbrtoc32.item_mbrtoc32'23str'2e36;
  IFunc HelloImage_mbrtowc.fn_rpl_mbrtowc;
  HelloImage_mbsrtowcsZ2dstate.item__gl_mbsrtowcs_state;
  IFunc HelloImage_mbsrtowcs.fn_rpl_mbsrtowcs;
  IFunc HelloImage_mbszero.fn_mbszero;
  IFunc HelloImage_memeq.fn_memeq;
  IFunc HelloImage_progname.fn_set_program_name;
  HelloImage_progname.item_program_name;
  HelloImage_progname.item_progname'23str'2e3;
  HelloImage_progname.item_progname'23str'2e4;
  IFunc HelloImage_propername.fn_proper_name;
  IFunc HelloImage_quotearg.fn_set_char_quoting;
  IFunc HelloImage_quotearg.fn_quotearg'23gettext_quote;
  IFunc HelloImage_quotearg.fn_quotearg'23quotearg_buffer_restyled;
  IFunc HelloImage_quotearg.fn_quotearg_char_mem;
  IFunc HelloImage_quotearg.fn_quotearg_char;
  IFunc HelloImage_quotearg.fn_quotearg_colon;
  HelloImage_quotearg.item_quotearg'23default_quoting_options;
  HelloImage_quotearg.item_quotearg'23gettext_quote'2equote'2e83;
  HelloImage_quotearg.item_quotearg'23nslots;
  HelloImage_quotearg.item_quotearg'23slot0;
  HelloImage_quotearg.item_quotearg'23slotvec;
  HelloImage_quotearg.item_quotearg'23slotvec0;
  HelloImage_quotearg.item_quotearg'23str'2e82;
  HelloImage_quotearg.item_quotearg'23str'2e84;
  HelloImage_quotearg.item_quotearg'23str'2e85;
  HelloImage_quotearg.item_quotearg'23str'2e86;
  IFunc HelloImage_setlocale_nullZ2dunlocked.fn_setlocale_null_unlocked;
  IFunc HelloImage_setlocale_nullZ2dunlocked.fn_setlocale_null_r_unlocked;
  IFunc HelloImage_setlocale_null.fn_setlocale_null_r;
  IFunc HelloImage_streq.fn_streq;
  IFunc HelloImage_strnlen1.fn_strnlen1;
  HelloImage_versionZ2detcZ2dfsf.item_version_etc_copyright;
  IFunc HelloImage_versionZ2detc.fn_version_etc_arn;
  IFunc HelloImage_versionZ2detc.fn_version_etc_va;
  IFunc HelloImage_versionZ2detc.fn_version_etc;
  IFunc HelloImage_versionZ2detc.fn_emit_bug_reporting_address;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e41;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e42;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e43;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e44;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e45;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e46;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e47;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e48;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e49;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e50;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e51;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e52].

Lemma hello_image_linked_items_01_zero : zero_nonneg hello_image_linked_items_01 = true.
Proof. reflexivity. Qed.
