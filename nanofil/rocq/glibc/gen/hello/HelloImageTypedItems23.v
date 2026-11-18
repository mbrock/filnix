(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedAB HelloImageTypedFI HelloImageTypedMP01 HelloImageTypedObjects11 HelloImageTypedPR07 HelloImageTypedSC HelloImageTypedU01 HelloImageTypedWP.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_23 : module :=
  [IFunc hello_image_fn_glibc_vfwprintf_internal'23__find_specwc'2egnu_inline;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23__printf_fp_spec;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_has_failed;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_mark_failed;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_pad;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_putc;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23scratch_buffer_free;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23scratch_buffer_init;
  hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep0_jumps'2e278;
  hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep1_jumps'2e279;
  hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep2_jumps'2e280;
  hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep3a_jumps'2e281;
  hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep3b_jumps'2e282;
  hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep4_jumps'2e283;
  hello_image_item_glibc_vfwprintf_internal'23jump_table;
  hello_image_item_glibc_vfwprintf_internal'23null;
  hello_image_item_glibc_vfwprintf_internal'23printf_positional'2estep4_jumps'2e295;
  hello_image_item_glibc_vfwprintf_internal'23str'2e285;
  hello_image_item_glibc_vfwprintf_internal'23str'2e286;
  hello_image_item_glibc_vfwprintf_internal'23str'2e287;
  hello_image_item_glibc_vfwprintf_internal'23str'2e290;
  hello_image_item_glibc_vfwprintf_internal'23str'2e291;
  hello_image_item_glibc_vfwprintf_internal'23str'2e292;
  hello_image_item_glibc_vfwprintf_internal'23str'2e293;
  hello_image_item_glibc_vfwprintf_internal'23str'2e294;
  IFunc hello_image_fn___wprintf_buffer_as_file_overflow;
  IFunc hello_image_fn___wprintf_buffer_as_file_xsputn;
  IFunc hello_image_fn___wprintf_buffer_as_file_init;
  IFunc hello_image_fn___wprintf_buffer_as_file_terminate;
  hello_image_item_glibc_wprintf_buffer_as_file'23str'2e266;
  hello_image_item_glibc_wprintf_buffer_as_file'23str'2e267;
  hello_image_item_glibc_wprintf_buffer_as_file'23str'2e268;
  hello_image_item_glibc_wprintf_buffer_as_file'23str'2e269;
  hello_image_item_glibc_wprintf_buffer_as_file'23str'2e270;
  hello_image_item_glibc_wprintf_buffer_as_file'23str'2e271;
  IFunc hello_image_fn___wprintf_buffer_done;
  IFunc hello_image_fn___wprintf_buffer_flush;
  hello_image_item_glibc_wprintf_buffer_flush'23str'2e39;
  hello_image_item_glibc_wprintf_buffer_flush'23str'2e40;
  hello_image_item_glibc_wprintf_buffer_flush'23str'2e41;
  IFunc hello_image_fn___wprintf_buffer_pad_1;
  hello_image_item_glibc_wprintf_buffer_pad_1'23str'2e41;
  hello_image_item_glibc_wprintf_buffer_pad_1'23str'2e42;
  hello_image_item_glibc_wprintf_buffer_pad_1'23str'2e43;
  IFunc hello_image_fn___wprintf_buffer_putc_1;
  hello_image_item_glibc_wprintf_buffer_putc_1'23str'2e39;
  hello_image_item_glibc_wprintf_buffer_putc_1'23str'2e40;
  hello_image_item_glibc_wprintf_buffer_putc_1'23str'2e41;
  IFunc hello_image_fn___wprintf_buffer_flush_to_file;
  IFunc hello_image_fn___wprintf_buffer_to_file_init;
  IFunc hello_image_fn___wprintf_buffer_to_file_done;
  IFunc hello_image_fn___wprintf_buffer_write;
  hello_image_item_glibc_wprintf_buffer_write'23str'2e41;
  hello_image_item_glibc_wprintf_buffer_write'23str'2e42;
  hello_image_item_glibc_wprintf_buffer_write'23str'2e43;
  IFunc hello_image_fn___wprintf_function_invoke;
  IFunc hello_image_fn___GI_abort;
  hello_image_item___GI___abort_msg;
  hello_image_item_glibc_abort'23str'2e268;
  hello_image_item_glibc_abort'23str'2e269;
  hello_image_item_abort;
  IFunc hello_image_fn___mpn_add_n;
  IFunc hello_image_fn___mpn_addmul_1;
  IFunc hello_image_fn_glibc_addmul_1'23u128_lshift].

Lemma hello_image_items_23_zero : zero_nonneg hello_image_items_23 = true.
Proof. reflexivity. Qed.
