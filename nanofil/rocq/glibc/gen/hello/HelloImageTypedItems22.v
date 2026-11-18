(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedFI HelloImageTypedGR HelloImageTypedHA HelloImageTypedOU HelloImageTypedObjects11 HelloImageTypedPR03 HelloImageTypedPR04 HelloImageTypedPR05 HelloImageTypedPR06 HelloImageTypedPR07 HelloImageTypedRE HelloImageTypedSC HelloImageTypedSN HelloImageTypedTR HelloImageTypedVF HelloImageTypedWP.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_22 : module :=
  [hello_image_item_glibc_printf_fp'23str'2e313;
  IFunc hello_image_fn_glibc_printf_fphex'23__printf_fphex_buffer;
  IFunc hello_image_fn___printf_fphex_l_buffer;
  IFunc hello_image_fn___printf_buffer_flush_fphex_to_wide;
  IFunc hello_image_fn___wprintf_fphex_l_buffer;
  hello_image_item_glibc_printf_fphex'23str'2e287;
  hello_image_item_glibc_printf_fphex'23str'2e288;
  hello_image_item_glibc_printf_fphex'23str'2e289;
  hello_image_item_glibc_printf_fphex'23str'2e290;
  hello_image_item_glibc_printf_fphex'23str'2e291;
  hello_image_item_glibc_printf_fphex'23str'2e292;
  hello_image_item_glibc_printf_fphex'23str'2e293;
  hello_image_item_glibc_printf_fphex'23str'2e295;
  IFunc hello_image_fn___printf_function_invoke;
  IFunc hello_image_fn___handle_registered_modifier_mb;
  IFunc hello_image_fn___handle_registered_modifier_wc;
  hello_image_item___printf_modifier_table;
  hello_image_item___printf_arginfo_table;
  hello_image_item___printf_function_table;
  hello_image_item___printf_va_arg_table;
  IFunc hello_image_fn___GI___snprintf;
  IFunc hello_image_fn___translated_number_width;
  hello_image_item_glibc_translated_number_width'23str'2e45;
  hello_image_item_glibc_translated_number_width'23str'2e46;
  hello_image_item_glibc_translated_number_width'23str'2e47;
  IFunc hello_image_fn_glibc_vfprintf_internal'23read_int;
  IFunc hello_image_fn_glibc_vfprintf_internal'23outstring_converted_wide_string;
  IFunc hello_image_fn___printf_buffer;
  IFunc hello_image_fn_glibc_vfprintf_internal'23printf_positional;
  IFunc hello_image_fn_glibc_vfprintf_internal'23printf_unknown;
  IFunc hello_image_fn_glibc_vfprintf_internal'23group_number;
  IFunc hello_image_fn___vfprintf_internal;
  IFunc hello_image_fn_glibc_vfprintf_internal'23__find_specmb'2egnu_inline;
  IFunc hello_image_fn_glibc_vfprintf_internal'23__printf_buffer_has_failed;
  IFunc hello_image_fn_glibc_vfprintf_internal'23__printf_buffer_mark_failed;
  IFunc hello_image_fn_glibc_vfprintf_internal'23__printf_buffer_pad;
  IFunc hello_image_fn_glibc_vfprintf_internal'23__printf_buffer_putc;
  IFunc hello_image_fn_glibc_vfprintf_internal'23__printf_fp_spec;
  IFunc hello_image_fn_glibc_vfprintf_internal'23scratch_buffer_free;
  IFunc hello_image_fn_glibc_vfprintf_internal'23scratch_buffer_init;
  hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep0_jumps'2e277;
  hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep1_jumps'2e278;
  hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep2_jumps'2e279;
  hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep3a_jumps'2e280;
  hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep3b_jumps'2e281;
  hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep4_jumps'2e282;
  hello_image_item_glibc_vfprintf_internal'23jump_table;
  hello_image_item_glibc_vfprintf_internal'23null;
  hello_image_item_glibc_vfprintf_internal'23printf_positional'2estep4_jumps'2e294;
  hello_image_item_glibc_vfprintf_internal'23str'2e284;
  hello_image_item_glibc_vfprintf_internal'23str'2e285;
  hello_image_item_glibc_vfprintf_internal'23str'2e286;
  hello_image_item_glibc_vfprintf_internal'23str'2e289;
  hello_image_item_glibc_vfprintf_internal'23str'2e290;
  hello_image_item_glibc_vfprintf_internal'23str'2e291;
  hello_image_item_glibc_vfprintf_internal'23str'2e292;
  hello_image_item_glibc_vfprintf_internal'23str'2e293;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23read_int;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23outstring_converted_wide_string;
  IFunc hello_image_fn___wprintf_buffer;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23printf_positional;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23printf_unknown;
  IFunc hello_image_fn_glibc_vfwprintf_internal'23group_number;
  IFunc hello_image_fn___vfwprintf_internal].

Lemma hello_image_items_22_zero : zero_nonneg hello_image_items_22 = true.
Proof. reflexivity. Qed.
