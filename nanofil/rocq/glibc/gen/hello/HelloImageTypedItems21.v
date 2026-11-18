(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedCT HelloImageTypedGE05 HelloImageTypedHA01 HelloImageTypedLI02 HelloImageTypedObjects11 HelloImageTypedPR02 HelloImageTypedPR03 HelloImageTypedRO HelloImageTypedWP01.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_21 : module :=
  [IFunc hello_image_fn___printf_buffer_as_file_xsputn;
  IFunc hello_image_fn___printf_buffer_as_file_init;
  IFunc hello_image_fn___printf_buffer_as_file_terminate;
  hello_image_item_glibc_printf_buffer_as_file'23str'2e266;
  hello_image_item_glibc_printf_buffer_as_file'23str'2e267;
  hello_image_item_glibc_printf_buffer_as_file'23str'2e268;
  hello_image_item_glibc_printf_buffer_as_file'23str'2e269;
  hello_image_item_glibc_printf_buffer_as_file'23str'2e270;
  hello_image_item_glibc_printf_buffer_as_file'23str'2e271;
  IFunc hello_image_fn___printf_buffer_done;
  IFunc hello_image_fn___printf_buffer_flush;
  hello_image_item_glibc_printf_buffer_flush'23str'2e39;
  hello_image_item_glibc_printf_buffer_flush'23str'2e40;
  hello_image_item_glibc_printf_buffer_flush'23str'2e41;
  IFunc hello_image_fn___printf_buffer_pad_1;
  hello_image_item_glibc_printf_buffer_pad_1'23str'2e41;
  hello_image_item_glibc_printf_buffer_pad_1'23str'2e42;
  hello_image_item_glibc_printf_buffer_pad_1'23str'2e43;
  IFunc hello_image_fn___printf_buffer_putc_1;
  hello_image_item_glibc_printf_buffer_putc_1'23str'2e39;
  hello_image_item_glibc_printf_buffer_putc_1'23str'2e40;
  hello_image_item_glibc_printf_buffer_putc_1'23str'2e41;
  IFunc hello_image_fn___printf_buffer_to_file_switch;
  IFunc hello_image_fn___printf_buffer_flush_to_file;
  IFunc hello_image_fn___printf_buffer_to_file_init;
  IFunc hello_image_fn___printf_buffer_to_file_done;
  hello_image_item_glibc_printf_buffer_to_file'23str'2e266;
  hello_image_item_glibc_printf_buffer_to_file'23str'2e267;
  hello_image_item_glibc_printf_buffer_to_file'23str'2e268;
  IFunc hello_image_fn___printf_buffer_write;
  hello_image_item_glibc_printf_buffer_write'23str'2e41;
  hello_image_item_glibc_printf_buffer_write'23str'2e42;
  hello_image_item_glibc_printf_buffer_write'23str'2e43;
  IFunc hello_image_fn_glibc_printf_fp'23round_away;
  IFunc hello_image_fn_glibc_printf_fp'23hack_digit;
  IFunc hello_image_fn_glibc_printf_fp'23__printf_fp_buffer_1;
  IFunc hello_image_fn___printf_buffer_flush_fp;
  IFunc hello_image_fn___printf_fp_l_buffer;
  IFunc hello_image_fn___printf_buffer_flush_fp_to_wide;
  IFunc hello_image_fn___wprintf_fp_l_buffer;
  IFunc hello_image_fn_glibc_printf_fp'23__ctype_b_loc'2egnu_inline;
  IFunc hello_image_fn_glibc_printf_fp'23__ctype_tolower_loc'2egnu_inline;
  IFunc hello_image_fn_glibc_printf_fp'23__libc_use_alloca'2egnu_inline;
  IFunc hello_image_fn_glibc_printf_fp'23__printf_buffer_mark_failed;
  IFunc hello_image_fn_glibc_printf_fp'23__printf_buffer_pad;
  IFunc hello_image_fn_glibc_printf_fp'23__printf_buffer_putc;
  IFunc hello_image_fn_glibc_printf_fp'23__printf_buffer_puts;
  IFunc hello_image_fn_glibc_printf_fp'23get_rounding_mode;
  hello_image_item_glibc_printf_fp'23str'2e295;
  hello_image_item_glibc_printf_fp'23str'2e296;
  hello_image_item_glibc_printf_fp'23str'2e297;
  hello_image_item_glibc_printf_fp'23str'2e298;
  hello_image_item_glibc_printf_fp'23str'2e301;
  hello_image_item_glibc_printf_fp'23str'2e302;
  hello_image_item_glibc_printf_fp'23str'2e303;
  hello_image_item_glibc_printf_fp'23str'2e304;
  hello_image_item_glibc_printf_fp'23str'2e305;
  hello_image_item_glibc_printf_fp'23str'2e306;
  hello_image_item_glibc_printf_fp'23str'2e307;
  hello_image_item_glibc_printf_fp'23str'2e308;
  hello_image_item_glibc_printf_fp'23str'2e309;
  hello_image_item_glibc_printf_fp'23str'2e310;
  hello_image_item_glibc_printf_fp'23str'2e311;
  hello_image_item_glibc_printf_fp'23str'2e312].

Lemma hello_image_items_21_zero : zero_nonneg hello_image_items_21 = true.
Proof. reflexivity. Qed.
