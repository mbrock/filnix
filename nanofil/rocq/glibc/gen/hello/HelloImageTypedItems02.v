(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedCT HelloImageTypedER HelloImageTypedLI01 HelloImageTypedMA HelloImageTypedObjects01 HelloImageTypedXA HelloImageTypedXC HelloImageTypedXM HelloImageTypedXP HelloImageTypedXR.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_02 : module :=
  [hello_image_item_version'2detc'23str'2e53;
  hello_image_item_version'2detc'23str'2e54;
  hello_image_item_version'2detc'23str'2e55;
  hello_image_item_version'2detc'23str'2e56;
  hello_image_item_version'2detc'23str'2e57;
  hello_image_item_version'2detc'23str'2e58;
  hello_image_item_version'2detc'23str'2e59;
  hello_image_item_version'2detc'23str'2e60;
  hello_image_item_version'2detc'23str'2e61;
  hello_image_item_version'2detc'23str'2e62;
  hello_image_item_version'2detc'23str'2e63;
  hello_image_item_version'2detc'23str'2e64;
  IFunc hello_image_fn_xalloc_die;
  hello_image_item_xalloc'2ddie'23str'2e41;
  hello_image_item_xalloc'2ddie'23str'2e42;
  hello_image_item_xalloc'2ddie'23str'2e43;
  IFunc hello_image_fn_xmalloc;
  IFunc hello_image_fn_xcharalloc;
  IFunc hello_image_fn_xrealloc;
  IFunc hello_image_fn_xpalloc;
  IFunc hello_image_fn_main;
  hello_image_item_hello'23parse_options'2elongopts'2e64;
  hello_image_item_hello'23str'2e54;
  hello_image_item_hello'23str'2e55;
  hello_image_item_hello'23str'2e56;
  hello_image_item_hello'23str'2e57;
  hello_image_item_hello'23str'2e58;
  hello_image_item_hello'23str'2e59;
  hello_image_item_hello'23str'2e60;
  hello_image_item_hello'23str'2e61;
  hello_image_item_hello'23str'2e62;
  hello_image_item_hello'23str'2e63;
  hello_image_item_hello'23str'2e65;
  hello_image_item_hello'23str'2e66;
  hello_image_item_hello'23str'2e67;
  hello_image_item_hello'23str'2e68;
  hello_image_item_hello'23str'2e69;
  hello_image_item_hello'23str'2e70;
  hello_image_item_hello'23str'2e71;
  hello_image_item_hello'23str'2e72;
  hello_image_item_hello'23str'2e73;
  hello_image_item_hello'23str'2e74;
  hello_image_item_hello'23str'2e75;
  hello_image_item_hello'23str'2e76;
  hello_image_item_hello'23str'2e77;
  hello_image_item_hello'23str'2e78;
  hello_image_item_hello'23str'2e79;
  hello_image_item_hello'23str'2e80;
  hello_image_item_hello'23str'2e81;
  hello_image_item_hello'23str'2e82;
  hello_image_item_hello'23str'2e83;
  IFunc hello_image_fn___libc_assert_fail;
  hello_image_item_glibc___libc_assert_fail'23str'2e21;
  hello_image_item_glibc___libc_assert_fail'23str'2e22;
  IFunc hello_image_fn___GI___errno_location;
  hello_image_item___errno_location;
  hello_image_item___libc_errno;
  hello_image_item_errno;
  IFunc hello_image_fn___ctype_b_loc;
  IFunc hello_image_fn___GI___ctype_init;
  hello_image_item___ctype32_b;
  hello_image_item___ctype32_tolower;
  hello_image_item___ctype32_toupper;
  hello_image_item___ctype_b].

Lemma hello_image_items_02_zero : zero_nonneg hello_image_items_02 = true.
Proof. reflexivity. Qed.
