(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedObjects08.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_13 : module :=
  [hello_image_item__nl_C_LC_TIME;
  hello_image_item_glibc_C_time'23str'2e100;
  hello_image_item_glibc_C_time'23str'2e101;
  hello_image_item_glibc_C_time'23str'2e102;
  hello_image_item_glibc_C_time'23str'2e103;
  hello_image_item_glibc_C_time'23str'2e104;
  hello_image_item_glibc_C_time'23str'2e105;
  hello_image_item_glibc_C_time'23str'2e106;
  hello_image_item_glibc_C_time'23str'2e107;
  hello_image_item_glibc_C_time'23str'2e108;
  hello_image_item_glibc_C_time'23str'2e109;
  hello_image_item_glibc_C_time'23str'2e110;
  hello_image_item_glibc_C_time'23str'2e111;
  hello_image_item_glibc_C_time'23str'2e112;
  hello_image_item_glibc_C_time'23str'2e113;
  hello_image_item_glibc_C_time'23str'2e114;
  hello_image_item_glibc_C_time'23str'2e115;
  hello_image_item_glibc_C_time'23str'2e116;
  hello_image_item_glibc_C_time'23str'2e117;
  hello_image_item_glibc_C_time'23str'2e118;
  hello_image_item_glibc_C_time'23str'2e119;
  hello_image_item_glibc_C_time'23str'2e120;
  hello_image_item_glibc_C_time'23str'2e121;
  hello_image_item_glibc_C_time'23str'2e122;
  hello_image_item_glibc_C_time'23str'2e123;
  hello_image_item_glibc_C_time'23str'2e124;
  hello_image_item_glibc_C_time'23str'2e125;
  hello_image_item_glibc_C_time'23str'2e126;
  hello_image_item_glibc_C_time'23str'2e127;
  hello_image_item_glibc_C_time'23str'2e128;
  hello_image_item_glibc_C_time'23str'2e129;
  hello_image_item_glibc_C_time'23str'2e130;
  hello_image_item_glibc_C_time'23str'2e131;
  hello_image_item_glibc_C_time'23str'2e132;
  hello_image_item_glibc_C_time'23str'2e133;
  hello_image_item_glibc_C_time'23str'2e40;
  hello_image_item_glibc_C_time'23str'2e41;
  hello_image_item_glibc_C_time'23str'2e42;
  hello_image_item_glibc_C_time'23str'2e43;
  hello_image_item_glibc_C_time'23str'2e44;
  hello_image_item_glibc_C_time'23str'2e45;
  hello_image_item_glibc_C_time'23str'2e46;
  hello_image_item_glibc_C_time'23str'2e47;
  hello_image_item_glibc_C_time'23str'2e48;
  hello_image_item_glibc_C_time'23str'2e49;
  hello_image_item_glibc_C_time'23str'2e50;
  hello_image_item_glibc_C_time'23str'2e51;
  hello_image_item_glibc_C_time'23str'2e52;
  hello_image_item_glibc_C_time'23str'2e53;
  hello_image_item_glibc_C_time'23str'2e54;
  hello_image_item_glibc_C_time'23str'2e55;
  hello_image_item_glibc_C_time'23str'2e56;
  hello_image_item_glibc_C_time'23str'2e57;
  hello_image_item_glibc_C_time'23str'2e58;
  hello_image_item_glibc_C_time'23str'2e59;
  hello_image_item_glibc_C_time'23str'2e60;
  hello_image_item_glibc_C_time'23str'2e61;
  hello_image_item_glibc_C_time'23str'2e62;
  hello_image_item_glibc_C_time'23str'2e63;
  hello_image_item_glibc_C_time'23str'2e64;
  hello_image_item_glibc_C_time'23str'2e65;
  hello_image_item_glibc_C_time'23str'2e66;
  hello_image_item_glibc_C_time'23str'2e67;
  hello_image_item_glibc_C_time'23str'2e68].

Lemma hello_image_items_13_zero : zero_nonneg hello_image_items_13 = true.
Proof. reflexivity. Qed.
