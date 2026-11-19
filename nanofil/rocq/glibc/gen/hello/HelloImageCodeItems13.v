(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_locale_CZ2dtime_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_13 : module :=
  [Unit_locale_CZ2dtime_os.item__nl_C_LC_TIME;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e100;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e101;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e102;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e103;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e104;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e105;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e106;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e107;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e108;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e109;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e110;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e111;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e112;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e113;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e114;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e115;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e116;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e117;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e118;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e119;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e120;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e121;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e122;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e123;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e124;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e125;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e126;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e127;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e128;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e129;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e130;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e131;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e132;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e133;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e40;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e41;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e42;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e43;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e44;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e45;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e46;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e47;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e48;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e49;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e50;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e51;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e52;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e53;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e54;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e55;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e56;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e57;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e58;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e59;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e60;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e61;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e62;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e63;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e64;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e65;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e66;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e67;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e68].

Lemma hello_image_linked_items_13_zero : zero_nonneg hello_image_linked_items_13 = true.
Proof. reflexivity. Qed.
