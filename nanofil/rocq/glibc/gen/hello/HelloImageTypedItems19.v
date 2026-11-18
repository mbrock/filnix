(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedObjects10.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_19 : module :=
  [hello_image_item_glibc_errlist_data_gen'23str'2e277;
  hello_image_item_glibc_errlist_data_gen'23str'2e278;
  hello_image_item_glibc_errlist_data_gen'23str'2e279;
  hello_image_item_glibc_errlist_data_gen'23str'2e280;
  hello_image_item_glibc_errlist_data_gen'23str'2e281;
  hello_image_item_glibc_errlist_data_gen'23str'2e282;
  hello_image_item_glibc_errlist_data_gen'23str'2e283;
  hello_image_item_glibc_errlist_data_gen'23str'2e284;
  hello_image_item_glibc_errlist_data_gen'23str'2e285;
  hello_image_item_glibc_errlist_data_gen'23str'2e286;
  hello_image_item_glibc_errlist_data_gen'23str'2e287;
  hello_image_item_glibc_errlist_data_gen'23str'2e288;
  hello_image_item_glibc_errlist_data_gen'23str'2e289;
  hello_image_item_glibc_errlist_data_gen'23str'2e290;
  hello_image_item_glibc_errlist_data_gen'23str'2e291;
  hello_image_item_glibc_errlist_data_gen'23str'2e292;
  hello_image_item_glibc_errlist_data_gen'23str'2e293;
  hello_image_item_glibc_errlist_data_gen'23str'2e294;
  hello_image_item_glibc_errlist_data_gen'23str'2e295;
  hello_image_item_glibc_errlist_data_gen'23str'2e296;
  hello_image_item_glibc_errlist_data_gen'23str'2e297;
  hello_image_item_glibc_errlist_data_gen'23str'2e298;
  hello_image_item_glibc_errlist_data_gen'23str'2e299;
  hello_image_item_glibc_errlist_data_gen'23str'2e300;
  hello_image_item_glibc_errlist_data_gen'23str'2e301;
  hello_image_item_glibc_errlist_data_gen'23str'2e302;
  hello_image_item_glibc_errlist_data_gen'23str'2e303;
  hello_image_item_glibc_errlist_data_gen'23str'2e304;
  hello_image_item_glibc_errlist_data_gen'23str'2e305;
  hello_image_item_glibc_errlist_data_gen'23str'2e306;
  hello_image_item_glibc_errlist_data_gen'23str'2e307;
  hello_image_item_glibc_errlist_data_gen'23str'2e308;
  hello_image_item_glibc_errlist_data_gen'23str'2e309;
  hello_image_item_glibc_errlist_data_gen'23str'2e310;
  hello_image_item_glibc_errlist_data_gen'23str'2e311;
  hello_image_item_glibc_errlist_data_gen'23str'2e312;
  hello_image_item_glibc_errlist_data_gen'23str'2e313;
  hello_image_item_glibc_errlist_data_gen'23str'2e314;
  hello_image_item_glibc_errlist_data_gen'23str'2e315;
  hello_image_item_glibc_errlist_data_gen'23str'2e316;
  hello_image_item_glibc_errlist_data_gen'23str'2e317;
  hello_image_item_glibc_errlist_data_gen'23str'2e318;
  hello_image_item_glibc_errlist_data_gen'23str'2e319;
  hello_image_item_glibc_errlist_data_gen'23str'2e320;
  hello_image_item_glibc_errlist_data_gen'23str'2e321;
  hello_image_item_glibc_errlist_data_gen'23str'2e322;
  hello_image_item_glibc_errlist_data_gen'23str'2e323;
  hello_image_item_glibc_errlist_data_gen'23str'2e324;
  hello_image_item_glibc_errlist_data_gen'23str'2e325;
  hello_image_item_glibc_errlist_data_gen'23str'2e326;
  hello_image_item_glibc_errlist_data_gen'23str'2e327;
  hello_image_item_glibc_errlist_data_gen'23str'2e328;
  hello_image_item_glibc_errlist_data_gen'23str'2e329;
  hello_image_item_glibc_errlist_data_gen'23str'2e330;
  hello_image_item_glibc_errlist_data_gen'23str'2e331;
  hello_image_item_glibc_errlist_data_gen'23str'2e332;
  hello_image_item_glibc_errlist_data_gen'23str'2e333;
  hello_image_item_glibc_errlist_data_gen'23str'2e334;
  hello_image_item_glibc_errlist_data_gen'23str'2e335;
  hello_image_item_glibc_errlist_data_gen'23str'2e336;
  hello_image_item_glibc_errlist_data_gen'23str'2e337;
  hello_image_item_glibc_errlist_data_gen'23str'2e338;
  hello_image_item_glibc_errlist_data_gen'23str'2e339;
  hello_image_item_glibc_errlist_data_gen'23str'2e340].

Lemma hello_image_items_19_zero : zero_nonneg hello_image_items_19 = true.
Proof. reflexivity. Qed.
