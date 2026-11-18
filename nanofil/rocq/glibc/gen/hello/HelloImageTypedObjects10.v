(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRBytes.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e276 : item :=
  (IData (a "glibc_errlist_data_gen#str.276") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 108); (Item Wb 108); (Item Wb 101); (Item Wb 103); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 101); (Item Wb 107); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e277 : item :=
  (IData (a "glibc_errlist_data_gen#str.277") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 45); (Item Wb 111); (Item Wb 110); (Item Wb 108); (Item Wb 121); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e278 : item :=
  (IData (a "glibc_errlist_data_gen#str.278") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 97); (Item Wb 110); (Item Wb 121); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 107); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e279 : item :=
  (IData (a "glibc_errlist_data_gen#str.279") (LRo (a "local")) 1 [(Item Wb 66); (Item Wb 114); (Item Wb 111); (Item Wb 107); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 112); (Item Wb 105); (Item Wb 112); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e280 : item :=
  (IData (a "glibc_errlist_data_gen#str.280") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 114); (Item Wb 105); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 100); (Item Wb 111); (Item Wb 109); (Item Wb 97); (Item Wb 105); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e281 : item :=
  (IData (a "glibc_errlist_data_gen#str.281") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 114); (Item Wb 105); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 117); (Item Wb 108); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 103); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e282 : item :=
  (IData (a "glibc_errlist_data_gen#str.282") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 115); (Item Wb 111); (Item Wb 117); (Item Wb 114); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 97); (Item Wb 114); (Item Wb 105); (Item Wb 108); (Item Wb 121); (Item Wb 32); (Item Wb 117); (Item Wb 110); (Item Wb 97); (Item Wb 118); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e283 : item :=
  (IData (a "glibc_errlist_data_gen#str.283") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 119); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e284 : item :=
  (IData (a "glibc_errlist_data_gen#str.284") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 108); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 121); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e285 : item :=
  (IData (a "glibc_errlist_data_gen#str.285") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 111); (Item Wb 99); (Item Wb 107); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 110); (Item Wb 45); (Item Wb 115); (Item Wb 111); (Item Wb 99); (Item Wb 107); (Item Wb 101); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e286 : item :=
  (IData (a "glibc_errlist_data_gen#str.286") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 108); (Item Wb 111); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e287 : item :=
  (IData (a "glibc_errlist_data_gen#str.287") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 114); (Item Wb 111); (Item Wb 116); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 108); (Item Wb 32); (Item Wb 119); (Item Wb 114); (Item Wb 111); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 116); (Item Wb 121); (Item Wb 112); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 111); (Item Wb 99); (Item Wb 107); (Item Wb 101); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e288 : item :=
  (IData (a "glibc_errlist_data_gen#str.288") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 114); (Item Wb 111); (Item Wb 116); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 108); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 118); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e289 : item :=
  (IData (a "glibc_errlist_data_gen#str.289") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 114); (Item Wb 111); (Item Wb 116); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 108); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e290 : item :=
  (IData (a "glibc_errlist_data_gen#str.290") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 111); (Item Wb 99); (Item Wb 107); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 116); (Item Wb 121); (Item Wb 112); (Item Wb 101); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e291 : item :=
  (IData (a "glibc_errlist_data_gen#str.291") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e292 : item :=
  (IData (a "glibc_errlist_data_gen#str.292") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 114); (Item Wb 111); (Item Wb 116); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 108); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 109); (Item Wb 105); (Item Wb 108); (Item Wb 121); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e293 : item :=
  (IData (a "glibc_errlist_data_gen#str.293") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 100); (Item Wb 100); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 109); (Item Wb 105); (Item Wb 108); (Item Wb 121); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 116); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e294 : item :=
  (IData (a "glibc_errlist_data_gen#str.294") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 100); (Item Wb 100); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 108); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 121); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e295 : item :=
  (IData (a "glibc_errlist_data_gen#str.295") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 110); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 101); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 97); (Item Wb 100); (Item Wb 100); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e296 : item :=
  (IData (a "glibc_errlist_data_gen#str.296") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 101); (Item Wb 116); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 107); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 100); (Item Wb 111); (Item Wb 119); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e297 : item :=
  (IData (a "glibc_errlist_data_gen#str.297") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 101); (Item Wb 116); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 107); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 117); (Item Wb 110); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e298 : item :=
  (IData (a "glibc_errlist_data_gen#str.298") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 101); (Item Wb 116); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 107); (Item Wb 32); (Item Wb 100); (Item Wb 114); (Item Wb 111); (Item Wb 112); (Item Wb 112); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 110); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e299 : item :=
  (IData (a "glibc_errlist_data_gen#str.299") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 111); (Item Wb 102); (Item Wb 116); (Item Wb 119); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 99); (Item Wb 97); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 110); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 98); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e300 : item :=
  (IData (a "glibc_errlist_data_gen#str.300") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 111); (Item Wb 110); (Item Wb 110); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 112); (Item Wb 101); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e301 : item :=
  (IData (a "glibc_errlist_data_gen#str.301") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 112); (Item Wb 97); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 118); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e302 : item :=
  (IData (a "glibc_errlist_data_gen#str.302") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 32); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 112); (Item Wb 111); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 108); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 121); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 110); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e303 : item :=
  (IData (a "glibc_errlist_data_gen#str.303") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 32); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 112); (Item Wb 111); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 110); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e304 : item :=
  (IData (a "glibc_errlist_data_gen#str.304") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 101); (Item Wb 115); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 100); (Item Wb 100); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e305 : item :=
  (IData (a "glibc_errlist_data_gen#str.305") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 97); (Item Wb 102); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 32); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 112); (Item Wb 111); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 104); (Item Wb 117); (Item Wb 116); (Item Wb 100); (Item Wb 111); (Item Wb 119); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e306 : item :=
  (IData (a "glibc_errlist_data_gen#str.306") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 97); (Item Wb 110); (Item Wb 121); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 101); (Item Wb 110); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 112); (Item Wb 108); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e307 : item :=
  (IData (a "glibc_errlist_data_gen#str.307") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 111); (Item Wb 110); (Item Wb 110); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 116); (Item Wb 105); (Item Wb 109); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e308 : item :=
  (IData (a "glibc_errlist_data_gen#str.308") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 111); (Item Wb 110); (Item Wb 110); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 102); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e309 : item :=
  (IData (a "glibc_errlist_data_gen#str.309") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 97); (Item Wb 110); (Item Wb 121); (Item Wb 32); (Item Wb 108); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 108); (Item Wb 115); (Item Wb 32); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 109); (Item Wb 98); (Item Wb 111); (Item Wb 108); (Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 107); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e310 : item :=
  (IData (a "glibc_errlist_data_gen#str.310") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 110); (Item Wb 97); (Item Wb 109); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 108); (Item Wb 111); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e311 : item :=
  (IData (a "glibc_errlist_data_gen#str.311") (LRo (a "local")) 1 [(Item Wb 72); (Item Wb 111); (Item Wb 115); (Item Wb 116); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 100); (Item Wb 111); (Item Wb 119); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e312 : item :=
  (IData (a "glibc_errlist_data_gen#str.312") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 114); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 104); (Item Wb 111); (Item Wb 115); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e313 : item :=
  (IData (a "glibc_errlist_data_gen#str.313") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 101); (Item Wb 109); (Item Wb 112); (Item Wb 116); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e314 : item :=
  (IData (a "glibc_errlist_data_gen#str.314") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 97); (Item Wb 110); (Item Wb 121); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e315 : item :=
  (IData (a "glibc_errlist_data_gen#str.315") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 105); (Item Wb 115); (Item Wb 107); (Item Wb 32); (Item Wb 113); (Item Wb 117); (Item Wb 111); (Item Wb 116); (Item Wb 97); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 99); (Item Wb 101); (Item Wb 101); (Item Wb 100); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e316 : item :=
  (IData (a "glibc_errlist_data_gen#str.316") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e317 : item :=
  (IData (a "glibc_errlist_data_gen#str.317") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 98); (Item Wb 106); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 116); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e318 : item :=
  (IData (a "glibc_errlist_data_gen#str.318") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 107); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 118); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e319 : item :=
  (IData (a "glibc_errlist_data_gen#str.319") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 117); (Item Wb 110); (Item Wb 99); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 105); (Item Wb 109); (Item Wb 112); (Item Wb 108); (Item Wb 101); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e320 : item :=
  (IData (a "glibc_errlist_data_gen#str.320") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 99); (Item Wb 111); (Item Wb 109); (Item Wb 112); (Item Wb 108); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 109); (Item Wb 117); (Item Wb 108); (Item Wb 116); (Item Wb 105); (Item Wb 98); (Item Wb 121); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e321 : item :=
  (IData (a "glibc_errlist_data_gen#str.321") (LRo (a "local")) 1 [(Item Wb 66); (Item Wb 97); (Item Wb 100); (Item Wb 32); (Item Wb 109); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e322 : item :=
  (IData (a "glibc_errlist_data_gen#str.322") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 100); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 105); (Item Wb 102); (Item Wb 105); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 118); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e323 : item :=
  (IData (a "glibc_errlist_data_gen#str.323") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 117); (Item Wb 108); (Item Wb 116); (Item Wb 105); (Item Wb 104); (Item Wb 111); (Item Wb 112); (Item Wb 32); (Item Wb 97); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 112); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e324 : item :=
  (IData (a "glibc_errlist_data_gen#str.324") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 32); (Item Wb 97); (Item Wb 118); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e325 : item :=
  (IData (a "glibc_errlist_data_gen#str.325") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 105); (Item Wb 110); (Item Wb 107); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 115); (Item Wb 32); (Item Wb 98); (Item Wb 101); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e326 : item :=
  (IData (a "glibc_errlist_data_gen#str.326") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 115); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 116); (Item Wb 121); (Item Wb 112); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e327 : item :=
  (IData (a "glibc_errlist_data_gen#str.327") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 115); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 111); (Item Wb 117); (Item Wb 114); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e328 : item :=
  (IData (a "glibc_errlist_data_gen#str.328") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e329 : item :=
  (IData (a "glibc_errlist_data_gen#str.329") (LRo (a "local")) 1 [(Item Wb 86); (Item Wb 97); (Item Wb 108); (Item Wb 117); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 108); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 102); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 32); (Item Wb 116); (Item Wb 121); (Item Wb 112); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e330 : item :=
  (IData (a "glibc_errlist_data_gen#str.330") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 114); (Item Wb 111); (Item Wb 116); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 108); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e331 : item :=
  (IData (a "glibc_errlist_data_gen#str.331") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 105); (Item Wb 109); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e332 : item :=
  (IData (a "glibc_errlist_data_gen#str.332") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 99); (Item Wb 101); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e333 : item :=
  (IData (a "glibc_errlist_data_gen#str.333") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 119); (Item Wb 110); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e334 : item :=
  (IData (a "glibc_errlist_data_gen#str.334") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 99); (Item Wb 111); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e335 : item :=
  (IData (a "glibc_errlist_data_gen#str.335") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 117); (Item Wb 112); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 32); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 32); (Item Wb 115); (Item Wb 104); (Item Wb 111); (Item Wb 117); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 98); (Item Wb 101); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e336 : item :=
  (IData (a "glibc_errlist_data_gen#str.336") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 101); (Item Wb 108); (Item Wb 32); (Item Wb 110); (Item Wb 117); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 103); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e337 : item :=
  (IData (a "glibc_errlist_data_gen#str.337") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 108); (Item Wb 32); (Item Wb 50); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 110); (Item Wb 99); (Item Wb 104); (Item Wb 114); (Item Wb 111); (Item Wb 110); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e338 : item :=
  (IData (a "glibc_errlist_data_gen#str.338") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 108); (Item Wb 32); (Item Wb 51); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 108); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e339 : item :=
  (IData (a "glibc_errlist_data_gen#str.339") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 108); (Item Wb 32); (Item Wb 51); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e340 : item :=
  (IData (a "glibc_errlist_data_gen#str.340") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 105); (Item Wb 110); (Item Wb 107); (Item Wb 32); (Item Wb 110); (Item Wb 117); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 103); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e341 : item :=
  (IData (a "glibc_errlist_data_gen#str.341") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 114); (Item Wb 111); (Item Wb 116); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 108); (Item Wb 32); (Item Wb 100); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 116); (Item Wb 116); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e342 : item :=
  (IData (a "glibc_errlist_data_gen#str.342") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 67); (Item Wb 83); (Item Wb 73); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 117); (Item Wb 99); (Item Wb 116); (Item Wb 117); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 118); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e343 : item :=
  (IData (a "glibc_errlist_data_gen#str.343") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 108); (Item Wb 32); (Item Wb 50); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 108); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e344 : item :=
  (IData (a "glibc_errlist_data_gen#str.344") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 103); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e345 : item :=
  (IData (a "glibc_errlist_data_gen#str.345") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 101); (Item Wb 115); (Item Wb 116); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 115); (Item Wb 99); (Item Wb 114); (Item Wb 105); (Item Wb 112); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e346 : item :=
  (IData (a "glibc_errlist_data_gen#str.346") (LRo (a "local")) 1 [(Item Wb 69); (Item Wb 120); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 117); (Item Wb 108); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e347 : item :=
  (IData (a "glibc_errlist_data_gen#str.347") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 111); (Item Wb 100); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e348 : item :=
  (IData (a "glibc_errlist_data_gen#str.348") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 101); (Item Wb 115); (Item Wb 116); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 100); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e349 : item :=
  (IData (a "glibc_errlist_data_gen#str.349") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 115); (Item Wb 108); (Item Wb 111); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e350 : item :=
  (IData (a "glibc_errlist_data_gen#str.350") (LRo (a "local")) 1 [(Item Wb 66); (Item Wb 97); (Item Wb 100); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 109); (Item Wb 97); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e351 : item :=
  (IData (a "glibc_errlist_data_gen#str.351") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 32); (Item Wb 110); (Item Wb 101); (Item Wb 116); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 107); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e352 : item :=
  (IData (a "glibc_errlist_data_gen#str.352") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 97); (Item Wb 99); (Item Wb 107); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e353 : item :=
  (IData (a "glibc_errlist_data_gen#str.353") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 100); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e354 : item :=
  (IData (a "glibc_errlist_data_gen#str.354") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 114); (Item Wb 109); (Item Wb 111); (Item Wb 117); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e355 : item :=
  (IData (a "glibc_errlist_data_gen#str.355") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 111); (Item Wb 109); (Item Wb 109); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 99); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e356 : item :=
  (IData (a "glibc_errlist_data_gen#str.356") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 70); (Item Wb 83); (Item Wb 32); (Item Wb 115); (Item Wb 112); (Item Wb 101); (Item Wb 99); (Item Wb 105); (Item Wb 102); (Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e357 : item :=
  (IData (a "glibc_errlist_data_gen#str.357") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 97); (Item Wb 109); (Item Wb 101); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 113); (Item Wb 117); (Item Wb 101); (Item Wb 32); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 101); (Item Wb 116); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 107); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e358 : item :=
  (IData (a "glibc_errlist_data_gen#str.358") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 115); (Item Wb 99); (Item Wb 114); (Item Wb 105); (Item Wb 112); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 97); (Item Wb 100); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e359 : item :=
  (IData (a "glibc_errlist_data_gen#str.359") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 100); (Item Wb 100); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 103); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e360 : item :=
  (IData (a "glibc_errlist_data_gen#str.360") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 99); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 110); (Item Wb 101); (Item Wb 101); (Item Wb 100); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 115); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 114); (Item Wb 97); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e361 : item :=
  (IData (a "glibc_errlist_data_gen#str.361") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 99); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 114); (Item Wb 114); (Item Wb 117); (Item Wb 112); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 115); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 114); (Item Wb 97); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e362 : item :=
  (IData (a "glibc_errlist_data_gen#str.362") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 46); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 114); (Item Wb 114); (Item Wb 117); (Item Wb 112); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e363 : item :=
  (IData (a "glibc_errlist_data_gen#str.363") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 107); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 97); (Item Wb 110); (Item Wb 121); (Item Wb 32); (Item Wb 115); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 114); (Item Wb 97); (Item Wb 114); (Item Wb 105); (Item Wb 101); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e364 : item :=
  (IData (a "glibc_errlist_data_gen#str.364") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 101); (Item Wb 99); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 115); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 114); (Item Wb 97); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 108); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e365 : item :=
  (IData (a "glibc_errlist_data_gen#str.365") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 115); (Item Wb 32); (Item Wb 112); (Item Wb 105); (Item Wb 112); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e366 : item :=
  (IData (a "glibc_errlist_data_gen#str.366") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 116); (Item Wb 114); (Item Wb 117); (Item Wb 99); (Item Wb 116); (Item Wb 117); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 110); (Item Wb 101); (Item Wb 101); (Item Wb 100); (Item Wb 115); (Item Wb 32); (Item Wb 99); (Item Wb 108); (Item Wb 101); (Item Wb 97); (Item Wb 110); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e367 : item :=
  (IData (a "glibc_errlist_data_gen#str.367") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 88); (Item Wb 69); (Item Wb 78); (Item Wb 73); (Item Wb 88); (Item Wb 32); (Item Wb 110); (Item Wb 97); (Item Wb 109); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 116); (Item Wb 121); (Item Wb 112); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e368 : item :=
  (IData (a "glibc_errlist_data_gen#str.368") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 88); (Item Wb 69); (Item Wb 78); (Item Wb 73); (Item Wb 88); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 109); (Item Wb 97); (Item Wb 112); (Item Wb 104); (Item Wb 111); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 118); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e369 : item :=
  (IData (a "glibc_errlist_data_gen#str.369") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 110); (Item Wb 97); (Item Wb 109); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 116); (Item Wb 121); (Item Wb 112); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e370 : item :=
  (IData (a "glibc_errlist_data_gen#str.370") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 73); (Item Wb 47); (Item Wb 79); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e371 : item :=
  (IData (a "glibc_errlist_data_gen#str.371") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 101); (Item Wb 100); (Item Wb 105); (Item Wb 117); (Item Wb 109); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 117); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e372 : item :=
  (IData (a "glibc_errlist_data_gen#str.372") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 111); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 109); (Item Wb 101); (Item Wb 100); (Item Wb 105); (Item Wb 117); (Item Wb 109); (Item Wb 32); (Item Wb 116); (Item Wb 121); (Item Wb 112); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e373 : item :=
  (IData (a "glibc_errlist_data_gen#str.373") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 107); (Item Wb 101); (Item Wb 121); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 118); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e374 : item :=
  (IData (a "glibc_errlist_data_gen#str.374") (LRo (a "local")) 1 [(Item Wb 75); (Item Wb 101); (Item Wb 121); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 115); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e375 : item :=
  (IData (a "glibc_errlist_data_gen#str.375") (LRo (a "local")) 1 [(Item Wb 75); (Item Wb 101); (Item Wb 121); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 115); (Item Wb 32); (Item Wb 98); (Item Wb 101); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 118); (Item Wb 111); (Item Wb 107); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e376 : item :=
  (IData (a "glibc_errlist_data_gen#str.376") (LRo (a "local")) 1 [(Item Wb 75); (Item Wb 101); (Item Wb 121); (Item Wb 32); (Item Wb 119); (Item Wb 97); (Item Wb 115); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 106); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e377 : item :=
  (IData (a "glibc_errlist_data_gen#str.377") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 112); (Item Wb 111); (Item Wb 115); (Item Wb 115); (Item Wb 105); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 100); (Item Wb 117); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 82); (Item Wb 70); (Item Wb 45); (Item Wb 107); (Item Wb 105); (Item Wb 108); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e378 : item :=
  (IData (a "glibc_errlist_data_gen#str.378") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 115); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 100); (Item Wb 119); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errname'23_sys_errname : item :=
  (IData (a "glibc_errname#_sys_errname") (LRo (a "local")) 1 (app (app (app ["0"%irbytes; (Zero 1); "EPERM"%irbytes; (Zero 1); "ENOENT"%irbytes; (Zero 1); "ESRCH"%irbytes; (Zero 1); "EINTR"%irbytes; (Zero 1); "EIO"%irbytes; (Zero 1); "ENXIO"%irbytes; (Zero 1); "E2BIG"%irbytes; (Zero 1); "ENOEXEC"%irbytes; (Zero 1); "EBADF"%irbytes; (Zero 1); "ECHILD"%irbytes; (Zero 1); "EDEADLK"%irbytes; (Zero 1); "ENOMEM"%irbytes; (Zero 1); "EACCES"%irbytes; (Zero 1); "EFAULT"%irbytes; (Zero 1); "ENOTBLK"%irbytes; (Zero 1); "EBUSY"%irbytes] [(Zero 1); "EEXIST"%irbytes; (Zero 1); "EXDEV"%irbytes; (Zero 1); "ENODEV"%irbytes; (Zero 1); "ENOTDIR"%irbytes; (Zero 1); "EISDIR"%irbytes; (Zero 1); "EINVAL"%irbytes; (Zero 1); "EMFILE"%irbytes; (Zero 1); "ENFILE"%irbytes; (Zero 1); "ENOTTY"%irbytes; (Zero 1); "ETXTBSY"%irbytes; (Zero 1); "EFBIG"%irbytes; (Zero 1); "ENOSPC"%irbytes; (Zero 1); "ESPIPE"%irbytes; (Zero 1); "EROFS"%irbytes; (Zero 1); "EMLINK"%irbytes; (Zero 1); "EPIPE"%irbytes; (Zero 1)]) (app ["EDOM"%irbytes; (Zero 1); "ERANGE"%irbytes; (Zero 1); "EAGAIN"%irbytes; (Zero 1); "EINPROGRESS"%irbytes; (Zero 1); "EALREADY"%irbytes; (Zero 1); "ENOTSOCK"%irbytes; (Zero 1); "EMSGSIZE"%irbytes; (Zero 1); "EPROTOTYPE"%irbytes; (Zero 1); "ENOPROTOOPT"%irbytes; (Zero 1); "EPROTONOSUPPORT"%irbytes; (Zero 1); "ESOCKTNOSUPPORT"%irbytes; (Zero 1); "EOPNOTSUPP"%irbytes; (Zero 1); "EPFNOSUPPORT"%irbytes; (Zero 1); "EAFNOSUPPORT"%irbytes; (Zero 1); "EADDRINUSE"%irbytes; (Zero 1); "EADDRNOTAVAIL"%irbytes; (Zero 1); "ENETDOWN"%irbytes] [(Zero 1); "ENETUNREACH"%irbytes; (Zero 1); "ENETRESET"%irbytes; (Zero 1); "ECONNABORTED"%irbytes; (Zero 1); "ECONNRESET"%irbytes; (Zero 1); "ENOBUFS"%irbytes; (Zero 1); "EISCONN"%irbytes; (Zero 1); "ENOTCONN"%irbytes; (Zero 1); "EDESTADDRREQ"%irbytes; (Zero 1); "ESHUTDOWN"%irbytes; (Zero 1); "ETOOMANYREFS"%irbytes; (Zero 1); "ETIMEDOUT"%irbytes; (Zero 1); "ECONNREFUSED"%irbytes; (Zero 1); "ELOOP"%irbytes; (Zero 1); "ENAMETOOLONG"%irbytes; (Zero 1); "EHOSTDOWN"%irbytes; (Zero 1); "EHOSTUNREACH"%irbytes; (Zero 1)])) (app (app ["ENOTEMPTY"%irbytes; (Zero 1); "EUSERS"%irbytes; (Zero 1); "EDQUOT"%irbytes; (Zero 1); "ESTALE"%irbytes; (Zero 1); "EREMOTE"%irbytes; (Zero 1); "ENOLCK"%irbytes; (Zero 1); "ENOSYS"%irbytes; (Zero 1); "EILSEQ"%irbytes; (Zero 1); "EBADMSG"%irbytes; (Zero 1); "EIDRM"%irbytes; (Zero 1); "EMULTIHOP"%irbytes; (Zero 1); "ENODATA"%irbytes; (Zero 1); "ENOLINK"%irbytes; (Zero 1); "ENOMSG"%irbytes; (Zero 1); "ENOSR"%irbytes; (Zero 1); "ENOSTR"%irbytes; (Zero 1); "EOVERFLOW"%irbytes] [(Zero 1); "EPROTO"%irbytes; (Zero 1); "ETIME"%irbytes; (Zero 1); "ECANCELED"%irbytes; (Zero 1); "EOWNERDEAD"%irbytes; (Zero 1); "ENOTRECOVERABLE"%irbytes; (Zero 1); "ERESTART"%irbytes; (Zero 1); "ECHRNG"%irbytes; (Zero 1); "EL2NSYNC"%irbytes; (Zero 1); "EL3HLT"%irbytes; (Zero 1); "EL3RST"%irbytes; (Zero 1); "ELNRNG"%irbytes; (Zero 1); "EUNATCH"%irbytes; (Zero 1); "ENOCSI"%irbytes; (Zero 1); "EL2HLT"%irbytes; (Zero 1); "EBADE"%irbytes; (Zero 1); "EBADR"%irbytes; (Zero 1)]) (app ["EXFULL"%irbytes; (Zero 1); "ENOANO"%irbytes; (Zero 1); "EBADRQC"%irbytes; (Zero 1); "EBADSLT"%irbytes; (Zero 1); "EBFONT"%irbytes; (Zero 1); "ENONET"%irbytes; (Zero 1); "ENOPKG"%irbytes; (Zero 1); "EADV"%irbytes; (Zero 1); "ESRMNT"%irbytes; (Zero 1); "ECOMM"%irbytes; (Zero 1); "EDOTDOT"%irbytes; (Zero 1); "ENOTUNIQ"%irbytes; (Zero 1); "EBADFD"%irbytes; (Zero 1); "EREMCHG"%irbytes; (Zero 1); "ELIBACC"%irbytes; (Zero 1); "ELIBBAD"%irbytes; (Zero 1); "ELIBSCN"%irbytes] [(Zero 1); "ELIBMAX"%irbytes; (Zero 1); "ELIBEXEC"%irbytes; (Zero 1); "ESTRPIPE"%irbytes; (Zero 1); "EUCLEAN"%irbytes; (Zero 1); "ENOTNAM"%irbytes; (Zero 1); "ENAVAIL"%irbytes; (Zero 1); "EISNAM"%irbytes; (Zero 1); "EREMOTEIO"%irbytes; (Zero 1); "ENOMEDIUM"%irbytes; (Zero 1); "EMEDIUMTYPE"%irbytes; (Zero 1); "ENOKEY"%irbytes; (Zero 1); "EKEYEXPIRED"%irbytes; (Zero 1); "EKEYREVOKED"%irbytes; (Zero 1); "EKEYREJECTED"%irbytes; (Zero 1); "ERFKILL"%irbytes; (Zero 1); "EHWPOISON"%irbytes; (Zero 1)])))).

Definition hello_image_item_glibc_errname'23_sys_errnameidx : item :=
  (IData (a "glibc_errname#_sys_errnameidx") (LRo (a "local")) 2 (app (app [(Item Wh 0); (Item Wh 2); (Item Wh 8); (Item Wh 15); (Item Wh 21); (Item Wh 27); (Item Wh 31); (Item Wh 37); (Item Wh 43); (Item Wh 51); (Item Wh 57); (Item Wh 229); (Item Wh 72); (Item Wh 79); (Item Wh 86); (Item Wh 93); (Item Wh 101); (Item Wh 107); (Item Wh 114); (Item Wh 120); (Item Wh 127); (Item Wh 135); (Item Wh 142); (Item Wh 156); (Item Wh 149); (Item Wh 163); (Item Wh 170); (Item Wh 178); (Item Wh 184); (Item Wh 191); (Item Wh 198); (Item Wh 204); (Item Wh 211)] [(Item Wh 217); (Item Wh 222); (Item Wh 64); (Item Wh 537); (Item Wh 612); (Item Wh 619); (Item Wh 573); (Item Wh 531); (Zero 2); (Item Wh 673); (Item Wh 641); (Item Wh 762); (Item Wh 769); (Item Wh 778); (Item Wh 785); (Item Wh 792); (Item Wh 799); (Item Wh 807); (Item Wh 814); (Item Wh 821); (Item Wh 827); (Item Wh 833); (Item Wh 840); (Item Wh 847); (Item Wh 855); (Zero 2); (Item Wh 863); (Item Wh 686); (Item Wh 657); (Item Wh 710); (Item Wh 680); (Item Wh 870); (Item Wh 877); (Item Wh 604)]) (app [(Item Wh 665); (Item Wh 884); (Item Wh 889); (Item Wh 896); (Item Wh 703); (Item Wh 647); (Item Wh 902); (Item Wh 633); (Item Wh 693); (Item Wh 910); (Item Wh 919); (Item Wh 926); (Item Wh 934); (Item Wh 942); (Item Wh 950); (Item Wh 958); (Item Wh 966); (Item Wh 626); (Item Wh 753); (Item Wh 975); (Item Wh 583); (Item Wh 257); (Item Wh 472); (Item Wh 266); (Item Wh 275); (Item Wh 286); (Item Wh 298); (Item Wh 314); (Item Wh 330); (Item Wh 341); (Item Wh 354); (Item Wh 367); (Item Wh 378)] [(Item Wh 392); (Item Wh 401); (Item Wh 413); (Item Wh 423); (Item Wh 436); (Item Wh 447); (Item Wh 455); (Item Wh 463); (Item Wh 485); (Item Wh 495); (Item Wh 508); (Item Wh 518); (Item Wh 550); (Item Wh 560); (Item Wh 248); (Item Wh 236); (Item Wh 597); (Item Wh 984); (Item Wh 992); (Item Wh 1000); (Item Wh 1008); (Item Wh 1015); (Item Wh 590); (Item Wh 1025); (Item Wh 1035); (Item Wh 716); (Item Wh 1047); (Item Wh 1054); (Item Wh 1066); (Item Wh 1078); (Item Wh 726); (Item Wh 737); (Item Wh 1091); (Item Wh 1099)]))).

Definition hello_image_item_fprintf : item :=
  (IAlias (a "fprintf") (a "export") (a "__fprintf")).

Definition hello_image_item__IO_funlockfile : item :=
  (IAlias (a "_IO_funlockfile") (a "weak") (a "__GI___funlockfile")).

Definition hello_image_item_glibc_grouping_iterator'23str'2e41 : item :=
  (IData (a "glibc_grouping_iterator#str.41") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 114); (Item Wb 101); (Item Wb 109); (Item Wb 97); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 62); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_grouping_iterator'23str'2e42 : item :=
  (IData (a "glibc_grouping_iterator#str.42") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 114); (Item Wb 111); (Item Wb 117); (Item Wb 112); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 95); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_grouping_iterator'23str'2e43 : item :=
  (IData (a "glibc_grouping_iterator#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 114); (Item Wb 111); (Item Wb 117); (Item Wb 112); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 95); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 95); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item___GI__itoa_lower_digits : item :=
  (IData (a "__GI__itoa_lower_digits") (LRo (a "export")) 1 ["0123456789abcdefghijklmnopqrstuvwxyz"%irbytes]).

Definition hello_image_item___GI__itoa_upper_digits : item :=
  (IData (a "__GI__itoa_upper_digits") (LRo (a "export")) 1 ["0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"%irbytes]).

Definition hello_image_item__itowa_lower_digits : item :=
  (IData (a "_itowa_lower_digits") (LRo (a "export")) 4 [(Str (app (app [48; 0; 0; 0; 49; 0; 0; 0; 50; 0; 0; 0; 51; 0; 0; 0; 52; 0; 0; 0; 53; 0; 0; 0; 54; 0; 0; 0; 55; 0; 0; 0; 56; 0; 0; 0] [57; 0; 0; 0; 97; 0; 0; 0; 98; 0; 0; 0; 99; 0; 0; 0; 100; 0; 0; 0; 101; 0; 0; 0; 102; 0; 0; 0; 103; 0; 0; 0; 104; 0; 0; 0]) (app [105; 0; 0; 0; 106; 0; 0; 0; 107; 0; 0; 0; 108; 0; 0; 0; 109; 0; 0; 0; 110; 0; 0; 0; 111; 0; 0; 0; 112; 0; 0; 0; 113; 0; 0; 0] [114; 0; 0; 0; 115; 0; 0; 0; 116; 0; 0; 0; 117; 0; 0; 0; 118; 0; 0; 0; 119; 0; 0; 0; 120; 0; 0; 0; 121; 0; 0; 0; 122; 0; 0; 0])))]).

Definition hello_image_item__itowa_upper_digits : item :=
  (IData (a "_itowa_upper_digits") (LRo (a "export")) 4 [(Str (app (app [48; 0; 0; 0; 49; 0; 0; 0; 50; 0; 0; 0; 51; 0; 0; 0; 52; 0; 0; 0; 53; 0; 0; 0; 54; 0; 0; 0; 55; 0; 0; 0; 56; 0; 0; 0] [57; 0; 0; 0; 65; 0; 0; 0; 66; 0; 0; 0; 67; 0; 0; 0; 68; 0; 0; 0; 69; 0; 0; 0; 70; 0; 0; 0; 71; 0; 0; 0; 72; 0; 0; 0]) (app [73; 0; 0; 0; 74; 0; 0; 0; 75; 0; 0; 0; 76; 0; 0; 0; 77; 0; 0; 0; 78; 0; 0; 0; 79; 0; 0; 0; 80; 0; 0; 0; 81; 0; 0; 0] [82; 0; 0; 0; 83; 0; 0; 0; 84; 0; 0; 0; 85; 0; 0; 0; 86; 0; 0; 0; 87; 0; 0; 0; 88; 0; 0; 0; 89; 0; 0; 0; 90; 0; 0; 0])))]).

Definition hello_image_item_printf : item :=
  (IAlias (a "printf") (a "export") (a "__printf")).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e266 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.266") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e267 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.267") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e268 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.268") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 99); (Item Wb 111); (Item Wb 109); (Item Wb 109); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).
