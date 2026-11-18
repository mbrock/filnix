(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e274 : item :=
  (IData (a "glibc_errlist_data_gen#str.274") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 108); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e275 : item :=
  (IData (a "glibc_errlist_data_gen#str.275") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 115); (Item Wb 112); (Item Wb 97); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 108); (Item Wb 101); (Item Wb 102); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).

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
  (IData (a "glibc_errname#_sys_errname") (LRo (a "local")) 1 (app (app (app [(Str [48]); (Zero 1); (Str [69; 80; 69; 82; 77]); (Zero 1); (Str [69; 78; 79; 69; 78; 84]); (Zero 1); (Str [69; 83; 82; 67; 72]); (Zero 1); (Str [69; 73; 78; 84; 82]); (Zero 1); (Str [69; 73; 79]); (Zero 1); (Str [69; 78; 88; 73; 79]); (Zero 1); (Str [69; 50; 66; 73; 71]); (Zero 1); (Str [69; 78; 79; 69; 88; 69; 67]); (Zero 1); (Str [69; 66; 65; 68; 70]); (Zero 1); (Str [69; 67; 72; 73; 76; 68]); (Zero 1); (Str [69; 68; 69; 65; 68; 76; 75]); (Zero 1); (Str [69; 78; 79; 77; 69; 77]); (Zero 1); (Str [69; 65; 67; 67; 69; 83]); (Zero 1); (Str [69; 70; 65; 85; 76; 84]); (Zero 1); (Str [69; 78; 79; 84; 66; 76; 75]); (Zero 1); (Str [69; 66; 85; 83; 89])] [(Zero 1); (Str [69; 69; 88; 73; 83; 84]); (Zero 1); (Str [69; 88; 68; 69; 86]); (Zero 1); (Str [69; 78; 79; 68; 69; 86]); (Zero 1); (Str [69; 78; 79; 84; 68; 73; 82]); (Zero 1); (Str [69; 73; 83; 68; 73; 82]); (Zero 1); (Str [69; 73; 78; 86; 65; 76]); (Zero 1); (Str [69; 77; 70; 73; 76; 69]); (Zero 1); (Str [69; 78; 70; 73; 76; 69]); (Zero 1); (Str [69; 78; 79; 84; 84; 89]); (Zero 1); (Str [69; 84; 88; 84; 66; 83; 89]); (Zero 1); (Str [69; 70; 66; 73; 71]); (Zero 1); (Str [69; 78; 79; 83; 80; 67]); (Zero 1); (Str [69; 83; 80; 73; 80; 69]); (Zero 1); (Str [69; 82; 79; 70; 83]); (Zero 1); (Str [69; 77; 76; 73; 78; 75]); (Zero 1); (Str [69; 80; 73; 80; 69]); (Zero 1)]) (app [(Str [69; 68; 79; 77]); (Zero 1); (Str [69; 82; 65; 78; 71; 69]); (Zero 1); (Str [69; 65; 71; 65; 73; 78]); (Zero 1); (Str [69; 73; 78; 80; 82; 79; 71; 82; 69; 83; 83]); (Zero 1); (Str [69; 65; 76; 82; 69; 65; 68; 89]); (Zero 1); (Str [69; 78; 79; 84; 83; 79; 67; 75]); (Zero 1); (Str [69; 77; 83; 71; 83; 73; 90; 69]); (Zero 1); (Str [69; 80; 82; 79; 84; 79; 84; 89; 80; 69]); (Zero 1); (Str [69; 78; 79; 80; 82; 79; 84; 79; 79; 80; 84]); (Zero 1); (Str [69; 80; 82; 79; 84; 79; 78; 79; 83; 85; 80; 80; 79; 82; 84]); (Zero 1); (Str [69; 83; 79; 67; 75; 84; 78; 79; 83; 85; 80; 80; 79; 82; 84]); (Zero 1); (Str [69; 79; 80; 78; 79; 84; 83; 85; 80; 80]); (Zero 1); (Str [69; 80; 70; 78; 79; 83; 85; 80; 80; 79; 82; 84]); (Zero 1); (Str [69; 65; 70; 78; 79; 83; 85; 80; 80; 79; 82; 84]); (Zero 1); (Str [69; 65; 68; 68; 82; 73; 78; 85; 83; 69]); (Zero 1); (Str [69; 65; 68; 68; 82; 78; 79; 84; 65; 86; 65; 73; 76]); (Zero 1); (Str [69; 78; 69; 84; 68; 79; 87; 78])] [(Zero 1); (Str [69; 78; 69; 84; 85; 78; 82; 69; 65; 67; 72]); (Zero 1); (Str [69; 78; 69; 84; 82; 69; 83; 69; 84]); (Zero 1); (Str [69; 67; 79; 78; 78; 65; 66; 79; 82; 84; 69; 68]); (Zero 1); (Str [69; 67; 79; 78; 78; 82; 69; 83; 69; 84]); (Zero 1); (Str [69; 78; 79; 66; 85; 70; 83]); (Zero 1); (Str [69; 73; 83; 67; 79; 78; 78]); (Zero 1); (Str [69; 78; 79; 84; 67; 79; 78; 78]); (Zero 1); (Str [69; 68; 69; 83; 84; 65; 68; 68; 82; 82; 69; 81]); (Zero 1); (Str [69; 83; 72; 85; 84; 68; 79; 87; 78]); (Zero 1); (Str [69; 84; 79; 79; 77; 65; 78; 89; 82; 69; 70; 83]); (Zero 1); (Str [69; 84; 73; 77; 69; 68; 79; 85; 84]); (Zero 1); (Str [69; 67; 79; 78; 78; 82; 69; 70; 85; 83; 69; 68]); (Zero 1); (Str [69; 76; 79; 79; 80]); (Zero 1); (Str [69; 78; 65; 77; 69; 84; 79; 79; 76; 79; 78; 71]); (Zero 1); (Str [69; 72; 79; 83; 84; 68; 79; 87; 78]); (Zero 1); (Str [69; 72; 79; 83; 84; 85; 78; 82; 69; 65; 67; 72]); (Zero 1)])) (app (app [(Str [69; 78; 79; 84; 69; 77; 80; 84; 89]); (Zero 1); (Str [69; 85; 83; 69; 82; 83]); (Zero 1); (Str [69; 68; 81; 85; 79; 84]); (Zero 1); (Str [69; 83; 84; 65; 76; 69]); (Zero 1); (Str [69; 82; 69; 77; 79; 84; 69]); (Zero 1); (Str [69; 78; 79; 76; 67; 75]); (Zero 1); (Str [69; 78; 79; 83; 89; 83]); (Zero 1); (Str [69; 73; 76; 83; 69; 81]); (Zero 1); (Str [69; 66; 65; 68; 77; 83; 71]); (Zero 1); (Str [69; 73; 68; 82; 77]); (Zero 1); (Str [69; 77; 85; 76; 84; 73; 72; 79; 80]); (Zero 1); (Str [69; 78; 79; 68; 65; 84; 65]); (Zero 1); (Str [69; 78; 79; 76; 73; 78; 75]); (Zero 1); (Str [69; 78; 79; 77; 83; 71]); (Zero 1); (Str [69; 78; 79; 83; 82]); (Zero 1); (Str [69; 78; 79; 83; 84; 82]); (Zero 1); (Str [69; 79; 86; 69; 82; 70; 76; 79; 87])] [(Zero 1); (Str [69; 80; 82; 79; 84; 79]); (Zero 1); (Str [69; 84; 73; 77; 69]); (Zero 1); (Str [69; 67; 65; 78; 67; 69; 76; 69; 68]); (Zero 1); (Str [69; 79; 87; 78; 69; 82; 68; 69; 65; 68]); (Zero 1); (Str [69; 78; 79; 84; 82; 69; 67; 79; 86; 69; 82; 65; 66; 76; 69]); (Zero 1); (Str [69; 82; 69; 83; 84; 65; 82; 84]); (Zero 1); (Str [69; 67; 72; 82; 78; 71]); (Zero 1); (Str [69; 76; 50; 78; 83; 89; 78; 67]); (Zero 1); (Str [69; 76; 51; 72; 76; 84]); (Zero 1); (Str [69; 76; 51; 82; 83; 84]); (Zero 1); (Str [69; 76; 78; 82; 78; 71]); (Zero 1); (Str [69; 85; 78; 65; 84; 67; 72]); (Zero 1); (Str [69; 78; 79; 67; 83; 73]); (Zero 1); (Str [69; 76; 50; 72; 76; 84]); (Zero 1); (Str [69; 66; 65; 68; 69]); (Zero 1); (Str [69; 66; 65; 68; 82]); (Zero 1)]) (app [(Str [69; 88; 70; 85; 76; 76]); (Zero 1); (Str [69; 78; 79; 65; 78; 79]); (Zero 1); (Str [69; 66; 65; 68; 82; 81; 67]); (Zero 1); (Str [69; 66; 65; 68; 83; 76; 84]); (Zero 1); (Str [69; 66; 70; 79; 78; 84]); (Zero 1); (Str [69; 78; 79; 78; 69; 84]); (Zero 1); (Str [69; 78; 79; 80; 75; 71]); (Zero 1); (Str [69; 65; 68; 86]); (Zero 1); (Str [69; 83; 82; 77; 78; 84]); (Zero 1); (Str [69; 67; 79; 77; 77]); (Zero 1); (Str [69; 68; 79; 84; 68; 79; 84]); (Zero 1); (Str [69; 78; 79; 84; 85; 78; 73; 81]); (Zero 1); (Str [69; 66; 65; 68; 70; 68]); (Zero 1); (Str [69; 82; 69; 77; 67; 72; 71]); (Zero 1); (Str [69; 76; 73; 66; 65; 67; 67]); (Zero 1); (Str [69; 76; 73; 66; 66; 65; 68]); (Zero 1); (Str [69; 76; 73; 66; 83; 67; 78])] [(Zero 1); (Str [69; 76; 73; 66; 77; 65; 88]); (Zero 1); (Str [69; 76; 73; 66; 69; 88; 69; 67]); (Zero 1); (Str [69; 83; 84; 82; 80; 73; 80; 69]); (Zero 1); (Str [69; 85; 67; 76; 69; 65; 78]); (Zero 1); (Str [69; 78; 79; 84; 78; 65; 77]); (Zero 1); (Str [69; 78; 65; 86; 65; 73; 76]); (Zero 1); (Str [69; 73; 83; 78; 65; 77]); (Zero 1); (Str [69; 82; 69; 77; 79; 84; 69; 73; 79]); (Zero 1); (Str [69; 78; 79; 77; 69; 68; 73; 85; 77]); (Zero 1); (Str [69; 77; 69; 68; 73; 85; 77; 84; 89; 80; 69]); (Zero 1); (Str [69; 78; 79; 75; 69; 89]); (Zero 1); (Str [69; 75; 69; 89; 69; 88; 80; 73; 82; 69; 68]); (Zero 1); (Str [69; 75; 69; 89; 82; 69; 86; 79; 75; 69; 68]); (Zero 1); (Str [69; 75; 69; 89; 82; 69; 74; 69; 67; 84; 69; 68]); (Zero 1); (Str [69; 82; 70; 75; 73; 76; 76]); (Zero 1); (Str [69; 72; 87; 80; 79; 73; 83; 79; 78]); (Zero 1)])))).

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
  (IData (a "__GI__itoa_lower_digits") (LRo (a "export")) 1 [(Str [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122])]).

Definition hello_image_item___GI__itoa_upper_digits : item :=
  (IData (a "__GI__itoa_upper_digits") (LRo (a "export")) 1 [(Str [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90])]).

Definition hello_image_item__itowa_lower_digits : item :=
  (IData (a "_itowa_lower_digits") (LRo (a "export")) 4 [(Str (app (app [48; 0; 0; 0; 49; 0; 0; 0; 50; 0; 0; 0; 51; 0; 0; 0; 52; 0; 0; 0; 53; 0; 0; 0; 54; 0; 0; 0; 55; 0; 0; 0; 56; 0; 0; 0] [57; 0; 0; 0; 97; 0; 0; 0; 98; 0; 0; 0; 99; 0; 0; 0; 100; 0; 0; 0; 101; 0; 0; 0; 102; 0; 0; 0; 103; 0; 0; 0; 104; 0; 0; 0]) (app [105; 0; 0; 0; 106; 0; 0; 0; 107; 0; 0; 0; 108; 0; 0; 0; 109; 0; 0; 0; 110; 0; 0; 0; 111; 0; 0; 0; 112; 0; 0; 0; 113; 0; 0; 0] [114; 0; 0; 0; 115; 0; 0; 0; 116; 0; 0; 0; 117; 0; 0; 0; 118; 0; 0; 0; 119; 0; 0; 0; 120; 0; 0; 0; 121; 0; 0; 0; 122; 0; 0; 0])))]).
