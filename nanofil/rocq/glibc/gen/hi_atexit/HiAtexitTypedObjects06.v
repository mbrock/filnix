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

Definition hi_item_glibc_C_ctype'23str'2e258 : item :=
  (IData (a "glibc_C_ctype#str.258") (LRo (a "local")) 1 (app [(Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 0); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 0); (Item Wb 97); (Item Wb 108); (Item Wb 112); (Item Wb 104); (Item Wb 97); (Item Wb 0); (Item Wb 100); (Item Wb 105); (Item Wb 103); (Item Wb 105); (Item Wb 116); (Item Wb 0); (Item Wb 120); (Item Wb 100); (Item Wb 105); (Item Wb 103); (Item Wb 105); (Item Wb 116); (Item Wb 0); (Item Wb 115); (Item Wb 112); (Item Wb 97); (Item Wb 99); (Item Wb 101); (Item Wb 0)] [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 0); (Item Wb 103); (Item Wb 114); (Item Wb 97); (Item Wb 112); (Item Wb 104); (Item Wb 0); (Item Wb 98); (Item Wb 108); (Item Wb 97); (Item Wb 110); (Item Wb 107); (Item Wb 0); (Item Wb 99); (Item Wb 110); (Item Wb 116); (Item Wb 114); (Item Wb 108); (Item Wb 0); (Item Wb 112); (Item Wb 117); (Item Wb 110); (Item Wb 99); (Item Wb 116); (Item Wb 0); (Item Wb 97); (Item Wb 108); (Item Wb 110); (Item Wb 117); (Item Wb 109); (Item Wb 0); (Item Wb 0)])).

Definition hi_item_glibc_C_ctype'23str'2e259 : item :=
  (IData (a "glibc_C_ctype#str.259") (LRo (a "local")) 1 [(Item Wb 116); (Item Wb 111); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 0); (Item Wb 116); (Item Wb 111); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 0); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e260 : item :=
  (IData (a "glibc_C_ctype#str.260") (LRo (a "local")) 1 [(Item Wb 48); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e261 : item :=
  (IData (a "glibc_C_ctype#str.261") (LRo (a "local")) 1 [(Item Wb 49); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e262 : item :=
  (IData (a "glibc_C_ctype#str.262") (LRo (a "local")) 1 [(Item Wb 50); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e263 : item :=
  (IData (a "glibc_C_ctype#str.263") (LRo (a "local")) 1 [(Item Wb 51); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e264 : item :=
  (IData (a "glibc_C_ctype#str.264") (LRo (a "local")) 1 [(Item Wb 52); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e265 : item :=
  (IData (a "glibc_C_ctype#str.265") (LRo (a "local")) 1 [(Item Wb 53); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e266 : item :=
  (IData (a "glibc_C_ctype#str.266") (LRo (a "local")) 1 [(Item Wb 54); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e267 : item :=
  (IData (a "glibc_C_ctype#str.267") (LRo (a "local")) 1 [(Item Wb 55); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e268 : item :=
  (IData (a "glibc_C_ctype#str.268") (LRo (a "local")) 1 [(Item Wb 56); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e269 : item :=
  (IData (a "glibc_C_ctype#str.269") (LRo (a "local")) 1 [(Item Wb 57); (Item Wb 0)]).

Definition hi_item_glibc_C_ctype'23str'2e270 : item :=
  (IData (a "glibc_C_ctype#str.270") (LRo (a "local")) 4 [(Item Ww 48); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e271 : item :=
  (IData (a "glibc_C_ctype#str.271") (LRo (a "local")) 4 [(Item Ww 49); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e272 : item :=
  (IData (a "glibc_C_ctype#str.272") (LRo (a "local")) 4 [(Item Ww 50); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e273 : item :=
  (IData (a "glibc_C_ctype#str.273") (LRo (a "local")) 4 [(Item Ww 51); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e274 : item :=
  (IData (a "glibc_C_ctype#str.274") (LRo (a "local")) 4 [(Item Ww 52); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e275 : item :=
  (IData (a "glibc_C_ctype#str.275") (LRo (a "local")) 4 [(Item Ww 53); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e276 : item :=
  (IData (a "glibc_C_ctype#str.276") (LRo (a "local")) 4 [(Item Ww 54); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e277 : item :=
  (IData (a "glibc_C_ctype#str.277") (LRo (a "local")) 4 [(Item Ww 55); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e278 : item :=
  (IData (a "glibc_C_ctype#str.278") (LRo (a "local")) 4 [(Item Ww 56); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e279 : item :=
  (IData (a "glibc_C_ctype#str.279") (LRo (a "local")) 4 [(Item Ww 57); (Item Ww 0)]).

Definition hi_item_glibc_C_ctype'23str'2e280 : item :=
  (IData (a "glibc_C_ctype#str.280") (LRo (a "local")) 4 [(Item Ww 63); (Item Ww 0)]).
