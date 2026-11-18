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

Definition hello_image_item_glibc_C_ctype'23str'2e258 : item :=
  (IData (a "glibc_C_ctype#str.258") (LRo (a "local")) 1 (app [(Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 0); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 0); (Item Wb 97); (Item Wb 108); (Item Wb 112); (Item Wb 104); (Item Wb 97); (Item Wb 0); (Item Wb 100); (Item Wb 105); (Item Wb 103); (Item Wb 105); (Item Wb 116); (Item Wb 0); (Item Wb 120); (Item Wb 100); (Item Wb 105); (Item Wb 103); (Item Wb 105); (Item Wb 116); (Item Wb 0); (Item Wb 115); (Item Wb 112); (Item Wb 97); (Item Wb 99); (Item Wb 101); (Item Wb 0)] [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 0); (Item Wb 103); (Item Wb 114); (Item Wb 97); (Item Wb 112); (Item Wb 104); (Item Wb 0); (Item Wb 98); (Item Wb 108); (Item Wb 97); (Item Wb 110); (Item Wb 107); (Item Wb 0); (Item Wb 99); (Item Wb 110); (Item Wb 116); (Item Wb 114); (Item Wb 108); (Item Wb 0); (Item Wb 112); (Item Wb 117); (Item Wb 110); (Item Wb 99); (Item Wb 116); (Item Wb 0); (Item Wb 97); (Item Wb 108); (Item Wb 110); (Item Wb 117); (Item Wb 109); (Item Wb 0); (Item Wb 0)])).

Definition hello_image_item_glibc_C_ctype'23str'2e259 : item :=
  (IData (a "glibc_C_ctype#str.259") (LRo (a "local")) 1 [(Item Wb 116); (Item Wb 111); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 0); (Item Wb 116); (Item Wb 111); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 0); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e260 : item :=
  (IData (a "glibc_C_ctype#str.260") (LRo (a "local")) 1 [(Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e261 : item :=
  (IData (a "glibc_C_ctype#str.261") (LRo (a "local")) 1 [(Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e262 : item :=
  (IData (a "glibc_C_ctype#str.262") (LRo (a "local")) 1 [(Item Wb 50); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e263 : item :=
  (IData (a "glibc_C_ctype#str.263") (LRo (a "local")) 1 [(Item Wb 51); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e264 : item :=
  (IData (a "glibc_C_ctype#str.264") (LRo (a "local")) 1 [(Item Wb 52); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e265 : item :=
  (IData (a "glibc_C_ctype#str.265") (LRo (a "local")) 1 [(Item Wb 53); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e266 : item :=
  (IData (a "glibc_C_ctype#str.266") (LRo (a "local")) 1 [(Item Wb 54); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e267 : item :=
  (IData (a "glibc_C_ctype#str.267") (LRo (a "local")) 1 [(Item Wb 55); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e268 : item :=
  (IData (a "glibc_C_ctype#str.268") (LRo (a "local")) 1 [(Item Wb 56); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e269 : item :=
  (IData (a "glibc_C_ctype#str.269") (LRo (a "local")) 1 [(Item Wb 57); (Item Wb 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e270 : item :=
  (IData (a "glibc_C_ctype#str.270") (LRo (a "local")) 4 [(Item Ww 48); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e271 : item :=
  (IData (a "glibc_C_ctype#str.271") (LRo (a "local")) 4 [(Item Ww 49); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e272 : item :=
  (IData (a "glibc_C_ctype#str.272") (LRo (a "local")) 4 [(Item Ww 50); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e273 : item :=
  (IData (a "glibc_C_ctype#str.273") (LRo (a "local")) 4 [(Item Ww 51); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e274 : item :=
  (IData (a "glibc_C_ctype#str.274") (LRo (a "local")) 4 [(Item Ww 52); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e275 : item :=
  (IData (a "glibc_C_ctype#str.275") (LRo (a "local")) 4 [(Item Ww 53); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e276 : item :=
  (IData (a "glibc_C_ctype#str.276") (LRo (a "local")) 4 [(Item Ww 54); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e277 : item :=
  (IData (a "glibc_C_ctype#str.277") (LRo (a "local")) 4 [(Item Ww 55); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e278 : item :=
  (IData (a "glibc_C_ctype#str.278") (LRo (a "local")) 4 [(Item Ww 56); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e279 : item :=
  (IData (a "glibc_C_ctype#str.279") (LRo (a "local")) 4 [(Item Ww 57); (Item Ww 0)]).

Definition hello_image_item_glibc_C_ctype'23str'2e280 : item :=
  (IData (a "glibc_C_ctype#str.280") (LRo (a "local")) 4 [(Item Ww 63); (Item Ww 0)]).

Definition hello_image_item__nl_C_LC_IDENTIFICATION : item :=
  (IData (a "_nl_C_LC_IDENTIFICATION") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 16); (Zero 4); (Sym (a "glibc_C_identification#str.40") 0); (Sym (a "glibc_C_identification#str.41") 0); (Sym (a "glibc_C_identification#str.42") 0); (Sym (a "glibc_C_identification#str.43") 0); (Sym (a "glibc_C_identification#str.44") 0); (Sym (a "glibc_C_identification#str.45") 0); (Sym (a "glibc_C_identification#str.46") 0); (Sym (a "glibc_C_identification#str.47") 0); (Sym (a "glibc_C_identification#str.48") 0); (Sym (a "glibc_C_identification#str.47") 0); (Sym (a "glibc_C_identification#str.47") 0); (Sym (a "glibc_C_identification#str.47") 0); (Sym (a "glibc_C_identification#str.49") 0); (Sym (a "glibc_C_identification#str.50") 0); (Sym (a "glibc_C_identification#str.51") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e40 : item :=
  (IData (a "glibc_C_identification#str.40") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 83); (Item Wb 79); (Item Wb 47); (Item Wb 73); (Item Wb 69); (Item Wb 67); (Item Wb 32); (Item Wb 49); (Item Wb 52); (Item Wb 54); (Item Wb 53); (Item Wb 50); (Item Wb 32); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 32); (Item Wb 70); (Item Wb 68); (Item Wb 67); (Item Wb 67); (Item Wb 45); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e41 : item :=
  (IData (a "glibc_C_identification#str.41") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 83); (Item Wb 79); (Item Wb 47); (Item Wb 73); (Item Wb 69); (Item Wb 67); (Item Wb 32); (Item Wb 74); (Item Wb 84); (Item Wb 67); (Item Wb 49); (Item Wb 47); (Item Wb 83); (Item Wb 67); (Item Wb 50); (Item Wb 50); (Item Wb 47); (Item Wb 87); (Item Wb 71); (Item Wb 50); (Item Wb 48); (Item Wb 32); (Item Wb 45); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 122); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e42 : item :=
  (IData (a "glibc_C_identification#str.42") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 47); (Item Wb 111); (Item Wb 32); (Item Wb 75); (Item Wb 101); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 83); (Item Wb 105); (Item Wb 109); (Item Wb 111); (Item Wb 110); (Item Wb 115); (Item Wb 101); (Item Wb 110); (Item Wb 44); (Item Wb 32); (Item Wb 83); (Item Wb 107); (Item Wb 116); (Item Wb 46); (Item Wb 32); (Item Wb 74); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 101); (Item Wb 110); (Item Wb 115); (Item Wb 32); (Item Wb 65); (Item Wb 108); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 56); (Item Wb 44); (Item Wb 32); (Item Wb 68); (Item Wb 75); (Item Wb 45); (Item Wb 49); (Item Wb 54); (Item Wb 49); (Item Wb 53); (Item Wb 32); (Item Wb 75); (Item Wb 111); (Item Wb 98); (Item Wb 101); (Item Wb 110); (Item Wb 104); (Item Wb 97); (Item Wb 118); (Item Wb 110); (Item Wb 32); (Item Wb 86); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e43 : item :=
  (IData (a "glibc_C_identification#str.43") (LRo (a "local")) 1 [(Item Wb 75); (Item Wb 101); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 83); (Item Wb 105); (Item Wb 109); (Item Wb 111); (Item Wb 110); (Item Wb 115); (Item Wb 101); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e44 : item :=
  (IData (a "glibc_C_identification#str.44") (LRo (a "local")) 1 [(Item Wb 107); (Item Wb 101); (Item Wb 108); (Item Wb 100); (Item Wb 64); (Item Wb 100); (Item Wb 107); (Item Wb 117); (Item Wb 117); (Item Wb 103); (Item Wb 46); (Item Wb 100); (Item Wb 107); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e45 : item :=
  (IData (a "glibc_C_identification#str.45") (LRo (a "local")) 1 [(Item Wb 43); (Item Wb 52); (Item Wb 53); (Item Wb 32); (Item Wb 51); (Item Wb 49); (Item Wb 50); (Item Wb 50); (Item Wb 45); (Item Wb 54); (Item Wb 53); (Item Wb 52); (Item Wb 51); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e46 : item :=
  (IData (a "glibc_C_identification#str.46") (LRo (a "local")) 1 [(Item Wb 43); (Item Wb 52); (Item Wb 53); (Item Wb 32); (Item Wb 51); (Item Wb 51); (Item Wb 50); (Item Wb 53); (Item Wb 45); (Item Wb 54); (Item Wb 53); (Item Wb 52); (Item Wb 51); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e47 : item :=
  (IData (a "glibc_C_identification#str.47") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e48 : item :=
  (IData (a "glibc_C_identification#str.48") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 83); (Item Wb 79); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e49 : item :=
  (IData (a "glibc_C_identification#str.49") (LRo (a "local")) 1 [(Item Wb 49); (Item Wb 46); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e50 : item :=
  (IData (a "glibc_C_identification#str.50") (LRo (a "local")) 1 [(Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 55); (Item Wb 45); (Item Wb 49); (Item Wb 50); (Item Wb 45); (Item Wb 50); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_C_identification'23str'2e51 : item :=
  (IData (a "glibc_C_identification#str.51") (LRo (a "local")) 1 (app (app [(Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0)] [(Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57)]) (app [(Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57)] [(Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0)]))).

Definition hello_image_item__nl_C_LC_MEASUREMENT : item :=
  (IData (a "_nl_C_LC_MEASUREMENT") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 2); (Zero 4); (Sym (a "glibc_C_measurement#str.40") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition hello_image_item_glibc_C_measurement'23str'2e40 : item :=
  (IData (a "glibc_C_measurement#str.40") (LRo (a "local")) 1 [(Item Wb 1); (Item Wb 0)]).

Definition hello_image_item__nl_C_LC_MESSAGES : item :=
  (IData (a "_nl_C_LC_MESSAGES") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 5); (Zero 4); (Sym (a "glibc_C_messages#str.40") 0); (Sym (a "glibc_C_messages#str.41") 0); (Sym (a "glibc_C_messages#str.42") 0); (Sym (a "glibc_C_messages#str.42") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition hello_image_item_glibc_C_messages'23str'2e40 : item :=
  (IData (a "glibc_C_messages#str.40") (LRo (a "local")) 1 [(Item Wb 94); (Item Wb 91); (Item Wb 121); (Item Wb 89); (Item Wb 93); (Item Wb 0)]).

Definition hello_image_item_glibc_C_messages'23str'2e41 : item :=
  (IData (a "glibc_C_messages#str.41") (LRo (a "local")) 1 [(Item Wb 94); (Item Wb 91); (Item Wb 110); (Item Wb 78); (Item Wb 93); (Item Wb 0)]).

Definition hello_image_item_glibc_C_messages'23str'2e42 : item :=
  (IData (a "glibc_C_messages#str.42") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item__nl_C_LC_MONETARY : item :=
  (IData (a "_nl_C_LC_MONETARY") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 46); (Zero 4); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#str.41") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Item Ww 10101); (Zero 4); (Item Ww 99991231); (Zero 4); (Item Ww 10101); (Zero 4); (Item Ww 99991231); (Zero 4); (Sym (a "glibc_C_monetary#conversion_rate") 0); (Item Ww 0); (Zero 4); (Item Ww 0); (Zero 4); (Sym (a "_nl_C_codeset") 0)]).

Definition hello_image_item_glibc_C_monetary'23conversion_rate : item :=
  (IData (a "glibc_C_monetary#conversion_rate") (LRo (a "local")) 4 [(Str [1; 0; 0; 0; 1; 0; 0; 0])]).

Definition hello_image_item_glibc_C_monetary'23not_available : item :=
  (IData (a "glibc_C_monetary#not_available") (LRo (a "local")) 1 [(Str [255]); (Zero 1)]).

Definition hello_image_item_glibc_C_monetary'23str'2e40 : item :=
  (IData (a "glibc_C_monetary#str.40") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item_glibc_C_monetary'23str'2e41 : item :=
  (IData (a "glibc_C_monetary#str.41") (LRo (a "local")) 1 [(Item Wb 45); (Item Wb 0)]).

Definition hello_image_item__nl_C_LC_NAME : item :=
  (IData (a "_nl_C_LC_NAME") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 7); (Zero 4); (Sym (a "glibc_C_name#str.40") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition hello_image_item_glibc_C_name'23str'2e40 : item :=
  (IData (a "glibc_C_name#str.40") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 112); (Item Wb 37); (Item Wb 116); (Item Wb 37); (Item Wb 103); (Item Wb 37); (Item Wb 116); (Item Wb 37); (Item Wb 109); (Item Wb 37); (Item Wb 116); (Item Wb 37); (Item Wb 102); (Item Wb 0)]).

Definition hello_image_item_glibc_C_name'23str'2e41 : item :=
  (IData (a "glibc_C_name#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item__nl_C_LC_NUMERIC : item :=
  (IData (a "_nl_C_LC_NUMERIC") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 6); (Zero 4); (Sym (a "glibc_C_numeric#str.40") 0); (Sym (a "glibc_C_numeric#str.41") 0); (Sym (a "glibc_C_numeric#str.41") 0); (Item Ww 46); (Zero 4); (Item Ww 0); (Zero 4); (Sym (a "_nl_C_codeset") 0)]).

Definition hello_image_item_glibc_C_numeric'23str'2e40 : item :=
  (IData (a "glibc_C_numeric#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 0)]).

Definition hello_image_item_glibc_C_numeric'23str'2e41 : item :=
  (IData (a "glibc_C_numeric#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item__nl_C_LC_PAPER : item :=
  (IData (a "_nl_C_LC_PAPER") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 3); (Zero 4); (Item Ww 297); (Zero 4); (Item Ww 210); (Zero 4); (Sym (a "_nl_C_codeset") 0)]).

Definition hello_image_item__nl_C_LC_TELEPHONE : item :=
  (IData (a "_nl_C_LC_TELEPHONE") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 5); (Zero 4); (Sym (a "glibc_C_telephone#str.40") 0); (Sym (a "glibc_C_telephone#str.41") 0); (Sym (a "glibc_C_telephone#str.41") 0); (Sym (a "glibc_C_telephone#str.41") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition hello_image_item_glibc_C_telephone'23str'2e40 : item :=
  (IData (a "glibc_C_telephone#str.40") (LRo (a "local")) 1 [(Item Wb 43); (Item Wb 37); (Item Wb 99); (Item Wb 32); (Item Wb 37); (Item Wb 97); (Item Wb 32); (Item Wb 37); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_C_telephone'23str'2e41 : item :=
  (IData (a "glibc_C_telephone#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item__nl_C_LC_TIME : item :=
  (IData (a "_nl_C_LC_TIME") (LRo (a "export")) 8 (app (app [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 159); (Zero 4); (Sym (a "glibc_C_time#str.40") 0); (Sym (a "glibc_C_time#str.41") 0); (Sym (a "glibc_C_time#str.42") 0); (Sym (a "glibc_C_time#str.43") 0); (Sym (a "glibc_C_time#str.44") 0); (Sym (a "glibc_C_time#str.45") 0); (Sym (a "glibc_C_time#str.46") 0); (Sym (a "glibc_C_time#str.47") 0); (Sym (a "glibc_C_time#str.48") 0); (Sym (a "glibc_C_time#str.49") 0); (Sym (a "glibc_C_time#str.50") 0); (Sym (a "glibc_C_time#str.51") 0); (Sym (a "glibc_C_time#str.52") 0); (Sym (a "glibc_C_time#str.53") 0); (Sym (a "glibc_C_time#str.54") 0); (Sym (a "glibc_C_time#str.55") 0); (Sym (a "glibc_C_time#str.56") 0); (Sym (a "glibc_C_time#str.57") 0); (Sym (a "glibc_C_time#str.58") 0); (Sym (a "glibc_C_time#str.59") 0); (Sym (a "glibc_C_time#str.60") 0); (Sym (a "glibc_C_time#str.61") 0); (Sym (a "glibc_C_time#str.62") 0); (Sym (a "glibc_C_time#str.63") 0); (Sym (a "glibc_C_time#str.64") 0); (Sym (a "glibc_C_time#str.65") 0); (Sym (a "glibc_C_time#str.66") 0); (Sym (a "glibc_C_time#str.67") 0); (Sym (a "glibc_C_time#str.68") 0); (Sym (a "glibc_C_time#str.69") 0); (Sym (a "glibc_C_time#str.58") 0); (Sym (a "glibc_C_time#str.70") 0)] [(Sym (a "glibc_C_time#str.71") 0); (Sym (a "glibc_C_time#str.72") 0); (Sym (a "glibc_C_time#str.73") 0); (Sym (a "glibc_C_time#str.74") 0); (Sym (a "glibc_C_time#str.75") 0); (Sym (a "glibc_C_time#str.76") 0); (Sym (a "glibc_C_time#str.77") 0); (Sym (a "glibc_C_time#str.78") 0); (Sym (a "glibc_C_time#str.79") 0); (Sym (a "glibc_C_time#str.80") 0); (Sym (a "glibc_C_time#str.81") 0); (Sym (a "glibc_C_time#str.82") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Item Ww 0); (Zero 4); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.84") 0); (Sym (a "glibc_C_time#str.85") 0); (Sym (a "glibc_C_time#str.86") 0); (Sym (a "glibc_C_time#str.87") 0); (Sym (a "glibc_C_time#str.88") 0); (Sym (a "glibc_C_time#str.89") 0); (Sym (a "glibc_C_time#str.90") 0); (Sym (a "glibc_C_time#str.91") 0); (Sym (a "glibc_C_time#str.92") 0); (Sym (a "glibc_C_time#str.93") 0); (Sym (a "glibc_C_time#str.94") 0); (Sym (a "glibc_C_time#str.95") 0); (Sym (a "glibc_C_time#str.96") 0); (Sym (a "glibc_C_time#str.97") 0); (Sym (a "glibc_C_time#str.98") 0); (Sym (a "glibc_C_time#str.99") 0); (Sym (a "glibc_C_time#str.100") 0); (Sym (a "glibc_C_time#str.101") 0); (Sym (a "glibc_C_time#str.102") 0); (Sym (a "glibc_C_time#str.103") 0); (Sym (a "glibc_C_time#str.104") 0); (Sym (a "glibc_C_time#str.105") 0)]) (app [(Sym (a "glibc_C_time#str.106") 0); (Sym (a "glibc_C_time#str.107") 0); (Sym (a "glibc_C_time#str.108") 0); (Sym (a "glibc_C_time#str.109") 0); (Sym (a "glibc_C_time#str.110") 0); (Sym (a "glibc_C_time#str.111") 0); (Sym (a "glibc_C_time#str.112") 0); (Sym (a "glibc_C_time#str.113") 0); (Sym (a "glibc_C_time#str.102") 0); (Sym (a "glibc_C_time#str.114") 0); (Sym (a "glibc_C_time#str.115") 0); (Sym (a "glibc_C_time#str.116") 0); (Sym (a "glibc_C_time#str.117") 0); (Sym (a "glibc_C_time#str.118") 0); (Sym (a "glibc_C_time#str.119") 0); (Sym (a "glibc_C_time#str.120") 0); (Sym (a "glibc_C_time#str.121") 0); (Sym (a "glibc_C_time#str.122") 0); (Sym (a "glibc_C_time#str.123") 0); (Sym (a "glibc_C_time#str.124") 0); (Sym (a "glibc_C_time#str.125") 0); (Sym (a "glibc_C_time#str.126") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.128") 0); (Item Ww 19971130); (Zero 4); (Sym (a "glibc_C_time#str.129") 0); (Sym (a "glibc_C_time#str.130") 0); (Sym (a "glibc_C_time#str.131") 0); (Sym (a "glibc_C_time#str.130") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.132") 0); (Sym (a "glibc_C_time#str.133") 0); (Sym (a "_nl_C_codeset") 0); (Sym (a "glibc_C_time#str.66") 0); (Sym (a "glibc_C_time#str.67") 0); (Sym (a "glibc_C_time#str.68") 0); (Sym (a "glibc_C_time#str.69") 0); (Sym (a "glibc_C_time#str.58") 0)] [(Sym (a "glibc_C_time#str.70") 0); (Sym (a "glibc_C_time#str.71") 0); (Sym (a "glibc_C_time#str.72") 0); (Sym (a "glibc_C_time#str.73") 0); (Sym (a "glibc_C_time#str.74") 0); (Sym (a "glibc_C_time#str.75") 0); (Sym (a "glibc_C_time#str.76") 0); (Sym (a "glibc_C_time#str.110") 0); (Sym (a "glibc_C_time#str.111") 0); (Sym (a "glibc_C_time#str.112") 0); (Sym (a "glibc_C_time#str.113") 0); (Sym (a "glibc_C_time#str.102") 0); (Sym (a "glibc_C_time#str.114") 0); (Sym (a "glibc_C_time#str.115") 0); (Sym (a "glibc_C_time#str.116") 0); (Sym (a "glibc_C_time#str.117") 0); (Sym (a "glibc_C_time#str.118") 0); (Sym (a "glibc_C_time#str.119") 0); (Sym (a "glibc_C_time#str.120") 0); (Sym (a "glibc_C_time#str.54") 0); (Sym (a "glibc_C_time#str.55") 0); (Sym (a "glibc_C_time#str.56") 0); (Sym (a "glibc_C_time#str.57") 0); (Sym (a "glibc_C_time#str.58") 0); (Sym (a "glibc_C_time#str.59") 0); (Sym (a "glibc_C_time#str.60") 0); (Sym (a "glibc_C_time#str.61") 0); (Sym (a "glibc_C_time#str.62") 0); (Sym (a "glibc_C_time#str.63") 0); (Sym (a "glibc_C_time#str.64") 0); (Sym (a "glibc_C_time#str.65") 0); (Sym (a "glibc_C_time#str.98") 0); (Sym (a "glibc_C_time#str.99") 0); (Sym (a "glibc_C_time#str.100") 0); (Sym (a "glibc_C_time#str.101") 0); (Sym (a "glibc_C_time#str.102") 0); (Sym (a "glibc_C_time#str.103") 0); (Sym (a "glibc_C_time#str.104") 0); (Sym (a "glibc_C_time#str.105") 0); (Sym (a "glibc_C_time#str.106") 0); (Sym (a "glibc_C_time#str.107") 0); (Sym (a "glibc_C_time#str.108") 0); (Sym (a "glibc_C_time#str.109") 0)]))).

Definition hello_image_item_glibc_C_time'23str'2e100 : item :=
  (IData (a "glibc_C_time#str.100") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 97); (Item Ww 114); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e101 : item :=
  (IData (a "glibc_C_time#str.101") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 112); (Item Ww 114); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e102 : item :=
  (IData (a "glibc_C_time#str.102") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e103 : item :=
  (IData (a "glibc_C_time#str.103") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 117); (Item Ww 110); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e104 : item :=
  (IData (a "glibc_C_time#str.104") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 117); (Item Ww 108); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e105 : item :=
  (IData (a "glibc_C_time#str.105") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 117); (Item Ww 103); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e106 : item :=
  (IData (a "glibc_C_time#str.106") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 101); (Item Ww 112); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e107 : item :=
  (IData (a "glibc_C_time#str.107") (LRo (a "local")) 4 [(Item Ww 79); (Item Ww 99); (Item Ww 116); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e108 : item :=
  (IData (a "glibc_C_time#str.108") (LRo (a "local")) 4 [(Item Ww 78); (Item Ww 111); (Item Ww 118); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e109 : item :=
  (IData (a "glibc_C_time#str.109") (LRo (a "local")) 4 [(Item Ww 68); (Item Ww 101); (Item Ww 99); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e110 : item :=
  (IData (a "glibc_C_time#str.110") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 97); (Item Ww 110); (Item Ww 117); (Item Ww 97); (Item Ww 114); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e111 : item :=
  (IData (a "glibc_C_time#str.111") (LRo (a "local")) 4 [(Item Ww 70); (Item Ww 101); (Item Ww 98); (Item Ww 114); (Item Ww 117); (Item Ww 97); (Item Ww 114); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e112 : item :=
  (IData (a "glibc_C_time#str.112") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 97); (Item Ww 114); (Item Ww 99); (Item Ww 104); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e113 : item :=
  (IData (a "glibc_C_time#str.113") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 112); (Item Ww 114); (Item Ww 105); (Item Ww 108); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e114 : item :=
  (IData (a "glibc_C_time#str.114") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 117); (Item Ww 110); (Item Ww 101); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e115 : item :=
  (IData (a "glibc_C_time#str.115") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 117); (Item Ww 108); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e116 : item :=
  (IData (a "glibc_C_time#str.116") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 117); (Item Ww 103); (Item Ww 117); (Item Ww 115); (Item Ww 116); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e117 : item :=
  (IData (a "glibc_C_time#str.117") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 101); (Item Ww 112); (Item Ww 116); (Item Ww 101); (Item Ww 109); (Item Ww 98); (Item Ww 101); (Item Ww 114); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e118 : item :=
  (IData (a "glibc_C_time#str.118") (LRo (a "local")) 4 [(Item Ww 79); (Item Ww 99); (Item Ww 116); (Item Ww 111); (Item Ww 98); (Item Ww 101); (Item Ww 114); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e119 : item :=
  (IData (a "glibc_C_time#str.119") (LRo (a "local")) 4 [(Item Ww 78); (Item Ww 111); (Item Ww 118); (Item Ww 101); (Item Ww 109); (Item Ww 98); (Item Ww 101); (Item Ww 114); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e120 : item :=
  (IData (a "glibc_C_time#str.120") (LRo (a "local")) 4 [(Item Ww 68); (Item Ww 101); (Item Ww 99); (Item Ww 101); (Item Ww 109); (Item Ww 98); (Item Ww 101); (Item Ww 114); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e121 : item :=
  (IData (a "glibc_C_time#str.121") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 77); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e122 : item :=
  (IData (a "glibc_C_time#str.122") (LRo (a "local")) 4 [(Item Ww 80); (Item Ww 77); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e123 : item :=
  (IData (a "glibc_C_time#str.123") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 97); (Item Ww 32); (Item Ww 37); (Item Ww 98); (Item Ww 32); (Item Ww 37); (Item Ww 101); (Item Ww 32); (Item Ww 37); (Item Ww 72); (Item Ww 58); (Item Ww 37); (Item Ww 77); (Item Ww 58); (Item Ww 37); (Item Ww 83); (Item Ww 32); (Item Ww 37); (Item Ww 89); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e124 : item :=
  (IData (a "glibc_C_time#str.124") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 109); (Item Ww 47); (Item Ww 37); (Item Ww 100); (Item Ww 47); (Item Ww 37); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e125 : item :=
  (IData (a "glibc_C_time#str.125") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 72); (Item Ww 58); (Item Ww 37); (Item Ww 77); (Item Ww 58); (Item Ww 37); (Item Ww 83); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e126 : item :=
  (IData (a "glibc_C_time#str.126") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 73); (Item Ww 58); (Item Ww 37); (Item Ww 77); (Item Ww 58); (Item Ww 37); (Item Ww 83); (Item Ww 32); (Item Ww 37); (Item Ww 112); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e127 : item :=
  (IData (a "glibc_C_time#str.127") (LRo (a "local")) 4 [(Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e128 : item :=
  (IData (a "glibc_C_time#str.128") (LRo (a "local")) 1 [(Item Wb 7); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e129 : item :=
  (IData (a "glibc_C_time#str.129") (LRo (a "local")) 1 [(Item Wb 4); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e130 : item :=
  (IData (a "glibc_C_time#str.130") (LRo (a "local")) 1 [(Item Wb 1); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e131 : item :=
  (IData (a "glibc_C_time#str.131") (LRo (a "local")) 1 [(Item Wb 2); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e132 : item :=
  (IData (a "glibc_C_time#str.132") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 97); (Item Wb 32); (Item Wb 37); (Item Wb 98); (Item Wb 32); (Item Wb 37); (Item Wb 101); (Item Wb 32); (Item Wb 37); (Item Wb 72); (Item Wb 58); (Item Wb 37); (Item Wb 77); (Item Wb 58); (Item Wb 37); (Item Wb 83); (Item Wb 32); (Item Wb 37); (Item Wb 90); (Item Wb 32); (Item Wb 37); (Item Wb 89); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e133 : item :=
  (IData (a "glibc_C_time#str.133") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 97); (Item Ww 32); (Item Ww 37); (Item Ww 98); (Item Ww 32); (Item Ww 37); (Item Ww 101); (Item Ww 32); (Item Ww 37); (Item Ww 72); (Item Ww 58); (Item Ww 37); (Item Ww 77); (Item Ww 58); (Item Ww 37); (Item Ww 83); (Item Ww 32); (Item Ww 37); (Item Ww 90); (Item Ww 32); (Item Ww 37); (Item Ww 89); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e40 : item :=
  (IData (a "glibc_C_time#str.40") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 117); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e41 : item :=
  (IData (a "glibc_C_time#str.41") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 111); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e42 : item :=
  (IData (a "glibc_C_time#str.42") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 117); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e43 : item :=
  (IData (a "glibc_C_time#str.43") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e44 : item :=
  (IData (a "glibc_C_time#str.44") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 104); (Item Wb 117); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e45 : item :=
  (IData (a "glibc_C_time#str.45") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 114); (Item Wb 105); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e46 : item :=
  (IData (a "glibc_C_time#str.46") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 97); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e47 : item :=
  (IData (a "glibc_C_time#str.47") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 117); (Item Wb 110); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e48 : item :=
  (IData (a "glibc_C_time#str.48") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 111); (Item Wb 110); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e49 : item :=
  (IData (a "glibc_C_time#str.49") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 117); (Item Wb 101); (Item Wb 115); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e50 : item :=
  (IData (a "glibc_C_time#str.50") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 101); (Item Wb 100); (Item Wb 110); (Item Wb 101); (Item Wb 115); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e51 : item :=
  (IData (a "glibc_C_time#str.51") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 104); (Item Wb 117); (Item Wb 114); (Item Wb 115); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e52 : item :=
  (IData (a "glibc_C_time#str.52") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 114); (Item Wb 105); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e53 : item :=
  (IData (a "glibc_C_time#str.53") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 114); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e54 : item :=
  (IData (a "glibc_C_time#str.54") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 97); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e55 : item :=
  (IData (a "glibc_C_time#str.55") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 101); (Item Wb 98); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e56 : item :=
  (IData (a "glibc_C_time#str.56") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 97); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e57 : item :=
  (IData (a "glibc_C_time#str.57") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 112); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e58 : item :=
  (IData (a "glibc_C_time#str.58") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e59 : item :=
  (IData (a "glibc_C_time#str.59") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 117); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e60 : item :=
  (IData (a "glibc_C_time#str.60") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 117); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e61 : item :=
  (IData (a "glibc_C_time#str.61") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 117); (Item Wb 103); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e62 : item :=
  (IData (a "glibc_C_time#str.62") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 101); (Item Wb 112); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e63 : item :=
  (IData (a "glibc_C_time#str.63") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 99); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e64 : item :=
  (IData (a "glibc_C_time#str.64") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 118); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e65 : item :=
  (IData (a "glibc_C_time#str.65") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 101); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e66 : item :=
  (IData (a "glibc_C_time#str.66") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 97); (Item Wb 110); (Item Wb 117); (Item Wb 97); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e67 : item :=
  (IData (a "glibc_C_time#str.67") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 101); (Item Wb 98); (Item Wb 114); (Item Wb 117); (Item Wb 97); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e68 : item :=
  (IData (a "glibc_C_time#str.68") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 97); (Item Wb 114); (Item Wb 99); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e69 : item :=
  (IData (a "glibc_C_time#str.69") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e70 : item :=
  (IData (a "glibc_C_time#str.70") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 117); (Item Wb 110); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e71 : item :=
  (IData (a "glibc_C_time#str.71") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 117); (Item Wb 108); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e72 : item :=
  (IData (a "glibc_C_time#str.72") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 117); (Item Wb 103); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e73 : item :=
  (IData (a "glibc_C_time#str.73") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 101); (Item Wb 112); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e74 : item :=
  (IData (a "glibc_C_time#str.74") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 99); (Item Wb 116); (Item Wb 111); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e75 : item :=
  (IData (a "glibc_C_time#str.75") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 118); (Item Wb 101); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e76 : item :=
  (IData (a "glibc_C_time#str.76") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 101); (Item Wb 99); (Item Wb 101); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e77 : item :=
  (IData (a "glibc_C_time#str.77") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 77); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e78 : item :=
  (IData (a "glibc_C_time#str.78") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 77); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e79 : item :=
  (IData (a "glibc_C_time#str.79") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 97); (Item Wb 32); (Item Wb 37); (Item Wb 98); (Item Wb 32); (Item Wb 37); (Item Wb 101); (Item Wb 32); (Item Wb 37); (Item Wb 72); (Item Wb 58); (Item Wb 37); (Item Wb 77); (Item Wb 58); (Item Wb 37); (Item Wb 83); (Item Wb 32); (Item Wb 37); (Item Wb 89); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e80 : item :=
  (IData (a "glibc_C_time#str.80") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 109); (Item Wb 47); (Item Wb 37); (Item Wb 100); (Item Wb 47); (Item Wb 37); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e81 : item :=
  (IData (a "glibc_C_time#str.81") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 72); (Item Wb 58); (Item Wb 37); (Item Wb 77); (Item Wb 58); (Item Wb 37); (Item Wb 83); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e82 : item :=
  (IData (a "glibc_C_time#str.82") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 73); (Item Wb 58); (Item Wb 37); (Item Wb 77); (Item Wb 58); (Item Wb 37); (Item Wb 83); (Item Wb 32); (Item Wb 37); (Item Wb 112); (Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e83 : item :=
  (IData (a "glibc_C_time#str.83") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item_glibc_C_time'23str'2e84 : item :=
  (IData (a "glibc_C_time#str.84") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 117); (Item Ww 110); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e85 : item :=
  (IData (a "glibc_C_time#str.85") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 111); (Item Ww 110); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e86 : item :=
  (IData (a "glibc_C_time#str.86") (LRo (a "local")) 4 [(Item Ww 84); (Item Ww 117); (Item Ww 101); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e87 : item :=
  (IData (a "glibc_C_time#str.87") (LRo (a "local")) 4 [(Item Ww 87); (Item Ww 101); (Item Ww 100); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e88 : item :=
  (IData (a "glibc_C_time#str.88") (LRo (a "local")) 4 [(Item Ww 84); (Item Ww 104); (Item Ww 117); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e89 : item :=
  (IData (a "glibc_C_time#str.89") (LRo (a "local")) 4 [(Item Ww 70); (Item Ww 114); (Item Ww 105); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e90 : item :=
  (IData (a "glibc_C_time#str.90") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 97); (Item Ww 116); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e91 : item :=
  (IData (a "glibc_C_time#str.91") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 117); (Item Ww 110); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e92 : item :=
  (IData (a "glibc_C_time#str.92") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 111); (Item Ww 110); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e93 : item :=
  (IData (a "glibc_C_time#str.93") (LRo (a "local")) 4 [(Item Ww 84); (Item Ww 117); (Item Ww 101); (Item Ww 115); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e94 : item :=
  (IData (a "glibc_C_time#str.94") (LRo (a "local")) 4 [(Item Ww 87); (Item Ww 101); (Item Ww 100); (Item Ww 110); (Item Ww 101); (Item Ww 115); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e95 : item :=
  (IData (a "glibc_C_time#str.95") (LRo (a "local")) 4 [(Item Ww 84); (Item Ww 104); (Item Ww 117); (Item Ww 114); (Item Ww 115); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e96 : item :=
  (IData (a "glibc_C_time#str.96") (LRo (a "local")) 4 [(Item Ww 70); (Item Ww 114); (Item Ww 105); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e97 : item :=
  (IData (a "glibc_C_time#str.97") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 97); (Item Ww 116); (Item Ww 117); (Item Ww 114); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e98 : item :=
  (IData (a "glibc_C_time#str.98") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 97); (Item Ww 110); (Item Ww 0)]).

Definition hello_image_item_glibc_C_time'23str'2e99 : item :=
  (IData (a "glibc_C_time#str.99") (LRo (a "local")) 4 [(Item Ww 70); (Item Ww 101); (Item Ww 98); (Item Ww 0)]).

Definition hello_image_item__nl_C_codeset : item :=
  (IData (a "_nl_C_codeset") (LRo (a "export")) 1 ["ANSI_X3.4-1968"%irbytes; (Zero 1)]).

Definition hello_image_item__nl_C_name : item :=
  (IData (a "_nl_C_name") (LRo (a "export")) 1 ["C"%irbytes; (Zero 1)]).

Definition hello_image_item__nl_POSIX_name : item :=
  (IData (a "_nl_POSIX_name") (LRo (a "export")) 1 ["POSIX"%irbytes; (Zero 1)]).

Definition hello_image_item___GI__libc_intl_domainname : item :=
  (IData (a "__GI__libc_intl_domainname") (LRo (a "export")) 1 ["libc"%irbytes; (Zero 1)]).

Definition hello_image_item__nl_default_locale_path : item :=
  (IData (a "_nl_default_locale_path") (LRo (a "export")) 1 ["/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44/lib/locale"%irbytes; (Zero 1)]).

Definition hello_image_item_glibc_findlocale'23_nl_find_locale'2ecodeset_idx'2e245 : item :=
  (IData (a "glibc_findlocale#_nl_find_locale.codeset_idx.245") (LRo (a "local")) 4 [(Item Ww 14); (Item Ww 5); (Item Ww 110); (Item Ww 18); (Item Ww 45); (Item Ww 4); (Zero 4); (Item Ww 2); (Item Ww 6); (Item Ww 12); (Item Ww 4); (Item Ww 1); (Item Ww 15)]).

Definition hello_image_item__nl_locale_file_list : item :=
  (IData (a "_nl_locale_file_list") LExport 8 [(Zero 104)]).

Definition hello_image_item_glibc_findlocale'23valid_locale_name'2eslashdot'2e250 : item :=
  (IData (a "glibc_findlocale#valid_locale_name.slashdot.250") (LRo (a "local")) 1 ["/../"%irbytes]).

Definition hello_image_item_glibc_findlocale'23str'2e243 : item :=
  (IData (a "glibc_findlocale#str.243") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 67); (Item Wb 95); (Item Wb 65); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_findlocale'23str'2e244 : item :=
  (IData (a "glibc_findlocale#str.244") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 65); (Item Wb 78); (Item Wb 71); (Item Wb 0)]).

Definition hello_image_item_glibc_findlocale'23str'2e246 : item :=
  (IData (a "glibc_findlocale#str.246") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 99); (Item Wb 111); (Item Wb 100); (Item Wb 101); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_findlocale'23str'2e247 : item :=
  (IData (a "glibc_findlocale#str.247") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_findlocale'23str'2e248 : item :=
  (IData (a "glibc_findlocale#str.248") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 110); (Item Wb 108); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 110); (Item Wb 100); (Item Wb 95); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_findlocale'23str'2e249 : item :=
  (IData (a "glibc_findlocale#str.249") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 83); (Item Wb 76); (Item Wb 73); (Item Wb 84); (Item Wb 0)]).

Definition hello_image_item___libc_tsd_LOCALE : item :=
  (IData (a "__libc_tsd_LOCALE") (LTls (a "export")) 8 [(Sym (a "_nl_global_locale") 0)]).

Definition hello_image_item__nl_global_locale : item :=
  (IData (a "_nl_global_locale") LExport 8 [(Sym (a "_nl_C_LC_CTYPE") 0); (Sym (a "_nl_C_LC_NUMERIC") 0); (Sym (a "_nl_C_LC_TIME") 0); (Sym (a "_nl_C_LC_COLLATE") 0); (Sym (a "_nl_C_LC_MONETARY") 0); (Sym (a "_nl_C_LC_MESSAGES") 0); (Zero 8); (Sym (a "_nl_C_LC_PAPER") 0); (Sym (a "_nl_C_LC_NAME") 0); (Sym (a "_nl_C_LC_ADDRESS") 0); (Sym (a "_nl_C_LC_TELEPHONE") 0); (Sym (a "_nl_C_LC_MEASUREMENT") 0); (Sym (a "_nl_C_LC_IDENTIFICATION") 0); (Sym (a "_nl_C_LC_CTYPE_class") 256); (Sym (a "_nl_C_LC_CTYPE_tolower") 512); (Sym (a "_nl_C_LC_CTYPE_toupper") 512); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0)]).

Definition hello_image_item_glibc_loadarchive'23archfname : item :=
  (IData (a "glibc_loadarchive#archfname") (LRo (a "local")) 1 ["/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44/lib/locale/locale-archive"%irbytes; (Zero 1)]).

Definition hello_image_item_glibc_loadarchive'23archive_stat : item :=
  (IData (a "glibc_loadarchive#archive_stat") LLocal 8 [(Zero 144)]).

Definition hello_image_item_glibc_loadarchive'23archloaded : item :=
  (IData (a "glibc_loadarchive#archloaded") LLocal 8 [(Zero 8)]).

Definition hello_image_item_glibc_loadarchive'23archmapped : item :=
  (IData (a "glibc_loadarchive#archmapped") LLocal 8 [(Zero 8)]).

Definition hello_image_item_glibc_loadarchive'23headmap : item :=
  (IData (a "glibc_loadarchive#headmap") LLocal 8 [(Zero 24)]).

Definition hello_image_item_glibc_loadarchive'23str'2e249 : item :=
  (IData (a "glibc_loadarchive#str.249") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 79); (Item Wb 67); (Item Wb 65); (Item Wb 76); (Item Wb 69); (Item Wb 95); (Item Wb 65); (Item Wb 82); (Item Wb 67); (Item Wb 72); (Item Wb 73); (Item Wb 86); (Item Wb 69); (Item Wb 95); (Item Wb 50); (Item Wb 95); (Item Wb 50); (Item Wb 55); (Item Wb 0)]).

Definition hello_image_item_glibc_loadarchive'23str'2e250 : item :=
  (IData (a "glibc_loadarchive#str.250") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 79); (Item Wb 67); (Item Wb 65); (Item Wb 76); (Item Wb 69); (Item Wb 95); (Item Wb 65); (Item Wb 82); (Item Wb 67); (Item Wb 72); (Item Wb 73); (Item Wb 86); (Item Wb 69); (Item Wb 0)]).

Definition hello_image_item_glibc_loadarchive'23str'2e251 : item :=
  (IData (a "glibc_loadarchive#str.251") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 114); (Item Wb 117); (Item Wb 110); (Item Wb 47); (Item Wb 99); (Item Wb 117); (Item Wb 114); (Item Wb 114); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 45); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 47); (Item Wb 115); (Item Wb 119); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 47); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 47); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 97); (Item Wb 114); (Item Wb 99); (Item Wb 104); (Item Wb 105); (Item Wb 118); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_loadarchive'23str'2e252 : item :=
  (IData (a "glibc_loadarchive#str.252") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 117); (Item Wb 115); (Item Wb 114); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 47); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 47); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 97); (Item Wb 114); (Item Wb 99); (Item Wb 104); (Item Wb 105); (Item Wb 118); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_loadarchive'23str'2e254 : item :=
  (IData (a "glibc_loadarchive#str.254") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 109); (Item Wb 97); (Item Wb 112); (Item Wb 46); (Item Wb 108); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 99); (Item Wb 104); (Item Wb 105); (Item Wb 118); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 46); (Item Wb 115); (Item Wb 116); (Item Wb 95); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_loadarchive'23str'2e255 : item :=
  (IData (a "glibc_loadarchive#str.255") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 111); (Item Wb 97); (Item Wb 100); (Item Wb 97); (Item Wb 114); (Item Wb 99); (Item Wb 104); (Item Wb 105); (Item Wb 118); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_loadarchive'23str'2e256 : item :=
  (IData (a "glibc_loadarchive#str.256") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 110); (Item Wb 108); (Item Wb 95); (Item Wb 108); (Item Wb 111); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 102); (Item Wb 114); (Item Wb 111); (Item Wb 109); (Item Wb 95); (Item Wb 97); (Item Wb 114); (Item Wb 99); (Item Wb 104); (Item Wb 105); (Item Wb 118); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_loadlocale'23_nl_category_num_items : item :=
  (IData (a "glibc_loadlocale#_nl_category_num_items") (LRo (a "local")) 8 [(Item Wl 86); (Item Wl 6); (Item Wl 159); (Item Wl 19); (Item Wl 46); (Item Wl 5); (Zero 8); (Item Wl 3); (Item Wl 7); (Item Wl 13); (Item Wl 5); (Item Wl 2); (Item Wl 16)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_ADDRESS : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_ADDRESS") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 5); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_COLLATE : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_COLLATE") (LRo (a "local")) 4 [(Item Ww 5); (Item Ww 1); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Zero 12); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 5); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_CTYPE : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_CTYPE") (LRo (a "local")) 4 (app [(Item Ww 8); (Item Ww 8); (Zero 4); (Item Ww 8); (Zero 4); (Item Ww 8); (Zero 16); (Item Ww 6); (Item Ww 6); (Item Ww 4); (Item Ww 5); (Item Ww 1); (Item Ww 8); (Item Ww 8); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 5); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8)] [(Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 5); (Item Ww 8); (Item Ww 5); (Item Ww 1); (Item Ww 5); (Item Ww 5); (Zero 56)])).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_IDENTIFICATION : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_IDENTIFICATION") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 2); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_MEASUREMENT : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_MEASUREMENT") (LRo (a "local")) 4 [(Item Ww 3); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_MESSAGES : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_MESSAGES") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_MONETARY : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_MONETARY") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 4); (Item Ww 1); (Item Ww 1); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 1); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 1); (Item Ww 1); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 7); (Item Ww 5); (Item Ww 5); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_NAME : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_NAME") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_NUMERIC : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_NUMERIC") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 4); (Item Ww 5); (Item Ww 5); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_PAPER : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_PAPER") (LRo (a "local")) 4 [(Item Ww 5); (Item Ww 5); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_TELEPHONE : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_TELEPHONE") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_type_LC_TIME : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_TIME") (LRo (a "local")) 4 [(Item Ww 2); (Zero 24); (Item Ww 2); (Zero 24); (Item Ww 2); (Zero 44); (Item Ww 2); (Zero 44); (Item Ww 2); (Zero 4); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 6); (Item Ww 1); (Item Ww 1); (Item Ww 6); (Item Ww 1); (Item Ww 1); (Item Ww 5); (Item Ww 1); (Item Ww 9); (Zero 24); (Item Ww 9); (Zero 24); (Item Ww 9); (Zero 44); (Item Ww 9); (Zero 44); (Item Ww 9); (Zero 4); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 10); (Item Ww 8); (Item Ww 8); (Item Ww 3); (Item Ww 5); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 1); (Item Ww 1); (Item Ww 8); (Item Ww 1); (Item Ww 2); (Zero 44); (Item Ww 9); (Zero 44); (Item Ww 2); (Zero 44); (Item Ww 9); (Zero 44)]).

Definition hello_image_item_glibc_loadlocale'23_nl_value_types : item :=
  (IData (a "glibc_loadlocale#_nl_value_types") (LRo (a "local")) 8 [(Sym (a "glibc_loadlocale#_nl_value_type_LC_CTYPE") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_NUMERIC") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_TIME") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_COLLATE") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_MONETARY") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_MESSAGES") 0); (Zero 8); (Sym (a "glibc_loadlocale#_nl_value_type_LC_PAPER") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_NAME") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_ADDRESS") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_TELEPHONE") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_MEASUREMENT") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_IDENTIFICATION") 0)]).

Definition hello_image_item_glibc_loadlocale'23str'2e240 : item :=
  (IData (a "glibc_loadlocale#str.240") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 103); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 67); (Item Wb 95); (Item Wb 67); (Item Wb 84); (Item Wb 89); (Item Wb 80); (Item Wb 69); (Item Wb 0)]).

Definition hello_image_item_glibc_loadlocale'23str'2e241 : item :=
  (IData (a "glibc_loadlocale#str.241") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 111); (Item Wb 97); (Item Wb 100); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_loadlocale'23str'2e242 : item :=
  (IData (a "glibc_loadlocale#str.242") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 110); (Item Wb 108); (Item Wb 95); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 95); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 0)]).

Definition hello_image_item_glibc_loadlocale'23str'2e243 : item :=
  (IData (a "glibc_loadlocale#str.243") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 83); (Item Wb 89); (Item Wb 83); (Item Wb 95); (Item Wb 0)]).

Definition hello_image_item___libc_setlocale_lock : item :=
  (IData (a "__libc_setlocale_lock") LExport 8 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4)]).

Definition hello_image_item__nl_category_name_idxs : item :=
  (IData (a "_nl_category_name_idxs") (LRo (a "export")) 1 [(Item Wb 11); (Item Wb 32); (Item Wb 43); (Item Wb 0); (Item Wb 20); (Item Wb 51); (Zero 1); (Item Wb 63); (Item Wb 72); (Item Wb 80); (Item Wb 91); (Item Wb 104); (Item Wb 119)]).

Definition hello_image_item__nl_category_name_sizes : item :=
  (IData (a "_nl_category_name_sizes") (LRo (a "export")) 1 [(Item Wb 8); (Item Wb 10); (Item Wb 7); (Item Wb 10); (Item Wb 11); (Item Wb 11); (Item Wb 6); (Item Wb 8); (Item Wb 7); (Item Wb 10); (Item Wb 12); (Item Wb 14); (Item Wb 17)]).

Definition hello_image_item__nl_category_names : item :=
  (IData (a "_nl_category_names") (LRo (a "export")) 1 ["LC_COLLATE"%irbytes; (Zero 1); "LC_CTYPE"%irbytes; (Zero 1); "LC_MONETARY"%irbytes; (Zero 1); "LC_NUMERIC"%irbytes; (Zero 1); "LC_TIME"%irbytes; (Zero 1); "LC_MESSAGES"%irbytes; (Zero 1); "LC_PAPER"%irbytes; (Zero 1); "LC_NAME"%irbytes; (Zero 1); "LC_ADDRESS"%irbytes; (Zero 1); "LC_TELEPHONE"%irbytes; (Zero 1); "LC_MEASUREMENT"%irbytes; (Zero 1); "LC_IDENTIFICATION"%irbytes; (Zero 1)]).
