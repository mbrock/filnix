(** This file defines checked IR from glibc’s `locale/C-identification.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__nl_C_LC_IDENTIFICATION : item :=
  (IData (a "_nl_C_LC_IDENTIFICATION") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 16); (Zero 4); (Sym (a "glibc_C_identification#str.40") 0); (Sym (a "glibc_C_identification#str.41") 0); (Sym (a "glibc_C_identification#str.42") 0); (Sym (a "glibc_C_identification#str.43") 0); (Sym (a "glibc_C_identification#str.44") 0); (Sym (a "glibc_C_identification#str.45") 0); (Sym (a "glibc_C_identification#str.46") 0); (Sym (a "glibc_C_identification#str.47") 0); (Sym (a "glibc_C_identification#str.48") 0); (Sym (a "glibc_C_identification#str.47") 0); (Sym (a "glibc_C_identification#str.47") 0); (Sym (a "glibc_C_identification#str.47") 0); (Sym (a "glibc_C_identification#str.49") 0); (Sym (a "glibc_C_identification#str.50") 0); (Sym (a "glibc_C_identification#str.51") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_identification'23str'2e40 : item :=
  (IData (a "glibc_C_identification#str.40") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 83); (Item Wb 79); (Item Wb 47); (Item Wb 73); (Item Wb 69); (Item Wb 67); (Item Wb 32); (Item Wb 49); (Item Wb 52); (Item Wb 54); (Item Wb 53); (Item Wb 50); (Item Wb 32); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 32); (Item Wb 70); (Item Wb 68); (Item Wb 67); (Item Wb 67); (Item Wb 45); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e41 : item :=
  (IData (a "glibc_C_identification#str.41") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 83); (Item Wb 79); (Item Wb 47); (Item Wb 73); (Item Wb 69); (Item Wb 67); (Item Wb 32); (Item Wb 74); (Item Wb 84); (Item Wb 67); (Item Wb 49); (Item Wb 47); (Item Wb 83); (Item Wb 67); (Item Wb 50); (Item Wb 50); (Item Wb 47); (Item Wb 87); (Item Wb 71); (Item Wb 50); (Item Wb 48); (Item Wb 32); (Item Wb 45); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 122); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e42 : item :=
  (IData (a "glibc_C_identification#str.42") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 47); (Item Wb 111); (Item Wb 32); (Item Wb 75); (Item Wb 101); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 83); (Item Wb 105); (Item Wb 109); (Item Wb 111); (Item Wb 110); (Item Wb 115); (Item Wb 101); (Item Wb 110); (Item Wb 44); (Item Wb 32); (Item Wb 83); (Item Wb 107); (Item Wb 116); (Item Wb 46); (Item Wb 32); (Item Wb 74); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 101); (Item Wb 110); (Item Wb 115); (Item Wb 32); (Item Wb 65); (Item Wb 108); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 56); (Item Wb 44); (Item Wb 32); (Item Wb 68); (Item Wb 75); (Item Wb 45); (Item Wb 49); (Item Wb 54); (Item Wb 49); (Item Wb 53); (Item Wb 32); (Item Wb 75); (Item Wb 111); (Item Wb 98); (Item Wb 101); (Item Wb 110); (Item Wb 104); (Item Wb 97); (Item Wb 118); (Item Wb 110); (Item Wb 32); (Item Wb 86); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e43 : item :=
  (IData (a "glibc_C_identification#str.43") (LRo (a "local")) 1 [(Item Wb 75); (Item Wb 101); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 83); (Item Wb 105); (Item Wb 109); (Item Wb 111); (Item Wb 110); (Item Wb 115); (Item Wb 101); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e44 : item :=
  (IData (a "glibc_C_identification#str.44") (LRo (a "local")) 1 [(Item Wb 107); (Item Wb 101); (Item Wb 108); (Item Wb 100); (Item Wb 64); (Item Wb 100); (Item Wb 107); (Item Wb 117); (Item Wb 117); (Item Wb 103); (Item Wb 46); (Item Wb 100); (Item Wb 107); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e45 : item :=
  (IData (a "glibc_C_identification#str.45") (LRo (a "local")) 1 [(Item Wb 43); (Item Wb 52); (Item Wb 53); (Item Wb 32); (Item Wb 51); (Item Wb 49); (Item Wb 50); (Item Wb 50); (Item Wb 45); (Item Wb 54); (Item Wb 53); (Item Wb 52); (Item Wb 51); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e46 : item :=
  (IData (a "glibc_C_identification#str.46") (LRo (a "local")) 1 [(Item Wb 43); (Item Wb 52); (Item Wb 53); (Item Wb 32); (Item Wb 51); (Item Wb 51); (Item Wb 50); (Item Wb 53); (Item Wb 45); (Item Wb 54); (Item Wb 53); (Item Wb 52); (Item Wb 51); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e47 : item :=
  (IData (a "glibc_C_identification#str.47") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e48 : item :=
  (IData (a "glibc_C_identification#str.48") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 83); (Item Wb 79); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e49 : item :=
  (IData (a "glibc_C_identification#str.49") (LRo (a "local")) 1 [(Item Wb 49); (Item Wb 46); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e50 : item :=
  (IData (a "glibc_C_identification#str.50") (LRo (a "local")) 1 [(Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 55); (Item Wb 45); (Item Wb 49); (Item Wb 50); (Item Wb 45); (Item Wb 50); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_C_identification'23str'2e51 : item :=
  (IData (a "glibc_C_identification#str.51") (LRo (a "local")) 1 (app (app [(Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0)] [(Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57)]) (app [(Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57)] [(Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0); (Item Wb 105); (Item Wb 49); (Item Wb 56); (Item Wb 110); (Item Wb 58); (Item Wb 49); (Item Wb 57); (Item Wb 57); (Item Wb 57); (Item Wb 0)]))).
