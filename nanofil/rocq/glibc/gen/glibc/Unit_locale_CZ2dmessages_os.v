(** This file defines checked IR from glibc’s `locale/C-messages.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__nl_C_LC_MESSAGES : item :=
  (IData (a "_nl_C_LC_MESSAGES") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 5); (Zero 4); (Sym (a "glibc_C_messages#str.40") 0); (Sym (a "glibc_C_messages#str.41") 0); (Sym (a "glibc_C_messages#str.42") 0); (Sym (a "glibc_C_messages#str.42") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_messages'23str'2e40 : item :=
  (IData (a "glibc_C_messages#str.40") (LRo (a "local")) 1 [(Item Wb 94); (Item Wb 91); (Item Wb 121); (Item Wb 89); (Item Wb 93); (Item Wb 0)]).

Definition item_glibc_C_messages'23str'2e41 : item :=
  (IData (a "glibc_C_messages#str.41") (LRo (a "local")) 1 [(Item Wb 94); (Item Wb 91); (Item Wb 110); (Item Wb 78); (Item Wb 93); (Item Wb 0)]).

Definition item_glibc_C_messages'23str'2e42 : item :=
  (IData (a "glibc_C_messages#str.42") (LRo (a "local")) 1 [(Item Wb 0)]).
