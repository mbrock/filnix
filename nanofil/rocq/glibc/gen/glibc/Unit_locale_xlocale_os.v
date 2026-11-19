(** This file defines checked IR from glibc’s `locale/xlocale.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__nl_C_locobj : item :=
  (IData (a "_nl_C_locobj") (LRo (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE") 0); (Sym (a "_nl_C_LC_NUMERIC") 0); (Sym (a "_nl_C_LC_TIME") 0); (Sym (a "_nl_C_LC_COLLATE") 0); (Sym (a "_nl_C_LC_MONETARY") 0); (Sym (a "_nl_C_LC_MESSAGES") 0); (Zero 8); (Sym (a "_nl_C_LC_PAPER") 0); (Sym (a "_nl_C_LC_NAME") 0); (Sym (a "_nl_C_LC_ADDRESS") 0); (Sym (a "_nl_C_LC_TELEPHONE") 0); (Sym (a "_nl_C_LC_MEASUREMENT") 0); (Sym (a "_nl_C_LC_IDENTIFICATION") 0); (Sym (a "_nl_C_LC_CTYPE_class") 256); (Sym (a "_nl_C_LC_CTYPE_tolower") 512); (Sym (a "_nl_C_LC_CTYPE_toupper") 512); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0)]).
