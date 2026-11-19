(** This file defines checked IR from the `roots` object of Stdlib.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item_stdlib_root : item :=
  (IData (a "stdlib_root") (LRo (a "export")) 8 [(Sym (a "malloc") 0); (Sym (a "free") 0); (Sym (a "calloc") 0); (Sym (a "atexit") 0); (Sym (a "__cxa_atexit") 0); (Sym (a "__errno_location") 0); (Sym (a "__ctype_b_loc") 0); (Sym (a "__ctype_get_mb_cur_max") 0); (Sym (a "mbsinit") 0); (Sym (a "iswprint") 0)]).
