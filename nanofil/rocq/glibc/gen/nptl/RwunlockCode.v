(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_nptl_pthread_rwlock_unlock_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition rwunlock_module : module :=
  [(IData (a "rwunlock_roots") (LRo (a "export")) 8 [(Sym (a "__GI___pthread_rwlock_unlock") 0)]);
  IFunc Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock;
  Unit_nptl_pthread_rwlock_unlock_os.item___GI___pthread_rwlock_unlock;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e286;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e287;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e288;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e289].
