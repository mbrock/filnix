(** This file contains part of glibc's checked option-parser module.
    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term.
From Glibc Require Import GetoptCode03 GetoptCode07.
Import ListNotations.
Open Scope string_scope.

(** The linked module joins every generated item without changing its order. *)
Definition getopt_term : term :=
  TApp "module" [TList (getopt_items_03 ++ getopt_items_07)].
