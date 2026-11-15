(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term.
From Glibc Require Import FormatterCode01 FormatterCode07 FormatterCode12 FormatterCode13.
Import ListNotations.
Open Scope string_scope.

(** The linked module joins every generated item without changing its order. *)
Definition formatter_term : term :=
  TApp "module" [TList (formatter_items_01 ++ formatter_items_07 ++ formatter_items_12 ++ formatter_items_13)].
