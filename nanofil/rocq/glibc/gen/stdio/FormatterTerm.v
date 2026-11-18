(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term.
From Nanofil Require Import CaptureNotation.
From Glibc Require Import FormatterCode01 FormatterCode06 FormatterCode10 FormatterCode11.
Import ListNotations.
Open Scope string_scope.

(** The linked module joins every generated item without changing its order. *)
Definition formatter_term : term :=
  TApp "module" [TList (formatter_items_01 ++ formatter_items_06 ++ formatter_items_10 ++ formatter_items_11)].
