(** This file contains part of glibc's checked option-parser module.
    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term.
From Nanofil Require Import CaptureNotation.
From Glibc Require Import GetoptCode01 GetoptCode04.
Import ListNotations.
Open Scope string_scope.

(** The linked module joins every generated item without changing its order. *)
Definition getopt_term : term :=
  TApp "module" [TList (getopt_items_01 ++ getopt_items_04)].
