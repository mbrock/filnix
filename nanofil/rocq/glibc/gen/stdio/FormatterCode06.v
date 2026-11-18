(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
From Glibc Require Import FormatterCode02 FormatterCode03 FormatterCode04 FormatterCode05.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** These items retain their order in the linked module. *)
Definition formatter_items_06 : list term :=
  [
    cap_fn{ "export" "__printf_buffer" [param "p" %"v0"; param "p" %"v2"; param "p" %"v4"; param "w" %"v6"] -> "void"
      blocks (formatter_blocks_02 ++ formatter_blocks_03 ++ formatter_blocks_04 ++ formatter_blocks_05) }
  ].
