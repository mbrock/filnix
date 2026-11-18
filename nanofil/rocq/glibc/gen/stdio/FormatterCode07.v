(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Glibc Require Import FormatterCode02 FormatterCode03 FormatterCode04 FormatterCode05 FormatterCode06.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These items retain their order in the linked module. *)
Definition formatter_items_07 : list term :=
  [
    TApp "func" [TAtom "__printf_buffer"; TAtom "export"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v4"]]; TApp "param" [TAtom "w"; TApp "tmp" [TAtom "v6"]]];
      TList (formatter_blocks_02 ++ formatter_blocks_03 ++ formatter_blocks_04 ++ formatter_blocks_05 ++ formatter_blocks_06)]
  ].
