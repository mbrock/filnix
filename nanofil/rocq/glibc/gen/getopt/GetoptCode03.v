(** This file contains part of glibc's checked option-parser module.
    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Glibc Require Import GetoptCode01 GetoptCode02.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These items retain their order in the linked module. *)
Definition getopt_items_03 : list term :=
  [
    TApp "func" [TAtom "glibc_getopt#process_long_option"; TAtom "local"; TAtom "w"; TList [TApp "param" [TAtom "w"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v4"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v6"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v8"]]; TApp "param" [TAtom "w"; TApp "tmp" [TAtom "v10"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v12"]]; TApp "param" [TAtom "w"; TApp "tmp" [TAtom "v14"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v16"]]];
      TList (getopt_blocks_01 ++ getopt_blocks_02)]
  ].
