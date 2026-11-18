(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedPABlocks1275x1 HelloImageTypedPABlocks1275x2 HelloImageTypedPABlocks1276x1 HelloImageTypedPABlocks1276x2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___parse_one_specmb : func :=
  mkFunc (a "__parse_one_specmb") (a "export") (RClass L) [(P, (a "v0")); (L, (a "v2")); (P, (a "v4")); (P, (a "v6")); (P, (a "v8"))] (hello_image_fn___parse_one_specmb'blocks1 ++ hello_image_fn___parse_one_specmb'blocks2).

Definition hello_image_fn___parse_one_specwc : func :=
  mkFunc (a "__parse_one_specwc") (a "export") (RClass L) [(P, (a "v0")); (L, (a "v2")); (P, (a "v4")); (P, (a "v6")); (P, (a "v8"))] (hello_image_fn___parse_one_specwc'blocks1 ++ hello_image_fn___parse_one_specwc'blocks2).
