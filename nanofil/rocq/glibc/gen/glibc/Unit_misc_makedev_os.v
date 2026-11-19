(** This file defines checked IR from glibc’s `misc/makedev.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___gnu_dev_major : func :=
  ir_fn{ "export" "__gnu_dev_major"(L %"v0") -> (RClass W) {
  @"start":
    %"v4" : L = And %"v0", #1048320;
    %"v5" : L = Shr %"v4", #8;
    %"v6" : W = Copy %"v5";
    %"v8" : L = And %"v0", #18446726481523507200;
    %"v9" : L = Shr %"v8", #32;
    %"v10" : L = (Ext Uw) %"v6";
    %"v11" : L = Or %"v10", %"v9";
    %"v12" : W = Copy %"v11"
    => ret %"v12"
} }.
