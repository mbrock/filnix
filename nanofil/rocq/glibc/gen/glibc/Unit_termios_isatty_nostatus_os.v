(** This file defines checked IR from glibc’s `termios/isatty_nostatus.os` object.
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

Definition fn___isatty_nostatus : func :=
  ir_fn{ "export" "__isatty_nostatus"(W %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 4) #44;
    call %"v18" : W = $"zsys_ioctl"(W %"v0", W #2150388778, P %"v2");
    %"v19" : W = (Cmp Eq W) %"v18", #0
    => ret %"v19"
} }.
