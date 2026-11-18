(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___GI___woverflow : func :=
  ir_fn{ "export" "__GI___woverflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => br %"v10" ? "L36" : "L6";
  @"L36":
    call %"v53" : W = $"_IO_fwide"(P %"v0", W #1)
    => goto "L6";
  @"L6":
    %"v56" = %"v0" +p #216;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v4" : L = Ptoi %"v57";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v59" = %"v57" +p #24;
    %"chk2" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : F = CheckFunction %"v60";
    rawcall %"v63" : W = %"chk3"(P %"v0", W %"v2")
    => ret %"v63"
} }.
