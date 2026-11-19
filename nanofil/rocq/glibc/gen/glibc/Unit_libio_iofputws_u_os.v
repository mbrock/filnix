(** This file defines checked IR from glibc’s `libio/iofputws_u.os` object.
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

Definition fn___GI_fputws_unlocked : func :=
  ir_fn{ "export" "__GI_fputws_unlocked"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v6" : L = $"__wcslen"(P %"v0");
    call %"v57" : W = $"_IO_fwide"(P %"v2", W #1);
    %"v59" : W = (Cmp Eq W) %"v57", #1
    => br %"v59" ? "L60" : "L61";
  @"L60":
    %"v63" = %"v2" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v64";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v66" = %"v64" +p #56;
    %"chk1" : A = (Check 0 8 Read 8) %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v67";
    rawcall %"v71" : L = %"chk2"(P %"v2", P %"v0", L %"v6");
    %"v73" : W = (Cmp Eq L) %"v71", %"v6"
    => goto "L61";
  @"L61" [%"v75" : W = phi("start" => #0, "iw_1.join" => %"v73")]:
    => br %"v75" ? "L14" : "L13";
  @"L13":
    => goto "L14";
  @"L14" [%"pr.1" : W = phi("L13" => #4294967295, "L61" => #1)]:
    => ret %"pr.1"
} }.
