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

Definition hi_fn___GI___overflow : func :=
  ir_fn{ "export" "__GI___overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => br %"v10" ? "L13" : "L6";
  @"L13":
    %"v27" = %"v0" +p #192;
    %"v28" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v29" : W = (Cmp Eq W) %"v28", #0
    => br %"v29" ? "L23" : "L25";
  @"L23":
    %"v31" = %"v0" +p #192;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v31";
    store Ww [%"chk2" + 0] <- #4294967295
    => goto "L25";
  @"L25":
    %"v34" = %"v0" +p #192;
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L6";
  @"L6":
    %"v58" = %"v0" +p #216;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v4" : L = Ptoi %"v59";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v61" = %"v59" +p #24;
    %"chk5" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : F = CheckFunction %"v62";
    rawcall %"v65" : W = %"chk6"(P %"v0", W %"v2")
    => ret %"v65"
} }.
