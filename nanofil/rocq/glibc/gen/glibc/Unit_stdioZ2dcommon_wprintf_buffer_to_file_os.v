(** This file defines checked IR from glibc’s `stdio-common/wprintf_buffer_to_file.os` object.
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

Definition fn___wprintf_buffer_flush_to_file : func :=
  ir_fn{ "export" "__wprintf_buffer_flush_to_file"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v7" = %"v0" +p #48;
    %"v8" : L = Ptoi %"v5";
    %"v9" : L = Ptoi %"v7";
    %"v10" : L = Sub %"v8", %"v9";
    %"v11" : L = Div %"v10", #4;
    %"v16" = %"v0" +p #40;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v18" = %"v17" +p #216;
    %"chk2" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v4" : L = Ptoi %"v19";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v21" = %"v19" +p #56;
    %"chk3" : A = (Check 0 8 Read 8) %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v24" = %"v0" +p #40;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v27" = %"v0" +p #48;
    %"chk5" : F = CheckFunction %"v22";
    rawcall %"v29" : L = %"chk5"(P %"v25", P %"v27", L %"v11");
    %"v31" : W = (Cmp Ne L) %"v29", %"v11"
    => br %"v31" ? "iw_2.start" : "L14";
  @"iw_2.start":
    %"iw_2.v3" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_2.v3";
    store Ww [%"chk6" + 0] <- #0
    => ret void;
  @"L14":
    %"v35" = %"v0" +p #24;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v35";
    %"v36" : L = (RawLoad LdL 0) %"chk7";
    %"v38" : L = Add %"v36", %"v11";
    %"chk8" : A = (Renew 0 8 Write 1) %"chk7", %"v35";
    store Wl [%"chk8" + 0] <- %"v38";
    %"v40" = %"v0" +p #8;
    %"v42" = %"v0" +p #48;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk0", %"v40";
    store.ptr [%"chk9" + 0] <- %"v42"
    => ret void
} }.

Definition fn___wprintf_buffer_to_file_done : func :=
  ir_fn{ "export" "__wprintf_buffer_to_file_done"(P %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    call void $"__wprintf_buffer_flush_to_file"(P %"v0");
    call %"v12" : W = $"__wprintf_buffer_done"(P %"v0")
    => ret %"v12"
} }.

Definition fn___wprintf_buffer_to_file_init : func :=
  ir_fn{ "export" "__wprintf_buffer_to_file_init"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #48;
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v6";
    %"iw_1.v11" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v6";
    %"iw_1.v14" = %"v0" +p #16;
    %"iw_1.v18" = %"v6" +p #512;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v18";
    %"iw_1.v20" = %"v0" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.v20";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.v22" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v22";
    store Ww [%"chk4" + 0] <- #2;
    %"v11" = %"v0" +p #40;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v11";
    store.ptr [%"chk5" + 0] <- %"v2"
    => ret void
} }.
