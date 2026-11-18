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

Definition hello_image_fn___fpending : func :=
  ir_fn{ "export" "__fpending"(P %"v0") -> (RClass L) {
  @"start":
    %"v6" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v8" : W = (Cmp Sgt W) %"v7", #0
    => br %"v8" ? "L2" : "L3";
  @"L2":
    %"v10" = %"v0" +p #160;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" = %"v11" +p #32;
    %"chk2" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v17" = %"v16" +p #24;
    %"chk4" : A = (Check 0 8 Read 8) %"v17";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v19" : L = Ptoi %"v13";
    %"v20" : L = Ptoi %"v18";
    %"v21" : L = Sub %"v19", %"v20";
    %"v22" : L = Div %"v21", #4
    => ret %"v22";
  @"L3":
    %"v25" = %"v0" +p #40;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v28" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v30" : L = Ptoi %"v26";
    %"v31" : L = Ptoi %"v29";
    %"v32" : L = Sub %"v30", %"v31"
    => ret %"v32"
} }.

Definition hello_image_fn___fprintf : func :=
  ir_fn{ "export" "__fprintf"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #16;
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- %"va_args";
    call %"v8" : W = $"__vfprintf_internal"(P %"v0", P %"v2", P %"v4", W #0)
    => ret %"v8"
} }.

Definition hello_image_fn___GI_fputws_unlocked : func :=
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
