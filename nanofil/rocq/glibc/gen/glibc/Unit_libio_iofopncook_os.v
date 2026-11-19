(** This file defines checked IR from glibc’s `libio/iofopncook.os` object.
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

Definition fn__IO_cookie_close : func :=
  ir_fn{ "export" "_IO_cookie_close"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #232;
    %"v7" = %"v6" +p #24;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : L = Ptoi %"v8";
    %"v15" : L = Ptoi #0;
    %"v16" : W = (Cmp Eq L) %"v14", %"v15"
    => br %"v16" ? "L10" : "L12";
  @"L10":
    => ret #0;
  @"L12":
    %"v20" = %"v0" +p #224;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v8";
    rawcall %"v22" : W = %"chk2"(P %"v21")
    => ret %"v22"
} }.

Definition fn__IO_cookie_read : func :=
  ir_fn{ "export" "_IO_cookie_read"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v10" = %"v0" +p #232;
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v17" : L = Ptoi %"v11";
    %"v18" : L = Ptoi #0;
    %"v19" : W = (Cmp Eq L) %"v17", %"v18"
    => br %"v19" ? "L13" : "L15";
  @"L13":
    => ret #18446744073709551615;
  @"L15":
    %"v25" = %"v0" +p #224;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v11";
    rawcall %"v29" : L = %"chk2"(P %"v26", P %"v2", L %"v4")
    => ret %"v29"
} }.

Definition fn__IO_cookie_seek : func :=
  ir_fn{ "export" "_IO_cookie_seek"(P %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v3" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Write 1) %"v3";
    store Wl [%"chk0" + 0] <- %"v2";
    %"v10" = %"v0" +p #232;
    %"v11" = %"v10" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v18" : L = Ptoi %"v12";
    %"v19" : L = Ptoi #0;
    %"v20" : W = (Cmp Eq L) %"v18", %"v19"
    => br %"v20" ? "L22" : "L21";
  @"L21":
    %"v25" = %"v0" +p #224;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : F = CheckFunction %"v12";
    rawcall %"v28" : W = %"chk3"(P %"v26", P %"v3", W %"v4");
    %"v30" : W = (Cmp Eq W) %"v28", #4294967295
    => goto "L22";
  @"L22" [%"v32" : W = phi("start" => #1, "L21" => %"v30")]:
    => br %"v32" ? "L34" : "L33";
  @"L33":
    %"chk4" : A = (Renew 0 8 Read 1) %"chk0", %"v3";
    %"v35" : L = (RawLoad LdL 0) %"chk4";
    %"v38" : W = (Cmp Eq L) %"v35", #18446744073709551615
    => goto "L34";
  @"L34" [%"v40" : W = phi("L22" => #1, "L33" => %"v38")]:
    => br %"v40" ? "L16" : "L15";
  @"L15":
    %"chk5" : A = (Renew 0 8 Read 1) %"chk0", %"v3";
    %"v43" : L = (RawLoad LdL 0) %"chk5"
    => goto "L16";
  @"L16" [%"v44" : L = phi("L15" => %"v43", "L34" => #18446744073709551615)]:
    => ret %"v44"
} }.

Definition fn__IO_cookie_seekoff : func :=
  ir_fn{ "export" "_IO_cookie_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v9" = %"v0" +p #144;
    %"chk0" : A = (Check 0 8 Write 1) %"v9";
    store Wl [%"chk0" + 0] <- #18446744073709551615;
    call %"v16" : L = $"__GI__IO_file_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6")
    => ret %"v16"
} }.

Definition fn__IO_cookie_write : func :=
  ir_fn{ "export" "_IO_cookie_write"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v10" = %"v0" +p #232;
    %"v11" = %"v10" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v18" : L = Ptoi %"v12";
    %"v19" : L = Ptoi #0;
    %"v20" : W = (Cmp Eq L) %"v18", %"v19"
    => br %"v20" ? "L14" : "L16";
  @"L14":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v23" : W = Or %"v22", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk1", %"v0";
    store Ww [%"chk2" + 0] <- %"v23"
    => ret #0;
  @"L16":
    %"v28" = %"v0" +p #224;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v12";
    rawcall %"v32" : L = %"chk4"(P %"v29", P %"v2", L %"v4");
    %"v38" : W = (Cmp Slt L) %"v32", %"v4"
    => br %"v38" ? "L33" : "L35";
  @"L33":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v40" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v41" : W = Or %"v40", #32;
    %"chk6" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk6" + 0] <- %"v41"
    => goto "L35";
  @"L35":
    => ret %"v32"
} }.
