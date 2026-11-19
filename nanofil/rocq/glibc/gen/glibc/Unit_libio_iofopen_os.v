(** This file defines checked IR from glibc’s `libio/iofopen.os` object.
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

Definition fn__IO_new_fopen : func :=
  ir_fn{ "export" "_IO_new_fopen"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"__fopen_internal"(P %"v0", P %"v2", W #1)
    => ret %"v6"
} }.

Definition fn___fopen_internal : func :=
  ir_fn{ "export" "__fopen_internal"(P %"v0", P %"v2", W %"v4") -> (RClass P) {
  @"start":
    call %"v7" : P = $"malloc"(L #472);
    %"v12" : L = Ptoi %"v7";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    => ret #0;
  @"L10":
    %"v17" = %"v7" +p #136;
    %"v19" = %"v7" +p #224;
    %"chk0" : A = (Check 0 8 Write 8) %"v17";
    store.ptr [%"chk0" + 0] <- %"v19";
    %"v22" = %"v7" +p #240;
    %"v23" : P = Copy $"__io_vtables";
    %"v24" = %"v23" +p #840;
    call void $"_IO_no_init"(P %"v7", W #0, W #0, P %"v22", P %"v24");
    %"v26" = %"v7" +p #216;
    %"v27" : P = Copy $"__io_vtables";
    %"v28" = %"v27" +p #336;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v26";
    store.ptr [%"chk1" + 0] <- %"v28";
    call void $"_IO_new_file_init_internal"(P %"v7");
    call %"v37" : P = $"__GI__IO_file_fopen"(P %"v7", P %"v0", P %"v2", W %"v4");
    %"v38" : L = Ptoi %"v37";
    %"v40" : W = (Cmp Ne L) %"v38", %"v13"
    => br %"v40" ? "L30" : "L32";
  @"L30":
    call %"v42" : P = $"__fopen_maybe_mmap"(P %"v7")
    => ret %"v42";
  @"L32":
    call void $"__GI__IO_un_link"(P %"v7");
    call void $"free"(P %"v7")
    => ret #0
} }.

Definition fn___fopen_maybe_mmap : func :=
  ir_fn{ "export" "__fopen_maybe_mmap"(P %"v0") -> (RClass P) {
  @"start":
    %"v6" = %"v0" +p #116;
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v8" : W = Shl %"v7", #8;
    %"v9" : W = Sar %"v8", #8;
    %"v10" : W = And %"v9", #1
    => br %"v10" ? "L11" : "L12";
  @"L11":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v15" : W = And %"v14", #8;
    %"v16" : W = (Cmp Ne W) %"v15", #0
    => goto "L12";
  @"L12" [%"v17" : W = phi("start" => #0, "L11" => %"v16")]:
    => br %"v17" ? "L2" : "L4";
  @"L2":
    %"v22" = %"v0" +p #192;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v22";
    %"v23" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v24" : W = (Cmp Sle W) %"v23", #0
    => br %"v24" ? "L18" : "L19";
  @"L18":
    %"v26" = %"v0" +p #216;
    %"v27" : P = Copy $"__io_vtables";
    %"v28" = %"v27" +p #672;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v26";
    store.ptr [%"chk3" + 0] <- %"v28"
    => goto "L20";
  @"L19":
    %"v30" = %"v0" +p #216;
    %"v31" : P = Copy $"__io_vtables";
    %"v32" = %"v31" +p #1176;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v30";
    store.ptr [%"chk4" + 0] <- %"v32"
    => goto "L20";
  @"L20":
    %"v34" = %"v0" +p #160;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v36" = %"v35" +p #224;
    %"v37" : P = Copy $"__io_vtables";
    %"v38" = %"v37" +p #1176;
    %"chk6" : A = (Check 0 8 Write 8) %"v36";
    store.ptr [%"chk6" + 0] <- %"v38"
    => goto "L4";
  @"L4":
    => ret %"v0"
} }.
