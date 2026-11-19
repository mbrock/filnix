(** This file defines checked IR from glibc’s `libio/wfiledoalloc.os` object.
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

Definition fn__IO_wfile_doallocate : func :=
  ir_fn{ "export" "_IO_wfile_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" : L = Ptoi %"v9";
    %"v11" : L = Ptoi #0;
    %"v12" : W = (Cmp Eq L) %"v10", %"v11"
    => br %"v12" ? "L4" : "L6";
  @"L4":
    call %"v14" : W = $"__GI__IO_file_doallocate"(P %"v0")
    => goto "L6";
  @"L6":
    %"v16" = %"v0" +p #64;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v19" = %"v0" +p #56;
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v21" : L = Ptoi %"v17";
    %"v22" : L = Ptoi %"v20";
    %"v23" : L = Sub %"v21", %"v22";
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v28" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v29" : W = And %"v28", #1
    => br %"v29" ? "L24" : "L26";
  @"L24":
    %"v31" : L = Add %"v23", #4;
    %"v32" : L = Sub %"v31", #1;
    %"v33" : L = Shr %"v32", #2
    => goto "L26";
  @"L26" [%"pr.1" : L = phi("L24" => %"v33", "L6" => %"v23")]:
    %"v35" : L = Shl %"pr.1", #2;
    call %"v36" : P = $"malloc"(L %"v35");
    %"v41" : L = Ptoi %"v36";
    %"v43" : W = (Cmp Eq L) %"v41", %"v11"
    => br %"v43" ? "L37" : "L39";
  @"L37":
    => ret #4294967295;
  @"L39":
    %"v53" = %"v36" +p %"v35";
    call void $"__GI__IO_wsetb"(P %"v0", P %"v36", P %"v53", W #1)
    => ret #1
} }.
