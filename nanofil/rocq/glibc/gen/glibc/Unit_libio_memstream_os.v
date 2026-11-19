(** This file defines checked IR from glibc’s `libio/memstream.os` object.
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

Definition fn__IO_mem_doallocate : func :=
  ir_fn{ "export" "_IO_mem_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    => ret #1
} }.

Definition fn__IO_mem_finish : func :=
  ir_fn{ "export" "_IO_mem_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v7" = %"v0" +p #240;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v0" +p #32;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" = %"v0" +p #40;
    %"v14" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v18" : L = Ptoi %"v14";
    %"v19" : L = Ptoi %"v17";
    %"v20" : L = Sub %"v18", %"v19";
    %"v21" : L = Add %"v20", #1;
    call %"v22" : P = $"realloc"(P %"v11", L %"v21");
    %"chk4" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk4" + 0] <- %"v22";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v7";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Read 8) %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v30" : L = Ptoi %"v29";
    %"v31" : L = Ptoi #0;
    %"v32" : W = (Cmp Ne L) %"v30", %"v31"
    => br %"v32" ? "L23" : "L25";
  @"L23":
    %"v34" = %"v0" +p #240;
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk8" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v38" = %"v0" +p #40;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v41" = %"v0" +p #32;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v43" : L = Ptoi %"v39";
    %"v44" : L = Ptoi %"v42";
    %"v45" : L = Sub %"v43", %"v44";
    %"v46" = %"v36" +p %"v45";
    %"chk11" : A = (Check 0 1 Write 1) %"v46";
    store Wb [%"chk11" + 0] <- #0;
    %"v48" = %"v0" +p #248;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v56" : L = Ptoi %"v52";
    %"v57" : L = Ptoi %"v55";
    %"v58" : L = Sub %"v56", %"v57";
    %"chk15" : A = (Check 0 8 Write 1) %"v49";
    store Wl [%"chk15" + 0] <- %"v58";
    %"v60" = %"v0" +p #56;
    %"chk16" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v60";
    store.ptr [%"chk16" + 0] <- #0
    => goto "L25";
  @"L25":
    call void $"_IO_str_finish"(P %"v0", W #0)
    => ret void
} }.

Definition fn__IO_mem_setbuf : func :=
  ir_fn{ "export" "_IO_mem_setbuf"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    => ret %"v0"
} }.

Definition fn__IO_mem_sync : func :=
  ir_fn{ "export" "_IO_mem_sync"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #48;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L4" : "L6";
  @"L4":
    call %"v17" : W = $"__GI__IO_str_overflow"(P %"v0", W #0);
    %"v19" = %"v0" +p #40;
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk2";
    (Flight (a "v21") Sub [(FAddress (t "v20")); (FValue (Const 1))] (LowerOf (t "v20")));
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v19";
    store.ptr [%"chk3" + 0] <- %"v21"
    => goto "L6";
  @"L6":
    %"v23" = %"v0" +p #240;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v26" = %"v0" +p #32;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk6" + 0] <- %"v27";
    %"v29" = %"v0" +p #248;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v32" = %"v0" +p #40;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Renew 0 8 Read 8) %"chk5", %"v26";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v37" : L = Ptoi %"v33";
    %"v38" : L = Ptoi %"v36";
    %"v39" : L = Sub %"v37", %"v38";
    %"chk10" : A = (Check 0 8 Write 1) %"v30";
    store Wl [%"chk10" + 0] <- %"v39"
    => ret #0
} }.
