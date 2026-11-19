(** This file defines checked IR from glibc’s `libio/wmemstream.os` object.
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

Definition fn__IO_wmem_doallocate : func :=
  ir_fn{ "export" "_IO_wmem_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    => ret #1
} }.

Definition fn__IO_wmem_finish : func :=
  ir_fn{ "export" "_IO_wmem_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v7" = %"v0" +p #240;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v0" +p #160;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" = %"v11" +p #24;
    %"chk2" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v17" = %"v16" +p #32;
    %"chk4" : A = (Check 0 8 Read 8) %"v17";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v22" = %"v21" +p #24;
    %"chk6" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v24" : L = Ptoi %"v18";
    %"v25" : L = Ptoi %"v23";
    %"v26" : L = Sub %"v24", %"v25";
    %"v27" : L = Div %"v26", #4;
    %"v28" : L = Add %"v27", #1;
    %"v29" : L = Shl %"v28", #2;
    call %"v30" : P = $"realloc"(P %"v13", L %"v29");
    %"chk7" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk7" + 0] <- %"v30";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v7";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v38" : L = Ptoi %"v37";
    %"v39" : L = Ptoi #0;
    %"v40" : W = (Cmp Ne L) %"v38", %"v39"
    => br %"v40" ? "L31" : "L33";
  @"L31":
    %"v43" = %"v0" +p #160;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v45" = %"v44" +p #32;
    %"chk11" : A = (Check 0 8 Read 8) %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v50" = %"v49" +p #24;
    %"chk13" : A = (Check 0 8 Read 8) %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v52" : L = Ptoi %"v46";
    %"v53" : L = Ptoi %"v51";
    %"v54" : L = Sub %"v52", %"v53";
    %"v55" : L = Div %"v54", #4;
    %"v57" = %"v0" +p #240;
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk15" : A = (Check 0 8 Read 8) %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v61" : L = Shl %"v55", #2;
    %"v62" = %"v59" +p %"v61";
    %"chk16" : A = (Check 0 4 Write 1) %"v62";
    store Ww [%"chk16" + 0] <- #0;
    %"v64" = %"v0" +p #248;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 8 Write 1) %"v65";
    store Wl [%"chk18" + 0] <- %"v55";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v70" = %"v69" +p #48;
    %"chk20" : A = (Check 0 8 Write 8) %"v70";
    store.ptr [%"chk20" + 0] <- #0
    => goto "L33";
  @"L33":
    call void $"_IO_wstr_finish"(P %"v0", W #0)
    => ret void
} }.

Definition fn__IO_wmem_setbuf : func :=
  ir_fn{ "export" "_IO_wmem_setbuf"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    => ret %"v0"
} }.

Definition fn__IO_wmem_sync : func :=
  ir_fn{ "export" "_IO_wmem_sync"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v9" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v15" = %"v14" +p #40;
    %"chk3" : A = (Check 0 8 Read 8) %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v17" : L = Ptoi %"v11";
    %"v18" : L = Ptoi %"v16";
    %"v19" : W = (Cmp Eq L) %"v17", %"v18"
    => br %"v19" ? "L4" : "L6";
  @"L4":
    call %"v21" : W = $"_IO_wstr_overflow"(P %"v0", W #0);
    %"v23" = %"v0" +p #160;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v25" = %"v24" +p #32;
    %"chk5" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    (Flight (a "v27") Sub [(FAddress (t "v26")); (FValue (Const 4))] (LowerOf (t "v26")));
    %"chk6" : A = (Renew 0 8 Write 8) %"chk5", %"v25";
    store.ptr [%"chk6" + 0] <- %"v27"
    => goto "L6";
  @"L6":
    %"v29" = %"v0" +p #240;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v32" = %"v0" +p #160;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v34" = %"v33" +p #24;
    %"chk9" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 8 Write 8) %"v30";
    store.ptr [%"chk10" + 0] <- %"v35";
    %"v37" = %"v0" +p #248;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v32";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v42" = %"v41" +p #32;
    %"chk13" : A = (Check 0 8 Read 8) %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v47" = %"v46" +p #24;
    %"chk15" : A = (Check 0 8 Read 8) %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v49" : L = Ptoi %"v43";
    %"v50" : L = Ptoi %"v48";
    %"v51" : L = Sub %"v49", %"v50";
    %"v52" : L = Div %"v51", #4;
    %"chk16" : A = (Check 0 8 Write 1) %"v38";
    store Wl [%"chk16" + 0] <- %"v52"
    => ret #0
} }.
