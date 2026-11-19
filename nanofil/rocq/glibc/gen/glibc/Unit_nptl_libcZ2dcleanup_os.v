(** This file defines checked IR from glibc’s `nptl/libc-cleanup.os` object.
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

Definition fn___GI___libc_cleanup_pop_restore : func :=
  ir_fn{ "export" "__GI___libc_cleanup_pop_restore"(P %"v0") -> RVoid {
  @"start":
    call %"v3" : P = $"zthread_self_cookie"();
    %"v5" = %"v3" +p #776;
    %"v7" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Write 8) %"v5";
    store.ptr [%"chk1" + 0] <- %"v8";
    %"v11" = %"v3" +p #792;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"v11";
    %"v12" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v17" = %"v0" +p #16;
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v17";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v19" : W = (Cmp Ne W) %"v18", #0
    => br %"v19" ? "L20" : "L21";
  @"L20":
    %"v24" : W = And %"v12", #2;
    %"v25" : W = (Cmp Eq W) %"v24", #0
    => goto "L21";
  @"L21" [%"v27" : W = phi("start" => #0, "L20" => %"v25")]:
    => br %"v27" ? "L29" : "L15";
  @"L29" [%"pr.1" : W = phi("L42" => %"pr.2", "L21" => %"v12")]:
    %"v34" : W = Or %"pr.1", #2;
    %"v36" = %"v3" +p #792;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 4) %"chk1", %"v36";
    %"v39" : W = (RawCas (CasNarrow Sw) 0) %"chk4", %"pr.1", %"v34";
    %"v40" : W = (Cmp Eq W) %"v39", %"pr.1"
    => br %"v40" ? "L42" : "L41";
  @"L41":
    => goto "L42";
  @"L42" [%"pr.2" : W = phi("L29" => %"pr.1", "L41" => %"v39")]:
    %"v43" : W = (Cmp Ne W) %"v39", %"pr.1"
    => br %"v43" ? poll "L29" : "iw_1.start";
  @"iw_1.start":
    %"iw_1.v10" : W = And %"pr.2", #57;
    %"iw_1.v12" : W = (Cmp Eq W) %"iw_1.v10", #8
    => br %"iw_1.v12" ? "L44" : "L15";
  @"L44":
    (Flight (a "v52") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    call %"iw_2.v3" : P = $"zthread_self_cookie"();
    %"iw_2.v5" = %"iw_2.v3" +p #1608;
    %"chk5" : A = (Check 0 8 Write 8) %"iw_2.v5";
    store.ptr [%"chk5" + 0] <- %"v52";
    %"iw_2.v9" = %"iw_2.v3" +p #792;
    %"chk6" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"iw_2.v9";
    %"iw_2.v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk6"
    => goto "iw_2.L12";
  @"iw_2.L12" [%"iw_2.pr.1" : W = phi("iw_2.L38" => %"iw_2.pr.2", "L44" => %"iw_2.v10")]:
    %"iw_2.v17" : W = Or %"iw_2.pr.1", #1;
    %"iw_2.v19" : W = Or %"iw_2.v17", #16;
    %"iw_2.v23" : W = And %"iw_2.v19", #4294967293;
    %"iw_2.v29" : W = (Cmp Eq W) %"iw_2.pr.1", %"iw_2.v23"
    => br %"iw_2.v29" ? "iw_2.L14" : "iw_2.L13";
  @"iw_2.L13":
    %"iw_2.v32" = %"iw_2.v3" +p #792;
    %"chk7" : A = (HalfCheck Lower 0 4 Write 4) %"chk5", %"iw_2.v32";
    %"iw_2.v35" : W = (RawCas (CasNarrow Sw) 0) %"chk7", %"iw_2.pr.1", %"iw_2.v23";
    %"iw_2.v36" : W = (Cmp Eq W) %"iw_2.v35", %"iw_2.pr.1"
    => br %"iw_2.v36" ? "iw_2.L38" : "iw_2.L37";
  @"iw_2.L37":
    => goto "iw_2.L38";
  @"iw_2.L38" [%"iw_2.pr.2" : W = phi("iw_2.L13" => %"iw_2.pr.1", "iw_2.L37" => %"iw_2.v35")]:
    %"iw_2.v39" : W = (Cmp Ne W) %"iw_2.v35", %"iw_2.pr.1"
    => br %"iw_2.v39" ? poll "iw_2.L12" : "iw_2.L14";
  @"iw_2.L14":
    %"iw_2.v41" = %"iw_2.v3" +p #784;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"iw_2.v41";
    %"iw_2.v42" : P = (RawLoadPointer 0 load_effects) %"chk8";
    call void $"__GI___pthread_unwind"(P %"iw_2.v42")
    => goto "L15";
  @"L15":
    => ret void
} }.

Definition fn___GI___libc_cleanup_push_defer : func :=
  ir_fn{ "export" "__GI___libc_cleanup_push_defer"(P %"v0") -> RVoid {
  @"start":
    call %"v3" : P = $"zthread_self_cookie"();
    %"v5" = %"v0" +p #24;
    %"v7" = %"v3" +p #776;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Write 8) %"v5";
    store.ptr [%"chk1" + 0] <- %"v8";
    %"v11" = %"v3" +p #792;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v11";
    %"v12" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v18" : W = And %"v12", #2;
    %"v19" : L = (Ext Sw) %"v18";
    %"v20" : W = (Cmp Ne L) %"v19", #0
    => br %"v20" ? "L22" : "L15";
  @"L22" [%"pr.2" : W = phi("L36" => %"pr.3", "start" => %"v12")]:
    %"v28" : W = And %"pr.2", #4294967293;
    %"v30" = %"v3" +p #792;
    %"chk3" : A = (HalfCheck Upper 0 4 Write 4) %"chk0", %"v30";
    %"v33" : W = (RawCas (CasNarrow Sw) 0) %"chk3", %"pr.2", %"v28";
    %"v34" : W = (Cmp Eq W) %"v33", %"pr.2"
    => br %"v34" ? "L36" : "L35";
  @"L35":
    => goto "L36";
  @"L36" [%"pr.3" : W = phi("L22" => %"pr.2", "L35" => %"v33")]:
    %"v37" : W = (Cmp Ne W) %"v33", %"pr.2"
    => br %"v37" ? poll "L22" : "L15";
  @"L15" [%"pr.1" : W = phi("L36" => %"pr.3", "start" => %"v12")]:
    %"v39" = %"v0" +p #16;
    %"v45" : W = And %"pr.1", #2
    => br %"v45" ? "L42" : "L41";
  @"L41":
    => goto "L42";
  @"L42" [%"v46" : W = phi("L41" => #0, "L15" => #1)]:
    %"chk4" : A = (HalfCheck Lower 0 4 Write 1) %"chk1", %"v39";
    store Ww [%"chk4" + 0] <- %"v46";
    %"v48" = %"v3" +p #776;
    %"chk5" : A = (Renew 0 8 Write 8) %"chk0", %"v48";
    store.ptr [%"chk5" + 0] <- %"v0"
    => ret void
} }.
