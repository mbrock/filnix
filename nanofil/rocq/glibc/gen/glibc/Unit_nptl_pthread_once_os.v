(** This file defines checked IR from glibc’s `nptl/pthread_once.os` object.
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

Definition item___GI___pthread_once : item :=
  (IAlias (a "__GI___pthread_once") (a "export") (a "___pthread_once")).

Definition fn____pthread_once : func :=
  ir_fn{ "export" "___pthread_once"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = And %"v6", #2;
    %"v12" : W = (Cmp Ne W) %"v11", #0
    => br %"v12" ? "L7" : "L8";
  @"L7":
    => ret #0;
  @"L8":
    call %"v18" : W = $"glibc_pthread_once#__pthread_once_slow"(P %"v0", P %"v2")
    => ret %"v18"
} }.

Definition item___fork_generation : item :=
  (IData (a "__fork_generation") LExport 8 [(Zero 8)]).

Definition fn_glibc_pthread_once'23__pthread_cleanup_combined_routine_voidptr : func :=
  ir_fn{ "local" "glibc_pthread_once#__pthread_cleanup_combined_routine_voidptr"(P %"v0") -> RVoid {
  @"start":
    %"v8" = %"v0" +p #16;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => br %"v9" ? "L4" : "L6";
  @"L4":
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" = %"v0" +p #8;
    %"v14" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"chk3" : F = CheckFunction %"v11";
    rawcall void %"chk3"(P %"v14");
    %"v16" = %"v0" +p #16;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk0", %"v16";
    store Ww [%"chk4" + 0] <- #0
    => goto "L6";
  @"L6":
    => ret void
} }.

Definition fn_glibc_pthread_once'23__pthread_once_slow : func :=
  ir_fn{ "local" "glibc_pthread_once#__pthread_once_slow"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v56" : P = (Alloc 8) #56
    => goto "L5";
  @"L5":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L11";
  @"L11" [%"pr.1" : W = phi("L32" => %"pr.2", "L5" => %"v10")]:
    %"v18" : W = And %"pr.1", #2;
    %"v19" : W = (Cmp Ne W) %"v18", #0
    => br %"v19" ? "L14" : "L16";
  @"L14":
    => ret #0;
  @"L16":
    %"v23" : P = Copy $"__fork_generation";
    %"chk1" : A = (Check 0 8 Read 1) %"v23";
    %"v24" : L = (RawLoad LdL 0) %"chk1";
    %"v25" : L = Or %"v24", #1;
    %"v27" : W = Copy %"v25";
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v0";
    %"v29" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"pr.1", %"v27";
    %"v30" : W = (Cmp Eq W) %"v29", %"pr.1"
    => br %"v30" ? "L32" : "L31";
  @"L31":
    => goto "L32";
  @"L32" [%"pr.2" : W = phi("L16" => %"pr.1", "L31" => %"v29")]:
    %"v33" : W = (Cmp Ne W) %"v29", %"pr.1"
    => br %"v33" ? poll "L11" : "L13";
  @"L13":
    %"v40" : W = And %"pr.2", #1
    => br %"v40" ? "L36" : "L51";
  @"L36":
    %"v46" : W = Copy %"v25";
    %"v47" : W = (Cmp Eq W) %"pr.2", %"v46"
    => br %"v47" ? "L42" : "L51";
  @"L42":
    %"v49" : W = Copy %"v25";
    call void $"zsys_futex_wait"(P %"v0", W %"v49", W #1)
    => goto poll "L5";
  @"L51":
    %"v55" : P = Copy $"glibc_pthread_once#clear_once_control";
    %"chk3" : A = (Check 0 8 Write 1) %"v56";
    store Wl [%"chk3" + 0] <- #0;
    %"v57" = %"v56" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v57";
    store Wl [%"chk4" + 0] <- #0;
    %"v58" = %"v56" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v58";
    store Wl [%"chk5" + 0] <- #0;
    %"v59" = %"v56" +p #24;
    %"chk6" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v59";
    store Wl [%"chk6" + 0] <- #0;
    %"v60" = %"v56" +p #32;
    %"chk7" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v60";
    store Wl [%"chk7" + 0] <- #0;
    %"v61" = %"v56" +p #40;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v61";
    store Wl [%"chk8" + 0] <- #0;
    %"v62" = %"v56" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v62";
    store Wl [%"chk9" + 0] <- #0;
    %"chk10" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v56";
    store.ptr [%"chk10" + 0] <- %"v55";
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk4", %"v57";
    store.ptr [%"chk11" + 0] <- %"v0";
    %"chk12" : A = (Renew 0 4 Write 1) %"chk5", %"v58";
    store Ww [%"chk12" + 0] <- #1;
    %"v68" : P = Copy $"glibc_pthread_once#__pthread_cleanup_combined_routine_voidptr";
    call void $"__GI___pthread_cleanup_push"(P %"v59", P %"v68", P %"v56");
    %"chk13" : F = CheckFunction %"v2";
    rawcall void %"chk13"();
    call void $"__GI___pthread_cleanup_pop"(P %"v59", W #0);
    %"chk14" : A = (Renew 0 4 Write 1) %"chk5", %"v58";
    store Ww [%"chk14" + 0] <- #0;
    %"iw_2.v6" = %"v56" +p #16;
    %"iw_2.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk14"
    => br %"iw_2.v7" ? "iw_2.L2" : "L78";
  @"iw_2.L2":
    %"chk16" : A = (Renew 0 8 Read 8) %"chk10", %"v56";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v11" = %"v56" +p #8;
    %"iw_2.v12" : P = (RawLoadPointer 8 load_effects) %"chk16";
    %"chk18" : F = CheckFunction %"iw_2.v9";
    rawcall void %"chk18"(P %"iw_2.v12");
    %"iw_2.v14" = %"v56" +p #16;
    %"chk19" : A = (Renew 0 4 Write 1) %"chk5", %"iw_2.v14";
    store Ww [%"chk19" + 0] <- #0;
    %"iw_2.v16" = %"v56" +p #24;
    call void $"__GI___pthread_cleanup_pop"(P %"iw_2.v16", W #0)
    => goto "L78";
  @"L78":
    %"chk20" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk20" + 0] <- #2;
    call void $"zsys_futex_wake"(P %"v0", W #2147483647, W #1)
    => ret #0
} }.

Definition fn_glibc_pthread_once'23clear_once_control : func :=
  ir_fn{ "local" "glibc_pthread_once#clear_once_control"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Write 1) %"v0";
    store Ww [%"chk0" + 0] <- #0;
    call void $"zsys_futex_wake"(P %"v0", W #2147483647, W #1)
    => ret void
} }.
