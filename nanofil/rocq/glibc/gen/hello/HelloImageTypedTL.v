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

Definition hello_image_fn___tls_init_tp : func :=
  ir_fn{ "export" "__tls_init_tp"() -> RVoid {
  @"start":
    call %"v1" : P = $"zthread_self_cookie"();
    %"v3" = %"v1" +p #720;
    call %"v4" : W = $"zthread_self_id"();
    %"chk0" : A = (Check 0 4 Write 1) %"v3";
    store Ww [%"chk0" + 0] <- %"v4";
    %"v6" = %"v1" +p #728;
    call %"v7" : P = $"zthread_self"();
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v6";
    store.ptr [%"chk1" + 0] <- %"v7";
    %"v9" = %"v1" +p #736;
    %"chk2" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v9";
    store Ww [%"chk2" + 0] <- #0;
    %"v11" = %"v1" +p #1312;
    %"v14" = %"v1" +p #800;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v11";
    store.ptr [%"chk3" + 0] <- %"v14";
    %"v17" = %"v1" +p #1572;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v17";
    store Ww [%"chk4" + 0] <- #2;
    %"v19" = %"v1" +p #1592;
    %"chk5" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v19";
    store Ww [%"chk5" + 0] <- #2;
    %"v21" = %"v1" +p #1569;
    %"v22" : P = Copy $"__nptl_initial_report_events";
    %"chk6" : A = (Check 0 1 Read 1) %"v22";
    %"v23" : W = (RawLoad (LdNarrow Ub) 0) %"chk6";
    %"chk7" : A = (HalfCheck Upper 0 1 Write 1) %"chk0", %"v21";
    store Wb [%"chk7" + 0] <- %"v23";
    %"v25" = %"v1" +p #744;
    %"v27" = %"v1" +p #752;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v25";
    store.ptr [%"chk8" + 0] <- %"v27";
    %"chk9" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v27";
    store.ptr [%"chk9" + 0] <- %"v27";
    %"v34" = %"v27" +p #8;
    %"chk10" : A = (HalfCheck Upper 0 8 Write 1) %"chk9", %"v34";
    store Wl [%"chk10" + 0] <- #18446744073709551584;
    %"v37" = %"v1" +p #1720;
    %"v38" : P = Copy $"__libc_stack_end";
    %"chk11" : A = (Check 0 8 Read 8) %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v40" : L = Ptoi %"v39";
    %"chk12" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v37";
    store Wl [%"chk12" + 0] <- %"v40"
    => ret void
} }.
