(** This file defines checked IR from glibc’s `nptl/pthread_setcancelstate.os` object.
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

Definition fn___GI___pthread_setcancelstate : func :=
  ir_fn{ "export" "__GI___pthread_setcancelstate"(W %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v9" : W = (Cmp Slt W) %"v0", #0
    => br %"v9" ? "L11" : "L10";
  @"L10":
    %"v13" : W = (Cmp Sgt W) %"v0", #1
    => goto "L11";
  @"L11" [%"v15" : W = phi("start" => #1, "L10" => %"v13")]:
    => br %"v15" ? "L5" : "L7";
  @"L5":
    => ret #22;
  @"L7":
    call %"v17" : P = $"zthread_self_cookie"();
    %"v20" = %"v17" +p #792;
    %"chk0" : A = (Check 0 4 Read 1) %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L22";
  @"L22" [%"pr.1" : W = phi("L7" => %"v21", "L71" => %"pr.2")]:
    %"v30" : W = (Cmp Eq W) %"v0", #1
    => br %"v30" ? "L26" : "L27";
  @"L26":
    %"v33" : W = Or %"pr.1", #1
    => goto "L28";
  @"L27":
    %"v37" : W = And %"pr.1", #4294967294
    => goto "L28";
  @"L28" [%"v38" : W = phi("L26" => %"v33", "L27" => %"v37")]:
    %"v43" : L = Ptoi %"v2";
    %"v44" : L = Ptoi #0;
    %"v45" : W = (Cmp Ne L) %"v43", %"v44"
    => br %"v45" ? "L39" : "L41";
  @"L39":
    %"v52" : W = And %"pr.1", #1
    => br %"v52" ? "L49" : "L48";
  @"L48":
    => goto "L49";
  @"L49" [%"v53" : W = phi("L48" => #0, "L39" => #1)]:
    %"chk1" : A = (Check 0 4 Write 1) %"v2";
    store Ww [%"chk1" + 0] <- %"v53"
    => goto "L41";
  @"L41":
    %"v59" : W = (Cmp Eq W) %"pr.1", %"v38"
    => br %"v59" ? "L24" : "L56";
  @"L56":
    %"v65" = %"v17" +p #792;
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v65";
    %"v68" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"pr.1", %"v38";
    %"v69" : W = (Cmp Eq W) %"v68", %"pr.1"
    => br %"v69" ? "L71" : "L70";
  @"L70":
    => goto "L71";
  @"L71" [%"pr.2" : W = phi("L56" => %"pr.1", "L70" => %"v68")]:
    => br %"v69" ? "iw_1.start" : poll "L22";
  @"iw_1.start":
    %"iw_1.v12" : W = And %"v38", #59;
    %"iw_1.v16" : W = (Cmp Eq W) %"iw_1.v12", #10
    => br %"iw_1.v16" ? "L72" : "L24";
  @"L72":
    (Flight (a "v80") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    call %"iw_2.v3" : P = $"zthread_self_cookie"();
    %"iw_2.v5" = %"iw_2.v3" +p #1608;
    %"chk3" : A = (Check 0 8 Write 8) %"iw_2.v5";
    store.ptr [%"chk3" + 0] <- %"v80";
    %"iw_2.v9" = %"iw_2.v3" +p #792;
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"iw_2.v9";
    %"iw_2.v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk4"
    => goto "iw_2.L12";
  @"iw_2.L12" [%"iw_2.pr.1" : W = phi("iw_2.L38" => %"iw_2.pr.2", "L72" => %"iw_2.v10")]:
    %"iw_2.v17" : W = Or %"iw_2.pr.1", #1;
    %"iw_2.v19" : W = Or %"iw_2.v17", #16;
    %"iw_2.v23" : W = And %"iw_2.v19", #4294967293;
    %"iw_2.v29" : W = (Cmp Eq W) %"iw_2.pr.1", %"iw_2.v23"
    => br %"iw_2.v29" ? "iw_2.L14" : "iw_2.L13";
  @"iw_2.L13":
    %"iw_2.v32" = %"iw_2.v3" +p #792;
    %"chk5" : A = (HalfCheck Lower 0 4 Write 4) %"chk3", %"iw_2.v32";
    %"iw_2.v35" : W = (RawCas (CasNarrow Sw) 0) %"chk5", %"iw_2.pr.1", %"iw_2.v23";
    %"iw_2.v36" : W = (Cmp Eq W) %"iw_2.v35", %"iw_2.pr.1"
    => br %"iw_2.v36" ? "iw_2.L38" : "iw_2.L37";
  @"iw_2.L37":
    => goto "iw_2.L38";
  @"iw_2.L38" [%"iw_2.pr.2" : W = phi("iw_2.L13" => %"iw_2.pr.1", "iw_2.L37" => %"iw_2.v35")]:
    %"iw_2.v39" : W = (Cmp Ne W) %"iw_2.v35", %"iw_2.pr.1"
    => br %"iw_2.v39" ? poll "iw_2.L12" : "iw_2.L14";
  @"iw_2.L14":
    %"iw_2.v41" = %"iw_2.v3" +p #784;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk3", %"iw_2.v41";
    %"iw_2.v42" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call void $"__GI___pthread_unwind"(P %"iw_2.v42")
    => goto "L24";
  @"L24":
    => ret #0
} }.
