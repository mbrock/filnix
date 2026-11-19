(** This file defines checked IR from glibc’s `stdio-common/reg-modifier.os` object.
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

Definition fn___handle_registered_modifier_mb : func :=
  ir_fn{ "export" "__handle_registered_modifier_mb"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v5" : P = Copy $"__printf_modifier_table";
    %"chk0" : A = (Check 0 8 Read 8) %"v5";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v0";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 1 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Ub) 0) %"chk2";
    %"v10" : L = (Ext Uw) %"v9";
    %"v11" : L = Shl %"v10", #3;
    %"v12" = %"v6" +p %"v11";
    %"chk3" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk3"
    => goto "L17";
  @"L17" [%"pr.6" : P = phi("L59" => %"pr.7", "start" => #0); %"pr.4" : W = phi("L59" => %"pr.5", "start" => #0); %"pr.2" : W = phi("L59" => %"pr.3", "start" => #0); %"pr.1" : P = phi("L59" => %"v87", "start" => %"v13")]:
    %"v21" : L = Ptoi %"pr.1";
    %"v22" : L = Ptoi #0;
    %"v23" : W = (Cmp Ne L) %"v21", %"v22"
    => br %"v23" ? "L18" : "L19";
  @"L18":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v27" = %"v26" +p #1;
    %"v30" = %"pr.1" +p #12
    => goto "L31";
  @"L31" [%"pr.9" : P = phi("L18" => %"v30", "L45" => %"v56"); %"pr.8" : P = phi("L18" => %"v27", "L45" => %"v54")]:
    %"chk5" : A = (Check 0 1 Read 1) %"pr.8";
    %"v35" : W = (RawLoad (LdNarrow Ub) 0) %"chk5";
    %"v36" : W = (Cmp Ne W) %"v35", #0
    => br %"v36" ? "L37" : "L38";
  @"L37":
    %"chk6" : A = (Check 0 4 Read 1) %"pr.9";
    %"v40" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v41" : W = (Cmp Ne W) %"v40", #0
    => goto "L38";
  @"L38" [%"v43" : W = phi("L31" => #0, "L37" => %"v41")]:
    => br %"v43" ? "L32" : "L33";
  @"L32":
    %"v48" : W = (RawLoad (LdNarrow Ub) 0) %"chk5";
    %"chk8" : A = (Check 0 4 Read 1) %"pr.9";
    %"v50" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v51" : W = (Cmp Ne W) %"v48", %"v50"
    => br %"v51" ? "L33" : "L45";
  @"L45":
    %"v54" = %"pr.8" +p #1;
    %"v56" = %"pr.9" +p #4
    => goto poll "L31";
  @"L33":
    %"chk9" : A = (Check 0 4 Read 1) %"pr.9";
    %"v61" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v62" : W = (Cmp Eq W) %"v61", #0
    => br %"v62" ? "L63" : "L64";
  @"L63":
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v68" : L = Ptoi %"pr.8";
    %"v69" : L = Ptoi %"v67";
    %"v70" : L = Sub %"v68", %"v69";
    %"v72" : L = (Ext Sw) %"pr.4";
    %"v73" : W = (Cmp Sgt L) %"v70", %"v72"
    => goto "L64";
  @"L64" [%"v75" : W = phi("L33" => #0, "L63" => %"v73")]:
    => br %"v75" ? "L57" : "L59";
  @"L57":
    %"chk11" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v80" : L = Ptoi %"pr.8";
    %"v81" : L = Ptoi %"v79";
    %"v82" : L = Sub %"v80", %"v81";
    %"v84" = %"pr.1" +p #8;
    %"chk12" : A = (Check 0 4 Read 1) %"v84";
    %"v85" : W = (RawLoad (LdNarrow Sw) 0) %"chk12"
    => goto "L59";
  @"L59" [%"pr.7" : P = phi("L57" => %"pr.8", "L64" => %"pr.6"); %"pr.5" : W = phi("L57" => %"v82", "L64" => %"pr.4"); %"pr.3" : W = phi("L57" => %"v85", "L64" => %"pr.2")]:
    %"chk13" : A = (Check 0 8 Read 8) %"pr.1";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk13"
    => goto poll "L17";
  @"L19":
    %"v92" : W = (Cmp Ne W) %"pr.2", #0
    => br %"v92" ? "L88" : "L90";
  @"L88":
    %"v94" = %"v2" +p #14;
    %"chk14" : A = (Check 0 2 Read 1) %"v94";
    %"v95" : W = (RawLoad (LdNarrow Uh) 0) %"chk14";
    %"v97" : W = Or %"v95", %"pr.2";
    %"v98" : W = (Ext Uh) %"v97";
    %"chk15" : A = (Renew 0 2 Write 1) %"chk14", %"v94";
    store Wh [%"chk15" + 0] <- %"v98";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk1", %"v0";
    store.ptr [%"chk16" + 0] <- %"pr.6"
    => ret #0;
  @"L90":
    => ret #1
} }.

Definition fn___handle_registered_modifier_wc : func :=
  ir_fn{ "export" "__handle_registered_modifier_wc"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v5" : P = Copy $"__printf_modifier_table";
    %"chk0" : A = (Check 0 8 Read 8) %"v5";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v0";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v10" : L = (Ext Uw) %"v9";
    %"v11" : L = Shl %"v10", #3;
    %"v12" = %"v6" +p %"v11";
    %"chk3" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk3"
    => goto "L17";
  @"L17" [%"pr.6" : P = phi("L59" => %"pr.7", "start" => #0); %"pr.4" : W = phi("L59" => %"pr.5", "start" => #0); %"pr.2" : W = phi("L59" => %"pr.3", "start" => #0); %"pr.1" : P = phi("L59" => %"v89", "start" => %"v13")]:
    %"v21" : L = Ptoi %"pr.1";
    %"v22" : L = Ptoi #0;
    %"v23" : W = (Cmp Ne L) %"v21", %"v22"
    => br %"v23" ? "L18" : "L19";
  @"L18":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v27" = %"v26" +p #4;
    %"v30" = %"pr.1" +p #12
    => goto "L31";
  @"L31" [%"pr.9" : P = phi("L18" => %"v30", "L45" => %"v56"); %"pr.8" : P = phi("L18" => %"v27", "L45" => %"v54")]:
    %"chk5" : A = (Check 0 4 Read 1) %"pr.8";
    %"v35" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v36" : W = (Cmp Ne W) %"v35", #0
    => br %"v36" ? "L37" : "L38";
  @"L37":
    %"chk6" : A = (Check 0 4 Read 1) %"pr.9";
    %"v40" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v41" : W = (Cmp Ne W) %"v40", #0
    => goto "L38";
  @"L38" [%"v43" : W = phi("L31" => #0, "L37" => %"v41")]:
    => br %"v43" ? "L32" : "L33";
  @"L32":
    %"v48" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"chk8" : A = (Check 0 4 Read 1) %"pr.9";
    %"v50" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v51" : W = (Cmp Ne W) %"v48", %"v50"
    => br %"v51" ? "L33" : "L45";
  @"L45":
    %"v54" = %"pr.8" +p #4;
    %"v56" = %"pr.9" +p #4
    => goto poll "L31";
  @"L33":
    %"chk9" : A = (Check 0 4 Read 1) %"pr.9";
    %"v61" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v62" : W = (Cmp Eq W) %"v61", #0
    => br %"v62" ? "L63" : "L64";
  @"L63":
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v68" : L = Ptoi %"pr.8";
    %"v69" : L = Ptoi %"v67";
    %"v70" : L = Sub %"v68", %"v69";
    %"v71" : L = Div %"v70", #4;
    %"v73" : L = (Ext Sw) %"pr.4";
    %"v74" : W = (Cmp Sgt L) %"v71", %"v73"
    => goto "L64";
  @"L64" [%"v76" : W = phi("L33" => #0, "L63" => %"v74")]:
    => br %"v76" ? "L57" : "L59";
  @"L57":
    %"chk11" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v81" : L = Ptoi %"pr.8";
    %"v82" : L = Ptoi %"v80";
    %"v83" : L = Sub %"v81", %"v82";
    %"v84" : L = Div %"v83", #4;
    %"v86" = %"pr.1" +p #8;
    %"chk12" : A = (Check 0 4 Read 1) %"v86";
    %"v87" : W = (RawLoad (LdNarrow Sw) 0) %"chk12"
    => goto "L59";
  @"L59" [%"pr.7" : P = phi("L57" => %"pr.8", "L64" => %"pr.6"); %"pr.5" : W = phi("L57" => %"v84", "L64" => %"pr.4"); %"pr.3" : W = phi("L57" => %"v87", "L64" => %"pr.2")]:
    %"chk13" : A = (Check 0 8 Read 8) %"pr.1";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk13"
    => goto poll "L17";
  @"L19":
    %"v94" : W = (Cmp Ne W) %"pr.2", #0
    => br %"v94" ? "L90" : "L92";
  @"L90":
    %"v96" = %"v2" +p #14;
    %"chk14" : A = (Check 0 2 Read 1) %"v96";
    %"v97" : W = (RawLoad (LdNarrow Uh) 0) %"chk14";
    %"v99" : W = Or %"v97", %"pr.2";
    %"v100" : W = (Ext Uh) %"v99";
    %"chk15" : A = (Renew 0 2 Write 1) %"chk14", %"v96";
    store Wh [%"chk15" + 0] <- %"v100";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk1", %"v0";
    store.ptr [%"chk16" + 0] <- %"pr.6"
    => ret #0;
  @"L92":
    => ret #1
} }.

Definition item___printf_modifier_table : item :=
  (IData (a "__printf_modifier_table") LExport 8 [(Zero 8)]).
