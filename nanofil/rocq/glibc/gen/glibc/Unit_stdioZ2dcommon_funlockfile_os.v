(** This file defines checked IR from glibc’s `stdio-common/funlockfile.os` object.
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

Definition item__IO_funlockfile : item :=
  (IAlias (a "_IO_funlockfile") (a "weak") (a "__GI___funlockfile")).

Definition fn___GI___funlockfile : func :=
  ir_fn{ "export" "__GI___funlockfile"(P %"v0") -> RVoid {
  @"start":
    %"v8" : P = Copy $"__libc_single_threaded_internal";
    %"chk0" : A = (Check 0 1 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v10" : W = (Cmp Ne W) %"v9", #0
    => br %"v10" ? "L11" : "L12";
  @"L11":
    %"v14" = %"v0" +p #136;
    %"chk1" : A = (Check 0 8 Read 8) %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v16" = %"v15" +p #4;
    %"chk2" : A = (Check 0 4 Read 1) %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v18" : W = (Cmp Eq W) %"v17", #0
    => goto "L12";
  @"L12" [%"v20" : W = phi("start" => #0, "L11" => %"v18")]:
    => br %"v20" ? "L5" : "L6";
  @"L5":
    %"v22" = %"v0" +p #136;
    %"chk3" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v24" = %"v23" +p #8;
    %"chk4" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk4" + 0] <- #0;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk3", %"v22";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 4 Write 1) %"v27";
    store Ww [%"chk6" + 0] <- #0
    => goto "L4";
  @"L6":
    %"v32" = %"v0" +p #136;
    %"chk7" : A = (Check 0 8 Read 8) %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v34" = %"v33" +p #4;
    %"chk8" : A = (Check 0 4 Read 1) %"v34";
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v36" : W = (Cmp Eq W) %"v35", #0
    => br %"v36" ? "L28" : "L29";
  @"L28":
    %"v38" = %"v0" +p #136;
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v40" = %"v39" +p #8;
    %"chk10" : A = (Check 0 8 Write 8) %"v40";
    store.ptr [%"chk10" + 0] <- #0;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk7", %"v38";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 4 Read 1) %"v44";
    %"v48" : W = (RawLoad (LdNarrow Sw) 0) %"chk12"
    => goto "L49";
  @"L49" [%"v51" : W = phi("L28" => %"v48", "L49" => %"v52")]:
    %"chk13" : A = (HalfCheck Lower 0 4 Write 4) %"chk12", %"v44";
    %"v52" : W = (RawCas (CasNarrow Sw) 0) %"chk13", %"v51", #0;
    %"v53" : W = (Cmp Eq W) %"v52", %"v51"
    => br %"v53" ? "L50" : poll "L49";
  @"L50":
    %"v58" : W = (Cmp Sgt W) %"v51", #1
    => br %"v58" ? "L61" : "L4";
  @"L61":
    call void $"__GI___lll_lock_wake_private"(P %"v44")
    => goto "L4";
  @"L29":
    %"v73" = %"v0" +p #136;
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v75" = %"v74" +p #4;
    %"chk15" : A = (Check 0 4 Read 1) %"v75";
    %"v76" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v77" : W = Sub %"v76", #1;
    %"chk16" : A = (Renew 0 4 Write 1) %"chk15", %"v75";
    store Ww [%"chk16" + 0] <- %"v77"
    => goto "L4";
  @"L4":
    => ret void
} }.
