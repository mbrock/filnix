(** This file defines checked IR from glibc’s `libio/obprintf.os` object.
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

Definition fn___printf_buffer_flush_obstack : func :=
  ir_fn{ "export" "__printf_buffer_flush_obstack"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 1) %"v3";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v6" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v10" : L = Ptoi %"v7";
    %"v11" : L = Ptoi %"v9";
    %"v12" : L = Sub %"v10", %"v11";
    %"v13" : L = Add %"v4", %"v12";
    %"chk3" : A = (Renew 0 8 Write 1) %"chk0", %"v3";
    store Wl [%"chk3" + 0] <- %"v13";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v21" = %"v0" +p #48;
    %"v22" = %"v21" +p #1;
    %"v23" : L = Ptoi %"v19";
    %"v24" : L = Ptoi %"v22";
    %"v25" : W = (Cmp Eq L) %"v23", %"v24"
    => br %"v25" ? "L14" : "L15";
  @"L14":
    %"v28" = %"v0" +p #40;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v34" = %"v29" +p #24;
    %"chk6" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v36" = %"v35" +p #1;
    %"v38" = %"v29" +p #32;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk6", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v40" : L = Ptoi %"v36";
    %"v41" : L = Ptoi %"v39";
    %"v42" : W = (Cmp Ugt L) %"v40", %"v41"
    => br %"v42" ? "L30" : "L32";
  @"L30":
    call void $"__GI__obstack_newchunk"(P %"v29", W #1)
    => goto "L32";
  @"L32":
    %"v45" = %"v29" +p #24;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk6", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v47" = %"v46" +p #1;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk6", %"v45";
    store.ptr [%"chk9" + 0] <- %"v47";
    %"v49" = %"v0" +p #48;
    %"chk10" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v49";
    %"v50" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"chk11" : A = (Check 0 1 Write 1) %"v46";
    store Wb [%"chk11" + 0] <- %"v50";
    %"v53" = %"v0" +p #40;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk5", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v55" = %"v54" +p #24;
    %"chk13" : A = (Check 0 8 Read 8) %"v55";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk14" + 0] <- %"v56";
    %"v58" = %"v0" +p #8;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk2", %"v0";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk1", %"v58";
    store.ptr [%"chk16" + 0] <- %"v60";
    %"chk17" : A = (Renew 0 8 Read 8) %"chk5", %"v53";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v67" = %"v65" +p #32;
    %"chk18" : A = (Check 0 8 Read 8) %"v67";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v70" = %"v65" +p #24;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk18", %"v70";
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v72" : L = Ptoi %"v68";
    %"v73" : L = Ptoi %"v71";
    %"v74" : L = Sub %"v72", %"v73";
    %"v75" : L = (Ext Uw) %"v74";
    %"v77" = %"v0" +p #16;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk1", %"v58";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v82" = %"v80" +p %"v75";
    %"chk21" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v77";
    store.ptr [%"chk21" + 0] <- %"v82";
    %"chk22" : A = (Renew 0 8 Read 8) %"chk5", %"v53";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v86" = %"v85" +p #24;
    %"chk23" : A = (Check 0 8 Read 8) %"v86";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v89" = %"v87" +p %"v75";
    %"chk24" : A = (Renew 0 8 Write 8) %"chk23", %"v86";
    store.ptr [%"chk24" + 0] <- %"v89"
    => goto "L16";
  @"L15":
    %"v92" = %"v0" +p #48;
    %"chk25" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk25" + 0] <- %"v92";
    %"v94" = %"v0" +p #8;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk1", %"v94";
    store.ptr [%"chk26" + 0] <- %"v92";
    %"v98" = %"v0" +p #16;
    %"v101" = %"v92" +p #1;
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v98";
    store.ptr [%"chk27" + 0] <- %"v101"
    => goto "L16";
  @"L16":
    => ret void
} }.
