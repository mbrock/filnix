(** This file defines checked IR from glibc’s `libio/vasprintf.os` object.
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

Definition fn___printf_buffer_flush_asprintf : func :=
  ir_fn{ "export" "__printf_buffer_flush_asprintf"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v8" : L = Ptoi %"v5";
    %"v9" : L = Ptoi %"v7";
    %"v10" : L = Sub %"v8", %"v9";
    %"v15" : W = (Cmp Uge L) %"v10", #2147483647
    => br %"v15" ? "L11" : "L13";
  @"L11":
    %"v16" : P = Copy $"__libc_errno";
    %"chk2" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk2" + 0] <- #75;
    %"iw_1.v3" = %"v0" +p #32;
    %"chk3" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v3";
    store Ww [%"chk3" + 0] <- #0
    => ret void;
  @"L13":
    %"v21" = %"v0" +p #16;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" : L = Ptoi %"v22";
    %"v26" : L = Ptoi %"v24";
    %"v27" : L = Sub %"v25", %"v26";
    %"v31" : L = Shr %"v27", #1;
    %"v32" : L = Add %"v27", %"v31";
    %"v33" : L = Add %"v32", #16;
    %"v34" : L = Sub %"v33", #1;
    %"v36" : L = And %"v34", #18446744073709551600;
    %"v37" : L = Or %"v36", #8;
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v45" = %"v0" +p #40;
    %"v46" : L = Ptoi %"v43";
    %"v47" : L = Ptoi %"v45";
    %"v48" : W = (Cmp Eq L) %"v46", %"v47"
    => br %"v48" ? "L39" : "L40";
  @"L39":
    call %"v50" : P = $"malloc"(L %"v37");
    %"v55" : L = Ptoi %"v50";
    %"v56" : L = Ptoi #0;
    %"v57" : W = (Cmp Eq L) %"v55", %"v56"
    => br %"v57" ? "iw_2.start" : "L53";
  @"iw_2.start":
    %"iw_2.v3" = %"v0" +p #32;
    %"chk7" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_2.v3";
    store Ww [%"chk7" + 0] <- #0
    => ret void;
  @"L53":
    %"v62" = %"v0" +p #40;
    call %"v64" : P = $"__GI_memcpy"(P %"v50", P %"v62", L %"v10")
    => goto "L41";
  @"L40":
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v68" : P = $"realloc"(P %"v66", L %"v37");
    %"v73" : L = Ptoi %"v68";
    %"v74" : L = Ptoi #0;
    %"v75" : W = (Cmp Eq L) %"v73", %"v74"
    => br %"v75" ? "iw_3.start" : "L41";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk9" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_3.v3";
    store Ww [%"chk9" + 0] <- #0
    => ret void;
  @"L41" [%"pr.1" : P = phi("L53" => %"v50", "L40" => %"v68")]:
    %"chk10" : A = (Renew 0 8 Write 8) %"chk1", %"v0";
    store.ptr [%"chk10" + 0] <- %"pr.1";
    %"v81" = %"v0" +p #8;
    %"v84" = %"pr.1" +p %"v10";
    %"chk11" : A = (Renew 0 8 Write 8) %"chk0", %"v81";
    store.ptr [%"chk11" + 0] <- %"v84";
    %"v86" = %"v0" +p #16;
    %"v89" = %"pr.1" +p %"v37";
    %"chk12" : A = (Renew 0 8 Write 8) %"chk4", %"v86";
    store.ptr [%"chk12" + 0] <- %"v89"
    => ret void
} }.

Definition fn___vasprintf_internal : func :=
  ir_fn{ "export" "__vasprintf_internal"(P %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    %"v8" : P = (Alloc 8) #240;
    %"v9" = %"v8" +p #40;
    %"iw_1.v12" = %"v9" +p #200;
    %"chk0" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk0" + 0] <- %"v9";
    %"iw_1.iw_1.v11" = %"v8" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v9";
    %"iw_1.iw_1.v14" = %"v8" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v12";
    %"iw_1.iw_1.v17" = %"v8" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.iw_1.v17";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.iw_1.v19" = %"v8" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.iw_1.v19";
    store Ww [%"chk4" + 0] <- #5;
    call void $"__printf_buffer"(P %"v8", P %"v2", P %"v4", W %"v6");
    call %"v17" : W = $"__printf_buffer_done"(P %"v8");
    %"v22" : W = (Cmp Slt W) %"v17", #0
    => br %"v22" ? "L18" : "L20";
  @"L18":
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v8";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v27" = %"v8" +p #40;
    %"v28" : L = Ptoi %"v26";
    %"v29" : L = Ptoi %"v27";
    %"v30" : W = (Cmp Ne L) %"v28", %"v29"
    => br %"v30" ? "L23" : "L25";
  @"L23":
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call void $"free"(P %"v31")
    => goto "L25";
  @"L25":
    %"chk7" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk7" + 0] <- #0
    => ret %"v17";
  @"L20":
    %"v36" = %"v8" +p #8;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Renew 0 8 Read 8) %"chk0", %"v8";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v39" : L = Ptoi %"v37";
    %"v40" : L = Ptoi %"v38";
    %"v41" : L = Sub %"v39", %"v40";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v46" = %"v8" +p #40;
    %"v47" : L = Ptoi %"v45";
    %"v48" : L = Ptoi %"v46";
    %"v49" : W = (Cmp Eq L) %"v47", %"v48"
    => br %"v49" ? "L42" : "L43";
  @"L42":
    %"v52" : L = Add %"v41", #1;
    call %"v53" : P = $"malloc"(L %"v52");
    %"chk11" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk11" + 0] <- %"v53";
    %"chk12" : A = (Renew 0 8 Read 8) %"chk11", %"v0";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v59" : L = Ptoi %"v58";
    %"v60" : L = Ptoi #0;
    %"v61" : W = (Cmp Eq L) %"v59", %"v60"
    => br %"v61" ? "L54" : "L56";
  @"L54":
    => ret #4294967295;
  @"L56":
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v66" = %"v8" +p #40;
    call %"v68" : P = $"__GI_memcpy"(P %"v65", P %"v66", L %"v41")
    => goto "L44";
  @"L43":
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v72" : L = Add %"v41", #1;
    call %"v73" : P = $"realloc"(P %"v70", L %"v72");
    %"chk15" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk15" + 0] <- %"v73";
    %"chk16" : A = (Renew 0 8 Read 8) %"chk15", %"v0";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v79" : L = Ptoi %"v78";
    %"v80" : L = Ptoi #0;
    %"v81" : W = (Cmp Eq L) %"v79", %"v80"
    => br %"v81" ? "L74" : "L44";
  @"L74":
    %"chk17" : A = (Renew 0 8 Read 8) %"chk0", %"v8";
    %"v82" : P = (RawLoadPointer 0 load_effects) %"chk17";
    call void $"free"(P %"v82")
    => ret #4294967295;
  @"L44":
    %"chk18" : A = (Check 0 8 Read 8) %"v0";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v88" = %"v86" +p %"v41";
    %"chk19" : A = (Check 0 1 Write 1) %"v88";
    store Wb [%"chk19" + 0] <- #0
    => ret %"v17"
} }.
