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

Definition hello_image_fn___vasprintf_internal : func :=
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
