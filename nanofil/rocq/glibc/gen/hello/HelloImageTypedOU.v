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

Definition hello_image_fn_glibc_vfprintf_internal'23outstring_converted_wide_string : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#outstring_converted_wide_string"(P %"v0", P %"v2", W %"v4", W %"v6", W %"v8") -> RVoid {
  @"start":
    %"v3" : P = (Alloc 8) #8;
    %"v10" : P = (Alloc 4) #256;
    %"v22" : P = (Alloc 4) #8;
    %"v24" : P = (Alloc 8) #8;
    %"v94" : P = (Alloc 4) #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v3";
    store.ptr [%"chk0" + 0] <- %"v2";
    %"v15" : W = (Cmp Sgt W) %"v6", #0
    => br %"v15" ? "L16" : "L17";
  @"L16":
    %"v18" : W = (Ext Ub) %"v8";
    %"v19" : W = (Cmp Eq W) %"v18", #0
    => goto "L17";
  @"L17" [%"v21" : W = phi("start" => #0, "L16" => %"v19")]:
    => br %"v21" ? "L11" : "L13";
  @"L11":
    %"chk1" : A = (Check 0 4 Write 1) %"v22";
    store Ww [%"chk1" + 0] <- #0;
    %"v23" = %"v22" +p #4;
    %"chk2" : A = (HalfCheck Upper 0 4 Write 1) %"chk1", %"v23";
    store Ww [%"chk2" + 0] <- #0;
    store Ww [%"chk1" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v3";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk5" + 0] <- %"v25";
    %"v31" : W = (Cmp Slt W) %"v4", #0
    => br %"v31" ? "L27" : "L28";
  @"L27":
    call %"v32" : L = $"__wcsrtombs"(P #0, P %"v24", L #0, P %"v22")
    => goto "L29";
  @"L28":
    %"v35" : L = (Ext Sw) %"v4"
    => goto "L36";
  @"L36" [%"pr.3" : L = phi("L28" => %"v35", "L71" => %"v80"); %"pr.2" : L = phi("L28" => #0, "L71" => %"v77")]:
    %"v40" : W = (Cmp Ugt L) %"pr.3", #0
    => br %"v40" ? "L41" : "L42";
  @"L41":
    %"chk6" : A = (Renew 0 8 Read 8) %"chk5", %"v24";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v44" : L = Ptoi %"v43";
    %"v45" : L = Ptoi #0;
    %"v46" : W = (Cmp Ne L) %"v44", %"v45"
    => goto "L42";
  @"L42" [%"v48" : W = phi("L36" => #0, "L41" => %"v46")]:
    => br %"v48" ? "L37" : "L29";
  @"L37":
    %"v55" : W = (Cmp Ult L) %"pr.3", #256
    => br %"v55" ? "L52" : "L51";
  @"L51":
    => goto "L52";
  @"L52" [%"pr.4" : L = phi("L51" => #256, "L37" => %"pr.3")]:
    call %"v59" : L = $"__wcsrtombs"(P %"v10", P %"v24", L %"pr.4", P %"v22");
    %"v66" : W = (Cmp Eq L) %"v59", #18446744073709551615
    => br %"v66" ? "iw_1.start" : "L62";
  @"iw_1.start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk7" : A = (Check 0 4 Write 1) %"iw_1.v3";
    store Ww [%"chk7" + 0] <- #0
    => ret void;
  @"L62":
    %"v73" : W = (Cmp Eq L) %"v59", #0
    => br %"v73" ? "L29" : "L71";
  @"L71":
    %"v77" : L = Add %"pr.2", %"v59";
    %"v80" : L = Sub %"pr.3", %"v59"
    => goto poll "L36";
  @"L29" [%"pr.1" : L = phi("L27" => %"v32", "L42" => %"pr.2", "L62" => %"pr.2")]:
    %"v84" : L = (Ext Sw) %"v6";
    %"v85" : L = Sub %"v84", %"pr.1";
    %"iw_2.v10" : W = (Cmp Sgt L) %"v85", #0
    => br %"iw_2.v10" ? "iw_2.L6" : "iw_3.start";
  @"iw_2.L6":
    call void $"__printf_buffer_pad_1"(P %"v0", W #32, L %"v85")
    => goto "iw_3.start";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk8" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L86" : "L13";
  @"L86":
    => ret void;
  @"L13":
    %"chk9" : A = (Check 0 4 Write 1) %"v94";
    store Ww [%"chk9" + 0] <- #0;
    %"v95" = %"v94" +p #4;
    %"chk10" : A = (HalfCheck Upper 0 4 Write 1) %"chk9", %"v95";
    store Ww [%"chk10" + 0] <- #0;
    store Ww [%"chk9" + 0] <- #0;
    %"v103" : W = (Cmp Sge W) %"v4", #0
    => br %"v103" ? "L99" : "L106";
  @"L99":
    %"v105" : L = (Ext Sw) %"v4"
    => goto "L106";
  @"L106" [%"pr.7" : L = phi("L99" => %"v105", "L13" => #18446744073709551615, "L150" => %"v157", "L141" => %"pr.7"); %"pr.5" : L = phi("L99" => #0, "L13" => #0, "L150" => %"v149", "L141" => %"v149")]:
    %"v110" : W = (Cmp Ugt L) %"pr.7", #0
    => br %"v110" ? "L111" : "L112";
  @"L111":
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v3";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v114" : L = Ptoi %"v113";
    %"v115" : L = Ptoi #0;
    %"v116" : W = (Cmp Ne L) %"v114", %"v115"
    => goto "L112";
  @"L112" [%"v118" : W = phi("L106" => #0, "L111" => %"v116")]:
    => br %"v118" ? "L107" : "L108";
  @"L107":
    %"v125" : W = (Cmp Ult L) %"pr.7", #256
    => br %"v125" ? "L122" : "L121";
  @"L121":
    => goto "L122";
  @"L122" [%"pr.9" : L = phi("L121" => #256, "L107" => %"pr.7")]:
    call %"v129" : L = $"__wcsrtombs"(P %"v10", P %"v3", L %"pr.9", P %"v94");
    %"v136" : W = (Cmp Eq L) %"v129", #18446744073709551615
    => br %"v136" ? "iw_4.start" : "L132";
  @"iw_4.start":
    %"iw_4.v3" = %"v0" +p #32;
    %"chk13" : A = (Check 0 4 Write 1) %"iw_4.v3";
    store Ww [%"chk13" + 0] <- #0
    => ret void;
  @"L132":
    %"v143" : W = (Cmp Eq L) %"v129", #0
    => br %"v143" ? "L108" : "L141";
  @"L141":
    call void $"__printf_buffer_write"(P %"v0", P %"v10", L %"v129");
    %"v149" : L = Add %"pr.5", %"v129"
    => br %"v103" ? "L150" : poll "L106";
  @"L150":
    %"v157" : L = Sub %"pr.7", %"v129"
    => goto poll "L106";
  @"L108":
    => br %"v15" ? "L163" : "L164";
  @"L163":
    %"v165" : W = (Ext Ub) %"v8";
    %"v166" : W = (Cmp Ne W) %"v165", #0
    => goto "L164";
  @"L164" [%"v167" : W = phi("L108" => #0, "L163" => %"v166")]:
    => br %"v167" ? "L158" : "L160";
  @"L158":
    %"v171" : L = (Ext Sw) %"v6";
    %"v172" : L = Sub %"v171", %"pr.5";
    %"iw_5.v10" : W = (Cmp Sgt L) %"v172", #0
    => br %"iw_5.v10" ? "iw_5.L6" : "L160";
  @"iw_5.L6":
    call void $"__printf_buffer_pad_1"(P %"v0", W #32, L %"v172")
    => goto "L160";
  @"L160":
    => ret void
} }.

Definition hello_image_fn_glibc_vfwprintf_internal'23outstring_converted_wide_string : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#outstring_converted_wide_string"(P %"v0", P %"v2", W %"v4", W %"v6", W %"v8") -> RVoid {
  @"start":
    %"v3" : P = (Alloc 8) #8;
    %"v10" : P = (Alloc 4) #256;
    %"v22" : P = (Alloc 4) #8;
    %"v24" : P = (Alloc 8) #8;
    %"v94" : P = (Alloc 4) #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v3";
    store.ptr [%"chk0" + 0] <- %"v2";
    %"v15" : W = (Cmp Sgt W) %"v6", #0
    => br %"v15" ? "L16" : "L17";
  @"L16":
    %"v18" : W = (Ext Ub) %"v8";
    %"v19" : W = (Cmp Eq W) %"v18", #0
    => goto "L17";
  @"L17" [%"v21" : W = phi("start" => #0, "L16" => %"v19")]:
    => br %"v21" ? "L11" : "L13";
  @"L11":
    %"chk1" : A = (Check 0 4 Write 1) %"v22";
    store Ww [%"chk1" + 0] <- #0;
    %"v23" = %"v22" +p #4;
    %"chk2" : A = (HalfCheck Upper 0 4 Write 1) %"chk1", %"v23";
    store Ww [%"chk2" + 0] <- #0;
    store Ww [%"chk1" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v3";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk5" + 0] <- %"v25";
    %"v31" : W = (Cmp Slt W) %"v4", #0
    => br %"v31" ? "L27" : "L28";
  @"L27":
    call %"v32" : L = $"__mbsrtowcs"(P #0, P %"v24", L #0, P %"v22")
    => goto "L29";
  @"L28":
    %"v35" : L = (Ext Sw) %"v4"
    => goto "L36";
  @"L36" [%"pr.3" : L = phi("L28" => %"v35", "L71" => %"v80"); %"pr.2" : L = phi("L28" => #0, "L71" => %"v77")]:
    %"v40" : W = (Cmp Ugt L) %"pr.3", #0
    => br %"v40" ? "L41" : "L42";
  @"L41":
    %"chk6" : A = (Renew 0 8 Read 8) %"chk5", %"v24";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v44" : L = Ptoi %"v43";
    %"v45" : L = Ptoi #0;
    %"v46" : W = (Cmp Ne L) %"v44", %"v45"
    => goto "L42";
  @"L42" [%"v48" : W = phi("L36" => #0, "L41" => %"v46")]:
    => br %"v48" ? "L37" : "L29";
  @"L37":
    %"v55" : W = (Cmp Ult L) %"pr.3", #64
    => br %"v55" ? "L52" : "L51";
  @"L51":
    => goto "L52";
  @"L52" [%"pr.4" : L = phi("L51" => #64, "L37" => %"pr.3")]:
    call %"v59" : L = $"__mbsrtowcs"(P %"v10", P %"v24", L %"pr.4", P %"v22");
    %"v66" : W = (Cmp Eq L) %"v59", #18446744073709551615
    => br %"v66" ? "iw_1.start" : "L62";
  @"iw_1.start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk7" : A = (Check 0 4 Write 1) %"iw_1.v3";
    store Ww [%"chk7" + 0] <- #0
    => ret void;
  @"L62":
    %"v73" : W = (Cmp Eq L) %"v59", #0
    => br %"v73" ? "L29" : "L71";
  @"L71":
    %"v77" : L = Add %"pr.2", %"v59";
    %"v80" : L = Sub %"pr.3", %"v59"
    => goto poll "L36";
  @"L29" [%"pr.1" : L = phi("L27" => %"v32", "L42" => %"pr.2", "L62" => %"pr.2")]:
    %"v84" : L = (Ext Sw) %"v6";
    %"v85" : L = Sub %"v84", %"pr.1";
    %"iw_2.v10" : W = (Cmp Sgt L) %"v85", #0
    => br %"iw_2.v10" ? "iw_2.L6" : "iw_3.start";
  @"iw_2.L6":
    call void $"__wprintf_buffer_pad_1"(P %"v0", W #32, L %"v85")
    => goto "iw_3.start";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk8" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L86" : "L13";
  @"L86":
    => ret void;
  @"L13":
    %"chk9" : A = (Check 0 4 Write 1) %"v94";
    store Ww [%"chk9" + 0] <- #0;
    %"v95" = %"v94" +p #4;
    %"chk10" : A = (HalfCheck Upper 0 4 Write 1) %"chk9", %"v95";
    store Ww [%"chk10" + 0] <- #0;
    store Ww [%"chk9" + 0] <- #0;
    %"v103" : W = (Cmp Sge W) %"v4", #0
    => br %"v103" ? "L99" : "L106";
  @"L99":
    %"v105" : L = (Ext Sw) %"v4"
    => goto "L106";
  @"L106" [%"pr.7" : L = phi("L99" => %"v105", "L13" => #18446744073709551615, "L150" => %"v157", "L141" => %"pr.7"); %"pr.5" : L = phi("L99" => #0, "L13" => #0, "L150" => %"v149", "L141" => %"v149")]:
    %"v110" : W = (Cmp Ugt L) %"pr.7", #0
    => br %"v110" ? "L111" : "L112";
  @"L111":
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v3";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v114" : L = Ptoi %"v113";
    %"v115" : L = Ptoi #0;
    %"v116" : W = (Cmp Ne L) %"v114", %"v115"
    => goto "L112";
  @"L112" [%"v118" : W = phi("L106" => #0, "L111" => %"v116")]:
    => br %"v118" ? "L107" : "L108";
  @"L107":
    %"v125" : W = (Cmp Ult L) %"pr.7", #64
    => br %"v125" ? "L122" : "L121";
  @"L121":
    => goto "L122";
  @"L122" [%"pr.9" : L = phi("L121" => #64, "L107" => %"pr.7")]:
    call %"v129" : L = $"__mbsrtowcs"(P %"v10", P %"v3", L %"pr.9", P %"v94");
    %"v136" : W = (Cmp Eq L) %"v129", #18446744073709551615
    => br %"v136" ? "iw_4.start" : "L132";
  @"iw_4.start":
    %"iw_4.v3" = %"v0" +p #32;
    %"chk13" : A = (Check 0 4 Write 1) %"iw_4.v3";
    store Ww [%"chk13" + 0] <- #0
    => ret void;
  @"L132":
    %"v143" : W = (Cmp Eq L) %"v129", #0
    => br %"v143" ? "L108" : "L141";
  @"L141":
    call void $"__wprintf_buffer_write"(P %"v0", P %"v10", L %"v129");
    %"v149" : L = Add %"pr.5", %"v129"
    => br %"v103" ? "L150" : poll "L106";
  @"L150":
    %"v157" : L = Sub %"pr.7", %"v129"
    => goto poll "L106";
  @"L108":
    => br %"v15" ? "L163" : "L164";
  @"L163":
    %"v165" : W = (Ext Ub) %"v8";
    %"v166" : W = (Cmp Ne W) %"v165", #0
    => goto "L164";
  @"L164" [%"v167" : W = phi("L108" => #0, "L163" => %"v166")]:
    => br %"v167" ? "L158" : "L160";
  @"L158":
    %"v171" : L = (Ext Sw) %"v6";
    %"v172" : L = Sub %"v171", %"pr.5";
    %"iw_5.v10" : W = (Cmp Sgt L) %"v172", #0
    => br %"iw_5.v10" ? "iw_5.L6" : "L160";
  @"iw_5.L6":
    call void $"__wprintf_buffer_pad_1"(P %"v0", W #32, L %"v172")
    => goto "L160";
  @"L160":
    => ret void
} }.
