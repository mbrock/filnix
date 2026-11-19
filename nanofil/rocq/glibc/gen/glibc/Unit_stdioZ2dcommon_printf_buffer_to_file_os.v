(** This file defines checked IR from glibc’s `stdio-common/printf_buffer_to_file.os` object.
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

Definition fn___printf_buffer_flush_to_file : func :=
  ir_fn{ "export" "__printf_buffer_flush_to_file"(P %"v0") -> RVoid {
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
    %"v18" = %"v0" +p #16;
    %"v19" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v21" = %"v0" +p #48;
    %"v25" = %"v21" +p #128;
    %"v26" : L = Ptoi %"v19";
    %"v27" : L = Ptoi %"v25";
    %"v28" : W = (Cmp Eq L) %"v26", %"v27"
    => br %"v28" ? "L14" : "L15";
  @"L14":
    %"v31" = %"v0" +p #8;
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v34" = %"v0" +p #48;
    %"v35" : L = Ptoi %"v32";
    %"v36" : L = Ptoi %"v34";
    %"v37" : L = Sub %"v35", %"v36";
    %"v42" = %"v0" +p #40;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v44" = %"v43" +p #216;
    %"chk7" : A = (Check 0 8 Read 8) %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v4" : L = Ptoi %"v45";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v47" = %"v45" +p #56;
    %"chk8" : A = (Check 0 8 Read 8) %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v50" = %"v0" +p #40;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk6", %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v53" = %"v0" +p #48;
    %"chk10" : F = CheckFunction %"v48";
    rawcall %"v55" : L = %"chk10"(P %"v51", P %"v53", L %"v37");
    %"v57" : W = (Cmp Ne L) %"v55", %"v37"
    => br %"v57" ? "iw_2.start" : "L40";
  @"iw_2.start":
    %"iw_2.v3" = %"v0" +p #32;
    %"chk11" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_2.v3";
    store Ww [%"chk11" + 0] <- #0
    => ret void;
  @"L40":
    call void $"__printf_buffer_to_file_switch"(P %"v0")
    => ret void;
  @"L15":
    %"v66" = %"v0" +p #16;
    %"v67" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v69" = %"v0" +p #48;
    %"v70" = %"v69" +p #1;
    %"v71" : L = Ptoi %"v67";
    %"v72" : L = Ptoi %"v70";
    %"v73" : W = (Cmp Eq L) %"v71", %"v72"
    => br %"v73" ? "L62" : "L16";
  @"L62":
    %"v78" = %"v0" +p #8;
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v81" = %"v0" +p #16;
    %"v82" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v83" : L = Ptoi %"v79";
    %"v84" : L = Ptoi %"v82";
    %"v85" : W = (Cmp Eq L) %"v83", %"v84"
    => br %"v85" ? "L74" : "L76";
  @"L74":
    %"v90" = %"v0" +p #40;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v93" = %"v0" +p #48;
    %"chk16" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v93";
    %"v94" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"v95" : W = (Ext Ub) %"v94";
    call %"v96" : W = $"__GI___overflow"(P %"v91", W %"v95");
    %"v98" : W = (Cmp Eq W) %"v96", #4294967295
    => br %"v98" ? "iw_3.start" : "L88";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk17" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_3.v3";
    store Ww [%"chk17" + 0] <- #0
    => ret void;
  @"L88":
    call void $"__printf_buffer_to_file_switch"(P %"v0")
    => goto "L76";
  @"L76":
    => ret void;
  @"L16":
    %"v107" = %"v0" +p #16;
    %"v108" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v110" = %"v0" +p #40;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v110";
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v112" = %"v111" +p #48;
    %"chk20" : A = (Check 0 8 Read 8) %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v114" : L = Ptoi %"v108";
    %"v115" : L = Ptoi %"v113";
    %"v116" : W = (Cmp Eq L) %"v114", %"v115"
    => br %"v116" ? "L105" : "L104";
  @"L104":
    %"v117" : P = Copy $"glibc_printf_buffer_to_file#str.266";
    %"v118" : P = Copy $"glibc_printf_buffer_to_file#str.267";
    %"v119" : P = Copy $"glibc_printf_buffer_to_file#str.268";
    call void $"__libc_assert_fail"(P %"v117", P %"v118", W #86, P %"v119")
    => goto "L105";
  @"L105":
    %"v121" = %"v0" +p #40;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk19", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v123" = %"v122" +p #40;
    %"v125" = %"v0" +p #8;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk1", %"v125";
    %"v126" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (Check 0 8 Write 8) %"v123";
    store.ptr [%"chk23" + 0] <- %"v126";
    %"chk24" : A = (Renew 0 8 Read 8) %"chk1", %"v125";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v134" = %"v0" +p #16;
    %"chk25" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v136" : L = Ptoi %"v132";
    %"v137" : L = Ptoi %"v135";
    %"v138" : W = (Cmp Eq L) %"v136", %"v137"
    => br %"v138" ? "L127" : "L129";
  @"L127":
    %"v140" = %"v0" +p #8;
    %"v142" = %"v0" +p #48;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk1", %"v140";
    store.ptr [%"chk26" + 0] <- %"v142";
    %"v144" = %"v0" +p #16;
    %"v147" = %"v142" +p #1;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk25", %"v144";
    store.ptr [%"chk27" + 0] <- %"v147"
    => goto "L129";
  @"L129":
    %"v150" = %"v0" +p #8;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk1", %"v150";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"chk29" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk29" + 0] <- %"v151"
    => ret void
} }.

Definition fn___printf_buffer_to_file_done : func :=
  ir_fn{ "export" "__printf_buffer_to_file_done"(P %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    call void $"__printf_buffer_flush_to_file"(P %"v0");
    call %"v12" : W = $"__printf_buffer_done"(P %"v0")
    => ret %"v12"
} }.

Definition fn___printf_buffer_to_file_init : func :=
  ir_fn{ "export" "__printf_buffer_to_file_init"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #48;
    %"iw_1.v12" = %"v6" +p #128;
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v6";
    %"iw_1.iw_1.v11" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v6";
    %"iw_1.iw_1.v14" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v12";
    %"iw_1.iw_1.v17" = %"v0" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.iw_1.v17";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.iw_1.v19" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.iw_1.v19";
    store Ww [%"chk4" + 0] <- #4;
    %"v11" = %"v0" +p #40;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v11";
    store.ptr [%"chk5" + 0] <- %"v2";
    call void $"__printf_buffer_to_file_switch"(P %"v0")
    => ret void
} }.

Definition fn___printf_buffer_to_file_switch : func :=
  ir_fn{ "export" "__printf_buffer_to_file_switch"(P %"v0") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" = %"v7" +p #40;
    %"chk1" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #48;
    %"chk3" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v15" : L = Ptoi %"v9";
    %"v16" : L = Ptoi %"v14";
    %"v17" : W = (Cmp Ult L) %"v15", %"v16"
    => br %"v17" ? "L2" : "L3";
  @"L2":
    %"v19" = %"v0" +p #8;
    %"v21" = %"v0" +p #40;
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v23" = %"v22" +p #40;
    %"chk5" : A = (Check 0 8 Read 8) %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v19";
    store.ptr [%"chk6" + 0] <- %"v24";
    %"v26" = %"v0" +p #16;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk0", %"v21";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v30" = %"v29" +p #48;
    %"chk8" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v26";
    store.ptr [%"chk9" + 0] <- %"v31"
    => goto "L4";
  @"L3":
    %"v33" = %"v0" +p #8;
    %"v35" = %"v0" +p #48;
    %"chk10" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v33";
    store.ptr [%"chk10" + 0] <- %"v35";
    %"v37" = %"v0" +p #16;
    %"v43" = %"v35" +p #128;
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v37";
    store.ptr [%"chk11" + 0] <- %"v43"
    => goto "L4";
  @"L4":
    %"v46" = %"v0" +p #8;
    %"chk12" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk13" + 0] <- %"v47"
    => ret void
} }.

Definition item_glibc_printf_buffer_to_file'23str'2e266 : item :=
  (IData (a "glibc_printf_buffer_to_file#str.266") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 46); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 102); (Item Wb 112); (Item Wb 45); (Item Wb 62); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_printf_buffer_to_file'23str'2e267 : item :=
  (IData (a "glibc_printf_buffer_to_file#str.267") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 116); (Item Wb 111); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_buffer_to_file'23str'2e268 : item :=
  (IData (a "glibc_printf_buffer_to_file#str.268") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 95); (Item Wb 116); (Item Wb 111); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).
