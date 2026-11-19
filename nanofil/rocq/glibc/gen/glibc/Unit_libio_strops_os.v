(** This file defines checked IR from glibc’s `libio/strops.os` object.
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

Definition fn__IO_str_count : func :=
  ir_fn{ "export" "_IO_str_count"(P %"v0") -> (RClass L) {
  @"start":
    %"v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : W = (Cmp Ugt L) %"v11", %"v12"
    => br %"v13" ? "L2" : "L3";
  @"L2":
    %"v15" = %"v0" +p #40;
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L4";
  @"L3":
    %"v18" = %"v0" +p #16;
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L4";
  @"L4" [%"v20" : P = phi("L2" => %"v16", "L3" => %"v19")]:
    %"v22" = %"v0" +p #24;
    %"v23" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v24" : L = Ptoi %"v20";
    %"v25" : L = Ptoi %"v23";
    %"v26" : L = Sub %"v24", %"v25"
    => ret %"v26"
} }.

Definition fn__IO_str_finish : func :=
  ir_fn{ "export" "_IO_str_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v8" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" : L = Ptoi %"v9";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L12" : "L13";
  @"L12":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v15" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v16" : W = And %"v15", #1;
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => goto "L13";
  @"L13" [%"v19" : W = phi("start" => #0, "L12" => %"v17")]:
    => br %"v19" ? "L4" : "L6";
  @"L4":
    %"v21" = %"v0" +p #56;
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"free"(P %"v22")
    => goto "L6";
  @"L6":
    %"v24" = %"v0" +p #56;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v24";
    store.ptr [%"chk3" + 0] <- #0;
    call void $"__GI__IO_default_finish"(P %"v0", W #0)
    => ret void
} }.

Definition fn___GI__IO_str_overflow : func :=
  ir_fn{ "export" "__GI__IO_str_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v7" : W = (Cmp Eq W) %"v2", #4294967295;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v13" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v14" : W = And %"v13", #8
    => br %"v14" ? "L9" : "L11";
  @"L9":
    => br %"v7" ? "L17" : "L16";
  @"L16":
    => goto "L17";
  @"L17" [%"v20" : W = phi("L16" => #4294967295, "L9" => #0)]:
    => ret %"v20";
  @"L11":
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v27" : W = And %"v26", #1024
    => br %"v27" ? "L28" : "L29";
  @"L28":
    %"v31" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v32" : W = And %"v31", #2048;
    %"v33" : W = (Cmp Eq W) %"v32", #0
    => goto "L29";
  @"L29" [%"v35" : W = phi("L11" => #0, "L28" => %"v33")]:
    => br %"v35" ? "L22" : "L24";
  @"L22":
    %"v37" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v38" : W = Or %"v37", #2048;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk4" + 0] <- %"v38";
    %"v40" = %"v0" +p #40;
    %"v42" = %"v0" +p #8;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v40";
    store.ptr [%"chk6" + 0] <- %"v43";
    %"v47" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk5", %"v42";
    store.ptr [%"chk8" + 0] <- %"v48"
    => goto "L24";
  @"L24":
    %"v50" = %"v0" +p #40;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v53" = %"v0" +p #32;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v55" : L = Ptoi %"v51";
    %"v56" : L = Ptoi %"v54";
    %"v57" : L = Sub %"v55", %"v56";
    %"v63" = %"v0" +p #64;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v66" = %"v0" +p #56;
    %"v67" : P = (RawLoadPointer (-8) load_effects) %"chk11";
    %"v68" : L = Ptoi %"v64";
    %"v69" : L = Ptoi %"v67";
    %"v70" : L = Sub %"v68", %"v69";
    %"v72" : L = (Ext Sw) %"v7";
    %"v73" : L = Add %"v70", %"v72";
    %"v74" : W = (Cmp Uge L) %"v57", %"v73"
    => br %"v74" ? "L58" : "L60";
  @"L58":
    %"chk13" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v79" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v80" : W = And %"v79", #1
    => br %"v80" ? "L75" : "L76";
  @"L75":
    => ret #4294967295;
  @"L76":
    %"v86" = %"v0" +p #56;
    %"v87" : P = (RawLoadPointer (-8) load_effects) %"chk11";
    %"v90" = %"v0" +p #64;
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v94" : P = (RawLoadPointer (-8) load_effects) %"chk11";
    %"v95" : L = Ptoi %"v91";
    %"v96" : L = Ptoi %"v94";
    %"v97" : L = Sub %"v95", %"v96";
    %"v100" : L = Shl %"v97", #1;
    %"v101" : L = Add %"v100", #100;
    %"v107" : W = (Cmp Ult L) %"v101", %"v97"
    => br %"v107" ? "L102" : "L104";
  @"L102":
    => ret #4294967295;
  @"L104":
    call %"v111" : P = $"malloc"(L %"v101");
    %"v116" : L = Ptoi %"v111";
    %"v117" : L = Ptoi #0;
    %"v118" : W = (Cmp Eq L) %"v116", %"v117"
    => br %"v118" ? "L112" : "L114";
  @"L112":
    => ret #4294967295;
  @"L114":
    %"v125" : L = Ptoi %"v87";
    %"v126" : W = (Cmp Ne L) %"v125", #0
    => br %"v126" ? "L121" : "L123";
  @"L121":
    call %"v130" : P = $"__GI_memcpy"(P %"v111", P %"v87", L %"v97");
    call void $"free"(P %"v87");
    %"v133" = %"v0" +p #56;
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v133";
    store.ptr [%"chk17" + 0] <- #0
    => goto "L123";
  @"L123":
    %"v136" = %"v111" +p %"v97";
    %"v139" : L = Sub %"v101", %"v97";
    call %"v140" : P = $"__GI_memset"(P %"v136", W #0, L %"v139");
    %"v145" = %"v111" +p %"v101";
    call void $"__GI__IO_setb"(P %"v0", P %"v111", P %"v145", W #1);
    %"v147" = %"v0" +p #24;
    %"chk18" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v147";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v153" : L = Ptoi %"v151";
    %"v155" : L = Sub %"v153", %"v125";
    %"v156" = %"v111" +p %"v155";
    %"chk19" : A = (Renew 0 8 Write 8) %"chk18", %"v147";
    store.ptr [%"chk19" + 0] <- %"v156";
    %"v158" = %"v0" +p #8;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v158";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v164" : L = Ptoi %"v162";
    %"v166" : L = Sub %"v164", %"v125";
    %"v167" = %"v111" +p %"v166";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk20", %"v158";
    store.ptr [%"chk21" + 0] <- %"v167";
    %"v169" = %"v0" +p #16;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v169";
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v175" : L = Ptoi %"v173";
    %"v177" : L = Sub %"v175", %"v125";
    %"v178" = %"v111" +p %"v177";
    %"chk23" : A = (Renew 0 8 Write 8) %"chk22", %"v169";
    store.ptr [%"chk23" + 0] <- %"v178";
    %"v180" = %"v0" +p #40;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk9", %"v180";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v186" : L = Ptoi %"v184";
    %"v188" : L = Sub %"v186", %"v125";
    %"v189" = %"v111" +p %"v188";
    %"chk25" : A = (Renew 0 8 Write 8) %"chk9", %"v180";
    store.ptr [%"chk25" + 0] <- %"v189";
    %"v191" = %"v0" +p #32;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk10", %"v191";
    store.ptr [%"chk26" + 0] <- %"v111";
    %"v194" = %"v0" +p #48;
    %"v196" = %"v0" +p #64;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk11", %"v196";
    %"v197" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk28" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v194";
    store.ptr [%"chk28" + 0] <- %"v197"
    => goto "L60";
  @"L60":
    %"v202" : W = (Cmp Ne W) %"v2", #4294967295
    => br %"v202" ? "L198" : "L200";
  @"L198":
    %"v204" = %"v0" +p #40;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk9", %"v204";
    %"v205" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v206" = %"v205" +p #1;
    %"chk30" : A = (Renew 0 8 Write 8) %"chk9", %"v204";
    store.ptr [%"chk30" + 0] <- %"v206";
    %"v208" : W = (Ext Ub) %"v2";
    %"v209" : W = (Ext Sb) %"v208";
    %"chk31" : A = (Check 0 1 Write 1) %"v205";
    store Wb [%"chk31" + 0] <- %"v209"
    => goto "L200";
  @"L200":
    %"v214" = %"v0" +p #40;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk9", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v217" = %"v0" +p #16;
    %"chk33" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v217";
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v219" : L = Ptoi %"v215";
    %"v220" : L = Ptoi %"v218";
    %"v221" : W = (Cmp Ugt L) %"v219", %"v220"
    => br %"v221" ? "L210" : "L212";
  @"L210":
    %"v223" = %"v0" +p #16;
    %"v225" = %"v0" +p #40;
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk35" : A = (Renew 0 8 Write 8) %"chk33", %"v223";
    store.ptr [%"chk35" + 0] <- %"v226"
    => goto "L212";
  @"L212":
    => br %"v7" ? "L227" : "L228";
  @"L227":
    => ret #0;
  @"L228":
    => ret %"v2"
} }.

Definition fn___GI__IO_str_pbackfail : func :=
  ir_fn{ "export" "__GI__IO_str_pbackfail"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = And %"v8", #8
    => br %"v9" ? "L10" : "L11";
  @"L10":
    %"v14" : W = (Cmp Ne W) %"v2", #4294967295
    => goto "L11";
  @"L11" [%"v16" : W = phi("start" => #0, "L10" => %"v14")]:
    => br %"v16" ? "L4" : "L6";
  @"L4":
    => ret #4294967295;
  @"L6":
    call %"v21" : W = $"__GI__IO_default_pbackfail"(P %"v0", W %"v2")
    => ret %"v21"
} }.

Definition fn___GI__IO_str_seekoff : func :=
  ir_fn{ "export" "__GI__IO_str_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v13" : W = (Cmp Eq W) %"v6", #0
    => br %"v13" ? "L14" : "L15";
  @"L14":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v18" : W = And %"v17", #1024;
    %"v19" : W = (Cmp Ne W) %"v18", #0
    => goto "L15";
  @"L15" [%"v20" : W = phi("start" => #0, "L14" => %"v19")]:
    => br %"v20" ? "L9" : "L11";
  @"L9":
    %"chk1" : A = (Check 0 4 Read 1) %"v0";
    %"v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v26" : W = And %"v25", #2048
    => br %"v26" ? "L11" : "L22";
  @"L22":
    => goto "L11";
  @"L11" [%"pr.1" : W = phi("L22" => #1, "L9" => #2, "L15" => %"v6")]:
    %"v30" = %"v0" +p #40;
    %"chk2" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v33" = %"v0" +p #32;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v35" : L = Ptoi %"v31";
    %"v36" : L = Ptoi %"v34";
    %"v37" : W = (Cmp Ugt L) %"v35", %"v36"
    => br %"v37" ? "L39" : "L38";
  @"L38":
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk2", %"v0";
    %"v41" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v42" : W = And %"v41", #2048;
    %"v43" : W = (Cmp Ne W) %"v42", #0
    => goto "L39";
  @"L39" [%"v44" : W = phi("L11" => #1, "L38" => %"v43")]:
    => br %"v44" ? "iw_1.start" : "L48";
  @"iw_1.start":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk2", %"v0";
    %"iw_1.v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"iw_1.v7" : W = And %"iw_1.v6", #256
    => br %"iw_1.v7" ? "iw_1.L2" : "iw_1.L3";
  @"iw_1.L2":
    %"iw_1.v9" = %"v0" +p #24;
    %"iw_1.v11" = %"v0" +p #80;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"iw_1.v9";
    store.ptr [%"chk7" + 0] <- %"iw_1.v12"
    => goto "iw_1.L4";
  @"iw_1.L3":
    %"iw_1.v14" = %"v0" +p #24;
    %"iw_1.v16" = %"v0" +p #56;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"iw_1.v16";
    %"iw_1.v17" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"iw_1.v14";
    store.ptr [%"chk9" + 0] <- %"iw_1.v17";
    %"iw_1.v22" = %"v0" +p #40;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v22";
    %"iw_1.v23" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v25" = %"v0" +p #16;
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"iw_1.v25";
    %"iw_1.v26" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v27" : L = Ptoi %"iw_1.v23";
    %"iw_1.v28" : L = Ptoi %"iw_1.v26";
    %"iw_1.v29" : W = (Cmp Ugt L) %"iw_1.v27", %"iw_1.v28"
    => br %"iw_1.v29" ? "iw_1.L18" : "iw_1.L4";
  @"iw_1.L18":
    %"iw_1.v31" = %"v0" +p #16;
    %"iw_1.v33" = %"v0" +p #40;
    %"iw_1.v34" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk13" : A = (Renew 0 8 Write 8) %"chk11", %"iw_1.v31";
    store.ptr [%"chk13" + 0] <- %"iw_1.v34"
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v36" = %"v0" +p #8;
    %"iw_1.v38" = %"v0" +p #16;
    %"iw_1.v40" = %"v0" +p #40;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"iw_1.v38";
    store.ptr [%"chk15" + 0] <- %"iw_1.v41";
    %"chk16" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"iw_1.v36";
    store.ptr [%"chk16" + 0] <- %"iw_1.v41";
    %"chk17" : A = (Renew 0 4 Read 1) %"chk5", %"v0";
    %"iw_1.v43" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"iw_1.v45" : W = And %"iw_1.v43", #4294965247;
    %"chk18" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk18" + 0] <- %"iw_1.v45"
    => goto "L48";
  @"L48":
    %"v55" : W = (Cmp Eq W) %"pr.1", #0
    => br %"v55" ? "L51" : "L52";
  @"L51":
    %"v57" = %"v0" +p #8;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v57";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v60" = %"v0" +p #24;
    %"chk20" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v62" : L = Ptoi %"v58";
    %"v63" : L = Ptoi %"v61";
    %"v64" : L = Sub %"v62", %"v63"
    => goto "L53";
  @"L52":
    call %"v67" : L = $"_IO_str_count"(P %"v0");
    %"v74" : W = And %"pr.1", #1
    => br %"v74" ? "L77" : "L72";
  @"L80":
    %"v82" = %"v0" +p #8;
    %"chk21" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v85" = %"v0" +p #24;
    %"chk22" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v85";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v87" : L = Ptoi %"v83";
    %"v88" : L = Ptoi %"v86";
    %"v89" : L = Sub %"v87", %"v88"
    => goto "L78";
  @"L77":
    %"v93" : W = (Cmp Eq W) %"v4", #0
    => br %"v93" ? "L78" : "L94";
  @"L94":
    %"v95" : W = (Cmp Eq W) %"v4", #1
    => br %"v95" ? poll "L80" : "L78";
  @"L78" [%"pr.5" : L = phi("L80" => %"v89", "L77" => #0, "L94" => %"v67")]:
    %"v99" : L = Sub #9223372036854775807, %"pr.5";
    %"v105" : L = Neg %"pr.5";
    %"v106" : W = (Cmp Slt L) %"v2", %"v105"
    => br %"v106" ? "L108" : "L107";
  @"L107":
    %"v111" : W = (Cmp Sgt L) %"v2", %"v99"
    => goto "L108";
  @"L108" [%"v113" : W = phi("L78" => #1, "L107" => %"v111")]:
    => br %"v113" ? "L100" : "L102";
  @"L100":
    %"v114" : P = Copy $"__libc_errno";
    %"chk23" : A = (Check 0 4 Write 1) %"v114";
    store Ww [%"chk23" + 0] <- #22
    => ret #18446744073709551615;
  @"L102":
    %"v120" : L = Add %"pr.5", %"v2";
    %"v126" : W = (Cmp Sgt L) %"v120", %"v67"
    => br %"v126" ? "L127" : "L128";
  @"L127":
    call %"v131" : W = $"glibc_strops#enlarge_userbuf"(P %"v0", L %"v120", W #1);
    %"v132" : W = (Cmp Ne W) %"v131", #0
    => goto "L128";
  @"L128" [%"v134" : W = phi("L102" => #0, "L127" => %"v132")]:
    => br %"v134" ? "L121" : "L123";
  @"L121":
    => ret #18446744073709551615;
  @"L123":
    %"v139" = %"v0" +p #8;
    %"v141" = %"v0" +p #24;
    %"chk24" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v141";
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v144" = %"v142" +p %"v120";
    %"chk25" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"v139";
    store.ptr [%"chk25" + 0] <- %"v144";
    %"v146" = %"v0" +p #16;
    %"chk26" : A = (Renew 0 8 Read 8) %"chk24", %"v141";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v151" = %"v149" +p %"v67";
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"v146";
    store.ptr [%"chk27" + 0] <- %"v151"
    => goto "L72";
  @"L72" [%"pr.4" : L = phi("L123" => %"v120", "L52" => #18446744073709551615)]:
    %"v157" : W = And %"pr.1", #2
    => br %"v157" ? "L160" : "L53";
  @"L163":
    %"v165" = %"v0" +p #40;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk2", %"v165";
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v168" = %"v0" +p #32;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk3", %"v168";
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v170" : L = Ptoi %"v166";
    %"v171" : L = Ptoi %"v169";
    %"v172" : L = Sub %"v170", %"v171"
    => goto "L161";
  @"L160":
    %"v176" : W = (Cmp Eq W) %"v4", #0
    => br %"v176" ? "L161" : "L177";
  @"L177":
    %"v178" : W = (Cmp Eq W) %"v4", #1
    => br %"v178" ? poll "L163" : "L161";
  @"L161" [%"pr.6" : L = phi("L163" => %"v172", "L160" => #0, "L177" => %"v67")]:
    %"v182" : L = Sub #9223372036854775807, %"pr.6";
    %"v188" : L = Neg %"pr.6";
    %"v189" : W = (Cmp Slt L) %"v2", %"v188"
    => br %"v189" ? "L191" : "L190";
  @"L190":
    %"v194" : W = (Cmp Sgt L) %"v2", %"v182"
    => goto "L191";
  @"L191" [%"v196" : W = phi("L161" => #1, "L190" => %"v194")]:
    => br %"v196" ? "L183" : "L185";
  @"L183":
    %"v197" : P = Copy $"__libc_errno";
    %"chk30" : A = (Check 0 4 Write 1) %"v197";
    store Ww [%"chk30" + 0] <- #22
    => ret #18446744073709551615;
  @"L185":
    %"v203" : L = Add %"pr.6", %"v2";
    %"v209" : W = (Cmp Sgt L) %"v203", %"v67"
    => br %"v209" ? "L210" : "L211";
  @"L210":
    call %"v214" : W = $"glibc_strops#enlarge_userbuf"(P %"v0", L %"v203", W #0);
    %"v215" : W = (Cmp Ne W) %"v214", #0
    => goto "L211";
  @"L211" [%"v217" : W = phi("L185" => #0, "L210" => %"v215")]:
    => br %"v217" ? "L204" : "L206";
  @"L204":
    => ret #18446744073709551615;
  @"L206":
    %"v222" = %"v0" +p #40;
    %"v224" = %"v0" +p #32;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk3", %"v224";
    %"v225" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v227" = %"v225" +p %"v203";
    %"chk32" : A = (Renew 0 8 Write 8) %"chk2", %"v222";
    store.ptr [%"chk32" + 0] <- %"v227"
    => goto "L53";
  @"L53" [%"pr.3" : L = phi("L51" => %"v64", "L206" => %"v203", "L72" => %"pr.4")]:
    => ret %"pr.3"
} }.

Definition fn___GI__IO_str_underflow : func :=
  ir_fn{ "export" "__GI__IO_str_underflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : W = (Cmp Ugt L) %"v11", %"v12"
    => br %"v13" ? "L2" : "L4";
  @"L2":
    %"v15" = %"v0" +p #16;
    %"v17" = %"v0" +p #40;
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk3" : A = (Renew 0 8 Write 8) %"chk1", %"v15";
    store.ptr [%"chk3" + 0] <- %"v18"
    => goto "L4";
  @"L4":
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v23" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v24" : W = And %"v23", #1024
    => br %"v24" ? "L25" : "L26";
  @"L25":
    %"v28" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v29" : W = And %"v28", #2048;
    %"v30" : W = (Cmp Ne W) %"v29", #0
    => goto "L26";
  @"L26" [%"v31" : W = phi("L4" => #0, "L25" => %"v30")]:
    => br %"v31" ? "L19" : "L21";
  @"L19":
    %"v33" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v35" : W = And %"v33", #4294965247;
    %"chk7" : A = (Renew 0 4 Write 1) %"chk4", %"v0";
    store Ww [%"chk7" + 0] <- %"v35";
    %"v37" = %"v0" +p #8;
    %"v39" = %"v0" +p #40;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v37";
    store.ptr [%"chk9" + 0] <- %"v40";
    %"v44" = %"v0" +p #48;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Renew 0 8 Write 8) %"chk0", %"v39";
    store.ptr [%"chk11" + 0] <- %"v45"
    => goto "L21";
  @"L21":
    %"v50" = %"v0" +p #8;
    %"chk12" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v53" = %"v0" +p #16;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk1", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v55" : L = Ptoi %"v51";
    %"v56" : L = Ptoi %"v54";
    %"v57" : W = (Cmp Ult L) %"v55", %"v56"
    => br %"v57" ? "L46" : "L47";
  @"L46":
    %"v59" = %"v0" +p #8;
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk15" : A = (Check 0 1 Read 1) %"v60";
    %"v61" : W = (RawLoad (LdNarrow Ub) 0) %"chk15"
    => ret %"v61";
  @"L47":
    => ret #4294967295
} }.

Definition fn_glibc_strops'23enlarge_userbuf : func :=
  ir_fn{ "local" "glibc_strops#enlarge_userbuf"(P %"v0", L %"v2", W %"v4") -> (RClass W) {
  @"start":
    %"v11" = %"v0" +p #64;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" = %"v0" +p #56;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v16" : L = Ptoi %"v12";
    %"v17" : L = Ptoi %"v15";
    %"v18" : L = Sub %"v16", %"v17";
    %"v19" : W = (Cmp Sle L) %"v2", %"v18"
    => br %"v19" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"v23" = %"v0" +p #48;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v26" = %"v0" +p #32;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v28" : L = Ptoi %"v24";
    %"v29" : L = Ptoi %"v27";
    %"v30" : L = Sub %"v28", %"v29";
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v36" : W = And %"v35", #1
    => br %"v36" ? "L31" : "L33";
  @"L31":
    => ret #1;
  @"L33":
    %"v40" : L = Add %"v2", #100;
    %"v43" = %"v0" +p #56;
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v47" : P = $"malloc"(L %"v40");
    %"v52" : L = Ptoi %"v47";
    %"v53" : L = Ptoi #0;
    %"v54" : W = (Cmp Eq L) %"v52", %"v53"
    => br %"v54" ? "L48" : "L50";
  @"L48":
    => ret #1;
  @"L50":
    %"v60" : L = Ptoi %"v44";
    %"v62" : W = (Cmp Ne L) %"v60", %"v53"
    => br %"v62" ? "L56" : "L58";
  @"L56":
    %"v66" = %"v0" +p #64;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v69" = %"v0" +p #56;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v71" : L = Ptoi %"v67";
    %"v72" : L = Ptoi %"v70";
    %"v73" : L = Sub %"v71", %"v72";
    call %"v74" : P = $"__GI_memcpy"(P %"v47", P %"v44", L %"v73");
    call void $"free"(P %"v44");
    %"chk8" : A = (Renew 0 8 Write 8) %"chk1", %"v69";
    store.ptr [%"chk8" + 0] <- #0
    => goto "L58";
  @"L58":
    %"v82" = %"v47" +p %"v40";
    call void $"__GI__IO_setb"(P %"v0", P %"v47", P %"v82", W #1)
    => br %"v4" ? "L83" : "L84";
  @"L83":
    %"v88" = %"v0" +p #32;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk3", %"v88";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v94" : L = Ptoi %"v92";
    %"v96" : L = Sub %"v94", %"v60";
    %"v97" = %"v47" +p %"v96";
    %"chk10" : A = (Renew 0 8 Write 8) %"chk3", %"v88";
    store.ptr [%"chk10" + 0] <- %"v97";
    %"v99" = %"v0" +p #40;
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v99";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v105" : L = Ptoi %"v103";
    %"v107" : L = Sub %"v105", %"v60";
    %"v108" = %"v47" +p %"v107";
    %"chk12" : A = (Renew 0 8 Write 8) %"chk11", %"v99";
    store.ptr [%"chk12" + 0] <- %"v108";
    %"v110" = %"v0" +p #48;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"v110";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v116" : L = Ptoi %"v114";
    %"v118" : L = Sub %"v116", %"v60";
    %"v119" = %"v47" +p %"v118";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk2", %"v110";
    store.ptr [%"chk14" + 0] <- %"v119";
    %"v121" = %"v0" +p #8;
    %"chk15" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v121";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v127" : L = Ptoi %"v125";
    %"v129" : L = Sub %"v127", %"v60";
    %"v130" = %"v47" +p %"v129";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk15", %"v121";
    store.ptr [%"chk16" + 0] <- %"v130";
    %"v132" = %"v0" +p #24;
    %"chk17" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v132";
    store.ptr [%"chk17" + 0] <- %"v47";
    %"v135" = %"v0" +p #16;
    %"v137" = %"v0" +p #64;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v135";
    store.ptr [%"chk19" + 0] <- %"v138"
    => goto "L85";
  @"L84":
    %"v140" = %"v0" +p #24;
    %"chk20" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v140";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v146" : L = Ptoi %"v144";
    %"v148" : L = Sub %"v146", %"v60";
    %"v149" = %"v47" +p %"v148";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk20", %"v140";
    store.ptr [%"chk21" + 0] <- %"v149";
    %"v151" = %"v0" +p #8;
    %"chk22" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v151";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v157" : L = Ptoi %"v155";
    %"v159" : L = Sub %"v157", %"v60";
    %"v160" = %"v47" +p %"v159";
    %"chk23" : A = (Renew 0 8 Write 8) %"chk22", %"v151";
    store.ptr [%"chk23" + 0] <- %"v160";
    %"v162" = %"v0" +p #16;
    %"chk24" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v162";
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v168" : L = Ptoi %"v166";
    %"v170" : L = Sub %"v168", %"v60";
    %"v171" = %"v47" +p %"v170";
    %"chk25" : A = (Renew 0 8 Write 8) %"chk24", %"v162";
    store.ptr [%"chk25" + 0] <- %"v171";
    %"v173" = %"v0" +p #40;
    %"chk26" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v173";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v179" : L = Ptoi %"v177";
    %"v181" : L = Sub %"v179", %"v60";
    %"v182" = %"v47" +p %"v181";
    %"chk27" : A = (Renew 0 8 Write 8) %"chk26", %"v173";
    store.ptr [%"chk27" + 0] <- %"v182";
    %"v184" = %"v0" +p #32;
    %"chk28" : A = (Renew 0 8 Write 8) %"chk3", %"v184";
    store.ptr [%"chk28" + 0] <- %"v47";
    %"v187" = %"v0" +p #48;
    %"v189" = %"v0" +p #64;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v189";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (Renew 0 8 Write 8) %"chk2", %"v187";
    store.ptr [%"chk30" + 0] <- %"v190"
    => goto "L85";
  @"L85":
    %"v196" : W = (Cmp Sge L) %"v2", %"v30"
    => br %"v196" ? "L193" : "L192";
  @"L192":
    %"v197" : P = Copy $"glibc_strops#str.257";
    %"v198" : P = Copy $"glibc_strops#str.258";
    %"v199" : P = Copy $"glibc_strops#str.259";
    call void $"__libc_assert_fail"(P %"v197", P %"v198", W #225, P %"v199")
    => goto "L193";
  @"L193":
    => br %"v4" ? "L200" : "L201";
  @"L200":
    %"v205" = %"v0" +p #24;
    %"chk31" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v205";
    %"v206" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v208" = %"v206" +p %"v30";
    %"v211" : L = Sub %"v2", %"v30";
    call %"v212" : P = $"__GI_memset"(P %"v208", W #0, L %"v211")
    => goto "L202";
  @"L201":
    %"v214" = %"v0" +p #32;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk3", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v217" = %"v215" +p %"v30";
    %"v220" : L = Sub %"v2", %"v30";
    call %"v221" : P = $"__GI_memset"(P %"v217", W #0, L %"v220")
    => goto "L202";
  @"L202":
    => ret #0
} }.

Definition item_glibc_strops'23str'2e257 : item :=
  (IData (a "glibc_strops#str.257") (LRo (a "local")) 1 [(Item Wb 111); (Item Wb 102); (Item Wb 102); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 111); (Item Wb 108); (Item Wb 100); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_strops'23str'2e258 : item :=
  (IData (a "glibc_strops#str.258") (LRo (a "local")) 1 [(Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 111); (Item Wb 112); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_strops'23str'2e259 : item :=
  (IData (a "glibc_strops#str.259") (LRo (a "local")) 1 [(Item Wb 101); (Item Wb 110); (Item Wb 108); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 101); (Item Wb 95); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 0)]).
