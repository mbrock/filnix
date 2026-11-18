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

Definition hello_image_fn__IO_mem_finish : func :=
  ir_fn{ "export" "_IO_mem_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v7" = %"v0" +p #240;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v0" +p #32;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" = %"v0" +p #40;
    %"v14" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v18" : L = Ptoi %"v14";
    %"v19" : L = Ptoi %"v17";
    %"v20" : L = Sub %"v18", %"v19";
    %"v21" : L = Add %"v20", #1;
    call %"v22" : P = $"realloc"(P %"v11", L %"v21");
    %"chk4" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk4" + 0] <- %"v22";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v7";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Read 8) %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v30" : L = Ptoi %"v29";
    %"v31" : L = Ptoi #0;
    %"v32" : W = (Cmp Ne L) %"v30", %"v31"
    => br %"v32" ? "L23" : "L25";
  @"L23":
    %"v34" = %"v0" +p #240;
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk8" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v38" = %"v0" +p #40;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v41" = %"v0" +p #32;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v43" : L = Ptoi %"v39";
    %"v44" : L = Ptoi %"v42";
    %"v45" : L = Sub %"v43", %"v44";
    %"v46" = %"v36" +p %"v45";
    %"chk11" : A = (Check 0 1 Write 1) %"v46";
    store Wb [%"chk11" + 0] <- #0;
    %"v48" = %"v0" +p #248;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v56" : L = Ptoi %"v52";
    %"v57" : L = Ptoi %"v55";
    %"v58" : L = Sub %"v56", %"v57";
    %"chk15" : A = (Check 0 8 Write 1) %"v49";
    store Wl [%"chk15" + 0] <- %"v58";
    %"v60" = %"v0" +p #56;
    %"chk16" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v60";
    store.ptr [%"chk16" + 0] <- #0
    => goto "L25";
  @"L25":
    call void $"_IO_str_finish"(P %"v0", W #0)
    => ret void
} }.

Definition hello_image_fn__IO_mem_setbuf : func :=
  ir_fn{ "export" "_IO_mem_setbuf"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    => ret %"v0"
} }.

Definition hello_image_fn__IO_mem_doallocate : func :=
  ir_fn{ "export" "_IO_mem_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    => ret #1
} }.

Definition hello_image_fn_glibc_stdfiles'23_IO_stdfiles_init : func :=
  ir_fn{ "local" "glibc_stdfiles#_IO_stdfiles_init"() -> RVoid {
  @"start":
    %"v1" : P = Copy $"__GI__IO_list_all"
    => goto "L2";
  @"L2" [%"pr.1" : P = phi("L3" => %"v17", "start" => %"v1")]:
    %"chk0" : A = (Check 0 8 Read 8) %"pr.1";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" : L = Ptoi %"v7";
    %"v9" : L = Ptoi #0;
    %"v10" : W = (Cmp Ne L) %"v8", %"v9"
    => br %"v10" ? "L3" : "L5";
  @"L3":
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #184;
    %"chk2" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk2" + 0] <- %"pr.1";
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"pr.1";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v17" = %"v16" +p #104
    => goto poll "L2";
  @"L5":
    => ret void
} }.

Definition hello_image_fn___GI__IO_str_overflow : func :=
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

Definition hello_image_fn___GI__IO_str_underflow : func :=
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

Definition hello_image_fn__IO_str_count : func :=
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

Definition hello_image_fn___GI__IO_str_seekoff : func :=
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

Definition hello_image_fn___GI__IO_str_pbackfail : func :=
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

Definition hello_image_fn__IO_str_finish : func :=
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

Definition hello_image_fn__IO_vtable_check : func :=
  ir_fn{ "export" "_IO_vtable_check"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_vtables#str.302";
    call void $"__GI___libc_fatal"(P %"v0")
    => ret void
} }.

Definition hello_image_fn__IO_wfile_doallocate : func :=
  ir_fn{ "export" "_IO_wfile_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" : L = Ptoi %"v9";
    %"v11" : L = Ptoi #0;
    %"v12" : W = (Cmp Eq L) %"v10", %"v11"
    => br %"v12" ? "L4" : "L6";
  @"L4":
    call %"v14" : W = $"__GI__IO_file_doallocate"(P %"v0")
    => goto "L6";
  @"L6":
    %"v16" = %"v0" +p #64;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v19" = %"v0" +p #56;
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v21" : L = Ptoi %"v17";
    %"v22" : L = Ptoi %"v20";
    %"v23" : L = Sub %"v21", %"v22";
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v28" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v29" : W = And %"v28", #1
    => br %"v29" ? "L24" : "L26";
  @"L24":
    %"v31" : L = Add %"v23", #4;
    %"v32" : L = Sub %"v31", #1;
    %"v33" : L = Shr %"v32", #2
    => goto "L26";
  @"L26" [%"pr.1" : L = phi("L24" => %"v33", "L6" => %"v23")]:
    %"v35" : L = Shl %"pr.1", #2;
    call %"v36" : P = $"malloc"(L %"v35");
    %"v41" : L = Ptoi %"v36";
    %"v43" : W = (Cmp Eq L) %"v41", %"v11"
    => br %"v43" ? "L37" : "L39";
  @"L37":
    => ret #4294967295;
  @"L39":
    %"v53" = %"v36" +p %"v35";
    call void $"__GI__IO_wsetb"(P %"v0", P %"v36", P %"v53", W #1)
    => ret #1
} }.

Definition hello_image_fn___GI__IO_wdo_write : func :=
  ir_fn{ "export" "__GI__IO_wdo_write"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v64" : P = (Alloc 8) #8;
    %"v65" : P = (Alloc 4) #16;
    %"v67" : P = (Alloc 8) #8;
    %"v8" = %"v0" +p #152;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : W = (Cmp Ugt L) %"v4", #0
    => br %"v14" ? "L10" : "L12";
  @"L10":
    %"v19" = %"v0" +p #48;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v22" = %"v0" +p #40;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v24" : L = Ptoi %"v20";
    %"v25" : L = Ptoi %"v23";
    %"v26" : W = (Cmp Eq L) %"v24", %"v25"
    => br %"v26" ? "L27" : "L28";
  @"L27":
    %"v30" = %"v0" +p #48;
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v33" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v35" : L = Ptoi %"v31";
    %"v36" : L = Ptoi %"v34";
    %"v37" : W = (Cmp Ne L) %"v35", %"v36"
    => goto "L28";
  @"L28" [%"v39" : W = phi("L10" => #0, "L27" => %"v37")]:
    => br %"v39" ? "L15" : "L60";
  @"L15":
    %"v45" = %"v0" +p #32;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v48" = %"v0" +p #40;
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v53" : L = Ptoi %"v49";
    %"v54" : L = Ptoi %"v52";
    %"v55" : L = Sub %"v53", %"v54";
    call %"v56" : W = $"_IO_new_do_write"(P %"v0", P %"v46", L %"v55");
    %"v58" : W = (Cmp Eq W) %"v56", #4294967295
    => br %"v58" ? "L40" : "L60";
  @"L40":
    => ret #(-1);
  @"L60" [%"pr.3" : L = phi("L129" => %"v126", "L15" => %"v4", "L28" => %"v4"); %"pr.1" : P = phi("L129" => %"v150", "L15" => %"v2", "L28" => %"v2")]:
    %"v73" = %"v0" +p #64;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v73";
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v76" = %"v0" +p #40;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk2", %"v76";
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v78" : L = Ptoi %"v74";
    %"v79" : L = Ptoi %"v77";
    %"v80" : L = Sub %"v78", %"v79";
    %"v81" : W = (Cmp Ult L) %"v80", #16
    => br %"v81" ? "L69" : "L70";
  @"L69":
    %"chk10" : A = (Check 0 8 Write 8) %"v67";
    store.ptr [%"chk10" + 0] <- %"v65";
    %"v82" = %"v65" +p #16
    => goto "L71";
  @"L70":
    %"v84" = %"v0" +p #40;
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk12" : A = (Check 0 8 Write 8) %"v67";
    store.ptr [%"chk12" + 0] <- %"v85";
    %"v87" = %"v0" +p #32;
    %"chk13" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v90" = %"v0" +p #64;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk8", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk14"
    => goto "L71";
  @"L71" [%"pr.5" : P = phi("L69" => %"v82", "L70" => %"v91"); %"pr.4" : P = phi("L69" => %"v65", "L70" => %"v88")]:
    %"v94" = %"v0" +p #160;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v94";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v96" = %"v95" +p #88;
    %"v100" : L = Shl %"pr.3", #2;
    %"v101" = %"pr.1" +p %"v100";
    %"chk16" : A = (Check 0 8 Read 8) %"v67";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk16";
    call %"v104" : W = $"__libio_codecvt_out"(P %"v9", P %"v96", P %"pr.1", P %"v101", P %"v64", P %"v102", P %"pr.5", P %"v67");
    %"chk17" : A = (Renew 0 8 Read 8) %"chk16", %"v67";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v112" : L = Ptoi %"v110";
    %"v113" : L = Ptoi %"pr.4";
    %"v114" : L = Sub %"v112", %"v113";
    call %"v115" : W = $"_IO_new_do_write"(P %"v0", P %"pr.4", L %"v114");
    %"v117" : W = (Cmp Eq W) %"v115", #4294967295
    => br %"v117" ? "L105" : "L107";
  @"L105":
    => ret #(-1);
  @"L107":
    %"chk18" : A = (Check 0 8 Read 8) %"v64";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v122" : L = Ptoi %"v120";
    %"v123" : L = Ptoi %"pr.1";
    %"v124" : L = Sub %"v122", %"v123";
    %"v125" : L = Div %"v124", #4;
    %"v126" : L = Sub %"pr.3", %"v125";
    %"v131" : W = (Cmp Ne W) %"v104", #0
    => br %"v131" ? "L132" : "L133";
  @"L132":
    %"v135" : W = (Cmp Ne W) %"v104", #1
    => br %"v135" ? "L133" : "L136";
  @"L136":
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v140" : L = Ptoi %"v138";
    %"v142" : L = Sub %"v140", %"v123";
    %"v143" : L = Div %"v142", #4;
    %"v144" : W = (Cmp Eq L) %"v143", #0
    => goto "L133";
  @"L133" [%"v148" : W = phi("L107" => #0, "L132" => #1, "L136" => %"v144")]:
    => br %"v148" ? "L12" : "L129";
  @"L129":
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v152" : W = (Cmp Ugt L) %"v126", #0
    => br %"v152" ? poll "L60" : "L12";
  @"L12" [%"pr.2" : L = phi("L129" => %"v126", "L133" => %"v126", "start" => %"v4")]:
    %"v154" = %"v0" +p #160;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v154";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v156" = %"v155" +p #16;
    %"v159" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v160" = %"v159" +p #48;
    %"chk23" : A = (Check 0 8 Read 8) %"v160";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Check 0 8 Write 8) %"v156";
    store.ptr [%"chk24" + 0] <- %"v161";
    %"chk25" : A = (Renew 0 8 Read 8) %"chk21", %"v154";
    %"v164" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v168" = %"v167" +p #48;
    %"chk27" : A = (Check 0 8 Read 8) %"v168";
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk28" : A = (Check 0 8 Write 8) %"v164";
    store.ptr [%"chk28" + 0] <- %"v169";
    %"chk29" : A = (Renew 0 8 Read 8) %"chk21", %"v154";
    %"v172" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v173" = %"v172" +p #8;
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v177" = %"v176" +p #48;
    %"chk31" : A = (Check 0 8 Read 8) %"v177";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Check 0 8 Write 8) %"v173";
    store.ptr [%"chk32" + 0] <- %"v178";
    %"chk33" : A = (Renew 0 8 Read 8) %"chk21", %"v154";
    %"v181" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v182" = %"v181" +p #24;
    %"v185" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v186" = %"v185" +p #32;
    %"v189" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v190" = %"v189" +p #48;
    %"chk36" : A = (Check 0 8 Read 8) %"v190";
    %"v191" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"chk37" : A = (Check 0 8 Write 8) %"v186";
    store.ptr [%"chk37" + 0] <- %"v191";
    %"chk38" : A = (Check 0 8 Write 8) %"v182";
    store.ptr [%"chk38" + 0] <- %"v191";
    %"chk39" : A = (Renew 0 8 Read 8) %"chk21", %"v154";
    %"v194" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v195" = %"v194" +p #40;
    %"chk40" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v200" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"v202" : W = And %"v200", #514
    => br %"v202" ? "L196" : "L197";
  @"L196":
    %"v204" = %"v0" +p #160;
    %"v205" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v206" = %"v205" +p #48;
    %"chk42" : A = (Check 0 8 Read 8) %"v206";
    %"v207" : P = (RawLoadPointer 0 load_effects) %"chk42"
    => goto "L198";
  @"L197":
    %"v209" = %"v0" +p #160;
    %"v210" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v211" = %"v210" +p #56;
    %"chk44" : A = (Check 0 8 Read 8) %"v211";
    %"v212" : P = (RawLoadPointer 0 load_effects) %"chk44"
    => goto "L198";
  @"L198" [%"v213" : P = phi("L196" => %"v207", "L197" => %"v212")]:
    %"chk45" : A = (Check 0 8 Write 8) %"v195";
    store.ptr [%"chk45" + 0] <- %"v213";
    %"v218" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v218" ? "L216" : "L215";
  @"L215":
    => goto "L216";
  @"L216" [%"v219" : W = phi("L215" => #4294967295, "L198" => #0)]:
    => ret %"v219"
} }.
