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

Definition hi_fn_glibc_genops'23save_for_backup : func :=
  ir_fn{ "local" "glibc_genops#save_for_backup"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"iw_1.v7" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v7";
    %"iw_1.v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v9" : L = Ptoi %"v2";
    %"iw_1.v10" : L = Ptoi %"iw_1.v8";
    %"iw_1.v11" : L = Sub %"iw_1.v9", %"iw_1.v10";
    %"iw_1.v14" = %"v0" +p #96;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v14";
    %"iw_1.v15" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "iw_1.L16";
  @"iw_1.L16" [%"iw_1.pr.3" : P = phi("iw_1.L26" => %"iw_1.v38", "start" => %"iw_1.v15"); %"iw_1.pr.1" : L = phi("iw_1.L26" => %"iw_1.pr.2", "start" => %"iw_1.v11")]:
    %"iw_1.v21" : L = Ptoi %"iw_1.pr.3";
    %"iw_1.v22" : L = Ptoi #0;
    %"iw_1.v23" : W = (Cmp Ne L) %"iw_1.v21", %"iw_1.v22"
    => br %"iw_1.v23" ? "iw_1.L17" : "iw_1.join";
  @"iw_1.L17":
    %"iw_1.v28" = %"iw_1.pr.3" +p #16;
    %"chk2" : A = (Check 0 4 Read 1) %"iw_1.v28";
    %"iw_1.v29" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.v31" : L = (Ext Sw) %"iw_1.v29";
    %"iw_1.v32" : W = (Cmp Slt L) %"iw_1.v31", %"iw_1.pr.1"
    => br %"iw_1.v32" ? "iw_1.L24" : "iw_1.L26";
  @"iw_1.L24":
    %"iw_1.v34" = %"iw_1.pr.3" +p #16;
    %"iw_1.v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.v36" : L = (Ext Sw) %"iw_1.v35"
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.pr.2" : L = phi("iw_1.L24" => %"iw_1.v36", "iw_1.L17" => %"iw_1.pr.1")]:
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"iw_1.pr.3";
    %"iw_1.v38" : P = (RawLoadPointer 0 load_effects) %"chk4"
    => goto poll "iw_1.L16";
  @"iw_1.join":
    %"v11" = %"v0" +p #24;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v14" : L = Ptoi %"v12";
    %"v15" : L = Sub %"iw_1.v9", %"v14";
    %"v17" : L = Sub %"v15", %"iw_1.pr.1";
    %"v20" = %"v0" +p #88;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v23" = %"v0" +p #72;
    %"v24" : P = (RawLoadPointer (-16) load_effects) %"chk6";
    %"v25" : L = Ptoi %"v21";
    %"v26" : L = Ptoi %"v24";
    %"v27" : L = Sub %"v25", %"v26";
    %"v36" : W = (Cmp Ugt L) %"v17", %"v27"
    => br %"v36" ? "L31" : "L32";
  @"L31":
    %"v40" : L = Add %"v17", #100;
    call %"v41" : P = $"malloc"(L %"v40");
    %"v46" : L = Ptoi %"v41";
    %"v48" : W = (Cmp Eq L) %"v46", %"iw_1.v22"
    => br %"v48" ? "L42" : "L44";
  @"L42":
    => ret #4294967295;
  @"L44":
    %"v55" : W = (Cmp Slt L) %"iw_1.pr.1", #0
    => br %"v55" ? "L51" : "L52";
  @"L51":
    %"v58" = %"v41" +p #100;
    %"v60" = %"v0" +p #88;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk6", %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v63" = %"v61" +p %"iw_1.pr.1";
    %"v65" : L = Neg %"iw_1.pr.1";
    call %"v66" : P = $"__GI_mempcpy"(P %"v58", P %"v63", L %"v65");
    %"v68" = %"v0" +p #24;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk0", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v75" : L = Ptoi %"v73";
    %"v76" : L = Sub %"iw_1.v9", %"v75";
    call %"v77" : P = $"__GI_mempcpy"(P %"v66", P %"v69", L %"v76")
    => goto "L53";
  @"L52":
    %"v80" = %"v41" +p #100;
    %"v82" = %"v0" +p #24;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk0", %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v85" = %"v83" +p %"iw_1.pr.1";
    call %"v87" : P = $"__GI_memcpy"(P %"v80", P %"v85", L %"v17")
    => goto "L53";
  @"L53":
    %"v90" = %"v0" +p #72;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_2.v9" = %"v0" +p #119;
    %"iw_2.v10" : L = Ptoi %"v91";
    %"iw_2.v11" : L = Ptoi %"iw_2.v9";
    %"iw_2.v12" : W = (Cmp Ne L) %"iw_2.v10", %"iw_2.v11"
    => br %"iw_2.v12" ? "iw_2.L4" : "iw_2.join";
  @"iw_2.L4":
    call void $"free"(P %"v91")
    => goto "iw_2.join";
  @"iw_2.join":
    %"v93" = %"v0" +p #72;
    %"chk13" : A = (Renew 0 8 Write 8) %"chk12", %"v93";
    store.ptr [%"chk13" + 0] <- %"v41";
    %"v96" = %"v0" +p #88;
    %"v99" = %"v41" +p #100;
    %"v101" = %"v99" +p %"v17";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk6", %"v96";
    store.ptr [%"chk14" + 0] <- %"v101"
    => goto "L33";
  @"L32":
    %"v104" : L = Sub %"v27", %"v17";
    %"v109" : W = (Cmp Slt L) %"iw_1.pr.1", #0
    => br %"v109" ? "L105" : "L106";
  @"L105":
    %"v111" = %"v0" +p #72;
    %"v112" : P = (RawLoadPointer (-16) load_effects) %"chk6";
    %"v114" = %"v112" +p %"v104";
    %"v116" = %"v0" +p #88;
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v119" = %"v117" +p %"iw_1.pr.1";
    %"v121" : L = Neg %"iw_1.pr.1";
    call %"v122" : P = $"__GI_memmove"(P %"v114", P %"v119", L %"v121");
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v111";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v127" = %"v125" +p %"v104";
    (Flight (a "v129") Sub [(FAddress (t "v127")); (FValue (t "iw_1.pr.1"))] (LowerOf (t "v127")));
    %"v131" = %"v0" +p #24;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"v131";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v138" : L = Ptoi %"v136";
    %"v139" : L = Sub %"iw_1.v9", %"v138";
    call %"v140" : P = $"__GI_memcpy"(P %"v129", P %"v132", L %"v139")
    => goto "L33";
  @"L106":
    %"v145" : W = (Cmp Ugt L) %"v17", #0
    => br %"v145" ? "L141" : "L33";
  @"L141":
    %"v147" = %"v0" +p #72;
    %"v148" : P = (RawLoadPointer (-16) load_effects) %"chk6";
    %"v150" = %"v148" +p %"v104";
    %"v152" = %"v0" +p #24;
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v155" = %"v153" +p %"iw_1.pr.1";
    call %"v157" : P = $"__GI_memcpy"(P %"v150", P %"v155", L %"v17")
    => goto "L33";
  @"L33" [%"pr.1" : L = phi("iw_2.join" => #100, "L105" => %"v104", "L141" => %"v104", "L106" => %"v104")]:
    %"v159" = %"v0" +p #80;
    %"v161" = %"v0" +p #72;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v161";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v164" = %"v162" +p %"pr.1";
    %"chk23" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v159";
    store.ptr [%"chk23" + 0] <- %"v164";
    %"v167" = %"v0" +p #24;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"v167";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v170" : L = Ptoi %"v168";
    %"v171" : L = Sub %"iw_1.v9", %"v170";
    %"v173" = %"v0" +p #96;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk1", %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk25"
    => goto "L175";
  @"L175" [%"pr.2" : P = phi("L176" => %"v190", "L33" => %"v174")]:
    %"v180" : L = Ptoi %"pr.2";
    %"v182" : W = (Cmp Ne L) %"v180", %"iw_1.v22"
    => br %"v182" ? "L176" : "L178";
  @"L176":
    %"v184" = %"pr.2" +p #16;
    %"chk26" : A = (Check 0 4 Read 1) %"v184";
    %"v185" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v187" : L = (Ext Sw) %"v185";
    %"v188" : L = Sub %"v187", %"v171";
    %"chk27" : A = (Renew 0 4 Write 1) %"chk26", %"v184";
    store Ww [%"chk27" + 0] <- %"v188";
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk26", %"pr.2";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk28"
    => goto poll "L175";
  @"L178":
    => ret #0
} }.
