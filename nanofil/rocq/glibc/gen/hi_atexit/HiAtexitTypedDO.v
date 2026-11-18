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

Definition hi_fn_glibc_dl_tunables'23do_tunable_update_val : func :=
  ir_fn{ "local" "glibc_dl_tunables#do_tunable_update_val"(P %"v0", P %"v2", P %"v4", P %"v6") -> RVoid {
  @"start":
    %"v15" = %"v0" +p #105;
    %"chk0" : A = (Check 0 1 Read 1) %"v15";
    %"v16" : W = (RawLoad (LdNarrow Ub) 0) %"chk0"
    => br %"v16" ? "L11" : "L13";
  @"L11":
    => ret void;
  @"L13":
    %"v19" = %"v0" +p #48;
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v19";
    %"v20" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v46" : W = (Cmp Eq W) %"v20", #3
    => br %"v46" ? "L23" : "L47";
  @"L23":
    %"v25" = %"v0" +p #88;
    %"chk2" : A = (Check 0 8 Read 8) %"v2";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v25";
    store.ptr [%"chk3" + 0] <- %"v27";
    %"v28" = %"v2" +p #8;
    %"v29" = %"v25" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 1) %"chk2", %"v28";
    %"v30" : L = (RawLoad LdL 0) %"chk4";
    %"chk5" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v29";
    store Wl [%"chk5" + 0] <- %"v30";
    %"v32" = %"v0" +p #104;
    %"chk6" : A = (HalfCheck Lower 0 1 Write 1) %"chk0", %"v32";
    store Wb [%"chk6" + 0] <- #1
    => ret void;
  @"L34":
    %"chk7" : A = (Check 0 8 Read 1) %"v2";
    %"v36" : L = (RawLoad LdL 0) %"chk7";
    %"v37" : L = (Ext Sw) %"v36"
    => goto "L22";
  @"L38":
    %"chk8" : A = (Check 0 8 Read 1) %"v2";
    %"v40" : L = (RawLoad LdL 0) %"chk8"
    => goto "L22";
  @"L41":
    %"chk9" : A = (Check 0 8 Read 1) %"v2";
    %"v43" : L = (RawLoad LdL 0) %"chk9"
    => goto "L22";
  @"L44":
    => unreachable;
  @"L47":
    %"v48" : W = (Cmp Eq W) %"v20", #0
    => br %"v48" ? poll "L34" : "L49";
  @"L49":
    %"v50" : W = (Cmp Eq W) %"v20", #1
    => br %"v50" ? poll "L38" : "L51";
  @"L51":
    %"v52" : W = (Cmp Eq W) %"v20", #2
    => br %"v52" ? poll "L41" : poll "L44";
  @"L22" [%"pr.1" : L = phi("L34" => %"v37", "L38" => %"v40", "L41" => %"v43")]:
    %"v56" = %"v0" +p #48;
    %"chk10" : A = (Renew 0 4 Read 1) %"chk1", %"v56";
    %"v57" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"iw_1.v13" : W = (Cmp Eq W) %"v57", #0
    => br %"iw_1.v13" ? "iw_1.join" : "iw_1.L14";
  @"iw_1.L14":
    %"iw_1.v15" : W = (Cmp Eq W) %"v57", #1
    => br %"iw_1.v15" ? "iw_1.join" : "iw_1.L16";
  @"iw_1.L16":
    %"iw_1.v17" : W = (Cmp Eq W) %"v57", #2
    => br %"iw_1.v17" ? "iw_1.join" : "iw_1.L18";
  @"iw_1.L18":
    %"iw_1.v19" : W = (Cmp Eq W) %"v57", #3
    => br %"iw_1.v19" ? "iw_1.L4" : "iw_1.L20";
  @"iw_1.L20":
    => goto "iw_1.L4";
  @"iw_1.L4":
    => unreachable;
  @"iw_1.join" [%"v58" : W = phi("L22" => #0, "iw_1.L14" => #1, "iw_1.L16" => #1)]:
    %"v64" : L = Ptoi %"v4";
    %"v65" : L = Ptoi #0;
    %"v66" : W = (Cmp Ne L) %"v64", %"v65"
    => br %"v66" ? "L60" : "L61";
  @"L60":
    %"chk11" : A = (Check 0 8 Read 1) %"v4";
    %"v68" : L = (RawLoad LdL 0) %"chk11"
    => goto "L62";
  @"L61":
    %"v70" = %"v0" +p #48;
    %"v71" = %"v70" +p #8;
    %"chk12" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v71";
    %"v72" : L = (RawLoad LdL 0) %"chk12"
    => goto "L62";
  @"L62" [%"v73" : L = phi("L60" => %"v68", "L61" => %"v72")]:
    %"v78" : L = Ptoi %"v6";
    %"v80" : W = (Cmp Ne L) %"v78", %"v65"
    => br %"v80" ? "L74" : "L75";
  @"L74":
    %"chk13" : A = (Check 0 8 Read 1) %"v6";
    %"v82" : L = (RawLoad LdL 0) %"chk13"
    => goto "L76";
  @"L75":
    %"v84" = %"v0" +p #48;
    %"v85" = %"v84" +p #16;
    %"chk14" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v85";
    %"v86" : L = (RawLoad LdL 0) %"chk14"
    => goto "L76";
  @"L76" [%"v87" : L = phi("L74" => %"v82", "L75" => %"v86")]:
    %"v93" = %"v0" +p #48;
    %"v94" = %"v93" +p #8;
    %"chk15" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v94";
    %"v95" : L = (RawLoad LdL 0) %"chk15"
    => br %"v58" ? "iw_2.L6" : "iw_2.L7";
  @"iw_2.L6":
    %"iw_2.v12" : W = (Cmp Ult L) %"v73", %"v95"
    => goto "iw_2.join";
  @"iw_2.L7":
    %"iw_2.v17" : W = (Cmp Slt L) %"v73", %"v95"
    => goto "iw_2.join";
  @"iw_2.join" [%"v97" : W = phi("iw_2.L6" => %"iw_2.v12", "iw_2.L7" => %"iw_2.v17")]:
    => br %"v97" ? "L88" : "L90";
  @"L88":
    %"v100" = %"v0" +p #48;
    %"v101" = %"v100" +p #8;
    %"v102" : L = (RawLoad LdL 0) %"chk15"
    => goto "L90";
  @"L90" [%"pr.3" : L = phi("L88" => %"v102", "iw_2.join" => %"v73")]:
    %"v108" = %"v0" +p #48;
    %"v109" = %"v108" +p #16;
    %"chk17" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v109";
    %"v110" : L = (RawLoad LdL 0) %"chk17"
    => br %"v58" ? "iw_3.L6" : "iw_3.L7";
  @"iw_3.L6":
    %"iw_3.v12" : W = (Cmp Ugt L) %"v87", %"v110"
    => goto "iw_3.join";
  @"iw_3.L7":
    %"iw_3.v17" : W = (Cmp Sgt L) %"v87", %"v110"
    => goto "iw_3.join";
  @"iw_3.join" [%"v112" : W = phi("iw_3.L6" => %"iw_3.v12", "iw_3.L7" => %"iw_3.v17")]:
    => br %"v112" ? "L103" : "L105";
  @"L103":
    %"v115" = %"v0" +p #48;
    %"v116" = %"v115" +p #16;
    %"v117" : L = (RawLoad LdL 0) %"chk17"
    => goto "L105";
  @"L105" [%"pr.4" : L = phi("L103" => %"v117", "iw_3.join" => %"v87")]:
    => br %"v58" ? "iw_4.L6" : "iw_4.L7";
  @"iw_4.L6":
    %"iw_4.v12" : W = (Cmp Ugt L) %"pr.3", %"pr.4"
    => goto "iw_4.join";
  @"iw_4.L7":
    %"iw_4.v17" : W = (Cmp Sgt L) %"pr.3", %"pr.4"
    => goto "iw_4.join";
  @"iw_4.join" [%"v124" : W = phi("iw_4.L6" => %"iw_4.v12", "iw_4.L7" => %"iw_4.v17")]:
    => br %"v124" ? "L118" : "L120";
  @"L118":
    %"v127" = %"v0" +p #48;
    %"v128" = %"v127" +p #8;
    %"v129" : L = (RawLoad LdL 0) %"chk15";
    %"v132" = %"v127" +p #16;
    %"v133" : L = (RawLoad LdL 0) %"chk17"
    => goto "L120";
  @"L120" [%"pr.5" : L = phi("L118" => %"v133", "iw_4.join" => %"pr.4"); %"pr.2" : L = phi("L118" => %"v129", "iw_4.join" => %"pr.3")]:
    => br %"v58" ? "iw_5.L6" : "iw_5.L7";
  @"iw_5.L6":
    %"iw_5.v12" : W = (Cmp Ult L) %"pr.1", %"pr.2"
    => goto "iw_5.join";
  @"iw_5.L7":
    %"iw_5.v17" : W = (Cmp Slt L) %"pr.1", %"pr.2"
    => goto "iw_5.join";
  @"iw_5.join" [%"v140" : W = phi("iw_5.L6" => %"iw_5.v12", "iw_5.L7" => %"iw_5.v17")]:
    => br %"v140" ? "L143" : "iw_6.start";
  @"iw_6.start":
    => br %"v58" ? "iw_6.L6" : "iw_6.L7";
  @"iw_6.L6":
    %"iw_6.v12" : W = (Cmp Ult L) %"pr.5", %"pr.1"
    => goto "L143";
  @"iw_6.L7":
    %"iw_6.v17" : W = (Cmp Slt L) %"pr.5", %"pr.1"
    => goto "L143";
  @"L143" [%"v150" : W = phi("iw_5.join" => #1, "iw_6.L6" => %"iw_6.v12", "iw_6.L7" => %"iw_6.v17")]:
    => br %"v150" ? "L134" : "L136";
  @"L134":
    => ret void;
  @"L136":
    %"v153" = %"v0" +p #88;
    %"chk21" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"v153";
    store Wl [%"chk21" + 0] <- %"pr.1";
    %"v156" = %"v0" +p #48;
    %"v157" = %"v156" +p #8;
    store Wl [%"chk15" + 0] <- %"pr.2";
    %"v161" = %"v156" +p #16;
    store Wl [%"chk17" + 0] <- %"pr.5";
    %"v164" = %"v0" +p #104;
    %"chk24" : A = (HalfCheck Lower 0 1 Write 1) %"chk0", %"v164";
    store Wb [%"chk24" + 0] <- #1
    => ret void
} }.
