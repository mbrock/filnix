(** This file defines checked IR from glibc’s `posix/getopt.os` object.
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

Definition fn__getopt_internal : func :=
  ir_fn{ "export" "_getopt_internal"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8", W %"v10", W %"v12") -> (RClass W) {
  @"start":
    %"v15" : P = Copy $"glibc_getopt#getopt_data";
    %"v16" : P = Copy $"optind";
    %"chk0" : A = (Check 0 4 Read 1) %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"chk1" : A = (Check 0 4 Write 1) %"v15";
    store Ww [%"chk1" + 0] <- %"v17";
    %"v18" : P = Copy $"glibc_getopt#getopt_data";
    %"v19" = %"v18" +p #4;
    %"v20" : P = Copy $"opterr";
    %"chk2" : A = (Check 0 4 Read 1) %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"chk3" : A = (Check 0 4 Write 1) %"v19";
    store Ww [%"chk3" + 0] <- %"v21";
    %"v28" : P = Copy $"glibc_getopt#getopt_data";
    call %"v30" : W = $"_getopt_internal_r"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8", W %"v10", P %"v28", W %"v12");
    %"v31" : P = Copy $"optind";
    %"v32" : P = Copy $"glibc_getopt#getopt_data";
    %"chk4" : A = (Check 0 4 Read 1) %"v32";
    %"v33" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"chk5" : A = (Check 0 4 Write 1) %"v31";
    store Ww [%"chk5" + 0] <- %"v33";
    %"v34" : P = Copy $"optarg";
    %"v35" : P = Copy $"glibc_getopt#getopt_data";
    %"v36" = %"v35" +p #16;
    %"chk6" : A = (Check 0 8 Read 8) %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Write 8) %"v34";
    store.ptr [%"chk7" + 0] <- %"v37";
    %"v38" : P = Copy $"optopt";
    %"v39" : P = Copy $"glibc_getopt#getopt_data";
    %"v40" = %"v39" +p #8;
    %"chk8" : A = (Check 0 4 Read 1) %"v40";
    %"v41" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"chk9" : A = (Check 0 4 Write 1) %"v38";
    store Ww [%"chk9" + 0] <- %"v41"
    => ret %"v30"
} }.

Definition fn__getopt_internal_r : func :=
  ir_fn{ "export" "_getopt_internal_r"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8", W %"v10", P %"v12", W %"v14") -> (RClass W) blocks ((app (app [ir_blk{ @"start":
    %"v18" = %"v12" +p #4;
    %"chk0" : A = (Check 0 4 Read 1) %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v24" : W = (Cmp Slt W) %"v0", #1
    => br %"v24" ? "L20" : "L22" };
  ir_blk{ @"L20":
    => ret #4294967295 };
  ir_blk{ @"L22":
    %"v28" = %"v12" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v28";
    store.ptr [%"chk1" + 0] <- #0;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v33" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v34" : W = (Cmp Eq W) %"v33", #0
    => br %"v34" ? "L36" : "L35" };
  ir_blk{ @"L35":
    %"v38" = %"v12" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v38";
    %"v39" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v40" : W = (Cmp Eq W) %"v39", #0
    => goto "L36" };
  ir_blk{ @"L36" [%"v42" : W = phi("L22" => #1, "L35" => %"v40")]:
    => br %"v42" ? "iw_1.start" : "L30" };
  ir_blk{ @"iw_1.start":
    %"iw_1.v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.v15" : W = (Cmp Eq W) %"iw_1.v14", #0
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.L12" };
  ir_blk{ @"iw_1.L10":
    %"chk5" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk5" + 0] <- #1
    => goto "iw_1.L12" };
  ir_blk{ @"iw_1.L12":
    %"iw_1.v18" = %"v12" +p #44;
    %"iw_1.v20" = %"v12" +p #48;
    %"iw_1.v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"chk7" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v20";
    store Ww [%"chk7" + 0] <- %"iw_1.v22";
    store Ww [%"chk7" + (-4)] <- %"iw_1.v22";
    %"iw_1.v24" = %"v12" +p #32;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v24";
    store.ptr [%"chk9" + 0] <- #0;
    %"chk10" : A = (Check 0 1 Read 1) %"v4";
    %"iw_1.v30" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"iw_1.v31" : W = (Cmp Eq W) %"iw_1.v30", #45
    => br %"iw_1.v31" ? "iw_1.L25" : "iw_1.L26" };
  ir_blk{ @"iw_1.L25":
    %"iw_1.v33" = %"v12" +p #40;
    %"chk11" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v33";
    store Ww [%"chk11" + 0] <- #2;
    %"iw_1.v35" = %"v4" +p #1
    => goto "iw_1.L27" };
  ir_blk{ @"iw_1.L26":
    %"iw_1.v41" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"iw_1.v42" : W = (Cmp Eq W) %"iw_1.v41", #43
    => br %"iw_1.v42" ? "iw_1.L36" : "iw_1.L37" };
  ir_blk{ @"iw_1.L36":
    %"iw_1.v44" = %"v12" +p #40;
    %"chk13" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v44";
    store Ww [%"chk13" + 0] <- #0;
    %"iw_1.v46" = %"v4" +p #1
    => goto "iw_1.L27" };
  ir_blk{ @"iw_1.L37":
    => br %"v14" ? "iw_1.L52" : "iw_1.L51" };
  ir_blk{ @"iw_1.L51":
    %"iw_1.v53" : P = Copy $"glibc_getopt#str.145";
    call %"iw_1.v54" : P = $"__GI_getenv"(P %"iw_1.v53");
    %"iw_1.v55" : L = Ptoi %"iw_1.v54";
    %"iw_1.v56" : W = (Cmp Ne L) %"iw_1.v55", #0
    => goto "iw_1.L52" };
  ir_blk{ @"iw_1.L52" [%"iw_1.v60" : W = phi("iw_1.L37" => #1, "iw_1.L51" => %"iw_1.v56")]:
    => br %"iw_1.v60" ? "iw_1.L47" : "iw_1.L48" };
  ir_blk{ @"iw_1.L47":
    %"iw_1.v62" = %"v12" +p #40;
    %"chk14" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v62";
    store Ww [%"chk14" + 0] <- #0
    => goto "iw_1.L27" };
  ir_blk{ @"iw_1.L48":
    %"iw_1.v64" = %"v12" +p #40;
    %"chk15" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v64";
    store Ww [%"chk15" + 0] <- #1
    => goto "iw_1.L27" };
  ir_blk{ @"iw_1.L27" [%"iw_1.pr.1" : P = phi("iw_1.L25" => %"iw_1.v35", "iw_1.L36" => %"iw_1.v46", "iw_1.L47" => %"v4", "iw_1.L48" => %"v4")]:
    %"iw_1.v66" = %"v12" +p #24;
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v66";
    store Ww [%"chk16" + 0] <- #1
    => goto "L31" };
  ir_blk{ @"L30":
    %"chk17" : A = (Check 0 1 Read 1) %"v4";
    %"v54" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v55" : W = (Cmp Eq W) %"v54", #45
    => br %"v55" ? "L57" : "L56" };
  ir_blk{ @"L56":
    %"v60" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v61" : W = (Cmp Eq W) %"v60", #43
    => goto "L57" };
  ir_blk{ @"L57" [%"v63" : W = phi("L30" => #1, "L56" => %"v61")]:
    => br %"v63" ? "L49" : "L31" };
  ir_blk{ @"L49":
    %"v65" = %"v4" +p #1
    => goto "L31" };
  ir_blk{ @"L31" [%"pr.1" : P = phi("iw_1.L27" => %"iw_1.pr.1", "L49" => %"v65", "L57" => %"v4")]:
    %"chk19" : A = (Check 0 1 Read 1) %"pr.1";
    %"v71" : W = (RawLoad (LdNarrow Sb) 0) %"chk19";
    %"v72" : W = (Cmp Eq W) %"v71", #58
    => br %"v72" ? "L68" : "L67" };
  ir_blk{ @"L67":
    => goto "L68" };
  ir_blk{ @"L68" [%"pr.3" : W = phi("L67" => %"v19", "L31" => #0)]:
    %"v77" = %"v12" +p #32;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v77";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v79" : L = Ptoi %"v78";
    %"v80" : L = Ptoi #0;
    %"v81" : W = (Cmp Eq L) %"v79", %"v80"
    => br %"v81" ? "L83" : "L82" };
  ir_blk{ @"L82":
    %"v85" = %"v12" +p #32;
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk22" : A = (Check 0 1 Read 1) %"v86";
    %"v87" : W = (RawLoad (LdNarrow Sb) 0) %"chk22";
    %"v88" : W = (Cmp Eq W) %"v87", #0
    => goto "L83" };
  ir_blk{ @"L83" [%"v90" : W = phi("L68" => #1, "L82" => %"v88")]:
    => br %"v90" ? "L73" : "L75" };
  ir_blk{ @"L73":
    %"v95" = %"v12" +p #48;
    %"chk23" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v95";
    %"v96" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"chk24" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v98" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"v99" : W = (Cmp Sgt W) %"v96", %"v98"
    => br %"v99" ? "L91" : "L93" };
  ir_blk{ @"L91":
    %"v101" = %"v12" +p #48;
    %"v103" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"chk26" : A = (Renew 0 4 Write 1) %"chk23", %"v101";
    store Ww [%"chk26" + 0] <- %"v103"
    => goto "L93" };
  ir_blk{ @"L93":
    %"v108" = %"v12" +p #44;
    %"v109" : W = (RawLoad (LdNarrow Sw) (-4)) %"chk23";
    %"v111" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"v112" : W = (Cmp Sgt W) %"v109", %"v111"
    => br %"v112" ? "L104" : "L106" };
  ir_blk{ @"L104":
    %"v114" = %"v12" +p #44;
    %"v116" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"chk30" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v114";
    store Ww [%"chk30" + 0] <- %"v116"
    => goto "L106" };
  ir_blk{ @"L106":
    %"v121" = %"v12" +p #40;
    %"v122" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk23";
    %"v123" : W = (Cmp Eq W) %"v122", #1
    => br %"v123" ? "L117" : "L119" };
  ir_blk{ @"L117":
    %"v128" = %"v12" +p #44;
    %"v129" : W = (RawLoad (LdNarrow Sw) (-4)) %"chk23";
    %"v131" = %"v12" +p #48;
    %"v132" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v133" : W = (Cmp Ne W) %"v129", %"v132"
    => br %"v133" ? "L134" : "L135" };
  ir_blk{ @"L134":
    %"v137" = %"v12" +p #48;
    %"v138" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v140" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"v141" : W = (Cmp Ne W) %"v138", %"v140"
    => goto "L135" };
  ir_blk{ @"L135" [%"v143" : W = phi("L117" => #0, "L134" => %"v141")]:
    => br %"v143" ? "iw_2.start" : "L125" }] [ir_blk{ @"iw_2.start":
    %"iw_2.v6" = %"v12" +p #44;
    %"iw_2.v7" : W = (RawLoad (LdNarrow Sw) (-4)) %"chk23";
    %"iw_2.v10" = %"v12" +p #48;
    %"iw_2.v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"iw_2.v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk24"
    => goto "iw_2.L16" };
  ir_blk{ @"iw_2.L16" [%"iw_2.pr.3" : W = phi("iw_2.start" => %"iw_2.v14", "iw_2.L47" => %"iw_2.v94", "iw_2.L103" => %"iw_2.pr.3"); %"iw_2.pr.1" : W = phi("iw_2.start" => %"iw_2.v7", "iw_2.L47" => %"iw_2.pr.1", "iw_2.L103" => %"iw_2.v142")]:
    %"iw_2.v21" : W = (Cmp Sgt W) %"iw_2.pr.3", %"iw_2.v11"
    => br %"iw_2.v21" ? "iw_2.L22" : "iw_2.L23" };
  ir_blk{ @"iw_2.L22":
    %"iw_2.v26" : W = (Cmp Sgt W) %"iw_2.v11", %"iw_2.pr.1"
    => goto "iw_2.L23" };
  ir_blk{ @"iw_2.L23" [%"iw_2.v28" : W = phi("iw_2.L16" => #0, "iw_2.L22" => %"iw_2.v26")]:
    => br %"iw_2.v28" ? "iw_2.L17" : "iw_2.L18" };
  ir_blk{ @"iw_2.L17":
    %"iw_2.v34" : W = Sub %"iw_2.pr.3", %"iw_2.v11";
    %"iw_2.v37" : W = Sub %"iw_2.v11", %"iw_2.pr.1";
    %"iw_2.v38" : W = (Cmp Sgt W) %"iw_2.v34", %"iw_2.v37"
    => br %"iw_2.v38" ? "iw_2.L44" : "iw_2.L100" };
  ir_blk{ @"iw_2.L44" [%"iw_2.pr.5" : W = phi("iw_2.L45" => %"iw_2.v91", "iw_2.L17" => #0)]:
    %"iw_2.v50" : W = (Cmp Slt W) %"iw_2.pr.5", %"iw_2.v37"
    => br %"iw_2.v50" ? "iw_2.L45" : "iw_2.L47" };
  ir_blk{ @"iw_2.L45":
    %"iw_2.v54" : W = Add %"iw_2.pr.1", %"iw_2.pr.5";
    %"iw_2.v55" : L = (Ext Sw) %"iw_2.v54";
    %"iw_2.v56" : L = Shl %"iw_2.v55", #3;
    %"iw_2.v57" = %"v2" +p %"iw_2.v56";
    %"chk39" : A = (Check 0 8 Read 8) %"iw_2.v57";
    %"iw_2.v58" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"iw_2.v71" : W = Sub %"iw_2.pr.3", %"iw_2.v37";
    %"iw_2.v73" : W = Add %"iw_2.v71", %"iw_2.pr.5";
    %"iw_2.v74" : L = (Ext Sw) %"iw_2.v73";
    %"iw_2.v75" : L = Shl %"iw_2.v74", #3;
    %"iw_2.v76" = %"v2" +p %"iw_2.v75";
    %"chk40" : A = (Check 0 8 Read 8) %"iw_2.v76";
    %"iw_2.v77" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : A = (Renew 0 8 Write 8) %"chk39", %"iw_2.v57";
    store.ptr [%"chk41" + 0] <- %"iw_2.v77";
    %"chk42" : A = (Renew 0 8 Write 8) %"chk40", %"iw_2.v76";
    store.ptr [%"chk42" + 0] <- %"iw_2.v58";
    %"iw_2.v91" : W = Add %"iw_2.pr.5", #1
    => goto poll "iw_2.L44" };
  ir_blk{ @"iw_2.L47":
    %"iw_2.v94" : W = Sub %"iw_2.pr.3", %"iw_2.v37"
    => goto poll "iw_2.L16" };
  ir_blk{ @"iw_2.L100" [%"iw_2.pr.6" : W = phi("iw_2.L101" => %"iw_2.v139", "iw_2.L17" => #0)]:
    %"iw_2.v106" : W = (Cmp Slt W) %"iw_2.pr.6", %"iw_2.v34"
    => br %"iw_2.v106" ? "iw_2.L101" : "iw_2.L103" };
  ir_blk{ @"iw_2.L101":
    %"iw_2.v110" : W = Add %"iw_2.pr.1", %"iw_2.pr.6";
    %"iw_2.v111" : L = (Ext Sw) %"iw_2.v110";
    %"iw_2.v112" : L = Shl %"iw_2.v111", #3;
    %"iw_2.v113" = %"v2" +p %"iw_2.v112";
    %"chk43" : A = (Check 0 8 Read 8) %"iw_2.v113";
    %"iw_2.v114" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"iw_2.v125" : W = Add %"iw_2.v11", %"iw_2.pr.6";
    %"iw_2.v126" : L = (Ext Sw) %"iw_2.v125";
    %"iw_2.v127" : L = Shl %"iw_2.v126", #3;
    %"iw_2.v128" = %"v2" +p %"iw_2.v127";
    %"chk44" : A = (Check 0 8 Read 8) %"iw_2.v128";
    %"iw_2.v129" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Renew 0 8 Write 8) %"chk43", %"iw_2.v113";
    store.ptr [%"chk45" + 0] <- %"iw_2.v129";
    %"chk46" : A = (Renew 0 8 Write 8) %"chk44", %"iw_2.v128";
    store.ptr [%"chk46" + 0] <- %"iw_2.v114";
    %"iw_2.v139" : W = Add %"iw_2.pr.6", #1
    => goto poll "iw_2.L100" };
  ir_blk{ @"iw_2.L103":
    %"iw_2.v142" : W = Add %"iw_2.pr.1", %"iw_2.v34"
    => goto poll "iw_2.L16" };
  ir_blk{ @"iw_2.L18":
    %"iw_2.v144" = %"v12" +p #44;
    %"chk47" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"iw_2.v144";
    %"iw_2.v145" : W = (RawLoad (LdNarrow Sw) 0) %"chk47";
    %"chk48" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"iw_2.v147" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"iw_2.v149" = %"v12" +p #48;
    %"chk49" : A = (Renew 0 4 Read 1) %"chk23", %"iw_2.v149";
    %"iw_2.v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk49";
    %"iw_2.v151" : W = Sub %"iw_2.v147", %"iw_2.v150";
    %"iw_2.v152" : W = Add %"iw_2.v145", %"iw_2.v151";
    %"chk50" : A = (Renew 0 4 Write 1) %"chk47", %"iw_2.v144";
    store Ww [%"chk50" + 0] <- %"iw_2.v152";
    %"iw_2.v156" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    store Ww [%"chk49" + 0] <- %"iw_2.v156"
    => goto "L159" };
  ir_blk{ @"L125":
    %"v150" = %"v12" +p #48;
    %"v151" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v153" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"v154" : W = (Cmp Ne W) %"v151", %"v153"
    => br %"v154" ? "L146" : "L159" };
  ir_blk{ @"L146":
    %"v156" = %"v12" +p #44;
    %"v158" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"chk56" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v156";
    store Ww [%"chk56" + 0] <- %"v158"
    => goto "L159" };
  ir_blk{ @"L159":
    %"chk57" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v163" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v165" : W = (Cmp Slt W) %"v163", %"v0"
    => br %"v165" ? "L166" : "L167" };
  ir_blk{ @"L166":
    %"v170" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v171" : L = (Ext Sw) %"v170";
    %"v172" : L = Shl %"v171", #3;
    %"v173" = %"v2" +p %"v172";
    %"chk59" : A = (Check 0 8 Read 8) %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"chk60" : A = (Check 0 1 Read 1) %"v174";
    %"v176" : W = (RawLoad (LdNarrow Sb) 0) %"chk60";
    %"v177" : W = (Cmp Ne W) %"v176", #45
    => br %"v177" ? "L167" : "L178" };
  ir_blk{ @"L178":
    %"v182" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v183" : L = (Ext Sw) %"v182";
    %"v184" : L = Shl %"v183", #3;
    %"v185" = %"v2" +p %"v184";
    %"chk62" : A = (Check 0 8 Read 8) %"v185";
    %"v186" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v187" = %"v186" +p #1;
    %"chk63" : A = (Check 0 1 Read 1) %"v187";
    %"v188" : W = (RawLoad (LdNarrow Sb) 0) %"chk63";
    %"v189" : W = (Cmp Eq W) %"v188", #0
    => goto "L167" };
  ir_blk{ @"L167" [%"v193" : W = phi("L159" => #0, "L166" => #1, "L178" => %"v189")]:
    => br %"v193" ? "L160" : "L161" };
  ir_blk{ @"L160":
    %"v195" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v196" : W = Add %"v195", #1;
    %"chk65" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk65" + 0] <- %"v196"
    => goto poll "L159" };
  ir_blk{ @"L161":
    %"v198" = %"v12" +p #48;
    %"v200" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"chk67" : A = (Renew 0 4 Write 1) %"chk23", %"v198";
    store Ww [%"chk67" + 0] <- %"v200"
    => goto "L119" };
  ir_blk{ @"L119":
    %"chk68" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v205" : W = (RawLoad (LdNarrow Sw) 0) %"chk68";
    %"v207" : W = (Cmp Ne W) %"v205", %"v0"
    => br %"v207" ? "L208" : "L209" };
  ir_blk{ @"L208":
    %"v212" : W = (RawLoad (LdNarrow Sw) 0) %"chk68";
    %"v213" : L = (Ext Sw) %"v212";
    %"v214" : L = Shl %"v213", #3;
    %"v215" = %"v2" +p %"v214";
    %"chk70" : A = (Check 0 8 Read 8) %"v215";
    %"v216" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v217" : P = Copy $"glibc_getopt#str.146";
    call %"v218" : W = $"__GI_strcmp"(P %"v216", P %"v217");
    %"v219" : W = (Cmp Eq W) %"v218", #0
    => goto "L209" };
  ir_blk{ @"L209" [%"v221" : W = phi("L119" => #0, "L208" => %"v219")]:
    => br %"v221" ? "L201" : "L203" };
  ir_blk{ @"L201":
    %"chk71" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v223" : W = (RawLoad (LdNarrow Sw) 0) %"chk71";
    %"v224" : W = Add %"v223", #1;
    %"chk72" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk72" + 0] <- %"v224";
    %"v229" = %"v12" +p #44;
    %"chk73" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v229";
    %"v230" : W = (RawLoad (LdNarrow Sw) 0) %"chk73";
    %"v232" = %"v12" +p #48;
    %"chk74" : A = (Renew 0 4 Read 1) %"chk23", %"v232";
    %"v233" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"v234" : W = (Cmp Ne W) %"v230", %"v233"
    => br %"v234" ? "L235" : "L236" };
  ir_blk{ @"L235":
    %"v238" = %"v12" +p #48;
    %"v239" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"v241" : W = (RawLoad (LdNarrow Sw) 0) %"chk72";
    %"v242" : W = (Cmp Ne W) %"v239", %"v241"
    => goto "L236" };
  ir_blk{ @"L236" [%"v244" : W = phi("L201" => #0, "L235" => %"v242")]:
    => br %"v244" ? "iw_3.start" : "L226" };
  ir_blk{ @"iw_3.start":
    %"iw_3.v6" = %"v12" +p #44;
    %"iw_3.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk73";
    %"iw_3.v10" = %"v12" +p #48;
    %"iw_3.v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"iw_3.v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk72"
    => goto "iw_3.L16" };
  ir_blk{ @"iw_3.L16" [%"iw_3.pr.3" : W = phi("iw_3.start" => %"iw_3.v14", "iw_3.L47" => %"iw_3.v94", "iw_3.L103" => %"iw_3.pr.3"); %"iw_3.pr.1" : W = phi("iw_3.start" => %"iw_3.v7", "iw_3.L47" => %"iw_3.pr.1", "iw_3.L103" => %"iw_3.v142")]:
    %"iw_3.v21" : W = (Cmp Sgt W) %"iw_3.pr.3", %"iw_3.v11"
    => br %"iw_3.v21" ? "iw_3.L22" : "iw_3.L23" };
  ir_blk{ @"iw_3.L22":
    %"iw_3.v26" : W = (Cmp Sgt W) %"iw_3.v11", %"iw_3.pr.1"
    => goto "iw_3.L23" };
  ir_blk{ @"iw_3.L23" [%"iw_3.v28" : W = phi("iw_3.L16" => #0, "iw_3.L22" => %"iw_3.v26")]:
    => br %"iw_3.v28" ? "iw_3.L17" : "iw_3.L18" };
  ir_blk{ @"iw_3.L17":
    %"iw_3.v34" : W = Sub %"iw_3.pr.3", %"iw_3.v11";
    %"iw_3.v37" : W = Sub %"iw_3.v11", %"iw_3.pr.1";
    %"iw_3.v38" : W = (Cmp Sgt W) %"iw_3.v34", %"iw_3.v37"
    => br %"iw_3.v38" ? "iw_3.L44" : "iw_3.L100" };
  ir_blk{ @"iw_3.L44" [%"iw_3.pr.5" : W = phi("iw_3.L45" => %"iw_3.v91", "iw_3.L17" => #0)]:
    %"iw_3.v50" : W = (Cmp Slt W) %"iw_3.pr.5", %"iw_3.v37"
    => br %"iw_3.v50" ? "iw_3.L45" : "iw_3.L47" };
  ir_blk{ @"iw_3.L45":
    %"iw_3.v54" : W = Add %"iw_3.pr.1", %"iw_3.pr.5";
    %"iw_3.v55" : L = (Ext Sw) %"iw_3.v54";
    %"iw_3.v56" : L = Shl %"iw_3.v55", #3;
    %"iw_3.v57" = %"v2" +p %"iw_3.v56";
    %"chk80" : A = (Check 0 8 Read 8) %"iw_3.v57";
    %"iw_3.v58" : P = (RawLoadPointer 0 load_effects) %"chk80";
    %"iw_3.v71" : W = Sub %"iw_3.pr.3", %"iw_3.v37";
    %"iw_3.v73" : W = Add %"iw_3.v71", %"iw_3.pr.5";
    %"iw_3.v74" : L = (Ext Sw) %"iw_3.v73";
    %"iw_3.v75" : L = Shl %"iw_3.v74", #3;
    %"iw_3.v76" = %"v2" +p %"iw_3.v75";
    %"chk81" : A = (Check 0 8 Read 8) %"iw_3.v76";
    %"iw_3.v77" : P = (RawLoadPointer 0 load_effects) %"chk81";
    %"chk82" : A = (Renew 0 8 Write 8) %"chk80", %"iw_3.v57";
    store.ptr [%"chk82" + 0] <- %"iw_3.v77";
    %"chk83" : A = (Renew 0 8 Write 8) %"chk81", %"iw_3.v76";
    store.ptr [%"chk83" + 0] <- %"iw_3.v58";
    %"iw_3.v91" : W = Add %"iw_3.pr.5", #1
    => goto poll "iw_3.L44" };
  ir_blk{ @"iw_3.L47":
    %"iw_3.v94" : W = Sub %"iw_3.pr.3", %"iw_3.v37"
    => goto poll "iw_3.L16" }]) (app [ir_blk{ @"iw_3.L100" [%"iw_3.pr.6" : W = phi("iw_3.L101" => %"iw_3.v139", "iw_3.L17" => #0)]:
    %"iw_3.v106" : W = (Cmp Slt W) %"iw_3.pr.6", %"iw_3.v34"
    => br %"iw_3.v106" ? "iw_3.L101" : "iw_3.L103" };
  ir_blk{ @"iw_3.L101":
    %"iw_3.v110" : W = Add %"iw_3.pr.1", %"iw_3.pr.6";
    %"iw_3.v111" : L = (Ext Sw) %"iw_3.v110";
    %"iw_3.v112" : L = Shl %"iw_3.v111", #3;
    %"iw_3.v113" = %"v2" +p %"iw_3.v112";
    %"chk84" : A = (Check 0 8 Read 8) %"iw_3.v113";
    %"iw_3.v114" : P = (RawLoadPointer 0 load_effects) %"chk84";
    %"iw_3.v125" : W = Add %"iw_3.v11", %"iw_3.pr.6";
    %"iw_3.v126" : L = (Ext Sw) %"iw_3.v125";
    %"iw_3.v127" : L = Shl %"iw_3.v126", #3;
    %"iw_3.v128" = %"v2" +p %"iw_3.v127";
    %"chk85" : A = (Check 0 8 Read 8) %"iw_3.v128";
    %"iw_3.v129" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"chk86" : A = (Renew 0 8 Write 8) %"chk84", %"iw_3.v113";
    store.ptr [%"chk86" + 0] <- %"iw_3.v129";
    %"chk87" : A = (Renew 0 8 Write 8) %"chk85", %"iw_3.v128";
    store.ptr [%"chk87" + 0] <- %"iw_3.v114";
    %"iw_3.v139" : W = Add %"iw_3.pr.6", #1
    => goto poll "iw_3.L100" };
  ir_blk{ @"iw_3.L103":
    %"iw_3.v142" : W = Add %"iw_3.pr.1", %"iw_3.v34"
    => goto poll "iw_3.L16" };
  ir_blk{ @"iw_3.L18":
    %"iw_3.v144" = %"v12" +p #44;
    %"chk88" : A = (Renew 0 4 Read 1) %"chk73", %"iw_3.v144";
    %"iw_3.v145" : W = (RawLoad (LdNarrow Sw) 0) %"chk88";
    %"chk89" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"iw_3.v147" : W = (RawLoad (LdNarrow Sw) 0) %"chk89";
    %"iw_3.v149" = %"v12" +p #48;
    %"chk90" : A = (Renew 0 4 Read 1) %"chk23", %"iw_3.v149";
    %"iw_3.v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk90";
    %"iw_3.v151" : W = Sub %"iw_3.v147", %"iw_3.v150";
    %"iw_3.v152" : W = Add %"iw_3.v145", %"iw_3.v151";
    %"chk91" : A = (Renew 0 4 Write 1) %"chk73", %"iw_3.v144";
    store Ww [%"chk91" + 0] <- %"iw_3.v152";
    %"iw_3.v156" : W = (RawLoad (LdNarrow Sw) 0) %"chk89";
    store Ww [%"chk90" + 0] <- %"iw_3.v156"
    => goto "L227" };
  ir_blk{ @"L226":
    %"v251" = %"v12" +p #44;
    %"v252" : W = (RawLoad (LdNarrow Sw) 0) %"chk73";
    %"v254" = %"v12" +p #48;
    %"v255" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"v256" : W = (Cmp Eq W) %"v252", %"v255"
    => br %"v256" ? "L247" : "L227" };
  ir_blk{ @"L247":
    %"v258" = %"v12" +p #44;
    %"v260" : W = (RawLoad (LdNarrow Sw) 0) %"chk72";
    store Ww [%"chk73" + 0] <- %"v260"
    => goto "L227" };
  ir_blk{ @"L227":
    %"v262" = %"v12" +p #48;
    %"chk98" : A = (Renew 0 4 Write 1) %"chk23", %"v262";
    store Ww [%"chk98" + 0] <- %"v0";
    %"chk99" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk99" + 0] <- %"v0"
    => goto "L203" };
  ir_blk{ @"L203":
    %"chk100" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v270" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v272" : W = (Cmp Eq W) %"v270", %"v0"
    => br %"v272" ? "L266" : "L268" };
  ir_blk{ @"L266":
    %"v277" = %"v12" +p #44;
    %"chk101" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v277";
    %"v278" : W = (RawLoad (LdNarrow Sw) 0) %"chk101";
    %"v280" = %"v12" +p #48;
    %"chk102" : A = (Renew 0 4 Read 1) %"chk23", %"v280";
    %"v281" : W = (RawLoad (LdNarrow Sw) 0) %"chk102";
    %"v282" : W = (Cmp Ne W) %"v278", %"v281"
    => br %"v282" ? "L273" : "L275" };
  ir_blk{ @"L273":
    %"v285" = %"v12" +p #44;
    %"v286" : W = (RawLoad (LdNarrow Sw) 0) %"chk101";
    %"chk104" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk104" + 0] <- %"v286"
    => goto "L275" };
  ir_blk{ @"L275":
    => ret #4294967295 };
  ir_blk{ @"L268":
    %"v294" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v295" : L = (Ext Sw) %"v294";
    %"v296" : L = Shl %"v295", #3;
    %"v297" = %"v2" +p %"v296";
    %"chk106" : A = (Check 0 8 Read 8) %"v297";
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"chk107" : A = (Check 0 1 Read 1) %"v298";
    %"v300" : W = (RawLoad (LdNarrow Sb) 0) %"chk107";
    %"v301" : W = (Cmp Ne W) %"v300", #45
    => br %"v301" ? "L303" : "L302" };
  ir_blk{ @"L302":
    %"v306" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v307" : L = (Ext Sw) %"v306";
    %"v308" : L = Shl %"v307", #3;
    %"v309" = %"v2" +p %"v308";
    %"chk109" : A = (Check 0 8 Read 8) %"v309";
    %"v310" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"v311" = %"v310" +p #1;
    %"chk110" : A = (Check 0 1 Read 1) %"v311";
    %"v312" : W = (RawLoad (LdNarrow Sb) 0) %"chk110";
    %"v313" : W = (Cmp Eq W) %"v312", #0
    => goto "L303" };
  ir_blk{ @"L303" [%"v315" : W = phi("L268" => #1, "L302" => %"v313")]:
    => br %"v315" ? "L289" : "L291" };
  ir_blk{ @"L289":
    %"v320" = %"v12" +p #40;
    %"chk111" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v320";
    %"v321" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
    %"v322" : W = (Cmp Eq W) %"v321", #0
    => br %"v322" ? "L316" : "L318" };
  ir_blk{ @"L316":
    => ret #4294967295 };
  ir_blk{ @"L318":
    %"v326" = %"v12" +p #16;
    %"v329" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v330" : W = Add %"v329", #1;
    %"chk113" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk113" + 0] <- %"v330";
    %"v331" : L = (Ext Sw) %"v329";
    %"v332" : L = Shl %"v331", #3;
    %"v333" = %"v2" +p %"v332";
    %"chk114" : A = (Check 0 8 Read 8) %"v333";
    %"v334" : P = (RawLoadPointer 0 load_effects) %"chk114";
    %"chk115" : A = (Renew 0 8 Write 8) %"chk1", %"v326";
    store.ptr [%"chk115" + 0] <- %"v334"
    => ret #1 };
  ir_blk{ @"L291":
    %"v340" : L = Ptoi %"v6";
    %"v341" : W = (Cmp Ne L) %"v340", #0
    => br %"v341" ? "L336" : "L338" };
  ir_blk{ @"L336":
    %"v347" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v348" : L = (Ext Sw) %"v347";
    %"v349" : L = Shl %"v348", #3;
    %"v350" = %"v2" +p %"v349";
    %"chk117" : A = (Check 0 8 Read 8) %"v350";
    %"v351" : P = (RawLoadPointer 0 load_effects) %"chk117";
    %"v352" = %"v351" +p #1;
    %"chk118" : A = (Check 0 1 Read 1) %"v352";
    %"v353" : W = (RawLoad (LdNarrow Sb) 0) %"chk118";
    %"v354" : W = (Cmp Eq W) %"v353", #45
    => br %"v354" ? "L342" : "L344" };
  ir_blk{ @"L342":
    %"v356" = %"v12" +p #32;
    %"v359" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v360" : L = (Ext Sw) %"v359";
    %"v361" : L = Shl %"v360", #3;
    %"v362" = %"v2" +p %"v361";
    %"chk120" : A = (Check 0 8 Read 8) %"v362";
    %"v363" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"v364" = %"v363" +p #2;
    %"chk121" : A = (Renew 0 8 Write 8) %"chk20", %"v356";
    store.ptr [%"chk121" + 0] <- %"v364";
    %"v373" : P = Copy $"glibc_getopt#str.146";
    call %"v374" : W = $"glibc_getopt#process_long_option"(W %"v0", P %"v2", P %"pr.1", P %"v6", P %"v8", W %"v10", P %"v12", W %"pr.3", P %"v373")
    => ret %"v374" };
  ir_blk{ @"L344":
    => br %"v10" ? "L380" : "L381" };
  ir_blk{ @"L380":
    %"v384" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v385" : L = (Ext Sw) %"v384";
    %"v386" : L = Shl %"v385", #3;
    %"v387" = %"v2" +p %"v386";
    %"chk123" : A = (Check 0 8 Read 8) %"v387";
    %"v388" : P = (RawLoadPointer 0 load_effects) %"chk123";
    %"v389" = %"v388" +p #2;
    %"chk124" : A = (Check 0 1 Read 1) %"v389";
    %"v390" : W = (RawLoad (LdNarrow Sb) 0) %"chk124"
    => br %"v390" ? "L381" : "L391" };
  ir_blk{ @"L391":
    %"v396" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v397" : L = (Ext Sw) %"v396";
    %"v398" : L = Shl %"v397", #3;
    %"v399" = %"v2" +p %"v398";
    %"chk126" : A = (Check 0 8 Read 8) %"v399";
    %"v400" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v401" = %"v400" +p #1;
    %"chk127" : A = (Check 0 1 Read 1) %"v401";
    %"v402" : W = (RawLoad (LdNarrow Sb) 0) %"chk127";
    call %"v403" : P = $"__GI_strchr"(P %"pr.1", W %"v402");
    %"v404" : L = Ptoi %"v403";
    %"v406" : W = (Cmp Eq L) %"v404", #0
    => goto "L381" };
  ir_blk{ @"L381" [%"v410" : W = phi("L344" => #0, "L380" => #1, "L391" => %"v406")]:
    => br %"v410" ? "L376" : "L338" };
  ir_blk{ @"L376":
    %"v413" = %"v12" +p #32;
    %"chk128" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v416" : W = (RawLoad (LdNarrow Sw) 0) %"chk128";
    %"v417" : L = (Ext Sw) %"v416";
    %"v418" : L = Shl %"v417", #3;
    %"v419" = %"v2" +p %"v418";
    %"chk129" : A = (Check 0 8 Read 8) %"v419";
    %"v420" : P = (RawLoadPointer 0 load_effects) %"chk129";
    %"v421" = %"v420" +p #1;
    %"chk130" : A = (Renew 0 8 Write 8) %"chk20", %"v413";
    store.ptr [%"chk130" + 0] <- %"v421";
    %"v430" : P = Copy $"glibc_getopt#str.147";
    call %"v431" : W = $"glibc_getopt#process_long_option"(W %"v0", P %"v2", P %"pr.1", P %"v6", P %"v8", W %"v10", P %"v12", W %"pr.3", P %"v430");
    %"v437" : W = (Cmp Ne W) %"v431", #4294967295
    => br %"v437" ? "L432" : "L338" };
  ir_blk{ @"L432":
    => ret %"v431" };
  ir_blk{ @"L338":
    %"v441" = %"v12" +p #32;
    %"chk131" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v444" : W = (RawLoad (LdNarrow Sw) 0) %"chk131";
    %"v445" : L = (Ext Sw) %"v444";
    %"v446" : L = Shl %"v445", #3;
    %"v447" = %"v2" +p %"v446";
    %"chk132" : A = (Check 0 8 Read 8) %"v447";
    %"v448" : P = (RawLoadPointer 0 load_effects) %"chk132";
    %"v449" = %"v448" +p #1;
    %"chk133" : A = (Renew 0 8 Write 8) %"chk20", %"v441";
    store.ptr [%"chk133" + 0] <- %"v449"
    => goto "L75" };
  ir_blk{ @"L75":
    %"v452" = %"v12" +p #32;
    %"chk134" : A = (Renew 0 8 Read 8) %"chk20", %"v452";
    %"v453" : P = (RawLoadPointer 0 load_effects) %"chk134";
    %"v454" = %"v453" +p #1;
    %"chk135" : A = (Renew 0 8 Write 8) %"chk20", %"v452";
    store.ptr [%"chk135" + 0] <- %"v454";
    %"chk136" : A = (Check 0 1 Read 1) %"v453";
    %"v455" : W = (RawLoad (LdNarrow Sb) 0) %"chk136";
    call %"v459" : P = $"__GI_strchr"(P %"pr.1", W %"v455");
    %"chk137" : A = (Renew 0 8 Read 8) %"chk20", %"v452";
    %"v465" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk138" : A = (Check 0 1 Read 1) %"v465";
    %"v466" : W = (RawLoad (LdNarrow Sb) 0) %"chk138";
    %"v467" : W = (Cmp Eq W) %"v466", #0
    => br %"v467" ? "L460" : "L462" };
  ir_blk{ @"L460":
    %"chk139" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v469" : W = (RawLoad (LdNarrow Sw) 0) %"chk139";
    %"v470" : W = Add %"v469", #1;
    %"chk140" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk140" + 0] <- %"v470"
    => goto "L462" };
  ir_blk{ @"L462":
    %"v475" : L = Ptoi %"v459";
    %"v477" : W = (Cmp Eq L) %"v475", %"v80"
    => br %"v477" ? "L479" : "L478" };
  ir_blk{ @"L478":
    %"v481" : W = (Cmp Eq W) %"v455", #58
    => goto "L479" };
  ir_blk{ @"L479" [%"v483" : W = phi("L462" => #1, "L478" => %"v481")]:
    => br %"v483" ? "L485" : "L484" };
  ir_blk{ @"L484":
    %"v487" : W = (Cmp Eq W) %"v455", #59
    => goto "L485" };
  ir_blk{ @"L485" [%"v489" : W = phi("L479" => #1, "L484" => %"v487")]:
    => br %"v489" ? "L471" : "L473" }] [ir_blk{ @"L471":
    => br %"pr.3" ? "L490" : "L492" };
  ir_blk{ @"L490":
    %"v494" : P = Copy $"stderr";
    %"chk141" : A = (Check 0 8 Read 8) %"v494";
    %"v495" : P = (RawLoadPointer 0 load_effects) %"chk141";
    %"v496" : P = Copy $"__GI__libc_intl_domainname";
    %"v497" : P = Copy $"glibc_getopt#str.148";
    call %"v498" : P = $"__GI___dcgettext"(P %"v496", P %"v497", W #5);
    %"chk142" : A = (Check 0 8 Read 8) %"v2";
    %"v501" : P = (RawLoadPointer 0 load_effects) %"chk142";
    call %"v503" : W = $"__fxprintf_nocancel"(P %"v495", P %"v498", P %"v501", W %"v455")
    => goto "L492" };
  ir_blk{ @"L492":
    %"v505" = %"v12" +p #8;
    %"chk143" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v505";
    store Ww [%"chk143" + 0] <- %"v455"
    => ret #63 };
  ir_blk{ @"L473":
    %"chk144" : A = (Check 0 1 Read 1) %"v459";
    %"v513" : W = (RawLoad (LdNarrow Sb) 0) %"chk144";
    %"v514" : W = (Cmp Eq W) %"v513", #87
    => br %"v514" ? "L515" : "L516" };
  ir_blk{ @"L515":
    %"v518" = %"v459" +p #1;
    %"chk145" : A = (HalfCheck Upper 0 1 Read 1) %"chk144", %"v518";
    %"v519" : W = (RawLoad (LdNarrow Sb) 0) %"chk145";
    %"v520" : W = (Cmp Eq W) %"v519", #59
    => goto "L516" };
  ir_blk{ @"L516" [%"v522" : W = phi("L473" => #0, "L515" => %"v520")]:
    => br %"v522" ? "L523" : "L524" };
  ir_blk{ @"L523":
    %"v526" : L = Ptoi %"v6";
    %"v528" : W = (Cmp Ne L) %"v526", %"v80"
    => goto "L524" };
  ir_blk{ @"L524" [%"v530" : W = phi("L516" => #0, "L523" => %"v528")]:
    => br %"v530" ? "L508" : "L510" };
  ir_blk{ @"L508":
    %"v535" = %"v12" +p #32;
    %"v536" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk147" : A = (Check 0 1 Read 1) %"v536";
    %"v537" : W = (RawLoad (LdNarrow Sb) 0) %"chk147";
    %"v538" : W = (Cmp Ne W) %"v537", #0
    => br %"v538" ? "L531" : "L532" };
  ir_blk{ @"L531":
    %"v540" = %"v12" +p #16;
    %"v542" = %"v12" +p #32;
    %"v543" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk149" : A = (Renew 0 8 Write 8) %"chk1", %"v540";
    store.ptr [%"chk149" + 0] <- %"v543"
    => goto "L533" };
  ir_blk{ @"L532":
    %"chk150" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v548" : W = (RawLoad (LdNarrow Sw) 0) %"chk150";
    %"v550" : W = (Cmp Eq W) %"v548", %"v0"
    => br %"v550" ? "L544" : "L545" };
  ir_blk{ @"L544":
    => br %"pr.3" ? "L551" : "L553" };
  ir_blk{ @"L551":
    %"v555" : P = Copy $"stderr";
    %"chk151" : A = (Check 0 8 Read 8) %"v555";
    %"v556" : P = (RawLoadPointer 0 load_effects) %"chk151";
    %"v557" : P = Copy $"__GI__libc_intl_domainname";
    %"v558" : P = Copy $"glibc_getopt#str.149";
    call %"v559" : P = $"__GI___dcgettext"(P %"v557", P %"v558", W #5);
    %"chk152" : A = (Check 0 8 Read 8) %"v2";
    %"v562" : P = (RawLoadPointer 0 load_effects) %"chk152";
    call %"v564" : W = $"__fxprintf_nocancel"(P %"v556", P %"v559", P %"v562", W %"v455")
    => goto "L553" };
  ir_blk{ @"L553":
    %"v566" = %"v12" +p #8;
    %"chk153" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v566";
    store Ww [%"chk153" + 0] <- %"v455";
    %"chk154" : A = (Renew 0 1 Read 1) %"chk19", %"pr.1";
    %"v573" : W = (RawLoad (LdNarrow Sb) 0) %"chk154";
    %"v574" : W = (Cmp Eq W) %"v573", #58
    => br %"v574" ? "L570" : "L569" };
  ir_blk{ @"L569":
    => goto "L570" };
  ir_blk{ @"L570" [%"pr.4" : W = phi("L569" => #63, "L553" => #58)]:
    %"v575" : W = (Ext Sb) %"pr.4"
    => ret %"v575" };
  ir_blk{ @"L545":
    %"v578" = %"v12" +p #16;
    %"v581" : W = (RawLoad (LdNarrow Sw) 0) %"chk150";
    %"v582" : L = (Ext Sw) %"v581";
    %"v583" : L = Shl %"v582", #3;
    %"v584" = %"v2" +p %"v583";
    %"chk156" : A = (Check 0 8 Read 8) %"v584";
    %"v585" : P = (RawLoadPointer 0 load_effects) %"chk156";
    %"chk157" : A = (Renew 0 8 Write 8) %"chk1", %"v578";
    store.ptr [%"chk157" + 0] <- %"v585"
    => goto "L533" };
  ir_blk{ @"L533":
    %"v587" = %"v12" +p #32;
    %"v589" = %"v12" +p #16;
    %"chk158" : A = (Renew 0 8 Read 8) %"chk1", %"v589";
    %"v590" : P = (RawLoadPointer 0 load_effects) %"chk158";
    %"chk159" : A = (Renew 0 8 Write 8) %"chk20", %"v587";
    store.ptr [%"chk159" + 0] <- %"v590";
    %"chk160" : A = (Renew 0 8 Write 8) %"chk1", %"v589";
    store.ptr [%"chk160" + 0] <- #0;
    %"v600" : P = Copy $"glibc_getopt#str.150";
    call %"v601" : W = $"glibc_getopt#process_long_option"(W %"v0", P %"v2", P %"pr.1", P %"v6", P %"v8", W #0, P %"v12", W %"pr.3", P %"v600")
    => ret %"v601" };
  ir_blk{ @"L510":
    %"v607" = %"v459" +p #1;
    %"chk161" : A = (HalfCheck Upper 0 1 Read 1) %"chk144", %"v607";
    %"v608" : W = (RawLoad (LdNarrow Sb) 0) %"chk161";
    %"v609" : W = (Cmp Eq W) %"v608", #58
    => br %"v609" ? "L603" : "L605" };
  ir_blk{ @"L603":
    %"v614" = %"v459" +p #2;
    %"chk162" : A = (HalfCheck Upper 0 1 Read 1) %"chk144", %"v614";
    %"v615" : W = (RawLoad (LdNarrow Sb) 0) %"chk162";
    %"v616" : W = (Cmp Eq W) %"v615", #58
    => br %"v616" ? "L610" : "L611" };
  ir_blk{ @"L610":
    %"v621" = %"v12" +p #32;
    %"v622" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk164" : A = (Check 0 1 Read 1) %"v622";
    %"v623" : W = (RawLoad (LdNarrow Sb) 0) %"chk164";
    %"v624" : W = (Cmp Ne W) %"v623", #0
    => br %"v624" ? "L617" : "L618" };
  ir_blk{ @"L617":
    %"v626" = %"v12" +p #16;
    %"v628" = %"v12" +p #32;
    %"v629" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk166" : A = (Renew 0 8 Write 8) %"chk1", %"v626";
    store.ptr [%"chk166" + 0] <- %"v629";
    %"chk167" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v631" : W = (RawLoad (LdNarrow Sw) 0) %"chk167";
    %"v632" : W = Add %"v631", #1;
    %"chk168" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk168" + 0] <- %"v632"
    => goto "L619" };
  ir_blk{ @"L618":
    %"v634" = %"v12" +p #16;
    %"chk169" : A = (Renew 0 8 Write 8) %"chk1", %"v634";
    store.ptr [%"chk169" + 0] <- #0
    => goto "L619" };
  ir_blk{ @"L619":
    %"v636" = %"v12" +p #32;
    %"chk170" : A = (Renew 0 8 Write 8) %"chk20", %"v636";
    store.ptr [%"chk170" + 0] <- #0
    => goto "L605" };
  ir_blk{ @"L611":
    %"v641" = %"v12" +p #32;
    %"v642" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk172" : A = (Check 0 1 Read 1) %"v642";
    %"v643" : W = (RawLoad (LdNarrow Sb) 0) %"chk172";
    %"v644" : W = (Cmp Ne W) %"v643", #0
    => br %"v644" ? "L637" : "L638" };
  ir_blk{ @"L637":
    %"v646" = %"v12" +p #16;
    %"v648" = %"v12" +p #32;
    %"v649" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk174" : A = (Renew 0 8 Write 8) %"chk1", %"v646";
    store.ptr [%"chk174" + 0] <- %"v649";
    %"chk175" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v651" : W = (RawLoad (LdNarrow Sw) 0) %"chk175";
    %"v652" : W = Add %"v651", #1;
    %"chk176" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk176" + 0] <- %"v652"
    => goto "L639" };
  ir_blk{ @"L638":
    %"chk177" : A = (Renew 0 4 Read 1) %"chk2", %"v12";
    %"v657" : W = (RawLoad (LdNarrow Sw) 0) %"chk177";
    %"v659" : W = (Cmp Eq W) %"v657", %"v0"
    => br %"v659" ? "L653" : "L654" };
  ir_blk{ @"L653":
    => br %"pr.3" ? "L660" : "L662" };
  ir_blk{ @"L660":
    %"v664" : P = Copy $"stderr";
    %"chk178" : A = (Check 0 8 Read 8) %"v664";
    %"v665" : P = (RawLoadPointer 0 load_effects) %"chk178";
    %"v666" : P = Copy $"__GI__libc_intl_domainname";
    %"v667" : P = Copy $"glibc_getopt#str.149";
    call %"v668" : P = $"__GI___dcgettext"(P %"v666", P %"v667", W #5);
    %"chk179" : A = (Check 0 8 Read 8) %"v2";
    %"v671" : P = (RawLoadPointer 0 load_effects) %"chk179";
    call %"v673" : W = $"__fxprintf_nocancel"(P %"v665", P %"v668", P %"v671", W %"v455")
    => goto "L662" };
  ir_blk{ @"L662":
    %"v675" = %"v12" +p #8;
    %"chk180" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v675";
    store Ww [%"chk180" + 0] <- %"v455";
    %"chk181" : A = (Renew 0 1 Read 1) %"chk19", %"pr.1";
    %"v682" : W = (RawLoad (LdNarrow Sb) 0) %"chk181";
    %"v683" : W = (Cmp Eq W) %"v682", #58
    => br %"v683" ? "L639" : "L678" };
  ir_blk{ @"L678":
    => goto "L639" };
  ir_blk{ @"L654":
    %"v685" = %"v12" +p #16;
    %"v688" : W = (RawLoad (LdNarrow Sw) 0) %"chk177";
    %"v689" : W = Add %"v688", #1;
    %"chk183" : A = (Renew 0 4 Write 1) %"chk2", %"v12";
    store Ww [%"chk183" + 0] <- %"v689";
    %"v690" : L = (Ext Sw) %"v688";
    %"v691" : L = Shl %"v690", #3;
    %"v692" = %"v2" +p %"v691";
    %"chk184" : A = (Check 0 8 Read 8) %"v692";
    %"v693" : P = (RawLoadPointer 0 load_effects) %"chk184";
    %"chk185" : A = (Renew 0 8 Write 8) %"chk1", %"v685";
    store.ptr [%"chk185" + 0] <- %"v693"
    => goto "L639" };
  ir_blk{ @"L639" [%"pr.7" : W = phi("L637" => %"v455", "L654" => %"v455", "L678" => #63, "L662" => #58)]:
    %"v695" = %"v12" +p #32;
    %"chk186" : A = (Renew 0 8 Write 8) %"chk20", %"v695";
    store.ptr [%"chk186" + 0] <- #0
    => goto "L605" };
  ir_blk{ @"L605" [%"pr.5" : W = phi("L619" => %"v455", "L639" => %"pr.7", "L510" => %"v455")]:
    %"v696" : W = (Ext Sb) %"pr.5"
    => ret %"v696" }]))) }.

Definition item_glibc_getopt'23getopt_data : item :=
  (IData (a "glibc_getopt#getopt_data") LLocal 8 [(Zero 56)]).

Definition fn_glibc_getopt'23process_long_option : func :=
  ir_fn{ "local" "glibc_getopt#process_long_option"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8", W %"v10", P %"v12", W %"v14", P %"v16") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v25" = %"v12" +p #32;
    %"chk0" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L27" };
  ir_blk{ @"L27" [%"pr.1" : P = phi("L29" => %"v41", "start" => %"v26")]:
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v32" : W = (RawLoad (LdNarrow Sb) 0) %"chk1"
    => br %"v32" ? "L33" : "L34" };
  ir_blk{ @"L33":
    %"v36" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v37" : W = (Cmp Ne W) %"v36", #61
    => goto "L34" };
  ir_blk{ @"L34" [%"v39" : W = phi("L27" => #0, "L33" => %"v37")]:
    => br %"v39" ? "L29" : "L30" };
  ir_blk{ @"L29":
    %"v41" = %"pr.1" +p #1
    => goto poll "L27" };
  ir_blk{ @"L30":
    %"v44" = %"v12" +p #32;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v46" : L = Ptoi %"pr.1";
    %"v47" : L = Ptoi %"v45";
    %"v48" : L = Sub %"v46", %"v47"
    => goto "L50" };
  ir_blk{ @"L50" [%"pr.9" : W = phi("L30" => #0, "L52" => %"v84"); %"pr.2" : P = phi("L30" => %"v6", "L52" => %"v82")]:
    %"chk4" : A = (Check 0 8 Read 8) %"pr.2";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v56" : L = Ptoi %"v55";
    %"v57" : W = (Cmp Ne L) %"v56", #0
    => br %"v57" ? "L51" : "L53" };
  ir_blk{ @"L51":
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v64" = %"v12" +p #32;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v67" : W = $"__GI_strncmp"(P %"v62", P %"v65", L %"v48");
    %"v68" : W = (Cmp Eq W) %"v67", #0
    => br %"v68" ? "L69" : "L70" };
  ir_blk{ @"L69":
    %"chk7" : A = (Renew 0 8 Read 8) %"chk4", %"pr.2";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call %"v74" : L = $"__GI_strlen"(P %"v73");
    %"v75" : W = (Cmp Eq L) %"v48", %"v74"
    => goto "L70" };
  ir_blk{ @"L70" [%"v77" : W = phi("L51" => #0, "L69" => %"v75")]:
    => br %"v77" ? "L53" : "L52" };
  ir_blk{ @"L52":
    %"v82" = %"pr.2" +p #32;
    %"v84" : W = Add %"pr.9", #1
    => goto poll "L50" };
  ir_blk{ @"L53" [%"pr.11" : W = phi("L50" => #0, "L70" => %"pr.9"); %"pr.6" : P = phi("L50" => #0, "L70" => %"pr.2")]:
    %"v89" : L = Ptoi %"pr.6";
    %"v90" : L = Ptoi #0;
    %"v91" : W = (Cmp Eq L) %"v89", %"v90"
    => br %"v91" ? "L98" : "L87" };
  ir_blk{ @"L98" [%"pr.42" : W = phi("L108" => %"pr.40", "L53" => #4294967295); %"pr.39" : W = phi("L108" => %"pr.31", "L53" => #0); %"pr.30" : W = phi("L108" => %"pr.22", "L53" => #0); %"pr.21" : P = phi("L108" => %"pr.14", "L53" => #0); %"pr.13" : W = phi("L108" => %"v227", "L53" => #0); %"pr.8" : P = phi("L108" => %"pr.4", "L53" => %"pr.6"); %"pr.3" : P = phi("L108" => %"v225", "L53" => %"v6")]:
    %"chk8" : A = (Check 0 8 Read 8) %"pr.3";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v104" : L = Ptoi %"v103";
    %"v105" : W = (Cmp Ne L) %"v104", #0
    => br %"v105" ? "L99" : "L101" };
  ir_blk{ @"L99":
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v112" = %"v12" +p #32;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk10";
    call %"v115" : W = $"__GI_strncmp"(P %"v110", P %"v113", L %"v48");
    %"v116" : W = (Cmp Eq W) %"v115", #0
    => br %"v116" ? "L106" : "L108" };
  ir_blk{ @"L106":
    %"v121" : L = Ptoi %"pr.8";
    %"v123" : W = (Cmp Eq L) %"v121", %"v90"
    => br %"v123" ? "L108" : "L118" };
  ir_blk{ @"L118":
    => br %"v10" ? "L131" : "L130" };
  ir_blk{ @"L130":
    %"v133" = %"pr.8" +p #8;
    %"chk11" : A = (Check 0 4 Read 1) %"v133";
    %"v134" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"v136" = %"pr.3" +p #8;
    %"chk12" : A = (HalfCheck Upper 0 4 Read 1) %"chk8", %"v136";
    %"v137" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v138" : W = (Cmp Ne W) %"v134", %"v137"
    => goto "L131" };
  ir_blk{ @"L131" [%"v140" : W = phi("L118" => #1, "L130" => %"v138")]:
    => br %"v140" ? "L142" : "L141" };
  ir_blk{ @"L141":
    %"v144" = %"pr.8" +p #16;
    %"chk13" : A = (Check 0 8 Read 8) %"v144";
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v147" = %"pr.3" +p #16;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk8", %"v147";
    %"v148" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v149" : L = Ptoi %"v145";
    %"v150" : L = Ptoi %"v148";
    %"v151" : W = (Cmp Ne L) %"v149", %"v150"
    => goto "L142" };
  ir_blk{ @"L142" [%"v153" : W = phi("L131" => #1, "L141" => %"v151")]:
    => br %"v153" ? "L155" : "L154" };
  ir_blk{ @"L154":
    %"v157" = %"pr.8" +p #24;
    %"chk15" : A = (Check 0 4 Read 1) %"v157";
    %"v158" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v160" = %"pr.3" +p #24;
    %"chk16" : A = (HalfCheck Upper 0 4 Read 1) %"chk8", %"v160";
    %"v161" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v162" : W = (Cmp Ne W) %"v158", %"v161"
    => goto "L155" };
  ir_blk{ @"L155" [%"v164" : W = phi("L142" => #1, "L154" => %"v162")]:
    => br %"v164" ? "L126" : "L108" };
  ir_blk{ @"L126":
    %"v169" : W = (Cmp Eq W) %"pr.39", #0
    => br %"v169" ? "L165" : "L108" };
  ir_blk{ @"L165":
    %"v174" : W = (Cmp Eq W) %"v14", #0
    => br %"v174" ? "L172" : "L171" };
  ir_blk{ @"L171":
    %"v179" : L = Ptoi %"pr.21";
    %"v181" : W = (Cmp Eq L) %"v179", #0
    => br %"v181" ? "L175" : "L172" };
  ir_blk{ @"L175":
    %"v186" : L = (Ext Sw) %"pr.9";
    call %"iw_1.v3" : W = $"__GI___libc_alloca_cutoff"(L %"v186");
    %"iw_1.v4" : L = (Ext Sw) %"iw_1.v3";
    %"iw_1.v5" : W = (Cmp Ne L) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "iw_1.L7" : "iw_1.L6" };
  ir_blk{ @"iw_1.L6":
    %"iw_1.v11" : W = (Cmp Ule L) %"v186", #4096
    => goto "iw_1.L7" };
  ir_blk{ @"iw_1.L7" [%"iw_1.v15" : W = phi("L175" => #1, "iw_1.L6" => %"iw_1.v11")]:
    => br %"iw_1.v15" ? "L182" : "L183" };
  ir_blk{ @"L182":
    %"v190" : P = (Alloc 16) %"v186"
    => goto "L184" };
  ir_blk{ @"L183":
    call %"v196" : P = $"malloc"(L %"v186");
    %"v197" : L = Ptoi %"v196";
    %"v199" : W = (Cmp Eq L) %"v197", %"v90"
    => br %"v199" ? "L184" : "L192" };
  ir_blk{ @"L192":
    => goto "L184" };
  ir_blk{ @"L184" [%"pr.37" : W = phi("L182" => %"pr.39", "L192" => %"pr.39", "L183" => #1); %"pr.28" : W = phi("L182" => %"pr.30", "L192" => #1, "L183" => %"pr.30"); %"pr.20" : P = phi("L182" => %"v190", "L192" => %"v196", "L183" => %"v196")]:
    %"v204" : L = Ptoi %"pr.20";
    %"v205" : W = (Cmp Ne L) %"v204", #0
    => br %"v205" ? "L200" : "L172" };
  ir_blk{ @"L200":
    call %"v209" : P = $"__GI_memset"(P %"pr.20", W #0, L %"v186");
    %"v212" : L = (Ext Sw) %"pr.42";
    %"v213" = %"pr.20" +p %"v212";
    %"chk17" : A = (Check 0 1 Write 1) %"v213";
    store Wb [%"chk17" + 0] <- #1
    => goto "L172" };
  ir_blk{ @"L172" [%"pr.35" : W = phi("L165" => #1, "L200" => %"pr.37", "L184" => %"pr.37", "L171" => %"pr.39"); %"pr.26" : W = phi("L165" => %"pr.30", "L200" => %"pr.28", "L184" => %"pr.28", "L171" => %"pr.30"); %"pr.18" : P = phi("L165" => %"pr.21", "L200" => %"pr.20", "L184" => %"pr.20", "L171" => %"pr.21")]:
    %"v218" : L = Ptoi %"pr.18";
    %"v219" : W = (Cmp Ne L) %"v218", #0
    => br %"v219" ? "L214" : "L108" };
  ir_blk{ @"L214":
    %"v222" : L = (Ext Sw) %"pr.13";
    %"v223" = %"pr.18" +p %"v222";
    %"chk18" : A = (Check 0 1 Write 1) %"v223";
    store Wb [%"chk18" + 0] <- #1
    => goto "L108" };
  ir_blk{ @"L108" [%"pr.40" : W = phi("L106" => %"pr.13", "L214" => %"pr.42", "L172" => %"pr.42", "L126" => %"pr.42", "L155" => %"pr.42", "L99" => %"pr.42"); %"pr.31" : W = phi("L106" => %"pr.39", "L214" => %"pr.35", "L172" => %"pr.35", "L126" => %"pr.39", "L155" => %"pr.39", "L99" => %"pr.39"); %"pr.22" : W = phi("L106" => %"pr.30", "L214" => %"pr.26", "L172" => %"pr.26", "L126" => %"pr.30", "L155" => %"pr.30", "L99" => %"pr.30"); %"pr.14" : P = phi("L106" => %"pr.21", "L214" => %"pr.18", "L172" => %"pr.18", "L126" => %"pr.21", "L155" => %"pr.21", "L99" => %"pr.21"); %"pr.4" : P = phi("L106" => %"pr.3", "L214" => %"pr.8", "L172" => %"pr.8", "L126" => %"pr.8", "L155" => %"pr.8", "L99" => %"pr.8")]:
    %"v225" = %"pr.3" +p #32;
    %"v227" : W = Add %"pr.13", #1
    => goto poll "L98" };
  ir_blk{ @"L101":
    %"v232" : L = Ptoi %"pr.21";
    %"v233" : W = (Cmp Ne L) %"v232", #0
    => br %"v233" ? "L235" : "L234" };
  ir_blk{ @"L234":
    %"v237" : W = (Cmp Ne W) %"pr.39", #0
    => goto "L235" };
  ir_blk{ @"L235" [%"v238" : W = phi("L101" => #1, "L234" => %"v237")]:
    => br %"v238" ? "L228" : "L87" };
  ir_blk{ @"L228":
    => br %"v14" ? "L239" : "L241" }] [ir_blk{ @"L239":
    => br %"pr.39" ? "L243" : "L244" };
  ir_blk{ @"L243":
    %"v247" : P = Copy $"stderr";
    %"chk19" : A = (Check 0 8 Read 8) %"v247";
    %"v248" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v249" : P = Copy $"__GI__libc_intl_domainname";
    %"v250" : P = Copy $"glibc_getopt#str.138";
    call %"v251" : P = $"__GI___dcgettext"(P %"v249", P %"v250", W #5);
    %"chk20" : A = (Check 0 8 Read 8) %"v2";
    %"v254" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v257" = %"v12" +p #32;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk0", %"v257";
    %"v258" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"v259" : W = $"__fxprintf_nocancel"(P %"v248", P %"v251", P %"v254", P %"v16", P %"v258")
    => goto "L241" };
  ir_blk{ @"L244":
    %"v260" : P = Copy $"stderr";
    %"chk22" : A = (Check 0 8 Read 8) %"v260";
    %"v261" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v262" : P = Copy $"__GI__libc_intl_domainname";
    %"v263" : P = Copy $"glibc_getopt#str.139";
    call %"v264" : P = $"__GI___dcgettext"(P %"v262", P %"v263", W #5);
    %"chk23" : A = (Check 0 8 Read 8) %"v2";
    %"v267" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v270" = %"v12" +p #32;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"v270";
    %"v271" : P = (RawLoadPointer 0 load_effects) %"chk24";
    call %"v272" : W = $"__fxprintf_nocancel"(P %"v261", P %"v264", P %"v267", P %"v16", P %"v271")
    => goto "L273" };
  ir_blk{ @"L273" [%"pr.10" : W = phi("L244" => #0, "L275" => %"v300")]:
    %"v279" : W = (Cmp Slt W) %"pr.10", %"pr.9"
    => br %"v279" ? "L274" : "L276" };
  ir_blk{ @"L274":
    %"v285" : L = (Ext Sw) %"pr.10";
    %"v286" = %"pr.21" +p %"v285";
    %"chk25" : A = (Check 0 1 Read 1) %"v286";
    %"v287" : W = (RawLoad (LdNarrow Ub) 0) %"chk25"
    => br %"v287" ? "L280" : "L275" };
  ir_blk{ @"L280":
    %"v288" : P = Copy $"stderr";
    %"chk26" : A = (Check 0 8 Read 8) %"v288";
    %"v289" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v290" : P = Copy $"glibc_getopt#str.140";
    %"v295" : L = Shl %"v285", #5;
    %"v296" = %"v6" +p %"v295";
    %"chk27" : A = (Check 0 8 Read 8) %"v296";
    %"v297" : P = (RawLoadPointer 0 load_effects) %"chk27";
    call %"v298" : W = $"__fxprintf_nocancel"(P %"v289", P %"v290", P %"v16", P %"v297")
    => goto "L275" };
  ir_blk{ @"L275":
    %"v300" : W = Add %"pr.10", #1
    => goto poll "L273" };
  ir_blk{ @"L276":
    %"v301" : P = Copy $"stderr";
    %"chk28" : A = (Check 0 8 Read 8) %"v301";
    %"v302" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v303" : P = Copy $"glibc_getopt#str.141";
    call %"v304" : W = $"__fxprintf_nocancel"(P %"v302", P %"v303")
    => goto "L241" };
  ir_blk{ @"L241":
    => br %"pr.30" ? "L305" : "L307" };
  ir_blk{ @"L305":
    call void $"free"(P %"pr.21")
    => goto "L307" };
  ir_blk{ @"L307":
    %"v311" = %"v12" +p #32;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v311";
    %"v312" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v315" : P = (RawLoadPointer 0 load_effects) %"chk29";
    call %"v316" : L = $"__GI_strlen"(P %"v315");
    %"v317" = %"v312" +p %"v316";
    %"chk31" : A = (Renew 0 8 Write 8) %"chk0", %"v311";
    store.ptr [%"chk31" + 0] <- %"v317";
    %"chk32" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v319" : W = (RawLoad (LdNarrow Sw) 0) %"chk32";
    %"v320" : W = Add %"v319", #1;
    %"chk33" : A = (Renew 0 4 Write 1) %"chk32", %"v12";
    store Ww [%"chk33" + 0] <- %"v320";
    %"v322" = %"v12" +p #8;
    %"chk34" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v322";
    store Ww [%"chk34" + 0] <- #0
    => ret #63 };
  ir_blk{ @"L87" [%"pr.12" : W = phi("L235" => %"pr.42", "L53" => %"pr.11"); %"pr.7" : P = phi("L235" => %"pr.8", "L53" => %"pr.6")]:
    %"v329" : L = Ptoi %"pr.7";
    %"v331" : W = (Cmp Eq L) %"v329", %"v90"
    => br %"v331" ? "L325" : "L327" };
  ir_blk{ @"L325":
    %"v336" : W = (Cmp Eq W) %"v10", #0
    => br %"v336" ? "L338" : "L337" };
  ir_blk{ @"L337":
    %"chk35" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v341" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v342" : L = (Ext Sw) %"v341";
    %"v343" : L = Shl %"v342", #3;
    %"v344" = %"v2" +p %"v343";
    %"chk36" : A = (Check 0 8 Read 8) %"v344";
    %"v345" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v346" = %"v345" +p #1;
    %"chk37" : A = (Check 0 1 Read 1) %"v346";
    %"v347" : W = (RawLoad (LdNarrow Sb) 0) %"chk37";
    %"v348" : W = (Cmp Eq W) %"v347", #45
    => goto "L338" };
  ir_blk{ @"L338" [%"v350" : W = phi("L325" => #1, "L337" => %"v348")]:
    => br %"v350" ? "L352" : "L351" };
  ir_blk{ @"L351":
    %"v355" = %"v12" +p #32;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk0", %"v355";
    %"v356" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 1 Read 1) %"v356";
    %"v357" : W = (RawLoad (LdNarrow Sb) 0) %"chk39";
    call %"v358" : P = $"__GI_strchr"(P %"v4", W %"v357");
    %"v359" : L = Ptoi %"v358";
    %"v361" : W = (Cmp Eq L) %"v359", %"v90"
    => goto "L352" };
  ir_blk{ @"L352" [%"v363" : W = phi("L338" => #1, "L351" => %"v361")]:
    => br %"v363" ? "L332" : "L334" };
  ir_blk{ @"L332":
    => br %"v14" ? "L364" : "L366" };
  ir_blk{ @"L364":
    %"v368" : P = Copy $"stderr";
    %"chk40" : A = (Check 0 8 Read 8) %"v368";
    %"v369" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v370" : P = Copy $"__GI__libc_intl_domainname";
    %"v371" : P = Copy $"glibc_getopt#str.142";
    call %"v372" : P = $"__GI___dcgettext"(P %"v370", P %"v371", W #5);
    %"chk41" : A = (Check 0 8 Read 8) %"v2";
    %"v375" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v378" = %"v12" +p #32;
    %"chk42" : A = (Renew 0 8 Read 8) %"chk0", %"v378";
    %"v379" : P = (RawLoadPointer 0 load_effects) %"chk42";
    call %"v380" : W = $"__fxprintf_nocancel"(P %"v369", P %"v372", P %"v375", P %"v16", P %"v379")
    => goto "L366" };
  ir_blk{ @"L366":
    %"v382" = %"v12" +p #32;
    %"chk43" : A = (Renew 0 8 Write 8) %"chk0", %"v382";
    store.ptr [%"chk43" + 0] <- #0;
    %"chk44" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v384" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"v385" : W = Add %"v384", #1;
    %"chk45" : A = (Renew 0 4 Write 1) %"chk44", %"v12";
    store Ww [%"chk45" + 0] <- %"v385";
    %"v387" = %"v12" +p #8;
    %"chk46" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v387";
    store Ww [%"chk46" + 0] <- #0
    => ret #63 };
  ir_blk{ @"L334":
    => ret #4294967295 };
  ir_blk{ @"L327":
    %"chk47" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v392" : W = (RawLoad (LdNarrow Sw) 0) %"chk47";
    %"v393" : W = Add %"v392", #1;
    %"chk48" : A = (Renew 0 4 Write 1) %"chk47", %"v12";
    store Ww [%"chk48" + 0] <- %"v393";
    %"v395" = %"v12" +p #32;
    %"chk49" : A = (Renew 0 8 Write 8) %"chk0", %"v395";
    store.ptr [%"chk49" + 0] <- #0;
    %"chk50" : A = (Renew 0 1 Read 1) %"chk1", %"pr.1";
    %"v400" : W = (RawLoad (LdNarrow Sb) 0) %"chk50"
    => br %"v400" ? "L396" : "L397" };
  ir_blk{ @"L396":
    %"v405" = %"pr.7" +p #8;
    %"chk51" : A = (Check 0 4 Read 1) %"v405";
    %"v406" : W = (RawLoad (LdNarrow Sw) 0) %"chk51"
    => br %"v406" ? "L401" : "L402" };
  ir_blk{ @"L401":
    %"v408" = %"v12" +p #16;
    %"v410" = %"pr.1" +p #1;
    %"chk52" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v408";
    store.ptr [%"chk52" + 0] <- %"v410"
    => goto "L398" };
  ir_blk{ @"L402":
    => br %"v14" ? "L411" : "L413" };
  ir_blk{ @"L411":
    %"v415" : P = Copy $"stderr";
    %"chk53" : A = (Check 0 8 Read 8) %"v415";
    %"v416" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v417" : P = Copy $"__GI__libc_intl_domainname";
    %"v418" : P = Copy $"glibc_getopt#str.143";
    call %"v419" : P = $"__GI___dcgettext"(P %"v417", P %"v418", W #5);
    %"chk54" : A = (Check 0 8 Read 8) %"v2";
    %"v422" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"chk55" : A = (HalfCheck Lower 0 8 Read 8) %"chk51", %"pr.7";
    %"v425" : P = (RawLoadPointer 0 load_effects) %"chk55";
    call %"v426" : W = $"__fxprintf_nocancel"(P %"v416", P %"v419", P %"v422", P %"v16", P %"v425")
    => goto "L413" };
  ir_blk{ @"L413":
    %"v428" = %"v12" +p #8;
    %"v430" = %"pr.7" +p #24;
    %"chk56" : A = (HalfCheck Upper 0 4 Read 1) %"chk51", %"v430";
    %"v431" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"chk57" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v428";
    store Ww [%"chk57" + 0] <- %"v431"
    => ret #63 };
  ir_blk{ @"L397":
    %"v436" = %"pr.7" +p #8;
    %"chk58" : A = (Check 0 4 Read 1) %"v436";
    %"v437" : W = (RawLoad (LdNarrow Sw) 0) %"chk58";
    %"v438" : W = (Cmp Eq W) %"v437", #1
    => br %"v438" ? "L432" : "L398" };
  ir_blk{ @"L432":
    %"chk59" : A = (Renew 0 4 Read 1) %"chk47", %"v12";
    %"v443" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"v445" : W = (Cmp Slt W) %"v443", %"v0"
    => br %"v445" ? "L439" : "L440" };
  ir_blk{ @"L439":
    %"v447" = %"v12" +p #16;
    %"v450" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"v451" : W = Add %"v450", #1;
    %"chk61" : A = (Renew 0 4 Write 1) %"chk47", %"v12";
    store Ww [%"chk61" + 0] <- %"v451";
    %"v452" : L = (Ext Sw) %"v450";
    %"v453" : L = Shl %"v452", #3;
    %"v454" = %"v2" +p %"v453";
    %"chk62" : A = (Check 0 8 Read 8) %"v454";
    %"v455" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"chk63" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v447";
    store.ptr [%"chk63" + 0] <- %"v455"
    => goto "L398" };
  ir_blk{ @"L440":
    => br %"v14" ? "L456" : "L458" };
  ir_blk{ @"L456":
    %"v460" : P = Copy $"stderr";
    %"chk64" : A = (Check 0 8 Read 8) %"v460";
    %"v461" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v462" : P = Copy $"__GI__libc_intl_domainname";
    %"v463" : P = Copy $"glibc_getopt#str.144";
    call %"v464" : P = $"__GI___dcgettext"(P %"v462", P %"v463", W #5);
    %"chk65" : A = (Check 0 8 Read 8) %"v2";
    %"v467" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (HalfCheck Lower 0 8 Read 8) %"chk58", %"pr.7";
    %"v470" : P = (RawLoadPointer 0 load_effects) %"chk66";
    call %"v471" : W = $"__fxprintf_nocancel"(P %"v461", P %"v464", P %"v467", P %"v16", P %"v470")
    => goto "L458" };
  ir_blk{ @"L458":
    %"v473" = %"v12" +p #8;
    %"v475" = %"pr.7" +p #24;
    %"chk67" : A = (HalfCheck Upper 0 4 Read 1) %"chk58", %"v475";
    %"v476" : W = (RawLoad (LdNarrow Sw) 0) %"chk67";
    %"chk68" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v473";
    store Ww [%"chk68" + 0] <- %"v476";
    %"chk69" : A = (Check 0 1 Read 1) %"v4";
    %"v482" : W = (RawLoad (LdNarrow Sb) 0) %"chk69";
    %"v483" : W = (Cmp Eq W) %"v482", #58
    => br %"v483" ? "L479" : "L478" };
  ir_blk{ @"L478":
    => goto "L479" };
  ir_blk{ @"L479" [%"v484" : W = phi("L478" => #63, "L458" => #58)]:
    => ret %"v484" };
  ir_blk{ @"L398":
    %"v489" : L = Ptoi %"v8";
    %"v491" : W = (Cmp Ne L) %"v489", %"v90"
    => br %"v491" ? "L485" : "L487" };
  ir_blk{ @"L485":
    %"chk70" : A = (Check 0 4 Write 1) %"v8";
    store Ww [%"chk70" + 0] <- %"pr.12"
    => goto "L487" };
  ir_blk{ @"L487":
    %"v498" = %"pr.7" +p #16;
    %"chk71" : A = (Check 0 8 Read 8) %"v498";
    %"v499" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v500" : L = Ptoi %"v499";
    %"v501" : W = (Cmp Ne L) %"v500", #0
    => br %"v501" ? "L494" : "L496" };
  ir_blk{ @"L494":
    %"v503" = %"pr.7" +p #16;
    %"v504" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v506" = %"pr.7" +p #24;
    %"chk73" : A = (HalfCheck Upper 0 4 Read 1) %"chk71", %"v506";
    %"v507" : W = (RawLoad (LdNarrow Sw) 0) %"chk73";
    %"chk74" : A = (Check 0 4 Write 1) %"v504";
    store Ww [%"chk74" + 0] <- %"v507"
    => ret #0 };
  ir_blk{ @"L496":
    %"v510" = %"pr.7" +p #24;
    %"chk75" : A = (HalfCheck Upper 0 4 Read 1) %"chk71", %"v510";
    %"v511" : W = (RawLoad (LdNarrow Sw) 0) %"chk75"
    => ret %"v511" }])) }.

Definition item_glibc_getopt'23str'2e138 : item :=
  (IData (a "glibc_getopt#str.138") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 109); (Item Wb 98); (Item Wb 105); (Item Wb 103); (Item Wb 117); (Item Wb 111); (Item Wb 117); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e139 : item :=
  (IData (a "glibc_getopt#str.139") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 109); (Item Wb 98); (Item Wb 105); (Item Wb 103); (Item Wb 117); (Item Wb 111); (Item Wb 117); (Item Wb 115); (Item Wb 59); (Item Wb 32); (Item Wb 112); (Item Wb 111); (Item Wb 115); (Item Wb 115); (Item Wb 105); (Item Wb 98); (Item Wb 105); (Item Wb 108); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 101); (Item Wb 115); (Item Wb 58); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e140 : item :=
  (IData (a "glibc_getopt#str.140") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e141 : item :=
  (IData (a "glibc_getopt#str.141") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e142 : item :=
  (IData (a "glibc_getopt#str.142") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 117); (Item Wb 110); (Item Wb 114); (Item Wb 101); (Item Wb 99); (Item Wb 111); (Item Wb 103); (Item Wb 110); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e143 : item :=
  (IData (a "glibc_getopt#str.143") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 32); (Item Wb 100); (Item Wb 111); (Item Wb 101); (Item Wb 115); (Item Wb 110); (Item Wb 39); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e144 : item :=
  (IData (a "glibc_getopt#str.144") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e145 : item :=
  (IData (a "glibc_getopt#str.145") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 79); (Item Wb 83); (Item Wb 73); (Item Wb 88); (Item Wb 76); (Item Wb 89); (Item Wb 95); (Item Wb 67); (Item Wb 79); (Item Wb 82); (Item Wb 82); (Item Wb 69); (Item Wb 67); (Item Wb 84); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e146 : item :=
  (IData (a "glibc_getopt#str.146") (LRo (a "local")) 1 [(Item Wb 45); (Item Wb 45); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e147 : item :=
  (IData (a "glibc_getopt#str.147") (LRo (a "local")) 1 [(Item Wb 45); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e148 : item :=
  (IData (a "glibc_getopt#str.148") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 99); (Item Wb 39); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e149 : item :=
  (IData (a "glibc_getopt#str.149") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 99); (Item Wb 39); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_getopt'23str'2e150 : item :=
  (IData (a "glibc_getopt#str.150") (LRo (a "local")) 1 [(Item Wb 45); (Item Wb 87); (Item Wb 32); (Item Wb 0)]).

Definition item_optarg : item :=
  (IData (a "optarg") LExport 8 [(Zero 8)]).

Definition item_opterr : item :=
  (IData (a "opterr") LExport 4 [(Item Ww 1)]).

Definition item_optind : item :=
  (IData (a "optind") LExport 4 [(Item Ww 1)]).

Definition item_optopt : item :=
  (IData (a "optopt") LExport 4 [(Item Ww 63)]).
