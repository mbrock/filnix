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

Definition hello_image_fn__getopt_internal_r : func :=
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

Definition hello_image_fn__getopt_internal : func :=
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

Definition hello_image_fn_getopt_long : func :=
  ir_fn{ "export" "getopt_long"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8") -> (RClass W) {
  @"start":
    call %"v15" : W = $"_getopt_internal"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8", W #0, W #0)
    => ret %"v15"
} }.

Definition hello_image_fn___GI___getrlimit64 : func :=
  ir_fn{ "export" "__GI___getrlimit64"(W %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v6" : W = $"zsys_getrlimit"(W %"v0", P %"v2")
    => ret %"v6"
} }.

Definition hello_image_fn___get_errlist : func :=
  ir_fn{ "export" "__get_errlist"(W %"v0") -> (RClass P) {
  @"start":
    %"v8" : W = (Cmp Sge W) %"v0", #0
    => br %"v8" ? "L9" : "L10";
  @"L9":
    %"v12" : P = Copy $"_sys_errlist_internal_len";
    %"chk0" : A = (Check 0 8 Read 1) %"v12";
    %"v13" : L = (RawLoad LdL 0) %"chk0";
    %"v14" : L = (Ext Sw) %"v0";
    %"v15" : W = (Cmp Ult L) %"v14", %"v13"
    => goto "L10";
  @"L10" [%"v17" : W = phi("start" => #0, "L9" => %"v15")]:
    => br %"v17" ? "L4" : "L6";
  @"L4":
    %"v18" : P = Copy $"_sys_errlist_internal";
    %"v20" : L = (Ext Sw) %"v0";
    %"v21" : L = Shl %"v20", #3;
    %"v22" = %"v18" +p %"v21";
    %"chk1" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => ret %"v23";
  @"L6":
    => ret #0
} }.

Definition hello_image_fn___get_errname : func :=
  ir_fn{ "export" "__get_errname"(W %"v0") -> (RClass P) {
  @"start":
    %"v8" : W = (Cmp Slt W) %"v0", #0
    => br %"v8" ? "L10" : "L9";
  @"L9":
    %"v15" : L = (Ext Sw) %"v0";
    %"v16" : W = (Cmp Uge L) %"v15", #134
    => goto "L10";
  @"L10" [%"v18" : W = phi("start" => #1, "L9" => %"v16")]:
    => br %"v18" ? "L20" : "L19";
  @"L19":
    %"v22" : W = (Cmp Sgt W) %"v0", #0
    => br %"v22" ? "L23" : "L20";
  @"L23":
    %"v25" : P = Copy $"glibc_errname#_sys_errnameidx";
    %"v27" : L = (Ext Sw) %"v0";
    %"v28" : L = Shl %"v27", #1;
    %"v29" = %"v25" +p %"v28";
    %"chk0" : A = (Check 0 2 Read 1) %"v29";
    %"v30" : W = (RawLoad (LdNarrow Uh) 0) %"chk0";
    %"v31" : W = (Cmp Eq W) %"v30", #0
    => goto "L20";
  @"L20" [%"v35" : W = phi("L10" => #1, "L19" => #0, "L23" => %"v31")]:
    => br %"v35" ? "L4" : "L6";
  @"L4":
    => ret #0;
  @"L6":
    %"v37" : P = Copy $"glibc_errname#_sys_errname";
    %"v38" : P = Copy $"glibc_errname#_sys_errnameidx";
    %"v40" : L = (Ext Sw) %"v0";
    %"v41" : L = Shl %"v40", #1;
    %"v42" = %"v38" +p %"v41";
    %"chk1" : A = (Check 0 2 Read 1) %"v42";
    %"v43" : W = (RawLoad (LdNarrow Uh) 0) %"chk1";
    %"v44" : L = (Ext Uw) %"v43";
    %"v45" = %"v37" +p %"v44"
    => ret %"v45"
} }.

Definition hello_image_fn_glibc_printf_fp'23get_rounding_mode : func :=
  ir_fn{ "local" "glibc_printf_fp#get_rounding_mode"() -> (RClass W) {
  @"start":
    call %"v7" : W = $"zmath_getcw"();
    %"v8" : W = (Ext Uh) %"v7";
    %"v11" : W = And %"v8", #3072;
    %"v19" : W = (Cmp Eq W) %"v11", #1024
    => br %"v19" ? "L14" : "L20";
  @"L14":
    => ret #1024;
  @"L15":
    => ret #0;
  @"L16":
    => ret #3072;
  @"L17":
    => ret #2048;
  @"L18":
    call void $"__GI_abort"()
    => ret #0;
  @"L20":
    %"v21" : W = (Cmp Eq W) %"v11", #0
    => br %"v21" ? poll "L15" : "L22";
  @"L22":
    %"v23" : W = (Cmp Eq W) %"v11", #3072
    => br %"v23" ? poll "L16" : "L24";
  @"L24":
    %"v25" : W = (Cmp Eq W) %"v11", #2048
    => br %"v25" ? poll "L17" : poll "L18"
} }.

Definition hello_image_fn___GI_getenv : func :=
  ir_fn{ "export" "__GI_getenv"(P %"v0") -> (RClass P) {
  @"start":
    => goto "L3";
  @"L3":
    %"v6" : P = Copy $"__environ_counter";
    %"chk0" : A = (Check 0 8 Read 1) %"v6";
    %"v7" : L = (RawLoad LdL 0) %"chk0";
    %"v9" : P = Copy $"__environ";
    %"chk1" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 [AtomicRead]) %"chk1";
    %"v15" : L = Ptoi %"v10";
    %"v16" : L = Ptoi #0;
    %"v17" : W = (Cmp Eq L) %"v15", %"v16"
    => br %"v17" ? "L19" : "L18";
  @"L18":
    %"chk2" : A = (Check 0 1 Read 1) %"v0";
    %"v22" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v23" : W = (Cmp Eq W) %"v22", #0
    => goto "L19";
  @"L19" [%"v25" : W = phi("L3" => #1, "L18" => %"v23")]:
    => br %"v25" ? "L11" : "L13";
  @"L11":
    => ret #0;
  @"L13":
    call %"v29" : L = $"__GI_strlen"(P %"v0")
    => goto "L32";
  @"L32" [%"pr.1" : P = phi("L13" => %"v10", "L34" => %"v81")]:
    %"chk3" : A = (Check 0 8 Read 8) %"pr.1";
    %"v38" : P = (RawLoadPointer 0 [AtomicRead]) %"chk3";
    %"v43" : L = Ptoi %"v38";
    %"v45" : W = (Cmp Eq L) %"v43", %"v16"
    => br %"v45" ? "L35" : "L41";
  @"L41":
    %"chk4" : A = (Check 0 1 Read 1) %"v0";
    %"v52" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"chk5" : A = (Check 0 1 Read 1) %"v38";
    %"v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v56" : W = (Cmp Eq W) %"v52", %"v55"
    => br %"v56" ? "L57" : "L58";
  @"L57":
    call %"v62" : W = $"__GI_strncmp"(P %"v0", P %"v38", L %"v29");
    %"v63" : W = (Cmp Eq W) %"v62", #0
    => goto "L58";
  @"L58" [%"v65" : W = phi("L41" => #0, "L57" => %"v63")]:
    => br %"v65" ? "L66" : "L67";
  @"L66":
    %"v70" = %"v38" +p %"v29";
    %"chk6" : A = (Check 0 1 Read 1) %"v70";
    %"v71" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v72" : W = (Cmp Eq W) %"v71", #61
    => goto "L67";
  @"L67" [%"v74" : W = phi("L58" => #0, "L66" => %"v72")]:
    => br %"v74" ? "L47" : "L34";
  @"L47":
    %"v77" = %"v38" +p %"v29";
    %"v78" = %"v77" +p #1
    => ret %"v78";
  @"L34":
    %"v81" = %"pr.1" +p #8
    => goto poll "L32";
  @"L35":
    %"v85" : P = Copy $"__environ_counter";
    %"chk7" : A = (Check 0 8 Read 1) %"v85";
    %"v86" : L = (RawLoad LdL 0) %"chk7";
    %"v88" : W = (Cmp Eq L) %"v86", %"v7"
    => br %"v88" ? "L82" : poll "L3";
  @"L82":
    => ret #0
} }.

Definition hello_image_fn_glibc_libc_start'23get_isa_level : func :=
  ir_fn{ "local" "glibc_libc_start#get_isa_level"(P %"v0") -> (RClass W) {
  @"start":
    %"v7" = %"v0" +p #20;
    %"v9" = %"v7" +p #16;
    %"v10" = %"v9" +p #12;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v13" : W = And %"v11", #32768;
    %"v14" : W = (Cmp Ne W) %"v13", #0
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v18" = %"v0" +p #20;
    %"v20" = %"v18" +p #16;
    %"v21" = %"v20" +p #12;
    %"v22" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v24" : W = And %"v22", #256;
    %"v25" : W = (Cmp Ne W) %"v24", #0
    => goto "L16";
  @"L16" [%"v27" : W = phi("start" => #0, "L15" => %"v25")]:
    => br %"v27" ? "L28" : "L29";
  @"L28":
    %"v31" = %"v0" +p #20;
    %"v33" = %"v31" +p #12;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v33";
    %"v34" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v36" : W = And %"v34", #1
    => goto "L29";
  @"L29" [%"v39" : W = phi("L16" => #0, "L28" => %"v36")]:
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v43" = %"v0" +p #20;
    %"v45" = %"v43" +p #16;
    %"v46" = %"v45" +p #12;
    %"v47" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v49" : W = And %"v47", #16777216;
    %"v50" : W = (Cmp Ne W) %"v49", #0
    => goto "L41";
  @"L41" [%"v52" : W = phi("L29" => #0, "L40" => %"v50")]:
    => br %"v52" ? "L53" : "L54";
  @"L53":
    %"v56" = %"v0" +p #20;
    %"v58" = %"v56" +p #16;
    %"v59" = %"v58" +p #12;
    %"v60" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v62" : W = And %"v60", #8388608;
    %"v63" : W = (Cmp Ne W) %"v62", #0
    => goto "L54";
  @"L54" [%"v65" : W = phi("L41" => #0, "L53" => %"v63")]:
    => br %"v65" ? "L66" : "L67";
  @"L66":
    %"v69" = %"v0" +p #20;
    %"v71" = %"v69" +p #16;
    %"v72" = %"v71" +p #12;
    %"v73" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v75" : W = And %"v73", #33554432;
    %"v76" : W = (Cmp Ne W) %"v75", #0
    => goto "L67";
  @"L67" [%"v78" : W = phi("L54" => #0, "L66" => %"v76")]:
    => br %"v78" ? "L79" : "L80";
  @"L79":
    %"v82" = %"v0" +p #20;
    %"v84" = %"v82" +p #16;
    %"v85" = %"v84" +p #12;
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v88" : W = And %"v86", #67108864;
    %"v89" : W = (Cmp Ne W) %"v88", #0
    => goto "L80";
  @"L80" [%"v91" : W = phi("L67" => #0, "L79" => %"v89")]:
    => br %"v91" ? "L3" : "L5";
  @"L3":
    %"v97" = %"v0" +p #20;
    %"v99" = %"v97" +p #16;
    %"v100" = %"v99" +p #8;
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v100";
    %"v101" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v103" : W = And %"v101", #8192;
    %"v104" : W = (Cmp Ne W) %"v103", #0
    => br %"v104" ? "L105" : "L106";
  @"L105":
    %"v108" = %"v0" +p #20;
    %"v109" = %"v108" +p #64;
    %"v110" = %"v109" +p #16;
    %"v111" = %"v110" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v111";
    %"v112" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v114" : W = And %"v112", #1
    => goto "L106";
  @"L106" [%"v117" : W = phi("L3" => #0, "L105" => %"v114")]:
    => br %"v117" ? "L118" : "L119";
  @"L118":
    %"v121" = %"v0" +p #20;
    %"v123" = %"v121" +p #16;
    %"v124" = %"v123" +p #8;
    %"v125" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v127" : W = And %"v125", #8388608;
    %"v128" : W = (Cmp Ne W) %"v127", #0
    => goto "L119";
  @"L119" [%"v130" : W = phi("L106" => #0, "L118" => %"v128")]:
    => br %"v130" ? "L131" : "L132";
  @"L131":
    %"v134" = %"v0" +p #20;
    %"v136" = %"v134" +p #16;
    %"v137" = %"v136" +p #8;
    %"v138" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v140" : W = And %"v138", #1
    => goto "L132";
  @"L132" [%"v143" : W = phi("L119" => #0, "L131" => %"v140")]:
    => br %"v143" ? "L144" : "L145";
  @"L144":
    %"v147" = %"v0" +p #20;
    %"v149" = %"v147" +p #16;
    %"v150" = %"v149" +p #8;
    %"v151" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v153" : W = And %"v151", #512;
    %"v154" : W = (Cmp Ne W) %"v153", #0
    => goto "L145";
  @"L145" [%"v156" : W = phi("L132" => #0, "L144" => %"v154")]:
    => br %"v156" ? "L157" : "L158";
  @"L157":
    %"v160" = %"v0" +p #20;
    %"v162" = %"v160" +p #16;
    %"v163" = %"v162" +p #8;
    %"v164" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v166" : W = And %"v164", #524288;
    %"v167" : W = (Cmp Ne W) %"v166", #0
    => goto "L158";
  @"L158" [%"v169" : W = phi("L145" => #0, "L157" => %"v167")]:
    => br %"v169" ? "L170" : "L171";
  @"L170":
    %"v173" = %"v0" +p #20;
    %"v175" = %"v173" +p #16;
    %"v176" = %"v175" +p #8;
    %"v177" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v179" : W = And %"v177", #1048576;
    %"v180" : W = (Cmp Ne W) %"v179", #0
    => goto "L171";
  @"L171" [%"v182" : W = phi("L158" => #0, "L170" => %"v180")]:
    => br %"v182" ? "L93" : "L5";
  @"L93":
    %"v190" = %"v0" +p #20;
    %"v192" = %"v190" +p #16;
    %"v193" = %"v192" +p #8;
    %"v194" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v196" : W = And %"v194", #268435456;
    %"v197" : W = (Cmp Ne W) %"v196", #0
    => br %"v197" ? "L198" : "L199";
  @"L198":
    %"v201" = %"v0" +p #20;
    %"v202" = %"v201" +p #32;
    %"v203" = %"v202" +p #16;
    %"v204" = %"v203" +p #4;
    %"chk15" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v204";
    %"v205" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"v207" : W = And %"v205", #32;
    %"v208" : W = (Cmp Ne W) %"v207", #0
    => goto "L199";
  @"L199" [%"v210" : W = phi("L93" => #0, "L198" => %"v208")]:
    => br %"v210" ? "L211" : "L212";
  @"L211":
    %"v214" = %"v0" +p #20;
    %"v215" = %"v214" +p #32;
    %"v216" = %"v215" +p #16;
    %"v217" = %"v216" +p #4;
    %"chk16" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v217";
    %"v218" : W = (RawLoad (LdNarrow Uw) 0) %"chk16";
    %"v220" : W = And %"v218", #8;
    %"v221" : W = (Cmp Ne W) %"v220", #0
    => goto "L212";
  @"L212" [%"v223" : W = phi("L199" => #0, "L211" => %"v221")]:
    => br %"v223" ? "L224" : "L225";
  @"L224":
    %"v227" = %"v0" +p #20;
    %"v228" = %"v227" +p #32;
    %"v229" = %"v228" +p #16;
    %"v230" = %"v229" +p #4;
    %"chk17" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v230";
    %"v231" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v233" : W = And %"v231", #256;
    %"v234" : W = (Cmp Ne W) %"v233", #0
    => goto "L225";
  @"L225" [%"v236" : W = phi("L212" => #0, "L224" => %"v234")]:
    => br %"v236" ? "L237" : "L238";
  @"L237":
    %"v240" = %"v0" +p #20;
    %"v242" = %"v240" +p #16;
    %"v243" = %"v242" +p #8;
    %"v244" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v246" : W = And %"v244", #536870912;
    %"v247" : W = (Cmp Ne W) %"v246", #0
    => goto "L238";
  @"L238" [%"v249" : W = phi("L225" => #0, "L237" => %"v247")]:
    => br %"v249" ? "L250" : "L251";
  @"L250":
    %"v253" = %"v0" +p #20;
    %"v255" = %"v253" +p #16;
    %"v256" = %"v255" +p #8;
    %"v257" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v259" : W = And %"v257", #4096;
    %"v260" : W = (Cmp Ne W) %"v259", #0
    => goto "L251";
  @"L251" [%"v262" : W = phi("L238" => #0, "L250" => %"v260")]:
    => br %"v262" ? "L263" : "L264";
  @"L263":
    %"v266" = %"v0" +p #20;
    %"v267" = %"v266" +p #64;
    %"v268" = %"v267" +p #16;
    %"v269" = %"v268" +p #8;
    %"chk20" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v269";
    %"v270" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v272" : W = And %"v270", #32;
    %"v273" : W = (Cmp Ne W) %"v272", #0
    => goto "L264";
  @"L264" [%"v275" : W = phi("L251" => #0, "L263" => %"v273")]:
    => br %"v275" ? "L276" : "L277";
  @"L276":
    %"v279" = %"v0" +p #20;
    %"v281" = %"v279" +p #16;
    %"v282" = %"v281" +p #8;
    %"v283" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v285" : W = And %"v283", #4194304;
    %"v286" : W = (Cmp Ne W) %"v285", #0
    => goto "L277";
  @"L277" [%"v288" : W = phi("L264" => #0, "L276" => %"v286")]:
    => br %"v288" ? "L186" : "L5";
  @"L186":
    %"v296" = %"v0" +p #20;
    %"v297" = %"v296" +p #32;
    %"v298" = %"v297" +p #16;
    %"v299" = %"v298" +p #4;
    %"chk22" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v299";
    %"v300" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v302" : W = And %"v300", #65536;
    %"v303" : W = (Cmp Ne W) %"v302", #0
    => br %"v303" ? "L304" : "L305";
  @"L304":
    %"v307" = %"v0" +p #20;
    %"v308" = %"v307" +p #32;
    %"v309" = %"v308" +p #16;
    %"v310" = %"v309" +p #4;
    %"v311" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v313" : W = And %"v311", #1073741824;
    %"v314" : W = (Cmp Ne W) %"v313", #0
    => goto "L305";
  @"L305" [%"v316" : W = phi("L186" => #0, "L304" => %"v314")]:
    => br %"v316" ? "L317" : "L318";
  @"L317":
    %"v320" = %"v0" +p #20;
    %"v321" = %"v320" +p #32;
    %"v322" = %"v321" +p #16;
    %"v323" = %"v322" +p #4;
    %"v324" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v326" : W = And %"v324", #268435456;
    %"v327" : W = (Cmp Ne W) %"v326", #0
    => goto "L318";
  @"L318" [%"v329" : W = phi("L305" => #0, "L317" => %"v327")]:
    => br %"v329" ? "L330" : "L331";
  @"L330":
    %"v333" = %"v0" +p #20;
    %"v334" = %"v333" +p #32;
    %"v335" = %"v334" +p #16;
    %"v336" = %"v335" +p #4;
    %"v337" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v339" : W = And %"v337", #131072;
    %"v340" : W = (Cmp Ne W) %"v339", #0
    => goto "L331";
  @"L331" [%"v342" : W = phi("L318" => #0, "L330" => %"v340")]:
    => br %"v342" ? "L343" : "L344";
  @"L343":
    %"v346" = %"v0" +p #20;
    %"v347" = %"v346" +p #32;
    %"v348" = %"v347" +p #16;
    %"v349" = %"v348" +p #4;
    %"v350" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v352" : W = And %"v350", #2147483648;
    %"v353" : W = (Cmp Ne W) %"v352", #0
    => goto "L344";
  @"L344" [%"v355" : W = phi("L331" => #0, "L343" => %"v353")]:
    => br %"v355" ? "L5" : "L293";
  @"L293":
    => goto "L5";
  @"L5" [%"pr.3" : W = phi("L293" => #7, "L344" => #15, "L277" => #3, "L171" => #1, "L80" => #0)]:
    => ret %"pr.3"
} }.
