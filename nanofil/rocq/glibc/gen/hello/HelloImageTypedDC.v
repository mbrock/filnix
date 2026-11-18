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

Definition hello_image_fn___GI___dcgettext : func :=
  ir_fn{ "export" "__GI___dcgettext"(P %"v0", P %"v2", W %"v4") -> (RClass P) {
  @"start":
    call %"v9" : P = $"__dcigettext"(P %"v0", P %"v2", P #0, W #0, L #0, W %"v4")
    => ret %"v9"
} }.

Definition hello_image_fn___dcigettext : func :=
  ir_fn{ "export" "__dcigettext"(P %"v0", P %"v2", P %"v4", W %"v6", L %"v8", W %"v10") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v17" : P = (Alloc 8) #8;
    %"v21" : P = (Alloc 8) #8;
    %"v23" : P = (Alloc 8) #64;
    %"chk0" : A = (Check 0 8 Write 8) %"v17";
    store.ptr [%"chk0" + 0] <- #0;
    %"v31" : L = Ptoi %"v2";
    %"v32" : L = Ptoi #0;
    %"v33" : W = (Cmp Eq L) %"v31", %"v32"
    => br %"v33" ? "L27" : "L29" };
  ir_blk{ @"L27":
    => ret #0 };
  ir_blk{ @"L29":
    %"v39" : W = (Cmp Slt W) %"v10", #0
    => br %"v39" ? "L41" : "L40" };
  ir_blk{ @"L40":
    %"v43" : W = (Cmp Sge W) %"v10", #13
    => goto "L41" };
  ir_blk{ @"L41" [%"v45" : W = phi("L29" => #1, "L40" => %"v43")]:
    => br %"v45" ? "L47" : "L46" };
  ir_blk{ @"L46":
    %"v49" : W = (Cmp Eq W) %"v10", #6
    => goto "L47" };
  ir_blk{ @"L47" [%"v51" : W = phi("L41" => #1, "L46" => %"v49")]:
    => br %"v51" ? "L35" : "L37" };
  ir_blk{ @"L35":
    %"v56" : W = (Cmp Eq W) %"v6", #0
    => br %"v56" ? "L54" : "L53" };
  ir_blk{ @"L53":
    %"v62" : W = (Cmp Eq L) %"v8", #1
    => br %"v62" ? "L54" : "L59" };
  ir_blk{ @"L59":
    => goto "L54" };
  ir_blk{ @"L54" [%"v66" : P = phi("L35" => %"v2", "L59" => %"v4", "L53" => %"v2")]:
    => ret %"v66" };
  ir_blk{ @"L37":
    %"v68" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Read 1) %"v68";
    %"v69" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v70" : P = Copy $"__libc_setlocale_lock";
    call %"v71" : W = $"__GI___pthread_rwlock_rdlock"(P %"v70");
    %"v72" : P = Copy $"_nl_state_lock";
    call %"v73" : W = $"__GI___pthread_rwlock_rdlock"(P %"v72");
    %"v78" : L = Ptoi %"v0";
    %"v80" : W = (Cmp Eq L) %"v78", %"v32"
    => br %"v80" ? "L74" : "L76" };
  ir_blk{ @"L74":
    %"v81" : P = Copy $"_nl_current_default_domain";
    %"chk2" : A = (Check 0 8 Read 8) %"v81";
    %"v82" : P = (RawLoadPointer 0 load_effects) %"chk2"
    => goto "L76" };
  ir_blk{ @"L76" [%"pr.1" : P = phi("L74" => %"v82", "L37" => %"v0")]:
    %"v83" = %"v23" +p #32;
    %"chk3" : A = (Check 0 8 Write 8) %"v83";
    store.ptr [%"chk3" + 0] <- #0;
    %"v84" = %"v23" +p #56;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v84";
    store.ptr [%"chk4" + 0] <- %"v2";
    %"chk5" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v23";
    store.ptr [%"chk5" + 0] <- %"pr.1";
    %"v87" = %"v23" +p #8;
    %"chk6" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v87";
    store Ww [%"chk6" + 0] <- %"v10";
    call %"v90" : P = $"__current_locale_name"(W %"v10");
    %"v91" = %"v23" +p #16;
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v91";
    store.ptr [%"chk7" + 0] <- %"v90";
    %"v93" : P = Copy $"glibc_dcigettext#tree_lock";
    call %"v94" : W = $"__GI___pthread_rwlock_rdlock"(P %"v93");
    %"v95" : P = Copy $"glibc_dcigettext#root";
    %"v96" : P = Copy $"glibc_dcigettext#transcmp";
    call %"v97" : P = $"__GI___tfind"(P %"v23", P %"v95", P %"v96");
    %"v98" : P = Copy $"glibc_dcigettext#tree_lock";
    call %"v99" : W = $"__GI___pthread_rwlock_unlock"(P %"v98");
    %"v104" : L = Ptoi %"v97";
    %"v106" : W = (Cmp Ne L) %"v104", %"v32"
    => br %"v106" ? "L107" : "L108" };
  ir_blk{ @"L107":
    %"chk8" : A = (Check 0 8 Read 8) %"v97";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v111" = %"v110" +p #24;
    %"chk9" : A = (Check 0 4 Read 1) %"v111";
    %"v112" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v113" : P = Copy $"_nl_msg_cat_cntr";
    %"chk10" : A = (Check 0 4 Read 1) %"v113";
    %"v114" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v115" : W = (Cmp Eq W) %"v112", %"v114"
    => goto "L108" };
  ir_blk{ @"L108" [%"v117" : W = phi("L76" => #0, "L107" => %"v115")]:
    => br %"v117" ? "L100" : "L102" };
  ir_blk{ @"L100":
    => br %"v6" ? "L118" : "L119" };
  ir_blk{ @"L118":
    %"chk11" : A = (Check 0 8 Read 8) %"v97";
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v124" = %"v123" +p #32;
    %"chk12" : A = (Check 0 8 Read 8) %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v129" = %"v128" +p #40;
    %"chk14" : A = (Check 0 8 Read 8) %"v129";
    %"v130" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v133" = %"v132" +p #48;
    %"chk16" : A = (Check 0 8 Read 1) %"v133";
    %"v134" : L = (RawLoad LdL 0) %"chk16";
    %"iw_1.v10" = %"v125" +p #16;
    %"chk17" : A = (Check 0 8 Read 8) %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_1.v16" = %"iw_1.v11" +p #184;
    %"chk18" : A = (Check 0 8 Read 8) %"iw_1.v16";
    %"iw_1.v17" : P = (RawLoadPointer 0 load_effects) %"chk18";
    (Call (CTuple [((a "iw_1.iw_1.v7"), L); ((a "iw_1.iw_1.v8"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "iw_1.v17")); (Arg L (t "v8")); (Arg W (Const 100))]);
    %"iw_1.v30" : W = Copy %"iw_1.iw_1.v7";
    %"iw_1.v31" : W = (Cmp Ne W) %"iw_1.v30", #0
    => br %"iw_1.v31" ? "iw_1.L44" : "iw_1.L28" };
  ir_blk{ @"iw_1.L28":
    %"iw_1.v38" = %"iw_1.v11" +p #192;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 1) %"chk18", %"iw_1.v38";
    %"iw_1.v39" : L = (RawLoad LdL 0) %"chk19";
    %"iw_1.v40" : W = (Cmp Uge L) %"iw_1.iw_1.v8", %"iw_1.v39"
    => br %"iw_1.v40" ? "iw_1.L44" : "iw_1.L33" };
  ir_blk{ @"iw_1.L33":
    => goto "iw_1.L44" };
  ir_blk{ @"iw_1.L44" [%"iw_1.pr.4" : P = phi("L118" => %"v130", "iw_1.L33" => %"v130", "iw_1.L28" => %"v130", "iw_1.L45" => %"iw_1.v53"); %"iw_1.pr.3" : L = phi("L118" => #0, "iw_1.L33" => %"iw_1.iw_1.v8", "iw_1.L28" => #0, "iw_1.L45" => %"iw_1.v48")]:
    %"iw_1.v48" : L = Sub %"iw_1.pr.3", #1;
    %"iw_1.v49" : W = (Cmp Ugt L) %"iw_1.pr.3", #0
    => br %"iw_1.v49" ? "iw_1.L45" : "L120" };
  ir_blk{ @"iw_1.L45":
    call %"iw_1.v51" : P = $"__GI_strchr"(P %"iw_1.pr.4", W #0);
    %"iw_1.v53" = %"iw_1.v51" +p #1;
    %"iw_1.v60" = %"v130" +p %"v134";
    %"iw_1.v61" : L = Ptoi %"iw_1.v53";
    %"iw_1.v62" : L = Ptoi %"iw_1.v60";
    %"iw_1.v63" : W = (Cmp Uge L) %"iw_1.v61", %"iw_1.v62"
    => br %"iw_1.v63" ? "L120" : poll "iw_1.L44" };
  ir_blk{ @"L119":
    %"chk20" : A = (Check 0 8 Read 8) %"v97";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v138" = %"v137" +p #40;
    %"chk21" : A = (Check 0 8 Read 8) %"v138";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk21"
    => goto "L120" };
  ir_blk{ @"L120" [%"pr.14" : P = phi("L119" => %"v139", "iw_1.L45" => %"v130", "iw_1.L44" => %"iw_1.pr.4")]:
    %"v140" : P = Copy $"_nl_state_lock";
    call %"v141" : W = $"__GI___pthread_rwlock_unlock"(P %"v140");
    %"v142" : P = Copy $"__libc_setlocale_lock";
    call %"v143" : W = $"__GI___pthread_rwlock_unlock"(P %"v142");
    %"v144" : P = Copy $"__libc_errno";
    %"chk22" : A = (Check 0 4 Write 1) %"v144";
    store Ww [%"chk22" + 0] <- %"v69"
    => ret %"pr.14" };
  ir_blk{ @"L102":
    %"v148" : P = Copy $"_nl_domain_bindings";
    %"chk23" : A = (Check 0 8 Read 8) %"v148";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk23"
    => goto "L150" };
  ir_blk{ @"L150" [%"pr.4" : P = phi("L102" => %"v149", "L152" => %"v176")]:
    %"v155" : L = Ptoi %"pr.4";
    %"v157" : W = (Cmp Ne L) %"v155", %"v32"
    => br %"v157" ? "L151" : "L153" };
  ir_blk{ @"L151":
    %"v161" = %"pr.4" +p #24;
    call %"v162" : W = $"__GI_strcmp"(P %"pr.1", P %"v161");
    %"v167" : W = (Cmp Eq W) %"v162", #0
    => br %"v167" ? "L153" : "L165" };
  ir_blk{ @"L165":
    %"v173" : W = (Cmp Slt W) %"v162", #0
    => br %"v173" ? "L153" : "L152" };
  ir_blk{ @"L152":
    %"chk24" : A = (Check 0 8 Read 8) %"pr.4";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk24"
    => goto poll "L150" };
  ir_blk{ @"L153" [%"pr.5" : P = phi("L150" => %"pr.4", "L151" => %"pr.4", "L165" => #0)]:
    %"v181" : L = Ptoi %"pr.5";
    %"v183" : W = (Cmp Eq L) %"v181", %"v32"
    => br %"v183" ? "L177" : "L178" };
  ir_blk{ @"L177":
    %"v184" : P = Copy $"__GI__nl_default_dirname"
    => goto "L179" };
  ir_blk{ @"L178":
    %"v186" = %"pr.5" +p #8;
    %"chk25" : A = (Check 0 8 Read 8) %"v186";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : A = (Check 0 1 Read 1) %"v187";
    %"v193" : W = (RawLoad (LdNarrow Sb) 0) %"chk26";
    %"v195" : W = (Cmp Ne W) %"v193", #47
    => br %"v195" ? "L188" : "L179" };
  ir_blk{ @"L188":
    call %"v197" : P = $"__GI___getcwd"(P #0, L #0);
    %"v202" : L = Ptoi %"v197";
    %"v204" : W = (Cmp Eq L) %"v202", %"v32"
    => br %"v204" ? "L205" : "L200" };
  ir_blk{ @"L200":
    %"v208" : P = Copy $"glibc_dcigettext#str.275";
    call %"v211" : W = $"__GI___asprintf"(P %"v17", P %"v208", P %"v197", P %"v187");
    call void $"free"(P %"v197");
    %"v217" : W = (Cmp Slt W) %"v211", #0
    => br %"v217" ? "L205" : "L215" };
  ir_blk{ @"L215":
    %"chk27" : A = (Renew 0 8 Read 8) %"chk0", %"v17";
    %"v219" : P = (RawLoadPointer 0 load_effects) %"chk27"
    => goto "L179" };
  ir_blk{ @"L179" [%"pr.10" : P = phi("L177" => %"v184", "L215" => %"v219", "L178" => %"v187")]:
    %"iw_2.v2" : P = Copy $"_nl_category_names";
    %"iw_2.v3" : P = Copy $"_nl_category_name_idxs";
    %"iw_2.v5" : L = (Ext Sw) %"v10";
    %"iw_2.v6" = %"iw_2.v3" +p %"iw_2.v5";
    %"chk28" : A = (Check 0 1 Read 1) %"iw_2.v6";
    %"iw_2.v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk28";
    %"iw_2.v8" : L = (Ext Uw) %"iw_2.v7";
    %"iw_2.v9" = %"iw_2.v2" +p %"iw_2.v8";
    call %"iw_3.v7" : P = $"__current_locale_name"(W %"v10");
    %"chk29" : A = (Check 0 1 Read 1) %"iw_3.v7";
    %"iw_3.v13" : W = (RawLoad (LdNarrow Sb) 0) %"chk29";
    %"iw_3.v14" : W = (Cmp Eq W) %"iw_3.v13", #67
    => br %"iw_3.v14" ? "iw_3.L15" : "iw_3.L16" };
  ir_blk{ @"iw_3.L15":
    %"iw_3.v18" = %"iw_3.v7" +p #1;
    %"chk30" : A = (HalfCheck Upper 0 1 Read 1) %"chk29", %"iw_3.v18";
    %"iw_3.v19" : W = (RawLoad (LdNarrow Sb) 0) %"chk30";
    %"iw_3.v20" : W = (Cmp Eq W) %"iw_3.v19", #0
    => br %"iw_3.v20" ? "iw_3.L16" : "iw_3.L21" };
  ir_blk{ @"iw_3.L21":
    %"iw_3.v24" = %"iw_3.v7" +p #1;
    %"iw_3.v25" : W = (RawLoad (LdNarrow Sb) 0) %"chk30";
    %"iw_3.v26" : W = (Cmp Eq W) %"iw_3.v25", #46
    => goto "iw_3.L16" };
  ir_blk{ @"iw_3.L16" [%"iw_3.v30" : W = phi("L179" => #0, "iw_3.L15" => #1, "iw_3.L21" => %"iw_3.v26")]:
    => br %"iw_3.v30" ? "iw_3.join" : "iw_3.L10" };
  ir_blk{ @"iw_3.L10":
    %"iw_3.v33" : P = Copy $"glibc_dcigettext#str.285";
    call %"iw_3.v34" : P = $"__GI_getenv"(P %"iw_3.v33");
    %"iw_3.v39" : L = Ptoi %"iw_3.v34";
    %"iw_3.v41" : W = (Cmp Ne L) %"iw_3.v39", %"v32"
    => br %"iw_3.v41" ? "iw_3.L42" : "iw_3.L43" };
  ir_blk{ @"iw_3.L42":
    %"chk32" : A = (Check 0 1 Read 1) %"iw_3.v34";
    %"iw_3.v46" : W = (RawLoad (LdNarrow Sb) 0) %"chk32";
    %"iw_3.v47" : W = (Cmp Ne W) %"iw_3.v46", #0
    => goto "iw_3.L43" };
  ir_blk{ @"iw_3.L43" [%"iw_3.v49" : W = phi("iw_3.L10" => #0, "iw_3.L42" => %"iw_3.v47")]:
    => br %"iw_3.v49" ? "iw_3.join" : "iw_3.L37" };
  ir_blk{ @"iw_3.L37":
    => goto "iw_3.join" };
  ir_blk{ @"iw_3.join" [%"v224" : P = phi("iw_3.L37" => %"iw_3.v7", "iw_3.L16" => %"iw_3.v7", "iw_3.L43" => %"iw_3.v34")]:
    call %"v226" : L = $"__GI_strlen"(P %"pr.1");
    call %"v228" : L = $"__GI_strlen"(P %"iw_2.v9");
    %"v230" : L = Add %"v228", %"v226";
    %"v231" : L = Add %"v230", #5;
    call %"v232" : P = $"malloc"(L %"v231");
    %"v237" : L = Ptoi %"v232";
    %"v239" : W = (Cmp Eq L) %"v237", %"v32"
    => br %"v239" ? "L205" : "L235" };
  ir_blk{ @"L235":
    call %"v243" : P = $"__GI_stpcpy"(P %"v232", P %"iw_2.v9");
    %"v244" : P = Copy $"glibc_dcigettext#str.276";
    call %"v245" : P = $"__GI_stpcpy"(P %"v243", P %"v244");
    call %"v248" : P = $"__GI_mempcpy"(P %"v245", P %"pr.1", L %"v226");
    %"v249" : P = Copy $"glibc_dcigettext#str.277";
    call %"v250" : P = $"__GI_stpcpy"(P %"v248", P %"v249");
    call %"v252" : L = $"__GI_strlen"(P %"v224");
    %"v253" : L = Add %"v252", #1;
    call %"v254" : P = $"malloc"(L %"v253");
    %"v259" : L = Ptoi %"v254";
    %"v261" : W = (Cmp Eq L) %"v259", %"v32"
    => br %"v261" ? "L205" : "L263" };
  ir_blk{ @"L263" [%"pr.6" : P = phi("L235" => %"v224", "L323" => %"pr.9", "L444" => %"pr.8", "L334" => %"pr.8")]:
    => goto "L266" }] [ir_blk{ @"L266" [%"pr.7" : P = phi("L267" => %"v282", "L263" => %"pr.6")]:
    %"chk33" : A = (Check 0 1 Read 1) %"pr.7";
    %"v271" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v272" : W = (Cmp Ne W) %"v271", #0
    => br %"v272" ? "L273" : "L274" };
  ir_blk{ @"L273":
    %"v277" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v278" : W = (Cmp Eq W) %"v277", #58
    => goto "L274" };
  ir_blk{ @"L274" [%"v280" : W = phi("L266" => #0, "L273" => %"v278")]:
    => br %"v280" ? "L267" : "L268" };
  ir_blk{ @"L267":
    %"v282" = %"pr.7" +p #1
    => goto poll "L266" };
  ir_blk{ @"L268":
    %"v288" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v289" : W = (Cmp Eq W) %"v288", #0
    => br %"v289" ? "L283" : "L296" };
  ir_blk{ @"L283":
    %"chk36" : A = (Check 0 1 Write 1) %"v254";
    store Wb [%"chk36" + 0] <- #67;
    %"v293" = %"v254" +p #1;
    %"chk37" : A = (HalfCheck Upper 0 1 Write 1) %"chk36", %"v293";
    store Wb [%"chk37" + 0] <- #0
    => goto "L285" };
  ir_blk{ @"L296" [%"pr.19" : P = phi("L297" => %"v312", "L268" => %"v254"); %"pr.9" : P = phi("L297" => %"v314", "L268" => %"pr.7")]:
    %"chk38" : A = (Check 0 1 Read 1) %"pr.9";
    %"v301" : W = (RawLoad (LdNarrow Sb) 0) %"chk38";
    %"v302" : W = (Cmp Ne W) %"v301", #0
    => br %"v302" ? "L303" : "L304" };
  ir_blk{ @"L303":
    %"v307" : W = (RawLoad (LdNarrow Sb) 0) %"chk38";
    %"v308" : W = (Cmp Ne W) %"v307", #58
    => goto "L304" };
  ir_blk{ @"L304" [%"v310" : W = phi("L296" => #0, "L303" => %"v308")]:
    => br %"v310" ? "L297" : "L298" };
  ir_blk{ @"L297":
    %"v312" = %"pr.19" +p #1;
    %"v314" = %"pr.9" +p #1;
    %"v315" : W = (RawLoad (LdNarrow Sb) 0) %"chk38";
    %"chk41" : A = (Check 0 1 Write 1) %"pr.19";
    store Wb [%"chk41" + 0] <- %"v315"
    => goto poll "L296" };
  ir_blk{ @"L298":
    %"chk42" : A = (Check 0 1 Write 1) %"pr.19";
    store Wb [%"chk42" + 0] <- #0;
    %"v320" : P = Copy $"__libc_enable_secure";
    %"chk43" : A = (Check 0 4 Read 1) %"v320";
    %"v321" : W = (RawLoad (LdNarrow Sw) 0) %"chk43"
    => br %"v321" ? "L322" : "L323" };
  ir_blk{ @"L322":
    call %"v325" : P = $"__GI_strchr"(P %"v254", W #47);
    %"v326" : L = Ptoi %"v325";
    %"v328" : W = (Cmp Ne L) %"v326", %"v32"
    => goto "L323" };
  ir_blk{ @"L323" [%"v330" : W = phi("L298" => #0, "L322" => %"v328")]:
    => br %"v330" ? poll "L263" : "L285" };
  ir_blk{ @"L285" [%"pr.8" : P = phi("L283" => %"pr.7", "L323" => %"pr.9")]:
    %"chk44" : A = (Check 0 1 Read 1) %"v254";
    %"v337" : W = (RawLoad (LdNarrow Sb) 0) %"chk44";
    %"v338" : W = (Cmp Eq W) %"v337", #67
    => br %"v338" ? "L339" : "L340" };
  ir_blk{ @"L339":
    %"v342" = %"v254" +p #1;
    %"chk45" : A = (HalfCheck Upper 0 1 Read 1) %"chk44", %"v342";
    %"v343" : W = (RawLoad (LdNarrow Sb) 0) %"chk45";
    %"v344" : W = (Cmp Eq W) %"v343", #0
    => br %"v344" ? "L340" : "L345" };
  ir_blk{ @"L345":
    %"v348" = %"v254" +p #1;
    %"v349" : W = (RawLoad (LdNarrow Sb) 0) %"chk45";
    %"v350" : W = (Cmp Eq W) %"v349", #46
    => goto "L340" };
  ir_blk{ @"L340" [%"v354" : W = phi("L285" => #0, "L339" => #1, "L345" => %"v350")]:
    => br %"v354" ? "L356" : "L355" };
  ir_blk{ @"L355":
    %"v358" : P = Copy $"glibc_dcigettext#str.278";
    call %"v359" : W = $"__GI_strcmp"(P %"v254", P %"v358");
    %"v360" : W = (Cmp Eq W) %"v359", #0
    => goto "L356" };
  ir_blk{ @"L356" [%"v362" : W = phi("L340" => #1, "L355" => %"v360")]:
    => br %"v362" ? "L205" : "L334" };
  ir_blk{ @"L334":
    call %"v368" : P = $"_nl_find_domain"(P %"pr.10", P %"v254", P %"v232", P %"pr.5");
    %"v373" : L = Ptoi %"v368";
    %"v375" : W = (Cmp Ne L) %"v373", %"v32"
    => br %"v375" ? "L369" : poll "L263" };
  ir_blk{ @"L369":
    call %"v379" : P = $"_nl_find_msg"(P %"v368", P %"pr.5", P %"v2", W #1, P %"v21");
    %"v384" : L = Ptoi %"v379";
    %"v386" : W = (Cmp Eq L) %"v384", %"v32"
    => br %"v386" ? "L388" : "L382" };
  ir_blk{ @"L388" [%"pr.20" : W = phi("L390" => %"v441", "L369" => #0); %"pr.16" : P = phi("L390" => %"v411", "L369" => %"v379")]:
    %"v393" = %"v368" +p #32;
    %"v395" : L = (Ext Sw) %"pr.20";
    %"v396" : L = Shl %"v395", #3;
    %"v397" = %"v393" +p %"v396";
    %"chk47" : A = (Check 0 8 Read 8) %"v397";
    %"v398" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v399" : L = Ptoi %"v398";
    %"v401" : W = (Cmp Ne L) %"v399", %"v32"
    => br %"v401" ? "L389" : "L382" };
  ir_blk{ @"L389":
    %"v403" = %"v368" +p #32;
    %"v407" = %"v403" +p %"v396";
    %"chk48" : A = (Check 0 8 Read 8) %"v407";
    %"v408" : P = (RawLoadPointer 0 load_effects) %"chk48";
    call %"v411" : P = $"_nl_find_msg"(P %"v408", P %"pr.5", P %"v2", W #1, P %"v21");
    (Flight (a "v418") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v419" : L = Ptoi %"v411";
    %"v420" : L = Ptoi %"v418";
    %"v421" : W = (Cmp Eq L) %"v419", %"v420"
    => br %"v421" ? "L205" : "L414" };
  ir_blk{ @"L414":
    %"v431" : W = (Cmp Ne L) %"v419", %"v32"
    => br %"v431" ? "L425" : "L390" };
  ir_blk{ @"L425":
    %"v433" = %"v368" +p #32;
    %"v437" = %"v433" +p %"v396";
    %"chk49" : A = (Check 0 8 Read 8) %"v437";
    %"v438" : P = (RawLoadPointer 0 load_effects) %"chk49"
    => goto "L382" };
  ir_blk{ @"L390":
    %"v441" : W = Add %"pr.20", #1
    => goto poll "L388" };
  ir_blk{ @"L382" [%"pr.15" : P = phi("L388" => %"pr.16", "L425" => %"v411", "L369" => %"v379"); %"pr.2" : P = phi("L388" => %"v368", "L425" => %"v438", "L369" => %"v368")]:
    (Flight (a "v448") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v449" : L = Ptoi %"pr.15";
    %"v450" : L = Ptoi %"v448";
    %"v451" : W = (Cmp Eq L) %"v449", %"v450"
    => br %"v451" ? "L205" : "L444" };
  ir_blk{ @"L444":
    %"v461" : W = (Cmp Ne L) %"v449", %"v32"
    => br %"v461" ? "L455" : poll "L263" };
  ir_blk{ @"L455":
    %"chk50" : A = (Renew 0 8 Read 8) %"chk0", %"v17";
    %"v462" : P = (RawLoadPointer 0 load_effects) %"chk50";
    call void $"free"(P %"v462");
    call void $"free"(P %"v232");
    call void $"free"(P %"v254");
    %"v471" : W = (Cmp Eq L) %"v104", %"v32"
    => br %"v471" ? "L465" : "L466" };
  ir_blk{ @"L465":
    call %"v476" : L = $"__GI_strlen"(P %"v2");
    %"v477" : L = Add %"v476", #1;
    %"v479" : L = Add %"v477", #56;
    %"v481" : L = Add %"v479", %"v226";
    %"v482" : L = Add %"v481", #1;
    call %"v485" : L = $"__GI_strlen"(P %"v90");
    %"v486" : L = Add %"v485", #1;
    %"v487" : L = Add %"v482", %"v486";
    call %"v489" : P = $"malloc"(L %"v487");
    %"v494" : L = Ptoi %"v489";
    %"v496" : W = (Cmp Ne L) %"v494", %"v32"
    => br %"v496" ? "L490" : "L467" };
  ir_blk{ @"L490":
    %"v500" = %"v489" +p #56;
    call %"v503" : P = $"__GI_mempcpy"(P %"v500", P %"v2", L %"v477");
    %"v507" : L = Add %"v226", #1;
    call %"v508" : P = $"__GI_memcpy"(P %"v503", P %"pr.1", L %"v507");
    %"v511" = %"v503" +p %"v226";
    %"v512" = %"v511" +p #1;
    call %"v515" : P = $"__GI_strcpy"(P %"v512", P %"v90");
    %"chk51" : A = (Check 0 8 Write 8) %"v489";
    store.ptr [%"chk51" + 0] <- %"v503";
    %"v519" = %"v489" +p #8;
    %"chk52" : A = (HalfCheck Upper 0 4 Write 1) %"chk51", %"v519";
    store Ww [%"chk52" + 0] <- %"v10";
    %"v522" = %"v489" +p #16;
    %"chk53" : A = (HalfCheck Upper 0 8 Write 8) %"chk51", %"v522";
    store.ptr [%"chk53" + 0] <- %"v512";
    %"v525" = %"v489" +p #24;
    %"v526" : P = Copy $"_nl_msg_cat_cntr";
    %"chk54" : A = (Check 0 4 Read 1) %"v526";
    %"v527" : W = (RawLoad (LdNarrow Sw) 0) %"chk54";
    %"chk55" : A = (HalfCheck Upper 0 4 Write 1) %"chk51", %"v525";
    store Ww [%"chk55" + 0] <- %"v527";
    %"v529" = %"v489" +p #32;
    %"chk56" : A = (HalfCheck Upper 0 8 Write 8) %"chk51", %"v529";
    store.ptr [%"chk56" + 0] <- %"pr.2";
    %"v532" = %"v489" +p #40;
    %"chk57" : A = (HalfCheck Upper 0 8 Write 8) %"chk51", %"v532";
    store.ptr [%"chk57" + 0] <- %"pr.15";
    %"v535" = %"v489" +p #48;
    %"chk58" : A = (Check 0 8 Read 1) %"v21";
    %"v536" : L = (RawLoad LdL 0) %"chk58";
    %"chk59" : A = (HalfCheck Upper 0 8 Write 1) %"chk51", %"v535";
    store Wl [%"chk59" + 0] <- %"v536";
    %"v537" : P = Copy $"glibc_dcigettext#tree_lock";
    call %"v538" : W = $"__GI___pthread_rwlock_wrlock"(P %"v537");
    %"v540" : P = Copy $"glibc_dcigettext#root";
    %"v541" : P = Copy $"glibc_dcigettext#transcmp";
    call %"v542" : P = $"__GI___tsearch"(P %"v489", P %"v540", P %"v541");
    %"v543" : P = Copy $"glibc_dcigettext#tree_lock";
    call %"v544" : W = $"__GI___pthread_rwlock_unlock"(P %"v543");
    %"v549" : L = Ptoi %"v542";
    %"v551" : W = (Cmp Eq L) %"v549", %"v32"
    => br %"v551" ? "L553" : "L552" };
  ir_blk{ @"L552":
    %"chk60" : A = (Check 0 8 Read 8) %"v542";
    %"v555" : P = (RawLoadPointer 0 load_effects) %"chk60";
    %"v557" : L = Ptoi %"v555";
    %"v559" : W = (Cmp Ne L) %"v557", %"v494"
    => goto "L553" };
  ir_blk{ @"L553" [%"v563" : W = phi("L490" => #1, "L552" => %"v559")]:
    => br %"v563" ? "L545" : "L467" };
  ir_blk{ @"L545":
    call void $"free"(P %"v489")
    => goto "L467" };
  ir_blk{ @"L466":
    %"chk61" : A = (Check 0 8 Read 8) %"v97";
    %"v566" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"v567" = %"v566" +p #24;
    %"v568" : P = Copy $"_nl_msg_cat_cntr";
    %"chk62" : A = (Check 0 4 Read 1) %"v568";
    %"v569" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"chk63" : A = (Check 0 4 Write 1) %"v567";
    store Ww [%"chk63" + 0] <- %"v569";
    %"chk64" : A = (Renew 0 8 Read 8) %"chk61", %"v97";
    %"v571" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v572" = %"v571" +p #32;
    %"chk65" : A = (Check 0 8 Write 8) %"v572";
    store.ptr [%"chk65" + 0] <- %"pr.2";
    %"chk66" : A = (Renew 0 8 Read 8) %"chk61", %"v97";
    %"v575" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"v576" = %"v575" +p #40;
    %"chk67" : A = (Check 0 8 Write 8) %"v576";
    store.ptr [%"chk67" + 0] <- %"pr.15";
    %"chk68" : A = (Renew 0 8 Read 8) %"chk61", %"v97";
    %"v579" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"v580" = %"v579" +p #48;
    %"chk69" : A = (Check 0 8 Read 1) %"v21";
    %"v581" : L = (RawLoad LdL 0) %"chk69";
    %"chk70" : A = (Check 0 8 Write 1) %"v580";
    store Wl [%"chk70" + 0] <- %"v581"
    => goto "L467" };
  ir_blk{ @"L467":
    %"v582" : P = Copy $"__libc_errno";
    %"chk71" : A = (Check 0 4 Write 1) %"v582";
    store Ww [%"chk71" + 0] <- %"v69"
    => br %"v6" ? "L584" : "L586" };
  ir_blk{ @"L584":
    %"chk72" : A = (Check 0 8 Read 1) %"v21";
    %"v591" : L = (RawLoad LdL 0) %"chk72";
    %"iw_4.v10" = %"pr.2" +p #16;
    %"chk73" : A = (Check 0 8 Read 8) %"iw_4.v10";
    %"iw_4.v11" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"iw_4.v16" = %"iw_4.v11" +p #184;
    %"chk74" : A = (Check 0 8 Read 8) %"iw_4.v16";
    %"iw_4.v17" : P = (RawLoadPointer 0 load_effects) %"chk74";
    (Call (CTuple [((a "iw_4.iw_1.v7"), L); ((a "iw_4.iw_1.v8"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "iw_4.v17")); (Arg L (t "v8")); (Arg W (Const 100))]);
    %"iw_4.v30" : W = Copy %"iw_4.iw_1.v7";
    %"iw_4.v31" : W = (Cmp Ne W) %"iw_4.v30", #0
    => br %"iw_4.v31" ? "iw_4.L44" : "iw_4.L28" };
  ir_blk{ @"iw_4.L28":
    %"iw_4.v38" = %"iw_4.v11" +p #192;
    %"chk75" : A = (HalfCheck Upper 0 8 Read 1) %"chk74", %"iw_4.v38";
    %"iw_4.v39" : L = (RawLoad LdL 0) %"chk75";
    %"iw_4.v40" : W = (Cmp Uge L) %"iw_4.iw_1.v8", %"iw_4.v39"
    => br %"iw_4.v40" ? "iw_4.L44" : "iw_4.L33" };
  ir_blk{ @"iw_4.L33":
    => goto "iw_4.L44" };
  ir_blk{ @"iw_4.L44" [%"iw_4.pr.4" : P = phi("L584" => %"pr.15", "iw_4.L33" => %"pr.15", "iw_4.L28" => %"pr.15", "iw_4.L45" => %"iw_4.v53"); %"iw_4.pr.3" : L = phi("L584" => #0, "iw_4.L33" => %"iw_4.iw_1.v8", "iw_4.L28" => #0, "iw_4.L45" => %"iw_4.v48")]:
    %"iw_4.v48" : L = Sub %"iw_4.pr.3", #1;
    %"iw_4.v49" : W = (Cmp Ugt L) %"iw_4.pr.3", #0
    => br %"iw_4.v49" ? "iw_4.L45" : "L586" };
  ir_blk{ @"iw_4.L45":
    call %"iw_4.v51" : P = $"__GI_strchr"(P %"iw_4.pr.4", W #0);
    %"iw_4.v53" = %"iw_4.v51" +p #1;
    %"iw_4.v60" = %"pr.15" +p %"v591";
    %"iw_4.v61" : L = Ptoi %"iw_4.v53";
    %"iw_4.v62" : L = Ptoi %"iw_4.v60";
    %"iw_4.v63" : W = (Cmp Uge L) %"iw_4.v61", %"iw_4.v62"
    => br %"iw_4.v63" ? "L586" : poll "iw_4.L44" };
  ir_blk{ @"L586" [%"pr.18" : P = phi("iw_4.L45" => %"pr.15", "iw_4.L44" => %"iw_4.pr.4", "L467" => %"pr.15")]:
    %"v593" : P = Copy $"_nl_state_lock";
    call %"v594" : W = $"__GI___pthread_rwlock_unlock"(P %"v593");
    %"v595" : P = Copy $"__libc_setlocale_lock";
    call %"v596" : W = $"__GI___pthread_rwlock_unlock"(P %"v595")
    => ret %"pr.18" };
  ir_blk{ @"L205" [%"pr.13" : P = phi("L188" => #0, "L200" => #0, "iw_3.join" => #0, "L235" => %"v254", "L389" => %"v254", "L356" => %"v254", "L382" => %"v254"); %"pr.12" : P = phi("L188" => #0, "L200" => #0, "iw_3.join" => %"v232", "L235" => %"v232", "L389" => %"v232", "L356" => %"v232", "L382" => %"v232")]:
    %"chk76" : A = (Renew 0 8 Read 8) %"chk0", %"v17";
    %"v599" : P = (RawLoadPointer 0 load_effects) %"chk76";
    call void $"free"(P %"v599");
    call void $"free"(P %"pr.12");
    call void $"free"(P %"pr.13");
    %"v602" : P = Copy $"_nl_state_lock";
    call %"v603" : W = $"__GI___pthread_rwlock_unlock"(P %"v602");
    %"v604" : P = Copy $"__libc_setlocale_lock";
    call %"v605" : W = $"__GI___pthread_rwlock_unlock"(P %"v604");
    %"v606" : P = Copy $"__libc_errno";
    %"chk77" : A = (Check 0 4 Write 1) %"v606";
    store Ww [%"chk77" + 0] <- %"v69";
    %"v612" : W = (Cmp Eq W) %"v6", #0
    => br %"v612" ? "L610" : "L609" };
  ir_blk{ @"L609":
    %"v618" : W = (Cmp Eq L) %"v8", #1
    => br %"v618" ? "L610" : "L615" };
  ir_blk{ @"L615":
    => goto "L610" };
  ir_blk{ @"L610" [%"v622" : P = phi("L205" => %"v2", "L615" => %"v4", "L609" => %"v2")]:
    => ret %"v622" }])) }.
