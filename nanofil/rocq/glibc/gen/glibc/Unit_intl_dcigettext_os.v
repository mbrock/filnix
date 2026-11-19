(** This file defines checked IR from glibc’s `intl/dcigettext.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRBytes IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___GI__nl_default_dirname : item :=
  (IData (a "__GI__nl_default_dirname") (LRo (a "export")) 1 ["/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44/share/locale"%irbytes; (Zero 1)]).

Definition fn___dcigettext : func :=
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

Definition item__nl_current_default_domain : item :=
  (IData (a "_nl_current_default_domain") LExport 8 [(Sym (a "_nl_default_default_domain") 0)]).

Definition item__nl_default_default_domain : item :=
  (IData (a "_nl_default_default_domain") (LRo (a "export")) 1 ["messages"%irbytes; (Zero 1)]).

Definition item__nl_domain_bindings : item :=
  (IData (a "_nl_domain_bindings") LExport 8 [(Zero 8)]).

Definition fn__nl_find_msg : func :=
  ir_fn{ "export" "_nl_find_msg"(P %"v0", P %"v2", P %"v4", W %"v6", P %"v8") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v528" : P = (Alloc 8) #8;
    %"v585" : P = (Alloc 8) #24;
    %"v770" : P = (Alloc 8) #8;
    %"v771" : P = (Alloc 8) #8;
    %"v814" : P = (Alloc 8) #8;
    %"v19" = %"v0" +p #8;
    %"chk0" : A = (Check 0 4 Read 1) %"v19";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v21" : W = (Cmp Sle W) %"v20", #0
    => br %"v21" ? "L15" : "L17" };
  ir_blk{ @"L15":
    call void $"_nl_load_domain"(P %"v0", P %"v2")
    => goto "L17" };
  ir_blk{ @"L17":
    %"v28" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v30" : L = Ptoi %"v29";
    %"v31" : L = Ptoi #0;
    %"v32" : W = (Cmp Eq L) %"v30", %"v31"
    => br %"v32" ? "L24" : "L26" };
  ir_blk{ @"L24":
    => ret #0 };
  ir_blk{ @"L26":
    %"v35" = %"v0" +p #16;
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v38" = %"v36" +p #40;
    %"chk3" : A = (Check 0 4 Read 1) %"v38";
    %"v39" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v44" = %"v36" +p #96;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v46" : L = Ptoi %"v45";
    %"v48" : W = (Cmp Ne L) %"v46", %"v31"
    => br %"v48" ? "L40" : "L41" };
  ir_blk{ @"L40":
    call %"v51" : L = $"__GI_strlen"(P %"v4");
    call %"v54" : L = $"__hash_string"(P %"v4");
    %"v56" : W = Copy %"v54";
    %"v58" = %"v36" +p #88;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v58";
    %"v59" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v60" : W = Urem %"v56", %"v59";
    %"v62" : W = Copy %"v54";
    %"v65" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v66" : W = Sub %"v65", #2;
    %"v67" : W = Urem %"v62", %"v66";
    %"v68" : W = Add %"v67", #1
    => goto "L69" };
  ir_blk{ @"L69" [%"pr.9" : W = phi("L40" => %"v60", "L213" => %"v229", "L214" => %"v232")]:
    %"v77" = %"v36" +p #104;
    %"chk7" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v77";
    %"v78" : W = (RawLoad (LdNarrow Sw) 0) %"chk7"
    => br %"v78" ? "L73" : "L74" };
  ir_blk{ @"L73":
    %"v80" = %"v36" +p #96;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk4", %"v80";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v83" : L = (Ext Uw) %"pr.9";
    %"v84" : L = Shl %"v83", #2;
    %"v85" = %"v81" +p %"v84";
    %"chk9" : A = (Check 0 4 Read 1) %"v85";
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    call %"v87" : W = $"glibc_dcigettext#__bswap_32"(W %"v86")
    => goto "L75" };
  ir_blk{ @"L74":
    %"v89" = %"v36" +p #96;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk4", %"v89";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v92" : L = (Ext Uw) %"pr.9";
    %"v93" : L = Shl %"v92", #2;
    %"v94" = %"v90" +p %"v93";
    %"chk11" : A = (Check 0 4 Read 1) %"v94";
    %"v95" : W = (RawLoad (LdNarrow Uw) 0) %"chk11"
    => goto "L75" };
  ir_blk{ @"L75" [%"v96" : W = phi("L73" => %"v87", "L74" => %"v95")]:
    %"v101" : W = (Cmp Eq W) %"v96", #0
    => br %"v101" ? "L97" : "L99" };
  ir_blk{ @"L97":
    => ret #0 };
  ir_blk{ @"L99":
    %"v104" : W = Sub %"v96", #1;
    %"v113" : W = (Cmp Ult W) %"v104", %"v39"
    => br %"v113" ? "L108" : "L109" };
  ir_blk{ @"L108":
    %"v118" = %"v36" +p #24;
    %"chk12" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"v118";
    %"v119" : W = (RawLoad (LdNarrow Sw) 0) %"chk12"
    => br %"v119" ? "L114" : "L115" };
  ir_blk{ @"L114":
    %"v121" = %"v36" +p #48;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v124" : L = (Ext Uw) %"v104";
    %"v125" : L = Shl %"v124", #3;
    %"v126" = %"v122" +p %"v125";
    %"chk14" : A = (Check 0 4 Read 1) %"v126";
    %"v127" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    call %"v128" : W = $"glibc_dcigettext#__bswap_32"(W %"v127")
    => goto "L116" };
  ir_blk{ @"L115":
    %"v130" = %"v36" +p #48;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v130";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v133" : L = (Ext Uw) %"v104";
    %"v134" : L = Shl %"v133", #3;
    %"v135" = %"v131" +p %"v134";
    %"chk16" : A = (Check 0 4 Read 1) %"v135";
    %"v136" : W = (RawLoad (LdNarrow Uw) 0) %"chk16"
    => goto "L116" };
  ir_blk{ @"L116" [%"v137" : W = phi("L114" => %"v128", "L115" => %"v136")]:
    %"v138" : W = Copy %"v51";
    %"v139" : W = (Cmp Uge W) %"v137", %"v138"
    => br %"v139" ? "L140" : "L110" };
  ir_blk{ @"L140":
    %"chk17" : A = (HalfCheck Lower 0 8 Read 8) %"chk3", %"v36";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v149" = %"v36" +p #24;
    %"chk18" : A = (Renew 0 4 Read 1) %"chk12", %"v149";
    %"v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk18"
    => br %"v150" ? "L145" : "L146" };
  ir_blk{ @"L145":
    %"v152" = %"v36" +p #48;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v152";
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v155" : L = (Ext Uw) %"v104";
    %"v156" : L = Shl %"v155", #3;
    %"v157" = %"v153" +p %"v156";
    %"v158" = %"v157" +p #4;
    %"chk20" : A = (Check 0 4 Read 1) %"v158";
    %"v159" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    call %"v160" : W = $"glibc_dcigettext#__bswap_32"(W %"v159")
    => goto "L147" };
  ir_blk{ @"L146":
    %"v162" = %"v36" +p #48;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v162";
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v165" : L = (Ext Uw) %"v104";
    %"v166" : L = Shl %"v165", #3;
    %"v167" = %"v163" +p %"v166";
    %"v168" = %"v167" +p #4;
    %"chk22" : A = (Check 0 4 Read 1) %"v168";
    %"v169" : W = (RawLoad (LdNarrow Uw) 0) %"chk22"
    => goto "L147" };
  ir_blk{ @"L147" [%"v170" : W = phi("L145" => %"v160", "L146" => %"v169")]:
    %"v171" : L = (Ext Uw) %"v170";
    %"v172" = %"v144" +p %"v171";
    call %"v173" : W = $"__GI_strcmp"(P %"v4", P %"v172");
    %"v174" : W = (Cmp Eq W) %"v173", #0
    => goto "L110" };
  ir_blk{ @"L109":
    %"v178" = %"v36" +p #72;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v178";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v182" : W = Sub %"v104", %"v39";
    %"v183" : L = (Ext Uw) %"v182";
    %"v184" : L = Shl %"v183", #4;
    %"v185" = %"v179" +p %"v184";
    %"chk24" : A = (Check 0 8 Read 1) %"v185";
    %"v186" : L = (RawLoad LdL 0) %"chk24";
    %"v187" : W = Copy %"v51";
    %"v188" : L = (Ext Uw) %"v187";
    %"v189" : W = (Cmp Ugt L) %"v186", %"v188"
    => br %"v189" ? "L190" : "L110" };
  ir_blk{ @"L190":
    %"v194" = %"v36" +p #72;
    %"v195" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v201" = %"v195" +p %"v184";
    %"v202" = %"v201" +p #8;
    %"chk26" : A = (Check 0 8 Read 8) %"v202";
    %"v203" : P = (RawLoadPointer 0 load_effects) %"chk26";
    call %"v204" : W = $"__GI_strcmp"(P %"v4", P %"v203");
    %"v205" : W = (Cmp Eq W) %"v204", #0
    => goto "L110" };
  ir_blk{ @"L110" [%"v208" : W = phi("L116" => #0, "L147" => %"v174", "L109" => #0, "L190" => %"v205")]:
    => br %"v208" ? "L105" : "L107" };
  ir_blk{ @"L105":
    %"v210" : L = (Ext Uw) %"v104"
    => goto "L211" };
  ir_blk{ @"L107":
    %"v218" = %"v36" +p #88;
    %"chk27" : A = (Renew 0 4 Read 1) %"chk5", %"v218";
    %"v219" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v221" : W = Sub %"v219", %"v68";
    %"v222" : W = (Cmp Uge W) %"pr.9", %"v221"
    => br %"v222" ? "L213" : "L214" };
  ir_blk{ @"L213":
    %"v225" = %"v36" +p #88;
    %"v226" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v228" : W = Sub %"v226", %"v68";
    %"v229" : W = Sub %"pr.9", %"v228"
    => goto poll "L69" };
  ir_blk{ @"L214":
    %"v232" : W = Add %"pr.9", %"v68"
    => goto poll "L69" };
  ir_blk{ @"L41":
    %"v236" : L = (Ext Uw) %"v39"
    => goto "L237" };
  ir_blk{ @"L237" [%"pr.12" : L = phi("L41" => #0, "L253" => %"pr.12", "L284" => %"v290"); %"pr.10" : L = phi("L41" => %"v236", "L253" => %"v247", "L284" => %"pr.10")]:
    %"v242" : W = (Cmp Ult L) %"pr.12", %"pr.10"
    => br %"v242" ? "L238" : "L239" };
  ir_blk{ @"L238":
    %"v246" : L = Add %"pr.12", %"pr.10";
    %"v247" : L = Shr %"v246", #1;
    %"chk29" : A = (HalfCheck Lower 0 8 Read 8) %"chk3", %"v36";
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v255" = %"v36" +p #24;
    %"chk30" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"v255";
    %"v256" : W = (RawLoad (LdNarrow Sw) 0) %"chk30"
    => br %"v256" ? "L251" : "L252" };
  ir_blk{ @"L251":
    %"v258" = %"v36" +p #48;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v258";
    %"v259" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v261" : L = Shl %"v247", #3;
    %"v262" = %"v259" +p %"v261";
    %"v263" = %"v262" +p #4;
    %"chk32" : A = (Check 0 4 Read 1) %"v263";
    %"v264" : W = (RawLoad (LdNarrow Uw) 0) %"chk32";
    call %"v265" : W = $"glibc_dcigettext#__bswap_32"(W %"v264")
    => goto "L253" };
  ir_blk{ @"L252":
    %"v267" = %"v36" +p #48;
    %"chk33" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v267";
    %"v268" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v270" : L = Shl %"v247", #3;
    %"v271" = %"v268" +p %"v270";
    %"v272" = %"v271" +p #4;
    %"chk34" : A = (Check 0 4 Read 1) %"v272";
    %"v273" : W = (RawLoad (LdNarrow Uw) 0) %"chk34"
    => goto "L253" };
  ir_blk{ @"L253" [%"v274" : W = phi("L251" => %"v265", "L252" => %"v273")]:
    %"v275" : L = (Ext Uw) %"v274";
    %"v276" = %"v250" +p %"v275";
    call %"v277" : W = $"__GI_strcmp"(P %"v4", P %"v276");
    %"v282" : W = (Cmp Slt W) %"v277", #0
    => br %"v282" ? poll "L237" : "L279" };
  ir_blk{ @"L279":
    %"v288" : W = (Cmp Sgt W) %"v277", #0
    => br %"v288" ? "L284" : "L211" };
  ir_blk{ @"L284":
    %"v290" : L = Add %"v247", #1
    => goto poll "L237" };
  ir_blk{ @"L239":
    => ret #0 };
  ir_blk{ @"L211" [%"pr.1" : L = phi("L105" => %"v210", "L279" => %"v247")]:
    %"v296" : L = (Ext Uw) %"v39";
    %"v297" : W = (Cmp Ult L) %"pr.1", %"v296"
    => br %"v297" ? "L291" : "L292" };
  ir_blk{ @"L291":
    %"chk35" : A = (HalfCheck Lower 0 8 Read 8) %"chk3", %"v36";
    %"v299" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v304" = %"v36" +p #24;
    %"chk36" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"v304";
    %"v305" : W = (RawLoad (LdNarrow Sw) 0) %"chk36"
    => br %"v305" ? "L300" : "L301" };
  ir_blk{ @"L300":
    %"v307" = %"v36" +p #56;
    %"chk37" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v307";
    %"v308" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v310" : L = Shl %"pr.1", #3;
    %"v311" = %"v308" +p %"v310";
    %"v312" = %"v311" +p #4;
    %"chk38" : A = (Check 0 4 Read 1) %"v312";
    %"v313" : W = (RawLoad (LdNarrow Uw) 0) %"chk38";
    call %"v314" : W = $"glibc_dcigettext#__bswap_32"(W %"v313")
    => goto "L302" };
  ir_blk{ @"L301":
    %"v316" = %"v36" +p #56;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v316";
    %"v317" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v319" : L = Shl %"pr.1", #3;
    %"v320" = %"v317" +p %"v319";
    %"v321" = %"v320" +p #4;
    %"chk40" : A = (Check 0 4 Read 1) %"v321";
    %"v322" : W = (RawLoad (LdNarrow Uw) 0) %"chk40"
    => goto "L302" };
  ir_blk{ @"L302" [%"v323" : W = phi("L300" => %"v314", "L301" => %"v322")]:
    %"v324" : L = (Ext Uw) %"v323";
    %"v325" = %"v299" +p %"v324";
    %"v330" = %"v36" +p #24;
    %"chk41" : A = (Renew 0 4 Read 1) %"chk36", %"v330";
    %"v331" : W = (RawLoad (LdNarrow Sw) 0) %"chk41"
    => br %"v331" ? "L326" : "L327" };
  ir_blk{ @"L326":
    %"v333" = %"v36" +p #56;
    %"chk42" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v333";
    %"v334" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v336" : L = Shl %"pr.1", #3;
    %"v337" = %"v334" +p %"v336";
    %"chk43" : A = (Check 0 4 Read 1) %"v337";
    %"v338" : W = (RawLoad (LdNarrow Uw) 0) %"chk43";
    call %"v339" : W = $"glibc_dcigettext#__bswap_32"(W %"v338")
    => goto "L328" };
  ir_blk{ @"L327":
    %"v341" = %"v36" +p #56;
    %"chk44" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v341";
    %"v342" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v344" : L = Shl %"pr.1", #3;
    %"v345" = %"v342" +p %"v344";
    %"chk45" : A = (Check 0 4 Read 1) %"v345";
    %"v346" : W = (RawLoad (LdNarrow Uw) 0) %"chk45"
    => goto "L328" };
  ir_blk{ @"L328" [%"v347" : W = phi("L326" => %"v339", "L327" => %"v346")]:
    %"v348" : W = Add %"v347", #1;
    %"v349" : L = (Ext Uw) %"v348"
    => goto "L293" };
  ir_blk{ @"L292":
    %"v351" = %"v36" +p #80;
    %"chk46" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v351";
    %"v352" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v356" : L = Sub %"pr.1", %"v296";
    %"v357" : L = Shl %"v356", #4;
    %"v358" = %"v352" +p %"v357";
    %"v359" = %"v358" +p #8;
    %"chk47" : A = (Check 0 8 Read 8) %"v359";
    %"v360" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v363" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v369" = %"v363" +p %"v357";
    %"chk49" : A = (Check 0 8 Read 1) %"v369";
    %"v370" : L = (RawLoad LdL 0) %"chk49"
    => goto "L293" };
  ir_blk{ @"L293" [%"pr.5" : L = phi("L292" => %"v370", "L328" => %"v349"); %"pr.2" : P = phi("L292" => %"v360", "L328" => %"v325")]:
    => br %"v6" ? "L371" : "L373" };
  ir_blk{ @"L371":
    call %"v377" : P = $"glibc_dcigettext#get_output_charset"(P %"v2");
    %"v382" = %"v36" +p #128;
    call %"v383" : W = $"__GI___pthread_rwlock_rdlock"(P %"v382");
    %"v385" = %"v36" +p #120;
    %"chk50" : A = (HalfCheck Upper 0 8 Read 1) %"chk3", %"v385";
    %"v386" : L = (RawLoad LdL 0) %"chk50"
    => goto "L388" };
  ir_blk{ @"L388" [%"pr.17" : L = phi("L371" => %"v386", "L389" => %"v395")]:
    %"v393" : W = (Cmp Ugt L) %"pr.17", #0
    => br %"v393" ? "L389" : "L391" };
  ir_blk{ @"L389":
    %"v395" : L = Sub %"pr.17", #1;
    %"v400" = %"v36" +p #112;
    %"chk51" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v400";
    %"v401" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v403" : L = Mul %"v395", #24;
    %"v404" = %"v401" +p %"v403";
    %"chk52" : A = (Check 0 8 Read 8) %"v404";
    %"v405" : P = (RawLoadPointer 0 load_effects) %"chk52";
    call %"v407" : W = $"__GI_strcmp"(P %"v405", P %"v377");
    %"v408" : W = (Cmp Eq W) %"v407", #0
    => br %"v408" ? "L396" : poll "L388" };
  ir_blk{ @"L396":
    %"v410" = %"v36" +p #112;
    %"chk53" : A = (Renew 0 8 Read 8) %"chk51", %"v410";
    %"v411" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v414" = %"v411" +p %"v403"
    => goto "L391" };
  ir_blk{ @"L391" [%"pr.14" : P = phi("L388" => #0, "L396" => %"v414")]:
    %"v417" = %"v36" +p #128;
    call %"v418" : W = $"__GI___pthread_rwlock_unlock"(P %"v417");
    %"v423" : L = Ptoi %"pr.14";
    %"v425" : W = (Cmp Eq L) %"v423", %"v31"
    => br %"v425" ? "L419" : "L421" };
  ir_blk{ @"L419":
    %"v427" = %"v36" +p #128;
    call %"v428" : W = $"__GI___pthread_rwlock_wrlock"(P %"v427");
    %"v430" = %"v36" +p #120;
    %"chk54" : A = (Renew 0 8 Read 1) %"chk50", %"v430";
    %"v431" : L = (RawLoad LdL 0) %"chk54"
    => goto "L433" };
  ir_blk{ @"L433" [%"pr.18" : L = phi("L419" => %"v431", "L434" => %"v440")]:
    %"v438" : W = (Cmp Ugt L) %"pr.18", #0
    => br %"v438" ? "L434" : "L436" };
  ir_blk{ @"L434":
    %"v440" : L = Sub %"pr.18", #1;
    %"v445" = %"v36" +p #112;
    %"chk55" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v445";
    %"v446" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v448" : L = Mul %"v440", #24;
    %"v449" = %"v446" +p %"v448";
    %"chk56" : A = (Check 0 8 Read 8) %"v449";
    %"v450" : P = (RawLoadPointer 0 load_effects) %"chk56";
    call %"v452" : W = $"__GI_strcmp"(P %"v450", P %"v377");
    %"v453" : W = (Cmp Eq W) %"v452", #0
    => br %"v453" ? "L441" : poll "L433" };
  ir_blk{ @"L441":
    %"v455" = %"v36" +p #112;
    %"chk57" : A = (Renew 0 8 Read 8) %"chk55", %"v455";
    %"v456" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"v459" = %"v456" +p %"v448"
    => goto "L460" };
  ir_blk{ @"L436":
    %"v467" = %"v36" +p #112;
    %"chk58" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v467";
    %"v468" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v469" : L = Ptoi %"v468";
    %"v471" : W = (Cmp Ne L) %"v469", %"v31"
    => br %"v471" ? "L463" : "L464" };
  ir_blk{ @"L463":
    %"v473" = %"v36" +p #112;
    %"v474" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v476" : L = Add %"v431", #1;
    %"v477" : L = Mul %"v476", #24;
    call %"v478" : P = $"realloc"(P %"v474", L %"v477")
    => goto "L465" };
  ir_blk{ @"L464":
    %"v480" : L = Add %"v431", #1;
    %"v481" : L = Mul %"v480", #24;
    call %"v482" : P = $"malloc"(L %"v481")
    => goto "L465" };
  ir_blk{ @"L465" [%"v483" : P = phi("L463" => %"v478", "L464" => %"v482")]:
    %"v488" : L = Ptoi %"v483";
    %"v490" : W = (Cmp Eq L) %"v488", %"v31"
    => br %"v490" ? "L493" : "L486" };
  ir_blk{ @"L493":
    %"v495" = %"v36" +p #128;
    call %"v496" : W = $"__GI___pthread_rwlock_unlock"(P %"v495");
    (Flight (a "v499") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v499" };
  ir_blk{ @"L486":
    %"v502" = %"v36" +p #112;
    %"chk60" : A = (Renew 0 8 Write 8) %"chk58", %"v502";
    store.ptr [%"chk60" + 0] <- %"v483";
    call %"v505" : P = $"__GI___strdup"(P %"v377");
    %"v510" : L = Ptoi %"v505";
    %"v512" : W = (Cmp Eq L) %"v510", %"v31"
    => br %"v512" ? poll "L493" : "L508" }] [ir_blk{ @"L508":
    %"v518" : L = Mul %"v431", #24;
    %"v519" = %"v483" +p %"v518";
    %"chk61" : A = (Check 0 8 Write 8) %"v519";
    store.ptr [%"chk61" + 0] <- %"v505";
    %"v523" = %"v519" +p #8;
    (Flight (a "v526") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk62" : A = (HalfCheck Upper 0 8 Write 8) %"chk61", %"v523";
    store.ptr [%"chk62" + 0] <- %"v526";
    %"v531" : P = Copy $"glibc_dcigettext#str.279";
    call %"v532" : P = $"_nl_find_msg"(P %"v0", P %"v2", P %"v531", W #0, P %"v528");
    %"v540" : L = Ptoi %"v532";
    %"v541" : L = Ptoi %"v526";
    %"v542" : W = (Cmp Eq L) %"v540", %"v541"
    => br %"v542" ? "L533" : "L535" };
  ir_blk{ @"L533":
    (Flight (a "v547") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v547" };
  ir_blk{ @"L535":
    %"v555" : W = (Cmp Ne L) %"v540", %"v31"
    => br %"v555" ? "L549" : "L551" };
  ir_blk{ @"L549":
    %"v558" : P = Copy $"glibc_dcigettext#str.280";
    call %"v559" : P = $"__GI_strstr"(P %"v532", P %"v558");
    %"v564" : L = Ptoi %"v559";
    %"v566" : W = (Cmp Ne L) %"v564", %"v31"
    => br %"v566" ? "L560" : "L551" };
  ir_blk{ @"L560":
    %"v571" : P = Copy $"glibc_dcigettext#str.280";
    call %"v572" : L = $"__GI_strlen"(P %"v571");
    %"v573" = %"v559" +p %"v572";
    %"v575" : P = Copy $"glibc_dcigettext#str.281";
    call %"v576" : L = $"__GI_strcspn"(P %"v573", P %"v575");
    %"v578" : L = Add %"v576", #1;
    %"v579" : P = (Alloc 16) %"v578";
    call %"v583" : P = $"__GI_mempcpy"(P %"v579", P %"v573", L %"v576");
    %"chk63" : A = (Check 0 1 Write 1) %"v583";
    store Wb [%"chk63" + 0] <- #0;
    call %"v588" : P = $"__GI___gconv_create_spec"(P %"v585", P %"v579", P %"v505");
    %"v589" = %"v585" +p #16;
    %"chk64" : A = (Check 0 1 Write 1) %"v589";
    store Wb [%"chk64" + 0] <- #1;
    %"v593" = %"v519" +p #8;
    call %"v594" : W = $"__GI___gconv_open"(P %"v585", P %"v593", W #1);
    call void $"__GI___gconv_destroy_spec"(P %"v585");
    %"v599" : W = (Cmp Ne W) %"v594", #0
    => br %"v599" ? "L595" : "L551" };
  ir_blk{ @"L595":
    %"v606" : W = (Cmp Ne W) %"v594", #(-1)
    => br %"v606" ? "L602" : "L604" };
  ir_blk{ @"L602":
    %"v610" = %"v36" +p #128;
    call %"v611" : W = $"__GI___pthread_rwlock_unlock"(P %"v610");
    call void $"free"(P %"v505")
    => ret #0 };
  ir_blk{ @"L604":
    %"v615" = %"v519" +p #8;
    (Flight (a "v618") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk65" : A = (Renew 0 8 Write 8) %"chk62", %"v615";
    store.ptr [%"chk65" + 0] <- %"v618"
    => goto "L551" };
  ir_blk{ @"L551":
    %"v620" = %"v519" +p #16;
    %"chk66" : A = (HalfCheck Upper 0 8 Write 8) %"chk61", %"v620";
    store.ptr [%"chk66" + 0] <- #0;
    %"v622" = %"v36" +p #120;
    %"chk67" : A = (Renew 0 8 Read 1) %"chk50", %"v622";
    %"v623" : L = (RawLoad LdL 0) %"chk67";
    %"v624" : L = Add %"v623", #1;
    %"chk68" : A = (Renew 0 8 Write 1) %"chk50", %"v622";
    store Wl [%"chk68" + 0] <- %"v624"
    => goto "L460" };
  ir_blk{ @"L460" [%"pr.16" : P = phi("L441" => %"v459", "L551" => %"v519")]:
    %"v626" = %"v36" +p #128;
    call %"v627" : W = $"__GI___pthread_rwlock_unlock"(P %"v626")
    => goto "L421" };
  ir_blk{ @"L421" [%"pr.15" : P = phi("L460" => %"pr.16", "L391" => %"pr.14")]:
    %"v632" = %"pr.15" +p #8;
    %"chk69" : A = (Check 0 8 Read 8) %"v632";
    %"v633" : P = (RawLoadPointer 0 load_effects) %"chk69";
    (Flight (a "v636") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v637" : L = Ptoi %"v633";
    %"v638" : L = Ptoi %"v636";
    %"v639" : W = (Cmp Ne L) %"v637", %"v638"
    => br %"v639" ? "L628" : "L373" };
  ir_blk{ @"L628":
    %"v644" = %"pr.15" +p #16;
    %"chk70" : A = (HalfCheck Upper 0 8 Read 8) %"chk69", %"v644";
    %"v645" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v646" : L = Ptoi %"v645";
    %"v648" : W = (Cmp Eq L) %"v646", %"v31"
    => br %"v648" ? "L640" : "L642" };
  ir_blk{ @"L640":
    %"v652" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk71" : A = (Check 0 4 Write 4) %"v652";
    %"v659" : W = (RawCas (CasNarrow Sw) 0) %"chk71", #0, #1;
    %"v660" : W = (Cmp Eq W) %"v659", #0
    => br %"v660" ? "L662" : "L661" };
  ir_blk{ @"L661":
    => goto "L662" };
  ir_blk{ @"L662":
    %"v663" : W = (Cmp Ne W) %"v659", #0
    => br %"v663" ? "L666" : "L655" };
  ir_blk{ @"L666":
    call void $"__GI___lll_lock_wait_private"(P %"v652")
    => goto "L655" };
  ir_blk{ @"L655":
    %"v680" = %"pr.15" +p #16;
    %"chk72" : A = (Renew 0 8 Read 8) %"chk70", %"v680";
    %"v681" : P = (RawLoadPointer 0 load_effects) %"chk72";
    %"v682" : L = Ptoi %"v681";
    %"v684" : W = (Cmp Eq L) %"v682", %"v31"
    => br %"v684" ? "L676" : "L678" };
  ir_blk{ @"L676":
    %"v686" = %"pr.15" +p #16;
    %"v689" = %"v36" +p #64;
    %"chk73" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v689";
    %"v690" : W = (RawLoad (LdNarrow Uw) 0) %"chk73";
    %"v691" : W = Add %"v39", %"v690";
    %"v692" : L = (Ext Uw) %"v691";
    call %"v693" : P = $"calloc"(L %"v692", L #8);
    %"chk74" : A = (Renew 0 8 Write 8) %"chk70", %"v686";
    store.ptr [%"chk74" + 0] <- %"v693";
    %"chk75" : A = (Renew 0 8 Read 8) %"chk70", %"v686";
    %"v699" : P = (RawLoadPointer 0 load_effects) %"chk75";
    %"v700" : L = Ptoi %"v699";
    %"v702" : W = (Cmp Ne L) %"v700", %"v31"
    => br %"v702" ? "L703" : "L696" };
  ir_blk{ @"L696":
    %"v706" = %"pr.15" +p #16;
    (Flight (a "v709") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk76" : A = (Renew 0 8 Write 8) %"chk70", %"v706";
    store.ptr [%"chk76" + 0] <- %"v709"
    => goto "L678" };
  ir_blk{ @"L678":
    %"v711" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk77" : A = (Check 0 4 Read 1) %"v711";
    %"v715" : W = (RawLoad (LdNarrow Sw) 0) %"chk77"
    => goto "L716" };
  ir_blk{ @"L716" [%"v718" : W = phi("L678" => %"v715", "L716" => %"v719")]:
    %"chk78" : A = (HalfCheck Lower 0 4 Write 4) %"chk77", %"v711";
    %"v719" : W = (RawCas (CasNarrow Sw) 0) %"chk78", %"v718", #0;
    %"v720" : W = (Cmp Eq W) %"v719", %"v718"
    => br %"v720" ? "L717" : poll "L716" };
  ir_blk{ @"L717":
    %"v725" : W = (Cmp Sgt W) %"v718", #1
    => br %"v725" ? "L728" : "L642" };
  ir_blk{ @"L728":
    call void $"__GI___lll_lock_wake_private"(P %"v711")
    => goto "L642" };
  ir_blk{ @"L642":
    %"v743" = %"pr.15" +p #16;
    %"chk79" : A = (Renew 0 8 Read 8) %"chk70", %"v743";
    %"v744" : P = (RawLoadPointer 0 load_effects) %"chk79";
    (Flight (a "v747") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v748" : L = Ptoi %"v744";
    %"v749" : L = Ptoi %"v747";
    %"v750" : W = (Cmp Eq L) %"v748", %"v749"
    => br %"v750" ? "L739" : "L741" };
  ir_blk{ @"L739":
    (Flight (a "v755") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v755" };
  ir_blk{ @"L741":
    %"v761" = %"pr.15" +p #16;
    %"v762" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v764" : L = Shl %"pr.1", #3;
    %"v765" = %"v762" +p %"v764";
    %"chk81" : A = (Check 0 8 Read 8) %"v765";
    %"v766" : P = (RawLoadPointer 0 load_effects) %"chk81";
    %"v767" : L = Ptoi %"v766";
    %"v769" : W = (Cmp Eq L) %"v767", %"v31"
    => br %"v769" ? "L757" : "L759" };
  ir_blk{ @"L757":
    %"v774" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk82" : A = (Check 0 4 Write 4) %"v774";
    %"v781" : W = (RawCas (CasNarrow Sw) 0) %"chk82", #0, #1;
    %"v782" : W = (Cmp Eq W) %"v781", #0
    => br %"v782" ? "L784" : "L783" };
  ir_blk{ @"L783":
    => goto "L784" };
  ir_blk{ @"L784":
    %"v785" : W = (Cmp Ne W) %"v781", #0
    => br %"v785" ? "L788" : "L703" };
  ir_blk{ @"L788":
    call void $"__GI___lll_lock_wait_private"(P %"v774")
    => goto "L703" };
  ir_blk{ @"L703":
    %"chk83" : A = (Check 0 8 Write 8) %"v770";
    store.ptr [%"chk83" + 0] <- %"pr.2"
    => goto "L799" };
  ir_blk{ @"L799" [%"pr.19" : W = phi("L703" => #0, "L927" => %"pr.20")]:
    %"v806" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk84" : A = (Check 0 8 Read 1) %"v806";
    %"v807" : L = (RawLoad LdL 0) %"chk84";
    %"v808" : W = (Cmp Ult L) %"v807", #8
    => br %"v808" ? "L809" : "L805" };
  ir_blk{ @"L805":
    %"v811" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk85" : A = (Check 0 8 Read 8) %"v811";
    %"v812" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v813" = %"v812" +p #8;
    %"chk86" : A = (Check 0 8 Write 8) %"v771";
    store.ptr [%"chk86" + 0] <- %"v813";
    %"v817" = %"pr.15" +p #8;
    %"chk87" : A = (Renew 0 8 Read 8) %"chk69", %"v817";
    %"v818" : P = (RawLoadPointer 0 load_effects) %"chk87";
    %"chk88" : A = (Renew 0 8 Read 8) %"chk83", %"v770";
    %"v819" : P = (RawLoadPointer 0 load_effects) %"chk88";
    %"v821" = %"v819" +p %"pr.5";
    %"chk89" : A = (Renew 0 8 Read 8) %"chk86", %"v771";
    %"v822" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"v823" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk90" : A = (Check 0 8 Read 1) %"v823";
    %"v824" : L = (RawLoad LdL 0) %"chk90";
    %"v825" = %"v822" +p %"v824";
    (Flight (a "v826") Sub [(FAddress (t "v825")); (FValue (Const 8))] (LowerOf (t "v825")));
    call %"v827" : W = $"__gconv"(P %"v818", P %"v770", P %"v821", P %"v771", P %"v826", P %"v814");
    %"v832" : W = (Cmp Eq W) %"v827", #0
    => br %"v832" ? "L834" : "L833" };
  ir_blk{ @"L833":
    %"v836" : W = (Cmp Eq W) %"v827", #4
    => goto "L834" };
  ir_blk{ @"L834" [%"v838" : W = phi("L805" => #1, "L833" => %"v836")]:
    => br %"v838" ? "L801" : "L830" };
  ir_blk{ @"L830":
    %"v844" : W = (Cmp Ne W) %"v827", #5
    => br %"v844" ? "L840" : "L842" };
  ir_blk{ @"L840":
    %"v846" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk91" : A = (Check 0 4 Read 1) %"v846";
    %"v850" : W = (RawLoad (LdNarrow Sw) 0) %"chk91"
    => goto "L851" };
  ir_blk{ @"L851" [%"v853" : W = phi("L840" => %"v850", "L851" => %"v854")]:
    %"chk92" : A = (HalfCheck Lower 0 4 Write 4) %"chk91", %"v846";
    %"v854" : W = (RawCas (CasNarrow Sw) 0) %"chk92", %"v853", #0;
    %"v855" : W = (Cmp Eq W) %"v854", %"v853"
    => br %"v855" ? "L852" : poll "L851" };
  ir_blk{ @"L852":
    %"v860" : W = (Cmp Sgt W) %"v853", #1
    => br %"v860" ? "L863" : "L858" };
  ir_blk{ @"L863":
    call void $"__GI___lll_lock_wake_private"(P %"v846")
    => goto "L858" };
  ir_blk{ @"L858":
    => ret #0 };
  ir_blk{ @"L842":
    %"chk93" : A = (Renew 0 8 Write 8) %"chk83", %"v770";
    store.ptr [%"chk93" + 0] <- %"pr.2"
    => goto "L809" };
  ir_blk{ @"L809":
    %"v880" : W = (Cmp Sgt W) %"pr.19", #0
    => br %"v880" ? "L876" : "L877" };
  ir_blk{ @"L876":
    %"v882" : W = Add %"pr.19", #1;
    %"v883" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"v885" : W = Mul %"v882", #4080;
    %"v886" : L = (Ext Sw) %"v885";
    %"chk94" : A = (Check 0 8 Write 1) %"v883";
    store Wl [%"chk94" + 0] <- %"v886";
    %"v887" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk95" : A = (Check 0 8 Read 8) %"v887";
    %"v888" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v889" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk96" : A = (Check 0 8 Read 1) %"v889";
    %"v890" : L = (RawLoad LdL 0) %"chk96";
    call %"v891" : P = $"realloc"(P %"v888", L %"v890");
    %"v896" : L = Ptoi %"v891";
    %"v898" : W = (Cmp Ne L) %"v896", %"v31"
    => br %"v898" ? "L892" : "L893" };
  ir_blk{ @"L892":
    %"v899" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk97" : A = (Check 0 8 Write 8) %"v899";
    store.ptr [%"chk97" + 0] <- %"v891"
    => goto "L878" };
  ir_blk{ @"L893":
    %"v902" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk98" : A = (Check 0 8 Read 8) %"v902";
    %"v903" : P = (RawLoadPointer 0 load_effects) %"chk98";
    %"v904" : P = Copy $"glibc_dcigettext#transmem_list";
    %"v905" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk99" : A = (Check 0 8 Read 8) %"v905";
    %"v906" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"chk100" : A = (Check 0 8 Read 8) %"v906";
    %"v907" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"chk101" : A = (Check 0 8 Write 8) %"v904";
    store.ptr [%"chk101" + 0] <- %"v907";
    call void $"free"(P %"v903")
    => goto "L878" };
  ir_blk{ @"L877":
    %"v909" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk102" : A = (Check 0 8 Write 1) %"v909";
    store Wl [%"chk102" + 0] <- #4080;
    %"v910" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk103" : A = (Check 0 8 Read 1) %"v910";
    %"v911" : L = (RawLoad LdL 0) %"chk103";
    call %"v912" : P = $"malloc"(L %"v911");
    %"v917" : L = Ptoi %"v912";
    %"v919" : W = (Cmp Ne L) %"v917", %"v31"
    => br %"v919" ? "L913" : "L878" };
  ir_blk{ @"L913":
    %"v921" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk104" : A = (Check 0 8 Read 8) %"v921";
    %"v922" : P = (RawLoadPointer 0 load_effects) %"chk104";
    %"chk105" : A = (Check 0 8 Write 8) %"v912";
    store.ptr [%"chk105" + 0] <- %"v922";
    %"v923" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk106" : A = (Check 0 8 Write 8) %"v923";
    store.ptr [%"chk106" + 0] <- %"v912"
    => goto "L878" };
  ir_blk{ @"L878" [%"pr.21" : P = phi("L892" => %"v891", "L893" => %"v891", "L913" => %"v912", "L877" => %"v912"); %"pr.20" : W = phi("L892" => %"v882", "L893" => %"v882", "L913" => #1, "L877" => #1)]:
    %"v929" : L = Ptoi %"pr.21";
    %"v931" : W = (Cmp Eq L) %"v929", %"v31"
    => br %"v931" ? "L925" : "L927" };
  ir_blk{ @"L925":
    %"v934" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk107" : A = (Check 0 8 Write 8) %"v934";
    store.ptr [%"chk107" + 0] <- #0;
    %"v935" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk108" : A = (Check 0 8 Write 1) %"v935";
    store Wl [%"chk108" + 0] <- #0;
    %"v937" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk109" : A = (Check 0 4 Read 1) %"v937";
    %"v941" : W = (RawLoad (LdNarrow Sw) 0) %"chk109"
    => goto "L942" };
  ir_blk{ @"L942" [%"v944" : W = phi("L925" => %"v941", "L942" => %"v945")]:
    %"chk110" : A = (HalfCheck Lower 0 4 Write 4) %"chk109", %"v937";
    %"v945" : W = (RawCas (CasNarrow Sw) 0) %"chk110", %"v944", #0;
    %"v946" : W = (Cmp Eq W) %"v945", %"v944"
    => br %"v946" ? "L943" : poll "L942" };
  ir_blk{ @"L943":
    %"v951" : W = (Cmp Sgt W) %"v944", #1
    => br %"v951" ? "L954" : "L949" };
  ir_blk{ @"L954":
    call void $"__GI___lll_lock_wake_private"(P %"v937")
    => goto "L949" };
  ir_blk{ @"L949":
    (Flight (a "v967") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v967" };
  ir_blk{ @"L927":
    %"v969" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"v971" = %"pr.21" +p #8;
    %"chk111" : A = (Check 0 8 Write 8) %"v969";
    store.ptr [%"chk111" + 0] <- %"v971";
    %"v972" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk112" : A = (Check 0 8 Read 1) %"v972";
    %"v973" : L = (RawLoad LdL 0) %"chk112";
    %"v974" : L = Sub %"v973", #8;
    %"chk113" : A = (Renew 0 8 Write 1) %"chk112", %"v972";
    store Wl [%"chk113" + 0] <- %"v974"
    => goto poll "L799" };
  ir_blk{ @"L801":
    %"v975" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk114" : A = (Check 0 8 Read 8) %"v975";
    %"v976" : P = (RawLoadPointer 0 load_effects) %"chk114";
    %"chk115" : A = (Renew 0 8 Read 8) %"chk86", %"v771";
    %"v977" : P = (RawLoadPointer 0 load_effects) %"chk115";
    %"v978" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk116" : A = (Check 0 8 Read 8) %"v978";
    %"v979" : P = (RawLoadPointer 0 load_effects) %"chk116";
    %"v980" : L = Ptoi %"v977";
    %"v981" : L = Ptoi %"v979";
    %"v982" : L = Sub %"v980", %"v981";
    %"v983" : L = Sub %"v982", #8;
    %"chk117" : A = (Check 0 8 Write 1) %"v976";
    store Wl [%"chk117" + 0] <- %"v983";
    %"v985" = %"pr.15" +p #16;
    %"chk118" : A = (Renew 0 8 Read 8) %"chk70", %"v985";
    %"v986" : P = (RawLoadPointer 0 load_effects) %"chk118";
    %"v988" : L = Shl %"pr.1", #3;
    %"v989" = %"v986" +p %"v988";
    %"v990" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk119" : A = (Check 0 8 Read 8) %"v990";
    %"v991" : P = (RawLoadPointer 0 load_effects) %"chk119";
    %"chk120" : A = (Check 0 8 Write 8) %"v989";
    store.ptr [%"chk120" + 0] <- %"v991";
    %"v992" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk121" : A = (Check 0 8 Read 1) %"v992";
    %"v993" : L = (RawLoad LdL 0) %"chk121";
    %"chk122" : A = (Renew 0 8 Read 8) %"chk86", %"v771";
    %"v994" : P = (RawLoadPointer 0 load_effects) %"chk122";
    %"v995" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk123" : A = (Check 0 8 Read 8) %"v995";
    %"v996" : P = (RawLoadPointer 0 load_effects) %"chk123";
    %"v997" : L = Ptoi %"v994";
    %"v998" : L = Ptoi %"v996";
    %"v999" : L = Sub %"v997", %"v998";
    %"v1000" : L = Sub %"v993", %"v999";
    %"chk124" : A = (Renew 0 8 Write 1) %"chk121", %"v992";
    store Wl [%"chk124" + 0] <- %"v1000";
    %"v1001" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk125" : A = (Renew 0 8 Read 8) %"chk86", %"v771";
    %"v1002" : P = (RawLoadPointer 0 load_effects) %"chk125";
    %"chk126" : A = (Check 0 8 Write 8) %"v1001";
    store.ptr [%"chk126" + 0] <- %"v1002";
    %"v1003" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk127" : A = (Check 0 8 Read 8) %"v1003";
    %"v1004" : P = (RawLoadPointer 0 load_effects) %"chk127";
    %"v1005" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk128" : A = (Check 0 8 Read 1) %"v1005";
    %"v1006" : L = (RawLoad LdL 0) %"chk128";
    %"v1008" : L = And %"v1006", #7;
    %"v1009" = %"v1004" +p %"v1008";
    %"chk129" : A = (Renew 0 8 Write 8) %"chk127", %"v1003";
    store.ptr [%"chk129" + 0] <- %"v1009";
    %"v1010" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"v1011" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk130" : A = (Check 0 8 Read 1) %"v1011";
    %"v1012" : L = (RawLoad LdL 0) %"chk130";
    %"v1015" : L = And %"v1012", #18446744073709551608;
    %"chk131" : A = (Check 0 8 Write 1) %"v1010";
    store Wl [%"chk131" + 0] <- %"v1015";
    %"v1017" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk132" : A = (Check 0 4 Read 1) %"v1017";
    %"v1021" : W = (RawLoad (LdNarrow Sw) 0) %"chk132"
    => goto "L1022" };
  ir_blk{ @"L1022" [%"v1024" : W = phi("L801" => %"v1021", "L1022" => %"v1025")]:
    %"chk133" : A = (HalfCheck Lower 0 4 Write 4) %"chk132", %"v1017";
    %"v1025" : W = (RawCas (CasNarrow Sw) 0) %"chk133", %"v1024", #0;
    %"v1026" : W = (Cmp Eq W) %"v1025", %"v1024"
    => br %"v1026" ? "L1023" : poll "L1022" };
  ir_blk{ @"L1023":
    %"v1031" : W = (Cmp Sgt W) %"v1024", #1
    => br %"v1031" ? "L1034" : "L759" };
  ir_blk{ @"L1034":
    call void $"__GI___lll_lock_wake_private"(P %"v1017")
    => goto "L759" };
  ir_blk{ @"L759":
    %"v1046" = %"pr.15" +p #16;
    %"chk134" : A = (Renew 0 8 Read 8) %"chk70", %"v1046";
    %"v1047" : P = (RawLoadPointer 0 load_effects) %"chk134";
    %"v1049" : L = Shl %"pr.1", #3;
    %"v1050" = %"v1047" +p %"v1049";
    %"chk135" : A = (Check 0 8 Read 8) %"v1050";
    %"v1051" : P = (RawLoadPointer 0 load_effects) %"chk135";
    %"v1052" = %"v1051" +p #8;
    %"v1055" : P = (RawLoadPointer 0 load_effects) %"chk134";
    %"v1058" = %"v1055" +p %"v1049";
    %"chk137" : A = (Check 0 8 Read 8) %"v1058";
    %"v1059" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk138" : A = (Check 0 8 Read 1) %"v1059";
    %"v1060" : L = (RawLoad LdL 0) %"chk138"
    => goto "L373" };
  ir_blk{ @"L373" [%"pr.6" : L = phi("L759" => %"v1060", "L421" => %"pr.5", "L293" => %"pr.5"); %"pr.3" : P = phi("L759" => %"v1052", "L421" => %"pr.2", "L293" => %"pr.2")]:
    %"chk139" : A = (Check 0 8 Write 1) %"v8";
    store Wl [%"chk139" + 0] <- %"pr.6"
    => ret %"pr.3" }])) }.

Definition item__nl_state_lock : item :=
  (IData (a "_nl_state_lock") LExport 8 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4)]).

Definition fn_glibc_dcigettext'23__bswap_32 : func :=
  ir_fn{ "local" "glibc_dcigettext#__bswap_32"(W %"v0") -> (RClass W) {
  @"start":
    %"v3" : W = And %"v0", #4278190080;
    %"v4" : W = Shr %"v3", #24;
    %"v6" : W = And %"v0", #16711680;
    %"v7" : W = Shr %"v6", #8;
    %"v8" : W = Or %"v4", %"v7";
    %"v10" : W = And %"v0", #65280;
    %"v11" : W = Shl %"v10", #8;
    %"v12" : W = Or %"v8", %"v11";
    %"v14" : W = And %"v0", #255;
    %"v15" : W = Shl %"v14", #24;
    %"v16" : W = Or %"v12", %"v15"
    => ret %"v16"
} }.

Definition item_glibc_dcigettext'23_nl_find_msg'2efreemem'2e283 : item :=
  (IData (a "glibc_dcigettext#_nl_find_msg.freemem.283") LLocal 8 [(Zero 8)]).

Definition item_glibc_dcigettext'23_nl_find_msg'2efreemem_size'2e284 : item :=
  (IData (a "glibc_dcigettext#_nl_find_msg.freemem_size.284") LLocal 8 [(Zero 8)]).

Definition item_glibc_dcigettext'23_nl_find_msg'2elock'2e282 : item :=
  (IData (a "glibc_dcigettext#_nl_find_msg.lock.282") LLocal 4 [(Zero 4)]).

Definition fn_glibc_dcigettext'23get_output_charset : func :=
  ir_fn{ "local" "glibc_dcigettext#get_output_charset"(P %"v0") -> (RClass P) {
  @"start":
    %"v6" : L = Ptoi %"v0";
    %"v7" : L = Ptoi #0;
    %"v8" : W = (Cmp Ne L) %"v6", %"v7"
    => br %"v8" ? "L9" : "L10";
  @"L9":
    %"v12" = %"v0" +p #16;
    %"chk0" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : L = Ptoi %"v13";
    %"v16" : W = (Cmp Ne L) %"v14", %"v7"
    => goto "L10";
  @"L10" [%"v18" : W = phi("start" => #0, "L9" => %"v16")]:
    => br %"v18" ? "L2" : "L3";
  @"L2":
    %"v20" = %"v0" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => ret %"v21";
  @"L3":
    %"v26" : P = Copy $"glibc_dcigettext#get_output_charset.output_charset_cached.287";
    %"chk2" : A = (Check 0 4 Read 1) %"v26";
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v28" : W = (Cmp Eq W) %"v27", #0
    => br %"v28" ? "L23" : "L25";
  @"L23":
    %"v30" : P = Copy $"glibc_dcigettext#str.288";
    call %"v31" : P = $"__GI_getenv"(P %"v30");
    %"v36" : L = Ptoi %"v31";
    %"v38" : W = (Cmp Ne L) %"v36", %"v7"
    => br %"v38" ? "L39" : "L40";
  @"L39":
    %"chk3" : A = (Check 0 1 Read 1) %"v31";
    %"v43" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v44" : W = (Cmp Ne W) %"v43", #0
    => goto "L40";
  @"L40" [%"v46" : W = phi("L23" => #0, "L39" => %"v44")]:
    => br %"v46" ? "L32" : "L34";
  @"L32":
    call %"v49" : L = $"__GI_strlen"(P %"v31");
    %"v50" : L = Add %"v49", #1;
    call %"v53" : P = $"malloc"(L %"v50");
    %"v58" : L = Ptoi %"v53";
    %"v60" : W = (Cmp Ne L) %"v58", %"v7"
    => br %"v60" ? "L54" : "L56";
  @"L54":
    call %"v64" : P = $"__GI_memcpy"(P %"v53", P %"v31", L %"v50")
    => goto "L56";
  @"L56":
    %"v65" : P = Copy $"glibc_dcigettext#get_output_charset.output_charset_cache.286";
    %"chk4" : A = (Check 0 8 Write 8) %"v65";
    store.ptr [%"chk4" + 0] <- %"v53"
    => goto "L34";
  @"L34":
    %"v67" : P = Copy $"glibc_dcigettext#get_output_charset.output_charset_cached.287";
    %"chk5" : A = (Check 0 4 Write 1) %"v67";
    store Ww [%"chk5" + 0] <- #1
    => goto "L25";
  @"L25":
    %"v71" : P = Copy $"glibc_dcigettext#get_output_charset.output_charset_cache.286";
    %"chk6" : A = (Check 0 8 Read 8) %"v71";
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v73" : L = Ptoi %"v72";
    %"v75" : W = (Cmp Ne L) %"v73", %"v7"
    => br %"v75" ? "L68" : "L69";
  @"L68":
    %"v76" : P = Copy $"glibc_dcigettext#get_output_charset.output_charset_cache.286";
    %"chk7" : A = (Check 0 8 Read 8) %"v76";
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk7"
    => ret %"v77";
  @"L69":
    %"v79" : P = Copy $"__libc_tsd_LOCALE";
    %"chk8" : A = (Check 0 8 Read 8) %"v79";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"v80";
    %"v82" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v83" = %"v82" +p #56;
    %"v87" = %"v83" +p #112;
    %"chk10" : A = (Check 0 8 Read 8) %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk10"
    => ret %"v88"
} }.

Definition item_glibc_dcigettext'23get_output_charset'2eoutput_charset_cache'2e286 : item :=
  (IData (a "glibc_dcigettext#get_output_charset.output_charset_cache.286") LLocal 8 [(Zero 8)]).

Definition item_glibc_dcigettext'23get_output_charset'2eoutput_charset_cached'2e287 : item :=
  (IData (a "glibc_dcigettext#get_output_charset.output_charset_cached.287") LLocal 4 [(Zero 4)]).

Definition fn_glibc_dcigettext'23plural_eval_recurse : func :=
  ir_fn{ "local" "glibc_dcigettext#plural_eval_recurse"(P %"v0", L %"v2", W %"v4") -> (RTuple [L; L]) blocks ((app [ir_blk{ @"start":
    %"v10" : W = (Cmp Eq W) %"v4", #0
    => br %"v10" ? "L6" : "L8" };
  ir_blk{ @"L6":
    => (JRets [(Const 3); (Const 0)]) };
  ir_blk{ @"L8":
    %"v18" : W = Sub %"v4", #1;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v505" : W = (Cmp Eq W) %"v20", #0
    => br %"v505" ? "L23" : "L506" };
  ir_blk{ @"L23":
    %"v25" = %"v0" +p #4;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v25";
    %"v26" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v49" : W = (Cmp Eq W) %"v26", #0
    => br %"v49" ? "L29" : "L50" };
  ir_blk{ @"L29":
    => (JRets [(Const 0); (t "v2")]) };
  ir_blk{ @"L37":
    %"v42" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v42";
    %"v43" : L = (RawLoad LdL 0) %"chk2"
    => (JRets [(Const 0); (t "v43")]) };
  ir_blk{ @"L50":
    %"v51" : W = (Cmp Eq W) %"v26", #1
    => br %"v51" ? poll "L37" : "L22" };
  ir_blk{ @"L53":
    %"v56" = %"v0" +p #8;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v56";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk3";
    (Call (CTuple [((a "v62"), L); ((a "v63"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v58")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.18" : L = Shr %"v62", #32;
    %"v72" : W = Copy %"v62";
    %"v73" : W = (Cmp Ne W) %"v72", #0
    => br %"v73" ? "L69" : "L71" };
  ir_blk{ @"L69":
    %"sw.20" : L = (Ext Uw) %"v62";
    %"sw.22" : L = (Ext Uw) %"sw.18";
    %"sw.23" : L = Shl %"sw.22", #32;
    %"v74" : L = Or %"sw.23", %"sw.20"
    => (JRets [(t "v74"); (t "v63")]) };
  ir_blk{ @"L71":
    %"v84" : W = (Cmp Eq L) %"v63", #0;
    %"v85" : L = (Ext Sw) %"v84"
    => (JRets [(Const 0); (t "v85")]) };
  ir_blk{ @"L89":
    %"v92" = %"v0" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v92";
    %"v94" : P = (RawLoadPointer 0 load_effects) %"chk4";
    (Call (CTuple [((a "v98"), L); ((a "v99"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v94")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.30" : L = Shr %"v98", #32;
    %"v108" : W = Copy %"v98";
    %"v109" : W = (Cmp Ne W) %"v108", #0
    => br %"v109" ? "L105" : "L107" };
  ir_blk{ @"L105":
    %"sw.32" : L = (Ext Uw) %"v98";
    %"sw.34" : L = (Ext Uw) %"sw.30";
    %"sw.35" : L = Shl %"sw.34", #32;
    %"v110" : L = Or %"sw.35", %"sw.32"
    => (JRets [(t "v110"); (t "v99")]) };
  ir_blk{ @"L107":
    %"v118" = %"v0" +p #4;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v118";
    %"v119" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v120" : W = (Cmp Eq W) %"v119", #15
    => br %"v120" ? "L114" : "L115" };
  ir_blk{ @"L114":
    %"v126" : W = (Cmp Ne L) %"v99", #0
    => br %"v126" ? "L121" : "L123" };
  ir_blk{ @"L121":
    => (JRets [(Const 0); (Const 1)]) };
  ir_blk{ @"L123":
    %"v136" = %"v0" +p #8;
    %"v137" = %"v136" +p #8;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk6";
    (Call (CTuple [((a "v142"), L); ((a "v143"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v138")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.42" : L = Shr %"v142", #32;
    %"v152" : W = Copy %"v142";
    %"v153" : W = (Cmp Ne W) %"v152", #0
    => br %"v153" ? "L149" : "L151" };
  ir_blk{ @"L149":
    %"sw.44" : L = (Ext Uw) %"v142";
    %"sw.46" : L = (Ext Uw) %"sw.42";
    %"sw.47" : L = Shl %"sw.46", #32;
    %"v154" : L = Or %"sw.47", %"sw.44"
    => (JRets [(t "v154"); (t "v143")]) };
  ir_blk{ @"L151":
    %"v166" : W = (Cmp Ne L) %"v143", #0
    => br %"v166" ? "L163" : "L162" };
  ir_blk{ @"L162":
    => goto "L163" };
  ir_blk{ @"L163" [%"v167" : W = phi("L162" => #0, "L151" => #1)]:
    %"v168" : L = (Ext Sw) %"v167"
    => (JRets [(Const 0); (t "v168")]) };
  ir_blk{ @"L115":
    %"v177" = %"v0" +p #4;
    %"v178" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v179" : W = (Cmp Eq W) %"v178", #14
    => br %"v179" ? "L173" : "L174" };
  ir_blk{ @"L173":
    %"v186" : W = (Cmp Eq L) %"v99", #0
    => br %"v186" ? "L180" : "L182" };
  ir_blk{ @"L180":
    => (JRets [(Const 0); (Const 0)]) };
  ir_blk{ @"L182":
    %"v196" = %"v0" +p #8;
    %"v197" = %"v196" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v197";
    %"v198" : P = (RawLoadPointer 0 load_effects) %"chk8";
    (Call (CTuple [((a "v202"), L); ((a "v203"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v198")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.60" : L = Shr %"v202", #32;
    %"v212" : W = Copy %"v202";
    %"v213" : W = (Cmp Ne W) %"v212", #0
    => br %"v213" ? "L209" : "L211" };
  ir_blk{ @"L209":
    %"sw.62" : L = (Ext Uw) %"v202";
    %"sw.64" : L = (Ext Uw) %"sw.60";
    %"sw.65" : L = Shl %"sw.64", #32;
    %"v214" : L = Or %"sw.65", %"sw.62"
    => (JRets [(t "v214"); (t "v203")]) };
  ir_blk{ @"L211":
    %"v226" : W = (Cmp Ne L) %"v203", #0
    => br %"v226" ? "L223" : "L222" };
  ir_blk{ @"L222":
    => goto "L223" };
  ir_blk{ @"L223" [%"v227" : W = phi("L222" => #0, "L211" => #1)]:
    %"v228" : L = (Ext Sw) %"v227"
    => (JRets [(Const 0); (t "v228")]) };
  ir_blk{ @"L174":
    %"v235" = %"v0" +p #8;
    %"v236" = %"v235" +p #8;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v236";
    %"v237" : P = (RawLoadPointer 0 load_effects) %"chk9";
    (Call (CTuple [((a "v241"), L); ((a "v242"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v237")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.72" : L = Shr %"v241", #32;
    %"v251" : W = Copy %"v241";
    %"v252" : W = (Cmp Ne W) %"v251", #0
    => br %"v252" ? "L248" : "L250" };
  ir_blk{ @"L248":
    %"sw.74" : L = (Ext Uw) %"v241";
    %"sw.76" : L = (Ext Uw) %"sw.72";
    %"sw.77" : L = Shl %"sw.76", #32;
    %"v253" : L = Or %"sw.77", %"sw.74"
    => (JRets [(t "v253"); (t "v242")]) };
  ir_blk{ @"L250":
    %"v258" = %"v0" +p #4;
    %"chk10" : A = (Renew 0 4 Read 1) %"chk5", %"v258";
    %"v259" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"v426" : W = (Cmp Ult W) %"v259", #8
    => br %"v426" ? "L427" : "L428" };
  ir_blk{ @"L262":
    %"v270" : L = Mul %"v99", %"v242"
    => (JRets [(Const 0); (t "v270")]) };
  ir_blk{ @"L274":
    %"v280" : W = (Cmp Eq L) %"v242", #0
    => br %"v280" ? "L275" : "L277" };
  ir_blk{ @"L275":
    => (JRets [(Const 1); (Const 0)]) }] [ir_blk{ @"L277":
    %"v294" : L = Udiv %"v99", %"v242"
    => (JRets [(Const 0); (t "v294")]) };
  ir_blk{ @"L298":
    %"v304" : W = (Cmp Eq L) %"v242", #0
    => br %"v304" ? "L299" : "L301" };
  ir_blk{ @"L299":
    => (JRets [(Const 1); (Const 0)]) };
  ir_blk{ @"L301":
    %"v318" : L = Urem %"v99", %"v242"
    => (JRets [(Const 0); (t "v318")]) };
  ir_blk{ @"L322":
    %"v330" : L = Add %"v99", %"v242"
    => (JRets [(Const 0); (t "v330")]) };
  ir_blk{ @"L334":
    %"v342" : L = Sub %"v99", %"v242"
    => (JRets [(Const 0); (t "v342")]) };
  ir_blk{ @"L346":
    %"v354" : W = (Cmp Ult L) %"v99", %"v242";
    %"v355" : L = (Ext Sw) %"v354"
    => (JRets [(Const 0); (t "v355")]) };
  ir_blk{ @"L359":
    %"v367" : W = (Cmp Ugt L) %"v99", %"v242";
    %"v368" : L = (Ext Sw) %"v367"
    => (JRets [(Const 0); (t "v368")]) };
  ir_blk{ @"L372":
    %"v380" : W = (Cmp Ule L) %"v99", %"v242";
    %"v381" : L = (Ext Sw) %"v380"
    => (JRets [(Const 0); (t "v381")]) };
  ir_blk{ @"L385":
    %"v393" : W = (Cmp Uge L) %"v99", %"v242";
    %"v394" : L = (Ext Sw) %"v393"
    => (JRets [(Const 0); (t "v394")]) };
  ir_blk{ @"L398":
    %"v406" : W = (Cmp Eq L) %"v99", %"v242";
    %"v407" : L = (Ext Sw) %"v406"
    => (JRets [(Const 0); (t "v407")]) };
  ir_blk{ @"L411":
    %"v419" : W = (Cmp Ne L) %"v99", %"v242";
    %"v420" : L = (Ext Sw) %"v419"
    => (JRets [(Const 0); (t "v420")]) };
  ir_blk{ @"L427":
    %"v429" : W = (Cmp Ult W) %"v259", #5
    => br %"v429" ? "L430" : "L431" };
  ir_blk{ @"L430":
    %"v432" : W = (Cmp Eq W) %"v259", #3
    => br %"v432" ? poll "L262" : "L433" };
  ir_blk{ @"L433":
    %"v434" : W = (Cmp Eq W) %"v259", #4
    => br %"v434" ? poll "L274" : "L22" };
  ir_blk{ @"L431":
    %"v436" : W = (Cmp Eq W) %"v259", #5
    => br %"v436" ? poll "L298" : "L437" };
  ir_blk{ @"L437":
    %"v438" : W = (Cmp Eq W) %"v259", #6
    => br %"v438" ? poll "L322" : "L439" };
  ir_blk{ @"L439":
    %"v440" : W = (Cmp Eq W) %"v259", #7
    => br %"v440" ? poll "L334" : "L22" };
  ir_blk{ @"L428":
    %"v442" : W = (Cmp Ult W) %"v259", #11
    => br %"v442" ? "L443" : "L444" };
  ir_blk{ @"L443":
    %"v445" : W = (Cmp Eq W) %"v259", #8
    => br %"v445" ? poll "L346" : "L446" };
  ir_blk{ @"L446":
    %"v447" : W = (Cmp Eq W) %"v259", #9
    => br %"v447" ? poll "L359" : "L448" };
  ir_blk{ @"L448":
    %"v449" : W = (Cmp Eq W) %"v259", #10
    => br %"v449" ? poll "L372" : "L22" };
  ir_blk{ @"L444":
    %"v451" : W = (Cmp Eq W) %"v259", #11
    => br %"v451" ? poll "L385" : "L452" };
  ir_blk{ @"L452":
    %"v453" : W = (Cmp Eq W) %"v259", #12
    => br %"v453" ? poll "L398" : "L454" };
  ir_blk{ @"L454":
    %"v455" : W = (Cmp Eq W) %"v259", #13
    => br %"v455" ? poll "L411" : "L22" };
  ir_blk{ @"L457":
    %"v460" = %"v0" +p #8;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v460";
    %"v462" : P = (RawLoadPointer 0 load_effects) %"chk11";
    (Call (CTuple [((a "v466"), L); ((a "v467"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v462")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.156" : L = Shr %"v466", #32;
    %"v476" : W = Copy %"v466";
    %"v477" : W = (Cmp Ne W) %"v476", #0
    => br %"v477" ? "L473" : "L475" };
  ir_blk{ @"L473":
    %"sw.158" : L = (Ext Uw) %"v466";
    %"sw.160" : L = (Ext Uw) %"sw.156";
    %"sw.161" : L = Shl %"sw.160", #32;
    %"v478" : L = Or %"sw.161", %"sw.158"
    => (JRets [(t "v478"); (t "v467")]) };
  ir_blk{ @"L475":
    %"v483" = %"v0" +p #8;
    %"v489" : W = (Cmp Ne L) %"v467", #0
    => br %"v489" ? "L486" : "L485" };
  ir_blk{ @"L485":
    => goto "L486" };
  ir_blk{ @"L486" [%"v490" : W = phi("L485" => #2, "L475" => #1)]:
    %"v491" : L = (Ext Sw) %"v490";
    %"v492" : L = Shl %"v491", #3;
    %"v493" = %"v483" +p %"v492";
    %"chk12" : A = (Check 0 8 Read 8) %"v493";
    %"v494" : P = (RawLoadPointer 0 load_effects) %"chk12";
    (Call (CTuple [((a "v498"), L); ((a "v499"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v494")); (Arg L (t "v2")); (Arg W (t "v18"))])
    => (JRets [(t "v498"); (t "v499")]) };
  ir_blk{ @"L506":
    %"v507" : W = (Cmp Eq W) %"v20", #1
    => br %"v507" ? poll "L53" : "L508" };
  ir_blk{ @"L508":
    %"v509" : W = (Cmp Eq W) %"v20", #2
    => br %"v509" ? poll "L89" : "L510" };
  ir_blk{ @"L510":
    %"v511" : W = (Cmp Eq W) %"v20", #3
    => br %"v511" ? poll "L457" : "L22" };
  ir_blk{ @"L22":
    => (JRets [(Const 4); (Const 0)]) }])) }.

Definition item_glibc_dcigettext'23root : item :=
  (IData (a "glibc_dcigettext#root") LLocal 8 [(Zero 8)]).

Definition item_glibc_dcigettext'23str'2e275 : item :=
  (IData (a "glibc_dcigettext#str.275") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 47); (Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition item_glibc_dcigettext'23str'2e276 : item :=
  (IData (a "glibc_dcigettext#str.276") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 0)]).

Definition item_glibc_dcigettext'23str'2e277 : item :=
  (IData (a "glibc_dcigettext#str.277") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 109); (Item Wb 111); (Item Wb 0)]).

Definition item_glibc_dcigettext'23str'2e278 : item :=
  (IData (a "glibc_dcigettext#str.278") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 79); (Item Wb 83); (Item Wb 73); (Item Wb 88); (Item Wb 0)]).

Definition item_glibc_dcigettext'23str'2e279 : item :=
  (IData (a "glibc_dcigettext#str.279") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition item_glibc_dcigettext'23str'2e280 : item :=
  (IData (a "glibc_dcigettext#str.280") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 61); (Item Wb 0)]).

Definition item_glibc_dcigettext'23str'2e281 : item :=
  (IData (a "glibc_dcigettext#str.281") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 9); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_dcigettext'23str'2e285 : item :=
  (IData (a "glibc_dcigettext#str.285") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 65); (Item Wb 78); (Item Wb 71); (Item Wb 85); (Item Wb 65); (Item Wb 71); (Item Wb 69); (Item Wb 0)]).

Definition item_glibc_dcigettext'23str'2e288 : item :=
  (IData (a "glibc_dcigettext#str.288") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 85); (Item Wb 84); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 95); (Item Wb 67); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 83); (Item Wb 69); (Item Wb 84); (Item Wb 0)]).

Definition fn_glibc_dcigettext'23transcmp : func :=
  ir_fn{ "local" "glibc_dcigettext#transcmp"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v13" = %"v0" +p #32;
    %"chk0" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v15" : L = Ptoi %"v14";
    %"v16" : L = Ptoi #0;
    %"v17" : W = (Cmp Ne L) %"v15", %"v16"
    => br %"v17" ? "L9" : "L10";
  @"L9":
    %"v19" = %"v0" +p #56
    => goto "L11";
  @"L10":
    %"v21" = %"v0" +p #56;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L11";
  @"L11" [%"v23" : P = phi("L9" => %"v19", "L10" => %"v22")]:
    %"v28" = %"v2" +p #32;
    %"chk2" : A = (Check 0 8 Read 8) %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v30" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ne L) %"v30", %"v16"
    => br %"v32" ? "L24" : "L25";
  @"L24":
    %"v34" = %"v2" +p #56
    => goto "L26";
  @"L25":
    %"v36" = %"v2" +p #56;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk3"
    => goto "L26";
  @"L26" [%"v38" : P = phi("L24" => %"v34", "L25" => %"v37")]:
    call %"v39" : W = $"__GI_strcmp"(P %"v23", P %"v38");
    %"v44" : W = (Cmp Eq W) %"v39", #0
    => br %"v44" ? "L40" : "L42";
  @"L40":
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v2";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v49" : W = $"__GI_strcmp"(P %"v46", P %"v48");
    %"v54" : W = (Cmp Eq W) %"v49", #0
    => br %"v54" ? "L50" : "L42";
  @"L50":
    %"v56" = %"v0" +p #16;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v59" = %"v2" +p #16;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call %"v61" : W = $"__GI_strcmp"(P %"v57", P %"v60");
    %"v66" : W = (Cmp Eq W) %"v61", #0
    => br %"v66" ? "L62" : "L42";
  @"L62":
    %"v68" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v68";
    %"v69" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v71" = %"v2" +p #8;
    %"chk9" : A = (HalfCheck Lower 0 4 Read 1) %"chk2", %"v71";
    %"v72" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v73" : W = Sub %"v69", %"v72"
    => goto "L42";
  @"L42" [%"pr.1" : W = phi("L62" => %"v73", "L50" => %"v61", "L40" => %"v49", "L26" => %"v39")]:
    => ret %"pr.1"
} }.

Definition item_glibc_dcigettext'23transmem_list : item :=
  (IData (a "glibc_dcigettext#transmem_list") LLocal 8 [(Zero 8)]).

Definition item_glibc_dcigettext'23tree_lock : item :=
  (IData (a "glibc_dcigettext#tree_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4)]).
