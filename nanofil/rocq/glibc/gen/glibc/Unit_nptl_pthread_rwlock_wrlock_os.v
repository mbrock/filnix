(** This file defines checked IR from glibc’s `nptl/pthread_rwlock_wrlock.os` object.
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

Definition item___GI___pthread_rwlock_wrlock : item :=
  (IAlias (a "__GI___pthread_rwlock_wrlock") (a "export") (a "___pthread_rwlock_wrlock")).

Definition fn____pthread_rwlock_wrlock : func :=
  ir_fn{ "export" "___pthread_rwlock_wrlock"(P %"v0") -> (RClass W) blocks ((app [ir_blk{ @"start":
    (Flight (a "iw_1.v4") Copy [(FAddress (Const 0))] (LowerOf (Const 0)));
    %"iw_1.v10" : L = Ptoi %"iw_1.v4";
    %"iw_1.v11" : W = (Cmp Ne L) %"iw_1.v10", #0
    => br %"iw_1.v11" ? "iw_1.L17" : "iw_1.L13" };
  ir_blk{ @"iw_1.L17":
    %"iw_1.v20" = %"iw_1.v4" +p #8;
    %"chk0" : A = (Check 0 8 Read 1) %"iw_1.v20";
    %"iw_1.v21" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.iw_2.v3" : W = (Cmp Sge L) %"iw_1.v21", #0
    => br %"iw_1.iw_2.v3" ? "iw_1.iw_2.L4" : "iw_1.iw_2.L5" };
  ir_blk{ @"iw_1.iw_2.L4":
    %"iw_1.iw_2.v7" : W = (Cmp Slt L) %"iw_1.v21", #1000000000
    => goto "iw_1.iw_2.L5" };
  ir_blk{ @"iw_1.iw_2.L5" [%"iw_1.iw_2.v9" : W = phi("iw_1.L17" => #0, "iw_1.iw_2.L4" => %"iw_1.iw_2.v7")]:
    %"iw_1.v24" : W = (Cmp Eq W) %"iw_1.iw_2.v9", #0
    => goto "iw_1.L13" };
  ir_blk{ @"iw_1.L13" [%"iw_1.v30" : W = phi("start" => #0, "iw_1.iw_2.L5" => %"iw_1.v24")]:
    => br %"iw_1.v30" ? "iw_1.join" : "iw_1.L8" };
  ir_blk{ @"iw_1.L8":
    %"iw_1.v36" = %"v0" +p #24;
    %"chk1" : A = (Check 0 4 Read 1) %"iw_1.v36";
    %"iw_1.v37" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call %"iw_1.v38" : P = $"zthread_self_cookie"();
    %"iw_1.v39" = %"iw_1.v38" +p #720;
    %"chk2" : A = (Check 0 4 Read 1) %"iw_1.v39";
    %"iw_1.v40" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.v41" : W = (Cmp Eq W) %"iw_1.v37", %"iw_1.v40"
    => br %"iw_1.v41" ? "iw_1.join" : "iw_1.L34" };
  ir_blk{ @"iw_1.L34":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"v0";
    %"iw_1.v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk3"
    => goto "iw_1.L50" };
  ir_blk{ @"iw_1.L50" [%"iw_1.v52" : W = phi("iw_1.L34" => %"iw_1.v49", "iw_1.L50" => %"iw_1.v54")]:
    %"iw_1.v53" : W = Or %"iw_1.v52", #2;
    %"chk4" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v54" : W = (RawCas (CasNarrow Uw) 0) %"chk4", %"iw_1.v52", %"iw_1.v53";
    %"iw_1.v55" : W = (Cmp Eq W) %"iw_1.v54", %"iw_1.v52"
    => br %"iw_1.v55" ? "iw_1.L51" : poll "iw_1.L50" };
  ir_blk{ @"iw_1.L51":
    %"iw_1.v60" : W = And %"iw_1.v52", #2;
    %"iw_1.v61" : W = (Cmp Ne W) %"iw_1.v60", #0
    => br %"iw_1.v61" ? "iw_1.L56" : "iw_1.L58" };
  ir_blk{ @"iw_1.L56":
    %"iw_1.v66" = %"v0" +p #48;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.v66";
    %"iw_1.v67" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"iw_1.v68" : W = (Cmp Ne W) %"iw_1.v67", #0
    => br %"iw_1.v68" ? "iw_1.L70" : "iw_1.L83" };
  ir_blk{ @"iw_1.L70":
    %"iw_1.v75" = %"v0" +p #4;
    %"chk6" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v75";
    %"iw_1.v76" : W = (RawLoad (LdNarrow Uw) 0) %"chk6"
    => goto "iw_1.L77" };
  ir_blk{ @"iw_1.L77" [%"iw_1.v79" : W = phi("iw_1.L70" => %"iw_1.v76", "iw_1.L77" => %"iw_1.v81")]:
    %"iw_1.v80" : W = Add %"iw_1.v79", #1;
    %"chk7" : A = (HalfCheck Lower 0 4 Write 4) %"chk6", %"iw_1.v75";
    %"iw_1.v81" : W = (RawCas (CasNarrow Uw) 0) %"chk7", %"iw_1.v79", %"iw_1.v80";
    %"iw_1.v82" : W = (Cmp Eq W) %"iw_1.v81", %"iw_1.v79"
    => br %"iw_1.v82" ? "iw_1.L83" : poll "iw_1.L77" };
  ir_blk{ @"iw_1.L83" [%"iw_1.pr.11" : W = phi("iw_1.L77" => %"iw_1.v52", "iw_1.L56" => %"iw_1.v52", "iw_1.L164" => %"iw_1.v192", "iw_1.L205" => %"iw_1.v260", "iw_1.L103" => %"iw_1.pr.5", "iw_1.L152" => %"iw_1.pr.11"); %"iw_1.pr.2" : W = phi("iw_1.L77" => #0, "iw_1.L56" => #0, "iw_1.L164" => %"iw_1.pr.2", "iw_1.L205" => #1, "iw_1.L103" => %"iw_1.pr.2", "iw_1.L152" => %"iw_1.pr.2")]:
    %"iw_1.v91" : W = And %"iw_1.pr.11", #2;
    %"iw_1.v92" : W = (Cmp Eq W) %"iw_1.v91", #0
    => br %"iw_1.v92" ? "iw_1.L87" : "iw_1.L89" };
  ir_blk{ @"iw_1.L87":
    %"iw_1.v98" : W = Or %"iw_1.pr.11", #2;
    %"chk8" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v100" : W = (RawCas (CasNarrow Uw) 0) %"chk8", %"iw_1.pr.11", %"iw_1.v98";
    %"iw_1.v101" : W = (Cmp Eq W) %"iw_1.v100", %"iw_1.pr.11"
    => br %"iw_1.v101" ? "iw_1.L103" : "iw_1.L102" };
  ir_blk{ @"iw_1.L102":
    => goto "iw_1.L103" };
  ir_blk{ @"iw_1.L103" [%"iw_1.pr.5" : W = phi("iw_1.L102" => %"iw_1.v100", "iw_1.L87" => %"iw_1.pr.11")]:
    => br %"iw_1.v101" ? "iw_1.L93" : poll "iw_1.L83" };
  ir_blk{ @"iw_1.L93":
    => br %"iw_1.v68" ? "iw_1.L104" : "iw_1.L86" };
  ir_blk{ @"iw_1.L104":
    %"iw_1.v109" = %"v0" +p #4;
    %"chk9" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v109";
    %"iw_1.v111" : W = (RawLoad (LdNarrow Uw) 0) %"chk9"
    => goto "iw_1.L112" };
  ir_blk{ @"iw_1.L112" [%"iw_1.v114" : W = phi("iw_1.L104" => %"iw_1.v111", "iw_1.L112" => %"iw_1.v116")]:
    %"iw_1.v115" : W = Add %"iw_1.v114", #4294967295;
    %"chk10" : A = (HalfCheck Lower 0 4 Write 4) %"chk9", %"iw_1.v109";
    %"iw_1.v116" : W = (RawCas (CasNarrow Uw) 0) %"chk10", %"iw_1.v114", %"iw_1.v115";
    %"iw_1.v117" : W = (Cmp Eq W) %"iw_1.v116", %"iw_1.v114"
    => br %"iw_1.v117" ? "iw_1.L86" : poll "iw_1.L112" };
  ir_blk{ @"iw_1.L89":
    => br %"iw_1.v68" ? "iw_1.L120" : "iw_1.iw_3.start" };
  ir_blk{ @"iw_1.L120":
    %"iw_1.v126" = %"v0" +p #4;
    %"chk11" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v126";
    %"iw_1.v127" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"iw_1.v135" : W = And %"iw_1.v127", #2147483648;
    %"iw_1.v136" : W = (Cmp Ne W) %"iw_1.v135", #0
    => br %"iw_1.v136" ? "iw_1.L128" : "iw_1.iw_3.start" };
  ir_blk{ @"iw_1.L128":
    %"iw_1.v141" = %"v0" +p #4;
    %"iw_1.v146" : W = Sub %"iw_1.v127", #2147483648;
    %"iw_1.v147" : W = Sub %"iw_1.v146", #1;
    %"chk12" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"iw_1.v141";
    %"iw_1.v149" : W = (RawCas (CasNarrow Uw) 0) %"chk12", %"iw_1.v127", %"iw_1.v147";
    %"iw_1.v150" : W = (Cmp Eq W) %"iw_1.v149", %"iw_1.v127"
    => br %"iw_1.v150" ? "iw_1.L152" : "iw_1.L151" };
  ir_blk{ @"iw_1.L151":
    => goto "iw_1.L152" };
  ir_blk{ @"iw_1.L152":
    => br %"iw_1.v150" ? "iw_1.L137" : poll "iw_1.L83" };
  ir_blk{ @"iw_1.L137":
    %"chk13" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"iw_1.v154" : W = (RawLoad (LdNarrow Uw) 0) %"chk13"
    => goto "iw_1.L86" };
  ir_blk{ @"iw_1.iw_3.start":
    %"iw_1.iw_3.v6" = %"v0" +p #28;
    %"chk14" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.iw_3.v6";
    %"iw_1.iw_3.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"iw_1.iw_3.v8" : W = (Cmp Ne W) %"iw_1.iw_3.v7", #0
    => br %"iw_1.iw_3.v8" ? "iw_1.iw_3.L4" : "iw_1.iw_3.L3" };
  ir_blk{ @"iw_1.iw_3.L3":
    => goto "iw_1.iw_3.L4" };
  ir_blk{ @"iw_1.iw_3.L4" [%"iw_1.iw_3.v9" : W = phi("iw_1.iw_3.L3" => #0, "iw_1.iw_3.start" => #128)]:
    %"iw_1.v162" = %"v0" +p #12;
    %"chk15" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v162";
    %"iw_1.v163" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"iw_1.v169" : W = And %"iw_1.v163", #4294967293;
    %"iw_1.v170" : W = (Cmp Ne W) %"iw_1.v169", #1
    => br %"iw_1.v170" ? "iw_1.L172" : "iw_1.L171" };
  ir_blk{ @"iw_1.L171":
    %"iw_1.v175" : W = (Cmp Ne W) %"iw_1.v163", #3
    => br %"iw_1.v175" ? "iw_1.L176" : "iw_1.L172" };
  ir_blk{ @"iw_1.L176":
    %"iw_1.v179" = %"v0" +p #12;
    %"chk16" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"iw_1.v179";
    %"iw_1.v182" : W = (RawCas (CasNarrow Uw) 0) %"chk16", %"iw_1.v163", #3;
    %"iw_1.v183" : W = (Cmp Eq W) %"iw_1.v182", %"iw_1.v163"
    => br %"iw_1.v183" ? "iw_1.L185" : "iw_1.L184" };
  ir_blk{ @"iw_1.L184":
    => goto "iw_1.L185" };
  ir_blk{ @"iw_1.L185":
    %"iw_1.v186" : W = (Cmp Ne W) %"iw_1.v182", %"iw_1.v163"
    => goto "iw_1.L172" };
  ir_blk{ @"iw_1.L172" [%"iw_1.v190" : W = phi("iw_1.iw_3.L4" => #1, "iw_1.L171" => #0, "iw_1.L185" => %"iw_1.v186")]:
    => br %"iw_1.v190" ? "iw_1.L164" : "iw_1.L166" };
  ir_blk{ @"iw_1.L164":
    %"chk17" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"iw_1.v192" : W = (RawLoad (LdNarrow Uw) 0) %"chk17"
    => goto poll "iw_1.L83" };
  ir_blk{ @"iw_1.L166":
    %"iw_1.v197" = %"v0" +p #12;
    call %"iw_1.v202" : W = $"__GI___futex_abstimed_wait64"(P %"iw_1.v197", W #3, W #0, P %"iw_1.v4", W %"iw_1.iw_3.v9");
    %"iw_1.v207" : W = (Cmp Eq W) %"iw_1.v202", #110
    => br %"iw_1.v207" ? "iw_1.L209" : "iw_1.L208" };
  ir_blk{ @"iw_1.L208":
    %"iw_1.v211" : W = (Cmp Eq W) %"iw_1.v202", #75
    => goto "iw_1.L209" };
  ir_blk{ @"iw_1.L209" [%"iw_1.v213" : W = phi("iw_1.L166" => #1, "iw_1.L208" => %"iw_1.v211")]:
    => br %"iw_1.v213" ? "iw_1.L203" : "iw_1.L205" };
  ir_blk{ @"iw_1.L203":
    => br %"iw_1.v68" ? "iw_1.L214" : "iw_1.join" };
  ir_blk{ @"iw_1.L214":
    %"iw_1.v220" = %"v0" +p #4;
    %"chk18" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v220";
    %"iw_1.v221" : W = (RawLoad (LdNarrow Uw) 0) %"chk18"
    => goto "iw_1.L222" };
  ir_blk{ @"iw_1.L222" [%"iw_1.pr.14" : W = phi("iw_1.L214" => %"iw_1.v221", "iw_1.L243" => %"iw_1.pr.15")]:
    %"iw_1.v226" = %"v0" +p #4;
    %"iw_1.v235" : W = (Cmp Eq W) %"iw_1.pr.14", #2147483649
    => br %"iw_1.v235" ? "iw_1.L229" : "iw_1.L228" };
  ir_blk{ @"iw_1.L228":
    %"iw_1.v237" : W = Sub %"iw_1.pr.14", #1
    => goto "iw_1.L229" };
  ir_blk{ @"iw_1.L229" [%"iw_1.v238" : W = phi("iw_1.L228" => %"iw_1.v237", "iw_1.L222" => #0)]:
    %"chk19" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"iw_1.v226";
    %"iw_1.v240" : W = (RawCas (CasNarrow Uw) 0) %"chk19", %"iw_1.pr.14", %"iw_1.v238";
    %"iw_1.v241" : W = (Cmp Eq W) %"iw_1.v240", %"iw_1.pr.14"
    => br %"iw_1.v241" ? "iw_1.L243" : "iw_1.L242" };
  ir_blk{ @"iw_1.L242":
    => goto "iw_1.L243" };
  ir_blk{ @"iw_1.L243" [%"iw_1.pr.15" : W = phi("iw_1.L229" => %"iw_1.pr.14", "iw_1.L242" => %"iw_1.v240")]:
    %"iw_1.v244" : W = (Cmp Ne W) %"iw_1.v240", %"iw_1.pr.14"
    => br %"iw_1.v244" ? poll "iw_1.L222" : "iw_1.L224" };
  ir_blk{ @"iw_1.L224":
    %"iw_1.v253" : W = (Cmp Eq W) %"iw_1.pr.15", #2147483649
    => br %"iw_1.v253" ? "iw_1.L245" : "iw_1.join" };
  ir_blk{ @"iw_1.L245":
    %"chk20" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"iw_1.v255" : W = (RawLoad (LdNarrow Uw) 0) %"chk20"
    => goto "iw_1.L86" };
  ir_blk{ @"iw_1.L205":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"iw_1.v260" : W = (RawLoad (LdNarrow Uw) 0) %"chk21"
    => goto poll "iw_1.L83" };
  ir_blk{ @"iw_1.L86" [%"iw_1.pr.13" : W = phi("iw_1.L137" => %"iw_1.v154", "iw_1.L245" => %"iw_1.v255", "iw_1.L112" => %"iw_1.pr.5", "iw_1.L93" => %"iw_1.pr.5"); %"iw_1.pr.4" : W = phi("iw_1.L137" => %"iw_1.pr.2", "iw_1.L245" => #1, "iw_1.L112" => %"iw_1.pr.2", "iw_1.L93" => %"iw_1.pr.2")]:
    %"iw_1.v262" : W = Or %"iw_1.pr.13", #2
    => goto "iw_1.L58" };
  ir_blk{ @"iw_1.L58" [%"iw_1.pr.10" : W = phi("iw_1.L86" => %"iw_1.v262", "iw_1.L51" => %"iw_1.v52"); %"iw_1.pr.1" : W = phi("iw_1.L86" => %"iw_1.pr.4", "iw_1.L51" => #0)]:
    %"iw_1.v267" = %"v0" +p #12
    => br %"iw_1.pr.1" ? "iw_1.L270" : "iw_1.L269" };
  ir_blk{ @"iw_1.L269":
    => goto "iw_1.L270" };
  ir_blk{ @"iw_1.L270" [%"iw_1.v272" : W = phi("iw_1.L269" => #0, "iw_1.L58" => #2)]:
    %"iw_1.v273" : W = Or %"iw_1.v272", #1;
    %"chk22" : A = (HalfCheck Lower 0 4 Write 1) %"chk1", %"iw_1.v267";
    store Ww [%"chk22" + 0] <- %"iw_1.v273";
    %"iw_1.v278" : W = And %"iw_1.pr.10", #1
    => br %"iw_1.v278" ? "iw_1.L512" : "iw_1.L282" };
  ir_blk{ @"iw_1.L282" [%"iw_1.pr.6" : W = phi("iw_1.L270" => %"iw_1.pr.10", "iw_1.L305" => %"iw_1.pr.7")]:
    %"iw_1.v286" : W = And %"iw_1.pr.6", #1
    => br %"iw_1.v286" ? "iw_1.L289" : "iw_1.L288" };
  ir_blk{ @"iw_1.L288":
    %"iw_1.v291" : W = Shr %"iw_1.pr.6", #3;
    %"iw_1.v292" : W = (Cmp Eq W) %"iw_1.v291", #0
    => goto "iw_1.L289" };
  ir_blk{ @"iw_1.L289" [%"iw_1.v294" : W = phi("iw_1.L282" => #0, "iw_1.L288" => %"iw_1.v292")]:
    => br %"iw_1.v294" ? "iw_1.L283" : "iw_1.L315" };
  ir_blk{ @"iw_1.L283":
    %"iw_1.v300" : W = Or %"iw_1.pr.6", #1;
    %"chk23" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v302" : W = (RawCas (CasNarrow Uw) 0) %"chk23", %"iw_1.pr.6", %"iw_1.v300";
    %"iw_1.v303" : W = (Cmp Eq W) %"iw_1.v302", %"iw_1.pr.6"
    => br %"iw_1.v303" ? "iw_1.L305" : "iw_1.L304" };
  ir_blk{ @"iw_1.L304":
    => goto "iw_1.L305" };
  ir_blk{ @"iw_1.L305" [%"iw_1.pr.7" : W = phi("iw_1.L283" => %"iw_1.pr.6", "iw_1.L304" => %"iw_1.v302")]:
    => br %"iw_1.v303" ? "iw_1.L306" : poll "iw_1.L282" };
  ir_blk{ @"iw_1.L306":
    %"iw_1.v310" = %"v0" +p #8;
    %"chk24" : A = (HalfCheck Lower 0 4 Write 1) %"chk1", %"iw_1.v310";
    store Ww [%"chk24" + 0] <- #1
    => goto "iw_1.L512" }] [ir_blk{ @"iw_1.L315" [%"iw_1.pr.16" : W = phi("iw_1.L289" => #0, "iw_1.L501" => #1, "iw_1.L505" => %"iw_1.pr.17")]:
    => goto "iw_1.L319" };
  ir_blk{ @"iw_1.L319":
    %"iw_1.v323" = %"v0" +p #8;
    %"chk25" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v323";
    %"iw_1.v324" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"iw_1.v325" : W = Or %"iw_1.v324", #2;
    %"iw_1.v326" : W = (Cmp Eq W) %"iw_1.v325", #2
    => br %"iw_1.v326" ? "iw_1.iw_4.start" : "iw_1.L321" };
  ir_blk{ @"iw_1.iw_4.start":
    %"iw_1.iw_4.v6" = %"v0" +p #28;
    %"chk26" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.iw_4.v6";
    %"iw_1.iw_4.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"iw_1.iw_4.v8" : W = (Cmp Ne W) %"iw_1.iw_4.v7", #0
    => br %"iw_1.iw_4.v8" ? "iw_1.iw_4.L4" : "iw_1.iw_4.L3" };
  ir_blk{ @"iw_1.iw_4.L3":
    => goto "iw_1.iw_4.L4" };
  ir_blk{ @"iw_1.iw_4.L4" [%"iw_1.iw_4.v9" : W = phi("iw_1.iw_4.L3" => #0, "iw_1.iw_4.start" => #128)]:
    %"iw_1.v334" : W = And %"iw_1.v324", #2;
    %"iw_1.v335" : W = (Cmp Eq W) %"iw_1.v334", #0
    => br %"iw_1.v335" ? "iw_1.L336" : "iw_1.L337" };
  ir_blk{ @"iw_1.L336":
    %"iw_1.v339" = %"v0" +p #8;
    %"chk27" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"iw_1.v339";
    %"iw_1.v341" : W = (RawCas (CasNarrow Uw) 0) %"chk27", %"iw_1.v324", #2;
    %"iw_1.v342" : W = (Cmp Eq W) %"iw_1.v341", %"iw_1.v324"
    => br %"iw_1.v342" ? "iw_1.L344" : "iw_1.L343" };
  ir_blk{ @"iw_1.L343":
    => goto "iw_1.L344" };
  ir_blk{ @"iw_1.L344":
    %"iw_1.v345" : W = (Cmp Ne W) %"iw_1.v341", %"iw_1.v324"
    => goto "iw_1.L337" };
  ir_blk{ @"iw_1.L337" [%"iw_1.v347" : W = phi("iw_1.iw_4.L4" => #0, "iw_1.L344" => %"iw_1.v345")]:
    => br %"iw_1.v347" ? poll "iw_1.L319" : "iw_1.L332" };
  ir_blk{ @"iw_1.L332":
    %"iw_1.v351" = %"v0" +p #8;
    call %"iw_1.v355" : W = $"__GI___futex_abstimed_wait64"(P %"iw_1.v351", W #2, W #0, P %"iw_1.v4", W %"iw_1.iw_4.v9");
    %"iw_1.v360" : W = (Cmp Eq W) %"iw_1.v355", #110
    => br %"iw_1.v360" ? "iw_1.L362" : "iw_1.L361" };
  ir_blk{ @"iw_1.L361":
    %"iw_1.v364" : W = (Cmp Eq W) %"iw_1.v355", #75
    => goto "iw_1.L362" };
  ir_blk{ @"iw_1.L362" [%"iw_1.v366" : W = phi("iw_1.L332" => #1, "iw_1.L361" => %"iw_1.v364")]:
    => br %"iw_1.v366" ? "iw_1.L356" : poll "iw_1.L319" };
  ir_blk{ @"iw_1.L356":
    %"iw_1.v371" = %"v0" +p #48;
    %"chk28" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.v371";
    %"iw_1.v372" : W = (RawLoad (LdNarrow Uw) 0) %"chk28";
    %"iw_1.v373" : W = (Cmp Ne W) %"iw_1.v372", #0
    => br %"iw_1.v373" ? "iw_1.L367" : "iw_1.L369" };
  ir_blk{ @"iw_1.L367":
    %"iw_1.v376" = %"v0" +p #4;
    %"chk29" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v376";
    %"iw_1.v377" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"iw_1.v382" : W = (Cmp Ne W) %"iw_1.v377", #0
    => br %"iw_1.v382" ? "iw_1.L378" : "iw_1.L369" };
  ir_blk{ @"iw_1.L378":
    %"iw_1.v385" = %"v0" +p #12;
    %"iw_1.v386" : W = (RawLoad (LdNarrow Uw) 8) %"chk29"
    => goto "iw_1.L387" };
  ir_blk{ @"iw_1.L387" [%"iw_1.v389" : W = phi("iw_1.L378" => %"iw_1.v386", "iw_1.L387" => %"iw_1.v390")]:
    %"chk31" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"iw_1.v385";
    %"iw_1.v390" : W = (RawCas (CasNarrow Uw) 0) %"chk31", %"iw_1.v389", #0;
    %"iw_1.v391" : W = (Cmp Eq W) %"iw_1.v390", %"iw_1.v389"
    => br %"iw_1.v391" ? "iw_1.L392" : poll "iw_1.L387" };
  ir_blk{ @"iw_1.L392" [%"iw_1.pr.19" : W = phi("iw_1.L387" => %"iw_1.v377", "iw_1.L411" => %"iw_1.pr.20")]:
    %"iw_1.v396" : W = (Cmp Ne W) %"iw_1.pr.19", #0
    => br %"iw_1.v396" ? "iw_1.L393" : "iw_1.L423" };
  ir_blk{ @"iw_1.L393":
    %"iw_1.v401" = %"v0" +p #4;
    %"iw_1.v406" : W = Or %"iw_1.pr.19", #2147483648;
    %"chk32" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"iw_1.v401";
    %"iw_1.v408" : W = (RawCas (CasNarrow Uw) 0) %"chk32", %"iw_1.pr.19", %"iw_1.v406";
    %"iw_1.v409" : W = (Cmp Eq W) %"iw_1.v408", %"iw_1.pr.19"
    => br %"iw_1.v409" ? "iw_1.L411" : "iw_1.L410" };
  ir_blk{ @"iw_1.L410":
    => goto "iw_1.L411" };
  ir_blk{ @"iw_1.L411" [%"iw_1.pr.20" : W = phi("iw_1.L393" => %"iw_1.pr.19", "iw_1.L410" => %"iw_1.v408")]:
    => br %"iw_1.v409" ? "iw_1.L397" : poll "iw_1.L392" };
  ir_blk{ @"iw_1.L397":
    %"iw_1.v416" : W = And %"iw_1.v389", #2;
    %"iw_1.v417" : W = (Cmp Ne W) %"iw_1.v416", #0
    => br %"iw_1.v417" ? "iw_1.L412" : "iw_1.join" };
  ir_blk{ @"iw_1.L412":
    %"iw_1.v419" = %"v0" +p #12;
    %"iw_1.iw_5.v16" : W = (Cmp Eq W) %"iw_1.iw_4.v9", #0
    => br %"iw_1.iw_5.v16" ? "iw_1.iw_5.L18" : "iw_1.iw_5.L17" };
  ir_blk{ @"iw_1.iw_5.L17":
    %"iw_1.iw_5.v20" : W = (Cmp Eq W) %"iw_1.iw_4.v9", #128
    => goto "iw_1.iw_5.L18" };
  ir_blk{ @"iw_1.iw_5.L18" [%"iw_1.iw_5.v22" : W = phi("iw_1.L412" => #1, "iw_1.iw_5.L17" => %"iw_1.iw_5.v20")]:
    => br %"iw_1.iw_5.v22" ? "iw_1.iw_5.L11" : "iw_1.iw_5.L14" };
  ir_blk{ @"iw_1.iw_5.L14":
    %"iw_1.iw_5.v24" : P = Copy $"glibc_pthread_rwlock_wrlock#str.286";
    %"iw_1.iw_5.v25" : P = Copy $"glibc_pthread_rwlock_wrlock#str.287";
    %"iw_1.iw_5.v26" : P = Copy $"glibc_pthread_rwlock_wrlock#str.288";
    %"iw_1.iw_5.v27" : P = Copy $"glibc_pthread_rwlock_wrlock#str.289";
    call void $"zerrorf"(P %"iw_1.iw_5.v24", P %"iw_1.iw_5.v25", W #173, P %"iw_1.iw_5.v26", P %"iw_1.iw_5.v27")
    => goto "iw_1.iw_5.L11" };
  ir_blk{ @"iw_1.iw_5.L11":
    => br %"iw_1.iw_5.v16" ? "iw_1.iw_5.L30" : "iw_1.iw_5.L29" };
  ir_blk{ @"iw_1.iw_5.L29":
    => goto "iw_1.iw_5.L30" };
  ir_blk{ @"iw_1.iw_5.L30" [%"iw_1.iw_5.v33" : W = phi("iw_1.iw_5.L29" => #0, "iw_1.iw_5.L11" => #1)]:
    call void $"zsys_futex_wake"(P %"iw_1.v419", W #1, W %"iw_1.iw_5.v33")
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L423":
    %"iw_1.v427" = %"v0" +p #12;
    %"chk33" : A = (Renew 0 4 Write 1) %"chk22", %"iw_1.v427";
    store Ww [%"chk33" + 0] <- %"iw_1.v389"
    => goto "iw_1.L369" };
  ir_blk{ @"iw_1.L369":
    %"chk34" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"iw_1.v430" : W = (RawLoad (LdNarrow Uw) 0) %"chk34";
    %"iw_1.v435" : W = And %"iw_1.v430", #1
    => br %"iw_1.v435" ? "iw_1.L489" : "iw_1.L431" };
  ir_blk{ @"iw_1.L431":
    %"iw_1.v439" = %"v0" +p #12;
    %"chk35" : A = (Renew 0 4 Read 1) %"chk22", %"iw_1.v439";
    %"iw_1.v440" : W = (RawLoad (LdNarrow Uw) 0) %"chk35"
    => goto "iw_1.L441" };
  ir_blk{ @"iw_1.L441" [%"iw_1.v443" : W = phi("iw_1.L431" => %"iw_1.v440", "iw_1.L441" => %"iw_1.v444")]:
    %"chk36" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"iw_1.v439";
    %"iw_1.v444" : W = (RawCas (CasNarrow Uw) 0) %"chk36", %"iw_1.v443", #0;
    %"iw_1.v445" : W = (Cmp Eq W) %"iw_1.v444", %"iw_1.v443"
    => br %"iw_1.v445" ? "iw_1.L446" : poll "iw_1.L441" };
  ir_blk{ @"iw_1.L446" [%"iw_1.pr.8" : W = phi("iw_1.L441" => %"iw_1.v430", "iw_1.L464" => %"iw_1.pr.9")]:
    %"iw_1.v450" : W = And %"iw_1.pr.8", #1
    => br %"iw_1.v450" ? "iw_1.L483" : "iw_1.L447" };
  ir_blk{ @"iw_1.L447":
    %"iw_1.v457" : W = Xor %"iw_1.pr.8", #2;
    %"iw_1.v459" : W = And %"iw_1.v457", #4294967291;
    %"chk37" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v461" : W = (RawCas (CasNarrow Uw) 0) %"chk37", %"iw_1.pr.8", %"iw_1.v459";
    %"iw_1.v462" : W = (Cmp Eq W) %"iw_1.v461", %"iw_1.pr.8"
    => br %"iw_1.v462" ? "iw_1.L464" : "iw_1.L463" };
  ir_blk{ @"iw_1.L463":
    => goto "iw_1.L464" };
  ir_blk{ @"iw_1.L464" [%"iw_1.pr.9" : W = phi("iw_1.L447" => %"iw_1.pr.8", "iw_1.L463" => %"iw_1.v461")]:
    => br %"iw_1.v462" ? "iw_1.L452" : poll "iw_1.L446" };
  ir_blk{ @"iw_1.L452":
    %"iw_1.v469" : W = And %"iw_1.v443", #2;
    %"iw_1.v470" : W = (Cmp Ne W) %"iw_1.v469", #0
    => br %"iw_1.v470" ? "iw_1.L465" : "iw_1.L467" };
  ir_blk{ @"iw_1.L465":
    %"iw_1.v472" = %"v0" +p #12;
    %"iw_1.iw_6.v16" : W = (Cmp Eq W) %"iw_1.iw_4.v9", #0
    => br %"iw_1.iw_6.v16" ? "iw_1.iw_6.L18" : "iw_1.iw_6.L17" };
  ir_blk{ @"iw_1.iw_6.L17":
    %"iw_1.iw_6.v20" : W = (Cmp Eq W) %"iw_1.iw_4.v9", #128
    => goto "iw_1.iw_6.L18" };
  ir_blk{ @"iw_1.iw_6.L18" [%"iw_1.iw_6.v22" : W = phi("iw_1.L465" => #1, "iw_1.iw_6.L17" => %"iw_1.iw_6.v20")]:
    => br %"iw_1.iw_6.v22" ? "iw_1.iw_6.L11" : "iw_1.iw_6.L14" };
  ir_blk{ @"iw_1.iw_6.L14":
    %"iw_1.iw_6.v24" : P = Copy $"glibc_pthread_rwlock_wrlock#str.286";
    %"iw_1.iw_6.v25" : P = Copy $"glibc_pthread_rwlock_wrlock#str.287";
    %"iw_1.iw_6.v26" : P = Copy $"glibc_pthread_rwlock_wrlock#str.288";
    %"iw_1.iw_6.v27" : P = Copy $"glibc_pthread_rwlock_wrlock#str.289";
    call void $"zerrorf"(P %"iw_1.iw_6.v24", P %"iw_1.iw_6.v25", W #173, P %"iw_1.iw_6.v26", P %"iw_1.iw_6.v27")
    => goto "iw_1.iw_6.L11" };
  ir_blk{ @"iw_1.iw_6.L11":
    => br %"iw_1.iw_6.v16" ? "iw_1.iw_6.L30" : "iw_1.iw_6.L29" };
  ir_blk{ @"iw_1.iw_6.L29":
    => goto "iw_1.iw_6.L30" };
  ir_blk{ @"iw_1.iw_6.L30" [%"iw_1.iw_6.v33" : W = phi("iw_1.iw_6.L29" => #0, "iw_1.iw_6.L11" => #1)]:
    call void $"zsys_futex_wake"(P %"iw_1.v472", W #1, W %"iw_1.iw_6.v33")
    => goto "iw_1.L467" };
  ir_blk{ @"iw_1.L467":
    %"iw_1.v478" : W = And %"iw_1.pr.9", #4;
    %"iw_1.v479" : W = (Cmp Ne W) %"iw_1.v478", #0
    => br %"iw_1.v479" ? "iw_1.iw_7.start" : "iw_1.join" };
  ir_blk{ @"iw_1.iw_7.start":
    %"iw_1.iw_7.v16" : W = (Cmp Eq W) %"iw_1.iw_4.v9", #0
    => br %"iw_1.iw_7.v16" ? "iw_1.iw_7.L18" : "iw_1.iw_7.L17" };
  ir_blk{ @"iw_1.iw_7.L17":
    %"iw_1.iw_7.v20" : W = (Cmp Eq W) %"iw_1.iw_4.v9", #128
    => goto "iw_1.iw_7.L18" };
  ir_blk{ @"iw_1.iw_7.L18" [%"iw_1.iw_7.v22" : W = phi("iw_1.iw_7.start" => #1, "iw_1.iw_7.L17" => %"iw_1.iw_7.v20")]:
    => br %"iw_1.iw_7.v22" ? "iw_1.iw_7.L11" : "iw_1.iw_7.L14" };
  ir_blk{ @"iw_1.iw_7.L14":
    %"iw_1.iw_7.v24" : P = Copy $"glibc_pthread_rwlock_wrlock#str.286";
    %"iw_1.iw_7.v25" : P = Copy $"glibc_pthread_rwlock_wrlock#str.287";
    %"iw_1.iw_7.v26" : P = Copy $"glibc_pthread_rwlock_wrlock#str.288";
    %"iw_1.iw_7.v27" : P = Copy $"glibc_pthread_rwlock_wrlock#str.289";
    call void $"zerrorf"(P %"iw_1.iw_7.v24", P %"iw_1.iw_7.v25", W #173, P %"iw_1.iw_7.v26", P %"iw_1.iw_7.v27")
    => goto "iw_1.iw_7.L11" };
  ir_blk{ @"iw_1.iw_7.L11":
    => br %"iw_1.iw_7.v16" ? "iw_1.iw_7.L30" : "iw_1.iw_7.L29" };
  ir_blk{ @"iw_1.iw_7.L29":
    => goto "iw_1.iw_7.L30" };
  ir_blk{ @"iw_1.iw_7.L30" [%"iw_1.iw_7.v33" : W = phi("iw_1.iw_7.L29" => #0, "iw_1.iw_7.L11" => #1)]:
    call void $"zsys_futex_wake"(P %"v0", W #2147483647, W %"iw_1.iw_7.v33")
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L483":
    %"iw_1.v487" = %"v0" +p #12;
    %"chk38" : A = (Renew 0 4 Write 1) %"chk22", %"iw_1.v487";
    store Ww [%"chk38" + 0] <- %"iw_1.v443"
    => goto "iw_1.L489" };
  ir_blk{ @"iw_1.L489":
    %"iw_1.v493" = %"v0" +p #8;
    %"chk39" : A = (Renew 0 4 Read 1) %"chk25", %"iw_1.v493";
    %"iw_1.v494" : W = (RawLoad (LdNarrow Uw) 0) %"chk39";
    %"iw_1.v495" : W = Or %"iw_1.v494", #2;
    %"iw_1.v496" : W = (Cmp Eq W) %"iw_1.v495", #2
    => br %"iw_1.v496" ? poll "iw_1.L489" : "iw_1.L321" };
  ir_blk{ @"iw_1.L321" [%"iw_1.pr.17" : W = phi("iw_1.L319" => %"iw_1.pr.16", "iw_1.L489" => #1)]:
    %"iw_1.v502" : W = (Ext Ub) %"iw_1.pr.17"
    => br %"iw_1.v502" ? "iw_1.L512" : "iw_1.L501" };
  ir_blk{ @"iw_1.L501":
    %"chk40" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"iw_1.v508" : W = (RawLoad (LdNarrow Uw) 0) %"chk40";
    %"iw_1.v509" : W = And %"iw_1.v508", #1
    => br %"iw_1.v509" ? poll "iw_1.L315" : "iw_1.L505" };
  ir_blk{ @"iw_1.L505":
    => goto poll "iw_1.L315" };
  ir_blk{ @"iw_1.L512":
    %"iw_1.v516" = %"v0" +p #24;
    call %"iw_1.v517" : P = $"zthread_self_cookie"();
    %"iw_1.v518" = %"iw_1.v517" +p #720;
    %"chk41" : A = (Check 0 4 Read 1) %"iw_1.v518";
    %"iw_1.v519" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"chk42" : A = (Renew 0 4 Write 1) %"chk1", %"iw_1.v516";
    store Ww [%"chk42" + 0] <- %"iw_1.v519"
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join" [%"v7" : W = phi("iw_1.L512" => #0, "iw_1.L13" => #22, "iw_1.L8" => #35, "iw_1.L203" => %"iw_1.v202", "iw_1.L224" => %"iw_1.v202", "iw_1.L397" => %"iw_1.v355", "iw_1.iw_5.L30" => %"iw_1.v355", "iw_1.L467" => #110, "iw_1.iw_7.L30" => #110)]:
    => ret %"v7" }])) }.

Definition item_glibc_pthread_rwlock_wrlock'23str'2e286 : item :=
  (IData (a "glibc_pthread_rwlock_wrlock#str.286") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition item_glibc_pthread_rwlock_wrlock'23str'2e287 : item :=
  (IData (a "glibc_pthread_rwlock_wrlock#str.287") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 110); (Item Wb 112); (Item Wb 116); (Item Wb 108); (Item Wb 47); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition item_glibc_pthread_rwlock_wrlock'23str'2e288 : item :=
  (IData (a "glibc_pthread_rwlock_wrlock#str.288") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 107); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_pthread_rwlock_wrlock'23str'2e289 : item :=
  (IData (a "glibc_pthread_rwlock_wrlock#str.289") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).
