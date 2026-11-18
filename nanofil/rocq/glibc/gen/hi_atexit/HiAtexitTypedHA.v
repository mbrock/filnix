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

Definition hi_fn_glibc_libc_start'23handle_intel : func :=
  ir_fn{ "local" "glibc_libc_start#handle_intel"(W %"v0", P %"v2", P %"v4") -> (RClass L) {
  @"start":
    %"v19" : P = (Alloc 4) #1;
    %"v21" : P = (Alloc 4) #1;
    %"v8" = %"v2" +p #4;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v14" : W = (Cmp Ult W) %"v9", #2
    => br %"v14" ? "L10" : "L12";
  @"L10":
    => ret #18446744073709551615;
  @"L12":
    %"chk1" : A = (Check 0 1 Write 1) %"v19";
    store Wb [%"chk1" + 0] <- #0;
    %"chk2" : A = (Check 0 1 Write 1) %"v21";
    store Wb [%"chk2" + 0] <- #0;
    %"chk3" : A = (Check 0 1 Read 1) %"v4";
    %"v28" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"v29" : W = (Cmp Eq W) %"v28", #0
    => br %"v29" ? "L24" : "L26";
  @"L24":
    %"v31" = %"v4" +p #4;
    %"v35" = %"v31" +p #4;
    %"v38" = %"v31" +p #8;
    %"v41" = %"v31" +p #12;
    call void $"zcpuid"(W #2, P %"v31", P %"v35", P %"v38", P %"v41");
    %"chk4" : A = (Renew 0 1 Write 1) %"chk3", %"v4";
    store Wb [%"chk4" + 0] <- #1
    => goto "L26";
  @"L26":
    %"v47" = %"v4" +p #4;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v47";
    %"v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v50" : W = And %"v49", #255;
    %"v51" : W = (Cmp Ne W) %"v50", #1
    => br %"v51" ? "L43" : "L45";
  @"L43":
    call %"v55" : L = $"glibc_libc_start#intel_check_word"(W %"v0", W #255, P %"v21", P %"v19", P %"v2", P %"v4")
    => ret %"v55";
  @"L45":
    %"v59" = %"v4" +p #4;
    %"v61" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v62" : W = And %"v61", #4294967040;
    call %"v65" : L = $"glibc_libc_start#intel_check_word"(W %"v0", W %"v62", P %"v21", P %"v19", P %"v2", P %"v4");
    %"v70" : W = (Cmp Ne L) %"v65", #0
    => br %"v70" ? "L66" : "L73";
  @"L66":
    => ret %"v65";
  @"L73" [%"pr.1" : W = phi("L75" => %"v98", "L45" => #1)]:
    %"v78" : W = (Cmp Slt W) %"pr.1", #4
    => br %"v78" ? "L74" : "L76";
  @"L74":
    %"v81" = %"v4" +p #4;
    %"v83" : L = (Ext Sw) %"pr.1";
    %"v84" : L = Shl %"v83", #2;
    %"v85" = %"v81" +p %"v84";
    %"chk7" : A = (Check 0 4 Read 1) %"v85";
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    call %"v89" : L = $"glibc_libc_start#intel_check_word"(W %"v0", W %"v86", P %"v21", P %"v19", P %"v2", P %"v4");
    %"v94" : W = (Cmp Ne L) %"v89", #0
    => br %"v94" ? "L90" : "L75";
  @"L90":
    => ret %"v89";
  @"L75":
    %"v98" : W = Add %"pr.1", #1
    => goto poll "L73";
  @"L76":
    %"v103" : W = (Cmp Sge W) %"v0", #191
    => br %"v103" ? "L104" : "L105";
  @"L104":
    %"v107" : W = (Cmp Sle W) %"v0", #196
    => goto "L105";
  @"L105" [%"v109" : W = phi("L76" => #0, "L104" => %"v107")]:
    => br %"v109" ? "L110" : "L111";
  @"L110":
    %"chk8" : A = (Renew 0 1 Read 1) %"chk1", %"v19";
    %"v112" : W = (RawLoad (LdNarrow Ub) 0) %"chk8";
    %"v113" : W = (Cmp Ne W) %"v112", #0
    => goto "L111";
  @"L111" [%"v114" : W = phi("L105" => #0, "L110" => %"v113")]:
    => br %"v114" ? "L99" : "L101";
  @"L99":
    => ret #18446744073709551615;
  @"L101":
    => ret #0
} }.

Definition hi_fn_glibc_libc_start'23handle_amd : func :=
  ir_fn{ "local" "glibc_libc_start#handle_amd"(W %"v0") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v2" : P = (Alloc 4) #4;
    %"v3" : P = (Alloc 4) #4;
    %"v4" : P = (Alloc 4) #4;
    %"v5" : P = (Alloc 4) #4;
    %"v6" : P = (Alloc 4) #4;
    %"chk0" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk0" + 0] <- #0;
    %"chk1" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk1" + 0] <- #0;
    %"v12" : W = (Cmp Sgt W) %"v0", #196
    => br %"v12" ? "L8" : "L10" };
  ir_blk{ @"L8":
    => ret #0 };
  ir_blk{ @"L10":
    call void $"zcpuid"(W #2147483648, P %"v6", P %"v3", P %"v4", P %"v5");
    %"chk2" : A = (Renew 0 4 Read 1) %"chk1", %"v6";
    %"v17" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v18" : W = (Cmp Uge W) %"v17", #2147483677
    => br %"v18" ? "L14" : "L16" };
  ir_blk{ @"L14":
    %"v24" : W = (Cmp Sge W) %"v0", #194
    => br %"v24" ? "L22" : "L21" };
  ir_blk{ @"L21":
    %"v29" : W = (Cmp Sge W) %"v0", #191
    => br %"v29" ? "L22" : "L26" };
  ir_blk{ @"L26":
    %"v34" : W = (Cmp Sge W) %"v0", #188
    => br %"v34" ? "L22" : "L31" };
  ir_blk{ @"L31":
    => goto "L22" };
  ir_blk{ @"L22" [%"pr.2" : W = phi("L14" => #3, "L21" => #2, "L31" => #1, "L26" => #0)]:
    call void $"zcpuid_count"(W #2147483677, W %"pr.2", P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk3" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v39" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v40" : W = (Cmp Ne W) %"v39", #0
    => br %"v40" ? "L42" : "L16" };
  ir_blk{ @"L47":
    %"chk4" : A = (Check 0 4 Read 1) %"v3";
    %"v48" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v49" : W = Shr %"v48", #22;
    %"v50" : W = And %"v49", #1023;
    %"v51" : W = Add %"v50", #1;
    %"v52" : L = (Ext Uw) %"v51"
    => ret %"v52" };
  ir_blk{ @"L56":
    %"chk5" : A = (Check 0 4 Read 1) %"v3";
    %"v57" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v58" : W = And %"v57", #4095;
    %"v59" : W = Add %"v58", #1;
    %"v60" : L = (Ext Uw) %"v59"
    => ret %"v60" };
  ir_blk{ @"L64":
    %"chk6" : A = (Check 0 4 Read 1) %"v3";
    %"v65" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v66" : W = Shr %"v65", #22;
    %"v67" : W = And %"v66", #1023;
    %"v68" : W = Add %"v67", #1;
    %"v69" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v70" : W = And %"v69", #4095;
    %"v71" : W = Add %"v70", #1;
    %"v72" : W = Mul %"v68", %"v71";
    %"chk8" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v73" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v74" : W = Add %"v73", #1;
    %"v75" : W = Mul %"v72", %"v74";
    %"v76" : L = (Ext Uw) %"v75"
    => ret %"v76" };
  ir_blk{ @"L77":
    => unreachable };
  ir_blk{ @"L42":
    %"v79" : W = (Cmp Slt W) %"v0", #191
    => br %"v79" ? "L80" : "L81" };
  ir_blk{ @"L80":
    %"v82" : W = (Cmp Slt W) %"v0", #188
    => br %"v82" ? "L83" : "L84" };
  ir_blk{ @"L83":
    %"v85" : W = (Cmp Eq W) %"v0", #185
    => br %"v85" ? poll "L64" : "L86" };
  ir_blk{ @"L86":
    %"v87" : W = (Cmp Eq W) %"v0", #186
    => br %"v87" ? poll "L47" : "L88" };
  ir_blk{ @"L88":
    %"v89" : W = (Cmp Eq W) %"v0", #187
    => br %"v89" ? poll "L56" : poll "L77" };
  ir_blk{ @"L84":
    %"v91" : W = (Cmp Eq W) %"v0", #188
    => br %"v91" ? poll "L64" : "L92" };
  ir_blk{ @"L92":
    %"v93" : W = (Cmp Eq W) %"v0", #189
    => br %"v93" ? poll "L47" : "L94" };
  ir_blk{ @"L94":
    %"v95" : W = (Cmp Eq W) %"v0", #190
    => br %"v95" ? poll "L56" : poll "L77" };
  ir_blk{ @"L81":
    %"v97" : W = (Cmp Slt W) %"v0", #194
    => br %"v97" ? "L98" : "L99" };
  ir_blk{ @"L98":
    %"v100" : W = (Cmp Eq W) %"v0", #191
    => br %"v100" ? poll "L64" : "L101" };
  ir_blk{ @"L101":
    %"v102" : W = (Cmp Eq W) %"v0", #192
    => br %"v102" ? poll "L47" : "L103" };
  ir_blk{ @"L103":
    %"v104" : W = (Cmp Eq W) %"v0", #193
    => br %"v104" ? poll "L56" : poll "L77" };
  ir_blk{ @"L99":
    %"v106" : W = (Cmp Eq W) %"v0", #194
    => br %"v106" ? poll "L64" : "L107" };
  ir_blk{ @"L107":
    %"v108" : W = (Cmp Eq W) %"v0", #195
    => br %"v108" ? poll "L47" : "L109" };
  ir_blk{ @"L109":
    %"v110" : W = (Cmp Eq W) %"v0", #196
    => br %"v110" ? poll "L56" : poll "L77" };
  ir_blk{ @"L16":
    %"v116" : W = (Cmp Sge W) %"v0", #191;
    %"v117" : W = Add %"v116", #2147483653;
    %"chk9" : A = (Renew 0 4 Read 1) %"chk1", %"v6";
    %"v121" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"v123" : W = (Cmp Ult W) %"v121", %"v117"
    => br %"v123" ? "L118" : "L120" };
  ir_blk{ @"L118":
    => ret #0 };
  ir_blk{ @"L120":
    call void $"zcpuid"(W %"v117", P %"v2", P %"v3", P %"v4", P %"v5");
    %"v130" : W = (Cmp Slt W) %"v0", #188
    => br %"v130" ? "L126" : "L128" };
  ir_blk{ @"L126":
    %"v133" : W = Add %"v0", #3;
    %"chk10" : A = (Check 0 4 Read 1) %"v5";
    %"v134" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"chk11" : A = (Renew 0 4 Write 1) %"chk0", %"v4";
    store Ww [%"chk11" + 0] <- %"v134"
    => goto "L128" };
  ir_blk{ @"L128" [%"pr.1" : W = phi("L126" => %"v133", "L120" => %"v0")]:
    %"v397" : W = (Cmp Slt W) %"pr.1", #192
    => br %"v397" ? "L398" : "L399" };
  ir_blk{ @"L138":
    %"chk12" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v139" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"v140" : W = Shr %"v139", #14;
    %"v141" : W = And %"v140", #261120;
    %"v142" : L = (Ext Uw) %"v141"
    => ret %"v142" };
  ir_blk{ @"L143":
    %"chk13" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v144" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"v145" : W = Shr %"v144", #16;
    %"chk14" : A = (Renew 0 4 Write 1) %"chk0", %"v4";
    store Ww [%"chk14" + 0] <- %"v145";
    %"v149" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"v150" : W = And %"v149", #255;
    %"v151" : W = (Cmp Eq W) %"v150", #255
    => br %"v151" ? "L146" : "L148" };
  ir_blk{ @"L146":
    %"v152" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"v153" : W = Shl %"v152", #2;
    %"v154" : W = And %"v153", #261120;
    %"v155" : L = (Ext Uw) %"v154"
    => ret %"v155" };
  ir_blk{ @"L148":
    %"v157" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"v158" : W = And %"v157", #255;
    %"v159" : L = (Ext Uw) %"v158"
    => ret %"v159" };
  ir_blk{ @"L160":
    %"chk18" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v161" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v162" : W = And %"v161", #255;
    %"v163" : L = (Ext Uw) %"v162"
    => ret %"v163" };
  ir_blk{ @"L164":
    %"chk19" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v168" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v169" : W = And %"v168", #61440;
    %"v170" : W = (Cmp Eq W) %"v169", #0
    => br %"v170" ? "L167" : "L166" };
  ir_blk{ @"L166":
    %"v171" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v172" : W = Shr %"v171", #6;
    %"v173" : W = And %"v172", #67107840
    => goto "L167" };
  ir_blk{ @"L167" [%"v174" : W = phi("L166" => %"v173", "L164" => #0)]:
    %"v175" : L = (Ext Uw) %"v174"
    => ret %"v175" };
  ir_blk{ @"L176":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v177" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v178" : W = Shr %"v177", #12;
    %"v179" : W = And %"v178", #15;
    %"v207" : W = (Cmp Ult W) %"v179", #10
    => br %"v207" ? "L208" : "L209" };
  ir_blk{ @"L185":
    %"chk22" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v186" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v187" : W = Shr %"v186", #12;
    %"v188" : W = And %"v187", #15;
    %"v189" : L = (Ext Uw) %"v188"
    => ret %"v189" };
  ir_blk{ @"L190":
    => ret #8 };
  ir_blk{ @"L191":
    => ret #16 };
  ir_blk{ @"L192":
    => ret #32 };
  ir_blk{ @"L193":
    => ret #48 };
  ir_blk{ @"L194":
    => ret #64 };
  ir_blk{ @"L195":
    => ret #96 };
  ir_blk{ @"L196":
    => ret #128 };
  ir_blk{ @"L197":
    %"chk23" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v198" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v199" : W = Shr %"v198", #6;
    %"v200" : W = And %"v199", #67107840;
    %"v201" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v202" : W = And %"v201", #255;
    %"v203" : W = Udiv %"v200", %"v202";
    %"v204" : L = (Ext Uw) %"v203"
    => ret %"v204" };
  ir_blk{ @"L205":
    => ret #0 };
  ir_blk{ @"L208":
    %"v210" : W = (Cmp Ult W) %"v179", #4
    => br %"v210" ? "L211" : "L212" };
  ir_blk{ @"L211":
    %"v213" : W = (Cmp Eq W) %"v179", #0
    => br %"v213" ? poll "L185" : "L214" };
  ir_blk{ @"L214":
    %"v215" : W = (Cmp Eq W) %"v179", #1
    => br %"v215" ? poll "L185" : "L216" };
  ir_blk{ @"L216":
    %"v217" : W = (Cmp Eq W) %"v179", #2
    => br %"v217" ? poll "L185" : poll "L205" };
  ir_blk{ @"L212":
    %"v219" : W = (Cmp Eq W) %"v179", #4
    => br %"v219" ? poll "L185" : "L220" };
  ir_blk{ @"L220":
    %"v221" : W = (Cmp Eq W) %"v179", #6
    => br %"v221" ? poll "L190" : "L222" };
  ir_blk{ @"L222":
    %"v223" : W = (Cmp Eq W) %"v179", #8
    => br %"v223" ? poll "L191" : poll "L205" };
  ir_blk{ @"L209":
    %"v225" : W = (Cmp Ult W) %"v179", #13
    => br %"v225" ? "L226" : "L227" }] [ir_blk{ @"L226":
    %"v228" : W = (Cmp Eq W) %"v179", #10
    => br %"v228" ? poll "L192" : "L229" };
  ir_blk{ @"L229":
    %"v230" : W = (Cmp Eq W) %"v179", #11
    => br %"v230" ? poll "L193" : "L231" };
  ir_blk{ @"L231":
    %"v232" : W = (Cmp Eq W) %"v179", #12
    => br %"v232" ? poll "L194" : poll "L205" };
  ir_blk{ @"L227":
    %"v234" : W = (Cmp Eq W) %"v179", #13
    => br %"v234" ? poll "L195" : "L235" };
  ir_blk{ @"L235":
    %"v236" : W = (Cmp Eq W) %"v179", #14
    => br %"v236" ? poll "L196" : "L237" };
  ir_blk{ @"L237":
    %"v238" : W = (Cmp Eq W) %"v179", #15
    => br %"v238" ? poll "L197" : poll "L205" };
  ir_blk{ @"L240":
    %"chk25" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v244" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"v245" : W = And %"v244", #61440;
    %"v246" : W = (Cmp Eq W) %"v245", #0
    => br %"v246" ? "L243" : "L242" };
  ir_blk{ @"L242":
    %"v247" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"v248" : W = And %"v247", #255
    => goto "L243" };
  ir_blk{ @"L243" [%"v249" : W = phi("L242" => %"v248", "L240" => #0)]:
    %"v250" : L = (Ext Uw) %"v249"
    => ret %"v250" };
  ir_blk{ @"L251":
    %"chk27" : A = (Check 0 4 Read 1) %"v5";
    %"v259" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v260" : W = And %"v259", #61440;
    %"v261" : W = (Cmp Eq W) %"v260", #0
    => br %"v261" ? "L256" : "L258" };
  ir_blk{ @"L256":
    => ret #0 };
  ir_blk{ @"L258":
    %"v263" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v264" : W = And %"v263", #1073479680;
    %"v265" : W = Shl %"v264", #1;
    %"v266" : L = (Ext Uw) %"v265";
    %"v267" : P = Copy $"_dl_x86_cpu_features";
    %"chk29" : A = (Renew 0 4 Read 1) %"chk1", %"v6";
    %"v271" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v272" : W = (Cmp Uge W) %"v271", #2147483656
    => br %"v272" ? "L268" : "L270" };
  ir_blk{ @"L268":
    call void $"zcpuid"(W #2147483656, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk30" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v273" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v274" : W = And %"v273", #255;
    %"v275" : W = Add %"v274", #1
    => goto "L270" };
  ir_blk{ @"L270" [%"pr.6" : W = phi("L268" => %"v275", "L258" => #0)]:
    %"v280" : W = (Cmp Eq W) %"pr.6", #0
    => br %"v280" ? "L276" : "L278" };
  ir_blk{ @"L276":
    call void $"zcpuid"(W #1, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk31" : A = (Renew 0 4 Read 1) %"chk27", %"v5";
    %"v284" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v286" : W = And %"v284", #268435456;
    %"v287" : W = (Cmp Ne W) %"v286", #0
    => br %"v287" ? "L281" : "L278" };
  ir_blk{ @"L281":
    %"chk32" : A = (Check 0 4 Read 1) %"v3";
    %"v288" : W = (RawLoad (LdNarrow Uw) 0) %"chk32";
    %"v289" : W = Shr %"v288", #16;
    %"v290" : W = And %"v289", #255
    => goto "L278" };
  ir_blk{ @"L278" [%"pr.7" : W = phi("L281" => %"v290", "L276" => %"pr.6", "L270" => %"pr.6")]:
    %"v295" : W = (Cmp Ugt W) %"pr.7", #0
    => br %"v295" ? "L291" : "L293" };
  ir_blk{ @"L291":
    %"v298" : L = (Ext Uw) %"pr.7";
    %"v299" : L = Div %"v266", %"v298"
    => goto "L293" };
  ir_blk{ @"L293" [%"pr.5" : L = phi("L291" => %"v299", "L278" => #0)]:
    %"v304" = %"v267" +p #8;
    %"chk33" : A = (Check 0 4 Read 1) %"v304";
    %"v305" : W = (RawLoad (LdNarrow Uw) 0) %"chk33";
    %"v306" : W = (Cmp Uge W) %"v305", #23
    => br %"v306" ? "L300" : "L301" };
  ir_blk{ @"L300":
    call void $"zcpuid_count"(W #2147483677, W #3, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk34" : A = (Check 0 4 Read 1) %"v2";
    %"v309" : W = (RawLoad (LdNarrow Uw) 0) %"chk34";
    %"v310" : W = Shr %"v309", #14;
    %"v311" : W = And %"v310", #4095;
    %"v312" : W = Add %"v311", #1;
    %"v315" : L = (Ext Uw) %"v312";
    %"v316" : L = Mul %"pr.5", %"v315"
    => ret %"v316" };
  ir_blk{ @"L301":
    => ret %"pr.5" };
  ir_blk{ @"L320":
    %"chk35" : A = (Check 0 4 Read 1) %"v5";
    %"v321" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v322" : W = Shr %"v321", #12;
    %"v323" : W = And %"v322", #15;
    %"v351" : W = (Cmp Ult W) %"v323", #10
    => br %"v351" ? "L352" : "L353" };
  ir_blk{ @"L329":
    %"chk36" : A = (Renew 0 4 Read 1) %"chk35", %"v5";
    %"v330" : W = (RawLoad (LdNarrow Uw) 0) %"chk36";
    %"v331" : W = Shr %"v330", #12;
    %"v332" : W = And %"v331", #15;
    %"v333" : L = (Ext Uw) %"v332"
    => ret %"v333" };
  ir_blk{ @"L334":
    => ret #8 };
  ir_blk{ @"L335":
    => ret #16 };
  ir_blk{ @"L336":
    => ret #32 };
  ir_blk{ @"L337":
    => ret #48 };
  ir_blk{ @"L338":
    => ret #64 };
  ir_blk{ @"L339":
    => ret #96 };
  ir_blk{ @"L340":
    => ret #128 };
  ir_blk{ @"L341":
    %"chk37" : A = (Renew 0 4 Read 1) %"chk35", %"v5";
    %"v342" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v343" : W = And %"v342", #1073479680;
    %"v344" : W = Shl %"v343", #1;
    %"v345" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v346" : W = And %"v345", #255;
    %"v347" : W = Udiv %"v344", %"v346";
    %"v348" : L = (Ext Uw) %"v347"
    => ret %"v348" };
  ir_blk{ @"L349":
    => ret #0 };
  ir_blk{ @"L352":
    %"v354" : W = (Cmp Ult W) %"v323", #4
    => br %"v354" ? "L355" : "L356" };
  ir_blk{ @"L355":
    %"v357" : W = (Cmp Eq W) %"v323", #0
    => br %"v357" ? poll "L329" : "L358" };
  ir_blk{ @"L358":
    %"v359" : W = (Cmp Eq W) %"v323", #1
    => br %"v359" ? poll "L329" : "L360" };
  ir_blk{ @"L360":
    %"v361" : W = (Cmp Eq W) %"v323", #2
    => br %"v361" ? poll "L329" : poll "L349" };
  ir_blk{ @"L356":
    %"v363" : W = (Cmp Eq W) %"v323", #4
    => br %"v363" ? poll "L329" : "L364" };
  ir_blk{ @"L364":
    %"v365" : W = (Cmp Eq W) %"v323", #6
    => br %"v365" ? poll "L334" : "L366" };
  ir_blk{ @"L366":
    %"v367" : W = (Cmp Eq W) %"v323", #8
    => br %"v367" ? poll "L335" : poll "L349" };
  ir_blk{ @"L353":
    %"v369" : W = (Cmp Ult W) %"v323", #13
    => br %"v369" ? "L370" : "L371" };
  ir_blk{ @"L370":
    %"v372" : W = (Cmp Eq W) %"v323", #10
    => br %"v372" ? poll "L336" : "L373" };
  ir_blk{ @"L373":
    %"v374" : W = (Cmp Eq W) %"v323", #11
    => br %"v374" ? poll "L337" : "L375" };
  ir_blk{ @"L375":
    %"v376" : W = (Cmp Eq W) %"v323", #12
    => br %"v376" ? poll "L338" : poll "L349" };
  ir_blk{ @"L371":
    %"v378" : W = (Cmp Eq W) %"v323", #13
    => br %"v378" ? poll "L339" : "L379" };
  ir_blk{ @"L379":
    %"v380" : W = (Cmp Eq W) %"v323", #14
    => br %"v380" ? poll "L340" : "L381" };
  ir_blk{ @"L381":
    %"v382" : W = (Cmp Eq W) %"v323", #15
    => br %"v382" ? poll "L341" : poll "L349" };
  ir_blk{ @"L384":
    %"chk39" : A = (Check 0 4 Read 1) %"v5";
    %"v388" : W = (RawLoad (LdNarrow Uw) 0) %"chk39";
    %"v389" : W = And %"v388", #61440;
    %"v390" : W = (Cmp Eq W) %"v389", #0
    => br %"v390" ? "L387" : "L386" };
  ir_blk{ @"L386":
    %"v391" : W = (RawLoad (LdNarrow Uw) 0) %"chk39";
    %"v392" : W = And %"v391", #255
    => goto "L387" };
  ir_blk{ @"L387" [%"v393" : W = phi("L386" => %"v392", "L384" => #0)]:
    %"v394" : L = (Ext Uw) %"v393"
    => ret %"v394" };
  ir_blk{ @"L395":
    => unreachable };
  ir_blk{ @"L398":
    %"v400" : W = (Cmp Eq W) %"pr.1", #188
    => br %"v400" ? poll "L138" : "L401" };
  ir_blk{ @"L401":
    %"v402" : W = (Cmp Eq W) %"pr.1", #189
    => br %"v402" ? poll "L143" : "L403" };
  ir_blk{ @"L403":
    %"v404" : W = (Cmp Eq W) %"pr.1", #190
    => br %"v404" ? poll "L160" : "L405" };
  ir_blk{ @"L405":
    %"v406" : W = (Cmp Eq W) %"pr.1", #191
    => br %"v406" ? poll "L164" : poll "L395" };
  ir_blk{ @"L399":
    %"v408" : W = (Cmp Slt W) %"pr.1", #194
    => br %"v408" ? "L409" : "L410" };
  ir_blk{ @"L409":
    %"v411" : W = (Cmp Eq W) %"pr.1", #192
    => br %"v411" ? poll "L176" : "L412" };
  ir_blk{ @"L412":
    %"v413" : W = (Cmp Eq W) %"pr.1", #193
    => br %"v413" ? poll "L240" : poll "L395" };
  ir_blk{ @"L410":
    %"v415" : W = (Cmp Eq W) %"pr.1", #194
    => br %"v415" ? poll "L251" : "L416" };
  ir_blk{ @"L416":
    %"v417" : W = (Cmp Eq W) %"pr.1", #195
    => br %"v417" ? poll "L320" : "L418" };
  ir_blk{ @"L418":
    %"v419" : W = (Cmp Eq W) %"pr.1", #196
    => br %"v419" ? poll "L384" : poll "L395" }])) }.

Definition hi_fn_glibc_libc_start'23handle_zhaoxin : func :=
  ir_fn{ "local" "glibc_libc_start#handle_zhaoxin"(W %"v0") -> (RClass L) {
  @"start":
    %"v2" : P = (Alloc 4) #4;
    %"v3" : P = (Alloc 4) #4;
    %"v4" : P = (Alloc 4) #4;
    %"v5" : P = (Alloc 4) #4;
    %"v8" : W = Sub %"v0", #185;
    %"v9" : W = Div %"v8", #3;
    %"v10" : W = Mul %"v9", #3
    => goto "L12";
  @"L12" [%"pr.1" : W = phi("L31" => %"v143", "start" => #0)]:
    call void $"zcpuid_count"(W #4, W %"pr.1", P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk0" : A = (Check 0 4 Read 1) %"v2";
    %"v17" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v18" : W = And %"v17", #31;
    %"v23" : W = (Cmp Eq W) %"v18", #0
    => br %"v23" ? "L14" : "L21";
  @"L21":
    %"v26" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v27" : W = Shr %"v26", #5;
    %"v28" : W = And %"v27", #7;
    %"v33" : W = (Cmp Eq W) %"v28", #1
    => br %"v33" ? "L34" : "L35";
  @"L34":
    %"v37" : W = (Cmp Eq W) %"v18", #1
    => goto "L35";
  @"L35" [%"v39" : W = phi("L21" => #0, "L34" => %"v37")]:
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v44" : W = (Cmp Eq W) %"v10", #3
    => goto "L41";
  @"L41" [%"v46" : W = phi("L35" => #0, "L40" => %"v44")]:
    => br %"v46" ? "L48" : "L47";
  @"L47":
    => br %"v33" ? "L51" : "L52";
  @"L51":
    %"v54" : W = (Cmp Eq W) %"v18", #2
    => goto "L52";
  @"L52" [%"v56" : W = phi("L47" => #0, "L51" => %"v54")]:
    => br %"v56" ? "L57" : "L48";
  @"L57":
    %"v61" : W = (Cmp Eq W) %"v10", #0
    => goto "L48";
  @"L48" [%"v65" : W = phi("L41" => #1, "L52" => #0, "L57" => %"v61")]:
    => br %"v65" ? "L67" : "L66";
  @"L66":
    %"v69" : W = (Cmp Eq W) %"v28", #2
    => br %"v69" ? "L70" : "L67";
  @"L70":
    %"v74" : W = (Cmp Eq W) %"v10", #6
    => goto "L67";
  @"L67" [%"v78" : W = phi("L48" => #1, "L66" => #0, "L70" => %"v74")]:
    => br %"v78" ? "L80" : "L79";
  @"L79":
    %"v82" : W = (Cmp Eq W) %"v28", #3
    => br %"v82" ? "L83" : "L80";
  @"L83":
    %"v87" : W = (Cmp Eq W) %"v10", #9
    => goto "L80";
  @"L80" [%"v91" : W = phi("L67" => #1, "L79" => #0, "L83" => %"v87")]:
    => br %"v91" ? "L29" : "L31";
  @"L29":
    %"v96" : W = Sub %"v8", %"v10";
    %"v101" : W = (Cmp Eq W) %"v96", #0
    => br %"v101" ? "L97" : "L99";
  @"L97":
    %"chk2" : A = (Check 0 4 Read 1) %"v3";
    %"v102" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v103" : W = Shr %"v102", #22;
    %"v104" : W = Add %"v103", #1;
    %"v105" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v106" : W = Shr %"v105", #12;
    %"v107" : W = And %"v106", #1023;
    %"v108" : W = Add %"v107", #1;
    %"v109" : W = Mul %"v104", %"v108";
    %"v110" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v111" : W = And %"v110", #4095;
    %"v112" : W = Add %"v111", #1;
    %"v113" : W = Mul %"v109", %"v112";
    %"chk5" : A = (Check 0 4 Read 1) %"v4";
    %"v114" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v115" : W = Add %"v114", #1;
    %"v116" : W = Mul %"v113", %"v115";
    %"v117" : L = (Ext Uw) %"v116"
    => ret %"v117";
  @"L99":
    %"v123" : W = (Cmp Eq W) %"v96", #1
    => br %"v123" ? "L119" : "L121";
  @"L119":
    %"chk6" : A = (Check 0 4 Read 1) %"v3";
    %"v124" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v125" : W = Shr %"v124", #22;
    %"v126" : W = Add %"v125", #1;
    %"v127" : L = (Ext Uw) %"v126"
    => ret %"v127";
  @"L121":
    %"v133" : W = (Cmp Eq W) %"v96", #2
    => br %"v133" ? "L131" : "L130";
  @"L130":
    %"v134" : P = Copy $"glibc_libc_start#str.301";
    %"v135" : P = Copy $"glibc_libc_start#str.302";
    %"v136" : P = Copy $"glibc_libc_start#str.304";
    call void $"__libc_assert_fail"(P %"v134", P %"v135", W #587, P %"v136")
    => goto "L131";
  @"L131":
    %"chk7" : A = (Check 0 4 Read 1) %"v3";
    %"v137" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v138" : W = And %"v137", #4095;
    %"v139" : W = Add %"v138", #1;
    %"v140" : L = (Ext Uw) %"v139"
    => ret %"v140";
  @"L31":
    %"v143" : W = Add %"pr.1", #1
    => goto poll "L12";
  @"L14":
    => ret #0
} }.

Definition hi_fn_glibc_libc_start'23handle_hygon : func :=
  ir_fn{ "local" "glibc_libc_start#handle_hygon"(W %"v0") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v2" : P = (Alloc 4) #4;
    %"v3" : P = (Alloc 4) #4;
    %"v4" : P = (Alloc 4) #4;
    %"v5" : P = (Alloc 4) #4;
    %"v6" : P = (Alloc 4) #4;
    %"chk0" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk0" + 0] <- #0;
    %"v11" : W = (Cmp Sgt W) %"v0", #196
    => br %"v11" ? "L7" : "L9" };
  ir_blk{ @"L7":
    => ret #0 };
  ir_blk{ @"L9":
    call void $"zcpuid"(W #2147483648, P %"v6", P %"v3", P %"v4", P %"v5");
    %"chk1" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v17" : W = (Cmp Uge W) %"v16", #2147483677
    => br %"v17" ? "L13" : "L15" };
  ir_blk{ @"L13":
    %"v23" : W = (Cmp Sge W) %"v0", #194
    => br %"v23" ? "L21" : "L20" };
  ir_blk{ @"L20":
    %"v28" : W = (Cmp Sge W) %"v0", #191
    => br %"v28" ? "L21" : "L25" };
  ir_blk{ @"L25":
    %"v33" : W = (Cmp Sge W) %"v0", #188
    => br %"v33" ? "L21" : "L30" };
  ir_blk{ @"L30":
    => goto "L21" };
  ir_blk{ @"L21" [%"pr.2" : W = phi("L13" => #3, "L20" => #2, "L30" => #1, "L25" => #0)]:
    call void $"zcpuid_count"(W #2147483677, W %"pr.2", P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk2" : A = (Check 0 4 Read 1) %"v4";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v39" : W = (Cmp Ne W) %"v38", #0
    => br %"v39" ? "L41" : "L15" };
  ir_blk{ @"L46":
    %"chk3" : A = (Check 0 4 Read 1) %"v3";
    %"v47" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v48" : W = Shr %"v47", #22;
    %"v49" : W = And %"v48", #1023;
    %"v50" : W = Add %"v49", #1;
    %"v51" : L = (Ext Uw) %"v50"
    => ret %"v51" };
  ir_blk{ @"L55":
    %"chk4" : A = (Check 0 4 Read 1) %"v3";
    %"v56" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v57" : W = And %"v56", #4095;
    %"v58" : W = Add %"v57", #1;
    %"v59" : L = (Ext Uw) %"v58"
    => ret %"v59" };
  ir_blk{ @"L63":
    %"chk5" : A = (Check 0 4 Read 1) %"v3";
    %"v64" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v65" : W = Shr %"v64", #22;
    %"v66" : W = And %"v65", #1023;
    %"v67" : W = Add %"v66", #1;
    %"v68" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v69" : W = And %"v68", #4095;
    %"v70" : W = Add %"v69", #1;
    %"v71" : W = Mul %"v67", %"v70";
    %"chk7" : A = (Renew 0 4 Read 1) %"chk2", %"v4";
    %"v72" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v73" : W = Add %"v72", #1;
    %"v74" : W = Mul %"v71", %"v73";
    %"v75" : L = (Ext Uw) %"v74"
    => ret %"v75" };
  ir_blk{ @"L76":
    => unreachable };
  ir_blk{ @"L41":
    %"v78" : W = (Cmp Slt W) %"v0", #191
    => br %"v78" ? "L79" : "L80" };
  ir_blk{ @"L79":
    %"v81" : W = (Cmp Slt W) %"v0", #188
    => br %"v81" ? "L82" : "L83" };
  ir_blk{ @"L82":
    %"v84" : W = (Cmp Eq W) %"v0", #185
    => br %"v84" ? poll "L63" : "L85" };
  ir_blk{ @"L85":
    %"v86" : W = (Cmp Eq W) %"v0", #186
    => br %"v86" ? poll "L46" : "L87" };
  ir_blk{ @"L87":
    %"v88" : W = (Cmp Eq W) %"v0", #187
    => br %"v88" ? poll "L55" : poll "L76" };
  ir_blk{ @"L83":
    %"v90" : W = (Cmp Eq W) %"v0", #188
    => br %"v90" ? poll "L63" : "L91" };
  ir_blk{ @"L91":
    %"v92" : W = (Cmp Eq W) %"v0", #189
    => br %"v92" ? poll "L46" : "L93" };
  ir_blk{ @"L93":
    %"v94" : W = (Cmp Eq W) %"v0", #190
    => br %"v94" ? poll "L55" : poll "L76" };
  ir_blk{ @"L80":
    %"v96" : W = (Cmp Slt W) %"v0", #194
    => br %"v96" ? "L97" : "L98" };
  ir_blk{ @"L97":
    %"v99" : W = (Cmp Eq W) %"v0", #191
    => br %"v99" ? poll "L63" : "L100" };
  ir_blk{ @"L100":
    %"v101" : W = (Cmp Eq W) %"v0", #192
    => br %"v101" ? poll "L46" : "L102" };
  ir_blk{ @"L102":
    %"v103" : W = (Cmp Eq W) %"v0", #193
    => br %"v103" ? poll "L55" : poll "L76" };
  ir_blk{ @"L98":
    %"v105" : W = (Cmp Eq W) %"v0", #194
    => br %"v105" ? poll "L63" : "L106" };
  ir_blk{ @"L106":
    %"v107" : W = (Cmp Eq W) %"v0", #195
    => br %"v107" ? poll "L46" : "L108" };
  ir_blk{ @"L108":
    %"v109" : W = (Cmp Eq W) %"v0", #196
    => br %"v109" ? poll "L55" : poll "L76" };
  ir_blk{ @"L15":
    %"v116" : W = (Cmp Sge W) %"v0", #191;
    %"v117" : W = Add %"v116", #2147483653;
    %"chk8" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"v121" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v123" : W = (Cmp Ult W) %"v121", %"v117"
    => br %"v123" ? "L118" : "L120" };
  ir_blk{ @"L118":
    => ret #0 };
  ir_blk{ @"L120":
    call void $"zcpuid"(W %"v117", P %"v2", P %"v3", P %"v4", P %"v5");
    %"v130" : W = (Cmp Slt W) %"v0", #188
    => br %"v130" ? "L126" : "L128" };
  ir_blk{ @"L126":
    %"v133" : W = Add %"v0", #3;
    %"chk9" : A = (Check 0 4 Read 1) %"v5";
    %"v134" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"chk10" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk10" + 0] <- %"v134"
    => goto "L128" };
  ir_blk{ @"L128" [%"pr.1" : W = phi("L126" => %"v133", "L120" => %"v0")]:
    %"v386" : W = (Cmp Slt W) %"pr.1", #192
    => br %"v386" ? "L387" : "L388" };
  ir_blk{ @"L138":
    %"chk11" : A = (Check 0 4 Read 1) %"v4";
    %"v139" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v140" : W = Shr %"v139", #14;
    %"v141" : W = And %"v140", #261120;
    %"v142" : L = (Ext Uw) %"v141"
    => ret %"v142" };
  ir_blk{ @"L143":
    %"chk12" : A = (Check 0 4 Read 1) %"v4";
    %"v144" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"v145" : W = Shr %"v144", #16;
    %"chk13" : A = (Renew 0 4 Write 1) %"chk12", %"v4";
    store Ww [%"chk13" + 0] <- %"v145";
    %"v149" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"v150" : W = And %"v149", #255;
    %"v151" : W = (Cmp Eq W) %"v150", #255
    => br %"v151" ? "L146" : "L148" };
  ir_blk{ @"L146":
    %"v152" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"v153" : W = Shl %"v152", #2;
    %"v154" : W = And %"v153", #261120;
    %"v155" : L = (Ext Uw) %"v154"
    => ret %"v155" };
  ir_blk{ @"L148":
    %"v157" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"v158" : W = And %"v157", #255;
    %"v159" : L = (Ext Uw) %"v158"
    => ret %"v159" };
  ir_blk{ @"L160":
    %"chk17" : A = (Check 0 4 Read 1) %"v4";
    %"v161" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v162" : W = And %"v161", #255;
    %"v163" : L = (Ext Uw) %"v162"
    => ret %"v163" };
  ir_blk{ @"L164":
    %"chk18" : A = (Check 0 4 Read 1) %"v4";
    %"v168" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v169" : W = And %"v168", #61440;
    %"v170" : W = (Cmp Eq W) %"v169", #0
    => br %"v170" ? "L167" : "L166" };
  ir_blk{ @"L166":
    %"v171" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v172" : W = Shr %"v171", #6;
    %"v173" : W = And %"v172", #67107840
    => goto "L167" };
  ir_blk{ @"L167" [%"v174" : W = phi("L166" => %"v173", "L164" => #0)]:
    %"v175" : L = (Ext Uw) %"v174"
    => ret %"v175" };
  ir_blk{ @"L176":
    %"chk20" : A = (Check 0 4 Read 1) %"v4";
    %"v177" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v178" : W = Shr %"v177", #12;
    %"v179" : W = And %"v178", #15;
    %"v207" : W = (Cmp Ult W) %"v179", #10
    => br %"v207" ? "L208" : "L209" };
  ir_blk{ @"L185":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk20", %"v4";
    %"v186" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v187" : W = Shr %"v186", #12;
    %"v188" : W = And %"v187", #15;
    %"v189" : L = (Ext Uw) %"v188"
    => ret %"v189" };
  ir_blk{ @"L190":
    => ret #8 };
  ir_blk{ @"L191":
    => ret #16 };
  ir_blk{ @"L192":
    => ret #32 };
  ir_blk{ @"L193":
    => ret #48 };
  ir_blk{ @"L194":
    => ret #64 };
  ir_blk{ @"L195":
    => ret #96 };
  ir_blk{ @"L196":
    => ret #128 };
  ir_blk{ @"L197":
    %"chk22" : A = (Renew 0 4 Read 1) %"chk20", %"v4";
    %"v198" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v199" : W = Shr %"v198", #6;
    %"v200" : W = And %"v199", #67107840;
    %"v201" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v202" : W = And %"v201", #255;
    %"v203" : W = Udiv %"v200", %"v202";
    %"v204" : L = (Ext Uw) %"v203"
    => ret %"v204" };
  ir_blk{ @"L205":
    => ret #0 };
  ir_blk{ @"L208":
    %"v210" : W = (Cmp Ult W) %"v179", #4
    => br %"v210" ? "L211" : "L212" };
  ir_blk{ @"L211":
    %"v213" : W = (Cmp Eq W) %"v179", #0
    => br %"v213" ? poll "L185" : "L214" };
  ir_blk{ @"L214":
    %"v215" : W = (Cmp Eq W) %"v179", #1
    => br %"v215" ? poll "L185" : "L216" };
  ir_blk{ @"L216":
    %"v217" : W = (Cmp Eq W) %"v179", #2
    => br %"v217" ? poll "L185" : poll "L205" };
  ir_blk{ @"L212":
    %"v219" : W = (Cmp Eq W) %"v179", #4
    => br %"v219" ? poll "L185" : "L220" };
  ir_blk{ @"L220":
    %"v221" : W = (Cmp Eq W) %"v179", #6
    => br %"v221" ? poll "L190" : "L222" };
  ir_blk{ @"L222":
    %"v223" : W = (Cmp Eq W) %"v179", #8
    => br %"v223" ? poll "L191" : poll "L205" }] [ir_blk{ @"L209":
    %"v225" : W = (Cmp Ult W) %"v179", #13
    => br %"v225" ? "L226" : "L227" };
  ir_blk{ @"L226":
    %"v228" : W = (Cmp Eq W) %"v179", #10
    => br %"v228" ? poll "L192" : "L229" };
  ir_blk{ @"L229":
    %"v230" : W = (Cmp Eq W) %"v179", #11
    => br %"v230" ? poll "L193" : "L231" };
  ir_blk{ @"L231":
    %"v232" : W = (Cmp Eq W) %"v179", #12
    => br %"v232" ? poll "L194" : poll "L205" };
  ir_blk{ @"L227":
    %"v234" : W = (Cmp Eq W) %"v179", #13
    => br %"v234" ? poll "L195" : "L235" };
  ir_blk{ @"L235":
    %"v236" : W = (Cmp Eq W) %"v179", #14
    => br %"v236" ? poll "L196" : "L237" };
  ir_blk{ @"L237":
    %"v238" : W = (Cmp Eq W) %"v179", #15
    => br %"v238" ? poll "L197" : poll "L205" };
  ir_blk{ @"L240":
    %"chk24" : A = (Check 0 4 Read 1) %"v4";
    %"v244" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"v245" : W = And %"v244", #61440;
    %"v246" : W = (Cmp Eq W) %"v245", #0
    => br %"v246" ? "L243" : "L242" };
  ir_blk{ @"L242":
    %"v247" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"v248" : W = And %"v247", #255
    => goto "L243" };
  ir_blk{ @"L243" [%"v249" : W = phi("L242" => %"v248", "L240" => #0)]:
    %"v250" : L = (Ext Uw) %"v249"
    => ret %"v250" };
  ir_blk{ @"L251":
    %"chk26" : A = (Check 0 4 Read 1) %"v5";
    %"v258" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v259" : W = And %"v258", #61440;
    %"v260" : W = (Cmp Eq W) %"v259", #0
    => br %"v260" ? "L255" : "L257" };
  ir_blk{ @"L255":
    => ret #0 };
  ir_blk{ @"L257":
    %"v262" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v263" : W = And %"v262", #1073479680;
    %"v264" : W = Shl %"v263", #1;
    %"v265" : L = (Ext Uw) %"v264";
    %"chk28" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"v269" : W = (RawLoad (LdNarrow Uw) 0) %"chk28";
    %"v270" : W = (Cmp Uge W) %"v269", #2147483656
    => br %"v270" ? "L266" : "L268" };
  ir_blk{ @"L266":
    call void $"zcpuid"(W #2147483656, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk29" : A = (Check 0 4 Read 1) %"v4";
    %"v271" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v272" : W = And %"v271", #255;
    %"v273" : W = Add %"v272", #1
    => goto "L268" };
  ir_blk{ @"L268" [%"pr.6" : W = phi("L266" => %"v273", "L257" => #0)]:
    %"v278" : W = (Cmp Eq W) %"pr.6", #0
    => br %"v278" ? "L274" : "L276" };
  ir_blk{ @"L274":
    call void $"zcpuid"(W #1, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk30" : A = (Renew 0 4 Read 1) %"chk26", %"v5";
    %"v282" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v284" : W = And %"v282", #268435456;
    %"v285" : W = (Cmp Ne W) %"v284", #0
    => br %"v285" ? "L279" : "L276" };
  ir_blk{ @"L279":
    %"chk31" : A = (Check 0 4 Read 1) %"v3";
    %"v286" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v287" : W = Shr %"v286", #16;
    %"v288" : W = And %"v287", #255
    => goto "L276" };
  ir_blk{ @"L276" [%"pr.7" : W = phi("L279" => %"v288", "L274" => %"pr.6", "L268" => %"pr.6")]:
    %"v293" : W = (Cmp Ugt W) %"pr.7", #0
    => br %"v293" ? "L289" : "L291" };
  ir_blk{ @"L289":
    %"v296" : L = (Ext Uw) %"pr.7";
    %"v297" : L = Div %"v265", %"v296"
    => goto "L291" };
  ir_blk{ @"L291" [%"pr.5" : L = phi("L289" => %"v297", "L276" => #0)]:
    call void $"zcpuid_count"(W #2147483677, W #3, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk32" : A = (Check 0 4 Read 1) %"v2";
    %"v299" : W = (RawLoad (LdNarrow Uw) 0) %"chk32";
    %"v300" : W = Shr %"v299", #14;
    %"v301" : W = And %"v300", #4095;
    %"v302" : W = Add %"v301", #1;
    %"v306" : L = (Ext Uw) %"v302";
    %"v307" : L = Mul %"pr.5", %"v306"
    => ret %"v307" };
  ir_blk{ @"L309":
    %"chk33" : A = (Check 0 4 Read 1) %"v5";
    %"v310" : W = (RawLoad (LdNarrow Uw) 0) %"chk33";
    %"v311" : W = Shr %"v310", #12;
    %"v312" : W = And %"v311", #15;
    %"v340" : W = (Cmp Ult W) %"v312", #10
    => br %"v340" ? "L341" : "L342" };
  ir_blk{ @"L318":
    %"chk34" : A = (Renew 0 4 Read 1) %"chk33", %"v5";
    %"v319" : W = (RawLoad (LdNarrow Uw) 0) %"chk34";
    %"v320" : W = Shr %"v319", #12;
    %"v321" : W = And %"v320", #15;
    %"v322" : L = (Ext Uw) %"v321"
    => ret %"v322" };
  ir_blk{ @"L323":
    => ret #8 };
  ir_blk{ @"L324":
    => ret #16 };
  ir_blk{ @"L325":
    => ret #32 };
  ir_blk{ @"L326":
    => ret #48 };
  ir_blk{ @"L327":
    => ret #64 };
  ir_blk{ @"L328":
    => ret #96 };
  ir_blk{ @"L329":
    => ret #128 };
  ir_blk{ @"L330":
    %"chk35" : A = (Renew 0 4 Read 1) %"chk33", %"v5";
    %"v331" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v332" : W = And %"v331", #1073479680;
    %"v333" : W = Shl %"v332", #1;
    %"v334" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v335" : W = And %"v334", #255;
    %"v336" : W = Udiv %"v333", %"v335";
    %"v337" : L = (Ext Uw) %"v336"
    => ret %"v337" };
  ir_blk{ @"L338":
    => ret #0 };
  ir_blk{ @"L341":
    %"v343" : W = (Cmp Ult W) %"v312", #4
    => br %"v343" ? "L344" : "L345" };
  ir_blk{ @"L344":
    %"v346" : W = (Cmp Eq W) %"v312", #0
    => br %"v346" ? poll "L318" : "L347" };
  ir_blk{ @"L347":
    %"v348" : W = (Cmp Eq W) %"v312", #1
    => br %"v348" ? poll "L318" : "L349" };
  ir_blk{ @"L349":
    %"v350" : W = (Cmp Eq W) %"v312", #2
    => br %"v350" ? poll "L318" : poll "L338" };
  ir_blk{ @"L345":
    %"v352" : W = (Cmp Eq W) %"v312", #4
    => br %"v352" ? poll "L318" : "L353" };
  ir_blk{ @"L353":
    %"v354" : W = (Cmp Eq W) %"v312", #6
    => br %"v354" ? poll "L323" : "L355" };
  ir_blk{ @"L355":
    %"v356" : W = (Cmp Eq W) %"v312", #8
    => br %"v356" ? poll "L324" : poll "L338" };
  ir_blk{ @"L342":
    %"v358" : W = (Cmp Ult W) %"v312", #13
    => br %"v358" ? "L359" : "L360" };
  ir_blk{ @"L359":
    %"v361" : W = (Cmp Eq W) %"v312", #10
    => br %"v361" ? poll "L325" : "L362" };
  ir_blk{ @"L362":
    %"v363" : W = (Cmp Eq W) %"v312", #11
    => br %"v363" ? poll "L326" : "L364" };
  ir_blk{ @"L364":
    %"v365" : W = (Cmp Eq W) %"v312", #12
    => br %"v365" ? poll "L327" : poll "L338" };
  ir_blk{ @"L360":
    %"v367" : W = (Cmp Eq W) %"v312", #13
    => br %"v367" ? poll "L328" : "L368" };
  ir_blk{ @"L368":
    %"v369" : W = (Cmp Eq W) %"v312", #14
    => br %"v369" ? poll "L329" : "L370" };
  ir_blk{ @"L370":
    %"v371" : W = (Cmp Eq W) %"v312", #15
    => br %"v371" ? poll "L330" : poll "L338" };
  ir_blk{ @"L373":
    %"chk37" : A = (Check 0 4 Read 1) %"v5";
    %"v377" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v378" : W = And %"v377", #61440;
    %"v379" : W = (Cmp Eq W) %"v378", #0
    => br %"v379" ? "L376" : "L375" };
  ir_blk{ @"L375":
    %"v380" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v381" : W = And %"v380", #255
    => goto "L376" };
  ir_blk{ @"L376" [%"v382" : W = phi("L375" => %"v381", "L373" => #0)]:
    %"v383" : L = (Ext Uw) %"v382"
    => ret %"v383" };
  ir_blk{ @"L384":
    => unreachable };
  ir_blk{ @"L387":
    %"v389" : W = (Cmp Eq W) %"pr.1", #188
    => br %"v389" ? poll "L138" : "L390" };
  ir_blk{ @"L390":
    %"v391" : W = (Cmp Eq W) %"pr.1", #189
    => br %"v391" ? poll "L143" : "L392" };
  ir_blk{ @"L392":
    %"v393" : W = (Cmp Eq W) %"pr.1", #190
    => br %"v393" ? poll "L160" : "L394" };
  ir_blk{ @"L394":
    %"v395" : W = (Cmp Eq W) %"pr.1", #191
    => br %"v395" ? poll "L164" : poll "L384" };
  ir_blk{ @"L388":
    %"v397" : W = (Cmp Slt W) %"pr.1", #194
    => br %"v397" ? "L398" : "L399" };
  ir_blk{ @"L398":
    %"v400" : W = (Cmp Eq W) %"pr.1", #192
    => br %"v400" ? poll "L176" : "L401" };
  ir_blk{ @"L401":
    %"v402" : W = (Cmp Eq W) %"pr.1", #193
    => br %"v402" ? poll "L240" : poll "L384" };
  ir_blk{ @"L399":
    %"v404" : W = (Cmp Eq W) %"pr.1", #194
    => br %"v404" ? poll "L251" : "L405" };
  ir_blk{ @"L405":
    %"v406" : W = (Cmp Eq W) %"pr.1", #195
    => br %"v406" ? poll "L309" : "L407" };
  ir_blk{ @"L407":
    %"v408" : W = (Cmp Eq W) %"pr.1", #196
    => br %"v408" ? poll "L373" : poll "L384" }])) }.
