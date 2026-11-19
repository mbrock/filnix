(** This file defines checked IR from glibc’s `libio/genops.os` object.
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

Definition fn__IO_cleanup : func :=
  ir_fn{ "export" "_IO_cleanup"() -> (RClass W) blocks ((app [ir_blk{ @"start":
    call %"v1" : W = $"__GI__IO_flush_all"();
    %"iw_1.v2" : P = (Alloc 8) #32;
    %"iw_1.v4" : P = Copy $"glibc_genops#flush_cleanup";
    %"iw_1.v5" = %"iw_1.v2" +p #8;
    %"chk0" : A = (Check 0 8 Write 8) %"iw_1.v5";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"iw_1.v2";
    store.ptr [%"chk1" + 0] <- %"iw_1.v4";
    call void $"__GI___libc_cleanup_push_defer"(P %"iw_1.v2");
    call %"iw_1.v16" : P = $"zthread_self_cookie"();
    %"iw_1.v20" : P = Copy $"__libc_single_threaded_internal";
    %"chk2" : A = (Check 0 1 Read 1) %"iw_1.v20";
    %"iw_1.v21" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"iw_1.v22" : W = (Cmp Ne W) %"iw_1.v21", #0
    => br %"iw_1.v22" ? "iw_1.L23" : "iw_1.L24" };
  ir_blk{ @"iw_1.L23":
    %"iw_1.v25" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v26" = %"iw_1.v25" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v26";
    %"iw_1.v27" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v28" : L = Ptoi %"iw_1.v27";
    %"iw_1.v29" : L = Ptoi #0;
    %"iw_1.v30" : W = (Cmp Eq L) %"iw_1.v28", %"iw_1.v29"
    => goto "iw_1.L24" };
  ir_blk{ @"iw_1.L24" [%"iw_1.v32" : W = phi("start" => #0, "iw_1.L23" => %"iw_1.v30")]:
    => br %"iw_1.v32" ? "iw_1.L17" : "iw_1.L18" };
  ir_blk{ @"iw_1.L17":
    %"iw_1.v33" : P = Copy $"glibc_genops#list_all_lock";
    %"chk4" : A = (Check 0 4 Write 1) %"iw_1.v33";
    store Ww [%"chk4" + 0] <- #1;
    %"iw_1.v34" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v35" = %"iw_1.v34" +p #8;
    %"chk5" : A = (Check 0 8 Write 8) %"iw_1.v35";
    store.ptr [%"chk5" + 0] <- %"iw_1.v16"
    => goto "iw_1.L14" };
  ir_blk{ @"iw_1.L18":
    %"iw_1.v40" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v41" = %"iw_1.v40" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v41";
    %"iw_1.v42" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v44" : L = Ptoi %"iw_1.v42";
    %"iw_1.v45" : L = Ptoi %"iw_1.v16";
    %"iw_1.v46" : W = (Cmp Ne L) %"iw_1.v44", %"iw_1.v45"
    => br %"iw_1.v46" ? "iw_1.L37" : "iw_1.L38" };
  ir_blk{ @"iw_1.L37":
    %"iw_1.v48" : P = Copy $"glibc_genops#list_all_lock";
    %"chk7" : A = (Check 0 4 Write 4) %"iw_1.v48";
    %"iw_1.v55" : W = (RawCas (CasNarrow Sw) 0) %"chk7", #0, #1;
    %"iw_1.v56" : W = (Cmp Eq W) %"iw_1.v55", #0
    => br %"iw_1.v56" ? "iw_1.L58" : "iw_1.L57" };
  ir_blk{ @"iw_1.L57":
    => goto "iw_1.L58" };
  ir_blk{ @"iw_1.L58":
    %"iw_1.v59" : W = (Cmp Ne W) %"iw_1.v55", #0
    => br %"iw_1.v59" ? "iw_1.L62" : "iw_1.L51" };
  ir_blk{ @"iw_1.L62":
    call void $"__GI___lll_lock_wait_private"(P %"iw_1.v48")
    => goto "iw_1.L51" };
  ir_blk{ @"iw_1.L51":
    %"iw_1.v72" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v73" = %"iw_1.v72" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"iw_1.v73";
    store.ptr [%"chk8" + 0] <- %"iw_1.v16"
    => goto "iw_1.L14" };
  ir_blk{ @"iw_1.L38":
    %"iw_1.v75" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v76" = %"iw_1.v75" +p #4;
    %"chk9" : A = (Check 0 4 Read 1) %"iw_1.v76";
    %"iw_1.v77" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"iw_1.v78" : W = Add %"iw_1.v77", #1;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk9", %"iw_1.v76";
    store Ww [%"chk10" + 0] <- %"iw_1.v78"
    => goto "iw_1.L14" };
  ir_blk{ @"iw_1.L14":
    %"iw_1.v79" : P = Copy $"__GI__IO_list_all";
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v79";
    %"iw_1.v80" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto "iw_1.L81" };
  ir_blk{ @"iw_1.L81" [%"iw_1.pr.1" : P = phi("iw_1.L14" => %"iw_1.v80", "iw_1.L301" => %"iw_1.v385")]:
    %"iw_1.v86" : L = Ptoi %"iw_1.pr.1";
    %"iw_1.v87" : W = (Cmp Ne L) %"iw_1.v86", #0
    => br %"iw_1.v87" ? "iw_1.L82" : "iw_1.L386" };
  ir_blk{ @"iw_1.L82":
    %"iw_1.v89" : P = Copy $"glibc_genops#run_fp";
    %"chk12" : A = (Check 0 8 Write 8) %"iw_1.v89";
    store.ptr [%"chk12" + 0] <- %"iw_1.pr.1";
    %"chk13" : A = (Check 0 4 Read 1) %"iw_1.pr.1";
    %"iw_1.v95" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"iw_1.v96" : W = And %"iw_1.v95", #32768;
    %"iw_1.v97" : W = (Cmp Eq W) %"iw_1.v96", #0
    => br %"iw_1.v97" ? "iw_1.L98" : "iw_1.L93" };
  ir_blk{ @"iw_1.L98":
    call %"iw_1.v102" : P = $"zthread_self_cookie"();
    %"iw_1.v106" : P = Copy $"__libc_single_threaded_internal";
    %"chk14" : A = (Check 0 1 Read 1) %"iw_1.v106";
    %"iw_1.v107" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_1.v108" : W = (Cmp Ne W) %"iw_1.v107", #0
    => br %"iw_1.v108" ? "iw_1.L109" : "iw_1.L110" };
  ir_blk{ @"iw_1.L109":
    %"iw_1.v112" = %"iw_1.pr.1" +p #136;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v112";
    %"iw_1.v113" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_1.v114" = %"iw_1.v113" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"iw_1.v114";
    %"iw_1.v115" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_1.v116" : L = Ptoi %"iw_1.v115";
    %"iw_1.v117" : L = Ptoi #0;
    %"iw_1.v118" : W = (Cmp Eq L) %"iw_1.v116", %"iw_1.v117"
    => goto "iw_1.L110" };
  ir_blk{ @"iw_1.L110" [%"iw_1.v120" : W = phi("iw_1.L98" => #0, "iw_1.L109" => %"iw_1.v118")]:
    => br %"iw_1.v120" ? "iw_1.L103" : "iw_1.L104" };
  ir_blk{ @"iw_1.L103":
    %"iw_1.v122" = %"iw_1.pr.1" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v122";
    %"iw_1.v123" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Write 1) %"iw_1.v123";
    store Ww [%"chk18" + 0] <- #1;
    %"iw_1.v126" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_1.v127" = %"iw_1.v126" +p #8;
    %"chk20" : A = (Check 0 8 Write 8) %"iw_1.v127";
    store.ptr [%"chk20" + 0] <- %"iw_1.v102"
    => goto "iw_1.L93" };
  ir_blk{ @"iw_1.L104":
    %"iw_1.v133" = %"iw_1.pr.1" +p #136;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v133";
    %"iw_1.v134" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_1.v135" = %"iw_1.v134" +p #8;
    %"chk22" : A = (Check 0 8 Read 8) %"iw_1.v135";
    %"iw_1.v136" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_1.v138" : L = Ptoi %"iw_1.v136";
    %"iw_1.v139" : L = Ptoi %"iw_1.v102";
    %"iw_1.v140" : W = (Cmp Ne L) %"iw_1.v138", %"iw_1.v139"
    => br %"iw_1.v140" ? "iw_1.L129" : "iw_1.L130" };
  ir_blk{ @"iw_1.L129":
    %"iw_1.v143" = %"iw_1.pr.1" +p #136;
    %"iw_1.v144" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 4 Write 4) %"iw_1.v144";
    %"iw_1.v151" : W = (RawCas (CasNarrow Sw) 0) %"chk24", #0, #1;
    %"iw_1.v152" : W = (Cmp Eq W) %"iw_1.v151", #0
    => br %"iw_1.v152" ? "iw_1.L154" : "iw_1.L153" };
  ir_blk{ @"iw_1.L153":
    => goto "iw_1.L154" };
  ir_blk{ @"iw_1.L154":
    %"iw_1.v155" : W = (Cmp Ne W) %"iw_1.v151", #0
    => br %"iw_1.v155" ? "iw_1.L158" : "iw_1.L147" };
  ir_blk{ @"iw_1.L158":
    call void $"__GI___lll_lock_wait_private"(P %"iw_1.v144")
    => goto "iw_1.L147" };
  ir_blk{ @"iw_1.L147":
    %"iw_1.v169" = %"iw_1.pr.1" +p #136;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk21", %"iw_1.v169";
    %"iw_1.v170" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_1.v171" = %"iw_1.v170" +p #8;
    %"chk26" : A = (Check 0 8 Write 8) %"iw_1.v171";
    store.ptr [%"chk26" + 0] <- %"iw_1.v102"
    => goto "iw_1.L93" };
  ir_blk{ @"iw_1.L130":
    %"iw_1.v174" = %"iw_1.pr.1" +p #136;
    %"iw_1.v175" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_1.v176" = %"iw_1.v175" +p #4;
    %"chk28" : A = (Check 0 4 Read 1) %"iw_1.v176";
    %"iw_1.v177" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"iw_1.v178" : W = Add %"iw_1.v177", #1;
    %"chk29" : A = (Renew 0 4 Write 1) %"chk28", %"iw_1.v176";
    store Ww [%"chk29" + 0] <- %"iw_1.v178"
    => goto "iw_1.L93" };
  ir_blk{ @"iw_1.L93":
    %"iw_1.v183" = %"iw_1.pr.1" +p #80;
    %"chk30" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v183";
    %"iw_1.v184" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_1.v185" : L = Ptoi %"iw_1.v184";
    %"iw_1.v186" : L = Ptoi #0;
    %"iw_1.v187" : W = (Cmp Ne L) %"iw_1.v185", %"iw_1.v186"
    => br %"iw_1.v187" ? "iw_1.L179" : "iw_1.L194" };
  ir_blk{ @"iw_1.L179":
    call void $"__GI__IO_free_backup_area"(P %"iw_1.pr.1")
    => goto "iw_1.L194" };
  ir_blk{ @"iw_1.L194":
    %"iw_1.v197" = %"iw_1.pr.1" +p #192;
    %"chk31" : A = (HalfCheck Upper 0 4 Read 1) %"chk13", %"iw_1.v197";
    %"iw_1.v198" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"iw_1.v199" : W = (Cmp Sgt W) %"iw_1.v198", #0
    => br %"iw_1.v199" ? "iw_1.L202" : "iw_1.L203" };
  ir_blk{ @"iw_1.L202":
    %"iw_1.v205" = %"iw_1.pr.1" +p #160;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v205";
    %"iw_1.v206" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"iw_1.v207" = %"iw_1.v206" +p #72;
    %"chk33" : A = (Check 0 8 Read 8) %"iw_1.v207";
    %"iw_1.v208" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"iw_1.v209" : L = Ptoi %"iw_1.v208";
    %"iw_1.v211" : W = (Cmp Ne L) %"iw_1.v209", %"iw_1.v186"
    => goto "iw_1.L203" };
  ir_blk{ @"iw_1.L203" [%"iw_1.v213" : W = phi("iw_1.L194" => #0, "iw_1.L202" => %"iw_1.v211")]:
    => br %"iw_1.v213" ? "iw_1.L189" : "iw_1.L191" };
  ir_blk{ @"iw_1.L189":
    call void $"__GI__IO_free_wbackup_area"(P %"iw_1.pr.1")
    => goto "iw_1.L191" };
  ir_blk{ @"iw_1.L191":
    %"chk34" : A = (Renew 0 4 Read 1) %"chk13", %"iw_1.pr.1";
    %"iw_1.v219" : W = (RawLoad (LdNarrow Sw) 0) %"chk34";
    %"iw_1.v220" : W = And %"iw_1.v219", #2;
    %"iw_1.v221" : W = (Cmp Eq W) %"iw_1.v220", #0
    => br %"iw_1.v221" ? "iw_1.L225" : "iw_1.L223" }] [ir_blk{ @"iw_1.L225":
    %"iw_1.v228" = %"iw_1.pr.1" +p #192;
    %"chk35" : A = (Renew 0 4 Read 1) %"chk31", %"iw_1.v228";
    %"iw_1.v229" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"iw_1.v230" : W = (Cmp Ne W) %"iw_1.v229", #0
    => goto "iw_1.L223" };
  ir_blk{ @"iw_1.L223" [%"iw_1.v234" : W = phi("iw_1.L191" => #0, "iw_1.L225" => %"iw_1.v230")]:
    => br %"iw_1.v234" ? "iw_1.L240" : "iw_1.L291" };
  ir_blk{ @"iw_1.L240":
    %"iw_1.v242" : P = Copy $"glibc_genops#dealloc_buffers";
    %"chk36" : A = (Check 0 1 Read 1) %"iw_1.v242";
    %"iw_1.v243" : W = (RawLoad (LdNarrow Ub) 0) %"chk36";
    %"iw_1.v244" : W = (Cmp Eq W) %"iw_1.v243", #0
    => br %"iw_1.v244" ? "iw_1.L247" : "iw_1.L248" };
  ir_blk{ @"iw_1.L247":
    %"chk37" : A = (Renew 0 4 Read 1) %"chk13", %"iw_1.pr.1";
    %"iw_1.v250" : W = (RawLoad (LdNarrow Sw) 0) %"chk37";
    %"iw_1.v251" : W = And %"iw_1.v250", #1;
    %"iw_1.v252" : W = (Cmp Eq W) %"iw_1.v251", #0
    => goto "iw_1.L248" };
  ir_blk{ @"iw_1.L248" [%"iw_1.v254" : W = phi("iw_1.L240" => #0, "iw_1.L247" => %"iw_1.v252")]:
    => br %"iw_1.v254" ? "iw_1.L235" : "iw_1.L237" };
  ir_blk{ @"iw_1.L235":
    %"chk38" : A = (Renew 0 4 Read 1) %"chk13", %"iw_1.pr.1";
    %"iw_1.v256" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"iw_1.v257" : W = Or %"iw_1.v256", #1;
    %"chk39" : A = (Renew 0 4 Write 1) %"chk13", %"iw_1.pr.1";
    store Ww [%"chk39" + 0] <- %"iw_1.v257";
    %"iw_1.v259" = %"iw_1.pr.1" +p #168;
    %"iw_1.v260" : P = Copy $"glibc_genops#freeres_list";
    %"chk40" : A = (Check 0 8 Read 8) %"iw_1.v260";
    %"iw_1.v261" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : A = (HalfCheck Upper 0 8 Write 8) %"chk13", %"iw_1.v259";
    store.ptr [%"chk41" + 0] <- %"iw_1.v261";
    %"iw_1.v262" : P = Copy $"glibc_genops#freeres_list";
    %"chk42" : A = (Check 0 8 Write 8) %"iw_1.v262";
    store.ptr [%"chk42" + 0] <- %"iw_1.pr.1";
    %"iw_1.v265" = %"iw_1.pr.1" +p #176;
    %"iw_1.v267" = %"iw_1.pr.1" +p #56;
    %"chk43" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v267";
    %"iw_1.v268" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"chk44" : A = (HalfCheck Upper 0 8 Write 8) %"chk13", %"iw_1.v265";
    store.ptr [%"chk44" + 0] <- %"iw_1.v268"
    => goto "iw_1.L237" };
  ir_blk{ @"iw_1.L237":
    %"iw_1.v270" = %"iw_1.pr.1" +p #216;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v270";
    %"iw_1.v271" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"iw_1.iw_1.v4" : L = Ptoi %"iw_1.v271";
    %"iw_1.iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_1.v8" : L = Ptoi %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v9" : L = Sub %"iw_1.iw_1.v4", %"iw_1.iw_1.v8";
    %"iw_1.iw_1.v15" : W = (Cmp Uge L) %"iw_1.iw_1.v9", #2352
    => br %"iw_1.iw_1.v15" ? "iw_1.iw_1.L10" : "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.join":
    %"iw_1.v273" = %"iw_1.v271" +p #88;
    %"chk46" : A = (Check 0 8 Read 8) %"iw_1.v273";
    %"iw_1.v274" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"chk47" : F = CheckFunction %"iw_1.v274";
    rawcall %"iw_1.v276" : P = %"chk47"(P %"iw_1.pr.1", P #0, L #0);
    %"iw_1.v285" = %"iw_1.pr.1" +p #192;
    %"chk48" : A = (Renew 0 4 Read 1) %"chk31", %"iw_1.v285";
    %"iw_1.v286" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"iw_1.v287" : W = (Cmp Sgt W) %"iw_1.v286", #0
    => br %"iw_1.v287" ? "iw_1.L277" : "iw_1.L291" };
  ir_blk{ @"iw_1.L277":
    call void $"__GI__IO_wsetb"(P %"iw_1.pr.1", P #0, P #0, W #0)
    => goto "iw_1.L291" };
  ir_blk{ @"iw_1.L291":
    %"iw_1.v297" = %"iw_1.pr.1" +p #192;
    %"chk49" : A = (Renew 0 4 Write 1) %"chk31", %"iw_1.v297";
    store Ww [%"chk49" + 0] <- #4294967295;
    %"chk50" : A = (Renew 0 4 Read 1) %"chk13", %"iw_1.pr.1";
    %"iw_1.v303" : W = (RawLoad (LdNarrow Sw) 0) %"chk50";
    %"iw_1.v304" : W = And %"iw_1.v303", #32768;
    %"iw_1.v305" : W = (Cmp Eq W) %"iw_1.v304", #0
    => br %"iw_1.v305" ? "iw_1.L306" : "iw_1.L301" };
  ir_blk{ @"iw_1.L306":
    %"iw_1.v312" : P = Copy $"__libc_single_threaded_internal";
    %"chk51" : A = (Check 0 1 Read 1) %"iw_1.v312";
    %"iw_1.v313" : W = (RawLoad (LdNarrow Sb) 0) %"chk51";
    %"iw_1.v314" : W = (Cmp Ne W) %"iw_1.v313", #0
    => br %"iw_1.v314" ? "iw_1.L315" : "iw_1.L316" };
  ir_blk{ @"iw_1.L315":
    %"iw_1.v318" = %"iw_1.pr.1" +p #136;
    %"chk52" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v318";
    %"iw_1.v319" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"iw_1.v320" = %"iw_1.v319" +p #4;
    %"chk53" : A = (Check 0 4 Read 1) %"iw_1.v320";
    %"iw_1.v321" : W = (RawLoad (LdNarrow Sw) 0) %"chk53";
    %"iw_1.v322" : W = (Cmp Eq W) %"iw_1.v321", #0
    => goto "iw_1.L316" };
  ir_blk{ @"iw_1.L316" [%"iw_1.v324" : W = phi("iw_1.L306" => #0, "iw_1.L315" => %"iw_1.v322")]:
    => br %"iw_1.v324" ? "iw_1.L309" : "iw_1.L310" };
  ir_blk{ @"iw_1.L309":
    %"iw_1.v326" = %"iw_1.pr.1" +p #136;
    %"chk54" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v326";
    %"iw_1.v327" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"iw_1.v328" = %"iw_1.v327" +p #8;
    %"chk55" : A = (Check 0 8 Write 8) %"iw_1.v328";
    store.ptr [%"chk55" + 0] <- #0;
    %"chk56" : A = (Renew 0 8 Read 8) %"chk54", %"iw_1.v326";
    %"iw_1.v331" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"chk57" : A = (Check 0 4 Write 1) %"iw_1.v331";
    store Ww [%"chk57" + 0] <- #0
    => goto "iw_1.L301" };
  ir_blk{ @"iw_1.L310":
    %"iw_1.v336" = %"iw_1.pr.1" +p #136;
    %"chk58" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v336";
    %"iw_1.v337" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"iw_1.v338" = %"iw_1.v337" +p #4;
    %"chk59" : A = (Check 0 4 Read 1) %"iw_1.v338";
    %"iw_1.v339" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"iw_1.v340" : W = (Cmp Eq W) %"iw_1.v339", #0
    => br %"iw_1.v340" ? "iw_1.L332" : "iw_1.L333" };
  ir_blk{ @"iw_1.L332":
    %"iw_1.v342" = %"iw_1.pr.1" +p #136;
    %"iw_1.v343" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"iw_1.v344" = %"iw_1.v343" +p #8;
    %"chk61" : A = (Check 0 8 Write 8) %"iw_1.v344";
    store.ptr [%"chk61" + 0] <- #0;
    %"chk62" : A = (Renew 0 8 Read 8) %"chk58", %"iw_1.v342";
    %"iw_1.v348" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"chk63" : A = (Check 0 4 Read 1) %"iw_1.v348";
    %"iw_1.v352" : W = (RawLoad (LdNarrow Sw) 0) %"chk63"
    => goto "iw_1.L353" };
  ir_blk{ @"iw_1.L353" [%"iw_1.v355" : W = phi("iw_1.L332" => %"iw_1.v352", "iw_1.L353" => %"iw_1.v356")]:
    %"chk64" : A = (HalfCheck Lower 0 4 Write 4) %"chk63", %"iw_1.v348";
    %"iw_1.v356" : W = (RawCas (CasNarrow Sw) 0) %"chk64", %"iw_1.v355", #0;
    %"iw_1.v357" : W = (Cmp Eq W) %"iw_1.v356", %"iw_1.v355"
    => br %"iw_1.v357" ? "iw_1.L354" : poll "iw_1.L353" };
  ir_blk{ @"iw_1.L354":
    %"iw_1.v362" : W = (Cmp Sgt W) %"iw_1.v355", #1
    => br %"iw_1.v362" ? "iw_1.L365" : "iw_1.L301" };
  ir_blk{ @"iw_1.L365":
    call void $"__GI___lll_lock_wake_private"(P %"iw_1.v348")
    => goto "iw_1.L301" };
  ir_blk{ @"iw_1.L333":
    %"iw_1.v377" = %"iw_1.pr.1" +p #136;
    %"iw_1.v378" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"iw_1.v379" = %"iw_1.v378" +p #4;
    %"chk66" : A = (Check 0 4 Read 1) %"iw_1.v379";
    %"iw_1.v380" : W = (RawLoad (LdNarrow Sw) 0) %"chk66";
    %"iw_1.v381" : W = Sub %"iw_1.v380", #1;
    %"chk67" : A = (Renew 0 4 Write 1) %"chk66", %"iw_1.v379";
    store Ww [%"chk67" + 0] <- %"iw_1.v381"
    => goto "iw_1.L301" };
  ir_blk{ @"iw_1.L301":
    %"iw_1.v382" : P = Copy $"glibc_genops#run_fp";
    %"chk68" : A = (Check 0 8 Write 8) %"iw_1.v382";
    store.ptr [%"chk68" + 0] <- #0;
    %"iw_1.v384" = %"iw_1.pr.1" +p #104;
    %"chk69" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v384";
    %"iw_1.v385" : P = (RawLoadPointer 0 load_effects) %"chk69"
    => goto poll "iw_1.L81" };
  ir_blk{ @"iw_1.L386":
    %"iw_1.v392" : P = Copy $"__libc_single_threaded_internal";
    %"chk70" : A = (Check 0 1 Read 1) %"iw_1.v392";
    %"iw_1.v393" : W = (RawLoad (LdNarrow Sb) 0) %"chk70";
    %"iw_1.v394" : W = (Cmp Ne W) %"iw_1.v393", #0
    => br %"iw_1.v394" ? "iw_1.L395" : "iw_1.L396" };
  ir_blk{ @"iw_1.L395":
    %"iw_1.v397" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v398" = %"iw_1.v397" +p #4;
    %"chk71" : A = (Check 0 4 Read 1) %"iw_1.v398";
    %"iw_1.v399" : W = (RawLoad (LdNarrow Sw) 0) %"chk71";
    %"iw_1.v400" : W = (Cmp Eq W) %"iw_1.v399", #0
    => goto "iw_1.L396" };
  ir_blk{ @"iw_1.L396" [%"iw_1.v402" : W = phi("iw_1.L386" => #0, "iw_1.L395" => %"iw_1.v400")]:
    => br %"iw_1.v402" ? "iw_1.L389" : "iw_1.L390" };
  ir_blk{ @"iw_1.L389":
    %"iw_1.v403" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v404" = %"iw_1.v403" +p #8;
    %"chk72" : A = (Check 0 8 Write 8) %"iw_1.v404";
    store.ptr [%"chk72" + 0] <- #0;
    %"iw_1.v405" : P = Copy $"glibc_genops#list_all_lock";
    %"chk73" : A = (Check 0 4 Write 1) %"iw_1.v405";
    store Ww [%"chk73" + 0] <- #0
    => goto "iw_1.L448" };
  ir_blk{ @"iw_1.L390":
    %"iw_1.v409" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v410" = %"iw_1.v409" +p #4;
    %"chk74" : A = (Check 0 4 Read 1) %"iw_1.v410";
    %"iw_1.v411" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"iw_1.v412" : W = (Cmp Eq W) %"iw_1.v411", #0
    => br %"iw_1.v412" ? "iw_1.L406" : "iw_1.L407" };
  ir_blk{ @"iw_1.L406":
    %"iw_1.v413" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v414" = %"iw_1.v413" +p #8;
    %"chk75" : A = (Check 0 8 Write 8) %"iw_1.v414";
    store.ptr [%"chk75" + 0] <- #0;
    %"iw_1.v416" : P = Copy $"glibc_genops#list_all_lock";
    %"chk76" : A = (Check 0 4 Read 1) %"iw_1.v416";
    %"iw_1.v420" : W = (RawLoad (LdNarrow Sw) 0) %"chk76"
    => goto "iw_1.L421" };
  ir_blk{ @"iw_1.L421" [%"iw_1.v423" : W = phi("iw_1.L406" => %"iw_1.v420", "iw_1.L421" => %"iw_1.v424")]:
    %"chk77" : A = (HalfCheck Lower 0 4 Write 4) %"chk76", %"iw_1.v416";
    %"iw_1.v424" : W = (RawCas (CasNarrow Sw) 0) %"chk77", %"iw_1.v423", #0;
    %"iw_1.v425" : W = (Cmp Eq W) %"iw_1.v424", %"iw_1.v423"
    => br %"iw_1.v425" ? "iw_1.L422" : poll "iw_1.L421" };
  ir_blk{ @"iw_1.L422":
    %"iw_1.v430" : W = (Cmp Sgt W) %"iw_1.v423", #1
    => br %"iw_1.v430" ? "iw_1.L433" : "iw_1.L448" };
  ir_blk{ @"iw_1.L433":
    call void $"__GI___lll_lock_wake_private"(P %"iw_1.v416")
    => goto "iw_1.L448" };
  ir_blk{ @"iw_1.L407":
    %"iw_1.v444" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v445" = %"iw_1.v444" +p #4;
    %"chk78" : A = (Check 0 4 Read 1) %"iw_1.v445";
    %"iw_1.v446" : W = (RawLoad (LdNarrow Sw) 0) %"chk78";
    %"iw_1.v447" : W = Sub %"iw_1.v446", #1;
    %"chk79" : A = (Renew 0 4 Write 1) %"chk78", %"iw_1.v445";
    store Ww [%"chk79" + 0] <- %"iw_1.v447"
    => goto "iw_1.L448" };
  ir_blk{ @"iw_1.L448":
    call void $"__GI___libc_cleanup_pop_restore"(P %"iw_1.v2")
    => ret %"v1" }])) }.

Definition fn__IO_default_imbue : func :=
  ir_fn{ "export" "_IO_default_imbue"(P %"v0", P %"v2") -> RVoid {
  @"start":
    => ret void
} }.

Definition fn__IO_default_read : func :=
  ir_fn{ "export" "_IO_default_read"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => ret #18446744073709551615
} }.

Definition fn__IO_default_seek : func :=
  ir_fn{ "export" "_IO_default_seek"(P %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    => ret #18446744073709551615
} }.

Definition fn__IO_default_seekpos : func :=
  ir_fn{ "export" "_IO_default_seekpos"(P %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v7" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v8";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v10" = %"v8" +p #72;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v11";
    rawcall %"v15" : L = %"chk2"(P %"v0", L %"v2", W #0, W %"v4")
    => ret %"v15"
} }.

Definition fn__IO_default_setbuf : func :=
  ir_fn{ "export" "_IO_default_setbuf"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v10" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v11";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v13" = %"v11" +p #96;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v14";
    rawcall %"v16" : W = %"chk2"(P %"v0");
    %"v18" : W = (Cmp Eq W) %"v16", #4294967295
    => br %"v18" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"v24" : L = Ptoi %"v2";
    %"v25" : L = Ptoi #0;
    %"v26" : W = (Cmp Eq L) %"v24", %"v25"
    => br %"v26" ? "L28" : "L27";
  @"L27":
    %"v30" : W = (Cmp Eq L) %"v4", #0
    => goto "L28";
  @"L28" [%"v32" : W = phi("L8" => #1, "L27" => %"v30")]:
    => br %"v32" ? "L20" : "L21";
  @"L20":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v35" : W = Or %"v34", #2;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk4" + 0] <- %"v35";
    %"v38" = %"v0" +p #131;
    %"v41" = %"v38" +p #1;
    call void $"__GI__IO_setb"(P %"v0", P %"v38", P %"v41", W #0)
    => goto "L22";
  @"L21":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v43" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v45" : W = And %"v43", #4294967293;
    %"chk6" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk6" + 0] <- %"v45";
    %"v50" = %"v2" +p %"v4";
    call void $"__GI__IO_setb"(P %"v0", P %"v2", P %"v50", W #0)
    => goto "L22";
  @"L22":
    %"v52" = %"v0" +p #32;
    %"v54" = %"v0" +p #40;
    %"v56" = %"v0" +p #48;
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v56";
    store.ptr [%"chk7" + 0] <- #0;
    %"chk8" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v54";
    store.ptr [%"chk8" + 0] <- #0;
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v52";
    store.ptr [%"chk9" + 0] <- #0;
    %"v58" = %"v0" +p #24;
    %"v60" = %"v0" +p #8;
    %"v62" = %"v0" +p #16;
    %"chk10" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v62";
    store.ptr [%"chk10" + 0] <- #0;
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v60";
    store.ptr [%"chk11" + 0] <- #0;
    %"chk12" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v58";
    store.ptr [%"chk12" + 0] <- #0
    => ret %"v0"
} }.

Definition fn__IO_default_showmanyc : func :=
  ir_fn{ "export" "_IO_default_showmanyc"(P %"v0") -> (RClass W) {
  @"start":
    => ret #4294967295
} }.

Definition fn__IO_default_stat : func :=
  ir_fn{ "export" "_IO_default_stat"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    => ret #4294967295
} }.

Definition fn__IO_default_sync : func :=
  ir_fn{ "export" "_IO_default_sync"(P %"v0") -> (RClass W) {
  @"start":
    => ret #0
} }.

Definition fn__IO_default_write : func :=
  ir_fn{ "export" "_IO_default_write"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => ret #0
} }.

Definition fn__IO_no_init : func :=
  ir_fn{ "export" "_IO_no_init"(P %"v0", W %"v2", W %"v4", P %"v6", P %"v8") -> RVoid {
  @"start":
    call void $"_IO_old_init"(P %"v0", W %"v2");
    %"v13" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk0" + 0] <- %"v4";
    %"v19" : W = (Cmp Sge W) %"v4", #0
    => br %"v19" ? "L15" : "L16";
  @"L15":
    %"v21" = %"v0" +p #160;
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v21";
    store.ptr [%"chk1" + 0] <- %"v6";
    %"chk2" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v26" = %"v25" +p #48;
    %"chk3" : A = (Check 0 8 Write 8) %"v26";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v30" = %"v29" +p #56;
    %"chk5" : A = (Check 0 8 Write 8) %"v30";
    store.ptr [%"chk5" + 0] <- #0;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v34" = %"v33" +p #16;
    %"chk7" : A = (Check 0 8 Write 8) %"v34";
    store.ptr [%"chk7" + 0] <- #0;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Write 8) %"v37";
    store.ptr [%"chk9" + 0] <- #0;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v41" = %"v40" +p #8;
    %"chk11" : A = (Check 0 8 Write 8) %"v41";
    store.ptr [%"chk11" + 0] <- #0;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v45" = %"v44" +p #24;
    %"chk13" : A = (Check 0 8 Write 8) %"v45";
    store.ptr [%"chk13" + 0] <- #0;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v49" = %"v48" +p #32;
    %"chk15" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk15" + 0] <- #0;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v53" = %"v52" +p #40;
    %"chk17" : A = (Check 0 8 Write 8) %"v53";
    store.ptr [%"chk17" + 0] <- #0;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v57" = %"v56" +p #64;
    %"chk19" : A = (Check 0 8 Write 8) %"v57";
    store.ptr [%"chk19" + 0] <- #0;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v61" = %"v60" +p #72;
    %"chk21" : A = (Check 0 8 Write 8) %"v61";
    store.ptr [%"chk21" + 0] <- #0;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v65" = %"v64" +p #80;
    %"chk23" : A = (Check 0 8 Write 8) %"v65";
    store.ptr [%"chk23" + 0] <- #0;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v69" = %"v68" +p #224;
    %"chk25" : A = (Check 0 8 Write 8) %"v69";
    store.ptr [%"chk25" + 0] <- %"v8"
    => goto "L17";
  @"L16":
    %"v72" = %"v0" +p #160;
    (Flight (a "v74") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk26" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v72";
    store.ptr [%"chk26" + 0] <- %"v74"
    => goto "L17";
  @"L17":
    %"v76" = %"v0" +p #168;
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v76";
    store.ptr [%"chk27" + 0] <- #0;
    %"v78" = %"v0" +p #200;
    %"chk28" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v78";
    store Wl [%"chk28" + 0] <- #0
    => ret void
} }.

Definition fn__IO_old_init : func :=
  ir_fn{ "export" "_IO_old_init"(P %"v0", W %"v2") -> RVoid {
  @"start":
    alloca "v72" 16;
    %"v6" : W = Or %"v2", #4222418944;
    %"chk0" : A = (Check 0 4 Write 1) %"v0";
    store Ww [%"chk0" + 0] <- %"v6";
    %"v8" = %"v0" +p #116;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v10" : W = And %"v9", #4278190080;
    store Ww [%"chk1" + 0] <- %"v10";
    %"v18" : P = Copy $"glibc_genops#stdio_needs_locking";
    %"chk3" : A = (Check 0 4 Read 1) %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk3"
    => br %"v19" ? "L15" : "L17";
  @"L15":
    %"v21" = %"v0" +p #116;
    %"chk4" : A = (Renew 0 4 Read 1) %"chk1", %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v23" : W = Shl %"v22", #8;
    %"v24" : W = Sar %"v23", #8;
    %"v25" : W = Or %"v24", #128;
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v27" : W = And %"v26", #4278190080;
    %"v28" : W = And %"v25", #16777215;
    %"v29" : W = Or %"v27", %"v28";
    %"chk6" : A = (Renew 0 4 Write 1) %"chk1", %"v21";
    store Ww [%"chk6" + 0] <- %"v29"
    => goto "L17";
  @"L17":
    %"v33" = %"v0" +p #56;
    %"chk7" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v33";
    store.ptr [%"chk7" + 0] <- #0;
    %"v35" = %"v0" +p #64;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v35";
    store.ptr [%"chk8" + 0] <- #0;
    %"v37" = %"v0" +p #24;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v37";
    store.ptr [%"chk9" + 0] <- #0;
    %"v39" = %"v0" +p #8;
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v39";
    store.ptr [%"chk10" + 0] <- #0;
    %"v41" = %"v0" +p #16;
    %"chk11" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v41";
    store.ptr [%"chk11" + 0] <- #0;
    %"v43" = %"v0" +p #32;
    %"chk12" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v43";
    store.ptr [%"chk12" + 0] <- #0;
    %"v45" = %"v0" +p #40;
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v45";
    store.ptr [%"chk13" + 0] <- #0;
    %"v47" = %"v0" +p #48;
    %"chk14" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v47";
    store.ptr [%"chk14" + 0] <- #0;
    %"v49" = %"v0" +p #104;
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v49";
    store.ptr [%"chk15" + 0] <- #0;
    %"v51" = %"v0" +p #72;
    %"chk16" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v51";
    store.ptr [%"chk16" + 0] <- #0;
    %"v53" = %"v0" +p #80;
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v53";
    store.ptr [%"chk17" + 0] <- #0;
    %"v55" = %"v0" +p #88;
    %"chk18" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v55";
    store.ptr [%"chk18" + 0] <- #0;
    %"v57" = %"v0" +p #96;
    %"chk19" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v57";
    store.ptr [%"chk19" + 0] <- #0;
    %"v59" = %"v0" +p #128;
    %"chk20" : A = (HalfCheck Upper 0 2 Write 1) %"chk0", %"v59";
    store Wh [%"chk20" + 0] <- #0;
    %"v64" = %"v0" +p #136;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v66" : L = Ptoi %"v65";
    %"v67" : L = Ptoi #0;
    %"v68" : W = (Cmp Ne L) %"v66", %"v67"
    => br %"v68" ? "L60" : "L62";
  @"L60":
    %"v70" = %"v0" +p #136;
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk23" : A = (CheckLocal (a "v72") 0 8 Write 1);
    store Wl [%"chk23" + 0] <- #0;
    %"chk24" : A = (CheckLocal (a "v72") 8 8 Write 1);
    store Wl [%"chk24" + 0] <- #0;
    %"chk25" : A = (CheckLocal (a "v72") 0 4 Write 1);
    store Ww [%"chk25" + 0] <- #0;
    %"chk26" : A = (CheckLocal (a "v72") 4 4 Write 1);
    store Ww [%"chk26" + 0] <- #0;
    %"chk27" : A = (CheckLocal (a "v72") 8 8 Write 8);
    (RawStorePointer 0 (Const 0) (t "chk27") [LowerWrite; AddressWrite]);
    %"chk28" : A = (CheckLocal (a "v72") 0 8 Read 1);
    %"v76" : L = (RawLoad LdL 0) %"chk28";
    %"chk29" : A = (Check 0 8 Write 1) %"v71";
    store Wl [%"chk29" + 0] <- %"v76";
    %"v78" = %"v71" +p #8;
    %"chk30" : A = (CheckLocal (a "v72") 8 8 Read 8);
    %"v79" : P = (RawLoadPointer 0 local_load_effects) %"chk30";
    %"chk31" : A = (HalfCheck Upper 0 8 Write 8) %"chk29", %"v78";
    store.ptr [%"chk31" + 0] <- %"v79"
    => goto "L62";
  @"L62":
    => ret void
} }.

Definition fn__IO_switch_to_backup_area : func :=
  ir_fn{ "export" "_IO_switch_to_backup_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v5" : W = Or %"v4", #256;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk1" + 0] <- %"v5";
    %"v7" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v12" = %"v0" +p #88;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Write 8) %"chk2", %"v7";
    store.ptr [%"chk4" + 0] <- %"v13";
    %"chk5" : A = (Renew 0 8 Write 8) %"chk3", %"v12";
    store.ptr [%"chk5" + 0] <- %"v8";
    %"v18" = %"v0" +p #24;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v23" = %"v0" +p #72;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk6", %"v18";
    store.ptr [%"chk8" + 0] <- %"v24";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk7", %"v23";
    store.ptr [%"chk9" + 0] <- %"v19";
    %"v29" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk2", %"v7";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v29";
    store.ptr [%"chk11" + 0] <- %"v32"
    => ret void
} }.

Definition fn__IO_switch_to_main_get_area : func :=
  ir_fn{ "export" "_IO_switch_to_main_get_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v6" : W = And %"v4", #4294967039;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk1" + 0] <- %"v6";
    %"v8" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v13" = %"v0" +p #88;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Write 8) %"chk2", %"v8";
    store.ptr [%"chk4" + 0] <- %"v14";
    %"chk5" : A = (Renew 0 8 Write 8) %"chk3", %"v13";
    store.ptr [%"chk5" + 0] <- %"v9";
    %"v19" = %"v0" +p #24;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v24" = %"v0" +p #72;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk6", %"v19";
    store.ptr [%"chk8" + 0] <- %"v25";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk7", %"v24";
    store.ptr [%"chk9" + 0] <- %"v20";
    %"v30" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk6", %"v19";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v30";
    store.ptr [%"chk11" + 0] <- %"v33"
    => ret void
} }.

Definition fn___GI__IO_adjust_column : func :=
  ir_fn{ "export" "__GI__IO_adjust_column"(W %"v0", P %"v2", W %"v4") -> (RClass W) {
  @"start":
    %"v9" : L = (Ext Sw) %"v4";
    %"v10" = %"v2" +p %"v9"
    => goto "L11";
  @"L11" [%"pr.1" : P = phi("start" => %"v10", "L12" => %"v23")]:
    %"v16" : L = Ptoi %"pr.1";
    %"v17" : L = Ptoi %"v2";
    %"v18" : W = (Cmp Ugt L) %"v16", %"v17"
    => br %"v18" ? "L12" : "L13";
  @"L12":
    (Flight (a "v23") Sub [(FAddress (t "pr.1")); (FValue (Const 1))] (LowerOf (t "pr.1")));
    %"chk0" : A = (Check 0 1 Read 1) %"v23";
    %"v24" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v25" : W = (Cmp Eq W) %"v24", #10
    => br %"v25" ? "L19" : poll "L11";
  @"L19":
    %"v31" : L = Ptoi %"v10";
    %"v32" : L = Ptoi %"v23";
    %"v33" : L = Sub %"v31", %"v32";
    %"v34" : L = Sub %"v33", #1
    => ret %"v34";
  @"L13":
    %"v38" : W = Add %"v0", %"v4"
    => ret %"v38"
} }.

Definition fn___GI__IO_default_doallocate : func :=
  ir_fn{ "export" "__GI__IO_default_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    call %"v3" : P = $"malloc"(L #8192);
    %"v8" : L = Ptoi %"v3";
    %"v9" : L = Ptoi #0;
    %"v10" : W = (Cmp Eq L) %"v8", %"v9"
    => br %"v10" ? "L4" : "L6";
  @"L4":
    => ret #4294967295;
  @"L6":
    %"v18" = %"v3" +p #8192;
    call void $"__GI__IO_setb"(P %"v0", P %"v3", P %"v18", W #1)
    => ret #1
} }.

Definition fn___GI__IO_default_finish : func :=
  ir_fn{ "export" "__GI__IO_default_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v9" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" : L = Ptoi %"v10";
    %"v12" : W = (Cmp Ne L) %"v11", #0
    => br %"v12" ? "L13" : "L14";
  @"L13":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v17" : W = And %"v16", #1;
    %"v18" : W = (Cmp Eq W) %"v17", #0
    => goto "L14";
  @"L14" [%"v20" : W = phi("start" => #0, "L13" => %"v18")]:
    => br %"v20" ? "L5" : "L7";
  @"L5":
    %"v22" = %"v0" +p #56;
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"free"(P %"v23");
    %"v27" = %"v0" +p #64;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v27";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk0", %"v22";
    store.ptr [%"chk4" + 0] <- #0
    => goto "L7";
  @"L7":
    %"v29" = %"v0" +p #96;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5"
    => goto "L31";
  @"L31" [%"pr.1" : P = phi("L32" => %"v42", "L7" => %"v30")]:
    %"v36" : L = Ptoi %"pr.1";
    %"v37" : L = Ptoi #0;
    %"v38" : W = (Cmp Ne L) %"v36", %"v37"
    => br %"v38" ? "L32" : "L34";
  @"L32":
    %"v40" = %"pr.1" +p #8;
    %"chk6" : A = (Check 0 8 Write 8) %"v40";
    store.ptr [%"chk6" + 0] <- #0;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk6", %"pr.1";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk7"
    => goto poll "L31";
  @"L34":
    %"v47" = %"v0" +p #80;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v49" : L = Ptoi %"v48";
    %"v51" : W = (Cmp Ne L) %"v49", %"v37"
    => br %"v51" ? "L43" : "L45";
  @"L43":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L45";
  @"L45":
    call void $"__GI__IO_un_link"(P %"v0");
    %"v58" = %"v0" +p #136;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v60" : L = Ptoi %"v59";
    %"v62" : W = (Cmp Ne L) %"v60", %"v37"
    => br %"v62" ? "L56" : "L55";
  @"L55":
    => goto "L56";
  @"L56":
    => ret void
} }.

Definition fn___GI__IO_default_pbackfail : func :=
  ir_fn{ "export" "__GI__IO_default_pbackfail"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ugt L) %"v13", %"v14"
    => br %"v15" ? "L16" : "L17";
  @"L16":
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v20" : W = And %"v19", #256;
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => goto "L17";
  @"L17" [%"v23" : W = phi("start" => #0, "L16" => %"v21")]:
    => br %"v23" ? "L24" : "L25";
  @"L24":
    %"v27" = %"v0" +p #8;
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v31" = %"v28" +p #18446744073709551615;
    %"chk4" : A = (Check 0 1 Read 1) %"v31";
    %"v32" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v33" : W = (Ext Ub) %"v32";
    %"v35" : W = (Cmp Eq W) %"v33", %"v2"
    => goto "L25";
  @"L25" [%"v37" : W = phi("L17" => #0, "L24" => %"v35")]:
    => br %"v37" ? "L4" : "L5";
  @"L4":
    %"v39" = %"v0" +p #8;
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk0";
    (Flight (a "v41") Sub [(FAddress (t "v40")); (FValue (Const 1))] (LowerOf (t "v40")));
    %"chk6" : A = (Renew 0 8 Write 8) %"chk0", %"v39";
    store.ptr [%"chk6" + 0] <- %"v41"
    => goto "L6";
  @"L5":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v46" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v47" : W = And %"v46", #256;
    %"v48" : W = (Cmp Eq W) %"v47", #0
    => br %"v48" ? "L42" : "L43";
  @"L42":
    %"v53" = %"v0" +p #8;
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v56" = %"v0" +p #24;
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v58" : L = Ptoi %"v54";
    %"v59" : L = Ptoi %"v57";
    %"v60" : W = (Cmp Ugt L) %"v58", %"v59"
    => br %"v60" ? "L61" : "L62";
  @"L61":
    %"v64" = %"v0" +p #80;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v66" : L = Ptoi %"v65";
    %"v67" : L = Ptoi #0;
    %"v68" : W = (Cmp Ne L) %"v66", %"v67"
    => goto "L62";
  @"L62" [%"v70" : W = phi("L42" => #0, "L61" => %"v68")]:
    => br %"v70" ? "L49" : "L50";
  @"L49":
    %"v76" = %"v0" +p #8;
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v78" : W = $"glibc_genops#save_for_backup"(P %"v0", P %"v77")
    => br %"v78" ? "L71" : "L51";
  @"L71":
    => ret #4294967295;
  @"L50":
    %"v85" = %"v0" +p #80;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v85";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v87" : L = Ptoi %"v86";
    %"v88" : L = Ptoi #0;
    %"v90" : W = (Cmp Eq L) %"v87", %"v88"
    => br %"v90" ? "L81" : "L51";
  @"L81":
    call %"v95" : P = $"malloc"(L #128);
    %"v100" : L = Ptoi %"v95";
    %"v102" : W = (Cmp Eq L) %"v100", %"v88"
    => br %"v102" ? "L96" : "L98";
  @"L96":
    %"v104" = %"v0" +p #119
    => goto "L98";
  @"L98" [%"pr.2" : P = phi("L96" => %"v104", "L81" => %"v95"); %"pr.1" : W = phi("L96" => #1, "L81" => #128)]:
    %"v106" = %"v0" +p #72;
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v106";
    store.ptr [%"chk13" + 0] <- %"pr.2";
    %"v109" = %"v0" +p #88;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk13", %"v106";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v114" : L = (Ext Sw) %"pr.1";
    %"v115" = %"v112" +p %"v114";
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v109";
    store.ptr [%"chk15" + 0] <- %"v115";
    %"v117" = %"v0" +p #80;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk15", %"v109";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Renew 0 8 Write 8) %"chk12", %"v117";
    store.ptr [%"chk17" + 0] <- %"v120"
    => goto "L51";
  @"L51":
    %"v122" = %"v0" +p #24;
    %"v124" = %"v0" +p #8;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (Renew 0 8 Write 8) %"chk1", %"v122";
    store.ptr [%"chk19" + 0] <- %"v125";
    call void $"_IO_switch_to_backup_area"(P %"v0")
    => goto "L44";
  @"L43":
    %"v131" = %"v0" +p #8;
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v134" = %"v0" +p #24;
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v136" : L = Ptoi %"v132";
    %"v137" : L = Ptoi %"v135";
    %"v138" : W = (Cmp Ule L) %"v136", %"v137"
    => br %"v138" ? "L127" : "L44";
  @"L127":
    %"v142" = %"v0" +p #16;
    %"v143" : P = (RawLoadPointer (-8) load_effects) %"chk1";
    %"v145" = %"v0" +p #24;
    %"v146" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v147" : L = Ptoi %"v143";
    %"v148" : L = Ptoi %"v146";
    %"v149" : L = Sub %"v147", %"v148";
    %"v152" : L = Shl %"v149", #1;
    call %"v154" : P = $"malloc"(L %"v152");
    %"v159" : L = Ptoi %"v154";
    %"v160" : L = Ptoi #0;
    %"v161" : W = (Cmp Eq L) %"v159", %"v160"
    => br %"v161" ? "L155" : "L157";
  @"L155":
    => ret #4294967295;
  @"L157":
    %"v167" : L = Sub %"v152", %"v149";
    %"v168" = %"v154" +p %"v167";
    %"v170" = %"v0" +p #24;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk1", %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk24";
    call %"v173" : P = $"__GI_memcpy"(P %"v168", P %"v171", L %"v149");
    %"chk25" : A = (Renew 0 8 Read 8) %"chk1", %"v170";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v177";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    call void $"free"(P %"v177")
    => goto "iw_1.join";
  @"iw_1.join":
    %"v179" = %"v0" +p #24;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk1", %"v179";
    store.ptr [%"chk26" + 0] <- %"v154";
    %"v182" = %"v0" +p #8;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk0", %"v182";
    store.ptr [%"chk27" + 0] <- %"v168";
    %"v189" = %"v0" +p #16;
    %"v192" = %"v154" +p %"v152";
    %"chk28" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v189";
    store.ptr [%"chk28" + 0] <- %"v192";
    %"v194" = %"v0" +p #80;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v182";
    %"v197" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v194";
    store.ptr [%"chk30" + 0] <- %"v197"
    => goto "L44";
  @"L44":
    %"v199" = %"v0" +p #8;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk0", %"v199";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk31";
    (Flight (a "v201") Sub [(FAddress (t "v200")); (FValue (Const 1))] (LowerOf (t "v200")));
    %"chk32" : A = (Renew 0 8 Write 8) %"chk0", %"v199";
    store.ptr [%"chk32" + 0] <- %"v201";
    %"v203" : W = (Ext Sb) %"v2";
    %"chk33" : A = (Check 0 1 Write 1) %"v201";
    store Wb [%"chk33" + 0] <- %"v203"
    => goto "L6";
  @"L6":
    %"v205" : W = (Ext Ub) %"v2"
    => ret %"v205"
} }.

Definition fn___GI__IO_default_uflow : func :=
  ir_fn{ "export" "__GI__IO_default_uflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v4" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v5";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v7" = %"v5" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v8";
    rawcall %"v10" : W = %"chk2"(P %"v0");
    %"v16" : W = (Cmp Eq W) %"v10", #4294967295
    => br %"v16" ? "L11" : "L13";
  @"L11":
    => ret #4294967295;
  @"L13":
    %"v20" = %"v0" +p #8;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v22" = %"v21" +p #1;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk3", %"v20";
    store.ptr [%"chk4" + 0] <- %"v22";
    %"chk5" : A = (Check 0 1 Read 1) %"v21";
    %"v23" : W = (RawLoad (LdNarrow Ub) 0) %"chk5"
    => ret %"v23"
} }.

Definition fn___GI__IO_default_xsgetn : func :=
  ir_fn{ "export" "__GI__IO_default_xsgetn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => goto "L10";
  @"L10" [%"pr.3" : P = phi("start" => %"v2", "L93" => %"pr.4"); %"pr.1" : L = phi("start" => %"v4", "L93" => %"pr.2")]:
    %"v18" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v21" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v23" : L = Ptoi %"v19";
    %"v24" : L = Ptoi %"v22";
    %"v25" : W = (Cmp Ult L) %"v23", %"v24"
    => br %"v25" ? "L14" : "L16";
  @"L14":
    %"v28" = %"v0" +p #16;
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v31" = %"v0" +p #8;
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v33" : L = Ptoi %"v29";
    %"v34" : L = Ptoi %"v32";
    %"v35" : L = Sub %"v33", %"v34";
    %"v41" : W = (Cmp Ugt L) %"v35", %"pr.1"
    => br %"v41" ? "L38" : "L37";
  @"L37":
    => goto "L38";
  @"L38" [%"pr.8" : L = phi("L37" => %"v35", "L14" => %"pr.1")]:
    %"v47" : W = (Cmp Ugt L) %"pr.8", #20
    => br %"v47" ? "L43" : "L44";
  @"L43":
    %"v50" = %"v0" +p #8;
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v53" : P = $"__GI_mempcpy"(P %"pr.3", P %"v51", L %"pr.8");
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v50";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v58" = %"v56" +p %"pr.8";
    %"chk6" : A = (Renew 0 8 Write 8) %"chk0", %"v50";
    store.ptr [%"chk6" + 0] <- %"v58"
    => goto "L45";
  @"L44":
    %"v63" : W = (Cmp Ne L) %"pr.8", #0
    => br %"v63" ? "L59" : "L45";
  @"L59":
    %"v66" = %"v0" +p #8;
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L70";
  @"L70" [%"pr.10" : W = phi("L59" => %"pr.8", "L71" => %"v74"); %"pr.9" : P = phi("L59" => %"v67", "L71" => %"v79"); %"pr.7" : P = phi("L59" => %"pr.3", "L71" => %"v77")]:
    %"v74" : W = Sub %"pr.10", #1;
    %"v75" : W = (Cmp Sge W) %"v74", #0
    => br %"v75" ? "L71" : "L72";
  @"L71":
    %"v77" = %"pr.7" +p #1;
    %"v79" = %"pr.9" +p #1;
    %"chk8" : A = (Check 0 1 Read 1) %"pr.9";
    %"v80" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"chk9" : A = (Check 0 1 Write 1) %"pr.7";
    store Wb [%"chk9" + 0] <- %"v80"
    => goto poll "L70";
  @"L72":
    %"v82" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Write 8) %"chk0", %"v82";
    store.ptr [%"chk10" + 0] <- %"pr.9"
    => goto "L45";
  @"L45" [%"pr.5" : P = phi("L43" => %"v53", "L72" => %"pr.7", "L44" => %"pr.3")]:
    %"v86" : L = Sub %"pr.1", %"pr.8"
    => goto "L16";
  @"L16" [%"pr.4" : P = phi("L45" => %"pr.5", "L10" => %"pr.3"); %"pr.2" : L = phi("L45" => %"v86", "L10" => %"pr.1")]:
    %"v91" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v91" ? "L93" : "L92";
  @"L92":
    call %"v95" : W = $"__GI___underflow"(P %"v0");
    %"v97" : W = (Cmp Eq W) %"v95", #4294967295
    => goto "L93";
  @"L93" [%"v99" : W = phi("L16" => #1, "L92" => %"v97")]:
    => br %"v99" ? "L13" : poll "L10";
  @"L13":
    %"v103" : L = Sub %"v4", %"pr.2"
    => ret %"v103"
} }.

Definition fn___GI__IO_default_xsputn : func :=
  ir_fn{ "export" "__GI__IO_default_xsputn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v14" : W = (Cmp Ule L) %"v4", #0
    => br %"v14" ? "L10" : "L16";
  @"L10":
    => ret #0;
  @"L16" [%"pr.7" : L = phi("start" => %"v4", "L96" => %"v119"); %"pr.2" : P = phi("start" => %"v2", "L96" => %"pr.1")]:
    %"v24" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v27" = %"v0" +p #48;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v29" : L = Ptoi %"v25";
    %"v30" : L = Ptoi %"v28";
    %"v31" : W = (Cmp Ult L) %"v29", %"v30"
    => br %"v31" ? "L20" : "L22";
  @"L20":
    %"v34" = %"v0" +p #48;
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v37" = %"v0" +p #40;
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v39" : L = Ptoi %"v35";
    %"v40" : L = Ptoi %"v38";
    %"v41" : L = Sub %"v39", %"v40";
    %"v47" : W = (Cmp Ugt L) %"v41", %"pr.7"
    => br %"v47" ? "L44" : "L43";
  @"L43":
    => goto "L44";
  @"L44" [%"pr.9" : L = phi("L43" => %"v41", "L20" => %"pr.7")]:
    %"v53" : W = (Cmp Ugt L) %"pr.9", #20
    => br %"v53" ? "L49" : "L50";
  @"L49":
    %"v55" = %"v0" +p #40;
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v61" : P = $"__GI_mempcpy"(P %"v58", P %"pr.2", L %"pr.9");
    %"chk5" : A = (Renew 0 8 Write 8) %"chk0", %"v55";
    store.ptr [%"chk5" + 0] <- %"v61";
    %"v64" = %"pr.2" +p %"pr.9"
    => goto "L51";
  @"L50":
    %"v69" : W = (Cmp Ne L) %"pr.9", #0
    => br %"v69" ? "L65" : "L51";
  @"L65":
    %"v72" = %"v0" +p #40;
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L76";
  @"L76" [%"pr.11" : L = phi("L65" => %"pr.9", "L77" => %"v81"); %"pr.10" : P = phi("L65" => %"v73", "L77" => %"v84"); %"pr.6" : P = phi("L65" => %"pr.2", "L77" => %"v86")]:
    %"v81" : L = Sub %"pr.11", #1;
    %"v82" : W = (Cmp Sge L) %"v81", #0
    => br %"v82" ? "L77" : "L79";
  @"L77":
    %"v84" = %"pr.10" +p #1;
    %"v86" = %"pr.6" +p #1;
    %"chk7" : A = (Check 0 1 Read 1) %"pr.6";
    %"v87" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"chk8" : A = (Check 0 1 Write 1) %"pr.10";
    store Wb [%"chk8" + 0] <- %"v87"
    => goto poll "L76";
  @"L79":
    %"v89" = %"v0" +p #40;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk0", %"v89";
    store.ptr [%"chk9" + 0] <- %"pr.10"
    => goto "L51";
  @"L51" [%"pr.4" : P = phi("L49" => %"v64", "L79" => %"pr.6", "L50" => %"pr.2")]:
    %"v93" : L = Sub %"pr.7", %"pr.9"
    => goto "L22";
  @"L22" [%"pr.8" : L = phi("L51" => %"v93", "L16" => %"pr.7"); %"pr.3" : P = phi("L51" => %"pr.4", "L16" => %"pr.2")]:
    %"v98" : W = (Cmp Eq L) %"pr.8", #0
    => br %"v98" ? "L100" : "L99";
  @"L99":
    %"v102" = %"v0" +p #216;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v102";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v4" : L = Ptoi %"v103";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v105" = %"v103" +p #24;
    %"chk11" : A = (Check 0 8 Read 8) %"v105";
    %"v106" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v109" = %"pr.3" +p #1;
    %"chk12" : A = (Check 0 1 Read 1) %"pr.3";
    %"v110" : W = (RawLoad (LdNarrow Sb) 0) %"chk12";
    %"v111" : W = (Ext Ub) %"v110";
    %"chk13" : F = CheckFunction %"v106";
    rawcall %"v112" : W = %"chk13"(P %"v0", W %"v111");
    %"v114" : W = (Cmp Eq W) %"v112", #4294967295
    => goto "L100";
  @"L100" [%"v116" : W = phi("L22" => #1, "iw_1.join" => %"v114"); %"pr.1" : P = phi("L22" => %"pr.3", "iw_1.join" => %"v109")]:
    => br %"v116" ? "L19" : "L96";
  @"L96":
    %"v119" : L = Sub %"pr.8", #1
    => goto poll "L16";
  @"L19":
    %"v122" : L = Sub %"v4", %"pr.8"
    => ret %"v122"
} }.

Definition fn___GI__IO_doallocbuf : func :=
  ir_fn{ "export" "__GI__IO_doallocbuf"(P %"v0") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" : L = Ptoi %"v7";
    %"v9" : W = (Cmp Ne L) %"v8", #0
    => br %"v9" ? "L2" : "L4";
  @"L2":
    => ret void;
  @"L4":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v15" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v16" : W = And %"v15", #2;
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => br %"v17" ? "L19" : "L18";
  @"L18":
    %"v21" = %"v0" +p #192;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v23" : W = (Cmp Sgt W) %"v22", #0
    => goto "L19";
  @"L19" [%"v25" : W = phi("L4" => #1, "L18" => %"v23")]:
    => br %"v25" ? "L11" : "L13";
  @"L11":
    %"v30" = %"v0" +p #216;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v4" : L = Ptoi %"v31";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v33" = %"v31" +p #104;
    %"chk4" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : F = CheckFunction %"v34";
    rawcall %"v36" : W = %"chk5"(P %"v0");
    %"v38" : W = (Cmp Ne W) %"v36", #4294967295
    => br %"v38" ? "L26" : "L13";
  @"L26":
    => ret void;
  @"L13":
    %"v42" = %"v0" +p #131;
    %"v45" = %"v42" +p #1;
    call void $"__GI__IO_setb"(P %"v0", P %"v42", P %"v45", W #0)
    => ret void
} }.

Definition fn___GI__IO_flush_all : func :=
  ir_fn{ "export" "__GI__IO_flush_all"() -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v3" : P = (Alloc 8) #32;
    %"v5" : P = Copy $"glibc_genops#flush_cleanup";
    %"v6" = %"v3" +p #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v6";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v3";
    store.ptr [%"chk1" + 0] <- %"v5";
    call void $"__GI___libc_cleanup_push_defer"(P %"v3");
    call %"v17" : P = $"zthread_self_cookie"();
    %"v21" : P = Copy $"__libc_single_threaded_internal";
    %"chk2" : A = (Check 0 1 Read 1) %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v23" : W = (Cmp Ne W) %"v22", #0
    => br %"v23" ? "L24" : "L25" };
  ir_blk{ @"L24":
    %"v26" : P = Copy $"glibc_genops#list_all_lock";
    %"v27" = %"v26" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v29" : L = Ptoi %"v28";
    %"v30" : L = Ptoi #0;
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => goto "L25" };
  ir_blk{ @"L25" [%"v33" : W = phi("start" => #0, "L24" => %"v31")]:
    => br %"v33" ? "L18" : "L19" };
  ir_blk{ @"L18":
    %"v34" : P = Copy $"glibc_genops#list_all_lock";
    %"chk4" : A = (Check 0 4 Write 1) %"v34";
    store Ww [%"chk4" + 0] <- #1;
    %"v35" : P = Copy $"glibc_genops#list_all_lock";
    %"v36" = %"v35" +p #8;
    %"chk5" : A = (Check 0 8 Write 8) %"v36";
    store.ptr [%"chk5" + 0] <- %"v17"
    => goto "L15" };
  ir_blk{ @"L19":
    %"v41" : P = Copy $"glibc_genops#list_all_lock";
    %"v42" = %"v41" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v45" : L = Ptoi %"v43";
    %"v46" : L = Ptoi %"v17";
    %"v47" : W = (Cmp Ne L) %"v45", %"v46"
    => br %"v47" ? "L38" : "L39" };
  ir_blk{ @"L38":
    %"v49" : P = Copy $"glibc_genops#list_all_lock";
    %"chk7" : A = (Check 0 4 Write 4) %"v49";
    %"v56" : W = (RawCas (CasNarrow Sw) 0) %"chk7", #0, #1;
    %"v57" : W = (Cmp Eq W) %"v56", #0
    => br %"v57" ? "L59" : "L58" };
  ir_blk{ @"L58":
    => goto "L59" };
  ir_blk{ @"L59":
    %"v60" : W = (Cmp Ne W) %"v56", #0
    => br %"v60" ? "L63" : "L52" };
  ir_blk{ @"L63":
    call void $"__GI___lll_lock_wait_private"(P %"v49")
    => goto "L52" };
  ir_blk{ @"L52":
    %"v73" : P = Copy $"glibc_genops#list_all_lock";
    %"v74" = %"v73" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"v74";
    store.ptr [%"chk8" + 0] <- %"v17"
    => goto "L15" };
  ir_blk{ @"L39":
    %"v76" : P = Copy $"glibc_genops#list_all_lock";
    %"v77" = %"v76" +p #4;
    %"chk9" : A = (Check 0 4 Read 1) %"v77";
    %"v78" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v79" : W = Add %"v78", #1;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk9", %"v77";
    store Ww [%"chk10" + 0] <- %"v79"
    => goto "L15" };
  ir_blk{ @"L15":
    %"v80" : P = Copy $"__GI__IO_list_all";
    %"chk11" : A = (Check 0 8 Read 8) %"v80";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto "L82" };
  ir_blk{ @"L82" [%"pr.5" : P = phi("L15" => %"v81", "L329" => %"v413"); %"pr.4" : W = phi("L15" => #0, "L329" => %"pr.1")]:
    %"v87" : L = Ptoi %"pr.5";
    %"v88" : L = Ptoi #0;
    %"v89" : W = (Cmp Ne L) %"v87", %"v88"
    => br %"v89" ? "L83" : "L414" };
  ir_blk{ @"L83":
    %"v90" : P = Copy $"glibc_genops#run_fp";
    %"chk12" : A = (Check 0 8 Write 8) %"v90";
    store.ptr [%"chk12" + 0] <- %"pr.5";
    %"chk13" : A = (Check 0 4 Read 1) %"pr.5";
    %"v96" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v97" : W = And %"v96", #32768;
    %"v98" : W = (Cmp Eq W) %"v97", #0
    => br %"v98" ? "L99" : "L94" };
  ir_blk{ @"L99":
    call %"v103" : P = $"zthread_self_cookie"();
    %"v107" : P = Copy $"__libc_single_threaded_internal";
    %"chk14" : A = (Check 0 1 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v109" : W = (Cmp Ne W) %"v108", #0
    => br %"v109" ? "L110" : "L111" };
  ir_blk{ @"L110":
    %"v113" = %"pr.5" +p #136;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v115" = %"v114" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"v115";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v117" : L = Ptoi %"v116";
    %"v119" : W = (Cmp Eq L) %"v117", %"v88"
    => goto "L111" };
  ir_blk{ @"L111" [%"v121" : W = phi("L99" => #0, "L110" => %"v119")]:
    => br %"v121" ? "L104" : "L105" };
  ir_blk{ @"L104":
    %"v123" = %"pr.5" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v123";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Write 1) %"v124";
    store Ww [%"chk18" + 0] <- #1;
    %"v127" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v128" = %"v127" +p #8;
    %"chk20" : A = (Check 0 8 Write 8) %"v128";
    store.ptr [%"chk20" + 0] <- %"v103"
    => goto "L94" };
  ir_blk{ @"L105":
    %"v134" = %"pr.5" +p #136;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v136" = %"v135" +p #8;
    %"chk22" : A = (Check 0 8 Read 8) %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v139" : L = Ptoi %"v137";
    %"v140" : L = Ptoi %"v103";
    %"v141" : W = (Cmp Ne L) %"v139", %"v140"
    => br %"v141" ? "L130" : "L131" };
  ir_blk{ @"L130":
    %"v144" = %"pr.5" +p #136;
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 4 Write 4) %"v145";
    %"v152" : W = (RawCas (CasNarrow Sw) 0) %"chk24", #0, #1;
    %"v153" : W = (Cmp Eq W) %"v152", #0
    => br %"v153" ? "L155" : "L154" };
  ir_blk{ @"L154":
    => goto "L155" };
  ir_blk{ @"L155":
    %"v156" : W = (Cmp Ne W) %"v152", #0
    => br %"v156" ? "L159" : "L148" };
  ir_blk{ @"L159":
    call void $"__GI___lll_lock_wait_private"(P %"v145")
    => goto "L148" };
  ir_blk{ @"L148":
    %"v170" = %"pr.5" +p #136;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk21", %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v172" = %"v171" +p #8;
    %"chk26" : A = (Check 0 8 Write 8) %"v172";
    store.ptr [%"chk26" + 0] <- %"v103"
    => goto "L94" };
  ir_blk{ @"L131":
    %"v175" = %"pr.5" +p #136;
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v177" = %"v176" +p #4;
    %"chk28" : A = (Check 0 4 Read 1) %"v177";
    %"v178" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v179" : W = Add %"v178", #1;
    %"chk29" : A = (Renew 0 4 Write 1) %"chk28", %"v177";
    store Ww [%"chk29" + 0] <- %"v179"
    => goto "L94" };
  ir_blk{ @"L94":
    %"v184" = %"pr.5" +p #116;
    %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk13", %"v184";
    %"v185" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v186" : W = Shl %"v185", #8;
    %"v187" : W = Sar %"v186", #8;
    %"v188" : W = And %"v187", #32;
    %"v189" : W = (Cmp Eq W) %"v188", #0
    => br %"v189" ? "L180" : "L182" };
  ir_blk{ @"L180":
    %"v194" = %"pr.5" +p #192;
    %"chk31" : A = (HalfCheck Upper 0 4 Read 1) %"chk13", %"v194";
    %"v195" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v196" : W = (Cmp Sle W) %"v195", #0
    => br %"v196" ? "L197" : "L198" };
  ir_blk{ @"L197":
    %"v200" = %"pr.5" +p #40;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v200";
    %"v201" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v203" = %"pr.5" +p #32;
    %"chk33" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v203";
    %"v204" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v205" : L = Ptoi %"v201";
    %"v206" : L = Ptoi %"v204";
    %"v207" : W = (Cmp Ugt L) %"v205", %"v206"
    => goto "L198" };
  ir_blk{ @"L198" [%"v209" : W = phi("L180" => #0, "L197" => %"v207")]:
    => br %"v209" ? "L211" : "L213" };
  ir_blk{ @"L213":
    %"v216" = %"pr.5" +p #192;
    %"v217" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v218" : W = (Cmp Sgt W) %"v217", #0
    => br %"v218" ? "L221" : "L211" };
  ir_blk{ @"L221":
    %"v224" = %"pr.5" +p #160;
    %"chk35" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v224";
    %"v225" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v226" = %"v225" +p #32;
    %"chk36" : A = (Check 0 8 Read 8) %"v226";
    %"v227" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v230" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v231" = %"v230" +p #24;
    %"chk38" : A = (Check 0 8 Read 8) %"v231";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v233" : L = Ptoi %"v227";
    %"v234" : L = Ptoi %"v232";
    %"v235" : W = (Cmp Ugt L) %"v233", %"v234"
    => goto "L211" };
  ir_blk{ @"L211" [%"v239" : W = phi("L198" => #1, "L213" => #0, "L221" => %"v235")]:
    => br %"v239" ? "L240" : "L241" };
  ir_blk{ @"L240":
    %"v243" = %"pr.5" +p #216;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v243";
    %"v244" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"iw_1.v4" : L = Ptoi %"v244";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join" };
  ir_blk{ @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join":
    %"v246" = %"v244" +p #24;
    %"chk40" : A = (Check 0 8 Read 8) %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : F = CheckFunction %"v247";
    rawcall %"v250" : W = %"chk41"(P %"pr.5", W #4294967295);
    %"v252" : W = (Cmp Eq W) %"v250", #4294967295
    => goto "L241" };
  ir_blk{ @"L241" [%"v254" : W = phi("L211" => #0, "iw_1.join" => %"v252")]:
    => br %"v254" ? "L192" : "L191" }] [ir_blk{ @"L191":
    => goto "L192" };
  ir_blk{ @"L192" [%"pr.2" : W = phi("L191" => %"pr.4", "L241" => #4294967295)]:
    %"v260" = %"pr.5" +p #112;
    %"chk42" : A = (HalfCheck Upper 0 4 Read 1) %"chk13", %"v260";
    %"v261" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v262" : W = (Cmp Sge W) %"v261", #0
    => br %"v262" ? "L263" : "L264" };
  ir_blk{ @"L263":
    %"v266" = %"pr.5" +p #192;
    %"chk43" : A = (Renew 0 4 Read 1) %"chk31", %"v266";
    %"v267" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v268" : W = (Cmp Sle W) %"v267", #0
    => br %"v268" ? "L269" : "L270" };
  ir_blk{ @"L269":
    %"v272" = %"pr.5" +p #8;
    %"chk44" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v272";
    %"v273" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v275" = %"pr.5" +p #16;
    %"v276" : P = (RawLoadPointer 8 load_effects) %"chk44";
    %"v277" : L = Ptoi %"v273";
    %"v278" : L = Ptoi %"v276";
    %"v279" : W = (Cmp Ult L) %"v277", %"v278"
    => goto "L270" };
  ir_blk{ @"L270" [%"v281" : W = phi("L263" => #0, "L269" => %"v279")]:
    => br %"v281" ? "L264" : "L285" };
  ir_blk{ @"L285":
    %"v288" = %"pr.5" +p #192;
    %"v289" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v290" : W = (Cmp Sgt W) %"v289", #0
    => br %"v290" ? "L293" : "L264" };
  ir_blk{ @"L293":
    %"v296" = %"pr.5" +p #160;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v296";
    %"v297" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"chk48" : A = (Check 0 8 Read 8) %"v297";
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v301" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v302" = %"v301" +p #8;
    %"chk50" : A = (Check 0 8 Read 8) %"v302";
    %"v303" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v304" : L = Ptoi %"v298";
    %"v305" : L = Ptoi %"v303";
    %"v306" : W = (Cmp Ult L) %"v304", %"v305"
    => goto "L264" };
  ir_blk{ @"L264" [%"v312" : W = phi("L192" => #0, "L270" => #1, "L285" => #0, "L293" => %"v306")]:
    => br %"v312" ? "L313" : "L314" };
  ir_blk{ @"L313":
    %"v316" = %"pr.5" +p #216;
    %"chk51" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v316";
    %"v317" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"iw_2.v4" : L = Ptoi %"v317";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join" };
  ir_blk{ @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join":
    %"v319" = %"v317" +p #96;
    %"chk52" : A = (Check 0 8 Read 8) %"v319";
    %"v320" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"chk53" : F = CheckFunction %"v320";
    rawcall %"v322" : W = %"chk53"(P %"pr.5");
    %"v323" : W = (Cmp Ne W) %"v322", #0
    => goto "L314" };
  ir_blk{ @"L314" [%"v325" : W = phi("L264" => #0, "iw_2.join" => %"v323")]:
    => br %"v325" ? "L182" : "L257" };
  ir_blk{ @"L257":
    => goto "L182" };
  ir_blk{ @"L182" [%"pr.1" : W = phi("L257" => %"pr.2", "L314" => #4294967295, "L94" => %"pr.4")]:
    %"chk54" : A = (Renew 0 4 Read 1) %"chk13", %"pr.5";
    %"v331" : W = (RawLoad (LdNarrow Sw) 0) %"chk54";
    %"v332" : W = And %"v331", #32768;
    %"v333" : W = (Cmp Eq W) %"v332", #0
    => br %"v333" ? "L334" : "L329" };
  ir_blk{ @"L334":
    %"v340" : P = Copy $"__libc_single_threaded_internal";
    %"chk55" : A = (Check 0 1 Read 1) %"v340";
    %"v341" : W = (RawLoad (LdNarrow Sb) 0) %"chk55";
    %"v342" : W = (Cmp Ne W) %"v341", #0
    => br %"v342" ? "L343" : "L344" };
  ir_blk{ @"L343":
    %"v346" = %"pr.5" +p #136;
    %"chk56" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v346";
    %"v347" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v348" = %"v347" +p #4;
    %"chk57" : A = (Check 0 4 Read 1) %"v348";
    %"v349" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v350" : W = (Cmp Eq W) %"v349", #0
    => goto "L344" };
  ir_blk{ @"L344" [%"v352" : W = phi("L334" => #0, "L343" => %"v350")]:
    => br %"v352" ? "L337" : "L338" };
  ir_blk{ @"L337":
    %"v354" = %"pr.5" +p #136;
    %"chk58" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v354";
    %"v355" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v356" = %"v355" +p #8;
    %"chk59" : A = (Check 0 8 Write 8) %"v356";
    store.ptr [%"chk59" + 0] <- #0;
    %"chk60" : A = (Renew 0 8 Read 8) %"chk58", %"v354";
    %"v359" : P = (RawLoadPointer 0 load_effects) %"chk60";
    %"chk61" : A = (Check 0 4 Write 1) %"v359";
    store Ww [%"chk61" + 0] <- #0
    => goto "L329" };
  ir_blk{ @"L338":
    %"v364" = %"pr.5" +p #136;
    %"chk62" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v364";
    %"v365" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v366" = %"v365" +p #4;
    %"chk63" : A = (Check 0 4 Read 1) %"v366";
    %"v367" : W = (RawLoad (LdNarrow Sw) 0) %"chk63";
    %"v368" : W = (Cmp Eq W) %"v367", #0
    => br %"v368" ? "L360" : "L361" };
  ir_blk{ @"L360":
    %"v370" = %"pr.5" +p #136;
    %"v371" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v372" = %"v371" +p #8;
    %"chk65" : A = (Check 0 8 Write 8) %"v372";
    store.ptr [%"chk65" + 0] <- #0;
    %"chk66" : A = (Renew 0 8 Read 8) %"chk62", %"v370";
    %"v376" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"chk67" : A = (Check 0 4 Read 1) %"v376";
    %"v380" : W = (RawLoad (LdNarrow Sw) 0) %"chk67"
    => goto "L381" };
  ir_blk{ @"L381" [%"v383" : W = phi("L360" => %"v380", "L381" => %"v384")]:
    %"chk68" : A = (HalfCheck Lower 0 4 Write 4) %"chk67", %"v376";
    %"v384" : W = (RawCas (CasNarrow Sw) 0) %"chk68", %"v383", #0;
    %"v385" : W = (Cmp Eq W) %"v384", %"v383"
    => br %"v385" ? "L382" : poll "L381" };
  ir_blk{ @"L382":
    %"v390" : W = (Cmp Sgt W) %"v383", #1
    => br %"v390" ? "L393" : "L329" };
  ir_blk{ @"L393":
    call void $"__GI___lll_lock_wake_private"(P %"v376")
    => goto "L329" };
  ir_blk{ @"L361":
    %"v405" = %"pr.5" +p #136;
    %"v406" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v407" = %"v406" +p #4;
    %"chk70" : A = (Check 0 4 Read 1) %"v407";
    %"v408" : W = (RawLoad (LdNarrow Sw) 0) %"chk70";
    %"v409" : W = Sub %"v408", #1;
    %"chk71" : A = (Renew 0 4 Write 1) %"chk70", %"v407";
    store Ww [%"chk71" + 0] <- %"v409"
    => goto "L329" };
  ir_blk{ @"L329":
    %"v410" : P = Copy $"glibc_genops#run_fp";
    %"chk72" : A = (Check 0 8 Write 8) %"v410";
    store.ptr [%"chk72" + 0] <- #0;
    %"v412" = %"pr.5" +p #104;
    %"chk73" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v412";
    %"v413" : P = (RawLoadPointer 0 load_effects) %"chk73"
    => goto poll "L82" };
  ir_blk{ @"L414":
    %"v420" : P = Copy $"__libc_single_threaded_internal";
    %"chk74" : A = (Check 0 1 Read 1) %"v420";
    %"v421" : W = (RawLoad (LdNarrow Sb) 0) %"chk74";
    %"v422" : W = (Cmp Ne W) %"v421", #0
    => br %"v422" ? "L423" : "L424" };
  ir_blk{ @"L423":
    %"v425" : P = Copy $"glibc_genops#list_all_lock";
    %"v426" = %"v425" +p #4;
    %"chk75" : A = (Check 0 4 Read 1) %"v426";
    %"v427" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"v428" : W = (Cmp Eq W) %"v427", #0
    => goto "L424" };
  ir_blk{ @"L424" [%"v430" : W = phi("L414" => #0, "L423" => %"v428")]:
    => br %"v430" ? "L417" : "L418" };
  ir_blk{ @"L417":
    %"v431" : P = Copy $"glibc_genops#list_all_lock";
    %"v432" = %"v431" +p #8;
    %"chk76" : A = (Check 0 8 Write 8) %"v432";
    store.ptr [%"chk76" + 0] <- #0;
    %"v433" : P = Copy $"glibc_genops#list_all_lock";
    %"chk77" : A = (Check 0 4 Write 1) %"v433";
    store Ww [%"chk77" + 0] <- #0
    => goto "L476" };
  ir_blk{ @"L418":
    %"v437" : P = Copy $"glibc_genops#list_all_lock";
    %"v438" = %"v437" +p #4;
    %"chk78" : A = (Check 0 4 Read 1) %"v438";
    %"v439" : W = (RawLoad (LdNarrow Sw) 0) %"chk78";
    %"v440" : W = (Cmp Eq W) %"v439", #0
    => br %"v440" ? "L434" : "L435" };
  ir_blk{ @"L434":
    %"v441" : P = Copy $"glibc_genops#list_all_lock";
    %"v442" = %"v441" +p #8;
    %"chk79" : A = (Check 0 8 Write 8) %"v442";
    store.ptr [%"chk79" + 0] <- #0;
    %"v444" : P = Copy $"glibc_genops#list_all_lock";
    %"chk80" : A = (Check 0 4 Read 1) %"v444";
    %"v448" : W = (RawLoad (LdNarrow Sw) 0) %"chk80"
    => goto "L449" };
  ir_blk{ @"L449" [%"v451" : W = phi("L434" => %"v448", "L449" => %"v452")]:
    %"chk81" : A = (HalfCheck Lower 0 4 Write 4) %"chk80", %"v444";
    %"v452" : W = (RawCas (CasNarrow Sw) 0) %"chk81", %"v451", #0;
    %"v453" : W = (Cmp Eq W) %"v452", %"v451"
    => br %"v453" ? "L450" : poll "L449" };
  ir_blk{ @"L450":
    %"v458" : W = (Cmp Sgt W) %"v451", #1
    => br %"v458" ? "L461" : "L476" };
  ir_blk{ @"L461":
    call void $"__GI___lll_lock_wake_private"(P %"v444")
    => goto "L476" };
  ir_blk{ @"L435":
    %"v472" : P = Copy $"glibc_genops#list_all_lock";
    %"v473" = %"v472" +p #4;
    %"chk82" : A = (Check 0 4 Read 1) %"v473";
    %"v474" : W = (RawLoad (LdNarrow Sw) 0) %"chk82";
    %"v475" : W = Sub %"v474", #1;
    %"chk83" : A = (Renew 0 4 Write 1) %"chk82", %"v473";
    store Ww [%"chk83" + 0] <- %"v475"
    => goto "L476" };
  ir_blk{ @"L476":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v3")
    => ret %"pr.4" }])) }.

Definition fn___GI__IO_free_backup_area : func :=
  ir_fn{ "export" "__GI__IO_free_backup_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #256
    => br %"v7" ? "L2" : "L4";
  @"L2":
    call void $"_IO_switch_to_main_get_area"(P %"v0")
    => goto "L4";
  @"L4":
    %"v11" = %"v0" +p #72;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v12";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    call void $"free"(P %"v12")
    => goto "iw_1.join";
  @"iw_1.join":
    %"v14" = %"v0" +p #72;
    %"chk2" : A = (Renew 0 8 Write 8) %"chk1", %"v14";
    store.ptr [%"chk2" + 0] <- #0;
    %"v16" = %"v0" +p #88;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v16";
    store.ptr [%"chk3" + 0] <- #0;
    %"v18" = %"v0" +p #80;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v18";
    store.ptr [%"chk4" + 0] <- #0
    => ret void
} }.

Definition fn___GI__IO_link_in : func :=
  ir_fn{ "export" "__GI__IO_link_in"(P %"v0") -> RVoid {
  @"start":
    %"v13" : P = (Alloc 8) #32;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #128;
    %"v8" : W = (Cmp Eq W) %"v7", #0
    => br %"v8" ? "L2" : "L4";
  @"L2":
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = Or %"v10", #128;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v11";
    %"v15" : P = Copy $"glibc_genops#flush_cleanup";
    %"v16" = %"v13" +p #8;
    %"chk3" : A = (Check 0 8 Write 8) %"v16";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v13";
    store.ptr [%"chk4" + 0] <- %"v15";
    call void $"__GI___libc_cleanup_push_defer"(P %"v13");
    call %"v27" : P = $"zthread_self_cookie"();
    %"v31" : P = Copy $"__libc_single_threaded_internal";
    %"chk5" : A = (Check 0 1 Read 1) %"v31";
    %"v32" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v33" : W = (Cmp Ne W) %"v32", #0
    => br %"v33" ? "L34" : "L35";
  @"L34":
    %"v36" : P = Copy $"glibc_genops#list_all_lock";
    %"v37" = %"v36" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v39" : L = Ptoi %"v38";
    %"v40" : L = Ptoi #0;
    %"v41" : W = (Cmp Eq L) %"v39", %"v40"
    => goto "L35";
  @"L35" [%"v43" : W = phi("L2" => #0, "L34" => %"v41")]:
    => br %"v43" ? "L28" : "L29";
  @"L28":
    %"v44" : P = Copy $"glibc_genops#list_all_lock";
    %"chk7" : A = (Check 0 4 Write 1) %"v44";
    store Ww [%"chk7" + 0] <- #1;
    %"v45" : P = Copy $"glibc_genops#list_all_lock";
    %"v46" = %"v45" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"v46";
    store.ptr [%"chk8" + 0] <- %"v27"
    => goto "L25";
  @"L29":
    %"v51" : P = Copy $"glibc_genops#list_all_lock";
    %"v52" = %"v51" +p #8;
    %"chk9" : A = (Check 0 8 Read 8) %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v55" : L = Ptoi %"v53";
    %"v56" : L = Ptoi %"v27";
    %"v57" : W = (Cmp Ne L) %"v55", %"v56"
    => br %"v57" ? "L48" : "L49";
  @"L48":
    %"v59" : P = Copy $"glibc_genops#list_all_lock";
    %"chk10" : A = (Check 0 4 Write 4) %"v59";
    %"v66" : W = (RawCas (CasNarrow Sw) 0) %"chk10", #0, #1;
    %"v67" : W = (Cmp Eq W) %"v66", #0
    => br %"v67" ? "L69" : "L68";
  @"L68":
    => goto "L69";
  @"L69":
    %"v70" : W = (Cmp Ne W) %"v66", #0
    => br %"v70" ? "L73" : "L62";
  @"L73":
    call void $"__GI___lll_lock_wait_private"(P %"v59")
    => goto "L62";
  @"L62":
    %"v83" : P = Copy $"glibc_genops#list_all_lock";
    %"v84" = %"v83" +p #8;
    %"chk11" : A = (Check 0 8 Write 8) %"v84";
    store.ptr [%"chk11" + 0] <- %"v27"
    => goto "L25";
  @"L49":
    %"v86" : P = Copy $"glibc_genops#list_all_lock";
    %"v87" = %"v86" +p #4;
    %"chk12" : A = (Check 0 4 Read 1) %"v87";
    %"v88" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v89" : W = Add %"v88", #1;
    %"chk13" : A = (Renew 0 4 Write 1) %"chk12", %"v87";
    store Ww [%"chk13" + 0] <- %"v89"
    => goto "L25";
  @"L25":
    %"v90" : P = Copy $"glibc_genops#run_fp";
    %"chk14" : A = (Check 0 8 Write 8) %"v90";
    store.ptr [%"chk14" + 0] <- %"v0";
    %"chk15" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v96" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v97" : W = And %"v96", #32768;
    %"v98" : W = (Cmp Eq W) %"v97", #0
    => br %"v98" ? "L99" : "L94";
  @"L99":
    call %"v103" : P = $"zthread_self_cookie"();
    %"v107" : P = Copy $"__libc_single_threaded_internal";
    %"chk16" : A = (Check 0 1 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"v109" : W = (Cmp Ne W) %"v108", #0
    => br %"v109" ? "L110" : "L111";
  @"L110":
    %"v113" = %"v0" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v115" = %"v114" +p #8;
    %"chk18" : A = (Check 0 8 Read 8) %"v115";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v117" : L = Ptoi %"v116";
    %"v118" : L = Ptoi #0;
    %"v119" : W = (Cmp Eq L) %"v117", %"v118"
    => goto "L111";
  @"L111" [%"v121" : W = phi("L99" => #0, "L110" => %"v119")]:
    => br %"v121" ? "L104" : "L105";
  @"L104":
    %"v123" = %"v0" +p #136;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v123";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Check 0 4 Write 1) %"v124";
    store Ww [%"chk20" + 0] <- #1;
    %"v127" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v128" = %"v127" +p #8;
    %"chk22" : A = (Check 0 8 Write 8) %"v128";
    store.ptr [%"chk22" + 0] <- %"v103"
    => goto "L94";
  @"L105":
    %"v134" = %"v0" +p #136;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v136" = %"v135" +p #8;
    %"chk24" : A = (Check 0 8 Read 8) %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v139" : L = Ptoi %"v137";
    %"v140" : L = Ptoi %"v103";
    %"v141" : W = (Cmp Ne L) %"v139", %"v140"
    => br %"v141" ? "L130" : "L131";
  @"L130":
    %"v144" = %"v0" +p #136;
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk26" : A = (Check 0 4 Write 4) %"v145";
    %"v152" : W = (RawCas (CasNarrow Sw) 0) %"chk26", #0, #1;
    %"v153" : W = (Cmp Eq W) %"v152", #0
    => br %"v153" ? "L155" : "L154";
  @"L154":
    => goto "L155";
  @"L155":
    %"v156" : W = (Cmp Ne W) %"v152", #0
    => br %"v156" ? "L159" : "L148";
  @"L159":
    call void $"__GI___lll_lock_wait_private"(P %"v145")
    => goto "L148";
  @"L148":
    %"v170" = %"v0" +p #136;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk23", %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v172" = %"v171" +p #8;
    %"chk28" : A = (Check 0 8 Write 8) %"v172";
    store.ptr [%"chk28" + 0] <- %"v103"
    => goto "L94";
  @"L131":
    %"v175" = %"v0" +p #136;
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v177" = %"v176" +p #4;
    %"chk30" : A = (Check 0 4 Read 1) %"v177";
    %"v178" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v179" : W = Add %"v178", #1;
    %"chk31" : A = (Renew 0 4 Write 1) %"chk30", %"v177";
    store Ww [%"chk31" + 0] <- %"v179"
    => goto "L94";
  @"L94":
    %"v181" = %"v0" +p #104;
    %"v182" : P = Copy $"__GI__IO_list_all";
    %"chk32" : A = (Check 0 8 Read 8) %"v182";
    %"v183" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v181";
    store.ptr [%"chk33" + 0] <- %"v183";
    %"v189" = %"v0" +p #184;
    %"v190" : P = Copy $"__GI__IO_list_all";
    %"chk34" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v189";
    store.ptr [%"chk34" + 0] <- %"v190";
    %"v194" : P = Copy $"__GI__IO_list_all";
    %"chk35" : A = (Check 0 8 Read 8) %"v194";
    %"v195" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v196" : L = Ptoi %"v195";
    %"v197" : L = Ptoi #0;
    %"v198" : W = (Cmp Ne L) %"v196", %"v197"
    => br %"v198" ? "L191" : "L186";
  @"L191":
    %"v199" : P = Copy $"__GI__IO_list_all";
    %"chk36" : A = (Check 0 8 Read 8) %"v199";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v201" = %"v200" +p #184;
    %"v203" = %"v0" +p #104;
    %"chk37" : A = (Check 0 8 Write 8) %"v201";
    store.ptr [%"chk37" + 0] <- %"v203"
    => goto "L186";
  @"L186":
    %"v204" : P = Copy $"__GI__IO_list_all";
    %"chk38" : A = (Check 0 8 Write 8) %"v204";
    store.ptr [%"chk38" + 0] <- %"v0";
    %"chk39" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v210" : W = (RawLoad (LdNarrow Sw) 0) %"chk39";
    %"v211" : W = And %"v210", #32768;
    %"v212" : W = (Cmp Eq W) %"v211", #0
    => br %"v212" ? "L213" : "L208";
  @"L213":
    %"v219" : P = Copy $"__libc_single_threaded_internal";
    %"chk40" : A = (Check 0 1 Read 1) %"v219";
    %"v220" : W = (RawLoad (LdNarrow Sb) 0) %"chk40";
    %"v221" : W = (Cmp Ne W) %"v220", #0
    => br %"v221" ? "L222" : "L223";
  @"L222":
    %"v225" = %"v0" +p #136;
    %"chk41" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v225";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v227" = %"v226" +p #4;
    %"chk42" : A = (Check 0 4 Read 1) %"v227";
    %"v228" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v229" : W = (Cmp Eq W) %"v228", #0
    => goto "L223";
  @"L223" [%"v231" : W = phi("L213" => #0, "L222" => %"v229")]:
    => br %"v231" ? "L216" : "L217";
  @"L216":
    %"v233" = %"v0" +p #136;
    %"chk43" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v233";
    %"v234" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v235" = %"v234" +p #8;
    %"chk44" : A = (Check 0 8 Write 8) %"v235";
    store.ptr [%"chk44" + 0] <- #0;
    %"chk45" : A = (Renew 0 8 Read 8) %"chk43", %"v233";
    %"v238" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"chk46" : A = (Check 0 4 Write 1) %"v238";
    store Ww [%"chk46" + 0] <- #0
    => goto "L208";
  @"L217":
    %"v243" = %"v0" +p #136;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v243";
    %"v244" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v245" = %"v244" +p #4;
    %"chk48" : A = (Check 0 4 Read 1) %"v245";
    %"v246" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"v247" : W = (Cmp Eq W) %"v246", #0
    => br %"v247" ? "L239" : "L240";
  @"L239":
    %"v249" = %"v0" +p #136;
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v251" = %"v250" +p #8;
    %"chk50" : A = (Check 0 8 Write 8) %"v251";
    store.ptr [%"chk50" + 0] <- #0;
    %"chk51" : A = (Renew 0 8 Read 8) %"chk47", %"v249";
    %"v255" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"chk52" : A = (Check 0 4 Read 1) %"v255";
    %"v259" : W = (RawLoad (LdNarrow Sw) 0) %"chk52"
    => goto "L260";
  @"L260" [%"v262" : W = phi("L239" => %"v259", "L260" => %"v263")]:
    %"chk53" : A = (HalfCheck Lower 0 4 Write 4) %"chk52", %"v255";
    %"v263" : W = (RawCas (CasNarrow Sw) 0) %"chk53", %"v262", #0;
    %"v264" : W = (Cmp Eq W) %"v263", %"v262"
    => br %"v264" ? "L261" : poll "L260";
  @"L261":
    %"v269" : W = (Cmp Sgt W) %"v262", #1
    => br %"v269" ? "L272" : "L208";
  @"L272":
    call void $"__GI___lll_lock_wake_private"(P %"v255")
    => goto "L208";
  @"L240":
    %"v284" = %"v0" +p #136;
    %"v285" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v286" = %"v285" +p #4;
    %"chk55" : A = (Check 0 4 Read 1) %"v286";
    %"v287" : W = (RawLoad (LdNarrow Sw) 0) %"chk55";
    %"v288" : W = Sub %"v287", #1;
    %"chk56" : A = (Renew 0 4 Write 1) %"chk55", %"v286";
    store Ww [%"chk56" + 0] <- %"v288"
    => goto "L208";
  @"L208":
    %"v289" : P = Copy $"glibc_genops#run_fp";
    %"chk57" : A = (Check 0 8 Write 8) %"v289";
    store.ptr [%"chk57" + 0] <- #0;
    %"v296" : P = Copy $"__libc_single_threaded_internal";
    %"chk58" : A = (Check 0 1 Read 1) %"v296";
    %"v297" : W = (RawLoad (LdNarrow Sb) 0) %"chk58";
    %"v298" : W = (Cmp Ne W) %"v297", #0
    => br %"v298" ? "L299" : "L300";
  @"L299":
    %"v301" : P = Copy $"glibc_genops#list_all_lock";
    %"v302" = %"v301" +p #4;
    %"chk59" : A = (Check 0 4 Read 1) %"v302";
    %"v303" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"v304" : W = (Cmp Eq W) %"v303", #0
    => goto "L300";
  @"L300" [%"v306" : W = phi("L208" => #0, "L299" => %"v304")]:
    => br %"v306" ? "L293" : "L294";
  @"L293":
    %"v307" : P = Copy $"glibc_genops#list_all_lock";
    %"v308" = %"v307" +p #8;
    %"chk60" : A = (Check 0 8 Write 8) %"v308";
    store.ptr [%"chk60" + 0] <- #0;
    %"v309" : P = Copy $"glibc_genops#list_all_lock";
    %"chk61" : A = (Check 0 4 Write 1) %"v309";
    store Ww [%"chk61" + 0] <- #0
    => goto "L352";
  @"L294":
    %"v313" : P = Copy $"glibc_genops#list_all_lock";
    %"v314" = %"v313" +p #4;
    %"chk62" : A = (Check 0 4 Read 1) %"v314";
    %"v315" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"v316" : W = (Cmp Eq W) %"v315", #0
    => br %"v316" ? "L310" : "L311";
  @"L310":
    %"v317" : P = Copy $"glibc_genops#list_all_lock";
    %"v318" = %"v317" +p #8;
    %"chk63" : A = (Check 0 8 Write 8) %"v318";
    store.ptr [%"chk63" + 0] <- #0;
    %"v320" : P = Copy $"glibc_genops#list_all_lock";
    %"chk64" : A = (Check 0 4 Read 1) %"v320";
    %"v324" : W = (RawLoad (LdNarrow Sw) 0) %"chk64"
    => goto "L325";
  @"L325" [%"v327" : W = phi("L310" => %"v324", "L325" => %"v328")]:
    %"chk65" : A = (HalfCheck Lower 0 4 Write 4) %"chk64", %"v320";
    %"v328" : W = (RawCas (CasNarrow Sw) 0) %"chk65", %"v327", #0;
    %"v329" : W = (Cmp Eq W) %"v328", %"v327"
    => br %"v329" ? "L326" : poll "L325";
  @"L326":
    %"v334" : W = (Cmp Sgt W) %"v327", #1
    => br %"v334" ? "L337" : "L352";
  @"L337":
    call void $"__GI___lll_lock_wake_private"(P %"v320")
    => goto "L352";
  @"L311":
    %"v348" : P = Copy $"glibc_genops#list_all_lock";
    %"v349" = %"v348" +p #4;
    %"chk66" : A = (Check 0 4 Read 1) %"v349";
    %"v350" : W = (RawLoad (LdNarrow Sw) 0) %"chk66";
    %"v351" : W = Sub %"v350", #1;
    %"chk67" : A = (Renew 0 4 Write 1) %"chk66", %"v349";
    store Ww [%"chk67" + 0] <- %"v351"
    => goto "L352";
  @"L352":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v13")
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition fn___GI__IO_setb : func :=
  ir_fn{ "export" "__GI__IO_setb"(P %"v0", P %"v2", P %"v4", W %"v6") -> RVoid {
  @"start":
    %"v12" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : L = Ptoi %"v13";
    %"v15" : W = (Cmp Ne L) %"v14", #0
    => br %"v15" ? "L16" : "L17";
  @"L16":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v20" : W = And %"v19", #1;
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => goto "L17";
  @"L17" [%"v23" : W = phi("start" => #0, "L16" => %"v21")]:
    => br %"v23" ? "L8" : "L10";
  @"L8":
    %"v25" = %"v0" +p #56;
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"free"(P %"v26")
    => goto "L10";
  @"L10":
    %"v28" = %"v0" +p #56;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v28";
    store.ptr [%"chk3" + 0] <- %"v2";
    %"v31" = %"v0" +p #64;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v31";
    store.ptr [%"chk4" + 0] <- %"v4"
    => br %"v6" ? "L33" : "L34";
  @"L33":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v40" : W = And %"v38", #4294967294;
    %"chk6" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk6" + 0] <- %"v40"
    => goto "L35";
  @"L34":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v42" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v43" : W = Or %"v42", #1;
    %"chk8" : A = (Renew 0 4 Write 1) %"chk7", %"v0";
    store Ww [%"chk8" + 0] <- %"v43"
    => goto "L35";
  @"L35":
    => ret void
} }.

Definition fn___GI__IO_sputbackc : func :=
  ir_fn{ "export" "__GI__IO_sputbackc"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v9" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v12" = %"v0" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v14" : L = Ptoi %"v10";
    %"v15" : L = Ptoi %"v13";
    %"v16" : W = (Cmp Ugt L) %"v14", %"v15"
    => br %"v16" ? "L17" : "L18";
  @"L17":
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v21" : W = And %"v20", #256;
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => goto "L18";
  @"L18" [%"v24" : W = phi("start" => #0, "L17" => %"v22")]:
    => br %"v24" ? "L25" : "L26";
  @"L25":
    %"v28" = %"v0" +p #8;
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v32" = %"v29" +p #18446744073709551615;
    %"chk4" : A = (Check 0 1 Read 1) %"v32";
    %"v33" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v34" : W = (Ext Ub) %"v33";
    %"v36" : W = (Ext Ub) %"v2";
    %"v37" : W = (Cmp Eq W) %"v34", %"v36"
    => goto "L26";
  @"L26" [%"v39" : W = phi("L18" => #0, "L25" => %"v37")]:
    => br %"v39" ? "L5" : "L6";
  @"L5":
    %"v41" = %"v0" +p #8;
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk0";
    (Flight (a "v43") Sub [(FAddress (t "v42")); (FValue (Const 1))] (LowerOf (t "v42")));
    %"chk6" : A = (Renew 0 8 Write 8) %"chk0", %"v41";
    store.ptr [%"chk6" + 0] <- %"v43";
    %"v45" : W = (Ext Ub) %"v2"
    => goto "L7";
  @"L6":
    %"v47" = %"v0" +p #216;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v4" : L = Ptoi %"v48";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v50" = %"v48" +p #48;
    %"chk8" : A = (Check 0 8 Read 8) %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : F = CheckFunction %"v51";
    rawcall %"v54" : W = %"chk9"(P %"v0", W %"v2")
    => goto "L7";
  @"L7" [%"pr.1" : W = phi("L5" => %"v45", "iw_1.join" => %"v54")]:
    %"v60" : W = (Cmp Ne W) %"pr.1", #4294967295
    => br %"v60" ? "L55" : "L57";
  @"L55":
    %"chk10" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v64" : W = And %"v62", #4294967279;
    %"chk11" : A = (Renew 0 4 Write 1) %"chk10", %"v0";
    store Ww [%"chk11" + 0] <- %"v64"
    => goto "L57";
  @"L57":
    => ret %"pr.1"
} }.

Definition fn___GI__IO_switch_to_get_mode : func :=
  ir_fn{ "export" "__GI__IO_switch_to_get_mode"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" = %"v0" +p #32;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : W = (Cmp Ugt L) %"v11", %"v12"
    => br %"v13" ? "L2" : "L4";
  @"L2":
    %"v18" = %"v0" +p #216;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v4" : L = Ptoi %"v19";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v21" = %"v19" +p #24;
    %"chk3" : A = (Check 0 8 Read 8) %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v22";
    rawcall %"v25" : W = %"chk4"(P %"v0", W #4294967295);
    %"v27" : W = (Cmp Eq W) %"v25", #4294967295
    => br %"v27" ? "L14" : "L4";
  @"L14":
    => ret #4294967295;
  @"L4":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v35" : W = And %"v34", #256
    => br %"v35" ? "L30" : "L31";
  @"L30":
    %"v37" = %"v0" +p #24;
    %"v39" = %"v0" +p #80;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v37";
    store.ptr [%"chk7" + 0] <- %"v40"
    => goto "L32";
  @"L31":
    %"v42" = %"v0" +p #24;
    %"v44" = %"v0" +p #56;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v42";
    store.ptr [%"chk9" + 0] <- %"v45";
    %"v50" = %"v0" +p #40;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v53" = %"v0" +p #16;
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v55" : L = Ptoi %"v51";
    %"v56" : L = Ptoi %"v54";
    %"v57" : W = (Cmp Ugt L) %"v55", %"v56"
    => br %"v57" ? "L46" : "L32";
  @"L46":
    %"v59" = %"v0" +p #16;
    %"v61" = %"v0" +p #40;
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk13" : A = (Renew 0 8 Write 8) %"chk11", %"v59";
    store.ptr [%"chk13" + 0] <- %"v62"
    => goto "L32";
  @"L32":
    %"v64" = %"v0" +p #8;
    %"v66" = %"v0" +p #40;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk0", %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v64";
    store.ptr [%"chk15" + 0] <- %"v67";
    %"v69" = %"v0" +p #32;
    %"v73" = %"v0" +p #48;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk15", %"v64";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v73";
    store.ptr [%"chk17" + 0] <- %"v76";
    %"chk18" : A = (Renew 0 8 Write 8) %"chk0", %"v66";
    store.ptr [%"chk18" + 0] <- %"v76";
    %"chk19" : A = (Renew 0 8 Write 8) %"chk1", %"v69";
    store.ptr [%"chk19" + 0] <- %"v76";
    %"chk20" : A = (Renew 0 4 Read 1) %"chk5", %"v0";
    %"v78" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"v80" : W = And %"v78", #4294965247;
    %"chk21" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk21" + 0] <- %"v80"
    => ret #0
} }.

Definition fn___GI__IO_un_link : func :=
  ir_fn{ "export" "__GI__IO_un_link"(P %"v0") -> RVoid {
  @"start":
    %"v10" : P = (Alloc 8) #32;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #128
    => br %"v7" ? "L2" : "L4";
  @"L2":
    %"v12" : P = Copy $"glibc_genops#flush_cleanup";
    %"v13" = %"v10" +p #8;
    %"chk1" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk1" + 0] <- #0;
    %"chk2" : A = (HalfCheck Lower 0 8 Write 8) %"chk1", %"v10";
    store.ptr [%"chk2" + 0] <- %"v12";
    call void $"__GI___libc_cleanup_push_defer"(P %"v10");
    call %"v24" : P = $"zthread_self_cookie"();
    %"v28" : P = Copy $"__libc_single_threaded_internal";
    %"chk3" : A = (Check 0 1 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v30" : W = (Cmp Ne W) %"v29", #0
    => br %"v30" ? "L31" : "L32";
  @"L31":
    %"v33" : P = Copy $"glibc_genops#list_all_lock";
    %"v34" = %"v33" +p #8;
    %"chk4" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v36" : L = Ptoi %"v35";
    %"v37" : L = Ptoi #0;
    %"v38" : W = (Cmp Eq L) %"v36", %"v37"
    => goto "L32";
  @"L32" [%"v40" : W = phi("L2" => #0, "L31" => %"v38")]:
    => br %"v40" ? "L25" : "L26";
  @"L25":
    %"v41" : P = Copy $"glibc_genops#list_all_lock";
    %"chk5" : A = (Check 0 4 Write 1) %"v41";
    store Ww [%"chk5" + 0] <- #1;
    %"v42" : P = Copy $"glibc_genops#list_all_lock";
    %"v43" = %"v42" +p #8;
    %"chk6" : A = (Check 0 8 Write 8) %"v43";
    store.ptr [%"chk6" + 0] <- %"v24"
    => goto "L22";
  @"L26":
    %"v48" : P = Copy $"glibc_genops#list_all_lock";
    %"v49" = %"v48" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v52" : L = Ptoi %"v50";
    %"v53" : L = Ptoi %"v24";
    %"v54" : W = (Cmp Ne L) %"v52", %"v53"
    => br %"v54" ? "L45" : "L46";
  @"L45":
    %"v56" : P = Copy $"glibc_genops#list_all_lock";
    %"chk8" : A = (Check 0 4 Write 4) %"v56";
    %"v63" : W = (RawCas (CasNarrow Sw) 0) %"chk8", #0, #1;
    %"v64" : W = (Cmp Eq W) %"v63", #0
    => br %"v64" ? "L66" : "L65";
  @"L65":
    => goto "L66";
  @"L66":
    %"v67" : W = (Cmp Ne W) %"v63", #0
    => br %"v67" ? "L70" : "L59";
  @"L70":
    call void $"__GI___lll_lock_wait_private"(P %"v56")
    => goto "L59";
  @"L59":
    %"v80" : P = Copy $"glibc_genops#list_all_lock";
    %"v81" = %"v80" +p #8;
    %"chk9" : A = (Check 0 8 Write 8) %"v81";
    store.ptr [%"chk9" + 0] <- %"v24"
    => goto "L22";
  @"L46":
    %"v83" : P = Copy $"glibc_genops#list_all_lock";
    %"v84" = %"v83" +p #4;
    %"chk10" : A = (Check 0 4 Read 1) %"v84";
    %"v85" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v86" : W = Add %"v85", #1;
    %"chk11" : A = (Renew 0 4 Write 1) %"chk10", %"v84";
    store Ww [%"chk11" + 0] <- %"v86"
    => goto "L22";
  @"L22":
    %"v87" : P = Copy $"glibc_genops#run_fp";
    %"chk12" : A = (Check 0 8 Write 8) %"v87";
    store.ptr [%"chk12" + 0] <- %"v0";
    %"chk13" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v94" : W = And %"v93", #32768;
    %"v95" : W = (Cmp Eq W) %"v94", #0
    => br %"v95" ? "L96" : "L91";
  @"L96":
    call %"v100" : P = $"zthread_self_cookie"();
    %"v104" : P = Copy $"__libc_single_threaded_internal";
    %"chk14" : A = (Check 0 1 Read 1) %"v104";
    %"v105" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v106" : W = (Cmp Ne W) %"v105", #0
    => br %"v106" ? "L107" : "L108";
  @"L107":
    %"v110" = %"v0" +p #136;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v110";
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v112" = %"v111" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v114" : L = Ptoi %"v113";
    %"v115" : L = Ptoi #0;
    %"v116" : W = (Cmp Eq L) %"v114", %"v115"
    => goto "L108";
  @"L108" [%"v118" : W = phi("L96" => #0, "L107" => %"v116")]:
    => br %"v118" ? "L101" : "L102";
  @"L101":
    %"v120" = %"v0" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v120";
    %"v121" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Write 1) %"v121";
    store Ww [%"chk18" + 0] <- #1;
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v125" = %"v124" +p #8;
    %"chk20" : A = (Check 0 8 Write 8) %"v125";
    store.ptr [%"chk20" + 0] <- %"v100"
    => goto "L91";
  @"L102":
    %"v131" = %"v0" +p #136;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v131";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v133" = %"v132" +p #8;
    %"chk22" : A = (Check 0 8 Read 8) %"v133";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v136" : L = Ptoi %"v134";
    %"v137" : L = Ptoi %"v100";
    %"v138" : W = (Cmp Ne L) %"v136", %"v137"
    => br %"v138" ? "L127" : "L128";
  @"L127":
    %"v141" = %"v0" +p #136;
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 4 Write 4) %"v142";
    %"v149" : W = (RawCas (CasNarrow Sw) 0) %"chk24", #0, #1;
    %"v150" : W = (Cmp Eq W) %"v149", #0
    => br %"v150" ? "L152" : "L151";
  @"L151":
    => goto "L152";
  @"L152":
    %"v153" : W = (Cmp Ne W) %"v149", #0
    => br %"v153" ? "L156" : "L145";
  @"L156":
    call void $"__GI___lll_lock_wait_private"(P %"v142")
    => goto "L145";
  @"L145":
    %"v167" = %"v0" +p #136;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk21", %"v167";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v169" = %"v168" +p #8;
    %"chk26" : A = (Check 0 8 Write 8) %"v169";
    store.ptr [%"chk26" + 0] <- %"v100"
    => goto "L91";
  @"L128":
    %"v172" = %"v0" +p #136;
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v174" = %"v173" +p #4;
    %"chk28" : A = (Check 0 4 Read 1) %"v174";
    %"v175" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v176" : W = Add %"v175", #1;
    %"chk29" : A = (Renew 0 4 Write 1) %"chk28", %"v174";
    store Ww [%"chk29" + 0] <- %"v176"
    => goto "L91";
  @"L91":
    %"v180" : P = Copy $"__GI__IO_list_all";
    %"chk30" : A = (Check 0 8 Read 8) %"v180";
    %"v181" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v182" : L = Ptoi %"v181";
    %"v183" : L = Ptoi #0;
    %"v184" : W = (Cmp Eq L) %"v182", %"v183"
    => br %"v184" ? "L179" : "L185";
  @"L185":
    %"v191" = %"v0" +p #184;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v191";
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v195" = %"v0" +p #104;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v195";
    %"v196" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Check 0 8 Write 8) %"v192";
    store.ptr [%"chk33" + 0] <- %"v196";
    %"v203" : L = Ptoi %"v196";
    %"v205" : W = (Cmp Ne L) %"v203", %"v183"
    => br %"v205" ? "L199" : "L179";
  @"L199":
    %"v207" = %"v196" +p #184;
    %"chk34" : A = (Check 0 8 Write 8) %"v207";
    store.ptr [%"chk34" + 0] <- %"v192"
    => goto "L179";
  @"L179":
    %"chk35" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v252" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v254" : W = And %"v252", #4294967167;
    %"chk36" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk36" + 0] <- %"v254";
    %"v259" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"v260" : W = And %"v259", #32768;
    %"v261" : W = (Cmp Eq W) %"v260", #0
    => br %"v261" ? "L262" : "L257";
  @"L262":
    %"v268" : P = Copy $"__libc_single_threaded_internal";
    %"chk38" : A = (Check 0 1 Read 1) %"v268";
    %"v269" : W = (RawLoad (LdNarrow Sb) 0) %"chk38";
    %"v270" : W = (Cmp Ne W) %"v269", #0
    => br %"v270" ? "L271" : "L272";
  @"L271":
    %"v274" = %"v0" +p #136;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v274";
    %"v275" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v276" = %"v275" +p #4;
    %"chk40" : A = (Check 0 4 Read 1) %"v276";
    %"v277" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"v278" : W = (Cmp Eq W) %"v277", #0
    => goto "L272";
  @"L272" [%"v280" : W = phi("L262" => #0, "L271" => %"v278")]:
    => br %"v280" ? "L265" : "L266";
  @"L265":
    %"v282" = %"v0" +p #136;
    %"chk41" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v282";
    %"v283" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v284" = %"v283" +p #8;
    %"chk42" : A = (Check 0 8 Write 8) %"v284";
    store.ptr [%"chk42" + 0] <- #0;
    %"chk43" : A = (Renew 0 8 Read 8) %"chk41", %"v282";
    %"v287" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"chk44" : A = (Check 0 4 Write 1) %"v287";
    store Ww [%"chk44" + 0] <- #0
    => goto "L257";
  @"L266":
    %"v292" = %"v0" +p #136;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v292";
    %"v293" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v294" = %"v293" +p #4;
    %"chk46" : A = (Check 0 4 Read 1) %"v294";
    %"v295" : W = (RawLoad (LdNarrow Sw) 0) %"chk46";
    %"v296" : W = (Cmp Eq W) %"v295", #0
    => br %"v296" ? "L288" : "L289";
  @"L288":
    %"v298" = %"v0" +p #136;
    %"v299" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v300" = %"v299" +p #8;
    %"chk48" : A = (Check 0 8 Write 8) %"v300";
    store.ptr [%"chk48" + 0] <- #0;
    %"chk49" : A = (Renew 0 8 Read 8) %"chk45", %"v298";
    %"v304" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"chk50" : A = (Check 0 4 Read 1) %"v304";
    %"v308" : W = (RawLoad (LdNarrow Sw) 0) %"chk50"
    => goto "L309";
  @"L309" [%"v311" : W = phi("L288" => %"v308", "L309" => %"v312")]:
    %"chk51" : A = (HalfCheck Lower 0 4 Write 4) %"chk50", %"v304";
    %"v312" : W = (RawCas (CasNarrow Sw) 0) %"chk51", %"v311", #0;
    %"v313" : W = (Cmp Eq W) %"v312", %"v311"
    => br %"v313" ? "L310" : poll "L309";
  @"L310":
    %"v318" : W = (Cmp Sgt W) %"v311", #1
    => br %"v318" ? "L321" : "L257";
  @"L321":
    call void $"__GI___lll_lock_wake_private"(P %"v304")
    => goto "L257";
  @"L289":
    %"v333" = %"v0" +p #136;
    %"v334" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v335" = %"v334" +p #4;
    %"chk53" : A = (Check 0 4 Read 1) %"v335";
    %"v336" : W = (RawLoad (LdNarrow Sw) 0) %"chk53";
    %"v337" : W = Sub %"v336", #1;
    %"chk54" : A = (Renew 0 4 Write 1) %"chk53", %"v335";
    store Ww [%"chk54" + 0] <- %"v337"
    => goto "L257";
  @"L257":
    %"v338" : P = Copy $"glibc_genops#run_fp";
    %"chk55" : A = (Check 0 8 Write 8) %"v338";
    store.ptr [%"chk55" + 0] <- #0;
    %"v345" : P = Copy $"__libc_single_threaded_internal";
    %"chk56" : A = (Check 0 1 Read 1) %"v345";
    %"v346" : W = (RawLoad (LdNarrow Sb) 0) %"chk56";
    %"v347" : W = (Cmp Ne W) %"v346", #0
    => br %"v347" ? "L348" : "L349";
  @"L348":
    %"v350" : P = Copy $"glibc_genops#list_all_lock";
    %"v351" = %"v350" +p #4;
    %"chk57" : A = (Check 0 4 Read 1) %"v351";
    %"v352" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v353" : W = (Cmp Eq W) %"v352", #0
    => goto "L349";
  @"L349" [%"v355" : W = phi("L257" => #0, "L348" => %"v353")]:
    => br %"v355" ? "L342" : "L343";
  @"L342":
    %"v356" : P = Copy $"glibc_genops#list_all_lock";
    %"v357" = %"v356" +p #8;
    %"chk58" : A = (Check 0 8 Write 8) %"v357";
    store.ptr [%"chk58" + 0] <- #0;
    %"v358" : P = Copy $"glibc_genops#list_all_lock";
    %"chk59" : A = (Check 0 4 Write 1) %"v358";
    store Ww [%"chk59" + 0] <- #0
    => goto "L401";
  @"L343":
    %"v362" : P = Copy $"glibc_genops#list_all_lock";
    %"v363" = %"v362" +p #4;
    %"chk60" : A = (Check 0 4 Read 1) %"v363";
    %"v364" : W = (RawLoad (LdNarrow Sw) 0) %"chk60";
    %"v365" : W = (Cmp Eq W) %"v364", #0
    => br %"v365" ? "L359" : "L360";
  @"L359":
    %"v366" : P = Copy $"glibc_genops#list_all_lock";
    %"v367" = %"v366" +p #8;
    %"chk61" : A = (Check 0 8 Write 8) %"v367";
    store.ptr [%"chk61" + 0] <- #0;
    %"v369" : P = Copy $"glibc_genops#list_all_lock";
    %"chk62" : A = (Check 0 4 Read 1) %"v369";
    %"v373" : W = (RawLoad (LdNarrow Sw) 0) %"chk62"
    => goto "L374";
  @"L374" [%"v376" : W = phi("L359" => %"v373", "L374" => %"v377")]:
    %"chk63" : A = (HalfCheck Lower 0 4 Write 4) %"chk62", %"v369";
    %"v377" : W = (RawCas (CasNarrow Sw) 0) %"chk63", %"v376", #0;
    %"v378" : W = (Cmp Eq W) %"v377", %"v376"
    => br %"v378" ? "L375" : poll "L374";
  @"L375":
    %"v383" : W = (Cmp Sgt W) %"v376", #1
    => br %"v383" ? "L386" : "L401";
  @"L386":
    call void $"__GI___lll_lock_wake_private"(P %"v369")
    => goto "L401";
  @"L360":
    %"v397" : P = Copy $"glibc_genops#list_all_lock";
    %"v398" = %"v397" +p #4;
    %"chk64" : A = (Check 0 4 Read 1) %"v398";
    %"v399" : W = (RawLoad (LdNarrow Sw) 0) %"chk64";
    %"v400" : W = Sub %"v399", #1;
    %"chk65" : A = (Renew 0 4 Write 1) %"chk64", %"v398";
    store Ww [%"chk65" + 0] <- %"v400"
    => goto "L401";
  @"L401":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v10")
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition fn___GI__IO_unsave_markers : func :=
  ir_fn{ "export" "__GI__IO_unsave_markers"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #96;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" : L = Ptoi %"v5";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L6" : "L8";
  @"L6":
    %"v13" = %"v0" +p #96;
    %"chk1" : A = (Renew 0 8 Write 8) %"chk0", %"v13";
    store.ptr [%"chk1" + 0] <- #0
    => goto "L8";
  @"L8":
    %"v18" = %"v0" +p #80;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v20" : L = Ptoi %"v19";
    %"v21" : L = Ptoi #0;
    %"v22" : W = (Cmp Ne L) %"v20", %"v21"
    => br %"v22" ? "L14" : "L16";
  @"L14":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L16";
  @"L16":
    => ret void
} }.

Definition fn___GI___overflow : func :=
  ir_fn{ "export" "__GI___overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => br %"v10" ? "L13" : "L6";
  @"L13":
    %"v27" = %"v0" +p #192;
    %"v28" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v29" : W = (Cmp Eq W) %"v28", #0
    => br %"v29" ? "L23" : "L25";
  @"L23":
    %"v31" = %"v0" +p #192;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v31";
    store Ww [%"chk2" + 0] <- #4294967295
    => goto "L25";
  @"L25":
    %"v34" = %"v0" +p #192;
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L6";
  @"L6":
    %"v58" = %"v0" +p #216;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v4" : L = Ptoi %"v59";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v61" = %"v59" +p #24;
    %"chk5" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : F = CheckFunction %"v62";
    rawcall %"v65" : W = %"chk6"(P %"v0", W %"v2")
    => ret %"v65"
} }.

Definition fn___GI___uflow : func :=
  ir_fn{ "export" "__GI___uflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v24" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v26" : W = (Cmp Eq W) %"v25", #0
    => br %"v26" ? "L20" : "L22";
  @"L20":
    %"v28" = %"v0" +p #192;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v28";
    store Ww [%"chk1" + 0] <- #4294967295
    => goto "L22";
  @"L22":
    %"v31" = %"v0" +p #192;
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v55" : W = (Cmp Ne W) %"v32", #4294967295
    => br %"v55" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v64" = %"v0" +p #192;
    %"v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v66" : W = (Cmp Eq W) %"v65", #0
    => br %"v66" ? "L69" : "L62";
  @"L69":
    %"v83" = %"v0" +p #192;
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v85" : W = (Cmp Eq W) %"v84", #0
    => br %"v85" ? "L79" : "L81";
  @"L79":
    %"v87" = %"v0" +p #192;
    %"chk5" : A = (Renew 0 4 Write 1) %"chk0", %"v87";
    store Ww [%"chk5" + 0] <- #4294967295
    => goto "L81";
  @"L81":
    %"v90" = %"v0" +p #192;
    %"v91" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L62";
  @"L62":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v117" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v118" : W = And %"v117", #2048
    => br %"v118" ? "L113" : "L115";
  @"L113":
    call %"v123" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v125" : W = (Cmp Eq W) %"v123", #4294967295
    => br %"v125" ? "L119" : "L115";
  @"L119":
    => ret #4294967295;
  @"L115":
    %"v132" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v132";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v135" = %"v0" +p #16;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v135";
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v137" : L = Ptoi %"v133";
    %"v138" : L = Ptoi %"v136";
    %"v139" : W = (Cmp Ult L) %"v137", %"v138"
    => br %"v139" ? "L128" : "L130";
  @"L128":
    %"v141" = %"v0" +p #8;
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v143" = %"v142" +p #1;
    %"chk11" : A = (Renew 0 8 Write 8) %"chk8", %"v141";
    store.ptr [%"chk11" + 0] <- %"v143";
    %"chk12" : A = (Check 0 1 Read 1) %"v142";
    %"v144" : W = (RawLoad (LdNarrow Ub) 0) %"chk12"
    => ret %"v144";
  @"L130":
    %"chk13" : A = (Renew 0 4 Read 1) %"chk7", %"v0";
    %"v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v151" : W = And %"v150", #256
    => br %"v151" ? "L146" : "L148";
  @"L146":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v157" = %"v0" +p #8;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk8", %"v157";
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v160" = %"v0" +p #16;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk9", %"v160";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v162" : L = Ptoi %"v158";
    %"v163" : L = Ptoi %"v161";
    %"v164" : W = (Cmp Ult L) %"v162", %"v163"
    => br %"v164" ? "L153" : "L148";
  @"L153":
    %"v166" = %"v0" +p #8;
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v168" = %"v167" +p #1;
    %"chk17" : A = (Renew 0 8 Write 8) %"chk8", %"v166";
    store.ptr [%"chk17" + 0] <- %"v168";
    %"chk18" : A = (Check 0 1 Read 1) %"v167";
    %"v169" : W = (RawLoad (LdNarrow Ub) 0) %"chk18"
    => ret %"v169";
  @"L148":
    %"v175" = %"v0" +p #96;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v175";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v177" : L = Ptoi %"v176";
    %"v178" : L = Ptoi #0;
    %"v179" : W = (Cmp Ne L) %"v177", %"v178"
    => br %"v179" ? "L171" : "L172";
  @"L171":
    %"v185" = %"v0" +p #16;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk9", %"v185";
    %"v186" : P = (RawLoadPointer 0 load_effects) %"chk20";
    call %"v187" : W = $"glibc_genops#save_for_backup"(P %"v0", P %"v186")
    => br %"v187" ? "L180" : "L173";
  @"L180":
    => ret #4294967295;
  @"L172":
    %"v194" = %"v0" +p #80;
    %"chk21" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v194";
    %"v195" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v196" : L = Ptoi %"v195";
    %"v198" : W = (Cmp Ne L) %"v196", %"v178"
    => br %"v198" ? "L190" : "L173";
  @"L190":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L173";
  @"L173":
    %"v201" = %"v0" +p #216;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v201";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_1.v4" : L = Ptoi %"v202";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v204" = %"v202" +p #40;
    %"chk23" : A = (Check 0 8 Read 8) %"v204";
    %"v205" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : F = CheckFunction %"v205";
    rawcall %"v207" : W = %"chk24"(P %"v0")
    => ret %"v207"
} }.

Definition fn___GI___underflow : func :=
  ir_fn{ "export" "__GI___underflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v24" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v26" : W = (Cmp Eq W) %"v25", #0
    => br %"v26" ? "L20" : "L22";
  @"L20":
    %"v28" = %"v0" +p #192;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v28";
    store Ww [%"chk1" + 0] <- #4294967295
    => goto "L22";
  @"L22":
    %"v31" = %"v0" +p #192;
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v55" : W = (Cmp Ne W) %"v32", #4294967295
    => br %"v55" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v64" = %"v0" +p #192;
    %"v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v66" : W = (Cmp Eq W) %"v65", #0
    => br %"v66" ? "L69" : "L62";
  @"L69":
    %"v83" = %"v0" +p #192;
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v85" : W = (Cmp Eq W) %"v84", #0
    => br %"v85" ? "L79" : "L81";
  @"L79":
    %"v87" = %"v0" +p #192;
    %"chk5" : A = (Renew 0 4 Write 1) %"chk0", %"v87";
    store Ww [%"chk5" + 0] <- #4294967295
    => goto "L81";
  @"L81":
    %"v90" = %"v0" +p #192;
    %"v91" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L62";
  @"L62":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v117" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v118" : W = And %"v117", #2048
    => br %"v118" ? "L113" : "L115";
  @"L113":
    call %"v123" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v125" : W = (Cmp Eq W) %"v123", #4294967295
    => br %"v125" ? "L119" : "L115";
  @"L119":
    => ret #4294967295;
  @"L115":
    %"v132" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v132";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v135" = %"v0" +p #16;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v135";
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v137" : L = Ptoi %"v133";
    %"v138" : L = Ptoi %"v136";
    %"v139" : W = (Cmp Ult L) %"v137", %"v138"
    => br %"v139" ? "L128" : "L130";
  @"L128":
    %"v141" = %"v0" +p #8;
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk11" : A = (Check 0 1 Read 1) %"v142";
    %"v143" : W = (RawLoad (LdNarrow Ub) 0) %"chk11"
    => ret %"v143";
  @"L130":
    %"chk12" : A = (Renew 0 4 Read 1) %"chk7", %"v0";
    %"v149" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v150" : W = And %"v149", #256
    => br %"v150" ? "L145" : "L147";
  @"L145":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v156" = %"v0" +p #8;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk8", %"v156";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v159" = %"v0" +p #16;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk9", %"v159";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v161" : L = Ptoi %"v157";
    %"v162" : L = Ptoi %"v160";
    %"v163" : W = (Cmp Ult L) %"v161", %"v162"
    => br %"v163" ? "L152" : "L147";
  @"L152":
    %"v165" = %"v0" +p #8;
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk16" : A = (Check 0 1 Read 1) %"v166";
    %"v167" : W = (RawLoad (LdNarrow Ub) 0) %"chk16"
    => ret %"v167";
  @"L147":
    %"v173" = %"v0" +p #96;
    %"chk17" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v175" : L = Ptoi %"v174";
    %"v176" : L = Ptoi #0;
    %"v177" : W = (Cmp Ne L) %"v175", %"v176"
    => br %"v177" ? "L169" : "L170";
  @"L169":
    %"v183" = %"v0" +p #16;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk9", %"v183";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call %"v185" : W = $"glibc_genops#save_for_backup"(P %"v0", P %"v184")
    => br %"v185" ? "L178" : "L171";
  @"L178":
    => ret #4294967295;
  @"L170":
    %"v192" = %"v0" +p #80;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v192";
    %"v193" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v194" : L = Ptoi %"v193";
    %"v196" : W = (Cmp Ne L) %"v194", %"v176"
    => br %"v196" ? "L188" : "L171";
  @"L188":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L171";
  @"L171":
    %"v199" = %"v0" +p #216;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v199";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_1.v4" : L = Ptoi %"v200";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v202" = %"v200" +p #32;
    %"chk21" : A = (Check 0 8 Read 8) %"v202";
    %"v203" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : F = CheckFunction %"v203";
    rawcall %"v205" : W = %"chk22"(P %"v0")
    => ret %"v205"
} }.

Definition item_glibc_genops'23dealloc_buffers : item :=
  (IData (a "glibc_genops#dealloc_buffers") LLocal 1 [(Zero 1)]).

Definition fn_glibc_genops'23flush_cleanup : func :=
  ir_fn{ "local" "glibc_genops#flush_cleanup"(P %"v0") -> RVoid {
  @"start":
    %"v5" : P = Copy $"glibc_genops#run_fp";
    %"chk0" : A = (Check 0 8 Read 8) %"v5";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v7" : L = Ptoi %"v6";
    %"v8" : L = Ptoi #0;
    %"v9" : W = (Cmp Ne L) %"v7", %"v8"
    => br %"v9" ? "L2" : "L101";
  @"L2":
    %"v13" : P = Copy $"glibc_genops#run_fp";
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 4 Read 1) %"v14";
    %"v15" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v16" : W = And %"v15", #32768;
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => br %"v17" ? "L18" : "L101";
  @"L18":
    %"v24" : P = Copy $"__libc_single_threaded_internal";
    %"chk3" : A = (Check 0 1 Read 1) %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v26" : W = (Cmp Ne W) %"v25", #0
    => br %"v26" ? "L27" : "L28";
  @"L27":
    %"v29" : P = Copy $"glibc_genops#run_fp";
    %"chk4" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v31" = %"v30" +p #136;
    %"chk5" : A = (Check 0 8 Read 8) %"v31";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v33" = %"v32" +p #4;
    %"chk6" : A = (Check 0 4 Read 1) %"v33";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v35" : W = (Cmp Eq W) %"v34", #0
    => goto "L28";
  @"L28" [%"v37" : W = phi("L18" => #0, "L27" => %"v35")]:
    => br %"v37" ? "L21" : "L22";
  @"L21":
    %"v38" : P = Copy $"glibc_genops#run_fp";
    %"chk7" : A = (Check 0 8 Read 8) %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v40" = %"v39" +p #136;
    %"chk8" : A = (Check 0 8 Read 8) %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v42" = %"v41" +p #8;
    %"chk9" : A = (Check 0 8 Write 8) %"v42";
    store.ptr [%"chk9" + 0] <- #0;
    %"v43" : P = Copy $"glibc_genops#run_fp";
    %"chk10" : A = (Check 0 8 Read 8) %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v45" = %"v44" +p #136;
    %"chk11" : A = (Check 0 8 Read 8) %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 4 Write 1) %"v46";
    store Ww [%"chk12" + 0] <- #0
    => goto "L101";
  @"L22":
    %"v50" : P = Copy $"glibc_genops#run_fp";
    %"chk13" : A = (Check 0 8 Read 8) %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v52" = %"v51" +p #136;
    %"chk14" : A = (Check 0 8 Read 8) %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v54" = %"v53" +p #4;
    %"chk15" : A = (Check 0 4 Read 1) %"v54";
    %"v55" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v56" : W = (Cmp Eq W) %"v55", #0
    => br %"v56" ? "L47" : "L48";
  @"L47":
    %"v57" : P = Copy $"glibc_genops#run_fp";
    %"chk16" : A = (Check 0 8 Read 8) %"v57";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v59" = %"v58" +p #136;
    %"chk17" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v61" = %"v60" +p #8;
    %"chk18" : A = (Check 0 8 Write 8) %"v61";
    store.ptr [%"chk18" + 0] <- #0;
    %"v63" : P = Copy $"glibc_genops#run_fp";
    %"chk19" : A = (Check 0 8 Read 8) %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v65" = %"v64" +p #136;
    %"chk20" : A = (Check 0 8 Read 8) %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Check 0 4 Read 1) %"v66";
    %"v70" : W = (RawLoad (LdNarrow Sw) 0) %"chk21"
    => goto "L71";
  @"L71" [%"v73" : W = phi("L47" => %"v70", "L71" => %"v74")]:
    %"chk22" : A = (HalfCheck Lower 0 4 Write 4) %"chk21", %"v66";
    %"v74" : W = (RawCas (CasNarrow Sw) 0) %"chk22", %"v73", #0;
    %"v75" : W = (Cmp Eq W) %"v74", %"v73"
    => br %"v75" ? "L72" : poll "L71";
  @"L72":
    %"v80" : W = (Cmp Sgt W) %"v73", #1
    => br %"v80" ? "L83" : "L101";
  @"L83":
    call void $"__GI___lll_lock_wake_private"(P %"v66")
    => goto "L101";
  @"L48":
    %"v94" : P = Copy $"glibc_genops#run_fp";
    %"chk23" : A = (Check 0 8 Read 8) %"v94";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v96" = %"v95" +p #136;
    %"chk24" : A = (Check 0 8 Read 8) %"v96";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v98" = %"v97" +p #4;
    %"chk25" : A = (Check 0 4 Read 1) %"v98";
    %"v99" : W = (RawLoad (LdNarrow Sw) 0) %"chk25";
    %"v100" : W = Sub %"v99", #1;
    %"chk26" : A = (Renew 0 4 Write 1) %"chk25", %"v98";
    store Ww [%"chk26" + 0] <- %"v100"
    => goto "L101";
  @"L101":
    %"v107" : P = Copy $"__libc_single_threaded_internal";
    %"chk27" : A = (Check 0 1 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Sb) 0) %"chk27";
    %"v109" : W = (Cmp Ne W) %"v108", #0
    => br %"v109" ? "L110" : "L111";
  @"L110":
    %"v112" : P = Copy $"glibc_genops#list_all_lock";
    %"v113" = %"v112" +p #4;
    %"chk28" : A = (Check 0 4 Read 1) %"v113";
    %"v114" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v115" : W = (Cmp Eq W) %"v114", #0
    => goto "L111";
  @"L111" [%"v117" : W = phi("L101" => #0, "L110" => %"v115")]:
    => br %"v117" ? "L104" : "L105";
  @"L104":
    %"v118" : P = Copy $"glibc_genops#list_all_lock";
    %"v119" = %"v118" +p #8;
    %"chk29" : A = (Check 0 8 Write 8) %"v119";
    store.ptr [%"chk29" + 0] <- #0;
    %"v120" : P = Copy $"glibc_genops#list_all_lock";
    %"chk30" : A = (Check 0 4 Write 1) %"v120";
    store Ww [%"chk30" + 0] <- #0
    => goto "L103";
  @"L105":
    %"v124" : P = Copy $"glibc_genops#list_all_lock";
    %"v125" = %"v124" +p #4;
    %"chk31" : A = (Check 0 4 Read 1) %"v125";
    %"v126" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v127" : W = (Cmp Eq W) %"v126", #0
    => br %"v127" ? "L121" : "L122";
  @"L121":
    %"v128" : P = Copy $"glibc_genops#list_all_lock";
    %"v129" = %"v128" +p #8;
    %"chk32" : A = (Check 0 8 Write 8) %"v129";
    store.ptr [%"chk32" + 0] <- #0;
    %"v131" : P = Copy $"glibc_genops#list_all_lock";
    %"chk33" : A = (Check 0 4 Read 1) %"v131";
    %"v135" : W = (RawLoad (LdNarrow Sw) 0) %"chk33"
    => goto "L136";
  @"L136" [%"v138" : W = phi("L121" => %"v135", "L136" => %"v139")]:
    %"chk34" : A = (HalfCheck Lower 0 4 Write 4) %"chk33", %"v131";
    %"v139" : W = (RawCas (CasNarrow Sw) 0) %"chk34", %"v138", #0;
    %"v140" : W = (Cmp Eq W) %"v139", %"v138"
    => br %"v140" ? "L137" : poll "L136";
  @"L137":
    %"v145" : W = (Cmp Sgt W) %"v138", #1
    => br %"v145" ? "L148" : "L103";
  @"L148":
    call void $"__GI___lll_lock_wake_private"(P %"v131")
    => goto "L103";
  @"L122":
    %"v159" : P = Copy $"glibc_genops#list_all_lock";
    %"v160" = %"v159" +p #4;
    %"chk35" : A = (Check 0 4 Read 1) %"v160";
    %"v161" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v162" : W = Sub %"v161", #1;
    %"chk36" : A = (Renew 0 4 Write 1) %"chk35", %"v160";
    store Ww [%"chk36" + 0] <- %"v162"
    => goto "L103";
  @"L103":
    => ret void
} }.

Definition item_glibc_genops'23freeres_list : item :=
  (IData (a "glibc_genops#freeres_list") LLocal 8 [(Zero 8)]).

Definition item_glibc_genops'23list_all_lock : item :=
  (IData (a "glibc_genops#list_all_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition item_glibc_genops'23run_fp : item :=
  (IData (a "glibc_genops#run_fp") LLocal 8 [(Zero 8)]).

Definition fn_glibc_genops'23save_for_backup : func :=
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

Definition item_glibc_genops'23stdio_needs_locking : item :=
  (IData (a "glibc_genops#stdio_needs_locking") LLocal 4 [(Zero 4)]).
