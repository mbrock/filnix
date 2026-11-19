(** This file defines checked IR from glibc’s `locale/loadlocale.os` object.
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

Definition fn__nl_intern_locale_data : func :=
  ir_fn{ "export" "_nl_intern_locale_data"(W %"v0", P %"v2", L %"v4") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v14" : W = (Cmp Ult L) %"v4", #8
    => br %"v14" ? "L18" : "L17" };
  ir_blk{ @"L17":
    %"chk0" : A = (Check 0 4 Read 1) %"v2";
    %"v20" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v25" : W = (Cmp Eq W) %"v0", #3
    => br %"v25" ? "L21" : "L22" };
  ir_blk{ @"L21":
    %"v27" : W = Xor %"v0", #537202708
    => goto "L23" };
  ir_blk{ @"L22":
    %"v32" : W = (Cmp Eq W) %"v0", #0
    => br %"v32" ? "L28" : "L29" };
  ir_blk{ @"L28":
    %"v34" : W = Xor %"v0", #537462560
    => goto "L23" };
  ir_blk{ @"L29":
    %"v36" : W = Xor %"v0", #537071893
    => goto "L23" };
  ir_blk{ @"L23" [%"v38" : W = phi("L21" => %"v27", "L28" => %"v34", "L29" => %"v36")]:
    %"v39" : W = (Cmp Ne W) %"v20", %"v38"
    => goto "L18" };
  ir_blk{ @"L18" [%"v43" : W = phi("start" => #1, "L23" => %"v39")]:
    => br %"v43" ? "L10" : "L12" };
  ir_blk{ @"L10":
    %"v44" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Write 1) %"v44";
    store Ww [%"chk1" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L12":
    %"v50" = %"v2" +p #4;
    %"chk2" : A = (Check 0 4 Read 1) %"v50";
    %"v51" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v52" : P = Copy $"glibc_loadlocale#_nl_category_num_items";
    %"v54" : L = (Ext Sw) %"v0";
    %"v55" : L = Shl %"v54", #3;
    %"v56" = %"v52" +p %"v55";
    %"chk3" : A = (Check 0 8 Read 1) %"v56";
    %"v57" : L = (RawLoad LdL 0) %"chk3";
    %"v58" : L = (Ext Uw) %"v51";
    %"v59" : W = (Cmp Ult L) %"v58", %"v57"
    => br %"v59" ? "L63" : "L62" };
  ir_blk{ @"L62":
    %"v65" = %"v2" +p #4;
    %"chk4" : A = (Renew 0 4 Read 1) %"chk2", %"v65";
    %"v66" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v67" : L = (Ext Uw) %"v66";
    %"v68" : L = Shl %"v67", #2;
    %"v69" : L = Add %"v68", #8;
    %"v71" : W = (Cmp Uge L) %"v69", %"v4"
    => goto "L63" };
  ir_blk{ @"L63" [%"v75" : W = phi("L12" => #1, "L62" => %"v71")]:
    => br %"v75" ? "L46" : "L48" };
  ir_blk{ @"L46":
    %"v76" : P = Copy $"__libc_errno";
    %"chk5" : A = (Check 0 4 Write 1) %"v76";
    store Ww [%"chk5" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L48":
    %"v80" = %"v2" +p #4;
    %"chk6" : A = (Renew 0 4 Read 1) %"chk2", %"v80";
    %"v81" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v82" : L = (Ext Uw) %"v81";
    %"v83" : L = Shl %"v82", #3;
    %"v84" : L = Add %"v83", #56;
    %"iw_1.v8" : W = (Cmp Eq W) %"v0", #0
    => br %"iw_1.v8" ? "iw_1.join" : "iw_1.L6" };
  ir_blk{ @"iw_1.L6":
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join" [%"v87" : L = phi("iw_1.L6" => #0, "L48" => #24)]:
    %"v90" : L = Add %"v84", %"v87";
    call %"v91" : P = $"malloc"(L %"v90");
    %"v96" : L = Ptoi %"v91";
    %"v97" : L = Ptoi #0;
    %"v98" : W = (Cmp Eq L) %"v96", %"v97"
    => br %"v98" ? "L92" : "L94" };
  ir_blk{ @"L92":
    => ret #0 };
  ir_blk{ @"L94":
    %"v101" = %"v91" +p #8;
    %"chk7" : A = (Check 0 8 Write 8) %"v101";
    store.ptr [%"chk7" + 0] <- %"v2";
    %"v104" = %"v91" +p #16;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 1) %"chk7", %"v104";
    store Wl [%"chk8" + 0] <- %"v4";
    %"v110" : W = (Cmp Eq L) %"v87", #0
    => br %"v110" ? "L106" : "L107" };
  ir_blk{ @"L106":
    %"v112" = %"v91" +p #32;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v112";
    store.ptr [%"chk9" + 0] <- #0
    => goto "L108" };
  ir_blk{ @"L107":
    %"v114" = %"v91" +p #32;
    %"v117" = %"v91" +p %"v84";
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v114";
    store.ptr [%"chk10" + 0] <- %"v117";
    %"chk11" : A = (Renew 0 8 Read 8) %"chk10", %"v114";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk11";
    call %"v122" : P = $"__GI_memset"(P %"v120", W #0, L %"v87")
    => goto "L108" };
  ir_blk{ @"L108":
    %"v124" = %"v91" +p #40;
    %"chk12" : A = (HalfCheck Upper 0 4 Write 1) %"chk7", %"v124";
    store Ww [%"chk12" + 0] <- #0;
    %"v126" = %"v91" +p #44;
    %"chk13" : A = (HalfCheck Upper 0 4 Write 1) %"chk7", %"v126";
    store Ww [%"chk13" + 0] <- #0;
    %"v128" = %"v91" +p #48;
    %"v130" = %"v2" +p #4;
    %"chk14" : A = (Renew 0 4 Read 1) %"chk2", %"v130";
    %"v131" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"chk15" : A = (HalfCheck Upper 0 4 Write 1) %"chk7", %"v128";
    store Ww [%"chk15" + 0] <- %"v131"
    => goto "L132" };
  ir_blk{ @"L132" [%"pr.1" : L = phi("L108" => #0, "L134" => %"v356")]:
    %"v138" = %"v91" +p #48;
    %"chk16" : A = (Renew 0 4 Read 1) %"chk15", %"v138";
    %"v139" : W = (RawLoad (LdNarrow Uw) 0) %"chk16";
    %"v140" : L = (Ext Uw) %"v139";
    %"v141" : W = (Cmp Ult L) %"pr.1", %"v140"
    => br %"v141" ? "L133" : "L135" };
  ir_blk{ @"L133":
    %"v144" = %"v2" +p #8;
    %"v146" : L = Shl %"pr.1", #2;
    %"v147" = %"v144" +p %"v146";
    %"chk17" : A = (Check 0 4 Read 1) %"v147";
    %"v148" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v149" : L = (Ext Uw) %"v148";
    %"v155" = %"v91" +p #16;
    %"chk18" : A = (Renew 0 8 Read 1) %"chk8", %"v155";
    %"v156" : L = (RawLoad LdL 0) %"chk18";
    %"v157" : W = (Cmp Ugt L) %"v149", %"v156"
    => br %"v157" ? "L160" : "L165" };
  ir_blk{ @"L160":
    call void $"free"(P %"v91");
    %"v162" : P = Copy $"__libc_errno";
    %"chk19" : A = (Check 0 4 Write 1) %"v162";
    store Ww [%"chk19" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L167":
    %"v173" : W = (Cmp Uge L) %"pr.1", #6
    => br %"v173" ? poll "L160" : "L166" };
  ir_blk{ @"L175":
    %"v181" : W = (Cmp Uge L) %"pr.1", #159
    => br %"v181" ? poll "L160" : "L166" };
  ir_blk{ @"L183":
    %"v189" : W = (Cmp Uge L) %"pr.1", #19
    => br %"v189" ? poll "L160" : "L166" };
  ir_blk{ @"L191":
    %"v197" : W = (Cmp Uge L) %"pr.1", #46
    => br %"v197" ? poll "L160" : "L166" };
  ir_blk{ @"L199":
    %"v205" : W = (Cmp Uge L) %"pr.1", #5
    => br %"v205" ? poll "L160" : "L166" };
  ir_blk{ @"L207":
    %"v213" : W = (Cmp Uge L) %"pr.1", #3
    => br %"v213" ? poll "L160" : "L166" };
  ir_blk{ @"L215":
    %"v221" : W = (Cmp Uge L) %"pr.1", #7
    => br %"v221" ? poll "L160" : "L166" };
  ir_blk{ @"L223":
    %"v229" : W = (Cmp Uge L) %"pr.1", #13
    => br %"v229" ? poll "L160" : "L166" };
  ir_blk{ @"L231":
    %"v237" : W = (Cmp Uge L) %"pr.1", #5
    => br %"v237" ? poll "L160" : "L166" };
  ir_blk{ @"L239":
    %"v245" : W = (Cmp Uge L) %"pr.1", #2
    => br %"v245" ? poll "L160" : "L166" };
  ir_blk{ @"L247":
    %"v253" : W = (Cmp Uge L) %"pr.1", #16
    => br %"v253" ? poll "L160" : "L166" };
  ir_blk{ @"L255":
    => br %"iw_1.v8" ? "L166" : "L257" };
  ir_blk{ @"L257":
    %"v261" : P = Copy $"glibc_loadlocale#str.240";
    %"v262" : P = Copy $"glibc_loadlocale#str.241";
    %"v263" : P = Copy $"glibc_loadlocale#str.242";
    call void $"__libc_assert_fail"(P %"v261", P %"v262", W #206, P %"v263")
    => goto "L166" }] [ir_blk{ @"L165":
    %"v265" : W = (Cmp Slt W) %"v0", #7
    => br %"v265" ? "L266" : "L267" };
  ir_blk{ @"L266":
    %"v268" : W = (Cmp Slt W) %"v0", #3
    => br %"v268" ? "L269" : "L270" };
  ir_blk{ @"L269":
    %"v271" : W = (Cmp Eq W) %"v0", #1
    => br %"v271" ? poll "L167" : "L272" };
  ir_blk{ @"L272":
    %"v273" : W = (Cmp Eq W) %"v0", #2
    => br %"v273" ? poll "L175" : poll "L255" };
  ir_blk{ @"L270":
    %"v275" : W = (Cmp Eq W) %"v0", #3
    => br %"v275" ? poll "L183" : "L276" };
  ir_blk{ @"L276":
    %"v277" : W = (Cmp Eq W) %"v0", #4
    => br %"v277" ? poll "L191" : "L278" };
  ir_blk{ @"L278":
    %"v279" : W = (Cmp Eq W) %"v0", #5
    => br %"v279" ? poll "L199" : poll "L255" };
  ir_blk{ @"L267":
    %"v281" : W = (Cmp Slt W) %"v0", #10
    => br %"v281" ? "L282" : "L283" };
  ir_blk{ @"L282":
    %"v284" : W = (Cmp Eq W) %"v0", #7
    => br %"v284" ? poll "L207" : "L285" };
  ir_blk{ @"L285":
    %"v286" : W = (Cmp Eq W) %"v0", #8
    => br %"v286" ? poll "L215" : "L287" };
  ir_blk{ @"L287":
    %"v288" : W = (Cmp Eq W) %"v0", #9
    => br %"v288" ? poll "L223" : poll "L255" };
  ir_blk{ @"L283":
    %"v290" : W = (Cmp Eq W) %"v0", #10
    => br %"v290" ? poll "L231" : "L291" };
  ir_blk{ @"L291":
    %"v292" : W = (Cmp Eq W) %"v0", #11
    => br %"v292" ? poll "L239" : "L293" };
  ir_blk{ @"L293":
    %"v294" : W = (Cmp Eq W) %"v0", #12
    => br %"v294" ? poll "L247" : poll "L255" };
  ir_blk{ @"L166":
    => br %"iw_1.v8" ? "L301" : "L302" };
  ir_blk{ @"L301":
    %"v305" : W = (Cmp Uge L) %"pr.1", #86
    => goto "L302" };
  ir_blk{ @"L302" [%"v307" : W = phi("L166" => #0, "L301" => %"v305")]:
    => br %"v307" ? "L309" : "L308" };
  ir_blk{ @"L308":
    %"v310" : P = Copy $"glibc_loadlocale#_nl_value_types";
    %"v314" = %"v310" +p %"v55";
    %"chk20" : A = (Check 0 8 Read 8) %"v314";
    %"v315" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v318" = %"v315" +p %"v146";
    %"chk21" : A = (Check 0 4 Read 1) %"v318";
    %"v319" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v320" : W = (Cmp Ne W) %"v319", #5
    => goto "L309" };
  ir_blk{ @"L309" [%"v324" : W = phi("L302" => #1, "L308" => %"v320")]:
    => br %"v324" ? "L296" : "L297" };
  ir_blk{ @"L296":
    %"v326" = %"v91" +p #56;
    %"v328" : L = Shl %"pr.1", #3;
    %"v329" = %"v326" +p %"v328";
    %"v331" = %"v91" +p #8;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk7", %"v331";
    %"v332" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v334" = %"v332" +p %"v149";
    %"chk23" : A = (Check 0 8 Write 8) %"v329";
    store.ptr [%"chk23" + 0] <- %"v334"
    => goto "L134" };
  ir_blk{ @"L297":
    %"v340" : L = And %"v149", #3;
    %"v342" : W = (Cmp Ne L) %"v340", #0
    => br %"v342" ? poll "L160" : "L337" };
  ir_blk{ @"L337":
    %"v345" = %"v91" +p #56;
    %"v347" : L = Shl %"pr.1", #3;
    %"v348" = %"v345" +p %"v347";
    %"v350" = %"v91" +p #8;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk7", %"v350";
    %"v351" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v353" = %"v351" +p %"v149";
    %"chk25" : A = (Check 0 4 Read 1) %"v353";
    %"v354" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"chk26" : A = (Check 0 4 Write 1) %"v348";
    store Ww [%"chk26" + 0] <- %"v354"
    => goto "L134" };
  ir_blk{ @"L134":
    %"v356" : L = Add %"pr.1", #1
    => goto poll "L132" };
  ir_blk{ @"L135":
    %"v361" : W = (Cmp Ugt L) %"v87", #0
    => br %"v361" ? "iw_2.start" : "L359" };
  ir_blk{ @"iw_2.start":
    => br %"iw_1.v8" ? "iw_2.iw_1.start" : "L359" };
  ir_blk{ @"iw_2.iw_1.start":
    %"iw_2.iw_1.v4" = %"v91" +p #32;
    %"chk27" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"iw_2.iw_1.v4";
    %"iw_2.iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"iw_2.iw_1.v7" = %"iw_2.iw_1.v5" +p #9;
    call %"iw_2.iw_1.v8" : P = $"__GI_memset"(P %"iw_2.iw_1.v7", W #1, L #10)
    => goto "iw_2.iw_1.L10" };
  ir_blk{ @"iw_2.iw_1.L10" [%"iw_2.iw_1.pr.1" : W = phi("iw_2.iw_1.L12" => %"iw_2.iw_1.v83", "iw_2.iw_1.start" => #0)]:
    %"iw_2.iw_1.v15" : W = (Cmp Sle W) %"iw_2.iw_1.pr.1", #9
    => br %"iw_2.iw_1.v15" ? "iw_2.iw_1.L11" : "L359" };
  ir_blk{ @"iw_2.iw_1.L11":
    %"iw_2.iw_1.v18" = %"v91" +p #56;
    %"iw_2.iw_1.v20" : W = Add %"iw_2.iw_1.pr.1", #41;
    %"iw_2.iw_1.v21" : W = And %"iw_2.iw_1.v20", #65535;
    %"iw_2.iw_1.v22" : L = (Ext Sw) %"iw_2.iw_1.v21";
    %"iw_2.iw_1.v23" : L = Shl %"iw_2.iw_1.v22", #3;
    %"iw_2.iw_1.v24" = %"iw_2.iw_1.v18" +p %"iw_2.iw_1.v23";
    %"chk28" : A = (Check 0 8 Read 8) %"iw_2.iw_1.v24";
    %"iw_2.iw_1.v25" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"chk29" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v25";
    %"iw_2.iw_1.v32" : W = (RawLoad (LdNarrow Sb) 0) %"chk29";
    %"iw_2.iw_1.v34" : W = Add %"iw_2.iw_1.pr.1", #48;
    %"iw_2.iw_1.v35" : W = (Cmp Ne W) %"iw_2.iw_1.v32", %"iw_2.iw_1.v34"
    => br %"iw_2.iw_1.v35" ? "iw_2.iw_1.L37" : "iw_2.iw_1.L36" };
  ir_blk{ @"iw_2.iw_1.L36":
    %"iw_2.iw_1.v39" = %"iw_2.iw_1.v25" +p #1;
    %"chk30" : A = (HalfCheck Upper 0 1 Read 1) %"chk29", %"iw_2.iw_1.v39";
    %"iw_2.iw_1.v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk30";
    %"iw_2.iw_1.v41" : W = (Cmp Ne W) %"iw_2.iw_1.v40", #0
    => goto "iw_2.iw_1.L37" };
  ir_blk{ @"iw_2.iw_1.L37" [%"iw_2.iw_1.v43" : W = phi("iw_2.iw_1.L11" => #1, "iw_2.iw_1.L36" => %"iw_2.iw_1.v41")]:
    => br %"iw_2.iw_1.v43" ? "iw_2.iw_1.L27" : "iw_2.iw_1.L29" };
  ir_blk{ @"iw_2.iw_1.L27":
    %"iw_2.iw_1.v45" = %"iw_2.iw_1.v5" +p #8;
    %"chk31" : A = (Check 0 1 Write 1) %"iw_2.iw_1.v45";
    store Wb [%"chk31" + 0] <- #1;
    %"iw_2.iw_1.v48" = %"v91" +p #56;
    %"iw_2.iw_1.v54" = %"iw_2.iw_1.v48" +p %"iw_2.iw_1.v23";
    %"chk32" : A = (Check 0 8 Read 8) %"iw_2.iw_1.v54";
    %"iw_2.iw_1.v55" : P = (RawLoadPointer 0 load_effects) %"chk32";
    call %"iw_2.iw_1.v56" : L = $"__GI_strlen"(P %"iw_2.iw_1.v55");
    %"iw_2.iw_1.v57" : W = (Ext Ub) %"iw_2.iw_1.v56"
    => goto "iw_2.iw_1.L29" };
  ir_blk{ @"iw_2.iw_1.L29" [%"iw_2.iw_1.pr.2" : W = phi("iw_2.iw_1.L27" => %"iw_2.iw_1.v57", "iw_2.iw_1.L37" => #1)]:
    %"iw_2.iw_1.v59" = %"iw_2.iw_1.v5" +p #9;
    %"iw_2.iw_1.v61" : L = (Ext Sw) %"iw_2.iw_1.pr.1";
    %"iw_2.iw_1.v62" = %"iw_2.iw_1.v59" +p %"iw_2.iw_1.v61";
    %"iw_2.iw_1.v63" : W = (Ext Ub) %"iw_2.iw_1.pr.2";
    %"chk33" : A = (Check 0 1 Write 1) %"iw_2.iw_1.v62";
    store Wb [%"chk33" + 0] <- %"iw_2.iw_1.v63";
    %"iw_2.iw_1.v68" : W = (Cmp Eq W) %"iw_2.iw_1.pr.1", #0
    => br %"iw_2.iw_1.v68" ? "iw_2.iw_1.L64" : "iw_2.iw_1.L65" };
  ir_blk{ @"iw_2.iw_1.L64":
    %"iw_2.iw_1.v70" = %"iw_2.iw_1.v5" +p #19;
    %"chk34" : A = (Check 0 1 Write 1) %"iw_2.iw_1.v70";
    store Wb [%"chk34" + 0] <- %"iw_2.iw_1.v63"
    => goto "iw_2.iw_1.L12" };
  ir_blk{ @"iw_2.iw_1.L65":
    %"iw_2.iw_1.v76" = %"iw_2.iw_1.v5" +p #19;
    %"chk35" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v76";
    %"iw_2.iw_1.v77" : W = (RawLoad (LdNarrow Ub) 0) %"chk35";
    %"iw_2.iw_1.v79" : W = (Cmp Ne W) %"iw_2.iw_1.v77", %"iw_2.iw_1.v63"
    => br %"iw_2.iw_1.v79" ? "iw_2.iw_1.L72" : "iw_2.iw_1.L12" };
  ir_blk{ @"iw_2.iw_1.L72":
    %"iw_2.iw_1.v81" = %"iw_2.iw_1.v5" +p #19;
    %"chk36" : A = (Renew 0 1 Write 1) %"chk35", %"iw_2.iw_1.v81";
    store Wb [%"chk36" + 0] <- #0
    => goto "iw_2.iw_1.L12" };
  ir_blk{ @"iw_2.iw_1.L12":
    %"iw_2.iw_1.v83" : W = Add %"iw_2.iw_1.pr.1", #1
    => goto poll "iw_2.iw_1.L10" };
  ir_blk{ @"L359":
    => ret %"v91" }])) }.

Definition fn__nl_load_locale : func :=
  ir_fn{ "export" "_nl_load_locale"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v6" : P = (Alloc 8) #144;
    %"v11" = %"v0" +p #16;
    %"chk0" : A = (Check 0 8 Write 8) %"v11";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v15" : W = $"__GI___open_nocancel"(P %"v13", W #524288);
    %"v20" : L = (Ext Sw) %"v15";
    %"v21" : W = (Cmp Slt L) %"v20", #0
    => br %"v21" ? "L16" : "L18";
  @"L16":
    => ret void;
  @"L18":
    call %"v27" : W = $"__GI___fstat64"(W %"v15", P %"v6");
    %"v28" : W = (Cmp Slt W) %"v27", #0
    => br %"v28" ? "L31" : "L25";
  @"L31" [%"pr.1" : W = phi("L18" => %"v15", "L82" => %"v79", "L153" => %"pr.2", "L147" => %"pr.2")]:
    call void $"__GI___close_nocancel_nostatus"(W %"pr.1")
    => ret void;
  @"L25":
    %"v37" = %"v6" +p #24;
    %"chk2" : A = (Check 0 4 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v39" : W = And %"v38", #61440;
    %"v40" : W = (Cmp Eq W) %"v39", #16384
    => br %"v40" ? "L34" : "L36";
  @"L34":
    call void $"__GI___close_nocancel_nostatus"(W %"v15");
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call %"v48" : L = $"__GI_strlen"(P %"v47");
    %"v50" : L = Add %"v48", #5;
    %"v51" : P = Copy $"_nl_category_name_sizes";
    %"v53" : L = (Ext Sw) %"v2";
    %"v54" = %"v51" +p %"v53";
    %"chk4" : A = (Check 0 1 Read 1) %"v54";
    %"v55" : W = (RawLoad (LdNarrow Ub) 0) %"chk4";
    %"v56" : L = (Ext Uw) %"v55";
    %"v57" : L = Add %"v50", %"v56";
    %"v58" : L = Add %"v57", #1;
    %"v59" : P = (Alloc 16) %"v58";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v64" : P = $"__GI_mempcpy"(P %"v59", P %"v62", L %"v48");
    %"v65" : P = Copy $"glibc_loadlocale#str.243";
    call %"v66" : P = $"__GI_mempcpy"(P %"v64", P %"v65", L #5);
    %"iw_1.v2" : P = Copy $"_nl_category_names";
    %"iw_1.v3" : P = Copy $"_nl_category_name_idxs";
    %"iw_1.v6" = %"iw_1.v3" +p %"v53";
    %"chk6" : A = (Check 0 1 Read 1) %"iw_1.v6";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk6";
    %"iw_1.v8" : L = (Ext Uw) %"iw_1.v7";
    %"iw_1.v9" = %"iw_1.v2" +p %"iw_1.v8";
    %"v69" : P = Copy $"_nl_category_name_sizes";
    %"v72" = %"v69" +p %"v53";
    %"chk7" : A = (Check 0 1 Read 1) %"v72";
    %"v73" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v74" : W = Add %"v73", #1;
    %"v75" : L = (Ext Sw) %"v74";
    call %"v76" : P = $"__GI_mempcpy"(P %"v66", P %"iw_1.v9", L %"v75");
    call %"v79" : W = $"__GI___open_nocancel"(P %"v59", W #524288);
    %"v84" : L = (Ext Sw) %"v79";
    %"v85" : W = (Cmp Slt L) %"v84", #0
    => br %"v85" ? "L80" : "L82";
  @"L80":
    => ret void;
  @"L82":
    call %"v91" : W = $"__GI___fstat64"(W %"v79", P %"v6");
    %"v92" : W = (Cmp Slt W) %"v91", #0
    => br %"v92" ? poll "L31" : "L36";
  @"L36" [%"pr.2" : W = phi("L82" => %"v79", "L25" => %"v15")]:
    %"v96" : P = Copy $"__libc_errno";
    %"chk8" : A = (Check 0 4 Read 1) %"v96";
    %"v97" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v98" = %"v6" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 1) %"chk2", %"v98";
    %"v99" : L = (RawLoad LdL 0) %"chk9";
    call %"v102" : P = $"__GI___mmap"(P #0, L %"v99", W #1, W #2, W %"pr.2", L #0);
    (Flight (a "v109") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v110" : L = Ptoi %"v102";
    %"v111" : L = Ptoi %"v109";
    %"v112" : W = (Cmp Eq L) %"v110", %"v111"
    => br %"v112" ? "L103" : "L105";
  @"L103":
    %"v118" : P = Copy $"__libc_errno";
    %"chk10" : A = (Check 0 4 Read 1) %"v118";
    %"v119" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v120" : L = (Ext Sw) %"v119";
    %"v121" : W = (Cmp Eq L) %"v120", #38
    => br %"v121" ? "L115" : "L105";
  @"L115":
    %"v122" = %"v6" +p #48;
    %"chk11" : A = (Renew 0 8 Read 1) %"chk9", %"v122";
    %"v123" : L = (RawLoad LdL 0) %"chk11";
    call %"v124" : P = $"malloc"(L %"v123");
    %"v129" : L = Ptoi %"v124";
    %"v130" : L = Ptoi #0;
    %"v131" : W = (Cmp Ne L) %"v129", %"v130"
    => br %"v131" ? "L125" : "L105";
  @"L125":
    %"v133" = %"v6" +p #48;
    %"chk12" : A = (Renew 0 8 Read 1) %"chk9", %"v133";
    %"v134" : L = (RawLoad LdL 0) %"chk12"
    => goto "L138";
  @"L138" [%"pr.8" : P = phi("L125" => %"v124", "L149" => %"v162"); %"pr.7" : L = phi("L125" => %"v134", "L149" => %"v165")]:
    %"v142" : W = (Cmp Sgt L) %"pr.7", #0
    => br %"v142" ? "L139" : "L140";
  @"L139":
    call %"v146" : L = $"__GI___read_nocancel"(W %"pr.2", P %"pr.8", L %"pr.7");
    %"v151" : W = (Cmp Sle L) %"v146", #0
    => br %"v151" ? "L147" : "L149";
  @"L147":
    call void $"free"(P %"v124");
    %"v157" : W = (Cmp Eq L) %"v146", #0
    => br %"v157" ? "L153" : poll "L31";
  @"L153":
    %"v158" : P = Copy $"__libc_errno";
    %"chk13" : A = (Check 0 4 Write 1) %"v158";
    store Ww [%"chk13" + 0] <- #22
    => goto poll "L31";
  @"L149":
    %"v162" = %"pr.8" +p %"v146";
    %"v165" : L = Sub %"pr.7", %"v146"
    => goto poll "L138";
  @"L140":
    %"v166" : P = Copy $"__libc_errno";
    %"chk14" : A = (Check 0 4 Write 1) %"v166";
    store Ww [%"chk14" + 0] <- %"v97"
    => goto "L105";
  @"L105" [%"pr.5" : W = phi("L140" => #0, "L115" => #0, "L103" => #1, "L36" => #1); %"pr.3" : P = phi("L140" => %"v124", "L115" => %"v124", "L103" => #0, "L36" => %"v102")]:
    call void $"__GI___close_nocancel_nostatus"(W %"pr.2");
    %"v173" : L = Ptoi %"pr.3";
    %"v174" : L = Ptoi #0;
    %"v175" : W = (Cmp Eq L) %"v173", %"v174"
    => br %"v175" ? "L169" : "L171";
  @"L169":
    => ret void;
  @"L171":
    %"v181" = %"v6" +p #48;
    %"chk15" : A = (Renew 0 8 Read 1) %"chk9", %"v181";
    %"v182" : L = (RawLoad LdL 0) %"chk15";
    call %"v183" : P = $"_nl_intern_locale_data"(W %"v2", P %"pr.3", L %"v182");
    %"v188" : L = Ptoi %"v183";
    %"v190" : W = (Cmp Eq L) %"v188", %"v174"
    => br %"v190" ? "L184" : "L186";
  @"L184":
    => br %"pr.5" ? "L193" : "L195";
  @"L193":
    %"v199" = %"v6" +p #48;
    %"chk16" : A = (Renew 0 8 Read 1) %"chk9", %"v199";
    %"v200" : L = (RawLoad LdL 0) %"chk16";
    call %"v201" : W = $"__GI___munmap"(P %"pr.3", L %"v200")
    => goto "L195";
  @"L195":
    => ret void;
  @"L186":
    %"chk17" : A = (Check 0 8 Write 8) %"v183";
    store.ptr [%"chk17" + 0] <- #0;
    %"v205" = %"v183" +p #24;
    %"chk18" : A = (HalfCheck Upper 0 4 Write 1) %"chk17", %"v205";
    store Ww [%"chk18" + 0] <- %"pr.5";
    %"v208" = %"v0" +p #16;
    %"chk19" : A = (Renew 0 8 Write 8) %"chk0", %"v208";
    store.ptr [%"chk19" + 0] <- %"v183";
    %"v211" = %"v0" +p #8;
    %"chk20" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v211";
    store Ww [%"chk20" + 0] <- #1
    => ret void
} }.

Definition item_glibc_loadlocale'23_nl_category_num_items : item :=
  (IData (a "glibc_loadlocale#_nl_category_num_items") (LRo (a "local")) 8 [(Item Wl 86); (Item Wl 6); (Item Wl 159); (Item Wl 19); (Item Wl 46); (Item Wl 5); (Zero 8); (Item Wl 3); (Item Wl 7); (Item Wl 13); (Item Wl 5); (Item Wl 2); (Item Wl 16)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_ADDRESS : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_ADDRESS") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 5); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_COLLATE : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_COLLATE") (LRo (a "local")) 4 [(Item Ww 5); (Item Ww 1); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Zero 12); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 5); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_CTYPE : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_CTYPE") (LRo (a "local")) 4 (app [(Item Ww 8); (Item Ww 8); (Zero 4); (Item Ww 8); (Zero 4); (Item Ww 8); (Zero 16); (Item Ww 6); (Item Ww 6); (Item Ww 4); (Item Ww 5); (Item Ww 1); (Item Ww 8); (Item Ww 8); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 5); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8)] [(Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 5); (Item Ww 8); (Item Ww 5); (Item Ww 1); (Item Ww 5); (Item Ww 5); (Zero 56)])).

Definition item_glibc_loadlocale'23_nl_value_type_LC_IDENTIFICATION : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_IDENTIFICATION") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 2); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_MEASUREMENT : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_MEASUREMENT") (LRo (a "local")) 4 [(Item Ww 3); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_MESSAGES : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_MESSAGES") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_MONETARY : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_MONETARY") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 4); (Item Ww 1); (Item Ww 1); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 1); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 1); (Item Ww 1); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 5); (Item Ww 7); (Item Ww 5); (Item Ww 5); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_NAME : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_NAME") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_NUMERIC : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_NUMERIC") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 4); (Item Ww 5); (Item Ww 5); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_PAPER : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_PAPER") (LRo (a "local")) 4 [(Item Ww 5); (Item Ww 5); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_TELEPHONE : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_TELEPHONE") (LRo (a "local")) 4 [(Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1)]).

Definition item_glibc_loadlocale'23_nl_value_type_LC_TIME : item :=
  (IData (a "glibc_loadlocale#_nl_value_type_LC_TIME") (LRo (a "local")) 4 [(Item Ww 2); (Zero 24); (Item Ww 2); (Zero 24); (Item Ww 2); (Zero 44); (Item Ww 2); (Zero 44); (Item Ww 2); (Zero 4); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 1); (Item Ww 6); (Item Ww 1); (Item Ww 1); (Item Ww 6); (Item Ww 1); (Item Ww 1); (Item Ww 5); (Item Ww 1); (Item Ww 9); (Zero 24); (Item Ww 9); (Zero 24); (Item Ww 9); (Zero 44); (Item Ww 9); (Zero 44); (Item Ww 9); (Zero 4); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 8); (Item Ww 10); (Item Ww 8); (Item Ww 8); (Item Ww 3); (Item Ww 5); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 3); (Item Ww 1); (Item Ww 1); (Item Ww 8); (Item Ww 1); (Item Ww 2); (Zero 44); (Item Ww 9); (Zero 44); (Item Ww 2); (Zero 44); (Item Ww 9); (Zero 44)]).

Definition item_glibc_loadlocale'23_nl_value_types : item :=
  (IData (a "glibc_loadlocale#_nl_value_types") (LRo (a "local")) 8 [(Sym (a "glibc_loadlocale#_nl_value_type_LC_CTYPE") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_NUMERIC") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_TIME") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_COLLATE") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_MONETARY") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_MESSAGES") 0); (Zero 8); (Sym (a "glibc_loadlocale#_nl_value_type_LC_PAPER") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_NAME") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_ADDRESS") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_TELEPHONE") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_MEASUREMENT") 0); (Sym (a "glibc_loadlocale#_nl_value_type_LC_IDENTIFICATION") 0)]).

Definition item_glibc_loadlocale'23str'2e240 : item :=
  (IData (a "glibc_loadlocale#str.240") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 103); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 67); (Item Wb 95); (Item Wb 67); (Item Wb 84); (Item Wb 89); (Item Wb 80); (Item Wb 69); (Item Wb 0)]).

Definition item_glibc_loadlocale'23str'2e241 : item :=
  (IData (a "glibc_loadlocale#str.241") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 111); (Item Wb 97); (Item Wb 100); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_loadlocale'23str'2e242 : item :=
  (IData (a "glibc_loadlocale#str.242") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 110); (Item Wb 108); (Item Wb 95); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 95); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 0)]).

Definition item_glibc_loadlocale'23str'2e243 : item :=
  (IData (a "glibc_loadlocale#str.243") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 83); (Item Wb 89); (Item Wb 83); (Item Wb 95); (Item Wb 0)]).
