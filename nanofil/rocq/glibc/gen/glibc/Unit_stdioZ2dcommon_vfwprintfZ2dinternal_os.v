(** This file defines checked IR from glibc’s `stdio-common/vfwprintf-internal.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os_Blocks_5f5f777072696e74665f627566666572_1 Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os_Blocks_5f5f777072696e74665f627566666572_2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___vfwprintf_internal : func :=
  ir_fn{ "export" "__vfwprintf_internal"(P %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    %"v169" : P = (Alloc 8) #560;
    %"v178" : P = (Alloc 8) #32;
    %"v281" : P = (Alloc 8) #560;
    call %"v53" : W = $"_IO_fwide"(P %"v0", W #1);
    %"v55" : W = (Cmp Ne W) %"v53", #1
    => br %"v55" ? "L8" : "L63";
  @"L8":
    => ret #4294967295;
  @"L63":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v68" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v69" : W = And %"v68", #8
    => br %"v69" ? "L64" : "L66";
  @"L64":
    %"v71" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v72" : W = Or %"v71", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v72";
    %"v73" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"v73";
    store Ww [%"chk3" + 0] <- #9
    => ret #4294967295;
  @"L66":
    %"v80" : L = Ptoi %"v2";
    %"v81" : L = Ptoi #0;
    %"v82" : W = (Cmp Eq L) %"v80", %"v81"
    => br %"v82" ? "L76" : "L123";
  @"L76":
    %"v83" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v83";
    store Ww [%"chk4" + 0] <- #22
    => ret #4294967295;
  @"L123":
    call %"v146" : W = $"_IO_fwide"(P %"v0", W #1);
    %"v154" : W = (Cmp Ne W) %"v146", #1
    => br %"v154" ? "L86" : "L88";
  @"L86":
    => ret #(-1);
  @"L88":
    %"v162" = %"v0" +p #116;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v162";
    %"v163" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v164" : W = Shl %"v163", #8;
    %"v165" : W = Sar %"v164", #8;
    %"v166" : W = And %"v165", #128;
    %"v168" : W = (Cmp Eq W) %"v166", #0
    => br %"v168" ? "L158" : "L160";
  @"L158":
    call void $"__wprintf_buffer_to_file_init"(P %"v169", P %"v0");
    call void $"__wprintf_buffer"(P %"v169", P %"v2", P %"v4", W %"v6");
    call %"v174" : W = $"__wprintf_buffer_to_file_done"(P %"v169")
    => ret %"v174";
  @"L160":
    %"v180" : P = Copy $"_IO_funlockfile";
    %"v181" = %"v178" +p #8;
    %"chk6" : A = (Check 0 8 Write 8) %"v181";
    store.ptr [%"chk6" + 0] <- %"v0";
    %"chk7" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v187" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v188" : W = And %"v187", #32768;
    %"v189" : W = (Cmp Eq W) %"v188", #0
    => br %"v189" ? "L183" : "L185";
  @"L183":
    %"chk8" : A = (HalfCheck Lower 0 8 Write 8) %"chk6", %"v178";
    store.ptr [%"chk8" + 0] <- %"v180";
    call void $"__GI___libc_cleanup_push_defer"(P %"v178")
    => goto "L185";
  @"L185" [%"pr.5" : W = phi("L183" => #1, "L160" => #0)]:
    %"chk9" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v197" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v198" : W = And %"v197", #32768;
    %"v199" : W = (Cmp Eq W) %"v198", #0
    => br %"v199" ? "L200" : "L195";
  @"L200":
    call %"v204" : P = $"zthread_self_cookie"();
    %"v208" : P = Copy $"__libc_single_threaded_internal";
    %"chk10" : A = (Check 0 1 Read 1) %"v208";
    %"v209" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"v210" : W = (Cmp Ne W) %"v209", #0
    => br %"v210" ? "L211" : "L212";
  @"L211":
    %"v214" = %"v0" +p #136;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v216" = %"v215" +p #8;
    %"chk12" : A = (Check 0 8 Read 8) %"v216";
    %"v217" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v218" : L = Ptoi %"v217";
    %"v220" : W = (Cmp Eq L) %"v218", %"v81"
    => goto "L212";
  @"L212" [%"v222" : W = phi("L200" => #0, "L211" => %"v220")]:
    => br %"v222" ? "L205" : "L206";
  @"L205":
    %"v224" = %"v0" +p #136;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v224";
    %"v225" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 4 Write 1) %"v225";
    store Ww [%"chk14" + 0] <- #1;
    %"v228" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v229" = %"v228" +p #8;
    %"chk16" : A = (Check 0 8 Write 8) %"v229";
    store.ptr [%"chk16" + 0] <- %"v204"
    => goto "L195";
  @"L206":
    %"v235" = %"v0" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v235";
    %"v236" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v237" = %"v236" +p #8;
    %"chk18" : A = (Check 0 8 Read 8) %"v237";
    %"v238" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v240" : L = Ptoi %"v238";
    %"v241" : L = Ptoi %"v204";
    %"v242" : W = (Cmp Ne L) %"v240", %"v241"
    => br %"v242" ? "L231" : "L232";
  @"L231":
    %"v245" = %"v0" +p #136;
    %"v246" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk20" : A = (Check 0 4 Write 4) %"v246";
    %"v253" : W = (RawCas (CasNarrow Sw) 0) %"chk20", #0, #1;
    %"v254" : W = (Cmp Eq W) %"v253", #0
    => br %"v254" ? "L256" : "L255";
  @"L255":
    => goto "L256";
  @"L256":
    %"v257" : W = (Cmp Ne W) %"v253", #0
    => br %"v257" ? "L260" : "L249";
  @"L260":
    call void $"__GI___lll_lock_wait_private"(P %"v246")
    => goto "L249";
  @"L249":
    %"v271" = %"v0" +p #136;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk17", %"v271";
    %"v272" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v273" = %"v272" +p #8;
    %"chk22" : A = (Check 0 8 Write 8) %"v273";
    store.ptr [%"chk22" + 0] <- %"v204"
    => goto "L195";
  @"L232":
    %"v276" = %"v0" +p #136;
    %"v277" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v278" = %"v277" +p #4;
    %"chk24" : A = (Check 0 4 Read 1) %"v278";
    %"v279" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"v280" : W = Add %"v279", #1;
    %"chk25" : A = (Renew 0 4 Write 1) %"chk24", %"v278";
    store Ww [%"chk25" + 0] <- %"v280"
    => goto "L195";
  @"L195":
    call void $"__wprintf_buffer_to_file_init"(P %"v281", P %"v0");
    call void $"__wprintf_buffer"(P %"v281", P %"v2", P %"v4", W %"v6");
    call %"v286" : W = $"__wprintf_buffer_to_file_done"(P %"v281");
    %"chk26" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v291" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v292" : W = And %"v291", #32768;
    %"v293" : W = (Cmp Eq W) %"v292", #0
    => br %"v293" ? "L294" : "L289";
  @"L294":
    %"v300" : P = Copy $"__libc_single_threaded_internal";
    %"chk27" : A = (Check 0 1 Read 1) %"v300";
    %"v301" : W = (RawLoad (LdNarrow Sb) 0) %"chk27";
    %"v302" : W = (Cmp Ne W) %"v301", #0
    => br %"v302" ? "L303" : "L304";
  @"L303":
    %"v306" = %"v0" +p #136;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v306";
    %"v307" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v308" = %"v307" +p #4;
    %"chk29" : A = (Check 0 4 Read 1) %"v308";
    %"v309" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"v310" : W = (Cmp Eq W) %"v309", #0
    => goto "L304";
  @"L304" [%"v312" : W = phi("L294" => #0, "L303" => %"v310")]:
    => br %"v312" ? "L297" : "L298";
  @"L297":
    %"v314" = %"v0" +p #136;
    %"chk30" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v314";
    %"v315" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v316" = %"v315" +p #8;
    %"chk31" : A = (Check 0 8 Write 8) %"v316";
    store.ptr [%"chk31" + 0] <- #0;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk30", %"v314";
    %"v319" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Check 0 4 Write 1) %"v319";
    store Ww [%"chk33" + 0] <- #0
    => goto "L289";
  @"L298":
    %"v324" = %"v0" +p #136;
    %"chk34" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v324";
    %"v325" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v326" = %"v325" +p #4;
    %"chk35" : A = (Check 0 4 Read 1) %"v326";
    %"v327" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v328" : W = (Cmp Eq W) %"v327", #0
    => br %"v328" ? "L320" : "L321";
  @"L320":
    %"v330" = %"v0" +p #136;
    %"v331" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v332" = %"v331" +p #8;
    %"chk37" : A = (Check 0 8 Write 8) %"v332";
    store.ptr [%"chk37" + 0] <- #0;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk34", %"v330";
    %"v336" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 4 Read 1) %"v336";
    %"v340" : W = (RawLoad (LdNarrow Sw) 0) %"chk39"
    => goto "L341";
  @"L341" [%"v343" : W = phi("L320" => %"v340", "L341" => %"v344")]:
    %"chk40" : A = (HalfCheck Lower 0 4 Write 4) %"chk39", %"v336";
    %"v344" : W = (RawCas (CasNarrow Sw) 0) %"chk40", %"v343", #0;
    %"v345" : W = (Cmp Eq W) %"v344", %"v343"
    => br %"v345" ? "L342" : poll "L341";
  @"L342":
    %"v350" : W = (Cmp Sgt W) %"v343", #1
    => br %"v350" ? "L353" : "L289";
  @"L353":
    call void $"__GI___lll_lock_wake_private"(P %"v336")
    => goto "L289";
  @"L321":
    %"v365" = %"v0" +p #136;
    %"v366" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v367" = %"v366" +p #4;
    %"chk42" : A = (Check 0 4 Read 1) %"v367";
    %"v368" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v369" : W = Sub %"v368", #1;
    %"chk43" : A = (Renew 0 4 Write 1) %"chk42", %"v367";
    store Ww [%"chk43" + 0] <- %"v369"
    => goto "L289";
  @"L289":
    => br %"pr.5" ? "L370" : "L376";
  @"L370":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v178")
    => goto "L376";
  @"L376":
    => ret %"v286"
} }.

Definition fn___wprintf_buffer : func :=
  ir_fn{ "export" "__wprintf_buffer"(P %"v0", P %"v2", P %"v4", W %"v6") -> RVoid blocks (fn___wprintf_buffer'blocks1 ++ fn___wprintf_buffer'blocks2) }.

Definition fn_glibc_vfwprintf_internal'23__find_specwc'2egnu_inline : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__find_specwc.gnu_inline"(P %"v0") -> (RClass P) {
  @"start":
    call %"v3" : P = $"__wcschrnul"(P %"v0", W #37)
    => ret %"v3"
} }.

Definition fn_glibc_vfwprintf_internal'23__printf_fp_spec : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__printf_fp_spec"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v10" = %"v2" +p #8;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = (Cmp Eq W) %"v11", #97
    => br %"v12" ? "L14" : "L13";
  @"L13":
    %"v16" = %"v2" +p #8;
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v18" : W = (Cmp Eq W) %"v17", #65
    => goto "L14";
  @"L14" [%"v20" : W = phi("start" => #1, "L13" => %"v18")]:
    => br %"v20" ? "L6" : "L7";
  @"L6":
    %"v22" : P = Copy $"__libc_tsd_LOCALE";
    %"chk2" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call void $"__wprintf_fphex_l_buffer"(P %"v0", P %"v23", P %"v2", P %"v4")
    => goto "L8";
  @"L7":
    %"v27" : P = Copy $"__libc_tsd_LOCALE";
    %"chk3" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call void $"__wprintf_fp_l_buffer"(P %"v0", P %"v28", P %"v2", P %"v4")
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep0_jumps'2e278 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 1); (Item Ww 2); (Item Ww 3); (Item Ww 4); (Item Ww 5); (Item Ww 6); (Item Ww 7); (Item Ww 8); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 29); (Item Ww 30); (Item Ww 31)]).

Definition item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep1_jumps'2e279 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step1_jumps.279") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 0); (Item Ww 30); (Item Ww 31)]).

Definition item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep2_jumps'2e280 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step2_jumps.280") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 0); (Item Ww 30); (Item Ww 31)]).

Definition item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep3a_jumps'2e281 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step3a_jumps.281") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 32); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 23); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep3b_jumps'2e282 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 12); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep4_jumps'2e283 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step4_jumps.283") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition fn_glibc_vfwprintf_internal'23__wprintf_buffer_has_failed : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__wprintf_buffer_has_failed"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"v3";
    %"v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v5" : W = (Cmp Eq W) %"v4", #0
    => ret %"v5"
} }.

Definition fn_glibc_vfwprintf_internal'23__wprintf_buffer_mark_failed : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Write 1) %"v3";
    store Ww [%"chk0" + 0] <- #0
    => ret void
} }.

Definition fn_glibc_vfwprintf_internal'23__wprintf_buffer_pad : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W %"v2", L %"v4") -> RVoid {
  @"start":
    %"v10" : W = (Cmp Sgt L) %"v4", #0
    => br %"v10" ? "L6" : "L8";
  @"L6":
    %"v12" : W = (Ext Sb) %"v2";
    call void $"__wprintf_buffer_pad_1"(P %"v0", W %"v12", L %"v4")
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition fn_glibc_vfwprintf_internal'23__wprintf_buffer_putc : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ne L) %"v13", %"v14"
    => br %"v15" ? "L4" : "L5";
  @"L4":
    %"v17" = %"v0" +p #8;
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v19" = %"v18" +p #4;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v17";
    store.ptr [%"chk3" + 0] <- %"v19";
    %"chk4" : A = (Check 0 4 Write 1) %"v18";
    store Ww [%"chk4" + 0] <- %"v2"
    => goto "L6";
  @"L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v2")
    => goto "L6";
  @"L6":
    => ret void
} }.

Definition fn_glibc_vfwprintf_internal'23group_number : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#group_number"(P %"v0", P %"v2", P %"v4", P %"v6", W %"v8", W %"v10") -> RVoid {
  @"start":
    %"v15" : W = (Ext Ub) %"v10";
    %"v16" : W = (Cmp Eq W) %"v15", #0
    => br %"v16" ? "L19" : "L43";
  @"L19" [%"pr.1" : P = phi("L21" => %"v40", "start" => %"v4")]:
    %"v25" : L = Ptoi %"pr.1";
    %"v26" : L = Ptoi %"v6";
    %"v27" : W = (Cmp Ne L) %"v25", %"v26"
    => br %"v27" ? "L20" : "L14";
  @"L20":
    call %"v32" : W = $"__grouping_iterator_next"(P %"v2");
    %"v33" : W = (Ext Ub) %"v32"
    => br %"v33" ? "iw_1.start" : "L30";
  @"iw_1.start":
    %"iw_1.v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v11" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v13" : L = Ptoi %"iw_1.v9";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Ne L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L5";
  @"iw_1.L4":
    %"iw_1.v17" = %"v0" +p #8;
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v19" = %"iw_1.v18" +p #4;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"iw_1.v17";
    store.ptr [%"chk3" + 0] <- %"iw_1.v19";
    %"chk4" : A = (Check 0 4 Write 1) %"iw_1.v18";
    store Ww [%"chk4" + 0] <- %"v8"
    => goto "L30";
  @"iw_1.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v8")
    => goto "L30";
  @"L30":
    %"chk5" : A = (Check 0 4 Read 1) %"pr.1";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"iw_2.v8" = %"v0" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_2.v8";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_2.v11" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk6", %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_2.v13" : L = Ptoi %"iw_2.v9";
    %"iw_2.v14" : L = Ptoi %"iw_2.v12";
    %"iw_2.v15" : W = (Cmp Ne L) %"iw_2.v13", %"iw_2.v14"
    => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
  @"iw_2.L4":
    %"iw_2.v17" = %"v0" +p #8;
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_2.v19" = %"iw_2.v18" +p #4;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk6", %"iw_2.v17";
    store.ptr [%"chk9" + 0] <- %"iw_2.v19";
    %"chk10" : A = (Check 0 4 Write 1) %"iw_2.v18";
    store Ww [%"chk10" + 0] <- %"v38"
    => goto "L21";
  @"iw_2.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v38")
    => goto "L21";
  @"L21":
    %"v40" = %"pr.1" +p #4
    => goto poll "L19";
  @"L43" [%"pr.2" : P = phi("L45" => %"v78", "start" => %"v4")]:
    %"v49" : L = Ptoi %"pr.2";
    %"v50" : L = Ptoi %"v6";
    %"v51" : W = (Cmp Ne L) %"v49", %"v50"
    => br %"v51" ? "L44" : "L14";
  @"L44":
    call %"v56" : W = $"__grouping_iterator_next"(P %"v2");
    %"v57" : W = (Ext Ub) %"v56"
    => br %"v57" ? "iw_3.start" : "L54";
  @"iw_3.start":
    %"iw_3.v8" = %"v0" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_3.v8";
    %"iw_3.v9" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_3.v11" = %"v0" +p #16;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk11", %"iw_3.v11";
    %"iw_3.v12" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_3.v13" : L = Ptoi %"iw_3.v9";
    %"iw_3.v14" : L = Ptoi %"iw_3.v12";
    %"iw_3.v15" : W = (Cmp Ne L) %"iw_3.v13", %"iw_3.v14"
    => br %"iw_3.v15" ? "iw_3.L4" : "iw_3.L5";
  @"iw_3.L4":
    %"iw_3.v17" = %"v0" +p #8;
    %"iw_3.v18" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_3.v19" = %"iw_3.v18" +p #4;
    %"chk14" : A = (Renew 0 8 Write 8) %"chk11", %"iw_3.v17";
    store.ptr [%"chk14" + 0] <- %"iw_3.v19";
    %"chk15" : A = (Check 0 4 Write 1) %"iw_3.v18";
    store Ww [%"chk15" + 0] <- %"v8"
    => goto "L54";
  @"iw_3.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v8")
    => goto "L54";
  @"L54":
    %"chk16" : A = (Check 0 4 Read 1) %"pr.2";
    %"v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v63" : W = Sub %"v62", #48;
    %"v65" : P = Copy $"__libc_tsd_LOCALE";
    %"chk17" : A = (Check 0 8 Read 8) %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 8 Read 8) %"v66";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v69" = %"v68" +p #56;
    %"v71" : W = Add %"v63", #51;
    %"v72" : W = And %"v71", #65535;
    %"v73" : L = (Ext Sw) %"v72";
    %"v74" : L = Shl %"v73", #3;
    %"v75" = %"v69" +p %"v74";
    %"chk19" : A = (Check 0 4 Read 1) %"v75";
    %"v76" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"iw_4.v8" = %"v0" +p #8;
    %"chk20" : A = (Check 0 8 Read 8) %"iw_4.v8";
    %"iw_4.v9" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_4.v11" = %"v0" +p #16;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk20", %"iw_4.v11";
    %"iw_4.v12" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_4.v13" : L = Ptoi %"iw_4.v9";
    %"iw_4.v14" : L = Ptoi %"iw_4.v12";
    %"iw_4.v15" : W = (Cmp Ne L) %"iw_4.v13", %"iw_4.v14"
    => br %"iw_4.v15" ? "iw_4.L4" : "iw_4.L5";
  @"iw_4.L4":
    %"iw_4.v17" = %"v0" +p #8;
    %"iw_4.v18" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_4.v19" = %"iw_4.v18" +p #4;
    %"chk23" : A = (Renew 0 8 Write 8) %"chk20", %"iw_4.v17";
    store.ptr [%"chk23" + 0] <- %"iw_4.v19";
    %"chk24" : A = (Check 0 4 Write 1) %"iw_4.v18";
    store Ww [%"chk24" + 0] <- %"v76"
    => goto "L45";
  @"iw_4.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v76")
    => goto "L45";
  @"L45":
    %"v78" = %"pr.2" +p #4
    => goto poll "L43";
  @"L14":
    => ret void
} }.

Definition item_glibc_vfwprintf_internal'23jump_table : item :=
  (IData (a "glibc_vfwprintf_internal#jump_table") (LRo (a "local")) 1 [(Str (app [1; 0; 0; 4; 0; 14; 0; 6; 0; 0; 7; 2; 0; 3; 9; 0; 5; 8; 8; 8; 8; 8; 8; 8; 8; 8; 0; 0; 0; 0; 0; 0; 0; 26; 30; 25; 0; 19; 19; 19; 0; 29; 0; 0; 12] [0; 0; 0; 0; 0; 0; 21; 0; 0; 0; 0; 18; 0; 13; 0; 0; 0; 0; 0; 0; 26; 30; 20; 15; 19; 19; 19; 10; 15; 28; 0; 11; 24; 23; 17; 22; 12; 0; 21; 27; 16; 0; 31; 18; 0; 13]))]).

Definition item_glibc_vfwprintf_internal'23null : item :=
  (IData (a "glibc_vfwprintf_internal#null") (LRo (a "local")) 4 [(Str [40; 0; 0; 0; 110; 0; 0; 0; 117; 0; 0; 0; 108; 0; 0; 0; 108; 0; 0; 0; 41; 0; 0; 0]); (Zero 4)]).

Definition fn_glibc_vfwprintf_internal'23outstring_converted_wide_string : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#outstring_converted_wide_string"(P %"v0", P %"v2", W %"v4", W %"v6", W %"v8") -> RVoid {
  @"start":
    %"v3" : P = (Alloc 8) #8;
    %"v10" : P = (Alloc 4) #256;
    %"v22" : P = (Alloc 4) #8;
    %"v24" : P = (Alloc 8) #8;
    %"v94" : P = (Alloc 4) #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v3";
    store.ptr [%"chk0" + 0] <- %"v2";
    %"v15" : W = (Cmp Sgt W) %"v6", #0
    => br %"v15" ? "L16" : "L17";
  @"L16":
    %"v18" : W = (Ext Ub) %"v8";
    %"v19" : W = (Cmp Eq W) %"v18", #0
    => goto "L17";
  @"L17" [%"v21" : W = phi("start" => #0, "L16" => %"v19")]:
    => br %"v21" ? "L11" : "L13";
  @"L11":
    %"chk1" : A = (Check 0 4 Write 1) %"v22";
    store Ww [%"chk1" + 0] <- #0;
    %"v23" = %"v22" +p #4;
    %"chk2" : A = (HalfCheck Upper 0 4 Write 1) %"chk1", %"v23";
    store Ww [%"chk2" + 0] <- #0;
    store Ww [%"chk1" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v3";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk5" + 0] <- %"v25";
    %"v31" : W = (Cmp Slt W) %"v4", #0
    => br %"v31" ? "L27" : "L28";
  @"L27":
    call %"v32" : L = $"__mbsrtowcs"(P #0, P %"v24", L #0, P %"v22")
    => goto "L29";
  @"L28":
    %"v35" : L = (Ext Sw) %"v4"
    => goto "L36";
  @"L36" [%"pr.3" : L = phi("L28" => %"v35", "L71" => %"v80"); %"pr.2" : L = phi("L28" => #0, "L71" => %"v77")]:
    %"v40" : W = (Cmp Ugt L) %"pr.3", #0
    => br %"v40" ? "L41" : "L42";
  @"L41":
    %"chk6" : A = (Renew 0 8 Read 8) %"chk5", %"v24";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v44" : L = Ptoi %"v43";
    %"v45" : L = Ptoi #0;
    %"v46" : W = (Cmp Ne L) %"v44", %"v45"
    => goto "L42";
  @"L42" [%"v48" : W = phi("L36" => #0, "L41" => %"v46")]:
    => br %"v48" ? "L37" : "L29";
  @"L37":
    %"v55" : W = (Cmp Ult L) %"pr.3", #64
    => br %"v55" ? "L52" : "L51";
  @"L51":
    => goto "L52";
  @"L52" [%"pr.4" : L = phi("L51" => #64, "L37" => %"pr.3")]:
    call %"v59" : L = $"__mbsrtowcs"(P %"v10", P %"v24", L %"pr.4", P %"v22");
    %"v66" : W = (Cmp Eq L) %"v59", #18446744073709551615
    => br %"v66" ? "iw_1.start" : "L62";
  @"iw_1.start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk7" : A = (Check 0 4 Write 1) %"iw_1.v3";
    store Ww [%"chk7" + 0] <- #0
    => ret void;
  @"L62":
    %"v73" : W = (Cmp Eq L) %"v59", #0
    => br %"v73" ? "L29" : "L71";
  @"L71":
    %"v77" : L = Add %"pr.2", %"v59";
    %"v80" : L = Sub %"pr.3", %"v59"
    => goto poll "L36";
  @"L29" [%"pr.1" : L = phi("L27" => %"v32", "L42" => %"pr.2", "L62" => %"pr.2")]:
    %"v84" : L = (Ext Sw) %"v6";
    %"v85" : L = Sub %"v84", %"pr.1";
    %"iw_2.v10" : W = (Cmp Sgt L) %"v85", #0
    => br %"iw_2.v10" ? "iw_2.L6" : "iw_3.start";
  @"iw_2.L6":
    call void $"__wprintf_buffer_pad_1"(P %"v0", W #32, L %"v85")
    => goto "iw_3.start";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk8" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L86" : "L13";
  @"L86":
    => ret void;
  @"L13":
    %"chk9" : A = (Check 0 4 Write 1) %"v94";
    store Ww [%"chk9" + 0] <- #0;
    %"v95" = %"v94" +p #4;
    %"chk10" : A = (HalfCheck Upper 0 4 Write 1) %"chk9", %"v95";
    store Ww [%"chk10" + 0] <- #0;
    store Ww [%"chk9" + 0] <- #0;
    %"v103" : W = (Cmp Sge W) %"v4", #0
    => br %"v103" ? "L99" : "L106";
  @"L99":
    %"v105" : L = (Ext Sw) %"v4"
    => goto "L106";
  @"L106" [%"pr.7" : L = phi("L99" => %"v105", "L13" => #18446744073709551615, "L150" => %"v157", "L141" => %"pr.7"); %"pr.5" : L = phi("L99" => #0, "L13" => #0, "L150" => %"v149", "L141" => %"v149")]:
    %"v110" : W = (Cmp Ugt L) %"pr.7", #0
    => br %"v110" ? "L111" : "L112";
  @"L111":
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v3";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v114" : L = Ptoi %"v113";
    %"v115" : L = Ptoi #0;
    %"v116" : W = (Cmp Ne L) %"v114", %"v115"
    => goto "L112";
  @"L112" [%"v118" : W = phi("L106" => #0, "L111" => %"v116")]:
    => br %"v118" ? "L107" : "L108";
  @"L107":
    %"v125" : W = (Cmp Ult L) %"pr.7", #64
    => br %"v125" ? "L122" : "L121";
  @"L121":
    => goto "L122";
  @"L122" [%"pr.9" : L = phi("L121" => #64, "L107" => %"pr.7")]:
    call %"v129" : L = $"__mbsrtowcs"(P %"v10", P %"v3", L %"pr.9", P %"v94");
    %"v136" : W = (Cmp Eq L) %"v129", #18446744073709551615
    => br %"v136" ? "iw_4.start" : "L132";
  @"iw_4.start":
    %"iw_4.v3" = %"v0" +p #32;
    %"chk13" : A = (Check 0 4 Write 1) %"iw_4.v3";
    store Ww [%"chk13" + 0] <- #0
    => ret void;
  @"L132":
    %"v143" : W = (Cmp Eq L) %"v129", #0
    => br %"v143" ? "L108" : "L141";
  @"L141":
    call void $"__wprintf_buffer_write"(P %"v0", P %"v10", L %"v129");
    %"v149" : L = Add %"pr.5", %"v129"
    => br %"v103" ? "L150" : poll "L106";
  @"L150":
    %"v157" : L = Sub %"pr.7", %"v129"
    => goto poll "L106";
  @"L108":
    => br %"v15" ? "L163" : "L164";
  @"L163":
    %"v165" : W = (Ext Ub) %"v8";
    %"v166" : W = (Cmp Ne W) %"v165", #0
    => goto "L164";
  @"L164" [%"v167" : W = phi("L108" => #0, "L163" => %"v166")]:
    => br %"v167" ? "L158" : "L160";
  @"L158":
    %"v171" : L = (Ext Sw) %"v6";
    %"v172" : L = Sub %"v171", %"pr.5";
    %"iw_5.v10" : W = (Cmp Sgt L) %"v172", #0
    => br %"iw_5.v10" ? "iw_5.L6" : "L160";
  @"iw_5.L6":
    call void $"__wprintf_buffer_pad_1"(P %"v0", W #32, L %"v172")
    => goto "L160";
  @"L160":
    => ret void
} }.

Definition fn_glibc_vfwprintf_internal'23printf_positional : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#printf_positional"(P %"v0", P %"v2", W %"v4", P %"v6", P %"v8", W %"v10", P %"v12", P %"v14", W %"v16", P %"v18", W %"v20", W %"v22") -> RVoid blocks ((app (app (app [ir_blk{ @"start":
    %"v24" : P = (Alloc 16) #1040;
    %"v31" : P = (Alloc 16) #1040;
    %"v34" : P = (Alloc 8) #8;
    %"v107" : P = (Alloc 4) #1;
    %"v1251" : P = (Alloc 8) #24;
    %"v1916" : P = (Alloc 8) #8;
    call void $"glibc_vfwprintf_internal#scratch_buffer_init"(P %"v24");
    %"chk0" : A = (Check 0 8 Read 8) %"v24";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v28" = %"v24" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v28";
    %"v29" : L = (RawLoad LdL 0) %"chk1";
    %"v30" : L = Udiv %"v29", #72;
    call void $"glibc_vfwprintf_internal#scratch_buffer_init"(P %"v31");
    %"chk2" : A = (Check 0 8 Write 1) %"v34";
    store Wl [%"chk2" + 0] <- #0;
    (Flight (a "v42") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v43" : L = Ptoi %"v18";
    %"v44" : L = Ptoi %"v42";
    %"v45" : W = (Cmp Eq L) %"v43", %"v44"
    => br %"v45" ? "L36" : "L38" };
  ir_blk{ @"L36":
    %"v46" : P = Copy $"__libc_tsd_LOCALE";
    %"chk3" : A = (Check 0 8 Read 8) %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v48" = %"v47" +p #8;
    %"chk4" : A = (Check 0 8 Read 8) %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v50" = %"v49" +p #56;
    %"v54" = %"v50" +p #32;
    %"chk5" : A = (Check 0 4 Read 1) %"v54";
    %"v55" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v56" : P = Copy $"__libc_tsd_LOCALE";
    %"chk6" : A = (Check 0 8 Read 8) %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v58" = %"v57" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v60" = %"v59" +p #56;
    %"v64" = %"v60" +p #16;
    %"chk8" : A = (Check 0 8 Read 8) %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 1 Read 1) %"v65";
    %"v70" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"v71" : W = (Cmp Eq W) %"v70", #0
    => br %"v71" ? "L73" : "L72" };
  ir_blk{ @"L72":
    %"v75" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"v76" : W = (Cmp Eq W) %"v75", #127
    => goto "L73" };
  ir_blk{ @"L73" [%"v78" : W = phi("L36" => #1, "L72" => %"v76")]:
    => br %"v78" ? "L38" : "L67" };
  ir_blk{ @"L67":
    => goto "L38" };
  ir_blk{ @"L38" [%"pr.6" : W = phi("L67" => %"v55", "L73" => %"v55", "start" => %"v20")]:
    => goto "L81" };
  ir_blk{ @"L81" [%"pr.15" : P = phi("L38" => %"v12", "L83" => %"v129"); %"pr.12" : L = phi("L38" => #0, "L83" => %"v116"); %"pr.11" : L = phi("L38" => #0, "L83" => %"v125"); %"pr.9" : L = phi("L38" => %"v30", "L83" => %"pr.10"); %"pr.7" : P = phi("L38" => %"v26", "L83" => %"pr.8")]:
    %"chk11" : A = (Check 0 4 Read 1) %"pr.15";
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v87" : W = (Cmp Ne W) %"v86", #0
    => br %"v87" ? "L82" : "L84" };
  ir_blk{ @"L82":
    %"v93" : W = (Cmp Eq L) %"pr.11", %"pr.9"
    => br %"v93" ? "iw_1.start" : "L90" };
  ir_blk{ @"iw_1.start":
    call %"iw_1.v3" : W = $"__GI___libc_scratch_buffer_grow_preserve"(P %"v24");
    %"iw_1.v4" : W = (Ext Ub) %"iw_1.v3";
    %"iw_1.v5" : L = (Ext Uw) %"iw_1.v4";
    %"v99" : W = (Cmp Eq L) %"iw_1.v5", #0
    => br %"v99" ? "L94" : "L96" };
  ir_blk{ @"L94":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L96":
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v24";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v104" = %"v24" +p #8;
    %"chk13" : A = (Renew 0 8 Read 1) %"chk1", %"v104";
    %"v105" : L = (RawLoad LdL 0) %"chk13";
    %"v106" : L = Udiv %"v105", #72
    => goto "L90" };
  ir_blk{ @"L90" [%"pr.10" : L = phi("L96" => %"v106", "L82" => %"pr.9"); %"pr.8" : P = phi("L96" => %"v103", "L82" => %"pr.7")]:
    %"v113" : L = Mul %"pr.11", #72;
    %"v114" = %"pr.8" +p %"v113";
    call %"v115" : L = $"__parse_one_specwc"(P %"pr.15", L %"pr.12", P %"v114", P %"v34", P %"v107");
    %"v116" : L = Add %"pr.12", %"v115";
    %"chk14" : A = (Check 0 1 Read 1) %"v107";
    %"v120" : W = (RawLoad (LdNarrow Ub) 0) %"chk14"
    => br %"v120" ? "L117" : "L83" };
  ir_blk{ @"L117":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L83":
    %"v125" : L = Add %"pr.11", #1;
    %"v128" = %"v114" +p #32;
    %"chk15" : A = (Check 0 8 Read 8) %"v128";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk15"
    => goto poll "L81" };
  ir_blk{ @"L84":
    %"chk16" : A = (Renew 0 8 Read 1) %"chk2", %"v34";
    %"v134" : L = (RawLoad LdL 0) %"chk16";
    %"v135" : W = (Cmp Ugt L) %"pr.12", %"v134"
    => br %"v135" ? "L132" : "L131" };
  ir_blk{ @"L131":
    %"v137" : L = (RawLoad LdL 0) %"chk16"
    => goto "L132" };
  ir_blk{ @"L132" [%"v138" : L = phi("L131" => %"v137", "L84" => %"pr.12")]:
    call %"iw_2.v9" : W = $"__GI___libc_scratch_buffer_set_array_size"(P %"v31", L %"v138", L #24);
    %"iw_2.v10" : W = (Ext Ub) %"iw_2.v9";
    %"iw_2.v11" : L = (Ext Uw) %"iw_2.v10";
    %"v154" : W = (Cmp Eq L) %"iw_2.v11", #0
    => br %"v154" ? "L147" : "L149" };
  ir_blk{ @"L147":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L149":
    %"chk18" : A = (Check 0 8 Read 8) %"v31";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v160" : L = Shl %"v138", #4;
    %"v161" = %"v157" +p %"v160";
    %"v164" : L = Shl %"v138", #2;
    %"v165" = %"v161" +p %"v164";
    %"v169" = %"v165" +p %"v164";
    %"v175" : W = And %"v22", #2;
    %"v176" : W = (Cmp Ne W) %"v175", #0
    => br %"v176" ? "L173" : "L172" };
  ir_blk{ @"L172":
    => goto "L173" };
  ir_blk{ @"L173" [%"v177" : W = phi("L172" => #0, "L149" => #(-1))]:
    call %"v180" : P = $"__GI_memset"(P %"v165", W %"v177", L %"v164")
    => goto "L181" };
  ir_blk{ @"L181" [%"pr.13" : L = phi("L173" => #0, "L183" => %"v322")]:
    %"v187" : W = (Cmp Ult L) %"pr.13", %"pr.11"
    => br %"v187" ? "L182" : "L323" };
  ir_blk{ @"L182":
    %"v193" : L = Mul %"pr.13", #72;
    %"v194" = %"pr.7" +p %"v193";
    %"v195" = %"v194" +p #44;
    %"chk19" : A = (Check 0 4 Read 1) %"v195";
    %"v196" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v198" : W = (Cmp Ne W) %"v196", #4294967295
    => br %"v198" ? "L188" : "L190" };
  ir_blk{ @"L188":
    %"v204" = %"v194" +p #44;
    %"v205" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v206" : L = (Ext Sw) %"v205";
    %"v207" : L = Shl %"v206", #2;
    %"v208" = %"v165" +p %"v207";
    %"chk21" : A = (Check 0 4 Write 1) %"v208";
    store Ww [%"chk21" + 0] <- #0
    => goto "L190" };
  ir_blk{ @"L190":
    %"v216" = %"v194" +p #40;
    %"chk22" : A = (HalfCheck Lower 0 4 Read 1) %"chk19", %"v216";
    %"v217" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v219" : W = (Cmp Ne W) %"v217", #4294967295
    => br %"v219" ? "L209" : "L211" };
  ir_blk{ @"L209":
    %"v225" = %"v194" +p #40;
    %"v226" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v227" : L = (Ext Sw) %"v226";
    %"v228" : L = Shl %"v227", #2;
    %"v229" = %"v165" +p %"v228";
    %"chk24" : A = (Check 0 4 Write 1) %"v229";
    store Ww [%"chk24" + 0] <- #0
    => goto "L211" };
  ir_blk{ @"L211":
    %"v234" = %"v194" +p #56;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 1) %"chk19", %"v234";
    %"v235" : L = (RawLoad LdL 0) %"chk25";
    %"v317" : W = (Cmp Eq L) %"v235", #0
    => br %"v317" ? "L183" : "L318" };
  ir_blk{ @"L239":
    %"v245" = %"v194" +p #48;
    %"chk26" : A = (HalfCheck Upper 0 4 Read 1) %"chk19", %"v245";
    %"v246" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v247" : L = (Ext Sw) %"v246";
    %"v248" : L = Shl %"v247", #2;
    %"v249" = %"v165" +p %"v248";
    %"v254" = %"v194" +p #52;
    %"chk27" : A = (HalfCheck Upper 0 4 Read 1) %"chk19", %"v254";
    %"v255" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"chk28" : A = (Check 0 4 Write 1) %"v249";
    store Ww [%"chk28" + 0] <- %"v255";
    %"v262" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v263" : L = (Ext Sw) %"v262";
    %"v264" : L = Shl %"v263", #2;
    %"v265" = %"v161" +p %"v264";
    %"v270" = %"v194" +p #64;
    %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk19", %"v270";
    %"v271" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"chk31" : A = (Check 0 4 Write 1) %"v265";
    store Ww [%"chk31" + 0] <- %"v271"
    => goto "L183" };
  ir_blk{ @"L272":
    %"v273" : P = Copy $"__printf_arginfo_table";
    %"chk32" : A = (Check 0 8 Read 8) %"v273";
    %"v274" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v279" = %"v194" +p #8;
    %"chk33" : A = (HalfCheck Lower 0 4 Read 1) %"chk19", %"v279";
    %"v280" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"v281" : L = (Ext Sw) %"v280";
    %"v282" : L = Shl %"v281", #3;
    %"v283" = %"v274" +p %"v282";
    %"chk34" : A = (Check 0 8 Read 8) %"v283";
    %"v284" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v293" = %"v194" +p #56;
    %"chk35" : A = (Renew 0 8 Read 1) %"chk25", %"v293";
    %"v294" : L = (RawLoad LdL 0) %"chk35";
    %"v300" = %"v194" +p #48;
    %"v301" : W = (RawLoad (LdNarrow Sw) (-8)) %"chk35";
    %"v302" : L = (Ext Sw) %"v301";
    %"v303" : L = Shl %"v302", #2;
    %"v304" = %"v165" +p %"v303";
    %"v311" : W = (RawLoad (LdNarrow Sw) (-8)) %"chk35";
    %"v312" : L = (Ext Sw) %"v311";
    %"v313" : L = Shl %"v312", #2;
    %"v314" = %"v161" +p %"v313";
    %"chk38" : F = CheckFunction %"v284";
    rawcall %"v315" : W = %"chk38"(P %"v194", L %"v294", P %"v304", P %"v314")
    => goto "L183" };
  ir_blk{ @"L318":
    %"v319" : W = (Cmp Eq L) %"v235", #1
    => br %"v319" ? poll "L239" : poll "L272" };
  ir_blk{ @"L183":
    %"v322" : L = Add %"pr.13", #1
    => goto poll "L181" };
  ir_blk{ @"L323" [%"pr.31" : P = phi("L336" => %"pr.32", "L181" => %"v169"); %"pr.26" : P = phi("L336" => %"pr.27", "L181" => %"v165"); %"pr.21" : P = phi("L336" => %"pr.22", "L181" => %"v161"); %"pr.16" : P = phi("L336" => %"pr.17", "L181" => %"v157"); %"pr.14" : L = phi("L336" => %"v586", "L181" => #0)]:
    %"v329" : W = (Cmp Ult L) %"pr.14", %"v138"
    => br %"v329" ? "L324" : "L587" };
  ir_blk{ @"L324":
    %"v332" : L = Shl %"pr.14", #2;
    %"v333" = %"pr.26" +p %"v332";
    %"chk39" : A = (Check 0 4 Read 1) %"v333";
    %"v334" : W = (RawLoad (LdNarrow Sw) 0) %"chk39";
    %"v550" : W = (Cmp Slt W) %"v334", #5
    => br %"v550" ? "L551" : "L552" };
  ir_blk{ @"L337":
    %"v340" : L = Shl %"pr.14", #4;
    %"v341" = %"pr.16" +p %"v340";
    %"v343" : W = VaArg %"v8";
    %"chk40" : A = (Check 0 4 Write 1) %"v341";
    store Ww [%"chk40" + 0] <- %"v343"
    => goto "L336" };
  ir_blk{ @"L346":
    %"v349" : L = Shl %"pr.14", #4;
    %"v350" = %"pr.16" +p %"v349";
    %"v352" : W = VaArg %"v8";
    %"chk41" : A = (Check 0 4 Write 1) %"v350";
    store Ww [%"chk41" + 0] <- %"v352"
    => goto "L336" };
  ir_blk{ @"L354":
    %"v357" : L = Shl %"pr.14", #4;
    %"v358" = %"pr.16" +p %"v357";
    %"v360" : L = VaArg %"v8";
    %"chk42" : A = (Check 0 8 Write 1) %"v358";
    store Wl [%"chk42" + 0] <- %"v360"
    => goto "L336" }] [ir_blk{ @"L362":
    %"v365" : L = Shl %"pr.14", #4;
    %"v366" = %"pr.16" +p %"v365";
    %"v368" : Double = VaArg %"v8";
    %"chk43" : A = (Check 0 8 Write 1) %"v366";
    store Wd [%"chk43" + 0] <- %"v368"
    => goto "L336" };
  ir_blk{ @"L369":
    %"v374" : W = And %"v22", #1
    => br %"v374" ? "L370" : "L371" };
  ir_blk{ @"L370":
    %"v380" : L = Shl %"pr.14", #4;
    %"v381" = %"pr.16" +p %"v380";
    %"v383" : Double = VaArg %"v8";
    %"chk44" : A = (Check 0 8 Write 1) %"v381";
    store Wd [%"chk44" + 0] <- %"v383";
    %"chk45" : A = (Renew 0 4 Read 1) %"chk39", %"v333";
    %"v388" : W = (RawLoad (LdNarrow Sw) 0) %"chk45";
    %"v391" : W = And %"v388", #4294967039;
    %"chk46" : A = (Renew 0 4 Write 1) %"chk39", %"v333";
    store Ww [%"chk46" + 0] <- %"v391"
    => goto "L336" };
  ir_blk{ @"L371":
    %"v394" : L = Shl %"pr.14", #4;
    %"v395" = %"pr.16" +p %"v394";
    %"v397" : Extended = VaArg %"v8";
    %"chk47" : A = (Check 0 10 Write 8) %"v395";
    store Wx [%"chk47" + 0] <- %"v397"
    => goto "L336" };
  ir_blk{ @"L400":
    %"v403" : L = Shl %"pr.14", #4;
    %"v404" = %"pr.16" +p %"v403";
    %"v406" : P = VaArg %"v8";
    %"chk48" : A = (Check 0 8 Write 8) %"v404";
    store.ptr [%"chk48" + 0] <- %"v406"
    => goto "L336" };
  ir_blk{ @"L407":
    %"chk49" : A = (Renew 0 4 Read 1) %"chk39", %"v333";
    %"v415" : W = (RawLoad (LdNarrow Sw) 0) %"chk49";
    %"v417" : W = And %"v415", #2048;
    %"v418" : W = (Cmp Ne W) %"v417", #0
    => br %"v418" ? "L408" : "L409" };
  ir_blk{ @"L408":
    %"v421" : L = Shl %"pr.14", #4;
    %"v422" = %"pr.16" +p %"v421";
    %"v424" : P = VaArg %"v8";
    %"chk50" : A = (Check 0 8 Write 8) %"v422";
    store.ptr [%"chk50" + 0] <- %"v424"
    => goto "L336" };
  ir_blk{ @"L409":
    %"v428" : P = Copy $"__printf_va_arg_table";
    %"chk51" : A = (Check 0 8 Read 8) %"v428";
    %"v429" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v430" : L = Ptoi %"v429";
    %"v431" : L = Ptoi #0;
    %"v432" : W = (Cmp Ne L) %"v430", %"v431"
    => br %"v432" ? "L435" : "L436" };
  ir_blk{ @"L435":
    %"v437" : P = Copy $"__printf_va_arg_table";
    %"chk52" : A = (Check 0 8 Read 8) %"v437";
    %"v438" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"chk53" : A = (Renew 0 4 Read 1) %"chk39", %"v333";
    %"v443" : W = (RawLoad (LdNarrow Sw) 0) %"chk53";
    %"v444" : W = Sub %"v443", #8;
    %"v445" : L = (Ext Sw) %"v444";
    %"v446" : L = Shl %"v445", #3;
    %"v447" = %"v438" +p %"v446";
    %"chk54" : A = (Check 0 8 Read 8) %"v447";
    %"v448" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v449" : L = Ptoi %"v448";
    %"v451" : W = (Cmp Ne L) %"v449", %"v431"
    => goto "L436" };
  ir_blk{ @"L436" [%"v453" : W = phi("L409" => #0, "L435" => %"v451")]:
    => br %"v453" ? "L454" : "L426" };
  ir_blk{ @"L454" [%"pr.35" : P = phi("L482" => %"v502", "L436" => %"pr.31"); %"pr.30" : P = phi("L482" => %"v496", "L436" => %"pr.26"); %"pr.25" : P = phi("L482" => %"v492", "L436" => %"pr.21"); %"pr.20" : P = phi("L482" => %"v488", "L436" => %"pr.16")]:
    %"v461" = %"pr.25" +p %"v332";
    %"chk55" : A = (Check 0 4 Read 1) %"v461";
    %"v462" : W = (RawLoad (LdNarrow Sw) 0) %"chk55";
    %"v463" : L = (Ext Sw) %"v462";
    %"v464" = %"pr.35" +p %"v463";
    %"chk56" : A = (Renew 0 8 Read 8) %"chk18", %"v31";
    %"v465" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v466" = %"v31" +p #8;
    %"chk57" : A = (HalfCheck Upper 0 8 Read 1) %"chk18", %"v466";
    %"v467" : L = (RawLoad LdL 0) %"chk57";
    %"v468" = %"v465" +p %"v467";
    %"v469" : L = Ptoi %"v464";
    %"v470" : L = Ptoi %"v468";
    %"v471" : W = (Cmp Ugt L) %"v469", %"v470"
    => br %"v471" ? "L455" : "L456" };
  ir_blk{ @"L455":
    %"v476" = %"pr.30" +p %"v164";
    %"v477" : L = Ptoi %"pr.35";
    %"v478" : L = Ptoi %"v476";
    %"v479" : L = Sub %"v477", %"v478";
    call %"iw_3.v3" : W = $"__GI___libc_scratch_buffer_grow_preserve"(P %"v31");
    %"iw_3.v4" : W = (Ext Ub) %"iw_3.v3";
    %"iw_3.v5" : L = (Ext Uw) %"iw_3.v4";
    %"v485" : W = (Cmp Eq L) %"iw_3.v5", #0
    => br %"v485" ? "L480" : "L482" };
  ir_blk{ @"L480":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L482":
    %"chk58" : A = (Renew 0 8 Read 8) %"chk18", %"v31";
    %"v488" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v492" = %"v488" +p %"v160";
    %"v496" = %"v492" +p %"v164";
    %"v500" = %"v496" +p %"v164";
    %"v502" = %"v500" +p %"v479"
    => goto poll "L454" };
  ir_blk{ @"L456":
    %"v505" : L = Shl %"pr.14", #4;
    %"v506" = %"pr.20" +p %"v505";
    %"chk59" : A = (Check 0 8 Write 8) %"v506";
    store.ptr [%"chk59" + 0] <- %"pr.35";
    %"chk60" : A = (Renew 0 4 Read 1) %"chk55", %"v461";
    %"v513" : W = (RawLoad (LdNarrow Sw) 0) %"chk60";
    %"v514" : L = (Ext Sw) %"v513";
    %"v515" = %"pr.35" +p %"v514";
    %"v516" : P = Copy $"__printf_va_arg_table";
    %"chk61" : A = (Check 0 8 Read 8) %"v516";
    %"v517" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"v521" = %"pr.30" +p %"v332";
    %"chk62" : A = (Check 0 4 Read 1) %"v521";
    %"v522" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"v523" : W = Sub %"v522", #8;
    %"v524" : L = (Ext Sw) %"v523";
    %"v525" : L = Shl %"v524", #3;
    %"v526" = %"v517" +p %"v525";
    %"chk63" : A = (Check 0 8 Read 8) %"v526";
    %"v527" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"chk64" : A = (Renew 0 8 Read 8) %"chk59", %"v506";
    %"v532" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"chk65" : F = CheckFunction %"v527";
    rawcall void %"chk65"(P %"v532", P %"v8")
    => goto "L336" };
  ir_blk{ @"L426":
    %"v536" : L = Shl %"pr.14", #4;
    %"v537" = %"pr.16" +p %"v536";
    call %"v538" : P = $"__GI_memset"(P %"v537", W #0, L #16)
    => goto "L336" };
  ir_blk{ @"L539":
    => br %"v176" ? "L542" : "L541" };
  ir_blk{ @"L541":
    %"v546" : P = Copy $"glibc_vfwprintf_internal#str.291";
    %"v547" : P = Copy $"glibc_vfwprintf_internal#str.292";
    %"v548" : P = Copy $"glibc_vfwprintf_internal#str.293";
    call void $"__libc_assert_fail"(P %"v546", P %"v547", W #1270, P %"v548")
    => goto "L542" };
  ir_blk{ @"L542":
    %"v549" : P = Copy $"glibc_vfwprintf_internal#str.294";
    call void $"__GI___libc_fatal"(P %"v549")
    => goto "L336" };
  ir_blk{ @"L551":
    %"v553" : W = (Cmp Slt W) %"v334", #2
    => br %"v553" ? "L554" : "L555" };
  ir_blk{ @"L554":
    %"v556" : W = (Cmp Eq W) %"v334", #(-1)
    => br %"v556" ? poll "L539" : "L557" };
  ir_blk{ @"L557":
    %"v558" : W = (Cmp Eq W) %"v334", #0
    => br %"v558" ? poll "L346" : "L559" };
  ir_blk{ @"L559":
    %"v560" : W = (Cmp Eq W) %"v334", #1
    => br %"v560" ? poll "L346" : poll "L407" };
  ir_blk{ @"L555":
    %"v562" : W = (Cmp Eq W) %"v334", #2
    => br %"v562" ? poll "L337" : "L563" };
  ir_blk{ @"L563":
    %"v564" : W = (Cmp Eq W) %"v334", #3
    => br %"v564" ? poll "L400" : "L565" };
  ir_blk{ @"L565":
    %"v566" : W = (Cmp Eq W) %"v334", #4
    => br %"v566" ? poll "L400" : poll "L407" };
  ir_blk{ @"L552":
    %"v568" : W = (Cmp Slt W) %"v334", #256
    => br %"v568" ? "L569" : "L570" };
  ir_blk{ @"L569":
    %"v571" : W = (Cmp Eq W) %"v334", #5
    => br %"v571" ? poll "L400" : "L572" };
  ir_blk{ @"L572":
    %"v573" : W = (Cmp Eq W) %"v334", #6
    => br %"v573" ? poll "L362" : "L574" };
  ir_blk{ @"L574":
    %"v575" : W = (Cmp Eq W) %"v334", #7
    => br %"v575" ? poll "L362" : poll "L407" };
  ir_blk{ @"L570":
    %"v577" : W = (Cmp Eq W) %"v334", #256
    => br %"v577" ? poll "L354" : "L578" };
  ir_blk{ @"L578":
    %"v579" : W = (Cmp Eq W) %"v334", #263
    => br %"v579" ? poll "L369" : "L580" };
  ir_blk{ @"L580":
    %"v581" : W = (Cmp Eq W) %"v334", #512
    => br %"v581" ? poll "L354" : "L582" };
  ir_blk{ @"L582":
    %"v583" : W = (Cmp Eq W) %"v334", #1024
    => br %"v583" ? poll "L346" : poll "L407" };
  ir_blk{ @"L336" [%"pr.32" : P = phi("L337" => %"pr.31", "L346" => %"pr.31", "L354" => %"pr.31", "L362" => %"pr.31", "L400" => %"pr.31", "L542" => %"pr.31", "L370" => %"pr.31", "L371" => %"pr.31", "L408" => %"pr.31", "L456" => %"v515", "L426" => %"pr.31"); %"pr.27" : P = phi("L337" => %"pr.26", "L346" => %"pr.26", "L354" => %"pr.26", "L362" => %"pr.26", "L400" => %"pr.26", "L542" => %"pr.26", "L370" => %"pr.26", "L371" => %"pr.26", "L408" => %"pr.26", "L456" => %"pr.30", "L426" => %"pr.26"); %"pr.22" : P = phi("L337" => %"pr.21", "L346" => %"pr.21", "L354" => %"pr.21", "L362" => %"pr.21", "L400" => %"pr.21", "L542" => %"pr.21", "L370" => %"pr.21", "L371" => %"pr.21", "L408" => %"pr.21", "L456" => %"pr.25", "L426" => %"pr.21"); %"pr.17" : P = phi("L337" => %"pr.16", "L346" => %"pr.16", "L354" => %"pr.16", "L362" => %"pr.16", "L400" => %"pr.16", "L542" => %"pr.16", "L370" => %"pr.16", "L371" => %"pr.16", "L408" => %"pr.16", "L456" => %"pr.20", "L426" => %"pr.16")]:
    %"v586" : L = Add %"pr.14", #1
    => goto poll "L323" };
  ir_blk{ @"L587" [%"pr.5" : W = phi("L865" => %"v2013", "L323" => %"v10"); %"pr.3" : W = phi("L865" => %"pr.4", "L323" => %"v4")]:
    %"v592" : L = (Ext Sw) %"pr.5";
    %"v594" : W = (Cmp Ult L) %"v592", %"pr.11"
    => br %"v594" ? "L595" : "L596" };
  ir_blk{ @"L595":
    call %"v598" : W = $"glibc_vfwprintf_internal#__wprintf_buffer_has_failed"(P %"v0");
    %"v599" : W = (Ext Ub) %"v598";
    %"v600" : W = (Cmp Eq W) %"v599", #0
    => goto "L596" }]) (app [ir_blk{ @"L596" [%"v602" : W = phi("L587" => #0, "L595" => %"v600")]:
    => br %"v602" ? "L588" : "L101" };
  ir_blk{ @"L588":
    %"v611" : L = Mul %"v592", #72;
    %"v612" = %"pr.7" +p %"v611";
    %"v613" = %"v612" +p #12;
    %"chk66" : A = (Check 0 4 Read 1) %"v613";
    %"v614" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v615" : W = Shl %"v614", #28;
    %"v616" : W = Shr %"v615", #31;
    %"v624" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v625" : W = Shl %"v624", #27;
    %"v626" : W = Shr %"v625", #31;
    %"v634" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v635" : W = Shl %"v634", #26;
    %"v636" : W = Shr %"v635", #31;
    %"v644" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v645" : W = Shl %"v644", #25;
    %"v646" : W = Shr %"v645", #31;
    %"v654" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v655" : W = Shl %"v654", #24;
    %"v656" : W = Shr %"v655", #31;
    %"v664" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v674" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v675" : W = Shl %"v674", #30;
    %"v676" : W = Shr %"v675", #31;
    %"v684" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v685" : W = Shl %"v684", #22;
    %"v686" : W = Shr %"v685", #31;
    %"v694" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v695" : W = Shl %"v694", #29;
    %"v696" : W = Shr %"v695", #31;
    %"v703" = %"v612" +p #4;
    %"chk75" : A = (HalfCheck Lower 0 4 Read 1) %"chk66", %"v703";
    %"v704" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"chk76" : A = (HalfCheck Lower 0 4 Read 1) %"chk66", %"v612";
    %"v711" : W = (RawLoad (LdNarrow Sw) 0) %"chk76";
    %"v719" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v720" : W = Shl %"v719", #20;
    %"v721" : W = Shr %"v720", #31;
    %"v728" = %"v612" +p #16;
    %"chk78" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v728";
    %"v729" : W = (RawLoad (LdNarrow Sw) 0) %"chk78";
    %"v730" : W = (Ext Sb) %"v729";
    %"v737" = %"v612" +p #8;
    %"v738" : W = (RawLoad (LdNarrow Sw) 4) %"chk75";
    %"v741" = %"v14" +p #1000;
    %"v750" = %"v612" +p #44;
    %"chk80" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v750";
    %"v751" : W = (RawLoad (LdNarrow Sw) 0) %"chk80";
    %"v753" : W = (Cmp Ne W) %"v751", #4294967295
    => br %"v753" ? "L742" : "L744" };
  ir_blk{ @"L742":
    %"v759" = %"v612" +p #4;
    %"v766" = %"v612" +p #44;
    %"v767" : W = (RawLoad (LdNarrow Sw) 0) %"chk80";
    %"v768" : L = (Ext Sw) %"v767";
    %"v769" : L = Shl %"v768", #4;
    %"v770" = %"pr.16" +p %"v769";
    %"chk82" : A = (Check 0 4 Read 1) %"v770";
    %"v771" : W = (RawLoad (LdNarrow Sw) 0) %"chk82";
    %"chk83" : A = (Renew 0 4 Write 1) %"chk75", %"v759";
    store Ww [%"chk83" + 0] <- %"v771";
    %"v781" : W = (RawLoad (LdNarrow Sw) 0) %"chk83";
    %"v782" : W = (Cmp Slt W) %"v781", #0
    => br %"v782" ? "L772" : "L774" };
  ir_blk{ @"L772":
    %"v788" = %"v612" +p #4;
    %"v789" : W = (RawLoad (LdNarrow Sw) 0) %"chk83";
    %"v791" : W = Mul %"v789", #4294967295;
    store Ww [%"chk83" + 0] <- %"v791";
    %"v797" = %"v612" +p #12;
    %"v798" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v799" : W = And %"v798", #4294967263;
    %"v802" : W = Or %"v799", #32;
    store Ww [%"chk66" + 0] <- %"v802"
    => goto "L774" };
  ir_blk{ @"L774" [%"pr.65" : W = phi("L772" => #1, "L742" => %"v636")]:
    %"v810" = %"v612" +p #4;
    %"v811" : W = (RawLoad (LdNarrow Sw) 0) %"chk83"
    => goto "L744" };
  ir_blk{ @"L744" [%"pr.81" : W = phi("L774" => %"v811", "L588" => %"v704"); %"pr.64" : W = phi("L774" => %"pr.65", "L588" => %"v636")]:
    %"v820" = %"v612" +p #40;
    %"v821" : W = (RawLoad (LdNarrow Sw) (-4)) %"chk80";
    %"v823" : W = (Cmp Ne W) %"v821", #4294967295
    => br %"v823" ? "L812" : "L814" };
  ir_blk{ @"L812":
    %"v835" = %"v612" +p #40;
    %"v836" : W = (RawLoad (LdNarrow Sw) (-4)) %"chk80";
    %"v837" : L = (Ext Sw) %"v836";
    %"v838" : L = Shl %"v837", #4;
    %"v839" = %"pr.16" +p %"v838";
    %"chk92" : A = (Check 0 4 Read 1) %"v839";
    %"v840" : W = (RawLoad (LdNarrow Sw) 0) %"chk92";
    %"chk93" : A = (Renew 0 4 Write 1) %"chk76", %"v612";
    store Ww [%"chk93" + 0] <- %"v840";
    %"v849" : W = (RawLoad (LdNarrow Sw) 0) %"chk93";
    %"v850" : W = (Cmp Slt W) %"v849", #0
    => br %"v850" ? "L841" : "L843" };
  ir_blk{ @"L841":
    store Ww [%"chk93" + 0] <- #4294967295
    => goto "L843" };
  ir_blk{ @"L843":
    %"v862" : W = (RawLoad (LdNarrow Sw) 0) %"chk93"
    => goto "L814" };
  ir_blk{ @"L814" [%"pr.89" : W = phi("L843" => %"v862", "L744" => %"v711")]:
    %"v872" : W = (Cmp Sle W) %"v738", #255
    => br %"v872" ? "L873" : "L874" };
  ir_blk{ @"L873":
    %"v875" : P = Copy $"__printf_function_table";
    %"chk97" : A = (Check 0 8 Read 8) %"v875";
    %"v876" : P = (RawLoadPointer 0 load_effects) %"chk97";
    %"v877" : L = Ptoi %"v876";
    %"v878" : L = Ptoi #0;
    %"v879" : W = (Cmp Ne L) %"v877", %"v878"
    => goto "L874" };
  ir_blk{ @"L874" [%"v881" : W = phi("L814" => #0, "L873" => %"v879")]:
    => br %"v881" ? "L882" : "L883" };
  ir_blk{ @"L882":
    %"v884" : P = Copy $"__printf_function_table";
    %"chk98" : A = (Check 0 8 Read 8) %"v884";
    %"v885" : P = (RawLoadPointer 0 load_effects) %"chk98";
    %"v887" : L = (Ext Sw) %"v738";
    %"v888" : L = Shl %"v887", #3;
    %"v889" = %"v885" +p %"v888";
    %"chk99" : A = (Check 0 8 Read 8) %"v889";
    %"v890" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"v891" : L = Ptoi %"v890";
    %"v892" : L = Ptoi #0;
    %"v893" : W = (Cmp Ne L) %"v891", %"v892"
    => goto "L883" };
  ir_blk{ @"L883" [%"v895" : W = phi("L874" => #0, "L882" => %"v893")]:
    => br %"v895" ? "L866" : "L943" };
  ir_blk{ @"L866":
    %"v898" : P = Copy $"__printf_function_table";
    %"chk100" : A = (Check 0 8 Read 8) %"v898";
    %"v899" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"v901" : L = (Ext Sw) %"v738";
    %"v902" : L = Shl %"v901", #3;
    %"v903" = %"v899" +p %"v902";
    %"chk101" : A = (Check 0 8 Read 8) %"v903";
    %"v904" : P = (RawLoadPointer 0 load_effects) %"chk101";
    %"v911" = %"v612" +p #48;
    %"chk102" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v911";
    %"v912" : W = (RawLoad (LdNarrow Sw) 0) %"chk102";
    %"v913" : L = (Ext Sw) %"v912";
    %"v914" : L = Shl %"v913", #4;
    %"v915" = %"pr.16" +p %"v914";
    %"v921" = %"v612" +p #56;
    %"chk103" : A = (HalfCheck Upper 0 8 Read 1) %"chk66", %"v921";
    %"v922" : L = (RawLoad LdL 0) %"chk103";
    call %"v928" : W = $"__wprintf_function_invoke"(P %"v0", P %"v904", P %"v915", L %"v922", P %"v612");
    %"v934" : W = (Cmp Ne W) %"v928", #4294967294
    => br %"v934" ? "L929" : "L943" };
  ir_blk{ @"L929":
    %"v939" : W = (Cmp Slt W) %"v928", #0
    => br %"v939" ? "L935" : "L865" };
  ir_blk{ @"L935":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L943":
    %"v953" : W = (Cmp Slt W) %"v738", #32
    => br %"v953" ? "L955" : "L954" };
  ir_blk{ @"L954":
    %"v957" : W = (Cmp Sgt W) %"v738", #122
    => goto "L955" };
  ir_blk{ @"L955" [%"v959" : W = phi("L943" => #1, "L954" => %"v957")]:
    => br %"v959" ? "L951" : "L950" };
  ir_blk{ @"L950":
    %"v963" : P = Copy $"glibc_vfwprintf_internal#printf_positional.step4_jumps.295";
    %"v964" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v966" : W = Sub %"v738", #32;
    %"v967" : L = (Ext Uw) %"v966";
    %"v968" = %"v964" +p %"v967";
    %"chk104" : A = (Check 0 1 Read 1) %"v968";
    %"v969" : W = (RawLoad (LdNarrow Ub) 0) %"chk104";
    %"v970" : L = (Ext Uw) %"v969";
    %"v971" : L = Shl %"v970", #2;
    %"v972" = %"v963" +p %"v971";
    %"chk105" : A = (Check 0 4 Read 1) %"v972";
    %"v973" : W = (RawLoad (LdNarrow Sw) 0) %"chk105";
    %"v974" : L = (Ext Sw) %"v973"
    => goto "L951" };
  ir_blk{ @"L951" [%"v975" : L = phi("L950" => %"v974", "L955" => #0)]:
    %"v976" : W = Copy %"v975";
    %"v977" : L = (Ext Sw) %"v976";
    %"v978" = #1 +p %"v977";
    %"v980" : L = Ptoi %"v978";
    %"v2016" : W = (Cmp Ult L) %"v980", #8
    => br %"v2016" ? "L2017" : "L2018" };
  ir_blk{ @"L983":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #37)
    => goto "L865" };
  ir_blk{ @"L987":
    => br %"v696" ? "L1015" : "L1016" };
  ir_blk{ @"L1015":
    %"v1025" = %"v612" +p #48;
    %"chk106" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1025";
    %"v1026" : W = (RawLoad (LdNarrow Sw) 0) %"chk106";
    %"v1027" : L = (Ext Sw) %"v1026";
    %"v1028" : L = Shl %"v1027", #4;
    %"v1029" = %"pr.16" +p %"v1028";
    %"chk107" : A = (Check 0 8 Read 1) %"v1029";
    %"v1030" : L = (RawLoad LdL 0) %"chk107"
    => goto "L1017" };
  ir_blk{ @"L1016":
    => br %"v686" ? "L1031" : "L1032" };
  ir_blk{ @"L1031":
    %"v1041" = %"v612" +p #48;
    %"chk108" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1041";
    %"v1042" : W = (RawLoad (LdNarrow Sw) 0) %"chk108";
    %"v1043" : L = (Ext Sw) %"v1042";
    %"v1044" : L = Shl %"v1043", #4;
    %"v1045" = %"pr.16" +p %"v1044";
    %"chk109" : A = (Check 0 4 Read 1) %"v1045";
    %"v1046" : W = (RawLoad (LdNarrow Uw) 0) %"chk109";
    %"v1047" : W = (Ext Sb) %"v1046";
    %"v1048" : L = (Ext Sw) %"v1047"
    => goto "L1017" };
  ir_blk{ @"L1032":
    %"v1053" : W = (Cmp Eq W) %"v676", #0
    => br %"v1053" ? "L1049" : "L1050" };
  ir_blk{ @"L1049":
    %"v1060" = %"v612" +p #48;
    %"chk110" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1060";
    %"v1061" : W = (RawLoad (LdNarrow Sw) 0) %"chk110";
    %"v1062" : L = (Ext Sw) %"v1061";
    %"v1063" : L = Shl %"v1062", #4;
    %"v1064" = %"pr.16" +p %"v1063";
    %"chk111" : A = (Check 0 4 Read 1) %"v1064";
    %"v1065" : W = (RawLoad (LdNarrow Sw) 0) %"chk111";
    %"v1066" : L = (Ext Sw) %"v1065"
    => goto "L1017" };
  ir_blk{ @"L1050":
    %"v1073" = %"v612" +p #48;
    %"chk112" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1073";
    %"v1074" : W = (RawLoad (LdNarrow Sw) 0) %"chk112";
    %"v1075" : L = (Ext Sw) %"v1074";
    %"v1076" : L = Shl %"v1075", #4;
    %"v1077" = %"pr.16" +p %"v1076";
    %"chk113" : A = (Check 0 4 Read 1) %"v1077";
    %"v1078" : W = (RawLoad (LdNarrow Uw) 0) %"chk113";
    %"v1079" : W = (Ext Sh) %"v1078";
    %"v1080" : L = (Ext Sw) %"v1079"
    => goto "L1017" };
  ir_blk{ @"L1017" [%"pr.95" : L = phi("L1015" => %"v1030", "L1031" => %"v1048", "L1049" => %"v1066", "L1050" => %"v1080")]:
    %"v1082" : W = (Cmp Slt L) %"pr.95", #0
    => br %"v1082" ? "L1083" : "L1091" };
  ir_blk{ @"L1083":
    %"v1088" : L = Neg %"pr.95"
    => goto "L1091" };
  ir_blk{ @"L1093" [%"pr.48" : W = phi("L2021" => #10, "L2029" => #8, "L2031" => #16, "L2052" => #2)]:
    => br %"v696" ? "L1150" : "L1151" };
  ir_blk{ @"L1150":
    %"v1160" = %"v612" +p #48;
    %"chk114" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1160";
    %"v1161" : W = (RawLoad (LdNarrow Sw) 0) %"chk114";
    %"v1162" : L = (Ext Sw) %"v1161";
    %"v1163" : L = Shl %"v1162", #4;
    %"v1164" = %"pr.16" +p %"v1163";
    %"chk115" : A = (Check 0 8 Read 1) %"v1164";
    %"v1165" : L = (RawLoad LdL 0) %"chk115"
    => goto "L1091" };
  ir_blk{ @"L1151":
    => br %"v686" ? "L1166" : "L1167" };
  ir_blk{ @"L1166":
    %"v1176" = %"v612" +p #48;
    %"chk116" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1176";
    %"v1177" : W = (RawLoad (LdNarrow Sw) 0) %"chk116";
    %"v1178" : L = (Ext Sw) %"v1177";
    %"v1179" : L = Shl %"v1178", #4;
    %"v1180" = %"pr.16" +p %"v1179";
    %"chk117" : A = (Check 0 4 Read 1) %"v1180";
    %"v1181" : W = (RawLoad (LdNarrow Uw) 0) %"chk117";
    %"v1182" : W = (Ext Ub) %"v1181";
    %"v1183" : L = (Ext Uw) %"v1182"
    => goto "L1091" };
  ir_blk{ @"L1167":
    %"v1188" : W = (Cmp Eq W) %"v676", #0
    => br %"v1188" ? "L1184" : "L1185" }] [ir_blk{ @"L1184":
    %"v1195" = %"v612" +p #48;
    %"chk118" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1195";
    %"v1196" : W = (RawLoad (LdNarrow Sw) 0) %"chk118";
    %"v1197" : L = (Ext Sw) %"v1196";
    %"v1198" : L = Shl %"v1197", #4;
    %"v1199" = %"pr.16" +p %"v1198";
    %"chk119" : A = (Check 0 4 Read 1) %"v1199";
    %"v1200" : W = (RawLoad (LdNarrow Uw) 0) %"chk119";
    %"v1201" : L = (Ext Uw) %"v1200"
    => goto "L1091" };
  ir_blk{ @"L1185":
    %"v1208" = %"v612" +p #48;
    %"chk120" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1208";
    %"v1209" : W = (RawLoad (LdNarrow Sw) 0) %"chk120";
    %"v1210" : L = (Ext Sw) %"v1209";
    %"v1211" : L = Shl %"v1210", #4;
    %"v1212" = %"pr.16" +p %"v1211";
    %"chk121" : A = (Check 0 4 Read 1) %"v1212";
    %"v1213" : W = (RawLoad (LdNarrow Uw) 0) %"chk121";
    %"v1214" : W = (Ext Uh) %"v1213";
    %"v1215" : L = (Ext Uw) %"v1214"
    => goto "L1091" };
  ir_blk{ @"L1091" [%"pr.93" : W = phi("L1083" => %"v738", "L1017" => %"v738", "L1150" => %"v738", "L1166" => %"v738", "L1184" => %"v738", "L1185" => %"v738", "L1599" => #120, "L1735" => %"v738", "L1724" => %"v738"); %"pr.69" : W = phi("L1083" => %"v656", "L1017" => %"v656", "L1150" => %"v656", "L1166" => %"v656", "L1184" => %"v656", "L1185" => %"v656", "L1599" => #0, "L1735" => %"v656", "L1724" => %"v656"); %"pr.67" : W = phi("L1083" => %"v646", "L1017" => %"v646", "L1150" => #0, "L1166" => #0, "L1184" => #0, "L1185" => #0, "L1599" => %"v646", "L1735" => %"v646", "L1724" => %"v646"); %"pr.62" : W = phi("L1083" => %"v626", "L1017" => %"v626", "L1150" => #0, "L1166" => #0, "L1184" => #0, "L1185" => #0, "L1599" => %"v626", "L1735" => %"v626", "L1724" => %"v626"); %"pr.59" : W = phi("L1083" => %"v616", "L1017" => %"v616", "L1150" => %"v616", "L1166" => %"v616", "L1184" => %"v616", "L1185" => %"v616", "L1599" => #1, "L1735" => %"v616", "L1724" => %"v616"); %"pr.47" : W = phi("L1083" => #10, "L1017" => #10, "L1150" => %"pr.48", "L1166" => %"pr.48", "L1184" => %"pr.48", "L1185" => %"pr.48", "L1599" => #16, "L1735" => #10, "L1724" => #10); %"pr.40" : L = phi("L1083" => %"v1088", "L1017" => %"pr.95", "L1150" => %"v1165", "L1166" => %"v1183", "L1184" => %"v1201", "L1185" => %"v1215", "L1599" => %"v1617", "L1735" => %"v1740", "L1724" => %"v1734"); %"pr.37" : W = phi("L1083" => %"v1082", "L1017" => %"v1082", "L1150" => #0, "L1166" => #0, "L1184" => #0, "L1185" => #0, "L1599" => #0, "L1735" => %"v1732", "L1724" => %"v1732")]:
    %"v1220" : W = (Cmp Slt W) %"pr.89", #0
    => br %"v1220" ? "L1218" : "L1217" };
  ir_blk{ @"L1217":
    => goto "L1218" };
  ir_blk{ @"L1218" [%"pr.92" : W = phi("L1217" => #32, "L1091" => %"v730"); %"pr.86" : W = phi("L1217" => %"pr.89", "L1091" => #1)]:
    %"v1225" : W = (Cmp Eq W) %"pr.86", #0
    => br %"v1225" ? "L1226" : "L1227" };
  ir_blk{ @"L1226":
    %"v1229" : W = (Cmp Eq L) %"pr.40", #0
    => goto "L1227" };
  ir_blk{ @"L1227" [%"v1231" : W = phi("L1218" => #0, "L1226" => %"v1229")]:
    => br %"v1231" ? "L1221" : "L1222" };
  ir_blk{ @"L1221":
    %"v1237" : W = (Cmp Eq W) %"pr.47", #8
    => br %"v1237" ? "L1238" : "L1239" };
  ir_blk{ @"L1238":
    %"v1241" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1239" };
  ir_blk{ @"L1239" [%"v1242" : W = phi("L1221" => #0, "L1238" => %"v1241")]:
    => br %"v1242" ? "L1233" : "L1223" };
  ir_blk{ @"L1233":
    (Flight (a "v1244") Sub [(FAddress (t "v741")); (FValue (Const 4))] (LowerOf (t "v741")));
    %"chk122" : A = (Check 0 4 Write 1) %"v1244";
    store Ww [%"chk122" + 0] <- #48
    => goto "L1223" };
  ir_blk{ @"L1222":
    %"v1249" : W = (Cmp Eq W) %"pr.93", #88
    => br %"v1249" ? "iw_5.L9" : "iw_5.L10" };
  ir_blk{ @"iw_5.L9":
    %"iw_5.v13" : P = Copy $"_itowa_upper_digits"
    => goto "iw_5.L11" };
  ir_blk{ @"iw_5.L10":
    %"iw_5.v14" : P = Copy $"_itowa_lower_digits"
    => goto "iw_5.L11" };
  ir_blk{ @"iw_5.L11" [%"iw_5.v15" : P = phi("iw_5.L9" => %"iw_5.v13", "iw_5.L10" => %"iw_5.v14")]:
    %"iw_5.v85" : W = (Cmp Eq W) %"pr.47", #10
    => br %"iw_5.v85" ? "iw_5.L22" : "iw_5.L86" };
  ir_blk{ @"iw_5.L22" [%"iw_5.pr.6" : P = phi("iw_5.L22" => %"iw_5.v26", "iw_5.L11" => %"v741"); %"iw_5.pr.1" : L = phi("iw_5.L22" => %"iw_5.v34", "iw_5.L11" => %"pr.40")]:
    (Flight (a "iw_5.v26") Sub [(FAddress (t "iw_5.pr.6")); (FValue (Const 4))] (LowerOf (t "iw_5.pr.6")));
    %"iw_5.v29" : L = Urem %"iw_5.pr.1", #10;
    %"iw_5.v30" : L = Shl %"iw_5.v29", #2;
    %"iw_5.v31" = %"iw_5.v15" +p %"iw_5.v30";
    %"chk123" : A = (Check 0 4 Read 1) %"iw_5.v31";
    %"iw_5.v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk123";
    %"chk124" : A = (Check 0 4 Write 1) %"iw_5.v26";
    store Ww [%"chk124" + 0] <- %"iw_5.v32";
    %"iw_5.v34" : L = Udiv %"iw_5.pr.1", #10;
    %"iw_5.v35" : W = (Cmp Ne L) %"iw_5.v34", #0
    => br %"iw_5.v35" ? poll "iw_5.L22" : "iw_5.L20" };
  ir_blk{ @"iw_5.L37" [%"iw_5.pr.7" : P = phi("iw_5.L37" => %"iw_5.v41", "iw_5.L86" => %"v741"); %"iw_5.pr.2" : L = phi("iw_5.L37" => %"iw_5.v49", "iw_5.L86" => %"pr.40")]:
    (Flight (a "iw_5.v41") Sub [(FAddress (t "iw_5.pr.7")); (FValue (Const 4))] (LowerOf (t "iw_5.pr.7")));
    %"iw_5.v44" : L = And %"iw_5.pr.2", #15;
    %"iw_5.v45" : L = Shl %"iw_5.v44", #2;
    %"iw_5.v46" = %"iw_5.v15" +p %"iw_5.v45";
    %"chk125" : A = (Check 0 4 Read 1) %"iw_5.v46";
    %"iw_5.v47" : W = (RawLoad (LdNarrow Sw) 0) %"chk125";
    %"chk126" : A = (Check 0 4 Write 1) %"iw_5.v41";
    store Ww [%"chk126" + 0] <- %"iw_5.v47";
    %"iw_5.v49" : L = Shr %"iw_5.pr.2", #4;
    %"iw_5.v50" : W = (Cmp Ne L) %"iw_5.v49", #0
    => br %"iw_5.v50" ? poll "iw_5.L37" : "iw_5.L20" };
  ir_blk{ @"iw_5.L52" [%"iw_5.pr.8" : P = phi("iw_5.L52" => %"iw_5.v56", "iw_5.L88" => %"v741"); %"iw_5.pr.3" : L = phi("iw_5.L52" => %"iw_5.v64", "iw_5.L88" => %"pr.40")]:
    (Flight (a "iw_5.v56") Sub [(FAddress (t "iw_5.pr.8")); (FValue (Const 4))] (LowerOf (t "iw_5.pr.8")));
    %"iw_5.v59" : L = And %"iw_5.pr.3", #7;
    %"iw_5.v60" : L = Shl %"iw_5.v59", #2;
    %"iw_5.v61" = %"iw_5.v15" +p %"iw_5.v60";
    %"chk127" : A = (Check 0 4 Read 1) %"iw_5.v61";
    %"iw_5.v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk127";
    %"chk128" : A = (Check 0 4 Write 1) %"iw_5.v56";
    store Ww [%"chk128" + 0] <- %"iw_5.v62";
    %"iw_5.v64" : L = Shr %"iw_5.pr.3", #3;
    %"iw_5.v65" : W = (Cmp Ne L) %"iw_5.v64", #0
    => br %"iw_5.v65" ? poll "iw_5.L52" : "iw_5.L20" };
  ir_blk{ @"iw_5.L67" [%"iw_5.pr.9" : P = phi("iw_5.L67" => %"iw_5.v71", "iw_5.L88" => %"v741"); %"iw_5.pr.4" : L = phi("iw_5.L67" => %"iw_5.v83", "iw_5.L88" => %"pr.40")]:
    (Flight (a "iw_5.v71") Sub [(FAddress (t "iw_5.pr.9")); (FValue (Const 4))] (LowerOf (t "iw_5.pr.9")));
    %"iw_5.v75" : L = (Ext Uw) %"pr.47";
    %"iw_5.v76" : L = Urem %"iw_5.pr.4", %"iw_5.v75";
    %"iw_5.v77" : L = Shl %"iw_5.v76", #2;
    %"iw_5.v78" = %"iw_5.v15" +p %"iw_5.v77";
    %"chk129" : A = (Check 0 4 Read 1) %"iw_5.v78";
    %"iw_5.v79" : W = (RawLoad (LdNarrow Sw) 0) %"chk129";
    %"chk130" : A = (Check 0 4 Write 1) %"iw_5.v71";
    store Ww [%"chk130" + 0] <- %"iw_5.v79";
    %"iw_5.v83" : L = Udiv %"iw_5.pr.4", %"iw_5.v75";
    %"iw_5.v84" : W = (Cmp Ne L) %"iw_5.v83", #0
    => br %"iw_5.v84" ? poll "iw_5.L67" : "iw_5.L20" };
  ir_blk{ @"iw_5.L86":
    %"iw_5.v87" : W = (Cmp Eq W) %"pr.47", #16
    => br %"iw_5.v87" ? poll "iw_5.L37" : "iw_5.L88" };
  ir_blk{ @"iw_5.L88":
    %"iw_5.v89" : W = (Cmp Eq W) %"pr.47", #8
    => br %"iw_5.v89" ? poll "iw_5.L52" : poll "iw_5.L67" };
  ir_blk{ @"iw_5.L20" [%"iw_5.pr.5" : P = phi("iw_5.L22" => %"iw_5.v26", "iw_5.L37" => %"iw_5.v41", "iw_5.L52" => %"iw_5.v56", "iw_5.L67" => %"iw_5.v71")]:
    => goto "L1223" };
  ir_blk{ @"L1223" [%"pr.53" : P = phi("L1233" => %"v1244", "L1239" => %"v741", "iw_5.L20" => %"iw_5.pr.5")]:
    => br %"pr.69" ? "L1255" : "L1254" };
  ir_blk{ @"L1254":
    => br %"v721" ? "L1257" : "L1255" };
  ir_blk{ @"L1257":
    %"v1260" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1255" };
  ir_blk{ @"L1255" [%"v1264" : W = phi("L1223" => #1, "L1254" => #0, "L1257" => %"v1260")]:
    => br %"pr.69" ? "L1266" : "L1267" };
  ir_blk{ @"L1266":
    %"v1270" : P = Copy $"__libc_tsd_LOCALE";
    %"chk131" : A = (Check 0 8 Read 8) %"v1270";
    %"v1271" : P = (RawLoadPointer 0 load_effects) %"chk131";
    %"v1274" : L = Ptoi %"v741";
    %"v1275" : L = Ptoi %"pr.53";
    %"v1276" : L = Sub %"v1274", %"v1275";
    %"v1277" : L = Div %"v1276", #4;
    call %"v1278" : W = $"__grouping_iterator_init"(P %"v1251", W #1, P %"v1271", W %"v1277")
    => goto "L1268" };
  ir_blk{ @"L1267":
    => br %"v721" ? "L1284" : "L1285" };
  ir_blk{ @"L1284":
    %"v1287" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1285" };
  ir_blk{ @"L1285" [%"v1289" : W = phi("L1267" => #0, "L1284" => %"v1287")]:
    => br %"v1289" ? "L1280" : "L1268" };
  ir_blk{ @"L1280":
    %"v1292" : L = Ptoi %"v741";
    %"v1293" : L = Ptoi %"pr.53";
    %"v1294" : L = Sub %"v1292", %"v1293";
    %"v1295" : L = Div %"v1294", #4;
    call %"v1296" : W = $"__grouping_iterator_init_none"(P %"v1251", W %"v1295")
    => goto "L1268" };
  ir_blk{ @"L1268":
    %"v1301" : L = Ptoi %"v741";
    %"v1302" : L = Ptoi %"pr.53";
    %"v1303" : L = Sub %"v1301", %"v1302";
    %"v1304" : L = Div %"v1303", #4
    => br %"pr.69" ? "L1309" : "L1310" };
  ir_blk{ @"L1309":
    %"v1312" : W = (Cmp Ne W) %"pr.6", #0
    => goto "L1310" };
  ir_blk{ @"L1310" [%"v1314" : W = phi("L1268" => #0, "L1309" => %"v1312")]:
    => br %"v1314" ? "L1305" : "L1307" };
  ir_blk{ @"L1305":
    %"v1315" : W = Copy %"v1304";
    %"v1316" = %"v1251" +p #20;
    %"chk132" : A = (Check 0 4 Read 1) %"v1316";
    %"v1317" : W = (RawLoad (LdNarrow Uw) 0) %"chk132";
    %"v1318" : W = Add %"v1315", %"v1317"
    => goto "L1307" };
  ir_blk{ @"L1307" [%"pr.98" : W = phi("L1305" => %"v1318", "L1310" => %"v1304")]:
    %"v1322" : W = (Cmp Sle W) %"pr.86", %"pr.98"
    => br %"v1322" ? "L1323" : "L1324" };
  ir_blk{ @"L1323":
    %"v1326" : W = (Cmp Ne L) %"pr.40", #0
    => goto "L1324" }])) (app (app [ir_blk{ @"L1324" [%"v1328" : W = phi("L1307" => #0, "L1323" => %"v1326")]:
    => br %"v1328" ? "L1329" : "L1330" };
  ir_blk{ @"L1329":
    %"v1332" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1330" };
  ir_blk{ @"L1330" [%"v1333" : W = phi("L1324" => #0, "L1329" => %"v1332")]:
    => br %"v1333" ? "L1334" : "L1335" };
  ir_blk{ @"L1334":
    %"v1337" : W = (Cmp Eq W) %"pr.47", #8
    => goto "L1335" };
  ir_blk{ @"L1335" [%"v1339" : W = phi("L1330" => #0, "L1334" => %"v1337")]:
    %"v1351" : L = Div %"v1303", #4;
    %"v1352" : L = (Ext Sw) %"pr.86";
    %"v1353" : L = Sub %"v1352", %"v1351";
    %"v1354" : W = (Cmp Slt L) %"v1353", #0
    => br %"v1354" ? "L1344" : "L1343" };
  ir_blk{ @"L1343":
    %"v1361" : L = Div %"v1303", #4;
    %"v1363" : L = Sub %"v1352", %"v1361"
    => goto "L1344" };
  ir_blk{ @"L1344" [%"v1364" : L = phi("L1343" => %"v1363", "L1335" => #0)]:
    %"v1369" : W = (Cmp Eq W) %"pr.64", #0
    => br %"v1369" ? "L1365" : "L1366" };
  ir_blk{ @"L1365":
    %"v1372" : W = Copy %"v1364";
    %"v1373" : W = Add %"pr.98", %"v1372";
    %"v1374" : W = Sub %"pr.81", %"v1373";
    %"v1379" : W = (Cmp Ne L) %"pr.40", #0
    => br %"v1379" ? "L1380" : "L1381" };
  ir_blk{ @"L1380":
    %"v1383" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1381" };
  ir_blk{ @"L1381" [%"v1384" : W = phi("L1365" => #0, "L1380" => %"v1383")]:
    => br %"v1384" ? "L1385" : "L1386" };
  ir_blk{ @"L1385":
    %"v1388" : W = (Cmp Eq W) %"pr.47", #16
    => br %"v1388" ? "L1386" : "L1389" };
  ir_blk{ @"L1389":
    %"v1392" : W = (Cmp Eq W) %"pr.47", #2
    => goto "L1386" };
  ir_blk{ @"L1386" [%"v1396" : W = phi("L1381" => #0, "L1385" => #1, "L1389" => %"v1392")]:
    => br %"v1396" ? "L1375" : "L1377" };
  ir_blk{ @"L1375":
    %"v1398" : W = Sub %"v1374", #2
    => goto "L1377" };
  ir_blk{ @"L1377" [%"pr.72" : W = phi("L1375" => %"v1398", "L1386" => %"v1374")]:
    => br %"v1339" ? "L1399" : "L1401" };
  ir_blk{ @"L1399":
    %"v1404" : W = Sub %"pr.72", #1
    => goto "L1401" };
  ir_blk{ @"L1401" [%"pr.73" : W = phi("L1399" => %"v1404", "L1377" => %"pr.72")]:
    => br %"pr.37" ? "L1410" : "L1409" };
  ir_blk{ @"L1409":
    %"v1412" : W = (Cmp Ne W) %"pr.67", #0
    => goto "L1410" };
  ir_blk{ @"L1410" [%"v1413" : W = phi("L1401" => #1, "L1409" => %"v1412")]:
    => br %"v1413" ? "L1415" : "L1414" };
  ir_blk{ @"L1414":
    %"v1417" : W = (Cmp Ne W) %"pr.62", #0
    => goto "L1415" };
  ir_blk{ @"L1415" [%"v1418" : W = phi("L1410" => #1, "L1414" => %"v1417")]:
    => br %"v1418" ? "L1405" : "L1407" };
  ir_blk{ @"L1405":
    %"v1420" : W = Sub %"pr.73", #1
    => goto "L1407" };
  ir_blk{ @"L1407" [%"pr.74" : W = phi("L1405" => %"v1420", "L1415" => %"pr.73")]:
    %"v1424" : W = (Ext Sb) %"pr.92";
    %"v1425" : W = (Cmp Eq W) %"v1424", #32
    => br %"v1425" ? "L1421" : "L1423" };
  ir_blk{ @"L1421":
    %"v1428" : L = (Ext Sw) %"pr.74";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1428")
    => goto "L1423" };
  ir_blk{ @"L1423" [%"pr.75" : W = phi("L1421" => #0, "L1407" => %"pr.74")]:
    => br %"pr.37" ? "L1429" : "L1430" };
  ir_blk{ @"L1429":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #45)
    => goto "L1431" };
  ir_blk{ @"L1430":
    => br %"pr.67" ? "L1434" : "L1435" };
  ir_blk{ @"L1434":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #43)
    => goto "L1431" };
  ir_blk{ @"L1435":
    => br %"pr.62" ? "L1439" : "L1431" };
  ir_blk{ @"L1439":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #32)
    => goto "L1431" };
  ir_blk{ @"L1431":
    => br %"v1379" ? "L1449" : "L1450" };
  ir_blk{ @"L1449":
    %"v1452" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1450" };
  ir_blk{ @"L1450" [%"v1453" : W = phi("L1431" => #0, "L1449" => %"v1452")]:
    => br %"v1453" ? "L1454" : "L1455" };
  ir_blk{ @"L1454":
    %"v1457" : W = (Cmp Eq W) %"pr.47", #16
    => br %"v1457" ? "L1455" : "L1458" };
  ir_blk{ @"L1458":
    %"v1461" : W = (Cmp Eq W) %"pr.47", #2
    => goto "L1455" };
  ir_blk{ @"L1455" [%"v1465" : W = phi("L1450" => #0, "L1454" => #1, "L1458" => %"v1461")]:
    => br %"v1465" ? "L1444" : "L1446" }] [ir_blk{ @"L1444":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #48);
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"pr.93")
    => goto "L1446" };
  ir_blk{ @"L1446":
    %"v1470" : W = Copy %"v1364";
    %"v1471" : W = Add %"pr.75", %"v1470";
    %"v1474" : L = (Ext Sw) %"v1471";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #48, L %"v1474")
    => br %"v1339" ? "L1475" : "L1477" };
  ir_blk{ @"L1475":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #48)
    => goto "L1477" };
  ir_blk{ @"L1477":
    => br %"v1264" ? "L1480" : "L1481" };
  ir_blk{ @"L1480":
    => br %"v721" ? "L1489" : "L1490" };
  ir_blk{ @"L1489":
    %"v1492" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1490" };
  ir_blk{ @"L1490" [%"v1494" : W = phi("L1480" => #0, "L1489" => %"v1492")]:
    call void $"glibc_vfwprintf_internal#group_number"(P %"v0", P %"v1251", P %"pr.53", P %"v741", W %"pr.6", W %"v1494")
    => goto "L865" };
  ir_blk{ @"L1481":
    %"v1503" : L = Div %"v1303", #4;
    call void $"__wprintf_buffer_write"(P %"v0", P %"pr.53", L %"v1503")
    => goto "L865" };
  ir_blk{ @"L1366":
    => br %"pr.37" ? "L1505" : "L1506" };
  ir_blk{ @"L1505":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #45);
    %"v1511" : W = Sub %"pr.81", #1
    => goto "L1507" };
  ir_blk{ @"L1506":
    => br %"pr.67" ? "L1512" : "L1513" };
  ir_blk{ @"L1512":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #43);
    %"v1518" : W = Sub %"pr.81", #1
    => goto "L1507" };
  ir_blk{ @"L1513":
    => br %"pr.62" ? "L1519" : "L1507" };
  ir_blk{ @"L1519":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #32);
    %"v1525" : W = Sub %"pr.81", #1
    => goto "L1507" };
  ir_blk{ @"L1507" [%"pr.76" : W = phi("L1505" => %"v1511", "L1512" => %"v1518", "L1519" => %"v1525", "L1513" => %"pr.81")]:
    %"v1530" : W = (Cmp Ne L) %"pr.40", #0
    => br %"v1530" ? "L1531" : "L1532" };
  ir_blk{ @"L1531":
    %"v1534" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1532" };
  ir_blk{ @"L1532" [%"v1535" : W = phi("L1507" => #0, "L1531" => %"v1534")]:
    => br %"v1535" ? "L1536" : "L1537" };
  ir_blk{ @"L1536":
    %"v1539" : W = (Cmp Eq W) %"pr.47", #16
    => br %"v1539" ? "L1537" : "L1540" };
  ir_blk{ @"L1540":
    %"v1543" : W = (Cmp Eq W) %"pr.47", #2
    => goto "L1537" };
  ir_blk{ @"L1537" [%"v1547" : W = phi("L1532" => #0, "L1536" => #1, "L1540" => %"v1543")]:
    => br %"v1547" ? "L1526" : "L1528" };
  ir_blk{ @"L1526":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #48);
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"pr.93");
    %"v1552" : W = Sub %"pr.76", #2
    => goto "L1528" };
  ir_blk{ @"L1528" [%"pr.79" : W = phi("L1526" => %"v1552", "L1537" => %"pr.76")]:
    => br %"v1339" ? "L1553" : "L1555" };
  ir_blk{ @"L1553":
    %"v1558" : W = Sub %"pr.79", #1
    => goto "L1555" };
  ir_blk{ @"L1555" [%"pr.80" : W = phi("L1553" => %"v1558", "L1528" => %"pr.79")]:
    %"v1561" : W = Copy %"v1364";
    %"v1562" : W = Add %"pr.98", %"v1561";
    %"v1563" : W = Sub %"pr.80", %"v1562";
    %"v1565" : W = Copy %"v1364";
    %"v1566" : L = (Ext Uw) %"v1565";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #48, L %"v1566")
    => br %"v1339" ? "L1567" : "L1569" };
  ir_blk{ @"L1567":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #48)
    => goto "L1569" };
  ir_blk{ @"L1569":
    => br %"v1264" ? "L1572" : "L1573" };
  ir_blk{ @"L1572":
    => br %"v721" ? "L1581" : "L1582" };
  ir_blk{ @"L1581":
    %"v1584" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1582" };
  ir_blk{ @"L1582" [%"v1586" : W = phi("L1572" => #0, "L1581" => %"v1584")]:
    call void $"glibc_vfwprintf_internal#group_number"(P %"v0", P %"v1251", P %"pr.53", P %"v741", W %"pr.6", W %"v1586")
    => goto "L1574" };
  ir_blk{ @"L1573":
    %"v1595" : L = Div %"v1303", #4;
    call void $"__wprintf_buffer_write"(P %"v0", P %"pr.53", L %"v1595")
    => goto "L1574" };
  ir_blk{ @"L1574":
    %"v1598" : L = (Ext Sw) %"v1563";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1598")
    => goto "L865" };
  ir_blk{ @"L1599":
    %"v1607" = %"v612" +p #48;
    %"chk133" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1607";
    %"v1608" : W = (RawLoad (LdNarrow Sw) 0) %"chk133";
    %"v1609" : L = (Ext Sw) %"v1608";
    %"v1610" : L = Shl %"v1609", #4;
    %"v1611" = %"pr.16" +p %"v1610";
    %"chk134" : A = (Check 0 8 Read 8) %"v1611";
    %"v1612" : P = (RawLoadPointer 0 load_effects) %"chk134";
    %"v1617" : L = Ptoi %"v1612";
    %"v1618" : L = Ptoi #0;
    %"v1619" : W = (Cmp Ne L) %"v1617", %"v1618"
    => br %"v1619" ? poll "L1091" : "L1614" };
  ir_blk{ @"L1614":
    %"v1623" : P = Copy $"glibc_vfwprintf_internal#str.285";
    %"v1628" : W = (Cmp Slt W) %"pr.89", #5
    => br %"v1628" ? "L1630" : "L1625" };
  ir_blk{ @"L1625":
    => goto "L1630" };
  ir_blk{ @"L1631":
    => br %"v176" ? "L1632" : "L1634" };
  ir_blk{ @"L1632":
    %"v1642" : W = (Cmp Eq W) %"pr.3", #0
    => br %"v1642" ? "L1638" : "L1640" };
  ir_blk{ @"L1638":
    call %"v1645" : L = $"__wcslen"(P %"v2");
    %"v1646" : L = Add %"v1645", #1;
    %"v1647" : L = Shl %"v1646", #2;
    call %"v1648" : W = $"__readonly_area"(P %"v2", L %"v1647")
    => goto "L1640" }]) (app [ir_blk{ @"L1640" [%"pr.2" : W = phi("L1638" => %"v1648", "L1632" => %"pr.3")]:
    %"v1659" : W = (Cmp Eq W) %"pr.2", #1
    => br %"v1659" ? "L1652" : "L1660" };
  ir_blk{ @"L1652":
    %"v1653" : P = Copy $"glibc_vfwprintf_internal#str.286";
    call void $"__GI___libc_fatal"(P %"v1653")
    => goto "L1654" };
  ir_blk{ @"L1654":
    %"v1655" : P = Copy $"glibc_vfwprintf_internal#str.287";
    call void $"__GI___libc_fatal"(P %"v1655")
    => goto "L1634" };
  ir_blk{ @"L1660":
    %"v1661" : W = (Cmp Eq W) %"pr.2", #3
    => br %"v1661" ? poll "L1654" : "L1662" };
  ir_blk{ @"L1662":
    %"v1663" : W = (Cmp Eq W) %"pr.2", #2
    => br %"v1663" ? "L1634" : "L1664" };
  ir_blk{ @"L1664":
    %"v1665" : W = (Cmp Eq W) %"pr.2", #0
    => br %"v1665" ? "L1634" : "L1666" };
  ir_blk{ @"L1666":
    => goto "L1634" };
  ir_blk{ @"L1634" [%"pr.1" : W = phi("L1666" => %"pr.2", "L1664" => %"pr.2", "L1654" => %"pr.2", "L1662" => %"pr.2", "L1631" => %"pr.3")]:
    %"v1674" = %"v612" +p #48;
    %"chk135" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1674";
    %"v1675" : W = (RawLoad (LdNarrow Sw) 0) %"chk135";
    %"v1676" : L = (Ext Sw) %"v1675";
    %"v1677" : L = Shl %"v1676", #4;
    %"v1678" = %"pr.16" +p %"v1677";
    %"chk136" : A = (Check 0 8 Read 8) %"v1678";
    %"v1679" : P = (RawLoadPointer 0 load_effects) %"chk136";
    call %"v1682" : W = $"__wprintf_buffer_done"(P %"v0")
    => br %"v696" ? "L1689" : "L1690" };
  ir_blk{ @"L1689":
    %"v1695" : L = (Ext Uw) %"v1682";
    %"chk137" : A = (Check 0 8 Write 1) %"v1679";
    store Wl [%"chk137" + 0] <- %"v1695"
    => goto "L865" };
  ir_blk{ @"L1690":
    => br %"v686" ? "L1696" : "L1697" };
  ir_blk{ @"L1696":
    %"v1702" : W = (Ext Sb) %"v1682";
    %"chk138" : A = (Check 0 1 Write 1) %"v1679";
    store Wb [%"chk138" + 0] <- %"v1702"
    => goto "L865" };
  ir_blk{ @"L1697":
    %"v1707" : W = (Cmp Eq W) %"v676", #0
    => br %"v1707" ? "L1703" : "L1704" };
  ir_blk{ @"L1703":
    %"chk139" : A = (Check 0 4 Write 1) %"v1679";
    store Ww [%"chk139" + 0] <- %"v1682"
    => goto "L865" };
  ir_blk{ @"L1704":
    %"v1712" : W = (Ext Sh) %"v1682";
    %"chk140" : A = (Check 0 2 Write 1) %"v1679";
    store Wh [%"chk140" + 0] <- %"v1712"
    => goto "L865" };
  ir_blk{ @"L1713":
    => br %"v616" ? "L1714" : "L1715" };
  ir_blk{ @"L1714":
    call %"v1719" : P = $"__get_errname"(W %"v16")
    => goto "L1716" };
  ir_blk{ @"L1715":
    call %"v1723" : P = $"__GI___strerror_r"(W %"v16", P %"v14", L #1000)
    => goto "L1716" };
  ir_blk{ @"L1716" [%"pr.56" : P = phi("L1714" => %"v1719", "L1715" => %"v1723")]:
    %"v1728" : L = Ptoi %"pr.56";
    %"v1729" : L = Ptoi #0;
    %"v1730" : W = (Cmp Eq L) %"v1728", %"v1729"
    => br %"v1730" ? "L1724" : "L1630" };
  ir_blk{ @"L1724":
    %"v1732" : W = (Cmp Slt W) %"v16", #0;
    %"v1734" : L = (Ext Sw) %"v16"
    => br %"v1732" ? "L1735" : poll "L1091" };
  ir_blk{ @"L1735":
    %"v1740" : L = Neg %"v1734"
    => goto poll "L1091" };
  ir_blk{ @"L1742":
    => br %"v696" ? "L1747" : "L1745" };
  ir_blk{ @"L1745":
    %"v1750" : W = Sub %"pr.81", #1;
    %"v1755" : W = (Cmp Eq W) %"pr.64", #0
    => br %"v1755" ? "L1751" : "L1753" };
  ir_blk{ @"L1751":
    %"v1758" : L = (Ext Sw) %"v1750";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1758")
    => goto "L1753" };
  ir_blk{ @"L1753":
    %"v1766" = %"v612" +p #48;
    %"chk141" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1766";
    %"v1767" : W = (RawLoad (LdNarrow Sw) 0) %"chk141";
    %"v1768" : L = (Ext Sw) %"v1767";
    %"v1769" : L = Shl %"v1768", #4;
    %"v1770" = %"pr.16" +p %"v1769";
    %"chk142" : A = (Check 0 4 Read 1) %"v1770";
    %"v1771" : W = (RawLoad (LdNarrow Sw) 0) %"chk142";
    %"v1772" : W = (Ext Ub) %"v1771";
    call %"v1773" : W = $"__btowc"(W %"v1772");
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v1773")
    => br %"pr.64" ? "L1774" : "L865" };
  ir_blk{ @"L1774":
    %"v1780" : L = (Ext Sw) %"v1750";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1780")
    => goto "L865" };
  ir_blk{ @"L1781":
    %"v1789" = %"v612" +p #48;
    %"chk143" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1789";
    %"v1790" : W = (RawLoad (LdNarrow Sw) 0) %"chk143";
    %"v1791" : L = (Ext Sw) %"v1790";
    %"v1792" : L = Shl %"v1791", #4;
    %"v1793" = %"pr.16" +p %"v1792";
    %"chk144" : A = (Check 0 8 Read 8) %"v1793";
    %"v1794" : P = (RawLoadPointer 0 load_effects) %"chk144"
    => goto "L1630" };
  ir_blk{ @"L1630" [%"pr.88" : W = phi("L1781" => %"pr.89", "L1625" => %"pr.89", "L1614" => #5, "L1716" => %"pr.89"); %"pr.71" : W = phi("L1781" => %"v696", "L1625" => #1, "L1614" => #1, "L1716" => #0); %"pr.55" : P = phi("L1781" => %"v1794", "L1625" => %"v1623", "L1614" => %"v1623", "L1716" => %"pr.56")]:
    %"v1799" : L = Ptoi %"pr.55";
    %"v1800" : L = Ptoi #0;
    %"v1801" : W = (Cmp Eq L) %"v1799", %"v1800"
    => br %"v1801" ? "L1795" : "L1796" };
  ir_blk{ @"L1795":
    %"v1807" : W = (Cmp Eq W) %"pr.88", #4294967295
    => br %"v1807" ? "L1809" : "L1808" };
  ir_blk{ @"L1808":
    %"v1815" : W = (Cmp Sge W) %"pr.88", #6
    => goto "L1809" };
  ir_blk{ @"L1809" [%"v1817" : W = phi("L1795" => #1, "L1808" => %"v1815")]:
    => br %"v1817" ? "L1802" : "L1803" };
  ir_blk{ @"L1802":
    %"v1818" : P = Copy $"glibc_vfwprintf_internal#null"
    => goto "L1797" };
  ir_blk{ @"L1803":
    %"v1823" : P = Copy $"glibc_vfwprintf_internal#str.290"
    => goto "L1797" };
  ir_blk{ @"L1796":
    %"v1828" : W = (Cmp Eq W) %"pr.71", #0
    => br %"v1828" ? "L1829" : "L1830" };
  ir_blk{ @"L1829":
    %"v1832" : W = (Cmp Ne W) %"v738", #83
    => goto "L1830" };
  ir_blk{ @"L1830" [%"v1834" : W = phi("L1796" => #0, "L1829" => %"v1832")]:
    => br %"v1834" ? "L1824" : "L1825" };
  ir_blk{ @"L1824":
    %"v1840" : W = (Cmp Ne W) %"pr.64", #0;
    call void $"glibc_vfwprintf_internal#outstring_converted_wide_string"(P %"v0", P %"pr.55", W %"pr.88", W %"pr.81", W %"v1840")
    => goto "L865" };
  ir_blk{ @"L1825":
    %"v1847" : W = (Cmp Ne W) %"pr.88", #4294967295
    => br %"v1847" ? "L1842" : "L1843" }] [ir_blk{ @"L1842":
    %"v1850" : L = (Ext Sw) %"pr.88";
    call %"v1851" : L = $"__wcsnlen"(P %"pr.55", L %"v1850")
    => goto "L1844" };
  ir_blk{ @"L1843":
    call %"v1853" : L = $"__wcslen"(P %"pr.55")
    => goto "L1844" };
  ir_blk{ @"L1844" [%"pr.101" : L = phi("L1842" => %"v1851", "L1843" => %"v1853")]:
    => goto "L1797" };
  ir_blk{ @"L1797" [%"pr.99" : L = phi("L1802" => #6, "L1803" => #0, "L1844" => %"pr.101"); %"pr.57" : P = phi("L1802" => %"v1818", "L1803" => %"v1823", "L1844" => %"pr.55")]:
    %"v1859" : L = (Ext Sw) %"pr.81";
    %"v1860" : L = Sub %"v1859", %"pr.99";
    %"v1861" : W = (Cmp Slt W) %"v1860", #0
    => br %"v1861" ? "L1854" : "L1856" };
  ir_blk{ @"L1854":
    call void $"__wprintf_buffer_write"(P %"v0", P %"pr.57", L %"pr.99")
    => goto "L865" };
  ir_blk{ @"L1856":
    %"v1870" : W = (Cmp Eq W) %"pr.64", #0
    => br %"v1870" ? "L1866" : "L1868" };
  ir_blk{ @"L1866":
    %"v1872" : W = Copy %"v1860";
    %"v1873" : L = (Ext Sw) %"v1872";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1873")
    => goto "L1868" };
  ir_blk{ @"L1868":
    call void $"__wprintf_buffer_write"(P %"v0", P %"pr.57", L %"pr.99")
    => br %"pr.64" ? "L1877" : "L865" };
  ir_blk{ @"L1877":
    %"v1882" : W = Copy %"v1860";
    %"v1883" : L = (Ext Sw) %"v1882";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1883")
    => goto "L865" };
  ir_blk{ @"L1747":
    %"v1885" : W = Sub %"pr.81", #1;
    %"v1890" : W = (Cmp Eq W) %"pr.64", #0
    => br %"v1890" ? "L1886" : "L1888" };
  ir_blk{ @"L1886":
    %"v1893" : L = (Ext Sw) %"v1885";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1893")
    => goto "L1888" };
  ir_blk{ @"L1888":
    %"v1901" = %"v612" +p #48;
    %"chk145" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1901";
    %"v1902" : W = (RawLoad (LdNarrow Sw) 0) %"chk145";
    %"v1903" : L = (Ext Sw) %"v1902";
    %"v1904" : L = Shl %"v1903", #4;
    %"v1905" = %"pr.16" +p %"v1904";
    %"chk146" : A = (Check 0 4 Read 1) %"v1905";
    %"v1906" : W = (RawLoad (LdNarrow Sw) 0) %"chk146";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v1906")
    => br %"pr.64" ? "L1907" : "L865" };
  ir_blk{ @"L1907":
    %"v1913" : L = (Ext Sw) %"v1885";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1913")
    => goto "L865" };
  ir_blk{ @"L1915":
    %"v1923" = %"v612" +p #48;
    %"chk147" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1923";
    %"v1924" : W = (RawLoad (LdNarrow Sw) 0) %"chk147";
    %"v1925" : L = (Ext Sw) %"v1924";
    %"v1926" : L = Shl %"v1925", #4;
    %"v1927" = %"pr.16" +p %"v1926";
    %"chk148" : A = (Check 0 8 Write 8) %"v1916";
    store.ptr [%"chk148" + 0] <- %"v1927";
    %"v1932" : W = And %"v22", #1
    => br %"v1932" ? "L1928" : "L1954" };
  ir_blk{ @"L1928":
    %"v1941" = %"v612" +p #52;
    %"chk149" : A = (HalfCheck Upper 0 4 Write 1) %"chk66", %"v1941";
    store Ww [%"chk149" + 0] <- #7;
    %"v1947" = %"v612" +p #12;
    %"chk150" : A = (Renew 0 4 Read 1) %"chk66", %"v1947";
    %"v1948" : W = (RawLoad (LdNarrow Uw) 0) %"chk150";
    %"v1949" : W = And %"v1948", #4294967294;
    store Ww [%"chk150" + 0] <- %"v1949"
    => goto "L1954" };
  ir_blk{ @"L1954":
    %"v1962" = %"v612" +p #12;
    %"chk152" : A = (Renew 0 4 Read 1) %"chk66", %"v1962";
    %"v1963" : W = (RawLoad (LdNarrow Uw) 0) %"chk152";
    %"v1964" : W = And %"v1963", #4294963199;
    %"chk153" : A = (Renew 0 4 Write 1) %"chk66", %"v1962";
    store Ww [%"chk153" + 0] <- %"v1964";
    call void $"glibc_vfwprintf_internal#__printf_fp_spec"(P %"v0", P %"v612", P %"v1916")
    => goto "L865" };
  ir_blk{ @"L1976":
    call void $"glibc_vfwprintf_internal#printf_unknown"(P %"v0", P %"v612")
    => goto "L865" };
  ir_blk{ @"L865" [%"pr.4" : W = phi("L1574" => %"pr.3", "L1824" => %"pr.3", "L1854" => %"pr.3", "L1954" => %"pr.3", "L1976" => %"pr.3", "L983" => %"pr.3", "L929" => %"pr.3", "L1490" => %"pr.3", "L1481" => %"pr.3", "L1689" => %"pr.1", "L1696" => %"pr.1", "L1703" => %"pr.1", "L1704" => %"pr.1", "L1774" => %"pr.3", "L1753" => %"pr.3", "L1877" => %"pr.3", "L1868" => %"pr.3", "L1907" => %"pr.3", "L1888" => %"pr.3")]:
    %"v1992" = %"v612" +p #24;
    %"chk154" : A = (HalfCheck Upper 0 8 Read 8) %"chk66", %"v1992";
    %"v1993" : P = (RawLoadPointer 0 load_effects) %"chk154";
    %"v1999" = %"v612" +p #32;
    %"chk155" : A = (HalfCheck Upper 0 8 Read 8) %"chk66", %"v1999";
    %"v2000" : P = (RawLoadPointer 0 load_effects) %"chk155";
    %"v2007" : P = (RawLoadPointer 0 load_effects) %"chk154";
    %"v2008" : L = Ptoi %"v2000";
    %"v2009" : L = Ptoi %"v2007";
    %"v2010" : L = Sub %"v2008", %"v2009";
    %"v2011" : L = Div %"v2010", #4;
    call void $"__wprintf_buffer_write"(P %"v0", P %"v1993", L %"v2011");
    %"v2013" : W = Add %"pr.5", #1
    => goto poll "L587" };
  ir_blk{ @"L101":
    call void $"glibc_vfwprintf_internal#scratch_buffer_free"(P %"v31");
    call void $"glibc_vfwprintf_internal#scratch_buffer_free"(P %"v24")
    => ret void };
  ir_blk{ @"L2017":
    %"v2019" : W = (Cmp Ult L) %"v980", #4
    => br %"v2019" ? "L2020" : "L2021" };
  ir_blk{ @"L2020":
    %"v2022" : W = (Cmp Eq L) %"v980", #1
    => br %"v2022" ? poll "L1976" : "L2023" };
  ir_blk{ @"L2023":
    %"v2024" : W = (Cmp Eq L) %"v980", #2
    => br %"v2024" ? poll "L983" : "L2025" };
  ir_blk{ @"L2025":
    %"v2026" : W = (Cmp Eq L) %"v980", #3
    => br %"v2026" ? poll "L987" : "L2015" };
  ir_blk{ @"L2021":
    %"v2028" : W = (Cmp Eq L) %"v980", #4
    => br %"v2028" ? poll "L1093" : "L2029" };
  ir_blk{ @"L2029":
    %"v2030" : W = (Cmp Eq L) %"v980", #5
    => br %"v2030" ? poll "L1093" : "L2031" };
  ir_blk{ @"L2031":
    %"v2032" : W = (Cmp Eq L) %"v980", #6
    => br %"v2032" ? poll "L1093" : "L2033" };
  ir_blk{ @"L2033":
    %"v2034" : W = (Cmp Eq L) %"v980", #7
    => br %"v2034" ? poll "L1915" : "L2015" };
  ir_blk{ @"L2018":
    %"v2036" : W = (Cmp Ult L) %"v980", #12
    => br %"v2036" ? "L2037" : "L2038" };
  ir_blk{ @"L2037":
    %"v2039" : W = (Cmp Eq L) %"v980", #8
    => br %"v2039" ? poll "L1742" : "L2040" };
  ir_blk{ @"L2040":
    %"v2041" : W = (Cmp Eq L) %"v980", #9
    => br %"v2041" ? poll "L1781" : "L2042" };
  ir_blk{ @"L2042":
    %"v2043" : W = (Cmp Eq L) %"v980", #10
    => br %"v2043" ? poll "L1599" : "L2044" };
  ir_blk{ @"L2044":
    %"v2045" : W = (Cmp Eq L) %"v980", #11
    => br %"v2045" ? poll "L1631" : "L2015" };
  ir_blk{ @"L2038":
    %"v2047" : W = (Cmp Eq L) %"v980", #12
    => br %"v2047" ? poll "L1713" : "L2048" };
  ir_blk{ @"L2048":
    %"v2049" : W = (Cmp Eq L) %"v980", #13
    => br %"v2049" ? poll "L1747" : "L2050" };
  ir_blk{ @"L2050":
    %"v2051" : W = (Cmp Eq L) %"v980", #14
    => br %"v2051" ? poll "L1915" : "L2052" };
  ir_blk{ @"L2052":
    %"v2053" : W = (Cmp Eq L) %"v980", #15
    => br %"v2053" ? poll "L1093" : "L2015" };
  ir_blk{ @"L2015":
    => unreachable }])))) }.

Definition item_glibc_vfwprintf_internal'23printf_positional'2estep4_jumps'2e295 : item :=
  (IData (a "glibc_vfwprintf_internal#printf_positional.step4_jumps.295") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 1); (Item Ww 2); (Item Ww 3); (Item Ww 4); (Item Ww 5); (Item Ww 6); (Item Ww 7); (Item Ww 8); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 0)]).

Definition fn_glibc_vfwprintf_internal'23printf_unknown : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#printf_unknown"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v4" : P = (Alloc 4) #48;
    %"v8" = %"v4" +p #48;
    %"iw_1.v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v11" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v13" : L = Ptoi %"iw_1.v9";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Ne L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L5";
  @"iw_1.L4":
    %"iw_1.v17" = %"v0" +p #8;
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v19" = %"iw_1.v18" +p #4;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"iw_1.v17";
    store.ptr [%"chk3" + 0] <- %"iw_1.v19";
    %"chk4" : A = (Check 0 4 Write 1) %"iw_1.v18";
    store Ww [%"chk4" + 0] <- #37
    => goto "iw_1.join";
  @"iw_1.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #37)
    => goto "iw_1.join";
  @"iw_1.join":
    %"v15" = %"v2" +p #12;
    %"chk5" : A = (Check 0 4 Read 1) %"v15";
    %"v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v17" : W = Shl %"v16", #28;
    %"v18" : W = Shr %"v17", #31
    => br %"v18" ? "iw_2.start" : "L13";
  @"iw_2.start":
    %"iw_2.v8" = %"v0" +p #8;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"iw_2.v8";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_2.v11" = %"v0" +p #16;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_2.v13" : L = Ptoi %"iw_2.v9";
    %"iw_2.v14" : L = Ptoi %"iw_2.v12";
    %"iw_2.v15" : W = (Cmp Ne L) %"iw_2.v13", %"iw_2.v14"
    => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
  @"iw_2.L4":
    %"iw_2.v17" = %"v0" +p #8;
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_2.v19" = %"iw_2.v18" +p #4;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk0", %"iw_2.v17";
    store.ptr [%"chk9" + 0] <- %"iw_2.v19";
    %"chk10" : A = (Check 0 4 Write 1) %"iw_2.v18";
    store Ww [%"chk10" + 0] <- #35
    => goto "L13";
  @"iw_2.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #35)
    => goto "L13";
  @"L13":
    %"v24" = %"v2" +p #12;
    %"chk11" : A = (Renew 0 4 Read 1) %"chk5", %"v24";
    %"v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v26" : W = Shl %"v25", #24;
    %"v27" : W = Shr %"v26", #31
    => br %"v27" ? "iw_3.start" : "L22";
  @"iw_3.start":
    %"iw_3.v8" = %"v0" +p #8;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"iw_3.v8";
    %"iw_3.v9" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_3.v11" = %"v0" +p #16;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk1", %"iw_3.v11";
    %"iw_3.v12" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_3.v13" : L = Ptoi %"iw_3.v9";
    %"iw_3.v14" : L = Ptoi %"iw_3.v12";
    %"iw_3.v15" : W = (Cmp Ne L) %"iw_3.v13", %"iw_3.v14"
    => br %"iw_3.v15" ? "iw_3.L4" : "iw_3.L5";
  @"iw_3.L4":
    %"iw_3.v17" = %"v0" +p #8;
    %"iw_3.v18" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_3.v19" = %"iw_3.v18" +p #4;
    %"chk15" : A = (Renew 0 8 Write 8) %"chk0", %"iw_3.v17";
    store.ptr [%"chk15" + 0] <- %"iw_3.v19";
    %"chk16" : A = (Check 0 4 Write 1) %"iw_3.v18";
    store Ww [%"chk16" + 0] <- #39
    => goto "L22";
  @"iw_3.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #39)
    => goto "L22";
  @"L22":
    %"v33" = %"v2" +p #12;
    %"chk17" : A = (Renew 0 4 Read 1) %"chk5", %"v33";
    %"v34" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v35" : W = Shl %"v34", #25;
    %"v36" : W = Shr %"v35", #31
    => br %"v36" ? "iw_4.start" : "L30";
  @"iw_4.start":
    %"iw_4.v8" = %"v0" +p #8;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"iw_4.v8";
    %"iw_4.v9" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"iw_4.v11" = %"v0" +p #16;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v11";
    %"iw_4.v12" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"iw_4.v13" : L = Ptoi %"iw_4.v9";
    %"iw_4.v14" : L = Ptoi %"iw_4.v12";
    %"iw_4.v15" : W = (Cmp Ne L) %"iw_4.v13", %"iw_4.v14"
    => br %"iw_4.v15" ? "iw_4.L4" : "iw_4.L5";
  @"iw_4.L4":
    %"iw_4.v17" = %"v0" +p #8;
    %"iw_4.v18" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"iw_4.v19" = %"iw_4.v18" +p #4;
    %"chk21" : A = (Renew 0 8 Write 8) %"chk0", %"iw_4.v17";
    store.ptr [%"chk21" + 0] <- %"iw_4.v19";
    %"chk22" : A = (Check 0 4 Write 1) %"iw_4.v18";
    store Ww [%"chk22" + 0] <- #43
    => goto "L31";
  @"iw_4.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #43)
    => goto "L31";
  @"L30":
    %"v42" = %"v2" +p #12;
    %"v43" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v44" : W = Shl %"v43", #27;
    %"v45" : W = Shr %"v44", #31
    => br %"v45" ? "iw_5.start" : "L31";
  @"iw_5.start":
    %"iw_5.v8" = %"v0" +p #8;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"iw_5.v8";
    %"iw_5.v9" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_5.v11" = %"v0" +p #16;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk1", %"iw_5.v11";
    %"iw_5.v12" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_5.v13" : L = Ptoi %"iw_5.v9";
    %"iw_5.v14" : L = Ptoi %"iw_5.v12";
    %"iw_5.v15" : W = (Cmp Ne L) %"iw_5.v13", %"iw_5.v14"
    => br %"iw_5.v15" ? "iw_5.L4" : "iw_5.L5";
  @"iw_5.L4":
    %"iw_5.v17" = %"v0" +p #8;
    %"iw_5.v18" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_5.v19" = %"iw_5.v18" +p #4;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk0", %"iw_5.v17";
    store.ptr [%"chk27" + 0] <- %"iw_5.v19";
    %"chk28" : A = (Check 0 4 Write 1) %"iw_5.v18";
    store Ww [%"chk28" + 0] <- #32
    => goto "L31";
  @"iw_5.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #32)
    => goto "L31";
  @"L31":
    %"v51" = %"v2" +p #12;
    %"chk29" : A = (Renew 0 4 Read 1) %"chk5", %"v51";
    %"v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v53" : W = Shl %"v52", #26;
    %"v54" : W = Shr %"v53", #31
    => br %"v54" ? "iw_6.start" : "L49";
  @"iw_6.start":
    %"iw_6.v8" = %"v0" +p #8;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk0", %"iw_6.v8";
    %"iw_6.v9" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_6.v11" = %"v0" +p #16;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk1", %"iw_6.v11";
    %"iw_6.v12" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_6.v13" : L = Ptoi %"iw_6.v9";
    %"iw_6.v14" : L = Ptoi %"iw_6.v12";
    %"iw_6.v15" : W = (Cmp Ne L) %"iw_6.v13", %"iw_6.v14"
    => br %"iw_6.v15" ? "iw_6.L4" : "iw_6.L5";
  @"iw_6.L4":
    %"iw_6.v17" = %"v0" +p #8;
    %"iw_6.v18" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_6.v19" = %"iw_6.v18" +p #4;
    %"chk33" : A = (Renew 0 8 Write 8) %"chk0", %"iw_6.v17";
    store.ptr [%"chk33" + 0] <- %"iw_6.v19";
    %"chk34" : A = (Check 0 4 Write 1) %"iw_6.v18";
    store Ww [%"chk34" + 0] <- #45
    => goto "L49";
  @"iw_6.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #45)
    => goto "L49";
  @"L49":
    %"v60" = %"v2" +p #16;
    %"chk35" : A = (HalfCheck Upper 0 4 Read 1) %"chk5", %"v60";
    %"v61" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v62" : W = (Cmp Eq W) %"v61", #48
    => br %"v62" ? "iw_7.start" : "L58";
  @"iw_7.start":
    %"iw_7.v8" = %"v0" +p #8;
    %"chk36" : A = (Renew 0 8 Read 8) %"chk0", %"iw_7.v8";
    %"iw_7.v9" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"iw_7.v11" = %"v0" +p #16;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk1", %"iw_7.v11";
    %"iw_7.v12" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_7.v13" : L = Ptoi %"iw_7.v9";
    %"iw_7.v14" : L = Ptoi %"iw_7.v12";
    %"iw_7.v15" : W = (Cmp Ne L) %"iw_7.v13", %"iw_7.v14"
    => br %"iw_7.v15" ? "iw_7.L4" : "iw_7.L5";
  @"iw_7.L4":
    %"iw_7.v17" = %"v0" +p #8;
    %"iw_7.v18" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"iw_7.v19" = %"iw_7.v18" +p #4;
    %"chk39" : A = (Renew 0 8 Write 8) %"chk0", %"iw_7.v17";
    store.ptr [%"chk39" + 0] <- %"iw_7.v19";
    %"chk40" : A = (Check 0 4 Write 1) %"iw_7.v18";
    store Ww [%"chk40" + 0] <- #48
    => goto "L58";
  @"iw_7.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #48)
    => goto "L58";
  @"L58":
    %"v68" = %"v2" +p #12;
    %"chk41" : A = (Renew 0 4 Read 1) %"chk5", %"v68";
    %"v69" : W = (RawLoad (LdNarrow Uw) 0) %"chk41";
    %"v70" : W = Shl %"v69", #20;
    %"v71" : W = Shr %"v70", #31
    => br %"v71" ? "L64" : "L66";
  @"L64":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #73)
    => goto "L66";
  @"L66":
    %"v77" = %"v2" +p #4;
    %"chk42" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v77";
    %"v78" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v79" : W = (Cmp Ne W) %"v78", #0
    => br %"v79" ? "L73" : "L75";
  @"L73":
    %"v81" = %"v2" +p #4;
    %"v82" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v83" : L = (Ext Sw) %"v82";
    %"iw_8.v14" : P = Copy $"_itowa_lower_digits"
    => goto "iw_8.L22";
  @"iw_8.L22" [%"iw_8.pr.6" : P = phi("iw_8.L22" => %"iw_8.v26", "L73" => %"v8"); %"iw_8.pr.1" : L = phi("iw_8.L22" => %"iw_8.v34", "L73" => %"v83")]:
    (Flight (a "iw_8.v26") Sub [(FAddress (t "iw_8.pr.6")); (FValue (Const 4))] (LowerOf (t "iw_8.pr.6")));
    %"iw_8.v29" : L = Urem %"iw_8.pr.1", #10;
    %"iw_8.v30" : L = Shl %"iw_8.v29", #2;
    %"iw_8.v31" = %"iw_8.v14" +p %"iw_8.v30";
    %"chk44" : A = (Check 0 4 Read 1) %"iw_8.v31";
    %"iw_8.v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"chk45" : A = (Check 0 4 Write 1) %"iw_8.v26";
    store Ww [%"chk45" + 0] <- %"iw_8.v32";
    %"iw_8.v34" : L = Udiv %"iw_8.pr.1", #10;
    %"iw_8.v35" : W = (Cmp Ne L) %"iw_8.v34", #0
    => br %"iw_8.v35" ? poll "iw_8.L22" : "L86";
  @"L86" [%"pr.2" : P = phi("L87" => %"v96", "iw_8.L22" => %"iw_8.v26")]:
    %"v91" : L = Ptoi %"pr.2";
    %"v92" : L = Ptoi %"v8";
    %"v93" : W = (Cmp Ult L) %"v91", %"v92"
    => br %"v93" ? "L87" : "L75";
  @"L87":
    %"v96" = %"pr.2" +p #4;
    %"chk46" : A = (Check 0 4 Read 1) %"pr.2";
    %"v97" : W = (RawLoad (LdNarrow Sw) 0) %"chk46";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v97")
    => goto poll "L86";
  @"L75":
    %"chk47" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v2";
    %"v102" : W = (RawLoad (LdNarrow Sw) 0) %"chk47";
    %"v104" : W = (Cmp Ne W) %"v102", #4294967295
    => br %"v104" ? "L98" : "L100";
  @"L98":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #46);
    %"chk48" : A = (Renew 0 4 Read 1) %"chk47", %"v2";
    %"v107" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"v108" : L = (Ext Sw) %"v107";
    %"iw_9.v14" : P = Copy $"_itowa_lower_digits"
    => goto "iw_9.L22";
  @"iw_9.L22" [%"iw_9.pr.6" : P = phi("iw_9.L22" => %"iw_9.v26", "L98" => %"v8"); %"iw_9.pr.1" : L = phi("iw_9.L22" => %"iw_9.v34", "L98" => %"v108")]:
    (Flight (a "iw_9.v26") Sub [(FAddress (t "iw_9.pr.6")); (FValue (Const 4))] (LowerOf (t "iw_9.pr.6")));
    %"iw_9.v29" : L = Urem %"iw_9.pr.1", #10;
    %"iw_9.v30" : L = Shl %"iw_9.v29", #2;
    %"iw_9.v31" = %"iw_9.v14" +p %"iw_9.v30";
    %"chk49" : A = (Check 0 4 Read 1) %"iw_9.v31";
    %"iw_9.v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk49";
    %"chk50" : A = (Check 0 4 Write 1) %"iw_9.v26";
    store Ww [%"chk50" + 0] <- %"iw_9.v32";
    %"iw_9.v34" : L = Udiv %"iw_9.pr.1", #10;
    %"iw_9.v35" : W = (Cmp Ne L) %"iw_9.v34", #0
    => br %"iw_9.v35" ? poll "iw_9.L22" : "L111";
  @"L111" [%"pr.1" : P = phi("L112" => %"v121", "iw_9.L22" => %"iw_9.v26")]:
    %"v116" : L = Ptoi %"pr.1";
    %"v117" : L = Ptoi %"v8";
    %"v118" : W = (Cmp Ult L) %"v116", %"v117"
    => br %"v118" ? "L112" : "L100";
  @"L112":
    %"v121" = %"pr.1" +p #4;
    %"chk51" : A = (Check 0 4 Read 1) %"pr.1";
    %"v122" : W = (RawLoad (LdNarrow Sw) 0) %"chk51";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v122")
    => goto poll "L111";
  @"L100":
    %"v127" = %"v2" +p #8;
    %"chk52" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v127";
    %"v128" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    %"v129" : W = (Cmp Ne W) %"v128", #0
    => br %"v129" ? "L123" : "L125";
  @"L123":
    %"v132" = %"v2" +p #8;
    %"v133" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v133")
    => goto "L125";
  @"L125":
    => ret void
} }.

Definition fn_glibc_vfwprintf_internal'23read_int : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#read_int"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 4 Read 1) %"v4";
    %"v5" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v6" : W = Sub %"v5", #48
    => goto "L7";
  @"L7" [%"pr.4" : W = phi("start" => %"v6", "L16" => #4294967295, "L36" => %"v45", "L22" => #4294967295, "L8" => %"pr.4")]:
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v12" = %"v11" +p #4;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk3" + 0] <- %"v12";
    %"chk4" : A = (Check 0 4 Read 1) %"v12";
    %"v13" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v14" : W = Sub %"v13", #48;
    %"v15" : W = (Cmp Ult W) %"v14", #10
    => br %"v15" ? "L8" : "L9";
  @"L8":
    %"v20" : W = (Cmp Sge W) %"pr.4", #0
    => br %"v20" ? "L16" : poll "L7";
  @"L16":
    %"v26" : W = (Cmp Sgt W) %"pr.4", #214748364
    => br %"v26" ? poll "L7" : "L22";
  @"L22":
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 4 Read 1) %"v30";
    %"v31" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v32" : W = Sub %"v31", #48;
    %"v34" : W = Mul %"pr.4", #10;
    %"v39" : W = Sub #2147483647, %"v32";
    %"v41" : W = (Cmp Slt W) %"v39", %"v34"
    => br %"v41" ? poll "L7" : "L36";
  @"L36":
    %"v45" : W = Add %"v34", %"v32"
    => goto poll "L7";
  @"L9":
    => ret %"pr.4"
} }.

Definition fn_glibc_vfwprintf_internal'23scratch_buffer_free : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#scratch_buffer_free"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" = %"v0" +p #16;
    %"v9" : L = Ptoi %"v6";
    %"v10" : L = Ptoi %"v8";
    %"v11" : W = (Cmp Ne L) %"v9", %"v10"
    => br %"v11" ? "L2" : "L4";
  @"L2":
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"free"(P %"v13")
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition fn_glibc_vfwprintf_internal'23scratch_buffer_init : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#scratch_buffer_init"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #16;
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v4";
    %"v6" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v6";
    store Wl [%"chk1" + 0] <- #1024
    => ret void
} }.

Definition item_glibc_vfwprintf_internal'23str'2e285 : item :=
  (IData (a "glibc_vfwprintf_internal#str.285") (LRo (a "local")) 4 [(Item Ww 40); (Item Ww 110); (Item Ww 105); (Item Ww 108); (Item Ww 41); (Item Ww 0)]).

Definition item_glibc_vfwprintf_internal'23str'2e286 : item :=
  (IData (a "glibc_vfwprintf_internal#str.286") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 37); (Item Wb 110); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 103); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 115); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_vfwprintf_internal'23str'2e287 : item :=
  (IData (a "glibc_vfwprintf_internal#str.287") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 102); (Item Wb 115); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 117); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_vfwprintf_internal'23str'2e290 : item :=
  (IData (a "glibc_vfwprintf_internal#str.290") (LRo (a "local")) 4 [(Item Ww 0)]).

Definition item_glibc_vfwprintf_internal'23str'2e291 : item :=
  (IData (a "glibc_vfwprintf_internal#str.291") (LRo (a "local")) 1 [(Item Wb 40); (Item Wb 109); (Item Wb 111); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 97); (Item Wb 103); (Item Wb 115); (Item Wb 32); (Item Wb 38); (Item Wb 32); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 70); (Item Wb 95); (Item Wb 70); (Item Wb 79); (Item Wb 82); (Item Wb 84); (Item Wb 73); (Item Wb 70); (Item Wb 89); (Item Wb 41); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_vfwprintf_internal'23str'2e292 : item :=
  (IData (a "glibc_vfwprintf_internal#str.292") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 118); (Item Wb 102); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_vfwprintf_internal'23str'2e293 : item :=
  (IData (a "glibc_vfwprintf_internal#str.293") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 112); (Item Wb 111); (Item Wb 115); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_vfwprintf_internal'23str'2e294 : item :=
  (IData (a "glibc_vfwprintf_internal#str.294") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 78); (Item Wb 36); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).
