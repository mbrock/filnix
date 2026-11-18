(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedINBlocks1663x1 HelloImageTypedINBlocks1663x2 IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___init_misc : func :=
  ir_fn{ "export" "__init_misc"(W %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v10" : L = Ptoi %"v2";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L12" : "L13";
  @"L12":
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v17" : L = Ptoi %"v16";
    %"v18" : W = (Cmp Ne L) %"v17", #0
    => goto "L13";
  @"L13" [%"v20" : W = phi("start" => #0, "L12" => %"v18")]:
    => br %"v20" ? "L6" : "L8";
  @"L6":
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v25" : P = $"__GI_strrchr"(P %"v24", W #47);
    %"v30" : L = Ptoi %"v25";
    %"v31" : L = Ptoi #0;
    %"v32" : W = (Cmp Eq L) %"v30", %"v31"
    => br %"v32" ? "L26" : "L27";
  @"L26":
    %"v33" : P = Copy $"__progname";
    %"chk2" : A = (Renew 0 8 Read 8) %"chk1", %"v2";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (Check 0 8 Write 8) %"v33";
    store.ptr [%"chk3" + 0] <- %"v36"
    => goto "L28";
  @"L27":
    %"v37" : P = Copy $"__progname";
    %"v39" = %"v25" +p #1;
    %"chk4" : A = (Check 0 8 Write 8) %"v37";
    store.ptr [%"chk4" + 0] <- %"v39"
    => goto "L28";
  @"L28":
    %"v40" : P = Copy $"__progname_full";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk1", %"v2";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Write 8) %"v40";
    store.ptr [%"chk6" + 0] <- %"v43"
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition hello_image_fn___internal_atexit : func :=
  ir_fn{ "export" "__internal_atexit"(P %"v0", P %"v2", P %"v4", P %"v6") -> (RClass W) {
  @"start":
    %"v13" : L = Ptoi %"v0";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Ne L) %"v13", %"v14"
    => br %"v15" ? "L11" : "L10";
  @"L10":
    %"v16" : P = Copy $"glibc_cxa_atexit#str.233";
    %"v17" : P = Copy $"glibc_cxa_atexit#str.234";
    %"v18" : P = Copy $"glibc_cxa_atexit#str.235";
    call void $"__libc_assert_fail"(P %"v16", P %"v17", W #41, P %"v18")
    => goto "L11";
  @"L11":
    %"v20" : P = Copy $"__exit_funcs_lock";
    %"chk0" : A = (Check 0 4 Write 4) %"v20";
    %"v27" : W = (RawCas (CasNarrow Sw) 0) %"chk0", #0, #1;
    %"v28" : W = (Cmp Eq W) %"v27", #0
    => br %"v28" ? "L30" : "L29";
  @"L29":
    => goto "L30";
  @"L30":
    %"v31" : W = (Cmp Ne W) %"v27", #0
    => br %"v31" ? "L34" : "L23";
  @"L34":
    call void $"__GI___lll_lock_wait_private"(P %"v20")
    => goto "L23";
  @"L23":
    call %"v45" : P = $"__new_exitfn"(P %"v6");
    %"v50" : L = Ptoi %"v45";
    %"v52" : W = (Cmp Eq L) %"v50", %"v14"
    => br %"v52" ? "L46" : "L48";
  @"L46":
    %"v54" : P = Copy $"__exit_funcs_lock";
    %"chk1" : A = (Check 0 4 Read 1) %"v54";
    %"v58" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => goto "L59";
  @"L59" [%"v61" : W = phi("L46" => %"v58", "L59" => %"v62")]:
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v54";
    %"v62" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"v61", #0;
    %"v63" : W = (Cmp Eq W) %"v62", %"v61"
    => br %"v63" ? "L60" : poll "L59";
  @"L60":
    %"v68" : W = (Cmp Sgt W) %"v61", #1
    => br %"v68" ? "L71" : "L66";
  @"L71":
    call void $"__GI___lll_lock_wake_private"(P %"v54")
    => goto "L66";
  @"L66":
    => ret #4294967295;
  @"L48":
    %"v86" = %"v45" +p #8;
    %"chk3" : A = (Check 0 8 Write 8) %"v86";
    store.ptr [%"chk3" + 0] <- %"v0";
    %"v90" = %"v86" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v90";
    store.ptr [%"chk4" + 0] <- %"v2";
    %"v94" = %"v86" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v94";
    store.ptr [%"chk5" + 0] <- %"v4";
    %"chk6" : A = (HalfCheck Lower 0 8 Write 1) %"chk3", %"v45";
    store Wl [%"chk6" + 0] <- #4;
    %"v98" : P = Copy $"__exit_funcs_lock";
    %"chk7" : A = (Check 0 4 Read 1) %"v98";
    %"v102" : W = (RawLoad (LdNarrow Sw) 0) %"chk7"
    => goto "L103";
  @"L103" [%"v105" : W = phi("L48" => %"v102", "L103" => %"v106")]:
    %"chk8" : A = (HalfCheck Lower 0 4 Write 4) %"chk7", %"v98";
    %"v106" : W = (RawCas (CasNarrow Sw) 0) %"chk8", %"v105", #0;
    %"v107" : W = (Cmp Eq W) %"v106", %"v105"
    => br %"v107" ? "L104" : poll "L103";
  @"L104":
    %"v112" : W = (Cmp Sgt W) %"v105", #1
    => br %"v112" ? "L115" : "L110";
  @"L115":
    call void $"__GI___lll_lock_wake_private"(P %"v98")
    => goto "L110";
  @"L110":
    => ret #0
} }.

Definition hello_image_fn_glibc_libc_start'23intel_02_known_compare : func :=
  ir_fn{ "local" "glibc_libc_start#intel_02_known_compare"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 1 Read 1) %"v0";
    %"v12" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    %"chk1" : A = (Check 0 1 Read 1) %"v2";
    %"v14" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v15" : W = (Cmp Eq W) %"v12", %"v14"
    => br %"v15" ? "L8" : "L10";
  @"L8":
    => ret #0;
  @"L10":
    %"v21" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    %"v23" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v24" : W = (Cmp Slt W) %"v21", %"v23"
    => br %"v24" ? "L19" : "L18";
  @"L18":
    => goto "L19";
  @"L19" [%"v26" : W = phi("L18" => #1, "L10" => #4294967295)]:
    => ret %"v26"
} }.

Definition hello_image_fn_glibc_libc_start'23intel_check_word : func :=
  ir_fn{ "local" "glibc_libc_start#intel_check_word"(W %"v0", W %"v2", P %"v4", P %"v6", P %"v8", P %"v10") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v51" : P = (Alloc 4) #4;
    %"v52" : P = (Alloc 4) #4;
    %"v53" : P = (Alloc 4) #4;
    %"v54" : P = (Alloc 4) #4;
    %"v334" : P = (Alloc 4) #8;
    %"v16" : W = And %"v2", #2147483648;
    %"v17" : W = (Cmp Ne W) %"v16", #0
    => br %"v17" ? "L12" : "L14" };
  ir_blk{ @"L12":
    => ret #0 };
  ir_blk{ @"L14":
    %"v21" : W = Sub %"v0", #185;
    %"v22" : W = Div %"v21", #3;
    %"v23" : W = Mul %"v22", #3
    => goto "L24" };
  ir_blk{ @"L24" [%"pr.6" : W = phi("L14" => %"v23", "L34" => %"pr.9"); %"pr.5" : W = phi("L14" => %"v2", "L34" => %"v405"); %"pr.1" : W = phi("L14" => %"v0", "L34" => %"pr.4")]:
    %"v28" : W = (Cmp Ne W) %"pr.5", #0
    => br %"v28" ? "L25" : "L26" };
  ir_blk{ @"L25":
    %"v31" : W = And %"pr.5", #255;
    %"v36" : W = (Cmp Eq W) %"v31", #64
    => br %"v36" ? "L32" : "L33" };
  ir_blk{ @"L32":
    %"chk0" : A = (Check 0 1 Write 1) %"v6";
    store Wb [%"chk0" + 0] <- #1;
    %"v44" : W = (Cmp Eq W) %"pr.6", #9
    => br %"v44" ? "L26" : "L34" };
  ir_blk{ @"L33":
    %"v50" : W = (Cmp Eq W) %"v31", #255
    => br %"v50" ? "L56" : "L47" };
  ir_blk{ @"L56" [%"pr.10" : W = phi("L169" => %"v294", "L33" => #0)]:
    %"v64" = %"v10" +p #1;
    %"chk1" : A = (Check 0 1 Read 1) %"v64";
    %"v65" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v66" : W = (Cmp Ult W) %"pr.10", %"v65"
    => br %"v66" ? "L59" : "L60" };
  ir_blk{ @"L59":
    %"v68" = %"v10" +p #20;
    %"v70" : L = (Ext Uw) %"pr.10";
    %"v71" : L = Shl %"v70", #4;
    %"v72" = %"v68" +p %"v71";
    %"chk2" : A = (Check 0 4 Read 1) %"v72";
    %"v74" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"chk3" : A = (Check 0 4 Write 1) %"v51";
    store Ww [%"chk3" + 0] <- %"v74";
    %"v81" = %"v72" +p #4;
    %"chk4" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v81";
    %"v82" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"chk5" : A = (Check 0 4 Write 1) %"v52";
    store Ww [%"chk5" + 0] <- %"v82";
    %"v89" = %"v72" +p #8;
    %"chk6" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v89";
    %"v90" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"chk7" : A = (Check 0 4 Write 1) %"v53";
    store Ww [%"chk7" + 0] <- %"v90";
    %"v97" = %"v72" +p #12;
    %"chk8" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v97";
    %"v98" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"chk9" : A = (Check 0 4 Write 1) %"v54";
    store Ww [%"chk9" + 0] <- %"v98"
    => goto "L61" };
  ir_blk{ @"L60":
    %"v104" = %"v10" +p #1;
    %"v105" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v106" : W = (Cmp Eq W) %"pr.10", %"v105"
    => br %"v106" ? "L107" : "L108" };
  ir_blk{ @"L107":
    %"v111" : L = (Ext Uw) %"pr.10";
    %"v112" : W = (Cmp Ult L) %"v111", #16
    => goto "L108" };
  ir_blk{ @"L108" [%"v114" : W = phi("L60" => #0, "L107" => %"v112")]:
    => br %"v114" ? "L99" : "L100" };
  ir_blk{ @"L99":
    call void $"zcpuid_count"(W #4, W %"pr.10", P %"v51", P %"v52", P %"v53", P %"v54");
    %"v117" = %"v10" +p #20;
    %"v119" : L = (Ext Uw) %"pr.10";
    %"v120" : L = Shl %"v119", #4;
    %"v121" = %"v117" +p %"v120";
    %"chk11" : A = (Check 0 4 Read 1) %"v51";
    %"v123" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"chk12" : A = (Check 0 4 Write 1) %"v121";
    store Ww [%"chk12" + 0] <- %"v123";
    %"v130" = %"v121" +p #4;
    %"chk13" : A = (Check 0 4 Read 1) %"v52";
    %"v131" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"chk14" : A = (HalfCheck Upper 0 4 Write 1) %"chk12", %"v130";
    store Ww [%"chk14" + 0] <- %"v131";
    %"v138" = %"v121" +p #8;
    %"chk15" : A = (Check 0 4 Read 1) %"v53";
    %"v139" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk12", %"v138";
    store Ww [%"chk16" + 0] <- %"v139";
    %"v146" = %"v121" +p #12;
    %"chk17" : A = (Check 0 4 Read 1) %"v54";
    %"v147" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"chk18" : A = (HalfCheck Upper 0 4 Write 1) %"chk12", %"v146";
    store Ww [%"chk18" + 0] <- %"v147";
    %"v149" = %"v10" +p #1;
    %"chk19" : A = (Renew 0 1 Read 1) %"chk1", %"v149";
    %"v150" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"v151" : W = Add %"v150", #1;
    %"v152" : W = (Ext Ub) %"v151";
    %"chk20" : A = (Renew 0 1 Write 1) %"chk1", %"v149";
    store Wb [%"chk20" + 0] <- %"v152"
    => goto "L61" };
  ir_blk{ @"L100":
    call void $"zcpuid_count"(W #4, W %"pr.10", P %"v51", P %"v52", P %"v53", P %"v54")
    => goto "L61" };
  ir_blk{ @"L61":
    %"chk21" : A = (Check 0 4 Read 1) %"v51";
    %"v155" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v156" : W = And %"v155", #31;
    %"v161" : W = (Cmp Eq W) %"v156", #0
    => br %"v161" ? "L58" : "L159" };
  ir_blk{ @"L159":
    %"v164" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v165" : W = Shr %"v164", #5;
    %"v166" : W = And %"v165", #7;
    %"v171" : W = (Cmp Eq W) %"v166", #1
    => br %"v171" ? "L172" : "L173" };
  ir_blk{ @"L172":
    %"v175" : W = (Cmp Eq W) %"v156", #1
    => goto "L173" };
  ir_blk{ @"L173" [%"v177" : W = phi("L159" => #0, "L172" => %"v175")]:
    => br %"v177" ? "L178" : "L179" };
  ir_blk{ @"L178":
    %"v182" : W = (Cmp Eq W) %"pr.6", #3
    => goto "L179" };
  ir_blk{ @"L179" [%"v184" : W = phi("L173" => #0, "L178" => %"v182")]:
    => br %"v184" ? "L186" : "L185" };
  ir_blk{ @"L185":
    => br %"v171" ? "L189" : "L190" };
  ir_blk{ @"L189":
    %"v192" : W = (Cmp Eq W) %"v156", #2
    => goto "L190" };
  ir_blk{ @"L190" [%"v194" : W = phi("L185" => #0, "L189" => %"v192")]:
    => br %"v194" ? "L195" : "L186" };
  ir_blk{ @"L195":
    %"v199" : W = (Cmp Eq W) %"pr.6", #0
    => goto "L186" };
  ir_blk{ @"L186" [%"v203" : W = phi("L179" => #1, "L190" => #0, "L195" => %"v199")]:
    => br %"v203" ? "L205" : "L204" };
  ir_blk{ @"L204":
    %"v207" : W = (Cmp Eq W) %"v166", #2
    => br %"v207" ? "L208" : "L205" };
  ir_blk{ @"L208":
    %"v212" : W = (Cmp Eq W) %"pr.6", #6
    => goto "L205" };
  ir_blk{ @"L205" [%"v216" : W = phi("L186" => #1, "L204" => #0, "L208" => %"v212")]:
    => br %"v216" ? "L218" : "L217" };
  ir_blk{ @"L217":
    %"v220" : W = (Cmp Eq W) %"v166", #3
    => br %"v220" ? "L221" : "L218" };
  ir_blk{ @"L221":
    %"v225" : W = (Cmp Eq W) %"pr.6", #9
    => goto "L218" };
  ir_blk{ @"L218" [%"v229" : W = phi("L205" => #1, "L217" => #0, "L221" => %"v225")]:
    => br %"v229" ? "L231" : "L230" };
  ir_blk{ @"L230":
    %"v233" : W = (Cmp Eq W) %"v166", #4
    => br %"v233" ? "L234" : "L231" };
  ir_blk{ @"L234":
    %"v238" : W = (Cmp Eq W) %"pr.6", #12
    => goto "L231" };
  ir_blk{ @"L231" [%"v242" : W = phi("L218" => #1, "L230" => #0, "L234" => %"v238")]:
    => br %"v242" ? "L167" : "L169" }] [ir_blk{ @"L167":
    %"v245" : W = Sub %"pr.1", #185;
    %"v247" : W = Sub %"v245", %"pr.6";
    %"v252" : W = (Cmp Eq W) %"v247", #0
    => br %"v252" ? "L248" : "L250" };
  ir_blk{ @"L248":
    %"chk23" : A = (Check 0 4 Read 1) %"v52";
    %"v253" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v254" : W = Shr %"v253", #22;
    %"v255" : W = Add %"v254", #1;
    %"v256" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v257" : W = Shr %"v256", #12;
    %"v258" : W = And %"v257", #1023;
    %"v259" : W = Add %"v258", #1;
    %"v260" : W = Mul %"v255", %"v259";
    %"v261" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v262" : W = And %"v261", #4095;
    %"v263" : W = Add %"v262", #1;
    %"v264" : W = Mul %"v260", %"v263";
    %"chk26" : A = (Check 0 4 Read 1) %"v53";
    %"v265" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v266" : W = Add %"v265", #1;
    %"v267" : W = Mul %"v264", %"v266";
    %"v268" : L = (Ext Uw) %"v267"
    => ret %"v268" };
  ir_blk{ @"L250":
    %"v274" : W = (Cmp Eq W) %"v247", #1
    => br %"v274" ? "L270" : "L272" };
  ir_blk{ @"L270":
    %"chk27" : A = (Check 0 4 Read 1) %"v52";
    %"v275" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v276" : W = Shr %"v275", #22;
    %"v277" : W = Add %"v276", #1;
    %"v278" : L = (Ext Uw) %"v277"
    => ret %"v278" };
  ir_blk{ @"L272":
    %"v284" : W = (Cmp Eq W) %"v247", #2
    => br %"v284" ? "L282" : "L281" };
  ir_blk{ @"L281":
    %"v285" : P = Copy $"glibc_libc_start#str.301";
    %"v286" : P = Copy $"glibc_libc_start#str.302";
    %"v287" : P = Copy $"glibc_libc_start#str.303";
    call void $"__libc_assert_fail"(P %"v285", P %"v286", W #217, P %"v287")
    => goto "L282" };
  ir_blk{ @"L282":
    %"chk28" : A = (Check 0 4 Read 1) %"v52";
    %"v288" : W = (RawLoad (LdNarrow Uw) 0) %"chk28";
    %"v289" : W = And %"v288", #4095;
    %"v290" : W = Add %"v289", #1;
    %"v291" : L = (Ext Uw) %"v290"
    => ret %"v291" };
  ir_blk{ @"L169":
    %"v294" : W = Add %"pr.10", #1
    => goto poll "L56" };
  ir_blk{ @"L58":
    => ret #18446744073709551615 };
  ir_blk{ @"L47":
    %"v302" : W = (Cmp Eq W) %"v31", #73
    => br %"v302" ? "L303" : "L304" };
  ir_blk{ @"L303":
    %"v307" : W = (Cmp Eq W) %"pr.6", #9
    => goto "L304" };
  ir_blk{ @"L304" [%"v309" : W = phi("L47" => #0, "L303" => %"v307")]:
    => br %"v309" ? "L298" : "L300" };
  ir_blk{ @"L298":
    %"v312" = %"v8" +p #8;
    %"chk29" : A = (Check 0 4 Read 1) %"v312";
    %"v313" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v316" = %"v8" +p #12;
    %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk29", %"v316";
    %"v317" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v322" : W = (Cmp Eq W) %"v313", #15
    => br %"v322" ? "L323" : "L324" };
  ir_blk{ @"L323":
    %"v326" : W = (Cmp Eq W) %"v317", #6
    => goto "L324" };
  ir_blk{ @"L324" [%"v328" : W = phi("L298" => #0, "L323" => %"v326")]:
    => br %"v328" ? "L318" : "L300" };
  ir_blk{ @"L318":
    %"v330" : W = Sub %"pr.1", #194;
    %"v331" : W = Add %"v330", #191
    => goto "L300" };
  ir_blk{ @"L300" [%"pr.7" : W = phi("L318" => #6, "L324" => %"pr.6", "L304" => %"pr.6"); %"pr.2" : W = phi("L318" => %"v331", "L324" => %"pr.1", "L304" => %"pr.1")]:
    %"v336" : W = (Ext Ub) %"v31";
    %"chk31" : A = (Check 0 1 Write 1) %"v334";
    store Wb [%"chk31" + 0] <- %"v336";
    %"v337" : P = Copy $"glibc_libc_start#intel_02_known";
    %"v339" : P = Copy $"glibc_libc_start#intel_02_known_compare"
    => goto "iw_1.L12" };
  ir_blk{ @"iw_1.L12" [%"iw_1.pr.3" : L = phi("iw_1.L36" => %"iw_1.v45", "L300" => #68); %"iw_1.pr.1" : P = phi("iw_1.L36" => %"iw_1.pr.2", "L300" => %"v337")]:
    %"iw_1.v16" : W = (Cmp Ne L) %"iw_1.pr.3", #0
    => br %"iw_1.v16" ? "iw_1.L13" : "iw_1.join" };
  ir_blk{ @"iw_1.L13":
    %"iw_1.v19" : L = Shr %"iw_1.pr.3", #1;
    %"iw_1.v21" : L = Shl %"iw_1.v19", #3;
    %"iw_1.v22" = %"iw_1.pr.1" +p %"iw_1.v21";
    %"chk32" : F = CheckFunction %"v339";
    rawcall %"iw_1.v26" : W = %"chk32"(P %"v334", P %"iw_1.v22");
    %"iw_1.v31" : W = (Cmp Eq W) %"iw_1.v26", #0
    => br %"iw_1.v31" ? "iw_1.join" : "iw_1.L29" };
  ir_blk{ @"iw_1.L29":
    %"iw_1.v38" : W = (Cmp Sgt W) %"iw_1.v26", #0
    => br %"iw_1.v38" ? "iw_1.L34" : "iw_1.L36" };
  ir_blk{ @"iw_1.L34":
    %"iw_1.v41" = %"iw_1.v22" +p #8;
    %"iw_1.v43" : L = Sub %"iw_1.pr.3", #1
    => goto "iw_1.L36" };
  ir_blk{ @"iw_1.L36" [%"iw_1.pr.4" : L = phi("iw_1.L34" => %"iw_1.v43", "iw_1.L29" => %"iw_1.pr.3"); %"iw_1.pr.2" : P = phi("iw_1.L34" => %"iw_1.v41", "iw_1.L29" => %"iw_1.pr.1")]:
    %"iw_1.v45" : L = Shr %"iw_1.pr.4", #1
    => goto poll "iw_1.L12" };
  ir_blk{ @"iw_1.join" [%"v340" : P = phi("iw_1.L13" => %"iw_1.v22", "iw_1.L12" => #0)]:
    %"v345" : L = Ptoi %"v340";
    %"v346" : L = Ptoi #0;
    %"v347" : W = (Cmp Ne L) %"v345", %"v346"
    => br %"v347" ? "L341" : "L34" };
  ir_blk{ @"L341":
    %"v352" = %"v340" +p #3;
    %"chk33" : A = (Check 0 1 Read 1) %"v352";
    %"v353" : W = (RawLoad (LdNarrow Ub) 0) %"chk33";
    %"v355" : W = (Cmp Eq W) %"v353", %"pr.7"
    => br %"v355" ? "L348" : "L350" };
  ir_blk{ @"L348":
    %"v358" : W = Sub %"pr.2", #185;
    %"v360" : W = Sub %"v358", %"pr.7";
    %"v365" : W = (Cmp Eq W) %"v360", #0
    => br %"v365" ? "L361" : "L363" };
  ir_blk{ @"L361":
    %"v367" = %"v340" +p #4;
    %"chk34" : A = (HalfCheck Upper 0 4 Read 1) %"chk33", %"v367";
    %"v368" : W = (RawLoad (LdNarrow Uw) 0) %"chk34";
    %"v369" : L = (Ext Uw) %"v368"
    => ret %"v369" };
  ir_blk{ @"L363":
    %"v375" : W = (Cmp Eq W) %"v360", #1
    => br %"v375" ? "L371" : "L373" };
  ir_blk{ @"L371":
    %"v377" = %"v340" +p #1;
    %"chk35" : A = (HalfCheck Lower 0 1 Read 1) %"chk33", %"v377";
    %"v378" : W = (RawLoad (LdNarrow Ub) 0) %"chk35";
    %"v379" : L = (Ext Uw) %"v378"
    => ret %"v379" };
  ir_blk{ @"L373":
    %"v385" : W = (Cmp Eq W) %"v360", #2
    => br %"v385" ? "L383" : "L382" };
  ir_blk{ @"L382":
    %"v386" : P = Copy $"glibc_libc_start#str.301";
    %"v387" : P = Copy $"glibc_libc_start#str.302";
    %"v388" : P = Copy $"glibc_libc_start#str.303";
    call void $"__libc_assert_fail"(P %"v386", P %"v387", W #266, P %"v388")
    => goto "L383" };
  ir_blk{ @"L383":
    %"v390" = %"v340" +p #2;
    %"chk36" : A = (HalfCheck Lower 0 1 Read 1) %"chk33", %"v390";
    %"v391" : W = (RawLoad (LdNarrow Ub) 0) %"chk36";
    %"v392" : L = (Ext Uw) %"v391"
    => ret %"v392" };
  ir_blk{ @"L350":
    %"v398" = %"v340" +p #3;
    %"v399" : W = (RawLoad (LdNarrow Ub) 0) %"chk33";
    %"v401" : W = (Cmp Eq W) %"v399", #6
    => br %"v401" ? "L394" : "L34" };
  ir_blk{ @"L394":
    %"chk38" : A = (Check 0 1 Write 1) %"v4";
    store Wb [%"chk38" + 0] <- #1
    => goto "L34" };
  ir_blk{ @"L34" [%"pr.9" : W = phi("L32" => %"pr.6", "L394" => %"pr.7", "L350" => %"pr.7", "iw_1.join" => %"pr.7"); %"pr.4" : W = phi("L32" => %"pr.1", "L394" => %"pr.2", "L350" => %"pr.2", "iw_1.join" => %"pr.2")]:
    %"v405" : W = Shr %"pr.5", #8
    => goto poll "L24" };
  ir_blk{ @"L26":
    => ret #0 }])) }.

Definition hello_image_fn_glibc_libc_start'23init_cpu_features : func :=
  ir_fn{ "local" "glibc_libc_start#init_cpu_features"(P %"v0") -> RVoid blocks (hello_image_fn_glibc_libc_start'23init_cpu_features'blocks1 ++ hello_image_fn_glibc_libc_start'23init_cpu_features'blocks2) }.

Definition hello_image_fn_glibc_libc_start'23internal_signal_block_all : func :=
  ir_fn{ "local" "glibc_libc_start#internal_signal_block_all"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_libc_start#sigall_set";
    call %"v4" : W = $"zsys_sigprocmask"(W #0, P %"v2", P %"v0")
    => ret void
} }.

Definition hello_image_fn_glibc_init_first'23_init_first : func :=
  ir_fn{ "local" "glibc_init_first#_init_first"(W %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v6" : P = Copy $"__libc_argc";
    %"chk0" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk0" + 0] <- %"v0";
    %"v8" : P = Copy $"__libc_argv";
    %"chk1" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk1" + 0] <- %"v2";
    %"v10" : P = Copy $"__environ";
    %"chk2" : A = (Check 0 8 Write 8) %"v10";
    store.ptr [%"chk2" + 0] <- %"v4";
    call void $"__init_misc"(W %"v0", P %"v2", P %"v4")
    => ret void
} }.
