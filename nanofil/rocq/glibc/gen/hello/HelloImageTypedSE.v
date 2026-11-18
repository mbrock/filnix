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

Definition hello_image_fn_set_program_name : func :=
  ir_fn{ "export" "set_program_name"(P %"v0") -> RVoid {
  @"start":
    call %"v4" : P = $"strrchr"(P %"v0", W #47);
    %"v10" : L = Ptoi %"v4";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L6" : "L8";
  @"L6":
    %"v13" = %"v4" +p #1
    => goto "L8";
  @"L8" [%"v15" : P = phi("L6" => %"v13", "start" => %"v0")]:
    %"v21" : L = Ptoi %"v15";
    %"v22" : L = Ptoi %"v0";
    %"v23" : L = Sub %"v21", %"v22";
    %"v24" : W = (Cmp Sge L) %"v23", #7
    => br %"v24" ? "L25" : "L26";
  @"L25":
    (Flight (a "v28") Sub [(FAddress (t "v15")); (FValue (Const 7))] (LowerOf (t "v15")));
    %"v29" : P = Copy $"progname#str.3";
    call %"v30" : W = $"memeq"(P %"v28", P %"v29", L #7);
    %"v31" : W = (Ext Ub) %"v30";
    %"v32" : W = (Cmp Ne W) %"v31", #0
    => goto "L26";
  @"L26" [%"v33" : W = phi("L8" => #0, "L25" => %"v32")]:
    => br %"v33" ? "L16" : "L18";
  @"L16":
    %"v39" : P = Copy $"progname#str.4";
    call %"v40" : W = $"strncmp"(P %"v15", P %"v39", L #3);
    %"v41" : W = (Cmp Eq W) %"v40", #0
    => br %"v41" ? "L35" : "L18";
  @"L35":
    %"v43" = %"v15" +p #3
    => goto "L18";
  @"L18" [%"pr.3" : P = phi("L35" => %"v43", "L16" => %"v15", "L26" => %"v15"); %"pr.1" : P = phi("L35" => %"v43", "L16" => %"v15", "L26" => %"v0")]:
    %"v45" : P = Copy $"program_name";
    %"chk0" : A = (Check 0 8 Write 8) %"v45";
    store.ptr [%"chk0" + 0] <- %"pr.1";
    %"v47" : P = Copy $"program_invocation_name";
    %"chk1" : A = (Check 0 8 Write 8) %"v47";
    store.ptr [%"chk1" + 0] <- %"pr.1";
    %"v49" : P = Copy $"program_invocation_short_name";
    %"chk2" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk2" + 0] <- %"pr.3"
    => ret void
} }.

Definition hello_image_fn_set_char_quoting : func :=
  ir_fn{ "export" "set_char_quoting"(P %"v0", W %"v2", W %"v4") -> (RClass W) {
  @"start":
    %"v7" : W = (Ext Sb) %"v2";
    %"v8" : W = (Ext Ub) %"v7";
    %"v14" : L = Ptoi %"v0";
    %"v15" : W = (Cmp Ne L) %"v14", #0
    => br %"v15" ? "L12" : "L11";
  @"L11":
    %"v17" : P = Copy $"quotearg#default_quoting_options"
    => goto "L12";
  @"L12" [%"v18" : P = phi("L11" => %"v17", "start" => %"v0")]:
    %"v19" = %"v18" +p #8;
    %"v22" : L = (Ext Uw) %"v8";
    %"v23" : L = Shr %"v22", #5;
    %"v24" : L = Shl %"v23", #2;
    %"v25" = %"v19" +p %"v24";
    %"v30" : L = And %"v22", #31;
    %"chk0" : A = (Check 0 4 Read 1) %"v25";
    %"v33" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v34" : W = Copy %"v30";
    %"v35" : W = Shr %"v33", %"v34";
    %"v36" : W = And %"v35", #1;
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v40" : W = And %"v4", #1;
    %"v42" : W = Xor %"v40", %"v36";
    %"v43" : W = Copy %"v30";
    %"v44" : W = Shl %"v42", %"v43";
    %"v45" : W = Xor %"v38", %"v44";
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v25";
    store Ww [%"chk2" + 0] <- %"v45"
    => ret %"v36"
} }.

Definition hello_image_fn_setlocale_null_unlocked : func :=
  ir_fn{ "export" "setlocale_null_unlocked"(W %"v0") -> (RClass P) {
  @"start":
    call %"v4" : P = $"setlocale"(W %"v0", P #0)
    => ret %"v4"
} }.

Definition hello_image_fn_setlocale_null_r_unlocked : func :=
  ir_fn{ "export" "setlocale_null_r_unlocked"(W %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    call %"v8" : P = $"setlocale_null_unlocked"(W %"v0");
    %"v13" : L = Ptoi %"v8";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L9" : "L10";
  @"L9":
    %"v20" : W = (Cmp Ugt L) %"v4", #0
    => br %"v20" ? "L16" : "L18";
  @"L16":
    %"chk0" : A = (Check 0 1 Write 1) %"v2";
    store Wb [%"chk0" + 0] <- #0
    => goto "L18";
  @"L18":
    => ret #22;
  @"L10":
    call %"v26" : L = $"strlen"(P %"v8");
    %"v32" : W = (Cmp Ult L) %"v26", %"v4"
    => br %"v32" ? "L27" : "L28";
  @"L27":
    %"v36" : L = Add %"v26", #1;
    call %"v37" : P = $"memcpy"(P %"v2", P %"v8", L %"v36")
    => ret #0;
  @"L28":
    %"v43" : W = (Cmp Ugt L) %"v4", #0
    => br %"v43" ? "L39" : "L41";
  @"L39":
    %"v47" : L = Sub %"v4", #1;
    call %"v48" : P = $"memcpy"(P %"v2", P %"v8", L %"v47");
    %"v52" = %"v2" +p %"v47";
    %"chk1" : A = (Check 0 1 Write 1) %"v52";
    store Wb [%"chk1" + 0] <- #0
    => goto "L41";
  @"L41":
    => ret #34
} }.

Definition hello_image_fn_setlocale_null_r : func :=
  ir_fn{ "export" "setlocale_null_r"(W %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    call %"v9" : W = $"setlocale_null_r_unlocked"(W %"v0", P %"v2", L %"v4")
    => ret %"v9"
} }.

Definition hello_image_fn___GI_setlocale : func :=
  ir_fn{ "export" "__GI_setlocale"(W %"v0", P %"v2") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v4" : P = (Alloc 8) #8;
    %"v5" : P = (Alloc 8) #8;
    %"v103" : P = (Alloc 8) #104;
    %"v104" : P = (Alloc 8) #104;
    %"v482" : P = (Alloc 8) #8;
    %"v12" : L = (Ext Sw) %"v0";
    %"v13" : W = (Cmp Slt L) %"v12", #0
    => br %"v13" ? "L15" : "L14" };
  ir_blk{ @"L14":
    %"v18" : W = (Cmp Sge L) %"v12", #13
    => goto "L15" };
  ir_blk{ @"L15" [%"v20" : W = phi("start" => #1, "L14" => %"v18")]:
    => br %"v20" ? "L21" : "L10" };
  ir_blk{ @"L21":
    %"v24" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v24";
    store Ww [%"chk0" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L10":
    %"v29" : L = Ptoi %"v2";
    %"v30" : L = Ptoi #0;
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => br %"v31" ? "L25" : "L27" };
  ir_blk{ @"L25":
    %"v32" : P = Copy $"_nl_global_locale";
    %"v33" = %"v32" +p #128;
    %"v36" : L = Shl %"v12", #3;
    %"v37" = %"v33" +p %"v36";
    %"chk1" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => ret %"v38" };
  ir_blk{ @"L27":
    %"v40" : P = Copy $"__libc_setlocale_lock";
    call %"v41" : W = $"__GI___pthread_rwlock_wrlock"(P %"v40");
    %"v46" : P = Copy $"_nl_global_locale";
    %"v47" = %"v46" +p #128;
    %"v50" : L = Shl %"v12", #3;
    %"v51" = %"v47" +p %"v50";
    %"chk2" : A = (Check 0 8 Read 8) %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call %"v53" : W = $"__GI_strcmp"(P %"v2", P %"v52");
    %"v54" : W = (Cmp Eq W) %"v53", #0
    => br %"v54" ? "L42" : "L44" };
  ir_blk{ @"L42":
    %"v55" : P = Copy $"__libc_setlocale_lock";
    call %"v56" : W = $"__GI___pthread_rwlock_unlock"(P %"v55");
    %"v57" : P = Copy $"_nl_global_locale";
    %"v58" = %"v57" +p #128;
    %"v62" = %"v58" +p %"v50";
    %"chk3" : A = (Check 0 8 Read 8) %"v62";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk3"
    => ret %"v63" };
  ir_blk{ @"L44":
    %"chk4" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk4" + 0] <- #0;
    %"chk5" : A = (Check 0 8 Write 1) %"v5";
    store Wl [%"chk5" + 0] <- #0;
    %"v65" : P = Copy $"glibc_setlocale#str.234";
    call %"v66" : P = $"__GI_getenv"(P %"v65");
    %"v71" : L = Ptoi %"v66";
    %"v73" : W = (Cmp Ne L) %"v71", %"v30"
    => br %"v73" ? "L74" : "L75" };
  ir_blk{ @"L74":
    %"chk6" : A = (Check 0 1 Read 1) %"v66";
    %"v78" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v79" : W = (Cmp Ne W) %"v78", #0
    => goto "L75" };
  ir_blk{ @"L75" [%"v81" : W = phi("L44" => #0, "L74" => %"v79")]:
    => br %"v81" ? "L67" : "L69" };
  ir_blk{ @"L67":
    call %"v86" : W = $"__argz_create_sep"(P %"v66", W #58, P %"v4", P %"v5");
    %"v87" : W = (Cmp Ne W) %"v86", #0
    => br %"v87" ? "L89" : "L88" };
  ir_blk{ @"L88":
    %"v90" : P = Copy $"_nl_default_locale_path";
    call %"v91" : W = $"__argz_add_sep"(P %"v4", P %"v5", P %"v90", W #58);
    %"v92" : W = (Cmp Ne W) %"v91", #0
    => goto "L89" };
  ir_blk{ @"L89" [%"v94" : W = phi("L67" => #1, "L88" => %"v92")]:
    => br %"v94" ? "L82" : "L69" };
  ir_blk{ @"L82":
    %"v95" : P = Copy $"__libc_setlocale_lock";
    call %"v96" : W = $"__GI___pthread_rwlock_unlock"(P %"v95")
    => ret #0 };
  ir_blk{ @"L69":
    %"v102" : W = (Cmp Eq W) %"v0", #6
    => br %"v102" ? "L106" : "L99" };
  ir_blk{ @"L106" [%"pr.1" : W = phi("L108" => %"v123", "L69" => #0)]:
    %"v111" : W = (Cmp Slt W) %"pr.1", #13
    => br %"v111" ? "L107" : "L109" };
  ir_blk{ @"L107":
    %"v116" : W = (Cmp Ne W) %"pr.1", #6
    => br %"v116" ? "L112" : "L108" };
  ir_blk{ @"L112":
    %"v118" : L = (Ext Sw) %"pr.1";
    %"v119" : L = Shl %"v118", #3;
    %"v120" = %"v103" +p %"v119";
    %"chk7" : A = (Check 0 8 Write 8) %"v120";
    store.ptr [%"chk7" + 0] <- %"v2"
    => goto "L108" };
  ir_blk{ @"L108":
    %"v123" : W = Add %"pr.1", #1
    => goto poll "L106" };
  ir_blk{ @"L109":
    call %"v128" : P = $"__GI_strchr"(P %"v2", W #59);
    %"v129" : L = Ptoi %"v128";
    %"v131" : W = (Cmp Ne L) %"v129", %"v30"
    => br %"v131" ? "L124" : "L126" };
  ir_blk{ @"L124":
    call %"v135" : P = $"__GI___strdup"(P %"v2");
    %"v140" : L = Ptoi %"v135";
    %"v142" : W = (Cmp Eq L) %"v140", %"v30"
    => br %"v142" ? "L136" : "L152" };
  ir_blk{ @"L136":
    %"v145" : P = Copy $"__libc_setlocale_lock";
    call %"v146" : W = $"__GI___pthread_rwlock_unlock"(P %"v145")
    => ret #0 };
  ir_blk{ @"L152" [%"pr.6" : P = phi("L124" => %"v135", "L225" => %"v234")]:
    call %"v156" : P = $"__GI_strchr"(P %"pr.6", W #61);
    %"v157" : L = Ptoi %"v156";
    %"v159" : W = (Cmp Ne L) %"v157", %"v30"
    => br %"v159" ? "L160" : "L235" };
  ir_blk{ @"L160" [%"pr.7" : W = phi("L162" => %"v203", "L152" => #0)]:
    %"v165" : W = (Cmp Slt W) %"pr.7", #13
    => br %"v165" ? "L161" : "L163" };
  ir_blk{ @"L161":
    %"v170" : W = (Cmp Ne W) %"pr.7", #6
    => br %"v170" ? "L171" : "L172" };
  ir_blk{ @"L171":
    %"v176" : L = Ptoi %"pr.6";
    %"v177" : L = Sub %"v157", %"v176";
    %"v178" : P = Copy $"_nl_category_name_sizes";
    %"v180" : L = (Ext Sw) %"pr.7";
    %"v181" = %"v178" +p %"v180";
    %"chk8" : A = (Check 0 1 Read 1) %"v181";
    %"v182" : W = (RawLoad (LdNarrow Ub) 0) %"chk8";
    %"v183" : L = (Ext Uw) %"v182";
    %"v184" : W = (Cmp Eq L) %"v177", %"v183"
    => goto "L172" };
  ir_blk{ @"L172" [%"v186" : W = phi("L161" => #0, "L171" => %"v184")]:
    => br %"v186" ? "iw_1.start" : "L188" };
  ir_blk{ @"iw_1.start":
    %"iw_1.v2" : P = Copy $"_nl_category_names";
    %"iw_1.v3" : P = Copy $"_nl_category_name_idxs";
    %"iw_1.v5" : L = (Ext Sw) %"pr.7";
    %"iw_1.v6" = %"iw_1.v3" +p %"iw_1.v5";
    %"chk9" : A = (Check 0 1 Read 1) %"iw_1.v6";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"iw_1.v8" : L = (Ext Uw) %"iw_1.v7";
    %"iw_1.v9" = %"iw_1.v2" +p %"iw_1.v8";
    %"v195" : L = Ptoi %"pr.6";
    %"v196" : L = Sub %"v157", %"v195";
    call %"v197" : W = $"__GI_memcmp"(P %"pr.6", P %"iw_1.v9", L %"v196");
    %"v198" : W = (Cmp Eq W) %"v197", #0
    => goto "L188" };
  ir_blk{ @"L188" [%"v200" : W = phi("L172" => #0, "iw_1.start" => %"v198")]:
    => br %"v200" ? "L163" : "L162" };
  ir_blk{ @"L162":
    %"v203" : W = Add %"pr.7", #1
    => goto poll "L160" };
  ir_blk{ @"L163":
    %"v208" : W = (Cmp Eq W) %"pr.7", #13
    => br %"v208" ? "L209" : "L206" };
  ir_blk{ @"L209":
    %"v210" : P = Copy $"__libc_setlocale_lock";
    call %"v211" : W = $"__GI___pthread_rwlock_unlock"(P %"v210");
    call void $"free"(P %"v135");
    %"v216" : P = Copy $"__libc_errno";
    %"chk10" : A = (Check 0 4 Write 1) %"v216";
    store Ww [%"chk10" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L206":
    %"v218" : L = (Ext Sw) %"pr.7";
    %"v219" : L = Shl %"v218", #3;
    %"v220" = %"v103" +p %"v219";
    %"v222" = %"v156" +p #1;
    %"chk11" : A = (Check 0 8 Write 8) %"v220";
    store.ptr [%"chk11" + 0] <- %"v222";
    call %"v224" : P = $"__GI_strchr"(P %"v222", W #59);
    %"v229" : L = Ptoi %"v224";
    %"v231" : W = (Cmp Ne L) %"v229", %"v30"
    => br %"v231" ? "L225" : "L235" };
  ir_blk{ @"L225":
    %"chk12" : A = (Check 0 1 Write 1) %"v224";
    store Wb [%"chk12" + 0] <- #0;
    %"v234" = %"v224" +p #1
    => goto poll "L152" };
  ir_blk{ @"L235" [%"pr.8" : W = phi("L237" => %"v261", "L152" => #0, "L206" => #0)]:
    %"v240" : W = (Cmp Slt W) %"pr.8", #13
    => br %"v240" ? "L236" : "L126" };
  ir_blk{ @"L236":
    %"v245" : W = (Cmp Ne W) %"pr.8", #6
    => br %"v245" ? "L246" : "L247" };
  ir_blk{ @"L246":
    %"v249" : L = (Ext Sw) %"pr.8";
    %"v250" : L = Shl %"v249", #3;
    %"v251" = %"v103" +p %"v250";
    %"chk13" : A = (Check 0 8 Read 8) %"v251";
    %"v252" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v254" : L = Ptoi %"v252";
    %"v256" : W = (Cmp Eq L) %"v254", %"v29"
    => goto "L247" };
  ir_blk{ @"L247" [%"v258" : W = phi("L236" => #0, "L246" => %"v256")]:
    => br %"v258" ? poll "L209" : "L237" };
  ir_blk{ @"L237":
    %"v261" : W = Add %"pr.8", #1
    => goto poll "L235" };
  ir_blk{ @"L126" [%"pr.5" : P = phi("L235" => %"v135", "L109" => #0)]:
    => goto "L262" };
  ir_blk{ @"L262" [%"pr.2" : W = phi("L126" => %"pr.1", "L330" => %"v266", "L331" => %"v266", "L299" => %"v266", "L263" => %"v266")]:
    %"v266" : W = Sub %"pr.2", #1;
    %"v267" : W = (Cmp Sgt W) %"pr.2", #0
    => br %"v267" ? "L263" : "L264" };
  ir_blk{ @"L263":
    %"v272" : W = (Cmp Ne W) %"v266", #6
    => br %"v272" ? "L268" : poll "L262" };
  ir_blk{ @"L268":
    %"v274" : L = (Ext Sw) %"v266";
    %"v275" : L = Shl %"v274", #3;
    %"v276" = %"v104" +p %"v275";
    %"chk14" : A = (Renew 0 8 Read 8) %"chk4", %"v4";
    %"v277" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Renew 0 8 Read 1) %"chk5", %"v5";
    %"v278" : L = (RawLoad LdL 0) %"chk15";
    %"v283" = %"v103" +p %"v275";
    call %"v284" : P = $"_nl_find_locale"(P %"v277", L %"v278", W %"v266", P %"v283");
    %"chk16" : A = (Check 0 8 Write 8) %"v276";
    store.ptr [%"chk16" + 0] <- %"v284";
    %"chk17" : A = (Renew 0 8 Read 8) %"chk16", %"v276";
    %"v292" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v293" : L = Ptoi %"v292";
    %"v295" : W = (Cmp Eq L) %"v293", %"v30"
    => br %"v295" ? "L264" : "L287" };
  ir_blk{ @"L287":
    %"v304" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v305" = %"v304" +p #40;
    %"chk19" : A = (Check 0 4 Read 1) %"v305";
    %"v306" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v309" : W = (Cmp Ne W) %"v306", #4294967295
    => br %"v309" ? "L297" : "L299" };
  ir_blk{ @"L297":
    %"v314" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v315" = %"v314" +p #40;
    %"chk21" : A = (Check 0 4 Write 1) %"v315";
    store Ww [%"chk21" + 0] <- #4294967295
    => goto "L299" };
  ir_blk{ @"L299":
    %"chk22" : A = (Check 0 8 Read 8) %"v283";
    %"v325" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v326" : P = Copy $"_nl_C_name";
    %"v327" : L = Ptoi %"v325";
    %"v328" : L = Ptoi %"v326";
    %"v329" : W = (Cmp Ne L) %"v327", %"v328"
    => br %"v329" ? "L318" : poll "L262" };
  ir_blk{ @"L318":
    %"chk23" : A = (Renew 0 8 Read 8) %"chk22", %"v283";
    %"v337" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v338" : P = Copy $"_nl_global_locale";
    %"v339" = %"v338" +p #128;
    %"v343" = %"v339" +p %"v275";
    %"chk24" : A = (Check 0 8 Read 8) %"v343";
    %"v344" : P = (RawLoadPointer 0 load_effects) %"chk24";
    call %"v345" : W = $"__GI_strcmp"(P %"v337", P %"v344");
    %"v346" : W = (Cmp Eq W) %"v345", #0
    => br %"v346" ? "L330" : "L331" };
  ir_blk{ @"L330":
    %"v351" : P = Copy $"_nl_global_locale";
    %"v352" = %"v351" +p #128;
    %"v356" = %"v352" +p %"v275";
    %"chk25" : A = (Check 0 8 Read 8) %"v356";
    %"v357" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : A = (Renew 0 8 Write 8) %"chk22", %"v283";
    store.ptr [%"chk26" + 0] <- %"v357"
    => goto poll "L262" };
  ir_blk{ @"L331":
    %"chk27" : A = (Renew 0 8 Read 8) %"chk22", %"v283";
    %"v366" : P = (RawLoadPointer 0 load_effects) %"chk27";
    call %"v367" : P = $"__GI___strdup"(P %"v366");
    %"chk28" : A = (Renew 0 8 Write 8) %"chk22", %"v283";
    store.ptr [%"chk28" + 0] <- %"v367";
    %"chk29" : A = (Renew 0 8 Read 8) %"chk22", %"v283";
    %"v375" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v376" : L = Ptoi %"v375";
    %"v378" : W = (Cmp Eq L) %"v376", %"v30"
    => br %"v378" ? "L264" : poll "L262" };
  ir_blk{ @"L264":
    %"v384" : W = (Cmp Sge W) %"v266", #0
    => br %"v384" ? "L382" : "iw_2.L10" };
  ir_blk{ @"iw_2.L10" [%"iw_2.pr.9" : W = phi("iw_2.L18" => %"iw_2.pr.10", "L264" => #1); %"iw_2.pr.5" : W = phi("iw_2.L18" => %"iw_2.v91", "L264" => #0); %"iw_2.pr.3" : L = phi("iw_2.L18" => %"iw_2.pr.4", "L264" => #0); %"iw_2.pr.1" : L = phi("iw_2.L18" => %"iw_2.pr.2", "L264" => #0)]:
    %"iw_2.v15" : W = (Cmp Slt W) %"iw_2.pr.5", #13
    => br %"iw_2.v15" ? "iw_2.L11" : "iw_2.L13" };
  ir_blk{ @"iw_2.L11":
    %"iw_2.v20" : W = (Cmp Ne W) %"iw_2.pr.5", #6
    => br %"iw_2.v20" ? "iw_2.L22" : "iw_2.L18" };
  ir_blk{ @"iw_2.L22":
    %"iw_2.v29" : L = (Ext Sw) %"iw_2.pr.5";
    %"iw_2.v30" : L = Shl %"iw_2.v29", #3;
    %"iw_2.v31" = %"v103" +p %"iw_2.v30";
    %"chk30" : A = (Check 0 8 Read 8) %"iw_2.v31";
    %"iw_2.v32" : P = (RawLoadPointer 0 load_effects) %"chk30";
    call %"iw_2.v52" : L = $"__GI_strlen"(P %"iw_2.v32");
    %"iw_2.v54" : P = Copy $"_nl_category_name_sizes";
    %"iw_2.v57" = %"iw_2.v54" +p %"iw_2.v29";
    %"chk31" : A = (Check 0 1 Read 1) %"iw_2.v57";
    %"iw_2.v58" : W = (RawLoad (LdNarrow Ub) 0) %"chk31";
    %"iw_2.v59" : W = Add %"iw_2.v58", #1;
    %"iw_2.v61" : L = (Ext Sw) %"iw_2.v59";
    %"iw_2.v62" : L = Add %"iw_2.v61", %"iw_2.v52";
    %"iw_2.v63" : L = Add %"iw_2.v62", #1;
    %"iw_2.v64" : L = Add %"iw_2.pr.3", %"iw_2.v63"
    => br %"iw_2.pr.9" ? "iw_2.L69" : "iw_2.L70" };
  ir_blk{ @"iw_2.L69":
    %"chk32" : A = (Check 0 8 Read 8) %"v103";
    %"iw_2.v74" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"iw_2.v75" : L = Ptoi %"iw_2.v32";
    %"iw_2.v76" : L = Ptoi %"iw_2.v74";
    %"iw_2.v77" : W = (Cmp Ne L) %"iw_2.v75", %"iw_2.v76"
    => goto "iw_2.L70" };
  ir_blk{ @"iw_2.L70" [%"iw_2.v79" : W = phi("iw_2.L22" => #0, "iw_2.L69" => %"iw_2.v77")]:
    => br %"iw_2.v79" ? "iw_2.L80" : "iw_2.L81" };
  ir_blk{ @"iw_2.L80":
    %"chk33" : A = (Check 0 8 Read 8) %"v103";
    %"iw_2.v85" : P = (RawLoadPointer 0 load_effects) %"chk33";
    call %"iw_2.v86" : W = $"__GI_strcmp"(P %"iw_2.v32", P %"iw_2.v85");
    %"iw_2.v87" : W = (Cmp Ne W) %"iw_2.v86", #0
    => goto "iw_2.L81" };
  ir_blk{ @"iw_2.L81" [%"iw_2.v89" : W = phi("iw_2.L70" => #0, "iw_2.L80" => %"iw_2.v87")]:
    => br %"iw_2.v89" ? "iw_2.L18" : "iw_2.L66" };
  ir_blk{ @"iw_2.L66":
    => goto "iw_2.L18" }] [ir_blk{ @"iw_2.L18" [%"iw_2.pr.10" : W = phi("iw_2.L66" => %"iw_2.pr.9", "iw_2.L81" => #0, "iw_2.L11" => %"iw_2.pr.9"); %"iw_2.pr.4" : L = phi("iw_2.L66" => %"iw_2.v64", "iw_2.L81" => %"iw_2.v64", "iw_2.L11" => %"iw_2.pr.3"); %"iw_2.pr.2" : L = phi("iw_2.L66" => %"iw_2.v52", "iw_2.L81" => %"iw_2.v52", "iw_2.L11" => %"iw_2.pr.1")]:
    %"iw_2.v91" : W = Add %"iw_2.pr.5", #1
    => goto poll "iw_2.L10" };
  ir_blk{ @"iw_2.L13":
    => br %"iw_2.pr.9" ? "iw_2.L92" : "iw_2.L94" };
  ir_blk{ @"iw_2.L92":
    %"chk34" : A = (Check 0 8 Read 8) %"v103";
    %"iw_2.v101" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_2.v102" : P = Copy $"_nl_C_name";
    call %"iw_2.v103" : W = $"__GI_strcmp"(P %"iw_2.v101", P %"iw_2.v102");
    %"iw_2.v104" : W = (Cmp Eq W) %"iw_2.v103", #0
    => br %"iw_2.v104" ? "iw_2.L106" : "iw_2.L105" };
  ir_blk{ @"iw_2.L105":
    %"chk35" : A = (Renew 0 8 Read 8) %"chk34", %"v103";
    %"iw_2.v109" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"iw_2.v110" : P = Copy $"_nl_POSIX_name";
    call %"iw_2.v111" : W = $"__GI_strcmp"(P %"iw_2.v109", P %"iw_2.v110");
    %"iw_2.v112" : W = (Cmp Eq W) %"iw_2.v111", #0
    => goto "iw_2.L106" };
  ir_blk{ @"iw_2.L106" [%"iw_2.v114" : W = phi("iw_2.L92" => #1, "iw_2.L105" => %"iw_2.v112")]:
    => br %"iw_2.v114" ? "iw_2.L96" : "iw_2.L98" };
  ir_blk{ @"iw_2.L96":
    %"iw_2.v115" : P = Copy $"_nl_C_name"
    => goto "L382" };
  ir_blk{ @"iw_2.L98":
    %"iw_2.v118" : L = Add %"iw_2.pr.1", #1;
    call %"iw_2.v119" : P = $"malloc"(L %"iw_2.v118");
    %"iw_2.v124" : L = Ptoi %"iw_2.v119";
    %"iw_2.v126" : W = (Cmp Eq L) %"iw_2.v124", %"v30"
    => br %"iw_2.v126" ? "L382" : "iw_2.L121" };
  ir_blk{ @"iw_2.L121":
    %"chk36" : A = (Renew 0 8 Read 8) %"chk34", %"v103";
    %"iw_2.v130" : P = (RawLoadPointer 0 load_effects) %"chk36";
    call %"iw_2.v133" : P = $"__GI_memcpy"(P %"iw_2.v119", P %"iw_2.v130", L %"iw_2.v118")
    => goto "L382" };
  ir_blk{ @"iw_2.L94":
    call %"iw_2.v137" : P = $"malloc"(L %"iw_2.pr.3");
    %"iw_2.v142" : L = Ptoi %"iw_2.v137";
    %"iw_2.v144" : W = (Cmp Eq L) %"iw_2.v142", %"v30"
    => br %"iw_2.v144" ? "L382" : "iw_2.L147" };
  ir_blk{ @"iw_2.L147" [%"iw_2.pr.7" : P = phi("iw_2.L155" => %"iw_2.pr.8", "iw_2.L94" => %"iw_2.v137"); %"iw_2.pr.6" : W = phi("iw_2.L155" => %"iw_2.v200", "iw_2.L94" => #0)]:
    %"iw_2.v152" : W = (Cmp Slt W) %"iw_2.pr.6", #13
    => br %"iw_2.v152" ? "iw_2.L148" : "iw_2.L150" };
  ir_blk{ @"iw_2.L148":
    %"iw_2.v157" : W = (Cmp Ne W) %"iw_2.pr.6", #6
    => br %"iw_2.v157" ? "iw_2.L159" : "iw_2.L155" };
  ir_blk{ @"iw_2.L159":
    %"iw_2.v166" : L = (Ext Sw) %"iw_2.pr.6";
    %"iw_2.v167" : L = Shl %"iw_2.v166", #3;
    %"iw_2.v168" = %"v103" +p %"iw_2.v167";
    %"chk37" : A = (Check 0 8 Read 8) %"iw_2.v168";
    %"iw_2.v169" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_2.iw_1.v2" : P = Copy $"_nl_category_names";
    %"iw_2.iw_1.v3" : P = Copy $"_nl_category_name_idxs";
    %"iw_2.iw_1.v6" = %"iw_2.iw_1.v3" +p %"iw_2.v166";
    %"chk38" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v6";
    %"iw_2.iw_1.v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk38";
    %"iw_2.iw_1.v8" : L = (Ext Uw) %"iw_2.iw_1.v7";
    %"iw_2.iw_1.v9" = %"iw_2.iw_1.v2" +p %"iw_2.iw_1.v8";
    call %"iw_2.v191" : P = $"__GI_stpcpy"(P %"iw_2.pr.7", P %"iw_2.iw_1.v9");
    %"iw_2.v193" = %"iw_2.v191" +p #1;
    %"chk39" : A = (Check 0 1 Write 1) %"iw_2.v191";
    store Wb [%"chk39" + 0] <- #61;
    call %"iw_2.v196" : P = $"__GI_stpcpy"(P %"iw_2.v193", P %"iw_2.v169");
    %"iw_2.v198" = %"iw_2.v196" +p #1;
    %"chk40" : A = (Check 0 1 Write 1) %"iw_2.v196";
    store Wb [%"chk40" + 0] <- #59
    => goto "iw_2.L155" };
  ir_blk{ @"iw_2.L155" [%"iw_2.pr.8" : P = phi("iw_2.L159" => %"iw_2.v198", "iw_2.L148" => %"iw_2.pr.7")]:
    %"iw_2.v200" : W = Add %"iw_2.pr.6", #1
    => goto poll "iw_2.L147" };
  ir_blk{ @"iw_2.L150":
    %"iw_2.v204" = %"iw_2.pr.7" +p #18446744073709551615;
    %"chk41" : A = (Check 0 1 Write 1) %"iw_2.v204";
    store Wb [%"chk41" + 0] <- #0
    => goto "L382" };
  ir_blk{ @"L382" [%"v386" : P = phi("L264" => #0, "iw_2.L96" => %"iw_2.v115", "iw_2.L150" => %"iw_2.v137", "iw_2.L98" => #0, "iw_2.L121" => %"iw_2.v133", "iw_2.L94" => #0)]:
    %"v391" : L = Ptoi %"v386";
    %"v393" : W = (Cmp Ne L) %"v391", %"v30"
    => br %"v393" ? "L394" : "L388" };
  ir_blk{ @"L394" [%"pr.3" : W = phi("L396" => %"v418", "L382" => #0)]:
    %"v399" : W = (Cmp Slt W) %"pr.3", #13
    => br %"v399" ? "L395" : "iw_5.start" };
  ir_blk{ @"L395":
    %"v404" : W = (Cmp Ne W) %"pr.3", #6
    => br %"v404" ? "L400" : "L396" };
  ir_blk{ @"L400":
    %"v407" : L = (Ext Sw) %"pr.3";
    %"v408" : L = Shl %"v407", #3;
    %"v409" = %"v104" +p %"v408";
    %"chk42" : A = (Check 0 8 Read 8) %"v409";
    %"v410" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"iw_3.v7" : P = Copy $"_nl_global_locale";
    %"iw_3.v11" = %"iw_3.v7" +p %"v408";
    %"chk43" : A = (Check 0 8 Write 8) %"iw_3.v11";
    store.ptr [%"chk43" + 0] <- %"v410";
    %"iw_3.v16" : P = Copy $"glibc_setlocale#_nl_category_postload";
    %"iw_3.v20" = %"iw_3.v16" +p %"v408";
    %"chk44" : A = (Check 0 8 Read 8) %"iw_3.v20";
    %"iw_3.v21" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"iw_3.v22" : L = Ptoi %"iw_3.v21";
    %"iw_3.v23" : W = (Cmp Ne L) %"iw_3.v22", #0
    => br %"iw_3.v23" ? "iw_3.L13" : "iw_3.join" };
  ir_blk{ @"iw_3.L13":
    %"iw_3.v24" : P = Copy $"glibc_setlocale#_nl_category_postload";
    %"iw_3.v28" = %"iw_3.v24" +p %"v408";
    %"chk45" : A = (Check 0 8 Read 8) %"iw_3.v28";
    %"iw_3.v29" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"chk46" : F = CheckFunction %"iw_3.v29";
    rawcall void %"chk46"()
    => goto "iw_3.join" };
  ir_blk{ @"iw_3.join":
    %"v415" = %"v103" +p %"v408";
    %"chk47" : A = (Check 0 8 Read 8) %"v415";
    %"v416" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"iw_4.v7" : P = Copy $"_nl_global_locale";
    %"iw_4.v8" = %"iw_4.v7" +p #128;
    %"iw_4.v12" = %"iw_4.v8" +p %"v408";
    %"chk48" : A = (Check 0 8 Read 8) %"iw_4.v12";
    %"iw_4.v13" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"iw_4.v15" : L = Ptoi %"iw_4.v13";
    %"iw_4.v16" : L = Ptoi %"v416";
    %"iw_4.v17" : W = (Cmp Eq L) %"iw_4.v15", %"iw_4.v16"
    => br %"iw_4.v17" ? "L396" : "iw_4.L6" };
  ir_blk{ @"iw_4.L6":
    %"iw_4.v22" : P = Copy $"_nl_global_locale";
    %"iw_4.v23" = %"iw_4.v22" +p #128;
    %"iw_4.v27" = %"iw_4.v23" +p %"v408";
    %"chk49" : A = (Check 0 8 Read 8) %"iw_4.v27";
    %"iw_4.v28" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_4.v29" : P = Copy $"_nl_C_name";
    %"iw_4.v30" : L = Ptoi %"iw_4.v28";
    %"iw_4.v31" : L = Ptoi %"iw_4.v29";
    %"iw_4.v32" : W = (Cmp Ne L) %"iw_4.v30", %"iw_4.v31"
    => br %"iw_4.v32" ? "iw_4.L19" : "iw_4.L21" };
  ir_blk{ @"iw_4.L19":
    %"iw_4.v33" : P = Copy $"_nl_global_locale";
    %"iw_4.v34" = %"iw_4.v33" +p #128;
    %"iw_4.v38" = %"iw_4.v34" +p %"v408";
    %"chk50" : A = (Check 0 8 Read 8) %"iw_4.v38";
    %"iw_4.v39" : P = (RawLoadPointer 0 load_effects) %"chk50";
    call void $"free"(P %"iw_4.v39")
    => goto "iw_4.L21" };
  ir_blk{ @"iw_4.L21":
    %"iw_4.v40" : P = Copy $"_nl_global_locale";
    %"iw_4.v41" = %"iw_4.v40" +p #128;
    %"iw_4.v45" = %"iw_4.v41" +p %"v408";
    %"chk51" : A = (Check 0 8 Write 8) %"iw_4.v45";
    store.ptr [%"chk51" + 0] <- %"v416"
    => goto "L396" };
  ir_blk{ @"L396":
    %"v418" : W = Add %"pr.3", #1
    => goto poll "L394" };
  ir_blk{ @"iw_5.start":
    %"iw_5.v7" : P = Copy $"_nl_global_locale";
    %"iw_5.v8" = %"iw_5.v7" +p #128;
    %"iw_5.v12" = %"iw_5.v8" +p #48;
    %"chk52" : A = (Check 0 8 Read 8) %"iw_5.v12";
    %"iw_5.v13" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"iw_5.v15" : L = Ptoi %"iw_5.v13";
    %"iw_5.v17" : W = (Cmp Eq L) %"iw_5.v15", %"v391"
    => br %"iw_5.v17" ? "iw_5.join" : "iw_5.L6" };
  ir_blk{ @"iw_5.L6":
    %"iw_5.v22" : P = Copy $"_nl_global_locale";
    %"iw_5.v23" = %"iw_5.v22" +p #128;
    %"iw_5.v27" = %"iw_5.v23" +p #48;
    %"chk53" : A = (Check 0 8 Read 8) %"iw_5.v27";
    %"iw_5.v28" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"iw_5.v29" : P = Copy $"_nl_C_name";
    %"iw_5.v30" : L = Ptoi %"iw_5.v28";
    %"iw_5.v31" : L = Ptoi %"iw_5.v29";
    %"iw_5.v32" : W = (Cmp Ne L) %"iw_5.v30", %"iw_5.v31"
    => br %"iw_5.v32" ? "iw_5.L19" : "iw_5.L21" };
  ir_blk{ @"iw_5.L19":
    %"iw_5.v33" : P = Copy $"_nl_global_locale";
    %"iw_5.v34" = %"iw_5.v33" +p #128;
    %"iw_5.v38" = %"iw_5.v34" +p #48;
    %"chk54" : A = (Check 0 8 Read 8) %"iw_5.v38";
    %"iw_5.v39" : P = (RawLoadPointer 0 load_effects) %"chk54";
    call void $"free"(P %"iw_5.v39")
    => goto "iw_5.L21" };
  ir_blk{ @"iw_5.L21":
    %"iw_5.v40" : P = Copy $"_nl_global_locale";
    %"iw_5.v41" = %"iw_5.v40" +p #128;
    %"iw_5.v45" = %"iw_5.v41" +p #48;
    %"chk55" : A = (Check 0 8 Write 8) %"iw_5.v45";
    store.ptr [%"chk55" + 0] <- %"v386"
    => goto "iw_5.join" };
  ir_blk{ @"iw_5.join":
    %"v420" : P = Copy $"_nl_msg_cat_cntr";
    %"chk56" : A = (Check 0 4 Read 1) %"v420";
    %"v421" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"v422" : W = Add %"v421", #1;
    %"chk57" : A = (Renew 0 4 Write 1) %"chk56", %"v420";
    store Ww [%"chk57" + 0] <- %"v422"
    => goto "L389" };
  ir_blk{ @"L388":
    %"v424" : W = Add %"v266", #1
    => goto "L425" };
  ir_blk{ @"L425" [%"pr.4" : W = phi("L388" => %"v424", "L427" => %"v474")]:
    %"v430" : W = (Cmp Slt W) %"pr.4", #13
    => br %"v430" ? "L426" : "L389" };
  ir_blk{ @"L426":
    %"v435" : W = (Cmp Ne W) %"pr.4", #6
    => br %"v435" ? "L436" : "L437" };
  ir_blk{ @"L436":
    %"v439" : L = (Ext Sw) %"pr.4";
    %"v440" : L = Shl %"v439", #3;
    %"v441" = %"v103" +p %"v440";
    %"chk58" : A = (Check 0 8 Read 8) %"v441";
    %"v442" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v443" : P = Copy $"_nl_C_name";
    %"v444" : L = Ptoi %"v442";
    %"v445" : L = Ptoi %"v443";
    %"v446" : W = (Cmp Ne L) %"v444", %"v445"
    => goto "L437" };
  ir_blk{ @"L437" [%"v448" : W = phi("L426" => #0, "L436" => %"v446")]:
    => br %"v448" ? "L449" : "L450" };
  ir_blk{ @"L449":
    %"v452" : L = (Ext Sw) %"pr.4";
    %"v453" : L = Shl %"v452", #3;
    %"v454" = %"v103" +p %"v453";
    %"chk59" : A = (Check 0 8 Read 8) %"v454";
    %"v455" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"v456" : P = Copy $"_nl_global_locale";
    %"v457" = %"v456" +p #128;
    %"v461" = %"v457" +p %"v453";
    %"chk60" : A = (Check 0 8 Read 8) %"v461";
    %"v462" : P = (RawLoadPointer 0 load_effects) %"chk60";
    %"v463" : L = Ptoi %"v455";
    %"v464" : L = Ptoi %"v462";
    %"v465" : W = (Cmp Ne L) %"v463", %"v464"
    => goto "L450" };
  ir_blk{ @"L450" [%"v467" : W = phi("L437" => #0, "L449" => %"v465")]:
    => br %"v467" ? "L431" : "L427" };
  ir_blk{ @"L431":
    %"v469" : L = (Ext Sw) %"pr.4";
    %"v470" : L = Shl %"v469", #3;
    %"v471" = %"v103" +p %"v470";
    %"chk61" : A = (Check 0 8 Read 8) %"v471";
    %"v472" : P = (RawLoadPointer 0 load_effects) %"chk61";
    call void $"free"(P %"v472")
    => goto "L427" };
  ir_blk{ @"L427":
    %"v474" : W = Add %"pr.4", #1
    => goto poll "L425" };
  ir_blk{ @"L389":
    %"v475" : P = Copy $"__libc_setlocale_lock";
    call %"v476" : W = $"__GI___pthread_rwlock_unlock"(P %"v475");
    %"chk62" : A = (Renew 0 8 Read 8) %"chk4", %"v4";
    %"v477" : P = (RawLoadPointer 0 load_effects) %"chk62";
    call void $"free"(P %"v477");
    call void $"free"(P %"pr.5")
    => ret %"v386" };
  ir_blk{ @"L99":
    %"chk63" : A = (Check 0 8 Write 1) %"v482";
    store Wl [%"chk63" + 0] <- #0;
    %"chk64" : A = (HalfCheck Lower 0 8 Write 8) %"chk63", %"v482";
    store.ptr [%"chk64" + 0] <- %"v2";
    %"chk65" : A = (Renew 0 8 Read 8) %"chk4", %"v4";
    %"v487" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Renew 0 8 Read 1) %"chk5", %"v5";
    %"v488" : L = (RawLoad LdL 0) %"chk66";
    call %"v491" : P = $"_nl_find_locale"(P %"v487", L %"v488", W %"v0", P %"v482");
    %"v496" : L = Ptoi %"v491";
    %"v498" : W = (Cmp Eq L) %"v496", %"v30"
    => br %"v498" ? "L499" : "L494" };
  ir_blk{ @"L494":
    %"v505" = %"v491" +p #40;
    %"chk67" : A = (Check 0 4 Read 1) %"v505";
    %"v506" : W = (RawLoad (LdNarrow Uw) 0) %"chk67";
    %"v509" : W = (Cmp Ne W) %"v506", #4294967295
    => br %"v509" ? "L501" : "L486" };
  ir_blk{ @"L501":
    %"v511" = %"v491" +p #40;
    %"chk68" : A = (Renew 0 4 Write 1) %"chk67", %"v511";
    store Ww [%"chk68" + 0] <- #4294967295
    => goto "L486" };
  ir_blk{ @"L486":
    %"chk69" : A = (Renew 0 8 Read 8) %"chk64", %"v482";
    %"v518" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"v519" : P = Copy $"_nl_C_name";
    %"v520" : L = Ptoi %"v518";
    %"v521" : L = Ptoi %"v519";
    %"v522" : W = (Cmp Ne L) %"v520", %"v521"
    => br %"v522" ? "L514" : "L516" };
  ir_blk{ @"L514":
    %"chk70" : A = (Renew 0 8 Read 8) %"chk64", %"v482";
    %"v525" : P = (RawLoadPointer 0 load_effects) %"chk70";
    call %"v526" : P = $"__GI___strdup"(P %"v525");
    %"chk71" : A = (Renew 0 8 Write 8) %"chk64", %"v482";
    store.ptr [%"chk71" + 0] <- %"v526";
    %"chk72" : A = (Renew 0 8 Read 8) %"chk64", %"v482";
    %"v531" : P = (RawLoadPointer 0 load_effects) %"chk72";
    %"v532" : L = Ptoi %"v531";
    %"v534" : W = (Cmp Eq L) %"v532", %"v30"
    => br %"v534" ? "L499" : "L516" };
  ir_blk{ @"L516":
    call %"v537" : P = $"glibc_setlocale#new_composite_name"(W %"v0", P %"v482");
    %"v542" : L = Ptoi %"v537";
    %"v544" : W = (Cmp Eq L) %"v542", %"v30"
    => br %"v544" ? "L538" : "iw_6.start" };
  ir_blk{ @"L538":
    %"chk73" : A = (Renew 0 8 Read 8) %"chk64", %"v482";
    %"v549" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"v550" : P = Copy $"_nl_C_name";
    %"v551" : L = Ptoi %"v549";
    %"v552" : L = Ptoi %"v550";
    %"v553" : W = (Cmp Ne L) %"v551", %"v552"
    => br %"v553" ? "L545" : "L499" };
  ir_blk{ @"L545":
    %"chk74" : A = (Renew 0 8 Read 8) %"chk64", %"v482";
    %"v555" : P = (RawLoadPointer 0 load_effects) %"chk74";
    call void $"free"(P %"v555")
    => goto "L499" };
  ir_blk{ @"L499":
    %"chk75" : A = (Renew 0 8 Write 8) %"chk64", %"v482";
    store.ptr [%"chk75" + 0] <- #0
    => goto "L540" };
  ir_blk{ @"iw_6.start":
    %"iw_6.v7" : P = Copy $"_nl_global_locale";
    %"iw_6.v11" = %"iw_6.v7" +p %"v50";
    %"chk76" : A = (Check 0 8 Write 8) %"iw_6.v11";
    store.ptr [%"chk76" + 0] <- %"v491";
    %"iw_6.v16" : P = Copy $"glibc_setlocale#_nl_category_postload";
    %"iw_6.v20" = %"iw_6.v16" +p %"v50";
    %"chk77" : A = (Check 0 8 Read 8) %"iw_6.v20";
    %"iw_6.v21" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"iw_6.v22" : L = Ptoi %"iw_6.v21";
    %"iw_6.v23" : W = (Cmp Ne L) %"iw_6.v22", #0
    => br %"iw_6.v23" ? "iw_6.L13" : "L559" };
  ir_blk{ @"iw_6.L13":
    %"iw_6.v24" : P = Copy $"glibc_setlocale#_nl_category_postload";
    %"iw_6.v28" = %"iw_6.v24" +p %"v50";
    %"chk78" : A = (Check 0 8 Read 8) %"iw_6.v28";
    %"iw_6.v29" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"chk79" : F = CheckFunction %"iw_6.v29";
    rawcall void %"chk79"()
    => goto "L559" };
  ir_blk{ @"L559":
    %"chk80" : A = (Renew 0 8 Read 8) %"chk64", %"v482";
    %"v564" : P = (RawLoadPointer 0 load_effects) %"chk80";
    %"iw_7.v7" : P = Copy $"_nl_global_locale";
    %"iw_7.v8" = %"iw_7.v7" +p #128;
    %"iw_7.v12" = %"iw_7.v8" +p %"v50";
    %"chk81" : A = (Check 0 8 Read 8) %"iw_7.v12";
    %"iw_7.v13" : P = (RawLoadPointer 0 load_effects) %"chk81";
    %"iw_7.v15" : L = Ptoi %"iw_7.v13";
    %"iw_7.v16" : L = Ptoi %"v564";
    %"iw_7.v17" : W = (Cmp Eq L) %"iw_7.v15", %"iw_7.v16"
    => br %"iw_7.v17" ? "iw_8.start" : "iw_7.L6" };
  ir_blk{ @"iw_7.L6":
    %"iw_7.v22" : P = Copy $"_nl_global_locale";
    %"iw_7.v23" = %"iw_7.v22" +p #128;
    %"iw_7.v27" = %"iw_7.v23" +p %"v50";
    %"chk82" : A = (Check 0 8 Read 8) %"iw_7.v27";
    %"iw_7.v28" : P = (RawLoadPointer 0 load_effects) %"chk82";
    %"iw_7.v29" : P = Copy $"_nl_C_name";
    %"iw_7.v30" : L = Ptoi %"iw_7.v28";
    %"iw_7.v31" : L = Ptoi %"iw_7.v29";
    %"iw_7.v32" : W = (Cmp Ne L) %"iw_7.v30", %"iw_7.v31"
    => br %"iw_7.v32" ? "iw_7.L19" : "iw_7.L21" };
  ir_blk{ @"iw_7.L19":
    %"iw_7.v33" : P = Copy $"_nl_global_locale";
    %"iw_7.v34" = %"iw_7.v33" +p #128;
    %"iw_7.v38" = %"iw_7.v34" +p %"v50";
    %"chk83" : A = (Check 0 8 Read 8) %"iw_7.v38";
    %"iw_7.v39" : P = (RawLoadPointer 0 load_effects) %"chk83";
    call void $"free"(P %"iw_7.v39")
    => goto "iw_7.L21" };
  ir_blk{ @"iw_7.L21":
    %"iw_7.v40" : P = Copy $"_nl_global_locale";
    %"iw_7.v41" = %"iw_7.v40" +p #128;
    %"iw_7.v45" = %"iw_7.v41" +p %"v50";
    %"chk84" : A = (Check 0 8 Write 8) %"iw_7.v45";
    store.ptr [%"chk84" + 0] <- %"v564"
    => goto "iw_8.start" };
  ir_blk{ @"iw_8.start":
    %"iw_8.v7" : P = Copy $"_nl_global_locale";
    %"iw_8.v8" = %"iw_8.v7" +p #128;
    %"iw_8.v12" = %"iw_8.v8" +p #48;
    %"chk85" : A = (Check 0 8 Read 8) %"iw_8.v12";
    %"iw_8.v13" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"iw_8.v15" : L = Ptoi %"iw_8.v13";
    %"iw_8.v17" : W = (Cmp Eq L) %"iw_8.v15", %"v542"
    => br %"iw_8.v17" ? "iw_8.join" : "iw_8.L6" };
  ir_blk{ @"iw_8.L6":
    %"iw_8.v22" : P = Copy $"_nl_global_locale";
    %"iw_8.v23" = %"iw_8.v22" +p #128;
    %"iw_8.v27" = %"iw_8.v23" +p #48;
    %"chk86" : A = (Check 0 8 Read 8) %"iw_8.v27";
    %"iw_8.v28" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"iw_8.v29" : P = Copy $"_nl_C_name";
    %"iw_8.v30" : L = Ptoi %"iw_8.v28";
    %"iw_8.v31" : L = Ptoi %"iw_8.v29";
    %"iw_8.v32" : W = (Cmp Ne L) %"iw_8.v30", %"iw_8.v31"
    => br %"iw_8.v32" ? "iw_8.L19" : "iw_8.L21" };
  ir_blk{ @"iw_8.L19":
    %"iw_8.v33" : P = Copy $"_nl_global_locale";
    %"iw_8.v34" = %"iw_8.v33" +p #128;
    %"iw_8.v38" = %"iw_8.v34" +p #48;
    %"chk87" : A = (Check 0 8 Read 8) %"iw_8.v38";
    %"iw_8.v39" : P = (RawLoadPointer 0 load_effects) %"chk87";
    call void $"free"(P %"iw_8.v39")
    => goto "iw_8.L21" };
  ir_blk{ @"iw_8.L21":
    %"iw_8.v40" : P = Copy $"_nl_global_locale";
    %"iw_8.v41" = %"iw_8.v40" +p #128;
    %"iw_8.v45" = %"iw_8.v41" +p #48;
    %"chk88" : A = (Check 0 8 Write 8) %"iw_8.v45";
    store.ptr [%"chk88" + 0] <- %"v537"
    => goto "iw_8.join" };
  ir_blk{ @"iw_8.join":
    %"v566" : P = Copy $"_nl_msg_cat_cntr";
    %"chk89" : A = (Check 0 4 Read 1) %"v566";
    %"v567" : W = (RawLoad (LdNarrow Sw) 0) %"chk89";
    %"v568" : W = Add %"v567", #1;
    %"chk90" : A = (Renew 0 4 Write 1) %"chk89", %"v566";
    store Ww [%"chk90" + 0] <- %"v568"
    => goto "L540" };
  ir_blk{ @"L540":
    %"v569" : P = Copy $"__libc_setlocale_lock";
    call %"v570" : W = $"__GI___pthread_rwlock_unlock"(P %"v569");
    %"chk91" : A = (Renew 0 8 Read 8) %"chk4", %"v4";
    %"v571" : P = (RawLoadPointer 0 load_effects) %"chk91";
    call void $"free"(P %"v571");
    %"chk92" : A = (Renew 0 8 Read 8) %"chk64", %"v482";
    %"v573" : P = (RawLoadPointer 0 load_effects) %"chk92"
    => ret %"v573" }])) }.

Definition hello_image_fn___set_vma_name : func :=
  ir_fn{ "export" "__set_vma_name"(P %"v0", L %"v2", P %"v4") -> RVoid {
  @"start":
    call %"v9" : W = $"__is_decorate_maps_enabled"();
    %"v10" : W = (Ext Ub) %"v9"
    => br %"v10" ? "L6" : "L8";
  @"L6":
    %"v38" : P = Copy $"glibc_setvmaname#str.282";
    call void $"zsafety_error"(P %"v38")
    => goto "L8";
  @"L8":
    => ret void
} }.
