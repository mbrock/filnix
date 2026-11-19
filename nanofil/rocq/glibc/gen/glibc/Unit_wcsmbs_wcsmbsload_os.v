(** This file defines checked IR from glibc’s `wcsmbs/wcsmbsload.os` object.
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

Definition fn___wcsmbs_clone_conv : func :=
  ir_fn{ "export" "__wcsmbs_clone_conv"(P %"v0") -> RVoid {
  @"start":
    %"v3" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v3";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v4" = %"v6" +p #32;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v4";
    %"iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v5";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v11" : L = Ptoi %"iw_1.v10";
    %"iw_1.v12" : L = Ptoi #0;
    %"iw_1.v13" : W = (Cmp Eq L) %"iw_1.v11", %"iw_1.v12"
    => br %"iw_1.v13" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    call void $"__wcsmbs_load_conv"(P %"v6")
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk3", %"iw_1.v5";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v16";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk6" + 0] <- %"v10";
    %"v11" = %"iw_1.v16" +p #8;
    %"v12" = %"v0" +p #8;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 1) %"chk5", %"v11";
    %"v13" : L = (RawLoad LdL 0) %"chk7";
    %"chk8" : A = (HalfCheck Upper 0 8 Write 1) %"chk6", %"v12";
    store Wl [%"chk8" + 0] <- %"v13";
    %"v14" = %"iw_1.v16" +p #16;
    %"v15" = %"v0" +p #16;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk5", %"v14";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk6", %"v15";
    store.ptr [%"chk10" + 0] <- %"v16";
    %"v17" = %"iw_1.v16" +p #24;
    %"v18" = %"v0" +p #24;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 1) %"chk5", %"v17";
    %"v19" : L = (RawLoad LdL 0) %"chk11";
    %"chk12" : A = (HalfCheck Upper 0 8 Write 1) %"chk6", %"v18";
    store Wl [%"chk12" + 0] <- %"v19";
    %"v21" : P = Copy $"__gconv_lock";
    %"chk13" : A = (Check 0 4 Write 4) %"v21";
    %"v28" : W = (RawCas (CasNarrow Sw) 0) %"chk13", #0, #1;
    %"v29" : W = (Cmp Eq W) %"v28", #0
    => br %"v29" ? "L31" : "L30";
  @"L30":
    => goto "L31";
  @"L31":
    %"v32" : W = (Cmp Ne W) %"v28", #0
    => br %"v32" ? "L35" : "L24";
  @"L35":
    call void $"__GI___lll_lock_wait_private"(P %"v21")
    => goto "L24";
  @"L24":
    %"chk14" : A = (Renew 0 8 Read 8) %"chk6", %"v0";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Read 8) %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v53" : L = Ptoi %"v52";
    %"v55" : W = (Cmp Ne L) %"v53", %"iw_1.v12"
    => br %"v55" ? "L47" : "L49";
  @"L47":
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v59" = %"v58" +p #16;
    %"chk17" : A = (Check 0 4 Read 1) %"v59";
    %"v60" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v63" = %"v62" +p #16;
    %"v64" : L = (Ext Sw) %"v60";
    %"v65" : L = Sar %"v64", #63;
    %"v68" : L = Add %"v64", #1;
    %"v69" : W = (Cmp Ult L) %"v68", %"v64";
    %"v70" : L = (Ext Uw) %"v69";
    %"v72" : L = Add %"v65", %"v70";
    %"chk19" : A = (Check 0 4 Write 1) %"v63";
    store Ww [%"chk19" + 0] <- %"v68";
    %"v73" : L = (Ext Sw) %"v68";
    %"v74" : L = Sar %"v73", #63;
    %"v75" : W = (Cmp Ne L) %"v68", %"v73";
    %"v76" : W = (Cmp Ne L) %"v72", %"v74";
    %"v77" : W = Or %"v75", %"v76"
    => goto "L49";
  @"L49" [%"pr.1" : W = phi("L47" => %"v77", "L24" => #0)]:
    %"v84" = %"v0" +p #16;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk10", %"v84";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Check 0 8 Read 8) %"v85";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v87" : L = Ptoi %"v86";
    %"v89" : W = (Cmp Ne L) %"v87", %"iw_1.v12"
    => br %"v89" ? "L80" : "L82";
  @"L80":
    %"v92" = %"v0" +p #16;
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v94" = %"v93" +p #16;
    %"chk23" : A = (Check 0 4 Read 1) %"v94";
    %"v95" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v98" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v99" = %"v98" +p #16;
    %"v100" : L = (Ext Sw) %"v95";
    %"v101" : L = Sar %"v100", #63;
    %"v104" : L = Add %"v100", #1;
    %"v105" : W = (Cmp Ult L) %"v104", %"v100";
    %"v106" : L = (Ext Uw) %"v105";
    %"v108" : L = Add %"v101", %"v106";
    %"chk25" : A = (Check 0 4 Write 1) %"v99";
    store Ww [%"chk25" + 0] <- %"v104";
    %"v109" : L = (Ext Sw) %"v104";
    %"v110" : L = Sar %"v109", #63;
    %"v111" : W = (Cmp Ne L) %"v104", %"v109";
    %"v112" : W = (Cmp Ne L) %"v108", %"v110";
    %"v113" : W = Or %"v111", %"v112";
    %"v114" : W = Or %"pr.1", %"v113"
    => goto "L82";
  @"L82" [%"pr.2" : W = phi("L80" => %"v114", "L49" => %"pr.1")]:
    %"v117" : P = Copy $"__gconv_lock";
    %"chk26" : A = (Check 0 4 Read 1) %"v117";
    %"v121" : W = (RawLoad (LdNarrow Sw) 0) %"chk26"
    => goto "L122";
  @"L122" [%"v124" : W = phi("L82" => %"v121", "L122" => %"v125")]:
    %"chk27" : A = (HalfCheck Lower 0 4 Write 4) %"chk26", %"v117";
    %"v125" : W = (RawCas (CasNarrow Sw) 0) %"chk27", %"v124", #0;
    %"v126" : W = (Cmp Eq W) %"v125", %"v124"
    => br %"v126" ? "L123" : poll "L122";
  @"L123":
    %"v131" : W = (Cmp Sgt W) %"v124", #1
    => br %"v131" ? "L134" : "L129";
  @"L134":
    call void $"__GI___lll_lock_wake_private"(P %"v117")
    => goto "L129";
  @"L129":
    => br %"pr.2" ? "L145" : "L147";
  @"L145":
    %"v149" : P = Copy $"glibc_wcsmbsload#str.259";
    call void $"__GI___libc_fatal"(P %"v149")
    => goto "L147";
  @"L147":
    => ret void
} }.

Definition item___wcsmbs_gconv_fcts_c : item :=
  (IData (a "__wcsmbs_gconv_fcts_c") (LRo (a "export")) 8 [(Sym (a "glibc_wcsmbsload#to_wc") 0); (Item Wl 1); (Sym (a "glibc_wcsmbsload#to_mb") 0); (Item Wl 1)]).

Definition fn___wcsmbs_getfct : func :=
  ir_fn{ "export" "__wcsmbs_getfct"(P %"v0", P %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v6" : P = (Alloc 8) #8;
    %"v7" : P = (Alloc 8) #8;
    call %"v13" : W = $"__gconv_find_transform"(P %"v0", P %"v2", P %"v7", P %"v6", W #0);
    %"v14" : W = (Cmp Ne W) %"v13", #0
    => br %"v14" ? "L8" : "L10";
  @"L8":
    => ret #0;
  @"L10":
    %"chk0" : A = (Check 0 8 Read 1) %"v6";
    %"v19" : L = (RawLoad LdL 0) %"chk0";
    %"v20" : W = (Cmp Ugt L) %"v19", #1
    => br %"v20" ? "L16" : "L17";
  @"L16":
    %"chk1" : A = (Check 0 8 Read 8) %"v7";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v22" : L = (RawLoad LdL 0) %"chk0";
    call %"v23" : W = $"__gconv_close_transform"(P %"v21", L %"v22");
    %"chk3" : A = (Renew 0 8 Write 8) %"chk1", %"v7";
    store.ptr [%"chk3" + 0] <- #0
    => goto "L18";
  @"L17":
    %"v25" : L = (RawLoad LdL 0) %"chk0";
    %"chk5" : A = (Check 0 8 Write 1) %"v4";
    store Wl [%"chk5" + 0] <- %"v25"
    => goto "L18";
  @"L18":
    %"chk6" : A = (Check 0 8 Read 8) %"v7";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk6"
    => ret %"v26"
} }.

Definition fn___wcsmbs_load_conv : func :=
  ir_fn{ "export" "__wcsmbs_load_conv"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #32;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v6" : P = Copy $"__libc_setlocale_lock";
    call %"v7" : W = $"__GI___pthread_rwlock_wrlock"(P %"v6");
    %"chk1" : A = (Check 0 8 Read 8) %"v5";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v12";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L8" : "L10";
  @"L8":
    call %"v22" : P = $"calloc"(L #1, L #32);
    %"v27" : L = Ptoi %"v22";
    %"v29" : W = (Cmp Eq L) %"v27", %"v14"
    => br %"v29" ? "L30" : "L25";
  @"L25":
    %"v33" = %"v0" +p #56;
    %"v37" = %"v33" +p #112;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v40" = %"v0" +p #44;
    %"chk3" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v40";
    %"v41" : W = (RawLoad (LdNarrow Sw) 0) %"chk3"
    => br %"v41" ? "L48" : "L49";
  @"L48":
    %"v52" : P = Copy $"glibc_wcsmbsload#str.256"
    => goto "L50";
  @"L49":
    %"v53" : P = Copy $"glibc_wcsmbsload#str.257"
    => goto "L50";
  @"L50" [%"v54" : P = phi("L48" => %"v52", "L49" => %"v53")]:
    call %"v55" : L = $"__GI_strlen"(P %"v54")
    => goto "L56";
  @"L56" [%"pr.9" : L = phi("L50" => #0, "L62" => %"v70", "L57" => %"pr.9"); %"pr.1" : P = phi("L50" => %"v38", "L62" => %"v66", "L57" => %"v66")]:
    %"chk4" : A = (Check 0 1 Read 1) %"pr.1";
    %"v60" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v61" : W = (Cmp Ne W) %"v60", #0
    => br %"v61" ? "L57" : "L58";
  @"L57":
    %"v66" = %"pr.1" +p #1;
    %"v67" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v68" : W = (Cmp Eq W) %"v67", #47
    => br %"v68" ? "L62" : poll "L56";
  @"L62":
    %"v70" : L = Add %"pr.9", #1
    => goto poll "L56";
  @"L58":
    %"v73" : L = Ptoi %"pr.1";
    %"v74" : L = Ptoi %"v38";
    %"v75" : L = Sub %"v73", %"v74";
    %"v76" : L = Add %"v75", #3;
    %"v78" : L = Add %"v76", %"v55";
    %"v79" : P = (Alloc 16) %"v78"
    => goto "L81";
  @"L81" [%"pr.8" : P = phi("L58" => %"v79", "L82" => %"v88"); %"pr.2" : P = phi("L58" => %"v38", "L82" => %"v132")]:
    %"chk6" : A = (Check 0 1 Read 1) %"pr.2";
    %"v85" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v86" : W = (Cmp Ne W) %"v85", #0
    => br %"v86" ? "L82" : "L83";
  @"L82":
    %"v88" = %"pr.8" +p #1;
    %"v128" : P = Copy $"_nl_C_locobj";
    %"v129" = %"v128" +p #120;
    %"chk7" : A = (Check 0 8 Read 8) %"v129";
    %"v130" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v132" = %"pr.2" +p #1;
    %"chk8" : A = (Renew 0 1 Read 1) %"chk6", %"pr.2";
    %"v133" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v134" : L = (Ext Sw) %"v133";
    %"v135" : L = Shl %"v134", #2;
    %"v136" = %"v130" +p %"v135";
    %"chk9" : A = (Check 0 4 Read 1) %"v136";
    %"v137" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v139" : W = (Ext Sb) %"v137";
    %"chk10" : A = (Check 0 1 Write 1) %"pr.8";
    store Wb [%"chk10" + 0] <- %"v139"
    => goto poll "L81";
  @"L83":
    %"v144" : W = (Cmp Ult L) %"pr.9", #2
    => br %"v144" ? "L140" : "L142";
  @"L140":
    %"v146" = %"pr.8" +p #1;
    %"chk11" : A = (Check 0 1 Write 1) %"pr.8";
    store Wb [%"chk11" + 0] <- #47;
    %"v151" : W = (Cmp Ult L) %"pr.9", #1
    => br %"v151" ? "L147" : "L142";
  @"L147":
    %"v153" = %"v146" +p #1;
    %"chk12" : A = (HalfCheck Upper 0 1 Write 1) %"chk11", %"v146";
    store Wb [%"chk12" + 0] <- #47;
    %"v158" : W = (Cmp Ne L) %"v55", #0
    => br %"v158" ? "L154" : "L142";
  @"L154":
    => br %"v41" ? "L160" : "L161";
  @"L160":
    %"v164" : P = Copy $"glibc_wcsmbsload#str.256"
    => goto "L162";
  @"L161":
    %"v165" : P = Copy $"glibc_wcsmbsload#str.257"
    => goto "L162";
  @"L162" [%"v166" : P = phi("L160" => %"v164", "L161" => %"v165")]:
    call %"v168" : P = $"__GI_mempcpy"(P %"v153", P %"v166", L %"v55")
    => goto "L142";
  @"L142" [%"pr.5" : P = phi("L162" => %"v168", "L147" => %"v153", "L140" => %"v146", "L83" => %"pr.8")]:
    %"chk13" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk13" + 0] <- #0;
    %"v172" : P = Copy $"glibc_wcsmbsload#str.258";
    %"v175" = %"v22" +p #8;
    call %"v176" : P = $"__wcsmbs_getfct"(P %"v172", P %"v79", P %"v175");
    %"chk14" : A = (Check 0 8 Write 8) %"v22";
    store.ptr [%"chk14" + 0] <- %"v176";
    %"chk15" : A = (Renew 0 8 Read 8) %"chk14", %"v22";
    %"v181" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v182" : L = Ptoi %"v181";
    %"v184" : W = (Cmp Ne L) %"v182", %"v14"
    => br %"v184" ? "L177" : "L179";
  @"L177":
    %"v186" = %"v22" +p #16;
    %"v188" : P = Copy $"glibc_wcsmbsload#str.258";
    %"v190" = %"v22" +p #24;
    call %"v191" : P = $"__wcsmbs_getfct"(P %"v79", P %"v188", P %"v190");
    %"chk16" : A = (HalfCheck Upper 0 8 Write 8) %"chk14", %"v186";
    store.ptr [%"chk16" + 0] <- %"v191"
    => goto "L179";
  @"L179":
    %"v196" = %"v22" +p #16;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk14", %"v196";
    %"v197" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v198" : L = Ptoi %"v197";
    %"v200" : W = (Cmp Eq L) %"v198", %"v14"
    => br %"v200" ? "L192" : "L193";
  @"L192":
    %"chk18" : A = (Renew 0 8 Read 8) %"chk14", %"v22";
    %"v205" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v206" : L = Ptoi %"v205";
    %"v208" : W = (Cmp Ne L) %"v206", %"v14"
    => br %"v208" ? "L201" : "L203";
  @"L201":
    %"v210" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v212" = %"v22" +p #8;
    %"v213" : L = (RawLoad LdL 8) %"chk18";
    call %"v214" : W = $"__gconv_close_transform"(P %"v210", L %"v213")
    => goto "L203";
  @"L203":
    call void $"free"(P %"v22")
    => goto "L30";
  @"L30":
    %"v217" : P = Copy $"__wcsmbs_gconv_fcts_c";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk1", %"v5";
    store.ptr [%"chk21" + 0] <- %"v217"
    => goto "L10";
  @"L193":
    %"chk22" : A = (Renew 0 8 Write 8) %"chk1", %"v5";
    store.ptr [%"chk22" + 0] <- %"v22"
    => goto "L10";
  @"L10":
    %"v220" : P = Copy $"__libc_setlocale_lock";
    call %"v221" : W = $"__GI___pthread_rwlock_unlock"(P %"v220")
    => ret void
} }.

Definition fn___wcsmbs_named_conv : func :=
  ir_fn{ "export" "__wcsmbs_named_conv"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v5" : P = Copy $"glibc_wcsmbsload#str.258";
    %"v8" = %"v0" +p #8;
    call %"v9" : P = $"__wcsmbs_getfct"(P %"v5", P %"v2", P %"v8");
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v9";
    %"chk1" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v15" : L = Ptoi %"v14";
    %"v16" : L = Ptoi #0;
    %"v17" : W = (Cmp Eq L) %"v15", %"v16"
    => br %"v17" ? "L10" : "L12";
  @"L10":
    => ret #1;
  @"L12":
    %"v20" = %"v0" +p #16;
    %"v22" : P = Copy $"glibc_wcsmbsload#str.258";
    %"v24" = %"v0" +p #24;
    call %"v25" : P = $"__wcsmbs_getfct"(P %"v2", P %"v22", P %"v24");
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v20";
    store.ptr [%"chk2" + 0] <- %"v25";
    %"chk3" : A = (Renew 0 8 Read 8) %"chk2", %"v20";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v32" : L = Ptoi %"v31";
    %"v34" : W = (Cmp Eq L) %"v32", %"v16"
    => br %"v34" ? "L26" : "L28";
  @"L26":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v38" = %"v0" +p #8;
    %"v39" : L = (RawLoad LdL 8) %"chk4";
    call %"v40" : W = $"__gconv_close_transform"(P %"v36", L %"v39")
    => ret #1;
  @"L28":
    => ret #0
} }.

Definition item_glibc_wcsmbsload'23str'2e256 : item :=
  (IData (a "glibc_wcsmbsload#str.256") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 83); (Item Wb 76); (Item Wb 73); (Item Wb 84); (Item Wb 0)]).

Definition item_glibc_wcsmbsload'23str'2e257 : item :=
  (IData (a "glibc_wcsmbsload#str.257") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition item_glibc_wcsmbsload'23str'2e258 : item :=
  (IData (a "glibc_wcsmbsload#str.258") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_wcsmbsload'23str'2e259 : item :=
  (IData (a "glibc_wcsmbsload#str.259") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 58); (Item Wb 32); (Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 32); (Item Wb 109); (Item Wb 111); (Item Wb 100); (Item Wb 117); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 101); (Item Wb 110); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 117); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 111); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 102); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_wcsmbsload'23str'2e260 : item :=
  (IData (a "glibc_wcsmbsload#str.260") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 78); (Item Wb 83); (Item Wb 73); (Item Wb 95); (Item Wb 88); (Item Wb 51); (Item Wb 46); (Item Wb 52); (Item Wb 45); (Item Wb 49); (Item Wb 57); (Item Wb 54); (Item Wb 56); (Item Wb 47); (Item Wb 47); (Item Wb 84); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 83); (Item Wb 76); (Item Wb 73); (Item Wb 84); (Item Wb 0)]).

Definition item_glibc_wcsmbsload'23to_mb : item :=
  (IData (a "glibc_wcsmbsload#to_mb") (LRo (a "local")) 8 [(Item Wl 0); (Item Wl 0); (Item Ww 2147483647); (Zero 4); (Sym (a "glibc_wcsmbsload#str.258") 0); (Sym (a "glibc_wcsmbsload#str.260") 0); (Sym (a "__gconv_transform_internal_ascii") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Ww 4); (Item Ww 4); (Item Ww 1); (Item Ww 1); (Item Ww 0); (Zero 4); (Item Wl 0)]).

Definition item_glibc_wcsmbsload'23to_wc : item :=
  (IData (a "glibc_wcsmbsload#to_wc") (LRo (a "local")) 8 [(Item Wl 0); (Item Wl 0); (Item Ww 2147483647); (Zero 4); (Sym (a "glibc_wcsmbsload#str.260") 0); (Sym (a "glibc_wcsmbsload#str.258") 0); (Sym (a "__gconv_transform_ascii_internal") 0); (Sym (a "__gconv_btwoc_ascii") 0); (Item Wl 0); (Item Wl 0); (Item Ww 1); (Item Ww 1); (Item Ww 4); (Item Ww 4); (Item Ww 0); (Zero 4); (Item Wl 0)]).
