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

Definition hello_image_fn___wcrtomb_internal : func :=
  ir_fn{ "export" "__wcrtomb_internal"(P %"v0", W %"v2", P %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v3" : P = (Alloc 4) #4;
    %"v8" : P = (Alloc 4) #16;
    %"v9" : P = (Alloc 8) #48;
    %"v12" : P = (Alloc 8) #8;
    %"v81" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 4 Write 1) %"v3";
    store Ww [%"chk0" + 0] <- %"v2";
    %"v14" = %"v9" +p #20;
    %"chk1" : A = (Check 0 4 Write 1) %"v14";
    store Ww [%"chk1" + 0] <- #0;
    %"v15" = %"v9" +p #24;
    %"chk2" : A = (HalfCheck Upper 0 4 Write 1) %"chk1", %"v15";
    store Ww [%"chk2" + 0] <- #1;
    %"v16" = %"v9" +p #16;
    %"chk3" : A = (HalfCheck Lower 0 4 Write 1) %"chk1", %"v16";
    store Ww [%"chk3" + 0] <- #1;
    %"v17" = %"v9" +p #32;
    %"v19" : L = Ptoi %"v4";
    %"v20" : W = (Cmp Ne L) %"v19", #0
    => br %"v20" ? "L23" : "L22";
  @"L22":
    %"v24" : P = Copy $"glibc_wcrtomb#state"
    => goto "L23";
  @"L23" [%"v25" : P = phi("L22" => %"v24", "start" => %"v4")]:
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk1", %"v17";
    store.ptr [%"chk4" + 0] <- %"v25";
    %"v30" : L = Ptoi %"v0";
    %"v31" : L = Ptoi #0;
    %"v32" : W = (Cmp Eq L) %"v30", %"v31"
    => br %"v32" ? "L26" : "L28";
  @"L26":
    %"chk5" : A = (Renew 0 4 Write 1) %"chk0", %"v3";
    store Ww [%"chk5" + 0] <- #0
    => goto "L28";
  @"L28":
    %"chk6" : A = (HalfCheck Lower 0 8 Write 8) %"chk1", %"v9";
    store.ptr [%"chk6" + 0] <- %"v8";
    %"v33" = %"v9" +p #8;
    %"v34" = %"v8" +p #16;
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk1", %"v33";
    store.ptr [%"chk7" + 0] <- %"v34";
    %"v35" : P = Copy $"__libc_tsd_LOCALE";
    %"chk8" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"v36";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v4" = %"v38" +p #32;
    %"chk10" : A = (Check 0 8 Read 8) %"iw_1.v4";
    %"iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v5";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v11" : L = Ptoi %"iw_1.v10";
    %"iw_1.v13" : W = (Cmp Eq L) %"iw_1.v11", %"v31"
    => br %"iw_1.v13" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    call void $"__wcsmbs_load_conv"(P %"v38")
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"chk12" : A = (Renew 0 8 Read 8) %"chk11", %"iw_1.v5";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v42" = %"iw_1.v16" +p #16;
    %"chk13" : A = (Check 0 8 Read 8) %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v44" = %"v43" +p #40;
    %"chk14" : A = (Check 0 8 Read 8) %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk16" : A = (Check 0 8 Read 8) %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v53" : L = Ptoi %"v52";
    %"v55" : W = (Cmp Ne L) %"v53", %"v31"
    => br %"v55" ? "L48" : "L47";
  @"L47":
    => goto "L48";
  @"L48":
    %"chk17" : A = (Renew 0 4 Read 1) %"chk0", %"v3";
    %"v60" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v61" : W = (Cmp Eq W) %"v60", #0
    => br %"v61" ? "iw_2.join" : "L58";
  @"iw_2.join":
    %"v65" = %"iw_1.v16" +p #16;
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk19" : F = CheckFunction %"v45";
    rawcall %"v67" : W = %"chk19"(P %"v66", P %"v9", P #0, P #0, P #0, P %"v12", W #1, W #1);
    %"v72" : W = (Cmp Eq W) %"v67", #0
    => br %"v72" ? "L74" : "L73";
  @"L73":
    %"v76" : W = (Cmp Eq W) %"v67", #4
    => goto "L74";
  @"L74" [%"v78" : W = phi("iw_2.join" => #1, "L73" => %"v76")]:
    => br %"v78" ? "L68" : "L59";
  @"L68":
    %"chk20" : A = (Renew 0 8 Read 8) %"chk6", %"v9";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v80" = %"v79" +p #1;
    %"chk21" : A = (Renew 0 8 Write 8) %"chk6", %"v9";
    store.ptr [%"chk21" + 0] <- %"v80";
    %"chk22" : A = (Check 0 1 Write 1) %"v79";
    store Wb [%"chk22" + 0] <- #0
    => goto "L59";
  @"L58":
    %"chk23" : A = (Check 0 8 Write 8) %"v81";
    store.ptr [%"chk23" + 0] <- %"v3";
    %"v85" = %"iw_1.v16" +p #16;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk13", %"v85";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"chk25" : A = (Renew 0 8 Read 8) %"chk23", %"v81";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v88" = %"v87" +p #4;
    %"chk26" : F = CheckFunction %"v45";
    rawcall %"v89" : W = %"chk26"(P %"v86", P %"v9", P %"v81", P %"v88", P #0, P %"v12", W #0, W #1)
    => goto "L59";
  @"L59" [%"pr.1" : W = phi("L58" => %"v89", "L68" => %"v67", "L74" => %"v67")]:
    %"v94" : W = (Cmp Eq W) %"pr.1", #0
    => br %"v94" ? "L96" : "L95";
  @"L95":
    %"v98" : W = (Cmp Eq W) %"pr.1", #4
    => goto "L96";
  @"L96" [%"v100" : W = phi("L59" => #1, "L95" => %"v98")]:
    => br %"v100" ? "L102" : "L101";
  @"L101":
    %"v104" : W = (Cmp Eq W) %"pr.1", #6
    => goto "L102";
  @"L102" [%"v106" : W = phi("L96" => #1, "L101" => %"v104")]:
    => br %"v106" ? "L108" : "L107";
  @"L107":
    %"v110" : W = (Cmp Eq W) %"pr.1", #7
    => goto "L108";
  @"L108" [%"v112" : W = phi("L102" => #1, "L107" => %"v110")]:
    => br %"v112" ? "L114" : "L113";
  @"L113":
    %"v116" : W = (Cmp Eq W) %"pr.1", #5
    => goto "L114";
  @"L114" [%"v118" : W = phi("L108" => #1, "L113" => %"v116")]:
    => br %"v118" ? "L92" : "L91";
  @"L91":
    %"v119" : P = Copy $"glibc_wcrtomb#str.270";
    %"v120" : P = Copy $"glibc_wcrtomb#str.271";
    %"v121" : P = Copy $"glibc_wcrtomb#str.272";
    call void $"__libc_assert_fail"(P %"v119", P %"v120", W #97, P %"v121")
    => goto "L92";
  @"L92":
    => br %"v94" ? "L128" : "L127";
  @"L127":
    %"v130" : W = (Cmp Eq W) %"pr.1", #4
    => goto "L128";
  @"L128" [%"v132" : W = phi("L92" => #1, "L127" => %"v130")]:
    => br %"v132" ? "L134" : "L133";
  @"L133":
    %"v136" : W = (Cmp Eq W) %"pr.1", #5
    => goto "L134";
  @"L134" [%"v138" : W = phi("L128" => #1, "L133" => %"v136")]:
    => br %"v138" ? "L122" : "L123";
  @"L122":
    %"chk27" : A = (Renew 0 8 Read 8) %"chk6", %"v9";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v140" : L = Ptoi %"v139";
    %"v141" : L = Ptoi %"v8";
    %"v142" : L = Sub %"v140", %"v141";
    %"v149" : W = (Cmp Ne L) %"v30", %"v31"
    => br %"v149" ? "L143" : "L124";
  @"L143":
    %"v155" : W = (Cmp Ugt L) %"v142", %"v6"
    => br %"v155" ? "L150" : "L152";
  @"L150":
    call void $"__GI___chk_fail"()
    => goto "L152";
  @"L152":
    call %"v158" : P = $"__GI_memcpy"(P %"v0", P %"v8", L %"v142")
    => goto "L124";
  @"L123":
    %"v161" : P = Copy $"__libc_errno";
    %"chk28" : A = (Check 0 4 Write 1) %"v161";
    store Ww [%"chk28" + 0] <- #84
    => goto "L124";
  @"L124" [%"pr.2" : L = phi("L123" => #18446744073709551615, "L152" => %"v142", "L122" => %"v142")]:
    => ret %"pr.2"
} }.

Definition hello_image_fn___wcrtomb : func :=
  ir_fn{ "export" "__wcrtomb"(P %"v0", W %"v2", P %"v4") -> (RClass L) {
  @"start":
    call %"v11" : L = $"__wcrtomb_internal"(P %"v0", W %"v2", P %"v4", L #18446744073709551615)
    => ret %"v11"
} }.

Definition hello_image_fn___wcschrnul : func :=
  ir_fn{ "export" "__wcschrnul"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    => goto "L4";
  @"L4" [%"pr.1" : P = phi("start" => %"v0", "L11" => %"v19")]:
    %"chk0" : A = (Check 0 4 Read 1) %"pr.1";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = (Cmp Ne W) %"v8", #0
    => br %"v9" ? "L5" : "L6";
  @"L5":
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v16" : W = (Cmp Eq W) %"v14", %"v2"
    => br %"v16" ? "L6" : "L11";
  @"L11":
    %"v19" = %"pr.1" +p #4
    => goto poll "L4";
  @"L6":
    => ret %"pr.1"
} }.

Definition hello_image_fn___wcslen : func :=
  ir_fn{ "export" "__wcslen"(P %"v0") -> (RClass L) {
  @"start":
    => goto "L3";
  @"L3" [%"pr.1" : L = phi("L38" => %"v49", "start" => #0)]:
    %"v8" : L = Shl %"pr.1", #2;
    %"v9" = %"v0" +p %"v8";
    %"chk0" : A = (Check 0 4 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = (Cmp Ne W) %"v10", #0
    => br %"v11" ? "L4" : "L5";
  @"L4":
    %"v17" : L = Add %"pr.1", #1;
    %"v18" : L = Shl %"v17", #2;
    %"v19" = %"v0" +p %"v18";
    %"chk1" : A = (Check 0 4 Read 1) %"v19";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => br %"v21" ? "L12" : "L14";
  @"L12":
    => ret %"v17";
  @"L14":
    %"v29" : L = Add %"v17", #1;
    %"v30" : L = Shl %"v29", #2;
    %"v31" = %"v0" +p %"v30";
    %"chk2" : A = (Check 0 4 Read 1) %"v31";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v33" : W = (Cmp Eq W) %"v32", #0
    => br %"v33" ? "L24" : "L26";
  @"L24":
    => ret %"v29";
  @"L26":
    %"v41" : L = Add %"v29", #1;
    %"v42" : L = Shl %"v41", #2;
    %"v43" = %"v0" +p %"v42";
    %"chk3" : A = (Check 0 4 Read 1) %"v43";
    %"v44" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v45" : W = (Cmp Eq W) %"v44", #0
    => br %"v45" ? "L36" : "L38";
  @"L36":
    => ret %"v41";
  @"L38":
    %"v49" : L = Add %"v41", #1
    => goto poll "L3";
  @"L5":
    => ret %"pr.1"
} }.

Definition hello_image_fn___wcsmbs_getfct : func :=
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

Definition hello_image_fn___wcsmbs_load_conv : func :=
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

Definition hello_image_fn___wcsmbs_clone_conv : func :=
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

Definition hello_image_fn___wcsmbs_named_conv : func :=
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

Definition hello_image_fn___wcsnlen : func :=
  ir_fn{ "export" "__wcsnlen"(P %"v0", L %"v2") -> (RClass L) {
  @"start":
    call %"v7" : P = $"__GI___wmemchr"(P %"v0", W #0, L %"v2");
    %"v12" : L = Ptoi %"v7";
    %"v13" : W = (Cmp Ne L) %"v12", #0
    => br %"v13" ? "L8" : "L10";
  @"L8":
    %"v17" : L = Ptoi %"v0";
    %"v18" : L = Sub %"v12", %"v17";
    %"v19" : L = Div %"v18", #4
    => goto "L10";
  @"L10" [%"pr.1" : L = phi("L8" => %"v19", "start" => %"v2")]:
    => ret %"pr.1"
} }.

Definition hello_image_fn___wcsrtombs : func :=
  ir_fn{ "export" "__wcsrtombs"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v8" : P = (Alloc 8) #48;
    %"v53" : P = (Alloc 4) #8;
    %"v54" : P = (Alloc 4) #256;
    %"v64" : P = (Alloc 8) #8;
    %"v67" : P = (Alloc 8) #8;
    %"v125" : P = (Alloc 8) #8;
    %"v13" = %"v8" +p #20;
    %"chk0" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk0" + 0] <- #0;
    %"v14" = %"v8" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v14";
    store Ww [%"chk1" + 0] <- #1;
    %"v15" = %"v8" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v15";
    store Ww [%"chk2" + 0] <- #1;
    %"v16" = %"v8" +p #32;
    %"v18" : L = Ptoi %"v6";
    %"v19" : W = (Cmp Ne L) %"v18", #0
    => br %"v19" ? "L22" : "L21";
  @"L21":
    %"v23" : P = Copy $"glibc_wcsrtombs#state"
    => goto "L22";
  @"L22" [%"v24" : P = phi("L21" => %"v23", "start" => %"v6")]:
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v16";
    store.ptr [%"chk3" + 0] <- %"v24";
    %"v25" : P = Copy $"__libc_tsd_LOCALE";
    %"chk4" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v26";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v4" = %"v28" +p #32;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v4";
    %"iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Read 8) %"iw_1.v5";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v11" : L = Ptoi %"iw_1.v10";
    %"iw_1.v12" : L = Ptoi #0;
    %"iw_1.v13" : W = (Cmp Eq L) %"iw_1.v11", %"iw_1.v12"
    => br %"iw_1.v13" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    call void $"__wcsmbs_load_conv"(P %"v28")
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"chk8" : A = (Renew 0 8 Read 8) %"chk7", %"iw_1.v5";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v31" = %"iw_1.v16" +p #16;
    %"chk9" : A = (Check 0 8 Read 8) %"v31";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v35" = %"v32" +p #40;
    %"chk10" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk10", %"v32";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v42" : L = Ptoi %"v41";
    %"v44" : W = (Cmp Ne L) %"v42", %"iw_1.v12"
    => br %"v44" ? "L39" : "L38";
  @"L38":
    => goto "L39";
  @"L39":
    %"v50" : L = Ptoi %"v0";
    %"v52" : W = (Cmp Eq L) %"v50", %"iw_1.v12"
    => br %"v52" ? "L46" : "L47";
  @"L46":
    %"chk12" : A = (Check 0 8 Read 8) %"v2";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk12";
    call %"v60" : L = $"__wcslen"(P %"v59");
    %"v61" : L = Shl %"v60", #2;
    %"v62" = %"v57" +p %"v61";
    %"v63" = %"v62" +p #4;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk12", %"v2";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"v64";
    store.ptr [%"chk15" + 0] <- %"v66";
    %"v68" = %"v8" +p #32;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk3", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 8 Read 1) %"v69";
    %"v70" : L = (RawLoad LdL 0) %"chk17";
    %"chk18" : A = (Check 0 8 Write 1) %"v53";
    store Wl [%"chk18" + 0] <- %"v70";
    %"chk19" : A = (Renew 0 8 Write 8) %"chk3", %"v68";
    store.ptr [%"chk19" + 0] <- %"v53";
    %"v72" = %"v8" +p #8;
    %"v73" = %"v54" +p #256;
    %"chk20" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v72";
    store.ptr [%"chk20" + 0] <- %"v73"
    => goto "L74";
  @"L74" [%"pr.5" : L = phi("L46" => #0, "L74" => %"v87")]:
    %"chk21" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v8";
    store.ptr [%"chk21" + 0] <- %"v54";
    %"chk22" : F = CheckFunction %"v36";
    rawcall %"v81" : W = %"chk22"(P %"v32", P %"v8", P %"v64", P %"v63", P #0, P %"v67", W #0, W #1);
    %"chk23" : A = (Renew 0 8 Read 8) %"chk21", %"v8";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v84" : L = Ptoi %"v83";
    %"v85" : L = Ptoi %"v54";
    %"v86" : L = Sub %"v84", %"v85";
    %"v87" : L = Add %"pr.5", %"v86";
    %"v89" : W = (Cmp Eq W) %"v81", #5
    => br %"v89" ? poll "L74" : "L76";
  @"L76":
    %"v94" : W = (Cmp Eq W) %"v81", #0
    => br %"v94" ? "L96" : "L95";
  @"L95":
    %"v98" : W = (Cmp Eq W) %"v81", #4
    => goto "L96";
  @"L96" [%"v100" : W = phi("L76" => #1, "L95" => %"v98")]:
    => br %"v100" ? "L90" : "L48";
  @"L90":
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v107" = %"v104" +p #18446744073709551615;
    %"chk25" : A = (Check 0 1 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Ub) 0) %"chk25";
    %"v109" : W = (Cmp Eq W) %"v108", #0
    => br %"v109" ? "L103" : "L102";
  @"L102":
    %"v110" : P = Copy $"glibc_wcsrtombs#str.270";
    %"v111" : P = Copy $"glibc_wcsrtombs#str.271";
    %"v112" : P = Copy $"glibc_wcsrtombs#str.272";
    call void $"__libc_assert_fail"(P %"v110", P %"v111", W #91, P %"v112")
    => goto "L103";
  @"L103":
    %"v114" : L = Sub %"v87", #1
    => goto "L48";
  @"L47":
    %"chk26" : A = (Check 0 8 Read 8) %"v2";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk26";
    call %"v121" : L = $"__wcsnlen"(P %"v119", L %"v4");
    %"v122" : L = Shl %"v121", #2;
    %"v123" = %"v117" +p %"v122";
    %"v124" = %"v123" +p #4;
    %"chk28" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v8";
    store.ptr [%"chk28" + 0] <- %"v0";
    %"v127" = %"v8" +p #8;
    %"v130" = %"v0" +p %"v4";
    %"chk29" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v127";
    store.ptr [%"chk29" + 0] <- %"v130";
    %"chk30" : F = CheckFunction %"v36";
    rawcall %"v136" : W = %"chk30"(P %"v32", P %"v8", P %"v2", P %"v124", P #0, P %"v125", W #0, W #1);
    %"chk31" : A = (Renew 0 8 Read 8) %"chk28", %"v8";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v139" : L = Ptoi %"v137";
    %"v141" : L = Sub %"v139", %"v50";
    %"v146" : W = (Cmp Eq W) %"v136", #0
    => br %"v146" ? "L148" : "L147";
  @"L147":
    %"v150" : W = (Cmp Eq W) %"v136", #4
    => goto "L148";
  @"L148" [%"v152" : W = phi("L47" => #1, "L147" => %"v150")]:
    => br %"v152" ? "L153" : "L154";
  @"L153":
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v158" = %"v155" +p #18446744073709551615;
    %"chk33" : A = (Check 0 1 Read 1) %"v158";
    %"v159" : W = (RawLoad (LdNarrow Ub) 0) %"chk33";
    %"v160" : W = (Cmp Eq W) %"v159", #0
    => goto "L154";
  @"L154" [%"v162" : W = phi("L148" => #0, "L153" => %"v160")]:
    => br %"v162" ? "L142" : "L48";
  @"L142":
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v168" : L = Ptoi %"v166";
    %"v170" : W = (Cmp Ne L) %"v168", %"v50"
    => br %"v170" ? "L165" : "L164";
  @"L164":
    %"v171" : P = Copy $"glibc_wcsrtombs#str.273";
    %"v172" : P = Copy $"glibc_wcsrtombs#str.271";
    %"v173" : P = Copy $"glibc_wcsrtombs#str.272";
    call void $"__libc_assert_fail"(P %"v171", P %"v172", W #119, P %"v173")
    => goto "L165";
  @"L165":
    %"v177" = %"v8" +p #32;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk3", %"v177";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Check 0 4 Read 1) %"v178";
    %"v179" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"v180" : W = (Cmp Eq W) %"v179", #0
    => br %"v180" ? "L176" : "L175";
  @"L175":
    %"v181" : P = Copy $"glibc_wcsrtombs#str.274";
    %"v182" : P = Copy $"glibc_wcsrtombs#str.271";
    %"v183" : P = Copy $"glibc_wcsrtombs#str.272";
    call void $"__libc_assert_fail"(P %"v181", P %"v182", W #120, P %"v183")
    => goto "L176";
  @"L176":
    %"chk37" : A = (Renew 0 8 Write 8) %"chk26", %"v2";
    store.ptr [%"chk37" + 0] <- #0;
    %"v186" : L = Sub %"v141", #1
    => goto "L48";
  @"L48" [%"pr.4" : L = phi("L103" => %"v114", "L96" => %"v87", "L176" => %"v186", "L154" => %"v141"); %"pr.1" : W = phi("L103" => %"v81", "L96" => %"v81", "L176" => %"v136", "L154" => %"v136")]:
    %"v191" : W = (Cmp Eq W) %"pr.1", #0
    => br %"v191" ? "L193" : "L192";
  @"L192":
    %"v195" : W = (Cmp Eq W) %"pr.1", #4
    => goto "L193";
  @"L193" [%"v197" : W = phi("L48" => #1, "L192" => %"v195")]:
    => br %"v197" ? "L199" : "L198";
  @"L198":
    %"v201" : W = (Cmp Eq W) %"pr.1", #6
    => goto "L199";
  @"L199" [%"v203" : W = phi("L193" => #1, "L198" => %"v201")]:
    => br %"v203" ? "L205" : "L204";
  @"L204":
    %"v207" : W = (Cmp Eq W) %"pr.1", #7
    => goto "L205";
  @"L205" [%"v209" : W = phi("L199" => #1, "L204" => %"v207")]:
    => br %"v209" ? "L211" : "L210";
  @"L210":
    %"v213" : W = (Cmp Eq W) %"pr.1", #5
    => goto "L211";
  @"L211" [%"v215" : W = phi("L205" => #1, "L210" => %"v213")]:
    => br %"v215" ? "L189" : "L188";
  @"L188":
    %"v216" : P = Copy $"glibc_wcsrtombs#str.275";
    %"v217" : P = Copy $"glibc_wcsrtombs#str.271";
    %"v218" : P = Copy $"glibc_wcsrtombs#str.272";
    call void $"__libc_assert_fail"(P %"v216", P %"v217", W #131, P %"v218")
    => goto "L189";
  @"L189":
    %"v223" : W = (Cmp Ne W) %"pr.1", #0
    => br %"v223" ? "L224" : "L225";
  @"L224":
    %"v227" : W = (Cmp Ne W) %"pr.1", #5
    => goto "L225";
  @"L225" [%"v229" : W = phi("L189" => #0, "L224" => %"v227")]:
    => br %"v229" ? "L230" : "L231";
  @"L230":
    %"v233" : W = (Cmp Ne W) %"pr.1", #4
    => goto "L231";
  @"L231" [%"v235" : W = phi("L225" => #0, "L230" => %"v233")]:
    => br %"v235" ? "L219" : "L221";
  @"L219":
    %"v238" : P = Copy $"__libc_errno";
    %"chk38" : A = (Check 0 4 Write 1) %"v238";
    store Ww [%"chk38" + 0] <- #84
    => goto "L221";
  @"L221" [%"pr.3" : L = phi("L219" => #18446744073709551615, "L231" => %"pr.4")]:
    => ret %"pr.3"
} }.
