(** This file defines checked IR from glibc’s `wcsmbs/wcrtomb.os` object.
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

Definition fn___wcrtomb : func :=
  ir_fn{ "export" "__wcrtomb"(P %"v0", W %"v2", P %"v4") -> (RClass L) {
  @"start":
    call %"v11" : L = $"__wcrtomb_internal"(P %"v0", W %"v2", P %"v4", L #18446744073709551615)
    => ret %"v11"
} }.

Definition fn___wcrtomb_internal : func :=
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

Definition item_glibc_wcrtomb'23state : item :=
  (IData (a "glibc_wcrtomb#state") LLocal 4 [(Zero 8)]).

Definition item_glibc_wcrtomb'23str'2e270 : item :=
  (IData (a "glibc_wcrtomb#str.270") (LRo (a "local")) 1 (app (app [(Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 79); (Item Wb 75); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78)] [(Item Wb 86); (Item Wb 95); (Item Wb 69); (Item Wb 77); (Item Wb 80); (Item Wb 84); (Item Wb 89); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 76); (Item Wb 76); (Item Wb 69); (Item Wb 71)]) (app [(Item Wb 65); (Item Wb 76); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 67); (Item Wb 79); (Item Wb 77); (Item Wb 80); (Item Wb 76); (Item Wb 69); (Item Wb 84); (Item Wb 69)] [(Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 70); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 79); (Item Wb 85); (Item Wb 84); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 0)]))).

Definition item_glibc_wcrtomb'23str'2e271 : item :=
  (IData (a "glibc_wcrtomb#str.271") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 99); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 98); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_wcrtomb'23str'2e272 : item :=
  (IData (a "glibc_wcrtomb#str.272") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 99); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 98); (Item Wb 95); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).
