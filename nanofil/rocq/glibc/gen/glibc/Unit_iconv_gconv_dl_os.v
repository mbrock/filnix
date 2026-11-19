(** This file defines checked IR from glibc’s `iconv/gconv_dl.os` object.
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

Definition fn___gconv_find_shlib : func :=
  ir_fn{ "export" "__gconv_find_shlib"(P %"v0") -> (RClass P) {
  @"start":
    %"v1" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v1";
    store.ptr [%"chk0" + 0] <- %"v0";
    %"v4" : P = Copy $"glibc_gconv_dl#loaded";
    %"v5" : P = Copy $"glibc_gconv_dl#known_compare";
    call %"v6" : P = $"__GI___tfind"(P %"v1", P %"v4", P %"v5");
    %"v11" : L = Ptoi %"v6";
    %"v12" : L = Ptoi #0;
    %"v13" : W = (Cmp Eq L) %"v11", %"v12"
    => br %"v13" ? "L7" : "L8";
  @"L7":
    %"chk1" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v16" : L = $"__GI_strlen"(P %"v15");
    %"v17" : L = Add %"v16", #1;
    %"v19" : L = Add %"v17", #48;
    call %"v20" : P = $"malloc"(L %"v19");
    %"v25" : L = Ptoi %"v20";
    %"v27" : W = (Cmp Ne L) %"v25", %"v12"
    => br %"v27" ? "L21" : "L9";
  @"L21":
    %"v30" = %"v20" +p #48;
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call %"v33" : P = $"__GI_memcpy"(P %"v30", P %"v31", L %"v17");
    %"chk3" : A = (Check 0 8 Write 8) %"v20";
    store.ptr [%"chk3" + 0] <- %"v33";
    %"v35" = %"v20" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v35";
    store Ww [%"chk4" + 0] <- #4294967293;
    %"v39" = %"v20" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v39";
    store.ptr [%"chk5" + 0] <- #0;
    %"v44" : P = Copy $"glibc_gconv_dl#loaded";
    %"v45" : P = Copy $"glibc_gconv_dl#known_compare";
    call %"v46" : P = $"__GI___tsearch"(P %"v20", P %"v44", P %"v45");
    %"v47" : L = Ptoi %"v46";
    %"v49" : W = (Cmp Eq L) %"v47", %"v12"
    => br %"v49" ? "L40" : "L9";
  @"L40":
    call void $"free"(P %"v20")
    => goto "L9";
  @"L8":
    %"chk6" : A = (Check 0 8 Read 8) %"v6";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk6"
    => goto "L9";
  @"L9" [%"pr.7" : P = phi("L8" => %"v54", "L40" => #0, "L21" => %"v20", "L7" => %"v20")]:
    %"v59" : L = Ptoi %"pr.7";
    %"v61" : W = (Cmp Ne L) %"v59", %"v12"
    => br %"v61" ? "L55" : "L57";
  @"L55":
    %"v66" = %"pr.7" +p #8;
    %"chk7" : A = (Check 0 4 Read 1) %"v66";
    %"v67" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v69" : W = (Cmp Slt W) %"v67", #4294967294
    => br %"v69" ? "L62" : "L63";
  @"L62":
    %"v74" = %"pr.7" +p #16;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v76" : L = Ptoi %"v75";
    %"v78" : W = (Cmp Eq L) %"v76", %"v12"
    => br %"v78" ? "L72" : "L71";
  @"L71":
    %"v79" : P = Copy $"glibc_gconv_dl#str.274";
    %"v80" : P = Copy $"glibc_gconv_dl#str.275";
    %"v81" : P = Copy $"glibc_gconv_dl#str.276";
    call void $"__libc_assert_fail"(P %"v79", P %"v80", W #113, P %"v81")
    => goto "L72";
  @"L72":
    %"v83" = %"pr.7" +p #16;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk7", %"pr.7";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call %"v86" : P = $"__libc_dlopen_mode"(P %"v85", W #2);
    %"chk10" : A = (Renew 0 8 Write 8) %"chk8", %"v83";
    store.ptr [%"chk10" + 0] <- %"v86";
    %"chk11" : A = (Renew 0 8 Read 8) %"chk8", %"v83";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v93" : L = Ptoi %"v92";
    %"v95" : W = (Cmp Ne L) %"v93", %"v12"
    => br %"v95" ? "L87" : "L57";
  @"L87":
    %"v97" = %"pr.7" +p #24;
    %"v99" = %"pr.7" +p #16;
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v101" : P = Copy $"glibc_gconv_dl#str.277";
    call %"v102" : P = $"__libc_dlsym"(P %"v100", P %"v101");
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v97";
    store.ptr [%"chk13" + 0] <- %"v102";
    %"chk14" : A = (Renew 0 8 Read 8) %"chk13", %"v97";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v109" : L = Ptoi %"v108";
    %"v111" : W = (Cmp Eq L) %"v109", %"v12"
    => br %"v111" ? "L103" : "L104";
  @"L103":
    call void $"__gconv_release_shlib"(P %"pr.7")
    => goto "L57";
  @"L104":
    %"v114" = %"pr.7" +p #32;
    %"v116" = %"pr.7" +p #16;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk8", %"v116";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v118" : P = Copy $"glibc_gconv_dl#str.278";
    call %"v119" : P = $"__libc_dlsym"(P %"v117", P %"v118");
    %"chk16" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v114";
    store.ptr [%"chk16" + 0] <- %"v119";
    %"v121" = %"pr.7" +p #40;
    %"chk17" : A = (Renew 0 8 Read 8) %"chk8", %"v116";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v125" : P = Copy $"glibc_gconv_dl#str.279";
    call %"v126" : P = $"__libc_dlsym"(P %"v124", P %"v125");
    %"chk18" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v121";
    store.ptr [%"chk18" + 0] <- %"v126";
    %"v128" = %"pr.7" +p #24;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk13", %"v128";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Renew 0 8 Read 8) %"chk16", %"v114";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Renew 0 8 Read 8) %"chk18", %"v121";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v137" = %"pr.7" +p #8;
    %"chk22" : A = (Renew 0 4 Write 1) %"chk7", %"v137";
    store Ww [%"chk22" + 0] <- #1
    => goto "L57";
  @"L63":
    %"v142" = %"pr.7" +p #16;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"v142";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v144" : L = Ptoi %"v143";
    %"v146" : W = (Cmp Ne L) %"v144", %"v12"
    => br %"v146" ? "L138" : "L57";
  @"L138":
    %"v148" = %"pr.7" +p #8;
    %"v154" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v155" : W = Add %"v154", #1;
    %"v156" : W = (Cmp Sgt W) %"v155", #1
    => br %"v156" ? "L149" : "L151";
  @"L149":
    %"v158" = %"pr.7" +p #8;
    %"v159" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v160" : W = Add %"v159", #1
    => goto "L151";
  @"L151" [%"v161" : W = phi("L149" => %"v160", "L138" => #1)]:
    %"chk26" : A = (Renew 0 4 Write 1) %"chk7", %"v148";
    store Ww [%"chk26" + 0] <- %"v161"
    => goto "L57";
  @"L57" [%"pr.4" : P = phi("L103" => #0, "L104" => %"pr.7", "L72" => #0, "L151" => %"pr.7", "L63" => %"pr.7", "L9" => %"pr.7")]:
    => ret %"pr.4"
} }.

Definition fn___gconv_release_shlib : func :=
  ir_fn{ "export" "__gconv_release_shlib"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_gconv_dl#loaded";
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v3" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v4" : P = Copy $"glibc_gconv_dl#do_release_shlib";
    call void $"__GI___twalk_r"(P %"v3", P %"v4", P %"v0")
    => ret void
} }.

Definition fn_glibc_gconv_dl'23do_release_shlib : func :=
  ir_fn{ "local" "glibc_gconv_dl#do_release_shlib"(P %"v0", W %"v2", P %"v4") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v15" : W = (Cmp Ne W) %"v2", #0
    => br %"v15" ? "L16" : "L17";
  @"L16":
    %"v19" : W = (Cmp Ne W) %"v2", #3
    => goto "L17";
  @"L17" [%"v21" : W = phi("start" => #0, "L16" => %"v19")]:
    => br %"v21" ? "L11" : "L13";
  @"L11":
    => ret void;
  @"L13":
    %"v28" : L = Ptoi %"v10";
    %"v29" : L = Ptoi %"v4";
    %"v30" : W = (Cmp Eq L) %"v28", %"v29"
    => br %"v30" ? "L23" : "L24";
  @"L23":
    %"v35" = %"v10" +p #8;
    %"chk1" : A = (Check 0 4 Read 1) %"v35";
    %"v36" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v37" : W = (Cmp Sgt W) %"v36", #0
    => br %"v37" ? "L33" : "L32";
  @"L32":
    %"v38" : P = Copy $"glibc_gconv_dl#str.280";
    %"v39" : P = Copy $"glibc_gconv_dl#str.275";
    %"v40" : P = Copy $"glibc_gconv_dl#str.281";
    call void $"__libc_assert_fail"(P %"v38", P %"v39", W #162, P %"v40")
    => goto "L33";
  @"L33":
    %"v42" = %"v10" +p #8;
    %"chk2" : A = (Renew 0 4 Read 1) %"chk1", %"v42";
    %"v43" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v44" : W = Sub %"v43", #1;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk1", %"v42";
    store Ww [%"chk3" + 0] <- %"v44"
    => goto "L25";
  @"L24":
    %"v49" = %"v10" +p #8;
    %"chk4" : A = (Check 0 4 Read 1) %"v49";
    %"v50" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v51" : W = (Cmp Sle W) %"v50", #0
    => br %"v51" ? "L52" : "L53";
  @"L52":
    %"v55" = %"v10" +p #8;
    %"v56" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v58" : W = (Cmp Sge W) %"v56", #4294967294
    => goto "L53";
  @"L53" [%"v60" : W = phi("L24" => #0, "L52" => %"v58")]:
    => br %"v60" ? "L61" : "L62";
  @"L61":
    %"v64" = %"v10" +p #8;
    %"v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v66" : W = Sub %"v65", #1;
    %"chk7" : A = (Renew 0 4 Write 1) %"chk4", %"v64";
    store Ww [%"chk7" + 0] <- %"v66";
    %"v68" : W = (Cmp Slt W) %"v66", #4294967294
    => goto "L62";
  @"L62" [%"v70" : W = phi("L53" => #0, "L61" => %"v68")]:
    => br %"v70" ? "L71" : "L72";
  @"L71":
    %"v74" = %"v10" +p #16;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk4", %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v76" : L = Ptoi %"v75";
    %"v77" : L = Ptoi #0;
    %"v78" : W = (Cmp Ne L) %"v76", %"v77"
    => goto "L72";
  @"L72" [%"v80" : W = phi("L62" => #0, "L71" => %"v78")]:
    => br %"v80" ? "L45" : "L25";
  @"L45":
    %"v82" = %"v10" +p #16;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk4", %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call %"v84" : W = $"__libc_dlclose"(P %"v83");
    %"chk10" : A = (Renew 0 8 Write 8) %"chk9", %"v82";
    store.ptr [%"chk10" + 0] <- #0
    => goto "L25";
  @"L25":
    => ret void
} }.

Definition fn_glibc_gconv_dl'23known_compare : func :=
  ir_fn{ "local" "glibc_gconv_dl#known_compare"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v12" : W = $"__GI_strcmp"(P %"v9", P %"v11")
    => ret %"v12"
} }.

Definition item_glibc_gconv_dl'23loaded : item :=
  (IData (a "glibc_gconv_dl#loaded") LLocal 8 [(Zero 8)]).

Definition item_glibc_gconv_dl'23str'2e274 : item :=
  (IData (a "glibc_gconv_dl#str.274") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 111); (Item Wb 117); (Item Wb 110); (Item Wb 100); (Item Wb 45); (Item Wb 62); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_gconv_dl'23str'2e275 : item :=
  (IData (a "glibc_gconv_dl#str.275") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 95); (Item Wb 100); (Item Wb 108); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_gconv_dl'23str'2e276 : item :=
  (IData (a "glibc_gconv_dl#str.276") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 110); (Item Wb 100); (Item Wb 95); (Item Wb 115); (Item Wb 104); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).

Definition item_glibc_gconv_dl'23str'2e277 : item :=
  (IData (a "glibc_gconv_dl#str.277") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 0)]).

Definition item_glibc_gconv_dl'23str'2e278 : item :=
  (IData (a "glibc_gconv_dl#str.278") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 95); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_gconv_dl'23str'2e279 : item :=
  (IData (a "glibc_gconv_dl#str.279") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_gconv_dl'23str'2e280 : item :=
  (IData (a "glibc_gconv_dl#str.280") (LRo (a "local")) 1 [(Item Wb 111); (Item Wb 98); (Item Wb 106); (Item Wb 45); (Item Wb 62); (Item Wb 99); (Item Wb 111); (Item Wb 117); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 62); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_gconv_dl'23str'2e281 : item :=
  (IData (a "glibc_gconv_dl#str.281") (LRo (a "local")) 1 [(Item Wb 100); (Item Wb 111); (Item Wb 95); (Item Wb 114); (Item Wb 101); (Item Wb 108); (Item Wb 101); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 104); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).
