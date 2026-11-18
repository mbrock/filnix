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

Definition hello_image_fn_rpl_mbrtoc32 : func :=
  ir_fn{ "export" "rpl_mbrtoc32"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v12" : L = Ptoi %"v2";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    %"v15" : P = Copy $"mbrtoc32#str.36"
    => goto "L10";
  @"L10" [%"pr.3" : L = phi("L8" => #1, "start" => %"v4"); %"pr.2" : P = phi("L8" => %"v15", "start" => %"v2"); %"pr.1" : P = phi("L8" => #0, "start" => %"v0")]:
    %"v20" : L = Ptoi %"v6";
    %"v22" : W = (Cmp Eq L) %"v20", %"v13"
    => br %"v22" ? "L16" : "L18";
  @"L16":
    %"v23" : P = Copy $"mbrtoc32#internal_state"
    => goto "L18";
  @"L18" [%"pr.4" : P = phi("L16" => %"v23", "L10" => %"v6")]:
    call %"v29" : L = $"mbrtoc32"(P %"pr.1", P %"pr.2", L %"pr.3", P %"pr.4");
    %"v36" : W = (Cmp Uge L) %"v29", #18446744073709551614
    => br %"v36" ? "L37" : "L38";
  @"L37":
    %"v40" : W = (Cmp Ne L) %"pr.3", #0
    => goto "L38";
  @"L38" [%"v42" : W = phi("L18" => #0, "L37" => %"v40")]:
    => br %"v42" ? "L43" : "L44";
  @"L43":
    call %"v45" : W = $"hard_locale"(W #0);
    %"v46" : W = (Ext Ub) %"v45";
    %"v47" : W = (Cmp Eq W) %"v46", #0
    => goto "L44";
  @"L44" [%"v49" : W = phi("L38" => #0, "L43" => %"v47")]:
    => br %"v49" ? "L30" : "L32";
  @"L30":
    %"v54" : L = Ptoi %"pr.1";
    %"v56" : W = (Cmp Ne L) %"v54", %"v13"
    => br %"v56" ? "L50" : "L52";
  @"L50":
    %"chk0" : A = (Check 0 1 Read 1) %"pr.2";
    %"v59" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v60" : W = (Ext Ub) %"v59";
    %"chk1" : A = (Check 0 4 Write 1) %"pr.1";
    store Ww [%"chk1" + 0] <- %"v60"
    => goto "L52";
  @"L52":
    => ret #1;
  @"L32":
    => ret %"v29"
} }.

Definition hello_image_fn_rpl_mbrtowc : func :=
  ir_fn{ "export" "rpl_mbrtowc"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v8" : P = (Alloc 4) #4;
    %"v13" : L = Ptoi %"v0";
    %"v15" : W = (Cmp Eq L) %"v13", #0
    => br %"v15" ? "L11" : "L10";
  @"L10":
    => goto "L11";
  @"L11" [%"pr.1" : P = phi("L10" => %"v0", "start" => %"v8")]:
    call %"v21" : L = $"mbrtowc"(P %"pr.1", P %"v2", L %"v4", P %"v6");
    %"v28" : W = (Cmp Uge L) %"v21", #18446744073709551614
    => br %"v28" ? "L29" : "L30";
  @"L29":
    %"v32" : W = (Cmp Ne L) %"v4", #0
    => goto "L30";
  @"L30" [%"v34" : W = phi("L11" => #0, "L29" => %"v32")]:
    => br %"v34" ? "L35" : "L36";
  @"L35":
    call %"v37" : W = $"hard_locale"(W #0);
    %"v38" : W = (Ext Ub) %"v37";
    %"v39" : W = (Cmp Eq W) %"v38", #0
    => goto "L36";
  @"L36" [%"v41" : W = phi("L30" => #0, "L35" => %"v39")]:
    => br %"v41" ? "L22" : "L24";
  @"L22":
    %"chk0" : A = (Check 0 1 Read 1) %"v2";
    %"v44" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v45" : W = (Ext Ub) %"v44";
    %"chk1" : A = (Check 0 4 Write 1) %"pr.1";
    store Ww [%"chk1" + 0] <- %"v45"
    => ret #1;
  @"L24":
    => ret %"v21"
} }.

Definition hello_image_fn_rpl_mbsrtowcs : func :=
  ir_fn{ "export" "rpl_mbsrtowcs"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v130" : P = (Alloc 4) #8;
    %"v12" : L = Ptoi %"v6";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    %"v15" : P = Copy $"_gl_mbsrtowcs_state"
    => goto "L10";
  @"L10" [%"pr.2" : P = phi("L8" => %"v15", "start" => %"v6")]:
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v23" : L = Ptoi %"v0";
    %"v25" : W = (Cmp Ne L) %"v23", %"v13"
    => br %"v25" ? "L28" : "L20";
  @"L28" [%"pr.7" : P = phi("L102" => %"v118", "L10" => %"v0"); %"pr.5" : P = phi("L102" => %"v116", "L10" => %"v18"); %"pr.1" : L = phi("L102" => %"v120", "L10" => %"v4")]:
    %"v33" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v33" ? "L29" : "L31";
  @"L29":
    %"chk1" : A = (Check 0 1 Read 1) %"pr.5";
    %"v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v41" : W = (Cmp Eq W) %"v40", #0
    => br %"v41" ? "L37" : "L36";
  @"L36":
    %"v46" = %"pr.5" +p #1;
    %"chk2" : A = (HalfCheck Upper 0 1 Read 1) %"chk1", %"v46";
    %"v47" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v48" : W = (Cmp Eq W) %"v47", #0
    => br %"v48" ? "L37" : "L43";
  @"L43":
    %"v53" = %"pr.5" +p #2;
    %"chk3" : A = (HalfCheck Upper 0 1 Read 1) %"chk1", %"v53";
    %"v54" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v55" : W = (Cmp Eq W) %"v54", #0
    => br %"v55" ? "L37" : "L60";
  @"L60":
    %"v63" = %"pr.5" +p #3;
    %"chk4" : A = (HalfCheck Upper 0 1 Read 1) %"chk1", %"v63";
    %"v64" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v65" : W = (Cmp Eq W) %"v64", #0
    => br %"v65" ? "L37" : "L57";
  @"L57":
    %"v69" = %"pr.5" +p #4;
    call %"v72" : L = $"strnlen1"(P %"v69", L #12);
    %"v73" : L = Add %"v72", #4
    => goto "L37";
  @"L37" [%"pr.8" : L = phi("L29" => #1, "L36" => #2, "L43" => #3, "L57" => %"v73", "L60" => #4)]:
    call %"v79" : L = $"rpl_mbrtowc"(P %"pr.7", P %"pr.5", L %"pr.8", P %"pr.2");
    %"v86" : W = (Cmp Eq L) %"v79", #18446744073709551614
    => br %"v86" ? "L80" : "L82";
  @"L80":
    call void $"abort"()
    => goto "L82";
  @"L82":
    %"v93" : W = (Cmp Eq L) %"v79", #18446744073709551615
    => br %"v93" ? "L94" : "L89";
  @"L89":
    %"v100" : W = (Cmp Eq L) %"v79", #0
    => br %"v100" ? "L31" : "L102";
  @"L102":
    %"v116" = %"pr.5" +p %"v79";
    %"v118" = %"pr.7" +p #4;
    %"v120" : L = Sub %"pr.1", #1
    => goto poll "L28";
  @"L31" [%"pr.6" : P = phi("L28" => %"pr.5", "L89" => #0)]:
    %"chk5" : A = (Renew 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk5" + 0] <- %"pr.6";
    %"v125" : L = Ptoi %"pr.7";
    %"v127" : L = Sub %"v125", %"v23";
    %"v128" : L = Div %"v127", #4
    => ret %"v128";
  @"L20":
    %"chk6" : A = (Check 0 8 Read 1) %"pr.2";
    %"v132" : L = (RawLoad LdL 0) %"chk6";
    %"chk7" : A = (Check 0 8 Write 1) %"v130";
    store Wl [%"chk7" + 0] <- %"v132"
    => goto "L134";
  @"L134" [%"pr.12" : L = phi("L200" => %"v208", "L20" => #0); %"pr.4" : P = phi("L200" => %"v206", "L20" => %"v18")]:
    %"chk8" : A = (Check 0 1 Read 1) %"pr.4";
    %"v144" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v145" : W = (Cmp Eq W) %"v144", #0
    => br %"v145" ? "L141" : "L140";
  @"L140":
    %"v150" = %"pr.4" +p #1;
    %"chk9" : A = (HalfCheck Upper 0 1 Read 1) %"chk8", %"v150";
    %"v151" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"v152" : W = (Cmp Eq W) %"v151", #0
    => br %"v152" ? "L141" : "L147";
  @"L147":
    %"v157" = %"pr.4" +p #2;
    %"chk10" : A = (HalfCheck Upper 0 1 Read 1) %"chk8", %"v157";
    %"v158" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"v159" : W = (Cmp Eq W) %"v158", #0
    => br %"v159" ? "L141" : "L164";
  @"L164":
    %"v167" = %"pr.4" +p #3;
    %"chk11" : A = (HalfCheck Upper 0 1 Read 1) %"chk8", %"v167";
    %"v168" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"v169" : W = (Cmp Eq W) %"v168", #0
    => br %"v169" ? "L141" : "L161";
  @"L161":
    %"v173" = %"pr.4" +p #4;
    call %"v176" : L = $"strnlen1"(P %"v173", L #12);
    %"v177" : L = Add %"v176", #4
    => goto "L141";
  @"L141" [%"pr.13" : L = phi("L134" => #1, "L140" => #2, "L147" => #3, "L161" => %"v177", "L164" => #4)]:
    call %"v181" : L = $"rpl_mbrtowc"(P #0, P %"pr.4", L %"pr.13", P %"v130");
    %"v188" : W = (Cmp Eq L) %"v181", #18446744073709551614
    => br %"v188" ? "L182" : "L184";
  @"L182":
    call void $"abort"()
    => goto "L184";
  @"L184":
    %"v195" : W = (Cmp Eq L) %"v181", #18446744073709551615
    => br %"v195" ? "L196" : "L191";
  @"L191":
    %"v202" : W = (Cmp Eq L) %"v181", #0
    => br %"v202" ? "L137" : "L200";
  @"L200":
    %"v206" = %"pr.4" +p %"v181";
    %"v208" : L = Add %"pr.12", #1
    => goto poll "L134";
  @"L137":
    => ret %"pr.12";
  @"L94":
    %"chk12" : A = (Renew 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk12" + 0] <- %"pr.5"
    => goto "L196";
  @"L196":
    call %"v212" : P = $"__errno_location"();
    %"chk13" : A = (Check 0 4 Write 1) %"v212";
    store Ww [%"chk13" + 0] <- #84
    => ret #18446744073709551615
} }.
