(** This file defines checked IR from glibc’s `intl/finddomain.os` object.
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

Definition fn__nl_find_domain : func :=
  ir_fn{ "export" "_nl_find_domain"(P %"v0", P %"v2", P %"v4", P %"v6") -> (RClass P) {
  @"start":
    %"v9" : P = (Alloc 8) #8;
    %"v10" : P = (Alloc 8) #8;
    %"v11" : P = (Alloc 8) #8;
    %"v12" : P = (Alloc 8) #8;
    %"v13" : P = (Alloc 8) #8;
    %"v16" : P = Copy $"glibc_finddomain#_nl_find_domain.lock.265";
    call %"v17" : W = $"__GI___pthread_rwlock_rdlock"(P %"v16");
    %"v18" : P = Copy $"glibc_finddomain#_nl_loaded_domains";
    call %"v21" : L = $"__GI_strlen"(P %"v0");
    %"v22" : L = Add %"v21", #1;
    call %"v25" : P = $"_nl_make_l10nflist"(P %"v18", P %"v0", L %"v22", W #0, P %"v2", P #0, P #0, P #0, P #0, P %"v4", W #0);
    %"v26" : P = Copy $"glibc_finddomain#_nl_find_domain.lock.265";
    call %"v27" : W = $"__GI___pthread_rwlock_unlock"(P %"v26");
    %"v32" : L = Ptoi %"v25";
    %"v33" : L = Ptoi #0;
    %"v34" : W = (Cmp Ne L) %"v32", %"v33"
    => br %"v34" ? "L28" : "L30";
  @"L28":
    %"v40" = %"v25" +p #8;
    %"chk0" : A = (Check 0 4 Read 1) %"v40";
    %"v41" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v42" : W = (Cmp Sle W) %"v41", #0
    => br %"v42" ? "L36" : "L38";
  @"L36":
    call void $"_nl_load_domain"(P %"v25", P %"v6")
    => goto "L38";
  @"L38":
    %"v49" = %"v25" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v51" : L = Ptoi %"v50";
    %"v53" : W = (Cmp Ne L) %"v51", %"v33"
    => br %"v53" ? "L45" : "L56";
  @"L45":
    => ret %"v25";
  @"L56" [%"pr.3" : W = phi("L58" => %"v108", "L38" => #0)]:
    %"v61" = %"v25" +p #32;
    %"v63" : L = (Ext Sw) %"pr.3";
    %"v64" : L = Shl %"v63", #3;
    %"v65" = %"v61" +p %"v64";
    %"chk2" : A = (Check 0 8 Read 8) %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v67" : L = Ptoi %"v66";
    %"v69" : W = (Cmp Ne L) %"v67", %"v33"
    => br %"v69" ? "L57" : "L59";
  @"L57":
    %"v74" = %"v25" +p #32;
    %"v78" = %"v74" +p %"v64";
    %"chk3" : A = (Check 0 8 Read 8) %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v80" = %"v79" +p #8;
    %"chk4" : A = (Check 0 4 Read 1) %"v80";
    %"v81" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v82" : W = (Cmp Sle W) %"v81", #0
    => br %"v82" ? "L70" : "L72";
  @"L70":
    %"v84" = %"v25" +p #32;
    %"v88" = %"v84" +p %"v64";
    %"chk5" : A = (Check 0 8 Read 8) %"v88";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call void $"_nl_load_domain"(P %"v89", P %"v6")
    => goto "L72";
  @"L72":
    %"v95" = %"v25" +p #32;
    %"v99" = %"v95" +p %"v64";
    %"chk6" : A = (Check 0 8 Read 8) %"v99";
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v101" = %"v100" +p #16;
    %"chk7" : A = (Check 0 8 Read 8) %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v103" : L = Ptoi %"v102";
    %"v105" : W = (Cmp Ne L) %"v103", %"v33"
    => br %"v105" ? "L59" : "L58";
  @"L58":
    %"v108" : W = Add %"pr.3", #1
    => goto poll "L56";
  @"L59":
    => ret %"v25";
  @"L30":
    call %"v112" : P = $"_nl_expand_alias"(P %"v2");
    %"v117" : L = Ptoi %"v112";
    %"v119" : W = (Cmp Ne L) %"v117", %"v33"
    => br %"v119" ? "L113" : "L115";
  @"L113":
    call %"v122" : L = $"__GI_strlen"(P %"v112");
    %"v123" : L = Add %"v122", #1;
    call %"v125" : P = $"malloc"(L %"v123");
    %"v130" : L = Ptoi %"v125";
    %"v132" : W = (Cmp Eq L) %"v130", %"v33"
    => br %"v132" ? "L126" : "L128";
  @"L126":
    => ret #0;
  @"L128":
    call %"v137" : P = $"__GI_memcpy"(P %"v125", P %"v112", L %"v123")
    => goto "L115";
  @"L115" [%"pr.1" : P = phi("L128" => %"v125", "L30" => %"v2")]:
    call %"v139" : W = $"_nl_explode_name"(P %"pr.1", P %"v9", P %"v10", P %"v11", P %"v12", P %"v13");
    %"v145" : W = (Cmp Ne W) %"v139", #4294967295
    => br %"v145" ? "L140" : "L142";
  @"L140":
    %"v146" : P = Copy $"glibc_finddomain#_nl_find_domain.lock.265";
    call %"v147" : W = $"__GI___pthread_rwlock_wrlock"(P %"v146");
    %"v148" : P = Copy $"glibc_finddomain#_nl_loaded_domains";
    call %"v151" : L = $"__GI_strlen"(P %"v0");
    %"v152" : L = Add %"v151", #1;
    %"chk8" : A = (Check 0 8 Read 8) %"v9";
    %"v154" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"v11";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 8 Read 8) %"v12";
    %"v156" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Read 8) %"v13";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 8 Read 8) %"v10";
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk12";
    call %"v160" : P = $"_nl_make_l10nflist"(P %"v148", P %"v0", L %"v152", W %"v139", P %"v154", P %"v155", P %"v156", P %"v157", P %"v158", P %"v4", W #1);
    %"v161" : P = Copy $"glibc_finddomain#_nl_find_domain.lock.265";
    call %"v162" : W = $"__GI___pthread_rwlock_unlock"(P %"v161");
    %"v167" : L = Ptoi %"v160";
    %"v169" : W = (Cmp Ne L) %"v167", %"v33"
    => br %"v169" ? "L163" : "L165";
  @"L163":
    %"v174" = %"v160" +p #8;
    %"chk13" : A = (Check 0 4 Read 1) %"v174";
    %"v175" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v176" : W = (Cmp Sle W) %"v175", #0
    => br %"v176" ? "L170" : "L172";
  @"L170":
    call void $"_nl_load_domain"(P %"v160", P %"v6")
    => goto "L172";
  @"L172":
    %"v183" = %"v160" +p #16;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v183";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v185" : L = Ptoi %"v184";
    %"v187" : W = (Cmp Eq L) %"v185", %"v33"
    => br %"v187" ? "L189" : "L165";
  @"L189" [%"pr.4" : W = phi("L191" => %"v241", "L172" => #0)]:
    %"v194" = %"v160" +p #32;
    %"v196" : L = (Ext Sw) %"pr.4";
    %"v197" : L = Shl %"v196", #3;
    %"v198" = %"v194" +p %"v197";
    %"chk15" : A = (Check 0 8 Read 8) %"v198";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v200" : L = Ptoi %"v199";
    %"v202" : W = (Cmp Ne L) %"v200", %"v33"
    => br %"v202" ? "L190" : "L165";
  @"L190":
    %"v207" = %"v160" +p #32;
    %"v211" = %"v207" +p %"v197";
    %"chk16" : A = (Check 0 8 Read 8) %"v211";
    %"v212" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v213" = %"v212" +p #8;
    %"chk17" : A = (Check 0 4 Read 1) %"v213";
    %"v214" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v215" : W = (Cmp Sle W) %"v214", #0
    => br %"v215" ? "L203" : "L205";
  @"L203":
    %"v217" = %"v160" +p #32;
    %"v221" = %"v217" +p %"v197";
    %"chk18" : A = (Check 0 8 Read 8) %"v221";
    %"v222" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call void $"_nl_load_domain"(P %"v222", P %"v6")
    => goto "L205";
  @"L205":
    %"v228" = %"v160" +p #32;
    %"v232" = %"v228" +p %"v197";
    %"chk19" : A = (Check 0 8 Read 8) %"v232";
    %"v233" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v234" = %"v233" +p #16;
    %"chk20" : A = (Check 0 8 Read 8) %"v234";
    %"v235" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v236" : L = Ptoi %"v235";
    %"v238" : W = (Cmp Ne L) %"v236", %"v33"
    => br %"v238" ? "L165" : "L191";
  @"L191":
    %"v241" : W = Add %"pr.4", #1
    => goto poll "L189";
  @"L165":
    %"v246" : W = And %"v139", #1
    => br %"v246" ? "L242" : "L142";
  @"L242":
    %"chk21" : A = (Renew 0 8 Read 8) %"chk11", %"v13";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call void $"free"(P %"v247")
    => goto "L142";
  @"L142" [%"pr.2" : P = phi("L242" => %"v160", "L165" => %"v160", "L115" => %"v25")]:
    => br %"v119" ? "L248" : "L250";
  @"L248":
    call void $"free"(P %"pr.1")
    => goto "L250";
  @"L250":
    => ret %"pr.2"
} }.

Definition item_glibc_finddomain'23_nl_find_domain'2elock'2e265 : item :=
  (IData (a "glibc_finddomain#_nl_find_domain.lock.265") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4)]).

Definition item_glibc_finddomain'23_nl_loaded_domains : item :=
  (IData (a "glibc_finddomain#_nl_loaded_domains") LLocal 8 [(Zero 8)]).
