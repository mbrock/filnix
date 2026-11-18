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

Definition hello_image_fn___correctly_grouped_prefixmb : func :=
  ir_fn{ "export" "__correctly_grouped_prefixmb"(P %"v0", P %"v2", P %"v4", P %"v6") -> (RClass P) {
  @"start":
    %"v12" : L = Ptoi %"v6";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    => ret %"v2";
  @"L10":
    call %"v19" : L = $"__GI_strlen"(P %"v4")
    => goto "L20";
  @"L20" [%"pr.1" : P = phi("L10" => %"v2", "L204" => %"pr.7", "L221" => %"v241", "L222" => %"pr.7")]:
    %"v25" : L = Ptoi %"pr.1";
    %"v26" : L = Ptoi %"v0";
    %"v27" : L = Sub %"v25", %"v26";
    %"v29" : W = (Cmp Uge L) %"v27", %"v19"
    => br %"v29" ? "L21" : "L22";
  @"L21":
    (Flight (a "v33") Sub [(FAddress (t "pr.1")); (FValue (t "v19"))] (LowerOf (t "pr.1")))
    => goto "L36";
  @"L36" [%"pr.7" : P = phi("L21" => %"v33", "L46" => %"v54")]:
    %"v41" : L = Ptoi %"pr.7";
    %"v43" : W = (Cmp Uge L) %"v41", %"v26"
    => br %"v43" ? "L37" : "L38";
  @"L37":
    call %"v50" : W = $"__GI_memcmp"(P %"pr.7", P %"v4", L %"v19");
    %"v51" : W = (Cmp Eq W) %"v50", #0
    => br %"v51" ? "L38" : "L46";
  @"L46":
    (Flight (a "v54") Sub [(FAddress (t "pr.7")); (FValue (Const 1))] (LowerOf (t "pr.7")))
    => goto poll "L36";
  @"L38":
    %"v62" : W = (Cmp Ult L) %"v41", %"v26"
    => br %"v62" ? "L55" : "L57";
  @"L55":
    => ret %"pr.1";
  @"L57":
    %"v72" : L = Sub %"v25", %"v41";
    %"chk0" : A = (Check 0 1 Read 1) %"v6";
    %"v74" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v76" : L = (Ext Sw) %"v74";
    %"v77" : L = Add %"v76", %"v19";
    %"v78" : W = (Cmp Eq L) %"v72", %"v77"
    => br %"v78" ? "L65" : "L66";
  @"L65":
    => br %"v62" ? "L80" : "L91";
  @"L80":
    => ret %"pr.1";
  @"L91" [%"pr.9" : P = phi("L65" => %"v6", "L121" => %"pr.10", "L204" => %"pr.10"); %"pr.8" : P = phi("L65" => %"pr.7", "L121" => %"pr.5", "L204" => %"pr.6")]:
    %"v95" = %"pr.9" +p #1;
    %"chk1" : A = (Check 0 1 Read 1) %"v95";
    %"v100" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v101" : W = (Cmp Eq W) %"v100", #0
    => br %"v101" ? "L96" : "L98";
  @"L96":
    (Flight (a "v103") Sub [(FAddress (t "v95")); (FValue (Const 1))] (LowerOf (t "v95")))
    => goto "L98";
  @"L98" [%"pr.10" : P = phi("L96" => %"v103", "L91" => %"v95")]:
    (Flight (a "v105") Sub [(FAddress (t "pr.8")); (FValue (Const 1))] (LowerOf (t "pr.8")));
    %"chk2" : A = (Check 0 1 Read 1) %"pr.10";
    %"v110" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v111" : W = (Cmp Eq W) %"v110", #127
    => br %"v111" ? "L113" : "L112";
  @"L112":
    %"v115" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v116" : W = (Cmp Slt W) %"v115", #0
    => goto "L113";
  @"L113" [%"v118" : W = phi("L98" => #1, "L112" => %"v116")]:
    => br %"v118" ? "L119" : "L150";
  @"L119" [%"pr.5" : P = phi("L129" => %"v137", "L113" => %"v105")]:
    %"v124" : L = Ptoi %"pr.5";
    %"v126" : W = (Cmp Uge L) %"v124", %"v26"
    => br %"v126" ? "L120" : "L121";
  @"L120":
    call %"v133" : W = $"__GI_memcmp"(P %"pr.5", P %"v4", L %"v19");
    %"v134" : W = (Cmp Eq W) %"v133", #0
    => br %"v134" ? "L121" : "L129";
  @"L129":
    (Flight (a "v137") Sub [(FAddress (t "pr.5")); (FValue (Const 1))] (LowerOf (t "pr.5")))
    => goto poll "L119";
  @"L121":
    %"v145" : W = (Cmp Ult L) %"v124", %"v26"
    => br %"v145" ? "L138" : poll "L91";
  @"L138":
    => ret %"pr.1";
  @"L150" [%"pr.6" : P = phi("L160" => %"v168", "L113" => %"v105")]:
    %"v155" : L = Ptoi %"pr.6";
    %"v157" : W = (Cmp Uge L) %"v155", %"v26"
    => br %"v157" ? "L151" : "L152";
  @"L151":
    call %"v164" : W = $"__GI_memcmp"(P %"pr.6", P %"v4", L %"v19");
    %"v165" : W = (Cmp Eq W) %"v164", #0
    => br %"v165" ? "L152" : "L160";
  @"L160":
    (Flight (a "v168") Sub [(FAddress (t "pr.6")); (FValue (Const 1))] (LowerOf (t "pr.6")))
    => goto poll "L150";
  @"L152":
    %"v176" : W = (Cmp Ult L) %"v155", %"v26"
    => br %"v176" ? "L177" : "L178";
  @"L177":
    %"v181" : L = Ptoi %"v105";
    %"v183" : L = Sub %"v181", %"v155";
    %"chk4" : A = (Renew 0 1 Read 1) %"chk2", %"pr.10";
    %"v185" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v187" : L = (Ext Sw) %"v185";
    %"v188" : L = Add %"v187", %"v19";
    %"v189" : L = Sub %"v188", #1;
    %"v190" : W = (Cmp Ule L) %"v183", %"v189"
    => goto "L178";
  @"L178" [%"v192" : W = phi("L152" => #0, "L177" => %"v190")]:
    => br %"v192" ? "L169" : "L171";
  @"L169":
    => ret %"pr.1";
  @"L171":
    => br %"v176" ? "L204" : "L203";
  @"L203":
    %"v207" : L = Ptoi %"v105";
    %"v209" : L = Sub %"v207", %"v155";
    %"chk5" : A = (Renew 0 1 Read 1) %"chk2", %"pr.10";
    %"v211" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v213" : L = (Ext Sw) %"v211";
    %"v214" : L = Add %"v213", %"v19";
    %"v215" : L = Sub %"v214", #1;
    %"v216" : W = (Cmp Ne L) %"v209", %"v215"
    => goto "L204";
  @"L204" [%"v218" : W = phi("L171" => #1, "L203" => %"v216")]:
    => br %"v218" ? poll "L20" : poll "L91";
  @"L66":
    %"v230" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v232" : L = (Ext Sw) %"v230";
    %"v233" : L = Add %"v232", %"v19";
    %"v234" : W = (Cmp Ugt L) %"v72", %"v233"
    => br %"v234" ? "L221" : "L222";
  @"L221":
    %"v237" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v238" : L = (Ext Sw) %"v237";
    %"v239" = %"pr.7" +p %"v238";
    %"v241" = %"v239" +p %"v19"
    => goto poll "L20";
  @"L222":
    => br %"v62" ? "L242" : poll "L20";
  @"L242":
    => ret %"pr.1";
  @"L22":
    %"v264" : W = (Cmp Ugt L) %"v26", %"v25"
    => br %"v264" ? "L259" : "L258";
  @"L258":
    => goto "L259";
  @"L259" [%"v267" : P = phi("L258" => %"pr.1", "L22" => %"v0")]:
    => ret %"v267"
} }.
