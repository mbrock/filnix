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

Definition hello_image_fn_glibc_dcigettext'23plural_eval_recurse : func :=
  ir_fn{ "local" "glibc_dcigettext#plural_eval_recurse"(P %"v0", L %"v2", W %"v4") -> (RTuple [L; L]) blocks ((app [ir_blk{ @"start":
    %"v10" : W = (Cmp Eq W) %"v4", #0
    => br %"v10" ? "L6" : "L8" };
  ir_blk{ @"L6":
    => (JRets [(Const 3); (Const 0)]) };
  ir_blk{ @"L8":
    %"v18" : W = Sub %"v4", #1;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v505" : W = (Cmp Eq W) %"v20", #0
    => br %"v505" ? "L23" : "L506" };
  ir_blk{ @"L23":
    %"v25" = %"v0" +p #4;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v25";
    %"v26" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v49" : W = (Cmp Eq W) %"v26", #0
    => br %"v49" ? "L29" : "L50" };
  ir_blk{ @"L29":
    => (JRets [(Const 0); (t "v2")]) };
  ir_blk{ @"L37":
    %"v42" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v42";
    %"v43" : L = (RawLoad LdL 0) %"chk2"
    => (JRets [(Const 0); (t "v43")]) };
  ir_blk{ @"L50":
    %"v51" : W = (Cmp Eq W) %"v26", #1
    => br %"v51" ? poll "L37" : "L22" };
  ir_blk{ @"L53":
    %"v56" = %"v0" +p #8;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v56";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk3";
    (Call (CTuple [((a "v62"), L); ((a "v63"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v58")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.18" : L = Shr %"v62", #32;
    %"v72" : W = Copy %"v62";
    %"v73" : W = (Cmp Ne W) %"v72", #0
    => br %"v73" ? "L69" : "L71" };
  ir_blk{ @"L69":
    %"sw.20" : L = (Ext Uw) %"v62";
    %"sw.22" : L = (Ext Uw) %"sw.18";
    %"sw.23" : L = Shl %"sw.22", #32;
    %"v74" : L = Or %"sw.23", %"sw.20"
    => (JRets [(t "v74"); (t "v63")]) };
  ir_blk{ @"L71":
    %"v84" : W = (Cmp Eq L) %"v63", #0;
    %"v85" : L = (Ext Sw) %"v84"
    => (JRets [(Const 0); (t "v85")]) };
  ir_blk{ @"L89":
    %"v92" = %"v0" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v92";
    %"v94" : P = (RawLoadPointer 0 load_effects) %"chk4";
    (Call (CTuple [((a "v98"), L); ((a "v99"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v94")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.30" : L = Shr %"v98", #32;
    %"v108" : W = Copy %"v98";
    %"v109" : W = (Cmp Ne W) %"v108", #0
    => br %"v109" ? "L105" : "L107" };
  ir_blk{ @"L105":
    %"sw.32" : L = (Ext Uw) %"v98";
    %"sw.34" : L = (Ext Uw) %"sw.30";
    %"sw.35" : L = Shl %"sw.34", #32;
    %"v110" : L = Or %"sw.35", %"sw.32"
    => (JRets [(t "v110"); (t "v99")]) };
  ir_blk{ @"L107":
    %"v118" = %"v0" +p #4;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v118";
    %"v119" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v120" : W = (Cmp Eq W) %"v119", #15
    => br %"v120" ? "L114" : "L115" };
  ir_blk{ @"L114":
    %"v126" : W = (Cmp Ne L) %"v99", #0
    => br %"v126" ? "L121" : "L123" };
  ir_blk{ @"L121":
    => (JRets [(Const 0); (Const 1)]) };
  ir_blk{ @"L123":
    %"v136" = %"v0" +p #8;
    %"v137" = %"v136" +p #8;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk6";
    (Call (CTuple [((a "v142"), L); ((a "v143"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v138")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.42" : L = Shr %"v142", #32;
    %"v152" : W = Copy %"v142";
    %"v153" : W = (Cmp Ne W) %"v152", #0
    => br %"v153" ? "L149" : "L151" };
  ir_blk{ @"L149":
    %"sw.44" : L = (Ext Uw) %"v142";
    %"sw.46" : L = (Ext Uw) %"sw.42";
    %"sw.47" : L = Shl %"sw.46", #32;
    %"v154" : L = Or %"sw.47", %"sw.44"
    => (JRets [(t "v154"); (t "v143")]) };
  ir_blk{ @"L151":
    %"v166" : W = (Cmp Ne L) %"v143", #0
    => br %"v166" ? "L163" : "L162" };
  ir_blk{ @"L162":
    => goto "L163" };
  ir_blk{ @"L163" [%"v167" : W = phi("L162" => #0, "L151" => #1)]:
    %"v168" : L = (Ext Sw) %"v167"
    => (JRets [(Const 0); (t "v168")]) };
  ir_blk{ @"L115":
    %"v177" = %"v0" +p #4;
    %"v178" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v179" : W = (Cmp Eq W) %"v178", #14
    => br %"v179" ? "L173" : "L174" };
  ir_blk{ @"L173":
    %"v186" : W = (Cmp Eq L) %"v99", #0
    => br %"v186" ? "L180" : "L182" };
  ir_blk{ @"L180":
    => (JRets [(Const 0); (Const 0)]) };
  ir_blk{ @"L182":
    %"v196" = %"v0" +p #8;
    %"v197" = %"v196" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v197";
    %"v198" : P = (RawLoadPointer 0 load_effects) %"chk8";
    (Call (CTuple [((a "v202"), L); ((a "v203"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v198")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.60" : L = Shr %"v202", #32;
    %"v212" : W = Copy %"v202";
    %"v213" : W = (Cmp Ne W) %"v212", #0
    => br %"v213" ? "L209" : "L211" };
  ir_blk{ @"L209":
    %"sw.62" : L = (Ext Uw) %"v202";
    %"sw.64" : L = (Ext Uw) %"sw.60";
    %"sw.65" : L = Shl %"sw.64", #32;
    %"v214" : L = Or %"sw.65", %"sw.62"
    => (JRets [(t "v214"); (t "v203")]) };
  ir_blk{ @"L211":
    %"v226" : W = (Cmp Ne L) %"v203", #0
    => br %"v226" ? "L223" : "L222" };
  ir_blk{ @"L222":
    => goto "L223" };
  ir_blk{ @"L223" [%"v227" : W = phi("L222" => #0, "L211" => #1)]:
    %"v228" : L = (Ext Sw) %"v227"
    => (JRets [(Const 0); (t "v228")]) };
  ir_blk{ @"L174":
    %"v235" = %"v0" +p #8;
    %"v236" = %"v235" +p #8;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v236";
    %"v237" : P = (RawLoadPointer 0 load_effects) %"chk9";
    (Call (CTuple [((a "v241"), L); ((a "v242"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v237")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.72" : L = Shr %"v241", #32;
    %"v251" : W = Copy %"v241";
    %"v252" : W = (Cmp Ne W) %"v251", #0
    => br %"v252" ? "L248" : "L250" };
  ir_blk{ @"L248":
    %"sw.74" : L = (Ext Uw) %"v241";
    %"sw.76" : L = (Ext Uw) %"sw.72";
    %"sw.77" : L = Shl %"sw.76", #32;
    %"v253" : L = Or %"sw.77", %"sw.74"
    => (JRets [(t "v253"); (t "v242")]) };
  ir_blk{ @"L250":
    %"v258" = %"v0" +p #4;
    %"chk10" : A = (Renew 0 4 Read 1) %"chk5", %"v258";
    %"v259" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"v426" : W = (Cmp Ult W) %"v259", #8
    => br %"v426" ? "L427" : "L428" };
  ir_blk{ @"L262":
    %"v270" : L = Mul %"v99", %"v242"
    => (JRets [(Const 0); (t "v270")]) };
  ir_blk{ @"L274":
    %"v280" : W = (Cmp Eq L) %"v242", #0
    => br %"v280" ? "L275" : "L277" };
  ir_blk{ @"L275":
    => (JRets [(Const 1); (Const 0)]) }] [ir_blk{ @"L277":
    %"v294" : L = Udiv %"v99", %"v242"
    => (JRets [(Const 0); (t "v294")]) };
  ir_blk{ @"L298":
    %"v304" : W = (Cmp Eq L) %"v242", #0
    => br %"v304" ? "L299" : "L301" };
  ir_blk{ @"L299":
    => (JRets [(Const 1); (Const 0)]) };
  ir_blk{ @"L301":
    %"v318" : L = Urem %"v99", %"v242"
    => (JRets [(Const 0); (t "v318")]) };
  ir_blk{ @"L322":
    %"v330" : L = Add %"v99", %"v242"
    => (JRets [(Const 0); (t "v330")]) };
  ir_blk{ @"L334":
    %"v342" : L = Sub %"v99", %"v242"
    => (JRets [(Const 0); (t "v342")]) };
  ir_blk{ @"L346":
    %"v354" : W = (Cmp Ult L) %"v99", %"v242";
    %"v355" : L = (Ext Sw) %"v354"
    => (JRets [(Const 0); (t "v355")]) };
  ir_blk{ @"L359":
    %"v367" : W = (Cmp Ugt L) %"v99", %"v242";
    %"v368" : L = (Ext Sw) %"v367"
    => (JRets [(Const 0); (t "v368")]) };
  ir_blk{ @"L372":
    %"v380" : W = (Cmp Ule L) %"v99", %"v242";
    %"v381" : L = (Ext Sw) %"v380"
    => (JRets [(Const 0); (t "v381")]) };
  ir_blk{ @"L385":
    %"v393" : W = (Cmp Uge L) %"v99", %"v242";
    %"v394" : L = (Ext Sw) %"v393"
    => (JRets [(Const 0); (t "v394")]) };
  ir_blk{ @"L398":
    %"v406" : W = (Cmp Eq L) %"v99", %"v242";
    %"v407" : L = (Ext Sw) %"v406"
    => (JRets [(Const 0); (t "v407")]) };
  ir_blk{ @"L411":
    %"v419" : W = (Cmp Ne L) %"v99", %"v242";
    %"v420" : L = (Ext Sw) %"v419"
    => (JRets [(Const 0); (t "v420")]) };
  ir_blk{ @"L427":
    %"v429" : W = (Cmp Ult W) %"v259", #5
    => br %"v429" ? "L430" : "L431" };
  ir_blk{ @"L430":
    %"v432" : W = (Cmp Eq W) %"v259", #3
    => br %"v432" ? poll "L262" : "L433" };
  ir_blk{ @"L433":
    %"v434" : W = (Cmp Eq W) %"v259", #4
    => br %"v434" ? poll "L274" : "L22" };
  ir_blk{ @"L431":
    %"v436" : W = (Cmp Eq W) %"v259", #5
    => br %"v436" ? poll "L298" : "L437" };
  ir_blk{ @"L437":
    %"v438" : W = (Cmp Eq W) %"v259", #6
    => br %"v438" ? poll "L322" : "L439" };
  ir_blk{ @"L439":
    %"v440" : W = (Cmp Eq W) %"v259", #7
    => br %"v440" ? poll "L334" : "L22" };
  ir_blk{ @"L428":
    %"v442" : W = (Cmp Ult W) %"v259", #11
    => br %"v442" ? "L443" : "L444" };
  ir_blk{ @"L443":
    %"v445" : W = (Cmp Eq W) %"v259", #8
    => br %"v445" ? poll "L346" : "L446" };
  ir_blk{ @"L446":
    %"v447" : W = (Cmp Eq W) %"v259", #9
    => br %"v447" ? poll "L359" : "L448" };
  ir_blk{ @"L448":
    %"v449" : W = (Cmp Eq W) %"v259", #10
    => br %"v449" ? poll "L372" : "L22" };
  ir_blk{ @"L444":
    %"v451" : W = (Cmp Eq W) %"v259", #11
    => br %"v451" ? poll "L385" : "L452" };
  ir_blk{ @"L452":
    %"v453" : W = (Cmp Eq W) %"v259", #12
    => br %"v453" ? poll "L398" : "L454" };
  ir_blk{ @"L454":
    %"v455" : W = (Cmp Eq W) %"v259", #13
    => br %"v455" ? poll "L411" : "L22" };
  ir_blk{ @"L457":
    %"v460" = %"v0" +p #8;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v460";
    %"v462" : P = (RawLoadPointer 0 load_effects) %"chk11";
    (Call (CTuple [((a "v466"), L); ((a "v467"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v462")); (Arg L (t "v2")); (Arg W (t "v18"))]);
    %"sw.156" : L = Shr %"v466", #32;
    %"v476" : W = Copy %"v466";
    %"v477" : W = (Cmp Ne W) %"v476", #0
    => br %"v477" ? "L473" : "L475" };
  ir_blk{ @"L473":
    %"sw.158" : L = (Ext Uw) %"v466";
    %"sw.160" : L = (Ext Uw) %"sw.156";
    %"sw.161" : L = Shl %"sw.160", #32;
    %"v478" : L = Or %"sw.161", %"sw.158"
    => (JRets [(t "v478"); (t "v467")]) };
  ir_blk{ @"L475":
    %"v483" = %"v0" +p #8;
    %"v489" : W = (Cmp Ne L) %"v467", #0
    => br %"v489" ? "L486" : "L485" };
  ir_blk{ @"L485":
    => goto "L486" };
  ir_blk{ @"L486" [%"v490" : W = phi("L485" => #2, "L475" => #1)]:
    %"v491" : L = (Ext Sw) %"v490";
    %"v492" : L = Shl %"v491", #3;
    %"v493" = %"v483" +p %"v492";
    %"chk12" : A = (Check 0 8 Read 8) %"v493";
    %"v494" : P = (RawLoadPointer 0 load_effects) %"chk12";
    (Call (CTuple [((a "v498"), L); ((a "v499"), L)]) (Global (a "glibc_dcigettext#plural_eval_recurse")) [(Arg P (t "v494")); (Arg L (t "v2")); (Arg W (t "v18"))])
    => (JRets [(t "v498"); (t "v499")]) };
  ir_blk{ @"L506":
    %"v507" : W = (Cmp Eq W) %"v20", #1
    => br %"v507" ? poll "L53" : "L508" };
  ir_blk{ @"L508":
    %"v509" : W = (Cmp Eq W) %"v20", #2
    => br %"v509" ? poll "L89" : "L510" };
  ir_blk{ @"L510":
    %"v511" : W = (Cmp Eq W) %"v20", #3
    => br %"v511" ? poll "L457" : "L22" };
  ir_blk{ @"L22":
    => (JRets [(Const 4); (Const 0)]) }])) }.
