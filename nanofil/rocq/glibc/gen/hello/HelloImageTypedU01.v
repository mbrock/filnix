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

Definition hello_image_fn_glibc_addmul_1'23u128_lshift : func :=
  ir_fn{ "local" "glibc_addmul_1#u128_lshift"(L %"v0", L %"v1", W %"v4") -> (RTuple [L; L]) blocks ((app (app [ir_blk{ @"start":
    %"v51" : W = (Cmp Ult W) %"v4", #64
    => br %"v51" ? "L52" : "L53" };
  ir_blk{ @"L9":
    => (JRets [(t "v0"); (t "v1")]) };
  ir_blk{ @"L13":
    %"v20" : L = Shl %"v1", %"v4";
    %"v23" : W = Sub #64, %"v4";
    %"v24" : L = Shr %"v0", %"v23";
    %"v25" : L = Or %"v20", %"v24";
    %"v28" : L = Shl %"v0", %"v4"
    => (JRets [(t "v28"); (t "v25")]) };
  ir_blk{ @"L32":
    %"v38" : W = Sub %"v4", #64;
    %"v39" : L = Shl %"v0", %"v38"
    => (JRets [(Const 0); (t "v39")]) };
  ir_blk{ @"L43":
    => (JRets [(Const 0); (Const 0)]) };
  ir_blk{ @"L52":
    %"v54" : W = (Cmp Ult W) %"v4", #32
    => br %"v54" ? "L55" : "L56" };
  ir_blk{ @"L55":
    %"v57" : W = (Cmp Ult W) %"v4", #16
    => br %"v57" ? "L58" : "L59" };
  ir_blk{ @"L58":
    %"v60" : W = (Cmp Ult W) %"v4", #8
    => br %"v60" ? "L61" : "L62" };
  ir_blk{ @"L61":
    %"v63" : W = (Cmp Ult W) %"v4", #4
    => br %"v63" ? "L64" : "L65" };
  ir_blk{ @"L64":
    %"v66" : W = (Cmp Eq W) %"v4", #0
    => br %"v66" ? poll "L9" : "L67" };
  ir_blk{ @"L67":
    %"v68" : W = (Cmp Eq W) %"v4", #1
    => br %"v68" ? poll "L13" : "L69" };
  ir_blk{ @"L69":
    %"v70" : W = (Cmp Eq W) %"v4", #2
    => br %"v70" ? poll "L13" : "L71" };
  ir_blk{ @"L71":
    %"v72" : W = (Cmp Eq W) %"v4", #3
    => br %"v72" ? poll "L13" : poll "L43" };
  ir_blk{ @"L65":
    %"v74" : W = (Cmp Eq W) %"v4", #4
    => br %"v74" ? poll "L13" : "L75" };
  ir_blk{ @"L75":
    %"v76" : W = (Cmp Eq W) %"v4", #5
    => br %"v76" ? poll "L13" : "L77" };
  ir_blk{ @"L77":
    %"v78" : W = (Cmp Eq W) %"v4", #6
    => br %"v78" ? poll "L13" : "L79" };
  ir_blk{ @"L79":
    %"v80" : W = (Cmp Eq W) %"v4", #7
    => br %"v80" ? poll "L13" : poll "L43" };
  ir_blk{ @"L62":
    %"v82" : W = (Cmp Ult W) %"v4", #12
    => br %"v82" ? "L83" : "L84" };
  ir_blk{ @"L83":
    %"v85" : W = (Cmp Eq W) %"v4", #8
    => br %"v85" ? poll "L13" : "L86" };
  ir_blk{ @"L86":
    %"v87" : W = (Cmp Eq W) %"v4", #9
    => br %"v87" ? poll "L13" : "L88" };
  ir_blk{ @"L88":
    %"v89" : W = (Cmp Eq W) %"v4", #10
    => br %"v89" ? poll "L13" : "L90" };
  ir_blk{ @"L90":
    %"v91" : W = (Cmp Eq W) %"v4", #11
    => br %"v91" ? poll "L13" : poll "L43" };
  ir_blk{ @"L84":
    %"v93" : W = (Cmp Eq W) %"v4", #12
    => br %"v93" ? poll "L13" : "L94" };
  ir_blk{ @"L94":
    %"v95" : W = (Cmp Eq W) %"v4", #13
    => br %"v95" ? poll "L13" : "L96" };
  ir_blk{ @"L96":
    %"v97" : W = (Cmp Eq W) %"v4", #14
    => br %"v97" ? poll "L13" : "L98" };
  ir_blk{ @"L98":
    %"v99" : W = (Cmp Eq W) %"v4", #15
    => br %"v99" ? poll "L13" : poll "L43" };
  ir_blk{ @"L59":
    %"v101" : W = (Cmp Ult W) %"v4", #24
    => br %"v101" ? "L102" : "L103" };
  ir_blk{ @"L102":
    %"v104" : W = (Cmp Ult W) %"v4", #20
    => br %"v104" ? "L105" : "L106" };
  ir_blk{ @"L105":
    %"v107" : W = (Cmp Eq W) %"v4", #16
    => br %"v107" ? poll "L13" : "L108" };
  ir_blk{ @"L108":
    %"v109" : W = (Cmp Eq W) %"v4", #17
    => br %"v109" ? poll "L13" : "L110" };
  ir_blk{ @"L110":
    %"v111" : W = (Cmp Eq W) %"v4", #18
    => br %"v111" ? poll "L13" : "L112" };
  ir_blk{ @"L112":
    %"v113" : W = (Cmp Eq W) %"v4", #19
    => br %"v113" ? poll "L13" : poll "L43" };
  ir_blk{ @"L106":
    %"v115" : W = (Cmp Eq W) %"v4", #20
    => br %"v115" ? poll "L13" : "L116" };
  ir_blk{ @"L116":
    %"v117" : W = (Cmp Eq W) %"v4", #21
    => br %"v117" ? poll "L13" : "L118" };
  ir_blk{ @"L118":
    %"v119" : W = (Cmp Eq W) %"v4", #22
    => br %"v119" ? poll "L13" : "L120" };
  ir_blk{ @"L120":
    %"v121" : W = (Cmp Eq W) %"v4", #23
    => br %"v121" ? poll "L13" : poll "L43" };
  ir_blk{ @"L103":
    %"v123" : W = (Cmp Ult W) %"v4", #28
    => br %"v123" ? "L124" : "L125" };
  ir_blk{ @"L124":
    %"v126" : W = (Cmp Eq W) %"v4", #24
    => br %"v126" ? poll "L13" : "L127" };
  ir_blk{ @"L127":
    %"v128" : W = (Cmp Eq W) %"v4", #25
    => br %"v128" ? poll "L13" : "L129" };
  ir_blk{ @"L129":
    %"v130" : W = (Cmp Eq W) %"v4", #26
    => br %"v130" ? poll "L13" : "L131" }] [ir_blk{ @"L131":
    %"v132" : W = (Cmp Eq W) %"v4", #27
    => br %"v132" ? poll "L13" : poll "L43" };
  ir_blk{ @"L125":
    %"v134" : W = (Cmp Eq W) %"v4", #28
    => br %"v134" ? poll "L13" : "L135" };
  ir_blk{ @"L135":
    %"v136" : W = (Cmp Eq W) %"v4", #29
    => br %"v136" ? poll "L13" : "L137" };
  ir_blk{ @"L137":
    %"v138" : W = (Cmp Eq W) %"v4", #30
    => br %"v138" ? poll "L13" : "L139" };
  ir_blk{ @"L139":
    %"v140" : W = (Cmp Eq W) %"v4", #31
    => br %"v140" ? poll "L13" : poll "L43" };
  ir_blk{ @"L56":
    %"v142" : W = (Cmp Ult W) %"v4", #48
    => br %"v142" ? "L143" : "L144" };
  ir_blk{ @"L143":
    %"v145" : W = (Cmp Ult W) %"v4", #40
    => br %"v145" ? "L146" : "L147" };
  ir_blk{ @"L146":
    %"v148" : W = (Cmp Ult W) %"v4", #36
    => br %"v148" ? "L149" : "L150" };
  ir_blk{ @"L149":
    %"v151" : W = (Cmp Eq W) %"v4", #32
    => br %"v151" ? poll "L13" : "L152" };
  ir_blk{ @"L152":
    %"v153" : W = (Cmp Eq W) %"v4", #33
    => br %"v153" ? poll "L13" : "L154" };
  ir_blk{ @"L154":
    %"v155" : W = (Cmp Eq W) %"v4", #34
    => br %"v155" ? poll "L13" : "L156" };
  ir_blk{ @"L156":
    %"v157" : W = (Cmp Eq W) %"v4", #35
    => br %"v157" ? poll "L13" : poll "L43" };
  ir_blk{ @"L150":
    %"v159" : W = (Cmp Eq W) %"v4", #36
    => br %"v159" ? poll "L13" : "L160" };
  ir_blk{ @"L160":
    %"v161" : W = (Cmp Eq W) %"v4", #37
    => br %"v161" ? poll "L13" : "L162" };
  ir_blk{ @"L162":
    %"v163" : W = (Cmp Eq W) %"v4", #38
    => br %"v163" ? poll "L13" : "L164" };
  ir_blk{ @"L164":
    %"v165" : W = (Cmp Eq W) %"v4", #39
    => br %"v165" ? poll "L13" : poll "L43" };
  ir_blk{ @"L147":
    %"v167" : W = (Cmp Ult W) %"v4", #44
    => br %"v167" ? "L168" : "L169" };
  ir_blk{ @"L168":
    %"v170" : W = (Cmp Eq W) %"v4", #40
    => br %"v170" ? poll "L13" : "L171" };
  ir_blk{ @"L171":
    %"v172" : W = (Cmp Eq W) %"v4", #41
    => br %"v172" ? poll "L13" : "L173" };
  ir_blk{ @"L173":
    %"v174" : W = (Cmp Eq W) %"v4", #42
    => br %"v174" ? poll "L13" : "L175" };
  ir_blk{ @"L175":
    %"v176" : W = (Cmp Eq W) %"v4", #43
    => br %"v176" ? poll "L13" : poll "L43" };
  ir_blk{ @"L169":
    %"v178" : W = (Cmp Eq W) %"v4", #44
    => br %"v178" ? poll "L13" : "L179" };
  ir_blk{ @"L179":
    %"v180" : W = (Cmp Eq W) %"v4", #45
    => br %"v180" ? poll "L13" : "L181" };
  ir_blk{ @"L181":
    %"v182" : W = (Cmp Eq W) %"v4", #46
    => br %"v182" ? poll "L13" : "L183" };
  ir_blk{ @"L183":
    %"v184" : W = (Cmp Eq W) %"v4", #47
    => br %"v184" ? poll "L13" : poll "L43" };
  ir_blk{ @"L144":
    %"v186" : W = (Cmp Ult W) %"v4", #56
    => br %"v186" ? "L187" : "L188" };
  ir_blk{ @"L187":
    %"v189" : W = (Cmp Ult W) %"v4", #52
    => br %"v189" ? "L190" : "L191" };
  ir_blk{ @"L190":
    %"v192" : W = (Cmp Eq W) %"v4", #48
    => br %"v192" ? poll "L13" : "L193" };
  ir_blk{ @"L193":
    %"v194" : W = (Cmp Eq W) %"v4", #49
    => br %"v194" ? poll "L13" : "L195" };
  ir_blk{ @"L195":
    %"v196" : W = (Cmp Eq W) %"v4", #50
    => br %"v196" ? poll "L13" : "L197" };
  ir_blk{ @"L197":
    %"v198" : W = (Cmp Eq W) %"v4", #51
    => br %"v198" ? poll "L13" : poll "L43" };
  ir_blk{ @"L191":
    %"v200" : W = (Cmp Eq W) %"v4", #52
    => br %"v200" ? poll "L13" : "L201" };
  ir_blk{ @"L201":
    %"v202" : W = (Cmp Eq W) %"v4", #53
    => br %"v202" ? poll "L13" : "L203" };
  ir_blk{ @"L203":
    %"v204" : W = (Cmp Eq W) %"v4", #54
    => br %"v204" ? poll "L13" : "L205" };
  ir_blk{ @"L205":
    %"v206" : W = (Cmp Eq W) %"v4", #55
    => br %"v206" ? poll "L13" : poll "L43" };
  ir_blk{ @"L188":
    %"v208" : W = (Cmp Ult W) %"v4", #60
    => br %"v208" ? "L209" : "L210" };
  ir_blk{ @"L209":
    %"v211" : W = (Cmp Eq W) %"v4", #56
    => br %"v211" ? poll "L13" : "L212" };
  ir_blk{ @"L212":
    %"v213" : W = (Cmp Eq W) %"v4", #57
    => br %"v213" ? poll "L13" : "L214" };
  ir_blk{ @"L214":
    %"v215" : W = (Cmp Eq W) %"v4", #58
    => br %"v215" ? poll "L13" : "L216" };
  ir_blk{ @"L216":
    %"v217" : W = (Cmp Eq W) %"v4", #59
    => br %"v217" ? poll "L13" : poll "L43" };
  ir_blk{ @"L210":
    %"v219" : W = (Cmp Eq W) %"v4", #60
    => br %"v219" ? poll "L13" : "L220" }]) (app [ir_blk{ @"L220":
    %"v221" : W = (Cmp Eq W) %"v4", #61
    => br %"v221" ? poll "L13" : "L222" };
  ir_blk{ @"L222":
    %"v223" : W = (Cmp Eq W) %"v4", #62
    => br %"v223" ? poll "L13" : "L224" };
  ir_blk{ @"L224":
    %"v225" : W = (Cmp Eq W) %"v4", #63
    => br %"v225" ? poll "L13" : poll "L43" };
  ir_blk{ @"L53":
    %"v227" : W = (Cmp Ult W) %"v4", #96
    => br %"v227" ? "L228" : "L229" };
  ir_blk{ @"L228":
    %"v230" : W = (Cmp Ult W) %"v4", #80
    => br %"v230" ? "L231" : "L232" };
  ir_blk{ @"L231":
    %"v233" : W = (Cmp Ult W) %"v4", #72
    => br %"v233" ? "L234" : "L235" };
  ir_blk{ @"L234":
    %"v236" : W = (Cmp Ult W) %"v4", #68
    => br %"v236" ? "L237" : "L238" };
  ir_blk{ @"L237":
    %"v239" : W = (Cmp Eq W) %"v4", #64
    => br %"v239" ? poll "L32" : "L240" };
  ir_blk{ @"L240":
    %"v241" : W = (Cmp Eq W) %"v4", #65
    => br %"v241" ? poll "L32" : "L242" };
  ir_blk{ @"L242":
    %"v243" : W = (Cmp Eq W) %"v4", #66
    => br %"v243" ? poll "L32" : "L244" };
  ir_blk{ @"L244":
    %"v245" : W = (Cmp Eq W) %"v4", #67
    => br %"v245" ? poll "L32" : poll "L43" };
  ir_blk{ @"L238":
    %"v247" : W = (Cmp Eq W) %"v4", #68
    => br %"v247" ? poll "L32" : "L248" };
  ir_blk{ @"L248":
    %"v249" : W = (Cmp Eq W) %"v4", #69
    => br %"v249" ? poll "L32" : "L250" };
  ir_blk{ @"L250":
    %"v251" : W = (Cmp Eq W) %"v4", #70
    => br %"v251" ? poll "L32" : "L252" };
  ir_blk{ @"L252":
    %"v253" : W = (Cmp Eq W) %"v4", #71
    => br %"v253" ? poll "L32" : poll "L43" };
  ir_blk{ @"L235":
    %"v255" : W = (Cmp Ult W) %"v4", #76
    => br %"v255" ? "L256" : "L257" };
  ir_blk{ @"L256":
    %"v258" : W = (Cmp Eq W) %"v4", #72
    => br %"v258" ? poll "L32" : "L259" };
  ir_blk{ @"L259":
    %"v260" : W = (Cmp Eq W) %"v4", #73
    => br %"v260" ? poll "L32" : "L261" };
  ir_blk{ @"L261":
    %"v262" : W = (Cmp Eq W) %"v4", #74
    => br %"v262" ? poll "L32" : "L263" };
  ir_blk{ @"L263":
    %"v264" : W = (Cmp Eq W) %"v4", #75
    => br %"v264" ? poll "L32" : poll "L43" };
  ir_blk{ @"L257":
    %"v266" : W = (Cmp Eq W) %"v4", #76
    => br %"v266" ? poll "L32" : "L267" };
  ir_blk{ @"L267":
    %"v268" : W = (Cmp Eq W) %"v4", #77
    => br %"v268" ? poll "L32" : "L269" };
  ir_blk{ @"L269":
    %"v270" : W = (Cmp Eq W) %"v4", #78
    => br %"v270" ? poll "L32" : "L271" };
  ir_blk{ @"L271":
    %"v272" : W = (Cmp Eq W) %"v4", #79
    => br %"v272" ? poll "L32" : poll "L43" };
  ir_blk{ @"L232":
    %"v274" : W = (Cmp Ult W) %"v4", #88
    => br %"v274" ? "L275" : "L276" };
  ir_blk{ @"L275":
    %"v277" : W = (Cmp Ult W) %"v4", #84
    => br %"v277" ? "L278" : "L279" };
  ir_blk{ @"L278":
    %"v280" : W = (Cmp Eq W) %"v4", #80
    => br %"v280" ? poll "L32" : "L281" };
  ir_blk{ @"L281":
    %"v282" : W = (Cmp Eq W) %"v4", #81
    => br %"v282" ? poll "L32" : "L283" };
  ir_blk{ @"L283":
    %"v284" : W = (Cmp Eq W) %"v4", #82
    => br %"v284" ? poll "L32" : "L285" };
  ir_blk{ @"L285":
    %"v286" : W = (Cmp Eq W) %"v4", #83
    => br %"v286" ? poll "L32" : poll "L43" };
  ir_blk{ @"L279":
    %"v288" : W = (Cmp Eq W) %"v4", #84
    => br %"v288" ? poll "L32" : "L289" };
  ir_blk{ @"L289":
    %"v290" : W = (Cmp Eq W) %"v4", #85
    => br %"v290" ? poll "L32" : "L291" };
  ir_blk{ @"L291":
    %"v292" : W = (Cmp Eq W) %"v4", #86
    => br %"v292" ? poll "L32" : "L293" };
  ir_blk{ @"L293":
    %"v294" : W = (Cmp Eq W) %"v4", #87
    => br %"v294" ? poll "L32" : poll "L43" };
  ir_blk{ @"L276":
    %"v296" : W = (Cmp Ult W) %"v4", #92
    => br %"v296" ? "L297" : "L298" };
  ir_blk{ @"L297":
    %"v299" : W = (Cmp Eq W) %"v4", #88
    => br %"v299" ? poll "L32" : "L300" };
  ir_blk{ @"L300":
    %"v301" : W = (Cmp Eq W) %"v4", #89
    => br %"v301" ? poll "L32" : "L302" };
  ir_blk{ @"L302":
    %"v303" : W = (Cmp Eq W) %"v4", #90
    => br %"v303" ? poll "L32" : "L304" };
  ir_blk{ @"L304":
    %"v305" : W = (Cmp Eq W) %"v4", #91
    => br %"v305" ? poll "L32" : poll "L43" };
  ir_blk{ @"L298":
    %"v307" : W = (Cmp Eq W) %"v4", #92
    => br %"v307" ? poll "L32" : "L308" };
  ir_blk{ @"L308":
    %"v309" : W = (Cmp Eq W) %"v4", #93
    => br %"v309" ? poll "L32" : "L310" }] [ir_blk{ @"L310":
    %"v311" : W = (Cmp Eq W) %"v4", #94
    => br %"v311" ? poll "L32" : "L312" };
  ir_blk{ @"L312":
    %"v313" : W = (Cmp Eq W) %"v4", #95
    => br %"v313" ? poll "L32" : poll "L43" };
  ir_blk{ @"L229":
    %"v315" : W = (Cmp Ult W) %"v4", #112
    => br %"v315" ? "L316" : "L317" };
  ir_blk{ @"L316":
    %"v318" : W = (Cmp Ult W) %"v4", #104
    => br %"v318" ? "L319" : "L320" };
  ir_blk{ @"L319":
    %"v321" : W = (Cmp Ult W) %"v4", #100
    => br %"v321" ? "L322" : "L323" };
  ir_blk{ @"L322":
    %"v324" : W = (Cmp Eq W) %"v4", #96
    => br %"v324" ? poll "L32" : "L325" };
  ir_blk{ @"L325":
    %"v326" : W = (Cmp Eq W) %"v4", #97
    => br %"v326" ? poll "L32" : "L327" };
  ir_blk{ @"L327":
    %"v328" : W = (Cmp Eq W) %"v4", #98
    => br %"v328" ? poll "L32" : "L329" };
  ir_blk{ @"L329":
    %"v330" : W = (Cmp Eq W) %"v4", #99
    => br %"v330" ? poll "L32" : poll "L43" };
  ir_blk{ @"L323":
    %"v332" : W = (Cmp Eq W) %"v4", #100
    => br %"v332" ? poll "L32" : "L333" };
  ir_blk{ @"L333":
    %"v334" : W = (Cmp Eq W) %"v4", #101
    => br %"v334" ? poll "L32" : "L335" };
  ir_blk{ @"L335":
    %"v336" : W = (Cmp Eq W) %"v4", #102
    => br %"v336" ? poll "L32" : "L337" };
  ir_blk{ @"L337":
    %"v338" : W = (Cmp Eq W) %"v4", #103
    => br %"v338" ? poll "L32" : poll "L43" };
  ir_blk{ @"L320":
    %"v340" : W = (Cmp Ult W) %"v4", #108
    => br %"v340" ? "L341" : "L342" };
  ir_blk{ @"L341":
    %"v343" : W = (Cmp Eq W) %"v4", #104
    => br %"v343" ? poll "L32" : "L344" };
  ir_blk{ @"L344":
    %"v345" : W = (Cmp Eq W) %"v4", #105
    => br %"v345" ? poll "L32" : "L346" };
  ir_blk{ @"L346":
    %"v347" : W = (Cmp Eq W) %"v4", #106
    => br %"v347" ? poll "L32" : "L348" };
  ir_blk{ @"L348":
    %"v349" : W = (Cmp Eq W) %"v4", #107
    => br %"v349" ? poll "L32" : poll "L43" };
  ir_blk{ @"L342":
    %"v351" : W = (Cmp Eq W) %"v4", #108
    => br %"v351" ? poll "L32" : "L352" };
  ir_blk{ @"L352":
    %"v353" : W = (Cmp Eq W) %"v4", #109
    => br %"v353" ? poll "L32" : "L354" };
  ir_blk{ @"L354":
    %"v355" : W = (Cmp Eq W) %"v4", #110
    => br %"v355" ? poll "L32" : "L356" };
  ir_blk{ @"L356":
    %"v357" : W = (Cmp Eq W) %"v4", #111
    => br %"v357" ? poll "L32" : poll "L43" };
  ir_blk{ @"L317":
    %"v359" : W = (Cmp Ult W) %"v4", #120
    => br %"v359" ? "L360" : "L361" };
  ir_blk{ @"L360":
    %"v362" : W = (Cmp Ult W) %"v4", #116
    => br %"v362" ? "L363" : "L364" };
  ir_blk{ @"L363":
    %"v365" : W = (Cmp Eq W) %"v4", #112
    => br %"v365" ? poll "L32" : "L366" };
  ir_blk{ @"L366":
    %"v367" : W = (Cmp Eq W) %"v4", #113
    => br %"v367" ? poll "L32" : "L368" };
  ir_blk{ @"L368":
    %"v369" : W = (Cmp Eq W) %"v4", #114
    => br %"v369" ? poll "L32" : "L370" };
  ir_blk{ @"L370":
    %"v371" : W = (Cmp Eq W) %"v4", #115
    => br %"v371" ? poll "L32" : poll "L43" };
  ir_blk{ @"L364":
    %"v373" : W = (Cmp Eq W) %"v4", #116
    => br %"v373" ? poll "L32" : "L374" };
  ir_blk{ @"L374":
    %"v375" : W = (Cmp Eq W) %"v4", #117
    => br %"v375" ? poll "L32" : "L376" };
  ir_blk{ @"L376":
    %"v377" : W = (Cmp Eq W) %"v4", #118
    => br %"v377" ? poll "L32" : "L378" };
  ir_blk{ @"L378":
    %"v379" : W = (Cmp Eq W) %"v4", #119
    => br %"v379" ? poll "L32" : poll "L43" };
  ir_blk{ @"L361":
    %"v381" : W = (Cmp Ult W) %"v4", #124
    => br %"v381" ? "L382" : "L383" };
  ir_blk{ @"L382":
    %"v384" : W = (Cmp Eq W) %"v4", #120
    => br %"v384" ? poll "L32" : "L385" };
  ir_blk{ @"L385":
    %"v386" : W = (Cmp Eq W) %"v4", #121
    => br %"v386" ? poll "L32" : "L387" };
  ir_blk{ @"L387":
    %"v388" : W = (Cmp Eq W) %"v4", #122
    => br %"v388" ? poll "L32" : "L389" };
  ir_blk{ @"L389":
    %"v390" : W = (Cmp Eq W) %"v4", #123
    => br %"v390" ? poll "L32" : poll "L43" };
  ir_blk{ @"L383":
    %"v392" : W = (Cmp Eq W) %"v4", #124
    => br %"v392" ? poll "L32" : "L393" };
  ir_blk{ @"L393":
    %"v394" : W = (Cmp Eq W) %"v4", #125
    => br %"v394" ? poll "L32" : "L395" };
  ir_blk{ @"L395":
    %"v396" : W = (Cmp Eq W) %"v4", #126
    => br %"v396" ? poll "L32" : "L397" };
  ir_blk{ @"L397":
    %"v398" : W = (Cmp Eq W) %"v4", #127
    => br %"v398" ? poll "L32" : poll "L43" }]))) }.

Definition hello_image_fn_glibc_mul_1'23u128_lshift : func :=
  ir_fn{ "local" "glibc_mul_1#u128_lshift"(L %"v0", L %"v1", W %"v4") -> (RTuple [L; L]) blocks ((app (app [ir_blk{ @"start":
    %"v51" : W = (Cmp Ult W) %"v4", #64
    => br %"v51" ? "L52" : "L53" };
  ir_blk{ @"L9":
    => (JRets [(t "v0"); (t "v1")]) };
  ir_blk{ @"L13":
    %"v20" : L = Shl %"v1", %"v4";
    %"v23" : W = Sub #64, %"v4";
    %"v24" : L = Shr %"v0", %"v23";
    %"v25" : L = Or %"v20", %"v24";
    %"v28" : L = Shl %"v0", %"v4"
    => (JRets [(t "v28"); (t "v25")]) };
  ir_blk{ @"L32":
    %"v38" : W = Sub %"v4", #64;
    %"v39" : L = Shl %"v0", %"v38"
    => (JRets [(Const 0); (t "v39")]) };
  ir_blk{ @"L43":
    => (JRets [(Const 0); (Const 0)]) };
  ir_blk{ @"L52":
    %"v54" : W = (Cmp Ult W) %"v4", #32
    => br %"v54" ? "L55" : "L56" };
  ir_blk{ @"L55":
    %"v57" : W = (Cmp Ult W) %"v4", #16
    => br %"v57" ? "L58" : "L59" };
  ir_blk{ @"L58":
    %"v60" : W = (Cmp Ult W) %"v4", #8
    => br %"v60" ? "L61" : "L62" };
  ir_blk{ @"L61":
    %"v63" : W = (Cmp Ult W) %"v4", #4
    => br %"v63" ? "L64" : "L65" };
  ir_blk{ @"L64":
    %"v66" : W = (Cmp Eq W) %"v4", #0
    => br %"v66" ? poll "L9" : "L67" };
  ir_blk{ @"L67":
    %"v68" : W = (Cmp Eq W) %"v4", #1
    => br %"v68" ? poll "L13" : "L69" };
  ir_blk{ @"L69":
    %"v70" : W = (Cmp Eq W) %"v4", #2
    => br %"v70" ? poll "L13" : "L71" };
  ir_blk{ @"L71":
    %"v72" : W = (Cmp Eq W) %"v4", #3
    => br %"v72" ? poll "L13" : poll "L43" };
  ir_blk{ @"L65":
    %"v74" : W = (Cmp Eq W) %"v4", #4
    => br %"v74" ? poll "L13" : "L75" };
  ir_blk{ @"L75":
    %"v76" : W = (Cmp Eq W) %"v4", #5
    => br %"v76" ? poll "L13" : "L77" };
  ir_blk{ @"L77":
    %"v78" : W = (Cmp Eq W) %"v4", #6
    => br %"v78" ? poll "L13" : "L79" };
  ir_blk{ @"L79":
    %"v80" : W = (Cmp Eq W) %"v4", #7
    => br %"v80" ? poll "L13" : poll "L43" };
  ir_blk{ @"L62":
    %"v82" : W = (Cmp Ult W) %"v4", #12
    => br %"v82" ? "L83" : "L84" };
  ir_blk{ @"L83":
    %"v85" : W = (Cmp Eq W) %"v4", #8
    => br %"v85" ? poll "L13" : "L86" };
  ir_blk{ @"L86":
    %"v87" : W = (Cmp Eq W) %"v4", #9
    => br %"v87" ? poll "L13" : "L88" };
  ir_blk{ @"L88":
    %"v89" : W = (Cmp Eq W) %"v4", #10
    => br %"v89" ? poll "L13" : "L90" };
  ir_blk{ @"L90":
    %"v91" : W = (Cmp Eq W) %"v4", #11
    => br %"v91" ? poll "L13" : poll "L43" };
  ir_blk{ @"L84":
    %"v93" : W = (Cmp Eq W) %"v4", #12
    => br %"v93" ? poll "L13" : "L94" };
  ir_blk{ @"L94":
    %"v95" : W = (Cmp Eq W) %"v4", #13
    => br %"v95" ? poll "L13" : "L96" };
  ir_blk{ @"L96":
    %"v97" : W = (Cmp Eq W) %"v4", #14
    => br %"v97" ? poll "L13" : "L98" };
  ir_blk{ @"L98":
    %"v99" : W = (Cmp Eq W) %"v4", #15
    => br %"v99" ? poll "L13" : poll "L43" };
  ir_blk{ @"L59":
    %"v101" : W = (Cmp Ult W) %"v4", #24
    => br %"v101" ? "L102" : "L103" };
  ir_blk{ @"L102":
    %"v104" : W = (Cmp Ult W) %"v4", #20
    => br %"v104" ? "L105" : "L106" };
  ir_blk{ @"L105":
    %"v107" : W = (Cmp Eq W) %"v4", #16
    => br %"v107" ? poll "L13" : "L108" };
  ir_blk{ @"L108":
    %"v109" : W = (Cmp Eq W) %"v4", #17
    => br %"v109" ? poll "L13" : "L110" };
  ir_blk{ @"L110":
    %"v111" : W = (Cmp Eq W) %"v4", #18
    => br %"v111" ? poll "L13" : "L112" };
  ir_blk{ @"L112":
    %"v113" : W = (Cmp Eq W) %"v4", #19
    => br %"v113" ? poll "L13" : poll "L43" };
  ir_blk{ @"L106":
    %"v115" : W = (Cmp Eq W) %"v4", #20
    => br %"v115" ? poll "L13" : "L116" };
  ir_blk{ @"L116":
    %"v117" : W = (Cmp Eq W) %"v4", #21
    => br %"v117" ? poll "L13" : "L118" };
  ir_blk{ @"L118":
    %"v119" : W = (Cmp Eq W) %"v4", #22
    => br %"v119" ? poll "L13" : "L120" };
  ir_blk{ @"L120":
    %"v121" : W = (Cmp Eq W) %"v4", #23
    => br %"v121" ? poll "L13" : poll "L43" };
  ir_blk{ @"L103":
    %"v123" : W = (Cmp Ult W) %"v4", #28
    => br %"v123" ? "L124" : "L125" };
  ir_blk{ @"L124":
    %"v126" : W = (Cmp Eq W) %"v4", #24
    => br %"v126" ? poll "L13" : "L127" };
  ir_blk{ @"L127":
    %"v128" : W = (Cmp Eq W) %"v4", #25
    => br %"v128" ? poll "L13" : "L129" };
  ir_blk{ @"L129":
    %"v130" : W = (Cmp Eq W) %"v4", #26
    => br %"v130" ? poll "L13" : "L131" }] [ir_blk{ @"L131":
    %"v132" : W = (Cmp Eq W) %"v4", #27
    => br %"v132" ? poll "L13" : poll "L43" };
  ir_blk{ @"L125":
    %"v134" : W = (Cmp Eq W) %"v4", #28
    => br %"v134" ? poll "L13" : "L135" };
  ir_blk{ @"L135":
    %"v136" : W = (Cmp Eq W) %"v4", #29
    => br %"v136" ? poll "L13" : "L137" };
  ir_blk{ @"L137":
    %"v138" : W = (Cmp Eq W) %"v4", #30
    => br %"v138" ? poll "L13" : "L139" };
  ir_blk{ @"L139":
    %"v140" : W = (Cmp Eq W) %"v4", #31
    => br %"v140" ? poll "L13" : poll "L43" };
  ir_blk{ @"L56":
    %"v142" : W = (Cmp Ult W) %"v4", #48
    => br %"v142" ? "L143" : "L144" };
  ir_blk{ @"L143":
    %"v145" : W = (Cmp Ult W) %"v4", #40
    => br %"v145" ? "L146" : "L147" };
  ir_blk{ @"L146":
    %"v148" : W = (Cmp Ult W) %"v4", #36
    => br %"v148" ? "L149" : "L150" };
  ir_blk{ @"L149":
    %"v151" : W = (Cmp Eq W) %"v4", #32
    => br %"v151" ? poll "L13" : "L152" };
  ir_blk{ @"L152":
    %"v153" : W = (Cmp Eq W) %"v4", #33
    => br %"v153" ? poll "L13" : "L154" };
  ir_blk{ @"L154":
    %"v155" : W = (Cmp Eq W) %"v4", #34
    => br %"v155" ? poll "L13" : "L156" };
  ir_blk{ @"L156":
    %"v157" : W = (Cmp Eq W) %"v4", #35
    => br %"v157" ? poll "L13" : poll "L43" };
  ir_blk{ @"L150":
    %"v159" : W = (Cmp Eq W) %"v4", #36
    => br %"v159" ? poll "L13" : "L160" };
  ir_blk{ @"L160":
    %"v161" : W = (Cmp Eq W) %"v4", #37
    => br %"v161" ? poll "L13" : "L162" };
  ir_blk{ @"L162":
    %"v163" : W = (Cmp Eq W) %"v4", #38
    => br %"v163" ? poll "L13" : "L164" };
  ir_blk{ @"L164":
    %"v165" : W = (Cmp Eq W) %"v4", #39
    => br %"v165" ? poll "L13" : poll "L43" };
  ir_blk{ @"L147":
    %"v167" : W = (Cmp Ult W) %"v4", #44
    => br %"v167" ? "L168" : "L169" };
  ir_blk{ @"L168":
    %"v170" : W = (Cmp Eq W) %"v4", #40
    => br %"v170" ? poll "L13" : "L171" };
  ir_blk{ @"L171":
    %"v172" : W = (Cmp Eq W) %"v4", #41
    => br %"v172" ? poll "L13" : "L173" };
  ir_blk{ @"L173":
    %"v174" : W = (Cmp Eq W) %"v4", #42
    => br %"v174" ? poll "L13" : "L175" };
  ir_blk{ @"L175":
    %"v176" : W = (Cmp Eq W) %"v4", #43
    => br %"v176" ? poll "L13" : poll "L43" };
  ir_blk{ @"L169":
    %"v178" : W = (Cmp Eq W) %"v4", #44
    => br %"v178" ? poll "L13" : "L179" };
  ir_blk{ @"L179":
    %"v180" : W = (Cmp Eq W) %"v4", #45
    => br %"v180" ? poll "L13" : "L181" };
  ir_blk{ @"L181":
    %"v182" : W = (Cmp Eq W) %"v4", #46
    => br %"v182" ? poll "L13" : "L183" };
  ir_blk{ @"L183":
    %"v184" : W = (Cmp Eq W) %"v4", #47
    => br %"v184" ? poll "L13" : poll "L43" };
  ir_blk{ @"L144":
    %"v186" : W = (Cmp Ult W) %"v4", #56
    => br %"v186" ? "L187" : "L188" };
  ir_blk{ @"L187":
    %"v189" : W = (Cmp Ult W) %"v4", #52
    => br %"v189" ? "L190" : "L191" };
  ir_blk{ @"L190":
    %"v192" : W = (Cmp Eq W) %"v4", #48
    => br %"v192" ? poll "L13" : "L193" };
  ir_blk{ @"L193":
    %"v194" : W = (Cmp Eq W) %"v4", #49
    => br %"v194" ? poll "L13" : "L195" };
  ir_blk{ @"L195":
    %"v196" : W = (Cmp Eq W) %"v4", #50
    => br %"v196" ? poll "L13" : "L197" };
  ir_blk{ @"L197":
    %"v198" : W = (Cmp Eq W) %"v4", #51
    => br %"v198" ? poll "L13" : poll "L43" };
  ir_blk{ @"L191":
    %"v200" : W = (Cmp Eq W) %"v4", #52
    => br %"v200" ? poll "L13" : "L201" };
  ir_blk{ @"L201":
    %"v202" : W = (Cmp Eq W) %"v4", #53
    => br %"v202" ? poll "L13" : "L203" };
  ir_blk{ @"L203":
    %"v204" : W = (Cmp Eq W) %"v4", #54
    => br %"v204" ? poll "L13" : "L205" };
  ir_blk{ @"L205":
    %"v206" : W = (Cmp Eq W) %"v4", #55
    => br %"v206" ? poll "L13" : poll "L43" };
  ir_blk{ @"L188":
    %"v208" : W = (Cmp Ult W) %"v4", #60
    => br %"v208" ? "L209" : "L210" };
  ir_blk{ @"L209":
    %"v211" : W = (Cmp Eq W) %"v4", #56
    => br %"v211" ? poll "L13" : "L212" };
  ir_blk{ @"L212":
    %"v213" : W = (Cmp Eq W) %"v4", #57
    => br %"v213" ? poll "L13" : "L214" };
  ir_blk{ @"L214":
    %"v215" : W = (Cmp Eq W) %"v4", #58
    => br %"v215" ? poll "L13" : "L216" };
  ir_blk{ @"L216":
    %"v217" : W = (Cmp Eq W) %"v4", #59
    => br %"v217" ? poll "L13" : poll "L43" };
  ir_blk{ @"L210":
    %"v219" : W = (Cmp Eq W) %"v4", #60
    => br %"v219" ? poll "L13" : "L220" }]) (app [ir_blk{ @"L220":
    %"v221" : W = (Cmp Eq W) %"v4", #61
    => br %"v221" ? poll "L13" : "L222" };
  ir_blk{ @"L222":
    %"v223" : W = (Cmp Eq W) %"v4", #62
    => br %"v223" ? poll "L13" : "L224" };
  ir_blk{ @"L224":
    %"v225" : W = (Cmp Eq W) %"v4", #63
    => br %"v225" ? poll "L13" : poll "L43" };
  ir_blk{ @"L53":
    %"v227" : W = (Cmp Ult W) %"v4", #96
    => br %"v227" ? "L228" : "L229" };
  ir_blk{ @"L228":
    %"v230" : W = (Cmp Ult W) %"v4", #80
    => br %"v230" ? "L231" : "L232" };
  ir_blk{ @"L231":
    %"v233" : W = (Cmp Ult W) %"v4", #72
    => br %"v233" ? "L234" : "L235" };
  ir_blk{ @"L234":
    %"v236" : W = (Cmp Ult W) %"v4", #68
    => br %"v236" ? "L237" : "L238" };
  ir_blk{ @"L237":
    %"v239" : W = (Cmp Eq W) %"v4", #64
    => br %"v239" ? poll "L32" : "L240" };
  ir_blk{ @"L240":
    %"v241" : W = (Cmp Eq W) %"v4", #65
    => br %"v241" ? poll "L32" : "L242" };
  ir_blk{ @"L242":
    %"v243" : W = (Cmp Eq W) %"v4", #66
    => br %"v243" ? poll "L32" : "L244" };
  ir_blk{ @"L244":
    %"v245" : W = (Cmp Eq W) %"v4", #67
    => br %"v245" ? poll "L32" : poll "L43" };
  ir_blk{ @"L238":
    %"v247" : W = (Cmp Eq W) %"v4", #68
    => br %"v247" ? poll "L32" : "L248" };
  ir_blk{ @"L248":
    %"v249" : W = (Cmp Eq W) %"v4", #69
    => br %"v249" ? poll "L32" : "L250" };
  ir_blk{ @"L250":
    %"v251" : W = (Cmp Eq W) %"v4", #70
    => br %"v251" ? poll "L32" : "L252" };
  ir_blk{ @"L252":
    %"v253" : W = (Cmp Eq W) %"v4", #71
    => br %"v253" ? poll "L32" : poll "L43" };
  ir_blk{ @"L235":
    %"v255" : W = (Cmp Ult W) %"v4", #76
    => br %"v255" ? "L256" : "L257" };
  ir_blk{ @"L256":
    %"v258" : W = (Cmp Eq W) %"v4", #72
    => br %"v258" ? poll "L32" : "L259" };
  ir_blk{ @"L259":
    %"v260" : W = (Cmp Eq W) %"v4", #73
    => br %"v260" ? poll "L32" : "L261" };
  ir_blk{ @"L261":
    %"v262" : W = (Cmp Eq W) %"v4", #74
    => br %"v262" ? poll "L32" : "L263" };
  ir_blk{ @"L263":
    %"v264" : W = (Cmp Eq W) %"v4", #75
    => br %"v264" ? poll "L32" : poll "L43" };
  ir_blk{ @"L257":
    %"v266" : W = (Cmp Eq W) %"v4", #76
    => br %"v266" ? poll "L32" : "L267" };
  ir_blk{ @"L267":
    %"v268" : W = (Cmp Eq W) %"v4", #77
    => br %"v268" ? poll "L32" : "L269" };
  ir_blk{ @"L269":
    %"v270" : W = (Cmp Eq W) %"v4", #78
    => br %"v270" ? poll "L32" : "L271" };
  ir_blk{ @"L271":
    %"v272" : W = (Cmp Eq W) %"v4", #79
    => br %"v272" ? poll "L32" : poll "L43" };
  ir_blk{ @"L232":
    %"v274" : W = (Cmp Ult W) %"v4", #88
    => br %"v274" ? "L275" : "L276" };
  ir_blk{ @"L275":
    %"v277" : W = (Cmp Ult W) %"v4", #84
    => br %"v277" ? "L278" : "L279" };
  ir_blk{ @"L278":
    %"v280" : W = (Cmp Eq W) %"v4", #80
    => br %"v280" ? poll "L32" : "L281" };
  ir_blk{ @"L281":
    %"v282" : W = (Cmp Eq W) %"v4", #81
    => br %"v282" ? poll "L32" : "L283" };
  ir_blk{ @"L283":
    %"v284" : W = (Cmp Eq W) %"v4", #82
    => br %"v284" ? poll "L32" : "L285" };
  ir_blk{ @"L285":
    %"v286" : W = (Cmp Eq W) %"v4", #83
    => br %"v286" ? poll "L32" : poll "L43" };
  ir_blk{ @"L279":
    %"v288" : W = (Cmp Eq W) %"v4", #84
    => br %"v288" ? poll "L32" : "L289" };
  ir_blk{ @"L289":
    %"v290" : W = (Cmp Eq W) %"v4", #85
    => br %"v290" ? poll "L32" : "L291" };
  ir_blk{ @"L291":
    %"v292" : W = (Cmp Eq W) %"v4", #86
    => br %"v292" ? poll "L32" : "L293" };
  ir_blk{ @"L293":
    %"v294" : W = (Cmp Eq W) %"v4", #87
    => br %"v294" ? poll "L32" : poll "L43" };
  ir_blk{ @"L276":
    %"v296" : W = (Cmp Ult W) %"v4", #92
    => br %"v296" ? "L297" : "L298" };
  ir_blk{ @"L297":
    %"v299" : W = (Cmp Eq W) %"v4", #88
    => br %"v299" ? poll "L32" : "L300" };
  ir_blk{ @"L300":
    %"v301" : W = (Cmp Eq W) %"v4", #89
    => br %"v301" ? poll "L32" : "L302" };
  ir_blk{ @"L302":
    %"v303" : W = (Cmp Eq W) %"v4", #90
    => br %"v303" ? poll "L32" : "L304" };
  ir_blk{ @"L304":
    %"v305" : W = (Cmp Eq W) %"v4", #91
    => br %"v305" ? poll "L32" : poll "L43" };
  ir_blk{ @"L298":
    %"v307" : W = (Cmp Eq W) %"v4", #92
    => br %"v307" ? poll "L32" : "L308" };
  ir_blk{ @"L308":
    %"v309" : W = (Cmp Eq W) %"v4", #93
    => br %"v309" ? poll "L32" : "L310" }] [ir_blk{ @"L310":
    %"v311" : W = (Cmp Eq W) %"v4", #94
    => br %"v311" ? poll "L32" : "L312" };
  ir_blk{ @"L312":
    %"v313" : W = (Cmp Eq W) %"v4", #95
    => br %"v313" ? poll "L32" : poll "L43" };
  ir_blk{ @"L229":
    %"v315" : W = (Cmp Ult W) %"v4", #112
    => br %"v315" ? "L316" : "L317" };
  ir_blk{ @"L316":
    %"v318" : W = (Cmp Ult W) %"v4", #104
    => br %"v318" ? "L319" : "L320" };
  ir_blk{ @"L319":
    %"v321" : W = (Cmp Ult W) %"v4", #100
    => br %"v321" ? "L322" : "L323" };
  ir_blk{ @"L322":
    %"v324" : W = (Cmp Eq W) %"v4", #96
    => br %"v324" ? poll "L32" : "L325" };
  ir_blk{ @"L325":
    %"v326" : W = (Cmp Eq W) %"v4", #97
    => br %"v326" ? poll "L32" : "L327" };
  ir_blk{ @"L327":
    %"v328" : W = (Cmp Eq W) %"v4", #98
    => br %"v328" ? poll "L32" : "L329" };
  ir_blk{ @"L329":
    %"v330" : W = (Cmp Eq W) %"v4", #99
    => br %"v330" ? poll "L32" : poll "L43" };
  ir_blk{ @"L323":
    %"v332" : W = (Cmp Eq W) %"v4", #100
    => br %"v332" ? poll "L32" : "L333" };
  ir_blk{ @"L333":
    %"v334" : W = (Cmp Eq W) %"v4", #101
    => br %"v334" ? poll "L32" : "L335" };
  ir_blk{ @"L335":
    %"v336" : W = (Cmp Eq W) %"v4", #102
    => br %"v336" ? poll "L32" : "L337" };
  ir_blk{ @"L337":
    %"v338" : W = (Cmp Eq W) %"v4", #103
    => br %"v338" ? poll "L32" : poll "L43" };
  ir_blk{ @"L320":
    %"v340" : W = (Cmp Ult W) %"v4", #108
    => br %"v340" ? "L341" : "L342" };
  ir_blk{ @"L341":
    %"v343" : W = (Cmp Eq W) %"v4", #104
    => br %"v343" ? poll "L32" : "L344" };
  ir_blk{ @"L344":
    %"v345" : W = (Cmp Eq W) %"v4", #105
    => br %"v345" ? poll "L32" : "L346" };
  ir_blk{ @"L346":
    %"v347" : W = (Cmp Eq W) %"v4", #106
    => br %"v347" ? poll "L32" : "L348" };
  ir_blk{ @"L348":
    %"v349" : W = (Cmp Eq W) %"v4", #107
    => br %"v349" ? poll "L32" : poll "L43" };
  ir_blk{ @"L342":
    %"v351" : W = (Cmp Eq W) %"v4", #108
    => br %"v351" ? poll "L32" : "L352" };
  ir_blk{ @"L352":
    %"v353" : W = (Cmp Eq W) %"v4", #109
    => br %"v353" ? poll "L32" : "L354" };
  ir_blk{ @"L354":
    %"v355" : W = (Cmp Eq W) %"v4", #110
    => br %"v355" ? poll "L32" : "L356" };
  ir_blk{ @"L356":
    %"v357" : W = (Cmp Eq W) %"v4", #111
    => br %"v357" ? poll "L32" : poll "L43" };
  ir_blk{ @"L317":
    %"v359" : W = (Cmp Ult W) %"v4", #120
    => br %"v359" ? "L360" : "L361" };
  ir_blk{ @"L360":
    %"v362" : W = (Cmp Ult W) %"v4", #116
    => br %"v362" ? "L363" : "L364" };
  ir_blk{ @"L363":
    %"v365" : W = (Cmp Eq W) %"v4", #112
    => br %"v365" ? poll "L32" : "L366" };
  ir_blk{ @"L366":
    %"v367" : W = (Cmp Eq W) %"v4", #113
    => br %"v367" ? poll "L32" : "L368" };
  ir_blk{ @"L368":
    %"v369" : W = (Cmp Eq W) %"v4", #114
    => br %"v369" ? poll "L32" : "L370" };
  ir_blk{ @"L370":
    %"v371" : W = (Cmp Eq W) %"v4", #115
    => br %"v371" ? poll "L32" : poll "L43" };
  ir_blk{ @"L364":
    %"v373" : W = (Cmp Eq W) %"v4", #116
    => br %"v373" ? poll "L32" : "L374" };
  ir_blk{ @"L374":
    %"v375" : W = (Cmp Eq W) %"v4", #117
    => br %"v375" ? poll "L32" : "L376" };
  ir_blk{ @"L376":
    %"v377" : W = (Cmp Eq W) %"v4", #118
    => br %"v377" ? poll "L32" : "L378" };
  ir_blk{ @"L378":
    %"v379" : W = (Cmp Eq W) %"v4", #119
    => br %"v379" ? poll "L32" : poll "L43" };
  ir_blk{ @"L361":
    %"v381" : W = (Cmp Ult W) %"v4", #124
    => br %"v381" ? "L382" : "L383" };
  ir_blk{ @"L382":
    %"v384" : W = (Cmp Eq W) %"v4", #120
    => br %"v384" ? poll "L32" : "L385" };
  ir_blk{ @"L385":
    %"v386" : W = (Cmp Eq W) %"v4", #121
    => br %"v386" ? poll "L32" : "L387" };
  ir_blk{ @"L387":
    %"v388" : W = (Cmp Eq W) %"v4", #122
    => br %"v388" ? poll "L32" : "L389" };
  ir_blk{ @"L389":
    %"v390" : W = (Cmp Eq W) %"v4", #123
    => br %"v390" ? poll "L32" : poll "L43" };
  ir_blk{ @"L383":
    %"v392" : W = (Cmp Eq W) %"v4", #124
    => br %"v392" ? poll "L32" : "L393" };
  ir_blk{ @"L393":
    %"v394" : W = (Cmp Eq W) %"v4", #125
    => br %"v394" ? poll "L32" : "L395" };
  ir_blk{ @"L395":
    %"v396" : W = (Cmp Eq W) %"v4", #126
    => br %"v396" ? poll "L32" : "L397" };
  ir_blk{ @"L397":
    %"v398" : W = (Cmp Eq W) %"v4", #127
    => br %"v398" ? poll "L32" : poll "L43" }]))) }.

Definition hello_image_fn_glibc_submul_1'23u128_lshift : func :=
  ir_fn{ "local" "glibc_submul_1#u128_lshift"(L %"v0", L %"v1", W %"v4") -> (RTuple [L; L]) blocks ((app (app [ir_blk{ @"start":
    %"v51" : W = (Cmp Ult W) %"v4", #64
    => br %"v51" ? "L52" : "L53" };
  ir_blk{ @"L9":
    => (JRets [(t "v0"); (t "v1")]) };
  ir_blk{ @"L13":
    %"v20" : L = Shl %"v1", %"v4";
    %"v23" : W = Sub #64, %"v4";
    %"v24" : L = Shr %"v0", %"v23";
    %"v25" : L = Or %"v20", %"v24";
    %"v28" : L = Shl %"v0", %"v4"
    => (JRets [(t "v28"); (t "v25")]) };
  ir_blk{ @"L32":
    %"v38" : W = Sub %"v4", #64;
    %"v39" : L = Shl %"v0", %"v38"
    => (JRets [(Const 0); (t "v39")]) };
  ir_blk{ @"L43":
    => (JRets [(Const 0); (Const 0)]) };
  ir_blk{ @"L52":
    %"v54" : W = (Cmp Ult W) %"v4", #32
    => br %"v54" ? "L55" : "L56" };
  ir_blk{ @"L55":
    %"v57" : W = (Cmp Ult W) %"v4", #16
    => br %"v57" ? "L58" : "L59" };
  ir_blk{ @"L58":
    %"v60" : W = (Cmp Ult W) %"v4", #8
    => br %"v60" ? "L61" : "L62" };
  ir_blk{ @"L61":
    %"v63" : W = (Cmp Ult W) %"v4", #4
    => br %"v63" ? "L64" : "L65" };
  ir_blk{ @"L64":
    %"v66" : W = (Cmp Eq W) %"v4", #0
    => br %"v66" ? poll "L9" : "L67" };
  ir_blk{ @"L67":
    %"v68" : W = (Cmp Eq W) %"v4", #1
    => br %"v68" ? poll "L13" : "L69" };
  ir_blk{ @"L69":
    %"v70" : W = (Cmp Eq W) %"v4", #2
    => br %"v70" ? poll "L13" : "L71" };
  ir_blk{ @"L71":
    %"v72" : W = (Cmp Eq W) %"v4", #3
    => br %"v72" ? poll "L13" : poll "L43" };
  ir_blk{ @"L65":
    %"v74" : W = (Cmp Eq W) %"v4", #4
    => br %"v74" ? poll "L13" : "L75" };
  ir_blk{ @"L75":
    %"v76" : W = (Cmp Eq W) %"v4", #5
    => br %"v76" ? poll "L13" : "L77" };
  ir_blk{ @"L77":
    %"v78" : W = (Cmp Eq W) %"v4", #6
    => br %"v78" ? poll "L13" : "L79" };
  ir_blk{ @"L79":
    %"v80" : W = (Cmp Eq W) %"v4", #7
    => br %"v80" ? poll "L13" : poll "L43" };
  ir_blk{ @"L62":
    %"v82" : W = (Cmp Ult W) %"v4", #12
    => br %"v82" ? "L83" : "L84" };
  ir_blk{ @"L83":
    %"v85" : W = (Cmp Eq W) %"v4", #8
    => br %"v85" ? poll "L13" : "L86" };
  ir_blk{ @"L86":
    %"v87" : W = (Cmp Eq W) %"v4", #9
    => br %"v87" ? poll "L13" : "L88" };
  ir_blk{ @"L88":
    %"v89" : W = (Cmp Eq W) %"v4", #10
    => br %"v89" ? poll "L13" : "L90" };
  ir_blk{ @"L90":
    %"v91" : W = (Cmp Eq W) %"v4", #11
    => br %"v91" ? poll "L13" : poll "L43" };
  ir_blk{ @"L84":
    %"v93" : W = (Cmp Eq W) %"v4", #12
    => br %"v93" ? poll "L13" : "L94" };
  ir_blk{ @"L94":
    %"v95" : W = (Cmp Eq W) %"v4", #13
    => br %"v95" ? poll "L13" : "L96" };
  ir_blk{ @"L96":
    %"v97" : W = (Cmp Eq W) %"v4", #14
    => br %"v97" ? poll "L13" : "L98" };
  ir_blk{ @"L98":
    %"v99" : W = (Cmp Eq W) %"v4", #15
    => br %"v99" ? poll "L13" : poll "L43" };
  ir_blk{ @"L59":
    %"v101" : W = (Cmp Ult W) %"v4", #24
    => br %"v101" ? "L102" : "L103" };
  ir_blk{ @"L102":
    %"v104" : W = (Cmp Ult W) %"v4", #20
    => br %"v104" ? "L105" : "L106" };
  ir_blk{ @"L105":
    %"v107" : W = (Cmp Eq W) %"v4", #16
    => br %"v107" ? poll "L13" : "L108" };
  ir_blk{ @"L108":
    %"v109" : W = (Cmp Eq W) %"v4", #17
    => br %"v109" ? poll "L13" : "L110" };
  ir_blk{ @"L110":
    %"v111" : W = (Cmp Eq W) %"v4", #18
    => br %"v111" ? poll "L13" : "L112" };
  ir_blk{ @"L112":
    %"v113" : W = (Cmp Eq W) %"v4", #19
    => br %"v113" ? poll "L13" : poll "L43" };
  ir_blk{ @"L106":
    %"v115" : W = (Cmp Eq W) %"v4", #20
    => br %"v115" ? poll "L13" : "L116" };
  ir_blk{ @"L116":
    %"v117" : W = (Cmp Eq W) %"v4", #21
    => br %"v117" ? poll "L13" : "L118" };
  ir_blk{ @"L118":
    %"v119" : W = (Cmp Eq W) %"v4", #22
    => br %"v119" ? poll "L13" : "L120" };
  ir_blk{ @"L120":
    %"v121" : W = (Cmp Eq W) %"v4", #23
    => br %"v121" ? poll "L13" : poll "L43" };
  ir_blk{ @"L103":
    %"v123" : W = (Cmp Ult W) %"v4", #28
    => br %"v123" ? "L124" : "L125" };
  ir_blk{ @"L124":
    %"v126" : W = (Cmp Eq W) %"v4", #24
    => br %"v126" ? poll "L13" : "L127" };
  ir_blk{ @"L127":
    %"v128" : W = (Cmp Eq W) %"v4", #25
    => br %"v128" ? poll "L13" : "L129" };
  ir_blk{ @"L129":
    %"v130" : W = (Cmp Eq W) %"v4", #26
    => br %"v130" ? poll "L13" : "L131" }] [ir_blk{ @"L131":
    %"v132" : W = (Cmp Eq W) %"v4", #27
    => br %"v132" ? poll "L13" : poll "L43" };
  ir_blk{ @"L125":
    %"v134" : W = (Cmp Eq W) %"v4", #28
    => br %"v134" ? poll "L13" : "L135" };
  ir_blk{ @"L135":
    %"v136" : W = (Cmp Eq W) %"v4", #29
    => br %"v136" ? poll "L13" : "L137" };
  ir_blk{ @"L137":
    %"v138" : W = (Cmp Eq W) %"v4", #30
    => br %"v138" ? poll "L13" : "L139" };
  ir_blk{ @"L139":
    %"v140" : W = (Cmp Eq W) %"v4", #31
    => br %"v140" ? poll "L13" : poll "L43" };
  ir_blk{ @"L56":
    %"v142" : W = (Cmp Ult W) %"v4", #48
    => br %"v142" ? "L143" : "L144" };
  ir_blk{ @"L143":
    %"v145" : W = (Cmp Ult W) %"v4", #40
    => br %"v145" ? "L146" : "L147" };
  ir_blk{ @"L146":
    %"v148" : W = (Cmp Ult W) %"v4", #36
    => br %"v148" ? "L149" : "L150" };
  ir_blk{ @"L149":
    %"v151" : W = (Cmp Eq W) %"v4", #32
    => br %"v151" ? poll "L13" : "L152" };
  ir_blk{ @"L152":
    %"v153" : W = (Cmp Eq W) %"v4", #33
    => br %"v153" ? poll "L13" : "L154" };
  ir_blk{ @"L154":
    %"v155" : W = (Cmp Eq W) %"v4", #34
    => br %"v155" ? poll "L13" : "L156" };
  ir_blk{ @"L156":
    %"v157" : W = (Cmp Eq W) %"v4", #35
    => br %"v157" ? poll "L13" : poll "L43" };
  ir_blk{ @"L150":
    %"v159" : W = (Cmp Eq W) %"v4", #36
    => br %"v159" ? poll "L13" : "L160" };
  ir_blk{ @"L160":
    %"v161" : W = (Cmp Eq W) %"v4", #37
    => br %"v161" ? poll "L13" : "L162" };
  ir_blk{ @"L162":
    %"v163" : W = (Cmp Eq W) %"v4", #38
    => br %"v163" ? poll "L13" : "L164" };
  ir_blk{ @"L164":
    %"v165" : W = (Cmp Eq W) %"v4", #39
    => br %"v165" ? poll "L13" : poll "L43" };
  ir_blk{ @"L147":
    %"v167" : W = (Cmp Ult W) %"v4", #44
    => br %"v167" ? "L168" : "L169" };
  ir_blk{ @"L168":
    %"v170" : W = (Cmp Eq W) %"v4", #40
    => br %"v170" ? poll "L13" : "L171" };
  ir_blk{ @"L171":
    %"v172" : W = (Cmp Eq W) %"v4", #41
    => br %"v172" ? poll "L13" : "L173" };
  ir_blk{ @"L173":
    %"v174" : W = (Cmp Eq W) %"v4", #42
    => br %"v174" ? poll "L13" : "L175" };
  ir_blk{ @"L175":
    %"v176" : W = (Cmp Eq W) %"v4", #43
    => br %"v176" ? poll "L13" : poll "L43" };
  ir_blk{ @"L169":
    %"v178" : W = (Cmp Eq W) %"v4", #44
    => br %"v178" ? poll "L13" : "L179" };
  ir_blk{ @"L179":
    %"v180" : W = (Cmp Eq W) %"v4", #45
    => br %"v180" ? poll "L13" : "L181" };
  ir_blk{ @"L181":
    %"v182" : W = (Cmp Eq W) %"v4", #46
    => br %"v182" ? poll "L13" : "L183" };
  ir_blk{ @"L183":
    %"v184" : W = (Cmp Eq W) %"v4", #47
    => br %"v184" ? poll "L13" : poll "L43" };
  ir_blk{ @"L144":
    %"v186" : W = (Cmp Ult W) %"v4", #56
    => br %"v186" ? "L187" : "L188" };
  ir_blk{ @"L187":
    %"v189" : W = (Cmp Ult W) %"v4", #52
    => br %"v189" ? "L190" : "L191" };
  ir_blk{ @"L190":
    %"v192" : W = (Cmp Eq W) %"v4", #48
    => br %"v192" ? poll "L13" : "L193" };
  ir_blk{ @"L193":
    %"v194" : W = (Cmp Eq W) %"v4", #49
    => br %"v194" ? poll "L13" : "L195" };
  ir_blk{ @"L195":
    %"v196" : W = (Cmp Eq W) %"v4", #50
    => br %"v196" ? poll "L13" : "L197" };
  ir_blk{ @"L197":
    %"v198" : W = (Cmp Eq W) %"v4", #51
    => br %"v198" ? poll "L13" : poll "L43" };
  ir_blk{ @"L191":
    %"v200" : W = (Cmp Eq W) %"v4", #52
    => br %"v200" ? poll "L13" : "L201" };
  ir_blk{ @"L201":
    %"v202" : W = (Cmp Eq W) %"v4", #53
    => br %"v202" ? poll "L13" : "L203" };
  ir_blk{ @"L203":
    %"v204" : W = (Cmp Eq W) %"v4", #54
    => br %"v204" ? poll "L13" : "L205" };
  ir_blk{ @"L205":
    %"v206" : W = (Cmp Eq W) %"v4", #55
    => br %"v206" ? poll "L13" : poll "L43" };
  ir_blk{ @"L188":
    %"v208" : W = (Cmp Ult W) %"v4", #60
    => br %"v208" ? "L209" : "L210" };
  ir_blk{ @"L209":
    %"v211" : W = (Cmp Eq W) %"v4", #56
    => br %"v211" ? poll "L13" : "L212" };
  ir_blk{ @"L212":
    %"v213" : W = (Cmp Eq W) %"v4", #57
    => br %"v213" ? poll "L13" : "L214" };
  ir_blk{ @"L214":
    %"v215" : W = (Cmp Eq W) %"v4", #58
    => br %"v215" ? poll "L13" : "L216" };
  ir_blk{ @"L216":
    %"v217" : W = (Cmp Eq W) %"v4", #59
    => br %"v217" ? poll "L13" : poll "L43" };
  ir_blk{ @"L210":
    %"v219" : W = (Cmp Eq W) %"v4", #60
    => br %"v219" ? poll "L13" : "L220" }]) (app [ir_blk{ @"L220":
    %"v221" : W = (Cmp Eq W) %"v4", #61
    => br %"v221" ? poll "L13" : "L222" };
  ir_blk{ @"L222":
    %"v223" : W = (Cmp Eq W) %"v4", #62
    => br %"v223" ? poll "L13" : "L224" };
  ir_blk{ @"L224":
    %"v225" : W = (Cmp Eq W) %"v4", #63
    => br %"v225" ? poll "L13" : poll "L43" };
  ir_blk{ @"L53":
    %"v227" : W = (Cmp Ult W) %"v4", #96
    => br %"v227" ? "L228" : "L229" };
  ir_blk{ @"L228":
    %"v230" : W = (Cmp Ult W) %"v4", #80
    => br %"v230" ? "L231" : "L232" };
  ir_blk{ @"L231":
    %"v233" : W = (Cmp Ult W) %"v4", #72
    => br %"v233" ? "L234" : "L235" };
  ir_blk{ @"L234":
    %"v236" : W = (Cmp Ult W) %"v4", #68
    => br %"v236" ? "L237" : "L238" };
  ir_blk{ @"L237":
    %"v239" : W = (Cmp Eq W) %"v4", #64
    => br %"v239" ? poll "L32" : "L240" };
  ir_blk{ @"L240":
    %"v241" : W = (Cmp Eq W) %"v4", #65
    => br %"v241" ? poll "L32" : "L242" };
  ir_blk{ @"L242":
    %"v243" : W = (Cmp Eq W) %"v4", #66
    => br %"v243" ? poll "L32" : "L244" };
  ir_blk{ @"L244":
    %"v245" : W = (Cmp Eq W) %"v4", #67
    => br %"v245" ? poll "L32" : poll "L43" };
  ir_blk{ @"L238":
    %"v247" : W = (Cmp Eq W) %"v4", #68
    => br %"v247" ? poll "L32" : "L248" };
  ir_blk{ @"L248":
    %"v249" : W = (Cmp Eq W) %"v4", #69
    => br %"v249" ? poll "L32" : "L250" };
  ir_blk{ @"L250":
    %"v251" : W = (Cmp Eq W) %"v4", #70
    => br %"v251" ? poll "L32" : "L252" };
  ir_blk{ @"L252":
    %"v253" : W = (Cmp Eq W) %"v4", #71
    => br %"v253" ? poll "L32" : poll "L43" };
  ir_blk{ @"L235":
    %"v255" : W = (Cmp Ult W) %"v4", #76
    => br %"v255" ? "L256" : "L257" };
  ir_blk{ @"L256":
    %"v258" : W = (Cmp Eq W) %"v4", #72
    => br %"v258" ? poll "L32" : "L259" };
  ir_blk{ @"L259":
    %"v260" : W = (Cmp Eq W) %"v4", #73
    => br %"v260" ? poll "L32" : "L261" };
  ir_blk{ @"L261":
    %"v262" : W = (Cmp Eq W) %"v4", #74
    => br %"v262" ? poll "L32" : "L263" };
  ir_blk{ @"L263":
    %"v264" : W = (Cmp Eq W) %"v4", #75
    => br %"v264" ? poll "L32" : poll "L43" };
  ir_blk{ @"L257":
    %"v266" : W = (Cmp Eq W) %"v4", #76
    => br %"v266" ? poll "L32" : "L267" };
  ir_blk{ @"L267":
    %"v268" : W = (Cmp Eq W) %"v4", #77
    => br %"v268" ? poll "L32" : "L269" };
  ir_blk{ @"L269":
    %"v270" : W = (Cmp Eq W) %"v4", #78
    => br %"v270" ? poll "L32" : "L271" };
  ir_blk{ @"L271":
    %"v272" : W = (Cmp Eq W) %"v4", #79
    => br %"v272" ? poll "L32" : poll "L43" };
  ir_blk{ @"L232":
    %"v274" : W = (Cmp Ult W) %"v4", #88
    => br %"v274" ? "L275" : "L276" };
  ir_blk{ @"L275":
    %"v277" : W = (Cmp Ult W) %"v4", #84
    => br %"v277" ? "L278" : "L279" };
  ir_blk{ @"L278":
    %"v280" : W = (Cmp Eq W) %"v4", #80
    => br %"v280" ? poll "L32" : "L281" };
  ir_blk{ @"L281":
    %"v282" : W = (Cmp Eq W) %"v4", #81
    => br %"v282" ? poll "L32" : "L283" };
  ir_blk{ @"L283":
    %"v284" : W = (Cmp Eq W) %"v4", #82
    => br %"v284" ? poll "L32" : "L285" };
  ir_blk{ @"L285":
    %"v286" : W = (Cmp Eq W) %"v4", #83
    => br %"v286" ? poll "L32" : poll "L43" };
  ir_blk{ @"L279":
    %"v288" : W = (Cmp Eq W) %"v4", #84
    => br %"v288" ? poll "L32" : "L289" };
  ir_blk{ @"L289":
    %"v290" : W = (Cmp Eq W) %"v4", #85
    => br %"v290" ? poll "L32" : "L291" };
  ir_blk{ @"L291":
    %"v292" : W = (Cmp Eq W) %"v4", #86
    => br %"v292" ? poll "L32" : "L293" };
  ir_blk{ @"L293":
    %"v294" : W = (Cmp Eq W) %"v4", #87
    => br %"v294" ? poll "L32" : poll "L43" };
  ir_blk{ @"L276":
    %"v296" : W = (Cmp Ult W) %"v4", #92
    => br %"v296" ? "L297" : "L298" };
  ir_blk{ @"L297":
    %"v299" : W = (Cmp Eq W) %"v4", #88
    => br %"v299" ? poll "L32" : "L300" };
  ir_blk{ @"L300":
    %"v301" : W = (Cmp Eq W) %"v4", #89
    => br %"v301" ? poll "L32" : "L302" };
  ir_blk{ @"L302":
    %"v303" : W = (Cmp Eq W) %"v4", #90
    => br %"v303" ? poll "L32" : "L304" };
  ir_blk{ @"L304":
    %"v305" : W = (Cmp Eq W) %"v4", #91
    => br %"v305" ? poll "L32" : poll "L43" };
  ir_blk{ @"L298":
    %"v307" : W = (Cmp Eq W) %"v4", #92
    => br %"v307" ? poll "L32" : "L308" };
  ir_blk{ @"L308":
    %"v309" : W = (Cmp Eq W) %"v4", #93
    => br %"v309" ? poll "L32" : "L310" }] [ir_blk{ @"L310":
    %"v311" : W = (Cmp Eq W) %"v4", #94
    => br %"v311" ? poll "L32" : "L312" };
  ir_blk{ @"L312":
    %"v313" : W = (Cmp Eq W) %"v4", #95
    => br %"v313" ? poll "L32" : poll "L43" };
  ir_blk{ @"L229":
    %"v315" : W = (Cmp Ult W) %"v4", #112
    => br %"v315" ? "L316" : "L317" };
  ir_blk{ @"L316":
    %"v318" : W = (Cmp Ult W) %"v4", #104
    => br %"v318" ? "L319" : "L320" };
  ir_blk{ @"L319":
    %"v321" : W = (Cmp Ult W) %"v4", #100
    => br %"v321" ? "L322" : "L323" };
  ir_blk{ @"L322":
    %"v324" : W = (Cmp Eq W) %"v4", #96
    => br %"v324" ? poll "L32" : "L325" };
  ir_blk{ @"L325":
    %"v326" : W = (Cmp Eq W) %"v4", #97
    => br %"v326" ? poll "L32" : "L327" };
  ir_blk{ @"L327":
    %"v328" : W = (Cmp Eq W) %"v4", #98
    => br %"v328" ? poll "L32" : "L329" };
  ir_blk{ @"L329":
    %"v330" : W = (Cmp Eq W) %"v4", #99
    => br %"v330" ? poll "L32" : poll "L43" };
  ir_blk{ @"L323":
    %"v332" : W = (Cmp Eq W) %"v4", #100
    => br %"v332" ? poll "L32" : "L333" };
  ir_blk{ @"L333":
    %"v334" : W = (Cmp Eq W) %"v4", #101
    => br %"v334" ? poll "L32" : "L335" };
  ir_blk{ @"L335":
    %"v336" : W = (Cmp Eq W) %"v4", #102
    => br %"v336" ? poll "L32" : "L337" };
  ir_blk{ @"L337":
    %"v338" : W = (Cmp Eq W) %"v4", #103
    => br %"v338" ? poll "L32" : poll "L43" };
  ir_blk{ @"L320":
    %"v340" : W = (Cmp Ult W) %"v4", #108
    => br %"v340" ? "L341" : "L342" };
  ir_blk{ @"L341":
    %"v343" : W = (Cmp Eq W) %"v4", #104
    => br %"v343" ? poll "L32" : "L344" };
  ir_blk{ @"L344":
    %"v345" : W = (Cmp Eq W) %"v4", #105
    => br %"v345" ? poll "L32" : "L346" };
  ir_blk{ @"L346":
    %"v347" : W = (Cmp Eq W) %"v4", #106
    => br %"v347" ? poll "L32" : "L348" };
  ir_blk{ @"L348":
    %"v349" : W = (Cmp Eq W) %"v4", #107
    => br %"v349" ? poll "L32" : poll "L43" };
  ir_blk{ @"L342":
    %"v351" : W = (Cmp Eq W) %"v4", #108
    => br %"v351" ? poll "L32" : "L352" };
  ir_blk{ @"L352":
    %"v353" : W = (Cmp Eq W) %"v4", #109
    => br %"v353" ? poll "L32" : "L354" };
  ir_blk{ @"L354":
    %"v355" : W = (Cmp Eq W) %"v4", #110
    => br %"v355" ? poll "L32" : "L356" };
  ir_blk{ @"L356":
    %"v357" : W = (Cmp Eq W) %"v4", #111
    => br %"v357" ? poll "L32" : poll "L43" };
  ir_blk{ @"L317":
    %"v359" : W = (Cmp Ult W) %"v4", #120
    => br %"v359" ? "L360" : "L361" };
  ir_blk{ @"L360":
    %"v362" : W = (Cmp Ult W) %"v4", #116
    => br %"v362" ? "L363" : "L364" };
  ir_blk{ @"L363":
    %"v365" : W = (Cmp Eq W) %"v4", #112
    => br %"v365" ? poll "L32" : "L366" };
  ir_blk{ @"L366":
    %"v367" : W = (Cmp Eq W) %"v4", #113
    => br %"v367" ? poll "L32" : "L368" };
  ir_blk{ @"L368":
    %"v369" : W = (Cmp Eq W) %"v4", #114
    => br %"v369" ? poll "L32" : "L370" };
  ir_blk{ @"L370":
    %"v371" : W = (Cmp Eq W) %"v4", #115
    => br %"v371" ? poll "L32" : poll "L43" };
  ir_blk{ @"L364":
    %"v373" : W = (Cmp Eq W) %"v4", #116
    => br %"v373" ? poll "L32" : "L374" };
  ir_blk{ @"L374":
    %"v375" : W = (Cmp Eq W) %"v4", #117
    => br %"v375" ? poll "L32" : "L376" };
  ir_blk{ @"L376":
    %"v377" : W = (Cmp Eq W) %"v4", #118
    => br %"v377" ? poll "L32" : "L378" };
  ir_blk{ @"L378":
    %"v379" : W = (Cmp Eq W) %"v4", #119
    => br %"v379" ? poll "L32" : poll "L43" };
  ir_blk{ @"L361":
    %"v381" : W = (Cmp Ult W) %"v4", #124
    => br %"v381" ? "L382" : "L383" };
  ir_blk{ @"L382":
    %"v384" : W = (Cmp Eq W) %"v4", #120
    => br %"v384" ? poll "L32" : "L385" };
  ir_blk{ @"L385":
    %"v386" : W = (Cmp Eq W) %"v4", #121
    => br %"v386" ? poll "L32" : "L387" };
  ir_blk{ @"L387":
    %"v388" : W = (Cmp Eq W) %"v4", #122
    => br %"v388" ? poll "L32" : "L389" };
  ir_blk{ @"L389":
    %"v390" : W = (Cmp Eq W) %"v4", #123
    => br %"v390" ? poll "L32" : poll "L43" };
  ir_blk{ @"L383":
    %"v392" : W = (Cmp Eq W) %"v4", #124
    => br %"v392" ? poll "L32" : "L393" };
  ir_blk{ @"L393":
    %"v394" : W = (Cmp Eq W) %"v4", #125
    => br %"v394" ? poll "L32" : "L395" };
  ir_blk{ @"L395":
    %"v396" : W = (Cmp Eq W) %"v4", #126
    => br %"v396" ? poll "L32" : "L397" };
  ir_blk{ @"L397":
    %"v398" : W = (Cmp Eq W) %"v4", #127
    => br %"v398" ? poll "L32" : poll "L43" }]))) }.
