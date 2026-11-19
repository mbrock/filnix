(** This file defines checked IR from glibc’s `io/getcwd.os` object.
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

Definition fn___GI___getcwd : func :=
  ir_fn{ "export" "__GI___getcwd"(P %"v0", L %"v2") -> (RClass P) {
  @"start":
    %"v11" : W = (Cmp Eq L) %"v2", #0
    => br %"v11" ? "L7" : "L9";
  @"L7":
    %"v16" : L = Ptoi %"v0";
    %"v17" : L = Ptoi #0;
    %"v18" : W = (Cmp Ne L) %"v16", %"v17"
    => br %"v18" ? "L12" : "L14";
  @"L12":
    %"v19" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v19";
    store Ww [%"chk0" + 0] <- #22
    => ret #0;
  @"L14":
    call %"v24" : W = $"__GI___getpagesize"();
    %"v25" : W = (Cmp Slt W) %"v24", #4096
    => br %"v25" ? "L23" : "L22";
  @"L22":
    call %"v26" : W = $"__GI___getpagesize"()
    => goto "L23";
  @"L23" [%"v27" : W = phi("L22" => %"v26", "L14" => #4096)]:
    %"v28" : L = (Ext Sw) %"v27"
    => goto "L9";
  @"L9" [%"pr.3" : L = phi("L23" => %"v28", "start" => %"v2")]:
    %"v33" : L = Ptoi %"v0";
    %"v34" : L = Ptoi #0;
    %"v35" : W = (Cmp Eq L) %"v33", %"v34"
    => br %"v35" ? "L29" : "L31";
  @"L29":
    call %"v37" : P = $"malloc"(L %"pr.3");
    %"v42" : L = Ptoi %"v37";
    %"v44" : W = (Cmp Eq L) %"v42", %"v34"
    => br %"v44" ? "L38" : "L31";
  @"L38":
    => ret #0;
  @"L31" [%"pr.2" : P = phi("L29" => %"v37", "L9" => %"v0")]:
    call %"v53" : P = $"zsys_getcwd"(P %"pr.2", L %"pr.3");
    %"v54" : L = Ptoi %"v53";
    %"v55" : W = (Cmp Ne L) %"v54", #0
    => br %"v55" ? "L50" : "L49";
  @"L49":
    => goto "L50";
  @"L50" [%"v57" : W = phi("L49" => #4294967295, "L31" => #1)]:
    %"v62" : W = (Cmp Sgt W) %"v57", #0
    => br %"v62" ? "L63" : "L64";
  @"L63":
    %"chk1" : A = (Check 0 1 Read 1) %"pr.2";
    %"v67" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v68" : W = (Cmp Eq W) %"v67", #47
    => goto "L64";
  @"L64" [%"v70" : W = phi("L50" => #0, "L63" => %"v68")]:
    => br %"v70" ? "L58" : "L60";
  @"L58":
    => br %"v35" ? "L73" : "L72";
  @"L72":
    => goto "L73";
  @"L73" [%"pr.1" : P = phi("L72" => %"v0", "L58" => %"pr.2")]:
    => ret %"pr.1";
  @"L60":
    %"v85" : W = (Cmp Sge W) %"v57", #0
    => br %"v85" ? "L87" : "L86";
  @"L86":
    %"v88" : P = Copy $"__libc_errno";
    %"chk2" : A = (Check 0 4 Read 1) %"v88";
    %"v89" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v90" : W = (Cmp Eq W) %"v89", #36
    => goto "L87";
  @"L87" [%"v92" : W = phi("L60" => #1, "L86" => %"v90")]:
    => br %"v92" ? "L93" : "L83";
  @"L93":
    %"v99" : P = Copy $"glibc_getcwd#str.242";
    %"v100" : L = Ptoi %"v99";
    %"v102" : W = (Cmp Eq L) %"v100", #0
    => br %"v102" ? "L83" : "L98";
  @"L98":
    %"v104" : P = Copy $"glibc_getcwd#str.243";
    %"v105" : P = Copy $"glibc_getcwd#str.244";
    %"v106" : P = Copy $"glibc_getcwd#str.245";
    %"v107" : P = Copy $"glibc_getcwd#str.246";
    call void $"zerrorf"(P %"v104", P %"v105", W #94, P %"v106", P %"v107")
    => goto "L83";
  @"L83":
    %"v111" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Read 1) %"v111";
    %"v112" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v113" : W = (Cmp Ne W) %"v112", #34
    => br %"v113" ? "L115" : "L114";
  @"L114":
    %"v119" : W = (Cmp Ne L) %"v33", %"v34"
    => goto "L115";
  @"L115" [%"v121" : W = phi("L83" => #1, "L114" => %"v119")]:
    => br %"v121" ? "L123" : "L122";
  @"L122":
    %"v125" : W = (Cmp Ne L) %"v2", #0
    => goto "L123";
  @"L123" [%"v127" : W = phi("L115" => #1, "L122" => %"v125")]:
    => br %"v127" ? "L110" : "L109";
  @"L109":
    %"v128" : P = Copy $"glibc_getcwd#str.247";
    %"v129" : P = Copy $"glibc_getcwd#str.244";
    %"v130" : P = Copy $"glibc_getcwd#str.245";
    call void $"__libc_assert_fail"(P %"v128", P %"v129", W #100, P %"v130")
    => goto "L110";
  @"L110":
    => br %"v35" ? "L131" : "L133";
  @"L131":
    call void $"free"(P %"pr.2")
    => goto "L133";
  @"L133":
    => ret #0
} }.

Definition item_glibc_getcwd'23str'2e242 : item :=
  (IData (a "glibc_getcwd#str.242") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 104); (Item Wb 111); (Item Wb 117); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 101); (Item Wb 114); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_getcwd'23str'2e243 : item :=
  (IData (a "glibc_getcwd#str.243") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition item_glibc_getcwd'23str'2e244 : item :=
  (IData (a "glibc_getcwd#str.244") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 118); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 47); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 99); (Item Wb 119); (Item Wb 100); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_getcwd'23str'2e245 : item :=
  (IData (a "glibc_getcwd#str.245") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 99); (Item Wb 119); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_getcwd'23str'2e246 : item :=
  (IData (a "glibc_getcwd#str.246") (LRo (a "local")) 1 [(Item Wb 33); (Item Wb 34); (Item Wb 83); (Item Wb 104); (Item Wb 111); (Item Wb 117); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 101); (Item Wb 114); (Item Wb 101); (Item Wb 34); (Item Wb 0)]).

Definition item_glibc_getcwd'23str'2e247 : item :=
  (IData (a "glibc_getcwd#str.247") (LRo (a "local")) 1 [(Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 110); (Item Wb 111); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 69); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 71); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).
