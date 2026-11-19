(** This file defines checked IR from glibc’s `stdlib/cxa_atexit.os` object.
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

Definition fn___GI___cxa_atexit : func :=
  ir_fn{ "export" "__GI___cxa_atexit"(P %"v0", P %"v2", P %"v4") -> (RClass W) {
  @"start":
    %"v9" : P = Copy $"__exit_funcs";
    call %"v10" : W = $"__internal_atexit"(P %"v0", P %"v2", P %"v4", P %"v9")
    => ret %"v10"
} }.

Definition item___cxa_atexit : item :=
  (IAlias (a "__cxa_atexit") (a "export") (a "__GI___cxa_atexit")).

Definition item___exit_funcs : item :=
  (IData (a "__exit_funcs") LExport 8 [(Sym (a "glibc_cxa_atexit#initial") 0)]).

Definition item___exit_funcs_lock : item :=
  (IData (a "__exit_funcs_lock") LExport 4 [(Zero 4)]).

Definition fn___internal_atexit : func :=
  ir_fn{ "export" "__internal_atexit"(P %"v0", P %"v2", P %"v4", P %"v6") -> (RClass W) {
  @"start":
    %"v13" : L = Ptoi %"v0";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Ne L) %"v13", %"v14"
    => br %"v15" ? "L11" : "L10";
  @"L10":
    %"v16" : P = Copy $"glibc_cxa_atexit#str.233";
    %"v17" : P = Copy $"glibc_cxa_atexit#str.234";
    %"v18" : P = Copy $"glibc_cxa_atexit#str.235";
    call void $"__libc_assert_fail"(P %"v16", P %"v17", W #41, P %"v18")
    => goto "L11";
  @"L11":
    %"v20" : P = Copy $"__exit_funcs_lock";
    %"chk0" : A = (Check 0 4 Write 4) %"v20";
    %"v27" : W = (RawCas (CasNarrow Sw) 0) %"chk0", #0, #1;
    %"v28" : W = (Cmp Eq W) %"v27", #0
    => br %"v28" ? "L30" : "L29";
  @"L29":
    => goto "L30";
  @"L30":
    %"v31" : W = (Cmp Ne W) %"v27", #0
    => br %"v31" ? "L34" : "L23";
  @"L34":
    call void $"__GI___lll_lock_wait_private"(P %"v20")
    => goto "L23";
  @"L23":
    call %"v45" : P = $"__new_exitfn"(P %"v6");
    %"v50" : L = Ptoi %"v45";
    %"v52" : W = (Cmp Eq L) %"v50", %"v14"
    => br %"v52" ? "L46" : "L48";
  @"L46":
    %"v54" : P = Copy $"__exit_funcs_lock";
    %"chk1" : A = (Check 0 4 Read 1) %"v54";
    %"v58" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => goto "L59";
  @"L59" [%"v61" : W = phi("L46" => %"v58", "L59" => %"v62")]:
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v54";
    %"v62" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"v61", #0;
    %"v63" : W = (Cmp Eq W) %"v62", %"v61"
    => br %"v63" ? "L60" : poll "L59";
  @"L60":
    %"v68" : W = (Cmp Sgt W) %"v61", #1
    => br %"v68" ? "L71" : "L66";
  @"L71":
    call void $"__GI___lll_lock_wake_private"(P %"v54")
    => goto "L66";
  @"L66":
    => ret #4294967295;
  @"L48":
    %"v86" = %"v45" +p #8;
    %"chk3" : A = (Check 0 8 Write 8) %"v86";
    store.ptr [%"chk3" + 0] <- %"v0";
    %"v90" = %"v86" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v90";
    store.ptr [%"chk4" + 0] <- %"v2";
    %"v94" = %"v86" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v94";
    store.ptr [%"chk5" + 0] <- %"v4";
    %"chk6" : A = (HalfCheck Lower 0 8 Write 1) %"chk3", %"v45";
    store Wl [%"chk6" + 0] <- #4;
    %"v98" : P = Copy $"__exit_funcs_lock";
    %"chk7" : A = (Check 0 4 Read 1) %"v98";
    %"v102" : W = (RawLoad (LdNarrow Sw) 0) %"chk7"
    => goto "L103";
  @"L103" [%"v105" : W = phi("L48" => %"v102", "L103" => %"v106")]:
    %"chk8" : A = (HalfCheck Lower 0 4 Write 4) %"chk7", %"v98";
    %"v106" : W = (RawCas (CasNarrow Sw) 0) %"chk8", %"v105", #0;
    %"v107" : W = (Cmp Eq W) %"v106", %"v105"
    => br %"v107" ? "L104" : poll "L103";
  @"L104":
    %"v112" : W = (Cmp Sgt W) %"v105", #1
    => br %"v112" ? "L115" : "L110";
  @"L115":
    call void $"__GI___lll_lock_wake_private"(P %"v98")
    => goto "L110";
  @"L110":
    => ret #0
} }.

Definition fn___new_exitfn : func :=
  ir_fn{ "export" "__new_exitfn"(P %"v0") -> (RClass P) {
  @"start":
    %"v9" : P = Copy $"__exit_funcs_done";
    %"chk0" : A = (Check 0 1 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Ub) 0) %"chk0"
    => br %"v10" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"chk1" : A = (Check 0 8 Read 8) %"v0";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L14";
  @"L14" [%"pr.6" : L = phi("L47" => %"pr.8", "L8" => #0); %"pr.3" : P = phi("L47" => %"v55", "L8" => %"v13"); %"pr.1" : P = phi("L47" => %"pr.3", "L8" => #0)]:
    %"v19" : L = Ptoi %"pr.3";
    %"v20" : L = Ptoi #0;
    %"v21" : W = (Cmp Ne L) %"v19", %"v20"
    => br %"v21" ? "L15" : "L17";
  @"L15":
    %"v23" = %"pr.3" +p #8;
    %"chk2" : A = (Check 0 8 Read 1) %"v23";
    %"v24" : L = (RawLoad LdL 0) %"chk2"
    => goto "L25";
  @"L25" [%"pr.8" : L = phi("L15" => %"v24", "L26" => %"v37")]:
    %"v30" : W = (Cmp Ugt L) %"pr.8", #0
    => br %"v30" ? "L26" : "L28";
  @"L26":
    %"v35" = %"pr.3" +p #16;
    %"v37" : L = Sub %"pr.8", #1;
    %"v38" : L = Shl %"v37", #5;
    %"v39" = %"v35" +p %"v38";
    %"chk3" : A = (Check 0 8 Read 1) %"v39";
    %"v40" : L = (RawLoad LdL 0) %"chk3";
    %"v41" : W = (Cmp Ne L) %"v40", #0
    => br %"v41" ? "L28" : poll "L25";
  @"L28":
    => br %"v30" ? "L17" : "L47";
  @"L47":
    %"v52" = %"pr.3" +p #8;
    %"chk4" : A = (Renew 0 8 Write 1) %"chk2", %"v52";
    store Wl [%"chk4" + 0] <- #0;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"pr.3";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk5"
    => goto poll "L14";
  @"L17" [%"pr.7" : L = phi("L14" => %"pr.6", "L28" => %"pr.8")]:
    %"v62" : W = (Cmp Eq L) %"v19", %"v20"
    => br %"v62" ? "L64" : "L63";
  @"L63":
    %"v67" : W = (Cmp Eq L) %"pr.7", #32
    => goto "L64";
  @"L64" [%"v69" : W = phi("L17" => #1, "L63" => %"v67")]:
    => br %"v69" ? "L56" : "L57";
  @"L56":
    %"v74" : L = Ptoi %"pr.1";
    %"v76" : W = (Cmp Eq L) %"v74", %"v20"
    => br %"v76" ? "L70" : "L72";
  @"L70":
    => br %"v21" ? "L79" : "L78";
  @"L78":
    %"v84" : P = Copy $"glibc_cxa_atexit#str.236";
    %"v85" : P = Copy $"glibc_cxa_atexit#str.234";
    %"v86" : P = Copy $"glibc_cxa_atexit#str.237";
    call void $"__libc_assert_fail"(P %"v84", P %"v85", W #110, P %"v86")
    => goto "L79";
  @"L79":
    call %"v87" : P = $"calloc"(L #1, L #1040);
    %"v92" : L = Ptoi %"v87";
    %"v94" : W = (Cmp Ne L) %"v92", %"v20"
    => br %"v94" ? "L88" : "L72";
  @"L88":
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Write 8) %"v87";
    store.ptr [%"chk7" + 0] <- %"v97";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk1", %"v0";
    store.ptr [%"chk8" + 0] <- %"v87"
    => goto "L72";
  @"L72" [%"pr.2" : P = phi("L88" => %"v87", "L79" => %"v87", "L56" => %"pr.1")]:
    %"v104" : L = Ptoi %"pr.2";
    %"v106" : W = (Cmp Ne L) %"v104", %"v20"
    => br %"v106" ? "L100" : "L58";
  @"L100":
    %"v108" = %"pr.2" +p #16;
    %"v111" = %"pr.2" +p #8;
    %"chk9" : A = (Check 0 8 Write 1) %"v111";
    store Wl [%"chk9" + 0] <- #1
    => goto "L58";
  @"L57":
    %"v113" = %"pr.3" +p #16;
    %"v115" : L = Shl %"pr.7", #5;
    %"v116" = %"v113" +p %"v115";
    %"v118" = %"pr.3" +p #8;
    %"v120" : L = Add %"pr.7", #1;
    %"chk10" : A = (Check 0 8 Write 1) %"v118";
    store Wl [%"chk10" + 0] <- %"v120"
    => goto "L58";
  @"L58" [%"pr.5" : P = phi("L57" => %"v116", "L100" => %"v108", "L72" => #0)]:
    %"v125" : L = Ptoi %"pr.5";
    %"v127" : W = (Cmp Ne L) %"v125", %"v20"
    => br %"v127" ? "L121" : "L123";
  @"L121":
    %"chk11" : A = (Check 0 8 Write 1) %"pr.5";
    store Wl [%"chk11" + 0] <- #1;
    %"v129" : P = Copy $"__new_exitfn_called";
    %"chk12" : A = (Check 0 8 Read 1) %"v129";
    %"v130" : L = (RawLoad LdL 0) %"chk12";
    %"v131" : L = Add %"v130", #1;
    %"chk13" : A = (Renew 0 8 Write 1) %"chk12", %"v129";
    store Wl [%"chk13" + 0] <- %"v131"
    => goto "L123";
  @"L123":
    => ret %"pr.5"
} }.

Definition item___new_exitfn_called : item :=
  (IData (a "__new_exitfn_called") LExport 8 [(Zero 8)]).

Definition item_glibc_cxa_atexit'23initial : item :=
  (IData (a "glibc_cxa_atexit#initial") LLocal 8 [(Zero 1040)]).

Definition item_glibc_cxa_atexit'23str'2e233 : item :=
  (IData (a "glibc_cxa_atexit#str.233") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 110); (Item Wb 99); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_cxa_atexit'23str'2e234 : item :=
  (IData (a "glibc_cxa_atexit#str.234") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 120); (Item Wb 97); (Item Wb 95); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_cxa_atexit'23str'2e235 : item :=
  (IData (a "glibc_cxa_atexit#str.235") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 95); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_cxa_atexit'23str'2e236 : item :=
  (IData (a "glibc_cxa_atexit#str.236") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_cxa_atexit'23str'2e237 : item :=
  (IData (a "glibc_cxa_atexit#str.237") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 110); (Item Wb 101); (Item Wb 119); (Item Wb 95); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 102); (Item Wb 110); (Item Wb 0)]).
