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

Definition hi_fn___new_exitfn : func :=
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
