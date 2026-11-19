(** This file defines checked IR from glibc’s `libio/libc_fatal.os` object.
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

Definition fn___GI___libc_fatal : func :=
  ir_fn{ "export" "__GI___libc_fatal"(P %"v0") -> RVoid {
  @"start":
    => goto "L3";
  @"L3":
    %"v5" : P = Copy $"glibc_libc_fatal#str.299";
    %"v6" : P = Copy $"glibc_libc_fatal#str.300";
    call void $"__libc_message_impl"(P %"v5", P %"v6", P %"v0")
    => goto poll "L3"
} }.

Definition fn___libc_message_impl : func :=
  ir_fn{ "export" "__libc_message_impl"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v4" : P = (Alloc 8) #24;
    %"v13" : P = (Alloc 8) #240;
    %"va_args" : P = VaArgs #16;
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- %"va_args"
    => goto "L18";
  @"L18" [%"pr.8" : P = phi("start" => %"v2", "L56" => %"pr.9"); %"pr.4" : L = phi("start" => #0, "L56" => %"v94"); %"pr.2" : W = phi("start" => #0, "L56" => %"v96")]:
    %"chk1" : A = (Check 0 1 Read 1) %"pr.8";
    %"v22" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v23" : W = (Cmp Ne W) %"v22", #0
    => br %"v23" ? "L26" : "L20";
  @"L26" [%"pr.10" : P = phi("L18" => %"pr.8", "L27" => %"v43")]:
    %"chk2" : A = (Check 0 1 Read 1) %"pr.10";
    %"v31" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v32" : W = (Cmp Ne W) %"v31", #37
    => br %"v32" ? "L34" : "L33";
  @"L33":
    %"v36" = %"pr.10" +p #1;
    %"chk3" : A = (HalfCheck Upper 0 1 Read 1) %"chk2", %"v36";
    %"v37" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v38" : W = (Cmp Ne W) %"v37", #115
    => goto "L34";
  @"L34" [%"v40" : W = phi("L26" => #1, "L33" => %"v38")]:
    => br %"v40" ? "L27" : "L28";
  @"L27":
    %"v42" = %"pr.10" +p #1;
    call %"v43" : P = $"__GI___strchrnul"(P %"v42", W #37);
    %"chk4" : A = (Check 0 1 Read 1) %"v43";
    %"v49" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v50" : W = (Cmp Eq W) %"v49", #0
    => br %"v50" ? "L28" : poll "L26";
  @"L28" [%"pr.11" : P = phi("L34" => %"pr.10", "L27" => %"v43")]:
    %"chk5" : A = (Renew 0 1 Read 1) %"chk1", %"pr.8";
    %"v59" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v60" : W = (Cmp Eq W) %"v59", #37
    => br %"v60" ? "L61" : "L62";
  @"L61":
    %"v64" = %"pr.8" +p #1;
    %"chk6" : A = (HalfCheck Upper 0 1 Read 1) %"chk1", %"v64";
    %"v65" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v66" : W = (Cmp Eq W) %"v65", #115
    => goto "L62";
  @"L62" [%"v68" : W = phi("L28" => #0, "L61" => %"v66")]:
    => br %"v68" ? "L54" : "L55";
  @"L54":
    %"v69" : P = VaArg %"v4";
    call %"v71" : L = $"__GI_strlen"(P %"v69");
    %"v73" = %"pr.8" +p #2
    => goto "L56";
  @"L55":
    %"v77" : L = Ptoi %"pr.11";
    %"v78" : L = Ptoi %"pr.8";
    %"v79" : L = Sub %"v77", %"v78"
    => goto "L56";
  @"L56" [%"pr.13" : L = phi("L54" => %"v71", "L55" => %"v79"); %"pr.12" : P = phi("L54" => %"v69", "L55" => %"pr.8"); %"pr.9" : P = phi("L54" => %"v73", "L55" => %"pr.11")]:
    %"v82" : L = (Ext Sw) %"pr.2";
    %"v83" : L = Shl %"v82", #4;
    %"v84" = %"v13" +p %"v83";
    %"chk7" : A = (Check 0 8 Write 8) %"v84";
    store.ptr [%"chk7" + 0] <- %"pr.12";
    %"v90" = %"v84" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 1) %"chk7", %"v90";
    store Wl [%"chk8" + 0] <- %"pr.13";
    %"v94" : L = Add %"pr.4", %"pr.13";
    %"v96" : W = Add %"pr.2", #1;
    %"v103" : W = (Cmp Sgt W) %"v96", #15
    => br %"v103" ? "L97" : poll "L18";
  @"L97":
    %"v108" : P = Copy $"glibc_libc_fatal#str.298";
    %"chk9" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk9" + 0] <- %"v108";
    %"v110" = %"v13" +p #8;
    %"chk10" : A = (HalfCheck Upper 0 8 Write 1) %"chk9", %"v110";
    store Wl [%"chk10" + 0] <- #70
    => goto "L20";
  @"L20" [%"pr.5" : L = phi("L18" => %"pr.4", "L97" => #70); %"pr.3" : W = phi("L18" => %"pr.2", "L97" => #1)]:
    %"v118" : W = (Cmp Sgt W) %"pr.3", #0
    => br %"v118" ? "L114" : "L116";
  @"L114":
    %"v121" : L = (Ext Sw) %"pr.3"
    => goto "iw_1.L9";
  @"iw_1.L9":
    call %"iw_1.v15" : L = $"zsys_writev"(W #2, P %"v13", W %"v121");
    %"iw_1.v17" : W = (Cmp Slt L) %"iw_1.v15", #0
    => br %"iw_1.v17" ? "iw_1.L18" : "iw_1.L19";
  @"iw_1.L18":
    %"iw_1.v20" : P = Copy $"__libc_errno";
    %"chk11" : A = (Check 0 4 Read 1) %"iw_1.v20";
    %"iw_1.v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"iw_1.v22" : W = (Cmp Eq W) %"iw_1.v21", #4
    => goto "iw_1.L19";
  @"iw_1.L19" [%"iw_1.v24" : W = phi("iw_1.L9" => #0, "iw_1.L18" => %"iw_1.v22")]:
    => br %"iw_1.v24" ? poll "iw_1.L9" : "iw_1.join";
  @"iw_1.join":
    %"v126" : L = Add %"pr.5", #4;
    %"v127" : L = Add %"v126", #1;
    %"v128" : P = Copy $"_dl_pagesize";
    %"chk12" : A = (Check 0 8 Read 1) %"v128";
    %"v129" : L = (RawLoad LdL 0) %"chk12";
    %"v130" : L = Add %"v127", %"v129";
    %"v131" : L = Sub %"v130", #1;
    %"v132" : P = Copy $"_dl_pagesize";
    %"chk13" : A = (Check 0 8 Read 1) %"v132";
    %"v133" : L = (RawLoad LdL 0) %"chk13";
    %"v134" : L = Neg %"v133";
    %"v135" : L = And %"v131", %"v134";
    call %"v141" : P = $"__GI___mmap"(P #0, L %"v135", W #3, W #34, W #4294967295, L #0);
    (Flight (a "v148") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v149" : L = Ptoi %"v141";
    %"v150" : L = Ptoi %"v148";
    %"v151" : W = (Cmp Ne L) %"v149", %"v150"
    => br %"v151" ? "L142" : "L116";
  @"L142":
    %"chk14" : A = (Check 0 4 Write 1) %"v141";
    store Ww [%"chk14" + 0] <- %"v135";
    %"v158" = %"v141" +p #4
    => goto "L160";
  @"L160" [%"pr.15" : W = phi("L142" => #0, "L161" => %"v181"); %"pr.14" : P = phi("L142" => %"v158", "L161" => %"v179")]:
    %"v166" : W = (Cmp Slt W) %"pr.15", %"pr.3"
    => br %"v166" ? "L161" : "L163";
  @"L161":
    %"v169" : L = (Ext Sw) %"pr.15";
    %"v170" : L = Shl %"v169", #4;
    %"v171" = %"v13" +p %"v170";
    %"chk15" : A = (Check 0 8 Read 8) %"v171";
    %"v172" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v177" = %"v171" +p #8;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 1) %"chk15", %"v177";
    %"v178" : L = (RawLoad LdL 0) %"chk16";
    call %"v179" : P = $"__GI_mempcpy"(P %"pr.14", P %"v172", L %"v178");
    %"v181" : W = Add %"pr.15", #1
    => goto poll "L160";
  @"L163":
    %"chk17" : A = (Check 0 1 Write 1) %"pr.14";
    store Wb [%"chk17" + 0] <- #0;
    call void $"__set_vma_name"(P %"v141", L %"v135", P %"v0");
    %"v187" : P = Copy $"__GI___abort_msg";
    %"chk18" : A = (Check 0 8 Read 8) %"v187";
    %"v189" : P = (RawLoadPointer 0 [AtomicRead]) %"chk18"
    => goto "L190";
  @"L190" [%"v192" : P = phi("L163" => %"v189", "L190" => %"v193")]:
    %"chk19" : A = (HalfCheck Lower 0 8 Write 8) %"chk18", %"v187";
    %"v193" : P = (RawCas CasP 0) %"chk19", %"v192", %"v141";
    %"v194" : L = Ptoi %"v193";
    %"v195" : L = Ptoi %"v192";
    %"v196" : W = (Cmp Eq L) %"v194", %"v195"
    => br %"v196" ? "L191" : poll "L190";
  @"L191":
    %"v202" : L = Ptoi #0;
    %"v203" : W = (Cmp Ne L) %"v195", %"v202"
    => br %"v203" ? "L197" : "L116";
  @"L197":
    %"chk20" : A = (Check 0 4 Read 1) %"v192";
    %"v206" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v207" : L = (Ext Uw) %"v206";
    call %"v208" : W = $"__GI___munmap"(P %"v192", L %"v207")
    => goto "L116";
  @"L116":
    call void $"__GI_abort"()
    => ret void
} }.

Definition item_glibc_libc_fatal'23str'2e298 : item :=
  (IData (a "glibc_libc_fatal#str.298") (LRo (a "local")) 1 (app [(Item Wb 70); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 58); (Item Wb 32); (Item Wb 73); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 95)] [(Item Wb 109); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 46); (Item Wb 32); (Item Wb 84); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 97); (Item Wb 110); (Item Wb 121); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)])).

Definition item_glibc_libc_fatal'23str'2e299 : item :=
  (IData (a "glibc_libc_fatal#str.299") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_libc_fatal'23str'2e300 : item :=
  (IData (a "glibc_libc_fatal#str.300") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 0)]).
