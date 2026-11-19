(** This file defines checked IR from glibc’s `libio/iopopen.os` object.
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

Definition fn__IO_new_proc_close : func :=
  ir_fn{ "export" "_IO_new_proc_close"(P %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 4) #4;
    %"v9" : P = (Alloc 8) #32;
    %"v204" : P = (Alloc 4) #4;
    %"v4" : P = Copy $"glibc_iopopen#proc_file_chain";
    %"v11" : P = Copy $"glibc_iopopen#unlock";
    %"v12" = %"v9" +p #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v12";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v9";
    store.ptr [%"chk1" + 0] <- %"v11";
    call void $"__GI___libc_cleanup_push_defer"(P %"v9");
    call %"v23" : P = $"zthread_self_cookie"();
    %"v27" : P = Copy $"__libc_single_threaded_internal";
    %"chk2" : A = (Check 0 1 Read 1) %"v27";
    %"v28" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v29" : W = (Cmp Ne W) %"v28", #0
    => br %"v29" ? "L30" : "L31";
  @"L30":
    %"v32" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v33" = %"v32" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v35" : L = Ptoi %"v34";
    %"v36" : L = Ptoi #0;
    %"v37" : W = (Cmp Eq L) %"v35", %"v36"
    => goto "L31";
  @"L31" [%"v39" : W = phi("start" => #0, "L30" => %"v37")]:
    => br %"v39" ? "L24" : "L25";
  @"L24":
    %"v40" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk4" : A = (Check 0 4 Write 1) %"v40";
    store Ww [%"chk4" + 0] <- #1;
    %"v41" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v42" = %"v41" +p #8;
    %"chk5" : A = (Check 0 8 Write 8) %"v42";
    store.ptr [%"chk5" + 0] <- %"v23"
    => goto "L86";
  @"L25":
    %"v47" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v48" = %"v47" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v51" : L = Ptoi %"v49";
    %"v52" : L = Ptoi %"v23";
    %"v53" : W = (Cmp Ne L) %"v51", %"v52"
    => br %"v53" ? "L44" : "L45";
  @"L44":
    %"v55" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk7" : A = (Check 0 4 Write 4) %"v55";
    %"v62" : W = (RawCas (CasNarrow Sw) 0) %"chk7", #0, #1;
    %"v63" : W = (Cmp Eq W) %"v62", #0
    => br %"v63" ? "L65" : "L64";
  @"L64":
    => goto "L65";
  @"L65":
    %"v66" : W = (Cmp Ne W) %"v62", #0
    => br %"v66" ? "L69" : "L58";
  @"L69":
    call void $"__GI___lll_lock_wait_private"(P %"v55")
    => goto "L58";
  @"L58":
    %"v79" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v80" = %"v79" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"v80";
    store.ptr [%"chk8" + 0] <- %"v23"
    => goto "L86";
  @"L45":
    %"v82" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v83" = %"v82" +p #4;
    %"chk9" : A = (Check 0 4 Read 1) %"v83";
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v85" : W = Add %"v84", #1;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk9", %"v83";
    store Ww [%"chk10" + 0] <- %"v85"
    => goto "L86";
  @"L86" [%"pr.1" : P = phi("L88" => %"v112", "L24" => %"v4", "L58" => %"v4", "L45" => %"v4")]:
    %"chk11" : A = (Check 0 8 Read 8) %"pr.1";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v92" : L = Ptoi %"v91";
    %"v93" : L = Ptoi #0;
    %"v94" : W = (Cmp Ne L) %"v92", %"v93"
    => br %"v94" ? "L87" : "L89";
  @"L87":
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v101" : L = Ptoi %"v99";
    %"v102" : L = Ptoi %"v0";
    %"v103" : W = (Cmp Eq L) %"v101", %"v102"
    => br %"v103" ? "L95" : "L88";
  @"L95":
    %"v106" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v107" = %"v106" +p #232;
    %"chk14" : A = (Check 0 8 Read 8) %"v107";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Renew 0 8 Write 8) %"chk11", %"pr.1";
    store.ptr [%"chk15" + 0] <- %"v108"
    => goto "L89";
  @"L88":
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v112" = %"v111" +p #232
    => goto poll "L86";
  @"L89" [%"pr.2" : W = phi("L86" => #4294967295, "L95" => #0)]:
    %"v119" : P = Copy $"__libc_single_threaded_internal";
    %"chk17" : A = (Check 0 1 Read 1) %"v119";
    %"v120" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v121" : W = (Cmp Ne W) %"v120", #0
    => br %"v121" ? "L122" : "L123";
  @"L122":
    %"v124" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v125" = %"v124" +p #4;
    %"chk18" : A = (Check 0 4 Read 1) %"v125";
    %"v126" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v127" : W = (Cmp Eq W) %"v126", #0
    => goto "L123";
  @"L123" [%"v129" : W = phi("L89" => #0, "L122" => %"v127")]:
    => br %"v129" ? "L116" : "L117";
  @"L116":
    %"v130" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v131" = %"v130" +p #8;
    %"chk19" : A = (Check 0 8 Write 8) %"v131";
    store.ptr [%"chk19" + 0] <- #0;
    %"v132" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk20" : A = (Check 0 4 Write 1) %"v132";
    store Ww [%"chk20" + 0] <- #0
    => goto "L175";
  @"L117":
    %"v136" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v137" = %"v136" +p #4;
    %"chk21" : A = (Check 0 4 Read 1) %"v137";
    %"v138" : W = (RawLoad (LdNarrow Sw) 0) %"chk21";
    %"v139" : W = (Cmp Eq W) %"v138", #0
    => br %"v139" ? "L133" : "L134";
  @"L133":
    %"v140" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v141" = %"v140" +p #8;
    %"chk22" : A = (Check 0 8 Write 8) %"v141";
    store.ptr [%"chk22" + 0] <- #0;
    %"v143" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk23" : A = (Check 0 4 Read 1) %"v143";
    %"v147" : W = (RawLoad (LdNarrow Sw) 0) %"chk23"
    => goto "L148";
  @"L148" [%"v150" : W = phi("L133" => %"v147", "L148" => %"v151")]:
    %"chk24" : A = (HalfCheck Lower 0 4 Write 4) %"chk23", %"v143";
    %"v151" : W = (RawCas (CasNarrow Sw) 0) %"chk24", %"v150", #0;
    %"v152" : W = (Cmp Eq W) %"v151", %"v150"
    => br %"v152" ? "L149" : poll "L148";
  @"L149":
    %"v157" : W = (Cmp Sgt W) %"v150", #1
    => br %"v157" ? "L160" : "L175";
  @"L160":
    call void $"__GI___lll_lock_wake_private"(P %"v143")
    => goto "L175";
  @"L134":
    %"v171" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v172" = %"v171" +p #4;
    %"chk25" : A = (Check 0 4 Read 1) %"v172";
    %"v173" : W = (RawLoad (LdNarrow Sw) 0) %"chk25";
    %"v174" : W = Sub %"v173", #1;
    %"chk26" : A = (Renew 0 4 Write 1) %"chk25", %"v172";
    store Ww [%"chk26" + 0] <- %"v174"
    => goto "L175";
  @"L175":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v9");
    %"v189" : W = (Cmp Slt W) %"pr.2", #0
    => br %"v189" ? "L191" : "L190";
  @"L190":
    %"v193" = %"v0" +p #112;
    %"chk27" : A = (Check 0 4 Read 1) %"v193";
    %"v194" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    call %"v195" : W = $"__GI___close_nocancel"(W %"v194");
    %"v196" : W = (Cmp Slt W) %"v195", #0
    => goto "L191";
  @"L191" [%"v198" : W = phi("L175" => #1, "L190" => %"v196")]:
    => br %"v198" ? "L185" : "L201";
  @"L185":
    => ret #4294967295;
  @"L201":
    call %"v205" : W = $"__GI___pthread_setcancelstate"(W #1, P %"v204");
    %"v207" = %"v0" +p #224;
    %"chk28" : A = (Check 0 4 Read 1) %"v207";
    %"v208" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    call %"v209" : W = $"__GI___waitpid"(W %"v208", P %"v2", W #0);
    %"chk29" : A = (Check 0 4 Read 1) %"v204";
    %"v210" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    call %"v211" : W = $"__GI___pthread_setcancelstate"(W %"v210", P #0);
    %"v214" : W = (Cmp Eq W) %"v209", #4294967295
    => br %"v214" ? "L215" : "L216";
  @"L215":
    %"v217" : P = Copy $"__libc_errno";
    %"chk30" : A = (Check 0 4 Read 1) %"v217";
    %"v218" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v219" : W = (Cmp Eq W) %"v218", #4
    => goto "L216";
  @"L216" [%"v221" : W = phi("L201" => #0, "L215" => %"v219")]:
    => br %"v221" ? poll "L201" : "L203";
  @"L203":
    => br %"v214" ? "L222" : "L224";
  @"L222":
    => ret #4294967295;
  @"L224":
    %"chk31" : A = (Check 0 4 Read 1) %"v2";
    %"v230" : W = (RawLoad (LdNarrow Sw) 0) %"chk31"
    => ret %"v230"
} }.

Definition item_glibc_iopopen'23proc_file_chain : item :=
  (IData (a "glibc_iopopen#proc_file_chain") LLocal 8 [(Zero 8)]).

Definition item_glibc_iopopen'23proc_file_chain_lock : item :=
  (IData (a "glibc_iopopen#proc_file_chain_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition fn_glibc_iopopen'23unlock : func :=
  ir_fn{ "local" "glibc_iopopen#unlock"(P %"v0") -> RVoid {
  @"start":
    %"v8" : P = Copy $"__libc_single_threaded_internal";
    %"chk0" : A = (Check 0 1 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v10" : W = (Cmp Ne W) %"v9", #0
    => br %"v10" ? "L11" : "L12";
  @"L11":
    %"v13" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v14" = %"v13" +p #4;
    %"chk1" : A = (Check 0 4 Read 1) %"v14";
    %"v15" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v16" : W = (Cmp Eq W) %"v15", #0
    => goto "L12";
  @"L12" [%"v18" : W = phi("start" => #0, "L11" => %"v16")]:
    => br %"v18" ? "L5" : "L6";
  @"L5":
    %"v19" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v20" = %"v19" +p #8;
    %"chk2" : A = (Check 0 8 Write 8) %"v20";
    store.ptr [%"chk2" + 0] <- #0;
    %"v21" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk3" : A = (Check 0 4 Write 1) %"v21";
    store Ww [%"chk3" + 0] <- #0
    => goto "L4";
  @"L6":
    %"v25" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v26" = %"v25" +p #4;
    %"chk4" : A = (Check 0 4 Read 1) %"v26";
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v28" : W = (Cmp Eq W) %"v27", #0
    => br %"v28" ? "L22" : "L23";
  @"L22":
    %"v29" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v30" = %"v29" +p #8;
    %"chk5" : A = (Check 0 8 Write 8) %"v30";
    store.ptr [%"chk5" + 0] <- #0;
    %"v32" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk6" : A = (Check 0 4 Read 1) %"v32";
    %"v36" : W = (RawLoad (LdNarrow Sw) 0) %"chk6"
    => goto "L37";
  @"L37" [%"v39" : W = phi("L22" => %"v36", "L37" => %"v40")]:
    %"chk7" : A = (HalfCheck Lower 0 4 Write 4) %"chk6", %"v32";
    %"v40" : W = (RawCas (CasNarrow Sw) 0) %"chk7", %"v39", #0;
    %"v41" : W = (Cmp Eq W) %"v40", %"v39"
    => br %"v41" ? "L38" : poll "L37";
  @"L38":
    %"v46" : W = (Cmp Sgt W) %"v39", #1
    => br %"v46" ? "L49" : "L4";
  @"L49":
    call void $"__GI___lll_lock_wake_private"(P %"v32")
    => goto "L4";
  @"L23":
    %"v60" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v61" = %"v60" +p #4;
    %"chk8" : A = (Check 0 4 Read 1) %"v61";
    %"v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v63" : W = Sub %"v62", #1;
    %"chk9" : A = (Renew 0 4 Write 1) %"chk8", %"v61";
    store Ww [%"chk9" + 0] <- %"v63"
    => goto "L4";
  @"L4":
    => ret void
} }.
