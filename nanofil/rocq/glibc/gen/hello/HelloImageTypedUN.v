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

Definition hello_image_fn___GI___underflow : func :=
  ir_fn{ "export" "__GI___underflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v24" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v26" : W = (Cmp Eq W) %"v25", #0
    => br %"v26" ? "L20" : "L22";
  @"L20":
    %"v28" = %"v0" +p #192;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v28";
    store Ww [%"chk1" + 0] <- #4294967295
    => goto "L22";
  @"L22":
    %"v31" = %"v0" +p #192;
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v55" : W = (Cmp Ne W) %"v32", #4294967295
    => br %"v55" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v64" = %"v0" +p #192;
    %"v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v66" : W = (Cmp Eq W) %"v65", #0
    => br %"v66" ? "L69" : "L62";
  @"L69":
    %"v83" = %"v0" +p #192;
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v85" : W = (Cmp Eq W) %"v84", #0
    => br %"v85" ? "L79" : "L81";
  @"L79":
    %"v87" = %"v0" +p #192;
    %"chk5" : A = (Renew 0 4 Write 1) %"chk0", %"v87";
    store Ww [%"chk5" + 0] <- #4294967295
    => goto "L81";
  @"L81":
    %"v90" = %"v0" +p #192;
    %"v91" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L62";
  @"L62":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v117" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v118" : W = And %"v117", #2048
    => br %"v118" ? "L113" : "L115";
  @"L113":
    call %"v123" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v125" : W = (Cmp Eq W) %"v123", #4294967295
    => br %"v125" ? "L119" : "L115";
  @"L119":
    => ret #4294967295;
  @"L115":
    %"v132" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v132";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v135" = %"v0" +p #16;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v135";
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v137" : L = Ptoi %"v133";
    %"v138" : L = Ptoi %"v136";
    %"v139" : W = (Cmp Ult L) %"v137", %"v138"
    => br %"v139" ? "L128" : "L130";
  @"L128":
    %"v141" = %"v0" +p #8;
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk11" : A = (Check 0 1 Read 1) %"v142";
    %"v143" : W = (RawLoad (LdNarrow Ub) 0) %"chk11"
    => ret %"v143";
  @"L130":
    %"chk12" : A = (Renew 0 4 Read 1) %"chk7", %"v0";
    %"v149" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v150" : W = And %"v149", #256
    => br %"v150" ? "L145" : "L147";
  @"L145":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v156" = %"v0" +p #8;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk8", %"v156";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v159" = %"v0" +p #16;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk9", %"v159";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v161" : L = Ptoi %"v157";
    %"v162" : L = Ptoi %"v160";
    %"v163" : W = (Cmp Ult L) %"v161", %"v162"
    => br %"v163" ? "L152" : "L147";
  @"L152":
    %"v165" = %"v0" +p #8;
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk16" : A = (Check 0 1 Read 1) %"v166";
    %"v167" : W = (RawLoad (LdNarrow Ub) 0) %"chk16"
    => ret %"v167";
  @"L147":
    %"v173" = %"v0" +p #96;
    %"chk17" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v175" : L = Ptoi %"v174";
    %"v176" : L = Ptoi #0;
    %"v177" : W = (Cmp Ne L) %"v175", %"v176"
    => br %"v177" ? "L169" : "L170";
  @"L169":
    %"v183" = %"v0" +p #16;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk9", %"v183";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call %"v185" : W = $"glibc_genops#save_for_backup"(P %"v0", P %"v184")
    => br %"v185" ? "L178" : "L171";
  @"L178":
    => ret #4294967295;
  @"L170":
    %"v192" = %"v0" +p #80;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v192";
    %"v193" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v194" : L = Ptoi %"v193";
    %"v196" : W = (Cmp Ne L) %"v194", %"v176"
    => br %"v196" ? "L188" : "L171";
  @"L188":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L171";
  @"L171":
    %"v199" = %"v0" +p #216;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v199";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_1.v4" : L = Ptoi %"v200";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v202" = %"v200" +p #32;
    %"chk21" : A = (Check 0 8 Read 8) %"v202";
    %"v203" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : F = CheckFunction %"v203";
    rawcall %"v205" : W = %"chk22"(P %"v0")
    => ret %"v205"
} }.

Definition hello_image_fn_glibc_iopopen'23unlock : func :=
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

Definition hello_image_fn_glibc_unwind'23unwind_stop : func :=
  ir_fn{ "local" "glibc_unwind#unwind_stop"(W %"v0", W %"v2", L %"v4", P %"v6", P %"v8", P %"v10") -> (RClass W) {
  @"start":
    call %"v15" : P = $"zthread_self_cookie"();
    %"v18" = %"v15" +p #776;
    %"chk0" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v23" = %"v15" +p #1712;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" : L = Ptoi %"v24";
    %"v27" = %"v15" +p #1720;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v27";
    %"v28" : L = (RawLoad LdL 0) %"chk2";
    %"v29" : L = Add %"v25", %"v28";
    %"v34" : W = And %"v2", #16
    => br %"v34" ? "L36" : "L35";
  @"L35":
    call %"v38" : L = $"_Unwind_GetCFA"(P %"v8");
    (Flight (a "v39") Copy [(FValue (t "v38"))] LowerNone);
    %"v40" : L = Ptoi %"v39";
    %"v42" : L = Sub %"v40", %"v29";
    %"chk3" : A = (Check 0 8 Read 8) %"v10";
    %"iw_1.iw_1.v3" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call %"iw_1.iw_1.v4" : P = $"zget_jmp_buf_impl_frame"(P %"iw_1.iw_1.v3");
    %"iw_1.v4" : L = Ptoi %"iw_1.iw_1.v4";
    %"v47" : L = Sub %"iw_1.v4", %"v29";
    %"v49" : W = (Cmp Uge L) %"v42", %"v47"
    => goto "L36";
  @"L36" [%"v51" : W = phi("start" => #1, "L35" => %"v49")]:
    => br %"v51" ? "L32" : "L31";
  @"L31":
    => goto "L32";
  @"L32" [%"pr.1" : W = phi("L31" => #0, "L36" => #1)]:
    %"v59" : L = Ptoi %"v19";
    %"v61" : W = (Cmp Eq L) %"v59", #0
    => br %"v61" ? "L54" : "L57";
  @"L57":
    %"v63" : P = Copy $"glibc_unwind#str.287";
    %"v64" : P = Copy $"glibc_unwind#str.288";
    %"v65" : P = Copy $"glibc_unwind#str.289";
    %"v66" : P = Copy $"glibc_unwind#str.290";
    call void $"zerrorf"(P %"v63", P %"v64", W #64, P %"v65", P %"v66")
    => goto "L54";
  @"L54":
    => br %"pr.1" ? "L67" : "L69";
  @"L67":
    call void $"__libc_longjmp"(P %"v10", W #1)
    => goto "L69";
  @"L69":
    => ret #0
} }.

Definition hello_image_fn_glibc_unwind'23unwind_cleanup : func :=
  ir_fn{ "local" "glibc_unwind#unwind_cleanup"(W %"v0", P %"v2") -> RVoid {
  @"start":
    %"v4" : P = Copy $"glibc_unwind#str.291";
    call void $"__GI___libc_fatal"(P %"v4")
    => ret void
} }.
