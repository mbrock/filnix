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

Definition hello_image_fn_glibc_gconv_db'23derivation_compare : func :=
  ir_fn{ "local" "glibc_gconv_db#derivation_compare"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v13" : W = $"__GI_strcmp"(P %"v10", P %"v12");
    %"v18" : W = (Cmp Eq W) %"v13", #0
    => br %"v18" ? "L14" : "L16";
  @"L14":
    %"v20" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v23" = %"v2" +p #8;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call %"v25" : W = $"__GI_strcmp"(P %"v21", P %"v24")
    => goto "L16";
  @"L16" [%"pr.1" : W = phi("L14" => %"v25", "start" => %"v13")]:
    => ret %"pr.1"
} }.

Definition hello_image_fn_glibc_fileops'23decide_maybe_mmap : func :=
  ir_fn{ "local" "glibc_fileops#decide_maybe_mmap"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = (Alloc 8) #144;
    %"v7" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v8";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v10" = %"v8" +p #144;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v11";
    rawcall %"v13" : W = %"chk2"(P %"v0", P %"v2");
    %"v14" : W = (Cmp Eq W) %"v13", #0
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v17" = %"v2" +p #24;
    %"chk3" : A = (Check 0 4 Read 1) %"v17";
    %"v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v19" : W = And %"v18", #61440;
    %"v20" : W = (Cmp Eq W) %"v19", #32768
    => goto "L16";
  @"L16" [%"v22" : W = phi("iw_1.join" => #0, "L15" => %"v20")]:
    => br %"v22" ? "L23" : "L24";
  @"L23":
    %"v25" = %"v2" +p #48;
    %"chk4" : A = (Check 0 8 Read 1) %"v25";
    %"v26" : L = (RawLoad LdL 0) %"chk4";
    %"v27" : W = (Cmp Ne L) %"v26", #0
    => goto "L24";
  @"L24" [%"v29" : W = phi("L16" => #0, "L23" => %"v27")]:
    => br %"v29" ? "L34" : "L31";
  @"L34":
    => goto "L31";
  @"L31" [%"v44" : W = phi("L24" => #0, "L34" => #1)]:
    => br %"v44" ? "L45" : "L46";
  @"L45":
    %"v48" = %"v0" +p #144;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v48";
    %"v49" : L = (RawLoad LdL 0) %"chk5";
    %"v52" : W = (Cmp Eq L) %"v49", #18446744073709551615
    => br %"v52" ? "L46" : "L53";
  @"L53":
    %"v56" = %"v0" +p #144;
    %"v57" : L = (RawLoad LdL 0) %"chk5";
    %"v58" = %"v2" +p #48;
    %"chk7" : A = (Check 0 8 Read 1) %"v58";
    %"v59" : L = (RawLoad LdL 0) %"chk7";
    %"v60" : W = (Cmp Sle L) %"v57", %"v59"
    => goto "L46";
  @"L46" [%"v64" : W = phi("L31" => #0, "L45" => #1, "L53" => %"v60")]:
    => br %"v64" ? "L3" : "L5";
  @"L3":
    %"v66" = %"v2" +p #48;
    %"chk8" : A = (Check 0 8 Read 1) %"v66";
    %"v67" : L = (RawLoad LdL 0) %"chk8";
    %"v69" = %"v0" +p #112;
    %"chk9" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v69";
    %"v70" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    call %"v71" : P = $"__GI___mmap64"(P #0, L %"v67", W #1, W #1, W %"v70", L #0);
    (Flight (a "v78") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v79" : L = Ptoi %"v71";
    %"v80" : L = Ptoi %"v78";
    %"v81" : W = (Cmp Ne L) %"v79", %"v80"
    => br %"v81" ? "L72" : "L5";
  @"L72":
    %"v86" = %"v0" +p #112;
    %"chk10" : A = (Renew 0 4 Read 1) %"chk9", %"v86";
    %"v87" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v88" = %"v2" +p #48;
    %"chk11" : A = (Renew 0 8 Read 1) %"chk8", %"v88";
    %"v89" : L = (RawLoad LdL 0) %"chk11";
    call %"v90" : L = $"__lseek64"(W %"v87", L %"v89", W #0);
    %"chk12" : A = (Renew 0 8 Read 1) %"chk8", %"v88";
    %"v92" : L = (RawLoad LdL 0) %"chk12";
    %"v93" : W = (Cmp Ne L) %"v90", %"v92"
    => br %"v93" ? "L82" : "L83";
  @"L82":
    %"v95" = %"v2" +p #48;
    %"v96" : L = (RawLoad LdL 0) %"chk12";
    call %"v97" : W = $"__GI___munmap"(P %"v71", L %"v96");
    %"v99" = %"v0" +p #144;
    %"chk14" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"v99";
    store Wl [%"chk14" + 0] <- #18446744073709551615
    => goto "L5";
  @"L83":
    %"v105" = %"v2" +p #48;
    %"v106" : L = (RawLoad LdL 0) %"chk12";
    %"v107" = %"v71" +p %"v106";
    call void $"__GI__IO_setb"(P %"v0", P %"v71", P %"v107", W #0);
    %"v112" = %"v0" +p #144;
    %"chk16" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v112";
    %"v113" : L = (RawLoad LdL 0) %"chk16";
    %"v116" : W = (Cmp Eq L) %"v113", #18446744073709551615
    => br %"v116" ? "L108" : "L110";
  @"L108":
    %"v118" = %"v0" +p #144;
    %"chk17" : A = (Renew 0 8 Write 1) %"chk16", %"v118";
    store Wl [%"chk17" + 0] <- #0
    => goto "L110";
  @"L110":
    %"v120" = %"v0" +p #24;
    %"chk18" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v120";
    store.ptr [%"chk18" + 0] <- %"v71";
    %"v123" = %"v0" +p #8;
    %"v126" = %"v0" +p #144;
    %"chk19" : A = (Renew 0 8 Read 1) %"chk16", %"v126";
    %"v127" : L = (RawLoad LdL 0) %"chk19";
    %"v128" = %"v71" +p %"v127";
    %"chk20" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v123";
    store.ptr [%"chk20" + 0] <- %"v128";
    %"v130" = %"v0" +p #16;
    %"v132" = %"v2" +p #48;
    %"chk21" : A = (Renew 0 8 Read 1) %"chk8", %"v132";
    %"v133" : L = (RawLoad LdL 0) %"chk21";
    %"v134" = %"v71" +p %"v133";
    %"chk22" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v130";
    store.ptr [%"chk22" + 0] <- %"v134";
    %"chk23" : A = (Renew 0 8 Read 1) %"chk8", %"v132";
    %"v138" : L = (RawLoad LdL 0) %"chk23";
    %"chk24" : A = (Renew 0 8 Write 1) %"chk16", %"v126";
    store Wl [%"chk24" + 0] <- %"v138";
    %"v143" = %"v0" +p #192;
    %"chk25" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v143";
    %"v144" : W = (RawLoad (LdNarrow Sw) 0) %"chk25";
    %"v145" : W = (Cmp Sle W) %"v144", #0
    => br %"v145" ? "L139" : "L140";
  @"L139":
    %"v147" = %"v0" +p #216;
    %"v148" : P = Copy $"__io_vtables";
    %"v149" = %"v148" +p #504;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk0", %"v147";
    store.ptr [%"chk26" + 0] <- %"v149"
    => goto "L141";
  @"L140":
    %"v151" = %"v0" +p #216;
    %"v152" : P = Copy $"__io_vtables";
    %"v153" = %"v152" +p #1008;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk0", %"v151";
    store.ptr [%"chk27" + 0] <- %"v153"
    => goto "L141";
  @"L141":
    %"v155" = %"v0" +p #160;
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v155";
    %"v156" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v157" = %"v156" +p #224;
    %"v158" : P = Copy $"__io_vtables";
    %"v159" = %"v158" +p #1008;
    %"chk29" : A = (Check 0 8 Write 8) %"v157";
    store.ptr [%"chk29" + 0] <- %"v159"
    => ret void;
  @"L5":
    %"v164" = %"v0" +p #192;
    %"chk30" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v164";
    %"v165" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v166" : W = (Cmp Sle W) %"v165", #0
    => br %"v166" ? "L160" : "L161";
  @"L160":
    %"v168" = %"v0" +p #216;
    %"v169" : P = Copy $"__io_vtables";
    %"v170" = %"v169" +p #336;
    %"chk31" : A = (Renew 0 8 Write 8) %"chk0", %"v168";
    store.ptr [%"chk31" + 0] <- %"v170"
    => goto "L162";
  @"L161":
    %"v172" = %"v0" +p #216;
    %"v173" : P = Copy $"__io_vtables";
    %"v174" = %"v173" +p #840;
    %"chk32" : A = (Renew 0 8 Write 8) %"chk0", %"v172";
    store.ptr [%"chk32" + 0] <- %"v174"
    => goto "L162";
  @"L162":
    %"v176" = %"v0" +p #160;
    %"chk33" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v176";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v178" = %"v177" +p #224;
    %"v179" : P = Copy $"__io_vtables";
    %"v180" = %"v179" +p #840;
    %"chk34" : A = (Check 0 8 Write 8) %"v178";
    store.ptr [%"chk34" + 0] <- %"v180"
    => ret void
} }.
