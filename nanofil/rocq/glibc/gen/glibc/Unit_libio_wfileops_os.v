(** This file defines checked IR from glibc’s `libio/wfileops.os` object.
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

Definition fn__IO_wfile_underflow_maybe_mmap : func :=
  ir_fn{ "export" "_IO_wfile_underflow_maybe_mmap"(P %"v0") -> (RClass W) {
  @"start":
    call %"v6" : W = $"_IO_file_underflow_maybe_mmap"(P %"v0");
    %"v8" : W = (Cmp Eq W) %"v6", #4294967295
    => br %"v8" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v11" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #224;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v15" = %"v14" +p #32;
    %"chk2" : A = (Check 0 8 Read 8) %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : F = CheckFunction %"v16";
    rawcall %"v18" : W = %"chk3"(P %"v0")
    => ret %"v18"
} }.

Definition fn__IO_wfile_underflow_mmap : func :=
  ir_fn{ "export" "_IO_wfile_underflow_mmap"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = And %"v8", #4;
    %"v10" : L = (Ext Sw) %"v9";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L4" : "L6";
  @"L4":
    %"v13" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v14" : W = Or %"v13", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v14";
    %"v15" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"v15";
    store Ww [%"chk3" + 0] <- #9
    => ret #4294967295;
  @"L6":
    %"v21" = %"v0" +p #160;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v27" = %"v26" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v29" : L = Ptoi %"v23";
    %"v30" : L = Ptoi %"v28";
    %"v31" : W = (Cmp Ult L) %"v29", %"v30"
    => br %"v31" ? "L17" : "L19";
  @"L17":
    %"v33" = %"v0" +p #160;
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk9" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 4 Read 1) %"v35";
    %"v36" : W = (RawLoad (LdNarrow Sw) 0) %"chk10"
    => ret %"v36";
  @"L19":
    %"v39" = %"v0" +p #152;
    %"v40" : P = (RawLoadPointer (-8) load_effects) %"chk4";
    %"v45" = %"v0" +p #8;
    %"v46" : P = (RawLoadPointer (-152) load_effects) %"chk4";
    %"v48" = %"v0" +p #16;
    %"v49" : P = (RawLoadPointer (-144) load_effects) %"chk4";
    %"v50" : L = Ptoi %"v46";
    %"v51" : L = Ptoi %"v49";
    %"v52" : W = (Cmp Uge L) %"v50", %"v51"
    => br %"v52" ? "L53" : "L54";
  @"L53":
    call %"v56" : W = $"_IO_file_underflow_mmap"(P %"v0");
    %"v58" : W = (Cmp Eq W) %"v56", #4294967295
    => goto "L54";
  @"L54" [%"v60" : W = phi("L19" => #0, "L53" => %"v58")]:
    => br %"v60" ? "L41" : "L43";
  @"L41":
    => ret #4294967295;
  @"L43":
    %"v63" = %"v0" +p #8;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"v3";
    store.ptr [%"chk15" + 0] <- %"v64";
    %"v69" = %"v0" +p #160;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk4", %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v71" = %"v70" +p #48;
    %"chk17" : A = (Check 0 8 Read 8) %"v71";
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v73" : L = Ptoi %"v72";
    %"v74" : L = Ptoi #0;
    %"v75" : W = (Cmp Eq L) %"v73", %"v74"
    => br %"v75" ? "L65" : "L67";
  @"L65":
    %"v80" = %"v0" +p #160;
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v82" = %"v81" +p #64;
    %"chk19" : A = (Check 0 8 Read 8) %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v84" : L = Ptoi %"v83";
    %"v86" : W = (Cmp Ne L) %"v84", %"v74"
    => br %"v86" ? "L76" : "L78";
  @"L76":
    %"v88" = %"v0" +p #160;
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v90" = %"v89" +p #64;
    %"chk21" : A = (Check 0 8 Read 8) %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call void $"free"(P %"v91");
    %"chk22" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v95" : W = And %"v93", #4294967039;
    %"chk23" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk23" + 0] <- %"v95"
    => goto "L78";
  @"L78":
    call void $"__GI__IO_wdoallocbuf"(P %"v0")
    => goto "L67";
  @"L67":
    %"v98" = %"v0" +p #160;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk4", %"v98";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v100" = %"v99" +p #96;
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v104" = %"v103" +p #88;
    %"chk26" : A = (Check 0 8 Read 1) %"v104";
    %"v105" : L = (RawLoad LdL 0) %"chk26";
    %"chk27" : A = (Check 0 8 Write 1) %"v100";
    store Wl [%"chk27" + 0] <- %"v105";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v109" = %"v108" +p #16;
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v115" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v116" = %"v115" +p #48;
    %"chk31" : A = (Check 0 8 Read 8) %"v116";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Check 0 8 Write 8) %"v112";
    store.ptr [%"chk32" + 0] <- %"v117";
    %"chk33" : A = (Check 0 8 Write 8) %"v109";
    store.ptr [%"chk33" + 0] <- %"v117";
    %"chk34" : A = (Renew 0 8 Read 8) %"chk4", %"v98";
    %"v121" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v122" = %"v121" +p #88;
    %"v124" = %"v0" +p #8;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk14", %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v127" = %"v0" +p #16;
    %"v128" : P = (RawLoadPointer 8 load_effects) %"chk35";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk38" : A = (Check 0 8 Read 8) %"v131";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v136" = %"v135" +p #56;
    %"chk40" : A = (Check 0 8 Read 8) %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v140" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v141" = %"v140" +p #8;
    call %"v142" : W = $"__libio_codecvt_in"(P %"v40", P %"v122", P %"v125", P %"v128", P %"v3", P %"v132", P %"v137", P %"v141");
    %"chk42" : A = (Renew 0 8 Read 8) %"chk15", %"v3";
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"chk43" : A = (Renew 0 8 Write 8) %"chk14", %"v124";
    store.ptr [%"chk43" + 0] <- %"v145";
    %"chk44" : A = (Renew 0 8 Read 8) %"chk4", %"v98";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Check 0 8 Read 8) %"v151";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v156" = %"v155" +p #8;
    %"chk47" : A = (Check 0 8 Read 8) %"v156";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v158" : L = Ptoi %"v152";
    %"v159" : L = Ptoi %"v157";
    %"v160" : W = (Cmp Ult L) %"v158", %"v159"
    => br %"v160" ? "L146" : "L148";
  @"L146":
    %"v162" = %"v0" +p #160;
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk49" : A = (Check 0 8 Read 8) %"v163";
    %"v164" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"chk50" : A = (Check 0 4 Read 1) %"v164";
    %"v165" : W = (RawLoad (LdNarrow Sw) 0) %"chk50"
    => ret %"v165";
  @"L148":
    %"v167" : P = Copy $"__libc_errno";
    %"chk51" : A = (Check 0 4 Write 1) %"v167";
    store Ww [%"chk51" + 0] <- #84;
    %"chk52" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v169" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    %"v170" : W = Or %"v169", #32;
    %"chk53" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk53" + 0] <- %"v170"
    => ret #4294967295
} }.

Definition fn___GI__IO_wdo_write : func :=
  ir_fn{ "export" "__GI__IO_wdo_write"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v64" : P = (Alloc 8) #8;
    %"v65" : P = (Alloc 4) #16;
    %"v67" : P = (Alloc 8) #8;
    %"v8" = %"v0" +p #152;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : W = (Cmp Ugt L) %"v4", #0
    => br %"v14" ? "L10" : "L12";
  @"L10":
    %"v19" = %"v0" +p #48;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v22" = %"v0" +p #40;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v24" : L = Ptoi %"v20";
    %"v25" : L = Ptoi %"v23";
    %"v26" : W = (Cmp Eq L) %"v24", %"v25"
    => br %"v26" ? "L27" : "L28";
  @"L27":
    %"v30" = %"v0" +p #48;
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v33" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v35" : L = Ptoi %"v31";
    %"v36" : L = Ptoi %"v34";
    %"v37" : W = (Cmp Ne L) %"v35", %"v36"
    => goto "L28";
  @"L28" [%"v39" : W = phi("L10" => #0, "L27" => %"v37")]:
    => br %"v39" ? "L15" : "L60";
  @"L15":
    %"v45" = %"v0" +p #32;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v48" = %"v0" +p #40;
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v53" : L = Ptoi %"v49";
    %"v54" : L = Ptoi %"v52";
    %"v55" : L = Sub %"v53", %"v54";
    call %"v56" : W = $"_IO_new_do_write"(P %"v0", P %"v46", L %"v55");
    %"v58" : W = (Cmp Eq W) %"v56", #4294967295
    => br %"v58" ? "L40" : "L60";
  @"L40":
    => ret #(-1);
  @"L60" [%"pr.3" : L = phi("L129" => %"v126", "L15" => %"v4", "L28" => %"v4"); %"pr.1" : P = phi("L129" => %"v150", "L15" => %"v2", "L28" => %"v2")]:
    %"v73" = %"v0" +p #64;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v73";
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v76" = %"v0" +p #40;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk2", %"v76";
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v78" : L = Ptoi %"v74";
    %"v79" : L = Ptoi %"v77";
    %"v80" : L = Sub %"v78", %"v79";
    %"v81" : W = (Cmp Ult L) %"v80", #16
    => br %"v81" ? "L69" : "L70";
  @"L69":
    %"chk10" : A = (Check 0 8 Write 8) %"v67";
    store.ptr [%"chk10" + 0] <- %"v65";
    %"v82" = %"v65" +p #16
    => goto "L71";
  @"L70":
    %"v84" = %"v0" +p #40;
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk12" : A = (Check 0 8 Write 8) %"v67";
    store.ptr [%"chk12" + 0] <- %"v85";
    %"v87" = %"v0" +p #32;
    %"chk13" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v90" = %"v0" +p #64;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk8", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk14"
    => goto "L71";
  @"L71" [%"pr.5" : P = phi("L69" => %"v82", "L70" => %"v91"); %"pr.4" : P = phi("L69" => %"v65", "L70" => %"v88")]:
    %"v94" = %"v0" +p #160;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v94";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v96" = %"v95" +p #88;
    %"v100" : L = Shl %"pr.3", #2;
    %"v101" = %"pr.1" +p %"v100";
    %"chk16" : A = (Check 0 8 Read 8) %"v67";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk16";
    call %"v104" : W = $"__libio_codecvt_out"(P %"v9", P %"v96", P %"pr.1", P %"v101", P %"v64", P %"v102", P %"pr.5", P %"v67");
    %"chk17" : A = (Renew 0 8 Read 8) %"chk16", %"v67";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v112" : L = Ptoi %"v110";
    %"v113" : L = Ptoi %"pr.4";
    %"v114" : L = Sub %"v112", %"v113";
    call %"v115" : W = $"_IO_new_do_write"(P %"v0", P %"pr.4", L %"v114");
    %"v117" : W = (Cmp Eq W) %"v115", #4294967295
    => br %"v117" ? "L105" : "L107";
  @"L105":
    => ret #(-1);
  @"L107":
    %"chk18" : A = (Check 0 8 Read 8) %"v64";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v122" : L = Ptoi %"v120";
    %"v123" : L = Ptoi %"pr.1";
    %"v124" : L = Sub %"v122", %"v123";
    %"v125" : L = Div %"v124", #4;
    %"v126" : L = Sub %"pr.3", %"v125";
    %"v131" : W = (Cmp Ne W) %"v104", #0
    => br %"v131" ? "L132" : "L133";
  @"L132":
    %"v135" : W = (Cmp Ne W) %"v104", #1
    => br %"v135" ? "L133" : "L136";
  @"L136":
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v140" : L = Ptoi %"v138";
    %"v142" : L = Sub %"v140", %"v123";
    %"v143" : L = Div %"v142", #4;
    %"v144" : W = (Cmp Eq L) %"v143", #0
    => goto "L133";
  @"L133" [%"v148" : W = phi("L107" => #0, "L132" => #1, "L136" => %"v144")]:
    => br %"v148" ? "L12" : "L129";
  @"L129":
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v152" : W = (Cmp Ugt L) %"v126", #0
    => br %"v152" ? poll "L60" : "L12";
  @"L12" [%"pr.2" : L = phi("L129" => %"v126", "L133" => %"v126", "start" => %"v4")]:
    %"v154" = %"v0" +p #160;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v154";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v156" = %"v155" +p #16;
    %"v159" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v160" = %"v159" +p #48;
    %"chk23" : A = (Check 0 8 Read 8) %"v160";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Check 0 8 Write 8) %"v156";
    store.ptr [%"chk24" + 0] <- %"v161";
    %"chk25" : A = (Renew 0 8 Read 8) %"chk21", %"v154";
    %"v164" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v168" = %"v167" +p #48;
    %"chk27" : A = (Check 0 8 Read 8) %"v168";
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk28" : A = (Check 0 8 Write 8) %"v164";
    store.ptr [%"chk28" + 0] <- %"v169";
    %"chk29" : A = (Renew 0 8 Read 8) %"chk21", %"v154";
    %"v172" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v173" = %"v172" +p #8;
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v177" = %"v176" +p #48;
    %"chk31" : A = (Check 0 8 Read 8) %"v177";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Check 0 8 Write 8) %"v173";
    store.ptr [%"chk32" + 0] <- %"v178";
    %"chk33" : A = (Renew 0 8 Read 8) %"chk21", %"v154";
    %"v181" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v182" = %"v181" +p #24;
    %"v185" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v186" = %"v185" +p #32;
    %"v189" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v190" = %"v189" +p #48;
    %"chk36" : A = (Check 0 8 Read 8) %"v190";
    %"v191" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"chk37" : A = (Check 0 8 Write 8) %"v186";
    store.ptr [%"chk37" + 0] <- %"v191";
    %"chk38" : A = (Check 0 8 Write 8) %"v182";
    store.ptr [%"chk38" + 0] <- %"v191";
    %"chk39" : A = (Renew 0 8 Read 8) %"chk21", %"v154";
    %"v194" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v195" = %"v194" +p #40;
    %"chk40" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v200" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"v202" : W = And %"v200", #514
    => br %"v202" ? "L196" : "L197";
  @"L196":
    %"v204" = %"v0" +p #160;
    %"v205" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v206" = %"v205" +p #48;
    %"chk42" : A = (Check 0 8 Read 8) %"v206";
    %"v207" : P = (RawLoadPointer 0 load_effects) %"chk42"
    => goto "L198";
  @"L197":
    %"v209" = %"v0" +p #160;
    %"v210" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v211" = %"v210" +p #56;
    %"chk44" : A = (Check 0 8 Read 8) %"v211";
    %"v212" : P = (RawLoadPointer 0 load_effects) %"chk44"
    => goto "L198";
  @"L198" [%"v213" : P = phi("L196" => %"v207", "L197" => %"v212")]:
    %"chk45" : A = (Check 0 8 Write 8) %"v195";
    store.ptr [%"chk45" + 0] <- %"v213";
    %"v218" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v218" ? "L216" : "L215";
  @"L215":
    => goto "L216";
  @"L216" [%"v219" : W = phi("L215" => #4294967295, "L198" => #0)]:
    => ret %"v219"
} }.

Definition fn___GI__IO_wfile_overflow : func :=
  ir_fn{ "export" "__GI__IO_wfile_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = And %"v8", #8
    => br %"v9" ? "L4" : "L6";
  @"L4":
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = Or %"v11", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v12";
    %"v13" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk3" + 0] <- #9
    => ret #4294967295;
  @"L6":
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v20" : W = And %"v19", #2048;
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => br %"v21" ? "L23" : "L22";
  @"L22":
    %"v25" = %"v0" +p #160;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v27" = %"v26" +p #24;
    %"chk6" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v29" : L = Ptoi %"v28";
    %"v30" : L = Ptoi #0;
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => goto "L23";
  @"L23" [%"v33" : W = phi("L6" => #1, "L22" => %"v31")]:
    => br %"v33" ? "L15" : "L17";
  @"L15":
    %"v38" = %"v0" +p #160;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v40" = %"v39" +p #24;
    %"chk8" : A = (Check 0 8 Read 8) %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v42" : L = Ptoi %"v41";
    %"v43" : L = Ptoi #0;
    %"v44" : W = (Cmp Eq L) %"v42", %"v43"
    => br %"v44" ? "L34" : "L35";
  @"L34":
    call void $"__GI__IO_wdoallocbuf"(P %"v0");
    call void $"__GI__IO_free_wbackup_area"(P %"v0");
    %"v51" = %"v0" +p #32;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v53" : L = Ptoi %"v52";
    %"v55" : W = (Cmp Eq L) %"v53", %"v43"
    => br %"v55" ? "L47" : "L49";
  @"L47":
    call void $"__GI__IO_doallocbuf"(P %"v0");
    %"v58" = %"v0" +p #24;
    %"v60" = %"v0" +p #56;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v58";
    store.ptr [%"chk11" + 0] <- %"v61";
    %"v63" = %"v0" +p #8;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk10", %"v60";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v63";
    store.ptr [%"chk13" + 0] <- %"v66";
    %"v68" = %"v0" +p #16;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk10", %"v60";
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v68";
    store.ptr [%"chk15" + 0] <- %"v71"
    => goto "L49";
  @"L49":
    %"v73" = %"v0" +p #160;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk7", %"v73";
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v75" = %"v74" +p #16;
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v79" = %"v78" +p #48;
    %"chk18" : A = (Check 0 8 Read 8) %"v79";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (Check 0 8 Write 8) %"v75";
    store.ptr [%"chk19" + 0] <- %"v80";
    %"chk20" : A = (Renew 0 8 Read 8) %"chk7", %"v73";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v87" = %"v86" +p #48;
    %"chk22" : A = (Check 0 8 Read 8) %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (Check 0 8 Write 8) %"v83";
    store.ptr [%"chk23" + 0] <- %"v88";
    %"chk24" : A = (Renew 0 8 Read 8) %"chk7", %"v73";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v92" = %"v91" +p #8;
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v96" = %"v95" +p #48;
    %"chk26" : A = (Check 0 8 Read 8) %"v96";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (Check 0 8 Write 8) %"v92";
    store.ptr [%"chk27" + 0] <- %"v97"
    => goto "L36";
  @"L35":
    %"v102" = %"v0" +p #160;
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk29" : A = (Check 0 8 Read 8) %"v103";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v107" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v108" = %"v107" +p #56;
    %"chk31" : A = (Check 0 8 Read 8) %"v108";
    %"v109" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v110" : L = Ptoi %"v104";
    %"v111" : L = Ptoi %"v109";
    %"v112" : W = (Cmp Eq L) %"v110", %"v111"
    => br %"v112" ? "L98" : "L36";
  @"L98":
    %"v114" = %"v0" +p #16;
    %"v116" = %"v0" +p #8;
    %"v118" = %"v0" +p #56;
    %"v119" : P = (RawLoadPointer (-104) load_effects) %"chk7";
    %"chk33" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v116";
    store.ptr [%"chk33" + 0] <- %"v119";
    %"chk34" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v114";
    store.ptr [%"chk34" + 0] <- %"v119";
    %"v121" = %"v0" +p #160;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk7", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v123" = %"v122" +p #8;
    %"v126" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v130" = %"v129" +p #48;
    %"chk38" : A = (Check 0 8 Read 8) %"v130";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 8 Write 8) %"v126";
    store.ptr [%"chk39" + 0] <- %"v131";
    %"chk40" : A = (Check 0 8 Write 8) %"v123";
    store.ptr [%"chk40" + 0] <- %"v131"
    => goto "L36";
  @"L36":
    code ((app ir[ %"v133" = %"v0" +p #160;
      %"chk41" : A = (Renew 0 8 Read 8) %"chk7", %"v133";
      %"v134" : P = (RawLoadPointer 0 load_effects) %"chk41";
      %"v135" = %"v134" +p #32;
      %"v138" : P = (RawLoadPointer 0 load_effects) %"chk41";
      %"chk43" : A = (Check 0 8 Read 8) %"v138";
      %"v139" : P = (RawLoadPointer 0 load_effects) %"chk43";
      %"chk44" : A = (Check 0 8 Write 8) %"v135";
      store.ptr [%"chk44" + 0] <- %"v139";
      %"chk45" : A = (Renew 0 8 Read 8) %"chk7", %"v133";
      %"v142" : P = (RawLoadPointer 0 load_effects) %"chk45";
      %"v143" = %"v142" +p #24;
      %"v146" : P = (RawLoadPointer 0 load_effects) %"chk45";
      %"v147" = %"v146" +p #32;
      %"chk47" : A = (Check 0 8 Read 8) %"v147";
      %"v148" : P = (RawLoadPointer 0 load_effects) %"chk47";
      %"chk48" : A = (Check 0 8 Write 8) %"v143";
      store.ptr [%"chk48" + 0] <- %"v148";
      %"chk49" : A = (Renew 0 8 Read 8) %"chk7", %"v133";
      %"v151" : P = (RawLoadPointer 0 load_effects) %"chk49";
      %"v152" = %"v151" +p #40;
      %"v155" : P = (RawLoadPointer 0 load_effects) %"chk49";
      %"v156" = %"v155" +p #56;
      %"chk51" : A = (Check 0 8 Read 8) %"v156";
      %"v157" : P = (RawLoadPointer 0 load_effects) %"chk51";
      %"chk52" : A = (Check 0 8 Write 8) %"v152";
      store.ptr [%"chk52" + 0] <- %"v157";
      %"chk53" : A = (Renew 0 8 Read 8) %"chk7", %"v133";
      %"v160" : P = (RawLoadPointer 0 load_effects) %"chk53";
      %"v161" = %"v160" +p #16;
      %"v164" : P = (RawLoadPointer 0 load_effects) %"chk53";
      %"v167" : P = (RawLoadPointer 0 load_effects) %"chk53";
      %"v168" = %"v167" +p #8;
      %"chk56" : A = (Check 0 8 Read 8) %"v168";
      %"v169" : P = (RawLoadPointer 0 load_effects) %"chk56"] ir[ %"chk57" : A = (Check 0 8 Write 8) %"v164";
      store.ptr [%"chk57" + 0] <- %"v169";
      %"chk58" : A = (Check 0 8 Write 8) %"v161";
      store.ptr [%"chk58" + 0] <- %"v169";
      %"v171" = %"v0" +p #40;
      %"v173" = %"v0" +p #8;
      %"chk59" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v173";
      %"v174" : P = (RawLoadPointer 0 load_effects) %"chk59";
      %"chk60" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v171";
      store.ptr [%"chk60" + 0] <- %"v174";
      %"v176" = %"v0" +p #32;
      %"chk61" : A = (Renew 0 8 Read 8) %"chk60", %"v171";
      %"v179" : P = (RawLoadPointer 0 load_effects) %"chk61";
      %"chk62" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v176";
      store.ptr [%"chk62" + 0] <- %"v179";
      %"v181" = %"v0" +p #48;
      %"v183" = %"v0" +p #64;
      %"chk63" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v183";
      %"v184" : P = (RawLoadPointer 0 load_effects) %"chk63";
      %"chk64" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v181";
      store.ptr [%"chk64" + 0] <- %"v184";
      %"v186" = %"v0" +p #24;
      %"v190" = %"v0" +p #16;
      %"chk65" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v190";
      %"v191" : P = (RawLoadPointer 0 load_effects) %"chk65";
      %"chk66" : A = (Renew 0 8 Write 8) %"chk59", %"v173";
      store.ptr [%"chk66" + 0] <- %"v191";
      %"chk67" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v186";
      store.ptr [%"chk67" + 0] <- %"v191";
      %"chk68" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
      %"v193" : W = (RawLoad (LdNarrow Sw) 0) %"chk68";
      %"v194" : W = Or %"v193", #2048;
      %"chk69" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
      store Ww [%"chk69" + 0] <- %"v194";
      %"v199" : W = (RawLoad (LdNarrow Sw) 0) %"chk69";
      %"v201" : W = And %"v199", #514]))
    => br %"v201" ? "L195" : "L17";
  @"L195":
    %"v203" = %"v0" +p #160;
    %"chk71" : A = (Renew 0 8 Read 8) %"chk7", %"v203";
    %"v204" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v205" = %"v204" +p #40;
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v209" = %"v208" +p #32;
    %"chk73" : A = (Check 0 8 Read 8) %"v209";
    %"v210" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"chk74" : A = (Check 0 8 Write 8) %"v205";
    store.ptr [%"chk74" + 0] <- %"v210"
    => goto "L17";
  @"L17":
    %"v215" : W = (Cmp Eq W) %"v2", #4294967295
    => br %"v215" ? "L211" : "L213";
  @"L211":
    %"v220" = %"v0" +p #192;
    %"chk75" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v220";
    %"v221" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"v222" : W = (Cmp Sle W) %"v221", #0
    => br %"v222" ? "L216" : "L217";
  @"L216":
    %"v225" = %"v0" +p #32;
    %"chk76" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v225";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v228" = %"v0" +p #40;
    %"v229" : P = (RawLoadPointer 8 load_effects) %"chk76";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v233" : L = Ptoi %"v229";
    %"v234" : L = Ptoi %"v232";
    %"v235" : L = Sub %"v233", %"v234";
    call %"v236" : W = $"__GI__IO_do_write"(P %"v0", P %"v226", L %"v235")
    => goto "L218";
  @"L217":
    %"v239" = %"v0" +p #160;
    %"chk79" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v239";
    %"v240" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v241" = %"v240" +p #24;
    %"chk80" : A = (Check 0 8 Read 8) %"v241";
    %"v242" : P = (RawLoadPointer 0 load_effects) %"chk80";
    %"v245" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v246" = %"v245" +p #32;
    %"chk82" : A = (Check 0 8 Read 8) %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk82";
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v251" = %"v250" +p #24;
    %"chk84" : A = (Check 0 8 Read 8) %"v251";
    %"v252" : P = (RawLoadPointer 0 load_effects) %"chk84";
    %"v253" : L = Ptoi %"v247";
    %"v254" : L = Ptoi %"v252";
    %"v255" : L = Sub %"v253", %"v254";
    %"v256" : L = Div %"v255", #4;
    call %"v257" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v242", L %"v256")
    => goto "L218";
  @"L218" [%"v258" : W = phi("L216" => %"v236", "L217" => %"v257")]:
    => ret %"v258";
  @"L213":
    %"v264" = %"v0" +p #160;
    %"chk85" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v264";
    %"v265" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v266" = %"v265" +p #32;
    %"chk86" : A = (Check 0 8 Read 8) %"v266";
    %"v267" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"v270" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v271" = %"v270" +p #56;
    %"chk88" : A = (Check 0 8 Read 8) %"v271";
    %"v272" : P = (RawLoadPointer 0 load_effects) %"chk88";
    %"v273" : L = Ptoi %"v267";
    %"v274" : L = Ptoi %"v272";
    %"v275" : W = (Cmp Eq L) %"v273", %"v274"
    => br %"v275" ? "L260" : "L262";
  @"L260":
    %"v283" = %"v0" +p #192;
    %"chk89" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v283";
    %"v284" : W = (RawLoad (LdNarrow Sw) 0) %"chk89";
    %"v285" : W = (Cmp Sle W) %"v284", #0
    => br %"v285" ? "L279" : "L280";
  @"L279":
    %"v288" = %"v0" +p #32;
    %"chk90" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v288";
    %"v289" : P = (RawLoadPointer 0 load_effects) %"chk90";
    %"v291" = %"v0" +p #40;
    %"v292" : P = (RawLoadPointer 8 load_effects) %"chk90";
    %"v295" : P = (RawLoadPointer 0 load_effects) %"chk90";
    %"v296" : L = Ptoi %"v292";
    %"v297" : L = Ptoi %"v295";
    %"v298" : L = Sub %"v296", %"v297";
    call %"v299" : W = $"__GI__IO_do_write"(P %"v0", P %"v289", L %"v298")
    => goto "L281";
  @"L280":
    %"v302" = %"v0" +p #160;
    %"v303" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v304" = %"v303" +p #24;
    %"chk94" : A = (Check 0 8 Read 8) %"v304";
    %"v305" : P = (RawLoadPointer 0 load_effects) %"chk94";
    %"v308" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v309" = %"v308" +p #32;
    %"chk96" : A = (Check 0 8 Read 8) %"v309";
    %"v310" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"v313" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v314" = %"v313" +p #24;
    %"chk98" : A = (Check 0 8 Read 8) %"v314";
    %"v315" : P = (RawLoadPointer 0 load_effects) %"chk98";
    %"v316" : L = Ptoi %"v310";
    %"v317" : L = Ptoi %"v315";
    %"v318" : L = Sub %"v316", %"v317";
    %"v319" : L = Div %"v318", #4;
    call %"v320" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v305", L %"v319")
    => goto "L281";
  @"L281" [%"v321" : W = phi("L279" => %"v299", "L280" => %"v320")]:
    %"v323" : W = (Cmp Eq W) %"v321", #4294967295
    => br %"v323" ? "L276" : "L262";
  @"L276":
    => ret #4294967295;
  @"L262":
    %"v326" = %"v0" +p #160;
    %"chk99" : A = (Renew 0 8 Read 8) %"chk85", %"v326";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"v328" = %"v327" +p #32;
    %"chk100" : A = (Check 0 8 Read 8) %"v328";
    %"v329" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"v330" = %"v329" +p #4;
    %"chk101" : A = (Renew 0 8 Write 8) %"chk100", %"v328";
    store.ptr [%"chk101" + 0] <- %"v330";
    %"chk102" : A = (Check 0 4 Write 1) %"v329";
    store Ww [%"chk102" + 0] <- %"v2";
    %"chk103" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v336" : W = (RawLoad (LdNarrow Sw) 0) %"chk103";
    %"v337" : W = And %"v336", #2
    => br %"v337" ? "L339" : "L338";
  @"L338":
    %"v341" : W = (RawLoad (LdNarrow Sw) 0) %"chk103";
    %"v342" : W = And %"v341", #512
    => br %"v342" ? "L343" : "L339";
  @"L343":
    %"v346" : W = (Cmp Eq W) %"v2", #10
    => goto "L339";
  @"L339" [%"v350" : W = phi("L262" => #1, "L338" => #0, "L343" => %"v346")]:
    => br %"v350" ? "L332" : "L334";
  @"L332":
    %"v358" = %"v0" +p #192;
    %"chk105" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v358";
    %"v359" : W = (RawLoad (LdNarrow Sw) 0) %"chk105";
    %"v360" : W = (Cmp Sle W) %"v359", #0
    => br %"v360" ? "L354" : "L355";
  @"L354":
    %"v363" = %"v0" +p #32;
    %"chk106" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v363";
    %"v364" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"v366" = %"v0" +p #40;
    %"v367" : P = (RawLoadPointer 8 load_effects) %"chk106";
    %"v370" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"v371" : L = Ptoi %"v367";
    %"v372" : L = Ptoi %"v370";
    %"v373" : L = Sub %"v371", %"v372";
    call %"v374" : W = $"__GI__IO_do_write"(P %"v0", P %"v364", L %"v373")
    => goto "L356";
  @"L355":
    %"v377" = %"v0" +p #160;
    %"chk109" : A = (Renew 0 8 Read 8) %"chk85", %"v377";
    %"v378" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"v379" = %"v378" +p #24;
    %"chk110" : A = (Check 0 8 Read 8) %"v379";
    %"v380" : P = (RawLoadPointer 0 load_effects) %"chk110";
    %"v383" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"v384" = %"v383" +p #32;
    %"chk112" : A = (Check 0 8 Read 8) %"v384";
    %"v385" : P = (RawLoadPointer 0 load_effects) %"chk112";
    %"v388" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"v389" = %"v388" +p #24;
    %"chk114" : A = (Check 0 8 Read 8) %"v389";
    %"v390" : P = (RawLoadPointer 0 load_effects) %"chk114";
    %"v391" : L = Ptoi %"v385";
    %"v392" : L = Ptoi %"v390";
    %"v393" : L = Sub %"v391", %"v392";
    %"v394" : L = Div %"v393", #4;
    call %"v395" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v380", L %"v394")
    => goto "L356";
  @"L356" [%"v396" : W = phi("L354" => %"v374", "L355" => %"v395")]:
    %"v398" : W = (Cmp Eq W) %"v396", #4294967295
    => br %"v398" ? "L351" : "L334";
  @"L351":
    => ret #4294967295;
  @"L334":
    => ret %"v2"
} }.

Definition fn___GI__IO_wfile_seekoff : func :=
  ir_fn{ "export" "__GI__IO_wfile_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v331" : P = (Alloc 8) #144;
    %"v16" : W = (Cmp Eq W) %"v6", #0
    => br %"v16" ? "iw_1.start" : "L14" };
  ir_blk{ @"iw_1.start":
    %"iw_1.v166" : P = (Alloc 4) #8;
    %"iw_1.v240" : P = (Alloc 8) #8;
    %"iw_1.v242" : P = (Alloc 8) #8;
    %"iw_1.v249" : P = (Alloc 4) #8;
    %"iw_1.v8" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v10" = %"iw_1.v9" +p #48;
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v12" : L = Ptoi %"iw_1.v11";
    %"iw_1.v13" : L = Ptoi #0;
    %"iw_1.v14" : W = (Cmp Ne L) %"iw_1.v12", %"iw_1.v13"
    => br %"iw_1.v14" ? "iw_1.L4" : "iw_1.L6" };
  ir_blk{ @"iw_1.L4":
    %"iw_1.v20" = %"v0" +p #160;
    %"iw_1.v21" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v22" = %"iw_1.v21" +p #32;
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v22";
    %"iw_1.v23" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v26" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v27" = %"iw_1.v26" +p #24;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v27";
    %"iw_1.v28" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v29" : L = Ptoi %"iw_1.v23";
    %"iw_1.v30" : L = Ptoi %"iw_1.v28";
    %"iw_1.v31" : W = (Cmp Ugt L) %"iw_1.v29", %"iw_1.v30";
    %"chk6" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"iw_1.v36" : W = And %"iw_1.v35", #4096;
    %"iw_1.v37" : W = (Cmp Eq W) %"iw_1.v36", #4096
    => br %"iw_1.v31" ? "iw_1.L43" : "iw_1.L44" };
  ir_blk{ @"iw_1.L43":
    => goto "iw_1.L44" };
  ir_blk{ @"iw_1.L44" [%"iw_1.v47" : W = phi("iw_1.L4" => #0, "iw_1.L43" => %"iw_1.v37")]:
    => br %"iw_1.v47" ? "iw_1.L39" : "iw_1.L41" };
  ir_blk{ @"iw_1.L39":
    %"iw_1.v49" = %"v0" +p #216;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v49";
    %"iw_1.v50" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.iw_1.v4" : L = Ptoi %"iw_1.v50";
    %"iw_1.iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_1.v8" : L = Ptoi %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v9" : L = Sub %"iw_1.iw_1.v4", %"iw_1.iw_1.v8";
    %"iw_1.iw_1.v15" : W = (Cmp Uge L) %"iw_1.iw_1.v9", #2352
    => br %"iw_1.iw_1.v15" ? "iw_1.iw_1.L10" : "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.join":
    %"iw_1.v52" = %"iw_1.v50" +p #128;
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v52";
    %"iw_1.v53" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : F = CheckFunction %"iw_1.v53";
    rawcall %"iw_1.v55" : L = %"chk9"(P %"v0", L #0, W #2);
    %"iw_1.v62" : W = (Cmp Eq L) %"iw_1.v55", #18446744073709551615
    => br %"iw_1.v62" ? "iw_1.join" : "iw_1.L57" };
  ir_blk{ @"iw_1.L57":
    %"iw_1.v67" = %"v0" +p #144;
    %"chk10" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"iw_1.v67";
    store Wl [%"chk10" + 0] <- %"iw_1.v55"
    => goto "iw_1.L41" };
  ir_blk{ @"iw_1.L41":
    %"chk11" : A = (Renew 0 4 Read 1) %"chk6", %"v0";
    %"iw_1.v73" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"iw_1.v74" : W = And %"iw_1.v73", #256
    => br %"iw_1.v74" ? "iw_1.L69" : "iw_1.L70" };
  ir_blk{ @"iw_1.L69":
    %"iw_1.v79" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v79";
    %"iw_1.v80" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (Check 0 8 Read 8) %"iw_1.v80";
    %"iw_1.v81" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v84" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v85" = %"iw_1.v84" +p #8;
    %"chk15" : A = (Check 0 8 Read 8) %"iw_1.v85";
    %"iw_1.v86" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_1.v87" : L = Ptoi %"iw_1.v81";
    %"iw_1.v88" : L = Ptoi %"iw_1.v86";
    %"iw_1.v89" : W = (Cmp Ult L) %"iw_1.v87", %"iw_1.v88"
    => br %"iw_1.v89" ? "iw_1.L75" : "iw_1.L77" };
  ir_blk{ @"iw_1.L75":
    %"iw_1.v90" : P = Copy $"__libc_errno";
    %"chk16" : A = (Check 0 4 Write 1) %"iw_1.v90";
    store Ww [%"chk16" + 0] <- #22
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L77":
    %"iw_1.v95" = %"v0" +p #160;
    %"iw_1.v96" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v97" = %"iw_1.v96" +p #64;
    %"chk18" : A = (Check 0 8 Read 8) %"iw_1.v97";
    %"iw_1.v98" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"iw_1.v102" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v103" = %"iw_1.v102" +p #80;
    %"chk20" : A = (Check 0 8 Read 8) %"iw_1.v103";
    %"iw_1.v104" : P = (RawLoadPointer 0 load_effects) %"chk20"
    => goto "iw_1.L71" };
  ir_blk{ @"iw_1.L70":
    %"iw_1.v106" = %"v0" +p #160;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v106";
    %"iw_1.v107" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_1.v108" = %"iw_1.v107" +p #16;
    %"chk22" : A = (Check 0 8 Read 8) %"iw_1.v108";
    %"iw_1.v109" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_1.v112" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 8 Read 8) %"iw_1.v112";
    %"iw_1.v113" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_1.v116" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_1.v117" = %"iw_1.v116" +p #8;
    %"chk26" : A = (Check 0 8 Read 8) %"iw_1.v117";
    %"iw_1.v118" : P = (RawLoadPointer 0 load_effects) %"chk26"
    => goto "iw_1.L71" };
  ir_blk{ @"iw_1.L71" [%"iw_1.pr.9" : P = phi("iw_1.L70" => %"iw_1.v118", "iw_1.L77" => %"iw_1.v104"); %"iw_1.pr.8" : P = phi("iw_1.L70" => %"iw_1.v113", "iw_1.L77" => %"iw_1.v98"); %"iw_1.pr.7" : P = phi("iw_1.L70" => %"iw_1.v109", "iw_1.L77" => %"iw_1.v98")]:
    %"iw_1.v121" = %"v0" +p #152;
    %"chk27" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v121";
    %"iw_1.v122" : P = (RawLoadPointer 0 load_effects) %"chk27";
    call %"iw_1.v125" : W = $"__libio_codecvt_encoding"(P %"iw_1.v122");
    %"iw_1.v130" : W = (Cmp Ule L) %"iw_1.v29", %"iw_1.v30"
    => br %"iw_1.v130" ? "iw_1.L126" : "iw_1.L127" };
  ir_blk{ @"iw_1.L126":
    %"iw_1.v135" : W = (Cmp Sgt W) %"iw_1.v125", #0
    => br %"iw_1.v135" ? "iw_1.L131" : "iw_1.L132" };
  ir_blk{ @"iw_1.L131":
    %"iw_1.v139" : L = Ptoi %"iw_1.pr.9";
    %"iw_1.v140" : L = Ptoi %"iw_1.pr.8";
    %"iw_1.v141" : L = Sub %"iw_1.v139", %"iw_1.v140";
    %"iw_1.v142" : L = Div %"iw_1.v141", #4;
    %"iw_1.v144" : L = (Ext Sw) %"iw_1.v125";
    %"iw_1.v145" : L = Mul %"iw_1.v142", %"iw_1.v144";
    %"iw_1.v146" : L = Sub #0, %"iw_1.v145";
    %"iw_1.v149" = %"v0" +p #16;
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v149";
    %"iw_1.v150" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"iw_1.v152" = %"v0" +p #8;
    %"chk29" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v152";
    %"iw_1.v153" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_1.v154" : L = Ptoi %"iw_1.v150";
    %"iw_1.v155" : L = Ptoi %"iw_1.v153";
    %"iw_1.v156" : L = Sub %"iw_1.v154", %"iw_1.v155";
    %"iw_1.v157" : L = Sub %"iw_1.v146", %"iw_1.v156"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L132":
    %"iw_1.v162" : L = Ptoi %"iw_1.pr.8";
    %"iw_1.v163" : L = Ptoi %"iw_1.pr.7";
    %"iw_1.v164" : L = Sub %"iw_1.v162", %"iw_1.v163";
    %"iw_1.v165" : L = Div %"iw_1.v164", #4;
    %"iw_1.v168" = %"v0" +p #160;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v168";
    %"iw_1.v169" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_1.v170" = %"iw_1.v169" +p #96;
    %"chk31" : A = (Check 0 8 Read 1) %"iw_1.v170";
    %"iw_1.v171" : L = (RawLoad LdL 0) %"chk31";
    %"chk32" : A = (Check 0 8 Write 1) %"iw_1.v166";
    store Wl [%"chk32" + 0] <- %"iw_1.v171";
    %"iw_1.v174" = %"v0" +p #24;
    %"chk33" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v174";
    %"iw_1.v175" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"iw_1.v177" = %"v0" +p #16;
    %"chk34" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v177";
    %"iw_1.v178" : P = (RawLoadPointer 0 load_effects) %"chk34";
    call %"iw_1.v180" : W = $"__libio_codecvt_length"(P %"iw_1.v122", P %"iw_1.v166", P %"iw_1.v175", P %"iw_1.v178", L %"iw_1.v165");
    %"chk35" : A = (Renew 0 8 Read 8) %"chk34", %"iw_1.v177";
    %"iw_1.v184" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Read 8) %"chk33", %"iw_1.v174";
    %"iw_1.v187" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"iw_1.v188" : L = Ptoi %"iw_1.v184";
    %"iw_1.v189" : L = Ptoi %"iw_1.v187";
    %"iw_1.v190" : L = Sub %"iw_1.v188", %"iw_1.v189";
    %"iw_1.v192" : L = (Ext Sw) %"iw_1.v180";
    %"iw_1.v193" : L = Sub %"iw_1.v190", %"iw_1.v192";
    %"iw_1.v194" : L = Sub #0, %"iw_1.v193"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L127":
    %"iw_1.v199" : W = (Cmp Sgt W) %"iw_1.v125", #0
    => br %"iw_1.v199" ? "iw_1.L195" : "iw_1.L196" };
  ir_blk{ @"iw_1.L195":
    %"iw_1.v202" = %"v0" +p #160;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v202";
    %"iw_1.v203" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_1.v204" = %"iw_1.v203" +p #32;
    %"chk38" : A = (Check 0 8 Read 8) %"iw_1.v204";
    %"iw_1.v205" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"iw_1.v208" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_1.v209" = %"iw_1.v208" +p #24;
    %"chk40" : A = (Check 0 8 Read 8) %"iw_1.v209";
    %"iw_1.v210" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"iw_1.v211" : L = Ptoi %"iw_1.v205";
    %"iw_1.v212" : L = Ptoi %"iw_1.v210";
    %"iw_1.v213" : L = Sub %"iw_1.v211", %"iw_1.v212";
    %"iw_1.v214" : L = Div %"iw_1.v213", #4;
    %"iw_1.v216" : L = (Ext Sw) %"iw_1.v125";
    %"iw_1.v217" : L = Mul %"iw_1.v214", %"iw_1.v216"
    => goto "iw_1.L197" };
  ir_blk{ @"iw_1.L196":
    %"iw_1.v221" = %"v0" +p #160;
    %"chk41" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v221";
    %"iw_1.v222" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"iw_1.v223" = %"iw_1.v222" +p #32;
    %"chk42" : A = (Check 0 8 Read 8) %"iw_1.v223";
    %"iw_1.v224" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"iw_1.v227" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"iw_1.v228" = %"iw_1.v227" +p #24;
    %"chk44" : A = (Check 0 8 Read 8) %"iw_1.v228";
    %"iw_1.v229" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"iw_1.v230" : L = Ptoi %"iw_1.v224";
    %"iw_1.v231" : L = Ptoi %"iw_1.v229";
    %"iw_1.v232" : L = Sub %"iw_1.v230", %"iw_1.v231";
    %"iw_1.v233" : L = Div %"iw_1.v232", #4;
    %"iw_1.v236" : L = Shl %"iw_1.v233", #2;
    call %"iw_1.v239" : P = $"malloc"(L %"iw_1.v236");
    %"chk45" : A = (Check 0 8 Write 8) %"iw_1.v240";
    store.ptr [%"chk45" + 0] <- %"iw_1.v239";
    %"chk46" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v221";
    %"iw_1.v245" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"iw_1.v246" = %"iw_1.v245" +p #24;
    %"chk47" : A = (Check 0 8 Read 8) %"iw_1.v246";
    %"iw_1.v247" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"chk48" : A = (Check 0 8 Write 8) %"iw_1.v242";
    store.ptr [%"chk48" + 0] <- %"iw_1.v247";
    %"chk49" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v221";
    %"iw_1.v252" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_1.v253" = %"iw_1.v252" +p #96;
    %"chk50" : A = (Check 0 8 Read 1) %"iw_1.v253";
    %"iw_1.v254" : L = (RawLoad LdL 0) %"chk50";
    %"chk51" : A = (Check 0 8 Write 1) %"iw_1.v249";
    store Wl [%"chk51" + 0] <- %"iw_1.v254";
    %"chk52" : A = (Renew 0 8 Read 8) %"chk48", %"iw_1.v242";
    %"iw_1.v256" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"iw_1.v257" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"iw_1.v260" = %"iw_1.v257" +p %"iw_1.v236";
    %"iw_1.v264" = %"iw_1.v239" +p %"iw_1.v236";
    call %"iw_1.v265" : W = $"__libio_codecvt_out"(P %"iw_1.v122", P %"iw_1.v249", P %"iw_1.v256", P %"iw_1.v260", P %"iw_1.v242", P %"iw_1.v239", P %"iw_1.v264", P %"iw_1.v240");
    %"iw_1.v270" : W = (Cmp Ne W) %"iw_1.v265", #0
    => br %"iw_1.v270" ? "iw_1.L266" : "iw_1.L268" };
  ir_blk{ @"iw_1.L266":
    call void $"free"(P %"iw_1.v239")
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L268":
    %"chk54" : A = (Renew 0 8 Read 8) %"chk45", %"iw_1.v240";
    %"iw_1.v276" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"iw_1.v278" : L = Ptoi %"iw_1.v276";
    %"iw_1.v279" : L = Ptoi %"iw_1.v239";
    %"iw_1.v280" : L = Sub %"iw_1.v278", %"iw_1.v279";
    call void $"free"(P %"iw_1.v239")
    => goto "iw_1.L197" };
  ir_blk{ @"iw_1.L197" [%"iw_1.pr.4" : L = phi("iw_1.L195" => %"iw_1.v217", "iw_1.L268" => %"iw_1.v280")]:
    => br %"iw_1.v37" ? "iw_1.L283" : "iw_1.L284" };
  ir_blk{ @"iw_1.L283":
    %"iw_1.v289" = %"v0" +p #40;
    %"chk55" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v289";
    %"iw_1.v290" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"iw_1.v292" = %"v0" +p #32;
    %"chk56" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v292";
    %"iw_1.v293" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"iw_1.v294" : L = Ptoi %"iw_1.v290";
    %"iw_1.v295" : L = Ptoi %"iw_1.v293";
    %"iw_1.v296" : L = Sub %"iw_1.v294", %"iw_1.v295";
    %"iw_1.v297" : L = Add %"iw_1.pr.4", %"iw_1.v296"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L284":
    %"iw_1.v300" = %"v0" +p #40;
    %"chk57" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v300";
    %"iw_1.v301" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"iw_1.v303" = %"v0" +p #16;
    %"chk58" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v303";
    %"iw_1.v304" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"iw_1.v305" : L = Ptoi %"iw_1.v301";
    %"iw_1.v306" : L = Ptoi %"iw_1.v304";
    %"iw_1.v307" : L = Sub %"iw_1.v305", %"iw_1.v306";
    %"iw_1.v308" : L = Add %"iw_1.pr.4", %"iw_1.v307"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L6" [%"iw_1.pr.6" : L = phi("iw_1.L131" => %"iw_1.v157", "iw_1.L132" => %"iw_1.v194", "iw_1.L283" => %"iw_1.v297", "iw_1.L284" => %"iw_1.v308", "iw_1.start" => #0)]:
    %"iw_1.v313" = %"v0" +p #144;
    %"chk59" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"iw_1.v313";
    %"iw_1.v314" : L = (RawLoad LdL 0) %"chk59";
    %"iw_1.v317" : W = (Cmp Ne L) %"iw_1.v314", #18446744073709551615
    => br %"iw_1.v317" ? "iw_1.L309" : "iw_1.L310" };
  ir_blk{ @"iw_1.L309":
    %"iw_1.v319" = %"v0" +p #144;
    %"iw_1.v320" : L = (RawLoad LdL 0) %"chk59"
    => goto "iw_1.L311" };
  ir_blk{ @"iw_1.L310":
    %"iw_1.v322" = %"v0" +p #216;
    %"chk61" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v322";
    %"iw_1.v323" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"iw_1.iw_2.v4" : L = Ptoi %"iw_1.v323";
    %"iw_1.iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_2.v8" : L = Ptoi %"iw_1.iw_2.v7";
    %"iw_1.iw_2.v9" : L = Sub %"iw_1.iw_2.v4", %"iw_1.iw_2.v8";
    %"iw_1.iw_2.v15" : W = (Cmp Uge L) %"iw_1.iw_2.v9", #2352
    => br %"iw_1.iw_2.v15" ? "iw_1.iw_2.L10" : "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.join":
    %"iw_1.v325" = %"iw_1.v323" +p #128;
    %"chk62" : A = (Check 0 8 Read 8) %"iw_1.v325";
    %"iw_1.v326" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"chk63" : F = CheckFunction %"iw_1.v326";
    rawcall %"iw_1.v328" : L = %"chk63"(P %"v0", L #0, W #1)
    => goto "iw_1.L311" };
  ir_blk{ @"iw_1.L311" [%"iw_1.pr.1" : L = phi("iw_1.L309" => %"iw_1.v320", "iw_1.iw_2.join" => %"iw_1.v328")]:
    %"iw_1.v335" : W = (Cmp Eq L) %"iw_1.pr.1", #18446744073709551615
    => br %"iw_1.v335" ? "iw_1.join" : "iw_1.L331" };
  ir_blk{ @"iw_1.L331":
    %"iw_1.v340" : L = Add %"iw_1.pr.1", %"iw_1.pr.6";
    %"iw_1.v345" : W = (Cmp Slt L) %"iw_1.v340", #0
    => br %"iw_1.v345" ? "iw_1.L341" : "iw_1.join" };
  ir_blk{ @"iw_1.L341":
    %"iw_1.v346" : P = Copy $"__libc_errno";
    %"chk64" : A = (Check 0 4 Write 1) %"iw_1.v346";
    store Ww [%"chk64" + 0] <- #22
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join" [%"v18" : L = phi("iw_1.L75" => #18446744073709551615, "iw_1.L266" => #4294967295, "iw_1.L341" => #18446744073709551615, "iw_1.iw_1.join" => #18446744073709551615, "iw_1.L311" => %"iw_1.pr.1", "iw_1.L331" => %"iw_1.v340")]:
    => ret %"v18" };
  ir_blk{ @"L14":
    %"v22" = %"v0" +p #160;
    %"chk65" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v24" = %"v23" +p #16;
    %"chk66" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v29" = %"v28" +p #8;
    %"chk68" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"v31" : L = Ptoi %"v25";
    %"v32" : L = Ptoi %"v30";
    %"v33" : W = (Cmp Eq L) %"v31", %"v32"
    => br %"v33" ? "L34" : "L35" };
  ir_blk{ @"L34":
    %"v37" = %"v0" +p #160;
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v39" = %"v38" +p #24;
    %"chk70" : A = (Check 0 8 Read 8) %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v44" = %"v43" +p #32;
    %"chk72" : A = (Check 0 8 Read 8) %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk72";
    %"v46" : L = Ptoi %"v40";
    %"v47" : L = Ptoi %"v45";
    %"v48" : W = (Cmp Eq L) %"v46", %"v47"
    => goto "L35" };
  ir_blk{ @"L35" [%"v50" : W = phi("L14" => #0, "L34" => %"v48")]:
    %"v53" = %"v0" +p #160;
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v55" = %"v54" +p #32;
    %"chk74" : A = (Check 0 8 Read 8) %"v55";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk74";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v60" = %"v59" +p #24;
    %"chk76" : A = (Check 0 8 Read 8) %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v62" : L = Ptoi %"v56";
    %"v63" : L = Ptoi %"v61";
    %"v64" : W = (Cmp Ugt L) %"v62", %"v63"
    => br %"v64" ? "L66" : "L65" };
  ir_blk{ @"L65":
    %"chk77" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v68" : W = (RawLoad (LdNarrow Sw) 0) %"chk77";
    %"v69" : W = And %"v68", #2048;
    %"v70" : W = (Cmp Ne W) %"v69", #0
    => goto "L66" };
  ir_blk{ @"L66" [%"v71" : W = phi("L35" => #1, "L65" => %"v70")]:
    => br %"v71" ? "L77" : "L78" };
  ir_blk{ @"L77":
    call %"v80" : W = $"__GI__IO_switch_to_wget_mode"(P %"v0");
    %"v81" : W = (Cmp Ne W) %"v80", #0
    => goto "L78" };
  ir_blk{ @"L78" [%"v82" : W = phi("L66" => #0, "L77" => %"v81")]:
    => br %"v82" ? "L73" : "L75" };
  ir_blk{ @"L73":
    => ret #4294967295 };
  ir_blk{ @"L75":
    %"v88" = %"v0" +p #160;
    %"chk78" : A = (Renew 0 8 Read 8) %"chk65", %"v88";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v90" = %"v89" +p #48;
    %"chk79" : A = (Check 0 8 Read 8) %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v92" : L = Ptoi %"v91";
    %"v93" : L = Ptoi #0;
    %"v94" : W = (Cmp Eq L) %"v92", %"v93"
    => br %"v94" ? "L84" : "L192" };
  ir_blk{ @"L84":
    %"v99" = %"v0" +p #160;
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v101" = %"v100" +p #16;
    %"chk81" : A = (Check 0 8 Read 8) %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk81";
    %"v103" : L = Ptoi %"v102";
    %"v105" : W = (Cmp Ne L) %"v103", %"v93"
    => br %"v105" ? "L95" : "L97" };
  ir_blk{ @"L95":
    %"v107" = %"v0" +p #160;
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v109" = %"v108" +p #16;
    %"chk83" : A = (Check 0 8 Read 8) %"v109";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk83";
    call void $"free"(P %"v110");
    %"chk84" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v112" : W = (RawLoad (LdNarrow Sw) 0) %"chk84";
    %"v114" : W = And %"v112", #4294967039;
    %"chk85" : A = (Renew 0 4 Write 1) %"chk84", %"v0";
    store Ww [%"chk85" + 0] <- %"v114"
    => goto "L97" };
  ir_blk{ @"L97":
    code ((app ir[ call void $"__GI__IO_doallocbuf"(P %"v0");
      %"v117" = %"v0" +p #32;
      %"v119" = %"v0" +p #40;
      %"v121" = %"v0" +p #56;
      %"chk86" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v121";
      %"v122" : P = (RawLoadPointer 0 load_effects) %"chk86";
      %"chk87" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v119";
      store.ptr [%"chk87" + 0] <- %"v122";
      %"chk88" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v117";
      store.ptr [%"chk88" + 0] <- %"v122";
      %"v124" = %"v0" +p #48;
      %"chk89" : A = (Renew 0 8 Read 8) %"chk86", %"v121";
      %"v127" : P = (RawLoadPointer 0 load_effects) %"chk89";
      %"chk90" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v124";
      store.ptr [%"chk90" + 0] <- %"v127";
      %"v129" = %"v0" +p #24;
      %"chk91" : A = (Renew 0 8 Read 8) %"chk86", %"v121";
      %"v132" : P = (RawLoadPointer 0 load_effects) %"chk91";
      %"chk92" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v129";
      store.ptr [%"chk92" + 0] <- %"v132";
      %"v134" = %"v0" +p #8;
      %"chk93" : A = (Renew 0 8 Read 8) %"chk86", %"v121";
      %"v137" : P = (RawLoadPointer 0 load_effects) %"chk93";
      %"chk94" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v134";
      store.ptr [%"chk94" + 0] <- %"v137";
      %"v139" = %"v0" +p #16;
      %"chk95" : A = (Renew 0 8 Read 8) %"chk86", %"v121";
      %"v142" : P = (RawLoadPointer 0 load_effects) %"chk95";
      %"chk96" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v139";
      store.ptr [%"chk96" + 0] <- %"v142";
      %"v144" = %"v0" +p #160;
      %"chk97" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v145" : P = (RawLoadPointer 0 load_effects) %"chk97";
      %"v146" = %"v145" +p #24;
      %"v149" : P = (RawLoadPointer 0 load_effects) %"chk97";
      %"v150" = %"v149" +p #32;
      %"v153" : P = (RawLoadPointer 0 load_effects) %"chk97";
      %"v154" = %"v153" +p #48;
      %"chk100" : A = (Check 0 8 Read 8) %"v154"] ir[ %"v155" : P = (RawLoadPointer 0 load_effects) %"chk100";
      %"chk101" : A = (Check 0 8 Write 8) %"v150";
      store.ptr [%"chk101" + 0] <- %"v155";
      %"chk102" : A = (Check 0 8 Write 8) %"v146";
      store.ptr [%"chk102" + 0] <- %"v155";
      %"chk103" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v158" : P = (RawLoadPointer 0 load_effects) %"chk103";
      %"v159" = %"v158" +p #40;
      %"v162" : P = (RawLoadPointer 0 load_effects) %"chk103";
      %"v163" = %"v162" +p #48;
      %"chk105" : A = (Check 0 8 Read 8) %"v163";
      %"v164" : P = (RawLoadPointer 0 load_effects) %"chk105";
      %"chk106" : A = (Check 0 8 Write 8) %"v159";
      store.ptr [%"chk106" + 0] <- %"v164";
      %"chk107" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v167" : P = (RawLoadPointer 0 load_effects) %"chk107";
      %"v168" = %"v167" +p #16;
      %"v171" : P = (RawLoadPointer 0 load_effects) %"chk107";
      %"v172" = %"v171" +p #48;
      %"chk109" : A = (Check 0 8 Read 8) %"v172";
      %"v173" : P = (RawLoadPointer 0 load_effects) %"chk109";
      %"chk110" : A = (Check 0 8 Write 8) %"v168";
      store.ptr [%"chk110" + 0] <- %"v173";
      %"chk111" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v176" : P = (RawLoadPointer 0 load_effects) %"chk111";
      %"v179" : P = (RawLoadPointer 0 load_effects) %"chk111";
      %"v180" = %"v179" +p #48;
      %"chk113" : A = (Check 0 8 Read 8) %"v180";
      %"v181" : P = (RawLoadPointer 0 load_effects) %"chk113";
      %"chk114" : A = (Check 0 8 Write 8) %"v176";
      store.ptr [%"chk114" + 0] <- %"v181";
      %"chk115" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v184" : P = (RawLoadPointer 0 load_effects) %"chk115";
      %"v185" = %"v184" +p #8;
      %"v188" : P = (RawLoadPointer 0 load_effects) %"chk115";
      %"v189" = %"v188" +p #48;
      %"chk117" : A = (Check 0 8 Read 8) %"v189";
      %"v190" : P = (RawLoadPointer 0 load_effects) %"chk117";
      %"chk118" : A = (Check 0 8 Write 8) %"v185";
      store.ptr [%"chk118" + 0] <- %"v190"]))
    => goto "L192" };
  ir_blk{ @"L196":
    %"v198" = %"v0" +p #152;
    %"chk119" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v198";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk119";
    call %"v201" : W = $"__libio_codecvt_encoding"(P %"v199");
    %"v206" : W = (Cmp Ne W) %"v6", #0
    => br %"v206" ? "L208" : "L207" };
  ir_blk{ @"L207":
    %"v210" : W = (Cmp Eq W) %"v71", #0
    => goto "L208" };
  ir_blk{ @"L208" [%"v212" : W = phi("L196" => #1, "L207" => %"v210")]:
    => br %"v212" ? "L202" : "L204" };
  ir_blk{ @"L202":
    %"v217" : W = (Cmp Sgt W) %"v201", #0
    => br %"v217" ? "L213" : "L214" };
  ir_blk{ @"L213":
    %"v220" = %"v0" +p #160;
    %"chk120" : A = (Renew 0 8 Read 8) %"chk65", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"v222" = %"v221" +p #8;
    %"chk121" : A = (Check 0 8 Read 8) %"v222";
    %"v223" : P = (RawLoadPointer 0 load_effects) %"chk121";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"chk123" : A = (Check 0 8 Read 8) %"v226";
    %"v227" : P = (RawLoadPointer 0 load_effects) %"chk123";
    %"v228" : L = Ptoi %"v223";
    %"v229" : L = Ptoi %"v227";
    %"v230" : L = Sub %"v228", %"v229";
    %"v231" : L = Div %"v230", #4;
    %"v233" : L = (Ext Sw) %"v201";
    %"v234" : L = Mul %"v231", %"v233";
    %"v235" : L = Sub %"v2", %"v234";
    %"v238" = %"v0" +p #16;
    %"chk124" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v238";
    %"v239" : P = (RawLoadPointer 0 load_effects) %"chk124";
    %"v241" = %"v0" +p #8;
    %"chk125" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v241";
    %"v242" : P = (RawLoadPointer 0 load_effects) %"chk125";
    %"v243" : L = Ptoi %"v239";
    %"v244" : L = Ptoi %"v242";
    %"v245" : L = Sub %"v243", %"v244";
    %"v246" : L = Sub %"v235", %"v245"
    => goto "L204" };
  ir_blk{ @"L214":
    %"v249" = %"v0" +p #160;
    %"chk126" : A = (Renew 0 8 Read 8) %"chk65", %"v249";
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"chk127" : A = (Check 0 8 Read 8) %"v250";
    %"v251" : P = (RawLoadPointer 0 load_effects) %"chk127";
    %"v254" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v255" = %"v254" +p #16;
    %"chk129" : A = (Check 0 8 Read 8) %"v255";
    %"v256" : P = (RawLoadPointer 0 load_effects) %"chk129";
    %"v257" : L = Ptoi %"v251";
    %"v258" : L = Ptoi %"v256";
    %"v259" : L = Sub %"v257", %"v258";
    %"v260" : L = Div %"v259", #4;
    %"v263" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v264" = %"v263" +p #88;
    %"v267" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v268" = %"v267" +p #96;
    %"chk132" : A = (Check 0 8 Read 1) %"v268";
    %"v269" : L = (RawLoad LdL 0) %"chk132";
    %"chk133" : A = (Check 0 8 Write 1) %"v264";
    store Wl [%"chk133" + 0] <- %"v269";
    %"v273" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v274" = %"v273" +p #88;
    %"v276" = %"v0" +p #24;
    %"chk135" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v276";
    %"v277" : P = (RawLoadPointer 0 load_effects) %"chk135";
    %"v279" = %"v0" +p #16;
    %"chk136" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v279";
    %"v280" : P = (RawLoadPointer 0 load_effects) %"chk136";
    call %"v282" : W = $"__libio_codecvt_length"(P %"v199", P %"v274", P %"v277", P %"v280", L %"v260");
    %"v284" = %"v0" +p #8;
    %"chk137" : A = (Renew 0 8 Read 8) %"chk135", %"v276";
    %"v287" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"v289" : L = (Ext Sw) %"v282";
    %"v290" = %"v287" +p %"v289";
    %"chk138" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v284";
    store.ptr [%"chk138" + 0] <- %"v290";
    %"chk139" : A = (Renew 0 8 Read 8) %"chk65", %"v249";
    %"v293" : P = (RawLoadPointer 0 load_effects) %"chk139";
    %"v294" = %"v293" +p #8;
    %"v297" : P = (RawLoadPointer 0 load_effects) %"chk139";
    %"chk141" : A = (Check 0 8 Read 8) %"v297";
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk141";
    %"chk142" : A = (Check 0 8 Write 8) %"v294";
    store.ptr [%"chk142" + 0] <- %"v298";
    %"chk143" : A = (Renew 0 8 Read 8) %"chk136", %"v279";
    %"v302" : P = (RawLoadPointer 0 load_effects) %"chk143";
    %"chk144" : A = (Renew 0 8 Read 8) %"chk135", %"v276";
    %"v305" : P = (RawLoadPointer 0 load_effects) %"chk144";
    %"v306" : L = Ptoi %"v302";
    %"v307" : L = Ptoi %"v305";
    %"v308" : L = Sub %"v306", %"v307";
    %"v311" : L = Sub %"v308", %"v289";
    %"v312" : L = Sub %"v2", %"v311"
    => goto "L204" };
  ir_blk{ @"L204" [%"pr.2" : L = phi("L213" => %"v246", "L214" => %"v312", "L208" => %"v2")]:
    %"v317" = %"v0" +p #144;
    %"chk145" : A = (HalfCheck Lower 0 8 Read 1) %"chk65", %"v317";
    %"v318" : L = (RawLoad LdL 0) %"chk145";
    %"v321" : W = (Cmp Eq L) %"v318", #18446744073709551615
    => br %"v321" ? "L322" : "L315" };
  ir_blk{ @"L315":
    %"v326" = %"v0" +p #144;
    %"v327" : L = (RawLoad LdL 0) %"chk145";
    %"v328" : L = Add %"pr.2", %"v327"
    => goto "L193" };
  ir_blk{ @"L330":
    %"v336" = %"v0" +p #216;
    %"chk147" : A = (HalfCheck Upper 0 8 Read 8) %"chk65", %"v336";
    %"v337" : P = (RawLoadPointer 0 load_effects) %"chk147";
    %"iw_2.v4" : L = Ptoi %"v337";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join" }] [ir_blk{ @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join":
    %"v339" = %"v337" +p #144;
    %"chk148" : A = (Check 0 8 Read 8) %"v339";
    %"v340" : P = (RawLoadPointer 0 load_effects) %"chk148";
    %"chk149" : F = CheckFunction %"v340";
    rawcall %"v342" : W = %"chk149"(P %"v0", P %"v331");
    %"v343" : W = (Cmp Eq W) %"v342", #0
    => br %"v343" ? "L344" : "L345" };
  ir_blk{ @"L344":
    %"v346" = %"v331" +p #24;
    %"chk150" : A = (Check 0 4 Read 1) %"v346";
    %"v347" : W = (RawLoad (LdNarrow Uw) 0) %"chk150";
    %"v348" : W = And %"v347", #61440;
    %"v349" : W = (Cmp Eq W) %"v348", #32768
    => goto "L345" };
  ir_blk{ @"L345" [%"v351" : W = phi("iw_2.join" => #0, "L344" => %"v349")]:
    => br %"v351" ? "L332" : "L322" };
  ir_blk{ @"L332":
    %"v353" = %"v331" +p #48;
    %"chk151" : A = (Check 0 8 Read 1) %"v353";
    %"v354" : L = (RawLoad LdL 0) %"chk151";
    %"v355" : L = Add %"v2", %"v354"
    => goto "L193" };
  ir_blk{ @"L192":
    %"v356" : W = (Cmp Eq W) %"v4", #1
    => br %"v356" ? poll "L196" : "L357" };
  ir_blk{ @"L357":
    %"v358" : W = (Cmp Eq W) %"v4", #0
    => br %"v358" ? "L193" : "L359" };
  ir_blk{ @"L359":
    %"v360" : W = (Cmp Eq W) %"v4", #2
    => br %"v360" ? poll "L330" : "L193" };
  ir_blk{ @"L193" [%"pr.5" : W = phi("L315" => #0, "L357" => %"v4", "L332" => #0, "L359" => %"v4"); %"pr.1" : L = phi("L315" => %"v328", "L357" => %"v2", "L332" => %"v355", "L359" => %"v2")]:
    call void $"__GI__IO_free_wbackup_area"(P %"v0");
    %"v367" = %"v0" +p #144;
    %"chk152" : A = (HalfCheck Lower 0 8 Read 1) %"chk65", %"v367";
    %"v368" : L = (RawLoad LdL 0) %"chk152";
    %"v371" : W = (Cmp Ne L) %"v368", #18446744073709551615
    => br %"v371" ? "L372" : "L373" };
  ir_blk{ @"L372":
    %"v375" = %"v0" +p #24;
    %"chk153" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v375";
    %"v376" : P = (RawLoadPointer 0 load_effects) %"chk153";
    %"v377" : L = Ptoi %"v376";
    %"v379" : W = (Cmp Ne L) %"v377", %"v93"
    => goto "L373" };
  ir_blk{ @"L373" [%"v381" : W = phi("L193" => #0, "L372" => %"v379")]:
    => br %"v381" ? "L382" : "L383" };
  ir_blk{ @"L382":
    %"chk154" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v385" : W = (RawLoad (LdNarrow Sw) 0) %"chk154";
    %"v386" : W = And %"v385", #256;
    %"v387" : W = (Cmp Eq W) %"v386", #0
    => goto "L383" };
  ir_blk{ @"L383" [%"v389" : W = phi("L373" => #0, "L382" => %"v387")]:
    => br %"v389" ? "L363" : "L365" };
  ir_blk{ @"L363":
    %"v392" = %"v0" +p #144;
    %"v393" : L = (RawLoad LdL 0) %"chk152";
    %"v395" = %"v0" +p #16;
    %"chk156" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v395";
    %"v396" : P = (RawLoadPointer 0 load_effects) %"chk156";
    %"v398" = %"v0" +p #56;
    %"v399" : P = (RawLoadPointer 40 load_effects) %"chk156";
    %"v400" : L = Ptoi %"v396";
    %"v401" : L = Ptoi %"v399";
    %"v402" : L = Sub %"v400", %"v401";
    %"v403" : L = Sub %"v393", %"v402";
    %"v409" : W = (Cmp Sge L) %"pr.1", %"v403"
    => br %"v409" ? "L410" : "L411" };
  ir_blk{ @"L410":
    %"v414" = %"v0" +p #144;
    %"v415" : L = (RawLoad LdL 0) %"chk152";
    %"v416" : W = (Cmp Slt L) %"pr.1", %"v415"
    => goto "L411" };
  ir_blk{ @"L411" [%"v418" : W = phi("L363" => #0, "L410" => %"v416")]:
    => br %"v418" ? "L404" : "L365" };
  ir_blk{ @"L404":
    code ((app ir[ %"v420" = %"v0" +p #24;
      %"v422" = %"v0" +p #56;
      %"v423" : P = (RawLoadPointer 40 load_effects) %"chk156";
      %"chk160" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v420";
      store.ptr [%"chk160" + 0] <- %"v423";
      %"v425" = %"v0" +p #8;
      %"chk161" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v422";
      %"v428" : P = (RawLoadPointer 0 load_effects) %"chk161";
      %"v431" : L = Sub %"pr.1", %"v403";
      %"v432" = %"v428" +p %"v431";
      %"chk162" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v425";
      store.ptr [%"chk162" + 0] <- %"v432";
      %"v434" = %"v0" +p #16;
      %"chk163" : A = (Renew 0 8 Read 8) %"chk156", %"v434";
      %"v437" : P = (RawLoadPointer 0 load_effects) %"chk163";
      %"chk164" : A = (Renew 0 8 Write 8) %"chk156", %"v434";
      store.ptr [%"chk164" + 0] <- %"v437";
      %"v439" = %"v0" +p #32;
      %"v441" = %"v0" +p #40;
      %"chk165" : A = (Renew 0 8 Read 8) %"chk161", %"v422";
      %"v444" : P = (RawLoadPointer 0 load_effects) %"chk165";
      %"chk166" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v441";
      store.ptr [%"chk166" + 0] <- %"v444";
      %"chk167" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v439";
      store.ptr [%"chk167" + 0] <- %"v444";
      %"v446" = %"v0" +p #48;
      %"chk168" : A = (Renew 0 8 Read 8) %"chk161", %"v422";
      %"v449" : P = (RawLoadPointer 0 load_effects) %"chk168";
      %"chk169" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v446";
      store.ptr [%"chk169" + 0] <- %"v449";
      %"v451" = %"v0" +p #160;
      %"chk170" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v452" : P = (RawLoadPointer 0 load_effects) %"chk170";
      %"v453" = %"v452" +p #16;
      %"v456" : P = (RawLoadPointer 0 load_effects) %"chk170";
      %"v457" = %"v456" +p #48;
      %"chk172" : A = (Check 0 8 Read 8) %"v457";
      %"v458" : P = (RawLoadPointer 0 load_effects) %"chk172";
      %"chk173" : A = (Check 0 8 Write 8) %"v453";
      store.ptr [%"chk173" + 0] <- %"v458";
      %"chk174" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v461" : P = (RawLoadPointer 0 load_effects) %"chk174"] ir[ %"v464" : P = (RawLoadPointer 0 load_effects) %"chk174";
      %"v465" = %"v464" +p #48;
      %"chk176" : A = (Check 0 8 Read 8) %"v465";
      %"v466" : P = (RawLoadPointer 0 load_effects) %"chk176";
      %"chk177" : A = (Check 0 8 Write 8) %"v461";
      store.ptr [%"chk177" + 0] <- %"v466";
      %"chk178" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v469" : P = (RawLoadPointer 0 load_effects) %"chk178";
      %"v470" = %"v469" +p #8;
      %"v473" : P = (RawLoadPointer 0 load_effects) %"chk178";
      %"v474" = %"v473" +p #48;
      %"chk180" : A = (Check 0 8 Read 8) %"v474";
      %"v475" : P = (RawLoadPointer 0 load_effects) %"chk180";
      %"chk181" : A = (Check 0 8 Write 8) %"v470";
      store.ptr [%"chk181" + 0] <- %"v475";
      %"chk182" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v478" : P = (RawLoadPointer 0 load_effects) %"chk182";
      %"v479" = %"v478" +p #24;
      %"v482" : P = (RawLoadPointer 0 load_effects) %"chk182";
      %"v483" = %"v482" +p #32;
      %"v486" : P = (RawLoadPointer 0 load_effects) %"chk182";
      %"v487" = %"v486" +p #48;
      %"chk185" : A = (Check 0 8 Read 8) %"v487";
      %"v488" : P = (RawLoadPointer 0 load_effects) %"chk185";
      %"chk186" : A = (Check 0 8 Write 8) %"v483";
      store.ptr [%"chk186" + 0] <- %"v488";
      %"chk187" : A = (Check 0 8 Write 8) %"v479";
      store.ptr [%"chk187" + 0] <- %"v488";
      %"chk188" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v491" : P = (RawLoadPointer 0 load_effects) %"chk188";
      %"v492" = %"v491" +p #40;
      %"v495" : P = (RawLoadPointer 0 load_effects) %"chk188";
      %"v496" = %"v495" +p #48;
      %"chk190" : A = (Check 0 8 Read 8) %"v496";
      %"v497" : P = (RawLoadPointer 0 load_effects) %"chk190";
      %"chk191" : A = (Check 0 8 Write 8) %"v492";
      store.ptr [%"chk191" + 0] <- %"v497";
      %"iw_3.v44" : P = (Alloc 8) #8;
      %"iw_3.v6" = %"v0" +p #152;
      %"chk192" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"iw_3.v6";
      %"iw_3.v7" : P = (RawLoadPointer 0 load_effects) %"chk192";
      call %"iw_3.v10" : W = $"__libio_codecvt_encoding"(P %"iw_3.v7");
      %"iw_3.v19" : W = (Cmp Sgt W) %"iw_3.v10", #0]))
    => br %"iw_3.v19" ? "iw_3.L11" : "iw_3.L13" };
  ir_blk{ @"iw_3.L11":
    %"iw_3.v23" = %"v0" +p #160;
    %"chk193" : A = (Renew 0 8 Read 8) %"chk65", %"iw_3.v23";
    %"iw_3.v24" : P = (RawLoadPointer 0 load_effects) %"chk193";
    %"iw_3.v25" = %"iw_3.v24" +p #8;
    %"chk194" : A = (Check 0 8 Read 8) %"iw_3.v25";
    %"iw_3.v26" : P = (RawLoadPointer 0 load_effects) %"chk194";
    %"iw_3.v28" = %"v0" +p #8;
    %"chk195" : A = (Renew 0 8 Read 8) %"chk162", %"iw_3.v28";
    %"iw_3.v29" : P = (RawLoadPointer 0 load_effects) %"chk195";
    %"iw_3.v31" = %"v0" +p #24;
    %"iw_3.v32" : P = (RawLoadPointer 16 load_effects) %"chk195";
    %"iw_3.v33" : L = Ptoi %"iw_3.v29";
    %"iw_3.v34" : L = Ptoi %"iw_3.v32";
    %"iw_3.v35" : L = Sub %"iw_3.v33", %"iw_3.v34";
    %"iw_3.v37" : L = (Ext Sw) %"iw_3.v10";
    %"iw_3.v38" : L = Div %"iw_3.v35", %"iw_3.v37";
    %"iw_3.v39" : L = Shl %"iw_3.v38", #2;
    %"iw_3.v40" = %"iw_3.v26" +p %"iw_3.v39";
    %"chk197" : A = (Renew 0 8 Write 8) %"chk194", %"iw_3.v25";
    store.ptr [%"chk197" + 0] <- %"iw_3.v40"
    => goto "iw_3.L41" };
  ir_blk{ @"iw_3.L13":
    %"iw_3.v46" = %"v0" +p #24;
    %"chk198" : A = (Renew 0 8 Read 8) %"chk160", %"iw_3.v46";
    %"iw_3.v47" : P = (RawLoadPointer 0 load_effects) %"chk198";
    %"chk199" : A = (Check 0 8 Write 8) %"iw_3.v44";
    store.ptr [%"chk199" + 0] <- %"iw_3.v47"
    => goto "iw_3.L48" };
  ir_blk{ @"iw_3.L48":
    %"iw_3.v52" = %"v0" +p #160;
    %"chk200" : A = (Renew 0 8 Read 8) %"chk65", %"iw_3.v52";
    %"iw_3.v53" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v54" = %"iw_3.v53" +p #96;
    %"iw_3.v57" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v58" = %"iw_3.v57" +p #88;
    %"chk202" : A = (Check 0 8 Read 1) %"iw_3.v58";
    %"iw_3.v59" : L = (RawLoad LdL 0) %"chk202";
    %"chk203" : A = (Check 0 8 Write 1) %"iw_3.v54";
    store Wl [%"chk203" + 0] <- %"iw_3.v59";
    %"iw_3.v63" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v64" = %"iw_3.v63" +p #88;
    %"iw_3.v66" = %"v0" +p #24;
    %"chk205" : A = (Renew 0 8 Read 8) %"chk160", %"iw_3.v66";
    %"iw_3.v67" : P = (RawLoadPointer 0 load_effects) %"chk205";
    %"iw_3.v69" = %"v0" +p #8;
    %"chk206" : A = (Renew 0 8 Read 8) %"chk162", %"iw_3.v69";
    %"iw_3.v70" : P = (RawLoadPointer 0 load_effects) %"chk206";
    %"iw_3.v73" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v74" = %"iw_3.v73" +p #16;
    %"chk208" : A = (Check 0 8 Read 8) %"iw_3.v74";
    %"iw_3.v75" : P = (RawLoadPointer 0 load_effects) %"chk208";
    %"iw_3.v78" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v79" = %"iw_3.v78" +p #56;
    %"chk210" : A = (Check 0 8 Read 8) %"iw_3.v79";
    %"iw_3.v80" : P = (RawLoadPointer 0 load_effects) %"chk210";
    %"iw_3.v83" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v84" = %"iw_3.v83" +p #8;
    call %"iw_3.v85" : W = $"__libio_codecvt_in"(P %"iw_3.v7", P %"iw_3.v64", P %"iw_3.v67", P %"iw_3.v70", P %"iw_3.v44", P %"iw_3.v75", P %"iw_3.v80", P %"iw_3.v84");
    %"iw_3.v90" : W = (Cmp Eq W) %"iw_3.v85", #2
    => br %"iw_3.v90" ? "iw_3.L86" : "iw_3.L49" };
  ir_blk{ @"iw_3.L86":
    %"chk212" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"iw_3.v94" : W = (RawLoad (LdNarrow Sw) 0) %"chk212";
    %"iw_3.v95" : W = Or %"iw_3.v94", #32;
    %"chk213" : A = (Renew 0 4 Write 1) %"chk212", %"v0";
    store Ww [%"chk213" + 0] <- %"iw_3.v95"
    => goto "iw_3.join" };
  ir_blk{ @"iw_3.L49":
    %"iw_3.v99" : W = (Cmp Eq W) %"iw_3.v85", #1
    => br %"iw_3.v99" ? poll "iw_3.L48" : "iw_3.L41" };
  ir_blk{ @"iw_3.L41":
    %"iw_3.v103" = %"v0" +p #160;
    %"chk214" : A = (Renew 0 8 Read 8) %"chk65", %"iw_3.v103";
    %"iw_3.v104" : P = (RawLoadPointer 0 load_effects) %"chk214";
    %"iw_3.v107" : P = (RawLoadPointer 0 load_effects) %"chk214";
    %"iw_3.v108" = %"iw_3.v107" +p #8;
    %"chk216" : A = (Check 0 8 Read 8) %"iw_3.v108";
    %"iw_3.v109" : P = (RawLoadPointer 0 load_effects) %"chk216";
    %"chk217" : A = (Check 0 8 Write 8) %"iw_3.v104";
    store.ptr [%"chk217" + 0] <- %"iw_3.v109"
    => goto "iw_3.join" };
  ir_blk{ @"iw_3.join" [%"v503" : W = phi("iw_3.L86" => #4294967295, "iw_3.L41" => #0)]:
    => br %"v503" ? "L322" : "L500" };
  ir_blk{ @"L500":
    %"chk218" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v507" : W = (RawLoad (LdNarrow Sw) 0) %"chk218";
    %"v509" : W = And %"v507", #4294967279;
    %"chk219" : A = (Renew 0 4 Write 1) %"chk218", %"v0";
    store Ww [%"chk219" + 0] <- %"v509";
    %"v826" = %"v0" +p #144;
    %"chk220" : A = (Renew 0 8 Read 1) %"chk152", %"v826";
    %"v827" : L = (RawLoad LdL 0) %"chk220";
    %"v828" : W = (Cmp Sge L) %"v827", #0
    => br %"v828" ? "L822" : "L824" };
  ir_blk{ @"L365":
    %"chk221" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v518" : W = (RawLoad (LdNarrow Sw) 0) %"chk221";
    %"v519" : W = And %"v518", #4
    => br %"v519" ? "L322" : "L516" };
  ir_blk{ @"L516":
    %"v523" = %"v0" +p #64;
    %"chk222" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v523";
    %"v524" : P = (RawLoadPointer 0 load_effects) %"chk222";
    %"v526" = %"v0" +p #56;
    %"v527" : P = (RawLoadPointer (-8) load_effects) %"chk222";
    %"v528" : L = Ptoi %"v524";
    %"v529" : L = Ptoi %"v527";
    %"v530" : L = Sub %"v528", %"v529";
    %"v531" : L = Sub %"v530", #1;
    %"v532" : L = Xor %"v531", #(-1);
    %"v533" : L = And %"pr.1", %"v532";
    %"v536" : L = Sub %"pr.1", %"v533";
    %"v543" : P = (RawLoadPointer 0 load_effects) %"chk222";
    %"v546" : P = (RawLoadPointer (-8) load_effects) %"chk222";
    %"v547" : L = Ptoi %"v543";
    %"v548" : L = Ptoi %"v546";
    %"v549" : L = Sub %"v547", %"v548";
    %"v550" : W = (Cmp Sgt L) %"v536", %"v549"
    => br %"v550" ? "L539" : "L538" };
  ir_blk{ @"L538":
    => goto "L539" };
  ir_blk{ @"L539" [%"pr.8" : L = phi("L538" => %"v533", "L516" => %"pr.1"); %"pr.7" : L = phi("L538" => %"v536", "L516" => #0)]:
    %"v553" = %"v0" +p #216;
    %"chk226" : A = (HalfCheck Upper 0 8 Read 8) %"chk65", %"v553";
    %"v554" : P = (RawLoadPointer 0 load_effects) %"chk226";
    %"iw_4.v4" : L = Ptoi %"v554";
    %"iw_4.v7" : P = Copy $"__io_vtables";
    %"iw_4.v8" : L = Ptoi %"iw_4.v7";
    %"iw_4.v9" : L = Sub %"iw_4.v4", %"iw_4.v8";
    %"iw_4.v15" : W = (Cmp Uge L) %"iw_4.v9", #2352
    => br %"iw_4.v15" ? "iw_4.L10" : "iw_4.join" };
  ir_blk{ @"iw_4.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.join":
    %"v556" = %"v554" +p #128;
    %"chk227" : A = (Check 0 8 Read 8) %"v556";
    %"v557" : P = (RawLoadPointer 0 load_effects) %"chk227";
    %"chk228" : F = CheckFunction %"v557";
    rawcall %"v560" : L = %"chk228"(P %"v0", L %"pr.8", W #0);
    %"v565" : W = (Cmp Slt L) %"v560", #0
    => br %"v565" ? "L561" : "L563" };
  ir_blk{ @"L561":
    => ret #18446744073709551615 };
  ir_blk{ @"L563":
    %"v573" : W = (Cmp Eq L) %"pr.7", #0
    => br %"v573" ? "L571" : "L570" };
  ir_blk{ @"L570":
    %"v575" = %"v0" +p #216;
    %"chk229" : A = (Renew 0 8 Read 8) %"chk226", %"v575";
    %"v576" : P = (RawLoadPointer 0 load_effects) %"chk229";
    %"iw_5.v4" : L = Ptoi %"v576";
    %"iw_5.v7" : P = Copy $"__io_vtables";
    %"iw_5.v8" : L = Ptoi %"iw_5.v7";
    %"iw_5.v9" : L = Sub %"iw_5.v4", %"iw_5.v8";
    %"iw_5.v15" : W = (Cmp Uge L) %"iw_5.v9", #2352
    => br %"iw_5.v15" ? "iw_5.L10" : "iw_5.join" };
  ir_blk{ @"iw_5.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_5.join" };
  ir_blk{ @"iw_5.join":
    %"v578" = %"v576" +p #112;
    %"chk230" : A = (Check 0 8 Read 8) %"v578";
    %"v579" : P = (RawLoadPointer 0 load_effects) %"chk230";
    %"v582" = %"v0" +p #56;
    %"chk231" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v582";
    %"v583" : P = (RawLoadPointer 0 load_effects) %"chk231"
    => br %"v50" ? "L586" : "L585" };
  ir_blk{ @"L585":
    %"v590" = %"v0" +p #64;
    %"chk232" : A = (Renew 0 8 Read 8) %"chk222", %"v590";
    %"v591" : P = (RawLoadPointer 0 load_effects) %"chk232";
    %"v593" = %"v0" +p #56;
    %"v594" : P = (RawLoadPointer 0 load_effects) %"chk231";
    %"v595" : L = Ptoi %"v591";
    %"v596" : L = Ptoi %"v594";
    %"v597" : L = Sub %"v595", %"v596"
    => goto "L586" };
  ir_blk{ @"L586" [%"v598" : L = phi("L585" => %"v597", "iw_5.join" => %"pr.7")]:
    %"chk234" : F = CheckFunction %"v579";
    rawcall %"v599" : L = %"chk234"(P %"v0", P %"v583", L %"v598");
    %"v605" : W = (Cmp Slt L) %"v599", %"pr.7"
    => br %"v605" ? "L600" : "L571" };
  ir_blk{ @"L600":
    %"v612" : W = (Cmp Eq L) %"v599", #18446744073709551615
    => br %"v612" ? "L322" : "L607" };
  ir_blk{ @"L607":
    %"v616" : L = Sub %"pr.7", %"v599"
    => goto "L322" };
  ir_blk{ @"L571" [%"pr.9" : L = phi("L563" => #0, "L586" => %"v599")]:
    code ((app ir[ %"v620" = %"v0" +p #24;
      %"v622" = %"v0" +p #56;
      %"chk235" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v622";
      %"v623" : P = (RawLoadPointer 0 load_effects) %"chk235";
      %"chk236" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v620";
      store.ptr [%"chk236" + 0] <- %"v623";
      %"v625" = %"v0" +p #8;
      %"chk237" : A = (Renew 0 8 Read 8) %"chk235", %"v622";
      %"v628" : P = (RawLoadPointer 0 load_effects) %"chk237";
      %"v630" = %"v628" +p %"pr.7";
      %"chk238" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v625";
      store.ptr [%"chk238" + 0] <- %"v630";
      %"v632" = %"v0" +p #16;
      %"chk239" : A = (Renew 0 8 Read 8) %"chk235", %"v622";
      %"v635" : P = (RawLoadPointer 0 load_effects) %"chk239";
      %"v637" = %"v635" +p %"pr.9";
      %"chk240" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v632";
      store.ptr [%"chk240" + 0] <- %"v637";
      %"v639" = %"v0" +p #32;
      %"v641" = %"v0" +p #40;
      %"chk241" : A = (Renew 0 8 Read 8) %"chk235", %"v622";
      %"v644" : P = (RawLoadPointer 0 load_effects) %"chk241";
      %"chk242" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v641";
      store.ptr [%"chk242" + 0] <- %"v644";
      %"chk243" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v639";
      store.ptr [%"chk243" + 0] <- %"v644";
      %"v646" = %"v0" +p #48;
      %"chk244" : A = (Renew 0 8 Read 8) %"chk235", %"v622";
      %"v649" : P = (RawLoadPointer 0 load_effects) %"chk244";
      %"chk245" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v646";
      store.ptr [%"chk245" + 0] <- %"v649";
      %"v651" = %"v0" +p #160;
      %"chk246" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v652" : P = (RawLoadPointer 0 load_effects) %"chk246";
      %"v653" = %"v652" +p #16;
      %"v656" : P = (RawLoadPointer 0 load_effects) %"chk246";
      %"v657" = %"v656" +p #48;
      %"chk248" : A = (Check 0 8 Read 8) %"v657";
      %"v658" : P = (RawLoadPointer 0 load_effects) %"chk248";
      %"chk249" : A = (Check 0 8 Write 8) %"v653";
      store.ptr [%"chk249" + 0] <- %"v658";
      %"chk250" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v661" : P = (RawLoadPointer 0 load_effects) %"chk250";
      %"v664" : P = (RawLoadPointer 0 load_effects) %"chk250";
      %"v665" = %"v664" +p #48] ir[ %"chk252" : A = (Check 0 8 Read 8) %"v665";
      %"v666" : P = (RawLoadPointer 0 load_effects) %"chk252";
      %"chk253" : A = (Check 0 8 Write 8) %"v661";
      store.ptr [%"chk253" + 0] <- %"v666";
      %"chk254" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v669" : P = (RawLoadPointer 0 load_effects) %"chk254";
      %"v670" = %"v669" +p #8;
      %"v673" : P = (RawLoadPointer 0 load_effects) %"chk254";
      %"v674" = %"v673" +p #48;
      %"chk256" : A = (Check 0 8 Read 8) %"v674";
      %"v675" : P = (RawLoadPointer 0 load_effects) %"chk256";
      %"chk257" : A = (Check 0 8 Write 8) %"v670";
      store.ptr [%"chk257" + 0] <- %"v675";
      %"chk258" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v678" : P = (RawLoadPointer 0 load_effects) %"chk258";
      %"v679" = %"v678" +p #24;
      %"v682" : P = (RawLoadPointer 0 load_effects) %"chk258";
      %"v683" = %"v682" +p #32;
      %"v686" : P = (RawLoadPointer 0 load_effects) %"chk258";
      %"v687" = %"v686" +p #48;
      %"chk261" : A = (Check 0 8 Read 8) %"v687";
      %"v688" : P = (RawLoadPointer 0 load_effects) %"chk261";
      %"chk262" : A = (Check 0 8 Write 8) %"v683";
      store.ptr [%"chk262" + 0] <- %"v688";
      %"chk263" : A = (Check 0 8 Write 8) %"v679";
      store.ptr [%"chk263" + 0] <- %"v688";
      %"chk264" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v691" : P = (RawLoadPointer 0 load_effects) %"chk264";
      %"v692" = %"v691" +p #40;
      %"v695" : P = (RawLoadPointer 0 load_effects) %"chk264";
      %"v696" = %"v695" +p #48;
      %"chk266" : A = (Check 0 8 Read 8) %"v696";
      %"v697" : P = (RawLoadPointer 0 load_effects) %"chk266";
      %"chk267" : A = (Check 0 8 Write 8) %"v692";
      store.ptr [%"chk267" + 0] <- %"v697";
      %"iw_6.v44" : P = (Alloc 8) #8;
      %"iw_6.v6" = %"v0" +p #152;
      %"chk268" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"iw_6.v6";
      %"iw_6.v7" : P = (RawLoadPointer 0 load_effects) %"chk268";
      call %"iw_6.v10" : W = $"__libio_codecvt_encoding"(P %"iw_6.v7");
      %"iw_6.v46" = %"v0" +p #24;
      %"chk269" : A = (Renew 0 8 Read 8) %"chk236", %"iw_6.v46";
      %"iw_6.v47" : P = (RawLoadPointer 0 load_effects) %"chk269";
      %"chk270" : A = (Check 0 8 Write 8) %"iw_6.v44";
      store.ptr [%"chk270" + 0] <- %"iw_6.v47"]))
    => goto "iw_6.L48" };
  ir_blk{ @"iw_6.L48":
    %"iw_6.v52" = %"v0" +p #160;
    %"chk271" : A = (Renew 0 8 Read 8) %"chk65", %"iw_6.v52";
    %"iw_6.v53" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v54" = %"iw_6.v53" +p #96;
    %"iw_6.v57" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v58" = %"iw_6.v57" +p #88;
    %"chk273" : A = (Check 0 8 Read 1) %"iw_6.v58";
    %"iw_6.v59" : L = (RawLoad LdL 0) %"chk273";
    %"chk274" : A = (Check 0 8 Write 1) %"iw_6.v54";
    store Wl [%"chk274" + 0] <- %"iw_6.v59";
    %"iw_6.v63" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v64" = %"iw_6.v63" +p #88;
    %"iw_6.v66" = %"v0" +p #24;
    %"chk276" : A = (Renew 0 8 Read 8) %"chk236", %"iw_6.v66";
    %"iw_6.v67" : P = (RawLoadPointer 0 load_effects) %"chk276";
    %"iw_6.v69" = %"v0" +p #8;
    %"chk277" : A = (Renew 0 8 Read 8) %"chk238", %"iw_6.v69";
    %"iw_6.v70" : P = (RawLoadPointer 0 load_effects) %"chk277";
    %"iw_6.v73" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v74" = %"iw_6.v73" +p #16;
    %"chk279" : A = (Check 0 8 Read 8) %"iw_6.v74";
    %"iw_6.v75" : P = (RawLoadPointer 0 load_effects) %"chk279";
    %"iw_6.v78" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v79" = %"iw_6.v78" +p #56;
    %"chk281" : A = (Check 0 8 Read 8) %"iw_6.v79";
    %"iw_6.v80" : P = (RawLoadPointer 0 load_effects) %"chk281";
    %"iw_6.v83" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v84" = %"iw_6.v83" +p #8;
    call %"iw_6.v85" : W = $"__libio_codecvt_in"(P %"iw_6.v7", P %"iw_6.v64", P %"iw_6.v67", P %"iw_6.v70", P %"iw_6.v44", P %"iw_6.v75", P %"iw_6.v80", P %"iw_6.v84");
    %"iw_6.v90" : W = (Cmp Eq W) %"iw_6.v85", #2
    => br %"iw_6.v90" ? "iw_6.L86" : "iw_6.L49" };
  ir_blk{ @"iw_6.L86":
    %"chk283" : A = (Renew 0 4 Read 1) %"chk221", %"v0";
    %"iw_6.v94" : W = (RawLoad (LdNarrow Sw) 0) %"chk283";
    %"iw_6.v95" : W = Or %"iw_6.v94", #32;
    %"chk284" : A = (Renew 0 4 Write 1) %"chk221", %"v0";
    store Ww [%"chk284" + 0] <- %"iw_6.v95"
    => goto "iw_6.join" };
  ir_blk{ @"iw_6.L49":
    %"iw_6.v99" : W = (Cmp Eq W) %"iw_6.v85", #1
    => br %"iw_6.v99" ? poll "iw_6.L48" : "iw_6.L41" };
  ir_blk{ @"iw_6.L41":
    %"iw_6.v103" = %"v0" +p #160;
    %"chk285" : A = (Renew 0 8 Read 8) %"chk65", %"iw_6.v103";
    %"iw_6.v104" : P = (RawLoadPointer 0 load_effects) %"chk285";
    %"iw_6.v107" : P = (RawLoadPointer 0 load_effects) %"chk285";
    %"iw_6.v108" = %"iw_6.v107" +p #8;
    %"chk287" : A = (Check 0 8 Read 8) %"iw_6.v108";
    %"iw_6.v109" : P = (RawLoadPointer 0 load_effects) %"chk287";
    %"chk288" : A = (Check 0 8 Write 8) %"iw_6.v104";
    store.ptr [%"chk288" + 0] <- %"iw_6.v109"
    => goto "iw_6.join" };
  ir_blk{ @"iw_6.join" [%"v703" : W = phi("iw_6.L86" => #4294967295, "iw_6.L41" => #0)]:
    => br %"v703" ? "L322" : "L700" };
  ir_blk{ @"L700":
    %"v706" = %"v0" +p #144;
    %"v709" : L = Add %"v560", %"pr.9";
    %"chk289" : A = (Renew 0 8 Write 1) %"chk152", %"v706";
    store Wl [%"chk289" + 0] <- %"v709";
    %"chk290" : A = (Renew 0 4 Read 1) %"chk221", %"v0";
    %"v712" : W = (RawLoad (LdNarrow Sw) 0) %"chk290";
    %"v714" : W = And %"v712", #4294967279;
    store Ww [%"chk290" + 0] <- %"v714"
    => ret %"pr.1" };
  ir_blk{ @"L322" [%"pr.6" : W = phi("L204" => %"v4", "L345" => %"v4", "iw_3.join" => %"pr.5", "L365" => %"pr.5", "L607" => #1, "L600" => #1, "iw_6.join" => %"pr.5"); %"pr.4" : L = phi("L204" => %"pr.2", "L345" => %"v2", "iw_3.join" => %"pr.1", "L365" => %"pr.1", "L607" => %"v616", "L600" => %"pr.7", "iw_6.join" => %"pr.1")]:
    call void $"__GI__IO_unsave_markers"(P %"v0");
    %"v720" = %"v0" +p #216;
    %"chk292" : A = (HalfCheck Upper 0 8 Read 8) %"chk65", %"v720";
    %"v721" : P = (RawLoadPointer 0 load_effects) %"chk292";
    %"iw_7.v4" : L = Ptoi %"v721";
    %"iw_7.v7" : P = Copy $"__io_vtables";
    %"iw_7.v8" : L = Ptoi %"iw_7.v7";
    %"iw_7.v9" : L = Sub %"iw_7.v4", %"iw_7.v8";
    %"iw_7.v15" : W = (Cmp Uge L) %"iw_7.v9", #2352
    => br %"iw_7.v15" ? "iw_7.L10" : "iw_7.join" };
  ir_blk{ @"iw_7.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.join":
    %"v723" = %"v721" +p #128;
    %"chk293" : A = (Check 0 8 Read 8) %"v723";
    %"v724" : P = (RawLoadPointer 0 load_effects) %"chk293";
    %"chk294" : F = CheckFunction %"v724";
    rawcall %"v728" : L = %"chk294"(P %"v0", L %"pr.4", W %"pr.6");
    %"v735" : W = (Cmp Ne L) %"v728", #18446744073709551615
    => br %"v735" ? "L729" : "L731" };
  ir_blk{ @"L729":
    code ((app ir[ %"chk295" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
      %"v738" : W = (RawLoad (LdNarrow Sw) 0) %"chk295";
      %"v740" : W = And %"v738", #4294967279;
      %"chk296" : A = (Renew 0 4 Write 1) %"chk295", %"v0";
      store Ww [%"chk296" + 0] <- %"v740";
      %"v744" = %"v0" +p #144;
      %"chk297" : A = (HalfCheck Lower 0 8 Write 1) %"chk65", %"v744";
      store Wl [%"chk297" + 0] <- %"v728";
      %"v747" = %"v0" +p #24;
      %"v749" = %"v0" +p #56;
      %"chk298" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v749";
      %"v750" : P = (RawLoadPointer 0 load_effects) %"chk298";
      %"chk299" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v747";
      store.ptr [%"chk299" + 0] <- %"v750";
      %"v752" = %"v0" +p #8;
      %"chk300" : A = (Renew 0 8 Read 8) %"chk298", %"v749";
      %"v755" : P = (RawLoadPointer 0 load_effects) %"chk300";
      %"chk301" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v752";
      store.ptr [%"chk301" + 0] <- %"v755";
      %"v757" = %"v0" +p #16;
      %"chk302" : A = (Renew 0 8 Read 8) %"chk298", %"v749";
      %"v760" : P = (RawLoadPointer 0 load_effects) %"chk302";
      %"chk303" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v757";
      store.ptr [%"chk303" + 0] <- %"v760";
      %"v762" = %"v0" +p #32;
      %"v764" = %"v0" +p #40;
      %"chk304" : A = (Renew 0 8 Read 8) %"chk298", %"v749";
      %"v767" : P = (RawLoadPointer 0 load_effects) %"chk304";
      %"chk305" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v764";
      store.ptr [%"chk305" + 0] <- %"v767";
      %"chk306" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v762";
      store.ptr [%"chk306" + 0] <- %"v767";
      %"v769" = %"v0" +p #48;
      %"chk307" : A = (Renew 0 8 Read 8) %"chk298", %"v749";
      %"v772" : P = (RawLoadPointer 0 load_effects) %"chk307";
      %"chk308" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v769";
      store.ptr [%"chk308" + 0] <- %"v772";
      %"v774" = %"v0" +p #160;
      %"chk309" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v775" : P = (RawLoadPointer 0 load_effects) %"chk309";
      %"v776" = %"v775" +p #16;
      %"v779" : P = (RawLoadPointer 0 load_effects) %"chk309";
      %"v780" = %"v779" +p #48] ir[ %"chk311" : A = (Check 0 8 Read 8) %"v780";
      %"v781" : P = (RawLoadPointer 0 load_effects) %"chk311";
      %"chk312" : A = (Check 0 8 Write 8) %"v776";
      store.ptr [%"chk312" + 0] <- %"v781";
      %"chk313" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v784" : P = (RawLoadPointer 0 load_effects) %"chk313";
      %"v787" : P = (RawLoadPointer 0 load_effects) %"chk313";
      %"v788" = %"v787" +p #48;
      %"chk315" : A = (Check 0 8 Read 8) %"v788";
      %"v789" : P = (RawLoadPointer 0 load_effects) %"chk315";
      %"chk316" : A = (Check 0 8 Write 8) %"v784";
      store.ptr [%"chk316" + 0] <- %"v789";
      %"chk317" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v792" : P = (RawLoadPointer 0 load_effects) %"chk317";
      %"v793" = %"v792" +p #8;
      %"v796" : P = (RawLoadPointer 0 load_effects) %"chk317";
      %"v797" = %"v796" +p #48;
      %"chk319" : A = (Check 0 8 Read 8) %"v797";
      %"v798" : P = (RawLoadPointer 0 load_effects) %"chk319";
      %"chk320" : A = (Check 0 8 Write 8) %"v793";
      store.ptr [%"chk320" + 0] <- %"v798";
      %"chk321" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v801" : P = (RawLoadPointer 0 load_effects) %"chk321";
      %"v802" = %"v801" +p #24;
      %"v805" : P = (RawLoadPointer 0 load_effects) %"chk321";
      %"v806" = %"v805" +p #32;
      %"v809" : P = (RawLoadPointer 0 load_effects) %"chk321";
      %"v810" = %"v809" +p #48;
      %"chk324" : A = (Check 0 8 Read 8) %"v810";
      %"v811" : P = (RawLoadPointer 0 load_effects) %"chk324";
      %"chk325" : A = (Check 0 8 Write 8) %"v806";
      store.ptr [%"chk325" + 0] <- %"v811";
      %"chk326" : A = (Check 0 8 Write 8) %"v802";
      store.ptr [%"chk326" + 0] <- %"v811";
      %"chk327" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v814" : P = (RawLoadPointer 0 load_effects) %"chk327";
      %"v815" = %"v814" +p #40;
      %"v818" : P = (RawLoadPointer 0 load_effects) %"chk327";
      %"v819" = %"v818" +p #48;
      %"chk329" : A = (Check 0 8 Read 8) %"v819";
      %"v820" : P = (RawLoadPointer 0 load_effects) %"chk329";
      %"chk330" : A = (Check 0 8 Write 8) %"v815";
      store.ptr [%"chk330" + 0] <- %"v820"]))
    => goto "L731" };
  ir_blk{ @"L731":
    => ret %"v728" };
  ir_blk{ @"L822":
    %"v830" = %"v0" +p #216;
    %"chk331" : A = (HalfCheck Upper 0 8 Read 8) %"chk65", %"v830";
    %"v831" : P = (RawLoadPointer 0 load_effects) %"chk331";
    %"iw_8.v4" : L = Ptoi %"v831";
    %"iw_8.v7" : P = Copy $"__io_vtables";
    %"iw_8.v8" : L = Ptoi %"iw_8.v7";
    %"iw_8.v9" : L = Sub %"iw_8.v4", %"iw_8.v8";
    %"iw_8.v15" : W = (Cmp Uge L) %"iw_8.v9", #2352
    => br %"iw_8.v15" ? "iw_8.L10" : "iw_8.join" };
  ir_blk{ @"iw_8.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_8.join" };
  ir_blk{ @"iw_8.join":
    %"v833" = %"v831" +p #128;
    %"chk332" : A = (Check 0 8 Read 8) %"v833";
    %"v834" : P = (RawLoadPointer 0 load_effects) %"chk332";
    %"v837" = %"v0" +p #144;
    %"chk333" : A = (Renew 0 8 Read 1) %"chk152", %"v837";
    %"v838" : L = (RawLoad LdL 0) %"chk333";
    %"chk334" : F = CheckFunction %"v834";
    rawcall %"v839" : L = %"chk334"(P %"v0", L %"v838", W #0)
    => goto "L824" };
  ir_blk{ @"L824":
    => ret %"pr.1" }])) }.

Definition fn___GI__IO_wfile_sync : func :=
  ir_fn{ "export" "__GI__IO_wfile_sync"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v9" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v15" = %"v14" +p #24;
    %"chk3" : A = (Check 0 8 Read 8) %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v17" : L = Ptoi %"v11";
    %"v18" : L = Ptoi %"v16";
    %"v19" : W = (Cmp Ugt L) %"v17", %"v18"
    => br %"v19" ? "L4" : "L6";
  @"L4":
    %"v27" = %"v0" +p #192;
    %"chk4" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v27";
    %"v28" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v29" : W = (Cmp Sle W) %"v28", #0
    => br %"v29" ? "L23" : "L24";
  @"L23":
    %"v32" = %"v0" +p #32;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v35" = %"v0" +p #40;
    %"v36" : P = (RawLoadPointer 8 load_effects) %"chk5";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v40" : L = Ptoi %"v36";
    %"v41" : L = Ptoi %"v39";
    %"v42" : L = Sub %"v40", %"v41";
    call %"v43" : W = $"__GI__IO_do_write"(P %"v0", P %"v33", L %"v42")
    => goto "L25";
  @"L24":
    %"v46" = %"v0" +p #160;
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v48" = %"v47" +p #24;
    %"chk9" : A = (Check 0 8 Read 8) %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v53" = %"v52" +p #32;
    %"chk11" : A = (Check 0 8 Read 8) %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v58" = %"v57" +p #24;
    %"chk13" : A = (Check 0 8 Read 8) %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v60" : L = Ptoi %"v54";
    %"v61" : L = Ptoi %"v59";
    %"v62" : L = Sub %"v60", %"v61";
    %"v63" : L = Div %"v62", #4;
    call %"v64" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v49", L %"v63")
    => goto "L25";
  @"L25" [%"v65" : W = phi("L23" => %"v43", "L24" => %"v64")]:
    => br %"v65" ? "L20" : "L6";
  @"L20":
    => ret #4294967295;
  @"L6":
    %"v68" = %"v0" +p #160;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk0", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Read 8) %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v74" = %"v73" +p #8;
    %"chk17" : A = (Check 0 8 Read 8) %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v76" : L = Ptoi %"v70";
    %"v77" : L = Ptoi %"v75";
    %"v78" : L = Sub %"v76", %"v77";
    %"v79" : L = Div %"v78", #4;
    %"v84" : W = (Cmp Ne L) %"v79", #0
    => br %"v84" ? "L80" : "L82";
  @"L80":
    %"v87" = %"v0" +p #152;
    %"chk18" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call %"v92" : W = $"__libio_codecvt_encoding"(P %"v88");
    %"v97" : W = (Cmp Sgt W) %"v92", #0
    => br %"v97" ? "L93" : "L94";
  @"L93":
    %"v100" : L = (Ext Sw) %"v92";
    %"v101" : L = Mul %"v79", %"v100"
    => goto "L95";
  @"L94":
    %"v105" = %"v0" +p #160;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk0", %"v105";
    %"v106" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Check 0 8 Read 8) %"v106";
    %"v107" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v111" = %"v110" +p #16;
    %"chk22" : A = (Check 0 8 Read 8) %"v111";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v113" : L = Ptoi %"v107";
    %"v114" : L = Ptoi %"v112";
    %"v115" : L = Sub %"v113", %"v114";
    %"v116" : L = Div %"v115", #4;
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v120" = %"v119" +p #88;
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v124" = %"v123" +p #96;
    %"chk25" : A = (Check 0 8 Read 1) %"v124";
    %"v125" : L = (RawLoad LdL 0) %"chk25";
    %"chk26" : A = (Check 0 8 Write 1) %"v120";
    store Wl [%"chk26" + 0] <- %"v125";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v130" = %"v129" +p #88;
    %"v132" = %"v0" +p #24;
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v132";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v135" = %"v0" +p #16;
    %"chk29" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v135";
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk29";
    call %"v138" : W = $"__libio_codecvt_length"(P %"v88", P %"v130", P %"v133", P %"v136", L %"v116");
    %"v140" = %"v0" +p #8;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk28", %"v132";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v145" : L = (Ext Sw) %"v138";
    %"v146" = %"v143" +p %"v145";
    %"chk31" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v140";
    store.ptr [%"chk31" + 0] <- %"v146";
    %"chk32" : A = (Renew 0 8 Read 8) %"chk29", %"v135";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Renew 0 8 Read 8) %"chk28", %"v132";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v153" : L = Ptoi %"v149";
    %"v154" : L = Ptoi %"v152";
    %"v155" : L = Sub %"v153", %"v154";
    %"v158" : L = Sub %"v155", %"v145";
    %"v159" : L = Neg %"v158"
    => goto "L95";
  @"L95" [%"pr.1" : L = phi("L93" => %"v101", "L94" => %"v159")]:
    %"v161" = %"v0" +p #216;
    %"chk34" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v161";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_1.v4" : L = Ptoi %"v162";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v164" = %"v162" +p #128;
    %"chk35" : A = (Check 0 8 Read 8) %"v164";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : F = CheckFunction %"v165";
    rawcall %"v168" : L = %"chk36"(P %"v0", L %"pr.1", W #1);
    %"v175" : W = (Cmp Ne L) %"v168", #18446744073709551615
    => br %"v175" ? "L169" : "L170";
  @"L169":
    %"v177" = %"v0" +p #160;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk0", %"v177";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v179" = %"v178" +p #8;
    %"v182" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"chk39" : A = (Check 0 8 Read 8) %"v182";
    %"v183" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"chk40" : A = (Check 0 8 Write 8) %"v179";
    store.ptr [%"chk40" + 0] <- %"v183";
    %"v185" = %"v0" +p #16;
    %"v187" = %"v0" +p #8;
    %"chk41" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v187";
    %"v188" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"chk42" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v185";
    store.ptr [%"chk42" + 0] <- %"v188"
    => goto "L82";
  @"L170":
    %"v192" : P = Copy $"__libc_errno";
    %"chk43" : A = (Check 0 4 Read 1) %"v192";
    %"v193" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v194" : W = (Cmp Eq W) %"v193", #29
    => br %"v194" ? "L82" : "L190";
  @"L190":
    => goto "L82";
  @"L82" [%"pr.4" : W = phi("L169" => #0, "L190" => #4294967295, "L170" => #0, "L6" => #0)]:
    %"v199" : W = (Cmp Ne W) %"pr.4", #4294967295
    => br %"v199" ? "L195" : "L197";
  @"L195":
    %"v201" = %"v0" +p #144;
    %"chk44" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"v201";
    store Wl [%"chk44" + 0] <- #18446744073709551615
    => goto "L197";
  @"L197":
    => ret %"pr.4"
} }.

Definition fn___GI__IO_wfile_underflow : func :=
  ir_fn{ "export" "__GI__IO_wfile_underflow"(P %"v0") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v61" : P = (Alloc 8) #8;
    %"v437" : P = (Alloc 8) #8;
    %"v438" : P = (Alloc 4) #16;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v10" : W = And %"v9", #16
    => br %"v10" ? "L5" : "L7" };
  ir_blk{ @"L5":
    => ret #4294967295 };
  ir_blk{ @"L7":
    %"v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v17" : W = And %"v16", #4;
    %"v18" : L = (Ext Sw) %"v17";
    %"v19" : W = (Cmp Ne L) %"v18", #0
    => br %"v19" ? "L12" : "L14" };
  ir_blk{ @"L12":
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v22" : W = Or %"v21", #32;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk3" + 0] <- %"v22";
    %"v23" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v23";
    store Ww [%"chk4" + 0] <- #9
    => ret #4294967295 };
  ir_blk{ @"L14":
    %"v29" = %"v0" +p #160;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v35" = %"v34" +p #8;
    %"chk8" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v37" : L = Ptoi %"v31";
    %"v38" : L = Ptoi %"v36";
    %"v39" : W = (Cmp Ult L) %"v37", %"v38"
    => br %"v39" ? "L25" : "L27" };
  ir_blk{ @"L25":
    %"v41" = %"v0" +p #160;
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk10" : A = (Check 0 8 Read 8) %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 4 Read 1) %"v43";
    %"v44" : W = (RawLoad (LdNarrow Sw) 0) %"chk11"
    => ret %"v44" };
  ir_blk{ @"L27":
    %"v47" = %"v0" +p #152;
    %"v48" : P = (RawLoadPointer (-8) load_effects) %"chk5";
    %"v53" = %"v0" +p #8;
    %"v54" : P = (RawLoadPointer (-152) load_effects) %"chk5";
    %"v56" = %"v0" +p #16;
    %"v57" : P = (RawLoadPointer (-144) load_effects) %"chk5";
    %"v58" : L = Ptoi %"v54";
    %"v59" : L = Ptoi %"v57";
    %"v60" : W = (Cmp Ult L) %"v58", %"v59"
    => br %"v60" ? "L49" : "L50" };
  ir_blk{ @"L49":
    %"v63" = %"v0" +p #8;
    %"v64" : P = (RawLoadPointer (-152) load_effects) %"chk5";
    %"chk16" : A = (Check 0 8 Write 8) %"v61";
    store.ptr [%"chk16" + 0] <- %"v64";
    %"v66" = %"v0" +p #160;
    %"chk17" : A = (Renew 0 8 Read 8) %"chk5", %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v68" = %"v67" +p #96;
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v72" = %"v71" +p #88;
    %"chk19" : A = (Check 0 8 Read 1) %"v72";
    %"v73" : L = (RawLoad LdL 0) %"chk19";
    %"chk20" : A = (Check 0 8 Write 1) %"v68";
    store Wl [%"chk20" + 0] <- %"v73";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v77" = %"v76" +p #16;
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v84" = %"v83" +p #48;
    %"chk24" : A = (Check 0 8 Read 8) %"v84";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"chk25" : A = (Check 0 8 Write 8) %"v80";
    store.ptr [%"chk25" + 0] <- %"v85";
    %"chk26" : A = (Check 0 8 Write 8) %"v77";
    store.ptr [%"chk26" + 0] <- %"v85";
    %"chk27" : A = (Renew 0 8 Read 8) %"chk5", %"v66";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v90" = %"v89" +p #88;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v63";
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v95" = %"v0" +p #16;
    %"v96" : P = (RawLoadPointer 8 load_effects) %"chk28";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk31" : A = (Check 0 8 Read 8) %"v99";
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v104" = %"v103" +p #56;
    %"chk33" : A = (Check 0 8 Read 8) %"v104";
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v109" = %"v108" +p #8;
    call %"v110" : W = $"__libio_codecvt_in"(P %"v48", P %"v90", P %"v93", P %"v96", P %"v61", P %"v100", P %"v105", P %"v109");
    %"v112" = %"v0" +p #24;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk28", %"v63";
    %"v115" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v112";
    store.ptr [%"chk36" + 0] <- %"v115";
    %"chk37" : A = (Renew 0 8 Read 8) %"chk16", %"v61";
    %"v118" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"chk38" : A = (Renew 0 8 Write 8) %"chk28", %"v63";
    store.ptr [%"chk38" + 0] <- %"v118";
    %"chk39" : A = (Renew 0 8 Read 8) %"chk5", %"v66";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"chk40" : A = (Check 0 8 Read 8) %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v129" = %"v128" +p #8;
    %"chk42" : A = (Check 0 8 Read 8) %"v129";
    %"v130" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v131" : L = Ptoi %"v125";
    %"v132" : L = Ptoi %"v130";
    %"v133" : W = (Cmp Ult L) %"v131", %"v132"
    => br %"v133" ? "L119" : "L121" };
  ir_blk{ @"L119":
    %"v135" = %"v0" +p #160;
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"chk44" : A = (Check 0 8 Read 8) %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Check 0 4 Read 1) %"v137";
    %"v138" : W = (RawLoad (LdNarrow Sw) 0) %"chk45"
    => ret %"v138" };
  ir_blk{ @"L121":
    %"v144" : W = (Cmp Eq W) %"v110", #2
    => br %"v144" ? "L140" : "L142" };
  ir_blk{ @"L140":
    %"v145" : P = Copy $"__libc_errno";
    %"chk46" : A = (Check 0 4 Write 1) %"v145";
    store Ww [%"chk46" + 0] <- #84;
    %"chk47" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v147" : W = (RawLoad (LdNarrow Sw) 0) %"chk47";
    %"v148" : W = Or %"v147", #32;
    %"chk48" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk48" + 0] <- %"v148"
    => ret #4294967295 };
  ir_blk{ @"L142":
    %"v151" = %"v0" +p #56;
    %"chk49" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v151";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v154" = %"v0" +p #8;
    %"chk50" : A = (Renew 0 8 Read 8) %"chk28", %"v154";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v157" = %"v0" +p #16;
    %"v158" : P = (RawLoadPointer 8 load_effects) %"chk50";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v162" : L = Ptoi %"v158";
    %"v163" : L = Ptoi %"v161";
    %"v164" : L = Sub %"v162", %"v163";
    call %"v165" : P = $"__GI_memmove"(P %"v152", P %"v155", L %"v164");
    %"chk53" : A = (Renew 0 8 Read 8) %"chk49", %"v151";
    %"v170" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"chk54" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v157";
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"chk55" : A = (Renew 0 8 Read 8) %"chk28", %"v154";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v177" : L = Ptoi %"v173";
    %"v178" : L = Ptoi %"v176";
    %"v179" : L = Sub %"v177", %"v178";
    %"v180" = %"v170" +p %"v179";
    %"chk56" : A = (Renew 0 8 Write 8) %"chk54", %"v157";
    store.ptr [%"chk56" + 0] <- %"v180";
    %"v182" = %"v0" +p #24;
    %"chk57" : A = (Renew 0 8 Read 8) %"chk49", %"v151";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"chk58" : A = (Renew 0 8 Write 8) %"chk28", %"v154";
    store.ptr [%"chk58" + 0] <- %"v187";
    %"chk59" : A = (Renew 0 8 Write 8) %"chk36", %"v182";
    store.ptr [%"chk59" + 0] <- %"v187"
    => goto "L51" };
  ir_blk{ @"L50":
    %"v189" = %"v0" +p #24;
    %"v191" = %"v0" +p #8;
    %"v193" = %"v0" +p #16;
    %"v195" = %"v0" +p #56;
    %"v196" : P = (RawLoadPointer (-104) load_effects) %"chk5";
    %"chk61" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v193";
    store.ptr [%"chk61" + 0] <- %"v196";
    %"chk62" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v191";
    store.ptr [%"chk62" + 0] <- %"v196";
    %"chk63" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v189";
    store.ptr [%"chk63" + 0] <- %"v196"
    => goto "L51" };
  ir_blk{ @"L51":
    %"v201" = %"v0" +p #56;
    %"chk64" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v201";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v203" : L = Ptoi %"v202";
    %"v204" : L = Ptoi #0;
    %"v205" : W = (Cmp Eq L) %"v203", %"v204"
    => br %"v205" ? "L197" : "L199" };
  ir_blk{ @"L197":
    %"v210" = %"v0" +p #72;
    %"chk65" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v210";
    %"v211" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v212" : L = Ptoi %"v211";
    %"v214" : W = (Cmp Ne L) %"v212", %"v204"
    => br %"v214" ? "L206" : "L208" };
  ir_blk{ @"L206":
    %"v217" = %"v0" +p #72;
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v218";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join" };
  ir_blk{ @"iw_1.L4":
    call void $"free"(P %"v218")
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join":
    %"chk67" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v220" : W = (RawLoad (LdNarrow Sw) 0) %"chk67";
    %"v222" : W = And %"v220", #4294967039;
    %"chk68" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk68" + 0] <- %"v222"
    => goto "L208" };
  ir_blk{ @"L208":
    call void $"__GI__IO_doallocbuf"(P %"v0");
    %"v225" = %"v0" +p #24;
    %"v227" = %"v0" +p #8;
    %"v229" = %"v0" +p #16;
    %"v231" = %"v0" +p #56;
    %"chk69" : A = (Renew 0 8 Read 8) %"chk64", %"v231";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"chk70" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v229";
    store.ptr [%"chk70" + 0] <- %"v232";
    %"chk71" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v227";
    store.ptr [%"chk71" + 0] <- %"v232";
    %"chk72" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v225";
    store.ptr [%"chk72" + 0] <- %"v232"
    => goto "L199" };
  ir_blk{ @"L199":
    %"v234" = %"v0" +p #32;
    %"v236" = %"v0" +p #40;
    %"v238" = %"v0" +p #48;
    %"v240" = %"v0" +p #56;
    %"chk73" : A = (Renew 0 8 Read 8) %"chk64", %"v240";
    %"v241" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"chk74" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v238";
    store.ptr [%"chk74" + 0] <- %"v241";
    %"chk75" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v236";
    store.ptr [%"chk75" + 0] <- %"v241";
    %"chk76" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v234";
    store.ptr [%"chk76" + 0] <- %"v241";
    %"v246" = %"v0" +p #160;
    %"chk77" : A = (Renew 0 8 Read 8) %"chk5", %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"v248" = %"v247" +p #48;
    %"chk78" : A = (Check 0 8 Read 8) %"v248";
    %"v249" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v250" : L = Ptoi %"v249";
    %"v252" : W = (Cmp Eq L) %"v250", %"v204"
    => br %"v252" ? "L242" : "L244" };
  ir_blk{ @"L242":
    %"v257" = %"v0" +p #160;
    %"v258" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"v259" = %"v258" +p #64;
    %"chk80" : A = (Check 0 8 Read 8) %"v259";
    %"v260" : P = (RawLoadPointer 0 load_effects) %"chk80";
    %"v261" : L = Ptoi %"v260";
    %"v263" : W = (Cmp Ne L) %"v261", %"v204"
    => br %"v263" ? "L253" : "L255" };
  ir_blk{ @"L253":
    %"v265" = %"v0" +p #160;
    %"v266" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"v267" = %"v266" +p #64;
    %"chk82" : A = (Check 0 8 Read 8) %"v267";
    %"v268" : P = (RawLoadPointer 0 load_effects) %"chk82";
    call void $"free"(P %"v268");
    %"chk83" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v270" : W = (RawLoad (LdNarrow Sw) 0) %"chk83";
    %"v272" : W = And %"v270", #4294967039;
    %"chk84" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk84" + 0] <- %"v272"
    => goto "L255" };
  ir_blk{ @"L255":
    call void $"__GI__IO_wdoallocbuf"(P %"v0")
    => goto "L244" };
  ir_blk{ @"L244":
    %"chk85" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v278" : W = (RawLoad (LdNarrow Sw) 0) %"chk85";
    %"v280" : W = And %"v278", #514
    => br %"v280" ? "L281" : "L276" };
  ir_blk{ @"L281":
    %"v285" : P = Copy $"stdout";
    %"chk86" : A = (Check 0 8 Read 8) %"v285";
    %"v286" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"chk87" : A = (Check 0 4 Read 1) %"v286";
    %"v291" : W = (RawLoad (LdNarrow Sw) 0) %"chk87";
    %"v292" : W = And %"v291", #32768;
    %"v293" : W = (Cmp Eq W) %"v292", #0
    => br %"v293" ? "L294" : "L289" };
  ir_blk{ @"L294":
    call %"v298" : P = $"zthread_self_cookie"();
    %"v302" : P = Copy $"__libc_single_threaded_internal";
    %"chk88" : A = (Check 0 1 Read 1) %"v302";
    %"v303" : W = (RawLoad (LdNarrow Sb) 0) %"chk88";
    %"v304" : W = (Cmp Ne W) %"v303", #0
    => br %"v304" ? "L305" : "L306" };
  ir_blk{ @"L305":
    %"v308" = %"v286" +p #136;
    %"chk89" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"v308";
    %"v309" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"v310" = %"v309" +p #8;
    %"chk90" : A = (Check 0 8 Read 8) %"v310";
    %"v311" : P = (RawLoadPointer 0 load_effects) %"chk90";
    %"v312" : L = Ptoi %"v311";
    %"v314" : W = (Cmp Eq L) %"v312", %"v204"
    => goto "L306" };
  ir_blk{ @"L306" [%"v316" : W = phi("L294" => #0, "L305" => %"v314")]:
    => br %"v316" ? "L299" : "L300" };
  ir_blk{ @"L299":
    %"v318" = %"v286" +p #136;
    %"chk91" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"v318";
    %"v319" : P = (RawLoadPointer 0 load_effects) %"chk91";
    %"chk92" : A = (Check 0 4 Write 1) %"v319";
    store Ww [%"chk92" + 0] <- #1;
    %"v322" : P = (RawLoadPointer 0 load_effects) %"chk91";
    %"v323" = %"v322" +p #8;
    %"chk94" : A = (Check 0 8 Write 8) %"v323";
    store.ptr [%"chk94" + 0] <- %"v298"
    => goto "L289" };
  ir_blk{ @"L300":
    %"v329" = %"v286" +p #136;
    %"chk95" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"v329";
    %"v330" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v331" = %"v330" +p #8;
    %"chk96" : A = (Check 0 8 Read 8) %"v331";
    %"v332" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"v334" : L = Ptoi %"v332";
    %"v335" : L = Ptoi %"v298";
    %"v336" : W = (Cmp Ne L) %"v334", %"v335"
    => br %"v336" ? "L325" : "L326" };
  ir_blk{ @"L325":
    %"v339" = %"v286" +p #136;
    %"v340" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"chk98" : A = (Check 0 4 Write 4) %"v340";
    %"v347" : W = (RawCas (CasNarrow Sw) 0) %"chk98", #0, #1;
    %"v348" : W = (Cmp Eq W) %"v347", #0
    => br %"v348" ? "L350" : "L349" };
  ir_blk{ @"L349":
    => goto "L350" };
  ir_blk{ @"L350":
    %"v351" : W = (Cmp Ne W) %"v347", #0
    => br %"v351" ? "L354" : "L343" };
  ir_blk{ @"L354":
    call void $"__GI___lll_lock_wait_private"(P %"v340")
    => goto "L343" };
  ir_blk{ @"L343":
    %"v365" = %"v286" +p #136;
    %"chk99" : A = (Renew 0 8 Read 8) %"chk95", %"v365";
    %"v366" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"v367" = %"v366" +p #8;
    %"chk100" : A = (Check 0 8 Write 8) %"v367";
    store.ptr [%"chk100" + 0] <- %"v298"
    => goto "L289" };
  ir_blk{ @"L326":
    %"v370" = %"v286" +p #136;
    %"v371" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v372" = %"v371" +p #4;
    %"chk102" : A = (Check 0 4 Read 1) %"v372";
    %"v373" : W = (RawLoad (LdNarrow Sw) 0) %"chk102";
    %"v374" : W = Add %"v373", #1;
    %"chk103" : A = (Renew 0 4 Write 1) %"chk102", %"v372";
    store Ww [%"chk103" + 0] <- %"v374"
    => goto "L289" };
  ir_blk{ @"L289":
    %"v378" : P = Copy $"stdout";
    %"chk104" : A = (Check 0 8 Read 8) %"v378";
    %"v379" : P = (RawLoadPointer 0 load_effects) %"chk104";
    %"chk105" : A = (Check 0 4 Read 1) %"v379";
    %"v380" : W = (RawLoad (LdNarrow Sw) 0) %"chk105";
    %"v383" : W = And %"v380", #648;
    %"v385" : W = (Cmp Eq W) %"v383", #640
    => br %"v385" ? "L375" : "iw_3.start" };
  ir_blk{ @"L375":
    %"v386" : P = Copy $"stdout";
    %"chk106" : A = (Check 0 8 Read 8) %"v386";
    %"v387" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"v388" = %"v387" +p #216;
    %"chk107" : A = (Check 0 8 Read 8) %"v388";
    %"v389" : P = (RawLoadPointer 0 load_effects) %"chk107";
    %"iw_2.v4" : L = Ptoi %"v389";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join" };
  ir_blk{ @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join":
    %"v391" = %"v389" +p #24;
    %"chk108" : A = (Check 0 8 Read 8) %"v391";
    %"v392" : P = (RawLoadPointer 0 load_effects) %"chk108";
    %"v393" : P = Copy $"stdout";
    %"chk109" : A = (Check 0 8 Read 8) %"v393";
    %"v394" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"chk110" : F = CheckFunction %"v392";
    rawcall %"v396" : W = %"chk110"(P %"v394", W #4294967295)
    => goto "iw_3.start" };
  ir_blk{ @"iw_3.start":
    %"chk111" : A = (Renew 0 4 Read 1) %"chk87", %"v286";
    %"iw_3.v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk111";
    %"iw_3.v10" : W = And %"iw_3.v9", #32768;
    %"iw_3.v11" : W = (Cmp Eq W) %"iw_3.v10", #0
    => br %"iw_3.v11" ? "iw_3.L5" : "L276" };
  ir_blk{ @"iw_3.L5":
    %"iw_3.v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk111";
    %"iw_3.v17" : W = And %"iw_3.v16", #32768;
    %"iw_3.v18" : W = (Cmp Eq W) %"iw_3.v17", #0
    => br %"iw_3.v18" ? "iw_3.L19" : "L276" };
  ir_blk{ @"iw_3.L19":
    %"iw_3.v25" : P = Copy $"__libc_single_threaded_internal";
    %"chk113" : A = (Check 0 1 Read 1) %"iw_3.v25";
    %"iw_3.v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk113";
    %"iw_3.v27" : W = (Cmp Ne W) %"iw_3.v26", #0
    => br %"iw_3.v27" ? "iw_3.L28" : "iw_3.L29" };
  ir_blk{ @"iw_3.L28":
    %"iw_3.v31" = %"v286" +p #136;
    %"chk114" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"iw_3.v31";
    %"iw_3.v32" : P = (RawLoadPointer 0 load_effects) %"chk114";
    %"iw_3.v33" = %"iw_3.v32" +p #4;
    %"chk115" : A = (Check 0 4 Read 1) %"iw_3.v33";
    %"iw_3.v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk115";
    %"iw_3.v35" : W = (Cmp Eq W) %"iw_3.v34", #0
    => goto "iw_3.L29" };
  ir_blk{ @"iw_3.L29" [%"iw_3.v37" : W = phi("iw_3.L19" => #0, "iw_3.L28" => %"iw_3.v35")]:
    => br %"iw_3.v37" ? "iw_3.L22" : "iw_3.L23" }] [ir_blk{ @"iw_3.L22":
    %"iw_3.v39" = %"v286" +p #136;
    %"chk116" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"iw_3.v39";
    %"iw_3.v40" : P = (RawLoadPointer 0 load_effects) %"chk116";
    %"iw_3.v41" = %"iw_3.v40" +p #8;
    %"chk117" : A = (Check 0 8 Write 8) %"iw_3.v41";
    store.ptr [%"chk117" + 0] <- #0;
    %"chk118" : A = (Renew 0 8 Read 8) %"chk116", %"iw_3.v39";
    %"iw_3.v44" : P = (RawLoadPointer 0 load_effects) %"chk118";
    %"chk119" : A = (Check 0 4 Write 1) %"iw_3.v44";
    store Ww [%"chk119" + 0] <- #0
    => goto "L276" };
  ir_blk{ @"iw_3.L23":
    %"iw_3.v49" = %"v286" +p #136;
    %"chk120" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"iw_3.v49";
    %"iw_3.v50" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_3.v51" = %"iw_3.v50" +p #4;
    %"chk121" : A = (Check 0 4 Read 1) %"iw_3.v51";
    %"iw_3.v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk121";
    %"iw_3.v53" : W = (Cmp Eq W) %"iw_3.v52", #0
    => br %"iw_3.v53" ? "iw_3.L45" : "iw_3.L46" };
  ir_blk{ @"iw_3.L45":
    %"iw_3.v55" = %"v286" +p #136;
    %"iw_3.v56" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_3.v57" = %"iw_3.v56" +p #8;
    %"chk123" : A = (Check 0 8 Write 8) %"iw_3.v57";
    store.ptr [%"chk123" + 0] <- #0;
    %"chk124" : A = (Renew 0 8 Read 8) %"chk120", %"iw_3.v55";
    %"iw_3.v61" : P = (RawLoadPointer 0 load_effects) %"chk124";
    %"chk125" : A = (Check 0 4 Read 1) %"iw_3.v61";
    %"iw_3.v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk125"
    => goto "iw_3.L66" };
  ir_blk{ @"iw_3.L66" [%"iw_3.v68" : W = phi("iw_3.L45" => %"iw_3.v65", "iw_3.L66" => %"iw_3.v69")]:
    %"chk126" : A = (HalfCheck Lower 0 4 Write 4) %"chk125", %"iw_3.v61";
    %"iw_3.v69" : W = (RawCas (CasNarrow Sw) 0) %"chk126", %"iw_3.v68", #0;
    %"iw_3.v70" : W = (Cmp Eq W) %"iw_3.v69", %"iw_3.v68"
    => br %"iw_3.v70" ? "iw_3.L67" : poll "iw_3.L66" };
  ir_blk{ @"iw_3.L67":
    %"iw_3.v75" : W = (Cmp Sgt W) %"iw_3.v68", #1
    => br %"iw_3.v75" ? "iw_3.L78" : "L276" };
  ir_blk{ @"iw_3.L78":
    call void $"__GI___lll_lock_wake_private"(P %"iw_3.v61")
    => goto "L276" };
  ir_blk{ @"iw_3.L46":
    %"iw_3.v90" = %"v286" +p #136;
    %"iw_3.v91" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_3.v92" = %"iw_3.v91" +p #4;
    %"chk128" : A = (Check 0 4 Read 1) %"iw_3.v92";
    %"iw_3.v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk128";
    %"iw_3.v94" : W = Sub %"iw_3.v93", #1;
    %"chk129" : A = (Renew 0 4 Write 1) %"chk128", %"iw_3.v92";
    store Ww [%"chk129" + 0] <- %"iw_3.v94"
    => goto "L276" };
  ir_blk{ @"L276":
    call %"v398" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v400" = %"v0" +p #160;
    %"chk130" : A = (Renew 0 8 Read 8) %"chk5", %"v400";
    %"v401" : P = (RawLoadPointer 0 load_effects) %"chk130";
    %"v402" = %"v401" +p #16;
    %"v405" : P = (RawLoadPointer 0 load_effects) %"chk130";
    %"v408" : P = (RawLoadPointer 0 load_effects) %"chk130";
    %"v409" = %"v408" +p #48;
    %"chk133" : A = (Check 0 8 Read 8) %"v409";
    %"v410" : P = (RawLoadPointer 0 load_effects) %"chk133";
    %"chk134" : A = (Check 0 8 Write 8) %"v405";
    store.ptr [%"chk134" + 0] <- %"v410";
    %"chk135" : A = (Check 0 8 Write 8) %"v402";
    store.ptr [%"chk135" + 0] <- %"v410";
    %"chk136" : A = (Renew 0 8 Read 8) %"chk5", %"v400";
    %"v413" : P = (RawLoadPointer 0 load_effects) %"chk136";
    %"v414" = %"v413" +p #8;
    %"v417" : P = (RawLoadPointer 0 load_effects) %"chk136";
    %"v418" = %"v417" +p #48;
    %"chk138" : A = (Check 0 8 Read 8) %"v418";
    %"v419" : P = (RawLoadPointer 0 load_effects) %"chk138";
    %"chk139" : A = (Check 0 8 Write 8) %"v414";
    store.ptr [%"chk139" + 0] <- %"v419";
    %"chk140" : A = (Renew 0 8 Read 8) %"chk5", %"v400";
    %"v422" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"v423" = %"v422" +p #24;
    %"v426" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"v427" = %"v426" +p #32;
    %"v430" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"v431" = %"v430" +p #40;
    %"v434" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"v435" = %"v434" +p #48;
    %"chk144" : A = (Check 0 8 Read 8) %"v435";
    %"v436" : P = (RawLoadPointer 0 load_effects) %"chk144";
    %"chk145" : A = (Check 0 8 Write 8) %"v431";
    store.ptr [%"chk145" + 0] <- %"v436";
    %"chk146" : A = (Check 0 8 Write 8) %"v427";
    store.ptr [%"chk146" + 0] <- %"v436";
    %"chk147" : A = (Check 0 8 Write 8) %"v423";
    store.ptr [%"chk147" + 0] <- %"v436"
    => goto "L440" };
  ir_blk{ @"L440" [%"pr.3" : L = phi("L276" => #0, "L662" => %"pr.5", "L665" => %"pr.4")]:
    %"v442" = %"v0" +p #216;
    %"chk148" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v442";
    %"v443" : P = (RawLoadPointer 0 load_effects) %"chk148";
    %"iw_4.v4" : L = Ptoi %"v443";
    %"iw_4.v7" : P = Copy $"__io_vtables";
    %"iw_4.v8" : L = Ptoi %"iw_4.v7";
    %"iw_4.v9" : L = Sub %"iw_4.v4", %"iw_4.v8";
    %"iw_4.v15" : W = (Cmp Uge L) %"iw_4.v9", #2352
    => br %"iw_4.v15" ? "iw_4.L10" : "iw_4.join" };
  ir_blk{ @"iw_4.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.join":
    %"v445" = %"v443" +p #112;
    %"chk149" : A = (Check 0 8 Read 8) %"v445";
    %"v446" : P = (RawLoadPointer 0 load_effects) %"chk149";
    %"v449" = %"v0" +p #16;
    %"chk150" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v449";
    %"v450" : P = (RawLoadPointer 0 load_effects) %"chk150";
    %"v452" = %"v0" +p #64;
    %"chk151" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v452";
    %"v453" : P = (RawLoadPointer 0 load_effects) %"chk151";
    %"v456" : P = (RawLoadPointer 0 load_effects) %"chk150";
    %"v457" : L = Ptoi %"v453";
    %"v458" : L = Ptoi %"v456";
    %"v459" : L = Sub %"v457", %"v458";
    %"chk153" : F = CheckFunction %"v446";
    rawcall %"v460" : L = %"chk153"(P %"v0", P %"v450", L %"v459");
    %"v465" : W = (Cmp Sle L) %"v460", #0
    => br %"v465" ? "L461" : "L463" };
  ir_blk{ @"L461":
    %"v470" : W = (Cmp Eq L) %"v460", #0
    => br %"v470" ? "L471" : "L472" };
  ir_blk{ @"L471":
    %"v474" : W = (Cmp Eq L) %"pr.3", #0
    => goto "L472" };
  ir_blk{ @"L472" [%"v476" : W = phi("L461" => #0, "L471" => %"v474")]:
    => br %"v476" ? "L466" : "L467" };
  ir_blk{ @"L466":
    %"chk154" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v478" : W = (RawLoad (LdNarrow Sw) 0) %"chk154";
    %"v479" : W = Or %"v478", #16;
    %"chk155" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk155" + 0] <- %"v479";
    %"v481" = %"v0" +p #144;
    %"chk156" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v481";
    store Wl [%"chk156" + 0] <- #18446744073709551615
    => goto "L463" };
  ir_blk{ @"L467":
    %"chk157" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v485" : W = (RawLoad (LdNarrow Sw) 0) %"chk157";
    %"v486" : W = Or %"v485", #32;
    %"chk158" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk158" + 0] <- %"v486"
    => goto "L463" };
  ir_blk{ @"L463" [%"pr.1" : L = phi("L466" => %"v460", "L467" => #0, "iw_4.join" => %"v460")]:
    %"v488" = %"v0" +p #16;
    %"chk159" : A = (Renew 0 8 Read 8) %"chk150", %"v488";
    %"v489" : P = (RawLoadPointer 0 load_effects) %"chk159";
    %"v491" = %"v489" +p %"pr.1";
    %"chk160" : A = (Renew 0 8 Write 8) %"chk150", %"v488";
    store.ptr [%"chk160" + 0] <- %"v491";
    %"v496" : W = (Cmp Eq L) %"pr.1", #0
    => br %"v496" ? "L492" : "L494" };
  ir_blk{ @"L492":
    %"v501" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v501" ? "L497" : "L499" };
  ir_blk{ @"L497":
    %"v502" : P = Copy $"__libc_errno";
    %"chk161" : A = (Check 0 4 Write 1) %"v502";
    store Ww [%"chk161" + 0] <- #84
    => goto "L499" };
  ir_blk{ @"L499":
    => ret #4294967295 };
  ir_blk{ @"L494":
    %"v508" = %"v0" +p #144;
    %"chk162" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v508";
    %"v509" : L = (RawLoad LdL 0) %"chk162";
    %"v512" : W = (Cmp Ne L) %"v509", #18446744073709551615
    => br %"v512" ? "L504" : "L506" };
  ir_blk{ @"L504":
    %"v514" = %"v0" +p #144;
    %"v515" : L = (RawLoad LdL 0) %"chk162";
    %"v517" : L = Add %"v515", %"pr.1";
    %"chk164" : A = (Renew 0 8 Write 1) %"chk162", %"v514";
    store Wl [%"chk164" + 0] <- %"v517"
    => goto "L506" };
  ir_blk{ @"L506":
    %"v519" = %"v0" +p #160;
    %"chk165" : A = (Renew 0 8 Read 8) %"chk5", %"v519";
    %"v520" : P = (RawLoadPointer 0 load_effects) %"chk165";
    %"v521" = %"v520" +p #96;
    %"v524" : P = (RawLoadPointer 0 load_effects) %"chk165";
    %"v525" = %"v524" +p #88;
    %"chk167" : A = (Check 0 8 Read 1) %"v525";
    %"v526" : L = (RawLoad LdL 0) %"chk167";
    %"chk168" : A = (Check 0 8 Write 1) %"v521";
    store Wl [%"chk168" + 0] <- %"v526";
    %"v528" = %"v0" +p #24;
    %"v530" = %"v0" +p #8;
    %"chk169" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v530";
    %"v531" : P = (RawLoadPointer 0 load_effects) %"chk169";
    %"chk170" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v528";
    store.ptr [%"chk170" + 0] <- %"v531";
    %"chk171" : A = (Renew 0 8 Read 8) %"chk169", %"v530";
    %"v535" : P = (RawLoadPointer 0 load_effects) %"chk171";
    %"v538" = %"v0" +p #16;
    %"chk172" : A = (Renew 0 8 Read 8) %"chk150", %"v538";
    %"v539" : P = (RawLoadPointer 0 load_effects) %"chk172";
    %"v546" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v546" ? "L542" : "L544" };
  ir_blk{ @"L542":
    %"v553" : L = Sub #16, %"pr.3";
    %"v555" : W = (Cmp Ult L) %"v553", %"pr.1"
    => br %"v555" ? "L551" : "L550" };
  ir_blk{ @"L550":
    => goto "L551" };
  ir_blk{ @"L551" [%"v559" : L = phi("L550" => %"pr.1", "L542" => %"v553")]:
    %"v561" = %"v438" +p %"pr.3";
    call %"v564" : P = $"__GI_mempcpy"(P %"v561", P %"v535", L %"v559");
    %"v567" : L = Add %"pr.3", %"v559"
    => goto "L544" };
  ir_blk{ @"L544" [%"pr.9" : L = phi("L551" => %"v559", "L506" => %"pr.1"); %"pr.8" : P = phi("L551" => %"v564", "L506" => %"v539"); %"pr.7" : P = phi("L551" => %"v438", "L506" => %"v535"); %"pr.4" : L = phi("L551" => %"v567", "L506" => %"pr.3")]:
    %"v570" = %"v0" +p #160;
    %"chk173" : A = (Renew 0 8 Read 8) %"chk5", %"v570";
    %"v571" : P = (RawLoadPointer 0 load_effects) %"chk173";
    %"v572" = %"v571" +p #88;
    %"v577" : P = (RawLoadPointer 0 load_effects) %"chk173";
    %"v578" = %"v577" +p #8;
    %"chk175" : A = (Check 0 8 Read 8) %"v578";
    %"v579" : P = (RawLoadPointer 0 load_effects) %"chk175";
    %"v582" : P = (RawLoadPointer 0 load_effects) %"chk173";
    %"v583" = %"v582" +p #56;
    %"chk177" : A = (Check 0 8 Read 8) %"v583";
    %"v584" : P = (RawLoadPointer 0 load_effects) %"chk177";
    %"v587" : P = (RawLoadPointer 0 load_effects) %"chk173";
    %"v588" = %"v587" +p #8;
    call %"v589" : W = $"__libio_codecvt_in"(P %"v48", P %"v572", P %"pr.7", P %"pr.8", P %"v437", P %"v579", P %"v584", P %"v588");
    %"v594" : W = (Cmp Ne L) %"pr.4", #0
    => br %"v594" ? "L590" : "L591" };
  ir_blk{ @"L590":
    %"v598" = %"v0" +p #8;
    %"chk179" : A = (Renew 0 8 Read 8) %"chk169", %"v598";
    %"v599" : P = (RawLoadPointer 0 load_effects) %"chk179";
    %"chk180" : A = (Check 0 8 Read 8) %"v437";
    %"v603" : P = (RawLoadPointer 0 load_effects) %"chk180";
    %"v606" : L = Sub %"pr.4", %"pr.9";
    %"v607" = %"v438" +p %"v606";
    %"v608" : L = Ptoi %"v603";
    %"v609" : L = Ptoi %"v607";
    %"v610" : L = Sub %"v608", %"v609";
    %"v611" : W = (Cmp Slt L) %"v610", #0
    => br %"v611" ? "L602" : "L601" };
  ir_blk{ @"L601":
    %"v612" : P = (RawLoadPointer 0 load_effects) %"chk180";
    %"v617" : L = Ptoi %"v612";
    %"v619" : L = Sub %"v617", %"v609"
    => goto "L602" };
  ir_blk{ @"L602" [%"v620" : L = phi("L601" => %"v619", "L590" => #0)]:
    %"v621" = %"v599" +p %"v620";
    %"chk182" : A = (Renew 0 8 Write 8) %"chk169", %"v598";
    store.ptr [%"chk182" + 0] <- %"v621"
    => goto "L592" };
  ir_blk{ @"L591":
    %"v623" = %"v0" +p #8;
    %"chk183" : A = (Check 0 8 Read 8) %"v437";
    %"v624" : P = (RawLoadPointer 0 load_effects) %"chk183";
    %"chk184" : A = (Renew 0 8 Write 8) %"chk169", %"v623";
    store.ptr [%"chk184" + 0] <- %"v624"
    => goto "L592" };
  ir_blk{ @"L592":
    %"v629" = %"v0" +p #160;
    %"chk185" : A = (Renew 0 8 Read 8) %"chk5", %"v629";
    %"v630" : P = (RawLoadPointer 0 load_effects) %"chk185";
    %"v631" = %"v630" +p #8;
    %"chk186" : A = (Check 0 8 Read 8) %"v631";
    %"v632" : P = (RawLoadPointer 0 load_effects) %"chk186";
    %"v635" : P = (RawLoadPointer 0 load_effects) %"chk185";
    %"v636" = %"v635" +p #48;
    %"chk188" : A = (Check 0 8 Read 8) %"v636";
    %"v637" : P = (RawLoadPointer 0 load_effects) %"chk188";
    %"v638" : L = Ptoi %"v632";
    %"v639" : L = Ptoi %"v637";
    %"v640" : W = (Cmp Eq L) %"v638", %"v639"
    => br %"v640" ? "L625" : "L627" };
  ir_blk{ @"L625":
    %"v645" : W = (Cmp Eq W) %"v589", #2
    => br %"v645" ? "L646" : "L643" };
  ir_blk{ @"L646":
    %"v647" : P = Copy $"__libc_errno";
    %"chk189" : A = (Check 0 4 Write 1) %"v647";
    store Ww [%"chk189" + 0] <- #84;
    %"chk190" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v649" : W = (RawLoad (LdNarrow Sw) 0) %"chk190";
    %"v650" : W = Or %"v649", #32;
    %"chk191" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk191" + 0] <- %"v650"
    => ret #4294967295 };
  ir_blk{ @"L643":
    %"v656" : W = (Cmp Eq W) %"v589", #1
    => br %"v656" ? "L654" : "L653" };
  ir_blk{ @"L653":
    %"v657" : P = Copy $"glibc_wfileops#str.254";
    %"v658" : P = Copy $"glibc_wfileops#str.255";
    %"v659" : P = Copy $"glibc_wfileops#str.256";
    call void $"__libc_assert_fail"(P %"v657", P %"v658", W #289, P %"v659")
    => goto "L654" };
  ir_blk{ @"L654":
    %"v664" : W = (Cmp Eq L) %"pr.4", #0
    => br %"v664" ? "L660" : "L661" };
  ir_blk{ @"L660":
    %"v669" = %"v0" +p #24;
    %"chk192" : A = (Renew 0 8 Read 8) %"chk170", %"v669";
    %"v670" : P = (RawLoadPointer 0 load_effects) %"chk192";
    %"v672" = %"v0" +p #8;
    %"chk193" : A = (Renew 0 8 Read 8) %"chk169", %"v672";
    %"v673" : P = (RawLoadPointer 0 load_effects) %"chk193";
    %"v674" : L = Ptoi %"v670";
    %"v675" : L = Ptoi %"v673";
    %"v676" : W = (Cmp Ult L) %"v674", %"v675"
    => br %"v676" ? "L665" : "L667" };
  ir_blk{ @"L665":
    %"v679" = %"v0" +p #16;
    %"v680" : P = (RawLoadPointer 8 load_effects) %"chk193";
    %"v682" = %"v0" +p #8;
    %"v683" : P = (RawLoadPointer 0 load_effects) %"chk193";
    %"v684" : L = Ptoi %"v680";
    %"v685" : L = Ptoi %"v683";
    %"v686" : L = Sub %"v684", %"v685";
    %"v688" = %"v0" +p #24;
    %"v689" : P = (RawLoadPointer 0 load_effects) %"chk192";
    %"v692" : P = (RawLoadPointer 0 load_effects) %"chk193";
    call %"v694" : P = $"__GI_memmove"(P %"v689", P %"v692", L %"v686");
    %"chk198" : A = (Renew 0 8 Read 8) %"chk170", %"v688";
    %"v699" : P = (RawLoadPointer 0 load_effects) %"chk198";
    %"chk199" : A = (Renew 0 8 Write 8) %"chk169", %"v682";
    store.ptr [%"chk199" + 0] <- %"v699";
    %"chk200" : A = (Renew 0 8 Read 8) %"chk150", %"v679";
    %"v702" : P = (RawLoadPointer 0 load_effects) %"chk200";
    (Flight (a "v704") Sub [(FAddress (t "v702")); (FValue (t "v686"))] (LowerOf (t "v702")));
    %"chk201" : A = (Renew 0 8 Write 8) %"chk150", %"v679";
    store.ptr [%"chk201" + 0] <- %"v704"
    => goto poll "L440" };
  ir_blk{ @"L667":
    %"v707" = %"v0" +p #16;
    %"v708" : P = (RawLoadPointer 8 load_effects) %"chk193";
    %"v710" = %"v0" +p #8;
    %"v711" : P = (RawLoadPointer 0 load_effects) %"chk193";
    %"v712" : L = Ptoi %"v708";
    %"v713" : L = Ptoi %"v711";
    %"v714" : L = Sub %"v712", %"v713";
    %"v719" : W = (Cmp Uge L) %"v714", #16
    => br %"v719" ? poll "L646" : "L717" };
  ir_blk{ @"L717":
    %"v722" = %"v0" +p #8;
    %"v723" : P = (RawLoadPointer 0 load_effects) %"chk193";
    call %"v725" : P = $"__GI_memcpy"(P %"v438", P %"v723", L %"v714")
    => goto "L662" };
  ir_blk{ @"L661":
    %"chk205" : A = (Check 0 8 Read 8) %"v437";
    %"v727" : P = (RawLoadPointer 0 load_effects) %"chk205";
    %"v728" : L = Ptoi %"v727";
    %"v729" : L = Ptoi %"v438";
    %"v730" : L = Sub %"v728", %"v729";
    %"v735" : W = (Cmp Ugt L) %"v730", #0
    => br %"v735" ? "L731" : "L733" };
  ir_blk{ @"L731":
    %"v736" : P = (RawLoadPointer 0 load_effects) %"chk205";
    %"v739" : L = Sub %"pr.4", %"v730";
    call %"v740" : P = $"__GI_memmove"(P %"v438", P %"v736", L %"v739")
    => goto "L733" };
  ir_blk{ @"L733" [%"pr.6" : L = phi("L731" => %"v739", "L661" => %"pr.4")]:
    %"v748" : W = (Cmp Eq L) %"pr.6", #16
    => br %"v748" ? poll "L646" : "L662" };
  ir_blk{ @"L662" [%"pr.5" : L = phi("L717" => %"v714", "L733" => %"pr.6")]:
    %"v751" = %"v0" +p #8;
    %"v753" = %"v0" +p #16;
    %"v755" = %"v0" +p #24;
    %"chk207" : A = (Renew 0 8 Read 8) %"chk170", %"v755";
    %"v756" : P = (RawLoadPointer 0 load_effects) %"chk207";
    %"chk208" : A = (Renew 0 8 Write 8) %"chk150", %"v753";
    store.ptr [%"chk208" + 0] <- %"v756";
    %"chk209" : A = (Renew 0 8 Write 8) %"chk169", %"v751";
    store.ptr [%"chk209" + 0] <- %"v756"
    => goto poll "L440" };
  ir_blk{ @"L627":
    %"v759" = %"v0" +p #160;
    %"v760" : P = (RawLoadPointer 0 load_effects) %"chk185";
    %"chk211" : A = (Check 0 8 Read 8) %"v760";
    %"v761" : P = (RawLoadPointer 0 load_effects) %"chk211";
    %"chk212" : A = (Check 0 4 Read 1) %"v761";
    %"v762" : W = (RawLoad (LdNarrow Sw) 0) %"chk212"
    => ret %"v762" }])) }.

Definition fn___GI__IO_wfile_xsputn : func :=
  ir_fn{ "export" "__GI__IO_wfile_xsputn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v16" : W = (Cmp Ule L) %"v4", #0
    => br %"v16" ? "L12" : "L14";
  @"L12":
    => ret #0;
  @"L14":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v23" : W = And %"v22", #512
    => br %"v23" ? "L24" : "L25";
  @"L24":
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v28" : W = And %"v27", #2048;
    %"v29" : W = (Cmp Ne W) %"v28", #0
    => goto "L25";
  @"L25" [%"v30" : W = phi("L14" => #0, "L24" => %"v29")]:
    => br %"v30" ? "L18" : "L19";
  @"L18":
    %"v32" = %"v0" +p #160;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v34" = %"v33" +p #56;
    %"chk3" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v39" = %"v38" +p #32;
    %"chk5" : A = (Check 0 8 Read 8) %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v41" : L = Ptoi %"v35";
    %"v42" : L = Ptoi %"v40";
    %"v43" : L = Sub %"v41", %"v42";
    %"v44" : L = Div %"v43", #4;
    %"v50" : W = (Cmp Uge L) %"v44", %"v4"
    => br %"v50" ? "L45" : "L20";
  @"L45":
    %"v54" : L = Shl %"v4", #2;
    %"v55" = %"v2" +p %"v54"
    => goto "L56";
  @"L56" [%"pr.14" : P = phi("L45" => %"v55", "L57" => %"v69")]:
    %"v62" : L = Ptoi %"pr.14";
    %"v63" : L = Ptoi %"v2";
    %"v64" : W = (Cmp Ugt L) %"v62", %"v63"
    => br %"v64" ? "L57" : "L20";
  @"L57":
    (Flight (a "v69") Sub [(FAddress (t "pr.14")); (FValue (Const 4))] (LowerOf (t "pr.14")));
    %"chk6" : A = (Check 0 4 Read 1) %"v69";
    %"v70" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v71" : W = (Cmp Eq W) %"v70", #10
    => br %"v71" ? "L65" : poll "L56";
  @"L65":
    %"v74" : L = Ptoi %"v69";
    %"v76" : L = Sub %"v74", %"v63";
    %"v77" : L = Div %"v76", #4;
    %"v78" : L = Add %"v77", #1
    => goto "L20";
  @"L19":
    %"v84" = %"v0" +p #160;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v84";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v86" = %"v85" +p #40;
    %"chk8" : A = (Check 0 8 Read 8) %"v86";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v91" = %"v90" +p #32;
    %"chk10" : A = (Check 0 8 Read 8) %"v91";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v93" : L = Ptoi %"v87";
    %"v94" : L = Ptoi %"v92";
    %"v95" : W = (Cmp Ugt L) %"v93", %"v94"
    => br %"v95" ? "L80" : "L20";
  @"L80":
    %"v97" = %"v0" +p #160;
    %"v98" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v99" = %"v98" +p #40;
    %"chk12" : A = (Check 0 8 Read 8) %"v99";
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v104" = %"v103" +p #32;
    %"chk14" : A = (Check 0 8 Read 8) %"v104";
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v106" : L = Ptoi %"v100";
    %"v107" : L = Ptoi %"v105";
    %"v108" : L = Sub %"v106", %"v107";
    %"v109" : L = Div %"v108", #4
    => goto "L20";
  @"L20" [%"pr.10" : L = phi("L56" => %"v44", "L65" => %"v78", "L18" => %"v44", "L80" => %"v109", "L19" => #0); %"pr.6" : W = phi("L56" => #0, "L65" => #1, "L18" => #0, "L80" => #0, "L19" => #0)]:
    %"v114" : W = (Cmp Ugt L) %"pr.10", #0
    => br %"v114" ? "L110" : "L112";
  @"L110":
    %"v120" : W = (Cmp Ugt L) %"pr.10", %"v4"
    => br %"v120" ? "L117" : "L116";
  @"L116":
    => goto "L117";
  @"L117" [%"pr.9" : L = phi("L116" => %"pr.10", "L110" => %"v4")]:
    %"v126" : W = (Cmp Ugt L) %"pr.9", #20
    => br %"v126" ? "L122" : "L123";
  @"L122":
    %"v128" = %"v0" +p #160;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v128";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v130" = %"v129" +p #32;
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v134" = %"v133" +p #32;
    %"chk17" : A = (Check 0 8 Read 8) %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk17";
    call %"v138" : P = $"__wmempcpy"(P %"v135", P %"v2", L %"pr.9");
    %"chk18" : A = (Check 0 8 Write 8) %"v130";
    store.ptr [%"chk18" + 0] <- %"v138";
    %"v141" : L = Shl %"pr.9", #2;
    %"v142" = %"v2" +p %"v141"
    => goto "L124";
  @"L123":
    %"v145" = %"v0" +p #160;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v145";
    %"v146" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v147" = %"v146" +p #32;
    %"chk20" : A = (Check 0 8 Read 8) %"v147";
    %"v148" : P = (RawLoadPointer 0 load_effects) %"chk20"
    => goto "L151";
  @"L151" [%"pr.16" : W = phi("L123" => %"pr.9", "L152" => %"v155"); %"pr.15" : P = phi("L123" => %"v148", "L152" => %"v158"); %"pr.3" : P = phi("L123" => %"v2", "L152" => %"v160")]:
    %"v155" : W = Sub %"pr.16", #1;
    %"v156" : W = (Cmp Sge W) %"v155", #0
    => br %"v156" ? "L152" : "L153";
  @"L152":
    %"v158" = %"pr.15" +p #4;
    %"v160" = %"pr.3" +p #4;
    %"chk21" : A = (Check 0 4 Read 1) %"pr.3";
    %"v161" : W = (RawLoad (LdNarrow Sw) 0) %"chk21";
    %"chk22" : A = (Check 0 4 Write 1) %"pr.15";
    store Ww [%"chk22" + 0] <- %"v161"
    => goto poll "L151";
  @"L153":
    %"v163" = %"v0" +p #160;
    %"chk23" : A = (Renew 0 8 Read 8) %"chk19", %"v163";
    %"v164" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v165" = %"v164" +p #32;
    %"chk24" : A = (Check 0 8 Write 8) %"v165";
    store.ptr [%"chk24" + 0] <- %"pr.15"
    => goto "L124";
  @"L124" [%"pr.2" : P = phi("L122" => %"v142", "L153" => %"pr.3")]:
    %"v169" : L = Sub %"v4", %"pr.9"
    => goto "L112";
  @"L112" [%"pr.4" : L = phi("L124" => %"v169", "L20" => %"v4"); %"pr.1" : P = phi("L124" => %"pr.2", "L20" => %"v2")]:
    %"v174" : W = (Cmp Ugt L) %"pr.4", #0
    => br %"v174" ? "L170" : "L172";
  @"L170":
    call %"v179" : L = $"__GI__IO_wdefault_xsputn"(P %"v0", P %"pr.1", L %"pr.4");
    %"v180" : L = Sub %"pr.4", %"v179"
    => goto "L172";
  @"L172" [%"pr.5" : L = phi("L170" => %"v180", "L112" => %"pr.4")]:
    => br %"pr.6" ? "L185" : "L186";
  @"L185":
    %"v188" = %"v0" +p #160;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v188";
    %"v189" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v190" = %"v189" +p #32;
    %"chk26" : A = (Check 0 8 Read 8) %"v190";
    %"v191" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v194" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v195" = %"v194" +p #24;
    %"chk28" : A = (Check 0 8 Read 8) %"v195";
    %"v196" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v197" : L = Ptoi %"v191";
    %"v198" : L = Ptoi %"v196";
    %"v199" : W = (Cmp Ne L) %"v197", %"v198"
    => goto "L186";
  @"L186" [%"v201" : W = phi("L172" => #0, "L185" => %"v199")]:
    => br %"v201" ? "L181" : "L183";
  @"L181":
    %"v204" = %"v0" +p #160;
    %"chk29" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v204";
    %"v205" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v206" = %"v205" +p #24;
    %"chk30" : A = (Check 0 8 Read 8) %"v206";
    %"v207" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v210" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v211" = %"v210" +p #32;
    %"chk32" : A = (Check 0 8 Read 8) %"v211";
    %"v212" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v216" = %"v215" +p #24;
    %"chk34" : A = (Check 0 8 Read 8) %"v216";
    %"v217" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v218" : L = Ptoi %"v212";
    %"v219" : L = Ptoi %"v217";
    %"v220" : L = Sub %"v218", %"v219";
    %"v221" : L = Div %"v220", #4;
    call %"v222" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v207", L %"v221")
    => goto "L183";
  @"L183":
    %"v225" : L = Sub %"v4", %"pr.5"
    => ret %"v225"
} }.

Definition item_glibc_wfileops'23str'2e254 : item :=
  (IData (a "glibc_wfileops#str.254") (LRo (a "local")) 1 [(Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 99); (Item Wb 111); (Item Wb 100); (Item Wb 101); (Item Wb 99); (Item Wb 118); (Item Wb 116); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_wfileops'23str'2e255 : item :=
  (IData (a "glibc_wfileops#str.255") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 111); (Item Wb 112); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_wfileops'23str'2e256 : item :=
  (IData (a "glibc_wfileops#str.256") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 117); (Item Wb 110); (Item Wb 100); (Item Wb 101); (Item Wb 114); (Item Wb 102); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 0)]).
