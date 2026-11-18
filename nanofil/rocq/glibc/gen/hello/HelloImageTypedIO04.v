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

Definition hello_image_fn___GI__IO_file_xsgetn : func :=
  ir_fn{ "export" "__GI__IO_file_xsgetn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v16" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v18" : L = Ptoi %"v17";
    %"v19" : L = Ptoi #0;
    %"v20" : W = (Cmp Eq L) %"v18", %"v19"
    => br %"v20" ? "L12" : "L39";
  @"L12":
    %"v25" = %"v0" +p #72;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v27" : L = Ptoi %"v26";
    %"v29" : W = (Cmp Ne L) %"v27", %"v19"
    => br %"v29" ? "L21" : "L23";
  @"L21":
    %"v32" = %"v0" +p #72;
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v33";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    call void $"free"(P %"v33")
    => goto "iw_1.join";
  @"iw_1.join":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v37" : W = And %"v35", #4294967039;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk4" + 0] <- %"v37"
    => goto "L23";
  @"L23":
    call void $"__GI__IO_doallocbuf"(P %"v0")
    => goto "L39";
  @"L39" [%"pr.7" : P = phi("L89" => %"pr.9", "L23" => %"v2", "start" => %"v2", "L97" => %"pr.9", "L53" => %"pr.7", "L218" => %"v214", "L197" => %"v214"); %"pr.1" : L = phi("L89" => %"pr.4", "L23" => %"v4", "start" => %"v4", "L97" => %"pr.4", "L53" => #0, "L218" => %"v217", "L197" => %"v217")]:
    %"v43" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v43" ? "L40" : "L41";
  @"L40":
    %"v45" = %"v0" +p #16;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v48" = %"v0" +p #8;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v50" : L = Ptoi %"v46";
    %"v51" : L = Ptoi %"v49";
    %"v52" : L = Sub %"v50", %"v51";
    %"v58" : W = (Cmp Ule L) %"pr.1", %"v52"
    => br %"v58" ? "L53" : "L54";
  @"L53":
    %"v61" = %"v0" +p #8;
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v64" : P = $"__GI_memcpy"(P %"pr.7", P %"v62", L %"pr.1");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk6", %"v61";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v69" = %"v67" +p %"pr.1";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk6", %"v61";
    store.ptr [%"chk9" + 0] <- %"v69"
    => goto poll "L39";
  @"L54":
    %"v74" : W = (Cmp Ugt L) %"v52", #0
    => br %"v74" ? "L70" : "L72";
  @"L70":
    %"v77" = %"v0" +p #8;
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v80" : P = $"__GI_mempcpy"(P %"pr.7", P %"v78", L %"v52");
    %"v83" : L = Sub %"pr.1", %"v52";
    %"chk11" : A = (Renew 0 8 Read 8) %"chk6", %"v77";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v88" = %"v86" +p %"v52";
    %"chk12" : A = (Renew 0 8 Write 8) %"chk6", %"v77";
    store.ptr [%"chk12" + 0] <- %"v88"
    => goto "L72";
  @"L72" [%"pr.9" : P = phi("L70" => %"v80", "L54" => %"pr.7"); %"pr.4" : L = phi("L70" => %"v83", "L54" => %"pr.1")]:
    %"chk13" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v94" : W = And %"v93", #256
    => br %"v94" ? "L89" : "L91";
  @"L89":
    call void $"_IO_switch_to_main_get_area"(P %"v0")
    => goto poll "L39";
  @"L91":
    %"v101" = %"v0" +p #56;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk0", %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v103" : L = Ptoi %"v102";
    %"v104" : W = (Cmp Ne L) %"v103", #0
    => br %"v104" ? "L105" : "L106";
  @"L105":
    %"v109" = %"v0" +p #64;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v109";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v112" = %"v0" +p #56;
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v114" : L = Ptoi %"v110";
    %"v115" : L = Ptoi %"v113";
    %"v116" : L = Sub %"v114", %"v115";
    %"v117" : W = (Cmp Ult L) %"pr.4", %"v116"
    => goto "L106";
  @"L106" [%"v119" : W = phi("L91" => #0, "L105" => %"v117")]:
    => br %"v119" ? "L97" : "L99";
  @"L97":
    call %"v124" : W = $"__GI___underflow"(P %"v0");
    %"v126" : W = (Cmp Eq W) %"v124", #4294967295
    => br %"v126" ? "L41" : poll "L39";
  @"L99":
    %"v130" = %"v0" +p #24;
    %"v132" = %"v0" +p #56;
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk18" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v130";
    store.ptr [%"chk18" + 0] <- %"v133";
    %"v135" = %"v0" +p #8;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Renew 0 8 Write 8) %"chk6", %"v135";
    store.ptr [%"chk20" + 0] <- %"v138";
    %"v140" = %"v0" +p #16;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (Renew 0 8 Write 8) %"chk5", %"v140";
    store.ptr [%"chk22" + 0] <- %"v143";
    %"v145" = %"v0" +p #32;
    %"v147" = %"v0" +p #40;
    %"chk23" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v147";
    store.ptr [%"chk24" + 0] <- %"v150";
    %"chk25" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v145";
    store.ptr [%"chk25" + 0] <- %"v150";
    %"v152" = %"v0" +p #48;
    %"chk26" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v152";
    store.ptr [%"chk27" + 0] <- %"v155";
    %"chk28" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v163" : L = Ptoi %"v162";
    %"v164" : W = (Cmp Ne L) %"v163", #0
    => br %"v164" ? "L157" : "L159";
  @"L157":
    %"v167" = %"v0" +p #64;
    %"chk29" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v167";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v170" = %"v0" +p #56;
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v172" : L = Ptoi %"v168";
    %"v173" : L = Ptoi %"v171";
    %"v174" : L = Sub %"v172", %"v173";
    %"v179" : W = (Cmp Uge L) %"v174", #128
    => br %"v179" ? "L175" : "L159";
  @"L175":
    %"v183" : L = Urem %"pr.4", %"v174";
    %"v184" : L = Sub %"pr.4", %"v183"
    => goto "L159";
  @"L159" [%"pr.5" : L = phi("L175" => %"v184", "L157" => %"pr.4", "L99" => %"pr.4")]:
    %"v186" = %"v0" +p #216;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v186";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_2.v4" : L = Ptoi %"v187";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join";
  @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join";
  @"iw_2.join":
    %"v189" = %"v187" +p #112;
    %"chk32" : A = (Check 0 8 Read 8) %"v189";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : F = CheckFunction %"v190";
    rawcall %"v194" : L = %"chk33"(P %"v0", P %"pr.9", L %"pr.5");
    %"v199" : W = (Cmp Sle L) %"v194", #0
    => br %"v199" ? "L195" : "L197";
  @"L195":
    %"v204" : W = (Cmp Eq L) %"v194", #0
    => br %"v204" ? "L200" : "L201";
  @"L200":
    %"chk34" : A = (Renew 0 4 Read 1) %"chk13", %"v0";
    %"v206" : W = (RawLoad (LdNarrow Sw) 0) %"chk34";
    %"v207" : W = Or %"v206", #16;
    %"chk35" : A = (Renew 0 4 Write 1) %"chk13", %"v0";
    store Ww [%"chk35" + 0] <- %"v207"
    => goto "L41";
  @"L201":
    %"chk36" : A = (Renew 0 4 Read 1) %"chk13", %"v0";
    %"v209" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"v210" : W = Or %"v209", #32;
    %"chk37" : A = (Renew 0 4 Write 1) %"chk13", %"v0";
    store Ww [%"chk37" + 0] <- %"v210"
    => goto "L41";
  @"L197":
    %"v214" = %"pr.9" +p %"v194";
    %"v217" : L = Sub %"pr.4", %"v194";
    %"v222" = %"v0" +p #144;
    %"chk38" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v222";
    %"v223" : L = (RawLoad LdL 0) %"chk38";
    %"v226" : W = (Cmp Ne L) %"v223", #18446744073709551615
    => br %"v226" ? "L218" : poll "L39";
  @"L218":
    %"v228" = %"v0" +p #144;
    %"v229" : L = (RawLoad LdL 0) %"chk38";
    %"v231" : L = Add %"v229", %"v194";
    %"chk40" : A = (Renew 0 8 Write 1) %"chk38", %"v228";
    store Wl [%"chk40" + 0] <- %"v231"
    => goto poll "L39";
  @"L41" [%"pr.2" : L = phi("L39" => %"pr.1", "L97" => %"pr.4", "L200" => %"pr.4", "L201" => %"pr.4")]:
    %"v234" : L = Sub %"v4", %"pr.2"
    => ret %"v234"
} }.

Definition hello_image_fn__IO_file_xsgetn_mmap : func :=
  ir_fn{ "export" "_IO_file_xsgetn_mmap"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v9" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v19" : L = Ptoi %"v15";
    %"v20" : L = Ptoi %"v18";
    %"v21" : L = Sub %"v19", %"v20";
    %"v27" : W = (Cmp Ult L) %"v21", %"v4"
    => br %"v27" ? "L22" : "L24";
  @"L22":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v33" : W = And %"v32", #256;
    %"v34" : L = (Ext Sw) %"v33";
    %"v35" : W = (Cmp Ne L) %"v34", #0
    => br %"v35" ? "L28" : "L30";
  @"L28":
    call %"v39" : P = $"__GI_mempcpy"(P %"v2", P %"v10", L %"v21");
    %"v42" : L = Sub %"v4", %"v21";
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v45" = %"v0" +p #8;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v48" = %"v0" +p #16;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk1", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v53" : L = Ptoi %"v49";
    %"v54" : L = Ptoi %"v52";
    %"v55" : L = Sub %"v53", %"v54"
    => goto "L30";
  @"L30" [%"pr.11" : P = phi("L28" => %"v39", "L22" => %"v2"); %"pr.7" : P = phi("L28" => %"v46", "L22" => %"v10"); %"pr.4" : L = phi("L28" => %"v55", "L22" => %"v21"); %"pr.2" : L = phi("L28" => %"v42", "L22" => %"v4")]:
    %"v61" : W = (Cmp Ult L) %"pr.4", %"pr.2"
    => br %"v61" ? "L56" : "L24";
  @"L56":
    call %"v66" : W = $"glibc_fileops#mmap_remap_check"(P %"v0");
    %"v67" : L = (Ext Sw) %"v66";
    %"v68" : W = (Cmp Ne L) %"v67", #0
    => br %"v68" ? "L62" : "L64";
  @"L62":
    %"v71" : L = Ptoi %"pr.11";
    %"v72" : L = Ptoi %"v2";
    %"v73" : L = Sub %"v71", %"v72";
    %"v75" = %"v0" +p #216;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v75";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v4" : L = Ptoi %"v76";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v78" = %"v76" +p #64;
    %"chk8" : A = (Check 0 8 Read 8) %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : F = CheckFunction %"v79";
    rawcall %"v83" : L = %"chk9"(P %"v0", P %"v2", L %"pr.2");
    %"v84" : L = Add %"v73", %"v83"
    => ret %"v84";
  @"L64":
    %"v87" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v90" = %"v0" +p #16;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk1", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v93" : L = Ptoi %"v91";
    %"v94" : L = Ptoi %"v88";
    %"v95" : L = Sub %"v93", %"v94"
    => goto "L24";
  @"L24" [%"pr.10" : P = phi("L64" => %"pr.11", "L30" => %"pr.11", "start" => %"v2"); %"pr.6" : P = phi("L64" => %"v88", "L30" => %"pr.7", "start" => %"v10"); %"pr.3" : L = phi("L64" => %"v95", "L30" => %"pr.4", "start" => %"v21"); %"pr.1" : L = phi("L64" => %"pr.2", "L30" => %"pr.2", "start" => %"v4")]:
    %"v101" : W = (Cmp Ult L) %"pr.3", %"pr.1"
    => br %"v101" ? "L96" : "L98";
  @"L96":
    %"chk12" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v103" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v104" : W = Or %"v103", #16;
    %"chk13" : A = (Renew 0 4 Write 1) %"chk12", %"v0";
    store Ww [%"chk13" + 0] <- %"v104"
    => goto "L98";
  @"L98":
    %"v109" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v109" ? "L105" : "L107";
  @"L105":
    => br %"v101" ? "L112" : "L111";
  @"L111":
    => goto "L112";
  @"L112" [%"v118" : L = phi("L111" => %"pr.1", "L105" => %"pr.3")]:
    call %"v122" : P = $"__GI_mempcpy"(P %"pr.10", P %"pr.6", L %"v118");
    %"v124" = %"v0" +p #8;
    %"v127" = %"pr.6" +p %"v118";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk0", %"v124";
    store.ptr [%"chk14" + 0] <- %"v127"
    => goto "L107";
  @"L107" [%"pr.9" : P = phi("L112" => %"v122", "L98" => %"pr.10")]:
    %"v130" : L = Ptoi %"pr.9";
    %"v131" : L = Ptoi %"v2";
    %"v132" : L = Sub %"v130", %"v131"
    => ret %"v132"
} }.

Definition hello_image_fn__IO_file_xsgetn_maybe_mmap : func :=
  ir_fn{ "export" "_IO_file_xsgetn_maybe_mmap"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call void $"glibc_fileops#decide_maybe_mmap"(P %"v0");
    %"v8" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v9";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v11" = %"v9" +p #64;
    %"chk1" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v12";
    rawcall %"v16" : L = %"chk2"(P %"v0", P %"v2", L %"v4")
    => ret %"v16"
} }.

Definition hello_image_fn___GI__IO_un_link : func :=
  ir_fn{ "export" "__GI__IO_un_link"(P %"v0") -> RVoid {
  @"start":
    %"v10" : P = (Alloc 8) #32;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #128
    => br %"v7" ? "L2" : "L4";
  @"L2":
    %"v12" : P = Copy $"glibc_genops#flush_cleanup";
    %"v13" = %"v10" +p #8;
    %"chk1" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk1" + 0] <- #0;
    %"chk2" : A = (HalfCheck Lower 0 8 Write 8) %"chk1", %"v10";
    store.ptr [%"chk2" + 0] <- %"v12";
    call void $"__GI___libc_cleanup_push_defer"(P %"v10");
    call %"v24" : P = $"zthread_self_cookie"();
    %"v28" : P = Copy $"__libc_single_threaded_internal";
    %"chk3" : A = (Check 0 1 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v30" : W = (Cmp Ne W) %"v29", #0
    => br %"v30" ? "L31" : "L32";
  @"L31":
    %"v33" : P = Copy $"glibc_genops#list_all_lock";
    %"v34" = %"v33" +p #8;
    %"chk4" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v36" : L = Ptoi %"v35";
    %"v37" : L = Ptoi #0;
    %"v38" : W = (Cmp Eq L) %"v36", %"v37"
    => goto "L32";
  @"L32" [%"v40" : W = phi("L2" => #0, "L31" => %"v38")]:
    => br %"v40" ? "L25" : "L26";
  @"L25":
    %"v41" : P = Copy $"glibc_genops#list_all_lock";
    %"chk5" : A = (Check 0 4 Write 1) %"v41";
    store Ww [%"chk5" + 0] <- #1;
    %"v42" : P = Copy $"glibc_genops#list_all_lock";
    %"v43" = %"v42" +p #8;
    %"chk6" : A = (Check 0 8 Write 8) %"v43";
    store.ptr [%"chk6" + 0] <- %"v24"
    => goto "L22";
  @"L26":
    %"v48" : P = Copy $"glibc_genops#list_all_lock";
    %"v49" = %"v48" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v52" : L = Ptoi %"v50";
    %"v53" : L = Ptoi %"v24";
    %"v54" : W = (Cmp Ne L) %"v52", %"v53"
    => br %"v54" ? "L45" : "L46";
  @"L45":
    %"v56" : P = Copy $"glibc_genops#list_all_lock";
    %"chk8" : A = (Check 0 4 Write 4) %"v56";
    %"v63" : W = (RawCas (CasNarrow Sw) 0) %"chk8", #0, #1;
    %"v64" : W = (Cmp Eq W) %"v63", #0
    => br %"v64" ? "L66" : "L65";
  @"L65":
    => goto "L66";
  @"L66":
    %"v67" : W = (Cmp Ne W) %"v63", #0
    => br %"v67" ? "L70" : "L59";
  @"L70":
    call void $"__GI___lll_lock_wait_private"(P %"v56")
    => goto "L59";
  @"L59":
    %"v80" : P = Copy $"glibc_genops#list_all_lock";
    %"v81" = %"v80" +p #8;
    %"chk9" : A = (Check 0 8 Write 8) %"v81";
    store.ptr [%"chk9" + 0] <- %"v24"
    => goto "L22";
  @"L46":
    %"v83" : P = Copy $"glibc_genops#list_all_lock";
    %"v84" = %"v83" +p #4;
    %"chk10" : A = (Check 0 4 Read 1) %"v84";
    %"v85" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v86" : W = Add %"v85", #1;
    %"chk11" : A = (Renew 0 4 Write 1) %"chk10", %"v84";
    store Ww [%"chk11" + 0] <- %"v86"
    => goto "L22";
  @"L22":
    %"v87" : P = Copy $"glibc_genops#run_fp";
    %"chk12" : A = (Check 0 8 Write 8) %"v87";
    store.ptr [%"chk12" + 0] <- %"v0";
    %"chk13" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v94" : W = And %"v93", #32768;
    %"v95" : W = (Cmp Eq W) %"v94", #0
    => br %"v95" ? "L96" : "L91";
  @"L96":
    call %"v100" : P = $"zthread_self_cookie"();
    %"v104" : P = Copy $"__libc_single_threaded_internal";
    %"chk14" : A = (Check 0 1 Read 1) %"v104";
    %"v105" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v106" : W = (Cmp Ne W) %"v105", #0
    => br %"v106" ? "L107" : "L108";
  @"L107":
    %"v110" = %"v0" +p #136;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v110";
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v112" = %"v111" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v114" : L = Ptoi %"v113";
    %"v115" : L = Ptoi #0;
    %"v116" : W = (Cmp Eq L) %"v114", %"v115"
    => goto "L108";
  @"L108" [%"v118" : W = phi("L96" => #0, "L107" => %"v116")]:
    => br %"v118" ? "L101" : "L102";
  @"L101":
    %"v120" = %"v0" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v120";
    %"v121" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Write 1) %"v121";
    store Ww [%"chk18" + 0] <- #1;
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v125" = %"v124" +p #8;
    %"chk20" : A = (Check 0 8 Write 8) %"v125";
    store.ptr [%"chk20" + 0] <- %"v100"
    => goto "L91";
  @"L102":
    %"v131" = %"v0" +p #136;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v131";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v133" = %"v132" +p #8;
    %"chk22" : A = (Check 0 8 Read 8) %"v133";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v136" : L = Ptoi %"v134";
    %"v137" : L = Ptoi %"v100";
    %"v138" : W = (Cmp Ne L) %"v136", %"v137"
    => br %"v138" ? "L127" : "L128";
  @"L127":
    %"v141" = %"v0" +p #136;
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 4 Write 4) %"v142";
    %"v149" : W = (RawCas (CasNarrow Sw) 0) %"chk24", #0, #1;
    %"v150" : W = (Cmp Eq W) %"v149", #0
    => br %"v150" ? "L152" : "L151";
  @"L151":
    => goto "L152";
  @"L152":
    %"v153" : W = (Cmp Ne W) %"v149", #0
    => br %"v153" ? "L156" : "L145";
  @"L156":
    call void $"__GI___lll_lock_wait_private"(P %"v142")
    => goto "L145";
  @"L145":
    %"v167" = %"v0" +p #136;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk21", %"v167";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v169" = %"v168" +p #8;
    %"chk26" : A = (Check 0 8 Write 8) %"v169";
    store.ptr [%"chk26" + 0] <- %"v100"
    => goto "L91";
  @"L128":
    %"v172" = %"v0" +p #136;
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v174" = %"v173" +p #4;
    %"chk28" : A = (Check 0 4 Read 1) %"v174";
    %"v175" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v176" : W = Add %"v175", #1;
    %"chk29" : A = (Renew 0 4 Write 1) %"chk28", %"v174";
    store Ww [%"chk29" + 0] <- %"v176"
    => goto "L91";
  @"L91":
    %"v180" : P = Copy $"__GI__IO_list_all";
    %"chk30" : A = (Check 0 8 Read 8) %"v180";
    %"v181" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v182" : L = Ptoi %"v181";
    %"v183" : L = Ptoi #0;
    %"v184" : W = (Cmp Eq L) %"v182", %"v183"
    => br %"v184" ? "L179" : "L185";
  @"L185":
    %"v191" = %"v0" +p #184;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v191";
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v195" = %"v0" +p #104;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v195";
    %"v196" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Check 0 8 Write 8) %"v192";
    store.ptr [%"chk33" + 0] <- %"v196";
    %"v203" : L = Ptoi %"v196";
    %"v205" : W = (Cmp Ne L) %"v203", %"v183"
    => br %"v205" ? "L199" : "L179";
  @"L199":
    %"v207" = %"v196" +p #184;
    %"chk34" : A = (Check 0 8 Write 8) %"v207";
    store.ptr [%"chk34" + 0] <- %"v192"
    => goto "L179";
  @"L179":
    %"chk35" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v252" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v254" : W = And %"v252", #4294967167;
    %"chk36" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk36" + 0] <- %"v254";
    %"v259" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"v260" : W = And %"v259", #32768;
    %"v261" : W = (Cmp Eq W) %"v260", #0
    => br %"v261" ? "L262" : "L257";
  @"L262":
    %"v268" : P = Copy $"__libc_single_threaded_internal";
    %"chk38" : A = (Check 0 1 Read 1) %"v268";
    %"v269" : W = (RawLoad (LdNarrow Sb) 0) %"chk38";
    %"v270" : W = (Cmp Ne W) %"v269", #0
    => br %"v270" ? "L271" : "L272";
  @"L271":
    %"v274" = %"v0" +p #136;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v274";
    %"v275" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v276" = %"v275" +p #4;
    %"chk40" : A = (Check 0 4 Read 1) %"v276";
    %"v277" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"v278" : W = (Cmp Eq W) %"v277", #0
    => goto "L272";
  @"L272" [%"v280" : W = phi("L262" => #0, "L271" => %"v278")]:
    => br %"v280" ? "L265" : "L266";
  @"L265":
    %"v282" = %"v0" +p #136;
    %"chk41" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v282";
    %"v283" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v284" = %"v283" +p #8;
    %"chk42" : A = (Check 0 8 Write 8) %"v284";
    store.ptr [%"chk42" + 0] <- #0;
    %"chk43" : A = (Renew 0 8 Read 8) %"chk41", %"v282";
    %"v287" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"chk44" : A = (Check 0 4 Write 1) %"v287";
    store Ww [%"chk44" + 0] <- #0
    => goto "L257";
  @"L266":
    %"v292" = %"v0" +p #136;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v292";
    %"v293" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v294" = %"v293" +p #4;
    %"chk46" : A = (Check 0 4 Read 1) %"v294";
    %"v295" : W = (RawLoad (LdNarrow Sw) 0) %"chk46";
    %"v296" : W = (Cmp Eq W) %"v295", #0
    => br %"v296" ? "L288" : "L289";
  @"L288":
    %"v298" = %"v0" +p #136;
    %"v299" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v300" = %"v299" +p #8;
    %"chk48" : A = (Check 0 8 Write 8) %"v300";
    store.ptr [%"chk48" + 0] <- #0;
    %"chk49" : A = (Renew 0 8 Read 8) %"chk45", %"v298";
    %"v304" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"chk50" : A = (Check 0 4 Read 1) %"v304";
    %"v308" : W = (RawLoad (LdNarrow Sw) 0) %"chk50"
    => goto "L309";
  @"L309" [%"v311" : W = phi("L288" => %"v308", "L309" => %"v312")]:
    %"chk51" : A = (HalfCheck Lower 0 4 Write 4) %"chk50", %"v304";
    %"v312" : W = (RawCas (CasNarrow Sw) 0) %"chk51", %"v311", #0;
    %"v313" : W = (Cmp Eq W) %"v312", %"v311"
    => br %"v313" ? "L310" : poll "L309";
  @"L310":
    %"v318" : W = (Cmp Sgt W) %"v311", #1
    => br %"v318" ? "L321" : "L257";
  @"L321":
    call void $"__GI___lll_lock_wake_private"(P %"v304")
    => goto "L257";
  @"L289":
    %"v333" = %"v0" +p #136;
    %"v334" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v335" = %"v334" +p #4;
    %"chk53" : A = (Check 0 4 Read 1) %"v335";
    %"v336" : W = (RawLoad (LdNarrow Sw) 0) %"chk53";
    %"v337" : W = Sub %"v336", #1;
    %"chk54" : A = (Renew 0 4 Write 1) %"chk53", %"v335";
    store Ww [%"chk54" + 0] <- %"v337"
    => goto "L257";
  @"L257":
    %"v338" : P = Copy $"glibc_genops#run_fp";
    %"chk55" : A = (Check 0 8 Write 8) %"v338";
    store.ptr [%"chk55" + 0] <- #0;
    %"v345" : P = Copy $"__libc_single_threaded_internal";
    %"chk56" : A = (Check 0 1 Read 1) %"v345";
    %"v346" : W = (RawLoad (LdNarrow Sb) 0) %"chk56";
    %"v347" : W = (Cmp Ne W) %"v346", #0
    => br %"v347" ? "L348" : "L349";
  @"L348":
    %"v350" : P = Copy $"glibc_genops#list_all_lock";
    %"v351" = %"v350" +p #4;
    %"chk57" : A = (Check 0 4 Read 1) %"v351";
    %"v352" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v353" : W = (Cmp Eq W) %"v352", #0
    => goto "L349";
  @"L349" [%"v355" : W = phi("L257" => #0, "L348" => %"v353")]:
    => br %"v355" ? "L342" : "L343";
  @"L342":
    %"v356" : P = Copy $"glibc_genops#list_all_lock";
    %"v357" = %"v356" +p #8;
    %"chk58" : A = (Check 0 8 Write 8) %"v357";
    store.ptr [%"chk58" + 0] <- #0;
    %"v358" : P = Copy $"glibc_genops#list_all_lock";
    %"chk59" : A = (Check 0 4 Write 1) %"v358";
    store Ww [%"chk59" + 0] <- #0
    => goto "L401";
  @"L343":
    %"v362" : P = Copy $"glibc_genops#list_all_lock";
    %"v363" = %"v362" +p #4;
    %"chk60" : A = (Check 0 4 Read 1) %"v363";
    %"v364" : W = (RawLoad (LdNarrow Sw) 0) %"chk60";
    %"v365" : W = (Cmp Eq W) %"v364", #0
    => br %"v365" ? "L359" : "L360";
  @"L359":
    %"v366" : P = Copy $"glibc_genops#list_all_lock";
    %"v367" = %"v366" +p #8;
    %"chk61" : A = (Check 0 8 Write 8) %"v367";
    store.ptr [%"chk61" + 0] <- #0;
    %"v369" : P = Copy $"glibc_genops#list_all_lock";
    %"chk62" : A = (Check 0 4 Read 1) %"v369";
    %"v373" : W = (RawLoad (LdNarrow Sw) 0) %"chk62"
    => goto "L374";
  @"L374" [%"v376" : W = phi("L359" => %"v373", "L374" => %"v377")]:
    %"chk63" : A = (HalfCheck Lower 0 4 Write 4) %"chk62", %"v369";
    %"v377" : W = (RawCas (CasNarrow Sw) 0) %"chk63", %"v376", #0;
    %"v378" : W = (Cmp Eq W) %"v377", %"v376"
    => br %"v378" ? "L375" : poll "L374";
  @"L375":
    %"v383" : W = (Cmp Sgt W) %"v376", #1
    => br %"v383" ? "L386" : "L401";
  @"L386":
    call void $"__GI___lll_lock_wake_private"(P %"v369")
    => goto "L401";
  @"L360":
    %"v397" : P = Copy $"glibc_genops#list_all_lock";
    %"v398" = %"v397" +p #4;
    %"chk64" : A = (Check 0 4 Read 1) %"v398";
    %"v399" : W = (RawLoad (LdNarrow Sw) 0) %"chk64";
    %"v400" : W = Sub %"v399", #1;
    %"chk65" : A = (Renew 0 4 Write 1) %"chk64", %"v398";
    store Ww [%"chk65" + 0] <- %"v400"
    => goto "L401";
  @"L401":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v10")
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition hello_image_fn___GI__IO_link_in : func :=
  ir_fn{ "export" "__GI__IO_link_in"(P %"v0") -> RVoid {
  @"start":
    %"v13" : P = (Alloc 8) #32;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #128;
    %"v8" : W = (Cmp Eq W) %"v7", #0
    => br %"v8" ? "L2" : "L4";
  @"L2":
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = Or %"v10", #128;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v11";
    %"v15" : P = Copy $"glibc_genops#flush_cleanup";
    %"v16" = %"v13" +p #8;
    %"chk3" : A = (Check 0 8 Write 8) %"v16";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v13";
    store.ptr [%"chk4" + 0] <- %"v15";
    call void $"__GI___libc_cleanup_push_defer"(P %"v13");
    call %"v27" : P = $"zthread_self_cookie"();
    %"v31" : P = Copy $"__libc_single_threaded_internal";
    %"chk5" : A = (Check 0 1 Read 1) %"v31";
    %"v32" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v33" : W = (Cmp Ne W) %"v32", #0
    => br %"v33" ? "L34" : "L35";
  @"L34":
    %"v36" : P = Copy $"glibc_genops#list_all_lock";
    %"v37" = %"v36" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v39" : L = Ptoi %"v38";
    %"v40" : L = Ptoi #0;
    %"v41" : W = (Cmp Eq L) %"v39", %"v40"
    => goto "L35";
  @"L35" [%"v43" : W = phi("L2" => #0, "L34" => %"v41")]:
    => br %"v43" ? "L28" : "L29";
  @"L28":
    %"v44" : P = Copy $"glibc_genops#list_all_lock";
    %"chk7" : A = (Check 0 4 Write 1) %"v44";
    store Ww [%"chk7" + 0] <- #1;
    %"v45" : P = Copy $"glibc_genops#list_all_lock";
    %"v46" = %"v45" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"v46";
    store.ptr [%"chk8" + 0] <- %"v27"
    => goto "L25";
  @"L29":
    %"v51" : P = Copy $"glibc_genops#list_all_lock";
    %"v52" = %"v51" +p #8;
    %"chk9" : A = (Check 0 8 Read 8) %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v55" : L = Ptoi %"v53";
    %"v56" : L = Ptoi %"v27";
    %"v57" : W = (Cmp Ne L) %"v55", %"v56"
    => br %"v57" ? "L48" : "L49";
  @"L48":
    %"v59" : P = Copy $"glibc_genops#list_all_lock";
    %"chk10" : A = (Check 0 4 Write 4) %"v59";
    %"v66" : W = (RawCas (CasNarrow Sw) 0) %"chk10", #0, #1;
    %"v67" : W = (Cmp Eq W) %"v66", #0
    => br %"v67" ? "L69" : "L68";
  @"L68":
    => goto "L69";
  @"L69":
    %"v70" : W = (Cmp Ne W) %"v66", #0
    => br %"v70" ? "L73" : "L62";
  @"L73":
    call void $"__GI___lll_lock_wait_private"(P %"v59")
    => goto "L62";
  @"L62":
    %"v83" : P = Copy $"glibc_genops#list_all_lock";
    %"v84" = %"v83" +p #8;
    %"chk11" : A = (Check 0 8 Write 8) %"v84";
    store.ptr [%"chk11" + 0] <- %"v27"
    => goto "L25";
  @"L49":
    %"v86" : P = Copy $"glibc_genops#list_all_lock";
    %"v87" = %"v86" +p #4;
    %"chk12" : A = (Check 0 4 Read 1) %"v87";
    %"v88" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v89" : W = Add %"v88", #1;
    %"chk13" : A = (Renew 0 4 Write 1) %"chk12", %"v87";
    store Ww [%"chk13" + 0] <- %"v89"
    => goto "L25";
  @"L25":
    %"v90" : P = Copy $"glibc_genops#run_fp";
    %"chk14" : A = (Check 0 8 Write 8) %"v90";
    store.ptr [%"chk14" + 0] <- %"v0";
    %"chk15" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v96" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v97" : W = And %"v96", #32768;
    %"v98" : W = (Cmp Eq W) %"v97", #0
    => br %"v98" ? "L99" : "L94";
  @"L99":
    call %"v103" : P = $"zthread_self_cookie"();
    %"v107" : P = Copy $"__libc_single_threaded_internal";
    %"chk16" : A = (Check 0 1 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"v109" : W = (Cmp Ne W) %"v108", #0
    => br %"v109" ? "L110" : "L111";
  @"L110":
    %"v113" = %"v0" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v115" = %"v114" +p #8;
    %"chk18" : A = (Check 0 8 Read 8) %"v115";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v117" : L = Ptoi %"v116";
    %"v118" : L = Ptoi #0;
    %"v119" : W = (Cmp Eq L) %"v117", %"v118"
    => goto "L111";
  @"L111" [%"v121" : W = phi("L99" => #0, "L110" => %"v119")]:
    => br %"v121" ? "L104" : "L105";
  @"L104":
    %"v123" = %"v0" +p #136;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v123";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Check 0 4 Write 1) %"v124";
    store Ww [%"chk20" + 0] <- #1;
    %"v127" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v128" = %"v127" +p #8;
    %"chk22" : A = (Check 0 8 Write 8) %"v128";
    store.ptr [%"chk22" + 0] <- %"v103"
    => goto "L94";
  @"L105":
    %"v134" = %"v0" +p #136;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v136" = %"v135" +p #8;
    %"chk24" : A = (Check 0 8 Read 8) %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v139" : L = Ptoi %"v137";
    %"v140" : L = Ptoi %"v103";
    %"v141" : W = (Cmp Ne L) %"v139", %"v140"
    => br %"v141" ? "L130" : "L131";
  @"L130":
    %"v144" = %"v0" +p #136;
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk26" : A = (Check 0 4 Write 4) %"v145";
    %"v152" : W = (RawCas (CasNarrow Sw) 0) %"chk26", #0, #1;
    %"v153" : W = (Cmp Eq W) %"v152", #0
    => br %"v153" ? "L155" : "L154";
  @"L154":
    => goto "L155";
  @"L155":
    %"v156" : W = (Cmp Ne W) %"v152", #0
    => br %"v156" ? "L159" : "L148";
  @"L159":
    call void $"__GI___lll_lock_wait_private"(P %"v145")
    => goto "L148";
  @"L148":
    %"v170" = %"v0" +p #136;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk23", %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v172" = %"v171" +p #8;
    %"chk28" : A = (Check 0 8 Write 8) %"v172";
    store.ptr [%"chk28" + 0] <- %"v103"
    => goto "L94";
  @"L131":
    %"v175" = %"v0" +p #136;
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v177" = %"v176" +p #4;
    %"chk30" : A = (Check 0 4 Read 1) %"v177";
    %"v178" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v179" : W = Add %"v178", #1;
    %"chk31" : A = (Renew 0 4 Write 1) %"chk30", %"v177";
    store Ww [%"chk31" + 0] <- %"v179"
    => goto "L94";
  @"L94":
    %"v181" = %"v0" +p #104;
    %"v182" : P = Copy $"__GI__IO_list_all";
    %"chk32" : A = (Check 0 8 Read 8) %"v182";
    %"v183" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v181";
    store.ptr [%"chk33" + 0] <- %"v183";
    %"v189" = %"v0" +p #184;
    %"v190" : P = Copy $"__GI__IO_list_all";
    %"chk34" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v189";
    store.ptr [%"chk34" + 0] <- %"v190";
    %"v194" : P = Copy $"__GI__IO_list_all";
    %"chk35" : A = (Check 0 8 Read 8) %"v194";
    %"v195" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v196" : L = Ptoi %"v195";
    %"v197" : L = Ptoi #0;
    %"v198" : W = (Cmp Ne L) %"v196", %"v197"
    => br %"v198" ? "L191" : "L186";
  @"L191":
    %"v199" : P = Copy $"__GI__IO_list_all";
    %"chk36" : A = (Check 0 8 Read 8) %"v199";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v201" = %"v200" +p #184;
    %"v203" = %"v0" +p #104;
    %"chk37" : A = (Check 0 8 Write 8) %"v201";
    store.ptr [%"chk37" + 0] <- %"v203"
    => goto "L186";
  @"L186":
    %"v204" : P = Copy $"__GI__IO_list_all";
    %"chk38" : A = (Check 0 8 Write 8) %"v204";
    store.ptr [%"chk38" + 0] <- %"v0";
    %"chk39" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v210" : W = (RawLoad (LdNarrow Sw) 0) %"chk39";
    %"v211" : W = And %"v210", #32768;
    %"v212" : W = (Cmp Eq W) %"v211", #0
    => br %"v212" ? "L213" : "L208";
  @"L213":
    %"v219" : P = Copy $"__libc_single_threaded_internal";
    %"chk40" : A = (Check 0 1 Read 1) %"v219";
    %"v220" : W = (RawLoad (LdNarrow Sb) 0) %"chk40";
    %"v221" : W = (Cmp Ne W) %"v220", #0
    => br %"v221" ? "L222" : "L223";
  @"L222":
    %"v225" = %"v0" +p #136;
    %"chk41" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v225";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v227" = %"v226" +p #4;
    %"chk42" : A = (Check 0 4 Read 1) %"v227";
    %"v228" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v229" : W = (Cmp Eq W) %"v228", #0
    => goto "L223";
  @"L223" [%"v231" : W = phi("L213" => #0, "L222" => %"v229")]:
    => br %"v231" ? "L216" : "L217";
  @"L216":
    %"v233" = %"v0" +p #136;
    %"chk43" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v233";
    %"v234" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v235" = %"v234" +p #8;
    %"chk44" : A = (Check 0 8 Write 8) %"v235";
    store.ptr [%"chk44" + 0] <- #0;
    %"chk45" : A = (Renew 0 8 Read 8) %"chk43", %"v233";
    %"v238" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"chk46" : A = (Check 0 4 Write 1) %"v238";
    store Ww [%"chk46" + 0] <- #0
    => goto "L208";
  @"L217":
    %"v243" = %"v0" +p #136;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v243";
    %"v244" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v245" = %"v244" +p #4;
    %"chk48" : A = (Check 0 4 Read 1) %"v245";
    %"v246" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"v247" : W = (Cmp Eq W) %"v246", #0
    => br %"v247" ? "L239" : "L240";
  @"L239":
    %"v249" = %"v0" +p #136;
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v251" = %"v250" +p #8;
    %"chk50" : A = (Check 0 8 Write 8) %"v251";
    store.ptr [%"chk50" + 0] <- #0;
    %"chk51" : A = (Renew 0 8 Read 8) %"chk47", %"v249";
    %"v255" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"chk52" : A = (Check 0 4 Read 1) %"v255";
    %"v259" : W = (RawLoad (LdNarrow Sw) 0) %"chk52"
    => goto "L260";
  @"L260" [%"v262" : W = phi("L239" => %"v259", "L260" => %"v263")]:
    %"chk53" : A = (HalfCheck Lower 0 4 Write 4) %"chk52", %"v255";
    %"v263" : W = (RawCas (CasNarrow Sw) 0) %"chk53", %"v262", #0;
    %"v264" : W = (Cmp Eq W) %"v263", %"v262"
    => br %"v264" ? "L261" : poll "L260";
  @"L261":
    %"v269" : W = (Cmp Sgt W) %"v262", #1
    => br %"v269" ? "L272" : "L208";
  @"L272":
    call void $"__GI___lll_lock_wake_private"(P %"v255")
    => goto "L208";
  @"L240":
    %"v284" = %"v0" +p #136;
    %"v285" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v286" = %"v285" +p #4;
    %"chk55" : A = (Check 0 4 Read 1) %"v286";
    %"v287" : W = (RawLoad (LdNarrow Sw) 0) %"chk55";
    %"v288" : W = Sub %"v287", #1;
    %"chk56" : A = (Renew 0 4 Write 1) %"chk55", %"v286";
    store Ww [%"chk56" + 0] <- %"v288"
    => goto "L208";
  @"L208":
    %"v289" : P = Copy $"glibc_genops#run_fp";
    %"chk57" : A = (Check 0 8 Write 8) %"v289";
    store.ptr [%"chk57" + 0] <- #0;
    %"v296" : P = Copy $"__libc_single_threaded_internal";
    %"chk58" : A = (Check 0 1 Read 1) %"v296";
    %"v297" : W = (RawLoad (LdNarrow Sb) 0) %"chk58";
    %"v298" : W = (Cmp Ne W) %"v297", #0
    => br %"v298" ? "L299" : "L300";
  @"L299":
    %"v301" : P = Copy $"glibc_genops#list_all_lock";
    %"v302" = %"v301" +p #4;
    %"chk59" : A = (Check 0 4 Read 1) %"v302";
    %"v303" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"v304" : W = (Cmp Eq W) %"v303", #0
    => goto "L300";
  @"L300" [%"v306" : W = phi("L208" => #0, "L299" => %"v304")]:
    => br %"v306" ? "L293" : "L294";
  @"L293":
    %"v307" : P = Copy $"glibc_genops#list_all_lock";
    %"v308" = %"v307" +p #8;
    %"chk60" : A = (Check 0 8 Write 8) %"v308";
    store.ptr [%"chk60" + 0] <- #0;
    %"v309" : P = Copy $"glibc_genops#list_all_lock";
    %"chk61" : A = (Check 0 4 Write 1) %"v309";
    store Ww [%"chk61" + 0] <- #0
    => goto "L352";
  @"L294":
    %"v313" : P = Copy $"glibc_genops#list_all_lock";
    %"v314" = %"v313" +p #4;
    %"chk62" : A = (Check 0 4 Read 1) %"v314";
    %"v315" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"v316" : W = (Cmp Eq W) %"v315", #0
    => br %"v316" ? "L310" : "L311";
  @"L310":
    %"v317" : P = Copy $"glibc_genops#list_all_lock";
    %"v318" = %"v317" +p #8;
    %"chk63" : A = (Check 0 8 Write 8) %"v318";
    store.ptr [%"chk63" + 0] <- #0;
    %"v320" : P = Copy $"glibc_genops#list_all_lock";
    %"chk64" : A = (Check 0 4 Read 1) %"v320";
    %"v324" : W = (RawLoad (LdNarrow Sw) 0) %"chk64"
    => goto "L325";
  @"L325" [%"v327" : W = phi("L310" => %"v324", "L325" => %"v328")]:
    %"chk65" : A = (HalfCheck Lower 0 4 Write 4) %"chk64", %"v320";
    %"v328" : W = (RawCas (CasNarrow Sw) 0) %"chk65", %"v327", #0;
    %"v329" : W = (Cmp Eq W) %"v328", %"v327"
    => br %"v329" ? "L326" : poll "L325";
  @"L326":
    %"v334" : W = (Cmp Sgt W) %"v327", #1
    => br %"v334" ? "L337" : "L352";
  @"L337":
    call void $"__GI___lll_lock_wake_private"(P %"v320")
    => goto "L352";
  @"L311":
    %"v348" : P = Copy $"glibc_genops#list_all_lock";
    %"v349" = %"v348" +p #4;
    %"chk66" : A = (Check 0 4 Read 1) %"v349";
    %"v350" : W = (RawLoad (LdNarrow Sw) 0) %"chk66";
    %"v351" : W = Sub %"v350", #1;
    %"chk67" : A = (Renew 0 4 Write 1) %"chk66", %"v349";
    store Ww [%"chk67" + 0] <- %"v351"
    => goto "L352";
  @"L352":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v13")
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition hello_image_fn__IO_switch_to_main_get_area : func :=
  ir_fn{ "export" "_IO_switch_to_main_get_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v6" : W = And %"v4", #4294967039;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk1" + 0] <- %"v6";
    %"v8" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v13" = %"v0" +p #88;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Write 8) %"chk2", %"v8";
    store.ptr [%"chk4" + 0] <- %"v14";
    %"chk5" : A = (Renew 0 8 Write 8) %"chk3", %"v13";
    store.ptr [%"chk5" + 0] <- %"v9";
    %"v19" = %"v0" +p #24;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v24" = %"v0" +p #72;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk6", %"v19";
    store.ptr [%"chk8" + 0] <- %"v25";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk7", %"v24";
    store.ptr [%"chk9" + 0] <- %"v20";
    %"v30" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk6", %"v19";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v30";
    store.ptr [%"chk11" + 0] <- %"v33"
    => ret void
} }.

Definition hello_image_fn__IO_switch_to_backup_area : func :=
  ir_fn{ "export" "_IO_switch_to_backup_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v5" : W = Or %"v4", #256;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk1" + 0] <- %"v5";
    %"v7" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v12" = %"v0" +p #88;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Write 8) %"chk2", %"v7";
    store.ptr [%"chk4" + 0] <- %"v13";
    %"chk5" : A = (Renew 0 8 Write 8) %"chk3", %"v12";
    store.ptr [%"chk5" + 0] <- %"v8";
    %"v18" = %"v0" +p #24;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v23" = %"v0" +p #72;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk6", %"v18";
    store.ptr [%"chk8" + 0] <- %"v24";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk7", %"v23";
    store.ptr [%"chk9" + 0] <- %"v19";
    %"v29" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk2", %"v7";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v29";
    store.ptr [%"chk11" + 0] <- %"v32"
    => ret void
} }.

Definition hello_image_fn___GI__IO_switch_to_get_mode : func :=
  ir_fn{ "export" "__GI__IO_switch_to_get_mode"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" = %"v0" +p #32;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : W = (Cmp Ugt L) %"v11", %"v12"
    => br %"v13" ? "L2" : "L4";
  @"L2":
    %"v18" = %"v0" +p #216;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v4" : L = Ptoi %"v19";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v21" = %"v19" +p #24;
    %"chk3" : A = (Check 0 8 Read 8) %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v22";
    rawcall %"v25" : W = %"chk4"(P %"v0", W #4294967295);
    %"v27" : W = (Cmp Eq W) %"v25", #4294967295
    => br %"v27" ? "L14" : "L4";
  @"L14":
    => ret #4294967295;
  @"L4":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v35" : W = And %"v34", #256
    => br %"v35" ? "L30" : "L31";
  @"L30":
    %"v37" = %"v0" +p #24;
    %"v39" = %"v0" +p #80;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v37";
    store.ptr [%"chk7" + 0] <- %"v40"
    => goto "L32";
  @"L31":
    %"v42" = %"v0" +p #24;
    %"v44" = %"v0" +p #56;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v42";
    store.ptr [%"chk9" + 0] <- %"v45";
    %"v50" = %"v0" +p #40;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v53" = %"v0" +p #16;
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v55" : L = Ptoi %"v51";
    %"v56" : L = Ptoi %"v54";
    %"v57" : W = (Cmp Ugt L) %"v55", %"v56"
    => br %"v57" ? "L46" : "L32";
  @"L46":
    %"v59" = %"v0" +p #16;
    %"v61" = %"v0" +p #40;
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk13" : A = (Renew 0 8 Write 8) %"chk11", %"v59";
    store.ptr [%"chk13" + 0] <- %"v62"
    => goto "L32";
  @"L32":
    %"v64" = %"v0" +p #8;
    %"v66" = %"v0" +p #40;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk0", %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v64";
    store.ptr [%"chk15" + 0] <- %"v67";
    %"v69" = %"v0" +p #32;
    %"v73" = %"v0" +p #48;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk15", %"v64";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v73";
    store.ptr [%"chk17" + 0] <- %"v76";
    %"chk18" : A = (Renew 0 8 Write 8) %"chk0", %"v66";
    store.ptr [%"chk18" + 0] <- %"v76";
    %"chk19" : A = (Renew 0 8 Write 8) %"chk1", %"v69";
    store.ptr [%"chk19" + 0] <- %"v76";
    %"chk20" : A = (Renew 0 4 Read 1) %"chk5", %"v0";
    %"v78" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"v80" : W = And %"v78", #4294965247;
    %"chk21" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk21" + 0] <- %"v80"
    => ret #0
} }.

Definition hello_image_fn___GI__IO_free_backup_area : func :=
  ir_fn{ "export" "__GI__IO_free_backup_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #256
    => br %"v7" ? "L2" : "L4";
  @"L2":
    call void $"_IO_switch_to_main_get_area"(P %"v0")
    => goto "L4";
  @"L4":
    %"v11" = %"v0" +p #72;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v12";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    call void $"free"(P %"v12")
    => goto "iw_1.join";
  @"iw_1.join":
    %"v14" = %"v0" +p #72;
    %"chk2" : A = (Renew 0 8 Write 8) %"chk1", %"v14";
    store.ptr [%"chk2" + 0] <- #0;
    %"v16" = %"v0" +p #88;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v16";
    store.ptr [%"chk3" + 0] <- #0;
    %"v18" = %"v0" +p #80;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v18";
    store.ptr [%"chk4" + 0] <- #0
    => ret void
} }.

Definition hello_image_fn___GI__IO_setb : func :=
  ir_fn{ "export" "__GI__IO_setb"(P %"v0", P %"v2", P %"v4", W %"v6") -> RVoid {
  @"start":
    %"v12" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : L = Ptoi %"v13";
    %"v15" : W = (Cmp Ne L) %"v14", #0
    => br %"v15" ? "L16" : "L17";
  @"L16":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v20" : W = And %"v19", #1;
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => goto "L17";
  @"L17" [%"v23" : W = phi("start" => #0, "L16" => %"v21")]:
    => br %"v23" ? "L8" : "L10";
  @"L8":
    %"v25" = %"v0" +p #56;
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"free"(P %"v26")
    => goto "L10";
  @"L10":
    %"v28" = %"v0" +p #56;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v28";
    store.ptr [%"chk3" + 0] <- %"v2";
    %"v31" = %"v0" +p #64;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v31";
    store.ptr [%"chk4" + 0] <- %"v4"
    => br %"v6" ? "L33" : "L34";
  @"L33":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v40" : W = And %"v38", #4294967294;
    %"chk6" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk6" + 0] <- %"v40"
    => goto "L35";
  @"L34":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v42" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v43" : W = Or %"v42", #1;
    %"chk8" : A = (Renew 0 4 Write 1) %"chk7", %"v0";
    store Ww [%"chk8" + 0] <- %"v43"
    => goto "L35";
  @"L35":
    => ret void
} }.

Definition hello_image_fn___GI__IO_doallocbuf : func :=
  ir_fn{ "export" "__GI__IO_doallocbuf"(P %"v0") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" : L = Ptoi %"v7";
    %"v9" : W = (Cmp Ne L) %"v8", #0
    => br %"v9" ? "L2" : "L4";
  @"L2":
    => ret void;
  @"L4":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v15" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v16" : W = And %"v15", #2;
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => br %"v17" ? "L19" : "L18";
  @"L18":
    %"v21" = %"v0" +p #192;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v23" : W = (Cmp Sgt W) %"v22", #0
    => goto "L19";
  @"L19" [%"v25" : W = phi("L4" => #1, "L18" => %"v23")]:
    => br %"v25" ? "L11" : "L13";
  @"L11":
    %"v30" = %"v0" +p #216;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v4" : L = Ptoi %"v31";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v33" = %"v31" +p #104;
    %"chk4" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : F = CheckFunction %"v34";
    rawcall %"v36" : W = %"chk5"(P %"v0");
    %"v38" : W = (Cmp Ne W) %"v36", #4294967295
    => br %"v38" ? "L26" : "L13";
  @"L26":
    => ret void;
  @"L13":
    %"v42" = %"v0" +p #131;
    %"v45" = %"v42" +p #1;
    call void $"__GI__IO_setb"(P %"v0", P %"v42", P %"v45", W #0)
    => ret void
} }.

Definition hello_image_fn___GI__IO_default_uflow : func :=
  ir_fn{ "export" "__GI__IO_default_uflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v4" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v5";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v7" = %"v5" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v8";
    rawcall %"v10" : W = %"chk2"(P %"v0");
    %"v16" : W = (Cmp Eq W) %"v10", #4294967295
    => br %"v16" ? "L11" : "L13";
  @"L11":
    => ret #4294967295;
  @"L13":
    %"v20" = %"v0" +p #8;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v22" = %"v21" +p #1;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk3", %"v20";
    store.ptr [%"chk4" + 0] <- %"v22";
    %"chk5" : A = (Check 0 1 Read 1) %"v21";
    %"v23" : W = (RawLoad (LdNarrow Ub) 0) %"chk5"
    => ret %"v23"
} }.

Definition hello_image_fn___GI__IO_default_xsputn : func :=
  ir_fn{ "export" "__GI__IO_default_xsputn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v14" : W = (Cmp Ule L) %"v4", #0
    => br %"v14" ? "L10" : "L16";
  @"L10":
    => ret #0;
  @"L16" [%"pr.7" : L = phi("start" => %"v4", "L96" => %"v119"); %"pr.2" : P = phi("start" => %"v2", "L96" => %"pr.1")]:
    %"v24" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v27" = %"v0" +p #48;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v29" : L = Ptoi %"v25";
    %"v30" : L = Ptoi %"v28";
    %"v31" : W = (Cmp Ult L) %"v29", %"v30"
    => br %"v31" ? "L20" : "L22";
  @"L20":
    %"v34" = %"v0" +p #48;
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v37" = %"v0" +p #40;
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v39" : L = Ptoi %"v35";
    %"v40" : L = Ptoi %"v38";
    %"v41" : L = Sub %"v39", %"v40";
    %"v47" : W = (Cmp Ugt L) %"v41", %"pr.7"
    => br %"v47" ? "L44" : "L43";
  @"L43":
    => goto "L44";
  @"L44" [%"pr.9" : L = phi("L43" => %"v41", "L20" => %"pr.7")]:
    %"v53" : W = (Cmp Ugt L) %"pr.9", #20
    => br %"v53" ? "L49" : "L50";
  @"L49":
    %"v55" = %"v0" +p #40;
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v61" : P = $"__GI_mempcpy"(P %"v58", P %"pr.2", L %"pr.9");
    %"chk5" : A = (Renew 0 8 Write 8) %"chk0", %"v55";
    store.ptr [%"chk5" + 0] <- %"v61";
    %"v64" = %"pr.2" +p %"pr.9"
    => goto "L51";
  @"L50":
    %"v69" : W = (Cmp Ne L) %"pr.9", #0
    => br %"v69" ? "L65" : "L51";
  @"L65":
    %"v72" = %"v0" +p #40;
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L76";
  @"L76" [%"pr.11" : L = phi("L65" => %"pr.9", "L77" => %"v81"); %"pr.10" : P = phi("L65" => %"v73", "L77" => %"v84"); %"pr.6" : P = phi("L65" => %"pr.2", "L77" => %"v86")]:
    %"v81" : L = Sub %"pr.11", #1;
    %"v82" : W = (Cmp Sge L) %"v81", #0
    => br %"v82" ? "L77" : "L79";
  @"L77":
    %"v84" = %"pr.10" +p #1;
    %"v86" = %"pr.6" +p #1;
    %"chk7" : A = (Check 0 1 Read 1) %"pr.6";
    %"v87" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"chk8" : A = (Check 0 1 Write 1) %"pr.10";
    store Wb [%"chk8" + 0] <- %"v87"
    => goto poll "L76";
  @"L79":
    %"v89" = %"v0" +p #40;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk0", %"v89";
    store.ptr [%"chk9" + 0] <- %"pr.10"
    => goto "L51";
  @"L51" [%"pr.4" : P = phi("L49" => %"v64", "L79" => %"pr.6", "L50" => %"pr.2")]:
    %"v93" : L = Sub %"pr.7", %"pr.9"
    => goto "L22";
  @"L22" [%"pr.8" : L = phi("L51" => %"v93", "L16" => %"pr.7"); %"pr.3" : P = phi("L51" => %"pr.4", "L16" => %"pr.2")]:
    %"v98" : W = (Cmp Eq L) %"pr.8", #0
    => br %"v98" ? "L100" : "L99";
  @"L99":
    %"v102" = %"v0" +p #216;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v102";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v4" : L = Ptoi %"v103";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v105" = %"v103" +p #24;
    %"chk11" : A = (Check 0 8 Read 8) %"v105";
    %"v106" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v109" = %"pr.3" +p #1;
    %"chk12" : A = (Check 0 1 Read 1) %"pr.3";
    %"v110" : W = (RawLoad (LdNarrow Sb) 0) %"chk12";
    %"v111" : W = (Ext Ub) %"v110";
    %"chk13" : F = CheckFunction %"v106";
    rawcall %"v112" : W = %"chk13"(P %"v0", W %"v111");
    %"v114" : W = (Cmp Eq W) %"v112", #4294967295
    => goto "L100";
  @"L100" [%"v116" : W = phi("L22" => #1, "iw_1.join" => %"v114"); %"pr.1" : P = phi("L22" => %"pr.3", "iw_1.join" => %"v109")]:
    => br %"v116" ? "L19" : "L96";
  @"L96":
    %"v119" : L = Sub %"pr.8", #1
    => goto poll "L16";
  @"L19":
    %"v122" : L = Sub %"v4", %"pr.8"
    => ret %"v122"
} }.

Definition hello_image_fn___GI__IO_default_xsgetn : func :=
  ir_fn{ "export" "__GI__IO_default_xsgetn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => goto "L10";
  @"L10" [%"pr.3" : P = phi("start" => %"v2", "L93" => %"pr.4"); %"pr.1" : L = phi("start" => %"v4", "L93" => %"pr.2")]:
    %"v18" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v21" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v23" : L = Ptoi %"v19";
    %"v24" : L = Ptoi %"v22";
    %"v25" : W = (Cmp Ult L) %"v23", %"v24"
    => br %"v25" ? "L14" : "L16";
  @"L14":
    %"v28" = %"v0" +p #16;
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v31" = %"v0" +p #8;
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v33" : L = Ptoi %"v29";
    %"v34" : L = Ptoi %"v32";
    %"v35" : L = Sub %"v33", %"v34";
    %"v41" : W = (Cmp Ugt L) %"v35", %"pr.1"
    => br %"v41" ? "L38" : "L37";
  @"L37":
    => goto "L38";
  @"L38" [%"pr.8" : L = phi("L37" => %"v35", "L14" => %"pr.1")]:
    %"v47" : W = (Cmp Ugt L) %"pr.8", #20
    => br %"v47" ? "L43" : "L44";
  @"L43":
    %"v50" = %"v0" +p #8;
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v53" : P = $"__GI_mempcpy"(P %"pr.3", P %"v51", L %"pr.8");
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v50";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v58" = %"v56" +p %"pr.8";
    %"chk6" : A = (Renew 0 8 Write 8) %"chk0", %"v50";
    store.ptr [%"chk6" + 0] <- %"v58"
    => goto "L45";
  @"L44":
    %"v63" : W = (Cmp Ne L) %"pr.8", #0
    => br %"v63" ? "L59" : "L45";
  @"L59":
    %"v66" = %"v0" +p #8;
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L70";
  @"L70" [%"pr.10" : W = phi("L59" => %"pr.8", "L71" => %"v74"); %"pr.9" : P = phi("L59" => %"v67", "L71" => %"v79"); %"pr.7" : P = phi("L59" => %"pr.3", "L71" => %"v77")]:
    %"v74" : W = Sub %"pr.10", #1;
    %"v75" : W = (Cmp Sge W) %"v74", #0
    => br %"v75" ? "L71" : "L72";
  @"L71":
    %"v77" = %"pr.7" +p #1;
    %"v79" = %"pr.9" +p #1;
    %"chk8" : A = (Check 0 1 Read 1) %"pr.9";
    %"v80" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"chk9" : A = (Check 0 1 Write 1) %"pr.7";
    store Wb [%"chk9" + 0] <- %"v80"
    => goto poll "L70";
  @"L72":
    %"v82" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Write 8) %"chk0", %"v82";
    store.ptr [%"chk10" + 0] <- %"pr.9"
    => goto "L45";
  @"L45" [%"pr.5" : P = phi("L43" => %"v53", "L72" => %"pr.7", "L44" => %"pr.3")]:
    %"v86" : L = Sub %"pr.1", %"pr.8"
    => goto "L16";
  @"L16" [%"pr.4" : P = phi("L45" => %"pr.5", "L10" => %"pr.3"); %"pr.2" : L = phi("L45" => %"v86", "L10" => %"pr.1")]:
    %"v91" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v91" ? "L93" : "L92";
  @"L92":
    call %"v95" : W = $"__GI___underflow"(P %"v0");
    %"v97" : W = (Cmp Eq W) %"v95", #4294967295
    => goto "L93";
  @"L93" [%"v99" : W = phi("L16" => #1, "L92" => %"v97")]:
    => br %"v99" ? "L13" : poll "L10";
  @"L13":
    %"v103" : L = Sub %"v4", %"pr.2"
    => ret %"v103"
} }.
