(** This file defines checked IR from glibc’s `locale/lc-ctype.os` object.
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

Definition fn__nl_postload_ctype : func :=
  ir_fn{ "export" "_nl_postload_ctype"() -> RVoid {
  @"start":
    %"v1" : P = Copy $"_nl_global_locale";
    %"chk0" : A = (Check 0 8 Read 8) %"v1";
    %"v3" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v4" = %"v3" +p #56;
    %"v5" : P = Copy $"_nl_global_locale";
    %"v6" = %"v5" +p #104;
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" = %"v12" +p #256;
    %"chk2" : A = (Check 0 8 Write 8) %"v6";
    store.ptr [%"chk2" + 0] <- %"v13";
    %"v14" : P = Copy $"_nl_global_locale";
    %"v15" = %"v14" +p #112;
    %"v20" = %"v4" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v22" = %"v21" +p #512;
    %"chk4" : A = (Check 0 8 Write 8) %"v15";
    store.ptr [%"chk4" + 0] <- %"v22";
    %"v23" : P = Copy $"_nl_global_locale";
    %"v24" = %"v23" +p #120;
    %"v29" = %"v4" +p #8;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v31" = %"v30" +p #512;
    %"chk6" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk6" + 0] <- %"v31";
    %"v35" : P = Copy $"__libc_tsd_LOCALE";
    %"chk7" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v37" : P = Copy $"_nl_global_locale";
    %"v38" : L = Ptoi %"v36";
    %"v39" : L = Ptoi %"v37";
    %"v40" : W = (Cmp Eq L) %"v38", %"v39"
    => br %"v40" ? "L32" : "L34";
  @"L32":
    %"v41" : P = Copy $"__libc_tsd_CTYPE_B";
    %"v42" : P = Copy $"_nl_global_locale";
    %"v43" = %"v42" +p #104;
    %"chk8" : A = (Check 0 8 Read 8) %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Write 8) %"v41";
    store.ptr [%"chk9" + 0] <- %"v44";
    %"v45" : P = Copy $"__libc_tsd_CTYPE_TOUPPER";
    %"v46" : P = Copy $"_nl_global_locale";
    %"v47" = %"v46" +p #120;
    %"chk10" : A = (Check 0 8 Read 8) %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Write 8) %"v45";
    store.ptr [%"chk11" + 0] <- %"v48";
    %"v49" : P = Copy $"__libc_tsd_CTYPE_TOLOWER";
    %"v50" : P = Copy $"_nl_global_locale";
    %"v51" = %"v50" +p #112;
    %"chk12" : A = (Check 0 8 Read 8) %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk13" + 0] <- %"v52"
    => goto "L34";
  @"L34":
    code ((app ir[ %"v53" : P = Copy $"__ctype_b";
      %"v54" : P = Copy $"__libc_tsd_LOCALE";
      %"chk14" : A = (Check 0 8 Read 8) %"v54";
      %"v55" : P = (RawLoadPointer 0 load_effects) %"chk14";
      %"chk15" : A = (Check 0 8 Read 8) %"v55";
      %"v57" : P = (RawLoadPointer 0 load_effects) %"chk15";
      %"v58" = %"v57" +p #56;
      %"chk16" : A = (Check 0 8 Read 8) %"v58";
      %"v63" : P = (RawLoadPointer 0 load_effects) %"chk16";
      %"v64" = %"v63" +p #256;
      %"chk17" : A = (Check 0 8 Write 8) %"v53";
      store.ptr [%"chk17" + 0] <- %"v64";
      %"v65" : P = Copy $"__ctype_toupper";
      %"v66" : P = Copy $"__libc_tsd_LOCALE";
      %"chk18" : A = (Check 0 8 Read 8) %"v66";
      %"v67" : P = (RawLoadPointer 0 load_effects) %"chk18";
      %"chk19" : A = (Check 0 8 Read 8) %"v67";
      %"v69" : P = (RawLoadPointer 0 load_effects) %"chk19";
      %"v70" = %"v69" +p #56;
      %"v74" = %"v70" +p #8;
      %"chk20" : A = (Check 0 8 Read 8) %"v74";
      %"v75" : P = (RawLoadPointer 0 load_effects) %"chk20";
      %"v76" = %"v75" +p #512;
      %"chk21" : A = (Check 0 8 Write 8) %"v65";
      store.ptr [%"chk21" + 0] <- %"v76";
      %"v77" : P = Copy $"__ctype_tolower";
      %"v78" : P = Copy $"__libc_tsd_LOCALE";
      %"chk22" : A = (Check 0 8 Read 8) %"v78";
      %"v79" : P = (RawLoadPointer 0 load_effects) %"chk22";
      %"chk23" : A = (Check 0 8 Read 8) %"v79";
      %"v81" : P = (RawLoadPointer 0 load_effects) %"chk23";
      %"v82" = %"v81" +p #56;
      %"v86" = %"v82" +p #24;
      %"chk24" : A = (Check 0 8 Read 8) %"v86";
      %"v87" : P = (RawLoadPointer 0 load_effects) %"chk24";
      %"v88" = %"v87" +p #512;
      %"chk25" : A = (Check 0 8 Write 8) %"v77"] ir[ store.ptr [%"chk25" + 0] <- %"v88";
      %"v89" : P = Copy $"__ctype32_b";
      %"v90" : P = Copy $"__libc_tsd_LOCALE";
      %"chk26" : A = (Check 0 8 Read 8) %"v90";
      %"v91" : P = (RawLoadPointer 0 load_effects) %"chk26";
      %"chk27" : A = (Check 0 8 Read 8) %"v91";
      %"v93" : P = (RawLoadPointer 0 load_effects) %"chk27";
      %"v94" = %"v93" +p #56;
      %"v98" = %"v94" +p #40;
      %"chk28" : A = (Check 0 8 Read 8) %"v98";
      %"v99" : P = (RawLoadPointer 0 load_effects) %"chk28";
      %"chk29" : A = (Check 0 8 Write 8) %"v89";
      store.ptr [%"chk29" + 0] <- %"v99";
      %"v101" : P = Copy $"__ctype32_toupper";
      %"v102" : P = Copy $"__libc_tsd_LOCALE";
      %"chk30" : A = (Check 0 8 Read 8) %"v102";
      %"v103" : P = (RawLoadPointer 0 load_effects) %"chk30";
      %"chk31" : A = (Check 0 8 Read 8) %"v103";
      %"v105" : P = (RawLoadPointer 0 load_effects) %"chk31";
      %"v106" = %"v105" +p #56;
      %"v110" = %"v106" +p #120;
      %"chk32" : A = (Check 0 8 Read 8) %"v110";
      %"v111" : P = (RawLoadPointer 0 load_effects) %"chk32";
      %"chk33" : A = (Check 0 8 Write 8) %"v101";
      store.ptr [%"chk33" + 0] <- %"v111";
      %"v113" : P = Copy $"__ctype32_tolower";
      %"v114" : P = Copy $"__libc_tsd_LOCALE";
      %"chk34" : A = (Check 0 8 Read 8) %"v114";
      %"v115" : P = (RawLoadPointer 0 load_effects) %"chk34";
      %"chk35" : A = (Check 0 8 Read 8) %"v115";
      %"v117" : P = (RawLoadPointer 0 load_effects) %"chk35";
      %"v118" = %"v117" +p #56;
      %"v122" = %"v118" +p #128;
      %"chk36" : A = (Check 0 8 Read 8) %"v122";
      %"v123" : P = (RawLoadPointer 0 load_effects) %"chk36";
      %"chk37" : A = (Check 0 8 Write 8) %"v113";
      store.ptr [%"chk37" + 0] <- %"v123"]))
    => ret void
} }.
