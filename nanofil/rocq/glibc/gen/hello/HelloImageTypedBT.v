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

Definition hello_image_fn___btowc : func :=
  ir_fn{ "export" "__btowc"(W %"v0") -> (RClass W) {
  @"start":
    %"v82" : P = (Alloc 4) #4;
    %"v83" : P = (Alloc 8) #48;
    %"v84" : P = (Alloc 4) #1;
    %"v85" : P = (Alloc 8) #8;
    %"v86" : P = (Alloc 8) #8;
    %"v9" : W = (Cmp Slt W) %"v0", #4294967168
    => br %"v9" ? "L11" : "L10";
  @"L10":
    %"v15" : W = (Cmp Sgt W) %"v0", #255
    => goto "L11";
  @"L11" [%"v17" : W = phi("start" => #1, "L10" => %"v15")]:
    => br %"v17" ? "L19" : "L18";
  @"L18":
    %"v22" : W = (Cmp Eq W) %"v0", #4294967295
    => goto "L19";
  @"L19" [%"v24" : W = phi("L11" => #1, "L18" => %"v22")]:
    => br %"v24" ? "L3" : "L5";
  @"L3":
    => ret #4294967295;
  @"L5":
    %"v31" : W = And %"v0", #4294967168;
    %"v32" : W = (Cmp Eq W) %"v31", #0
    => br %"v32" ? "L26" : "L28";
  @"L26":
    => ret %"v0";
  @"L28":
    %"v35" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v36";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v4" = %"v38" +p #32;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v4";
    %"iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v5";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v11" : L = Ptoi %"iw_1.v10";
    %"iw_1.v12" : L = Ptoi #0;
    %"iw_1.v13" : W = (Cmp Eq L) %"iw_1.v11", %"iw_1.v12"
    => br %"iw_1.v13" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    call void $"__wcsmbs_load_conv"(P %"v38")
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk3", %"iw_1.v5";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v16";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v43" = %"v42" +p #48;
    %"chk6" : A = (Check 0 8 Read 8) %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk8" : A = (Check 0 8 Read 8) %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v51" : L = Ptoi %"v50";
    %"v53" : W = (Cmp Ne L) %"v51", %"iw_1.v12"
    => br %"v53" ? "L47" : "L46";
  @"L46":
    => goto "L47";
  @"L47":
    %"v59" = %"iw_1.v16" +p #8;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 1) %"chk5", %"v59";
    %"v60" : L = (RawLoad LdL 0) %"chk9";
    %"v61" : W = (Cmp Eq L) %"v60", #1
    => br %"v61" ? "L64" : "L65";
  @"L64":
    %"v67" : L = Ptoi %"v44";
    %"v69" : W = (Cmp Ne L) %"v67", %"iw_1.v12"
    => goto "L65";
  @"L65" [%"v73" : W = phi("L47" => #0, "L64" => %"v69")]:
    => br %"v73" ? "iw_2.join" : "L56";
  @"iw_2.join":
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v79" : W = (Ext Ub) %"v0";
    %"chk11" : F = CheckFunction %"v44";
    rawcall %"v80" : W = %"chk11"(P %"v77", W %"v79")
    => ret %"v80";
  @"L56":
    %"chk12" : A = (Check 0 8 Write 8) %"v85";
    store.ptr [%"chk12" + 0] <- %"v84";
    %"chk13" : A = (Check 0 8 Write 8) %"v83";
    store.ptr [%"chk13" + 0] <- %"v82";
    %"v88" = %"v83" +p #8;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk13", %"v83";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v90" = %"v89" +p #4;
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk13", %"v88";
    store.ptr [%"chk15" + 0] <- %"v90";
    %"v91" = %"v83" +p #20;
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"v91";
    store Ww [%"chk16" + 0] <- #0;
    %"v92" = %"v83" +p #24;
    %"chk17" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"v92";
    store Ww [%"chk17" + 0] <- #1;
    %"v93" = %"v83" +p #16;
    %"chk18" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"v93";
    store Ww [%"chk18" + 0] <- #1;
    %"v94" = %"v83" +p #32;
    %"v95" = %"v83" +p #40;
    %"chk19" : A = (HalfCheck Upper 0 8 Write 8) %"chk13", %"v94";
    store.ptr [%"chk19" + 0] <- %"v95";
    call %"v97" : P = $"__GI_memset"(P %"v95", W #0, L #8);
    %"v100" : W = (Ext Ub) %"v0";
    %"chk20" : A = (Check 0 1 Write 1) %"v84";
    store Wb [%"chk20" + 0] <- %"v100";
    %"chk21" : A = (Renew 0 8 Read 8) %"chk5", %"iw_1.v16";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v104" = %"v103" +p #40;
    %"chk22" : A = (Check 0 8 Read 8) %"v104";
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 8 Read 8) %"v110";
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v112" : L = Ptoi %"v111";
    %"v114" : W = (Cmp Ne L) %"v112", %"iw_1.v12"
    => br %"v114" ? "iw_3.join" : "L107";
  @"L107":
    => goto "iw_3.join";
  @"iw_3.join":
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk26" : A = (Renew 0 8 Read 8) %"chk12", %"v85";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v121" = %"v120" +p #1;
    %"chk27" : F = CheckFunction %"v105";
    rawcall %"v122" : W = %"chk27"(P %"v119", P %"v83", P %"v85", P %"v121", P #0, P %"v86", W #0, W #1);
    %"v127" : W = (Cmp Ne W) %"v122", #0
    => br %"v127" ? "L128" : "L129";
  @"L128":
    %"v131" : W = (Cmp Ne W) %"v122", #5
    => goto "L129";
  @"L129" [%"v133" : W = phi("iw_3.join" => #0, "L128" => %"v131")]:
    => br %"v133" ? "L134" : "L135";
  @"L134":
    %"v137" : W = (Cmp Ne W) %"v122", #4
    => goto "L135";
  @"L135" [%"v139" : W = phi("L129" => #0, "L134" => %"v137")]:
    => br %"v139" ? "L123" : "L125";
  @"L123":
    %"chk28" : A = (Check 0 4 Write 1) %"v82";
    store Ww [%"chk28" + 0] <- #(-1)
    => goto "L125";
  @"L125":
    %"chk29" : A = (Check 0 4 Read 1) %"v82";
    %"v140" : W = (RawLoad (LdNarrow Sw) 0) %"chk29"
    => ret %"v140"
} }.
