(** This file defines checked IR from glibc’s `libio/iofwide.os` object.
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

Definition fn__IO_fwide : func :=
  ir_fn{ "export" "_IO_fwide"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v73" : P = (Alloc 8) #32;
    %"v8" : W = (Cmp Slt W) %"v2", #0
    => br %"v8" ? "L6" : "L5";
  @"L5":
    %"v14" : W = (Cmp Eq W) %"v2", #0
    => br %"v14" ? "L6" : "L11";
  @"L11":
    => goto "L6";
  @"L6" [%"v16" : W = phi("start" => #4294967295, "L11" => #1, "L5" => #0)]:
    %"v21" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v23" : W = (Cmp Ne W) %"v22", #0
    => br %"v23" ? "L25" : "L24";
  @"L24":
    %"v27" : W = (Cmp Eq W) %"v16", #0
    => goto "L25";
  @"L25" [%"v29" : W = phi("L6" => #1, "L24" => %"v27")]:
    => br %"v29" ? "L17" : "L19";
  @"L17":
    %"v31" = %"v0" +p #192;
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret %"v32";
  @"L19":
    %"v38" : W = (Cmp Sgt W) %"v16", #0
    => br %"v38" ? "L34" : "L36";
  @"L34":
    %"v41" = %"v0" +p #152;
    %"v43" = %"v0" +p #160;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v45" = %"v44" +p #104;
    %"chk3" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v41";
    store.ptr [%"chk3" + 0] <- %"v45";
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v43";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v52" = %"v51" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Write 8) %"v48";
    store.ptr [%"chk7" + 0] <- %"v53";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"v43";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v57" = %"v56" +p #32;
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v61" = %"v60" +p #24;
    %"chk10" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Write 8) %"v57";
    store.ptr [%"chk11" + 0] <- %"v62";
    %"chk12" : A = (Renew 0 8 Read 8) %"chk2", %"v43";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v66" = %"v65" +p #88;
    call %"v67" : P = $"__GI_memset"(P %"v66", W #0, L #8);
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"v43";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v71" = %"v70" +p #96;
    call %"v72" : P = $"__GI_memset"(P %"v71", W #0, L #8);
    call void $"__wcsmbs_clone_conv"(P %"v73");
    %"v77" = %"v73" +p #8;
    %"chk14" : A = (Check 0 8 Read 1) %"v77";
    %"v78" : L = (RawLoad LdL 0) %"chk14";
    %"v79" : W = (Cmp Eq L) %"v78", #1
    => br %"v79" ? "L76" : "L75";
  @"L75":
    %"v80" : P = Copy $"glibc_iofwide#str.288";
    %"v81" : P = Copy $"glibc_iofwide#str.289";
    %"v82" : P = Copy $"glibc_iofwide#str.290";
    call void $"__libc_assert_fail"(P %"v80", P %"v81", W #80, P %"v82")
    => goto "L76";
  @"L76":
    %"v86" = %"v73" +p #24;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 1) %"chk14", %"v86";
    %"v87" : L = (RawLoad LdL 0) %"chk15";
    %"v88" : W = (Cmp Eq L) %"v87", #1
    => br %"v88" ? "L85" : "L84";
  @"L84":
    %"v89" : P = Copy $"glibc_iofwide#str.291";
    %"v90" : P = Copy $"glibc_iofwide#str.289";
    %"v91" : P = Copy $"glibc_iofwide#str.290";
    call void $"__libc_assert_fail"(P %"v89", P %"v90", W #81, P %"v91")
    => goto "L85";
  @"L85":
    %"chk16" : A = (HalfCheck Lower 0 8 Read 8) %"chk14", %"v73";
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 8 Write 8) %"v45";
    store.ptr [%"chk17" + 0] <- %"v93";
    %"v95" = %"v45" +p #8;
    %"v96" = %"v95" +p #20;
    %"chk18" : A = (HalfCheck Upper 0 4 Write 1) %"chk17", %"v96";
    store Ww [%"chk18" + 0] <- #0;
    %"v99" = %"v95" +p #24;
    %"chk19" : A = (HalfCheck Upper 0 4 Write 1) %"chk18", %"v99";
    store Ww [%"chk19" + 0] <- #1;
    %"v102" = %"v95" +p #16;
    %"chk20" : A = (HalfCheck Lower 0 4 Write 1) %"chk18", %"v102";
    store Ww [%"chk20" + 0] <- #1;
    %"v105" = %"v95" +p #32;
    %"v107" = %"v0" +p #160;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk2", %"v107";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v109" = %"v108" +p #88;
    %"chk22" : A = (HalfCheck Upper 0 8 Write 8) %"chk18", %"v105";
    store.ptr [%"chk22" + 0] <- %"v109";
    %"v111" = %"v45" +p #56;
    %"v112" = %"v73" +p #16;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk14", %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (HalfCheck Upper 0 8 Write 8) %"chk17", %"v111";
    store.ptr [%"chk24" + 0] <- %"v113";
    %"v116" = %"v111" +p #8;
    %"v117" = %"v116" +p #20;
    %"chk25" : A = (HalfCheck Upper 0 4 Write 1) %"chk24", %"v117";
    store Ww [%"chk25" + 0] <- #0;
    %"v121" = %"v116" +p #24;
    %"chk26" : A = (HalfCheck Upper 0 4 Write 1) %"chk25", %"v121";
    store Ww [%"chk26" + 0] <- #1;
    %"v125" = %"v116" +p #16;
    %"chk27" : A = (HalfCheck Lower 0 4 Write 1) %"chk25", %"v125";
    store Ww [%"chk27" + 0] <- #9;
    %"v130" = %"v116" +p #32;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk2", %"v107";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v134" = %"v133" +p #88;
    %"chk29" : A = (HalfCheck Upper 0 8 Write 8) %"chk25", %"v130";
    store.ptr [%"chk29" + 0] <- %"v134";
    %"v136" = %"v0" +p #216;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk2", %"v107";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v140" = %"v139" +p #224;
    %"chk31" : A = (Check 0 8 Read 8) %"v140";
    %"v141" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v136";
    store.ptr [%"chk32" + 0] <- %"v141"
    => goto "L36";
  @"L36":
    %"v143" = %"v0" +p #192;
    %"chk33" : A = (Renew 0 4 Write 1) %"chk0", %"v143";
    store Ww [%"chk33" + 0] <- %"v16"
    => ret %"v16"
} }.

Definition fn___libio_codecvt_encoding : func :=
  ir_fn{ "export" "__libio_codecvt_encoding"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v7" = %"v6" +p #88;
    %"chk1" : A = (Check 0 4 Read 1) %"v7";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => br %"v8" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v16" = %"v15" +p #72;
    %"chk3" : A = (Check 0 4 Read 1) %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v20" = %"v19" +p #76;
    %"chk5" : A = (Check 0 4 Read 1) %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v22" : W = (Cmp Ne W) %"v17", %"v21"
    => br %"v22" ? "L11" : "L13";
  @"L11":
    => ret #0;
  @"L13":
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v26" = %"v25" +p #72;
    %"chk7" : A = (Check 0 4 Read 1) %"v26";
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk7"
    => ret %"v27"
} }.

Definition fn___libio_codecvt_in : func :=
  ir_fn{ "export" "__libio_codecvt_in"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", P %"v12", P %"v14") -> (RClass W) {
  @"start":
    %"v21" : P = (Alloc 8) #8;
    %"v22" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Write 8) %"v22";
    store.ptr [%"chk1" + 0] <- %"v4";
    %"v25" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v25";
    store.ptr [%"chk2" + 0] <- %"v10";
    %"v29" = %"v25" +p #8;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v29";
    store.ptr [%"chk3" + 0] <- %"v12";
    %"v33" = %"v25" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v33";
    store.ptr [%"chk4" + 0] <- %"v2";
    %"v37" = %"v19" +p #40;
    %"chk5" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v19";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v44" : L = Ptoi %"v43";
    %"v45" : L = Ptoi #0;
    %"v46" : W = (Cmp Ne L) %"v44", %"v45"
    => br %"v46" ? "iw_1.join" : "L40";
  @"L40":
    => goto "iw_1.join";
  @"iw_1.join":
    %"v52" = %"v0" +p #8;
    %"chk7" : F = CheckFunction %"v38";
    rawcall %"v54" : W = %"chk7"(P %"v19", P %"v52", P %"v22", P %"v6", P #0, P %"v21", W #0, W #0);
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v22";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk9" + 0] <- %"v56";
    %"chk10" : A = (Renew 0 8 Read 8) %"chk2", %"v52";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Write 8) %"v14";
    store.ptr [%"chk11" + 0] <- %"v60";
    %"v70" : W = (Cmp Eq W) %"v54", #0
    => br %"v70" ? "L63" : "L71";
  @"L71":
    %"v72" : W = (Cmp Eq W) %"v54", #4
    => br %"v72" ? "L63" : "L73";
  @"L73":
    %"v74" : W = (Cmp Eq W) %"v54", #5
    => br %"v74" ? "L63" : "L75";
  @"L75":
    %"v76" : W = (Cmp Eq W) %"v54", #7
    => br %"v76" ? "L63" : "L77";
  @"L77":
    => goto "L63";
  @"L63" [%"pr.1" : W = phi("L71" => #0, "iw_1.join" => #0, "L75" => #1, "L73" => #1, "L77" => #2)]:
    => ret %"pr.1"
} }.

Definition fn___libio_codecvt_length : func :=
  ir_fn{ "export" "__libio_codecvt_length"(P %"v0", P %"v2", P %"v4", P %"v6", L %"v8") -> (RClass W) {
  @"start":
    %"v11" : P = (Alloc 8) #8;
    %"v19" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v11";
    store.ptr [%"chk0" + 0] <- %"v4";
    %"v14" : L = Shl %"v8", #2;
    %"v15" : P = (Alloc 4) %"v14";
    %"chk1" : A = (Check 0 8 Read 8) %"v0";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v21" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk1", %"v21";
    store.ptr [%"chk2" + 0] <- %"v15";
    %"v24" = %"v21" +p #8;
    %"v27" = %"v15" +p %"v14";
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v24";
    store.ptr [%"chk3" + 0] <- %"v27";
    %"v30" = %"v21" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v30";
    store.ptr [%"chk4" + 0] <- %"v2";
    %"v34" = %"v18" +p #40;
    %"chk5" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v18";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v41" : L = Ptoi %"v40";
    %"v42" : L = Ptoi #0;
    %"v43" : W = (Cmp Ne L) %"v41", %"v42"
    => br %"v43" ? "iw_1.join" : "L37";
  @"L37":
    => goto "iw_1.join";
  @"iw_1.join":
    %"v49" = %"v0" +p #8;
    %"chk7" : F = CheckFunction %"v35";
    rawcall %"v51" : W = %"chk7"(P %"v18", P %"v49", P %"v11", P %"v6", P #0, P %"v19", W #0, W #0);
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v11";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v54" : L = Ptoi %"v52";
    %"v55" : L = Ptoi %"v4";
    %"v56" : L = Sub %"v54", %"v55";
    %"v57" : W = Copy %"v56"
    => ret %"v57"
} }.

Definition fn___libio_codecvt_out : func :=
  ir_fn{ "export" "__libio_codecvt_out"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", P %"v12", P %"v14") -> (RClass W) {
  @"start":
    %"v22" : P = (Alloc 8) #8;
    %"v23" : P = (Alloc 8) #8;
    %"v19" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Write 8) %"v23";
    store.ptr [%"chk1" + 0] <- %"v4";
    %"v27" = %"v19" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v27";
    store.ptr [%"chk2" + 0] <- %"v10";
    %"v32" = %"v27" +p #8;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v32";
    store.ptr [%"chk3" + 0] <- %"v12";
    %"v37" = %"v27" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v37";
    store.ptr [%"chk4" + 0] <- %"v2";
    %"v41" = %"v20" +p #40;
    %"chk5" : A = (Check 0 8 Read 8) %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v20";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v48" : L = Ptoi %"v47";
    %"v49" : L = Ptoi #0;
    %"v50" : W = (Cmp Ne L) %"v48", %"v49"
    => br %"v50" ? "iw_1.join" : "L44";
  @"L44":
    => goto "iw_1.join";
  @"iw_1.join":
    %"v56" = %"v0" +p #56;
    %"v57" = %"v56" +p #8;
    %"chk7" : F = CheckFunction %"v42";
    rawcall %"v59" : W = %"chk7"(P %"v20", P %"v57", P %"v23", P %"v6", P #0, P %"v22", W #0, W #0);
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v23";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk9" + 0] <- %"v61";
    %"chk10" : A = (Renew 0 8 Read 8) %"chk2", %"v57";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Write 8) %"v14";
    store.ptr [%"chk11" + 0] <- %"v66";
    %"v76" : W = (Cmp Eq W) %"v59", #0
    => br %"v76" ? "L69" : "L77";
  @"L77":
    %"v78" : W = (Cmp Eq W) %"v59", #4
    => br %"v78" ? "L69" : "L79";
  @"L79":
    %"v80" : W = (Cmp Eq W) %"v59", #5
    => br %"v80" ? "L69" : "L81";
  @"L81":
    %"v82" : W = (Cmp Eq W) %"v59", #7
    => br %"v82" ? "L69" : "L83";
  @"L83":
    => goto "L69";
  @"L69" [%"pr.1" : W = phi("L77" => #0, "iw_1.join" => #0, "L81" => #1, "L79" => #1, "L83" => #2)]:
    => ret %"pr.1"
} }.

Definition item_glibc_iofwide'23str'2e288 : item :=
  (IData (a "glibc_iofwide#str.288") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 99); (Item Wb 116); (Item Wb 115); (Item Wb 46); (Item Wb 116); (Item Wb 111); (Item Wb 119); (Item Wb 99); (Item Wb 95); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 49); (Item Wb 0)]).

Definition item_glibc_iofwide'23str'2e289 : item :=
  (IData (a "glibc_iofwide#str.289") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 111); (Item Wb 102); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_iofwide'23str'2e290 : item :=
  (IData (a "glibc_iofwide#str.290") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 102); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_iofwide'23str'2e291 : item :=
  (IData (a "glibc_iofwide#str.291") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 99); (Item Wb 116); (Item Wb 115); (Item Wb 46); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 98); (Item Wb 95); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 49); (Item Wb 0)]).
