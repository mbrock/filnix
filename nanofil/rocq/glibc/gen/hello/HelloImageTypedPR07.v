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

Definition hello_image_fn_glibc_vfwprintf_internal'23printf_unknown : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#printf_unknown"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v4" : P = (Alloc 4) #48;
    %"v8" = %"v4" +p #48;
    %"iw_1.v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v11" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v13" : L = Ptoi %"iw_1.v9";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Ne L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L5";
  @"iw_1.L4":
    %"iw_1.v17" = %"v0" +p #8;
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v19" = %"iw_1.v18" +p #4;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"iw_1.v17";
    store.ptr [%"chk3" + 0] <- %"iw_1.v19";
    %"chk4" : A = (Check 0 4 Write 1) %"iw_1.v18";
    store Ww [%"chk4" + 0] <- #37
    => goto "iw_1.join";
  @"iw_1.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #37)
    => goto "iw_1.join";
  @"iw_1.join":
    %"v15" = %"v2" +p #12;
    %"chk5" : A = (Check 0 4 Read 1) %"v15";
    %"v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v17" : W = Shl %"v16", #28;
    %"v18" : W = Shr %"v17", #31
    => br %"v18" ? "iw_2.start" : "L13";
  @"iw_2.start":
    %"iw_2.v8" = %"v0" +p #8;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"iw_2.v8";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_2.v11" = %"v0" +p #16;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_2.v13" : L = Ptoi %"iw_2.v9";
    %"iw_2.v14" : L = Ptoi %"iw_2.v12";
    %"iw_2.v15" : W = (Cmp Ne L) %"iw_2.v13", %"iw_2.v14"
    => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
  @"iw_2.L4":
    %"iw_2.v17" = %"v0" +p #8;
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_2.v19" = %"iw_2.v18" +p #4;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk0", %"iw_2.v17";
    store.ptr [%"chk9" + 0] <- %"iw_2.v19";
    %"chk10" : A = (Check 0 4 Write 1) %"iw_2.v18";
    store Ww [%"chk10" + 0] <- #35
    => goto "L13";
  @"iw_2.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #35)
    => goto "L13";
  @"L13":
    %"v24" = %"v2" +p #12;
    %"chk11" : A = (Renew 0 4 Read 1) %"chk5", %"v24";
    %"v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v26" : W = Shl %"v25", #24;
    %"v27" : W = Shr %"v26", #31
    => br %"v27" ? "iw_3.start" : "L22";
  @"iw_3.start":
    %"iw_3.v8" = %"v0" +p #8;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"iw_3.v8";
    %"iw_3.v9" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_3.v11" = %"v0" +p #16;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk1", %"iw_3.v11";
    %"iw_3.v12" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_3.v13" : L = Ptoi %"iw_3.v9";
    %"iw_3.v14" : L = Ptoi %"iw_3.v12";
    %"iw_3.v15" : W = (Cmp Ne L) %"iw_3.v13", %"iw_3.v14"
    => br %"iw_3.v15" ? "iw_3.L4" : "iw_3.L5";
  @"iw_3.L4":
    %"iw_3.v17" = %"v0" +p #8;
    %"iw_3.v18" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_3.v19" = %"iw_3.v18" +p #4;
    %"chk15" : A = (Renew 0 8 Write 8) %"chk0", %"iw_3.v17";
    store.ptr [%"chk15" + 0] <- %"iw_3.v19";
    %"chk16" : A = (Check 0 4 Write 1) %"iw_3.v18";
    store Ww [%"chk16" + 0] <- #39
    => goto "L22";
  @"iw_3.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #39)
    => goto "L22";
  @"L22":
    %"v33" = %"v2" +p #12;
    %"chk17" : A = (Renew 0 4 Read 1) %"chk5", %"v33";
    %"v34" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v35" : W = Shl %"v34", #25;
    %"v36" : W = Shr %"v35", #31
    => br %"v36" ? "iw_4.start" : "L30";
  @"iw_4.start":
    %"iw_4.v8" = %"v0" +p #8;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"iw_4.v8";
    %"iw_4.v9" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"iw_4.v11" = %"v0" +p #16;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v11";
    %"iw_4.v12" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"iw_4.v13" : L = Ptoi %"iw_4.v9";
    %"iw_4.v14" : L = Ptoi %"iw_4.v12";
    %"iw_4.v15" : W = (Cmp Ne L) %"iw_4.v13", %"iw_4.v14"
    => br %"iw_4.v15" ? "iw_4.L4" : "iw_4.L5";
  @"iw_4.L4":
    %"iw_4.v17" = %"v0" +p #8;
    %"iw_4.v18" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"iw_4.v19" = %"iw_4.v18" +p #4;
    %"chk21" : A = (Renew 0 8 Write 8) %"chk0", %"iw_4.v17";
    store.ptr [%"chk21" + 0] <- %"iw_4.v19";
    %"chk22" : A = (Check 0 4 Write 1) %"iw_4.v18";
    store Ww [%"chk22" + 0] <- #43
    => goto "L31";
  @"iw_4.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #43)
    => goto "L31";
  @"L30":
    %"v42" = %"v2" +p #12;
    %"v43" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v44" : W = Shl %"v43", #27;
    %"v45" : W = Shr %"v44", #31
    => br %"v45" ? "iw_5.start" : "L31";
  @"iw_5.start":
    %"iw_5.v8" = %"v0" +p #8;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"iw_5.v8";
    %"iw_5.v9" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_5.v11" = %"v0" +p #16;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk1", %"iw_5.v11";
    %"iw_5.v12" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_5.v13" : L = Ptoi %"iw_5.v9";
    %"iw_5.v14" : L = Ptoi %"iw_5.v12";
    %"iw_5.v15" : W = (Cmp Ne L) %"iw_5.v13", %"iw_5.v14"
    => br %"iw_5.v15" ? "iw_5.L4" : "iw_5.L5";
  @"iw_5.L4":
    %"iw_5.v17" = %"v0" +p #8;
    %"iw_5.v18" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_5.v19" = %"iw_5.v18" +p #4;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk0", %"iw_5.v17";
    store.ptr [%"chk27" + 0] <- %"iw_5.v19";
    %"chk28" : A = (Check 0 4 Write 1) %"iw_5.v18";
    store Ww [%"chk28" + 0] <- #32
    => goto "L31";
  @"iw_5.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #32)
    => goto "L31";
  @"L31":
    %"v51" = %"v2" +p #12;
    %"chk29" : A = (Renew 0 4 Read 1) %"chk5", %"v51";
    %"v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v53" : W = Shl %"v52", #26;
    %"v54" : W = Shr %"v53", #31
    => br %"v54" ? "iw_6.start" : "L49";
  @"iw_6.start":
    %"iw_6.v8" = %"v0" +p #8;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk0", %"iw_6.v8";
    %"iw_6.v9" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_6.v11" = %"v0" +p #16;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk1", %"iw_6.v11";
    %"iw_6.v12" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_6.v13" : L = Ptoi %"iw_6.v9";
    %"iw_6.v14" : L = Ptoi %"iw_6.v12";
    %"iw_6.v15" : W = (Cmp Ne L) %"iw_6.v13", %"iw_6.v14"
    => br %"iw_6.v15" ? "iw_6.L4" : "iw_6.L5";
  @"iw_6.L4":
    %"iw_6.v17" = %"v0" +p #8;
    %"iw_6.v18" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_6.v19" = %"iw_6.v18" +p #4;
    %"chk33" : A = (Renew 0 8 Write 8) %"chk0", %"iw_6.v17";
    store.ptr [%"chk33" + 0] <- %"iw_6.v19";
    %"chk34" : A = (Check 0 4 Write 1) %"iw_6.v18";
    store Ww [%"chk34" + 0] <- #45
    => goto "L49";
  @"iw_6.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #45)
    => goto "L49";
  @"L49":
    %"v60" = %"v2" +p #16;
    %"chk35" : A = (HalfCheck Upper 0 4 Read 1) %"chk5", %"v60";
    %"v61" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v62" : W = (Cmp Eq W) %"v61", #48
    => br %"v62" ? "iw_7.start" : "L58";
  @"iw_7.start":
    %"iw_7.v8" = %"v0" +p #8;
    %"chk36" : A = (Renew 0 8 Read 8) %"chk0", %"iw_7.v8";
    %"iw_7.v9" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"iw_7.v11" = %"v0" +p #16;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk1", %"iw_7.v11";
    %"iw_7.v12" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_7.v13" : L = Ptoi %"iw_7.v9";
    %"iw_7.v14" : L = Ptoi %"iw_7.v12";
    %"iw_7.v15" : W = (Cmp Ne L) %"iw_7.v13", %"iw_7.v14"
    => br %"iw_7.v15" ? "iw_7.L4" : "iw_7.L5";
  @"iw_7.L4":
    %"iw_7.v17" = %"v0" +p #8;
    %"iw_7.v18" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"iw_7.v19" = %"iw_7.v18" +p #4;
    %"chk39" : A = (Renew 0 8 Write 8) %"chk0", %"iw_7.v17";
    store.ptr [%"chk39" + 0] <- %"iw_7.v19";
    %"chk40" : A = (Check 0 4 Write 1) %"iw_7.v18";
    store Ww [%"chk40" + 0] <- #48
    => goto "L58";
  @"iw_7.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W #48)
    => goto "L58";
  @"L58":
    %"v68" = %"v2" +p #12;
    %"chk41" : A = (Renew 0 4 Read 1) %"chk5", %"v68";
    %"v69" : W = (RawLoad (LdNarrow Uw) 0) %"chk41";
    %"v70" : W = Shl %"v69", #20;
    %"v71" : W = Shr %"v70", #31
    => br %"v71" ? "L64" : "L66";
  @"L64":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #73)
    => goto "L66";
  @"L66":
    %"v77" = %"v2" +p #4;
    %"chk42" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v77";
    %"v78" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v79" : W = (Cmp Ne W) %"v78", #0
    => br %"v79" ? "L73" : "L75";
  @"L73":
    %"v81" = %"v2" +p #4;
    %"v82" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v83" : L = (Ext Sw) %"v82";
    %"iw_8.v14" : P = Copy $"_itowa_lower_digits"
    => goto "iw_8.L22";
  @"iw_8.L22" [%"iw_8.pr.6" : P = phi("iw_8.L22" => %"iw_8.v26", "L73" => %"v8"); %"iw_8.pr.1" : L = phi("iw_8.L22" => %"iw_8.v34", "L73" => %"v83")]:
    (Flight (a "iw_8.v26") Sub [(FAddress (t "iw_8.pr.6")); (FValue (Const 4))] (LowerOf (t "iw_8.pr.6")));
    %"iw_8.v29" : L = Urem %"iw_8.pr.1", #10;
    %"iw_8.v30" : L = Shl %"iw_8.v29", #2;
    %"iw_8.v31" = %"iw_8.v14" +p %"iw_8.v30";
    %"chk44" : A = (Check 0 4 Read 1) %"iw_8.v31";
    %"iw_8.v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"chk45" : A = (Check 0 4 Write 1) %"iw_8.v26";
    store Ww [%"chk45" + 0] <- %"iw_8.v32";
    %"iw_8.v34" : L = Udiv %"iw_8.pr.1", #10;
    %"iw_8.v35" : W = (Cmp Ne L) %"iw_8.v34", #0
    => br %"iw_8.v35" ? poll "iw_8.L22" : "L86";
  @"L86" [%"pr.2" : P = phi("L87" => %"v96", "iw_8.L22" => %"iw_8.v26")]:
    %"v91" : L = Ptoi %"pr.2";
    %"v92" : L = Ptoi %"v8";
    %"v93" : W = (Cmp Ult L) %"v91", %"v92"
    => br %"v93" ? "L87" : "L75";
  @"L87":
    %"v96" = %"pr.2" +p #4;
    %"chk46" : A = (Check 0 4 Read 1) %"pr.2";
    %"v97" : W = (RawLoad (LdNarrow Sw) 0) %"chk46";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v97")
    => goto poll "L86";
  @"L75":
    %"chk47" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v2";
    %"v102" : W = (RawLoad (LdNarrow Sw) 0) %"chk47";
    %"v104" : W = (Cmp Ne W) %"v102", #4294967295
    => br %"v104" ? "L98" : "L100";
  @"L98":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #46);
    %"chk48" : A = (Renew 0 4 Read 1) %"chk47", %"v2";
    %"v107" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"v108" : L = (Ext Sw) %"v107";
    %"iw_9.v14" : P = Copy $"_itowa_lower_digits"
    => goto "iw_9.L22";
  @"iw_9.L22" [%"iw_9.pr.6" : P = phi("iw_9.L22" => %"iw_9.v26", "L98" => %"v8"); %"iw_9.pr.1" : L = phi("iw_9.L22" => %"iw_9.v34", "L98" => %"v108")]:
    (Flight (a "iw_9.v26") Sub [(FAddress (t "iw_9.pr.6")); (FValue (Const 4))] (LowerOf (t "iw_9.pr.6")));
    %"iw_9.v29" : L = Urem %"iw_9.pr.1", #10;
    %"iw_9.v30" : L = Shl %"iw_9.v29", #2;
    %"iw_9.v31" = %"iw_9.v14" +p %"iw_9.v30";
    %"chk49" : A = (Check 0 4 Read 1) %"iw_9.v31";
    %"iw_9.v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk49";
    %"chk50" : A = (Check 0 4 Write 1) %"iw_9.v26";
    store Ww [%"chk50" + 0] <- %"iw_9.v32";
    %"iw_9.v34" : L = Udiv %"iw_9.pr.1", #10;
    %"iw_9.v35" : W = (Cmp Ne L) %"iw_9.v34", #0
    => br %"iw_9.v35" ? poll "iw_9.L22" : "L111";
  @"L111" [%"pr.1" : P = phi("L112" => %"v121", "iw_9.L22" => %"iw_9.v26")]:
    %"v116" : L = Ptoi %"pr.1";
    %"v117" : L = Ptoi %"v8";
    %"v118" : W = (Cmp Ult L) %"v116", %"v117"
    => br %"v118" ? "L112" : "L100";
  @"L112":
    %"v121" = %"pr.1" +p #4;
    %"chk51" : A = (Check 0 4 Read 1) %"pr.1";
    %"v122" : W = (RawLoad (LdNarrow Sw) 0) %"chk51";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v122")
    => goto poll "L111";
  @"L100":
    %"v127" = %"v2" +p #8;
    %"chk52" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v127";
    %"v128" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    %"v129" : W = (Cmp Ne W) %"v128", #0
    => br %"v129" ? "L123" : "L125";
  @"L123":
    %"v132" = %"v2" +p #8;
    %"v133" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v133")
    => goto "L125";
  @"L125":
    => ret void
} }.

Definition hello_image_fn_glibc_vfwprintf_internal'23__printf_fp_spec : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__printf_fp_spec"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v10" = %"v2" +p #8;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = (Cmp Eq W) %"v11", #97
    => br %"v12" ? "L14" : "L13";
  @"L13":
    %"v16" = %"v2" +p #8;
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v18" : W = (Cmp Eq W) %"v17", #65
    => goto "L14";
  @"L14" [%"v20" : W = phi("start" => #1, "L13" => %"v18")]:
    => br %"v20" ? "L6" : "L7";
  @"L6":
    %"v22" : P = Copy $"__libc_tsd_LOCALE";
    %"chk2" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call void $"__wprintf_fphex_l_buffer"(P %"v0", P %"v23", P %"v2", P %"v4")
    => goto "L8";
  @"L7":
    %"v27" : P = Copy $"__libc_tsd_LOCALE";
    %"chk3" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call void $"__wprintf_fp_l_buffer"(P %"v0", P %"v28", P %"v2", P %"v4")
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition hello_image_fn___printf_buffer_puts_1 : func :=
  ir_fn{ "export" "__printf_buffer_puts_1"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L4" : "L13";
  @"L4":
    => ret void;
  @"L13" [%"pr.1" : P = phi("L42" => %"v80", "start" => %"v2")]:
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v17" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v18" : W = (Cmp Ne W) %"v17", #0
    => br %"v18" ? "L14" : "L15";
  @"L14":
    %"v23" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v26" = %"v0" +p #16;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v28" : L = Ptoi %"v24";
    %"v29" : L = Ptoi %"v27";
    %"v30" : W = (Cmp Eq L) %"v28", %"v29"
    => br %"v30" ? "L31" : "L32";
  @"L31":
    call %"v34" : W = $"__printf_buffer_flush"(P %"v0");
    %"v35" : W = (Ext Ub) %"v34";
    %"v36" : W = (Cmp Eq W) %"v35", #0
    => goto "L32";
  @"L32" [%"v38" : W = phi("L14" => #0, "L31" => %"v36")]:
    => br %"v38" ? "L19" : "L21";
  @"L19":
    => ret void;
  @"L21":
    %"v44" = %"v0" +p #8;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v47" = %"v0" +p #16;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk3", %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v49" : L = Ptoi %"v45";
    %"v50" : L = Ptoi %"v48";
    %"v51" : W = (Cmp Ne L) %"v49", %"v50"
    => br %"v51" ? "L42" : "L41";
  @"L41":
    %"v52" : P = Copy $"glibc_printf_buffer_puts_1#str.41";
    %"v53" : P = Copy $"glibc_printf_buffer_puts_1#str.42";
    %"v54" : P = Copy $"glibc_printf_buffer_puts_1#str.43";
    call void $"__libc_assert_fail"(P %"v52", P %"v53", W #32, P %"v54")
    => goto "L42";
  @"L42":
    %"v58" = %"v0" +p #16;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk3", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v61" = %"v0" +p #8;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk2", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v63" : L = Ptoi %"v59";
    %"v64" : L = Ptoi %"v62";
    %"v65" : L = Sub %"v63", %"v64";
    call %"v66" : L = $"__GI___strnlen"(P %"pr.1", L %"v65");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"v61";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk8";
    call %"v72" : P = $"__GI_memcpy"(P %"v69", P %"pr.1", L %"v66");
    %"chk9" : A = (Renew 0 8 Read 8) %"chk2", %"v61";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v77" = %"v75" +p %"v66";
    %"chk10" : A = (Renew 0 8 Write 8) %"chk2", %"v61";
    store.ptr [%"chk10" + 0] <- %"v77";
    %"v80" = %"pr.1" +p %"v66"
    => goto poll "L13";
  @"L15":
    => ret void
} }.
