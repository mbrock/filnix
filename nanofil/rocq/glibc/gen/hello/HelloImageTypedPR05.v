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

Definition hello_image_fn_glibc_vfprintf_internal'23printf_unknown : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#printf_unknown"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v4" : P = (Alloc 4) #12;
    %"v7" = %"v4" +p #12;
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
    %"iw_1.v19" = %"iw_1.v18" +p #1;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"iw_1.v17";
    store.ptr [%"chk3" + 0] <- %"iw_1.v19";
    %"chk4" : A = (Check 0 1 Write 1) %"iw_1.v18";
    store Wb [%"chk4" + 0] <- #37
    => goto "iw_1.join";
  @"iw_1.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #37)
    => goto "iw_1.join";
  @"iw_1.join":
    %"v14" = %"v2" +p #12;
    %"chk5" : A = (Check 0 4 Read 1) %"v14";
    %"v15" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v16" : W = Shl %"v15", #28;
    %"v17" : W = Shr %"v16", #31
    => br %"v17" ? "iw_2.start" : "L12";
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
    %"iw_2.v19" = %"iw_2.v18" +p #1;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk0", %"iw_2.v17";
    store.ptr [%"chk9" + 0] <- %"iw_2.v19";
    %"chk10" : A = (Check 0 1 Write 1) %"iw_2.v18";
    store Wb [%"chk10" + 0] <- #35
    => goto "L12";
  @"iw_2.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #35)
    => goto "L12";
  @"L12":
    %"v23" = %"v2" +p #12;
    %"chk11" : A = (Renew 0 4 Read 1) %"chk5", %"v23";
    %"v24" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v25" : W = Shl %"v24", #24;
    %"v26" : W = Shr %"v25", #31
    => br %"v26" ? "iw_3.start" : "L21";
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
    %"iw_3.v19" = %"iw_3.v18" +p #1;
    %"chk15" : A = (Renew 0 8 Write 8) %"chk0", %"iw_3.v17";
    store.ptr [%"chk15" + 0] <- %"iw_3.v19";
    %"chk16" : A = (Check 0 1 Write 1) %"iw_3.v18";
    store Wb [%"chk16" + 0] <- #39
    => goto "L21";
  @"iw_3.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #39)
    => goto "L21";
  @"L21":
    %"v32" = %"v2" +p #12;
    %"chk17" : A = (Renew 0 4 Read 1) %"chk5", %"v32";
    %"v33" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v34" : W = Shl %"v33", #25;
    %"v35" : W = Shr %"v34", #31
    => br %"v35" ? "iw_4.start" : "L29";
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
    %"iw_4.v19" = %"iw_4.v18" +p #1;
    %"chk21" : A = (Renew 0 8 Write 8) %"chk0", %"iw_4.v17";
    store.ptr [%"chk21" + 0] <- %"iw_4.v19";
    %"chk22" : A = (Check 0 1 Write 1) %"iw_4.v18";
    store Wb [%"chk22" + 0] <- #43
    => goto "L30";
  @"iw_4.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #43)
    => goto "L30";
  @"L29":
    %"v41" = %"v2" +p #12;
    %"v42" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v43" : W = Shl %"v42", #27;
    %"v44" : W = Shr %"v43", #31
    => br %"v44" ? "iw_5.start" : "L30";
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
    %"iw_5.v19" = %"iw_5.v18" +p #1;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk0", %"iw_5.v17";
    store.ptr [%"chk27" + 0] <- %"iw_5.v19";
    %"chk28" : A = (Check 0 1 Write 1) %"iw_5.v18";
    store Wb [%"chk28" + 0] <- #32
    => goto "L30";
  @"iw_5.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #32)
    => goto "L30";
  @"L30":
    %"v50" = %"v2" +p #12;
    %"chk29" : A = (Renew 0 4 Read 1) %"chk5", %"v50";
    %"v51" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v52" : W = Shl %"v51", #26;
    %"v53" : W = Shr %"v52", #31
    => br %"v53" ? "iw_6.start" : "L48";
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
    %"iw_6.v19" = %"iw_6.v18" +p #1;
    %"chk33" : A = (Renew 0 8 Write 8) %"chk0", %"iw_6.v17";
    store.ptr [%"chk33" + 0] <- %"iw_6.v19";
    %"chk34" : A = (Check 0 1 Write 1) %"iw_6.v18";
    store Wb [%"chk34" + 0] <- #45
    => goto "L48";
  @"iw_6.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #45)
    => goto "L48";
  @"L48":
    %"v59" = %"v2" +p #16;
    %"chk35" : A = (HalfCheck Upper 0 4 Read 1) %"chk5", %"v59";
    %"v60" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v61" : W = (Cmp Eq W) %"v60", #48
    => br %"v61" ? "L55" : "L57";
  @"L55":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48)
    => goto "L57";
  @"L57":
    %"v67" = %"v2" +p #12;
    %"chk36" : A = (Renew 0 4 Read 1) %"chk5", %"v67";
    %"v68" : W = (RawLoad (LdNarrow Uw) 0) %"chk36";
    %"v69" : W = Shl %"v68", #20;
    %"v70" : W = Shr %"v69", #31
    => br %"v70" ? "L63" : "L65";
  @"L63":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #73)
    => goto "L65";
  @"L65":
    %"v76" = %"v2" +p #4;
    %"chk37" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v76";
    %"v77" : W = (RawLoad (LdNarrow Sw) 0) %"chk37";
    %"v78" : W = (Cmp Ne W) %"v77", #0
    => br %"v78" ? "L72" : "L74";
  @"L72":
    %"v80" = %"v2" +p #4;
    %"v81" : W = (RawLoad (LdNarrow Sw) 0) %"chk37";
    %"v82" : L = (Ext Sw) %"v81";
    call %"v84" : P = $"_itoa_word"(L %"v82", P %"v7", W #10, W #0)
    => goto "L85";
  @"L85" [%"pr.2" : P = phi("L72" => %"v84", "L86" => %"v95")]:
    %"v90" : L = Ptoi %"pr.2";
    %"v91" : L = Ptoi %"v7";
    %"v92" : W = (Cmp Ult L) %"v90", %"v91"
    => br %"v92" ? "L86" : "L74";
  @"L86":
    %"v95" = %"pr.2" +p #1;
    %"chk39" : A = (Check 0 1 Read 1) %"pr.2";
    %"v96" : W = (RawLoad (LdNarrow Sb) 0) %"chk39";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v96")
    => goto poll "L85";
  @"L74":
    %"chk40" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v2";
    %"v101" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"v103" : W = (Cmp Ne W) %"v101", #4294967295
    => br %"v103" ? "L97" : "L99";
  @"L97":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #46);
    %"chk41" : A = (Renew 0 4 Read 1) %"chk40", %"v2";
    %"v106" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"v107" : L = (Ext Sw) %"v106";
    call %"v109" : P = $"_itoa_word"(L %"v107", P %"v7", W #10, W #0)
    => goto "L110";
  @"L110" [%"pr.1" : P = phi("L111" => %"v120", "L97" => %"v109")]:
    %"v115" : L = Ptoi %"pr.1";
    %"v116" : L = Ptoi %"v7";
    %"v117" : W = (Cmp Ult L) %"v115", %"v116"
    => br %"v117" ? "L111" : "L99";
  @"L111":
    %"v120" = %"pr.1" +p #1;
    %"chk42" : A = (Check 0 1 Read 1) %"pr.1";
    %"v121" : W = (RawLoad (LdNarrow Sb) 0) %"chk42";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v121")
    => goto poll "L110";
  @"L99":
    %"v126" = %"v2" +p #8;
    %"chk43" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"v126";
    %"v127" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v128" : W = (Cmp Ne W) %"v127", #0
    => br %"v128" ? "L122" : "L124";
  @"L122":
    %"v131" = %"v2" +p #8;
    %"v132" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v133" : W = (Ext Sb) %"v132";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v133")
    => goto "L124";
  @"L124":
    => ret void
} }.

Definition hello_image_fn_glibc_vfprintf_internal'23__printf_buffer_has_failed : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#__printf_buffer_has_failed"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"v3";
    %"v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v5" : W = (Cmp Eq W) %"v4", #0
    => ret %"v5"
} }.

Definition hello_image_fn_glibc_vfprintf_internal'23__printf_buffer_mark_failed : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Write 1) %"v3";
    store Ww [%"chk0" + 0] <- #0
    => ret void
} }.

Definition hello_image_fn_glibc_vfprintf_internal'23__printf_buffer_pad : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W %"v2", L %"v4") -> RVoid {
  @"start":
    %"v10" : W = (Cmp Sgt L) %"v4", #0
    => br %"v10" ? "L6" : "L8";
  @"L6":
    %"v12" : W = (Ext Sb) %"v2";
    call void $"__printf_buffer_pad_1"(P %"v0", W %"v12", L %"v4")
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition hello_image_fn_glibc_vfprintf_internal'23__printf_buffer_putc : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ne L) %"v13", %"v14"
    => br %"v15" ? "L4" : "L5";
  @"L4":
    %"v17" = %"v0" +p #8;
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v19" = %"v18" +p #1;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v17";
    store.ptr [%"chk3" + 0] <- %"v19";
    %"v20" : W = (Ext Sb) %"v2";
    %"chk4" : A = (Check 0 1 Write 1) %"v18";
    store Wb [%"chk4" + 0] <- %"v20"
    => goto "L6";
  @"L5":
    %"v22" : W = (Ext Sb) %"v2";
    call void $"__printf_buffer_putc_1"(P %"v0", W %"v22")
    => goto "L6";
  @"L6":
    => ret void
} }.

Definition hello_image_fn_glibc_vfprintf_internal'23__printf_fp_spec : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#__printf_fp_spec"(P %"v0", P %"v2", P %"v4") -> RVoid {
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
    call void $"__printf_fphex_l_buffer"(P %"v0", P %"v23", P %"v2", P %"v4")
    => goto "L8";
  @"L7":
    %"v27" : P = Copy $"__libc_tsd_LOCALE";
    %"chk3" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call void $"__printf_fp_l_buffer"(P %"v0", P %"v28", P %"v2", P %"v4")
    => goto "L8";
  @"L8":
    => ret void
} }.
