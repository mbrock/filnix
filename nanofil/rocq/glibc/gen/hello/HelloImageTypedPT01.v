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

Definition hello_image_fn___ptmalloc_init : func :=
  ir_fn{ "export" "__ptmalloc_init"() -> RVoid {
  @"start":
    %"v12" : P = (Alloc 8) #8;
    %"v17" : P = (Alloc 4) #4;
    %"v22" : P = (Alloc 8) #8;
    %"v27" : P = (Alloc 8) #8;
    %"v32" : P = (Alloc 4) #4;
    %"v37" : P = (Alloc 8) #8;
    %"v42" : P = (Alloc 8) #8;
    %"v47" : P = (Alloc 8) #8;
    %"v52" : P = (Alloc 8) #8;
    %"v57" : P = (Alloc 8) #8;
    %"iw_1.v3" : P = Copy $"glibc_malloc#tcache_key";
    %"iw_1.iw_1.v7" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"iw_1.iw_1.v13" : L = $"zsys_getrandom"(P %"iw_1.v3", L #8, W #1);
    %"iw_1.iw_1.v14" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.iw_1.v14";
    store Ww [%"chk1" + 0] <- %"iw_1.iw_1.v8";
    %"iw_1.v5" : W = (Cmp Ne L) %"iw_1.iw_1.v13", #8
    => br %"iw_1.v5" ? "iw_1.L0" : "iw_1.L12";
  @"iw_1.L0":
    %"iw_1.v6" : P = Copy $"glibc_malloc#tcache_key";
    %"chk2" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk2" + 0] <- #0
    => goto "iw_1.L12";
  @"iw_1.L12":
    %"iw_1.v15" : P = Copy $"glibc_malloc#tcache_key";
    %"chk3" : A = (Check 0 8 Read 1) %"iw_1.v15";
    %"iw_1.v16" : L = (RawLoad LdL 0) %"chk3";
    %"iw_1.v17" : W = (Cmp Ule L) %"iw_1.v16", #16777216
    => br %"iw_1.v17" ? "iw_1.L19" : "iw_1.L18";
  @"iw_1.L18":
    %"iw_1.v20" : P = Copy $"glibc_malloc#tcache_key";
    %"chk4" : A = (Check 0 8 Read 1) %"iw_1.v20";
    %"iw_1.v21" : L = (RawLoad LdL 0) %"chk4";
    %"iw_1.v25" : W = (Cmp Uge L) %"iw_1.v21", #18446744073692774399
    => goto "iw_1.L19";
  @"iw_1.L19" [%"iw_1.v27" : W = phi("iw_1.L12" => #1, "iw_1.L18" => %"iw_1.v25")]:
    => br %"iw_1.v27" ? "iw_1.L29" : "iw_1.L28";
  @"iw_1.L28":
    %"iw_1.v30" : P = Copy $"glibc_malloc#tcache_key";
    %"chk5" : A = (Check 0 8 Read 1) %"iw_1.v30";
    %"iw_1.v31" : L = (RawLoad LdL 0) %"chk5";
    %"iw_1.iw_2.v3" : L = Shr %"iw_1.v31", #1;
    %"iw_1.iw_2.v4" : L = And %"iw_1.iw_2.v3", #6148914691236517205;
    %"iw_1.iw_2.v5" : L = Sub %"iw_1.v31", %"iw_1.iw_2.v4";
    %"iw_1.iw_2.v6" : L = And %"iw_1.iw_2.v5", #3689348814741910323;
    %"iw_1.iw_2.v7" : L = Shr %"iw_1.iw_2.v5", #2;
    %"iw_1.iw_2.v8" : L = And %"iw_1.iw_2.v7", #3689348814741910323;
    %"iw_1.iw_2.v9" : L = Add %"iw_1.iw_2.v6", %"iw_1.iw_2.v8";
    %"iw_1.iw_2.v10" : L = Shr %"iw_1.iw_2.v9", #4;
    %"iw_1.iw_2.v11" : L = Add %"iw_1.iw_2.v9", %"iw_1.iw_2.v10";
    %"iw_1.iw_2.v12" : L = And %"iw_1.iw_2.v11", #1085102592571150095;
    %"iw_1.iw_2.v13" : L = Mul %"iw_1.iw_2.v12", #72340172838076673;
    %"iw_1.iw_2.v14" : L = Shr %"iw_1.iw_2.v13", #56
    => goto "iw_1.iw_2.join";
  @"iw_1.iw_2.join" [%"iw_1.v32" : W = phi("iw_1.L28" => %"iw_1.iw_2.v14")]:
    %"iw_1.v34" : W = (Cmp Ult W) %"iw_1.v32", #16
    => goto "iw_1.L29";
  @"iw_1.L29" [%"iw_1.v36" : W = phi("iw_1.L19" => #1, "iw_1.iw_2.join" => %"iw_1.v34")]:
    => br %"iw_1.v36" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v39" : P = Copy $"glibc_malloc#tcache_key";
    %"chk6" : A = (Check 0 8 Read 1) %"iw_1.v39";
    %"iw_1.v40" : L = (RawLoad LdL 0) %"chk6";
    %"iw_1.iw_3.v3" : L = Shr %"iw_1.v40", #1;
    %"iw_1.iw_3.v4" : L = And %"iw_1.iw_3.v3", #6148914691236517205;
    %"iw_1.iw_3.v5" : L = Sub %"iw_1.v40", %"iw_1.iw_3.v4";
    %"iw_1.iw_3.v6" : L = And %"iw_1.iw_3.v5", #3689348814741910323;
    %"iw_1.iw_3.v7" : L = Shr %"iw_1.iw_3.v5", #2;
    %"iw_1.iw_3.v8" : L = And %"iw_1.iw_3.v7", #3689348814741910323;
    %"iw_1.iw_3.v9" : L = Add %"iw_1.iw_3.v6", %"iw_1.iw_3.v8";
    %"iw_1.iw_3.v10" : L = Shr %"iw_1.iw_3.v9", #4;
    %"iw_1.iw_3.v11" : L = Add %"iw_1.iw_3.v9", %"iw_1.iw_3.v10";
    %"iw_1.iw_3.v12" : L = And %"iw_1.iw_3.v11", #1085102592571150095;
    %"iw_1.iw_3.v13" : L = Mul %"iw_1.iw_3.v12", #72340172838076673;
    %"iw_1.iw_3.v14" : L = Shr %"iw_1.iw_3.v13", #56
    => goto "iw_1.iw_3.join";
  @"iw_1.iw_3.join" [%"iw_1.v41" : W = phi("iw_1.L37" => %"iw_1.iw_3.v14")]:
    %"iw_1.v43" : W = (Cmp Ugt W) %"iw_1.v41", #48
    => goto "iw_1.L38";
  @"iw_1.L38" [%"iw_1.v45" : W = phi("iw_1.L29" => #1, "iw_1.iw_3.join" => %"iw_1.v43")]:
    => br %"iw_1.v45" ? "iw_1.L13" : "iw_1.join";
  @"iw_1.L13":
    %"iw_1.v46" : P = Copy $"glibc_malloc#tcache_key";
    %"iw_1.iw_4.v0" : P = (Alloc 8) #16;
    call %"iw_1.iw_4.v1" : W = $"__GI___clock_gettime"(W #1, P %"iw_1.iw_4.v0");
    %"iw_1.iw_4.v3" = %"iw_1.iw_4.v0" +p #8;
    %"chk7" : A = (Check 0 8 Read 1) %"iw_1.iw_4.v3";
    %"iw_1.iw_4.v4" : L = (RawLoad LdL 0) %"chk7";
    %"chk8" : A = (HalfCheck Lower 0 8 Read 1) %"chk7", %"iw_1.iw_4.v0";
    %"iw_1.iw_4.v5" : L = (RawLoad LdL 0) %"chk8";
    %"iw_1.iw_4.v6" : L = Xor %"iw_1.iw_4.v4", %"iw_1.iw_4.v5";
    %"iw_1.iw_4.v7" : W = Copy %"iw_1.iw_4.v6";
    %"iw_1.iw_4.v8" : W = Copy %"iw_1.iw_4.v6";
    %"iw_1.iw_4.v9" : W = Shl %"iw_1.iw_4.v8", #24;
    %"iw_1.iw_4.v10" : W = Copy %"iw_1.iw_4.v6";
    %"iw_1.iw_4.v11" : W = Shr %"iw_1.iw_4.v10", #8;
    %"iw_1.iw_4.v12" : W = Or %"iw_1.iw_4.v9", %"iw_1.iw_4.v11";
    %"iw_1.iw_4.v13" : W = Xor %"iw_1.iw_4.v7", %"iw_1.iw_4.v12";
    %"iw_1.v48" : L = (Ext Uw) %"iw_1.iw_4.v13";
    %"chk9" : A = (Check 0 8 Write 1) %"iw_1.v46";
    store Wl [%"chk9" + 0] <- %"iw_1.v48";
    %"iw_1.v49" : P = Copy $"glibc_malloc#tcache_key";
    %"iw_1.v50" : P = Copy $"glibc_malloc#tcache_key";
    %"chk10" : A = (Check 0 8 Read 1) %"iw_1.v50";
    %"iw_1.v51" : L = (RawLoad LdL 0) %"chk10";
    %"iw_1.v52" : L = Shl %"iw_1.v51", #32;
    %"iw_1.iw_5.v0" : P = (Alloc 8) #16;
    call %"iw_1.iw_5.v1" : W = $"__GI___clock_gettime"(W #1, P %"iw_1.iw_5.v0");
    %"iw_1.iw_5.v3" = %"iw_1.iw_5.v0" +p #8;
    %"chk11" : A = (Check 0 8 Read 1) %"iw_1.iw_5.v3";
    %"iw_1.iw_5.v4" : L = (RawLoad LdL 0) %"chk11";
    %"chk12" : A = (HalfCheck Lower 0 8 Read 1) %"chk11", %"iw_1.iw_5.v0";
    %"iw_1.iw_5.v5" : L = (RawLoad LdL 0) %"chk12";
    %"iw_1.iw_5.v6" : L = Xor %"iw_1.iw_5.v4", %"iw_1.iw_5.v5";
    %"iw_1.iw_5.v7" : W = Copy %"iw_1.iw_5.v6";
    %"iw_1.iw_5.v8" : W = Copy %"iw_1.iw_5.v6";
    %"iw_1.iw_5.v9" : W = Shl %"iw_1.iw_5.v8", #24;
    %"iw_1.iw_5.v10" : W = Copy %"iw_1.iw_5.v6";
    %"iw_1.iw_5.v11" : W = Shr %"iw_1.iw_5.v10", #8;
    %"iw_1.iw_5.v12" : W = Or %"iw_1.iw_5.v9", %"iw_1.iw_5.v11";
    %"iw_1.iw_5.v13" : W = Xor %"iw_1.iw_5.v7", %"iw_1.iw_5.v12";
    %"iw_1.v54" : L = (Ext Uw) %"iw_1.iw_5.v13";
    %"iw_1.v55" : L = Or %"iw_1.v52", %"iw_1.v54";
    %"chk13" : A = (Check 0 8 Write 1) %"iw_1.v49";
    store Wl [%"chk13" + 0] <- %"iw_1.v55"
    => goto poll "iw_1.L12";
  @"iw_1.join":
    %"v3" : P = Copy $"__libc_initial";
    %"chk14" : A = (Check 0 1 Read 1) %"v3";
    %"v4" : W = (RawLoad (LdNarrow Ub) 0) %"chk14";
    %"v5" : W = (Cmp Eq W) %"v4", #0
    => br %"v5" ? "L0" : "L2";
  @"L0":
    %"v6" : P = Copy $"glibc_malloc#__always_fail_morecore";
    %"chk15" : A = (Check 0 1 Write 1) %"v6";
    store Wb [%"chk15" + 0] <- #1
    => goto "L2";
  @"L2":
    %"v8" : P = Copy $"thread_arena";
    %"v9" : P = Copy $"glibc_malloc#main_arena";
    %"chk16" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk16" + 0] <- %"v9";
    %"v10" : P = Copy $"glibc_malloc#main_arena"
    => goto "iw_2.L4";
  @"iw_2.L4" [%"iw_2.pr.1" : W = phi("iw_2.L5" => %"iw_2.v25", "L2" => #1)]:
    %"iw_2.v9" : W = (Cmp Slt W) %"iw_2.pr.1", #128
    => br %"iw_2.v9" ? "iw_2.L5" : "iw_2.L7";
  @"iw_2.L5":
    %"iw_2.v11" = %"v10" +p #24;
    %"iw_2.v13" : W = Sub %"iw_2.pr.1", #1;
    %"iw_2.v14" : W = Shl %"iw_2.v13", #1;
    %"iw_2.v15" : L = (Ext Sw) %"iw_2.v14";
    %"iw_2.v16" : L = Shl %"iw_2.v15", #3;
    %"iw_2.v17" = %"iw_2.v11" +p %"iw_2.v16";
    (Flight (a "iw_2.v18") Sub [(FAddress (t "iw_2.v17")); (FValue (Const 16))] (LowerOf (t "iw_2.v17")));
    %"iw_2.v20" = %"iw_2.v18" +p #16;
    %"iw_2.v22" = %"iw_2.v18" +p #24;
    %"chk17" : A = (Check 0 8 Write 8) %"iw_2.v22";
    store.ptr [%"chk17" + 0] <- %"iw_2.v18";
    %"chk18" : A = (HalfCheck Lower 0 8 Write 8) %"chk17", %"iw_2.v20";
    store.ptr [%"chk18" + 0] <- %"iw_2.v18";
    %"iw_2.v25" : W = Add %"iw_2.pr.1", #1
    => goto poll "iw_2.L4";
  @"iw_2.L7":
    %"iw_2.v30" : P = Copy $"glibc_malloc#main_arena";
    %"iw_2.v31" : L = Ptoi %"v10";
    %"iw_2.v32" : L = Ptoi %"iw_2.v30";
    %"iw_2.v33" : W = (Cmp Ne L) %"iw_2.v31", %"iw_2.v32"
    => br %"iw_2.v33" ? "iw_2.L26" : "iw_2.L28";
  @"iw_2.L26":
    %"iw_2.v35" = %"v10" +p #4;
    %"chk19" : A = (Check 0 4 Read 1) %"iw_2.v35";
    %"iw_2.v36" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"iw_2.v37" : W = Or %"iw_2.v36", #2;
    %"chk20" : A = (Renew 0 4 Write 1) %"chk19", %"iw_2.v35";
    store Ww [%"chk20" + 0] <- %"iw_2.v37"
    => goto "iw_2.L28";
  @"iw_2.L28":
    %"iw_2.v39" = %"v10" +p #8;
    %"iw_2.v41" = %"v10" +p #24;
    (Flight (a "iw_2.v47") Sub [(FAddress (t "iw_2.v41")); (FValue (Const 16))] (LowerOf (t "iw_2.v41")));
    %"chk21" : A = (Check 0 8 Write 8) %"iw_2.v39";
    store.ptr [%"chk21" + 0] <- %"iw_2.v47";
    %"v14" : P = Copy $"glibc_malloc#_dl_tunable_set_top_pad";
    call void $"__tunable_get_val"(W #24, P %"v12", P %"v14");
    %"chk22" : A = (Check 0 8 Read 1) %"v12";
    %"v15" : L = (RawLoad LdL 0) %"chk22";
    %"v19" : P = Copy $"glibc_malloc#_dl_tunable_set_perturb_byte";
    call void $"__tunable_get_val"(W #21, P %"v17", P %"v19");
    %"chk23" : A = (Check 0 4 Read 1) %"v17";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v24" : P = Copy $"glibc_malloc#_dl_tunable_set_mmap_threshold";
    call void $"__tunable_get_val"(W #19, P %"v22", P %"v24");
    %"chk24" : A = (Check 0 8 Read 1) %"v22";
    %"v25" : L = (RawLoad LdL 0) %"chk24";
    %"v29" : P = Copy $"glibc_malloc#_dl_tunable_set_trim_threshold";
    call void $"__tunable_get_val"(W #25, P %"v27", P %"v29");
    %"chk25" : A = (Check 0 8 Read 1) %"v27";
    %"v30" : L = (RawLoad LdL 0) %"chk25";
    %"v34" : P = Copy $"glibc_malloc#_dl_tunable_set_mmaps_max";
    call void $"__tunable_get_val"(W #18, P %"v32", P %"v34");
    %"chk26" : A = (Check 0 4 Read 1) %"v32";
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v39" : P = Copy $"glibc_malloc#_dl_tunable_set_arena_max";
    call void $"__tunable_get_val"(W #14, P %"v37", P %"v39");
    %"chk27" : A = (Check 0 8 Read 1) %"v37";
    %"v40" : L = (RawLoad LdL 0) %"chk27";
    %"v44" : P = Copy $"glibc_malloc#_dl_tunable_set_arena_test";
    call void $"__tunable_get_val"(W #15, P %"v42", P %"v44");
    %"chk28" : A = (Check 0 8 Read 1) %"v42";
    %"v45" : L = (RawLoad LdL 0) %"chk28";
    %"v49" : P = Copy $"glibc_malloc#_dl_tunable_set_tcache_max";
    call void $"__tunable_get_val"(W #23, P %"v47", P %"v49");
    %"chk29" : A = (Check 0 8 Read 1) %"v47";
    %"v50" : L = (RawLoad LdL 0) %"chk29";
    %"v54" : P = Copy $"glibc_malloc#_dl_tunable_set_tcache_count";
    call void $"__tunable_get_val"(W #22, P %"v52", P %"v54");
    %"chk30" : A = (Check 0 8 Read 1) %"v52";
    %"v55" : L = (RawLoad LdL 0) %"chk30";
    %"v59" : P = Copy $"glibc_malloc#_dl_tunable_set_hugetlb";
    call void $"__tunable_get_val"(W #17, P %"v57", P %"v59");
    %"chk31" : A = (Check 0 8 Read 1) %"v57";
    %"v60" : L = (RawLoad LdL 0) %"chk31";
    %"v64" : P = Copy $"glibc_malloc#mp_";
    %"v65" = %"v64" +p #56;
    %"chk32" : A = (Check 0 8 Read 1) %"v65";
    %"v66" : L = (RawLoad LdL 0) %"chk32";
    %"v67" : W = (Cmp Ugt L) %"v66", #0
    => br %"v67" ? "L68" : "L69";
  @"L68":
    %"v70" : P = Copy $"glibc_malloc#mp_";
    %"v71" = %"v70" +p #56;
    %"chk33" : A = (Check 0 8 Read 1) %"v71";
    %"v72" : L = (RawLoad LdL 0) %"chk33";
    %"v74" : W = (Cmp Ule L) %"v72", #67108864
    => goto "L69";
  @"L69" [%"v76" : W = phi("iw_2.L28" => #0, "L68" => %"v74")]:
    => br %"v76" ? "L61" : "L63";
  @"L61":
    call %"v82" : W = $"__tunable_is_initialized"(W #19);
    %"v83" : W = (Ext Ub) %"v82";
    %"v84" : W = (Cmp Eq W) %"v83", #0
    => br %"v84" ? "L77" : "L79";
  @"L77":
    %"v85" : P = Copy $"glibc_malloc#mp_";
    %"v86" = %"v85" +p #56;
    %"chk34" : A = (Check 0 8 Read 1) %"v86";
    %"v87" : L = (RawLoad LdL 0) %"chk34";
    %"iw_4.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_4.v6" = %"iw_4.v5" +p #16;
    %"chk35" : A = (Check 0 8 Write 1) %"iw_4.v6";
    store Wl [%"chk35" + 0] <- %"v87";
    %"iw_4.v8" : P = Copy $"glibc_malloc#mp_";
    %"iw_4.v9" = %"iw_4.v8" +p #80;
    %"chk36" : A = (Check 0 4 Write 1) %"iw_4.v9";
    store Ww [%"chk36" + 0] <- #1
    => goto "L79";
  @"L79":
    %"v89" : P = Copy $"glibc_malloc#__always_fail_morecore";
    %"chk37" : A = (Check 0 1 Write 1) %"v89";
    store Wb [%"chk37" + 0] <- #1
    => goto "L63";
  @"L63":
    => ret void
} }.

Definition hello_image_fn___GI___pthread_cleanup_push : func :=
  ir_fn{ "export" "__GI___pthread_cleanup_push"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    call %"v7" : P = $"zthread_self_cookie"();
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v2";
    %"v11" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v11";
    store.ptr [%"chk1" + 0] <- %"v4";
    %"v14" = %"v0" +p #24;
    %"v16" = %"v7" +p #776;
    %"chk2" : A = (Check 0 8 Read 8) %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v14";
    store.ptr [%"chk3" + 0] <- %"v17";
    %"chk4" : A = (Renew 0 8 Write 8) %"chk2", %"v16";
    store.ptr [%"chk4" + 0] <- %"v0"
    => ret void
} }.

Definition hello_image_fn___GI___pthread_cleanup_pop : func :=
  ir_fn{ "export" "__GI___pthread_cleanup_pop"(P %"v0", W %"v2") -> RVoid {
  @"start":
    call %"v5" : P = $"zthread_self_cookie"();
    %"v7" = %"v5" +p #776;
    %"v9" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Write 8) %"v7";
    store.ptr [%"chk1" + 0] <- %"v10"
    => br %"v2" ? "L11" : "L13";
  @"L11":
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v18" = %"v0" +p #8;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v16";
    rawcall void %"chk4"(P %"v19")
    => goto "L13";
  @"L13":
    => ret void
} }.

Definition hello_image_fn_glibc_pthread_once'23__pthread_once_slow : func :=
  ir_fn{ "local" "glibc_pthread_once#__pthread_once_slow"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v56" : P = (Alloc 8) #56
    => goto "L5";
  @"L5":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L11";
  @"L11" [%"pr.1" : W = phi("L32" => %"pr.2", "L5" => %"v10")]:
    %"v18" : W = And %"pr.1", #2;
    %"v19" : W = (Cmp Ne W) %"v18", #0
    => br %"v19" ? "L14" : "L16";
  @"L14":
    => ret #0;
  @"L16":
    %"v23" : P = Copy $"__fork_generation";
    %"chk1" : A = (Check 0 8 Read 1) %"v23";
    %"v24" : L = (RawLoad LdL 0) %"chk1";
    %"v25" : L = Or %"v24", #1;
    %"v27" : W = Copy %"v25";
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v0";
    %"v29" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"pr.1", %"v27";
    %"v30" : W = (Cmp Eq W) %"v29", %"pr.1"
    => br %"v30" ? "L32" : "L31";
  @"L31":
    => goto "L32";
  @"L32" [%"pr.2" : W = phi("L16" => %"pr.1", "L31" => %"v29")]:
    %"v33" : W = (Cmp Ne W) %"v29", %"pr.1"
    => br %"v33" ? poll "L11" : "L13";
  @"L13":
    %"v40" : W = And %"pr.2", #1
    => br %"v40" ? "L36" : "L51";
  @"L36":
    %"v46" : W = Copy %"v25";
    %"v47" : W = (Cmp Eq W) %"pr.2", %"v46"
    => br %"v47" ? "L42" : "L51";
  @"L42":
    %"v49" : W = Copy %"v25";
    call void $"zsys_futex_wait"(P %"v0", W %"v49", W #1)
    => goto poll "L5";
  @"L51":
    %"v55" : P = Copy $"glibc_pthread_once#clear_once_control";
    %"chk3" : A = (Check 0 8 Write 1) %"v56";
    store Wl [%"chk3" + 0] <- #0;
    %"v57" = %"v56" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v57";
    store Wl [%"chk4" + 0] <- #0;
    %"v58" = %"v56" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v58";
    store Wl [%"chk5" + 0] <- #0;
    %"v59" = %"v56" +p #24;
    %"chk6" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v59";
    store Wl [%"chk6" + 0] <- #0;
    %"v60" = %"v56" +p #32;
    %"chk7" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v60";
    store Wl [%"chk7" + 0] <- #0;
    %"v61" = %"v56" +p #40;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v61";
    store Wl [%"chk8" + 0] <- #0;
    %"v62" = %"v56" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v62";
    store Wl [%"chk9" + 0] <- #0;
    %"chk10" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v56";
    store.ptr [%"chk10" + 0] <- %"v55";
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk4", %"v57";
    store.ptr [%"chk11" + 0] <- %"v0";
    %"chk12" : A = (Renew 0 4 Write 1) %"chk5", %"v58";
    store Ww [%"chk12" + 0] <- #1;
    %"v68" : P = Copy $"glibc_pthread_once#__pthread_cleanup_combined_routine_voidptr";
    call void $"__GI___pthread_cleanup_push"(P %"v59", P %"v68", P %"v56");
    %"chk13" : F = CheckFunction %"v2";
    rawcall void %"chk13"();
    call void $"__GI___pthread_cleanup_pop"(P %"v59", W #0);
    %"chk14" : A = (Renew 0 4 Write 1) %"chk5", %"v58";
    store Ww [%"chk14" + 0] <- #0;
    %"iw_2.v6" = %"v56" +p #16;
    %"iw_2.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk14"
    => br %"iw_2.v7" ? "iw_2.L2" : "L78";
  @"iw_2.L2":
    %"chk16" : A = (Renew 0 8 Read 8) %"chk10", %"v56";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v11" = %"v56" +p #8;
    %"iw_2.v12" : P = (RawLoadPointer 8 load_effects) %"chk16";
    %"chk18" : F = CheckFunction %"iw_2.v9";
    rawcall void %"chk18"(P %"iw_2.v12");
    %"iw_2.v14" = %"v56" +p #16;
    %"chk19" : A = (Renew 0 4 Write 1) %"chk5", %"iw_2.v14";
    store Ww [%"chk19" + 0] <- #0;
    %"iw_2.v16" = %"v56" +p #24;
    call void $"__GI___pthread_cleanup_pop"(P %"iw_2.v16", W #0)
    => goto "L78";
  @"L78":
    %"chk20" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk20" + 0] <- #2;
    call void $"zsys_futex_wake"(P %"v0", W #2147483647, W #1)
    => ret #0
} }.

Definition hello_image_fn____pthread_once : func :=
  ir_fn{ "export" "___pthread_once"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = And %"v6", #2;
    %"v12" : W = (Cmp Ne W) %"v11", #0
    => br %"v12" ? "L7" : "L8";
  @"L7":
    => ret #0;
  @"L8":
    call %"v18" : W = $"glibc_pthread_once#__pthread_once_slow"(P %"v0", P %"v2")
    => ret %"v18"
} }.

Definition hello_image_fn_glibc_pthread_once'23__pthread_cleanup_combined_routine_voidptr : func :=
  ir_fn{ "local" "glibc_pthread_once#__pthread_cleanup_combined_routine_voidptr"(P %"v0") -> RVoid {
  @"start":
    %"v8" = %"v0" +p #16;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => br %"v9" ? "L4" : "L6";
  @"L4":
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" = %"v0" +p #8;
    %"v14" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"chk3" : F = CheckFunction %"v11";
    rawcall void %"chk3"(P %"v14");
    %"v16" = %"v0" +p #16;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk0", %"v16";
    store Ww [%"chk4" + 0] <- #0
    => goto "L6";
  @"L6":
    => ret void
} }.

Definition hello_image_fn____pthread_rwlock_init : func :=
  ir_fn{ "export" "___pthread_rwlock_init"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v6" : L = Ptoi %"v2";
    %"v7" : W = (Cmp Ne L) %"v6", #0
    => br %"v7" ? "L10" : "L9";
  @"L9":
    %"v11" : P = Copy $"glibc_pthread_rwlock_init#default_rwlockattr"
    => goto "L10";
  @"L10" [%"v12" : P = phi("L9" => %"v11", "start" => %"v2")]:
    call %"v14" : P = $"__GI_memset"(P %"v0", W #0, L #56);
    %"v16" = %"v0" +p #48;
    %"chk0" : A = (Check 0 4 Read 1) %"v12";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"chk1" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk1" + 0] <- %"v18";
    %"v20" = %"v0" +p #28;
    %"v22" = %"v12" +p #4;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v22";
    %"v23" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v24" : W = (Cmp Ne W) %"v23", #0;
    %"chk3" : A = (HalfCheck Lower 0 4 Write 1) %"chk1", %"v20";
    store Ww [%"chk3" + 0] <- %"v24"
    => ret #0
} }.

Definition hello_image_fn____pthread_rwlock_rdlock : func :=
  ir_fn{ "export" "___pthread_rwlock_rdlock"(P %"v0") -> (RClass W) blocks ((app [ir_blk{ @"start":
    (Flight (a "iw_1.v4") Copy [(FAddress (Const 0))] (LowerOf (Const 0)));
    %"iw_1.v11" : L = Ptoi %"iw_1.v4";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v11", #0
    => br %"iw_1.v12" ? "iw_1.L18" : "iw_1.L14" };
  ir_blk{ @"iw_1.L18":
    %"iw_1.v21" = %"iw_1.v4" +p #8;
    %"chk0" : A = (Check 0 8 Read 1) %"iw_1.v21";
    %"iw_1.v22" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.iw_2.v3" : W = (Cmp Sge L) %"iw_1.v22", #0
    => br %"iw_1.iw_2.v3" ? "iw_1.iw_2.L4" : "iw_1.iw_2.L5" };
  ir_blk{ @"iw_1.iw_2.L4":
    %"iw_1.iw_2.v7" : W = (Cmp Slt L) %"iw_1.v22", #1000000000
    => goto "iw_1.iw_2.L5" };
  ir_blk{ @"iw_1.iw_2.L5" [%"iw_1.iw_2.v9" : W = phi("iw_1.L18" => #0, "iw_1.iw_2.L4" => %"iw_1.iw_2.v7")]:
    %"iw_1.v25" : W = (Cmp Eq W) %"iw_1.iw_2.v9", #0
    => goto "iw_1.L14" };
  ir_blk{ @"iw_1.L14" [%"iw_1.v31" : W = phi("start" => #0, "iw_1.iw_2.L5" => %"iw_1.v25")]:
    => br %"iw_1.v31" ? "iw_1.join" : "iw_1.L9" };
  ir_blk{ @"iw_1.L9":
    %"iw_1.v37" = %"v0" +p #24;
    %"chk1" : A = (Check 0 4 Read 1) %"iw_1.v37";
    %"iw_1.v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call %"iw_1.v39" : P = $"zthread_self_cookie"();
    %"iw_1.v40" = %"iw_1.v39" +p #720;
    %"chk2" : A = (Check 0 4 Read 1) %"iw_1.v40";
    %"iw_1.v41" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.v42" : W = (Cmp Eq W) %"iw_1.v38", %"iw_1.v41"
    => br %"iw_1.v42" ? "iw_1.join" : "iw_1.L35" };
  ir_blk{ @"iw_1.L35":
    %"iw_1.v50" = %"v0" +p #48;
    %"chk3" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.v50";
    %"iw_1.v51" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"iw_1.v52" : W = (Cmp Eq W) %"iw_1.v51", #2
    => br %"iw_1.v52" ? "iw_1.L46" : "iw_1.L48" };
  ir_blk{ @"iw_1.L46":
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"v0";
    %"iw_1.v54" : W = (RawLoad (LdNarrow Uw) 0) %"chk4"
    => goto "iw_1.L55" };
  ir_blk{ @"iw_1.L55" [%"iw_1.pr.7" : W = phi("iw_1.L46" => %"iw_1.v54", "iw_1.L86" => %"iw_1.v90", "iw_1.L85" => %"iw_1.pr.9")]:
    %"iw_1.v59" : W = And %"iw_1.pr.7", #1
    => br %"iw_1.v59" ? "iw_1.L62" : "iw_1.L61" };
  ir_blk{ @"iw_1.L61":
    %"iw_1.v64" : W = And %"iw_1.pr.7", #2;
    %"iw_1.v65" : W = (Cmp Ne W) %"iw_1.v64", #0
    => goto "iw_1.L62" };
  ir_blk{ @"iw_1.L62" [%"iw_1.v67" : W = phi("iw_1.L55" => #0, "iw_1.L61" => %"iw_1.v65")]:
    => br %"iw_1.v67" ? "iw_1.L68" : "iw_1.L69" };
  ir_blk{ @"iw_1.L68":
    %"iw_1.v71" : W = Shr %"iw_1.pr.7", #3;
    %"iw_1.v72" : W = (Cmp Ugt W) %"iw_1.v71", #0
    => goto "iw_1.L69" };
  ir_blk{ @"iw_1.L69" [%"iw_1.v74" : W = phi("iw_1.L62" => #0, "iw_1.L68" => %"iw_1.v72")]:
    => br %"iw_1.v74" ? "iw_1.L56" : "iw_1.L48" };
  ir_blk{ @"iw_1.L56":
    %"iw_1.v80" : W = Or %"iw_1.pr.7", #4;
    %"chk5" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v82" : W = (RawCas (CasNarrow Uw) 0) %"chk5", %"iw_1.pr.7", %"iw_1.v80";
    %"iw_1.v83" : W = (Cmp Eq W) %"iw_1.v82", %"iw_1.pr.7"
    => br %"iw_1.v83" ? "iw_1.L85" : "iw_1.L84" };
  ir_blk{ @"iw_1.L84":
    => goto "iw_1.L85" };
  ir_blk{ @"iw_1.L85" [%"iw_1.pr.9" : W = phi("iw_1.L56" => %"iw_1.pr.7", "iw_1.L84" => %"iw_1.v82")]:
    => br %"iw_1.v83" ? "iw_1.L86" : poll "iw_1.L55" };
  ir_blk{ @"iw_1.L86":
    %"chk6" : A = (Renew 0 4 Read 1) %"chk4", %"v0";
    %"iw_1.v90" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"iw_1.v91" : W = And %"iw_1.v90", #4;
    %"iw_1.v92" : W = (Cmp Ne W) %"iw_1.v91", #0
    => br %"iw_1.v92" ? "iw_1.iw_3.start" : poll "iw_1.L55" };
  ir_blk{ @"iw_1.iw_3.start":
    %"iw_1.iw_3.v6" = %"v0" +p #28;
    %"chk7" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.iw_3.v6";
    %"iw_1.iw_3.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"iw_1.iw_3.v8" : W = (Cmp Ne W) %"iw_1.iw_3.v7", #0
    => br %"iw_1.iw_3.v8" ? "iw_1.iw_3.L4" : "iw_1.iw_3.L3" };
  ir_blk{ @"iw_1.iw_3.L3":
    => goto "iw_1.iw_3.L4" };
  ir_blk{ @"iw_1.iw_3.L4" [%"iw_1.iw_3.v9" : W = phi("iw_1.iw_3.L3" => #0, "iw_1.iw_3.start" => #128)]:
    call %"iw_1.v102" : W = $"__GI___futex_abstimed_wait64"(P %"v0", W %"iw_1.v90", W #0, P %"iw_1.v4", W %"iw_1.iw_3.v9");
    %"iw_1.v107" : W = (Cmp Eq W) %"iw_1.v102", #110
    => br %"iw_1.v107" ? "iw_1.L109" : "iw_1.L108" };
  ir_blk{ @"iw_1.L108":
    %"iw_1.v111" : W = (Cmp Eq W) %"iw_1.v102", #75
    => goto "iw_1.L109" };
  ir_blk{ @"iw_1.L109" [%"iw_1.v113" : W = phi("iw_1.iw_3.L4" => #1, "iw_1.L108" => %"iw_1.v111")]:
    => br %"iw_1.v113" ? "iw_1.join" : poll "iw_1.L86" };
  ir_blk{ @"iw_1.L48":
    %"chk8" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"v0";
    %"iw_1.v118" : W = (RawLoad (LdNarrow Uw) 0) %"chk8"
    => goto "iw_1.L119" };
  ir_blk{ @"iw_1.L119" [%"iw_1.v121" : W = phi("iw_1.L48" => %"iw_1.v118", "iw_1.L119" => %"iw_1.v123")]:
    %"iw_1.v122" : W = Add %"iw_1.v121", #8;
    %"chk9" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v123" : W = (RawCas (CasNarrow Uw) 0) %"chk9", %"iw_1.v121", %"iw_1.v122";
    %"iw_1.v124" : W = (Cmp Eq W) %"iw_1.v123", %"iw_1.v121"
    => br %"iw_1.v124" ? "iw_1.L127" : poll "iw_1.L119" };
  ir_blk{ @"iw_1.L127" [%"iw_1.pr.1" : W = phi("iw_1.L119" => %"iw_1.v122", "iw_1.L148" => %"iw_1.pr.2")]:
    %"iw_1.v134" : W = (Cmp Uge W) %"iw_1.pr.1", #2147483648
    => br %"iw_1.v134" ? "iw_1.L128" : "iw_1.L129" };
  ir_blk{ @"iw_1.L128":
    %"iw_1.v143" : W = Sub %"iw_1.pr.1", #8;
    %"chk10" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v145" : W = (RawCas (CasNarrow Uw) 0) %"chk10", %"iw_1.pr.1", %"iw_1.v143";
    %"iw_1.v146" : W = (Cmp Eq W) %"iw_1.v145", %"iw_1.pr.1"
    => br %"iw_1.v146" ? "iw_1.L148" : "iw_1.L147" };
  ir_blk{ @"iw_1.L147":
    => goto "iw_1.L148" };
  ir_blk{ @"iw_1.L148" [%"iw_1.pr.2" : W = phi("iw_1.L128" => %"iw_1.pr.1", "iw_1.L147" => %"iw_1.v145")]:
    => br %"iw_1.v146" ? "iw_1.join" : poll "iw_1.L127" };
  ir_blk{ @"iw_1.L129":
    %"iw_1.v154" : W = And %"iw_1.pr.1", #1
    => br %"iw_1.v154" ? "iw_1.L159" : "iw_1.join" };
  ir_blk{ @"iw_1.L159" [%"iw_1.pr.3" : W = phi("iw_1.L129" => %"iw_1.pr.1", "iw_1.L182" => %"iw_1.pr.4")]:
    %"iw_1.v163" : W = And %"iw_1.pr.3", #1
    => br %"iw_1.v163" ? "iw_1.L165" : "iw_1.L166" };
  ir_blk{ @"iw_1.L165":
    %"iw_1.v168" : W = And %"iw_1.pr.3", #2;
    %"iw_1.v169" : W = (Cmp Eq W) %"iw_1.v168", #0
    => goto "iw_1.L166" };
  ir_blk{ @"iw_1.L166" [%"iw_1.v171" : W = phi("iw_1.L159" => #0, "iw_1.L165" => %"iw_1.v169")]:
    => br %"iw_1.v171" ? "iw_1.L160" : "iw_1.L206" };
  ir_blk{ @"iw_1.L160":
    %"iw_1.v177" : W = Xor %"iw_1.pr.3", #1;
    %"chk11" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v179" : W = (RawCas (CasNarrow Uw) 0) %"chk11", %"iw_1.pr.3", %"iw_1.v177";
    %"iw_1.v180" : W = (Cmp Eq W) %"iw_1.v179", %"iw_1.pr.3"
    => br %"iw_1.v180" ? "iw_1.L182" : "iw_1.L181" };
  ir_blk{ @"iw_1.L181":
    => goto "iw_1.L182" }] [ir_blk{ @"iw_1.L182" [%"iw_1.pr.4" : W = phi("iw_1.L160" => %"iw_1.pr.3", "iw_1.L181" => %"iw_1.v179")]:
    => br %"iw_1.v180" ? "iw_1.L172" : poll "iw_1.L159" };
  ir_blk{ @"iw_1.L172":
    %"iw_1.v187" = %"v0" +p #8;
    %"chk12" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v187";
    %"iw_1.v188" : W = (RawLoad (LdNarrow Uw) 0) %"chk12"
    => goto "iw_1.L189" };
  ir_blk{ @"iw_1.L189" [%"iw_1.v191" : W = phi("iw_1.L172" => %"iw_1.v188", "iw_1.L189" => %"iw_1.v192")]:
    %"chk13" : A = (HalfCheck Lower 0 4 Write 4) %"chk12", %"iw_1.v187";
    %"iw_1.v192" : W = (RawCas (CasNarrow Uw) 0) %"chk13", %"iw_1.v191", #0;
    %"iw_1.v193" : W = (Cmp Eq W) %"iw_1.v192", %"iw_1.v191"
    => br %"iw_1.v193" ? "iw_1.L190" : poll "iw_1.L189" };
  ir_blk{ @"iw_1.L190":
    %"iw_1.v194" : W = And %"iw_1.v191", #2;
    %"iw_1.v195" : W = (Cmp Ne W) %"iw_1.v194", #0
    => br %"iw_1.v195" ? "iw_1.iw_4.start" : "iw_1.join" };
  ir_blk{ @"iw_1.iw_4.start":
    %"iw_1.iw_4.v6" = %"v0" +p #28;
    %"chk14" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.iw_4.v6";
    %"iw_1.iw_4.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"iw_1.iw_4.v8" : W = (Cmp Ne W) %"iw_1.iw_4.v7", #0
    => br %"iw_1.iw_4.v8" ? "iw_1.iw_4.L4" : "iw_1.iw_4.L3" };
  ir_blk{ @"iw_1.iw_4.L3":
    => goto "iw_1.iw_4.L4" };
  ir_blk{ @"iw_1.iw_4.L4" [%"iw_1.iw_4.v9" : W = phi("iw_1.iw_4.L3" => #0, "iw_1.iw_4.start" => #128)]:
    %"iw_1.v200" = %"v0" +p #8;
    %"iw_1.iw_5.v16" : W = (Cmp Eq W) %"iw_1.iw_4.v9", #0
    => br %"iw_1.iw_5.v16" ? "iw_1.iw_5.L18" : "iw_1.iw_5.L17" };
  ir_blk{ @"iw_1.iw_5.L17":
    %"iw_1.iw_5.v20" : W = (Cmp Eq W) %"iw_1.iw_4.v9", #128
    => goto "iw_1.iw_5.L18" };
  ir_blk{ @"iw_1.iw_5.L18" [%"iw_1.iw_5.v22" : W = phi("iw_1.iw_4.L4" => #1, "iw_1.iw_5.L17" => %"iw_1.iw_5.v20")]:
    => br %"iw_1.iw_5.v22" ? "iw_1.iw_5.L11" : "iw_1.iw_5.L14" };
  ir_blk{ @"iw_1.iw_5.L14":
    %"iw_1.iw_5.v24" : P = Copy $"glibc_pthread_rwlock_rdlock#str.286";
    %"iw_1.iw_5.v25" : P = Copy $"glibc_pthread_rwlock_rdlock#str.287";
    %"iw_1.iw_5.v26" : P = Copy $"glibc_pthread_rwlock_rdlock#str.288";
    %"iw_1.iw_5.v27" : P = Copy $"glibc_pthread_rwlock_rdlock#str.289";
    call void $"zerrorf"(P %"iw_1.iw_5.v24", P %"iw_1.iw_5.v25", W #173, P %"iw_1.iw_5.v26", P %"iw_1.iw_5.v27")
    => goto "iw_1.iw_5.L11" };
  ir_blk{ @"iw_1.iw_5.L11":
    => br %"iw_1.iw_5.v16" ? "iw_1.iw_5.L30" : "iw_1.iw_5.L29" };
  ir_blk{ @"iw_1.iw_5.L29":
    => goto "iw_1.iw_5.L30" };
  ir_blk{ @"iw_1.iw_5.L30" [%"iw_1.iw_5.v33" : W = phi("iw_1.iw_5.L29" => #0, "iw_1.iw_5.L11" => #1)]:
    call void $"zsys_futex_wake"(P %"iw_1.v200", W #2147483647, W %"iw_1.iw_5.v33")
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L206" [%"iw_1.pr.10" : W = phi("iw_1.L166" => #0, "iw_1.L297" => #1, "iw_1.L301" => %"iw_1.pr.11")]:
    => goto "iw_1.L210" };
  ir_blk{ @"iw_1.L210":
    %"iw_1.v214" = %"v0" +p #8;
    %"chk15" : A = (HalfCheck Lower 0 4 Read 1) %"chk1", %"iw_1.v214";
    %"iw_1.v215" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"iw_1.v216" : W = Or %"iw_1.v215", #2;
    %"iw_1.v218" : W = (Cmp Eq W) %"iw_1.v216", #3
    => br %"iw_1.v218" ? "iw_1.iw_6.start" : "iw_1.L212" };
  ir_blk{ @"iw_1.iw_6.start":
    %"iw_1.iw_6.v6" = %"v0" +p #28;
    %"chk16" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.iw_6.v6";
    %"iw_1.iw_6.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"iw_1.iw_6.v8" : W = (Cmp Ne W) %"iw_1.iw_6.v7", #0
    => br %"iw_1.iw_6.v8" ? "iw_1.iw_6.L4" : "iw_1.iw_6.L3" };
  ir_blk{ @"iw_1.iw_6.L3":
    => goto "iw_1.iw_6.L4" };
  ir_blk{ @"iw_1.iw_6.L4" [%"iw_1.iw_6.v9" : W = phi("iw_1.iw_6.L3" => #0, "iw_1.iw_6.start" => #128)]:
    %"iw_1.v226" : W = And %"iw_1.v215", #2;
    %"iw_1.v227" : W = (Cmp Eq W) %"iw_1.v226", #0
    => br %"iw_1.v227" ? "iw_1.L228" : "iw_1.L229" };
  ir_blk{ @"iw_1.L228":
    %"iw_1.v231" = %"v0" +p #8;
    %"chk17" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"iw_1.v231";
    %"iw_1.v235" : W = (RawCas (CasNarrow Uw) 0) %"chk17", %"iw_1.v215", %"iw_1.v216";
    %"iw_1.v236" : W = (Cmp Eq W) %"iw_1.v235", %"iw_1.v215"
    => br %"iw_1.v236" ? "iw_1.L238" : "iw_1.L237" };
  ir_blk{ @"iw_1.L237":
    => goto "iw_1.L238" };
  ir_blk{ @"iw_1.L238":
    %"iw_1.v239" : W = (Cmp Ne W) %"iw_1.v235", %"iw_1.v215"
    => goto "iw_1.L229" };
  ir_blk{ @"iw_1.L229" [%"iw_1.v241" : W = phi("iw_1.iw_6.L4" => #0, "iw_1.L238" => %"iw_1.v239")]:
    => br %"iw_1.v241" ? poll "iw_1.L210" : "iw_1.L224" };
  ir_blk{ @"iw_1.L224":
    %"iw_1.v245" = %"v0" +p #8;
    call %"iw_1.v250" : W = $"__GI___futex_abstimed_wait64"(P %"iw_1.v245", W #3, W #0, P %"iw_1.v4", W %"iw_1.iw_6.v9");
    %"iw_1.v255" : W = (Cmp Eq W) %"iw_1.v250", #110
    => br %"iw_1.v255" ? "iw_1.L257" : "iw_1.L256" };
  ir_blk{ @"iw_1.L256":
    %"iw_1.v259" : W = (Cmp Eq W) %"iw_1.v250", #75
    => goto "iw_1.L257" };
  ir_blk{ @"iw_1.L257" [%"iw_1.v261" : W = phi("iw_1.L224" => #1, "iw_1.L256" => %"iw_1.v259")]:
    => br %"iw_1.v261" ? "iw_1.L251" : poll "iw_1.L210" };
  ir_blk{ @"iw_1.L251":
    %"chk18" : A = (Renew 0 4 Read 1) %"chk8", %"v0";
    %"iw_1.v263" : W = (RawLoad (LdNarrow Uw) 0) %"chk18"
    => goto "iw_1.L264" };
  ir_blk{ @"iw_1.L264" [%"iw_1.pr.5" : W = phi("iw_1.L251" => %"iw_1.v263", "iw_1.L281" => %"iw_1.pr.6")]:
    %"iw_1.v268" : W = And %"iw_1.pr.5", #1
    => br %"iw_1.v268" ? "iw_1.L265" : "iw_1.L284" };
  ir_blk{ @"iw_1.L265":
    %"iw_1.v276" : W = Sub %"iw_1.pr.5", #8;
    %"chk19" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v0";
    %"iw_1.v278" : W = (RawCas (CasNarrow Uw) 0) %"chk19", %"iw_1.pr.5", %"iw_1.v276";
    %"iw_1.v279" : W = (Cmp Eq W) %"iw_1.v278", %"iw_1.pr.5"
    => br %"iw_1.v279" ? "iw_1.L281" : "iw_1.L280" };
  ir_blk{ @"iw_1.L280":
    => goto "iw_1.L281" };
  ir_blk{ @"iw_1.L281" [%"iw_1.pr.6" : W = phi("iw_1.L265" => %"iw_1.pr.5", "iw_1.L280" => %"iw_1.v278")]:
    => br %"iw_1.v279" ? "iw_1.join" : poll "iw_1.L264" };
  ir_blk{ @"iw_1.L284":
    %"iw_1.v288" = %"v0" +p #8;
    %"chk20" : A = (Renew 0 4 Read 1) %"chk15", %"iw_1.v288";
    %"iw_1.v289" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"iw_1.v290" : W = Or %"iw_1.v289", #2;
    %"iw_1.v292" : W = (Cmp Eq W) %"iw_1.v290", #3
    => br %"iw_1.v292" ? poll "iw_1.L284" : "iw_1.L212" };
  ir_blk{ @"iw_1.L212" [%"iw_1.pr.11" : W = phi("iw_1.L210" => %"iw_1.pr.10", "iw_1.L284" => #1)]:
    %"iw_1.v298" : W = (Ext Ub) %"iw_1.pr.11"
    => br %"iw_1.v298" ? "iw_1.join" : "iw_1.L297" };
  ir_blk{ @"iw_1.L297":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk8", %"v0";
    %"iw_1.v304" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"iw_1.v305" : W = And %"iw_1.v304", #1
    => br %"iw_1.v305" ? "iw_1.L301" : poll "iw_1.L206" };
  ir_blk{ @"iw_1.L301":
    => goto poll "iw_1.L206" };
  ir_blk{ @"iw_1.join" [%"v7" : W = phi("iw_1.L14" => #22, "iw_1.L9" => #35, "iw_1.L109" => %"iw_1.v102", "iw_1.L148" => #11, "iw_1.L129" => #0, "iw_1.L190" => #0, "iw_1.iw_5.L30" => #0, "iw_1.L281" => %"iw_1.v250", "iw_1.L212" => #0)]:
    => ret %"v7" }])) }.

Definition hello_image_fn____pthread_rwlock_unlock : func :=
  ir_fn{ "export" "___pthread_rwlock_unlock"(P %"v0") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v9" = %"v0" +p #24;
    %"chk0" : A = (Check 0 4 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"v11" : P = $"zthread_self_cookie"();
    %"v12" = %"v11" +p #720;
    %"chk1" : A = (Check 0 4 Read 1) %"v12";
    %"v13" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v14" : W = (Cmp Eq W) %"v10", %"v13"
    => br %"v14" ? "iw_1.start" : "iw_2.start" };
  ir_blk{ @"iw_1.start":
    %"iw_1.iw_1.v6" = %"v0" +p #28;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"iw_1.iw_1.v6";
    %"iw_1.iw_1.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.iw_1.v8" : W = (Cmp Ne W) %"iw_1.iw_1.v7", #0
    => br %"iw_1.iw_1.v8" ? "iw_1.iw_1.L4" : "iw_1.iw_1.L3" };
  ir_blk{ @"iw_1.iw_1.L3":
    => goto "iw_1.iw_1.L4" };
  ir_blk{ @"iw_1.iw_1.L4" [%"iw_1.iw_1.v9" : W = phi("iw_1.iw_1.L3" => #0, "iw_1.start" => #128)]:
    %"iw_1.v9" = %"v0" +p #24;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk0", %"iw_1.v9";
    store Ww [%"chk3" + 0] <- #0;
    %"iw_1.v12" = %"v0" +p #12;
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"iw_1.v12";
    %"iw_1.v13" : W = (RawLoad (LdNarrow Uw) 0) %"chk4"
    => goto "iw_1.L14" };
  ir_blk{ @"iw_1.L14" [%"iw_1.v16" : W = phi("iw_1.iw_1.L4" => %"iw_1.v13", "iw_1.L14" => %"iw_1.v17")]:
    %"chk5" : A = (HalfCheck Lower 0 4 Write 4) %"chk4", %"iw_1.v12";
    %"iw_1.v17" : W = (RawCas (CasNarrow Uw) 0) %"chk5", %"iw_1.v16", #0;
    %"iw_1.v18" : W = (Cmp Eq W) %"iw_1.v17", %"iw_1.v16"
    => br %"iw_1.v18" ? "iw_1.L15" : poll "iw_1.L14" };
  ir_blk{ @"iw_1.L15":
    %"iw_1.v19" : W = And %"iw_1.v16", #2;
    %"iw_1.v20" : W = (Cmp Ne W) %"iw_1.v19", #0;
    %"iw_1.v26" = %"v0" +p #48;
    %"chk6" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"iw_1.v26";
    %"iw_1.v27" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"iw_1.v28" : W = (Cmp Ne W) %"iw_1.v27", #0
    => br %"iw_1.v28" ? "iw_1.L22" : "iw_1.L24" };
  ir_blk{ @"iw_1.L22":
    %"iw_1.v31" = %"v0" +p #4;
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"iw_1.v31";
    %"iw_1.v32" : W = (RawLoad (LdNarrow Uw) 0) %"chk7"
    => goto "iw_1.L33" };
  ir_blk{ @"iw_1.L33" [%"iw_1.pr.1" : W = phi("iw_1.L22" => %"iw_1.v32", "iw_1.L52" => %"iw_1.pr.2")]:
    %"iw_1.v37" : W = (Cmp Ne W) %"iw_1.pr.1", #0
    => br %"iw_1.v37" ? "iw_1.L34" : "iw_1.L24" };
  ir_blk{ @"iw_1.L34":
    %"iw_1.v42" = %"v0" +p #4;
    %"iw_1.v47" : W = Or %"iw_1.pr.1", #2147483648;
    %"chk8" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"iw_1.v42";
    %"iw_1.v49" : W = (RawCas (CasNarrow Uw) 0) %"chk8", %"iw_1.pr.1", %"iw_1.v47";
    %"iw_1.v50" : W = (Cmp Eq W) %"iw_1.v49", %"iw_1.pr.1"
    => br %"iw_1.v50" ? "iw_1.L52" : "iw_1.L51" };
  ir_blk{ @"iw_1.L51":
    => goto "iw_1.L52" };
  ir_blk{ @"iw_1.L52" [%"iw_1.pr.2" : W = phi("iw_1.L34" => %"iw_1.pr.1", "iw_1.L51" => %"iw_1.v49")]:
    => br %"iw_1.v50" ? "iw_1.L53" : poll "iw_1.L33" };
  ir_blk{ @"iw_1.L24":
    %"chk9" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v57" : W = (RawLoad (LdNarrow Uw) 0) %"chk9"
    => goto "iw_1.L58" };
  ir_blk{ @"iw_1.L58" [%"iw_1.pr.3" : W = phi("iw_1.L24" => %"iw_1.v57", "iw_1.L76" => %"iw_1.pr.4")]:
    %"iw_1.v63" : W = Xor %"iw_1.pr.3", #2;
    %"iw_1.v68" : W = Shr %"iw_1.pr.3", #3;
    %"iw_1.v69" : W = (Cmp Eq W) %"iw_1.v68", #0
    => br %"iw_1.v69" ? "iw_1.L66" : "iw_1.L65" };
  ir_blk{ @"iw_1.L65":
    => goto "iw_1.L66" };
  ir_blk{ @"iw_1.L66" [%"iw_1.v70" : W = phi("iw_1.L65" => #1, "iw_1.L58" => #0)]:
    %"iw_1.v71" : W = Xor %"iw_1.v63", %"iw_1.v70";
    %"chk10" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v0";
    %"iw_1.v73" : W = (RawCas (CasNarrow Uw) 0) %"chk10", %"iw_1.pr.3", %"iw_1.v71";
    %"iw_1.v74" : W = (Cmp Eq W) %"iw_1.v73", %"iw_1.pr.3"
    => br %"iw_1.v74" ? "iw_1.L76" : "iw_1.L75" };
  ir_blk{ @"iw_1.L75":
    => goto "iw_1.L76" };
  ir_blk{ @"iw_1.L76" [%"iw_1.pr.4" : W = phi("iw_1.L66" => %"iw_1.pr.3", "iw_1.L75" => %"iw_1.v73")]:
    %"iw_1.v77" : W = (Cmp Ne W) %"iw_1.v73", %"iw_1.pr.3"
    => br %"iw_1.v77" ? poll "iw_1.L58" : "iw_1.L60" };
  ir_blk{ @"iw_1.L60":
    %"iw_1.v82" : W = Shr %"iw_1.pr.4", #3;
    %"iw_1.v83" : W = (Cmp Ne W) %"iw_1.v82", #0
    => br %"iw_1.v83" ? "iw_1.L78" : "iw_1.L53" };
  ir_blk{ @"iw_1.L78":
    %"iw_1.v88" = %"v0" +p #8;
    %"chk11" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"iw_1.v88";
    %"iw_1.v89" : W = (RawLoad (LdNarrow Uw) 0) %"chk11"
    => goto "iw_1.L90" };
  ir_blk{ @"iw_1.L90" [%"iw_1.v92" : W = phi("iw_1.L78" => %"iw_1.v89", "iw_1.L90" => %"iw_1.v93")]:
    %"chk12" : A = (HalfCheck Lower 0 4 Write 4) %"chk11", %"iw_1.v88";
    %"iw_1.v93" : W = (RawCas (CasNarrow Uw) 0) %"chk12", %"iw_1.v92", #0;
    %"iw_1.v94" : W = (Cmp Eq W) %"iw_1.v93", %"iw_1.v92"
    => br %"iw_1.v94" ? "iw_1.L91" : poll "iw_1.L90" };
  ir_blk{ @"iw_1.L91":
    %"iw_1.v95" : W = And %"iw_1.v92", #2;
    %"iw_1.v96" : W = (Cmp Ne W) %"iw_1.v95", #0
    => br %"iw_1.v96" ? "iw_1.L84" : "iw_1.L53" };
  ir_blk{ @"iw_1.L84":
    %"iw_1.v98" = %"v0" +p #8;
    %"iw_1.iw_2.v16" : W = (Cmp Eq W) %"iw_1.iw_1.v9", #0
    => br %"iw_1.iw_2.v16" ? "iw_1.iw_2.L18" : "iw_1.iw_2.L17" };
  ir_blk{ @"iw_1.iw_2.L17":
    %"iw_1.iw_2.v20" : W = (Cmp Eq W) %"iw_1.iw_1.v9", #128
    => goto "iw_1.iw_2.L18" };
  ir_blk{ @"iw_1.iw_2.L18" [%"iw_1.iw_2.v22" : W = phi("iw_1.L84" => #1, "iw_1.iw_2.L17" => %"iw_1.iw_2.v20")]:
    => br %"iw_1.iw_2.v22" ? "iw_1.iw_2.L11" : "iw_1.iw_2.L14" };
  ir_blk{ @"iw_1.iw_2.L14":
    %"iw_1.iw_2.v24" : P = Copy $"glibc_pthread_rwlock_unlock#str.286";
    %"iw_1.iw_2.v25" : P = Copy $"glibc_pthread_rwlock_unlock#str.287";
    %"iw_1.iw_2.v26" : P = Copy $"glibc_pthread_rwlock_unlock#str.288";
    %"iw_1.iw_2.v27" : P = Copy $"glibc_pthread_rwlock_unlock#str.289";
    call void $"zerrorf"(P %"iw_1.iw_2.v24", P %"iw_1.iw_2.v25", W #173, P %"iw_1.iw_2.v26", P %"iw_1.iw_2.v27")
    => goto "iw_1.iw_2.L11" };
  ir_blk{ @"iw_1.iw_2.L11":
    => br %"iw_1.iw_2.v16" ? "iw_1.iw_2.L30" : "iw_1.iw_2.L29" };
  ir_blk{ @"iw_1.iw_2.L29":
    => goto "iw_1.iw_2.L30" };
  ir_blk{ @"iw_1.iw_2.L30" [%"iw_1.iw_2.v33" : W = phi("iw_1.iw_2.L29" => #0, "iw_1.iw_2.L11" => #1)]:
    call void $"zsys_futex_wake"(P %"iw_1.v98", W #2147483647, W %"iw_1.iw_2.v33")
    => goto "iw_1.L53" };
  ir_blk{ @"iw_1.L53":
    => br %"iw_1.v20" ? "iw_1.L100" : "L7" };
  ir_blk{ @"iw_1.L100":
    %"iw_1.v105" = %"v0" +p #12;
    %"iw_1.iw_3.v16" : W = (Cmp Eq W) %"iw_1.iw_1.v9", #0
    => br %"iw_1.iw_3.v16" ? "iw_1.iw_3.L18" : "iw_1.iw_3.L17" };
  ir_blk{ @"iw_1.iw_3.L17":
    %"iw_1.iw_3.v20" : W = (Cmp Eq W) %"iw_1.iw_1.v9", #128
    => goto "iw_1.iw_3.L18" };
  ir_blk{ @"iw_1.iw_3.L18" [%"iw_1.iw_3.v22" : W = phi("iw_1.L100" => #1, "iw_1.iw_3.L17" => %"iw_1.iw_3.v20")]:
    => br %"iw_1.iw_3.v22" ? "iw_1.iw_3.L11" : "iw_1.iw_3.L14" };
  ir_blk{ @"iw_1.iw_3.L14":
    %"iw_1.iw_3.v24" : P = Copy $"glibc_pthread_rwlock_unlock#str.286";
    %"iw_1.iw_3.v25" : P = Copy $"glibc_pthread_rwlock_unlock#str.287";
    %"iw_1.iw_3.v26" : P = Copy $"glibc_pthread_rwlock_unlock#str.288";
    %"iw_1.iw_3.v27" : P = Copy $"glibc_pthread_rwlock_unlock#str.289";
    call void $"zerrorf"(P %"iw_1.iw_3.v24", P %"iw_1.iw_3.v25", W #173, P %"iw_1.iw_3.v26", P %"iw_1.iw_3.v27")
    => goto "iw_1.iw_3.L11" }] [ir_blk{ @"iw_1.iw_3.L11":
    => br %"iw_1.iw_3.v16" ? "iw_1.iw_3.L30" : "iw_1.iw_3.L29" };
  ir_blk{ @"iw_1.iw_3.L29":
    => goto "iw_1.iw_3.L30" };
  ir_blk{ @"iw_1.iw_3.L30" [%"iw_1.iw_3.v33" : W = phi("iw_1.iw_3.L29" => #0, "iw_1.iw_3.L11" => #1)]:
    call void $"zsys_futex_wake"(P %"iw_1.v105", W #1, W %"iw_1.iw_3.v33")
    => goto "L7" };
  ir_blk{ @"iw_2.start":
    %"iw_2.iw_1.v6" = %"v0" +p #28;
    %"chk13" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"iw_2.iw_1.v6";
    %"iw_2.iw_1.v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"iw_2.iw_1.v8" : W = (Cmp Ne W) %"iw_2.iw_1.v7", #0
    => br %"iw_2.iw_1.v8" ? "iw_2.iw_1.L4" : "iw_2.iw_1.L3" };
  ir_blk{ @"iw_2.iw_1.L3":
    => goto "iw_2.iw_1.L4" };
  ir_blk{ @"iw_2.iw_1.L4" [%"iw_2.iw_1.v9" : W = phi("iw_2.iw_1.L3" => #0, "iw_2.start" => #128)]:
    %"chk14" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"iw_2.v7" : W = (RawLoad (LdNarrow Uw) 0) %"chk14"
    => goto "iw_2.L9" };
  ir_blk{ @"iw_2.L9" [%"iw_2.pr.2" : W = phi("iw_2.iw_1.L4" => %"iw_2.v7", "iw_2.L42" => %"iw_2.pr.1")]:
    %"iw_2.v15" : W = Sub %"iw_2.pr.2", #8;
    %"iw_2.v20" : W = Shr %"iw_2.v15", #3;
    %"iw_2.v21" : W = (Cmp Eq W) %"iw_2.v20", #0
    => br %"iw_2.v21" ? "iw_2.L16" : "iw_2.L18" };
  ir_blk{ @"iw_2.L16":
    %"iw_2.v26" : W = And %"iw_2.v15", #2;
    %"iw_2.v27" : W = (Cmp Ne W) %"iw_2.v26", #0
    => br %"iw_2.v27" ? "iw_2.L22" : "iw_2.L24" };
  ir_blk{ @"iw_2.L22":
    %"iw_2.v29" : W = Or %"iw_2.v15", #1
    => goto "iw_2.L24" };
  ir_blk{ @"iw_2.L24" [%"iw_2.pr.4" : W = phi("iw_2.L22" => %"iw_2.v29", "iw_2.L16" => %"iw_2.v15")]:
    %"iw_2.v32" : W = And %"iw_2.pr.4", #4294967291
    => goto "iw_2.L18" };
  ir_blk{ @"iw_2.L18" [%"iw_2.pr.3" : W = phi("iw_2.L24" => %"iw_2.v32", "iw_2.L9" => %"iw_2.v15")]:
    %"chk15" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v0";
    %"iw_2.v39" : W = (RawCas (CasNarrow Uw) 0) %"chk15", %"iw_2.pr.2", %"iw_2.pr.3";
    %"iw_2.v40" : W = (Cmp Eq W) %"iw_2.v39", %"iw_2.pr.2"
    => br %"iw_2.v40" ? "iw_2.L42" : "iw_2.L41" };
  ir_blk{ @"iw_2.L41":
    => goto "iw_2.L42" };
  ir_blk{ @"iw_2.L42" [%"iw_2.pr.1" : W = phi("iw_2.L18" => %"iw_2.pr.2", "iw_2.L41" => %"iw_2.v39")]:
    => br %"iw_2.v40" ? "iw_2.L12" : poll "iw_2.L9" };
  ir_blk{ @"iw_2.L12":
    %"iw_2.v48" : W = And %"iw_2.pr.3", #1
    => br %"iw_2.v48" ? "iw_2.L44" : "iw_2.L46" };
  ir_blk{ @"iw_2.L44":
    %"iw_2.v54" = %"v0" +p #8;
    %"chk16" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"iw_2.v54";
    %"iw_2.v55" : W = (RawLoad (LdNarrow Uw) 0) %"chk16"
    => goto "iw_2.L56" };
  ir_blk{ @"iw_2.L56" [%"iw_2.v58" : W = phi("iw_2.L44" => %"iw_2.v55", "iw_2.L56" => %"iw_2.v59")]:
    %"chk17" : A = (HalfCheck Lower 0 4 Write 4) %"chk16", %"iw_2.v54";
    %"iw_2.v59" : W = (RawCas (CasNarrow Uw) 0) %"chk17", %"iw_2.v58", #1;
    %"iw_2.v60" : W = (Cmp Eq W) %"iw_2.v59", %"iw_2.v58"
    => br %"iw_2.v60" ? "iw_2.L57" : poll "iw_2.L56" };
  ir_blk{ @"iw_2.L57":
    %"iw_2.v61" : W = And %"iw_2.v58", #2;
    %"iw_2.v62" : W = (Cmp Ne W) %"iw_2.v61", #0
    => br %"iw_2.v62" ? "iw_2.L50" : "iw_2.L46" };
  ir_blk{ @"iw_2.L50":
    %"iw_2.v64" = %"v0" +p #8;
    %"iw_2.iw_2.v16" : W = (Cmp Eq W) %"iw_2.iw_1.v9", #0
    => br %"iw_2.iw_2.v16" ? "iw_2.iw_2.L18" : "iw_2.iw_2.L17" };
  ir_blk{ @"iw_2.iw_2.L17":
    %"iw_2.iw_2.v20" : W = (Cmp Eq W) %"iw_2.iw_1.v9", #128
    => goto "iw_2.iw_2.L18" };
  ir_blk{ @"iw_2.iw_2.L18" [%"iw_2.iw_2.v22" : W = phi("iw_2.L50" => #1, "iw_2.iw_2.L17" => %"iw_2.iw_2.v20")]:
    => br %"iw_2.iw_2.v22" ? "iw_2.iw_2.L11" : "iw_2.iw_2.L14" };
  ir_blk{ @"iw_2.iw_2.L14":
    %"iw_2.iw_2.v24" : P = Copy $"glibc_pthread_rwlock_unlock#str.286";
    %"iw_2.iw_2.v25" : P = Copy $"glibc_pthread_rwlock_unlock#str.287";
    %"iw_2.iw_2.v26" : P = Copy $"glibc_pthread_rwlock_unlock#str.288";
    %"iw_2.iw_2.v27" : P = Copy $"glibc_pthread_rwlock_unlock#str.289";
    call void $"zerrorf"(P %"iw_2.iw_2.v24", P %"iw_2.iw_2.v25", W #173, P %"iw_2.iw_2.v26", P %"iw_2.iw_2.v27")
    => goto "iw_2.iw_2.L11" };
  ir_blk{ @"iw_2.iw_2.L11":
    => br %"iw_2.iw_2.v16" ? "iw_2.iw_2.L30" : "iw_2.iw_2.L29" };
  ir_blk{ @"iw_2.iw_2.L29":
    => goto "iw_2.iw_2.L30" };
  ir_blk{ @"iw_2.iw_2.L30" [%"iw_2.iw_2.v33" : W = phi("iw_2.iw_2.L29" => #0, "iw_2.iw_2.L11" => #1)]:
    call void $"zsys_futex_wake"(P %"iw_2.v64", W #2147483647, W %"iw_2.iw_2.v33")
    => goto "iw_2.L46" };
  ir_blk{ @"iw_2.L46":
    %"iw_2.v70" : W = And %"iw_2.pr.1", #4;
    %"iw_2.v72" : W = And %"iw_2.pr.3", #4;
    %"iw_2.v73" : W = (Cmp Ne W) %"iw_2.v70", %"iw_2.v72"
    => br %"iw_2.v73" ? "iw_2.iw_3.start" : "L7" };
  ir_blk{ @"iw_2.iw_3.start":
    %"iw_2.iw_3.v16" : W = (Cmp Eq W) %"iw_2.iw_1.v9", #0
    => br %"iw_2.iw_3.v16" ? "iw_2.iw_3.L18" : "iw_2.iw_3.L17" };
  ir_blk{ @"iw_2.iw_3.L17":
    %"iw_2.iw_3.v20" : W = (Cmp Eq W) %"iw_2.iw_1.v9", #128
    => goto "iw_2.iw_3.L18" };
  ir_blk{ @"iw_2.iw_3.L18" [%"iw_2.iw_3.v22" : W = phi("iw_2.iw_3.start" => #1, "iw_2.iw_3.L17" => %"iw_2.iw_3.v20")]:
    => br %"iw_2.iw_3.v22" ? "iw_2.iw_3.L11" : "iw_2.iw_3.L14" };
  ir_blk{ @"iw_2.iw_3.L14":
    %"iw_2.iw_3.v24" : P = Copy $"glibc_pthread_rwlock_unlock#str.286";
    %"iw_2.iw_3.v25" : P = Copy $"glibc_pthread_rwlock_unlock#str.287";
    %"iw_2.iw_3.v26" : P = Copy $"glibc_pthread_rwlock_unlock#str.288";
    %"iw_2.iw_3.v27" : P = Copy $"glibc_pthread_rwlock_unlock#str.289";
    call void $"zerrorf"(P %"iw_2.iw_3.v24", P %"iw_2.iw_3.v25", W #173, P %"iw_2.iw_3.v26", P %"iw_2.iw_3.v27")
    => goto "iw_2.iw_3.L11" };
  ir_blk{ @"iw_2.iw_3.L11":
    => br %"iw_2.iw_3.v16" ? "iw_2.iw_3.L30" : "iw_2.iw_3.L29" };
  ir_blk{ @"iw_2.iw_3.L29":
    => goto "iw_2.iw_3.L30" };
  ir_blk{ @"iw_2.iw_3.L30" [%"iw_2.iw_3.v33" : W = phi("iw_2.iw_3.L29" => #0, "iw_2.iw_3.L11" => #1)]:
    call void $"zsys_futex_wake"(P %"v0", W #2147483647, W %"iw_2.iw_3.v33")
    => goto "L7" };
  ir_blk{ @"L7":
    => ret #0 }])) }.
