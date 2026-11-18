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

Definition hi_fn_glibc_malloc'23_dl_tunable_set_mmap_threshold : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_mmap_threshold"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #16;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk1" + 0] <- %"v4";
    %"iw_1.v8" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v9" = %"iw_1.v8" +p #80;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v9";
    store Ww [%"chk2" + 0] <- #1
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_mmaps_max : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_mmaps_max"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v5" : W = Copy %"v4";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #72;
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.v6";
    store Ww [%"chk1" + 0] <- %"v5";
    %"iw_1.v8" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v9" = %"iw_1.v8" +p #80;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v9";
    store Ww [%"chk2" + 0] <- #1
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_top_pad : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_top_pad"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #8;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk1" + 0] <- %"v4";
    %"iw_1.v8" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v9" = %"iw_1.v8" +p #80;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v9";
    store Ww [%"chk2" + 0] <- #1
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_perturb_byte : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_perturb_byte"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v5" : W = Copy %"v4";
    %"iw_1.v5" : P = Copy $"glibc_malloc#perturb_byte";
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.v5";
    store Ww [%"chk1" + 0] <- %"v5"
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_trim_threshold : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_trim_threshold"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v5";
    store Wl [%"chk1" + 0] <- %"v4";
    %"iw_1.v7" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v8" = %"iw_1.v7" +p #80;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v8";
    store Ww [%"chk2" + 0] <- #1
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_arena_max : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_arena_max"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #32;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk1" + 0] <- %"v4"
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_arena_test : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_arena_test"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #24;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk1" + 0] <- %"v4"
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_tcache_max : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_tcache_max"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v6" : W = (Cmp Ugt L) %"v4", #9223372036854775807
    => br %"iw_1.v6" ? "iw_1.join" : "iw_1.iw_1.start";
  @"iw_1.iw_1.start":
    => br %"iw_1.v6" ? "iw_1.iw_1.join" : "iw_1.iw_1.L4";
  @"iw_1.iw_1.L4":
    %"iw_1.iw_1.v14" : L = Add %"v4", #8;
    %"iw_1.iw_1.v23" : L = Add %"iw_1.iw_1.v14", #15;
    %"iw_1.iw_1.v43" : W = (Cmp Ult L) %"iw_1.iw_1.v23", #32
    => br %"iw_1.iw_1.v43" ? "iw_1.iw_1.join" : "iw_1.iw_1.L76";
  @"iw_1.iw_1.L76":
    %"iw_1.iw_1.v83" : L = And %"iw_1.iw_1.v23", #18446744073709551600
    => goto "iw_1.iw_1.join";
  @"iw_1.iw_1.join" [%"iw_1.v10" : L = phi("iw_1.iw_1.start" => #18446744073709551615, "iw_1.iw_1.L4" => #32, "iw_1.iw_1.L76" => %"iw_1.iw_1.v83")]:
    %"iw_1.v32" : L = Sub %"iw_1.v10", #32;
    %"iw_1.v40" : L = Shr %"iw_1.v32", #4;
    %"iw_1.v45" : W = (Cmp Uge L) %"iw_1.v40", #64
    => br %"iw_1.v45" ? "iw_1.iw_2.start" : "iw_1.L43";
  @"iw_1.iw_2.start":
    %"iw_1.iw_2.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_1.v10", #0
    => br %"iw_1.iw_2.iw_1.iw_1.v6" ? "iw_1.iw_2.iw_1.iw_1.L4" : "iw_1.iw_2.iw_1.iw_1.L3";
  @"iw_1.iw_2.iw_1.iw_1.L3":
    %"iw_1.iw_2.iw_1.iw_1.v8" : L = Shr %"iw_1.v10", #1;
    %"iw_1.iw_2.iw_1.iw_1.v9" : L = Or %"iw_1.v10", %"iw_1.iw_2.iw_1.iw_1.v8";
    %"iw_1.iw_2.iw_1.iw_1.v10" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v9", #2;
    %"iw_1.iw_2.iw_1.iw_1.v11" : L = Or %"iw_1.iw_2.iw_1.iw_1.v9", %"iw_1.iw_2.iw_1.iw_1.v10";
    %"iw_1.iw_2.iw_1.iw_1.v12" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v11", #4;
    %"iw_1.iw_2.iw_1.iw_1.v13" : L = Or %"iw_1.iw_2.iw_1.iw_1.v11", %"iw_1.iw_2.iw_1.iw_1.v12";
    %"iw_1.iw_2.iw_1.iw_1.v14" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v13", #8;
    %"iw_1.iw_2.iw_1.iw_1.v15" : L = Or %"iw_1.iw_2.iw_1.iw_1.v13", %"iw_1.iw_2.iw_1.iw_1.v14";
    %"iw_1.iw_2.iw_1.iw_1.v16" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v15", #16;
    %"iw_1.iw_2.iw_1.iw_1.v17" : L = Or %"iw_1.iw_2.iw_1.iw_1.v15", %"iw_1.iw_2.iw_1.iw_1.v16";
    %"iw_1.iw_2.iw_1.iw_1.v18" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v17", #32;
    %"iw_1.iw_2.iw_1.iw_1.v19" : L = Or %"iw_1.iw_2.iw_1.iw_1.v17", %"iw_1.iw_2.iw_1.iw_1.v18";
    %"iw_1.iw_2.iw_1.iw_1.v20" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v19", #1;
    %"iw_1.iw_2.iw_1.iw_1.v21" : L = And %"iw_1.iw_2.iw_1.iw_1.v20", #6148914691236517205;
    %"iw_1.iw_2.iw_1.iw_1.v22" : L = Sub %"iw_1.iw_2.iw_1.iw_1.v19", %"iw_1.iw_2.iw_1.iw_1.v21";
    %"iw_1.iw_2.iw_1.iw_1.v23" : L = And %"iw_1.iw_2.iw_1.iw_1.v22", #3689348814741910323;
    %"iw_1.iw_2.iw_1.iw_1.v24" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v22", #2;
    %"iw_1.iw_2.iw_1.iw_1.v25" : L = And %"iw_1.iw_2.iw_1.iw_1.v24", #3689348814741910323;
    %"iw_1.iw_2.iw_1.iw_1.v26" : L = Add %"iw_1.iw_2.iw_1.iw_1.v23", %"iw_1.iw_2.iw_1.iw_1.v25";
    %"iw_1.iw_2.iw_1.iw_1.v27" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v26", #4;
    %"iw_1.iw_2.iw_1.iw_1.v28" : L = Add %"iw_1.iw_2.iw_1.iw_1.v26", %"iw_1.iw_2.iw_1.iw_1.v27";
    %"iw_1.iw_2.iw_1.iw_1.v29" : L = And %"iw_1.iw_2.iw_1.iw_1.v28", #1085102592571150095;
    %"iw_1.iw_2.iw_1.iw_1.v30" : L = Mul %"iw_1.iw_2.iw_1.iw_1.v29", #72340172838076673;
    %"iw_1.iw_2.iw_1.iw_1.v31" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v30", #56;
    %"iw_1.iw_2.iw_1.iw_1.v32" : L = Sub %"iw_1.iw_2.iw_1.iw_1.v31", #64;
    %"iw_1.iw_2.iw_1.iw_1.v33" : L = Neg %"iw_1.iw_2.iw_1.iw_1.v32"
    => goto "iw_1.iw_2.iw_1.iw_1.L4";
  @"iw_1.iw_2.iw_1.iw_1.L4" [%"iw_1.iw_2.iw_1.iw_1.v34" : W = phi("iw_1.iw_2.iw_1.iw_1.L3" => %"iw_1.iw_2.iw_1.iw_1.v33", "iw_1.iw_2.start" => #64)]:
    %"iw_1.iw_2.iw_1.v4" : W = Sub #64, %"iw_1.iw_2.iw_1.iw_1.v34";
    %"iw_1.iw_2.v35" : W = Sub %"iw_1.iw_2.iw_1.v4", #11;
    %"iw_1.iw_2.v36" : L = (Ext Uw) %"iw_1.iw_2.v35";
    %"iw_1.iw_2.v38" : L = Add %"iw_1.iw_2.v36", #64
    => goto "iw_1.L43";
  @"iw_1.L43" [%"iw_1.pr.1" : L = phi("iw_1.iw_2.iw_1.iw_1.L4" => %"iw_1.iw_2.v38", "iw_1.iw_1.join" => %"iw_1.v40")]:
    %"iw_1.v57" : W = (Cmp Ult L) %"iw_1.pr.1", #76
    => br %"iw_1.v57" ? "iw_1.L51" : "iw_1.join";
  @"iw_1.L51":
    %"iw_1.v62" : W = (Cmp Ult L) %"iw_1.pr.1", #64
    => br %"iw_1.v62" ? "iw_1.L58" : "iw_1.L60";
  @"iw_1.L58":
    %"iw_1.v63" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v64" = %"iw_1.v63" +p #112;
    %"iw_1.v66" : L = Add %"iw_1.pr.1", #1;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v64";
    store Wl [%"chk1" + 0] <- %"iw_1.v66"
    => goto "iw_1.L60";
  @"iw_1.L60":
    %"iw_1.v67" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v68" = %"iw_1.v67" +p #120;
    %"iw_1.v70" : L = Add %"iw_1.v10", #1;
    %"chk2" : A = (Check 0 8 Write 1) %"iw_1.v68";
    store Wl [%"chk2" + 0] <- %"iw_1.v70"
    => goto "iw_1.join";
  @"iw_1.join":
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_tcache_count : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_tcache_count"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v6" : W = (Cmp Ule L) %"v4", #65535
    => br %"iw_1.v6" ? "iw_1.L9" : "iw_1.join";
  @"iw_1.L9":
    %"iw_1.v10" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v11" = %"iw_1.v10" +p #128;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v11";
    store Wl [%"chk1" + 0] <- %"v4"
    => goto "iw_1.join";
  @"iw_1.join":
    => ret void
} }.

Definition hi_fn_glibc_malloc'23_dl_tunable_set_hugetlb : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_hugetlb"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.iw_1.v0" : P = Copy $"_dl_thp_mode";
    %"chk1" : A = (Check 0 4 Read 1) %"iw_1.iw_1.v0";
    %"iw_1.iw_1.v1" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"iw_1.v24" : W = (Cmp Eq L) %"v4", #0
    => br %"iw_1.v24" ? "iw_1.L20" : "iw_1.L21";
  @"iw_1.L20":
    %"iw_1.v25" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v26" = %"iw_1.v25" +p #40;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v26";
    store Ww [%"chk2" + 0] <- #4;
    %"iw_1.v27" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v28" = %"iw_1.v27" +p #48;
    %"chk3" : A = (Check 0 8 Write 1) %"iw_1.v28";
    store Wl [%"chk3" + 0] <- #0
    => goto "iw_1.join";
  @"iw_1.L21":
    %"iw_1.v33" : W = (Cmp Eq L) %"v4", #1
    => br %"iw_1.v33" ? "iw_1.L36" : "iw_1.L30";
  @"iw_1.L36":
    %"iw_1.v43" : W = (Cmp Eq W) %"iw_1.iw_1.v1", #0
    => br %"iw_1.v43" ? "iw_1.L39" : "iw_1.L40";
  @"iw_1.L39":
    %"iw_1.v44" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v45" = %"iw_1.v44" +p #40;
    call %"iw_1.v46" : W = $"__get_thp_mode"();
    %"chk4" : A = (Check 0 4 Write 1) %"iw_1.v45";
    store Ww [%"chk4" + 0] <- %"iw_1.v46";
    %"iw_1.v50" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v51" = %"iw_1.v50" +p #40;
    %"chk5" : A = (Check 0 4 Read 1) %"iw_1.v51";
    %"iw_1.v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"iw_1.v53" : W = (Cmp Eq W) %"iw_1.v52", #3
    => br %"iw_1.v53" ? "iw_1.L55" : "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v56" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v57" = %"iw_1.v56" +p #40;
    %"chk6" : A = (Check 0 4 Read 1) %"iw_1.v57";
    %"iw_1.v58" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"iw_1.v59" : W = (Cmp Eq W) %"iw_1.v58", #2
    => goto "iw_1.L55";
  @"iw_1.L55" [%"iw_1.v61" : W = phi("iw_1.L39" => #1, "iw_1.L54" => %"iw_1.v59")]:
    => br %"iw_1.v61" ? "iw_1.L47" : "iw_1.join";
  @"iw_1.L47":
    %"iw_1.v62" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v63" = %"iw_1.v62" +p #48;
    call %"iw_1.v64" : L = $"__get_thp_size"();
    %"chk7" : A = (Check 0 8 Write 1) %"iw_1.v63";
    store Wl [%"chk7" + 0] <- %"iw_1.v64"
    => goto "iw_1.join";
  @"iw_1.L40":
    %"iw_1.v65" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v66" = %"iw_1.v65" +p #40;
    %"chk8" : A = (Check 0 4 Write 1) %"iw_1.v66";
    store Ww [%"chk8" + 0] <- %"iw_1.iw_1.v1";
    %"iw_1.v74" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v75" = %"iw_1.v74" +p #48;
    call %"iw_1.iw_2.v1" : L = $"__get_thp_size"();
    %"iw_1.iw_2.v9" : W = (Cmp Ugt L) %"iw_1.iw_2.v1", #33554432
    => br %"iw_1.iw_2.v9" ? "iw_1.iw_2.L4" : "iw_1.iw_2.L3";
  @"iw_1.iw_2.L3":
    => goto "iw_1.iw_2.L4";
  @"iw_1.iw_2.L4" [%"iw_1.iw_2.pr.1" : L = phi("iw_1.iw_2.L3" => %"iw_1.iw_2.v1", "iw_1.L40" => #0)]:
    %"chk9" : A = (Check 0 8 Write 1) %"iw_1.v75";
    store Wl [%"chk9" + 0] <- %"iw_1.iw_2.pr.1"
    => goto "iw_1.join";
  @"iw_1.L30":
    %"iw_1.v84" : W = (Cmp Uge L) %"v4", #2
    => br %"iw_1.v84" ? "iw_1.L80" : "iw_1.join";
  @"iw_1.L80":
    %"iw_1.v89" : W = (Cmp Eq L) %"v4", #2
    => br %"iw_1.v89" ? "iw_1.L87" : "iw_1.L86";
  @"iw_1.L86":
    => goto "iw_1.L87";
  @"iw_1.L87" [%"iw_1.v91" : L = phi("iw_1.L86" => %"v4", "iw_1.L80" => #0)]:
    %"iw_1.v92" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v93" = %"iw_1.v92" +p #56;
    %"iw_1.v94" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v95" = %"iw_1.v94" +p #64;
    call void $"__get_hugepage_config"(L %"iw_1.v91", P %"iw_1.v93", P %"iw_1.v95")
    => goto "iw_1.join";
  @"iw_1.join":
    => ret void
} }.

Definition hi_fn_glibc_libc_start'23dl_init_cacheinfo : func :=
  ir_fn{ "local" "glibc_libc_start#dl_init_cacheinfo"(P %"v0") -> RVoid {
  @"start":
    %"v5" : P = (Alloc 8) #8;
    %"v8" : P = (Alloc 8) #8;
    %"v11" : P = (Alloc 4) #4;
    %"v54" : P = (Alloc 4) #276;
    %"v333" : P = (Alloc 8) #8;
    %"v343" : P = (Alloc 8) #8;
    %"v365" : P = (Alloc 8) #8;
    %"v392" : P = (Alloc 8) #8;
    %"v410" : P = (Alloc 8) #8;
    %"v421" : P = (Alloc 8) #8;
    %"v439" : P = (Alloc 8) #16;
    %"v442" : P = (Alloc 8) #8;
    %"v444" : P = (Alloc 8) #8;
    %"v471" : P = (Alloc 8) #8;
    %"v474" : P = (Alloc 8) #16;
    %"v477" : P = (Alloc 8) #8;
    %"v478" : P = (Alloc 8) #8;
    %"v479" : P = (Alloc 8) #16;
    %"v482" : P = (Alloc 8) #8;
    %"v483" : P = (Alloc 8) #8;
    %"v484" : P = (Alloc 8) #16;
    %"v487" : P = (Alloc 8) #8;
    %"v488" : P = (Alloc 8) #8;
    %"v489" : P = (Alloc 8) #16;
    %"v492" : P = (Alloc 8) #8;
    %"v494" : P = (Alloc 8) #8;
    %"v496" : P = (Alloc 8) #16;
    %"v499" : P = (Alloc 8) #8;
    %"v501" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Write 1) %"v5";
    store Wl [%"chk0" + 0] <- #18446744073709551615;
    %"chk1" : A = (Check 0 8 Write 1) %"v8";
    store Wl [%"chk1" + 0] <- #18446744073709551615;
    %"chk2" : A = (Check 0 4 Write 1) %"v11";
    store Ww [%"chk2" + 0] <- #0;
    %"chk3" : A = (Check 0 4 Read 1) %"v0";
    %"v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v53" : W = (Cmp Eq W) %"v52", #1
    => br %"v53" ? "L48" : "L49";
  @"L48":
    %"v55" = %"v54" +p #1;
    %"chk4" : A = (Check 0 1 Write 1) %"v55";
    store Wb [%"chk4" + 0] <- #0;
    %"chk5" : A = (HalfCheck Lower 0 1 Write 1) %"chk4", %"v54";
    store Wb [%"chk5" + 0] <- #0;
    call %"v57" : L = $"glibc_libc_start#handle_intel"(W #188, P %"v0", P %"v54");
    call %"v59" : L = $"glibc_libc_start#handle_intel"(W #194, P %"v0", P %"v54");
    %"chk6" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk6" + 0] <- %"v59";
    %"v60" : L = (RawLoad LdL 0) %"chk6";
    %"chk8" : A = (Renew 0 8 Write 1) %"chk1", %"v8";
    store Wl [%"chk8" + 0] <- %"v60";
    call %"v62" : L = $"glibc_libc_start#handle_intel"(W #185, P %"v0", P %"v54");
    call %"v64" : L = $"glibc_libc_start#handle_intel"(W #187, P %"v0", P %"v54");
    call %"v67" : L = $"glibc_libc_start#handle_intel"(W #189, P %"v0", P %"v54");
    call %"v69" : L = $"glibc_libc_start#handle_intel"(W #190, P %"v0", P %"v54");
    call %"v71" : L = $"glibc_libc_start#handle_intel"(W #191, P %"v0", P %"v54");
    call %"v73" : L = $"glibc_libc_start#handle_intel"(W #192, P %"v0", P %"v54");
    call %"v75" : L = $"glibc_libc_start#handle_intel"(W #193, P %"v0", P %"v54");
    %"chk9" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v76" : L = (RawLoad LdL 0) %"chk9";
    call %"v78" : L = $"glibc_libc_start#handle_intel"(W #195, P %"v0", P %"v54");
    call %"v80" : L = $"glibc_libc_start#handle_intel"(W #196, P %"v0", P %"v54");
    call %"v82" : L = $"glibc_libc_start#handle_intel"(W #197, P %"v0", P %"v54");
    call void $"glibc_libc_start#get_common_cache_info"(P %"v5", P %"v8", P %"v11", L %"v71", P %"v54")
    => goto "L50";
  @"L49":
    %"v88" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v89" : W = (Cmp Eq W) %"v88", #3
    => br %"v89" ? "L84" : "L85";
  @"L84":
    call %"v90" : L = $"glibc_libc_start#handle_zhaoxin"(W #188);
    call %"v91" : L = $"glibc_libc_start#handle_zhaoxin"(W #194);
    %"chk11" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk11" + 0] <- %"v91";
    %"v92" : L = (RawLoad LdL 0) %"chk11";
    %"chk13" : A = (Renew 0 8 Write 1) %"chk1", %"v8";
    store Wl [%"chk13" + 0] <- %"v92";
    call %"v93" : L = $"glibc_libc_start#handle_zhaoxin"(W #185);
    call %"v94" : L = $"glibc_libc_start#handle_zhaoxin"(W #187);
    call %"v96" : L = $"glibc_libc_start#handle_zhaoxin"(W #189);
    call %"v97" : L = $"glibc_libc_start#handle_zhaoxin"(W #190);
    call %"v98" : L = $"glibc_libc_start#handle_zhaoxin"(W #191);
    call %"v99" : L = $"glibc_libc_start#handle_zhaoxin"(W #192);
    call %"v100" : L = $"glibc_libc_start#handle_zhaoxin"(W #193);
    %"chk14" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v101" : L = (RawLoad LdL 0) %"chk14";
    call %"v102" : L = $"glibc_libc_start#handle_zhaoxin"(W #195);
    call %"v103" : L = $"glibc_libc_start#handle_zhaoxin"(W #196);
    call void $"glibc_libc_start#get_common_cache_info"(P %"v5", P %"v8", P %"v11", L %"v98", P #0)
    => goto "L50";
  @"L85":
    %"v109" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v110" : W = (Cmp Eq W) %"v109", #2
    => br %"v110" ? "L105" : "L106";
  @"L105":
    call %"v111" : L = $"glibc_libc_start#handle_amd"(W #188);
    call %"v112" : L = $"glibc_libc_start#handle_amd"(W #194);
    %"chk16" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk16" + 0] <- %"v112";
    call %"v113" : L = $"glibc_libc_start#handle_amd"(W #185);
    call %"v114" : L = $"glibc_libc_start#handle_amd"(W #187);
    call %"v116" : L = $"glibc_libc_start#handle_amd"(W #189);
    call %"v117" : L = $"glibc_libc_start#handle_amd"(W #190);
    call %"v118" : L = $"glibc_libc_start#handle_amd"(W #191);
    call %"v119" : L = $"glibc_libc_start#handle_amd"(W #192);
    call %"v120" : L = $"glibc_libc_start#handle_amd"(W #193);
    %"chk17" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v121" : L = (RawLoad LdL 0) %"chk17";
    call %"v122" : L = $"glibc_libc_start#handle_amd"(W #195);
    call %"v123" : L = $"glibc_libc_start#handle_amd"(W #196);
    call %"v124" : L = $"glibc_libc_start#handle_amd"(W #197);
    %"chk18" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v128" : L = (RawLoad LdL 0) %"chk18";
    %"v129" : W = (Cmp Sle L) %"v128", #0
    => br %"v129" ? "L125" : "L126";
  @"L125":
    %"chk19" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk19" + 0] <- %"v118"
    => goto "L127";
  @"L126":
    %"v135" = %"v0" +p #8;
    %"chk20" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v135";
    %"v136" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v137" : W = (Cmp Ult W) %"v136", #23
    => br %"v137" ? "L131" : "L127";
  @"L131":
    %"v138" : L = (RawLoad LdL 0) %"chk18";
    %"v140" : L = Add %"v138", %"v118";
    %"chk22" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk22" + 0] <- %"v140"
    => goto "L127";
  @"L127":
    %"v141" : L = (RawLoad LdL 0) %"chk18";
    %"chk24" : A = (Renew 0 8 Write 1) %"chk1", %"v8";
    store Wl [%"chk24" + 0] <- %"v141"
    => goto "L50";
  @"L106":
    %"v146" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v147" : W = (Cmp Eq W) %"v146", #4
    => br %"v147" ? "L142" : "L50";
  @"L142":
    call %"v148" : L = $"glibc_libc_start#handle_hygon"(W #188);
    call %"v149" : L = $"glibc_libc_start#handle_hygon"(W #194);
    %"chk26" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk26" + 0] <- %"v149";
    %"v150" : L = (RawLoad LdL 0) %"chk26";
    %"chk28" : A = (Renew 0 8 Write 1) %"chk1", %"v8";
    store Wl [%"chk28" + 0] <- %"v150";
    call %"v151" : L = $"glibc_libc_start#handle_hygon"(W #185);
    call %"v152" : L = $"glibc_libc_start#handle_hygon"(W #187);
    call %"v154" : L = $"glibc_libc_start#handle_hygon"(W #189);
    call %"v155" : L = $"glibc_libc_start#handle_hygon"(W #190);
    call %"v156" : L = $"glibc_libc_start#handle_hygon"(W #191);
    call %"v157" : L = $"glibc_libc_start#handle_hygon"(W #192);
    call %"v158" : L = $"glibc_libc_start#handle_hygon"(W #193);
    %"chk29" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v159" : L = (RawLoad LdL 0) %"chk29";
    call %"v160" : L = $"glibc_libc_start#handle_hygon"(W #195);
    call %"v161" : L = $"glibc_libc_start#handle_hygon"(W #196)
    => goto "L50";
  @"L50" [%"pr.51" : L = phi("L48" => %"v82", "L84" => #18446744073709551615, "L127" => %"v124", "L142" => #18446744073709551615, "L106" => #18446744073709551615); %"pr.48" : L = phi("L48" => %"v80", "L84" => %"v103", "L127" => %"v123", "L142" => %"v161", "L106" => #18446744073709551615); %"pr.44" : L = phi("L48" => %"v78", "L84" => %"v102", "L127" => %"v122", "L142" => %"v160", "L106" => #18446744073709551615); %"pr.40" : L = phi("L48" => %"v76", "L84" => %"v101", "L127" => %"v121", "L142" => %"v159", "L106" => #18446744073709551615); %"pr.36" : L = phi("L48" => %"v75", "L84" => %"v100", "L127" => %"v120", "L142" => %"v158", "L106" => #18446744073709551615); %"pr.32" : L = phi("L48" => %"v73", "L84" => %"v99", "L127" => %"v119", "L142" => %"v157", "L106" => #18446744073709551615); %"pr.28" : L = phi("L48" => %"v71", "L84" => %"v98", "L127" => %"v118", "L142" => %"v156", "L106" => #18446744073709551615); %"pr.24" : L = phi("L48" => %"v69", "L84" => %"v97", "L127" => %"v117", "L142" => %"v155", "L106" => #18446744073709551615); %"pr.20" : L = phi("L48" => %"v67", "L84" => %"v96", "L127" => %"v116", "L142" => %"v154", "L106" => #18446744073709551615); %"pr.16" : L = phi("L48" => %"v57", "L84" => %"v90", "L127" => %"v111", "L142" => %"v148", "L106" => #18446744073709551615); %"pr.12" : L = phi("L48" => %"v64", "L84" => %"v94", "L127" => %"v114", "L142" => %"v152", "L106" => #18446744073709551615); %"pr.8" : L = phi("L48" => %"v62", "L84" => %"v93", "L127" => %"v113", "L142" => %"v151", "L106" => #18446744073709551615); %"pr.4" : L = phi("L48" => %"v57", "L84" => %"v90", "L127" => %"v111", "L142" => %"v148", "L106" => #18446744073709551615)]:
    %"v163" = %"v0" +p #424;
    %"chk30" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v163";
    store Wl [%"chk30" + 0] <- %"pr.8";
    %"v166" = %"v0" +p #432;
    %"chk31" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v166";
    store Wl [%"chk31" + 0] <- %"pr.12";
    %"v169" = %"v0" +p #440;
    %"chk32" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v169";
    store Wl [%"chk32" + 0] <- %"pr.16";
    %"v172" = %"v0" +p #448;
    %"chk33" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v172";
    store Wl [%"chk33" + 0] <- %"pr.20";
    %"v175" = %"v0" +p #456;
    %"chk34" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v175";
    store Wl [%"chk34" + 0] <- %"pr.24";
    %"v178" = %"v0" +p #464;
    %"chk35" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v178";
    store Wl [%"chk35" + 0] <- %"pr.28";
    %"v181" = %"v0" +p #472;
    %"chk36" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v181";
    store Wl [%"chk36" + 0] <- %"pr.32";
    %"v184" = %"v0" +p #480;
    %"chk37" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v184";
    store Wl [%"chk37" + 0] <- %"pr.36";
    %"v187" = %"v0" +p #488;
    %"chk38" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v187";
    store Wl [%"chk38" + 0] <- %"pr.40";
    %"v190" = %"v0" +p #496;
    %"chk39" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v190";
    store Wl [%"chk39" + 0] <- %"pr.44";
    %"v193" = %"v0" +p #504;
    %"chk40" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v193";
    store Wl [%"chk40" + 0] <- %"pr.48";
    %"v196" = %"v0" +p #512;
    %"chk41" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v196";
    store Wl [%"chk41" + 0] <- %"pr.51";
    %"v200" = %"v0" +p #520;
    %"chk42" : A = (HalfCheck Upper 0 8 Read 1) %"chk3", %"v200";
    %"v201" : L = (RawLoad LdL 0) %"chk42";
    %"v206" : W = (Cmp Ule L) %"v201", #0
    => br %"v206" ? "L204" : "L203";
  @"L203":
    => goto "L204";
  @"L204" [%"pr.53" : L = phi("L203" => %"v201", "L50" => #4)]:
    %"chk43" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v208" : L = (RawLoad LdL 0) %"chk43";
    %"v210" : L = Udiv %"v208", %"pr.53";
    %"chk44" : A = (Renew 0 8 Read 1) %"chk1", %"v8";
    %"v212" : L = (RawLoad LdL 0) %"chk44";
    %"v213" : L = Mul %"v212", #3;
    %"v214" : L = Div %"v213", #4;
    %"v220" : W = (Cmp Ult L) %"v210", %"v214"
    => br %"v220" ? "L217" : "L216";
  @"L216":
    => goto "L217";
  @"L217" [%"pr.54" : L = phi("L216" => %"v210", "L204" => %"v214")]:
    %"v226" = %"v0" +p #20;
    %"v227" = %"v226" +p #32;
    %"v228" = %"v227" +p #16;
    %"v229" = %"v228" +p #4;
    %"chk45" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v229";
    %"v230" : W = (RawLoad (LdNarrow Uw) 0) %"chk45";
    %"v232" : W = And %"v230", #512;
    %"v234" : W = (Cmp Eq W) %"v232", #0
    => br %"v234" ? "L235" : "L236";
  @"L235":
    %"chk46" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v238" : W = (RawLoad (LdNarrow Uw) 0) %"chk46";
    %"v239" : W = (Cmp Ne W) %"v238", #3
    => goto "L236";
  @"L236" [%"v241" : W = phi("L217" => #0, "L235" => %"v239")]:
    => br %"v241" ? "L224" : "L223";
  @"L223":
    => goto "L224";
  @"L224" [%"pr.55" : L = phi("L223" => %"pr.54", "L236" => %"v214")]:
    %"v251" : W = (Cmp Ult L) %"pr.55", #16448
    => br %"v251" ? "L248" : "L247";
  @"L247":
    %"v260" : W = (Cmp Ugt L) %"pr.55", #1152921504606846975
    => br %"v260" ? "L248" : "L256";
  @"L256":
    => goto "L248";
  @"L248" [%"pr.56" : L = phi("L224" => #67108864, "L256" => %"pr.55", "L247" => #1152921504606846975)]:
    %"v268" = %"v0" +p #20;
    %"v269" = %"v268" +p #32;
    %"v270" = %"v269" +p #16;
    %"v271" = %"v270" +p #4;
    %"v272" : W = (RawLoad (LdNarrow Uw) 0) %"chk45";
    %"v274" : W = And %"v272", #65536;
    %"v275" : W = (Cmp Ne W) %"v274", #0
    => br %"v275" ? "L276" : "L277";
  @"L276":
    %"v279" = %"v0" +p #340;
    %"v281" : W = (RawLoad (LdNarrow Uw) (-84)) %"chk30";
    %"v282" : W = And %"v281", #8192;
    %"v284" : W = (Cmp Eq W) %"v282", #0
    => goto "L277";
  @"L277" [%"v286" : W = phi("L248" => #0, "L276" => %"v284")]:
    => br %"v286" ? "L266" : "L265";
  @"L265":
    %"v296" = %"v0" +p #340;
    %"v298" : W = (RawLoad (LdNarrow Uw) (-84)) %"chk30";
    %"v299" : W = And %"v298", #512;
    %"v300" : W = (Cmp Ne W) %"v299", #0
    => br %"v300" ? "L266" : "L293";
  @"L293":
    => goto "L266";
  @"L266" [%"pr.62" : L = phi("L277" => #16384, "L293" => #2048, "L265" => #8192); %"pr.60" : L = phi("L277" => #512, "L293" => #128, "L265" => #256)]:
    %"v315" = %"v0" +p #20;
    %"v316" = %"v315" +p #32;
    %"v317" = %"v316" +p #16;
    %"v318" = %"v317" +p #12;
    %"v319" : W = (RawLoad (LdNarrow Uw) 8) %"chk45";
    %"v321" : W = And %"v319", #16;
    %"v322" : W = (Cmp Ne W) %"v321", #0
    => br %"v322" ? "L313" : "L312";
  @"L312":
    => goto "L313";
  @"L313" [%"pr.64" : L = phi("L312" => %"pr.62", "L266" => #2112)]:
    %"chk51" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v327" : W = (RawLoad (LdNarrow Uw) 0) %"chk51";
    %"v328" : W = (Cmp Eq W) %"v327", #2
    => br %"v328" ? "L325" : "L324";
  @"L324":
    => goto "L325";
  @"L325" [%"pr.65" : L = phi("L324" => %"pr.64", "L313" => %"pr.56")]:
    call void $"__tunable_get_val"(W #3, P %"v333", P #0);
    %"chk52" : A = (Check 0 8 Read 1) %"v333";
    %"v335" : L = (RawLoad LdL 0) %"chk52";
    %"v340" : W = (Cmp Ne L) %"v335", #0
    => br %"v340" ? "L338" : "L337";
  @"L337":
    => goto "L338";
  @"L338" [%"pr.3" : L = phi("L337" => %"pr.4", "L325" => %"v335")]:
    call void $"__tunable_get_val"(W #9, P %"v343", P #0);
    %"chk53" : A = (Check 0 8 Read 1) %"v343";
    %"v345" : L = (RawLoad LdL 0) %"chk53";
    %"v350" : W = (Cmp Ne L) %"v345", #0
    => br %"v350" ? "L346" : "L348";
  @"L346":
    %"chk54" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk54" + 0] <- %"v345"
    => goto "L348";
  @"L348":
    %"v357" = %"v0" +p #340;
    %"chk55" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v357";
    %"v359" : W = (RawLoad (LdNarrow Uw) 0) %"chk55";
    %"v360" : W = And %"v359", #131072;
    %"v362" : W = (Cmp Eq W) %"v360", #0
    => br %"v362" ? "L355" : "L354";
  @"L354":
    => goto "L355";
  @"L355" [%"pr.69" : L = phi("L354" => #18446744073709551615, "L348" => %"pr.56")]:
    call void $"__tunable_get_val"(W #6, P %"v365", P #0);
    %"chk56" : A = (Check 0 8 Read 1) %"v365";
    %"v367" : L = (RawLoad LdL 0) %"chk56";
    %"v373" : W = (Cmp Ugt L) %"v367", #16448
    => br %"v373" ? "L374" : "L375";
  @"L374":
    %"v378" : W = (Cmp Ule L) %"v367", #1152921504606846975
    => goto "L375";
  @"L375" [%"v380" : W = phi("L355" => #0, "L374" => %"v378")]:
    => br %"v380" ? "L370" : "L369";
  @"L369":
    %"chk57" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v386" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
    %"v387" : W = (Cmp Eq W) %"v386", #4
    => br %"v387" ? "L382" : "L370";
  @"L382":
    %"chk58" : A = (Renew 0 8 Read 1) %"chk1", %"v8";
    %"v388" : L = (RawLoad LdL 0) %"chk58";
    %"v389" : L = Mul %"v388", #3;
    %"v390" : L = Div %"v389", #8
    => goto "L370";
  @"L370" [%"pr.58" : L = phi("L375" => %"v367", "L382" => %"v390", "L369" => %"pr.56")]:
    call void $"__tunable_get_val"(W #5, P %"v392", P #0);
    %"chk59" : A = (Check 0 8 Read 1) %"v392";
    %"v394" : L = (RawLoad LdL 0) %"chk59";
    %"v400" : W = (Cmp Ugt L) %"v394", #16448
    => br %"v400" ? "L401" : "L402";
  @"L401":
    %"v405" : W = (Cmp Ule L) %"v394", #1152921504606846975
    => goto "L402";
  @"L402" [%"v407" : W = phi("L370" => #0, "L401" => %"v405")]:
    => br %"v407" ? "L397" : "L396";
  @"L396":
    => goto "L397";
  @"L397" [%"pr.70" : L = phi("L396" => %"pr.69", "L402" => %"v394")]:
    call void $"__tunable_get_val"(W #7, P %"v410", P #0);
    %"chk60" : A = (Check 0 8 Read 1) %"v410";
    %"v412" : L = (RawLoad LdL 0) %"chk60";
    %"v418" : W = (Cmp Ugt L) %"v412", %"pr.60"
    => br %"v418" ? "L415" : "L414";
  @"L414":
    => goto "L415";
  @"L415" [%"pr.66" : L = phi("L414" => %"pr.65", "L397" => %"v412")]:
    call void $"__tunable_get_val"(W #8, P %"v421", P #0);
    %"chk61" : A = (Check 0 8 Read 1) %"v421";
    %"v423" : L = (RawLoad LdL 0) %"chk61";
    %"chk62" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v428" : W = (RawLoad (LdNarrow Uw) 0) %"chk62";
    %"v429" : W = (Cmp Eq W) %"v428", #2
    => br %"v429" ? "L430" : "L431";
  @"L430":
    call %"v434" : W = $"__tunable_is_initialized"(W #8);
    %"v435" : W = (Ext Ub) %"v434";
    %"v436" : W = (Cmp Eq W) %"v435", #0
    => goto "L431";
  @"L431" [%"v438" : W = phi("L415" => #0, "L430" => %"v436")]:
    => br %"v438" ? "L426" : "L425";
  @"L425":
    => goto "L426";
  @"L426" [%"pr.67" : L = phi("L425" => %"v423", "L431" => #18446744073709551615)]:
    %"chk63" : A = (Check 0 8 Write 1) %"v439";
    store Wl [%"chk63" + 0] <- #0;
    %"v440" = %"v439" +p #8;
    %"chk64" : A = (HalfCheck Upper 0 8 Write 1) %"chk63", %"v440";
    store Wl [%"chk64" + 0] <- #0;
    store Wl [%"chk63" + 0] <- %"pr.70";
    %"chk66" : A = (Check 0 8 Write 1) %"v442";
    store Wl [%"chk66" + 0] <- #0;
    store Wl [%"chk66" + 0] <- #16448;
    %"chk68" : A = (Check 0 8 Write 1) %"v444";
    store Wl [%"chk68" + 0] <- #0;
    store Wl [%"chk68" + 0] <- #(-1);
    call void $"__tunable_set_val"(W #5, P %"v439", P %"v442", P %"v444");
    %"v449" = %"v0" +p #340;
    %"chk70" : A = (Renew 0 4 Read 1) %"chk55", %"v449";
    %"v451" : W = (RawLoad (LdNarrow Uw) 0) %"chk70";
    %"v452" : W = And %"v451", #262144;
    %"v453" : W = (Cmp Ne W) %"v452", #0
    => br %"v453" ? "L455" : "L454";
  @"L454":
    call %"v458" : W = $"__tunable_is_initialized"(W #8);
    %"v459" : W = (Ext Ub) %"v458";
    %"v460" : W = (Cmp Eq W) %"v459", #0
    => br %"v460" ? "L461" : "L455";
  @"L461":
    %"v465" : W = (Cmp Ugt L) %"pr.67", %"pr.70"
    => goto "L455";
  @"L455" [%"v469" : W = phi("L426" => #1, "L454" => #0, "L461" => %"v465")]:
    => br %"v469" ? "L445" : "L447";
  @"L445":
    call void $"__tunable_get_val"(W #5, P %"v471", P #0);
    %"chk71" : A = (Check 0 8 Read 1) %"v471";
    %"v473" : L = (RawLoad LdL 0) %"chk71"
    => goto "L447";
  @"L447" [%"pr.68" : L = phi("L445" => %"v473", "L455" => %"pr.67")]:
    code ((app ir[ %"chk72" : A = (Check 0 8 Write 1) %"v474";
      store Wl [%"chk72" + 0] <- #0;
      %"v475" = %"v474" +p #8;
      %"chk73" : A = (HalfCheck Upper 0 8 Write 1) %"chk72", %"v475";
      store Wl [%"chk73" + 0] <- #0;
      store Wl [%"chk72" + 0] <- %"pr.68";
      %"chk75" : A = (Check 0 8 Write 1) %"v477";
      store Wl [%"chk75" + 0] <- #0;
      store Wl [%"chk75" + 0] <- #1;
      %"chk77" : A = (Check 0 8 Write 1) %"v478";
      store Wl [%"chk77" + 0] <- #0;
      store Wl [%"chk77" + 0] <- #(-1);
      call void $"__tunable_set_val"(W #8, P %"v474", P %"v477", P %"v478");
      %"chk79" : A = (Check 0 8 Write 1) %"v479";
      store Wl [%"chk79" + 0] <- #0;
      %"v480" = %"v479" +p #8;
      %"chk80" : A = (HalfCheck Upper 0 8 Write 1) %"chk79", %"v480";
      store Wl [%"chk80" + 0] <- #0;
      store Wl [%"chk79" + 0] <- %"pr.3";
      %"chk82" : A = (Check 0 8 Write 1) %"v482";
      store Wl [%"chk82" + 0] <- #0;
      store Wl [%"chk82" + 0] <- #0;
      %"chk84" : A = (Check 0 8 Write 1) %"v483";
      store Wl [%"chk84" + 0] <- #0;
      store Wl [%"chk84" + 0] <- #(-1);
      call void $"__tunable_set_val"(W #3, P %"v479", P %"v482", P %"v483");
      %"chk86" : A = (Check 0 8 Write 1) %"v484";
      store Wl [%"chk86" + 0] <- #0;
      %"v485" = %"v484" +p #8;
      %"chk87" : A = (HalfCheck Upper 0 8 Write 1) %"chk86", %"v485";
      store Wl [%"chk87" + 0] <- #0;
      %"chk88" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
      %"v486" : L = (RawLoad LdL 0) %"chk88";
      store Wl [%"chk86" + 0] <- %"v486";
      %"chk90" : A = (Check 0 8 Write 1) %"v487";
      store Wl [%"chk90" + 0] <- #0;
      store Wl [%"chk90" + 0] <- #0;
      %"chk92" : A = (Check 0 8 Write 1) %"v488";
      store Wl [%"chk92" + 0] <- #0;
      store Wl [%"chk92" + 0] <- #(-1);
      call void $"__tunable_set_val"(W #9, P %"v484", P %"v487", P %"v488");
      %"chk94" : A = (Check 0 8 Write 1) %"v489";
      store Wl [%"chk94" + 0] <- #0;
      %"v490" = %"v489" +p #8] ir[ %"chk95" : A = (HalfCheck Upper 0 8 Write 1) %"chk94", %"v490";
      store Wl [%"chk95" + 0] <- #0;
      store Wl [%"chk94" + 0] <- %"pr.58";
      %"chk97" : A = (Check 0 8 Write 1) %"v492";
      store Wl [%"chk97" + 0] <- #0;
      store Wl [%"chk97" + 0] <- #16448;
      %"chk99" : A = (Check 0 8 Write 1) %"v494";
      store Wl [%"chk99" + 0] <- #0;
      store Wl [%"chk99" + 0] <- #1152921504606846975;
      call void $"__tunable_set_val"(W #6, P %"v489", P %"v492", P %"v494");
      %"chk101" : A = (Check 0 8 Write 1) %"v496";
      store Wl [%"chk101" + 0] <- #0;
      %"v497" = %"v496" +p #8;
      %"chk102" : A = (HalfCheck Upper 0 8 Write 1) %"chk101", %"v497";
      store Wl [%"chk102" + 0] <- #0;
      store Wl [%"chk101" + 0] <- %"pr.66";
      %"chk104" : A = (Check 0 8 Write 1) %"v499";
      store Wl [%"chk104" + 0] <- #0;
      store Wl [%"chk104" + 0] <- %"pr.60";
      %"chk106" : A = (Check 0 8 Write 1) %"v501";
      store Wl [%"chk106" + 0] <- #0;
      store Wl [%"chk106" + 0] <- #(-1);
      call void $"__tunable_set_val"(W #7, P %"v496", P %"v499", P %"v501");
      %"v505" = %"v0" +p #368;
      %"chk108" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v505";
      store Wl [%"chk108" + 0] <- %"pr.3";
      %"v508" = %"v0" +p #376;
      %"chk109" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
      %"v509" : L = (RawLoad LdL 0) %"chk109";
      %"chk110" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v508";
      store Wl [%"chk110" + 0] <- %"v509";
      %"v511" = %"v0" +p #384;
      %"chk111" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v511";
      store Wl [%"chk111" + 0] <- %"pr.58";
      %"v514" = %"v0" +p #392;
      %"chk112" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v514";
      store Wl [%"chk112" + 0] <- %"pr.70";
      %"v517" = %"v0" +p #400;
      %"chk113" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v517";
      store Wl [%"chk113" + 0] <- %"pr.66";
      %"v520" = %"v0" +p #416;
      %"chk114" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v520";
      store Wl [%"chk114" + 0] <- %"pr.68";
      %"v523" = %"v0" +p #408;
      store Wl [%"chk114" + (-8)] <- %"pr.58"]))
    => ret void
} }.

Definition hi_fn_glibc_libc_start'23_dl_tunable_set_plt_rewrite : func :=
  ir_fn{ "local" "glibc_libc_start#_dl_tunable_set_plt_rewrite"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v6" : L = (RawLoad LdL 0) %"chk0";
    %"v7" : W = (Cmp Ne L) %"v6", #0
    => br %"v7" ? "iw_1.start" : "L9";
  @"iw_1.start":
    %"iw_1.v30" : P = Copy $"glibc_libc_start#str.319";
    call void $"zsafety_error"(P %"iw_1.v30");
    (Flight (a "iw_1.v32") Copy [(FValue (Const 0))] LowerNone);
    (Flight (a "iw_1.v39") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"iw_1.v40" : L = Ptoi %"iw_1.v32";
    %"iw_1.v41" : L = Ptoi %"iw_1.v39";
    %"iw_1.v42" : W = (Cmp Eq L) %"iw_1.v40", %"iw_1.v41"
    => br %"iw_1.v42" ? "L9" : "iw_1.L35";
  @"iw_1.L35":
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.v32";
    store Ww [%"chk1" + 0] <- #1;
    %"iw_1.v65" : P = Copy $"glibc_libc_start#str.319";
    call void $"zsafety_error"(P %"iw_1.v65");
    %"iw_1.v80" : P = Copy $"glibc_libc_start#str.319";
    call void $"zsafety_error"(P %"iw_1.v80")
    => goto "L9";
  @"L9" [%"v13" : W = phi("start" => #0, "iw_1.L35" => #1, "iw_1.start" => #0)]:
    => br %"v13" ? "L2" : "L4";
  @"L2":
    %"v15" : P = Copy $"_dl_x86_cpu_features";
    %"v16" : P = Copy $"_dl_x86_feature_control";
    %"chk2" : A = (Renew 0 8 Read 1) %"chk0", %"v0";
    %"v21" : L = (RawLoad LdL 0) %"chk2";
    %"v22" : W = (Cmp Sgt L) %"v21", #1
    => br %"v22" ? "L23" : "L24";
  @"L23":
    %"v26" = %"v15" +p #20;
    %"v27" = %"v26" +p #192;
    %"v28" = %"v27" +p #12;
    %"chk3" : A = (Check 0 4 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v31" : W = And %"v29", #2097152;
    %"v32" : W = (Cmp Ne W) %"v31", #0
    => goto "L24";
  @"L24" [%"v34" : W = phi("L2" => #0, "L23" => %"v32")]:
    => br %"v34" ? "L19" : "L18";
  @"L18":
    => goto "L19";
  @"L19" [%"v35" : W = phi("L18" => #1, "L24" => #2)]:
    %"chk4" : A = (Check 0 4 Read 1) %"v16";
    %"v36" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v37" : W = And %"v36", #4294967247;
    %"v38" : W = Shl %"v35", #4;
    %"v39" : W = And %"v38", #48;
    %"v40" : W = Or %"v37", %"v39";
    %"chk5" : A = (Renew 0 4 Write 1) %"chk4", %"v16";
    store Ww [%"chk5" + 0] <- %"v40"
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition hi_fn_glibc_libc_start'23_dl_tunable_set_prefer_map_32bit_exec : func :=
  ir_fn{ "local" "glibc_libc_start#_dl_tunable_set_prefer_map_32bit_exec"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v6" : L = (RawLoad LdL 0) %"chk0";
    %"v7" : W = (Cmp Ne L) %"v6", #0
    => br %"v7" ? "L2" : "L4";
  @"L2":
    %"v8" : P = Copy $"_dl_x86_cpu_features";
    %"v9" = %"v8" +p #340;
    %"chk1" : A = (Check 0 4 Read 1) %"v9";
    %"v11" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v12" : W = Or %"v11", #1024;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk1", %"v9";
    store Ww [%"chk2" + 0] <- %"v12"
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition hi_fn_glibc_libc_start'23dlerror_handler : func :=
  ir_fn{ "local" "glibc_libc_start#dlerror_handler"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"__libc_dlerror_result_string";
    %"chk0" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk0" + 0] <- %"v0"
    => ret void
} }.

Definition hi_fn_glibc_pthread_mutex_conf'23_dl_tunable_set_mutex_spin_count : func :=
  ir_fn{ "local" "glibc_pthread_mutex_conf#_dl_tunable_set_mutex_spin_count"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"__GI___mutex_aconf";
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"chk1" : A = (Check 0 4 Write 1) %"v2";
    store Ww [%"chk1" + 0] <- %"v4"
    => ret void
} }.
