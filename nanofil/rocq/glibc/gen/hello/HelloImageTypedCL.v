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

Definition hello_image_fn_close_stream : func :=
  ir_fn{ "export" "close_stream"(P %"v0") -> (RClass W) {
  @"start":
    call %"v4" : L = $"__fpending"(P %"v0");
    %"v5" : W = (Cmp Ne L) %"v4", #0;
    call %"v9" : W = $"ferror"(P %"v0");
    %"v10" : W = (Cmp Ne W) %"v9", #0;
    call %"v14" : W = $"fclose"(P %"v0");
    %"v15" : W = (Cmp Ne W) %"v14", #0
    => br %"v10" ? "L22" : "L21";
  @"L21":
    => br %"v15" ? "L24" : "L22";
  @"L24":
    => br %"v5" ? "L22" : "L27";
  @"L27":
    call %"v29" : P = $"__errno_location"();
    %"chk0" : A = (Check 0 4 Read 1) %"v29";
    %"v30" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v31" : W = (Cmp Ne W) %"v30", #9
    => goto "L22";
  @"L22" [%"v37" : W = phi("start" => #1, "L21" => #0, "L24" => #1, "L27" => %"v31")]:
    => br %"v37" ? "L17" : "L19";
  @"L17":
    %"v42" : W = (Cmp Eq W) %"v14", #0
    => br %"v42" ? "L38" : "L40";
  @"L38":
    call %"v43" : P = $"__errno_location"();
    %"chk1" : A = (Check 0 4 Write 1) %"v43";
    store Ww [%"chk1" + 0] <- #0
    => goto "L40";
  @"L40":
    => ret #4294967295;
  @"L19":
    => ret #0
} }.

Definition hello_image_fn_close_stdout : func :=
  ir_fn{ "export" "close_stdout"() -> RVoid {
  @"start":
    %"v3" : P = Copy $"stdout";
    %"chk0" : A = (Check 0 8 Read 8) %"v3";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v5" : W = $"close_stream"(P %"v4");
    %"v6" : W = (Cmp Ne W) %"v5", #0
    => br %"v6" ? "L7" : "L8";
  @"L7":
    %"v9" : P = Copy $"closeout#ignore_EPIPE";
    %"chk1" : A = (Check 0 1 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Ub) 0) %"chk1"
    => br %"v10" ? "L11" : "L12";
  @"L11":
    call %"v13" : P = $"__errno_location"();
    %"chk2" : A = (Check 0 4 Read 1) %"v13";
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v15" : W = (Cmp Eq W) %"v14", #32
    => goto "L12";
  @"L12" [%"v17" : W = phi("L7" => #0, "L11" => %"v15")]:
    %"v18" : W = (Cmp Eq W) %"v17", #0
    => goto "L8";
  @"L8" [%"v20" : W = phi("start" => #0, "L12" => %"v18")]:
    => br %"v20" ? "L0" : "L91";
  @"L0":
    %"v22" : P = Copy $"closeout#str.52";
    %"v23" : P = Copy $"closeout#str.53";
    %"v27" : P = Copy $"closeout#file_name";
    %"chk3" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v29" : L = Ptoi %"v28";
    %"v30" : W = (Cmp Ne L) %"v29", #0
    => br %"v30" ? "L31" : "L61";
  @"L31":
    call %"v34" : P = $"__errno_location"();
    %"chk4" : A = (Check 0 4 Read 1) %"v34";
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v36" : P = Copy $"closeout#str.54";
    %"v37" : P = Copy $"closeout#file_name";
    %"chk5" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v39" : P = $"quotearg_colon"(P %"v38");
    call void $"error"(W #0, W %"v35", P %"v36", P %"v39", P %"v23")
    => goto "L26";
  @"L61":
    call %"v64" : P = $"__errno_location"();
    %"chk6" : A = (Check 0 4 Read 1) %"v64";
    %"v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v66" : P = Copy $"closeout#str.55";
    call void $"error"(W #0, W %"v65", P %"v66", P %"v23")
    => goto "L26";
  @"L26":
    %"v85" : P = Copy $"exit_failure";
    %"chk7" : A = (Check 0 4 Read 1) %"v85";
    %"v86" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    call void $"_exit"(W %"v86")
    => goto "L91";
  @"L91":
    %"v93" : P = Copy $"stderr";
    %"chk8" : A = (Check 0 8 Read 8) %"v93";
    %"v94" : P = (RawLoadPointer 0 load_effects) %"chk8";
    call %"v95" : W = $"close_stream"(P %"v94");
    %"v96" : W = (Cmp Ne W) %"v95", #0
    => br %"v96" ? "L87" : "L89";
  @"L87":
    %"v99" : P = Copy $"exit_failure";
    %"chk9" : A = (Check 0 4 Read 1) %"v99";
    %"v100" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    call void $"_exit"(W %"v100")
    => goto "L89";
  @"L89":
    => ret void
} }.

Definition hello_image_fn___closedir : func :=
  ir_fn{ "export" "__closedir"(P %"v0") -> (RClass W) {
  @"start":
    %"v7" : L = Ptoi %"v0";
    %"v8" : L = Ptoi #0;
    %"v9" : W = (Cmp Eq L) %"v7", %"v8"
    => br %"v9" ? "L3" : "L5";
  @"L3":
    %"v10" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk0" + 0] <- #22
    => ret #4294967295;
  @"L5":
    %"chk1" : A = (Check 0 4 Read 1) %"v0";
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call void $"free"(P %"v0");
    call %"v17" : W = $"__GI___close_nocancel"(W %"v14")
    => ret %"v17"
} }.

Definition hello_image_fn___GI___close_nocancel : func :=
  ir_fn{ "export" "__GI___close_nocancel"(W %"v0") -> (RClass W) {
  @"start":
    call %"v3" : W = $"zsys_close"(W %"v0")
    => ret %"v3"
} }.

Definition hello_image_fn___GI___close_nocancel_nostatus : func :=
  ir_fn{ "export" "__GI___close_nocancel_nostatus"(W %"v0") -> RVoid {
  @"start":
    call %"v3" : W = $"zsys_close"(W %"v0")
    => ret void
} }.

Definition hello_image_fn_glibc_pthread_once'23clear_once_control : func :=
  ir_fn{ "local" "glibc_pthread_once#clear_once_control"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Write 1) %"v0";
    store Ww [%"chk0" + 0] <- #0;
    call void $"zsys_futex_wake"(P %"v0", W #2147483647, W #1)
    => ret void
} }.

Definition hello_image_fn___GI___clock_gettime : func :=
  ir_fn{ "export" "__GI___clock_gettime"(W %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v6" : W = $"zsys_clock_gettime"(W %"v0", P %"v2")
    => ret %"v6"
} }.
