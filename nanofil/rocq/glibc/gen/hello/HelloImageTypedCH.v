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

Definition hello_image_fn___GI___chk_fail : func :=
  ir_fn{ "export" "__GI___chk_fail"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_chk_fail#str.134";
    call void $"__GI___fortify_fail"(P %"v0")
    => ret void
} }.

Definition hello_image_fn_glibc_vtables'23check_stdfiles_vtables : func :=
  ir_fn{ "local" "glibc_vtables#check_stdfiles_vtables"() -> RVoid {
  @"start":
    %"v3" : P = Copy $"_IO_2_1_stdin_";
    %"v4" = %"v3" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v6" : P = Copy $"__io_vtables";
    %"v7" = %"v6" +p #336;
    %"v8" : L = Ptoi %"v5";
    %"v9" : L = Ptoi %"v7";
    %"v10" : W = (Cmp Ne L) %"v8", %"v9"
    => br %"v10" ? "L12" : "L11";
  @"L11":
    %"v13" : P = Copy $"_IO_2_1_stdout_";
    %"v14" = %"v13" +p #216;
    %"chk1" : A = (Check 0 8 Read 8) %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v16" : P = Copy $"__io_vtables";
    %"v17" = %"v16" +p #336;
    %"v18" : L = Ptoi %"v15";
    %"v19" : L = Ptoi %"v17";
    %"v20" : W = (Cmp Ne L) %"v18", %"v19"
    => goto "L12";
  @"L12" [%"v22" : W = phi("start" => #1, "L11" => %"v20")]:
    => br %"v22" ? "L24" : "L23";
  @"L23":
    %"v25" : P = Copy $"_IO_2_1_stderr_";
    %"v26" = %"v25" +p #216;
    %"chk2" : A = (Check 0 8 Read 8) %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v28" : P = Copy $"__io_vtables";
    %"v29" = %"v28" +p #336;
    %"v30" : L = Ptoi %"v27";
    %"v31" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ne L) %"v30", %"v31"
    => goto "L24";
  @"L24" [%"v34" : W = phi("L12" => #1, "L23" => %"v32")]:
    => br %"v34" ? "L0" : "L2";
  @"L0":
    %"v35" : P = Copy $"_IO_vtable_check";
    %"iw_1.v6" : P = Copy $"IO_accept_foreign_vtables";
    %"chk3" : A = (Check 0 8 Write 8) %"iw_1.v6";
    (RawStorePointer 0 (t "v35") (t "chk3") [AtomicWrite])
    => goto "L2";
  @"L2":
    => ret void
} }.
