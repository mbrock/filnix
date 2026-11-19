(** This file defines checked IR from glibc’s `libio/filedoalloc.os` object.
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

Definition fn___GI__IO_file_doallocate : func :=
  ir_fn{ "export" "__GI__IO_file_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 8) #144;
    %"v9" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = (Cmp Sge W) %"v10", #0
    => br %"v11" ? "L12" : "L13";
  @"L12":
    %"v15" = %"v0" +p #216;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v4" : L = Ptoi %"v16";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v18" = %"v16" +p #144;
    %"chk2" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : F = CheckFunction %"v19";
    rawcall %"v21" : W = %"chk3"(P %"v0", P %"v4");
    %"v22" : L = (Ext Sw) %"v21";
    %"v23" : W = (Cmp Sge L) %"v22", #0
    => goto "L13";
  @"L13" [%"v25" : W = phi("start" => #0, "iw_1.join" => %"v23")]:
    => br %"v25" ? "L5" : "L7";
  @"L5":
    %"v29" = %"v4" +p #24;
    %"chk4" : A = (Check 0 4 Read 1) %"v29";
    %"v30" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v31" : W = And %"v30", #61440;
    %"v32" : W = (Cmp Eq W) %"v31", #8192
    => br %"v32" ? "L26" : "L28";
  @"L26":
    %"v37" = %"v4" +p #40;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 1) %"chk4", %"v37";
    %"v38" : L = (RawLoad LdL 0) %"chk5";
    call %"v39" : W = $"__gnu_dev_major"(L %"v38");
    %"v41" : W = (Cmp Sge W) %"v39", #136
    => br %"v41" ? "L42" : "L43";
  @"L42":
    %"v45" : W = (Cmp Sle W) %"v39", #143
    => goto "L43";
  @"L43" [%"v47" : W = phi("L26" => #0, "L42" => %"v45")]:
    => br %"v47" ? "L49" : "L48";
  @"L48":
    %"v51" = %"v0" +p #112;
    %"chk6" : A = (Renew 0 4 Read 1) %"chk0", %"v51";
    %"v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    call %"v53" : W = $"__isatty_nostatus"(W %"v52");
    %"v54" : W = (Cmp Ne W) %"v53", #0
    => goto "L49";
  @"L49" [%"v55" : W = phi("L43" => #1, "L48" => %"v54")]:
    => br %"v55" ? "L33" : "L28";
  @"L33":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v57" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v58" : W = Or %"v57", #512;
    %"chk8" : A = (Renew 0 4 Write 1) %"chk7", %"v0";
    store Ww [%"chk8" + 0] <- %"v58"
    => goto "L28";
  @"L28":
    %"v62" = %"v4" +p #56;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 1) %"chk4", %"v62";
    %"v63" : L = (RawLoad LdL 0) %"chk9";
    %"v64" : W = (Cmp Sgt L) %"v63", #0
    => br %"v64" ? "L65" : "L66";
  @"L65":
    %"v67" = %"v4" +p #56;
    %"v68" : L = (RawLoad LdL 0) %"chk9";
    %"v69" : W = (Cmp Slt L) %"v68", #8192
    => goto "L66";
  @"L66" [%"v71" : W = phi("L28" => #0, "L65" => %"v69")]:
    => br %"v71" ? "L59" : "L7";
  @"L59":
    %"v72" = %"v4" +p #56;
    %"v73" : L = (RawLoad LdL 0) %"chk9"
    => goto "L7";
  @"L7" [%"pr.2" : L = phi("L59" => %"v73", "L66" => #8192, "L13" => #8192)]:
    call %"v75" : P = $"malloc"(L %"pr.2");
    %"v80" : L = Ptoi %"v75";
    %"v81" : L = Ptoi #0;
    %"v82" : W = (Cmp Eq L) %"v80", %"v81"
    => br %"v82" ? "L76" : "L78";
  @"L76":
    => ret #4294967295;
  @"L78":
    %"v91" = %"v75" +p %"pr.2";
    call void $"__GI__IO_setb"(P %"v0", P %"v75", P %"v91", W #1)
    => ret #1
} }.
