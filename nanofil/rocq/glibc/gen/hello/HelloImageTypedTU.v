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

Definition hello_image_fn___tunable_is_initialized : func :=
  ir_fn{ "export" "__tunable_is_initialized"(W %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = Copy $"glibc_dl_tunables#tunable_list";
    %"v4" : L = (Ext Uw) %"v0";
    %"v5" : L = Mul %"v4", #136;
    %"v6" = %"v2" +p %"v5";
    %"v7" = %"v6" +p #104;
    %"chk0" : A = (Check 0 1 Read 1) %"v7";
    %"v8" : W = (RawLoad (LdNarrow Ub) 0) %"chk0"
    => ret %"v8"
} }.

Definition hello_image_fn___tunable_set_val : func :=
  ir_fn{ "export" "__tunable_set_val"(W %"v0", P %"v2", P %"v4", P %"v6") -> RVoid {
  @"start":
    %"v9" : P = Copy $"glibc_dl_tunables#tunable_list";
    %"v11" : L = (Ext Uw) %"v0";
    %"v12" : L = Mul %"v11", #136;
    %"v13" = %"v9" +p %"v12";
    call void $"glibc_dl_tunables#do_tunable_update_val"(P %"v13", P %"v2", P %"v4", P %"v6")
    => ret void
} }.

Definition hello_image_fn___tunable_get_val : func :=
  ir_fn{ "export" "__tunable_get_val"(W %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v7" : P = Copy $"glibc_dl_tunables#tunable_list";
    %"v9" : L = (Ext Uw) %"v0";
    %"v10" : L = Mul %"v9", #136;
    %"v11" = %"v7" +p %"v10";
    %"v13" = %"v11" +p #48;
    %"chk0" : A = (Check 0 4 Read 1) %"v13";
    %"v14" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v38" : W = (Cmp Eq W) %"v14", #1
    => br %"v38" ? "L17" : "L39";
  @"L17":
    %"v20" = %"v11" +p #88;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v20";
    %"v21" : L = (RawLoad LdL 0) %"chk1";
    %"chk2" : A = (Check 0 8 Write 1) %"v2";
    store Wl [%"chk2" + 0] <- %"v21"
    => goto "L16";
  @"L22":
    %"v25" = %"v11" +p #88;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v25";
    %"v26" : L = (RawLoad LdL 0) %"chk3";
    %"chk4" : A = (Check 0 4 Write 1) %"v2";
    store Ww [%"chk4" + 0] <- %"v26"
    => goto "L16";
  @"L27":
    %"v30" = %"v11" +p #88;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v30";
    %"v31" : L = (RawLoad LdL 0) %"chk5";
    %"chk6" : A = (Check 0 8 Write 1) %"v2";
    store Wl [%"chk6" + 0] <- %"v31"
    => goto "L16";
  @"L32":
    %"v35" = %"v11" +p #88;
    %"chk7" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk7" + 0] <- %"v35"
    => goto "L16";
  @"L36":
    => unreachable;
  @"L39":
    %"v40" : W = (Cmp Eq W) %"v14", #0
    => br %"v40" ? poll "L22" : "L41";
  @"L41":
    %"v42" : W = (Cmp Eq W) %"v14", #2
    => br %"v42" ? poll "L27" : "L43";
  @"L43":
    %"v44" : W = (Cmp Eq W) %"v14", #3
    => br %"v44" ? poll "L32" : poll "L36";
  @"L16":
    %"v50" = %"v11" +p #104;
    %"chk8" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v50";
    %"v51" : W = (RawLoad (LdNarrow Ub) 0) %"chk8"
    => br %"v51" ? "L52" : "L53";
  @"L52":
    %"v55" : L = Ptoi %"v4";
    %"v56" : L = Ptoi #0;
    %"v57" : W = (Cmp Ne L) %"v55", %"v56"
    => goto "L53";
  @"L53" [%"v59" : W = phi("L16" => #0, "L52" => %"v57")]:
    => br %"v59" ? "L46" : "L48";
  @"L46":
    %"v62" = %"v11" +p #88;
    %"chk9" : F = CheckFunction %"v4";
    rawcall void %"chk9"(P %"v62")
    => goto "L48";
  @"L48":
    => ret void
} }.
