(** This file defines checked IR from glibc’s `malloc/scratch_buffer_grow_preserve.os` object.
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

Definition fn___GI___libc_scratch_buffer_grow_preserve : func :=
  ir_fn{ "export" "__GI___libc_scratch_buffer_grow_preserve"(P %"v0") -> (RClass W) {
  @"start":
    %"v4" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 1) %"v4";
    %"v5" : L = (RawLoad LdL 0) %"chk0";
    %"v6" : L = Shl %"v5", #1;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v14" = %"v0" +p #16;
    %"v15" : L = Ptoi %"v12";
    %"v16" : L = Ptoi %"v14";
    %"v17" : W = (Cmp Eq L) %"v15", %"v16"
    => br %"v17" ? "L8" : "L9";
  @"L8":
    call %"v19" : P = $"malloc"(L %"v6");
    %"v24" : L = Ptoi %"v19";
    %"v25" : L = Ptoi #0;
    %"v26" : W = (Cmp Eq L) %"v24", %"v25"
    => br %"v26" ? "L20" : "L22";
  @"L20":
    => ret #0;
  @"L22":
    %"v31" = %"v0" +p #16;
    %"v33" = %"v0" +p #8;
    %"chk2" : A = (Renew 0 8 Read 1) %"chk0", %"v33";
    %"v34" : L = (RawLoad LdL 0) %"chk2";
    call %"v35" : P = $"__GI_memcpy"(P %"v19", P %"v31", L %"v34")
    => goto "L10";
  @"L9":
    %"v41" = %"v0" +p #8;
    %"v42" : L = (RawLoad LdL 0) %"chk0";
    %"v43" : W = (Cmp Uge L) %"v6", %"v42"
    => br %"v43" ? "L36" : "L37";
  @"L36":
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v49" : P = $"realloc"(P %"v47", L %"v6")
    => goto "L38";
  @"L37":
    %"v50" : P = Copy $"__libc_errno";
    %"chk5" : A = (Check 0 4 Write 1) %"v50";
    store Ww [%"chk5" + 0] <- #12
    => goto "L38";
  @"L38" [%"pr.2" : P = phi("L36" => %"v49", "L37" => #0)]:
    %"v55" : L = Ptoi %"pr.2";
    %"v56" : L = Ptoi #0;
    %"v57" : W = (Cmp Eq L) %"v55", %"v56"
    => br %"v57" ? "L51" : "L10";
  @"L51":
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call void $"free"(P %"v61");
    %"iw_1.v4" = %"v0" +p #16;
    %"chk7" : A = (Renew 0 8 Write 8) %"chk1", %"v0";
    store.ptr [%"chk7" + 0] <- %"iw_1.v4";
    %"iw_1.v6" = %"v0" +p #8;
    %"chk8" : A = (Renew 0 8 Write 1) %"chk0", %"iw_1.v6";
    store Wl [%"chk8" + 0] <- #1024
    => ret #0;
  @"L10" [%"pr.1" : P = phi("L22" => %"v19", "L38" => %"pr.2")]:
    %"chk9" : A = (Renew 0 8 Write 8) %"chk1", %"v0";
    store.ptr [%"chk9" + 0] <- %"pr.1";
    %"v68" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Write 1) %"chk0", %"v68";
    store Wl [%"chk10" + 0] <- %"v6"
    => ret #1
} }.
