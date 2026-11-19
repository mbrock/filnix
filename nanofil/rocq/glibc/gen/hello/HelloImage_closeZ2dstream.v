(** This file defines checked IR from the `close-stream` object of HelloImage.
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

Definition fn_close_stream : func :=
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
