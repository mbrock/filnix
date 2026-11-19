(** This file defines checked IR from the `hi_atexit` object of HiAtexit.
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

Definition fn_hi_atexit'23close_stdout_hi : func :=
  ir_fn{ "local" "hi_atexit#close_stdout_hi"() -> RVoid {
  @"start":
    %"v1" : P = Copy $"stdout";
    %"chk0" : A = (Check 0 8 Read 8) %"v1";
    %"v2" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v3" : W = $"__fpending"(P %"v2");
    %"v4" : W = (Cmp Ne W) %"v3", #0;
    %"v6" : P = Copy $"stdout";
    %"chk1" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v8" : W = $"ferror"(P %"v7");
    %"v9" : W = (Cmp Ne W) %"v8", #0;
    %"v11" : P = Copy $"stdout";
    %"chk2" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call %"v13" : W = $"fclose"(P %"v12");
    %"v14" : W = (Cmp Ne W) %"v13", #0
    => br %"v9" ? "L20" : "L19";
  @"L19":
    => goto "L20";
  @"L20" [%"v23" : W = phi("start" => #1, "L19" => %"v14")]:
    => br %"v23" ? "L15" : "L17";
  @"L15":
    => br %"v4" ? "L29" : "L28";
  @"L28":
    => goto "L29";
  @"L29" [%"v32" : W = phi("L15" => #1, "L28" => %"v14")]:
    => br %"v32" ? "L24" : "L17";
  @"L24":
    call void $"_exit"(W #1)
    => goto "L17";
  @"L17":
    => ret void
} }.

Definition item_hi_atexit'23str'2e0 : item :=
  (IData (a "hi_atexit#str.0") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 0)]).

Definition fn_main : func :=
  ir_fn{ "export" "main"() -> (RClass W) {
  @"start":
    %"v0" : P = Copy $"hi_atexit#close_stdout_hi";
    call %"v1" : W = $"atexit"(P %"v0");
    %"v2" : P = Copy $"hi_atexit#str.0";
    call %"v3" : W = $"puts"(P %"v2");
    call void $"exit"(W #0)
    => ret #0
} }.
