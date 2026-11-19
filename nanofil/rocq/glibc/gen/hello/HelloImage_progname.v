(** This file defines checked IR from the `progname` object of HelloImage.
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

Definition item_progname'23str'2e3 : item :=
  (IData (a "progname#str.3") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 46); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 115); (Item Wb 47); (Item Wb 0)]).

Definition item_progname'23str'2e4 : item :=
  (IData (a "progname#str.4") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 116); (Item Wb 45); (Item Wb 0)]).

Definition item_program_name : item :=
  (IData (a "program_name") LExport 8 [(Item Wl 0)]).

Definition fn_set_program_name : func :=
  ir_fn{ "export" "set_program_name"(P %"v0") -> RVoid {
  @"start":
    call %"v4" : P = $"strrchr"(P %"v0", W #47);
    %"v10" : L = Ptoi %"v4";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L6" : "L8";
  @"L6":
    %"v13" = %"v4" +p #1
    => goto "L8";
  @"L8" [%"v15" : P = phi("L6" => %"v13", "start" => %"v0")]:
    %"v21" : L = Ptoi %"v15";
    %"v22" : L = Ptoi %"v0";
    %"v23" : L = Sub %"v21", %"v22";
    %"v24" : W = (Cmp Sge L) %"v23", #7
    => br %"v24" ? "L25" : "L26";
  @"L25":
    (Flight (a "v28") Sub [(FAddress (t "v15")); (FValue (Const 7))] (LowerOf (t "v15")));
    %"v29" : P = Copy $"progname#str.3";
    call %"v30" : W = $"memeq"(P %"v28", P %"v29", L #7);
    %"v31" : W = (Ext Ub) %"v30";
    %"v32" : W = (Cmp Ne W) %"v31", #0
    => goto "L26";
  @"L26" [%"v33" : W = phi("L8" => #0, "L25" => %"v32")]:
    => br %"v33" ? "L16" : "L18";
  @"L16":
    %"v39" : P = Copy $"progname#str.4";
    call %"v40" : W = $"strncmp"(P %"v15", P %"v39", L #3);
    %"v41" : W = (Cmp Eq W) %"v40", #0
    => br %"v41" ? "L35" : "L18";
  @"L35":
    %"v43" = %"v15" +p #3
    => goto "L18";
  @"L18" [%"pr.3" : P = phi("L35" => %"v43", "L16" => %"v15", "L26" => %"v15"); %"pr.1" : P = phi("L35" => %"v43", "L16" => %"v15", "L26" => %"v0")]:
    %"v45" : P = Copy $"program_name";
    %"chk0" : A = (Check 0 8 Write 8) %"v45";
    store.ptr [%"chk0" + 0] <- %"pr.1";
    %"v47" : P = Copy $"program_invocation_name";
    %"chk1" : A = (Check 0 8 Write 8) %"v47";
    store.ptr [%"chk1" + 0] <- %"pr.1";
    %"v49" : P = Copy $"program_invocation_short_name";
    %"chk2" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk2" + 0] <- %"pr.3"
    => ret void
} }.
