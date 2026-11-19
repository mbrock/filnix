(** This file defines checked IR from the `closeout` object of HelloImage.
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

Definition fn_close_stdout : func :=
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

Definition item_closeout'23file_name : item :=
  (IData (a "closeout#file_name") LLocal 8 [(Zero 8)]).

Definition item_closeout'23ignore_EPIPE : item :=
  (IData (a "closeout#ignore_EPIPE") LLocal 1 [(Zero 1)]).

Definition item_closeout'23str'2e52 : item :=
  (IData (a "closeout#str.52") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).

Definition item_closeout'23str'2e53 : item :=
  (IData (a "closeout#str.53") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition item_closeout'23str'2e54 : item :=
  (IData (a "closeout#str.54") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition item_closeout'23str'2e55 : item :=
  (IData (a "closeout#str.55") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 0)]).
