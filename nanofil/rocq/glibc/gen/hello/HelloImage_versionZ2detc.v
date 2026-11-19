(** This file defines checked IR from the `version-etc` object of HelloImage.
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

Definition fn_emit_bug_reporting_address : func :=
  ir_fn{ "export" "emit_bug_reporting_address"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"version-etc#str.45";
    %"v1" : P = Copy $"stdout";
    %"chk0" : A = (Check 0 8 Read 8) %"v1";
    %"v2" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v3" : W = $"fputs"(P %"v0", P %"v2");
    %"v4" : P = Copy $"version-etc#str.43";
    %"v5" : P = Copy $"version-etc#str.58";
    %"v6" : P = Copy $"version-etc#str.59";
    call %"v7" : W = $"printf"(P %"v5", P %"v6");
    %"v8" : P = Copy $"version-etc#str.43";
    %"v9" : P = Copy $"version-etc#str.60";
    %"v10" : P = Copy $"version-etc#str.61";
    %"v11" : P = Copy $"version-etc#str.62";
    call %"v12" : W = $"printf"(P %"v9", P %"v10", P %"v11");
    %"v13" : P = Copy $"version-etc#str.43";
    %"v14" : P = Copy $"version-etc#str.63";
    %"v15" : P = Copy $"version-etc#str.64";
    call %"v16" : W = $"printf"(P %"v14", P %"v15")
    => ret void
} }.

Definition item_version'2detc'23str'2e41 : item :=
  (IData (a "version-etc#str.41") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 40); (Item Wb 37); (Item Wb 115); (Item Wb 41); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e42 : item :=
  (IData (a "version-etc#str.42") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e43 : item :=
  (IData (a "version-etc#str.43") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).

Definition item_version'2detc'23str'2e44 : item :=
  (IData (a "version-etc#str.44") (LRo (a "local")) 1 [(Item Wb 40); (Item Wb 67); (Item Wb 41); (Item Wb 0)]).

Definition item_version'2detc'23str'2e45 : item :=
  (IData (a "version-etc#str.45") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e46 : item :=
  (IData (a "version-etc#str.46") (LRo (a "local")) 1 (app (app [(Item Wb 76); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 110); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 71); (Item Wb 80); (Item Wb 76); (Item Wb 118); (Item Wb 51); (Item Wb 43); (Item Wb 58); (Item Wb 32); (Item Wb 71); (Item Wb 78); (Item Wb 85); (Item Wb 32); (Item Wb 71); (Item Wb 80); (Item Wb 76); (Item Wb 32); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 51); (Item Wb 32); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 114)] [(Item Wb 32); (Item Wb 60); (Item Wb 37); (Item Wb 115); (Item Wb 62); (Item Wb 46); (Item Wb 10); (Item Wb 84); (Item Wb 104); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 32); (Item Wb 115); (Item Wb 111); (Item Wb 102); (Item Wb 116); (Item Wb 119); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 58); (Item Wb 32); (Item Wb 121); (Item Wb 111); (Item Wb 117); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 32)]) (app [(Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 105); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 105); (Item Wb 98); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 116); (Item Wb 46); (Item Wb 10); (Item Wb 84); (Item Wb 104); (Item Wb 101); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 78); (Item Wb 79); (Item Wb 32)] [(Item Wb 87); (Item Wb 65); (Item Wb 82); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 84); (Item Wb 89); (Item Wb 44); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 109); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 108); (Item Wb 97); (Item Wb 119); (Item Wb 46); (Item Wb 10); (Item Wb 0)]))).

Definition item_version'2detc'23str'2e47 : item :=
  (IData (a "version-etc#str.47") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 116); (Item Wb 116); (Item Wb 112); (Item Wb 115); (Item Wb 58); (Item Wb 47); (Item Wb 47); (Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 110); (Item Wb 115); (Item Wb 101); (Item Wb 115); (Item Wb 47); (Item Wb 103); (Item Wb 112); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 116); (Item Wb 109); (Item Wb 108); (Item Wb 0)]).

Definition item_version'2detc'23str'2e48 : item :=
  (IData (a "version-etc#str.48") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e49 : item :=
  (IData (a "version-etc#str.49") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e50 : item :=
  (IData (a "version-etc#str.50") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e51 : item :=
  (IData (a "version-etc#str.51") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e52 : item :=
  (IData (a "version-etc#str.52") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e53 : item :=
  (IData (a "version-etc#str.53") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e54 : item :=
  (IData (a "version-etc#str.54") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e55 : item :=
  (IData (a "version-etc#str.55") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e56 : item :=
  (IData (a "version-etc#str.56") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e57 : item :=
  (IData (a "version-etc#str.57") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 111); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e58 : item :=
  (IData (a "version-etc#str.58") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 103); (Item Wb 115); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e59 : item :=
  (IData (a "version-etc#str.59") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 103); (Item Wb 45); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 64); (Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 0)]).

Definition item_version'2detc'23str'2e60 : item :=
  (IData (a "version-etc#str.60") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 104); (Item Wb 111); (Item Wb 109); (Item Wb 101); (Item Wb 32); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 58); (Item Wb 32); (Item Wb 60); (Item Wb 37); (Item Wb 115); (Item Wb 62); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e61 : item :=
  (IData (a "version-etc#str.61") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 78); (Item Wb 85); (Item Wb 32); (Item Wb 72); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 0)]).

Definition item_version'2detc'23str'2e62 : item :=
  (IData (a "version-etc#str.62") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 116); (Item Wb 116); (Item Wb 112); (Item Wb 115); (Item Wb 58); (Item Wb 47); (Item Wb 47); (Item Wb 119); (Item Wb 119); (Item Wb 119); (Item Wb 46); (Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 47); (Item Wb 115); (Item Wb 111); (Item Wb 102); (Item Wb 116); (Item Wb 119); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 47); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 47); (Item Wb 0)]).

Definition item_version'2detc'23str'2e63 : item :=
  (IData (a "version-etc#str.63") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 101); (Item Wb 110); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 71); (Item Wb 78); (Item Wb 85); (Item Wb 32); (Item Wb 115); (Item Wb 111); (Item Wb 102); (Item Wb 116); (Item Wb 119); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 58); (Item Wb 32); (Item Wb 60); (Item Wb 37); (Item Wb 115); (Item Wb 62); (Item Wb 10); (Item Wb 0)]).

Definition item_version'2detc'23str'2e64 : item :=
  (IData (a "version-etc#str.64") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 116); (Item Wb 116); (Item Wb 112); (Item Wb 115); (Item Wb 58); (Item Wb 47); (Item Wb 47); (Item Wb 119); (Item Wb 119); (Item Wb 119); (Item Wb 46); (Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 47); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 47); (Item Wb 0)]).

Definition fn_version_etc : func :=
  ir_fn{ "export" "version_etc"(P %"v0", P %"v2", P %"v4", P %"v6") -> RVoid {
  @"start":
    %"v8" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #32;
    %"chk0" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk0" + 0] <- %"va_args";
    call void $"version_etc_va"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8")
    => ret void
} }.

Definition fn_version_etc_arn : func :=
  ir_fn{ "export" "version_etc_arn"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", L %"v10") -> RVoid {
  @"start":
    %"v16" : L = Ptoi %"v2";
    %"v17" : W = (Cmp Ne L) %"v16", #0
    => br %"v17" ? "L12" : "L13";
  @"L12":
    %"v19" : P = Copy $"version-etc#str.41";
    call %"v23" : W = $"fprintf"(P %"v0", P %"v19", P %"v2", P %"v4", P %"v6")
    => goto "L14";
  @"L13":
    %"v25" : P = Copy $"version-etc#str.42";
    call %"v28" : W = $"fprintf"(P %"v0", P %"v25", P %"v4", P %"v6")
    => goto "L14";
  @"L14":
    %"v30" : P = Copy $"version_etc_copyright";
    %"v31" : P = Copy $"version-etc#str.43";
    %"v32" : P = Copy $"version-etc#str.44";
    call %"v33" : W = $"fprintf"(P %"v0", P %"v30", P %"v32", W #2026);
    %"v34" : P = Copy $"version-etc#str.45";
    call %"v36" : W = $"fputs"(P %"v34", P %"v0");
    %"v38" : P = Copy $"version-etc#str.43";
    %"v39" : P = Copy $"version-etc#str.46";
    %"v40" : P = Copy $"version-etc#str.47";
    call %"v41" : W = $"fprintf"(P %"v0", P %"v39", P %"v40");
    %"v42" : P = Copy $"version-etc#str.45";
    call %"v44" : W = $"fputs"(P %"v42", P %"v0");
    %"v262" : W = (Cmp Ult L) %"v10", #5
    => br %"v262" ? "L263" : "L264";
  @"L49":
    %"v51" : P = Copy $"version-etc#str.43";
    %"v52" : P = Copy $"version-etc#str.48";
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v56" : W = $"fprintf"(P %"v0", P %"v52", P %"v55")
    => goto "L47";
  @"L57":
    %"v59" : P = Copy $"version-etc#str.43";
    %"v60" : P = Copy $"version-etc#str.49";
    %"chk1" : A = (Check 0 8 Read 8) %"v8";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v65" = %"v8" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call %"v67" : W = $"fprintf"(P %"v0", P %"v60", P %"v63", P %"v66")
    => goto "L47";
  @"L68":
    %"v70" : P = Copy $"version-etc#str.43";
    %"v71" : P = Copy $"version-etc#str.50";
    %"chk3" : A = (Check 0 8 Read 8) %"v8";
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v76" = %"v8" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v76";
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v79" = %"v8" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v79";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v81" : W = $"fprintf"(P %"v0", P %"v71", P %"v74", P %"v77", P %"v80")
    => goto "L47";
  @"L82":
    %"v84" : P = Copy $"version-etc#str.43";
    %"v85" : P = Copy $"version-etc#str.51";
    %"chk6" : A = (Check 0 8 Read 8) %"v8";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v90" = %"v8" +p #8;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk6", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v93" = %"v8" +p #16;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk6", %"v93";
    %"v94" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v96" = %"v8" +p #24;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk6", %"v96";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call %"v98" : W = $"fprintf"(P %"v0", P %"v85", P %"v88", P %"v91", P %"v94", P %"v97")
    => goto "L47";
  @"L99":
    %"v101" : P = Copy $"version-etc#str.43";
    %"v102" : P = Copy $"version-etc#str.52";
    %"chk10" : A = (Check 0 8 Read 8) %"v8";
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v107" = %"v8" +p #8;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk10", %"v107";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v110" = %"v8" +p #16;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk10", %"v110";
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v113" = %"v8" +p #24;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk10", %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v116" = %"v8" +p #32;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk10", %"v116";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk14";
    call %"v118" : W = $"fprintf"(P %"v0", P %"v102", P %"v105", P %"v108", P %"v111", P %"v114", P %"v117")
    => goto "L47";
  @"L119":
    %"v121" : P = Copy $"version-etc#str.43";
    %"v122" : P = Copy $"version-etc#str.53";
    %"chk15" : A = (Check 0 8 Read 8) %"v8";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v127" = %"v8" +p #8;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk15", %"v127";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v130" = %"v8" +p #16;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk15", %"v130";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v133" = %"v8" +p #24;
    %"chk18" : A = (HalfCheck Upper 0 8 Read 8) %"chk15", %"v133";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v136" = %"v8" +p #32;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk15", %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v139" = %"v8" +p #40;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk15", %"v139";
    %"v140" : P = (RawLoadPointer 0 load_effects) %"chk20";
    call %"v141" : W = $"fprintf"(P %"v0", P %"v122", P %"v125", P %"v128", P %"v131", P %"v134", P %"v137", P %"v140")
    => goto "L47";
  @"L142":
    %"v144" : P = Copy $"version-etc#str.43";
    %"v145" : P = Copy $"version-etc#str.54";
    %"chk21" : A = (Check 0 8 Read 8) %"v8";
    %"v148" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v150" = %"v8" +p #8;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v150";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v153" = %"v8" +p #16;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v153";
    %"v154" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v156" = %"v8" +p #24;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v156";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v159" = %"v8" +p #32;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v159";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v162" = %"v8" +p #40;
    %"chk26" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v162";
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v165" = %"v8" +p #48;
    %"chk27" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v165";
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk27";
    call %"v167" : W = $"fprintf"(P %"v0", P %"v145", P %"v148", P %"v151", P %"v154", P %"v157", P %"v160", P %"v163", P %"v166")
    => goto "L47";
  @"L168":
    %"v170" : P = Copy $"version-etc#str.43";
    %"v171" : P = Copy $"version-etc#str.55";
    %"chk28" : A = (Check 0 8 Read 8) %"v8";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v176" = %"v8" +p #8;
    %"chk29" : A = (HalfCheck Upper 0 8 Read 8) %"chk28", %"v176";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v179" = %"v8" +p #16;
    %"chk30" : A = (HalfCheck Upper 0 8 Read 8) %"chk28", %"v179";
    %"v180" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v182" = %"v8" +p #24;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk28", %"v182";
    %"v183" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v185" = %"v8" +p #32;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk28", %"v185";
    %"v186" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v188" = %"v8" +p #40;
    %"chk33" : A = (HalfCheck Upper 0 8 Read 8) %"chk28", %"v188";
    %"v189" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v191" = %"v8" +p #48;
    %"chk34" : A = (HalfCheck Upper 0 8 Read 8) %"chk28", %"v191";
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v194" = %"v8" +p #56;
    %"chk35" : A = (HalfCheck Upper 0 8 Read 8) %"chk28", %"v194";
    %"v195" : P = (RawLoadPointer 0 load_effects) %"chk35";
    call %"v196" : W = $"fprintf"(P %"v0", P %"v171", P %"v174", P %"v177", P %"v180", P %"v183", P %"v186", P %"v189", P %"v192", P %"v195")
    => goto "L47";
  @"L197":
    %"v199" : P = Copy $"version-etc#str.43";
    %"v200" : P = Copy $"version-etc#str.56";
    %"chk36" : A = (Check 0 8 Read 8) %"v8";
    %"v203" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v205" = %"v8" +p #8;
    %"chk37" : A = (HalfCheck Upper 0 8 Read 8) %"chk36", %"v205";
    %"v206" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v208" = %"v8" +p #16;
    %"chk38" : A = (HalfCheck Upper 0 8 Read 8) %"chk36", %"v208";
    %"v209" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v211" = %"v8" +p #24;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk36", %"v211";
    %"v212" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v214" = %"v8" +p #32;
    %"chk40" : A = (HalfCheck Upper 0 8 Read 8) %"chk36", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v217" = %"v8" +p #40;
    %"chk41" : A = (HalfCheck Upper 0 8 Read 8) %"chk36", %"v217";
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v220" = %"v8" +p #48;
    %"chk42" : A = (HalfCheck Upper 0 8 Read 8) %"chk36", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v223" = %"v8" +p #56;
    %"chk43" : A = (HalfCheck Upper 0 8 Read 8) %"chk36", %"v223";
    %"v224" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v226" = %"v8" +p #64;
    %"chk44" : A = (HalfCheck Upper 0 8 Read 8) %"chk36", %"v226";
    %"v227" : P = (RawLoadPointer 0 load_effects) %"chk44";
    call %"v228" : W = $"fprintf"(P %"v0", P %"v200", P %"v203", P %"v206", P %"v209", P %"v212", P %"v215", P %"v218", P %"v221", P %"v224", P %"v227")
    => goto "L47";
  @"L229":
    %"v231" : P = Copy $"version-etc#str.43";
    %"v232" : P = Copy $"version-etc#str.57";
    %"chk45" : A = (Check 0 8 Read 8) %"v8";
    %"v235" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v237" = %"v8" +p #8;
    %"chk46" : A = (HalfCheck Upper 0 8 Read 8) %"chk45", %"v237";
    %"v238" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v240" = %"v8" +p #16;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk45", %"v240";
    %"v241" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v243" = %"v8" +p #24;
    %"chk48" : A = (HalfCheck Upper 0 8 Read 8) %"chk45", %"v243";
    %"v244" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v246" = %"v8" +p #32;
    %"chk49" : A = (HalfCheck Upper 0 8 Read 8) %"chk45", %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v249" = %"v8" +p #40;
    %"chk50" : A = (HalfCheck Upper 0 8 Read 8) %"chk45", %"v249";
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v252" = %"v8" +p #48;
    %"chk51" : A = (HalfCheck Upper 0 8 Read 8) %"chk45", %"v252";
    %"v253" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v255" = %"v8" +p #56;
    %"chk52" : A = (HalfCheck Upper 0 8 Read 8) %"chk45", %"v255";
    %"v256" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"v258" = %"v8" +p #64;
    %"chk53" : A = (HalfCheck Upper 0 8 Read 8) %"chk45", %"v258";
    %"v259" : P = (RawLoadPointer 0 load_effects) %"chk53";
    call %"v260" : W = $"fprintf"(P %"v0", P %"v232", P %"v235", P %"v238", P %"v241", P %"v244", P %"v247", P %"v250", P %"v253", P %"v256", P %"v259")
    => goto "L47";
  @"L263":
    %"v265" : W = (Cmp Ult L) %"v10", #2
    => br %"v265" ? "L266" : "L267";
  @"L266":
    %"v268" : W = (Cmp Eq L) %"v10", #0
    => br %"v268" ? "L47" : "L269";
  @"L269":
    %"v270" : W = (Cmp Eq L) %"v10", #1
    => br %"v270" ? poll "L49" : poll "L229";
  @"L267":
    %"v272" : W = (Cmp Eq L) %"v10", #2
    => br %"v272" ? poll "L57" : "L273";
  @"L273":
    %"v274" : W = (Cmp Eq L) %"v10", #3
    => br %"v274" ? poll "L68" : "L275";
  @"L275":
    %"v276" : W = (Cmp Eq L) %"v10", #4
    => br %"v276" ? poll "L82" : poll "L229";
  @"L264":
    %"v278" : W = (Cmp Ult L) %"v10", #7
    => br %"v278" ? "L279" : "L280";
  @"L279":
    %"v281" : W = (Cmp Eq L) %"v10", #5
    => br %"v281" ? poll "L99" : "L282";
  @"L282":
    %"v283" : W = (Cmp Eq L) %"v10", #6
    => br %"v283" ? poll "L119" : poll "L229";
  @"L280":
    %"v285" : W = (Cmp Eq L) %"v10", #7
    => br %"v285" ? poll "L142" : "L286";
  @"L286":
    %"v287" : W = (Cmp Eq L) %"v10", #8
    => br %"v287" ? poll "L168" : "L288";
  @"L288":
    %"v289" : W = (Cmp Eq L) %"v10", #9
    => br %"v289" ? poll "L197" : poll "L229";
  @"L47":
    => ret void
} }.

Definition fn_version_etc_va : func :=
  ir_fn{ "export" "version_etc_va"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8") -> RVoid {
  @"start":
    %"v11" : P = (Alloc 8) #80
    => goto "L12";
  @"L12" [%"pr.1" : L = phi("L14" => %"v31", "start" => #0)]:
    %"v17" : W = (Cmp Ult L) %"pr.1", #10
    => br %"v17" ? "L18" : "L19";
  @"L18":
    %"v21" : L = Shl %"pr.1", #3;
    %"v22" = %"v11" +p %"v21";
    %"v24" : P = VaArg %"v8";
    %"chk0" : A = (Check 0 8 Write 8) %"v22";
    store.ptr [%"chk0" + 0] <- %"v24";
    %"v25" : L = Ptoi %"v24";
    %"v26" : L = Ptoi #0;
    %"v27" : W = (Cmp Ne L) %"v25", %"v26"
    => goto "L19";
  @"L19" [%"v29" : W = phi("L12" => #0, "L18" => %"v27")]:
    => br %"v29" ? "L14" : "L15";
  @"L14":
    %"v31" : L = Add %"pr.1", #1
    => goto poll "L12";
  @"L15":
    call void $"version_etc_arn"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v11", L %"pr.1")
    => ret void
} }.
