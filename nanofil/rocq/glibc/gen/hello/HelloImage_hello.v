(** This file defines checked IR from the `hello` object of HelloImage.
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

Definition item_hello'23parse_options'2elongopts'2e64 : item :=
  (IData (a "hello#parse_options.longopts.64") (LRo (a "local")) 8 [(Sym (a "hello#str.65") 0); (Item Ww 1); (Zero 4); (Item Wl 0); (Item Ww 103); (Zero 4); (Sym (a "hello#str.66") 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 116); (Zero 4); (Sym (a "hello#str.67") 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 128); (Zero 4); (Sym (a "hello#str.68") 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 129); (Zero 4); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 0); (Zero 4)]).

Definition item_hello'23str'2e54 : item :=
  (IData (a "hello#str.54") (LRo (a "local")) 1 [(Item Wb 85); (Item Wb 115); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 91); (Item Wb 79); (Item Wb 80); (Item Wb 84); (Item Wb 73); (Item Wb 79); (Item Wb 78); (Item Wb 93); (Item Wb 46); (Item Wb 46); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_hello'23str'2e55 : item :=
  (IData (a "hello#str.55") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 102); (Item Wb 114); (Item Wb 105); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 121); (Item Wb 44); (Item Wb 32); (Item Wb 99); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 105); (Item Wb 122); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_hello'23str'2e56 : item :=
  (IData (a "hello#str.56") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 0)]).

Definition item_hello'23str'2e57 : item :=
  (IData (a "hello#str.57") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 32); (Item Wb 45); (Item Wb 116); (Item Wb 44); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 100); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 100); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 10); (Item Wb 0)]).

Definition item_hello'23str'2e58 : item :=
  (IData (a "hello#str.58") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 32); (Item Wb 45); (Item Wb 103); (Item Wb 44); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 61); (Item Wb 84); (Item Wb 69); (Item Wb 88); (Item Wb 84); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 84); (Item Wb 69); (Item Wb 88); (Item Wb 84); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 32); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 32); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 109); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 10); (Item Wb 0)]).

Definition item_hello'23str'2e59 : item :=
  (IData (a "hello#str.59") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 115); (Item Wb 112); (Item Wb 108); (Item Wb 97); (Item Wb 121); (Item Wb 32); (Item Wb 116); (Item Wb 104); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 10); (Item Wb 0)]).

Definition item_hello'23str'2e60 : item :=
  (IData (a "hello#str.60") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 32); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 109); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 10); (Item Wb 0)]).

Definition item_hello'23str'2e61 : item :=
  (IData (a "hello#str.61") (LRo (a "local")) 1 [(Item Wb 101); (Item Wb 110); (Item Wb 95); (Item Wb 0)]).

Definition item_hello'23str'2e62 : item :=
  (IData (a "hello#str.62") (LRo (a "local")) 1 (app [(Item Wb 82); (Item Wb 101); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 103); (Item Wb 115); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 60); (Item Wb 104); (Item Wb 116); (Item Wb 116); (Item Wb 112)] [(Item Wb 115); (Item Wb 58); (Item Wb 47); (Item Wb 47); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 106); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 47); (Item Wb 116); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 47); (Item Wb 62); (Item Wb 10); (Item Wb 0)])).

Definition item_hello'23str'2e63 : item :=
  (IData (a "hello#str.63") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 78); (Item Wb 85); (Item Wb 32); (Item Wb 72); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 0)]).

Definition item_hello'23str'2e65 : item :=
  (IData (a "hello#str.65") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition item_hello'23str'2e66 : item :=
  (IData (a "hello#str.66") (LRo (a "local")) 1 [(Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 100); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition item_hello'23str'2e67 : item :=
  (IData (a "hello#str.67") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 0)]).

Definition item_hello'23str'2e68 : item :=
  (IData (a "hello#str.68") (LRo (a "local")) 1 [(Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 0)]).

Definition item_hello'23str'2e69 : item :=
  (IData (a "hello#str.69") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 58); (Item Wb 116); (Item Wb 0)]).

Definition item_hello'23str'2e70 : item :=
  (IData (a "hello#str.70") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 0)]).

Definition item_hello'23str'2e71 : item :=
  (IData (a "hello#str.71") (LRo (a "local")) 1 [(Item Wb 50); (Item Wb 46); (Item Wb 49); (Item Wb 50); (Item Wb 46); (Item Wb 51); (Item Wb 0)]).

Definition item_hello'23str'2e72 : item :=
  (IData (a "hello#str.72") (LRo (a "local")) 1 [(Item Wb 75); (Item Wb 97); (Item Wb 114); (Item Wb 108); (Item Wb 32); (Item Wb 66); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition item_hello'23str'2e73 : item :=
  (IData (a "hello#str.73") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 97); (Item Wb 109); (Item Wb 105); (Item Wb 32); (Item Wb 75); (Item Wb 101); (Item Wb 114); (Item Wb 111); (Item Wb 108); (Item Wb 97); (Item Wb 0)]).

Definition item_hello'23str'2e74 : item :=
  (IData (a "hello#str.74") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 105); (Item Wb 109); (Item Wb 32); (Item Wb 77); (Item Wb 101); (Item Wb 121); (Item Wb 101); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition item_hello'23str'2e75 : item :=
  (IData (a "hello#str.75") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 117); (Item Wb 98); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 84); (Item Wb 104); (Item Wb 111); (Item Wb 109); (Item Wb 97); (Item Wb 115); (Item Wb 0)]).

Definition item_hello'23str'2e76 : item :=
  (IData (a "hello#str.76") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 44); (Item Wb 32); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 108); (Item Wb 100); (Item Wb 0)]).

Definition item_hello'23str'2e77 : item :=
  (IData (a "hello#str.77") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition item_hello'23str'2e78 : item :=
  (IData (a "hello#str.78") (LRo (a "local")) 1 [(Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_hello'23str'2e79 : item :=
  (IData (a "hello#str.79") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 39); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 109); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition item_hello'23str'2e80 : item :=
  (IData (a "hello#str.80") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition item_hello'23str'2e81 : item :=
  (IData (a "hello#str.81") (LRo (a "local")) 1 [(Item Wb 72); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 44); (Item Wb 32); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 108); (Item Wb 100); (Item Wb 33); (Item Wb 0)]).

Definition item_hello'23str'2e82 : item :=
  (IData (a "hello#str.82") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 109); (Item Wb 117); (Item Wb 108); (Item Wb 116); (Item Wb 105); (Item Wb 98); (Item Wb 121); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition item_hello'23str'2e83 : item :=
  (IData (a "hello#str.83") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 108); (Item Ww 115); (Item Ww 10); (Item Ww 0)]).

Definition fn_main : func :=
  ir_fn{ "export" "main"(W %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 8) #8;
    %"v6" : P = (Alloc 4) #8;
    call void $"mbszero"(P %"v6");
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"set_program_name"(P %"v10");
    %"v11" : P = Copy $"hello#str.80";
    call %"v12" : P = $"setlocale"(W #6, P %"v11");
    %"v13" : P = Copy $"hello#str.81";
    %"chk1" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk1" + 0] <- %"v13";
    %"v14" : P = Copy $"close_stdout";
    call %"v15" : W = $"atexit"(P %"v14")
    => goto "iw_1.L8";
  @"iw_1.L8" [%"iw_1.pr.2" : W = phi("iw_1.L35" => %"iw_1.pr.2", "iw_1.L42" => %"iw_1.pr.2", "iw_1.L52" => #1, "start" => #0)]:
    %"iw_1.v13" : P = Copy $"hello#str.69";
    %"iw_1.v14" : P = Copy $"hello#parse_options.longopts.64";
    call %"iw_1.v15" : W = $"getopt_long"(W %"v0", P %"v2", P %"iw_1.v13", P %"iw_1.v14", P #0);
    %"iw_1.v17" : W = (Cmp Ne W) %"iw_1.v15", #4294967295
    => br %"iw_1.v17" ? "iw_1.L19" : "iw_1.L10";
  @"iw_1.L21":
    %"iw_1.v22" : P = Copy $"stdout";
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v22";
    %"iw_1.v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v24" : P = Copy $"hello#str.70";
    %"iw_1.v25" : P = Copy $"hello#str.63";
    %"iw_1.v26" : P = Copy $"hello#str.71";
    %"iw_1.v27" : P = Copy $"hello#str.72";
    call %"iw_1.v28" : P = $"proper_name"(P %"iw_1.v27");
    %"iw_1.v29" : P = Copy $"hello#str.73";
    call %"iw_1.v30" : P = $"proper_name"(P %"iw_1.v29");
    %"iw_1.v31" : P = Copy $"hello#str.74";
    call %"iw_1.v32" : P = $"proper_name"(P %"iw_1.v31");
    %"iw_1.v33" : P = Copy $"hello#str.75";
    call %"iw_1.v34" : P = $"proper_name"(P %"iw_1.v33");
    call void $"version_etc"(P %"iw_1.v23", P %"iw_1.v24", P %"iw_1.v25", P %"iw_1.v26", P %"iw_1.v28", P %"iw_1.v30", P %"iw_1.v32", P %"iw_1.v34", P #0);
    call void $"exit"(W #0)
    => goto "iw_1.L35";
  @"iw_1.L35":
    %"iw_1.v37" : P = Copy $"optarg";
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v37";
    %"iw_1.v38" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Write 8) %"chk1", %"v4";
    store.ptr [%"chk4" + 0] <- %"iw_1.v38"
    => goto poll "iw_1.L8";
  @"iw_1.L39":
    %"iw_1.v40" : P = Copy $"stdout";
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"iw_1.iw_1.v3" : P = $"setlocale"(W #5, P #0);
    %"iw_1.iw_1.v5" : P = Copy $"hello#str.54";
    %"iw_1.iw_1.v6" : P = Copy $"program_name";
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v6";
    %"iw_1.iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"iw_1.iw_1.v8" : W = $"fprintf"(P %"iw_1.v41", P %"iw_1.iw_1.v5", P %"iw_1.iw_1.v7");
    %"iw_1.iw_1.v9" : P = Copy $"hello#str.55";
    call %"iw_1.iw_1.v11" : W = $"fputs"(P %"iw_1.iw_1.v9", P %"iw_1.v41");
    %"iw_1.iw_1.v12" : P = Copy $"hello#str.56";
    call %"iw_1.iw_1.v14" : W = $"fputs"(P %"iw_1.iw_1.v12", P %"iw_1.v41");
    %"iw_1.iw_1.v15" : P = Copy $"hello#str.57";
    call %"iw_1.iw_1.v17" : W = $"fputs"(P %"iw_1.iw_1.v15", P %"iw_1.v41");
    %"iw_1.iw_1.v18" : P = Copy $"hello#str.58";
    call %"iw_1.iw_1.v20" : W = $"fputs"(P %"iw_1.iw_1.v18", P %"iw_1.v41");
    %"iw_1.iw_1.v21" : P = Copy $"hello#str.56";
    call %"iw_1.iw_1.v23" : W = $"fputs"(P %"iw_1.iw_1.v21", P %"iw_1.v41");
    %"iw_1.iw_1.v24" : P = Copy $"hello#str.59";
    call %"iw_1.iw_1.v26" : W = $"fputs"(P %"iw_1.iw_1.v24", P %"iw_1.v41");
    %"iw_1.iw_1.v27" : P = Copy $"hello#str.60";
    call %"iw_1.iw_1.v29" : W = $"fputs"(P %"iw_1.iw_1.v27", P %"iw_1.v41");
    call void $"emit_bug_reporting_address"();
    %"iw_1.iw_1.v34" : L = Ptoi %"iw_1.iw_1.v3";
    %"iw_1.iw_1.v35" : W = (Cmp Ne L) %"iw_1.iw_1.v34", #0
    => br %"iw_1.iw_1.v35" ? "iw_1.iw_1.L36" : "iw_1.iw_1.L37";
  @"iw_1.iw_1.L36":
    %"iw_1.iw_1.v39" : P = Copy $"hello#str.61";
    call %"iw_1.iw_1.v41" : W = $"strncmp"(P %"iw_1.iw_1.v3", P %"iw_1.iw_1.v39", L #3);
    %"iw_1.iw_1.v42" : W = (Cmp Ne W) %"iw_1.iw_1.v41", #0
    => goto "iw_1.iw_1.L37";
  @"iw_1.iw_1.L37" [%"iw_1.iw_1.v43" : W = phi("iw_1.L39" => #0, "iw_1.iw_1.L36" => %"iw_1.iw_1.v42")]:
    => br %"iw_1.iw_1.v43" ? "iw_1.iw_1.L30" : "iw_1.iw_1.L32";
  @"iw_1.iw_1.L30":
    %"iw_1.iw_1.v45" : P = Copy $"hello#str.62";
    %"iw_1.iw_1.v46" : P = Copy $"hello#str.63";
    call %"iw_1.iw_1.v47" : W = $"fprintf"(P %"iw_1.v41", P %"iw_1.iw_1.v45", P %"iw_1.iw_1.v46")
    => goto "iw_1.iw_1.L32";
  @"iw_1.iw_1.L32":
    %"iw_1.iw_1.v52" : P = Copy $"stderr";
    %"chk7" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v52";
    %"iw_1.iw_1.v53" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.iw_1.v54" : L = Ptoi %"iw_1.v41";
    %"iw_1.iw_1.v55" : L = Ptoi %"iw_1.iw_1.v53";
    %"iw_1.iw_1.v56" : W = (Cmp Eq L) %"iw_1.iw_1.v54", %"iw_1.iw_1.v55"
    => br %"iw_1.iw_1.v56" ? "iw_1.iw_1.L50" : "iw_1.iw_1.L49";
  @"iw_1.iw_1.L49":
    => goto "iw_1.iw_1.L50";
  @"iw_1.iw_1.L50" [%"iw_1.iw_1.v57" : W = phi("iw_1.iw_1.L49" => #0, "iw_1.iw_1.L32" => #1)]:
    call void $"exit"(W %"iw_1.iw_1.v57")
    => goto "iw_1.L42";
  @"iw_1.L42":
    %"iw_1.v44" : P = Copy $"hello#str.76";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk1", %"v4";
    store.ptr [%"chk8" + 0] <- %"iw_1.v44"
    => goto poll "iw_1.L8";
  @"iw_1.L19":
    %"iw_1.v47" : W = (Cmp Eq W) %"iw_1.v15", #129
    => br %"iw_1.v47" ? poll "iw_1.L21" : "iw_1.L48";
  @"iw_1.L48":
    %"iw_1.v49" : W = (Cmp Eq W) %"iw_1.v15", #103
    => br %"iw_1.v49" ? poll "iw_1.L35" : "iw_1.L50";
  @"iw_1.L50":
    %"iw_1.v51" : W = (Cmp Eq W) %"iw_1.v15", #128
    => br %"iw_1.v51" ? poll "iw_1.L39" : "iw_1.L52";
  @"iw_1.L52":
    %"iw_1.v53" : W = (Cmp Eq W) %"iw_1.v15", #116
    => br %"iw_1.v53" ? poll "iw_1.L42" : poll "iw_1.L8";
  @"iw_1.L10":
    => br %"iw_1.pr.2" ? "iw_1.L60" : "iw_1.L59";
  @"iw_1.L59":
    %"iw_1.v61" : P = Copy $"optind";
    %"chk9" : A = (Check 0 4 Read 1) %"iw_1.v61";
    %"iw_1.v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"iw_1.v64" : W = (Cmp Slt W) %"iw_1.v62", %"v0"
    => goto "iw_1.L60";
  @"iw_1.L60" [%"iw_1.v66" : W = phi("iw_1.L10" => #1, "iw_1.L59" => %"iw_1.v64")]:
    => br %"iw_1.v66" ? "iw_1.L55" : "iw_1.join";
  @"iw_1.L55":
    %"iw_1.v71" : P = Copy $"optind";
    %"chk10" : A = (Check 0 4 Read 1) %"iw_1.v71";
    %"iw_1.v72" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"iw_1.v73" : L = (Ext Sw) %"iw_1.v72";
    %"iw_1.v74" : L = Shl %"iw_1.v73", #3;
    %"iw_1.v75" = %"v2" +p %"iw_1.v74";
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v75";
    %"iw_1.v76" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v77" : L = Ptoi %"iw_1.v76";
    %"iw_1.v78" : W = (Cmp Ne L) %"iw_1.v77", #0
    => br %"iw_1.v78" ? "iw_1.L79" : "iw_1.L113";
  @"iw_1.L79":
    %"iw_1.v82" : P = Copy $"hello#str.77";
    %"iw_1.v83" : P = Copy $"hello#str.78";
    %"iw_1.v85" : P = Copy $"optind";
    %"chk12" : A = (Check 0 4 Read 1) %"iw_1.v85";
    %"iw_1.v86" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"iw_1.v87" : L = (Ext Sw) %"iw_1.v86";
    %"iw_1.v88" : L = Shl %"iw_1.v87", #3;
    %"iw_1.v89" = %"v2" +p %"iw_1.v88";
    %"chk13" : A = (Check 0 8 Read 8) %"iw_1.v89";
    %"iw_1.v90" : P = (RawLoadPointer 0 load_effects) %"chk13";
    call void $"error"(W #0, W #0, P %"iw_1.v82", P %"iw_1.v83", P %"iw_1.v90")
    => goto "iw_1.L113";
  @"iw_1.L113":
    %"iw_1.v116" : P = Copy $"stderr";
    %"chk14" : A = (Check 0 8 Read 8) %"iw_1.v116";
    %"iw_1.v117" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"iw_1.v118" : P = Copy $"hello#str.79";
    %"iw_1.v119" : P = Copy $"program_name";
    %"chk15" : A = (Check 0 8 Read 8) %"iw_1.v119";
    %"iw_1.v120" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call %"iw_1.v121" : W = $"fprintf"(P %"iw_1.v117", P %"iw_1.v118", P %"iw_1.v120");
    call void $"exit"(W #1)
    => goto "iw_1.join";
  @"iw_1.join":
    %"chk16" : A = (Renew 0 8 Read 8) %"chk1", %"v4";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk16";
    call %"v19" : L = $"strlen"(P %"v18");
    %"v20" : L = Add %"v19", #1;
    %"v22" : L = Shl %"v20", #2;
    call %"v23" : P = $"xmalloc"(L %"v22");
    call %"v26" : L = $"rpl_mbsrtowcs"(P %"v23", P %"v4", L %"v20", P %"v6");
    %"v33" : W = (Cmp Eq L) %"v26", #18446744073709551615
    => br %"v33" ? "L34" : "L29";
  @"L34":
    call %"v37" : P = $"__errno_location"();
    %"chk17" : A = (Check 0 4 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v39" : P = Copy $"hello#str.82";
    call void $"error"(W #1, W %"v38", P %"v39")
    => unreachable;
  @"L29":
    %"v56" : P = Copy $"hello#str.83";
    call %"v58" : W = $"wprintf"(P %"v56", P %"v23");
    call void $"free"(P %"v23");
    call void $"exit"(W #0)
    => ret #0
} }.
