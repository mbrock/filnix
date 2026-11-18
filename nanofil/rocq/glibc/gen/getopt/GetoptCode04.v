(** This file contains part of glibc's checked option-parser module.
    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
From Glibc Require Import GetoptCode02 GetoptCode03.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** These items retain their order in the linked module. *)
Definition getopt_items_04 : list term :=
  [
    cap_fn{ "export" "_getopt_internal_r" [param "w" %"v0"; param "p" %"v2"; param "p" %"v4"; param "p" %"v6"; param "p" %"v8"; param "w" %"v10"; param "p" %"v12"; param "w" %"v14"] -> "w"
      blocks (getopt_blocks_02 ++ getopt_blocks_03) };
    cap_fn{ "export" "_getopt_internal" [param "w" %"v0"; param "p" %"v2"; param "p" %"v4"; param "p" %"v6"; param "p" %"v8"; param "w" %"v10"; param "w" %"v12"] -> "w"
      {
        @"start":
          %"v15" : "p" = "copy" $"glibc_getopt#getopt_data";
          %"v16" : "p" = "copy" $"optind";
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"v16";
          %"v17" : "w" = op "raw_load"("sw", int 0) %"chk0";
          %"chk1" : "a" = op "check"(int 0, int 4, "write", int 1) %"v15";
          store "w" [%"chk1" + 0] <- %"v17";
          %"v18" : "p" = "copy" $"glibc_getopt#getopt_data";
          %"v19" = %"v18" +p #4;
          %"v20" : "p" = "copy" $"opterr";
          %"chk2" : "a" = op "check"(int 0, int 4, "read", int 1) %"v20";
          %"v21" : "w" = op "raw_load"("sw", int 0) %"chk2";
          %"chk3" : "a" = op "check"(int 0, int 4, "write", int 1) %"v19";
          store "w" [%"chk3" + 0] <- %"v21";
          %"v28" : "p" = "copy" $"glibc_getopt#getopt_data";
          call %"v30" : "w" = $"_getopt_internal_r"("w" %"v0", "p" %"v2", "p" %"v4", "p" %"v6", "p" %"v8", "w" %"v10", "p" %"v28", "w" %"v12");
          %"v31" : "p" = "copy" $"optind";
          %"v32" : "p" = "copy" $"glibc_getopt#getopt_data";
          %"chk4" : "a" = op "check"(int 0, int 4, "read", int 1) %"v32";
          %"v33" : "w" = op "raw_load"("sw", int 0) %"chk4";
          %"chk5" : "a" = op "check"(int 0, int 4, "write", int 1) %"v31";
          store "w" [%"chk5" + 0] <- %"v33";
          %"v34" : "p" = "copy" $"optarg";
          %"v35" : "p" = "copy" $"glibc_getopt#getopt_data";
          %"v36" = %"v35" +p #16;
          %"chk6" : "a" = op "check"(int 0, int 8, "read", int 8) %"v36";
          %"v37" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          %"chk7" : "a" = op "check"(int 0, int 8, "write", int 8) %"v34";
          store.ptr [%"chk7" + 0] <- %"v37";
          %"v38" : "p" = "copy" $"optopt";
          %"v39" : "p" = "copy" $"glibc_getopt#getopt_data";
          %"v40" = %"v39" +p #8;
          %"chk8" : "a" = op "check"(int 0, int 4, "read", int 1) %"v40";
          %"v41" : "w" = op "raw_load"("sw", int 0) %"chk8";
          %"chk9" : "a" = op "check"(int 0, int 4, "write", int 1) %"v38";
          store "w" [%"chk9" + 0] <- %"v41"
          => ret %"v30"
      } };
    cap{ op "data"("glibc_getopt#getopt_data", "local", int 8, [op "zero"(int 56)]) };
    cap{ op "data"("optarg", "export", int 8, [op "zero"(int 8)]) };
    cap{ op "data"("opterr", "export", int 4, [op "item"("w", #1)]) };
    cap{ op "data"("optind", "export", int 4, [op "item"("w", #1)]) };
    cap{ op "data"("optopt", "export", int 4, [op "item"("w", #63)]) };
    cap{ op "data"("glibc_getopt#str.138", op "ro"("local"), int 1, [op "item"("b", #37); op "item"("b", #115); op "item"("b", #58); op "item"("b", #32); op "item"("b", #111); op "item"("b", #112); op "item"("b", #116); op "item"("b", #105); op "item"("b", #111); op "item"("b", #110); op "item"("b", #32); op "item"("b", #39); op "item"("b", #37); op "item"("b", #115); op "item"("b", #37); op "item"("b", #115); op "item"("b", #39); op "item"("b", #32); op "item"("b", #105); op "item"("b", #115); op "item"("b", #32); op "item"("b", #97); op "item"("b", #109); op "item"("b", #98); op "item"("b", #105); op "item"("b", #103); op "item"("b", #117); op "item"("b", #111); op "item"("b", #117); op "item"("b", #115); op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.139", op "ro"("local"), int 1, [op "item"("b", #37); op "item"("b", #115); op "item"("b", #58); op "item"("b", #32); op "item"("b", #111); op "item"("b", #112); op "item"("b", #116); op "item"("b", #105); op "item"("b", #111); op "item"("b", #110); op "item"("b", #32); op "item"("b", #39); op "item"("b", #37); op "item"("b", #115); op "item"("b", #37); op "item"("b", #115); op "item"("b", #39); op "item"("b", #32); op "item"("b", #105); op "item"("b", #115); op "item"("b", #32); op "item"("b", #97); op "item"("b", #109); op "item"("b", #98); op "item"("b", #105); op "item"("b", #103); op "item"("b", #117); op "item"("b", #111); op "item"("b", #117); op "item"("b", #115); op "item"("b", #59); op "item"("b", #32); op "item"("b", #112); op "item"("b", #111); op "item"("b", #115); op "item"("b", #115); op "item"("b", #105); op "item"("b", #98); op "item"("b", #105); op "item"("b", #108); op "item"("b", #105); op "item"("b", #116); op "item"("b", #105); op "item"("b", #101); op "item"("b", #115); op "item"("b", #58); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.140", op "ro"("local"), int 1, [op "item"("b", #32); op "item"("b", #39); op "item"("b", #37); op "item"("b", #115); op "item"("b", #37); op "item"("b", #115); op "item"("b", #39); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.141", op "ro"("local"), int 1, [op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.142", op "ro"("local"), int 1, [op "item"("b", #37); op "item"("b", #115); op "item"("b", #58); op "item"("b", #32); op "item"("b", #117); op "item"("b", #110); op "item"("b", #114); op "item"("b", #101); op "item"("b", #99); op "item"("b", #111); op "item"("b", #103); op "item"("b", #110); op "item"("b", #105); op "item"("b", #122); op "item"("b", #101); op "item"("b", #100); op "item"("b", #32); op "item"("b", #111); op "item"("b", #112); op "item"("b", #116); op "item"("b", #105); op "item"("b", #111); op "item"("b", #110); op "item"("b", #32); op "item"("b", #39); op "item"("b", #37); op "item"("b", #115); op "item"("b", #37); op "item"("b", #115); op "item"("b", #39); op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.143", op "ro"("local"), int 1, [op "item"("b", #37); op "item"("b", #115); op "item"("b", #58); op "item"("b", #32); op "item"("b", #111); op "item"("b", #112); op "item"("b", #116); op "item"("b", #105); op "item"("b", #111); op "item"("b", #110); op "item"("b", #32); op "item"("b", #39); op "item"("b", #37); op "item"("b", #115); op "item"("b", #37); op "item"("b", #115); op "item"("b", #39); op "item"("b", #32); op "item"("b", #100); op "item"("b", #111); op "item"("b", #101); op "item"("b", #115); op "item"("b", #110); op "item"("b", #39); op "item"("b", #116); op "item"("b", #32); op "item"("b", #97); op "item"("b", #108); op "item"("b", #108); op "item"("b", #111); op "item"("b", #119); op "item"("b", #32); op "item"("b", #97); op "item"("b", #110); op "item"("b", #32); op "item"("b", #97); op "item"("b", #114); op "item"("b", #103); op "item"("b", #117); op "item"("b", #109); op "item"("b", #101); op "item"("b", #110); op "item"("b", #116); op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.144", op "ro"("local"), int 1, [op "item"("b", #37); op "item"("b", #115); op "item"("b", #58); op "item"("b", #32); op "item"("b", #111); op "item"("b", #112); op "item"("b", #116); op "item"("b", #105); op "item"("b", #111); op "item"("b", #110); op "item"("b", #32); op "item"("b", #39); op "item"("b", #37); op "item"("b", #115); op "item"("b", #37); op "item"("b", #115); op "item"("b", #39); op "item"("b", #32); op "item"("b", #114); op "item"("b", #101); op "item"("b", #113); op "item"("b", #117); op "item"("b", #105); op "item"("b", #114); op "item"("b", #101); op "item"("b", #115); op "item"("b", #32); op "item"("b", #97); op "item"("b", #110); op "item"("b", #32); op "item"("b", #97); op "item"("b", #114); op "item"("b", #103); op "item"("b", #117); op "item"("b", #109); op "item"("b", #101); op "item"("b", #110); op "item"("b", #116); op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.145", op "ro"("local"), int 1, [op "item"("b", #80); op "item"("b", #79); op "item"("b", #83); op "item"("b", #73); op "item"("b", #88); op "item"("b", #76); op "item"("b", #89); op "item"("b", #95); op "item"("b", #67); op "item"("b", #79); op "item"("b", #82); op "item"("b", #82); op "item"("b", #69); op "item"("b", #67); op "item"("b", #84); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.146", op "ro"("local"), int 1, [op "item"("b", #45); op "item"("b", #45); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.147", op "ro"("local"), int 1, [op "item"("b", #45); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.148", op "ro"("local"), int 1, [op "item"("b", #37); op "item"("b", #115); op "item"("b", #58); op "item"("b", #32); op "item"("b", #105); op "item"("b", #110); op "item"("b", #118); op "item"("b", #97); op "item"("b", #108); op "item"("b", #105); op "item"("b", #100); op "item"("b", #32); op "item"("b", #111); op "item"("b", #112); op "item"("b", #116); op "item"("b", #105); op "item"("b", #111); op "item"("b", #110); op "item"("b", #32); op "item"("b", #45); op "item"("b", #45); op "item"("b", #32); op "item"("b", #39); op "item"("b", #37); op "item"("b", #99); op "item"("b", #39); op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.149", op "ro"("local"), int 1, [op "item"("b", #37); op "item"("b", #115); op "item"("b", #58); op "item"("b", #32); op "item"("b", #111); op "item"("b", #112); op "item"("b", #116); op "item"("b", #105); op "item"("b", #111); op "item"("b", #110); op "item"("b", #32); op "item"("b", #114); op "item"("b", #101); op "item"("b", #113); op "item"("b", #117); op "item"("b", #105); op "item"("b", #114); op "item"("b", #101); op "item"("b", #115); op "item"("b", #32); op "item"("b", #97); op "item"("b", #110); op "item"("b", #32); op "item"("b", #97); op "item"("b", #114); op "item"("b", #103); op "item"("b", #117); op "item"("b", #109); op "item"("b", #101); op "item"("b", #110); op "item"("b", #116); op "item"("b", #32); op "item"("b", #45); op "item"("b", #45); op "item"("b", #32); op "item"("b", #39); op "item"("b", #37); op "item"("b", #99); op "item"("b", #39); op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_getopt#str.150", op "ro"("local"), int 1, [op "item"("b", #45); op "item"("b", #87); op "item"("b", #32); op "item"("b", #0)]) };
    cap_fn{ "export" "getopt_long" [param "w" %"v0"; param "p" %"v2"; param "p" %"v4"; param "p" %"v6"; param "p" %"v8"] -> "w"
      {
        @"start":
          call %"v15" : "w" = $"_getopt_internal"("w" %"v0", "p" %"v2", "p" %"v4", "p" %"v6", "p" %"v8", "w" #0, "w" #0)
          => ret %"v15"
      } }
  ].
