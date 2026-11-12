(** This file contains part of glibc's checked option-parser module.
    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** Character atoms retain their byte values. *)
Definition chr (n : nat) : term := TAtom (String (ascii_of_nat n) EmptyString).

(** These blocks retain their order in the linked module. *)
Definition getopt_blocks_01 : list term :=
  [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v25"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v25"]]];
            TApp "let" [TApp "tmp" [TAtom "v26"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]]];
          TApp "goto" [TAtom "L27"]];
        TApp "block" [TAtom "L27"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.1"]; TAtom "p"; TList [TApp "-" [TAtom "L29"; TApp "tmp" [TAtom "v41"]]; TApp "-" [TAtom "start"; TApp "tmp" [TAtom "v26"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "pr.1"]]];
            TApp "let" [TApp "tmp" [TAtom "v32"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk1"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v32"]; TAtom "L33"; TAtom "L34"]];
        TApp "block" [TAtom "L33"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v36"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "let" [TApp "tmp" [TAtom "v37"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v36"]; TApp "const" [TInt 61]]]];
          TApp "goto" [TAtom "L34"]];
        TApp "block" [TAtom "L34"; TList [TApp "phi" [TApp "tmp" [TAtom "v39"]; TAtom "w"; TList [TApp "-" [TAtom "L27"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L33"; TApp "tmp" [TAtom "v37"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v39"]; TAtom "L29"; TAtom "L30"]];
        TApp "block" [TAtom "L29"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v41"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.1"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "pr.1"]]]];
          TApp "goto" [TApp "poll" [TAtom "L27"]]];
        TApp "block" [TAtom "L30"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v44"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v44"]]];
            TApp "let" [TApp "tmp" [TAtom "v45"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk3"]]];
            TApp "let" [TApp "tmp" [TAtom "v46"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.1"]]];
            TApp "let" [TApp "tmp" [TAtom "v47"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v45"]]];
            TApp "let" [TApp "tmp" [TAtom "v48"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "v46"]; TApp "tmp" [TAtom "v47"]]]];
          TApp "goto" [TAtom "L50"]];
        TApp "block" [TAtom "L50"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.9"]; TAtom "w"; TList [TApp "-" [TAtom "L30"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L52"; TApp "tmp" [TAtom "v84"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.2"]; TAtom "p"; TList [TApp "-" [TAtom "L30"; TApp "tmp" [TAtom "v6"]]; TApp "-" [TAtom "L52"; TApp "tmp" [TAtom "v82"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk4"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "pr.2"]]];
            TApp "let" [TApp "tmp" [TAtom "v55"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk4"]]];
            TApp "let" [TApp "tmp" [TAtom "v56"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v55"]]];
            TApp "let" [TApp "tmp" [TAtom "v57"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v56"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v57"]; TAtom "L51"; TAtom "L53"]];
        TApp "block" [TAtom "L51"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v62"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk4"]]];
            TApp "flight" [TApp "tmp" [TAtom "v64"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk6"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v64"]]];
            TApp "let" [TApp "tmp" [TAtom "v65"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk6"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v67"]; TAtom "w"]; TApp "global" [TAtom "__GI_strncmp"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v62"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v65"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v48"]]]];
            TApp "let" [TApp "tmp" [TAtom "v68"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v67"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v68"]; TAtom "L69"; TAtom "L70"]];
        TApp "block" [TAtom "L69"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk7"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk4"]; TApp "tmp" [TAtom "pr.2"]]];
            TApp "let" [TApp "tmp" [TAtom "v73"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk7"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v74"]; TAtom "l"]; TApp "global" [TAtom "__GI_strlen"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v73"]]]];
            TApp "let" [TApp "tmp" [TAtom "v75"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v48"]; TApp "tmp" [TAtom "v74"]]]];
          TApp "goto" [TAtom "L70"]];
        TApp "block" [TAtom "L70"; TList [TApp "phi" [TApp "tmp" [TAtom "v77"]; TAtom "w"; TList [TApp "-" [TAtom "L51"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L69"; TApp "tmp" [TAtom "v75"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v77"]; TAtom "L53"; TAtom "L52"]];
        TApp "block" [TAtom "L52"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v82"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.2"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "pr.2"]]];
            TApp "let" [TApp "tmp" [TAtom "v84"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "pr.9"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TApp "poll" [TAtom "L50"]]];
        TApp "block" [TAtom "L53"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.11"]; TAtom "w"; TList [TApp "-" [TAtom "L50"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L70"; TApp "tmp" [TAtom "pr.9"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.6"]; TAtom "p"; TList [TApp "-" [TAtom "L50"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L70"; TApp "tmp" [TAtom "pr.2"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v89"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.6"]]];
            TApp "let" [TApp "tmp" [TAtom "v90"]; TAtom "l"; TAtom "ptoi"; TList [TApp "const" [TInt 0]]];
            TApp "let" [TApp "tmp" [TAtom "v91"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v89"]; TApp "tmp" [TAtom "v90"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v91"]; TAtom "L98"; TAtom "L87"]];
        TApp "block" [TAtom "L98"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.42"]; TAtom "w"; TList [TApp "-" [TAtom "L108"; TApp "tmp" [TAtom "pr.40"]]; TApp "-" [TAtom "L53"; TApp "const" [TInt 4294967295]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.39"]; TAtom "w"; TList [TApp "-" [TAtom "L108"; TApp "tmp" [TAtom "pr.31"]]; TApp "-" [TAtom "L53"; TApp "const" [TInt 0]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.30"]; TAtom "w"; TList [TApp "-" [TAtom "L108"; TApp "tmp" [TAtom "pr.22"]]; TApp "-" [TAtom "L53"; TApp "const" [TInt 0]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.21"]; TAtom "p"; TList [TApp "-" [TAtom "L108"; TApp "tmp" [TAtom "pr.14"]]; TApp "-" [TAtom "L53"; TApp "const" [TInt 0]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.13"]; TAtom "w"; TList [TApp "-" [TAtom "L108"; TApp "tmp" [TAtom "v227"]]; TApp "-" [TAtom "L53"; TApp "const" [TInt 0]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.8"]; TAtom "p"; TList [TApp "-" [TAtom "L108"; TApp "tmp" [TAtom "pr.4"]]; TApp "-" [TAtom "L53"; TApp "tmp" [TAtom "pr.6"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.3"]; TAtom "p"; TList [TApp "-" [TAtom "L108"; TApp "tmp" [TAtom "v225"]]; TApp "-" [TAtom "L53"; TApp "tmp" [TAtom "v6"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk8"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "pr.3"]]];
            TApp "let" [TApp "tmp" [TAtom "v103"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk8"]]];
            TApp "let" [TApp "tmp" [TAtom "v104"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v103"]]];
            TApp "let" [TApp "tmp" [TAtom "v105"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v104"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v105"]; TAtom "L99"; TAtom "L101"]];
        TApp "block" [TAtom "L99"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v110"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk8"]]];
            TApp "flight" [TApp "tmp" [TAtom "v112"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk10"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v112"]]];
            TApp "let" [TApp "tmp" [TAtom "v113"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk10"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v115"]; TAtom "w"]; TApp "global" [TAtom "__GI_strncmp"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v110"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v113"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v48"]]]];
            TApp "let" [TApp "tmp" [TAtom "v116"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v115"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v116"]; TAtom "L106"; TAtom "L108"]];
        TApp "block" [TAtom "L106"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v121"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.8"]]];
            TApp "let" [TApp "tmp" [TAtom "v123"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v121"]; TApp "tmp" [TAtom "v90"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v123"]; TAtom "L108"; TAtom "L118"]];
        TApp "block" [TAtom "L118"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v10"]; TAtom "L131"; TAtom "L130"]];
        TApp "block" [TAtom "L130"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v133"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.8"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "pr.8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk11"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v133"]]];
            TApp "let" [TApp "tmp" [TAtom "v134"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk11"]]];
            TApp "flight" [TApp "tmp" [TAtom "v136"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.3"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "pr.3"]]];
            TApp "let" [TApp "tmp" [TAtom "chk12"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk8"]; TApp "tmp" [TAtom "v136"]]];
            TApp "let" [TApp "tmp" [TAtom "v137"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk12"]]];
            TApp "let" [TApp "tmp" [TAtom "v138"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v134"]; TApp "tmp" [TAtom "v137"]]]];
          TApp "goto" [TAtom "L131"]];
        TApp "block" [TAtom "L131"; TList [TApp "phi" [TApp "tmp" [TAtom "v140"]; TAtom "w"; TList [TApp "-" [TAtom "L118"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L130"; TApp "tmp" [TAtom "v138"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v140"]; TAtom "L142"; TAtom "L141"]];
        TApp "block" [TAtom "L141"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v144"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.8"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "pr.8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk13"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v144"]]];
            TApp "let" [TApp "tmp" [TAtom "v145"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk13"]]];
            TApp "flight" [TApp "tmp" [TAtom "v147"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.3"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "pr.3"]]];
            TApp "let" [TApp "tmp" [TAtom "chk14"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk8"]; TApp "tmp" [TAtom "v147"]]];
            TApp "let" [TApp "tmp" [TAtom "v148"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk14"]]];
            TApp "let" [TApp "tmp" [TAtom "v149"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v145"]]];
            TApp "let" [TApp "tmp" [TAtom "v150"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v148"]]];
            TApp "let" [TApp "tmp" [TAtom "v151"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v149"]; TApp "tmp" [TAtom "v150"]]]];
          TApp "goto" [TAtom "L142"]];
        TApp "block" [TAtom "L142"; TList [TApp "phi" [TApp "tmp" [TAtom "v153"]; TAtom "w"; TList [TApp "-" [TAtom "L131"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L141"; TApp "tmp" [TAtom "v151"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v153"]; TAtom "L155"; TAtom "L154"]];
        TApp "block" [TAtom "L154"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v157"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.8"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "pr.8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk15"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v157"]]];
            TApp "let" [TApp "tmp" [TAtom "v158"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk15"]]];
            TApp "flight" [TApp "tmp" [TAtom "v160"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.3"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "pr.3"]]];
            TApp "let" [TApp "tmp" [TAtom "chk16"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk8"]; TApp "tmp" [TAtom "v160"]]];
            TApp "let" [TApp "tmp" [TAtom "v161"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk16"]]];
            TApp "let" [TApp "tmp" [TAtom "v162"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v158"]; TApp "tmp" [TAtom "v161"]]]];
          TApp "goto" [TAtom "L155"]];
        TApp "block" [TAtom "L155"; TList [TApp "phi" [TApp "tmp" [TAtom "v164"]; TAtom "w"; TList [TApp "-" [TAtom "L142"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L154"; TApp "tmp" [TAtom "v162"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v164"]; TAtom "L126"; TAtom "L108"]];
        TApp "block" [TAtom "L126"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v169"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.39"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v169"]; TAtom "L165"; TAtom "L108"]];
        TApp "block" [TAtom "L165"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v174"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v14"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v174"]; TAtom "L172"; TAtom "L171"]];
        TApp "block" [TAtom "L171"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v179"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.21"]]];
            TApp "let" [TApp "tmp" [TAtom "v181"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v179"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v181"]; TAtom "L175"; TAtom "L172"]];
        TApp "block" [TAtom "L175"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v186"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "pr.9"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "iw_1.v3"]; TAtom "w"]; TApp "global" [TAtom "__GI___libc_alloca_cutoff"]; TList [TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v186"]]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v4"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "iw_1.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "iw_1.v4"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "iw_1.L7"; TAtom "iw_1.L6"]];
        TApp "block" [TAtom "iw_1.L6"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_1.v11"]; TAtom "w"; TApp "cmp" [TAtom "ule"; TAtom "l"]; TList [TApp "tmp" [TAtom "v186"]; TApp "const" [TInt 4096]]]];
          TApp "goto" [TAtom "iw_1.L7"]];
        TApp "block" [TAtom "iw_1.L7"; TList [TApp "phi" [TApp "tmp" [TAtom "iw_1.v15"]; TAtom "w"; TList [TApp "-" [TAtom "L175"; TApp "const" [TInt 1]]; TApp "-" [TAtom "iw_1.L6"; TApp "tmp" [TAtom "iw_1.v11"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "iw_1.v15"]; TAtom "L182"; TAtom "L183"]];
        TApp "block" [TAtom "L182"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v190"]; TAtom "p"; TApp "alloc" [TInt 16]; TList [TApp "tmp" [TAtom "v186"]]]];
          TApp "goto" [TAtom "L184"]];
        TApp "block" [TAtom "L183"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v196"]; TAtom "p"]; TApp "global" [TAtom "malloc"]; TList [TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v186"]]]];
            TApp "let" [TApp "tmp" [TAtom "v197"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v196"]]];
            TApp "let" [TApp "tmp" [TAtom "v199"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v197"]; TApp "tmp" [TAtom "v90"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v199"]; TAtom "L184"; TAtom "L192"]];
        TApp "block" [TAtom "L192"; TList [];
          TList [];
          TApp "goto" [TAtom "L184"]];
        TApp "block" [TAtom "L184"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.37"]; TAtom "w"; TList [TApp "-" [TAtom "L182"; TApp "tmp" [TAtom "pr.39"]]; TApp "-" [TAtom "L192"; TApp "tmp" [TAtom "pr.39"]]; TApp "-" [TAtom "L183"; TApp "const" [TInt 1]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.28"]; TAtom "w"; TList [TApp "-" [TAtom "L182"; TApp "tmp" [TAtom "pr.30"]]; TApp "-" [TAtom "L192"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L183"; TApp "tmp" [TAtom "pr.30"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.20"]; TAtom "p"; TList [TApp "-" [TAtom "L182"; TApp "tmp" [TAtom "v190"]]; TApp "-" [TAtom "L192"; TApp "tmp" [TAtom "v196"]]; TApp "-" [TAtom "L183"; TApp "tmp" [TAtom "v196"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v204"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.20"]]];
            TApp "let" [TApp "tmp" [TAtom "v205"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v204"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v205"]; TAtom "L200"; TAtom "L172"]];
        TApp "block" [TAtom "L200"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v209"]; TAtom "p"]; TApp "global" [TAtom "__GI_memset"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.20"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 0]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v186"]]]];
            TApp "let" [TApp "tmp" [TAtom "v212"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "pr.42"]]];
            TApp "flight" [TApp "tmp" [TAtom "v213"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.20"]]; TApp "tmp" [TAtom "v212"]]; TApp "lower" [TApp "tmp" [TAtom "pr.20"]]];
            TApp "let" [TApp "tmp" [TAtom "chk17"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v213"]]];
            TApp "raw_store" [TAtom "b"; TInt 0; TApp "const" [TInt 1]; TApp "tmp" [TAtom "chk17"]]];
          TApp "goto" [TAtom "L172"]];
        TApp "block" [TAtom "L172"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.35"]; TAtom "w"; TList [TApp "-" [TAtom "L165"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L200"; TApp "tmp" [TAtom "pr.37"]]; TApp "-" [TAtom "L184"; TApp "tmp" [TAtom "pr.37"]]; TApp "-" [TAtom "L171"; TApp "tmp" [TAtom "pr.39"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.26"]; TAtom "w"; TList [TApp "-" [TAtom "L165"; TApp "tmp" [TAtom "pr.30"]]; TApp "-" [TAtom "L200"; TApp "tmp" [TAtom "pr.28"]]; TApp "-" [TAtom "L184"; TApp "tmp" [TAtom "pr.28"]]; TApp "-" [TAtom "L171"; TApp "tmp" [TAtom "pr.30"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.18"]; TAtom "p"; TList [TApp "-" [TAtom "L165"; TApp "tmp" [TAtom "pr.21"]]; TApp "-" [TAtom "L200"; TApp "tmp" [TAtom "pr.20"]]; TApp "-" [TAtom "L184"; TApp "tmp" [TAtom "pr.20"]]; TApp "-" [TAtom "L171"; TApp "tmp" [TAtom "pr.21"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v218"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.18"]]];
            TApp "let" [TApp "tmp" [TAtom "v219"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v218"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v219"]; TAtom "L214"; TAtom "L108"]];
        TApp "block" [TAtom "L214"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v222"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "pr.13"]]];
            TApp "flight" [TApp "tmp" [TAtom "v223"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.18"]]; TApp "tmp" [TAtom "v222"]]; TApp "lower" [TApp "tmp" [TAtom "pr.18"]]];
            TApp "let" [TApp "tmp" [TAtom "chk18"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v223"]]];
            TApp "raw_store" [TAtom "b"; TInt 0; TApp "const" [TInt 1]; TApp "tmp" [TAtom "chk18"]]];
          TApp "goto" [TAtom "L108"]];
        TApp "block" [TAtom "L108"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.40"]; TAtom "w"; TList [TApp "-" [TAtom "L106"; TApp "tmp" [TAtom "pr.13"]]; TApp "-" [TAtom "L214"; TApp "tmp" [TAtom "pr.42"]]; TApp "-" [TAtom "L172"; TApp "tmp" [TAtom "pr.42"]]; TApp "-" [TAtom "L126"; TApp "tmp" [TAtom "pr.42"]]; TApp "-" [TAtom "L155"; TApp "tmp" [TAtom "pr.42"]]; TApp "-" [TAtom "L99"; TApp "tmp" [TAtom "pr.42"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.31"]; TAtom "w"; TList [TApp "-" [TAtom "L106"; TApp "tmp" [TAtom "pr.39"]]; TApp "-" [TAtom "L214"; TApp "tmp" [TAtom "pr.35"]]; TApp "-" [TAtom "L172"; TApp "tmp" [TAtom "pr.35"]]; TApp "-" [TAtom "L126"; TApp "tmp" [TAtom "pr.39"]]; TApp "-" [TAtom "L155"; TApp "tmp" [TAtom "pr.39"]]; TApp "-" [TAtom "L99"; TApp "tmp" [TAtom "pr.39"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.22"]; TAtom "w"; TList [TApp "-" [TAtom "L106"; TApp "tmp" [TAtom "pr.30"]]; TApp "-" [TAtom "L214"; TApp "tmp" [TAtom "pr.26"]]; TApp "-" [TAtom "L172"; TApp "tmp" [TAtom "pr.26"]]; TApp "-" [TAtom "L126"; TApp "tmp" [TAtom "pr.30"]]; TApp "-" [TAtom "L155"; TApp "tmp" [TAtom "pr.30"]]; TApp "-" [TAtom "L99"; TApp "tmp" [TAtom "pr.30"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.14"]; TAtom "p"; TList [TApp "-" [TAtom "L106"; TApp "tmp" [TAtom "pr.21"]]; TApp "-" [TAtom "L214"; TApp "tmp" [TAtom "pr.18"]]; TApp "-" [TAtom "L172"; TApp "tmp" [TAtom "pr.18"]]; TApp "-" [TAtom "L126"; TApp "tmp" [TAtom "pr.21"]]; TApp "-" [TAtom "L155"; TApp "tmp" [TAtom "pr.21"]]; TApp "-" [TAtom "L99"; TApp "tmp" [TAtom "pr.21"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.4"]; TAtom "p"; TList [TApp "-" [TAtom "L106"; TApp "tmp" [TAtom "pr.3"]]; TApp "-" [TAtom "L214"; TApp "tmp" [TAtom "pr.8"]]; TApp "-" [TAtom "L172"; TApp "tmp" [TAtom "pr.8"]]; TApp "-" [TAtom "L126"; TApp "tmp" [TAtom "pr.8"]]; TApp "-" [TAtom "L155"; TApp "tmp" [TAtom "pr.8"]]; TApp "-" [TAtom "L99"; TApp "tmp" [TAtom "pr.8"]]]]];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v225"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.3"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "pr.3"]]];
            TApp "let" [TApp "tmp" [TAtom "v227"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "pr.13"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TApp "poll" [TAtom "L98"]]];
        TApp "block" [TAtom "L101"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v232"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.21"]]];
            TApp "let" [TApp "tmp" [TAtom "v233"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v232"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v233"]; TAtom "L235"; TAtom "L234"]];
        TApp "block" [TAtom "L234"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v237"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.39"]; TApp "const" [TInt 0]]]];
          TApp "goto" [TAtom "L235"]];
        TApp "block" [TAtom "L235"; TList [TApp "phi" [TApp "tmp" [TAtom "v238"]; TAtom "w"; TList [TApp "-" [TAtom "L101"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L234"; TApp "tmp" [TAtom "v237"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v238"]; TAtom "L228"; TAtom "L87"]];
        TApp "block" [TAtom "L228"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v14"]; TAtom "L239"; TAtom "L241"]];
        TApp "block" [TAtom "L239"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.39"]; TAtom "L243"; TAtom "L244"]];
        TApp "block" [TAtom "L243"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v247"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk19"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v247"]]];
            TApp "let" [TApp "tmp" [TAtom "v248"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk19"]]];
            TApp "let" [TApp "tmp" [TAtom "v249"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__GI__libc_intl_domainname"]]];
            TApp "let" [TApp "tmp" [TAtom "v250"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.138"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v251"]; TAtom "p"]; TApp "global" [TAtom "__GI___dcgettext"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v249"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v250"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 5]]]];
            TApp "let" [TApp "tmp" [TAtom "chk20"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v254"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk20"]]];
            TApp "flight" [TApp "tmp" [TAtom "v257"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk21"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v257"]]];
            TApp "let" [TApp "tmp" [TAtom "v258"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk21"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v259"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v248"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v251"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v254"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v16"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v258"]]]]];
          TApp "goto" [TAtom "L241"]];
        TApp "block" [TAtom "L244"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v260"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk22"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v260"]]];
            TApp "let" [TApp "tmp" [TAtom "v261"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk22"]]];
            TApp "let" [TApp "tmp" [TAtom "v262"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__GI__libc_intl_domainname"]]];
            TApp "let" [TApp "tmp" [TAtom "v263"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.139"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v264"]; TAtom "p"]; TApp "global" [TAtom "__GI___dcgettext"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v262"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v263"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 5]]]];
            TApp "let" [TApp "tmp" [TAtom "chk23"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v267"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk23"]]];
            TApp "flight" [TApp "tmp" [TAtom "v270"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk24"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v270"]]];
            TApp "let" [TApp "tmp" [TAtom "v271"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk24"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v272"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v261"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v264"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v267"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v16"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v271"]]]]];
          TApp "goto" [TAtom "L273"]];
        TApp "block" [TAtom "L273"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.10"]; TAtom "w"; TList [TApp "-" [TAtom "L244"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L275"; TApp "tmp" [TAtom "v300"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v279"]; TAtom "w"; TApp "cmp" [TAtom "slt"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.10"]; TApp "tmp" [TAtom "pr.9"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v279"]; TAtom "L274"; TAtom "L276"]];
        TApp "block" [TAtom "L274"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v285"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "pr.10"]]];
            TApp "flight" [TApp "tmp" [TAtom "v286"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.21"]]; TApp "tmp" [TAtom "v285"]]; TApp "lower" [TApp "tmp" [TAtom "pr.21"]]];
            TApp "let" [TApp "tmp" [TAtom "chk25"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v286"]]];
            TApp "let" [TApp "tmp" [TAtom "v287"]; TAtom "w"; TApp "raw_load" [TAtom "ub"; TInt 0]; TList [TApp "tmp" [TAtom "chk25"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v287"]; TAtom "L280"; TAtom "L275"]];
        TApp "block" [TAtom "L280"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v288"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk26"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v288"]]];
            TApp "let" [TApp "tmp" [TAtom "v289"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk26"]]];
            TApp "let" [TApp "tmp" [TAtom "v290"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.140"]]];
            TApp "let" [TApp "tmp" [TAtom "v295"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v285"]; TApp "const" [TInt 5]]];
            TApp "flight" [TApp "tmp" [TAtom "v296"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v6"]]; TApp "tmp" [TAtom "v295"]]; TApp "lower" [TApp "tmp" [TAtom "v6"]]];
            TApp "let" [TApp "tmp" [TAtom "chk27"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v296"]]];
            TApp "let" [TApp "tmp" [TAtom "v297"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk27"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v298"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v289"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v290"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v16"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v297"]]]]];
          TApp "goto" [TAtom "L275"]];
        TApp "block" [TAtom "L275"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v300"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "pr.10"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TApp "poll" [TAtom "L273"]]];
        TApp "block" [TAtom "L276"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v301"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk28"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v301"]]];
            TApp "let" [TApp "tmp" [TAtom "v302"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk28"]]];
            TApp "let" [TApp "tmp" [TAtom "v303"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.141"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v304"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v302"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v303"]]]]];
          TApp "goto" [TAtom "L241"]];
        TApp "block" [TAtom "L241"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.30"]; TAtom "L305"; TAtom "L307"]];
        TApp "block" [TAtom "L305"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "free"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.21"]]]]];
          TApp "goto" [TAtom "L307"]];
        TApp "block" [TAtom "L307"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v311"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk29"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v311"]]];
            TApp "let" [TApp "tmp" [TAtom "v312"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk29"]]];
            TApp "let" [TApp "tmp" [TAtom "v315"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk29"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v316"]; TAtom "l"]; TApp "global" [TAtom "__GI_strlen"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v315"]]]];
            TApp "flight" [TApp "tmp" [TAtom "v317"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v312"]]; TApp "tmp" [TAtom "v316"]]; TApp "lower" [TApp "tmp" [TAtom "v312"]]];
            TApp "let" [TApp "tmp" [TAtom "chk31"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v311"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v317"]; TApp "tmp" [TAtom "chk31"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk32"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v319"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk32"]]];
            TApp "let" [TApp "tmp" [TAtom "v320"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v319"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk33"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk32"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v320"]; TApp "tmp" [TAtom "chk33"]];
            TApp "flight" [TApp "tmp" [TAtom "v322"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk34"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v322"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk34"]]];
          TApp "ret" [TApp "const" [TInt 63]]];
        TApp "block" [TAtom "L87"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.12"]; TAtom "w"; TList [TApp "-" [TAtom "L235"; TApp "tmp" [TAtom "pr.42"]]; TApp "-" [TAtom "L53"; TApp "tmp" [TAtom "pr.11"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.7"]; TAtom "p"; TList [TApp "-" [TAtom "L235"; TApp "tmp" [TAtom "pr.8"]]; TApp "-" [TAtom "L53"; TApp "tmp" [TAtom "pr.6"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v329"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "v331"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v329"]; TApp "tmp" [TAtom "v90"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v331"]; TAtom "L325"; TAtom "L327"]];
        TApp "block" [TAtom "L325"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v336"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v10"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v336"]; TAtom "L338"; TAtom "L337"]];
        TApp "block" [TAtom "L337"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk35"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v341"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk35"]]];
            TApp "let" [TApp "tmp" [TAtom "v342"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v341"]]];
            TApp "let" [TApp "tmp" [TAtom "v343"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v342"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v344"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v343"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk36"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v344"]]];
            TApp "let" [TApp "tmp" [TAtom "v345"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk36"]]];
            TApp "flight" [TApp "tmp" [TAtom "v346"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v345"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v345"]]];
            TApp "let" [TApp "tmp" [TAtom "chk37"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v346"]]];
            TApp "let" [TApp "tmp" [TAtom "v347"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk37"]]];
            TApp "let" [TApp "tmp" [TAtom "v348"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v347"]; TApp "const" [TInt 45]]]];
          TApp "goto" [TAtom "L338"]];
        TApp "block" [TAtom "L338"; TList [TApp "phi" [TApp "tmp" [TAtom "v350"]; TAtom "w"; TList [TApp "-" [TAtom "L325"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L337"; TApp "tmp" [TAtom "v348"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v350"]; TAtom "L352"; TAtom "L351"]];
        TApp "block" [TAtom "L351"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v355"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk38"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v355"]]];
            TApp "let" [TApp "tmp" [TAtom "v356"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk38"]]];
            TApp "let" [TApp "tmp" [TAtom "chk39"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v356"]]];
            TApp "let" [TApp "tmp" [TAtom "v357"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk39"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v358"]; TAtom "p"]; TApp "global" [TAtom "__GI_strchr"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v4"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v357"]]]];
            TApp "let" [TApp "tmp" [TAtom "v359"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v358"]]];
            TApp "let" [TApp "tmp" [TAtom "v361"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v359"]; TApp "tmp" [TAtom "v90"]]]];
          TApp "goto" [TAtom "L352"]];
        TApp "block" [TAtom "L352"; TList [TApp "phi" [TApp "tmp" [TAtom "v363"]; TAtom "w"; TList [TApp "-" [TAtom "L338"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L351"; TApp "tmp" [TAtom "v361"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v363"]; TAtom "L332"; TAtom "L334"]];
        TApp "block" [TAtom "L332"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v14"]; TAtom "L364"; TAtom "L366"]];
        TApp "block" [TAtom "L364"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v368"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk40"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v368"]]];
            TApp "let" [TApp "tmp" [TAtom "v369"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk40"]]];
            TApp "let" [TApp "tmp" [TAtom "v370"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__GI__libc_intl_domainname"]]];
            TApp "let" [TApp "tmp" [TAtom "v371"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.142"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v372"]; TAtom "p"]; TApp "global" [TAtom "__GI___dcgettext"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v370"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v371"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 5]]]];
            TApp "let" [TApp "tmp" [TAtom "chk41"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v375"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk41"]]];
            TApp "flight" [TApp "tmp" [TAtom "v378"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk42"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v378"]]];
            TApp "let" [TApp "tmp" [TAtom "v379"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk42"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v380"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v369"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v372"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v375"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v16"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v379"]]]]];
          TApp "goto" [TAtom "L366"]];
        TApp "block" [TAtom "L366"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v382"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk43"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v382"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk43"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk44"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v384"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk44"]]];
            TApp "let" [TApp "tmp" [TAtom "v385"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v384"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk45"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk44"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v385"]; TApp "tmp" [TAtom "chk45"]];
            TApp "flight" [TApp "tmp" [TAtom "v387"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk46"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v387"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk46"]]];
          TApp "ret" [TApp "const" [TInt 63]]];
        TApp "block" [TAtom "L334"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L327"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk47"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v392"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk47"]]];
            TApp "let" [TApp "tmp" [TAtom "v393"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v392"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk48"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk47"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v393"]; TApp "tmp" [TAtom "chk48"]];
            TApp "flight" [TApp "tmp" [TAtom "v395"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk49"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v395"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk49"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk50"]; TAtom "a"; TApp "renew" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "pr.1"]]];
            TApp "let" [TApp "tmp" [TAtom "v400"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk50"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v400"]; TAtom "L396"; TAtom "L397"]];
        TApp "block" [TAtom "L396"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v405"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "chk51"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v405"]]];
            TApp "let" [TApp "tmp" [TAtom "v406"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk51"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v406"]; TAtom "L401"; TAtom "L402"]];
        TApp "block" [TAtom "L401"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v408"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "flight" [TApp "tmp" [TAtom "v410"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.1"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "pr.1"]]];
            TApp "let" [TApp "tmp" [TAtom "chk52"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v408"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v410"]; TApp "tmp" [TAtom "chk52"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L398"]];
        TApp "block" [TAtom "L402"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v14"]; TAtom "L411"; TAtom "L413"]];
        TApp "block" [TAtom "L411"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v415"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk53"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v415"]]];
            TApp "let" [TApp "tmp" [TAtom "v416"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk53"]]];
            TApp "let" [TApp "tmp" [TAtom "v417"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__GI__libc_intl_domainname"]]];
            TApp "let" [TApp "tmp" [TAtom "v418"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.143"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v419"]; TAtom "p"]; TApp "global" [TAtom "__GI___dcgettext"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v417"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v418"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 5]]]];
            TApp "let" [TApp "tmp" [TAtom "chk54"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v422"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk54"]]];
            TApp "let" [TApp "tmp" [TAtom "chk55"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk51"]; TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "v425"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk55"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v426"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v416"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v419"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v422"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v16"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v425"]]]]];
          TApp "goto" [TAtom "L413"]];
        TApp "block" [TAtom "L413"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v428"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "flight" [TApp "tmp" [TAtom "v430"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "chk56"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk51"]; TApp "tmp" [TAtom "v430"]]];
            TApp "let" [TApp "tmp" [TAtom "v431"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk56"]]];
            TApp "let" [TApp "tmp" [TAtom "chk57"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v428"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v431"]; TApp "tmp" [TAtom "chk57"]]];
          TApp "ret" [TApp "const" [TInt 63]]];
        TApp "block" [TAtom "L397"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v436"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "chk58"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v436"]]];
            TApp "let" [TApp "tmp" [TAtom "v437"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk58"]]];
            TApp "let" [TApp "tmp" [TAtom "v438"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v437"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v438"]; TAtom "L432"; TAtom "L398"]];
        TApp "block" [TAtom "L432"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk59"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk47"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v443"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk59"]]];
            TApp "let" [TApp "tmp" [TAtom "v445"]; TAtom "w"; TApp "cmp" [TAtom "slt"; TAtom "w"]; TList [TApp "tmp" [TAtom "v443"]; TApp "tmp" [TAtom "v0"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v445"]; TAtom "L439"; TAtom "L440"]];
        TApp "block" [TAtom "L439"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v447"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v450"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk59"]]];
            TApp "let" [TApp "tmp" [TAtom "v451"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v450"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk61"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk47"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v451"]; TApp "tmp" [TAtom "chk61"]];
            TApp "let" [TApp "tmp" [TAtom "v452"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v450"]]];
            TApp "let" [TApp "tmp" [TAtom "v453"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v452"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v454"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v453"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk62"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v454"]]];
            TApp "let" [TApp "tmp" [TAtom "v455"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk62"]]];
            TApp "let" [TApp "tmp" [TAtom "chk63"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v447"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v455"]; TApp "tmp" [TAtom "chk63"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L398"]];
        TApp "block" [TAtom "L440"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v14"]; TAtom "L456"; TAtom "L458"]];
        TApp "block" [TAtom "L456"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v460"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk64"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v460"]]];
            TApp "let" [TApp "tmp" [TAtom "v461"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk64"]]];
            TApp "let" [TApp "tmp" [TAtom "v462"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__GI__libc_intl_domainname"]]];
            TApp "let" [TApp "tmp" [TAtom "v463"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.144"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v464"]; TAtom "p"]; TApp "global" [TAtom "__GI___dcgettext"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v462"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v463"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 5]]]];
            TApp "let" [TApp "tmp" [TAtom "chk65"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v467"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk65"]]];
            TApp "let" [TApp "tmp" [TAtom "chk66"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk58"]; TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "v470"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk66"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v471"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v461"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v464"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v467"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v16"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v470"]]]]];
          TApp "goto" [TAtom "L458"]];
        TApp "block" [TAtom "L458"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v473"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "flight" [TApp "tmp" [TAtom "v475"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "chk67"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk58"]; TApp "tmp" [TAtom "v475"]]];
            TApp "let" [TApp "tmp" [TAtom "v476"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk67"]]];
            TApp "let" [TApp "tmp" [TAtom "chk68"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v473"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v476"]; TApp "tmp" [TAtom "chk68"]];
            TApp "let" [TApp "tmp" [TAtom "chk69"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v4"]]];
            TApp "let" [TApp "tmp" [TAtom "v482"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk69"]]];
            TApp "let" [TApp "tmp" [TAtom "v483"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v482"]; TApp "const" [TInt 58]]]];
          TApp "branch" [TApp "tmp" [TAtom "v483"]; TAtom "L479"; TAtom "L478"]];
        TApp "block" [TAtom "L478"; TList [];
          TList [];
          TApp "goto" [TAtom "L479"]]
  ].
