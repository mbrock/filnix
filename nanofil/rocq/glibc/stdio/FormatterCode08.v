(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition formatter_blocks_08 : list term :=
  [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v24"]; TAtom "p"; TApp "alloc" [TInt 16]; TList [TApp "const" [TInt 1040]]];
            TApp "let" [TApp "tmp" [TAtom "v31"]; TAtom "p"; TApp "alloc" [TInt 16]; TList [TApp "const" [TInt 1040]]];
            TApp "let" [TApp "tmp" [TAtom "v34"]; TAtom "p"; TApp "alloc" [TInt 8]; TList [TApp "const" [TInt 8]]];
            TApp "let" [TApp "tmp" [TAtom "v107"]; TAtom "p"; TApp "alloc" [TInt 4]; TList [TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "v1248"]; TAtom "p"; TApp "alloc" [TInt 8]; TList [TApp "const" [TInt 24]]];
            TApp "let" [TApp "tmp" [TAtom "v1887"]; TAtom "p"; TApp "alloc" [TInt 4]; TList [TApp "const" [TInt 16]]];
            TApp "let" [TApp "tmp" [TAtom "v1888"]; TAtom "p"; TApp "alloc" [TInt 4]; TList [TApp "const" [TInt 8]]];
            TApp "let" [TApp "tmp" [TAtom "v1936"]; TAtom "p"; TApp "alloc" [TInt 8]; TList [TApp "const" [TInt 8]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#scratch_buffer_init"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v24"]]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v24"]]];
            TApp "let" [TApp "tmp" [TAtom "v26"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v28"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v24"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v24"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v28"]]];
            TApp "let" [TApp "tmp" [TAtom "v29"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt 0]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "let" [TApp "tmp" [TAtom "v30"]; TAtom "l"; TAtom "udiv"; TList [TApp "tmp" [TAtom "v29"]; TApp "const" [TInt 72]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#scratch_buffer_init"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v31"]]]];
            TApp "let" [TApp "tmp" [TAtom "chk2"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v34"]]];
            TApp "raw_store" [TAtom "l"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk2"]];
            TApp "flight" [TApp "tmp" [TAtom "v42"]; TAtom "copy"; TList [TApp "const" [TInt 18446744073709551615]]; TAtom "none"];
            TApp "let" [TApp "tmp" [TAtom "v43"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v18"]]];
            TApp "let" [TApp "tmp" [TAtom "v44"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v42"]]];
            TApp "let" [TApp "tmp" [TAtom "v45"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v43"]; TApp "tmp" [TAtom "v44"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v45"]; TAtom "L36"; TAtom "L38"]];
        TApp "block" [TAtom "L36"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v46"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_tsd_LOCALE"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v46"]]];
            TApp "let" [TApp "tmp" [TAtom "v47"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk3"]]];
            TApp "flight" [TApp "tmp" [TAtom "v48"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v47"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v47"]]];
            TApp "let" [TApp "tmp" [TAtom "chk4"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v48"]]];
            TApp "let" [TApp "tmp" [TAtom "v49"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk4"]]];
            TApp "flight" [TApp "tmp" [TAtom "v50"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v49"]]; TApp "const" [TInt 56]]; TApp "lower" [TApp "tmp" [TAtom "v49"]]];
            TApp "flight" [TApp "tmp" [TAtom "v54"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v50"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v50"]]];
            TApp "let" [TApp "tmp" [TAtom "chk5"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v54"]]];
            TApp "let" [TApp "tmp" [TAtom "v55"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk5"]]];
            TApp "let" [TApp "tmp" [TAtom "v56"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_tsd_LOCALE"]]];
            TApp "let" [TApp "tmp" [TAtom "chk6"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v56"]]];
            TApp "let" [TApp "tmp" [TAtom "v57"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk6"]]];
            TApp "flight" [TApp "tmp" [TAtom "v58"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v57"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v57"]]];
            TApp "let" [TApp "tmp" [TAtom "chk7"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v58"]]];
            TApp "let" [TApp "tmp" [TAtom "v59"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk7"]]];
            TApp "flight" [TApp "tmp" [TAtom "v60"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v59"]]; TApp "const" [TInt 56]]; TApp "lower" [TApp "tmp" [TAtom "v59"]]];
            TApp "flight" [TApp "tmp" [TAtom "v64"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v60"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v60"]]];
            TApp "let" [TApp "tmp" [TAtom "chk8"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v64"]]];
            TApp "let" [TApp "tmp" [TAtom "v65"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk9"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v65"]]];
            TApp "let" [TApp "tmp" [TAtom "v70"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk9"]]];
            TApp "let" [TApp "tmp" [TAtom "v71"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v70"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v71"]; TAtom "L73"; TAtom "L72"]];
        TApp "block" [TAtom "L72"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v75"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk9"]]];
            TApp "let" [TApp "tmp" [TAtom "v76"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v75"]; TApp "const" [TInt 127]]]];
          TApp "goto" [TAtom "L73"]];
        TApp "block" [TAtom "L73"; TList [TApp "phi" [TApp "tmp" [TAtom "v78"]; TAtom "w"; TList [TApp "-" [TAtom "L36"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L72"; TApp "tmp" [TAtom "v76"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v78"]; TAtom "L38"; TAtom "L67"]];
        TApp "block" [TAtom "L67"; TList [];
          TList [];
          TApp "goto" [TAtom "L38"]];
        TApp "block" [TAtom "L38"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.6"]; TAtom "p"; TList [TApp "-" [TAtom "L67"; TApp "tmp" [TAtom "v55"]]; TApp "-" [TAtom "L73"; TApp "tmp" [TAtom "v55"]]; TApp "-" [TAtom "start"; TApp "tmp" [TAtom "v20"]]]]];
          TList [];
          TApp "goto" [TAtom "L81"]];
        TApp "block" [TAtom "L81"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.15"]; TAtom "p"; TList [TApp "-" [TAtom "L38"; TApp "tmp" [TAtom "v12"]]; TApp "-" [TAtom "L83"; TApp "tmp" [TAtom "v129"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.12"]; TAtom "l"; TList [TApp "-" [TAtom "L38"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L83"; TApp "tmp" [TAtom "v116"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.11"]; TAtom "l"; TList [TApp "-" [TAtom "L38"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L83"; TApp "tmp" [TAtom "v125"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.9"]; TAtom "l"; TList [TApp "-" [TAtom "L38"; TApp "tmp" [TAtom "v30"]]; TApp "-" [TAtom "L83"; TApp "tmp" [TAtom "pr.10"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.7"]; TAtom "p"; TList [TApp "-" [TAtom "L38"; TApp "tmp" [TAtom "v26"]]; TApp "-" [TAtom "L83"; TApp "tmp" [TAtom "pr.8"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk11"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "pr.15"]]];
            TApp "let" [TApp "tmp" [TAtom "v86"]; TAtom "w"; TApp "raw_load" [TAtom "ub"; TInt 0]; TList [TApp "tmp" [TAtom "chk11"]]];
            TApp "let" [TApp "tmp" [TAtom "v87"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v86"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v87"]; TAtom "L82"; TAtom "L84"]];
        TApp "block" [TAtom "L82"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v93"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "pr.11"]; TApp "tmp" [TAtom "pr.9"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v93"]; TAtom "iw_1.start"; TAtom "L90"]];
        TApp "block" [TAtom "iw_1.start"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "iw_1.v3"]; TAtom "w"]; TApp "global" [TAtom "__GI___libc_scratch_buffer_grow_preserve"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v24"]]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v4"]; TAtom "w"; TApp "ext" [TAtom "ub"]; TList [TApp "tmp" [TAtom "iw_1.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "l"; TApp "ext" [TAtom "uw"]; TList [TApp "tmp" [TAtom "iw_1.v4"]]];
            TApp "let" [TApp "tmp" [TAtom "v99"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "iw_1.v5"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v99"]; TAtom "L94"; TAtom "L96"]];
        TApp "block" [TAtom "L94"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_mark_failed"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "L101"]];
        TApp "block" [TAtom "L96"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk12"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v24"]]];
            TApp "let" [TApp "tmp" [TAtom "v103"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk12"]]];
            TApp "flight" [TApp "tmp" [TAtom "v104"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v24"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v24"]]];
            TApp "let" [TApp "tmp" [TAtom "chk13"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v104"]]];
            TApp "let" [TApp "tmp" [TAtom "v105"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt 0]; TList [TApp "tmp" [TAtom "chk13"]]];
            TApp "let" [TApp "tmp" [TAtom "v106"]; TAtom "l"; TAtom "udiv"; TList [TApp "tmp" [TAtom "v105"]; TApp "const" [TInt 72]]]];
          TApp "goto" [TAtom "L90"]];
        TApp "block" [TAtom "L90"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.10"]; TAtom "l"; TList [TApp "-" [TAtom "L96"; TApp "tmp" [TAtom "v106"]]; TApp "-" [TAtom "L82"; TApp "tmp" [TAtom "pr.9"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.8"]; TAtom "p"; TList [TApp "-" [TAtom "L96"; TApp "tmp" [TAtom "v103"]]; TApp "-" [TAtom "L82"; TApp "tmp" [TAtom "pr.7"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v113"]; TAtom "l"; TAtom "mul"; TList [TApp "tmp" [TAtom "pr.11"]; TApp "const" [TInt 72]]];
            TApp "flight" [TApp "tmp" [TAtom "v114"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.8"]]; TApp "tmp" [TAtom "v113"]]; TApp "lower" [TApp "tmp" [TAtom "pr.8"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v115"]; TAtom "l"]; TApp "global" [TAtom "__parse_one_specmb"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.15"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "pr.12"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v114"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v34"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v107"]]]];
            TApp "let" [TApp "tmp" [TAtom "v116"]; TAtom "l"; TAtom "add"; TList [TApp "tmp" [TAtom "pr.12"]; TApp "tmp" [TAtom "v115"]]];
            TApp "let" [TApp "tmp" [TAtom "chk14"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v107"]]];
            TApp "let" [TApp "tmp" [TAtom "v120"]; TAtom "w"; TApp "raw_load" [TAtom "ub"; TInt 0]; TList [TApp "tmp" [TAtom "chk14"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v120"]; TAtom "L117"; TAtom "L83"]];
        TApp "block" [TAtom "L117"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_mark_failed"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "L101"]];
        TApp "block" [TAtom "L83"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v125"]; TAtom "l"; TAtom "add"; TList [TApp "tmp" [TAtom "pr.11"]; TApp "const" [TInt 1]]];
            TApp "flight" [TApp "tmp" [TAtom "v128"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v114"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v114"]]];
            TApp "let" [TApp "tmp" [TAtom "chk15"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v128"]]];
            TApp "let" [TApp "tmp" [TAtom "v129"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk15"]]]];
          TApp "goto" [TApp "poll" [TAtom "L81"]]];
        TApp "block" [TAtom "L84"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk16"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v34"]]];
            TApp "let" [TApp "tmp" [TAtom "v134"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt 0]; TList [TApp "tmp" [TAtom "chk16"]]];
            TApp "let" [TApp "tmp" [TAtom "v135"]; TAtom "w"; TApp "cmp" [TAtom "ugt"; TAtom "l"]; TList [TApp "tmp" [TAtom "pr.12"]; TApp "tmp" [TAtom "v134"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v135"]; TAtom "L132"; TAtom "L131"]];
        TApp "block" [TAtom "L131"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v137"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt 0]; TList [TApp "tmp" [TAtom "chk16"]]]];
          TApp "goto" [TAtom "L132"]];
        TApp "block" [TAtom "L132"; TList [TApp "phi" [TApp "tmp" [TAtom "v138"]; TAtom "l"; TList [TApp "-" [TAtom "L131"; TApp "tmp" [TAtom "v137"]]; TApp "-" [TAtom "L84"; TApp "tmp" [TAtom "pr.12"]]]]];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "iw_2.v9"]; TAtom "w"]; TApp "global" [TAtom "__GI___libc_scratch_buffer_set_array_size"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v31"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v138"]]; TApp "arg" [TAtom "l"; TApp "const" [TInt 24]]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v10"]; TAtom "w"; TApp "ext" [TAtom "ub"]; TList [TApp "tmp" [TAtom "iw_2.v9"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v11"]; TAtom "l"; TApp "ext" [TAtom "uw"]; TList [TApp "tmp" [TAtom "iw_2.v10"]]];
            TApp "let" [TApp "tmp" [TAtom "v154"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "iw_2.v11"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v154"]; TAtom "L147"; TAtom "L149"]];
        TApp "block" [TAtom "L147"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_mark_failed"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "L101"]];
        TApp "block" [TAtom "L149"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk18"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v31"]]];
            TApp "let" [TApp "tmp" [TAtom "v157"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk18"]]];
            TApp "let" [TApp "tmp" [TAtom "v160"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v138"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v161"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v157"]]; TApp "tmp" [TAtom "v160"]]; TApp "lower" [TApp "tmp" [TAtom "v157"]]];
            TApp "let" [TApp "tmp" [TAtom "v164"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v138"]; TApp "const" [TInt 2]]];
            TApp "flight" [TApp "tmp" [TAtom "v165"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v161"]]; TApp "tmp" [TAtom "v164"]]; TApp "lower" [TApp "tmp" [TAtom "v161"]]];
            TApp "flight" [TApp "tmp" [TAtom "v169"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v165"]]; TApp "tmp" [TAtom "v164"]]; TApp "lower" [TApp "tmp" [TAtom "v165"]]];
            TApp "let" [TApp "tmp" [TAtom "v175"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v22"]; TApp "const" [TInt 2]]];
            TApp "let" [TApp "tmp" [TAtom "v176"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v175"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v176"]; TAtom "L173"; TAtom "L172"]];
        TApp "block" [TAtom "L172"; TList [];
          TList [];
          TApp "goto" [TAtom "L173"]];
        TApp "block" [TAtom "L173"; TList [TApp "phi" [TApp "tmp" [TAtom "v177"]; TAtom "w"; TList [TApp "-" [TAtom "L172"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L149"; TApp "const" [TInt (-1)]]]]];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v180"]; TAtom "p"]; TApp "global" [TAtom "__GI_memset"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v165"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v177"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v164"]]]]];
          TApp "goto" [TAtom "L181"]];
        TApp "block" [TAtom "L181"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.13"]; TAtom "l"; TList [TApp "-" [TAtom "L173"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L183"; TApp "tmp" [TAtom "v322"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v187"]; TAtom "w"; TApp "cmp" [TAtom "ult"; TAtom "l"]; TList [TApp "tmp" [TAtom "pr.13"]; TApp "tmp" [TAtom "pr.11"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v187"]; TAtom "L182"; TAtom "L323"]];
        TApp "block" [TAtom "L182"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v193"]; TAtom "l"; TAtom "mul"; TList [TApp "tmp" [TAtom "pr.13"]; TApp "const" [TInt 72]]];
            TApp "flight" [TApp "tmp" [TAtom "v194"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "tmp" [TAtom "v193"]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "flight" [TApp "tmp" [TAtom "v195"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 44]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "chk19"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v195"]]];
            TApp "let" [TApp "tmp" [TAtom "v196"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk19"]]];
            TApp "let" [TApp "tmp" [TAtom "v198"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v196"]; TApp "const" [TInt 4294967295]]]];
          TApp "branch" [TApp "tmp" [TAtom "v198"]; TAtom "L188"; TAtom "L190"]];
        TApp "block" [TAtom "L188"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v204"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 44]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "v205"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk19"]]];
            TApp "let" [TApp "tmp" [TAtom "v206"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v205"]]];
            TApp "let" [TApp "tmp" [TAtom "v207"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v206"]; TApp "const" [TInt 2]]];
            TApp "flight" [TApp "tmp" [TAtom "v208"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v165"]]; TApp "tmp" [TAtom "v207"]]; TApp "lower" [TApp "tmp" [TAtom "v165"]]];
            TApp "let" [TApp "tmp" [TAtom "chk21"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v208"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk21"]]];
          TApp "goto" [TAtom "L190"]];
        TApp "block" [TAtom "L190"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v216"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "chk22"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "v216"]]];
            TApp "let" [TApp "tmp" [TAtom "v217"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk22"]]];
            TApp "let" [TApp "tmp" [TAtom "v219"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v217"]; TApp "const" [TInt 4294967295]]]];
          TApp "branch" [TApp "tmp" [TAtom "v219"]; TAtom "L209"; TAtom "L211"]];
        TApp "block" [TAtom "L209"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v225"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "v226"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk22"]]];
            TApp "let" [TApp "tmp" [TAtom "v227"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v226"]]];
            TApp "let" [TApp "tmp" [TAtom "v228"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v227"]; TApp "const" [TInt 2]]];
            TApp "flight" [TApp "tmp" [TAtom "v229"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v165"]]; TApp "tmp" [TAtom "v228"]]; TApp "lower" [TApp "tmp" [TAtom "v165"]]];
            TApp "let" [TApp "tmp" [TAtom "chk24"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v229"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk24"]]];
          TApp "goto" [TAtom "L211"]];
        TApp "block" [TAtom "L211"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v234"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 56]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "chk25"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "v234"]]];
            TApp "let" [TApp "tmp" [TAtom "v235"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt 0]; TList [TApp "tmp" [TAtom "chk25"]]];
            TApp "let" [TApp "tmp" [TAtom "v317"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v235"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v317"]; TAtom "L183"; TAtom "L318"]];
        TApp "block" [TAtom "L239"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v245"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "chk26"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "v245"]]];
            TApp "let" [TApp "tmp" [TAtom "v246"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk26"]]];
            TApp "let" [TApp "tmp" [TAtom "v247"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v246"]]];
            TApp "let" [TApp "tmp" [TAtom "v248"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v247"]; TApp "const" [TInt 2]]];
            TApp "flight" [TApp "tmp" [TAtom "v249"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v165"]]; TApp "tmp" [TAtom "v248"]]; TApp "lower" [TApp "tmp" [TAtom "v165"]]];
            TApp "flight" [TApp "tmp" [TAtom "v254"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 52]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "chk27"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "v254"]]];
            TApp "let" [TApp "tmp" [TAtom "v255"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk27"]]];
            TApp "let" [TApp "tmp" [TAtom "chk28"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v249"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v255"]; TApp "tmp" [TAtom "chk28"]];
            TApp "let" [TApp "tmp" [TAtom "v262"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk26"]]];
            TApp "let" [TApp "tmp" [TAtom "v263"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v262"]]];
            TApp "let" [TApp "tmp" [TAtom "v264"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v263"]; TApp "const" [TInt 2]]];
            TApp "flight" [TApp "tmp" [TAtom "v265"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v161"]]; TApp "tmp" [TAtom "v264"]]; TApp "lower" [TApp "tmp" [TAtom "v161"]]];
            TApp "flight" [TApp "tmp" [TAtom "v270"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 64]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "chk30"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "v270"]]];
            TApp "let" [TApp "tmp" [TAtom "v271"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk30"]]];
            TApp "let" [TApp "tmp" [TAtom "chk31"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v265"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v271"]; TApp "tmp" [TAtom "chk31"]]];
          TApp "goto" [TAtom "L183"]];
        TApp "block" [TAtom "L272"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v273"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__printf_arginfo_table"]]];
            TApp "let" [TApp "tmp" [TAtom "chk32"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v273"]]];
            TApp "let" [TApp "tmp" [TAtom "v274"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk32"]]];
            TApp "flight" [TApp "tmp" [TAtom "v279"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "chk33"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "v279"]]];
            TApp "let" [TApp "tmp" [TAtom "v280"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk33"]]];
            TApp "let" [TApp "tmp" [TAtom "v281"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v280"]]];
            TApp "let" [TApp "tmp" [TAtom "v282"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v281"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v283"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v274"]]; TApp "tmp" [TAtom "v282"]]; TApp "lower" [TApp "tmp" [TAtom "v274"]]];
            TApp "let" [TApp "tmp" [TAtom "chk34"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v283"]]];
            TApp "let" [TApp "tmp" [TAtom "v284"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk34"]]];
            TApp "flight" [TApp "tmp" [TAtom "v293"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 56]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "chk35"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk25"]; TApp "tmp" [TAtom "v293"]]];
            TApp "let" [TApp "tmp" [TAtom "v294"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt 0]; TList [TApp "tmp" [TAtom "chk35"]]];
            TApp "flight" [TApp "tmp" [TAtom "v300"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v194"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v194"]]];
            TApp "let" [TApp "tmp" [TAtom "v301"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt (-8)]; TList [TApp "tmp" [TAtom "chk35"]]];
            TApp "let" [TApp "tmp" [TAtom "v302"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v301"]]];
            TApp "let" [TApp "tmp" [TAtom "v303"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v302"]; TApp "const" [TInt 2]]];
            TApp "flight" [TApp "tmp" [TAtom "v304"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v165"]]; TApp "tmp" [TAtom "v303"]]; TApp "lower" [TApp "tmp" [TAtom "v165"]]];
            TApp "let" [TApp "tmp" [TAtom "v311"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt (-8)]; TList [TApp "tmp" [TAtom "chk35"]]];
            TApp "let" [TApp "tmp" [TAtom "v312"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v311"]]];
            TApp "let" [TApp "tmp" [TAtom "v313"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v312"]; TApp "const" [TInt 2]]];
            TApp "flight" [TApp "tmp" [TAtom "v314"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v161"]]; TApp "tmp" [TAtom "v313"]]; TApp "lower" [TApp "tmp" [TAtom "v161"]]];
            TApp "let" [TApp "tmp" [TAtom "chk38"]; TAtom "f"; TAtom "check_function"; TList [TApp "tmp" [TAtom "v284"]]];
            TApp "raw_call" [TApp "result" [TApp "tmp" [TAtom "v315"]; TAtom "w"]; TApp "tmp" [TAtom "chk38"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v194"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v294"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v304"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v314"]]]]];
          TApp "goto" [TAtom "L183"]];
        TApp "block" [TAtom "L318"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v319"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v235"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v319"]; TApp "poll" [TAtom "L239"]; TApp "poll" [TAtom "L272"]]];
        TApp "block" [TAtom "L183"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v322"]; TAtom "l"; TAtom "add"; TList [TApp "tmp" [TAtom "pr.13"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TApp "poll" [TAtom "L181"]]];
        TApp "block" [TAtom "L323"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.31"]; TAtom "p"; TList [TApp "-" [TAtom "L336"; TApp "tmp" [TAtom "pr.32"]]; TApp "-" [TAtom "L181"; TApp "tmp" [TAtom "v169"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.26"]; TAtom "p"; TList [TApp "-" [TAtom "L336"; TApp "tmp" [TAtom "pr.27"]]; TApp "-" [TAtom "L181"; TApp "tmp" [TAtom "v165"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.21"]; TAtom "p"; TList [TApp "-" [TAtom "L336"; TApp "tmp" [TAtom "pr.22"]]; TApp "-" [TAtom "L181"; TApp "tmp" [TAtom "v161"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.16"]; TAtom "p"; TList [TApp "-" [TAtom "L336"; TApp "tmp" [TAtom "pr.17"]]; TApp "-" [TAtom "L181"; TApp "tmp" [TAtom "v157"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.14"]; TAtom "l"; TList [TApp "-" [TAtom "L336"; TApp "tmp" [TAtom "v586"]]; TApp "-" [TAtom "L181"; TApp "const" [TInt 0]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v329"]; TAtom "w"; TApp "cmp" [TAtom "ult"; TAtom "l"]; TList [TApp "tmp" [TAtom "pr.14"]; TApp "tmp" [TAtom "v138"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v329"]; TAtom "L324"; TAtom "L587"]];
        TApp "block" [TAtom "L324"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v332"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 2]]];
            TApp "flight" [TApp "tmp" [TAtom "v333"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.26"]]; TApp "tmp" [TAtom "v332"]]; TApp "lower" [TApp "tmp" [TAtom "pr.26"]]];
            TApp "let" [TApp "tmp" [TAtom "chk39"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v333"]]];
            TApp "let" [TApp "tmp" [TAtom "v334"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk39"]]];
            TApp "let" [TApp "tmp" [TAtom "v550"]; TAtom "w"; TApp "cmp" [TAtom "slt"; TAtom "w"]; TList [TApp "tmp" [TAtom "v334"]; TApp "const" [TInt 5]]]];
          TApp "branch" [TApp "tmp" [TAtom "v550"]; TAtom "L551"; TAtom "L552"]];
        TApp "block" [TAtom "L337"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v340"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v341"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v340"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "let" [TApp "tmp" [TAtom "v343"]; TAtom "w"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk40"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v341"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v343"]; TApp "tmp" [TAtom "chk40"]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L346"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v349"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v350"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v349"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "let" [TApp "tmp" [TAtom "v352"]; TAtom "w"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk41"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v350"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v352"]; TApp "tmp" [TAtom "chk41"]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L354"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v357"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v358"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v357"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "let" [TApp "tmp" [TAtom "v360"]; TAtom "l"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk42"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v358"]]];
            TApp "raw_store" [TAtom "l"; TInt 0; TApp "tmp" [TAtom "v360"]; TApp "tmp" [TAtom "chk42"]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L362"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v365"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v366"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v365"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "let" [TApp "tmp" [TAtom "v368"]; TAtom "d"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk43"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v366"]]];
            TApp "raw_store" [TAtom "d"; TInt 0; TApp "tmp" [TAtom "v368"]; TApp "tmp" [TAtom "chk43"]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L369"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v374"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v22"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v374"]; TAtom "L370"; TAtom "L371"]];
        TApp "block" [TAtom "L370"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v380"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v381"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v380"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "let" [TApp "tmp" [TAtom "v383"]; TAtom "d"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk44"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v381"]]];
            TApp "raw_store" [TAtom "d"; TInt 0; TApp "tmp" [TAtom "v383"]; TApp "tmp" [TAtom "chk44"]];
            TApp "let" [TApp "tmp" [TAtom "chk45"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk39"]; TApp "tmp" [TAtom "v333"]]];
            TApp "let" [TApp "tmp" [TAtom "v388"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk45"]]];
            TApp "let" [TApp "tmp" [TAtom "v391"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v388"]; TApp "const" [TInt 4294967039]]];
            TApp "let" [TApp "tmp" [TAtom "chk46"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk39"]; TApp "tmp" [TAtom "v333"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v391"]; TApp "tmp" [TAtom "chk46"]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L371"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v394"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v395"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v394"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "let" [TApp "tmp" [TAtom "v397"]; TAtom "x"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk47"]; TAtom "a"; TApp "check" [TInt 0; TInt 10; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v395"]]];
            TApp "raw_store" [TAtom "x"; TInt 0; TApp "tmp" [TAtom "v397"]; TApp "tmp" [TAtom "chk47"]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L400"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v403"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v404"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v403"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "let" [TApp "tmp" [TAtom "v406"]; TAtom "p"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk48"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v404"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v406"]; TApp "tmp" [TAtom "chk48"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L407"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk49"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk39"]; TApp "tmp" [TAtom "v333"]]];
            TApp "let" [TApp "tmp" [TAtom "v415"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk49"]]];
            TApp "let" [TApp "tmp" [TAtom "v417"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v415"]; TApp "const" [TInt 2048]]];
            TApp "let" [TApp "tmp" [TAtom "v418"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v417"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v418"]; TAtom "L408"; TAtom "L409"]];
        TApp "block" [TAtom "L408"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v421"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v422"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v421"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "let" [TApp "tmp" [TAtom "v424"]; TAtom "p"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk50"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v422"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v424"]; TApp "tmp" [TAtom "chk50"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L409"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v428"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__printf_va_arg_table"]]];
            TApp "let" [TApp "tmp" [TAtom "chk51"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v428"]]];
            TApp "let" [TApp "tmp" [TAtom "v429"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk51"]]];
            TApp "let" [TApp "tmp" [TAtom "v430"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v429"]]];
            TApp "let" [TApp "tmp" [TAtom "v431"]; TAtom "l"; TAtom "ptoi"; TList [TApp "const" [TInt 0]]];
            TApp "let" [TApp "tmp" [TAtom "v432"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v430"]; TApp "tmp" [TAtom "v431"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v432"]; TAtom "L435"; TAtom "L436"]];
        TApp "block" [TAtom "L435"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v437"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__printf_va_arg_table"]]];
            TApp "let" [TApp "tmp" [TAtom "chk52"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v437"]]];
            TApp "let" [TApp "tmp" [TAtom "v438"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk52"]]];
            TApp "let" [TApp "tmp" [TAtom "chk53"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk39"]; TApp "tmp" [TAtom "v333"]]];
            TApp "let" [TApp "tmp" [TAtom "v443"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk53"]]];
            TApp "let" [TApp "tmp" [TAtom "v444"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "v443"]; TApp "const" [TInt 8]]];
            TApp "let" [TApp "tmp" [TAtom "v445"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v444"]]];
            TApp "let" [TApp "tmp" [TAtom "v446"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v445"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v447"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v438"]]; TApp "tmp" [TAtom "v446"]]; TApp "lower" [TApp "tmp" [TAtom "v438"]]];
            TApp "let" [TApp "tmp" [TAtom "chk54"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v447"]]];
            TApp "let" [TApp "tmp" [TAtom "v448"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk54"]]];
            TApp "let" [TApp "tmp" [TAtom "v449"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v448"]]];
            TApp "let" [TApp "tmp" [TAtom "v451"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v449"]; TApp "tmp" [TAtom "v431"]]]];
          TApp "goto" [TAtom "L436"]];
        TApp "block" [TAtom "L436"; TList [TApp "phi" [TApp "tmp" [TAtom "v453"]; TAtom "w"; TList [TApp "-" [TAtom "L409"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L435"; TApp "tmp" [TAtom "v451"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v453"]; TAtom "L454"; TAtom "L426"]];
        TApp "block" [TAtom "L454"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.35"]; TAtom "p"; TList [TApp "-" [TAtom "L482"; TApp "tmp" [TAtom "v502"]]; TApp "-" [TAtom "L436"; TApp "tmp" [TAtom "pr.31"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.30"]; TAtom "p"; TList [TApp "-" [TAtom "L482"; TApp "tmp" [TAtom "v496"]]; TApp "-" [TAtom "L436"; TApp "tmp" [TAtom "pr.26"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.25"]; TAtom "p"; TList [TApp "-" [TAtom "L482"; TApp "tmp" [TAtom "v492"]]; TApp "-" [TAtom "L436"; TApp "tmp" [TAtom "pr.21"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.20"]; TAtom "p"; TList [TApp "-" [TAtom "L482"; TApp "tmp" [TAtom "v488"]]; TApp "-" [TAtom "L436"; TApp "tmp" [TAtom "pr.16"]]]]];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v461"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.25"]]; TApp "tmp" [TAtom "v332"]]; TApp "lower" [TApp "tmp" [TAtom "pr.25"]]];
            TApp "let" [TApp "tmp" [TAtom "chk55"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v461"]]];
            TApp "let" [TApp "tmp" [TAtom "v462"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk55"]]];
            TApp "let" [TApp "tmp" [TAtom "v463"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v462"]]];
            TApp "flight" [TApp "tmp" [TAtom "v464"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.35"]]; TApp "tmp" [TAtom "v463"]]; TApp "lower" [TApp "tmp" [TAtom "pr.35"]]];
            TApp "let" [TApp "tmp" [TAtom "chk56"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk18"]; TApp "tmp" [TAtom "v31"]]];
            TApp "let" [TApp "tmp" [TAtom "v465"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk56"]]];
            TApp "flight" [TApp "tmp" [TAtom "v466"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v31"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v31"]]];
            TApp "let" [TApp "tmp" [TAtom "chk57"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk18"]; TApp "tmp" [TAtom "v466"]]];
            TApp "let" [TApp "tmp" [TAtom "v467"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt 0]; TList [TApp "tmp" [TAtom "chk57"]]];
            TApp "flight" [TApp "tmp" [TAtom "v468"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v465"]]; TApp "tmp" [TAtom "v467"]]; TApp "lower" [TApp "tmp" [TAtom "v465"]]];
            TApp "let" [TApp "tmp" [TAtom "v469"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v464"]]];
            TApp "let" [TApp "tmp" [TAtom "v470"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v468"]]];
            TApp "let" [TApp "tmp" [TAtom "v471"]; TAtom "w"; TApp "cmp" [TAtom "ugt"; TAtom "l"]; TList [TApp "tmp" [TAtom "v469"]; TApp "tmp" [TAtom "v470"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v471"]; TAtom "L455"; TAtom "L456"]];
        TApp "block" [TAtom "L455"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v476"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.30"]]; TApp "tmp" [TAtom "v164"]]; TApp "lower" [TApp "tmp" [TAtom "pr.30"]]];
            TApp "let" [TApp "tmp" [TAtom "v477"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.35"]]];
            TApp "let" [TApp "tmp" [TAtom "v478"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v476"]]];
            TApp "let" [TApp "tmp" [TAtom "v479"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "v477"]; TApp "tmp" [TAtom "v478"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "iw_3.v3"]; TAtom "w"]; TApp "global" [TAtom "__GI___libc_scratch_buffer_grow_preserve"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v31"]]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v4"]; TAtom "w"; TApp "ext" [TAtom "ub"]; TList [TApp "tmp" [TAtom "iw_3.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v5"]; TAtom "l"; TApp "ext" [TAtom "uw"]; TList [TApp "tmp" [TAtom "iw_3.v4"]]];
            TApp "let" [TApp "tmp" [TAtom "v485"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "iw_3.v5"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v485"]; TAtom "L480"; TAtom "L482"]];
        TApp "block" [TAtom "L480"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_mark_failed"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "L101"]];
        TApp "block" [TAtom "L482"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk58"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk18"]; TApp "tmp" [TAtom "v31"]]];
            TApp "let" [TApp "tmp" [TAtom "v488"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk58"]]];
            TApp "flight" [TApp "tmp" [TAtom "v492"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v488"]]; TApp "tmp" [TAtom "v160"]]; TApp "lower" [TApp "tmp" [TAtom "v488"]]];
            TApp "flight" [TApp "tmp" [TAtom "v496"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v492"]]; TApp "tmp" [TAtom "v164"]]; TApp "lower" [TApp "tmp" [TAtom "v492"]]];
            TApp "flight" [TApp "tmp" [TAtom "v500"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v496"]]; TApp "tmp" [TAtom "v164"]]; TApp "lower" [TApp "tmp" [TAtom "v496"]]];
            TApp "flight" [TApp "tmp" [TAtom "v502"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v500"]]; TApp "tmp" [TAtom "v479"]]; TApp "lower" [TApp "tmp" [TAtom "v500"]]]];
          TApp "goto" [TApp "poll" [TAtom "L454"]]];
        TApp "block" [TAtom "L456"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v505"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v506"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.20"]]; TApp "tmp" [TAtom "v505"]]; TApp "lower" [TApp "tmp" [TAtom "pr.20"]]];
            TApp "let" [TApp "tmp" [TAtom "chk59"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v506"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "pr.35"]; TApp "tmp" [TAtom "chk59"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk60"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk55"]; TApp "tmp" [TAtom "v461"]]];
            TApp "let" [TApp "tmp" [TAtom "v513"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk60"]]];
            TApp "let" [TApp "tmp" [TAtom "v514"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v513"]]];
            TApp "flight" [TApp "tmp" [TAtom "v515"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.35"]]; TApp "tmp" [TAtom "v514"]]; TApp "lower" [TApp "tmp" [TAtom "pr.35"]]];
            TApp "let" [TApp "tmp" [TAtom "v516"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__printf_va_arg_table"]]];
            TApp "let" [TApp "tmp" [TAtom "chk61"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v516"]]];
            TApp "let" [TApp "tmp" [TAtom "v517"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk61"]]];
            TApp "flight" [TApp "tmp" [TAtom "v521"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.30"]]; TApp "tmp" [TAtom "v332"]]; TApp "lower" [TApp "tmp" [TAtom "pr.30"]]];
            TApp "let" [TApp "tmp" [TAtom "chk62"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v521"]]];
            TApp "let" [TApp "tmp" [TAtom "v522"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk62"]]];
            TApp "let" [TApp "tmp" [TAtom "v523"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "v522"]; TApp "const" [TInt 8]]];
            TApp "let" [TApp "tmp" [TAtom "v524"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v523"]]];
            TApp "let" [TApp "tmp" [TAtom "v525"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v524"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v526"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v517"]]; TApp "tmp" [TAtom "v525"]]; TApp "lower" [TApp "tmp" [TAtom "v517"]]];
            TApp "let" [TApp "tmp" [TAtom "chk63"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v526"]]];
            TApp "let" [TApp "tmp" [TAtom "v527"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk63"]]];
            TApp "let" [TApp "tmp" [TAtom "chk64"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk59"]; TApp "tmp" [TAtom "v506"]]];
            TApp "let" [TApp "tmp" [TAtom "v532"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk64"]]];
            TApp "let" [TApp "tmp" [TAtom "chk65"]; TAtom "f"; TAtom "check_function"; TList [TApp "tmp" [TAtom "v527"]]];
            TApp "raw_call" [TAtom "void"; TApp "tmp" [TAtom "chk65"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v532"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v8"]]]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L426"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v536"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 4]]];
            TApp "flight" [TApp "tmp" [TAtom "v537"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.16"]]; TApp "tmp" [TAtom "v536"]]; TApp "lower" [TApp "tmp" [TAtom "pr.16"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v538"]; TAtom "p"]; TApp "global" [TAtom "__GI_memset"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v537"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 0]]; TApp "arg" [TAtom "l"; TApp "const" [TInt 16]]]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L539"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v176"]; TAtom "L542"; TAtom "L541"]];
        TApp "block" [TAtom "L541"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v546"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#str.290"]]];
            TApp "let" [TApp "tmp" [TAtom "v547"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#str.291"]]];
            TApp "let" [TApp "tmp" [TAtom "v548"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#str.292"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__libc_assert_fail"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v546"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v547"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 1270]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v548"]]]]];
          TApp "goto" [TAtom "L542"]];
        TApp "block" [TAtom "L542"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v549"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#str.293"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___libc_fatal"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v549"]]]]];
          TApp "goto" [TAtom "L336"]];
        TApp "block" [TAtom "L551"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v553"]; TAtom "w"; TApp "cmp" [TAtom "slt"; TAtom "w"]; TList [TApp "tmp" [TAtom "v334"]; TApp "const" [TInt 2]]]];
          TApp "branch" [TApp "tmp" [TAtom "v553"]; TAtom "L554"; TAtom "L555"]];
        TApp "block" [TAtom "L554"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v556"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v334"]; TApp "const" [TInt (-1)]]]];
          TApp "branch" [TApp "tmp" [TAtom "v556"]; TApp "poll" [TAtom "L539"]; TAtom "L557"]];
        TApp "block" [TAtom "L557"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v558"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v334"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v558"]; TApp "poll" [TAtom "L346"]; TAtom "L559"]];
        TApp "block" [TAtom "L559"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v560"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v334"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v560"]; TApp "poll" [TAtom "L346"]; TApp "poll" [TAtom "L407"]]];
        TApp "block" [TAtom "L555"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v562"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v334"]; TApp "const" [TInt 2]]]];
          TApp "branch" [TApp "tmp" [TAtom "v562"]; TApp "poll" [TAtom "L337"]; TAtom "L563"]];
        TApp "block" [TAtom "L563"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v564"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v334"]; TApp "const" [TInt 3]]]];
          TApp "branch" [TApp "tmp" [TAtom "v564"]; TApp "poll" [TAtom "L400"]; TAtom "L565"]];
        TApp "block" [TAtom "L565"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v566"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v334"]; TApp "const" [TInt 4]]]];
          TApp "branch" [TApp "tmp" [TAtom "v566"]; TApp "poll" [TAtom "L400"]; TApp "poll" [TAtom "L407"]]]
  ].
