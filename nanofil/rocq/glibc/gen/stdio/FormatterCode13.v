(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These items retain their order in the linked module. *)
Definition formatter_items_13 : list term :=
  [
    TApp "func" [TAtom "__vfprintf_internal"; TAtom "export"; TAtom "w"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v4"]]; TApp "param" [TAtom "w"; TApp "tmp" [TAtom "v6"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v178"]; TAtom "p"; TApp "alloc" [TInt 8]; TList [TApp "const" [TInt 176]]];
            TApp "let" [TApp "tmp" [TAtom "v187"]; TAtom "p"; TApp "alloc" [TInt 8]; TList [TApp "const" [TInt 32]]];
            TApp "let" [TApp "tmp" [TAtom "v290"]; TAtom "p"; TApp "alloc" [TInt 8]; TList [TApp "const" [TInt 176]]];
            TApp "flight" [TApp "tmp" [TAtom "v30"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 192]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v30"]]];
            TApp "let" [TApp "tmp" [TAtom "v31"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v32"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v31"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v32"]; TAtom "L26"; TAtom "L28"]];
        TApp "block" [TAtom "L26"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v34"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 192]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v34"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 4294967295]; TApp "tmp" [TAtom "chk1"]]];
          TApp "goto" [TAtom "L28"]];
        TApp "block" [TAtom "L28"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v37"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 192]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v38"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v61"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v38"]; TApp "const" [TInt 4294967295]]]];
          TApp "branch" [TApp "tmp" [TAtom "v61"]; TAtom "L8"; TAtom "L71"]];
        TApp "block" [TAtom "L8"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L71"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v76"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk3"]]];
            TApp "let" [TApp "tmp" [TAtom "v77"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v76"]; TApp "const" [TInt 8]]]];
          TApp "branch" [TApp "tmp" [TAtom "v77"]; TAtom "L72"; TAtom "L74"]];
        TApp "block" [TAtom "L72"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v79"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk3"]]];
            TApp "let" [TApp "tmp" [TAtom "v80"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v79"]; TApp "const" [TInt 32]]];
            TApp "let" [TApp "tmp" [TAtom "chk5"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk3"]; TApp "tmp" [TAtom "v0"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v80"]; TApp "tmp" [TAtom "chk5"]];
            TApp "let" [TApp "tmp" [TAtom "v81"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_errno"]]];
            TApp "let" [TApp "tmp" [TAtom "chk6"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v81"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 9]; TApp "tmp" [TAtom "chk6"]]];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L74"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v88"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v89"]; TAtom "l"; TAtom "ptoi"; TList [TApp "const" [TInt 0]]];
            TApp "let" [TApp "tmp" [TAtom "v90"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v88"]; TApp "tmp" [TAtom "v89"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v90"]; TAtom "L84"; TAtom "L107"]];
        TApp "block" [TAtom "L84"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v91"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_errno"]]];
            TApp "let" [TApp "tmp" [TAtom "chk7"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v91"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 22]; TApp "tmp" [TAtom "chk7"]]];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L107"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v121"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 192]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v122"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v123"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v122"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v123"]; TAtom "L117"; TAtom "L119"]];
        TApp "block" [TAtom "L117"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v125"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 192]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk9"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v125"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 4294967295]; TApp "tmp" [TAtom "chk9"]]];
          TApp "goto" [TAtom "L119"]];
        TApp "block" [TAtom "L119"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v128"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 192]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v129"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v162"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v129"]; TApp "const" [TInt 4294967295]]]];
          TApp "branch" [TApp "tmp" [TAtom "v162"]; TAtom "L94"; TAtom "L96"]];
        TApp "block" [TAtom "L94"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L96"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v171"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 116]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v172"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt (-76)]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v173"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "v172"]; TApp "const" [TInt 8]]];
            TApp "let" [TApp "tmp" [TAtom "v174"]; TAtom "w"; TAtom "sar"; TList [TApp "tmp" [TAtom "v173"]; TApp "const" [TInt 8]]];
            TApp "let" [TApp "tmp" [TAtom "v175"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v174"]; TApp "const" [TInt 128]]];
            TApp "let" [TApp "tmp" [TAtom "v177"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v175"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v177"]; TAtom "L167"; TAtom "L169"]];
        TApp "block" [TAtom "L167"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_to_file_init"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v178"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v178"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v4"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v6"]]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v183"]; TAtom "w"]; TApp "global" [TAtom "__printf_buffer_to_file_done"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v178"]]]]];
          TApp "ret" [TApp "tmp" [TAtom "v183"]]];
        TApp "block" [TAtom "L169"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v189"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "_IO_funlockfile"]]];
            TApp "flight" [TApp "tmp" [TAtom "v190"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v187"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v187"]]];
            TApp "let" [TApp "tmp" [TAtom "chk12"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v190"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v0"]; TApp "tmp" [TAtom "chk12"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk13"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk3"]; TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v196"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk13"]]];
            TApp "let" [TApp "tmp" [TAtom "v197"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v196"]; TApp "const" [TInt 32768]]];
            TApp "let" [TApp "tmp" [TAtom "v198"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v197"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v198"]; TAtom "L192"; TAtom "L194"]];
        TApp "block" [TAtom "L192"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk14"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk12"]; TApp "tmp" [TAtom "v187"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v189"]; TApp "tmp" [TAtom "chk14"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___libc_cleanup_push_defer"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v187"]]]]];
          TApp "goto" [TAtom "L194"]];
        TApp "block" [TAtom "L194"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.5"]; TAtom "w"; TList [TApp "-" [TAtom "L192"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L169"; TApp "const" [TInt 0]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk15"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk3"]; TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v206"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk15"]]];
            TApp "let" [TApp "tmp" [TAtom "v207"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v206"]; TApp "const" [TInt 32768]]];
            TApp "let" [TApp "tmp" [TAtom "v208"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v207"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v208"]; TAtom "L209"; TAtom "L204"]];
        TApp "block" [TAtom "L209"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v213"]; TAtom "p"]; TApp "global" [TAtom "zthread_self_cookie"]; TList []];
            TApp "let" [TApp "tmp" [TAtom "v217"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_single_threaded_internal"]]];
            TApp "let" [TApp "tmp" [TAtom "chk16"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v217"]]];
            TApp "let" [TApp "tmp" [TAtom "v218"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk16"]]];
            TApp "let" [TApp "tmp" [TAtom "v219"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v218"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v219"]; TAtom "L220"; TAtom "L221"]];
        TApp "block" [TAtom "L220"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v223"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk17"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v223"]]];
            TApp "let" [TApp "tmp" [TAtom "v224"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk17"]]];
            TApp "flight" [TApp "tmp" [TAtom "v225"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v224"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v224"]]];
            TApp "let" [TApp "tmp" [TAtom "chk18"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v225"]]];
            TApp "let" [TApp "tmp" [TAtom "v226"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk18"]]];
            TApp "let" [TApp "tmp" [TAtom "v227"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v226"]]];
            TApp "let" [TApp "tmp" [TAtom "v229"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v227"]; TApp "tmp" [TAtom "v89"]]]];
          TApp "goto" [TAtom "L221"]];
        TApp "block" [TAtom "L221"; TList [TApp "phi" [TApp "tmp" [TAtom "v231"]; TAtom "w"; TList [TApp "-" [TAtom "L209"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L220"; TApp "tmp" [TAtom "v229"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v231"]; TAtom "L214"; TAtom "L215"]];
        TApp "block" [TAtom "L214"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v233"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk19"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v233"]]];
            TApp "let" [TApp "tmp" [TAtom "v234"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk19"]]];
            TApp "let" [TApp "tmp" [TAtom "chk20"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v234"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 1]; TApp "tmp" [TAtom "chk20"]];
            TApp "let" [TApp "tmp" [TAtom "v237"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk19"]]];
            TApp "flight" [TApp "tmp" [TAtom "v238"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v237"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v237"]]];
            TApp "let" [TApp "tmp" [TAtom "chk22"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v238"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v213"]; TApp "tmp" [TAtom "chk22"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L204"]];
        TApp "block" [TAtom "L215"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v244"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk23"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v244"]]];
            TApp "let" [TApp "tmp" [TAtom "v245"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk23"]]];
            TApp "flight" [TApp "tmp" [TAtom "v246"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v245"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v245"]]];
            TApp "let" [TApp "tmp" [TAtom "chk24"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v246"]]];
            TApp "let" [TApp "tmp" [TAtom "v247"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk24"]]];
            TApp "let" [TApp "tmp" [TAtom "v249"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v247"]]];
            TApp "let" [TApp "tmp" [TAtom "v250"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v213"]]];
            TApp "let" [TApp "tmp" [TAtom "v251"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v249"]; TApp "tmp" [TAtom "v250"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v251"]; TAtom "L240"; TAtom "L241"]];
        TApp "block" [TAtom "L240"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v254"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v255"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk23"]]];
            TApp "let" [TApp "tmp" [TAtom "chk26"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 4]; TList [TApp "tmp" [TAtom "v255"]]];
            TApp "let" [TApp "tmp" [TAtom "v262"]; TAtom "w"; TApp "raw_cas" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk26"]; TApp "const" [TInt 0]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "v263"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v262"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v263"]; TAtom "L265"; TAtom "L264"]];
        TApp "block" [TAtom "L264"; TList [];
          TList [];
          TApp "goto" [TAtom "L265"]];
        TApp "block" [TAtom "L265"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v266"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v262"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v266"]; TAtom "L269"; TAtom "L258"]];
        TApp "block" [TAtom "L269"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___lll_lock_wait_private"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v255"]]]]];
          TApp "goto" [TAtom "L258"]];
        TApp "block" [TAtom "L258"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v280"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk27"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk23"]; TApp "tmp" [TAtom "v280"]]];
            TApp "let" [TApp "tmp" [TAtom "v281"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk27"]]];
            TApp "flight" [TApp "tmp" [TAtom "v282"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v281"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v281"]]];
            TApp "let" [TApp "tmp" [TAtom "chk28"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v282"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v213"]; TApp "tmp" [TAtom "chk28"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L204"]];
        TApp "block" [TAtom "L241"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v285"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v286"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk23"]]];
            TApp "flight" [TApp "tmp" [TAtom "v287"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v286"]]; TApp "const" [TInt 4]]; TApp "lower" [TApp "tmp" [TAtom "v286"]]];
            TApp "let" [TApp "tmp" [TAtom "chk30"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v287"]]];
            TApp "let" [TApp "tmp" [TAtom "v288"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk30"]]];
            TApp "let" [TApp "tmp" [TAtom "v289"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v288"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk31"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk30"]; TApp "tmp" [TAtom "v287"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v289"]; TApp "tmp" [TAtom "chk31"]]];
          TApp "goto" [TAtom "L204"]];
        TApp "block" [TAtom "L204"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_to_file_init"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v290"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v290"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v4"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v6"]]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v295"]; TAtom "w"]; TApp "global" [TAtom "__printf_buffer_to_file_done"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v290"]]]];
            TApp "let" [TApp "tmp" [TAtom "chk32"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk3"]; TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v300"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk32"]]];
            TApp "let" [TApp "tmp" [TAtom "v301"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v300"]; TApp "const" [TInt 32768]]];
            TApp "let" [TApp "tmp" [TAtom "v302"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v301"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v302"]; TAtom "L303"; TAtom "L298"]];
        TApp "block" [TAtom "L303"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v309"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_single_threaded_internal"]]];
            TApp "let" [TApp "tmp" [TAtom "chk33"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v309"]]];
            TApp "let" [TApp "tmp" [TAtom "v310"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk33"]]];
            TApp "let" [TApp "tmp" [TAtom "v311"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v310"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v311"]; TAtom "L312"; TAtom "L313"]];
        TApp "block" [TAtom "L312"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v315"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk34"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v315"]]];
            TApp "let" [TApp "tmp" [TAtom "v316"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk34"]]];
            TApp "flight" [TApp "tmp" [TAtom "v317"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v316"]]; TApp "const" [TInt 4]]; TApp "lower" [TApp "tmp" [TAtom "v316"]]];
            TApp "let" [TApp "tmp" [TAtom "chk35"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v317"]]];
            TApp "let" [TApp "tmp" [TAtom "v318"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk35"]]];
            TApp "let" [TApp "tmp" [TAtom "v319"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v318"]; TApp "const" [TInt 0]]]];
          TApp "goto" [TAtom "L313"]];
        TApp "block" [TAtom "L313"; TList [TApp "phi" [TApp "tmp" [TAtom "v321"]; TAtom "w"; TList [TApp "-" [TAtom "L303"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L312"; TApp "tmp" [TAtom "v319"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v321"]; TAtom "L306"; TAtom "L307"]];
        TApp "block" [TAtom "L306"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v323"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk36"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v323"]]];
            TApp "let" [TApp "tmp" [TAtom "v324"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk36"]]];
            TApp "flight" [TApp "tmp" [TAtom "v325"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v324"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v324"]]];
            TApp "let" [TApp "tmp" [TAtom "chk37"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v325"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk37"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk38"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk36"]; TApp "tmp" [TAtom "v323"]]];
            TApp "let" [TApp "tmp" [TAtom "v328"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk38"]]];
            TApp "let" [TApp "tmp" [TAtom "chk39"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v328"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk39"]]];
          TApp "goto" [TAtom "L298"]];
        TApp "block" [TAtom "L307"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v333"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk40"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v333"]]];
            TApp "let" [TApp "tmp" [TAtom "v334"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk40"]]];
            TApp "flight" [TApp "tmp" [TAtom "v335"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v334"]]; TApp "const" [TInt 4]]; TApp "lower" [TApp "tmp" [TAtom "v334"]]];
            TApp "let" [TApp "tmp" [TAtom "chk41"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v335"]]];
            TApp "let" [TApp "tmp" [TAtom "v336"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk41"]]];
            TApp "let" [TApp "tmp" [TAtom "v337"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v336"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v337"]; TAtom "L329"; TAtom "L330"]];
        TApp "block" [TAtom "L329"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v339"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v340"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk40"]]];
            TApp "flight" [TApp "tmp" [TAtom "v341"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v340"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v340"]]];
            TApp "let" [TApp "tmp" [TAtom "chk43"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v341"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk43"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk44"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk40"]; TApp "tmp" [TAtom "v339"]]];
            TApp "let" [TApp "tmp" [TAtom "v345"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk44"]]];
            TApp "let" [TApp "tmp" [TAtom "chk45"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v345"]]];
            TApp "let" [TApp "tmp" [TAtom "v349"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk45"]]]];
          TApp "goto" [TAtom "L350"]];
        TApp "block" [TAtom "L350"; TList [TApp "phi" [TApp "tmp" [TAtom "v352"]; TAtom "w"; TList [TApp "-" [TAtom "L329"; TApp "tmp" [TAtom "v349"]]; TApp "-" [TAtom "L350"; TApp "tmp" [TAtom "v353"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk46"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "write"; TInt 4]; TList [TApp "tmp" [TAtom "chk45"]; TApp "tmp" [TAtom "v345"]]];
            TApp "let" [TApp "tmp" [TAtom "v353"]; TAtom "w"; TApp "raw_cas" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk46"]; TApp "tmp" [TAtom "v352"]; TApp "const" [TInt 0]]];
            TApp "let" [TApp "tmp" [TAtom "v354"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v353"]; TApp "tmp" [TAtom "v352"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v354"]; TAtom "L351"; TApp "poll" [TAtom "L350"]]];
        TApp "block" [TAtom "L351"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v359"]; TAtom "w"; TApp "cmp" [TAtom "sgt"; TAtom "w"]; TList [TApp "tmp" [TAtom "v352"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v359"]; TAtom "L362"; TAtom "L298"]];
        TApp "block" [TAtom "L362"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___lll_lock_wake_private"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v345"]]]]];
          TApp "goto" [TAtom "L298"]];
        TApp "block" [TAtom "L330"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v374"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 136]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v375"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk40"]]];
            TApp "flight" [TApp "tmp" [TAtom "v376"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v375"]]; TApp "const" [TInt 4]]; TApp "lower" [TApp "tmp" [TAtom "v375"]]];
            TApp "let" [TApp "tmp" [TAtom "chk48"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v376"]]];
            TApp "let" [TApp "tmp" [TAtom "v377"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk48"]]];
            TApp "let" [TApp "tmp" [TAtom "v378"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "v377"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk49"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk48"]; TApp "tmp" [TAtom "v376"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v378"]; TApp "tmp" [TAtom "chk49"]]];
          TApp "goto" [TAtom "L298"]];
        TApp "block" [TAtom "L298"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.5"]; TAtom "L379"; TAtom "L385"]];
        TApp "block" [TAtom "L379"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___libc_cleanup_pop_restore"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v187"]]]]];
          TApp "goto" [TAtom "L385"]];
        TApp "block" [TAtom "L385"; TList [];
          TList [];
          TApp "ret" [TApp "tmp" [TAtom "v295"]]]]];
    TApp "func" [TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline"; TAtom "local"; TAtom "p"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v3"]; TAtom "p"]; TApp "global" [TAtom "__GI___strchrnul"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 37]]]]];
          TApp "ret" [TApp "tmp" [TAtom "v3"]]]]];
    TApp "func" [TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed"; TAtom "local"; TAtom "w"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v3"]]];
            TApp "let" [TApp "tmp" [TAtom "v4"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v5"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v4"]; TApp "const" [TInt 0]]]];
          TApp "ret" [TApp "tmp" [TAtom "v5"]]]]];
    TApp "func" [TAtom "glibc_vfprintf_internal#__printf_buffer_mark_failed"; TAtom "local"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v3"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk0"]]];
          TAtom "ret"]]];
    TApp "func" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"; TAtom "local"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "w"; TApp "tmp" [TAtom "v2"]]; TApp "param" [TAtom "l"; TApp "tmp" [TAtom "v4"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v10"]; TAtom "w"; TApp "cmp" [TAtom "sgt"; TAtom "l"]; TList [TApp "tmp" [TAtom "v4"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v10"]; TAtom "L6"; TAtom "L8"]];
        TApp "block" [TAtom "L6"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v12"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_pad_1"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v12"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v4"]]]]];
          TApp "goto" [TAtom "L8"]];
        TApp "block" [TAtom "L8"; TList [];
          TList [];
          TAtom "ret"]]];
    TApp "func" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"; TAtom "local"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "w"; TApp "tmp" [TAtom "v2"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v8"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "v9"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v11"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v11"]]];
            TApp "let" [TApp "tmp" [TAtom "v12"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "let" [TApp "tmp" [TAtom "v13"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v9"]]];
            TApp "let" [TApp "tmp" [TAtom "v14"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v15"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v13"]; TApp "tmp" [TAtom "v14"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v15"]; TAtom "L4"; TAtom "L5"]];
        TApp "block" [TAtom "L4"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v17"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v18"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v19"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v18"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v18"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v17"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v19"]; TApp "tmp" [TAtom "chk3"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "v20"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk4"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v18"]]];
            TApp "raw_store" [TAtom "b"; TInt 0; TApp "tmp" [TAtom "v20"]; TApp "tmp" [TAtom "chk4"]]];
          TApp "goto" [TAtom "L6"]];
        TApp "block" [TAtom "L5"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v22"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_putc_1"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v22"]]]]];
          TApp "goto" [TAtom "L6"]];
        TApp "block" [TAtom "L6"; TList [];
          TList [];
          TAtom "ret"]]];
    TApp "func" [TAtom "glibc_vfprintf_internal#__printf_fp_spec"; TAtom "local"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v4"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v10"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v10"]]];
            TApp "let" [TApp "tmp" [TAtom "v11"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v12"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v11"]; TApp "const" [TInt 97]]]];
          TApp "branch" [TApp "tmp" [TAtom "v12"]; TAtom "L14"; TAtom "L13"]];
        TApp "block" [TAtom "L13"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v16"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v17"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v18"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v17"]; TApp "const" [TInt 65]]]];
          TApp "goto" [TAtom "L14"]];
        TApp "block" [TAtom "L14"; TList [TApp "phi" [TApp "tmp" [TAtom "v20"]; TAtom "w"; TList [TApp "-" [TAtom "start"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L13"; TApp "tmp" [TAtom "v18"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v20"]; TAtom "L6"; TAtom "L7"]];
        TApp "block" [TAtom "L6"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v22"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_tsd_LOCALE"]]];
            TApp "let" [TApp "tmp" [TAtom "chk2"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v22"]]];
            TApp "let" [TApp "tmp" [TAtom "v23"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk2"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_fphex_l_buffer"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v23"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v4"]]]]];
          TApp "goto" [TAtom "L8"]];
        TApp "block" [TAtom "L7"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v27"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_tsd_LOCALE"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v27"]]];
            TApp "let" [TApp "tmp" [TAtom "v28"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk3"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_fp_l_buffer"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v28"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v4"]]]]];
          TApp "goto" [TAtom "L8"]];
        TApp "block" [TAtom "L8"; TList [];
          TList [];
          TAtom "ret"]]];
    TApp "func" [TAtom "glibc_vfprintf_internal#scratch_buffer_free"; TAtom "local"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v6"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v8"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v9"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v6"]]];
            TApp "let" [TApp "tmp" [TAtom "v10"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "v11"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v9"]; TApp "tmp" [TAtom "v10"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v11"]; TAtom "L2"; TAtom "L4"]];
        TApp "block" [TAtom "L2"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v13"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "free"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v13"]]]]];
          TApp "goto" [TAtom "L4"]];
        TApp "block" [TAtom "L4"; TList [];
          TList [];
          TAtom "ret"]]];
    TApp "func" [TAtom "glibc_vfprintf_internal#scratch_buffer_init"; TAtom "local"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v4"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v0"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v4"]; TApp "tmp" [TAtom "chk0"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "v6"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v6"]]];
            TApp "raw_store" [TAtom "l"; TInt 0; TApp "const" [TInt 1024]; TApp "tmp" [TAtom "chk1"]]];
          TAtom "ret"]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277"; TApp "ro" [TAtom "local"]; TInt 4; TList [TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 1]]; TApp "item" [TAtom "w"; TApp "const" [TInt 2]]; TApp "item" [TAtom "w"; TApp "const" [TInt 3]]; TApp "item" [TAtom "w"; TApp "const" [TInt 4]]; TApp "item" [TAtom "w"; TApp "const" [TInt 5]]; TApp "item" [TAtom "w"; TApp "const" [TInt 6]]; TApp "item" [TAtom "w"; TApp "const" [TInt 7]]; TApp "item" [TAtom "w"; TApp "const" [TInt 8]]; TApp "item" [TAtom "w"; TApp "const" [TInt 9]]; TApp "item" [TAtom "w"; TApp "const" [TInt 10]]; TApp "item" [TAtom "w"; TApp "const" [TInt 11]]; TApp "item" [TAtom "w"; TApp "const" [TInt 12]]; TApp "item" [TAtom "w"; TApp "const" [TInt 13]]; TApp "item" [TAtom "w"; TApp "const" [TInt 14]]; TApp "item" [TAtom "w"; TApp "const" [TInt 15]]; TApp "item" [TAtom "w"; TApp "const" [TInt 16]]; TApp "item" [TAtom "w"; TApp "const" [TInt 17]]; TApp "item" [TAtom "w"; TApp "const" [TInt 18]]; TApp "item" [TAtom "w"; TApp "const" [TInt 19]]; TApp "item" [TAtom "w"; TApp "const" [TInt 20]]; TApp "item" [TAtom "w"; TApp "const" [TInt 21]]; TApp "item" [TAtom "w"; TApp "const" [TInt 22]]; TApp "item" [TAtom "w"; TApp "const" [TInt 23]]; TApp "item" [TAtom "w"; TApp "const" [TInt 24]]; TApp "item" [TAtom "w"; TApp "const" [TInt 25]]; TApp "item" [TAtom "w"; TApp "const" [TInt 26]]; TApp "item" [TAtom "w"; TApp "const" [TInt 27]]; TApp "item" [TAtom "w"; TApp "const" [TInt 28]]; TApp "item" [TAtom "w"; TApp "const" [TInt 29]]; TApp "item" [TAtom "w"; TApp "const" [TInt 30]]; TApp "item" [TAtom "w"; TApp "const" [TInt 31]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#__printf_buffer.step1_jumps.278"; TApp "ro" [TAtom "local"]; TInt 4; TList [TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 9]]; TApp "item" [TAtom "w"; TApp "const" [TInt 10]]; TApp "item" [TAtom "w"; TApp "const" [TInt 11]]; TApp "item" [TAtom "w"; TApp "const" [TInt 12]]; TApp "item" [TAtom "w"; TApp "const" [TInt 13]]; TApp "item" [TAtom "w"; TApp "const" [TInt 14]]; TApp "item" [TAtom "w"; TApp "const" [TInt 15]]; TApp "item" [TAtom "w"; TApp "const" [TInt 16]]; TApp "item" [TAtom "w"; TApp "const" [TInt 17]]; TApp "item" [TAtom "w"; TApp "const" [TInt 18]]; TApp "item" [TAtom "w"; TApp "const" [TInt 19]]; TApp "item" [TAtom "w"; TApp "const" [TInt 20]]; TApp "item" [TAtom "w"; TApp "const" [TInt 21]]; TApp "item" [TAtom "w"; TApp "const" [TInt 22]]; TApp "item" [TAtom "w"; TApp "const" [TInt 23]]; TApp "item" [TAtom "w"; TApp "const" [TInt 24]]; TApp "item" [TAtom "w"; TApp "const" [TInt 25]]; TApp "item" [TAtom "w"; TApp "const" [TInt 26]]; TApp "item" [TAtom "w"; TApp "const" [TInt 27]]; TApp "item" [TAtom "w"; TApp "const" [TInt 28]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 30]]; TApp "item" [TAtom "w"; TApp "const" [TInt 31]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#__printf_buffer.step2_jumps.279"; TApp "ro" [TAtom "local"]; TInt 4; TList [TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 10]]; TApp "item" [TAtom "w"; TApp "const" [TInt 11]]; TApp "item" [TAtom "w"; TApp "const" [TInt 12]]; TApp "item" [TAtom "w"; TApp "const" [TInt 13]]; TApp "item" [TAtom "w"; TApp "const" [TInt 14]]; TApp "item" [TAtom "w"; TApp "const" [TInt 15]]; TApp "item" [TAtom "w"; TApp "const" [TInt 16]]; TApp "item" [TAtom "w"; TApp "const" [TInt 17]]; TApp "item" [TAtom "w"; TApp "const" [TInt 18]]; TApp "item" [TAtom "w"; TApp "const" [TInt 19]]; TApp "item" [TAtom "w"; TApp "const" [TInt 20]]; TApp "item" [TAtom "w"; TApp "const" [TInt 21]]; TApp "item" [TAtom "w"; TApp "const" [TInt 22]]; TApp "item" [TAtom "w"; TApp "const" [TInt 23]]; TApp "item" [TAtom "w"; TApp "const" [TInt 24]]; TApp "item" [TAtom "w"; TApp "const" [TInt 25]]; TApp "item" [TAtom "w"; TApp "const" [TInt 26]]; TApp "item" [TAtom "w"; TApp "const" [TInt 27]]; TApp "item" [TAtom "w"; TApp "const" [TInt 28]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 30]]; TApp "item" [TAtom "w"; TApp "const" [TInt 31]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#__printf_buffer.step3a_jumps.280"; TApp "ro" [TAtom "local"]; TInt 4; TList [TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 32]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 14]]; TApp "item" [TAtom "w"; TApp "const" [TInt 15]]; TApp "item" [TAtom "w"; TApp "const" [TInt 16]]; TApp "item" [TAtom "w"; TApp "const" [TInt 17]]; TApp "item" [TAtom "w"; TApp "const" [TInt 18]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 23]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 30]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#__printf_buffer.step3b_jumps.281"; TApp "ro" [TAtom "local"]; TInt 4; TList [TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 12]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 14]]; TApp "item" [TAtom "w"; TApp "const" [TInt 15]]; TApp "item" [TAtom "w"; TApp "const" [TInt 16]]; TApp "item" [TAtom "w"; TApp "const" [TInt 17]]; TApp "item" [TAtom "w"; TApp "const" [TInt 18]]; TApp "item" [TAtom "w"; TApp "const" [TInt 19]]; TApp "item" [TAtom "w"; TApp "const" [TInt 20]]; TApp "item" [TAtom "w"; TApp "const" [TInt 21]]; TApp "item" [TAtom "w"; TApp "const" [TInt 22]]; TApp "item" [TAtom "w"; TApp "const" [TInt 23]]; TApp "item" [TAtom "w"; TApp "const" [TInt 24]]; TApp "item" [TAtom "w"; TApp "const" [TInt 25]]; TApp "item" [TAtom "w"; TApp "const" [TInt 26]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 30]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#__printf_buffer.step4_jumps.282"; TApp "ro" [TAtom "local"]; TInt 4; TList [TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 14]]; TApp "item" [TAtom "w"; TApp "const" [TInt 15]]; TApp "item" [TAtom "w"; TApp "const" [TInt 16]]; TApp "item" [TAtom "w"; TApp "const" [TInt 17]]; TApp "item" [TAtom "w"; TApp "const" [TInt 18]]; TApp "item" [TAtom "w"; TApp "const" [TInt 19]]; TApp "item" [TAtom "w"; TApp "const" [TInt 20]]; TApp "item" [TAtom "w"; TApp "const" [TInt 21]]; TApp "item" [TAtom "w"; TApp "const" [TInt 22]]; TApp "item" [TAtom "w"; TApp "const" [TInt 23]]; TApp "item" [TAtom "w"; TApp "const" [TInt 24]]; TApp "item" [TAtom "w"; TApp "const" [TInt 25]]; TApp "item" [TAtom "w"; TApp "const" [TInt 26]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 30]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#jump_table"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "str" [TList (app [(chr 1); (chr 0); (chr 0); (chr 4); (chr 0); (chr 14); (chr 0); (chr 6); (chr 0); (chr 0); (chr 7); (chr 2); (chr 0); (chr 3); (chr 9); (chr 0); (chr 5); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 26); (chr 30); (chr 25); (chr 0); (chr 19); (chr 19); (chr 19); (chr 0); (chr 29); (chr 0); (chr 0); (chr 12)] [(chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 21); (chr 0); (chr 0); (chr 0); (chr 0); (chr 18); (chr 0); (chr 13); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 26); (chr 30); (chr 20); (chr 15); (chr 19); (chr 19); (chr 19); (chr 10); (chr 15); (chr 28); (chr 0); (chr 11); (chr 24); (chr 23); (chr 17); (chr 22); (chr 12); (chr 0); (chr 21); (chr 27); (chr 16); (chr 0); (chr 31); (chr 18); (chr 0); (chr 13)])]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#null"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "str" [TList [TAtom "("; TAtom "n"; TAtom "u"; TAtom "l"; TAtom "l"; TAtom ")"]]]; TApp "zero" [TInt 1]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#printf_positional.step4_jumps.294"; TApp "ro" [TAtom "local"]; TInt 4; TList [TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 1]]; TApp "item" [TAtom "w"; TApp "const" [TInt 2]]; TApp "item" [TAtom "w"; TApp "const" [TInt 3]]; TApp "item" [TAtom "w"; TApp "const" [TInt 4]]; TApp "item" [TAtom "w"; TApp "const" [TInt 5]]; TApp "item" [TAtom "w"; TApp "const" [TInt 6]]; TApp "item" [TAtom "w"; TApp "const" [TInt 7]]; TApp "item" [TAtom "w"; TApp "const" [TInt 8]]; TApp "item" [TAtom "w"; TApp "const" [TInt 9]]; TApp "item" [TAtom "w"; TApp "const" [TInt 10]]; TApp "item" [TAtom "w"; TApp "const" [TInt 11]]; TApp "item" [TAtom "w"; TApp "const" [TInt 12]]; TApp "item" [TAtom "w"; TApp "const" [TInt 13]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]; TApp "item" [TAtom "w"; TApp "const" [TInt 14]]; TApp "item" [TAtom "w"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#str.284"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "const" [TInt 40]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 108]]; TApp "item" [TAtom "b"; TApp "const" [TInt 41]]; TApp "item" [TAtom "b"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#str.285"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 37]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 119]]; TApp "item" [TAtom "b"; TApp "const" [TInt 114]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 97]]; TApp "item" [TAtom "b"; TApp "const" [TInt 98]]; TApp "item" [TAtom "b"; TApp "const" [TInt 108]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 115]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 103]]; TApp "item" [TAtom "b"; TApp "const" [TInt 109]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 115]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 100]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 99]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 100]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 10]]; TApp "item" [TAtom "b"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#str.286"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 112]]; TApp "item" [TAtom "b"; TApp "const" [TInt 114]]; TApp "item" [TAtom "b"; TApp "const" [TInt 111]]; TApp "item" [TAtom "b"; TApp "const" [TInt 99]]; TApp "item" [TAtom "b"; TApp "const" [TInt 102]]; TApp "item" [TAtom "b"; TApp "const" [TInt 115]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 99]]; TApp "item" [TAtom "b"; TApp "const" [TInt 111]]; TApp "item" [TAtom "b"; TApp "const" [TInt 117]]; TApp "item" [TAtom "b"; TApp "const" [TInt 108]]; TApp "item" [TAtom "b"; TApp "const" [TInt 100]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 111]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 111]]; TApp "item" [TAtom "b"; TApp "const" [TInt 112]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 10]]; TApp "item" [TAtom "b"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#str.289"; TApp "ro" [TAtom "local"]; TInt 4; TList [TApp "item" [TAtom "w"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#str.290"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "const" [TInt 40]]; TApp "item" [TAtom "b"; TApp "const" [TInt 109]]; TApp "item" [TAtom "b"; TApp "const" [TInt 111]]; TApp "item" [TAtom "b"; TApp "const" [TInt 100]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 95]]; TApp "item" [TAtom "b"; TApp "const" [TInt 102]]; TApp "item" [TAtom "b"; TApp "const" [TInt 108]]; TApp "item" [TAtom "b"; TApp "const" [TInt 97]]; TApp "item" [TAtom "b"; TApp "const" [TInt 103]]; TApp "item" [TAtom "b"; TApp "const" [TInt 115]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 38]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 80]]; TApp "item" [TAtom "b"; TApp "const" [TInt 82]]; TApp "item" [TAtom "b"; TApp "const" [TInt 73]]; TApp "item" [TAtom "b"; TApp "const" [TInt 78]]; TApp "item" [TAtom "b"; TApp "const" [TInt 84]]; TApp "item" [TAtom "b"; TApp "const" [TInt 70]]; TApp "item" [TAtom "b"; TApp "const" [TInt 95]]; TApp "item" [TAtom "b"; TApp "const" [TInt 70]]; TApp "item" [TAtom "b"; TApp "const" [TInt 79]]; TApp "item" [TAtom "b"; TApp "const" [TInt 82]]; TApp "item" [TAtom "b"; TApp "const" [TInt 84]]; TApp "item" [TAtom "b"; TApp "const" [TInt 73]]; TApp "item" [TAtom "b"; TApp "const" [TInt 70]]; TApp "item" [TAtom "b"; TApp "const" [TInt 89]]; TApp "item" [TAtom "b"; TApp "const" [TInt 41]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 33]]; TApp "item" [TAtom "b"; TApp "const" [TInt 61]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 48]]; TApp "item" [TAtom "b"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#str.291"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "const" [TInt 118]]; TApp "item" [TAtom "b"; TApp "const" [TInt 102]]; TApp "item" [TAtom "b"; TApp "const" [TInt 112]]; TApp "item" [TAtom "b"; TApp "const" [TInt 114]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 102]]; TApp "item" [TAtom "b"; TApp "const" [TInt 45]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 114]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 97]]; TApp "item" [TAtom "b"; TApp "const" [TInt 108]]; TApp "item" [TAtom "b"; TApp "const" [TInt 46]]; TApp "item" [TAtom "b"; TApp "const" [TInt 99]]; TApp "item" [TAtom "b"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#str.292"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "const" [TInt 112]]; TApp "item" [TAtom "b"; TApp "const" [TInt 114]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 102]]; TApp "item" [TAtom "b"; TApp "const" [TInt 95]]; TApp "item" [TAtom "b"; TApp "const" [TInt 112]]; TApp "item" [TAtom "b"; TApp "const" [TInt 111]]; TApp "item" [TAtom "b"; TApp "const" [TInt 115]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 111]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 97]]; TApp "item" [TAtom "b"; TApp "const" [TInt 108]]; TApp "item" [TAtom "b"; TApp "const" [TInt 0]]]];
    TApp "data" [TAtom "glibc_vfprintf_internal#str.293"; TApp "ro" [TAtom "local"]; TInt 1; TList [TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 110]]; TApp "item" [TAtom "b"; TApp "const" [TInt 118]]; TApp "item" [TAtom "b"; TApp "const" [TInt 97]]; TApp "item" [TAtom "b"; TApp "const" [TInt 108]]; TApp "item" [TAtom "b"; TApp "const" [TInt 105]]; TApp "item" [TAtom "b"; TApp "const" [TInt 100]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 37]]; TApp "item" [TAtom "b"; TApp "const" [TInt 78]]; TApp "item" [TAtom "b"; TApp "const" [TInt 36]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 117]]; TApp "item" [TAtom "b"; TApp "const" [TInt 115]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 100]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 99]]; TApp "item" [TAtom "b"; TApp "const" [TInt 116]]; TApp "item" [TAtom "b"; TApp "const" [TInt 101]]; TApp "item" [TAtom "b"; TApp "const" [TInt 100]]; TApp "item" [TAtom "b"; TApp "const" [TInt 32]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 42]]; TApp "item" [TAtom "b"; TApp "const" [TInt 10]]; TApp "item" [TAtom "b"; TApp "const" [TInt 0]]]]
  ].
