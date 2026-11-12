(** These checked bodies implement printf-buffer operations in user-glibc 2.44.
    They retain the source's failure paths and calls into stream operations;
    decoding these bodies does not establish contracts for those calls.

    rocq/glibc/stdio/buffer-code.sh reproduces these terms from the pinned
    capture with gallina.pl. Regenerate this file rather than editing it. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** This helper constructs the atom containing one character with code n. *)
Definition chr (n : nat) : term := TAtom (String (ascii_of_nat n) EmptyString).

(** This term contains the selected checked function bodies. *)
Definition printf_buffer_file_term : term :=
  TApp "module" [TList [
    TApp "func" [TAtom "__printf_buffer_to_file_switch"; TAtom "export"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v6"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v6"]]];
            TApp "let" [TApp "tmp" [TAtom "v7"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v8"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v7"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v7"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "v9"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "let" [TApp "tmp" [TAtom "v12"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v13"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v13"]]];
            TApp "let" [TApp "tmp" [TAtom "v14"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk3"]]];
            TApp "let" [TApp "tmp" [TAtom "v15"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v9"]]];
            TApp "let" [TApp "tmp" [TAtom "v16"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v14"]]];
            TApp "let" [TApp "tmp" [TAtom "v17"]; TAtom "w"; TApp "cmp" [TAtom "ult"; TAtom "l"]; TList [TApp "tmp" [TAtom "v15"]; TApp "tmp" [TAtom "v16"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v17"]; TAtom "L2"; TAtom "L3"]];
        TApp "block" [TAtom "L2"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v19"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v21"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v22"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v23"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v22"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v22"]]];
            TApp "let" [TApp "tmp" [TAtom "chk5"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v23"]]];
            TApp "let" [TApp "tmp" [TAtom "v24"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk5"]]];
            TApp "let" [TApp "tmp" [TAtom "chk6"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v19"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v24"]; TApp "tmp" [TAtom "chk6"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "v26"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk7"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v21"]]];
            TApp "let" [TApp "tmp" [TAtom "v29"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk7"]]];
            TApp "flight" [TApp "tmp" [TAtom "v30"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v29"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v29"]]];
            TApp "let" [TApp "tmp" [TAtom "chk8"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v30"]]];
            TApp "let" [TApp "tmp" [TAtom "v31"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk8"]]];
            TApp "let" [TApp "tmp" [TAtom "chk9"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v26"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v31"]; TApp "tmp" [TAtom "chk9"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L4"]];
        TApp "block" [TAtom "L3"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v33"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v35"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk10"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v33"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v35"]; TApp "tmp" [TAtom "chk10"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "v37"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v43"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v35"]]; TApp "const" [TInt 128]]; TApp "lower" [TApp "tmp" [TAtom "v35"]]];
            TApp "let" [TApp "tmp" [TAtom "chk11"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v37"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v43"]; TApp "tmp" [TAtom "chk11"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L4"]];
        TApp "block" [TAtom "L4"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v46"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk12"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v46"]]];
            TApp "let" [TApp "tmp" [TAtom "v47"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk13"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v0"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v47"]; TApp "tmp" [TAtom "chk13"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TAtom "ret"]]];
    TApp "func" [TAtom "__printf_buffer_flush_to_file"; TAtom "export"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v3"]]];
            TApp "let" [TApp "tmp" [TAtom "v4"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v6"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v6"]]];
            TApp "let" [TApp "tmp" [TAtom "v7"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "let" [TApp "tmp" [TAtom "chk2"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v9"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk2"]]];
            TApp "let" [TApp "tmp" [TAtom "v10"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v7"]]];
            TApp "let" [TApp "tmp" [TAtom "v11"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v9"]]];
            TApp "let" [TApp "tmp" [TAtom "v12"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "v10"]; TApp "tmp" [TAtom "v11"]]];
            TApp "let" [TApp "tmp" [TAtom "v13"]; TAtom "l"; TAtom "add"; TList [TApp "tmp" [TAtom "v4"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v3"]]];
            TApp "raw_store" [TAtom "l"; TInt 0; TApp "tmp" [TAtom "v13"]; TApp "tmp" [TAtom "chk3"]];
            TApp "flight" [TApp "tmp" [TAtom "v18"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v19"]; TAtom "p"; TApp "raw_load_pointer" [TInt 8; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "flight" [TApp "tmp" [TAtom "v21"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v25"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v21"]]; TApp "const" [TInt 128]]; TApp "lower" [TApp "tmp" [TAtom "v21"]]];
            TApp "let" [TApp "tmp" [TAtom "v26"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v19"]]];
            TApp "let" [TApp "tmp" [TAtom "v27"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v25"]]];
            TApp "let" [TApp "tmp" [TAtom "v28"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v26"]; TApp "tmp" [TAtom "v27"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v28"]; TAtom "L14"; TAtom "L15"]];
        TApp "block" [TAtom "L14"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v31"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v32"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "flight" [TApp "tmp" [TAtom "v34"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v35"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v32"]]];
            TApp "let" [TApp "tmp" [TAtom "v36"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v34"]]];
            TApp "let" [TApp "tmp" [TAtom "v37"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "v35"]; TApp "tmp" [TAtom "v36"]]];
            TApp "flight" [TApp "tmp" [TAtom "v42"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk6"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v42"]]];
            TApp "let" [TApp "tmp" [TAtom "v43"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk6"]]];
            TApp "flight" [TApp "tmp" [TAtom "v44"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v43"]]; TApp "const" [TInt 216]]; TApp "lower" [TApp "tmp" [TAtom "v43"]]];
            TApp "let" [TApp "tmp" [TAtom "chk7"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v44"]]];
            TApp "let" [TApp "tmp" [TAtom "v45"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk7"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v4"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v45"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v7"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__io_vtables"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v8"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "iw_1.v7"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v9"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "iw_1.v4"]; TApp "tmp" [TAtom "iw_1.v8"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v15"]; TAtom "w"; TApp "cmp" [TAtom "uge"; TAtom "l"]; TList [TApp "tmp" [TAtom "iw_1.v9"]; TApp "const" [TInt 2352]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_1.v15"]; TAtom "iw_1.L10"; TAtom "iw_1.join"]];
        TApp "block" [TAtom "iw_1.L10"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "_IO_vtable_check"]; TList []]];
          TApp "goto" [TAtom "iw_1.join"]];
        TApp "block" [TAtom "iw_1.join"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v47"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v45"]]; TApp "const" [TInt 56]]; TApp "lower" [TApp "tmp" [TAtom "v45"]]];
            TApp "let" [TApp "tmp" [TAtom "chk8"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v47"]]];
            TApp "let" [TApp "tmp" [TAtom "v48"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk8"]]];
            TApp "flight" [TApp "tmp" [TAtom "v50"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk9"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk6"]; TApp "tmp" [TAtom "v50"]]];
            TApp "let" [TApp "tmp" [TAtom "v51"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk9"]]];
            TApp "flight" [TApp "tmp" [TAtom "v53"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk10"]; TAtom "f"; TAtom "check_function"; TList [TApp "tmp" [TAtom "v48"]]];
            TApp "raw_call" [TApp "result" [TApp "tmp" [TAtom "v55"]; TAtom "l"]; TApp "tmp" [TAtom "chk10"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v51"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v53"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v37"]]]];
            TApp "let" [TApp "tmp" [TAtom "v57"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v55"]; TApp "tmp" [TAtom "v37"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v57"]; TAtom "iw_2.start"; TAtom "L40"]];
        TApp "block" [TAtom "iw_2.start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_2.v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk11"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "iw_2.v3"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk11"]]];
          TAtom "ret"];
        TApp "block" [TAtom "L40"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_to_file_switch"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TAtom "ret"];
        TApp "block" [TAtom "L15"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v66"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v67"]; TAtom "p"; TApp "raw_load_pointer" [TInt 8; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "flight" [TApp "tmp" [TAtom "v69"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v70"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v69"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v69"]]];
            TApp "let" [TApp "tmp" [TAtom "v71"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v67"]]];
            TApp "let" [TApp "tmp" [TAtom "v72"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v70"]]];
            TApp "let" [TApp "tmp" [TAtom "v73"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v71"]; TApp "tmp" [TAtom "v72"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v73"]; TAtom "L62"; TAtom "L16"]];
        TApp "block" [TAtom "L62"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v78"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v79"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "flight" [TApp "tmp" [TAtom "v81"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v82"]; TAtom "p"; TApp "raw_load_pointer" [TInt 8; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "let" [TApp "tmp" [TAtom "v83"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v79"]]];
            TApp "let" [TApp "tmp" [TAtom "v84"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v82"]]];
            TApp "let" [TApp "tmp" [TAtom "v85"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v83"]; TApp "tmp" [TAtom "v84"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v85"]; TAtom "L74"; TAtom "L76"]];
        TApp "block" [TAtom "L74"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v90"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk15"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v90"]]];
            TApp "let" [TApp "tmp" [TAtom "v91"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk15"]]];
            TApp "flight" [TApp "tmp" [TAtom "v93"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk16"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v93"]]];
            TApp "let" [TApp "tmp" [TAtom "v94"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk16"]]];
            TApp "let" [TApp "tmp" [TAtom "v95"]; TAtom "w"; TApp "ext" [TAtom "ub"]; TList [TApp "tmp" [TAtom "v94"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v96"]; TAtom "w"]; TApp "global" [TAtom "__GI___overflow"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v91"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v95"]]]];
            TApp "let" [TApp "tmp" [TAtom "v98"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v96"]; TApp "const" [TInt 4294967295]]]];
          TApp "branch" [TApp "tmp" [TAtom "v98"]; TAtom "iw_3.start"; TAtom "L88"]];
        TApp "block" [TAtom "iw_3.start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_3.v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk17"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "iw_3.v3"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk17"]]];
          TAtom "ret"];
        TApp "block" [TAtom "L88"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_to_file_switch"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "L76"]];
        TApp "block" [TAtom "L76"; TList [];
          TList [];
          TAtom "ret"];
        TApp "block" [TAtom "L16"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v107"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v108"]; TAtom "p"; TApp "raw_load_pointer" [TInt 8; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "flight" [TApp "tmp" [TAtom "v110"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk19"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v110"]]];
            TApp "let" [TApp "tmp" [TAtom "v111"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk19"]]];
            TApp "flight" [TApp "tmp" [TAtom "v112"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v111"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v111"]]];
            TApp "let" [TApp "tmp" [TAtom "chk20"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v112"]]];
            TApp "let" [TApp "tmp" [TAtom "v113"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk20"]]];
            TApp "let" [TApp "tmp" [TAtom "v114"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v108"]]];
            TApp "let" [TApp "tmp" [TAtom "v115"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v113"]]];
            TApp "let" [TApp "tmp" [TAtom "v116"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v114"]; TApp "tmp" [TAtom "v115"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v116"]; TAtom "L105"; TAtom "L104"]];
        TApp "block" [TAtom "L104"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v117"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_to_file#str.266"]]];
            TApp "let" [TApp "tmp" [TAtom "v118"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_to_file#str.267"]]];
            TApp "let" [TApp "tmp" [TAtom "v119"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_to_file#str.268"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__libc_assert_fail"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v117"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v118"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 86]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v119"]]]]];
          TApp "goto" [TAtom "L105"]];
        TApp "block" [TAtom "L105"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v121"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk21"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "v121"]]];
            TApp "let" [TApp "tmp" [TAtom "v122"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk21"]]];
            TApp "flight" [TApp "tmp" [TAtom "v123"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v122"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v122"]]];
            TApp "flight" [TApp "tmp" [TAtom "v125"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk22"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v125"]]];
            TApp "let" [TApp "tmp" [TAtom "v126"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk22"]]];
            TApp "let" [TApp "tmp" [TAtom "chk23"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v123"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v126"]; TApp "tmp" [TAtom "chk23"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk24"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v125"]]];
            TApp "let" [TApp "tmp" [TAtom "v132"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk24"]]];
            TApp "flight" [TApp "tmp" [TAtom "v134"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk25"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v134"]]];
            TApp "let" [TApp "tmp" [TAtom "v135"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk25"]]];
            TApp "let" [TApp "tmp" [TAtom "v136"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v132"]]];
            TApp "let" [TApp "tmp" [TAtom "v137"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v135"]]];
            TApp "let" [TApp "tmp" [TAtom "v138"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v136"]; TApp "tmp" [TAtom "v137"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v138"]; TAtom "L127"; TAtom "L129"]];
        TApp "block" [TAtom "L127"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v140"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v142"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk26"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v140"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v142"]; TApp "tmp" [TAtom "chk26"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "v144"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "flight" [TApp "tmp" [TAtom "v147"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v142"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v142"]]];
            TApp "let" [TApp "tmp" [TAtom "chk27"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk25"]; TApp "tmp" [TAtom "v144"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v147"]; TApp "tmp" [TAtom "chk27"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L129"]];
        TApp "block" [TAtom "L129"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v150"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk28"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v150"]]];
            TApp "let" [TApp "tmp" [TAtom "v151"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk28"]]];
            TApp "let" [TApp "tmp" [TAtom "chk29"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v0"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v151"]; TApp "tmp" [TAtom "chk29"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TAtom "ret"]]];
    TApp "func" [TAtom "__printf_buffer_to_file_init"; TAtom "export"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v2"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v6"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "flight" [TApp "tmp" [TAtom "iw_1.v12"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v6"]]; TApp "const" [TInt 128]]; TApp "lower" [TApp "tmp" [TAtom "v6"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v0"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v6"]; TApp "tmp" [TAtom "chk0"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "iw_1.iw_1.v11"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "iw_1.iw_1.v11"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v6"]; TApp "tmp" [TAtom "chk1"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "iw_1.iw_1.v14"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk2"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "iw_1.iw_1.v14"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "iw_1.v12"]; TApp "tmp" [TAtom "chk2"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "iw_1.iw_1.v17"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "iw_1.iw_1.v17"]]];
            TApp "raw_store" [TAtom "l"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk3"]];
            TApp "flight" [TApp "tmp" [TAtom "iw_1.iw_1.v19"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk4"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "iw_1.iw_1.v19"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 4]; TApp "tmp" [TAtom "chk4"]];
            TApp "flight" [TApp "tmp" [TAtom "v11"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk5"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v11"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v2"]; TApp "tmp" [TAtom "chk5"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_to_file_switch"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TAtom "ret"]]];
    TApp "func" [TAtom "__printf_buffer_to_file_done"; TAtom "export"; TAtom "w"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_1.v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "iw_1.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v4"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_1.v4"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "L2"; TAtom "L4"]];
        TApp "block" [TAtom "L2"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L4"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_to_file"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v12"]; TAtom "w"]; TApp "global" [TAtom "__printf_buffer_done"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "ret" [TApp "tmp" [TAtom "v12"]]]]]
  ]].

From Nanofil Require Import Syntax Transport Semantics.

(** Decoding gives the actual checked bodies used by instruction proofs. *)
Definition printf_buffer_file_module : module := Eval vm_compute in
  match decode_module printf_buffer_file_term with Some md => md | None => [] end.

(** Computation rules out the empty fallback in the decoded module. *)
Lemma printf_buffer_file_decodes : decode_module printf_buffer_file_term = Some printf_buffer_file_module.
Proof. vm_compute. reflexivity. Qed.

(** Function lookup selects a checked body without supplying its specification. *)
Definition printf_buffer_file_fn (n : string) : func :=
  match find_direct (TAtom n) printf_buffer_file_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** This definition selects the checked body of [__printf_buffer_to_file_switch]. *)
Definition glibc___printf_buffer_to_file_switch : func := Eval vm_compute in
  printf_buffer_file_fn "__printf_buffer_to_file_switch".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_file_find_printf_buffer_to_file_switch :
  find_direct (TAtom "__printf_buffer_to_file_switch") printf_buffer_file_module = Some (Defined glibc___printf_buffer_to_file_switch).
Proof. vm_compute. reflexivity. Qed.

(** This definition selects the checked body of [__printf_buffer_flush_to_file]. *)
Definition glibc___printf_buffer_flush_to_file : func := Eval vm_compute in
  printf_buffer_file_fn "__printf_buffer_flush_to_file".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_file_find_printf_buffer_flush_to_file :
  find_direct (TAtom "__printf_buffer_flush_to_file") printf_buffer_file_module = Some (Defined glibc___printf_buffer_flush_to_file).
Proof. vm_compute. reflexivity. Qed.

(** This definition selects the checked body of [__printf_buffer_to_file_init]. *)
Definition glibc___printf_buffer_to_file_init : func := Eval vm_compute in
  printf_buffer_file_fn "__printf_buffer_to_file_init".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_file_find_printf_buffer_to_file_init :
  find_direct (TAtom "__printf_buffer_to_file_init") printf_buffer_file_module = Some (Defined glibc___printf_buffer_to_file_init).
Proof. vm_compute. reflexivity. Qed.

(** This definition selects the checked body of [__printf_buffer_to_file_done]. *)
Definition glibc___printf_buffer_to_file_done : func := Eval vm_compute in
  printf_buffer_file_fn "__printf_buffer_to_file_done".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_file_find_printf_buffer_to_file_done :
  find_direct (TAtom "__printf_buffer_to_file_done") printf_buffer_file_module = Some (Defined glibc___printf_buffer_to_file_done).
Proof. vm_compute. reflexivity. Qed.
