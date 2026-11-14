(** These checked bodies implement printf-buffer operations in user-glibc 2.44.
    They retain the source's failure paths and calls into stream operations;
    decoding these bodies does not establish contracts for those calls.

    rocq/glibc/stdio/buffer-code.sh reproduces these terms from the pinned
    capture with gallina.pl. Regenerate this file rather than editing it. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** This term contains the selected checked function bodies. *)
Definition printf_buffer_io_term : term :=
  TApp "module" [TList [
    TApp "func" [TAtom "__printf_buffer_write"; TAtom "export"; TAtom "void"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "param" [TAtom "l"; TApp "tmp" [TAtom "v4"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_1.v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "iw_1.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v4"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_1.v4"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "L6"; TAtom "L15"]];
        TApp "block" [TAtom "L6"; TList [];
          TList [];
          TAtom "ret"];
        TApp "block" [TAtom "L15"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.2"]; TAtom "l"; TList [TApp "-" [TAtom "L68"; TApp "tmp" [TAtom "v89"]]; TApp "-" [TAtom "start"; TApp "tmp" [TAtom "v4"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.1"]; TAtom "p"; TList [TApp "-" [TAtom "L68"; TApp "tmp" [TAtom "v86"]]; TApp "-" [TAtom "start"; TApp "tmp" [TAtom "v2"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v19"]; TAtom "w"; TApp "cmp" [TAtom "ugt"; TAtom "l"]; TList [TApp "tmp" [TAtom "pr.2"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v19"]; TAtom "L16"; TAtom "L17"]];
        TApp "block" [TAtom "L16"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v24"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v24"]]];
            TApp "let" [TApp "tmp" [TAtom "v25"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "flight" [TApp "tmp" [TAtom "v27"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk2"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v27"]]];
            TApp "let" [TApp "tmp" [TAtom "v28"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk2"]]];
            TApp "let" [TApp "tmp" [TAtom "v29"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v25"]]];
            TApp "let" [TApp "tmp" [TAtom "v30"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v28"]]];
            TApp "let" [TApp "tmp" [TAtom "v31"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v29"]; TApp "tmp" [TAtom "v30"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v31"]; TAtom "L32"; TAtom "L33"]];
        TApp "block" [TAtom "L32"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v35"]; TAtom "w"]; TApp "global" [TAtom "__printf_buffer_flush"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]];
            TApp "let" [TApp "tmp" [TAtom "v36"]; TAtom "w"; TApp "ext" [TAtom "ub"]; TList [TApp "tmp" [TAtom "v35"]]];
            TApp "let" [TApp "tmp" [TAtom "v37"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v36"]; TApp "const" [TInt 0]]]];
          TApp "goto" [TAtom "L33"]];
        TApp "block" [TAtom "L33"; TList [TApp "phi" [TApp "tmp" [TAtom "v39"]; TAtom "w"; TList [TApp "-" [TAtom "L16"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L32"; TApp "tmp" [TAtom "v37"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v39"]; TAtom "L20"; TAtom "L22"]];
        TApp "block" [TAtom "L20"; TList [];
          TList [];
          TAtom "ret"];
        TApp "block" [TAtom "L22"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v45"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v45"]]];
            TApp "let" [TApp "tmp" [TAtom "v46"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk3"]]];
            TApp "flight" [TApp "tmp" [TAtom "v48"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk4"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v48"]]];
            TApp "let" [TApp "tmp" [TAtom "v49"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk4"]]];
            TApp "let" [TApp "tmp" [TAtom "v50"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v46"]]];
            TApp "let" [TApp "tmp" [TAtom "v51"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v49"]]];
            TApp "let" [TApp "tmp" [TAtom "v52"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v50"]; TApp "tmp" [TAtom "v51"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v52"]; TAtom "L43"; TAtom "L42"]];
        TApp "block" [TAtom "L42"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v53"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_write#str.41"]]];
            TApp "let" [TApp "tmp" [TAtom "v54"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_write#str.42"]]];
            TApp "let" [TApp "tmp" [TAtom "v55"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_write#str.43"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__libc_assert_fail"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v53"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v54"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 35]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v55"]]]]];
          TApp "goto" [TAtom "L43"]];
        TApp "block" [TAtom "L43"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v58"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk5"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v58"]]];
            TApp "let" [TApp "tmp" [TAtom "v59"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk5"]]];
            TApp "flight" [TApp "tmp" [TAtom "v61"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk6"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v61"]]];
            TApp "let" [TApp "tmp" [TAtom "v62"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk6"]]];
            TApp "let" [TApp "tmp" [TAtom "v63"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v59"]]];
            TApp "let" [TApp "tmp" [TAtom "v64"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v62"]]];
            TApp "let" [TApp "tmp" [TAtom "v65"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "v63"]; TApp "tmp" [TAtom "v64"]]];
            TApp "let" [TApp "tmp" [TAtom "v71"]; TAtom "w"; TApp "cmp" [TAtom "ugt"; TAtom "l"]; TList [TApp "tmp" [TAtom "v65"]; TApp "tmp" [TAtom "pr.2"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v71"]; TAtom "L68"; TAtom "L67"]];
        TApp "block" [TAtom "L67"; TList [];
          TList [];
          TApp "goto" [TAtom "L68"]];
        TApp "block" [TAtom "L68"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.3"]; TAtom "l"; TList [TApp "-" [TAtom "L67"; TApp "tmp" [TAtom "v65"]]; TApp "-" [TAtom "L43"; TApp "tmp" [TAtom "pr.2"]]]]];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v74"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v75"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk6"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v78"]; TAtom "p"]; TApp "global" [TAtom "__GI_memcpy"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v75"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.1"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "pr.3"]]]];
            TApp "let" [TApp "tmp" [TAtom "chk8"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v74"]]];
            TApp "let" [TApp "tmp" [TAtom "v81"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk8"]]];
            TApp "flight" [TApp "tmp" [TAtom "v83"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v81"]]; TApp "tmp" [TAtom "pr.3"]]; TApp "lower" [TApp "tmp" [TAtom "v81"]]];
            TApp "let" [TApp "tmp" [TAtom "chk9"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v74"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v83"]; TApp "tmp" [TAtom "chk9"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "v86"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.1"]]; TApp "tmp" [TAtom "pr.3"]]; TApp "lower" [TApp "tmp" [TAtom "pr.1"]]];
            TApp "let" [TApp "tmp" [TAtom "v89"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "pr.2"]; TApp "tmp" [TAtom "pr.3"]]]];
          TApp "goto" [TApp "poll" [TAtom "L15"]]];
        TApp "block" [TAtom "L17"; TList [];
          TList [];
          TAtom "ret"]]];
    TApp "func" [TAtom "__printf_buffer_flush"; TAtom "export"; TAtom "w"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_1.v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "iw_1.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v4"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_1.v4"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_1.v5"]; TAtom "L2"; TAtom "iw_2.start"]];
        TApp "block" [TAtom "L2"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 0]]];
        TApp "block" [TAtom "iw_2.start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_2.v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v4"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v30"]; TAtom "w"; TApp "cmp" [TAtom "ult"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 6]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v30"]; TAtom "iw_2.L31"; TAtom "iw_2.L32"]];
        TApp "block" [TAtom "iw_2.L9"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_snprintf"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L11"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___chk_fail"]; TList []]];
          TApp "goto" [TAtom "iw_2.L6"]];
        TApp "block" [TAtom "iw_2.L12"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_to_file"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L14"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_asprintf"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L16"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_dprintf"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L18"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v19"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_errno"]]];
            TApp "let" [TApp "tmp" [TAtom "chk2"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "iw_2.v19"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 7]; TApp "tmp" [TAtom "chk2"]];
            TApp "flight" [TApp "tmp" [TAtom "iw_2.iw_1.v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "iw_2.iw_1.v3"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk3"]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L21"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_fp"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L23"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_fp_to_wide"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L25"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_fphex_to_wide"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L27"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_flush_obstack"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "iw_3.start"]];
        TApp "block" [TAtom "iw_2.L31"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v33"]; TAtom "w"; TApp "cmp" [TAtom "ult"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 3]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v33"]; TAtom "iw_2.L34"; TAtom "iw_2.L35"]];
        TApp "block" [TAtom "iw_2.L34"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v36"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v36"]; TAtom "iw_3.start"; TAtom "iw_2.L37"]];
        TApp "block" [TAtom "iw_2.L37"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v38"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v38"]; TAtom "iw_3.start"; TAtom "iw_2.L39"]];
        TApp "block" [TAtom "iw_2.L39"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v40"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 2]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v40"]; TApp "poll" [TAtom "iw_2.L9"]; TAtom "iw_2.L6"]];
        TApp "block" [TAtom "iw_2.L35"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v42"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 3]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v42"]; TApp "poll" [TAtom "iw_2.L11"]; TAtom "iw_2.L43"]];
        TApp "block" [TAtom "iw_2.L43"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v44"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 4]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v44"]; TApp "poll" [TAtom "iw_2.L12"]; TAtom "iw_2.L45"]];
        TApp "block" [TAtom "iw_2.L45"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v46"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 5]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v46"]; TApp "poll" [TAtom "iw_2.L14"]; TAtom "iw_2.L6"]];
        TApp "block" [TAtom "iw_2.L32"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v48"]; TAtom "w"; TApp "cmp" [TAtom "ult"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 9]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v48"]; TAtom "iw_2.L49"; TAtom "iw_2.L50"]];
        TApp "block" [TAtom "iw_2.L49"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v51"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 6]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v51"]; TApp "poll" [TAtom "iw_2.L16"]; TAtom "iw_2.L52"]];
        TApp "block" [TAtom "iw_2.L52"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v53"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 7]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v53"]; TApp "poll" [TAtom "iw_2.L18"]; TAtom "iw_2.L54"]];
        TApp "block" [TAtom "iw_2.L54"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v55"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 8]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v55"]; TApp "poll" [TAtom "iw_2.L21"]; TAtom "iw_2.L6"]];
        TApp "block" [TAtom "iw_2.L50"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v57"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 9]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v57"]; TApp "poll" [TAtom "iw_2.L23"]; TAtom "iw_2.L58"]];
        TApp "block" [TAtom "iw_2.L58"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v59"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 10]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v59"]; TApp "poll" [TAtom "iw_2.L25"]; TAtom "iw_2.L60"]];
        TApp "block" [TAtom "iw_2.L60"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v61"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v4"]; TApp "const" [TInt 11]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v61"]; TApp "poll" [TAtom "iw_2.L27"]; TAtom "iw_2.L6"]];
        TApp "block" [TAtom "iw_2.L6"; TList [];
          TList [];
          TAtom "unreachable"];
        TApp "block" [TAtom "iw_3.start"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_3.v3"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk4"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "iw_3.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v4"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk4"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v5"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_3.v4"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_3.v5"]; TAtom "L13"; TAtom "L15"]];
        TApp "block" [TAtom "L13"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 0]]];
        TApp "block" [TAtom "L15"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v25"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk5"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v25"]]];
            TApp "let" [TApp "tmp" [TAtom "v26"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk5"]]];
            TApp "flight" [TApp "tmp" [TAtom "v28"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v29"]; TAtom "p"; TApp "raw_load_pointer" [TInt 8; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk5"]]];
            TApp "let" [TApp "tmp" [TAtom "v30"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v26"]]];
            TApp "let" [TApp "tmp" [TAtom "v31"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v29"]]];
            TApp "let" [TApp "tmp" [TAtom "v32"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v30"]; TApp "tmp" [TAtom "v31"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v32"]; TAtom "L23"; TAtom "L22"]];
        TApp "block" [TAtom "L22"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v33"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_flush#str.39"]]];
            TApp "let" [TApp "tmp" [TAtom "v34"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_flush#str.40"]]];
            TApp "let" [TApp "tmp" [TAtom "v35"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_printf_buffer_flush#str.41"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__libc_assert_fail"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v33"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v34"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 70]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v35"]]]]];
          TApp "goto" [TAtom "L23"]];
        TApp "block" [TAtom "L23"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 1]]]]]
  ]].

From Nanofil Require Import Syntax Transport Semantics.

(** Decoding gives the actual checked bodies used by instruction proofs. *)
Definition printf_buffer_io_module : module := Eval vm_compute in
  code_module printf_buffer_io_term.

(** Computation rules out the empty fallback in the decoded module. *)
Lemma printf_buffer_io_decodes : decode_module printf_buffer_io_term = Some printf_buffer_io_module.
Proof. vm_compute. reflexivity. Qed.

(** Function lookup selects a checked body without supplying its specification. *)
Definition printf_buffer_io_fn (n : string) : func :=
  code_function printf_buffer_io_module n.

(** This definition selects the checked body of [__printf_buffer_write]. *)
Definition glibc___printf_buffer_write : func := Eval vm_compute in
  printf_buffer_io_fn "__printf_buffer_write".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_io_find_printf_buffer_write :
  find_direct (TAtom "__printf_buffer_write") printf_buffer_io_module = Some (Defined glibc___printf_buffer_write).
Proof. vm_compute. reflexivity. Qed.

(** This definition selects the checked body of [__printf_buffer_flush]. *)
Definition glibc___printf_buffer_flush : func := Eval vm_compute in
  printf_buffer_io_fn "__printf_buffer_flush".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_io_find_printf_buffer_flush :
  find_direct (TAtom "__printf_buffer_flush") printf_buffer_io_module = Some (Defined glibc___printf_buffer_flush).
Proof. vm_compute. reflexivity. Qed.
