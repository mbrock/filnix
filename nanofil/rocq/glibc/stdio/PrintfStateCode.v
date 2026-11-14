(** These checked bodies implement cancellation-state changes and printf-buffer
    completion in user-glibc 2.44. The fixture supports instruction proofs
    without treating either function as an external contract.

    rocq/glibc/stdio/code.sh reproduces these terms from the pinned capture
    with gallina.pl. Regenerate this file rather than editing it. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** This term contains the selected checked function bodies. *)
Definition printf_state_term : term :=
  TApp "module" [TList [
    TApp "func" [TAtom "__GI___pthread_setcancelstate"; TAtom "export"; TAtom "w"; TList [TApp "param" [TAtom "w"; TApp "tmp" [TAtom "v0"]]; TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v2"]]];
      TList [
        TApp "block" [TAtom "start"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v9"]; TAtom "w"; TApp "cmp" [TAtom "slt"; TAtom "w"]; TList [TApp "tmp" [TAtom "v0"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v9"]; TAtom "L11"; TAtom "L10"]];
        TApp "block" [TAtom "L10"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v13"]; TAtom "w"; TApp "cmp" [TAtom "sgt"; TAtom "w"]; TList [TApp "tmp" [TAtom "v0"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TAtom "L11"]];
        TApp "block" [TAtom "L11"; TList [TApp "phi" [TApp "tmp" [TAtom "v15"]; TAtom "w"; TList [TApp "-" [TAtom "start"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L10"; TApp "tmp" [TAtom "v13"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v15"]; TAtom "L5"; TAtom "L7"]];
        TApp "block" [TAtom "L5"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 22]]];
        TApp "block" [TAtom "L7"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v17"]; TAtom "p"]; TApp "global" [TAtom "zthread_self_cookie"]; TList []];
            TApp "flight" [TApp "tmp" [TAtom "v20"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v17"]]; TApp "const" [TInt 792]]; TApp "lower" [TApp "tmp" [TAtom "v17"]]];
            TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v20"]]];
            TApp "let" [TApp "tmp" [TAtom "v21"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk0"]]]];
          TApp "goto" [TAtom "L22"]];
        TApp "block" [TAtom "L22"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.1"]; TAtom "w"; TList [TApp "-" [TAtom "L7"; TApp "tmp" [TAtom "v21"]]; TApp "-" [TAtom "L71"; TApp "tmp" [TAtom "pr.2"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v30"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v0"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v30"]; TAtom "L26"; TAtom "L27"]];
        TApp "block" [TAtom "L26"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v33"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "pr.1"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TAtom "L28"]];
        TApp "block" [TAtom "L27"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v37"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "pr.1"]; TApp "const" [TInt 4294967294]]]];
          TApp "goto" [TAtom "L28"]];
        TApp "block" [TAtom "L28"; TList [TApp "phi" [TApp "tmp" [TAtom "v38"]; TAtom "w"; TList [TApp "-" [TAtom "L26"; TApp "tmp" [TAtom "v33"]]; TApp "-" [TAtom "L27"; TApp "tmp" [TAtom "v37"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v43"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v44"]; TAtom "l"; TAtom "ptoi"; TList [TApp "const" [TInt 0]]];
            TApp "let" [TApp "tmp" [TAtom "v45"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v43"]; TApp "tmp" [TAtom "v44"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v45"]; TAtom "L39"; TAtom "L41"]];
        TApp "block" [TAtom "L39"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v52"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "pr.1"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v52"]; TAtom "L49"; TAtom "L48"]];
        TApp "block" [TAtom "L48"; TList [];
          TList [];
          TApp "goto" [TAtom "L49"]];
        TApp "block" [TAtom "L49"; TList [TApp "phi" [TApp "tmp" [TAtom "v53"]; TAtom "w"; TList [TApp "-" [TAtom "L48"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L39"; TApp "const" [TInt 1]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v53"]; TApp "tmp" [TAtom "chk1"]]];
          TApp "goto" [TAtom "L41"]];
        TApp "block" [TAtom "L41"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v59"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.1"]; TApp "tmp" [TAtom "v38"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v59"]; TAtom "L24"; TAtom "L56"]];
        TApp "block" [TAtom "L56"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v65"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v17"]]; TApp "const" [TInt 792]]; TApp "lower" [TApp "tmp" [TAtom "v17"]]];
            TApp "let" [TApp "tmp" [TAtom "chk2"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "write"; TInt 4]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v65"]]];
            TApp "let" [TApp "tmp" [TAtom "v68"]; TAtom "w"; TApp "raw_cas" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "pr.1"]; TApp "tmp" [TAtom "v38"]]];
            TApp "let" [TApp "tmp" [TAtom "v69"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v68"]; TApp "tmp" [TAtom "pr.1"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v69"]; TAtom "L71"; TAtom "L70"]];
        TApp "block" [TAtom "L70"; TList [];
          TList [];
          TApp "goto" [TAtom "L71"]];
        TApp "block" [TAtom "L71"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.2"]; TAtom "w"; TList [TApp "-" [TAtom "L56"; TApp "tmp" [TAtom "pr.1"]]; TApp "-" [TAtom "L70"; TApp "tmp" [TAtom "v68"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v69"]; TAtom "iw_1.start"; TApp "poll" [TAtom "L22"]]];
        TApp "block" [TAtom "iw_1.start"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_1.v12"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v38"]; TApp "const" [TInt 59]]];
            TApp "let" [TApp "tmp" [TAtom "iw_1.v16"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_1.v12"]; TApp "const" [TInt 10]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_1.v16"]; TAtom "L72"; TAtom "L24"]];
        TApp "block" [TAtom "L72"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v80"]; TAtom "copy"; TList [TApp "const" [TInt 18446744073709551615]]; TAtom "none"];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "iw_2.v3"]; TAtom "p"]; TApp "global" [TAtom "zthread_self_cookie"]; TList []];
            TApp "flight" [TApp "tmp" [TAtom "iw_2.v5"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "iw_2.v3"]]; TApp "const" [TInt 1608]]; TApp "lower" [TApp "tmp" [TAtom "iw_2.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "chk3"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "iw_2.v5"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v80"]; TApp "tmp" [TAtom "chk3"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "flight" [TApp "tmp" [TAtom "iw_2.v9"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "iw_2.v3"]]; TApp "const" [TInt 792]]; TApp "lower" [TApp "tmp" [TAtom "iw_2.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "chk4"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk3"]; TApp "tmp" [TAtom "iw_2.v9"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v10"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk4"]]]];
          TApp "goto" [TAtom "iw_2.L12"]];
        TApp "block" [TAtom "iw_2.L12"; TList [TApp "phi" [TApp "tmp" [TAtom "iw_2.pr.1"]; TAtom "w"; TList [TApp "-" [TAtom "iw_2.L38"; TApp "tmp" [TAtom "iw_2.pr.2"]]; TApp "-" [TAtom "L72"; TApp "tmp" [TAtom "iw_2.v10"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v17"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "iw_2.pr.1"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v19"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "iw_2.v17"]; TApp "const" [TInt 16]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v23"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "iw_2.v19"]; TApp "const" [TInt 4294967293]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v29"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.pr.1"]; TApp "tmp" [TAtom "iw_2.v23"]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v29"]; TAtom "iw_2.L14"; TAtom "iw_2.L13"]];
        TApp "block" [TAtom "iw_2.L13"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_2.v32"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "iw_2.v3"]]; TApp "const" [TInt 792]]; TApp "lower" [TApp "tmp" [TAtom "iw_2.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "chk5"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 4; TAtom "write"; TInt 4]; TList [TApp "tmp" [TAtom "chk3"]; TApp "tmp" [TAtom "iw_2.v32"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v35"]; TAtom "w"; TApp "raw_cas" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk5"]; TApp "tmp" [TAtom "iw_2.pr.1"]; TApp "tmp" [TAtom "iw_2.v23"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v36"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v35"]; TApp "tmp" [TAtom "iw_2.pr.1"]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v36"]; TAtom "iw_2.L38"; TAtom "iw_2.L37"]];
        TApp "block" [TAtom "iw_2.L37"; TList [];
          TList [];
          TApp "goto" [TAtom "iw_2.L38"]];
        TApp "block" [TAtom "iw_2.L38"; TList [TApp "phi" [TApp "tmp" [TAtom "iw_2.pr.2"]; TAtom "w"; TList [TApp "-" [TAtom "iw_2.L13"; TApp "tmp" [TAtom "iw_2.pr.1"]]; TApp "-" [TAtom "iw_2.L37"; TApp "tmp" [TAtom "iw_2.v35"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "iw_2.v39"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "iw_2.v35"]; TApp "tmp" [TAtom "iw_2.pr.1"]]]];
          TApp "branch" [TApp "tmp" [TAtom "iw_2.v39"]; TApp "poll" [TAtom "iw_2.L12"]; TAtom "iw_2.L14"]];
        TApp "block" [TAtom "iw_2.L14"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_2.v41"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "iw_2.v3"]]; TApp "const" [TInt 784]]; TApp "lower" [TApp "tmp" [TAtom "iw_2.v3"]]];
            TApp "let" [TApp "tmp" [TAtom "chk6"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk3"]; TApp "tmp" [TAtom "iw_2.v41"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_2.v42"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk6"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___pthread_unwind"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "iw_2.v42"]]]]];
          TApp "goto" [TAtom "L24"]];
        TApp "block" [TAtom "L24"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 0]]]]];
    TApp "func" [TAtom "__printf_buffer_done"; TAtom "export"; TAtom "w"; TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "v0"]]];
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
            TApp "flight" [TApp "tmp" [TAtom "v12"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "chk1"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v13"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk1"]]];
            TApp "let" [TApp "tmp" [TAtom "chk2"]; TAtom "a"; TApp "half_check" [TAtom "lower"; TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v15"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk2"]]];
            TApp "let" [TApp "tmp" [TAtom "v16"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v13"]]];
            TApp "let" [TApp "tmp" [TAtom "v17"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v15"]]];
            TApp "let" [TApp "tmp" [TAtom "v18"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "v16"]; TApp "tmp" [TAtom "v17"]]];
            TApp "flight" [TApp "tmp" [TAtom "v24"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v0"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "v0"]]];
            TApp "let" [TApp "tmp" [TAtom "v25"]; TAtom "l"; TApp "raw_load" [TAtom "l"; TInt (-8)]; TList [TApp "tmp" [TAtom "chk0"]]];
            TApp "let" [TApp "tmp" [TAtom "v27"]; TAtom "l"; TAtom "add"; TList [TApp "tmp" [TAtom "v25"]; TApp "tmp" [TAtom "v18"]]];
            TApp "let" [TApp "tmp" [TAtom "v28"]; TAtom "w"; TApp "cmp" [TAtom "ult"; TAtom "l"]; TList [TApp "tmp" [TAtom "v27"]; TApp "tmp" [TAtom "v25"]]];
            TApp "let" [TApp "tmp" [TAtom "v29"]; TAtom "l"; TApp "ext" [TAtom "uw"]; TList [TApp "tmp" [TAtom "v28"]]];
            TApp "let" [TApp "tmp" [TAtom "v32"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v27"]]];
            TApp "let" [TApp "tmp" [TAtom "v33"]; TAtom "l"; TAtom "sar"; TList [TApp "tmp" [TAtom "v32"]; TApp "const" [TInt 63]]];
            TApp "let" [TApp "tmp" [TAtom "v34"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v27"]; TApp "tmp" [TAtom "v32"]]];
            TApp "let" [TApp "tmp" [TAtom "v35"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v29"]; TApp "tmp" [TAtom "v33"]]];
            TApp "let" [TApp "tmp" [TAtom "v36"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v34"]; TApp "tmp" [TAtom "v35"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v36"]; TAtom "L20"; TAtom "L21"]];
        TApp "block" [TAtom "L20"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v37"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__libc_errno"]]];
            TApp "let" [TApp "tmp" [TAtom "chk4"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v37"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 75]; TApp "tmp" [TAtom "chk4"]]];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L21"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v40"]; TAtom "w"; TAtom "copy"; TList [TApp "tmp" [TAtom "v27"]]]];
          TApp "ret" [TApp "tmp" [TAtom "v40"]]]]]
  ]].

From Nanofil Require Import Syntax Transport Semantics.

(** Decoding gives the actual checked function bodies, not their specifications. *)
Definition printf_state_module : module := Eval vm_compute in
  code_module printf_state_term.

(** Computation checks that decoding did not take the empty fallback. *)
Lemma printf_state_decodes : decode_module printf_state_term = Some printf_state_module.
Proof. vm_compute. reflexivity. Qed.

(** Function lookup selects a decoded body for the subsequent instruction proofs. *)
Definition printf_state_fn (n : string) : func :=
  code_function printf_state_module n.

(** This body changes the thread's cancellation flag and optionally saves its old value. *)
Definition glibc___pthread_setcancelstate : func := Eval vm_compute in
  printf_state_fn "__GI___pthread_setcancelstate".

(** This body returns the accumulated count or reports failure and integer overflow. *)
Definition glibc___printf_buffer_done : func := Eval vm_compute in
  printf_state_fn "__printf_buffer_done".

(** Lookup finds the cancellation body rather than the empty fallback. *)
Lemma printf_state_find_cancel :
  find_direct (TAtom "__GI___pthread_setcancelstate") printf_state_module =
  Some (Defined glibc___pthread_setcancelstate).
Proof. vm_compute. reflexivity. Qed.

(** Lookup finds the completion body rather than the empty fallback. *)
Lemma printf_state_find_done :
  find_direct (TAtom "__printf_buffer_done") printf_state_module =
  Some (Defined glibc___printf_buffer_done).
Proof. vm_compute. reflexivity. Qed.
