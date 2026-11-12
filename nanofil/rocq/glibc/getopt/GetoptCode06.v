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
Definition getopt_blocks_06 : list term :=
  [
        TApp "block" [TAtom "L654"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v685"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v688"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk177"]]];
            TApp "let" [TApp "tmp" [TAtom "v689"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v688"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk183"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v689"]; TApp "tmp" [TAtom "chk183"]];
            TApp "let" [TApp "tmp" [TAtom "v690"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v688"]]];
            TApp "let" [TApp "tmp" [TAtom "v691"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v690"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v692"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v691"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk184"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v692"]]];
            TApp "let" [TApp "tmp" [TAtom "v693"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk184"]]];
            TApp "let" [TApp "tmp" [TAtom "chk185"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v685"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v693"]; TApp "tmp" [TAtom "chk185"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L639"]];
        TApp "block" [TAtom "L639"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.7"]; TAtom "w"; TList [TApp "-" [TAtom "L637"; TApp "tmp" [TAtom "v455"]]; TApp "-" [TAtom "L654"; TApp "tmp" [TAtom "v455"]]; TApp "-" [TAtom "L678"; TApp "const" [TInt 63]]; TApp "-" [TAtom "L662"; TApp "const" [TInt 58]]]]];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v695"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk186"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v695"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk186"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L605"]];
        TApp "block" [TAtom "L605"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.5"]; TAtom "w"; TList [TApp "-" [TAtom "L619"; TApp "tmp" [TAtom "v455"]]; TApp "-" [TAtom "L639"; TApp "tmp" [TAtom "pr.7"]]; TApp "-" [TAtom "L510"; TApp "tmp" [TAtom "v455"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v696"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "pr.5"]]]];
          TApp "ret" [TApp "tmp" [TAtom "v696"]]]
  ].
