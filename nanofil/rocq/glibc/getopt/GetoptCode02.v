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
Definition getopt_blocks_02 : list term :=
  [
        TApp "block" [TAtom "L479"; TList [TApp "phi" [TApp "tmp" [TAtom "v484"]; TAtom "w"; TList [TApp "-" [TAtom "L478"; TApp "const" [TInt 63]]; TApp "-" [TAtom "L458"; TApp "const" [TInt 58]]]]];
          TList [];
          TApp "ret" [TApp "tmp" [TAtom "v484"]]];
        TApp "block" [TAtom "L398"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v489"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "let" [TApp "tmp" [TAtom "v491"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v489"]; TApp "tmp" [TAtom "v90"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v491"]; TAtom "L485"; TAtom "L487"]];
        TApp "block" [TAtom "L485"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk70"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v8"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "pr.12"]; TApp "tmp" [TAtom "chk70"]]];
          TApp "goto" [TAtom "L487"]];
        TApp "block" [TAtom "L487"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v498"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "chk71"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v498"]]];
            TApp "let" [TApp "tmp" [TAtom "v499"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk71"]]];
            TApp "let" [TApp "tmp" [TAtom "v500"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v499"]]];
            TApp "let" [TApp "tmp" [TAtom "v501"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v500"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v501"]; TAtom "L494"; TAtom "L496"]];
        TApp "block" [TAtom "L494"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v503"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "v504"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk71"]]];
            TApp "flight" [TApp "tmp" [TAtom "v506"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "chk73"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk71"]; TApp "tmp" [TAtom "v506"]]];
            TApp "let" [TApp "tmp" [TAtom "v507"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk73"]]];
            TApp "let" [TApp "tmp" [TAtom "chk74"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v504"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v507"]; TApp "tmp" [TAtom "chk74"]]];
          TApp "ret" [TApp "const" [TInt 0]]];
        TApp "block" [TAtom "L496"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v510"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "pr.7"]]; TApp "const" [TInt 24]]; TApp "lower" [TApp "tmp" [TAtom "pr.7"]]];
            TApp "let" [TApp "tmp" [TAtom "chk75"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk71"]; TApp "tmp" [TAtom "v510"]]];
            TApp "let" [TApp "tmp" [TAtom "v511"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk75"]]]];
          TApp "ret" [TApp "tmp" [TAtom "v511"]]]
  ].
