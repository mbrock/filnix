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
Definition getopt_blocks_05 : list term :=
  [
        TApp "block" [TAtom "iw_3.L18"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "iw_3.v144"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 44]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk88"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk73"]; TApp "tmp" [TAtom "iw_3.v144"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v145"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk88"]]];
            TApp "let" [TApp "tmp" [TAtom "chk89"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v147"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk89"]]];
            TApp "flight" [TApp "tmp" [TAtom "iw_3.v149"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk90"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk23"]; TApp "tmp" [TAtom "iw_3.v149"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v150"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk90"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v151"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "iw_3.v147"]; TApp "tmp" [TAtom "iw_3.v150"]]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v152"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "iw_3.v145"]; TApp "tmp" [TAtom "iw_3.v151"]]];
            TApp "let" [TApp "tmp" [TAtom "chk91"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk73"]; TApp "tmp" [TAtom "iw_3.v144"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "iw_3.v152"]; TApp "tmp" [TAtom "chk91"]];
            TApp "let" [TApp "tmp" [TAtom "iw_3.v156"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk89"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "iw_3.v156"]; TApp "tmp" [TAtom "chk90"]]];
          TApp "goto" [TAtom "L227"]];
        TApp "block" [TAtom "L226"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v251"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 44]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v252"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk73"]]];
            TApp "flight" [TApp "tmp" [TAtom "v254"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v255"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk74"]]];
            TApp "let" [TApp "tmp" [TAtom "v256"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v252"]; TApp "tmp" [TAtom "v255"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v256"]; TAtom "L247"; TAtom "L227"]];
        TApp "block" [TAtom "L247"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v258"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 44]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v260"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk72"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v260"]; TApp "tmp" [TAtom "chk73"]]];
          TApp "goto" [TAtom "L227"]];
        TApp "block" [TAtom "L227"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v262"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk98"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk23"]; TApp "tmp" [TAtom "v262"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v0"]; TApp "tmp" [TAtom "chk98"]];
            TApp "let" [TApp "tmp" [TAtom "chk99"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v0"]; TApp "tmp" [TAtom "chk99"]]];
          TApp "goto" [TAtom "L203"]];
        TApp "block" [TAtom "L203"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk100"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v270"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk100"]]];
            TApp "let" [TApp "tmp" [TAtom "v272"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v270"]; TApp "tmp" [TAtom "v0"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v272"]; TAtom "L266"; TAtom "L268"]];
        TApp "block" [TAtom "L266"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v277"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 44]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk101"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v277"]]];
            TApp "let" [TApp "tmp" [TAtom "v278"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk101"]]];
            TApp "flight" [TApp "tmp" [TAtom "v280"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 48]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk102"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk23"]; TApp "tmp" [TAtom "v280"]]];
            TApp "let" [TApp "tmp" [TAtom "v281"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk102"]]];
            TApp "let" [TApp "tmp" [TAtom "v282"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v278"]; TApp "tmp" [TAtom "v281"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v282"]; TAtom "L273"; TAtom "L275"]];
        TApp "block" [TAtom "L273"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v285"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 44]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v286"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk101"]]];
            TApp "let" [TApp "tmp" [TAtom "chk104"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v286"]; TApp "tmp" [TAtom "chk104"]]];
          TApp "goto" [TAtom "L275"]];
        TApp "block" [TAtom "L275"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L268"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v294"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk100"]]];
            TApp "let" [TApp "tmp" [TAtom "v295"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v294"]]];
            TApp "let" [TApp "tmp" [TAtom "v296"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v295"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v297"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v296"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk106"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v297"]]];
            TApp "let" [TApp "tmp" [TAtom "v298"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk106"]]];
            TApp "let" [TApp "tmp" [TAtom "chk107"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v298"]]];
            TApp "let" [TApp "tmp" [TAtom "v300"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk107"]]];
            TApp "let" [TApp "tmp" [TAtom "v301"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v300"]; TApp "const" [TInt 45]]]];
          TApp "branch" [TApp "tmp" [TAtom "v301"]; TAtom "L303"; TAtom "L302"]];
        TApp "block" [TAtom "L302"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v306"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk100"]]];
            TApp "let" [TApp "tmp" [TAtom "v307"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v306"]]];
            TApp "let" [TApp "tmp" [TAtom "v308"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v307"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v309"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v308"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk109"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v309"]]];
            TApp "let" [TApp "tmp" [TAtom "v310"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk109"]]];
            TApp "flight" [TApp "tmp" [TAtom "v311"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v310"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v310"]]];
            TApp "let" [TApp "tmp" [TAtom "chk110"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v311"]]];
            TApp "let" [TApp "tmp" [TAtom "v312"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk110"]]];
            TApp "let" [TApp "tmp" [TAtom "v313"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v312"]; TApp "const" [TInt 0]]]];
          TApp "goto" [TAtom "L303"]];
        TApp "block" [TAtom "L303"; TList [TApp "phi" [TApp "tmp" [TAtom "v315"]; TAtom "w"; TList [TApp "-" [TAtom "L268"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L302"; TApp "tmp" [TAtom "v313"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v315"]; TAtom "L289"; TAtom "L291"]];
        TApp "block" [TAtom "L289"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v320"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 40]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk111"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v320"]]];
            TApp "let" [TApp "tmp" [TAtom "v321"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk111"]]];
            TApp "let" [TApp "tmp" [TAtom "v322"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v321"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v322"]; TAtom "L316"; TAtom "L318"]];
        TApp "block" [TAtom "L316"; TList [];
          TList [];
          TApp "ret" [TApp "const" [TInt 4294967295]]];
        TApp "block" [TAtom "L318"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v326"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v329"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk100"]]];
            TApp "let" [TApp "tmp" [TAtom "v330"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v329"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk113"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v330"]; TApp "tmp" [TAtom "chk113"]];
            TApp "let" [TApp "tmp" [TAtom "v331"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v329"]]];
            TApp "let" [TApp "tmp" [TAtom "v332"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v331"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v333"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v332"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk114"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v333"]]];
            TApp "let" [TApp "tmp" [TAtom "v334"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk114"]]];
            TApp "let" [TApp "tmp" [TAtom "chk115"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v326"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v334"]; TApp "tmp" [TAtom "chk115"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "ret" [TApp "const" [TInt 1]]];
        TApp "block" [TAtom "L291"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v340"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v6"]]];
            TApp "let" [TApp "tmp" [TAtom "v341"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v340"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v341"]; TAtom "L336"; TAtom "L338"]];
        TApp "block" [TAtom "L336"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v347"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk100"]]];
            TApp "let" [TApp "tmp" [TAtom "v348"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v347"]]];
            TApp "let" [TApp "tmp" [TAtom "v349"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v348"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v350"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v349"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk117"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v350"]]];
            TApp "let" [TApp "tmp" [TAtom "v351"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk117"]]];
            TApp "flight" [TApp "tmp" [TAtom "v352"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v351"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v351"]]];
            TApp "let" [TApp "tmp" [TAtom "chk118"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v352"]]];
            TApp "let" [TApp "tmp" [TAtom "v353"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk118"]]];
            TApp "let" [TApp "tmp" [TAtom "v354"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v353"]; TApp "const" [TInt 45]]]];
          TApp "branch" [TApp "tmp" [TAtom "v354"]; TAtom "L342"; TAtom "L344"]];
        TApp "block" [TAtom "L342"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v356"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v359"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk100"]]];
            TApp "let" [TApp "tmp" [TAtom "v360"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v359"]]];
            TApp "let" [TApp "tmp" [TAtom "v361"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v360"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v362"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v361"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk120"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v362"]]];
            TApp "let" [TApp "tmp" [TAtom "v363"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk120"]]];
            TApp "flight" [TApp "tmp" [TAtom "v364"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v363"]]; TApp "const" [TInt 2]]; TApp "lower" [TApp "tmp" [TAtom "v363"]]];
            TApp "let" [TApp "tmp" [TAtom "chk121"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v356"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v364"]; TApp "tmp" [TAtom "chk121"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "v373"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.146"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v374"]; TAtom "w"]; TApp "global" [TAtom "glibc_getopt#process_long_option"]; TList [TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.1"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v6"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v8"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v10"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v12"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "pr.3"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v373"]]]]];
          TApp "ret" [TApp "tmp" [TAtom "v374"]]];
        TApp "block" [TAtom "L344"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v10"]; TAtom "L380"; TAtom "L381"]];
        TApp "block" [TAtom "L380"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v384"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk100"]]];
            TApp "let" [TApp "tmp" [TAtom "v385"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v384"]]];
            TApp "let" [TApp "tmp" [TAtom "v386"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v385"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v387"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v386"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk123"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v387"]]];
            TApp "let" [TApp "tmp" [TAtom "v388"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk123"]]];
            TApp "flight" [TApp "tmp" [TAtom "v389"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v388"]]; TApp "const" [TInt 2]]; TApp "lower" [TApp "tmp" [TAtom "v388"]]];
            TApp "let" [TApp "tmp" [TAtom "chk124"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v389"]]];
            TApp "let" [TApp "tmp" [TAtom "v390"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk124"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v390"]; TAtom "L381"; TAtom "L391"]];
        TApp "block" [TAtom "L391"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v396"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk100"]]];
            TApp "let" [TApp "tmp" [TAtom "v397"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v396"]]];
            TApp "let" [TApp "tmp" [TAtom "v398"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v397"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v399"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v398"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk126"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v399"]]];
            TApp "let" [TApp "tmp" [TAtom "v400"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk126"]]];
            TApp "flight" [TApp "tmp" [TAtom "v401"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v400"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v400"]]];
            TApp "let" [TApp "tmp" [TAtom "chk127"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v401"]]];
            TApp "let" [TApp "tmp" [TAtom "v402"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk127"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v403"]; TAtom "p"]; TApp "global" [TAtom "__GI_strchr"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.1"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v402"]]]];
            TApp "let" [TApp "tmp" [TAtom "v404"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v403"]]];
            TApp "let" [TApp "tmp" [TAtom "v406"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v404"]; TApp "const" [TInt 0]]]];
          TApp "goto" [TAtom "L381"]];
        TApp "block" [TAtom "L381"; TList [TApp "phi" [TApp "tmp" [TAtom "v410"]; TAtom "w"; TList [TApp "-" [TAtom "L344"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L380"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L391"; TApp "tmp" [TAtom "v406"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v410"]; TAtom "L376"; TAtom "L338"]];
        TApp "block" [TAtom "L376"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v413"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk128"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v416"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk128"]]];
            TApp "let" [TApp "tmp" [TAtom "v417"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v416"]]];
            TApp "let" [TApp "tmp" [TAtom "v418"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v417"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v419"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v418"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk129"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v419"]]];
            TApp "let" [TApp "tmp" [TAtom "v420"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk129"]]];
            TApp "flight" [TApp "tmp" [TAtom "v421"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v420"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v420"]]];
            TApp "let" [TApp "tmp" [TAtom "chk130"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v413"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v421"]; TApp "tmp" [TAtom "chk130"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "v430"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.147"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v431"]; TAtom "w"]; TApp "global" [TAtom "glibc_getopt#process_long_option"]; TList [TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.1"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v6"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v8"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v10"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v12"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "pr.3"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v430"]]]];
            TApp "let" [TApp "tmp" [TAtom "v437"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v431"]; TApp "const" [TInt 4294967295]]]];
          TApp "branch" [TApp "tmp" [TAtom "v437"]; TAtom "L432"; TAtom "L338"]];
        TApp "block" [TAtom "L432"; TList [];
          TList [];
          TApp "ret" [TApp "tmp" [TAtom "v431"]]];
        TApp "block" [TAtom "L338"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v441"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk131"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v444"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk131"]]];
            TApp "let" [TApp "tmp" [TAtom "v445"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v444"]]];
            TApp "let" [TApp "tmp" [TAtom "v446"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v445"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v447"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v446"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk132"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v447"]]];
            TApp "let" [TApp "tmp" [TAtom "v448"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk132"]]];
            TApp "flight" [TApp "tmp" [TAtom "v449"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v448"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v448"]]];
            TApp "let" [TApp "tmp" [TAtom "chk133"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v441"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v449"]; TApp "tmp" [TAtom "chk133"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L75"]];
        TApp "block" [TAtom "L75"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v452"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk134"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v452"]]];
            TApp "let" [TApp "tmp" [TAtom "v453"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk134"]]];
            TApp "flight" [TApp "tmp" [TAtom "v454"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v453"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v453"]]];
            TApp "let" [TApp "tmp" [TAtom "chk135"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v452"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v454"]; TApp "tmp" [TAtom "chk135"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk136"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v453"]]];
            TApp "let" [TApp "tmp" [TAtom "v455"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk136"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v459"]; TAtom "p"]; TApp "global" [TAtom "__GI_strchr"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.1"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v455"]]]];
            TApp "let" [TApp "tmp" [TAtom "chk137"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v452"]]];
            TApp "let" [TApp "tmp" [TAtom "v465"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk137"]]];
            TApp "let" [TApp "tmp" [TAtom "chk138"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v465"]]];
            TApp "let" [TApp "tmp" [TAtom "v466"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk138"]]];
            TApp "let" [TApp "tmp" [TAtom "v467"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v466"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v467"]; TAtom "L460"; TAtom "L462"]];
        TApp "block" [TAtom "L460"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk139"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v469"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk139"]]];
            TApp "let" [TApp "tmp" [TAtom "v470"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v469"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk140"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v470"]; TApp "tmp" [TAtom "chk140"]]];
          TApp "goto" [TAtom "L462"]];
        TApp "block" [TAtom "L462"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v475"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v459"]]];
            TApp "let" [TApp "tmp" [TAtom "v477"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v475"]; TApp "tmp" [TAtom "v80"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v477"]; TAtom "L479"; TAtom "L478"]];
        TApp "block" [TAtom "L478"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v481"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v455"]; TApp "const" [TInt 58]]]];
          TApp "goto" [TAtom "L479"]];
        TApp "block" [TAtom "L479"; TList [TApp "phi" [TApp "tmp" [TAtom "v483"]; TAtom "w"; TList [TApp "-" [TAtom "L462"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L478"; TApp "tmp" [TAtom "v481"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v483"]; TAtom "L485"; TAtom "L484"]];
        TApp "block" [TAtom "L484"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v487"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v455"]; TApp "const" [TInt 59]]]];
          TApp "goto" [TAtom "L485"]];
        TApp "block" [TAtom "L485"; TList [TApp "phi" [TApp "tmp" [TAtom "v489"]; TAtom "w"; TList [TApp "-" [TAtom "L479"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L484"; TApp "tmp" [TAtom "v487"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v489"]; TAtom "L471"; TAtom "L473"]];
        TApp "block" [TAtom "L471"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.3"]; TAtom "L490"; TAtom "L492"]];
        TApp "block" [TAtom "L490"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v494"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk141"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v494"]]];
            TApp "let" [TApp "tmp" [TAtom "v495"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk141"]]];
            TApp "let" [TApp "tmp" [TAtom "v496"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__GI__libc_intl_domainname"]]];
            TApp "let" [TApp "tmp" [TAtom "v497"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.148"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v498"]; TAtom "p"]; TApp "global" [TAtom "__GI___dcgettext"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v496"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v497"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 5]]]];
            TApp "let" [TApp "tmp" [TAtom "chk142"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v501"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk142"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v503"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v495"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v498"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v501"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v455"]]]]];
          TApp "goto" [TAtom "L492"]];
        TApp "block" [TAtom "L492"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v505"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk143"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v505"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v455"]; TApp "tmp" [TAtom "chk143"]]];
          TApp "ret" [TApp "const" [TInt 63]]];
        TApp "block" [TAtom "L473"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk144"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v459"]]];
            TApp "let" [TApp "tmp" [TAtom "v513"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk144"]]];
            TApp "let" [TApp "tmp" [TAtom "v514"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v513"]; TApp "const" [TInt 87]]]];
          TApp "branch" [TApp "tmp" [TAtom "v514"]; TAtom "L515"; TAtom "L516"]];
        TApp "block" [TAtom "L515"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v518"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v459"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v459"]]];
            TApp "let" [TApp "tmp" [TAtom "chk145"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk144"]; TApp "tmp" [TAtom "v518"]]];
            TApp "let" [TApp "tmp" [TAtom "v519"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk145"]]];
            TApp "let" [TApp "tmp" [TAtom "v520"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v519"]; TApp "const" [TInt 59]]]];
          TApp "goto" [TAtom "L516"]];
        TApp "block" [TAtom "L516"; TList [TApp "phi" [TApp "tmp" [TAtom "v522"]; TAtom "w"; TList [TApp "-" [TAtom "L473"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L515"; TApp "tmp" [TAtom "v520"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v522"]; TAtom "L523"; TAtom "L524"]];
        TApp "block" [TAtom "L523"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v526"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v6"]]];
            TApp "let" [TApp "tmp" [TAtom "v528"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v526"]; TApp "tmp" [TAtom "v80"]]]];
          TApp "goto" [TAtom "L524"]];
        TApp "block" [TAtom "L524"; TList [TApp "phi" [TApp "tmp" [TAtom "v530"]; TAtom "w"; TList [TApp "-" [TAtom "L516"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L523"; TApp "tmp" [TAtom "v528"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v530"]; TAtom "L508"; TAtom "L510"]];
        TApp "block" [TAtom "L508"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v535"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v536"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk137"]]];
            TApp "let" [TApp "tmp" [TAtom "chk147"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v536"]]];
            TApp "let" [TApp "tmp" [TAtom "v537"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk147"]]];
            TApp "let" [TApp "tmp" [TAtom "v538"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v537"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v538"]; TAtom "L531"; TAtom "L532"]];
        TApp "block" [TAtom "L531"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v540"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "flight" [TApp "tmp" [TAtom "v542"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v543"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk137"]]];
            TApp "let" [TApp "tmp" [TAtom "chk149"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v540"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v543"]; TApp "tmp" [TAtom "chk149"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L533"]];
        TApp "block" [TAtom "L532"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk150"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v548"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk150"]]];
            TApp "let" [TApp "tmp" [TAtom "v550"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v548"]; TApp "tmp" [TAtom "v0"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v550"]; TAtom "L544"; TAtom "L545"]];
        TApp "block" [TAtom "L544"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.3"]; TAtom "L551"; TAtom "L553"]];
        TApp "block" [TAtom "L551"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v555"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk151"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v555"]]];
            TApp "let" [TApp "tmp" [TAtom "v556"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk151"]]];
            TApp "let" [TApp "tmp" [TAtom "v557"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__GI__libc_intl_domainname"]]];
            TApp "let" [TApp "tmp" [TAtom "v558"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.149"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v559"]; TAtom "p"]; TApp "global" [TAtom "__GI___dcgettext"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v557"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v558"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 5]]]];
            TApp "let" [TApp "tmp" [TAtom "chk152"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v562"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk152"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v564"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v556"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v559"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v562"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v455"]]]]];
          TApp "goto" [TAtom "L553"]];
        TApp "block" [TAtom "L553"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v566"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk153"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v566"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v455"]; TApp "tmp" [TAtom "chk153"]];
            TApp "let" [TApp "tmp" [TAtom "chk154"]; TAtom "a"; TApp "renew" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "pr.1"]]];
            TApp "let" [TApp "tmp" [TAtom "v573"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk154"]]];
            TApp "let" [TApp "tmp" [TAtom "v574"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v573"]; TApp "const" [TInt 58]]]];
          TApp "branch" [TApp "tmp" [TAtom "v574"]; TAtom "L570"; TAtom "L569"]];
        TApp "block" [TAtom "L569"; TList [];
          TList [];
          TApp "goto" [TAtom "L570"]];
        TApp "block" [TAtom "L570"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.4"]; TAtom "w"; TList [TApp "-" [TAtom "L569"; TApp "const" [TInt 63]]; TApp "-" [TAtom "L553"; TApp "const" [TInt 58]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v575"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "pr.4"]]]];
          TApp "ret" [TApp "tmp" [TAtom "v575"]]];
        TApp "block" [TAtom "L545"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v578"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v581"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk150"]]];
            TApp "let" [TApp "tmp" [TAtom "v582"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v581"]]];
            TApp "let" [TApp "tmp" [TAtom "v583"]; TAtom "l"; TAtom "shl"; TList [TApp "tmp" [TAtom "v582"]; TApp "const" [TInt 3]]];
            TApp "flight" [TApp "tmp" [TAtom "v584"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v2"]]; TApp "tmp" [TAtom "v583"]]; TApp "lower" [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "chk156"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v584"]]];
            TApp "let" [TApp "tmp" [TAtom "v585"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk156"]]];
            TApp "let" [TApp "tmp" [TAtom "chk157"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v578"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v585"]; TApp "tmp" [TAtom "chk157"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L533"]];
        TApp "block" [TAtom "L533"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v587"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "flight" [TApp "tmp" [TAtom "v589"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk158"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v589"]]];
            TApp "let" [TApp "tmp" [TAtom "v590"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk158"]]];
            TApp "let" [TApp "tmp" [TAtom "chk159"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v587"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v590"]; TApp "tmp" [TAtom "chk159"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk160"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v589"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk160"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "v600"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.150"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v601"]; TAtom "w"]; TApp "global" [TAtom "glibc_getopt#process_long_option"]; TList [TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.1"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v6"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v8"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 0]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v12"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "pr.3"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v600"]]]]];
          TApp "ret" [TApp "tmp" [TAtom "v601"]]];
        TApp "block" [TAtom "L510"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v607"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v459"]]; TApp "const" [TInt 1]]; TApp "lower" [TApp "tmp" [TAtom "v459"]]];
            TApp "let" [TApp "tmp" [TAtom "chk161"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk144"]; TApp "tmp" [TAtom "v607"]]];
            TApp "let" [TApp "tmp" [TAtom "v608"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk161"]]];
            TApp "let" [TApp "tmp" [TAtom "v609"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v608"]; TApp "const" [TInt 58]]]];
          TApp "branch" [TApp "tmp" [TAtom "v609"]; TAtom "L603"; TAtom "L605"]];
        TApp "block" [TAtom "L603"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v614"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v459"]]; TApp "const" [TInt 2]]; TApp "lower" [TApp "tmp" [TAtom "v459"]]];
            TApp "let" [TApp "tmp" [TAtom "chk162"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk144"]; TApp "tmp" [TAtom "v614"]]];
            TApp "let" [TApp "tmp" [TAtom "v615"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk162"]]];
            TApp "let" [TApp "tmp" [TAtom "v616"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v615"]; TApp "const" [TInt 58]]]];
          TApp "branch" [TApp "tmp" [TAtom "v616"]; TAtom "L610"; TAtom "L611"]];
        TApp "block" [TAtom "L610"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v621"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v622"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk137"]]];
            TApp "let" [TApp "tmp" [TAtom "chk164"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v622"]]];
            TApp "let" [TApp "tmp" [TAtom "v623"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk164"]]];
            TApp "let" [TApp "tmp" [TAtom "v624"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v623"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v624"]; TAtom "L617"; TAtom "L618"]];
        TApp "block" [TAtom "L617"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v626"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "flight" [TApp "tmp" [TAtom "v628"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v629"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk137"]]];
            TApp "let" [TApp "tmp" [TAtom "chk166"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v626"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v629"]; TApp "tmp" [TAtom "chk166"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk167"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v631"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk167"]]];
            TApp "let" [TApp "tmp" [TAtom "v632"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v631"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk168"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v632"]; TApp "tmp" [TAtom "chk168"]]];
          TApp "goto" [TAtom "L619"]];
        TApp "block" [TAtom "L618"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v634"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk169"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v634"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk169"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L619"]];
        TApp "block" [TAtom "L619"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v636"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk170"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk20"]; TApp "tmp" [TAtom "v636"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk170"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]]];
          TApp "goto" [TAtom "L605"]];
        TApp "block" [TAtom "L611"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v641"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v642"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk137"]]];
            TApp "let" [TApp "tmp" [TAtom "chk172"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "v642"]]];
            TApp "let" [TApp "tmp" [TAtom "v643"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk172"]]];
            TApp "let" [TApp "tmp" [TAtom "v644"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v643"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v644"]; TAtom "L637"; TAtom "L638"]];
        TApp "block" [TAtom "L637"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v646"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "flight" [TApp "tmp" [TAtom "v648"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 32]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v649"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk137"]]];
            TApp "let" [TApp "tmp" [TAtom "chk174"]; TAtom "a"; TApp "renew" [TInt 0; TInt 8; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "chk1"]; TApp "tmp" [TAtom "v646"]]];
            TApp "raw_store_pointer" [TInt 0; TApp "tmp" [TAtom "v649"]; TApp "tmp" [TAtom "chk174"]; TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]];
            TApp "let" [TApp "tmp" [TAtom "chk175"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v651"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk175"]]];
            TApp "let" [TApp "tmp" [TAtom "v652"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "v651"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "chk176"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v652"]; TApp "tmp" [TAtom "chk176"]]];
          TApp "goto" [TAtom "L639"]];
        TApp "block" [TAtom "L638"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk177"]; TAtom "a"; TApp "renew" [TInt 0; TInt 4; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk2"]; TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "v657"]; TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0]; TList [TApp "tmp" [TAtom "chk177"]]];
            TApp "let" [TApp "tmp" [TAtom "v659"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v657"]; TApp "tmp" [TAtom "v0"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v659"]; TAtom "L653"; TAtom "L654"]];
        TApp "block" [TAtom "L653"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.3"]; TAtom "L660"; TAtom "L662"]];
        TApp "block" [TAtom "L660"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v664"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "stderr"]]];
            TApp "let" [TApp "tmp" [TAtom "chk178"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v664"]]];
            TApp "let" [TApp "tmp" [TAtom "v665"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk178"]]];
            TApp "let" [TApp "tmp" [TAtom "v666"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "__GI__libc_intl_domainname"]]];
            TApp "let" [TApp "tmp" [TAtom "v667"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_getopt#str.149"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v668"]; TAtom "p"]; TApp "global" [TAtom "__GI___dcgettext"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v666"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v667"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 5]]]];
            TApp "let" [TApp "tmp" [TAtom "chk179"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]; TList [TApp "tmp" [TAtom "v2"]]];
            TApp "let" [TApp "tmp" [TAtom "v671"]; TAtom "p"; TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]]; TList [TApp "tmp" [TAtom "chk179"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v673"]; TAtom "w"]; TApp "global" [TAtom "__fxprintf_nocancel"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v665"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v668"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v671"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v455"]]]]];
          TApp "goto" [TAtom "L662"]];
        TApp "block" [TAtom "L662"; TList [];
          TList [
            TApp "flight" [TApp "tmp" [TAtom "v675"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v12"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v12"]]];
            TApp "let" [TApp "tmp" [TAtom "chk180"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk0"]; TApp "tmp" [TAtom "v675"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v455"]; TApp "tmp" [TAtom "chk180"]];
            TApp "let" [TApp "tmp" [TAtom "chk181"]; TAtom "a"; TApp "renew" [TInt 0; TInt 1; TAtom "read"; TInt 1]; TList [TApp "tmp" [TAtom "chk19"]; TApp "tmp" [TAtom "pr.1"]]];
            TApp "let" [TApp "tmp" [TAtom "v682"]; TAtom "w"; TApp "raw_load" [TAtom "sb"; TInt 0]; TList [TApp "tmp" [TAtom "chk181"]]];
            TApp "let" [TApp "tmp" [TAtom "v683"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "v682"]; TApp "const" [TInt 58]]]];
          TApp "branch" [TApp "tmp" [TAtom "v683"]; TAtom "L639"; TAtom "L678"]];
        TApp "block" [TAtom "L678"; TList [];
          TList [];
          TApp "goto" [TAtom "L639"]]
  ].
