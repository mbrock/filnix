(** Tap the λANF of Drive.v's [run] through CertiRocq's `-O 1 --anf-variant 8`
    pipeline, writing `AnfFrontend.Drive.run.ir` in the compilation directory.

    Besides the stdlib primitives registered in nanofil/anf/lower/Prims.v, the
    frontend registers its character-code, string-builder, and hash helpers to
    the same arena runtime functions used by nanofil/anf/backend/Tap.v. *)

From CertiRocq.Plugin Require Import CertiRocq.
From Frontend Require Import CLex CParse.
From AnfFrontend Require Import Prims Drive.

CertiRocq Register [
  CParse.env_string_hash => "nf_str_hash",
  CLex.code => "nf_id",
  CLex.byte => "nf_ascii_of_nat",
  CLex.string_of_rev => "nf_str_of_rev"
] Include [ "anf_prims.h" ].

CertiRocq Show IR -O 1 --anf-variant 8 run.
