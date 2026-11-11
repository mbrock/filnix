(** The λANF of Drive.v's [run], after CertiRocq's whole λANF pipeline
    with `-O 1 --anf-variant 8`, written by the tap
    (nix/certirocq-anf-tap.patch) to AnfBackend.Drive.run.ir in the
    directory run.sh compiles this file in.

    Besides the stdlib's constants that anf/lower/Prims.v registers, the
    backend's own string and character functions stay primitives: each
    computes what its Gallina definition does, on the represented
    strings and characters (anf/lower/anf_prims.c). *)

From CertiRocq.Plugin Require Import CertiRocq.
From Nanofil Require Import Maps.
From Backend Require Import Order IrText.
From AnfBackend Require Import Prims Drive.

CertiRocq Register [
  Maps.string_hash => "nf_str_hash", Order.atom_compare => "nf_str_compare",
  IrText.code => "nf_id", IrText.byte => "nf_ascii_of_nat",
  IrText.string_of_rev => "nf_str_of_rev"
] Include [ "anf_prims.h" ].

CertiRocq Show IR -O 1 --anf-variant 8 run.
