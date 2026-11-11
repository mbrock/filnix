(** Each gate program's λANF, after CertiRocq's whole λANF pipeline
    with `-O 1 --anf-variant 8`, written by the tap
    (nix/certirocq-anf-tap.patch) to PROGRAM.ir in the build
    directory run.sh sets. The stdlib's constants that Prims.v
    registers stay primitives, which the lowering realizes. *)

From CertiRocq.Plugin Require Import CertiRocq.
From AnfTests Require Import Prims Programs.

CertiRocq Show IR -O 1 --anf-variant 8 demo1_out.
CertiRocq Show IR -O 1 --anf-variant 8 demo2_out.
CertiRocq Show IR -O 1 --anf-variant 8 list_sum_out.
CertiRocq Show IR -O 1 --anf-variant 8 vs_easy_out.
CertiRocq Show IR -O 1 --anf-variant 8 vs_hard_out.
CertiRocq Show IR -O 1 --anf-variant 8 binom_out.
CertiRocq Show IR -O 1 --anf-variant 8 color_out.
CertiRocq Show IR -O 1 --anf-variant 8 clos_out.
CertiRocq Show IR -O 1 --anf-variant 8 rec_clos_out.
CertiRocq Show IR -O 1 --anf-variant 8 rec_clos2_out.
CertiRocq Show IR -O 1 --anf-variant 8 sha_fast_out.
CertiRocq Show IR -O 1 --anf-variant 8 order_out.
CertiRocq Show IR -O 1 --anf-variant 8 asm_out.
CertiRocq Show IR -O 1 --anf-variant 8 selftest_out.
