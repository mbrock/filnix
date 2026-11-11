(** The gate programs extracted to OCaml with Rocq's own extraction,
    no type mapped: the reference the arena's output must match byte
    for byte. Each program is extracted alone, so that its reference
    computes it only (run.sh writes the main that prints its bytes).
    The self-test's reference is its value as [vm_compute] computed
    it, [selftest_vm]. *)

From Stdlib Require Extraction.
From AnfTests Require Import Programs.

Extraction "ref_demo1.ml" demo1_out.
Extraction "ref_demo2.ml" demo2_out.
Extraction "ref_list_sum.ml" list_sum_out.
Extraction "ref_vs_easy.ml" vs_easy_out.
Extraction "ref_vs_hard.ml" vs_hard_out.
Extraction "ref_binom.ml" binom_out.
Extraction "ref_color.ml" color_out.
Extraction "ref_clos.ml" clos_out.
Extraction "ref_rec_clos.ml" rec_clos_out.
Extraction "ref_rec_clos2.ml" rec_clos2_out.
Extraction "ref_sha_fast.ml" sha_fast_out.
Extraction "ref_order.ml" order_out.
Extraction "ref_asm.ml" asm_out.
Extraction "ref_selftest.ml" selftest_vm.
