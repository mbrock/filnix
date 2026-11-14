(** An executor needs to know which values and memory regions a block may use.
    These tables list live temporaries and explicit memory accesses to guide that choice.
    Wrong hints can stop execution, but they cannot justify a memory access.
    No soundness theorem may assume that these tables are correct.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


From Glibc Require Import GetoptSrc GetoptBlocks01 GetoptBlocks02 GetoptBlocks03.
Module GetoptBlocks.
Include GetoptBlocks01.
Include GetoptBlocks02.
Include GetoptBlocks03.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("glibc_getopt#process_long_option", app (map fst fn_glibc_getopt_process_long_option.live_in) (app (map fst fn_glibc_getopt_process_long_option.live_out) (map fst fn_glibc_getopt_process_long_option.footprint))); ("_getopt_internal_r", app (map fst fn__getopt_internal_r.live_in) (app (map fst fn__getopt_internal_r.live_out) (map fst fn__getopt_internal_r.footprint))); ("_getopt_internal", app (map fst fn__getopt_internal.live_in) (app (map fst fn__getopt_internal.live_out) (map fst fn__getopt_internal.footprint))); ("getopt_long", app (map fst fn_getopt_long.live_in) (app (map fst fn_getopt_long.live_out) (map fst fn_getopt_long.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) GetoptSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End GetoptBlocks.
