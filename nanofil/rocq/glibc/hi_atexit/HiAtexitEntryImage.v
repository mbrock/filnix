(** Main's starting state must exist in memory, with no byte owned
    twice. This file checks every required byte, pointer and object
    against the prepared memory. It also checks the complete list for
    duplicate ownership before constructing its [[separation-logic]] heap. *)

From Stdlib Require Import ZArith List.
From stdpp Require Import list gmap.
From Nanofil Require Import Values Memory Pieces Heap.
From Glibc Require Import HiAtexitInitial HiAtexitInitialStdout HiAtexitInitialExit
  HiAtexitPrepare HiAtexitEntryList HiAtexitEntryFields.
Import ListNotations.
Open Scope Z_scope.

(** This concrete saved pointer is non-null and lies within the new
    thread object. Cleanup only saves and restores it; it never follows
    it on this entry path. This host-entry choice is not a claim about
    the saved address installed by real process startup. *)
Definition hi_entry_saved_jmp : ptr := mkPtr 4294968320 (Obj 4294967296).

(** The list includes everything that main will use: its allocator,
    streams, error cell, exit callbacks and thread. *)
Definition hi_entry_ps : list (piece * pval) :=
  concat [hi_initial_output_ps; hi_initial_exit_ps; hi_entry_list_ps; hi_entry_rest_ps;
    hi_entry_vtables_ps; hi_entry_single_ps; hi_entry_program_ps;
    hi_entry_thread_ps hi_entry_saved_jmp].

(** This memory is the successful host preparation of the actual
    loader image, not a replacement for the loader's definition. *)
Definition hi_prepared_memory : mem := hi_entry_mem hi_entry_saved_jmp.

(** Every required byte, pointer capability and object region has
    its listed value in the prepared memory. *)
Lemma hi_entry_agree : all_agree hi_prepared_memory hi_entry_ps.
Proof.
  apply checked_pieces_all_agree. vm_compute. reflexivity.
Qed.

(** Every owned key is unique across the complete image. In particular,
    the stream list does not duplicate stdout's or the other streams'
    object tokens. *)
Lemma hi_entry_nodup : NoDup hi_entry_ps.*1.
Proof. apply hi_unique_sound. vm_compute. reflexivity. Qed.

(** Combining the listed fields into one heap preserves their
    agreement with physical memory. *)
Lemma hi_entry_heap_agrees : agrees hi_prepared_memory (list_to_map hi_entry_ps).
Proof.
  intros l v H. apply (all_agree_elem _ _ _ _ hi_entry_agree).
  apply elem_of_list_to_map_2 in H. exact H.
Qed.
