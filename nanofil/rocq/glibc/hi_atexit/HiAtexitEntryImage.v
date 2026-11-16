(** Main's starting state must exist in memory, with no byte owned
    twice. This file checks every required byte, pointer and object
    against the prepared memory. It also checks the complete list for
    duplicate ownership before constructing its [[separation-logic]] heap. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import ZArith List.
From stdpp Require Import list gmap.
From Nanofil Require Import Term Values Memory Pieces Heap.
From Glibc Require Import HelloImageEraseMem HelloImagePieces HiAtexitModule.
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

(** ## Checking the prepared memory piece by piece

    Main's proof needs every byte, pointer and object it uses to be in
    memory when it starts. A computed check of that list is slow on the
    prepared memory, because each read walks past every store that the
    loader made. The check therefore reads most of the list from a
    smaller image, which zeroes each object that the list does not
    name, with the same host writes on top. It reads the rest, such as
    the new thread's fields, from the prepared memory itself. Both
    memories receive the same host writes, so they still agree on every
    object that the smaller image keeps. *)

(** This memory applies the host's preparation to an erased image. *)
Definition hi_prepared_erased (keep : name -> bool) : mem :=
  hi_entry_writes (allocated (hi_erased keep) hi_tcb_req 4294967296) 4294967296 hi_entry_saved_jmp.

(** Identical host writes keep two memories equal at an address. *)
Lemma hi_entry_writes_agree m1 m2 tb jb x :
  m_bytes m1 x = m_bytes m2 x /\ m_aux m1 x = m_aux m2 x ->
  m_bytes (hi_entry_writes m1 tb jb) x = m_bytes (hi_entry_writes m2 tb jb) x /\
  m_aux (hi_entry_writes m1 tb jb) x = m_aux (hi_entry_writes m2 tb jb) x.
Proof.
  intros [B A]. unfold hi_entry_writes. generalize (hi_entry_ptrs tb jb) as l.
  assert (H : m_bytes (store_bytes (store_bytes m1 76240 1 1) (tb + 792) 4 0) x =
              m_bytes (store_bytes (store_bytes m2 76240 1 1) (tb + 792) 4 0) x /\
              m_aux (store_bytes (store_bytes m1 76240 1 1) (tb + 792) 4 0) x =
              m_aux (store_bytes (store_bytes m2 76240 1 1) (tb + 792) 4 0) x).
  { split; [do 2 apply store_bytes_agree; exact B | exact A]. }
  revert H. generalize (store_bytes (store_bytes m1 76240 1 1) (tb + 792) 4 0) as n1.
  generalize (store_bytes (store_bytes m2 76240 1 1) (tb + 792) 4 0) as n2.
  intros n2 n1 H l. revert n1 n2 H. induction l as [|ap l IH]; intros n1 n2 [Hb Ha]; cbn [fold_left];
    [split; assumption|]. apply IH. unfold hi_host_ptr. split.
  - apply store_bytes_agree. exact Hb.
  - apply store_aux_agree. exact Ha.
Qed.

(** The prepared erased image has the prepared memory's regions and
    agrees with it at every address of a kept object. *)
Lemma hi_prepared_erased_agree keep :
  m_regions (hi_prepared_erased keep) = m_regions hi_prepared_memory /\
  forall x, kept_at keep hi_module hi_globals x ->
    m_bytes (hi_prepared_erased keep) x = m_bytes hi_prepared_memory x /\
    m_aux (hi_prepared_erased keep) x = m_aux hi_prepared_memory x.
Proof.
  destruct (hi_erased_agree keep) as [R K].
  unfold hi_prepared_erased, hi_prepared_memory, hi_entry_mem. split.
  - (* Each side's regions are the new thread's region before the image's. *)
    exact (f_equal (cons (mkRegion 4294967296 (4294967296 + req_extent hi_tcb_req)
      (req_kind hi_tcb_req) Live)) R).
  - (* The images are opaque here, so that no step compares them by computation. *)
    intros x Hx. generalize (K x Hx). generalize (hi_erased keep) hi_m0. intros m1 m2 H.
    apply hi_entry_writes_agree. exact H.
Qed.

(** A piece is checked on the erased memory when a kept object covers
    it, and on the genuine memory otherwise. *)
Definition hi_mixed_ok keep (m m' : mem) (ps : list (piece * pval)) : bool :=
  let iv := kept_intervals keep hi_module hi_globals in
  forallb (fun lv => if piece_covered iv (m_regions m') lv.1
    then bool_decide (checked_piece m' lv.1 lv.2)
    else bool_decide (checked_piece m lv.1 lv.2)) ps.

(** Both kinds of check give agreement with the genuine memory. *)
Lemma hi_mixed_all_agree m ps keep m' :
  m_regions m' = m_regions m /\
  (forall x, kept_at keep hi_module hi_globals x -> m_bytes m' x = m_bytes m x /\ m_aux m' x = m_aux m x) ->
  hi_mixed_ok keep m m' ps = true -> all_agree m ps.
Proof.
  intros [R K] H. apply checked_pieces_all_agree. unfold hi_mixed_ok in H. cbv zeta in H.
  rewrite forallb_forall in H |- *. intros lv Hlv. pose proof (H lv Hlv) as Hc.
  destruct (piece_covered _ _ lv.1) eqn:Hv; [|exact Hc].
  apply bool_decide_eq_true_2. apply bool_decide_eq_true_1 in Hc.
  exact (checked_transfer keep hi_module hi_module hi_globals m m' lv.1 lv.2 (incl_refl _) R K Hv Hc).
Qed.

(** Every required byte, pointer capability and object region has
    its listed value in the prepared memory. *)
Lemma hi_entry_agree : all_agree hi_prepared_memory hi_entry_ps.
Proof.
  apply (hi_mixed_all_agree _ _ (hi_keep hi_entry_ps) (hi_prepared_erased (hi_keep hi_entry_ps))).
  - apply hi_prepared_erased_agree.
  - vm_cast_no_check (eq_refl true).
Qed.

(** Every owned key is unique across the complete image. In particular,
    the stream list does not duplicate stdout's or the other streams'
    object tokens. *)
Lemma hi_entry_nodup : NoDup hi_entry_ps.*1.
Proof. apply hi_unique_sound. vm_cast_no_check (eq_refl true). Qed.

(** Combining the listed fields into one heap preserves their
    agreement with physical memory. *)
Lemma hi_entry_heap_agrees : agrees hi_prepared_memory (list_to_map hi_entry_ps).
Proof.
  intros l v H. apply (all_agree_elem _ _ _ _ hi_entry_agree).
  apply elem_of_list_to_map_2 in H. exact H.
Qed.
