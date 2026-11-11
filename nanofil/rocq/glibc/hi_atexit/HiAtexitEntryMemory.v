(** Host preparation must produce a usable physical state, not just
    values for a resource predicate. This file proves that its TCB
    allocation is fresh, all regions remain disjoint, and the runtime
    cursor remains ready after the finite writes. It also establishes
    the OS interpretation for every ghost heap agreeing with that
    prepared memory. *)

From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Values Memory Runtime Run Pieces Heap.
From Glibc Require Import OsWorld HiAtexitInitial HiAtexitImage HiAtexitPrepare.
Open Scope Z_scope.

(** A byte store below the runtime cursor cannot invalidate its
    region bounds or initialize previously unwritten high memory. *)
Lemma hi_ready_bytes next m a n x : a + n <= next ->
  InterpRuntime.ready next m -> InterpRuntime.ready next (store_bytes m a n x).
Proof.
  intros Hend (Hp & Ho & Hhigh). split; [exact Hp|]. split; [exact Ho|].
  intros a' Ha'. unfold store_bytes. cbn.
  assert (Houtside : (a' <? a + n) = false) by (apply Z.ltb_ge; lia).
  rewrite Houtside, Bool.andb_false_r. exact (Hhigh a' Ha').
Qed.

(** A capability store below the cursor preserves the same readiness. *)
Lemma hi_ready_aux next m a c : a < next ->
  InterpRuntime.ready next m -> InterpRuntime.ready next (store_aux m a c).
Proof.
  intros Hend (Hp & Ho & Hhigh). split; [exact Hp|]. split; [exact Ho|].
  intros a' Ha'. unfold store_aux. cbn.
  assert (Houtside : (a' =? a) = false) by (apply Z.eqb_neq; lia).
  rewrite Houtside. exact (Hhigh a' Ha').
Qed.

(** Preparing the fields cannot write into the space reserved for
    future allocations. Both the static image and thread object end
    below the new allocation cursor. *)
Lemma hi_entry_writes_ready next m tb jb :
  73809 <= next -> tb + 2560 <= next -> InterpRuntime.ready next m ->
  InterpRuntime.ready next (hi_entry_writes m tb jb).
Proof.
  intros Hstatic Htcb Hr. unfold hi_entry_writes, hi_entry_ptrs.
  cbn [fold_left hi_host_ptr fst snd].
  unfold hi_host_ptr. cbn [fst snd].
  repeat lazymatch goal with
    | |- InterpRuntime.ready _ (store_aux ?m ?a ?c) =>
        refine (hi_ready_aux next m a c _ _); [lia|]
    | |- InterpRuntime.ready _ (store_bytes ?m ?a ?n ?x) =>
        refine (hi_ready_bytes next m a n x _ _); [lia|]
    end.
  exact Hr.
Qed.

(** The allocation produces a fresh object and leaves the allocator
    ready for its next request. *)
Lemma hi_entry_allocation : fresh hi_m0 hi_tcb_req 4294967296 /\
  InterpRuntime.ready 4294969872 (allocated hi_m0 hi_tcb_req 4294967296).
Proof.
  eapply InterpRuntime.fresh_allocation;
    [exact hi_image_ready|change (0 < 16); lia|
     change (0 <= 2560); lia|exact hi_tcb_allocation].
Qed.

(** The prepared physical memory is ready for subsequent allocations. *)
Lemma hi_entry_ready jb : InterpRuntime.ready 4294969872 (hi_entry_mem jb).
Proof.
  apply hi_entry_writes_ready; [lia|lia|exact (proj2 hi_entry_allocation)].
Qed.

(** Freshness keeps the new heap region separate from every static
    object; the subsequent stores leave that region table unchanged. *)
Lemma hi_entry_live_disjoint jb : live_disjoint (hi_entry_mem jb).
Proof.
  apply (live_disjoint_regions (allocated hi_m0 hi_tcb_req 4294967296));
    [apply hi_entry_writes_regions|].
  apply live_disjoint_allocated;
    [exact hi_image_live_disjoint|exact (proj1 hi_entry_allocation)|change (0 <= 2560); lia].
Qed.

(** Errno remains the linked, permanent global-data object. This
    checks the physical region, not only an ownership token. *)
Lemma hi_entry_errno jb :
  permanent_errno (hi_entry_mem jb) (mkPtr 68176 (Obj 68176)).
Proof.
  exists 68176, (mkRegion 68176 68184 GlobalData Live).
  repeat split; try reflexivity; cbn; lia.
Qed.

(** The prepared state satisfies the OS checks: its error cell cannot
    be freed as a heap object, its thread pointer names a registered
    object, and its standard descriptors are not used for logging. *)
Lemma hi_entry_os_wi jb h : agrees (hi_entry_mem jb) h ->
  os_wi (hi_entry_world 4294967296) (hi_entry_mem jb) (hi_entry_world 4294967296) h.
Proof.
  intros Hag. split; [reflexivity|]. split.
  - intros p Hp. injection Hp as <-. split; [apply hi_entry_errno|].
    intros reg Hh. specialize (Hag _ _ Hh). cbn [agree_piece] in Hag.
    destruct Hag as [Hreg Hlive].
    change (Some (mkRegion 68176 68184 GlobalData Live) = Some reg) in Hreg.
    injection Hreg as <-. reflexivity.
  - split.
    + intros Hnz b [Hb|Hb]; [|discriminate Hb].
      injection Hb as <-. rewrite hi_entry_tcb_registered. discriminate.
    + repeat constructor; discriminate.
Qed.
