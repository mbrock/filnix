(** This file constructs the imported stream resources used by Hello.
    An explicit finite heap contains three empty streams, their linked
    list, thread cleanup fields, errno, jump tables and the idle allocator.
    The ownership keys are distinct, and Iris allocates the resources
    together rather than assuming that a caller can supply them.

    The fixture checks resource satisfiability, not program linking or
    the remaining M4 and M6 call proofs. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld FileInv HelloGlibcMainWitness.
From stdpp Require Import list.
From Glibc Require AllocLogic FileInv HelloGlibcMainWitness.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** The earlier fixture supplies the streams and allocator. *)
Import HelloGlibcMainWitness LG0 LG0.L FileInv FileInv.ML.

(** The resource environment assigns distinct pages to shared globals.
    The jump-table slots carry function capabilities, even though this
    fixture does not supply the functions' implementation bodies. *)
Definition witness_ge : genv := mkGenv []
  ([(TAtom "__io_vtables", mkPtr 16384 (Ro 16384));
    (TAtom "__GI__IO_list_all", mkPtr 86016 (Obj 86016));
    (TAtom "glibc_genops#list_all_lock", mkPtr 90112 (Obj 90112));
    (TAtom "glibc_genops#run_fp", mkPtr 94208 (Obj 94208));
    (TAtom "__libc_single_threaded_internal", mkPtr 98304 (Obj 98304))] ++
    ((fun sl => (TAtom sl.2, mkPtr (102400 + sl.1) (Fn (TAtom sl.2)))) <$> file_jumps)) R.free.

(** A lock image holds a live page, two zero integers and a null owner. *)
Definition witness_lock (b : Z) : list (piece * pval) :=
  concat [[(PLive b, VLive (hello_witness_region b))];
    byte_ps b 0 (int_bytes 0); byte_ps b 4 (int_bytes 0); hello_witness_pointer b 8 null].

(** The list image owns only the chain fields omitted by each file invariant. *)
Definition witness_list : list (piece * pval) :=
  concat [[(PLive 86016, VLive (hello_witness_region 86016))];
    hello_witness_pointer 86016 0 (mkPtr 8192 (Obj 8192));
    hello_witness_pointer 8192 off_prevchain (mkPtr 86016 (Obj 86016));
    hello_witness_pointer 8192 off_chain (mkPtr 4096 (Obj 4096));
    hello_witness_pointer 4096 off_prevchain (mkPtr (8192 + off_chain) (Obj 8192));
    hello_witness_pointer 4096 off_chain (mkPtr 12288 (Obj 12288));
    hello_witness_pointer 12288 off_prevchain (mkPtr (4096 + off_chain) (Obj 4096));
    hello_witness_pointer 12288 off_chain null; witness_lock 90112;
    [(PLive 94208, VLive (hello_witness_region 94208))]; hello_witness_pointer 94208 0 null].

(** Thread cleanup and errno occupy separate pages. *)
Definition witness_thread : list (piece * pval) :=
  concat [[(PLive 53248, VLive (hello_witness_region 53248))];
    hello_witness_pointer 53248 off_cleanup null;
    hello_witness_pointer 53248 off_cleanup_jmp null;
    byte_ps 53248 off_cancelhandling (int_bytes 0);
    [(PLive 49152, VLive (hello_witness_region 49152))];
    byte_ps 49152 0 [0; 0; 0; 0] ++ aux_ps 49152 0 (replicate 4 CNone)].

(** The read-only image contains each used jump slot and the single-thread flag. *)
Definition witness_readonly : list (piece * pval) :=
  concat [[(PLive 16384, VLive (hello_witness_region 16384))];
    concat ((fun sl => hello_witness_pointer 16384 (vt_file + sl.1) (sym_ptr witness_ge sl.2)) <$> file_jumps);
    [(PLive 98304, VLive (hello_witness_region 98304))]; byte_ps 98304 0 [1]].

(** The whole image includes every imported stream and allocator predicate together. *)
Definition witness_all : list (piece * pval) :=
  concat [hello_witness_pieces; witness_list; witness_thread; witness_readonly].

(** A finite computation checks that none of these ownership keys overlap. *)
Lemma witness_all_distinct : NoDup witness_all.*1.
Proof. apply hello_witness_unique_sound. vm_compute. reflexivity. Qed.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** The lock image establishes the concrete unlocked-lock predicate. *)
Lemma witness_lock_ok b : b mod 8 = 0 -> b + 4096 <= 2 ^ 63 ->
  pts (witness_lock b) -∗ lock_state b (hello_witness_region b) 0 0 null.
Proof.
  intros Hb He. rewrite /witness_lock witness_concat. cbn [big_opL].
  iIntros "(Hl & Hk & Hc & Ho & _)". iSplit; [iPureIntro; change (b mod 8 = 0 /\ b + 16 <= b + 4096 /\ b + 4096 <= 2 ^ 63); lia|].
  iFrame "Hl Ho". iSplitL "Hk"; iSplit; try iPureIntro; try lia; iAssumption.
Qed.

(** The explicit forward and backward links establish the open-stream list. *)
Lemma witness_list_ok : pts witness_list -∗
  io_list_inv witness_ge [mkPtr 8192 (Obj 8192); mkPtr 4096 (Obj 4096); mkPtr 12288 (Obj 12288)].
Proof.
  rewrite /witness_list witness_concat. cbn [big_opL].
  iIntros "(Hla & Hhead & Hep & Hen & Hop & Hon & Hip & Hin & Hlk & Hrf & Hrun & _)".
  iExists 86016, (hello_witness_region 86016), 90112, (hello_witness_region 90112),
    94208, (hello_witness_region 94208).
  iSplit; [iPureIntro; vm_compute; intuition congruence|].
  iFrame "Hla Hhead Hrf Hrun". iSplitL "Hep Hen Hop Hon Hip Hin".
  - cbn [chain_links]. iExists 8192. iSplit; [done|]. iFrame "Hep Hen".
    iExists 4096. iSplit; [done|]. iFrame "Hop Hon".
    iExists 12288. iSplit; [done|]. iFrame "Hip Hin".
  - iApply (witness_lock_ok with "Hlk"); vm_compute; intuition congruence.
Qed.

(** The thread image establishes cleanup state, errno bytes and errno lifetime. *)
Lemma witness_thread_ok : pts witness_thread -∗
  tcb_cleanup_inv (ow_self hello_witness_world) ∗ errno_any 49152 ∗
  live 49152 (hello_witness_region 49152).
Proof.
  rewrite /witness_thread witness_concat. cbn [big_opL].
  iIntros "(Ht & Hc & Hj & Hch & He & Herrno & _)". iSplitL "Ht Hc Hj Hch".
  - iExists 53248, (hello_witness_region 53248), null.
    iSplit; [iPureIntro; vm_compute; intuition congruence|]. iFrame "Ht Hc Hj".
    iSplit; [iPureIntro; lia|iExact "Hch"].
  - iSplitL "Herrno"; [|iExact "He"].
    iExists [0; 0; 0; 0], (replicate 4 CNone). iSplit; [done|iExact "Herrno"].
Qed.

(** Persisting the explicit image supplies both shared stream predicates. *)
Lemma witness_readonly_ok : pts witness_readonly ==∗
  vtables_ro witness_ge 16384 (hello_witness_region 16384) ∗
  single_ro witness_ge 98304 (hello_witness_region 98304).
Proof.
  iIntros "H". iMod (ptsq_persist (DfracOwn 1) with "H") as "#H". iModIntro.
  rewrite /witness_readonly witness_concatq. cbn [big_opL].
  iDestruct "H" as "(Hv & Hslots & Hs & Hb & _)". iSplit.
  - iSplit; [iPureIntro; vm_compute; intuition congruence|]. iFrame "Hv".
    rewrite witness_concatq big_sepL_fmap /pcellq /hello_witness_pointer. iExact "Hslots".
  - iSplit; [iPureIntro; vm_compute; intuition congruence|]. iFrame "Hs Hb".
Qed.

(** The complete fixture establishes all the imported stream and allocator resources. *)
Lemma witness_all_resources : pts witness_all ==∗
  file_inv 16384 (ow_self hello_witness_world) (mkPtr 4096 (Obj 4096)) ∗
  file_inv 16384 (ow_self hello_witness_world) (mkPtr 8192 (Obj 8192)) ∗
  file_inv 16384 (ow_self hello_witness_world) (mkPtr 12288 (Obj 12288)) ∗
  io_list_inv witness_ge [mkPtr 8192 (Obj 8192); mkPtr 4096 (Obj 4096); mkPtr 12288 (Obj 12288)] ∗
  tcb_cleanup_inv (ow_self hello_witness_world) ∗ errno_any 49152 ∗
  liveq DfracDiscarded 49152 (hello_witness_region 49152) ∗
  vtables_ro witness_ge 16384 (hello_witness_region 16384) ∗
  single_ro witness_ge 98304 (hello_witness_region 98304) ∗
  AllocLogic.tcache_idle DfracDiscarded 32768 36864 40960
    (hello_witness_region 32768) (hello_witness_region 36864) (hello_witness_region 40960).
Proof.
  rewrite /witness_all witness_concat. cbn [big_opL]. iIntros "(Hfiles & Hlist & Hthread & Hro & _)".
  rewrite /hello_witness_pieces witness_concat. cbn [big_opL].
  iDestruct "Hfiles" as "(Ho & He & Hi & Ha & _)".
  iDestruct (witness_thread_ok with "Hthread") as "(Ht & Herr & Hel)".
  iDestruct (witness_list_ok with "Hlist") as "Hlist".
  iMod (witness_readonly_ok with "Hro") as "Hro".
  iMod (witness_alloc_readonly with "Ha") as "Ha".
  iMod (ptsq_persist (DfracOwn 1) with "Hel") as "#Hel". iModIntro.
  iSplitL "Ho"; [iApply (witness_file with "Ho"); vm_compute; intuition congruence|].
  iSplitL "He"; [iApply (witness_file with "He"); vm_compute; intuition congruence|].
  iSplitL "Hi"; [iApply (witness_file with "Hi"); vm_compute; intuition congruence|].
  iFrame "Hlist Ht Herr Hel Ha Hro".
Qed.
End resources.

(** Iris allocates the resource bundle from the explicit finite heap.
    No initial separation-logic resource is a premise of this theorem. *)
Lemma witness_imported_allocatable Σ `{!gen_heapGpreS piece pval Σ} :
  ⊢ |==> ∃ Hh : gen_heapGS piece pval Σ,
    @pts Σ Hh witness_all.
Proof.
  iMod (gen_heap_init (list_to_map witness_all : gmap piece pval)) as (Hh) "(_ & Hpts & _)".
  iModIntro. iExists Hh.
  rewrite /pts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v));
    [iExact "Hpts"|exact witness_all_distinct].
Qed.

(** The concrete heap supplies the standard streams and shared prelude together.
    The only premise supplies Iris's ghost-state construction, not ownership
    of any program resource. *)
Lemma witness_imported_resources Σ `{!gen_heapGpreS piece pval Σ} :
  ⊢ |==> ∃ Hh : gen_heapGS piece pval Σ,
    @FileInv.file_inv Σ Hh 16384 (ow_self hello_witness_world) (mkPtr 4096 (Obj 4096)) ∗
    @FileInv.file_inv Σ Hh 16384 (ow_self hello_witness_world) (mkPtr 8192 (Obj 8192)) ∗
    @FileInv.file_inv Σ Hh 16384 (ow_self hello_witness_world) (mkPtr 12288 (Obj 12288)) ∗
    @FileInv.io_list_inv Σ Hh witness_ge [mkPtr 8192 (Obj 8192); mkPtr 4096 (Obj 4096); mkPtr 12288 (Obj 12288)] ∗
    @FileInv.tcb_cleanup_inv Σ Hh (ow_self hello_witness_world) ∗ @errno_any Σ Hh 49152 ∗
    @liveq Σ Hh DfracDiscarded 49152 (hello_witness_region 49152) ∗
    @FileInv.vtables_ro Σ Hh witness_ge 16384 (hello_witness_region 16384) ∗
    @FileInv.single_ro Σ Hh witness_ge 98304 (hello_witness_region 98304) ∗
    @AllocLogic.tcache_idle Σ Hh DfracDiscarded 32768 36864 40960
      (hello_witness_region 32768) (hello_witness_region 36864) (hello_witness_region 40960).
Proof.
  iMod (witness_imported_allocatable Σ) as (Hh) "H".
  iMod (witness_all_resources with "H") as "H". iModIntro. iExists Hh. iExact "H".
Qed.
