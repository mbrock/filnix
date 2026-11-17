From Glibc Require Import GlibcProgram.
(** The static streams initially link forward, but their backward
    links are null. The stdfiles constructor must build those links
    before exit can unlink stdout. This file checks its input against
    the linked initial memory and proves the actual constructor call. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioStdfiles HiAtexitBase HiAtexitGe
  HiAtexitInitial HiAtexitInitialAlloc HiAtexitInitialStdout.
From stdpp Require Import list.
From Glibc Require FileInv LibioStdfiles.
Import ListNotations.
Open Scope Z_scope.

(** The constructor uses the same interpreter logic as puts and close. *)
Import LibioStdfiles FileInv FileInv.ML FileInv.LG FileInv.L.

(** The static list runs from stderr through stdout to stdin. *)
Definition hi_initial_streams : list ptr :=
  [mkPtr 71760 (Obj 71760); mkPtr 72240 (Obj 72240); mkPtr 72000 (Obj 72000)].

(** These pieces exclude stdout's life, which the puts image already
    owns. The constructor borrows that life and returns all three. *)
Definition hi_initial_list_ps : list (piece * pval) :=
  concat [[(PLive 71760, VLive (mkRegion 71760 71984 GlobalData Live))];
    [(PLive 72000, VLive (mkRegion 72000 72224 GlobalData Live))];
    hi_pointer_ps 71760 184 null; hi_pointer_ps 71760 104 (mkPtr 72240 (Obj 72240));
    hi_pointer_ps 72240 184 null; hi_pointer_ps 72240 104 (mkPtr 72000 (Obj 72000));
    hi_pointer_ps 72000 184 null; hi_pointer_ps 72000 104 null;
    [(PLive 72480, VLive (mkRegion 72480 72488 GlobalData Live))];
    hi_pointer_ps 72480 0 (mkPtr 71760 (Obj 71760));
    [(PLive 71648, VLive (mkRegion 71648 71664 GlobalData Live))];
    byte_ps 71648 0 (int_bytes 0); byte_ps 71648 4 (int_bytes 0); hi_pointer_ps 71648 8 null;
    [(PLive 71680, VLive (mkRegion 71680 71688 GlobalData Live))]; hi_pointer_ps 71680 0 null].

(** The constructor's entire input image agrees with the linked memory. *)
Lemma hi_initial_list_agree : all_agree hi_m0 hi_initial_list_ps.
Proof. apply hi_m0_pieces. vm_compute. reflexivity. Qed.

(** The constructor and puts can own their inputs together without
    sharing a field. In particular, only puts owns stdout's object token. *)
Lemma hi_initial_list_output_nodup : NoDup (hi_initial_list_ps ++ hi_initial_output_ps).*1.
Proof. apply hi_unique_sound. vm_compute. reflexivity. Qed.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** The constructor runs with the linked program's OS registry. *)
Local Instance hi_initial_list_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** Running the actual stdfiles constructor establishes the linked
    stream-list invariant from its static input. It returns every
    stream's life so the caller can restore stdout's output predicate. *)
Lemma hi_initial_list_construct Φ :
  pts hi_initial_list_ps -∗ live 72240 hi_stdout_reg -∗
  ▷ (io_list_inv hge hi_initial_streams -∗ ([∗ list] f ∈ hi_initial_streams, stream_live f) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_stdfiles_init [] [] None (Enter (TAtom "start") None)) : sexpr) {{ Φ }}.
Proof using Type.
  rewrite /hi_initial_list_ps hi_pts_concat. cbn [big_opL].
  iIntros "(He & Hi & Hep & Hec & Hop & Hoc & Hip & Hic & Hla & Hlac & Hlk & Hlk0 & Hlk4 & Hlk8 & Hrf & Hrfc & _) Ho HK".
  iApply (wp_glibc_stdfiles_init (glibc_program := program_of w0 glibc_os_registry hge) _
    (mkPtr 71760 (Obj 71760)) (mkPtr 72240 (Obj 72240)) (mkPtr 72000 (Obj 72000))
    72480 (mkRegion 72480 72488 GlobalData Live) 71648 (mkRegion 71648 71664 GlobalData Live)
    71680 (mkRegion 71680 71688 GlobalData Live)
    with "Hla Hlac [He Hep Hec] [Ho Hop Hoc] [Hi Hip Hic] [Hlk Hlk0 Hlk4 Hlk8] Hrf Hrfc HK");
    [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; intuition congruence
    | vm_compute; reflexivity | vm_compute; intuition congruence | | | |].
  - iExists 71760, (mkRegion 71760 71984 GlobalData Live). iFrame "He Hep Hec".
    iPureIntro. vm_compute. intuition congruence.
  - iExists 72240, hi_stdout_reg. iFrame "Ho Hop Hoc".
    iPureIntro. vm_compute. intuition congruence.
  - iExists 72000, (mkRegion 72000 72224 GlobalData Live). iFrame "Hi Hip Hic".
    iPureIntro. vm_compute. intuition congruence.
  - unfold lock_state, int_cell. iFrame "Hlk Hlk0 Hlk4 Hlk8".
    iPureIntro. vm_compute. intuition congruence.
Qed.

End rules.
