(** The static streams initially link forward, but their backward
    links are null. The stdfiles constructor must build those links
    before exit can unlink stdout. This file checks its input against
    the linked initial memory and proves the actual constructor call. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioStdfiles HiAtexitBase HiAtexitGe
  HiAtexitInitial HiAtexitInitialAlloc HiAtexitInitialStdout.
From stdpp Require Import list.
Import ListNotations.
Open Scope Z_scope.

(** The constructor uses the same interpreter logic as puts and close. *)
Module HST := LibioStdfilesOn InterpRuntime HLG.
Import HST HST.CS.SW.FI HST.CS.SW.FI.ML HST.CS.SW.FI.LG HST.CS.SW.FI.L.

(** The static list runs from stderr through stdout to stdin. *)
Definition hi_initial_streams : list ptr :=
  [mkPtr 69328 (Obj 69328); mkPtr 69808 (Obj 69808); mkPtr 69568 (Obj 69568)].

(** These pieces exclude stdout's life, which the puts image already
    owns. The constructor borrows that life and returns all three. *)
Definition hi_initial_list_ps : list (piece * pval) :=
  concat [[(PLive 69328, VLive (mkRegion 69328 69552 GlobalData Live))];
    [(PLive 69568, VLive (mkRegion 69568 69792 GlobalData Live))];
    hi_pointer_ps 69328 184 null; hi_pointer_ps 69328 104 (mkPtr 69808 (Obj 69808));
    hi_pointer_ps 69808 184 null; hi_pointer_ps 69808 104 (mkPtr 69568 (Obj 69568));
    hi_pointer_ps 69568 184 null; hi_pointer_ps 69568 104 null;
    [(PLive 70048, VLive (mkRegion 70048 70056 GlobalData Live))];
    hi_pointer_ps 70048 0 (mkPtr 69328 (Obj 69328));
    [(PLive 69216, VLive (mkRegion 69216 69232 GlobalData Live))];
    byte_ps 69216 0 (int_bytes 0); byte_ps 69216 4 (int_bytes 0); hi_pointer_ps 69216 8 null;
    [(PLive 69248, VLive (mkRegion 69248 69256 GlobalData Live))]; hi_pointer_ps 69248 0 null].

(** The constructor's entire input image agrees with the linked memory. *)
Lemma hi_initial_list_agree : all_agree hi_m0 hi_initial_list_ps.
Proof. apply checked_pieces_all_agree. vm_compute. reflexivity. Qed.

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
  pts hi_initial_list_ps -∗ live 69808 hi_stdout_reg -∗
  ▷ (io_list_inv hge hi_initial_streams -∗ ([∗ list] f ∈ hi_initial_streams, stream_live f) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_stdfiles_init [] [] None (Enter (TAtom "start") None)) : sexpr) {{ Φ }}.
Proof.
  rewrite /hi_initial_list_ps hi_pts_concat. cbn [big_opL].
  iIntros "(He & Hi & Hep & Hec & Hop & Hoc & Hip & Hic & Hla & Hlac & Hlk & Hlk0 & Hlk4 & Hlk8 & Hrf & Hrfc & _) Ho HK".
  iApply (wp_glibc_stdfiles_init w0 glibc_os_registry hge _
    (mkPtr 69328 (Obj 69328)) (mkPtr 69808 (Obj 69808)) (mkPtr 69568 (Obj 69568))
    70048 (mkRegion 70048 70056 GlobalData Live) 69216 (mkRegion 69216 69232 GlobalData Live)
    69248 (mkRegion 69248 69256 GlobalData Live)
    with "Hla Hlac [He Hep Hec] [Ho Hop Hoc] [Hi Hip Hic] [Hlk Hlk0 Hlk4 Hlk8] Hrf Hrfc HK");
    [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; intuition congruence
    | vm_compute; reflexivity | vm_compute; intuition congruence | | | |].
  - iExists 69328, (mkRegion 69328 69552 GlobalData Live). iFrame "He Hep Hec".
    iPureIntro. vm_compute. intuition congruence.
  - iExists 69808, hi_stdout_reg. iFrame "Ho Hop Hoc".
    iPureIntro. vm_compute. intuition congruence.
  - iExists 69568, (mkRegion 69568 69792 GlobalData Live). iFrame "Hi Hip Hic".
    iPureIntro. vm_compute. intuition congruence.
  - unfold lock_state, int_cell. iFrame "Hlk Hlk0 Hlk4 Hlk8".
    iPureIntro. vm_compute. intuition congruence.
Qed.

End rules.
