(** Before `c: main` runs, glibc calls `c: _IO_stdfiles_init` to
    finish linking its three standard streams. The contract of that
    call in [StartStdfilesInitSpec](StartStdfilesInitSpec.v) expects
    the streams in the state that the linker leaves them in. This
    module checks that the hi_atexit program really starts in that
    state, so that the proof of its startup can make the call.

    The memory of a program at its start is fixed when the program is
    linked. The constructor reads only a small part of it: the three
    streams, the head of their list, the lock of the list and one
    pointer. [HiAtexitInitialList](../hi_atexit/HiAtexitInitialList.v)
    lists that part and checks that the linked program contains it.
    This module starts from that list. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioStdfiles HiAtexitGe HiAtexitInitial HiAtexitInitialAlloc
  HiAtexitInitialStdout HiAtexitInitialList StartStdfilesInitSpec.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv LibioStdfiles.
Open Scope Z_scope.

(** The three streams and the three other globals have fixed
    addresses in hi_atexit. The stream stderr is at 71760, stdout is
    at 72240 and stdin is at 72000. The variable `c: _IO_list_all` is
    at 72480, the lock of the stream list is at 71648 and
    `c: run_fp` is at 71680. *)
Definition hi_stdfiles_inputs : ptr * ptr * ptr * Z * region * Z * region * Z * region :=
  (mkPtr 71760 (Obj 71760), mkPtr 72240 (Obj 72240), mkPtr 72000 (Obj 72000),
   72480, mkRegion 72480 72488 GlobalData Live, 71648, mkRegion 71648 71664 GlobalData Live,
   71680, mkRegion 71680 71688 GlobalData Live).

(** The streams of the inputs are the streams of the image, in the
    order stderr, stdout, stdin. *)
Lemma hi_stdfiles_inputs_streams :
  let '(fe, fo, fi, _, _, _, _, _, _) := hi_stdfiles_inputs in [fe; fo; fi] = hi_initial_streams.
Proof. reflexivity. Qed.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).

(** When hi_atexit starts, each of its three streams points at the
    next one and none points back. The constructor expects exactly
    that, so hi_atexit can call it right away. The call also needs
    stdout to be alive. The proofs about output track that fact on
    its own, so it is asked for separately here. *)
Lemma hi_stdfiles_init_pre :
  pts hi_initial_list_ps -∗ live 72240 hi_stdout_reg -∗
  fs_pre (stdfiles_init_spec (glibc_program := program_of w0 glibc_os_registry hge)) hi_stdfiles_inputs.
Proof using Type.
  rewrite /hi_initial_list_ps hi_pts_concat. cbn [big_opL fs_pre stdfiles_init_spec hi_stdfiles_inputs].
  iIntros "(He & Hi & Hep & Hec & Hop & Hoc & Hip & Hic & Hla & Hlac & Hlk & Hlk0 & Hlk4 & Hlk8 & Hrf & Hrfc & _) Ho".
  iSplit; [iPureIntro; vm_compute; intuition congruence|].
  iSplitL "Hla"; [iExact "Hla"|]. iSplitL "Hlac"; [iExact "Hlac"|].
  iSplitL "He Hep Hec"; [|iSplitL "Ho Hop Hoc"; [|iSplitL "Hi Hip Hic"; [|iSplitR "Hrf Hrfc"]]].
  - iExists 71760, (mkRegion 71760 71984 GlobalData Live). iFrame "He Hep Hec".
    iPureIntro. vm_compute. intuition congruence.
  - iExists 72240, hi_stdout_reg. iFrame "Ho Hop Hoc". iPureIntro. vm_compute. intuition congruence.
  - iExists 72000, (mkRegion 72000 72224 GlobalData Live). iFrame "Hi Hip Hic".
    iPureIntro. vm_compute. intuition congruence.
  - unfold lock_state, int_cell. iFrame "Hlk Hlk0 Hlk4 Hlk8". iPureIntro. vm_compute. intuition congruence.
  - iFrame "Hrf Hrfc".
Qed.

End image.
