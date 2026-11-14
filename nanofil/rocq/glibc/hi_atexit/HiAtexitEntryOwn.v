(** Main can begin with the prepared memory and needs no additional
    library state. This file combines the checked fields into the
    starting assertions for the allocator, streams, exit callbacks and
    thread. It obtains read-only access by giving up write permission
    to fields already present in that same memory. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List.
From Nanofil Require Import Values Pieces Heap Logic.
From Glibc Require Import HiAtexitBase HiAtexitInitialAlloc HiAtexitInitialStdout
  HiAtexitInitialExit HiAtexitMain HiAtexitPrepare HiAtexitEntryList
  HiAtexitEntryFields HiAtexitEntryImage.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Every conjunct comes from its part of the same checked entry
    image. The caller does not supply any additional library resource. *)
Lemma hi_entry_own : pts hi_entry_ps ==∗ hi_main_state (hi_entry_world 4294967296).
Proof.
  rewrite /hi_entry_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Ho & Hex & Hlist & Hrest & Hvt & Hs & Hprog & Hthread & _)".
  iDestruct (hi_initial_output_own (hi_entry_world 4294967296) with "Ho") as "[HM Hout]";
    [cbn; auto|].
  iDestruct (hi_initial_exit_own with "Hex") as "[Hinv Hlock]".
  iDestruct (hi_entry_list_own with "Hlist") as "Hio".
  iDestruct (hi_entry_rest_own with "Hrest") as "Hrest".
  iDestruct (hi_entry_program_own with "Hprog") as "(Hso & Hsoc & Hstr)".
  iDestruct (hi_entry_thread_own with "Hthread") as "Htcb".
  iMod (hi_entry_vtables_own with "Hvt") as "Hvt".
  iMod (hi_entry_single_own with "Hs") as "Hs".
  iModIntro. rewrite /hi_main_state.
  iFrame "Hvt Hs Htcb Hso Hsoc Hout HM Hio Hrest Hstr Hinv Hlock".
Qed.

End resources.
