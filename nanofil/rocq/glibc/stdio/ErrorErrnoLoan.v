(** Printing a message can change errno before strerror runs. The proof tracks
    current errno separately from the error number passed to strerror.
    It combines permission for errno's bytes with separately supplied
    permission for its hidden pointer-capability storage. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic OsWorld.
Open Scope Z_scope.

Section errno.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A write to errno also needs permission for its hidden pointer storage.
    The caller supplies that permission once, separately from the data bytes. *)
Definition error_errno_aux eb : iProp Σ :=
  ∃ cs, ⌜length cs = 4%nat⌝ ∗ pts (aux_ps eb 0 cs).

(** Repacking is reversible and preserves the current 32-bit value. The
    lifetime of the errno object remains a separate caller resource. *)
Lemma error_errno_pack eb now :
  int_cell eb 0 now ∗ error_errno_aux eb ⊣⊢
  ⌜0 <= now < 2 ^ 32⌝ ∗ errno_own eb (le_bytes now 4).
Proof using Type.
  rewrite /int_cell /int_bytes /bytes /error_errno_aux /errno_own.
  iSplit.
  - iIntros "[[%Hnow Hb] [%cs [%Hcs Ha]]]". iSplit; [done |].
    iExists cs. iSplit; [iPureIntro; split; [apply length_le_bytes | done] |].
    rewrite pts_app. iFrame.
  - iIntros "[%Hnow [%cs [%Hlen H]]]". rewrite pts_app.
    iDestruct "H" as "[Hb Ha]". iSplitL "Hb"; [iFrame; done |].
    iExists cs. iFrame. iPureIntro. tauto.
Qed.

End errno.
