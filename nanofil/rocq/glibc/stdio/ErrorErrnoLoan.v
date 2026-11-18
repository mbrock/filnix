(** Printing a message can change errno before strerror runs. The proof tracks
    current errno separately from the error number passed to strerror.
    It combines permission for errno's bytes with separately supplied
    permission for its hidden pointer-capability storage. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic ErrorFailure ErrorMessage ErrorMessageNarrow.
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

(** Success retains the formatter's errno in its spare resources. Failure
    returns the current value, including any fallback mutation. Both paths
    assemble one errno block and retain the actual mode without repairing it. *)
Lemma error_message_errno_loan fb freg eb ereg r en md :
  error_message_returned fb freg eb ereg r en md -∗
  error_message_spare fb eb ereg r en md -∗ error_errno_aux eb -∗
  ∃ now, ⌜0 <= now < 2 ^ 32 /\ (r mod 2 ^ 32 < 2 ^ 31 -> now = en)⌝ ∗
    live eb ereg ∗ errno_own eb (le_bytes now 4) ∗ int_cell fb 192 md.
Proof using Type.
  rewrite /error_message_returned_q /error_message_spare /error_mode_own.
  destruct (decide (2 ^ 31 <= r mod 2 ^ 32)) as [Hneg | Hpos].
  - iIntros "(_ & Hl & [%now Hnow] & Hmode) Hsp Ha".
    iAssert (⌜0 <= now < 2 ^ 32⌝ ∗ errno_own eb (le_bytes now 4))%I with "[Hnow Ha]" as "[%Hrange He]".
    { rewrite -error_errno_pack. iFrame. }
    iExists now. iSplit; [iPureIntro; split; [done | lia] |]. iFrame.
    destruct (decide (en = 12)); [iDestruct "Hmode" as "[_ Hmode]" |]; iFrame.
  - iIntros "_ (Hl & Hnow & Hmode) Ha".
    iAssert (⌜0 <= en < 2 ^ 32⌝ ∗ errno_own eb (le_bytes en 4))%I with "[Hnow Ha]" as "[%Hrange He]".
    { rewrite -error_errno_pack. iFrame. }
    iExists en. iFrame. iPureIntro. tauto.
Qed.
End errno.
