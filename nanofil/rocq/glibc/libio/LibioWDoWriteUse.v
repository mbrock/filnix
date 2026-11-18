(** Hello's wide stdout is flushed in two places. When the program
    exits, closing stdout writes out the characters still in its buffer.
    While Hello prints, a full buffer is written out to make room for
    more characters. Both callers run the same glibc function,
    `c: _IO_wdo_write`, which converts the wide characters to bytes and
    writes them to the descriptor.

    Each caller was proved first with an assumption about that function,
    written in the caller's own terms. This file shows that the proof of
    the function itself meets both assumptions. The function needs the
    conversion's read-only tables and the current locale. Each caller
    keeps them among the [[separation-logic|resources]] it owns, so the
    proofs here take the tables out, lend the locale to the function,
    and give the resources back when it returns. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry SysCode FileInv LibioLogic LibioCloseSteps LibioReadCode
  LibioDoWriteCode LibioWIdle LibioWXsputnWindow LibioWOverflowWrite LibioWCloseIt LibioWConvAscii
  LibioWDoWriteLoop LibioWConvOut HelloImageLoad SysWrappers.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation objp b := (mkPtr b (Obj b)).

Section use.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__GI___write" glibc___libc_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write).
Context `{Hdw : !Defines ge "_IO_new_do_write" glibc__IO_new_do_write}
  `{Hcvf : !Defines ge "__libio_codecvt_out" codecvt_out_fn}.
Context (fd vb : Z) (vr : region) (eb : Z) (tw tm : ptr).
Context (Hfd : In fd (ow_fds w0)) (Herr : ow_errno w0 = Some (objp eb)).

(** ## Closing wide stdout

    Closing stdout must first write out the characters still in its
    buffer, and it already holds the FILE lock when it does so. The
    close proof assumed that this write leaves the stream intact with
    the same lock, and these lines prove that assumption. *)

(** Any caller can use this write if its frame keeps the conversion
    tables and can lend out the locale for the call. After the write,
    the buffer's cursors may point anywhere inside the buffer. Closing
    does not need to know where, so the proof forgets their values. *)
Lemma wclose_write_ok (CR L : iProp Σ) `{!Persistent CR} (Hcv : codecvt_out_rule CR L) (E : iProp Σ) :
  (E ⊢ □ CR) -> (E ⊢ L ∗ (L -∗ E)) ->
  forall fb freg wd, wclose_write_rule fd vb fb vr freg eb wd tw tm E.
Proof using Type*.
  intros HCR HL fb freg wd fr st nb w wr i j Ψ Hfr Hok B Hi Hj _.
  iIntros "#Hv #Hw Herr HE Hf Hfields Hnb Hdata HK".
  iDestruct (bi.persistent_entails_r _ _ HCR with "HE") as "[HE #HCR]".
  iDestruct (HL with "HE") as "[HL HLE]".
  iApply (wp_wdo_write Hreg Hext Hfw CR L Hcv fd vb fb vr freg eb wd w tw tm Hfd Herr
    with "Hv Hw HCR HL Herr Hf Hfields Hnb Hdata"); try assumption.
  iNext. iIntros (r st' k j' (Hr & Hok' & Hlk & _)) "HL Herr Hf Hfields Hnb Hdata".
  iApply ("HK" $! r st' nb w with "[%] Herr [HL HLE] Hf Hfields Hnb [Hdata]").
  - split_and!; assumption.
  - by iApply "HLE".
  - by iExists wr, _.
Qed.

(** ## Flushing while printing

    When Hello prints more characters than the wide buffer holds, glibc
    writes the full buffer out and then keeps printing into the emptied
    buffer. The printing proof assumed that this write either empties
    the buffer or fails and leaves a usable stream. The conversion
    function for the C locale is still an assumption here, until its
    own proof lands. *)

Context (dl : dfrac) (Hcv : codecvt_out_rule wconv_ro (wlocale dl)).

(** When the flush turns wide characters into bytes, it calls a glibc
    function that this file treats as a promise. That function now has
    its own proof, so the promise holds whenever the ASCII step it
    calls is linked into the image and keeps its own promise. *)
Lemma codecvt_out_ok `{!Defines ge "__gconv_transform_internal_ascii" glibc_internal_ascii} :
  ia_last_rule dl ->
  function_check_res ge (mkPtr (img_a "__gconv_transform_internal_ascii")
    (Fn (TAtom "__gconv_transform_internal_ascii"))) = Some ok ->
  lookup (TAtom "glibc_wcsmbsload#to_mb") (ge_globals ge) =
    Some (mkPtr (img_a "glibc_wcsmbsload#to_mb") (Ro (img_a "glibc_wcsmbsload#to_mb"))) ->
  codecvt_out_rule wconv_ro (wlocale dl).
Proof using Type.
  intros Hlast Hfct Htmb. unfold codecvt_out_rule. intros.
  eapply (wp_codecvt_out dl Hlast Hfct Htmb); eassumption.
Qed.

(** Printing can use this write if its frame keeps the stream tables
    and the conversion tables and can lend out the locale and errno.
    The write never takes the stream's lock, so the proof sets the lock
    aside and returns it unchanged. After a successful write the cursor
    is back at the start of the buffer. After a failed write the cursors
    may point anywhere in the buffer, and printing still gets a whole
    wide stream back. *)
Lemma wdo_pending_ok self (E : iProp Σ) :
  (E ⊢ □ (vtables_ro ge vb vr ∗ wvtables_ro ge vb ∗ wconv_ro)) ->
  (E ⊢ wlocale dl ∗ errno_any eb ∗ (wlocale dl -∗ errno_any eb -∗ E)) ->
  wdo_pending_spec vb self fd E.
Proof using Type*.
  intros HR HL fr fp wd w i Φ Hfr.
  iIntros "HP HE HK".
  iDestruct "HP" as (fb freg st nb tw' tm' wr j (B & Hi & Hj)) "(%Hok & Hf & Hfields & Hlock & Hnb & Hdata)".
  pose proof Hok as (-> & _).
  iDestruct (bi.persistent_entails_r _ _ HR with "HE") as "[HE #(Hv & Hw & HCR)]".
  iDestruct (HL with "HE") as "(HL & Herr & HLE)".
  iApply (wp_wdo_write Hreg Hext Hfw wconv_ro (wlocale dl) Hcv fd vb fb vr freg eb wd w tw' tm' Hfd Herr
    with "Hv Hw HCR HL Herr Hf Hfields Hnb Hdata"); try assumption.
  iNext. iIntros (r st' k j' (Hr & Hok' & Hlk & Hk & Hj' & H0)) "HL Herr Hf Hfields Hnb Hdata".
  iSpecialize ("HLE" with "HL Herr"). rewrite -Hlk.
  destruct Hr as [-> | ->].
  - rewrite (H0 eq_refl). iApply ("HK" $! true with "[-HLE] HLE").
    iExists fb, freg, st', nb, tw', tm', wr, j'. iSplit; [iPureIntro; split_and!; [done|lia..]|].
    rewrite /file_wide_at. by iFrame.
  - iApply ("HK" $! false with "[-HLE] HLE").
    iExists fb, freg, st', nb, wd, w, tw', tm'. rewrite /file_wide_at. iSplit; [done|]. by iFrame.
Qed.
End use.
