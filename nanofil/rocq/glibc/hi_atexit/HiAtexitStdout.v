(** Closing stdout must remain safe when a write fails or writes only
    part of the string. This file keeps the buffer and lock resources
    across puts so the close proof can use them. It records allocation
    independently of the returned byte count and leaves the generic
    FILE predicates unchanged. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioDefaultXsputnBuf LibioXsputnBase LibioPutsInv HiAtexitBase HiAtexitOutputState.
Import ListNotations.
Open Scope Z_scope.

(** The stream views use the same interpreter logic as output. *)
Module HPI := LibioPutsInvOn InterpRuntime HLG.
Import HPI HPI.CS HPI.CS.SW HPI.CS.SW.FI.ML HPI.CS.SW.FI.LG HPI.CS.SW.FI.L
  HPI.CS.SW.OW HPI.CS.SW.FI HPI.CS.SW.ST.
Import HXB HXB.DX.RM.SM.TL.BY.BF.

Section streams.
Context `{!gen_heapGS piece pval Σ}.

(** Output leaves the saved-buffer pointers and lock pointer alone.
    The lock state changes when puts acquires and releases it. *)
Definition hi_stdout_tail (self : ptr) (fb lb : Z) (held : option Z) : iProp Σ :=
  pcell fb 72 null ∗ pcell fb 80 null ∗ pcell fb 96 null ∗
    pcell fb off_lock (mkPtr lb (Obj lb)) ∗ lock_inv self (mkPtr lb (Obj lb)) held.

(** The input predicate names the physical mode so puts can orient
    stdout. Its buffer may still be absent before the first output. *)
Definition hi_stdout_before (w0 : os_world) (eb vb : Z) (fp : ptr) (mode : Z) (held : option Z) : iProp Σ :=
  ∃ fb freg nb wp we lb fl f2 fd tw off,
    ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\
      r_end freg <= 2 ^ 63 /\ 0 < lb⌝ ∗
    live fb freg ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗ wbuf fb nb wp we ∗
    xfields_body w0 eb fb nb fl f2 fd tw off mode ∗ hi_stdout_tail (ow_self w0) fb lb held.

(** The output predicate preserves every resource needed for close.
    A nonempty source guarantees a buffer, including on failure. Its
    physical mode remains narrow but need not be exposed to unlocking. *)
Definition hi_stdout_after (w0 : os_world) (eb vb : Z) (s : list Z) (fp : ptr) (held : option Z) : iProp Σ :=
  ∃ fb freg nb wp we lb,
    ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\
      r_end freg <= 2 ^ 63 /\ 0 < lb /\ (s <> [] -> nb <> None)⌝ ∗
    live fb freg ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗ wbuf fb nb wp we ∗
    xfields w0 eb fb nb ∗ hi_stdout_tail (ow_self w0) fb lb held.

(** Taking stdout's lock and choosing byte output leave its buffer
    intact. This rule returns all the stream resources after either
    operation and prevents either step from introducing wide output. *)
Lemma hi_stdout_before_open w0 eb vb fp mode held :
  hi_stdout_before w0 eb vb fp mode held ⊢
  file_open vb (ow_self w0) (hi_stdout_before w0 eb vb) fp mode held.
Proof.
  iIntros "(%fb & %freg & %nb & %wp & %we & %lb & %fl & %f2 & %fd & %tw & %off & %Hp &
    Hl & Hvtp & Hwb & Hxf & Htail)".
  destruct Hp as (Hfp & Hfb & Hal & Hend & Hreg & Hlb).
  iDestruct "Hxf" as "(%Hfields & Hfl & Hfl2 & Hfd & Htw & Hoff & Hcol & Hmd & Herr)".
  destruct Hfields as (Happ & Hf22 & Hfd & Hm & Hflags & Hfd31 & Hf2160).
  iDestruct "Hfl" as "[%Hflr Hfl]".
  iDestruct "Htail" as "(H72 & H80 & H96 & Hlp & Hlk)".
  assert (Hul : has fl io_user_lock = false).
  { unfold has. rewrite (xs_flags_mask _ _ io_user_lock eq_refl Hflags). reflexivity. }
  assert (Hmv : mode_vtable mode vt_file) by (left; tauto).
  iExists fb, freg, fl, lb, vt_file. iFrame "Hl Hlp Hlk Hmd Hvtp".
  iSplitR; [iPureIntro; tauto|]. iSplitL "Hfl"; [iSplit; done|].
  iIntros (mode' held' Hmv') "Hl Hfl Hlp Hlk Hmd Hvtp".
  assert (Hm' : mode' = 0 \/ mode' = 2 ^ 32 - 1).
  { destruct Hmv' as [[Hnarrow _] | [_ Hbad]]; [exact Hnarrow | unfold vt_file, vt_wfile in Hbad; lia]. }
  iExists fb, freg, nb, wp, we, lb, fl, f2, fd, tw, off.
  iFrame "Hl Hvtp Hwb". iSplitR; [iPureIntro; tauto|].
  iSplitL "Hfl Hfl2 Hfd Htw Hoff Hcol Hmd Herr".
  - unfold xfields_body. iFrame. iPureIntro. tauto.
  - unfold hi_stdout_tail. iFrame.
Qed.

(** The input predicate cannot describe a wide stream. The generic
    puts proof's skipped-output branch is therefore unreachable here. *)
Lemma hi_stdout_before_wide w0 eb vb s fp held :
  hi_stdout_before w0 eb vb fp 1 held ⊢ hi_stdout_after w0 eb vb s fp held.
Proof.
  iIntros "(%fb & %freg & %nb & %wp & %we & %lb & %fl & %f2 & %fd & %tw & %off & _ &
    _ & _ & _ & Hxf & _)".
  iDestruct "Hxf" as "[%Hp _]". destruct Hp as (_ & _ & _ & Hm & _). destruct Hm; lia.
Qed.

(** Unlocking preserves the output invariant without asking its
    existential mode to equal a caller-chosen mode. *)
Lemma hi_stdout_after_lock w0 eb vb s fp held :
  hi_stdout_after w0 eb vb s fp held ⊢
  file_lock_open (ow_self w0) fp (hi_stdout_after w0 eb vb s fp) held.
Proof.
  iIntros "(%fb & %freg & %nb & %wp & %we & %lb & %Hp & Hl & Hvtp & Hwb & Hxf & Htail)".
  destruct Hp as (Hfp & Hfb & Hal & Hend & Hreg & Hlb & Hprogress).
  iDestruct "Hxf" as (fl f2 fd tw off m Hfields) "(Hfl & Hfl2 & Hfd & Htw & Hoff & Hcol & Hmd & Herr)".
  destruct Hfields as (Happ & Hf22 & Hfd & Hm & Hflags & Hfd31 & Hf2160).
  iDestruct "Hfl" as "[%Hflr Hfl]".
  iDestruct "Htail" as "(H72 & H80 & H96 & Hlp & Hlk)".
  assert (Hul : has fl io_user_lock = false).
  { unfold has. rewrite (xs_flags_mask _ _ io_user_lock eq_refl Hflags). reflexivity. }
  iExists fb, freg, fl, lb. iFrame "Hl Hlp Hlk".
  iSplitR; [iPureIntro; tauto|]. iSplitL "Hfl"; [iSplit; done|].
  iIntros (held') "Hl Hfl Hlp Hlk".
  iExists fb, freg, nb, wp, we, lb. iFrame "Hl Hvtp Hwb". iSplitR; [iPureIntro; tauto|].
  iSplitL "Hfl Hfl2 Hfd Htw Hoff Hcol Hmd Herr".
  - iExists fl, f2, fd, tw, off, m. unfold xfields_body. iFrame. iPureIntro. tauto.
  - unfold hi_stdout_tail. iFrame.
Qed.

End streams.
