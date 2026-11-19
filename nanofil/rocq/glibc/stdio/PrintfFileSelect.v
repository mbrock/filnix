(** After flushing, printf selects either its inline staging array or space
    in the stream's heap buffer. Completion needs permission to read pointers
    into the selected allocation, even when it reads no character bytes.

    This view retains the selected allocation and a way to restore the
    stream. Inline selection keeps the stream intact and borrows two shares
    of the wrapper's single lifetime instead. *)
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  PrintfStreamHeap PrintfBufferXsputnSwitch LibioPutsInv Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Section selected.
Context `{!gen_heapGS piece pval Σ}.

(** The heap alternative temporarily opens the stream to lend its lifetime.
    Returning that same share closes the stream without changing its fields. *)
Definition printf_selected (bb : Z) (p : ptr) (F : iProp Σ) : iProp Σ :=
  (⌜p = mkPtr (bb+48) (Obj bb)⌝ ∗ F) ∨
  (∃ db dr bo dq, ⌜p = mkPtr (db+bo) (Obj db) /\
    0 < db /\ 0 <= bo /\ db+bo <= r_end dr /\ r_end dr <= 2^63⌝ ∗
    liveq dq db dr ∗ (liveq dq db dr -∗ F)).

Lemma printf_selected_close bb p F : printf_selected bb p F -∗ F.
Proof using Type.
  iIntros "[[_ HF]|(%db & %dr & %bo & %dq & _ & Hd & HK)]"; first done.
  iApply ("HK" with "Hd").
Qed.

(** The borrow returns the exact selected view, including its closing rule.
    Two halves come from the wrapper only when that wrapper is the target. *)
Lemma printf_selected_borrow bb br p F :
  0 < bb -> bb+176 <= r_end br -> r_end br <= 2^63 ->
  printf_selected bb p F -∗ ∃ db dr bo dq1 dq2,
    ⌜p = mkPtr (db+bo) (Obj db) /\ 0 < db /\ 0 <= bo /\
      db+bo <= r_end dr /\ r_end dr <= 2^63⌝ ∗
    (live bb br -∗ liveq dq1 bb br ∗ liveq dq2 db dr ∗
      (liveq dq1 bb br -∗ liveq dq2 db dr -∗ live bb br ∗ printf_selected bb p F)).
Proof using Type.
  intros Hb He Hr. iIntros "[[%Hp HF]|(%db & %dr & %bo & %dq & %Hp & Hd & HK)]".
  - subst p. iExists bb, br, 48, (DfracOwn (1/2)%Qp), (DfracOwn (1/2)%Qp).
    iSplit; [iPureIntro; repeat split; try reflexivity; lia|].
    iIntros "Hb". iDestruct (LibioPutsInv.live_halves with "Hb") as "[Hb1 Hb2]".
    iFrame "Hb1 Hb2".
    iIntros "Hb1 Hb2". iSplitL "Hb1 Hb2".
    { iApply LibioPutsInv.live_halves. iFrame. }
    iLeft. iFrame. done.
  - iExists db, dr, bo, (DfracOwn 1%Qp), dq. iSplit; [done|].
    iIntros "Hb". iFrame "Hb Hd". iIntros "Hb Hd". iFrame "Hb".
    iRight. iExists db, dr, bo, dq. iFrame. done.
Qed.
End selected.

Section selection.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (B : Z -> Z -> iProp Σ).
Context `{Hswitch : !Defines ge "__printf_buffer_to_file_switch" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_switch}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Selection retains the connection between the returned pointer and its
    stream allocation. The existing switch rule performs the actual call. *)
Lemma wp_printf_file_select e from bb br vb self fp mode flags2 held base cur stop Φ :
  0 < bb -> bb mod 8 = 0 -> bb+176 <= r_end br -> r_end br <= 2^63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  live bb br -∗ pcell bb 40 fp -∗
  printf_heap_stream_with B w0 vb self fp mode flags2 held -∗
  pcell bb 0 base -∗ pcell bb 8 cur -∗ pcell bb 16 stop -∗
  ▷ (∀ start finish, live bb br -∗ pcell bb 40 fp -∗
    pcell bb 0 start -∗ pcell bb 8 start -∗ pcell bb 16 finish -∗
    printf_selected bb start (printf_heap_stream_with B w0 vb self fp mode flags2 held) -∗
    Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L40") from)) : sexpr) {{ Φ }}.
Proof using Hswitch.
  intros Hb Ha He Hr Hv. iIntros "Hb Hfp HF Hbase Hcur Hend HK".
  iDestruct "HF" as "(%fb & %fr & %st & %db & %dr & %sz & %k & %we & %xs & %fl & %tw & %off & %col & %Hp & Hf & Hst & Hrest)".
  pose proof Hp as (Hfp & Hfb & Hfa & Hfe & Hfr & _). subst fp.
  iDestruct "Hst" as "(%Hd & Hd & Hxs & Hfl & Htw & Hoff & H0 & H1 & H2 & H3 & Hwp & Hwe & H6 & H7)".
  pose proof Hd as (Hdb & Hde & Hdr & Hsz & Hk & Hlen & Hbytes & Hwc & Hwa).
  remember (ptr_addr we-db) as eo eqn:Heo.
  assert (Hwe : we = mkPtr (db+eo) (Obj db)).
  { destruct we as [a c]. cbn in *. subst c. f_equal; lia. }
  rewrite Hwe.
  iApply (wp_printf_xsputn_switch_owned e from bb br fb fr db dr k eo
    (DfracOwn 1%Qp) (DfracOwn 1%Qp)
    with "Hb Hf Hd Hfp Hwp Hwe Hbase Hcur Hend");
    try assumption; try (unfold file_size in *; lia).
  iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hcur Hend".
  iApply ("HK" with "Hb Hfp Hbase Hcur Hend").
  destruct (Z.ltb_spec k eo) as [Hspace|Hfull].
  - iRight. iExists db, dr, k, (DfracOwn 1%Qp).
    iSplit; [iPureIntro; repeat split; try reflexivity; lia|].
    iFrame "Hd". iIntros "Hd".
    iExists fb, fr, st, db, dr, sz, k, we, xs, fl, tw, off, col.
    iFrame "Hf Hrest". iSplit; [done|].
    rewrite /LibioOverflowBase.ovf_state Hwe.
    iFrame "Hd Hxs Hfl Htw Hoff H0 H1 H2 H3 Hwp Hwe H6 H7".
    iPureIntro. rewrite -Hwe. exact Hd.
  - iLeft. iSplit; [done|].
    iExists fb, fr, st, db, dr, sz, k, we, xs, fl, tw, off, col.
    iFrame "Hf Hrest". iSplit; [done|].
    rewrite /LibioOverflowBase.ovf_state Hwe.
    iFrame "Hd Hxs Hfl Htw Hoff H0 H1 H2 H3 Hwp Hwe H6 H7".
    iPureIntro. rewrite -Hwe. exact Hd.
Qed.
End selection.
