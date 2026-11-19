(** Completing a FILE-backed printf buffer first flushes its pending bytes.
    The flush can change the buffer pointers, count, mode and errno. This
    rule takes those updated values from the supplied flush contract.

    Successful flushing leaves equal base and current pointers. Counting
    still reads both pointers, so the caller lends their allocation lifetime
    and recovers the exact shares afterward. Failure and count overflow
    remain separate outcomes; neither path promises successful output. *)
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_done_os Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  PrintfBufferDone PrintfBufferCount PrintfBufferOverflow Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Section completion.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A buffer already marked as failed returns without calling flush or count.
    The caller retains its other fields and stream ownership in the frame. *)
Lemma wp_printf_file_done_failed fr bb br Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end br -> r_end br <= 2^63 ->
  live bb br -∗ int_cell bb 32 0 -∗
  ▷ (live bb br -∗ int_cell bb 32 0 -∗ Φ (Ret (WInt 4294967295))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hb Ha He Hr. injection Hfr as <-.
  iIntros "Hb [%Hm Hmode] HK".
  step. step. check "Hb".
  load_bytes_dq "Hb Hmode" decode (cbn; reflexivity) by ar.
  iNext. iIntros "Hb Hmode". step. closed_ints. branch. step.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "Hb [Hmode]"). iSplit; [done|iExact "Hmode"].
Qed.

(** The flush contract returns the actual new header and errno values.
    Its remaining resources describe the updated stream and any caller frame.
    A successful stream view must lend the selected allocation reversibly;
    it cannot manufacture a second lifetime for inline storage. *)
Lemma wp_printf_file_done_flush fr bb br eb er mode
    (P : iProp Σ) (R : Z -> ptr -> ptr -> ptr -> Z -> iProp Σ) Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  find_fn ge (TAtom "__printf_buffer_flush_to_file") = Some (Defined Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file) ->
  find_fn ge (TAtom "__printf_buffer_done") = Some (Defined Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end br -> r_end br <= 2^63 -> mode <> 0 ->
  0 < eb -> eb + 4 <= r_end er -> r_end er <= 2^63 ->
  (forall fr' Ψ,
    call_frame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr' ->
    live bb br -∗ int_cell bb 32 mode -∗ P -∗
    (∀ m base cur stop written prior, ⌜0 <= written < 2^64⌝ -∗
      live bb br -∗ int_cell bb 32 m -∗ pcell bb 0 base -∗ pcell bb 8 cur -∗
      pcell bb 16 stop -∗ icell bb 24 written -∗
      live eb er -∗ int_cell eb 0 prior -∗ R m base cur stop written -∗ Ψ RetVoid) -∗
    WP (ERun fr' : sexpr) {{ Ψ }}) ->
  (forall m base cur stop written, m <> 0 ->
    R m base cur stop written ⊢ ∃ db dr bo dq1 dq2,
      ⌜base = mkPtr (db+bo) (Obj db) /\ cur = base /\
        0 < db /\ 0 <= bo /\ db+bo <= r_end dr /\ r_end dr <= 2^63⌝ ∗
      (live bb br -∗ liveq dq1 bb br ∗ liveq dq2 db dr ∗
        (liveq dq1 bb br -∗ liveq dq2 db dr -∗ live bb br ∗ R m base cur stop written))) ->
  live bb br -∗ int_cell bb 32 mode -∗ P -∗
  ▷ (∀ m base cur stop written prior,
    let result := if Z.eq_dec m 0 then 4294967295
      else if Z_lt_dec written (2^31) then written else 4294967295 in
    let err := if Z.eq_dec m 0 then prior
      else if Z_lt_dec written (2^31) then prior else 75 in
    live bb br -∗ int_cell bb 32 m -∗ pcell bb 0 base -∗ pcell bb 8 cur -∗
    pcell bb 16 stop -∗ icell bb 24 written -∗
    live eb er -∗ int_cell eb 0 err -∗ R m base cur stop written -∗
    Φ (Ret (WInt result))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hflushfn Hdonefn Herr Hb Ha He Hr Hmode Heb Hee Her Hflush Hborrow.
  injection Hfr as <-. iIntros "Hb [%Hm Hmode] HP HK".
  step. step. check "Hb".
  iApply (wp_raw_load_sub_bytes_dq with "Hb Hmode");
    [reflexivity | reflexivity | reflexivity |
     unfold int_bytes; rewrite of_bytes_int; [cbn; rewrite !(Z.mod_small mode (2^32) Hm); reflexivity|exact Hm] |
     left; reflexivity | ar |].
  iNext. iIntros "Hb Hmode". step. branch_as true. step.
  iApply wp_call_bind; [vx | exact Hflushfn | reflexivity |]. iNext.
  iApply (Hflush _ _ eq_refl with "Hb [Hmode] HP"); [iSplit; [done|iExact "Hmode"]|].
  iIntros (m base cur stop written prior Hw) "Hb Hmode Hbase Hcur Hend Hw Hel Herr HR".
  resume. iApply wp_call_bind; [vx | exact Hdonefn | reflexivity |]. iNext.
  destruct (Z.eq_dec m 0) as [->|Hnz].
  - iApply (wp_printf_buffer_done_failed _ bb br with "Hb Hmode"); try assumption; [reflexivity|].
    iNext. iIntros "Hb Hmode". resume.
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    iApply ("HK" $! 0 base cur stop written prior with "Hb Hmode Hbase Hcur Hend Hw Hel Herr HR").
  - iDestruct (Hborrow m base cur stop written Hnz with "HR")
      as (db dr bo dq1 dq2 (Hbase & Hcur & Hdb & Hbo & Hde & Hdr)) "Hlend".
    subst cur base. iDestruct ("Hlend" with "Hb") as "(Hb & Hd & Hrestore)".
    destruct (Z_lt_dec written (2^31)) as [Hcount|Hoverflow].
    + pose proof (fun fr' => wp_printf_buffer_done_count fr' bb br db dr bo 0 written m dq1 dq2) as Hcount_rule.
      rewrite !Z.add_0_r in Hcount_rule.
      iApply (Hcount_rule with "Hb Hd Hmode Hbase Hcur Hw"); try assumption; try lia; [reflexivity|].
      iNext. iIntros "Hb Hd Hmode Hbase Hcur Hw".
      iDestruct ("Hrestore" with "Hb Hd") as "[Hb HR]".
      resume. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      iSpecialize ("HK" $! m (mkPtr (db+bo) (Obj db)) (mkPtr (db+bo) (Obj db)) stop written prior).
      destruct (Z.eq_dec m 0); [contradiction|]. destruct (Z_lt_dec written (2^31)); [|lia].
      replace (written+0) with written by lia.
      norm.
      iApply ("HK" with "Hb Hmode Hbase Hcur Hend Hw Hel Herr HR").
    + pose proof (fun fr' => wp_printf_buffer_done_overflow fr' bb br db dr bo 0 written m dq1 dq2 eb er 0 prior) as Hoverflow_rule.
      rewrite !Z.add_0_r in Hoverflow_rule.
      iApply (Hoverflow_rule with "Hb Hd Hmode Hbase Hcur Hw Hel Herr"); try assumption; try lia;
        [reflexivity|].
      iNext. iIntros "Hb Hd Hmode Hbase Hcur Hw Hel Herr".
      iDestruct ("Hrestore" with "Hb Hd") as "[Hb HR]".
      resume. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      iSpecialize ("HK" $! m (mkPtr (db+bo) (Obj db)) (mkPtr (db+bo) (Obj db)) stop written prior).
      destruct (Z.eq_dec m 0); [contradiction|]. destruct (Z_lt_dec written (2^31)); [lia|].
      iApply ("HK" with "Hb Hmode Hbase Hcur Hend Hw Hel Herr HR").
Qed.
End completion.
