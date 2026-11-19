(** Completing a staged FILE buffer runs the checked flush and count calls.
    A count mismatch keeps the staging pointers and returns failure.
    An exact write selects a new buffer before completion reads its pointers.

    The stream backend remains a supplied contract, with arbitrary framed
    resources and errno that may change. This rule restores the stream after
    borrowing the selected lifetime. It does not prove that output succeeds. *)
From Glibc Require Import Unit_libio_fileops_os Unit_stdioZ2dcommon_printf_buffer_done_os Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic
  PrintfStreamHeap PrintfBufferXsputnCall
  PrintfFileSelect PrintfFileDone PrintfFileFlush Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic.
Open Scope Z_scope.
Section completion.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (B : Z -> Z -> iProp Σ) (vb : Z) (self : ptr)
  (mode flags2 : Z) (held : option Z) (E : iProp Σ) (eb : Z) (er : region).
Let F fp := printf_heap_stream_with B w0 vb self fp mode flags2 held.
Let Ex := (E ∗ ∃ prior, live eb er ∗ int_cell eb 0 prior)%I.
Context `{Hswitch : !Defines ge "__printf_buffer_to_file_switch" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_switch}.
Context (Hfn : ge_fn ge "_IO_new_file_xsputn" Unit_libio_fileops_os.fn__IO_new_file_xsputn).
Context (Hcall : printf_xsputn_call_spec w0 registry ge F Ex).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The result distinguishes failure, an in-range count and overflow.
    The count is the actual unsigned update performed before the stream call;
    overflow changes the errno returned by that call to EOVERFLOW. *)
Lemma wp_printf_file_staging_done fr bb br fb vr xs written prior Φ :
  let n := Z.of_nat (length xs) in
  let total := (written+n) mod 2^64 in
  call_frame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  find_fn ge (TAtom "__printf_buffer_flush_to_file") = Some (Defined Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file) ->
  find_fn ge (TAtom "__printf_buffer_done") = Some (Defined Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> bb mod 8 = 0 -> bb+176 <= r_end br -> r_end br <= 2^63 ->
  0 < fb -> fb mod 8 = 0 -> n <= 128 -> Forall (fun x => 0 <= x < 256) xs ->
  0 <= written < 2^64 -> 0 < eb -> eb+4 <= r_end er -> r_end er <= 2^63 ->
  vtables_ro ge vb vr -∗ live bb br -∗
  pcell bb 0 (mkPtr (bb+48) (Obj bb)) -∗ pcell bb 8 (mkPtr (bb+48+n) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb+176) (Obj bb)) -∗ icell bb 24 written -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 xs -∗ int_cell bb 32 4 -∗
  F (mkPtr fb (Obj fb)) -∗ E -∗ live eb er -∗ int_cell eb 0 prior -∗
  ▷ (∀ m base cur stop err,
    ⌜(m = 0 /\ base = mkPtr (bb+48) (Obj bb) /\
        cur = mkPtr (bb+48+n) (Obj bb) /\ stop = mkPtr (bb+176) (Obj bb)) \/
      (m = 4 /\ cur = base)⌝ -∗
    live bb br -∗ pcell bb 0 base -∗ pcell bb 8 cur -∗ pcell bb 16 stop -∗
    icell bb 24 total -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗
    bytes bb 48 xs -∗ int_cell bb 32 m -∗ F (mkPtr fb (Obj fb)) -∗ E -∗
    live eb er -∗ int_cell eb 0 (if Z.eq_dec m 0 then err
      else if Z_lt_dec total (2^31) then err else 75) -∗
    Φ (Ret (WInt (if Z.eq_dec m 0 then 4294967295
      else if Z_lt_dec total (2^31) then total else 4294967295)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  cbn zeta. intros Hfr Hflushfn Hdonefn Herr Hb Ha He Hr Hfb Hfa Hlen Hxs Hw Heb Hee Her.
  set (n := Z.of_nat (length xs)).
  set (total := (written+n) mod 2^64).
  set (R := fun m base cur stop w => (⌜w = total⌝ ∗
    pcell bb 40 (mkPtr fb (Obj fb)) ∗ bytes bb 48 xs ∗ E ∗
    ((⌜m = 0 /\ base = mkPtr (bb+48) (Obj bb) /\
      cur = mkPtr (bb+48+n) (Obj bb) /\ stop = mkPtr (bb+176) (Obj bb)⌝ ∗ F (mkPtr fb (Obj fb))) ∨
     (⌜m = 4 /\ cur = base⌝ ∗ printf_selected bb base (F (mkPtr fb (Obj fb))))))%I).
  set (P := (vtables_ro ge vb vr ∗ pcell bb 0 (mkPtr (bb+48) (Obj bb)) ∗
    pcell bb 8 (mkPtr (bb+48+n) (Obj bb)) ∗ pcell bb 16 (mkPtr (bb+176) (Obj bb)) ∗
    icell bb 24 written ∗ pcell bb 40 (mkPtr fb (Obj fb)) ∗ bytes bb 48 xs ∗
    F (mkPtr fb (Obj fb)) ∗ Ex)%I).
  iIntros "#Hvt Hb Hbase Hcur Hend Hw Hfp Hxs Hmode HF HE Hel Herr HK".
  iApply (wp_printf_file_done_flush fr bb br eb er 4 P R
    with "Hb Hmode [Hbase Hcur Hend Hw Hfp Hxs HF HE Hel Herr]");
    try assumption; try lia.
  - intros fr' Ψ Hframe. iIntros "Hb Hmode (#Hvt & Hbase & Hcur & Hend & Hw & Hfp & Hxs & HF & HE) HK".
    iApply (wp_wand with "[-HK]").
    { iApply (wp_printf_file_flush B vb self mode flags2 held Ex Hfn Hcall fr' bb br fb vr xs written
        with "Hvt Hb Hbase Hcur Hend Hw Hfp Hxs Hmode HF HE"); assumption. }
    iIntros (v) "(%Hv & Hb & Hw & Hfp & Hxs & HE & Hout)". subst v.
    iDestruct "HE" as "(HE & %err & Hel & Herr)".
    iDestruct "Hout" as "[(Hmode & Hbase & Hcur & Hend & HF)|(%start & %stop & Hmode & Hbase & Hcur & Hend & Hselected)]".
    + iApply ("HK" $! 0 _ _ _ total err with "[%] Hb Hmode Hbase Hcur Hend Hw Hel Herr [Hfp Hxs HE HF]").
      { unfold total. apply Z.mod_pos_bound. lia. }
      rewrite /R. iFrame. iSplit; [done|]. iLeft. iFrame. done.
    + iApply ("HK" $! 4 start start stop total err with "[%] Hb Hmode Hbase Hcur Hend Hw Hel Herr [Hfp Hxs HE Hselected]").
      { unfold total. apply Z.mod_pos_bound. lia. }
      rewrite /R. iFrame. iSplit; [done|]. iRight. iFrame. done.
  - intros m base cur stop w Hnz. iIntros "(%Hw' & Hfp & Hxs & HE & Hout)".
    iDestruct "Hout" as "[[%Hfail HF]|[%Hsuccess Hselected]]".
    { destruct Hfail as [Hfail _]. contradiction. }
    destruct Hsuccess as [Hm Hcur]. subst cur.
    iDestruct (printf_selected_borrow bb br base with "Hselected")
      as (db dr bo dq1 dq2 Hp) "Hlend"; try assumption.
    iExists db, dr, bo, dq1, dq2. iSplit; [iPureIntro; tauto|].
    iIntros "Hb". iDestruct ("Hlend" with "Hb") as "(Hb & Hd & Hrestore)".
    iFrame "Hb Hd". iIntros "Hb Hd".
    iDestruct ("Hrestore" with "Hb Hd") as "[Hb Hselected]". iFrame "Hb".
    rewrite /R. iFrame. iSplit; [done|]. iRight. iFrame. done.
  - rewrite /P /Ex. iFrame "Hvt Hbase Hcur Hend Hw Hfp Hxs HF HE". iExists prior. iFrame.
  - iNext. iIntros (m base cur stop w err) "Hb Hmode Hbase Hcur Hend Hw Hel Herr HR".
    iDestruct "HR" as "(%Hw' & Hfp & Hxs & HE & Hout)". subst w.
    iDestruct "Hout" as "[[%Hfail HF]|[%Hsuccess Hselected]]".
    + iApply ("HK" $! m base cur stop err with "[%] Hb Hbase Hcur Hend Hw Hfp Hxs Hmode HF HE Hel Herr"). tauto.
    + iDestruct (printf_selected_close with "Hselected") as "HF".
      iApply ("HK" $! m base cur stop err with "[%] Hb Hbase Hcur Hend Hw Hfp Hxs Hmode HF HE Hel Herr"). tauto.
Qed.
End completion.
