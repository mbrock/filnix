(** After formatting the unknown error number, snprintf terminates the
    active window and computes its return value. Counting reads the
    window pointers, not the bytes. This lets the caller keep the
    terminator even when the count overflows and sets errno. *)

From Glibc Require Import Unit_libio_vsnprintf_os Unit_stdioZ2dcommon_printf_buffer_done_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  ExternalMachine Pieces Heap Language Logic MemLogic.
From Glibc Require Import Fix FileInv OsWorld OsBlocks LibioLogic CStruct PrintfLayout PrintfOut PrintfSpec
  PrintfDone PrintfBufferDone PrintfBufferCount PrintfFlushStage WordString CodePrelude
  HelloCloseReportWindow HelloCloseReportFlush.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Definition report_done := Unit_libio_vsnprintf_os.fn___printf_buffer_snprintf_done.

Section done.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Variable eb : Z.
Context (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb)))
  (Hge : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb))).

(** Glibc subtracts the window's base from the write pointer to count
    its bytes. When both pointers name the discard array, it borrows
    permission to read that array from the buffer that contains it. *)
Local Lemma wp_report_count cf bb br w written mode Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done [WPtr (mkPtr bb (Obj bb))] = Some cf ->
  pwin_ok w -> 0 < bb -> bb mod 8 = 0 -> bb+40 <= r_end br -> r_end br <= 2^63 ->
  live bb br -∗ win_live bb br w -∗ int_cell bb 32 mode -∗
  pcell bb 0 (mkPtr (pw_base w) (Obj (pw_obj w))) -∗ pcell bb 8 (mkPtr (pw_ptr w) (Obj (pw_obj w))) -∗
  icell bb 24 written -∗ errno_any eb -∗
  ▷ (∀ n, ⌜0 <= n < 2^32⌝ -∗ win_live bb br w -∗ errno_any eb -∗ Φ (Ret (WInt n))) -∗ WP (ERun cf : sexpr) {{ Φ }}.
Proof using Herr Hge.
  intros Hcf Hw Hb Hal Hfit Hspace. iIntros "Hl Hd Hmode Hbase Hptr Hwr He HK".
  destruct (Z.eq_dec mode 0) as [->|Hmode].
  { iApply (wp_printf_buffer_done_failed with "Hl Hmode"); try assumption; try lia.
    iNext. iIntros "_ _". iApply ("HK" with "[%] Hd He"). lia. }
  iAssert (∃ d1 d2, liveq d1 bb br ∗ liveq d2 (pw_obj w) (pw_reg w) ∗
    (liveq d2 (pw_obj w) (pw_reg w) -∗ win_live bb br w))%I with "[Hl Hd]" as (d1 d2) "(Hl & Hd & Hback)".
  { unfold win_live. destruct (numbers.Z.eq_dec (pw_obj w) bb) as [E|E].
    - iDestruct "Hd" as %Er. rewrite E Er. iEval (rewrite /live pts_ptsq -Qp.half_half ptsq_split) in "Hl".
      iDestruct "Hl" as "[H1 H2]". iExists _, _. iFrame "H1 H2". by iIntros "_".
    - iExists (DfracOwn 1),(DfracOwn 1). iFrame "Hl Hd". by iIntros "$". }
  iEval (rewrite /icell -flush_count_repr -/icell) in "Hwr".
  set (z := written mod 2^64). assert (Hz : 0 <= z < 2^64) by (apply Z.mod_pos_bound; lia).
  set (bo := pw_base w - pw_obj w). set (used := pw_ptr w - pw_base w).
  assert (B : pw_obj w + bo = pw_base w) by (unfold bo; lia).
  assert (P : pw_base w + used = pw_ptr w) by (unfold used; lia).
  unfold pwin_ok in Hw. destruct (Z_lt_le_dec (z + used) (2^31)) as [Hsmall|Hbig].
  - pose proof (wp_printf_buffer_done_count cf bb br (pw_obj w) (pw_reg w) bo used z mode d1 d2 Φ) as C.
    rewrite B P in C. iApply (C with "Hl Hd Hmode Hbase Hptr Hwr"); try assumption; try (unfold bo, used; lia).
    iNext. iIntros "_ Hd _ _ _ _". iApply ("HK" with "[%] [Hd Hback] He"); [unfold used in *; lia|by iApply "Hback"].
  - iDestruct "He" as (bs cs [Hbs Hcs]) "He". iEval (rewrite pts_app) in "He". iDestruct "He" as "[He Hcs]".
    pose proof (wp_buffer_done_overflow cf bb br (pw_obj w) (pw_reg w) bo used z mode d1 d2 eb bs Φ) as C.
    rewrite B P in C. iApply (C with "Hl Hd Hmode Hbase Hptr Hwr He"); try assumption; try (unfold bo, used; lia).
    iNext. iIntros "_ Hd _ _ _ _ He". iApply ("HK" with "[%] [Hd Hback] [He Hcs]"); [lia|by iApply "Hback"|].
    iExists (le_bytes 75 4), cs. iSplit; [done|]. rewrite pts_app. iFrame.
Qed.

Variable db : Z.
Variable dr : region.

(** Finishing a user window turns the NUL store into a string loan.
    Finishing a discard window leaves the user's string untouched. *)
Local Lemma report_end_byte bb br w a : pwin_ok w -> pw_base w <= a < pw_end w ->
  win_own (pw_obj w) (pw_lo w) (pw_end w) -∗ snprintf_R db dr eb bb br (pw_place w) -∗
  errno_any eb ∗ ∃ x, ibyte (pw_obj w) (a - pw_obj w) x ∗
    (ibyte (pw_obj w) (a - pw_obj w) 0 -∗ win_live bb br w -∗
     ∃ s, word_string (DfracOwn 1) (mkPtr db (Obj db)) s).
Proof using Type.
  intros Hw Ha. iIntros "Hw ((%Hne & %Hapart & %Hfit & %Hspace) & $ & Hcase)".
  destruct w as [wb wr base pos stop]. iDestruct "Hcase" as "[[%E _]|[%E Hstring]]";
    injection E as -> -> -> ->; unfold pwin_ok in Hw; cbn [pw_obj pw_reg pw_base pw_ptr pw_end] in *.
  - iEval (rewrite /pw_lo /= (proj1 (proj2 Hw)) Z.sub_0_r) in "Hw".
    unfold win_live. cbn [pw_obj pw_reg]. destruct (numbers.Z.eq_dec db bb); [contradiction|].
    iApply (report_terminate with "Hw"); lia.
  - set (w' := PWin bb br (bb+40) a (bb+168)).
    iDestruct (window_byte w' with "Hw") as (x) "[Hx _]";
      [unfold w', pwin_ok; cbn [pw_obj pw_reg pw_base pw_ptr pw_end]; lia|exact (proj2 Ha)|].
    iExists x. iFrame "Hx". iIntros "_ _". iExact "Hstring".
Qed.

(** The terminator belongs at the write pointer if it is before the
    end, or at the preceding byte if the window is full. Both windows
    have positive length, so neither case needs a store outside it. *)
Lemma wp_report_done `{!Defines ge "__printf_buffer_done" Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done} cf bb Φ :
  call_frame report_done [WPtr (mkPtr bb (Obj bb))] = Some cf ->
  printf_out 2 (snprintf_R db dr eb) bb -∗
  ▷ (∀ n s, ⌜0 <= n < 2^32⌝ -∗ errno_any eb -∗ word_string (DfracOwn 1) (mkPtr db (Obj db)) s -∗
      Φ (Ret (WInt n))) -∗ WP (ERun cf : sexpr) {{ Φ }}.
Proof using Herr Hge.
  intros Hcf. injection Hcf as <-. iIntros "(%br & %w & %z & %mode & _ & HB & HR) HK". buf_open "HB".
  iAssert (⌜pw_base w < pw_end w⌝)%I as %Hlen.
  { iDestruct "HR" as "(_ & _ & [[%E _]|[%E _]])"; iPureIntro; unfold pw_place in E; injection E as _ _ B E; rewrite B E; lia. }
  step. step. check "Hl". load_window "Hl" "Hptr" "Hwl". step. check "Hl". load_window "Hl" "Hend" "Hwl".
  step. step. step. pose proof Hw as (Ho & Hal & B & P & E & F & S).
  destruct (Z_lt_le_dec (pw_ptr w) (pw_end w)) as [Hroom|Hfull].
  1: branch_as false; step; step; load_window "Hl" "Hptr" "Hwl".
  2: branch_as true; step; step; load_window "Hl" "Hptr" "Hwl"; check "Hl"; load_window "Hl" "Hbase" "Hwl";
     step; step; step; branch_as false; step; step; load_window "Hl" "Hptr" "Hwl"; step.
  2: lazymatch goal with |- context [put (TAtom "v33") (WPtr (mkPtr ?a _)) _] =>
       replace a with (pw_ptr w-1) by (cbn [ptr_addr]; Z.div_mod_to_equations; lia) end.
  1: iDestruct (report_end_byte _ _ w (pw_ptr w) Hw with "Hwin HR") as "(He & %x & Hx & Hback)"; [lia|].
  2: iDestruct (report_end_byte _ _ w (pw_ptr w-1) Hw with "Hwin HR") as "(He & %x & Hx & Hback)"; [lia|].
  all: iDestruct (win_live_acc with "Hl Hwl") as "[Hd Hrestore]"; check "Hd";
    rule2 "Hd" "Hx" ltac:(eapply wp_raw_store_byte; inst; [vx|vx|reflexivity|a2|wi_store]);
    iDestruct ("Hrestore" with "Hd") as "[Hl Hwl]"; step; step.
  all: iApply wp_call_bind; [vx|exact defines|reflexivity|]; iNext;
    iApply (wp_report_count _ bb br w z mode with "Hl Hwl Hmode Hbase Hptr Hwr He"); try assumption; try reflexivity; try lia.
  all: iNext; iIntros (n Hn) "Hwl He"; iDestruct ("Hback" with "Hx Hwl") as (s) "Hs";
    iExists _; iSplit; [done|]; iNext; iApply wp_ret; [reflexivity|vx|]; iNext;
    rewrite !(Z.mod_small n (2^32) Hn); iApply ("HK" with "[%] He Hs"); exact Hn.
Qed.

End done.
