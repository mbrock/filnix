(** Glibc's snprintf writes into the caller's array until it has to
    flush. On the first flush it terminates the array and redirects
    further output to its own discard buffer. Later flushes reset the
    discard buffer without touching the caller's string. *)

From Glibc Require Import Unit_libio_vsnprintf_os Unit_stdioZ2dcommon_printf_buffer_flush_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  ExternalMachine Pieces Heap Language Logic StringLogic MemLogic.
From Glibc Require Import Fix FileInv OsWorld OsBlocks LibioLogic CStruct PrintfLayout PrintfOut PrintfSpec
  PrintfFlushStage WordString CodePrelude HelloCloseReportWindow.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Definition report_flush := Unit_libio_vsnprintf_os.fn___printf_buffer_flush_snprintf.

Section flush.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Variable db : Z.
Variable dr : region.
Variable eb : Z.

(** The formatter owns the active window. The backend keeps the other
    one: either an unused discard buffer or a terminated string in the
    caller's array. It also holds errno for the formatter to borrow. *)
Definition snprintf_R (bb : Z) (br : region) (place : Z * region * Z * Z) : iProp Σ :=
  ⌜(db <> bb /\ db <> bb+40 /\ bb+168 <= r_end br /\ r_end dr <= 2^48)%Z⌝ ∗ errno_any eb ∗
  ((⌜place = (db, dr, db, (db+1024)%Z)⌝ ∗ win_own bb (bb+40) (bb+168)) ∨
   (⌜place = (bb, br, (bb+40)%Z, (bb+168)%Z)⌝ ∗ ∃ s, word_string (DfracOwn 1) (mkPtr db (Obj db)) s)).

Lemma snprintf_lends_errno bb : ⊢ lends_errno snprintf_R bb eb.
Proof using Type.
  iModIntro. iIntros (br pl) "(%H & He & Hwin)". iFrame "He". iIntros "He". by iFrame.
Qed.

Local Ltac window_branch b :=
  branch_symbolic; lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let E := fresh in assert (E : c = b) by (cbn [pw_base pw_ptr pw_end]; decide_ints); rewrite E; clear E end; cbn [edge_label].

(** Every flush leaves room for another byte in the discard buffer.
    The count may wrap, but the count never selects an address. *)
Lemma wp_report_flush cf bb br w written Φ :
  call_frame report_flush [WPtr (mkPtr bb (Obj bb))] = Some cf ->
  printf_buf bb br w written 2 -∗ snprintf_R bb br (pw_place w) -∗
  ▷ (∀ total, printf_buf bb br (PWin bb br (bb+40) (bb+40) (bb+168)) total 2 -∗
    snprintf_R bb br (bb, br, bb+40, bb+168) -∗ Φ RetVoid) -∗ WP (ERun cf : sexpr) {{ Φ }}.
Proof using Type.
  intros Hcf. injection Hcf as <-. iIntros "Hbuf (%H & He & Hcase) HK".
  destruct H as (Hne & Hapart & Hfit & Hspace). buf_open "Hbuf".
  iEval (rewrite /icell -flush_count_repr -/icell) in "Hwr".
  set (v := written mod 2^64). assert (Hv : 0 <= v < 2^64) by (apply Z.mod_pos_bound; lia).
  step. step. check "Hl". iApply (wp_raw_load_read_dq with "Hl Hwr"); [reflexivity|vx|left; reflexivity|a2|].
  iNext. iIntros "Hl Hwr". step. check "Hl". load_window "Hl" "Hptr" "Hwl".
  check "Hl". load_window "Hl" "Hbase" "Hwl". step. step. step. step. check "Hl". store_long "Hl" "Hwr".
  load_window "Hl" "Hbase" "Hwl". step. step. step. step.
  destruct w as [wb wr base pos stop]. iDestruct "Hcase" as "[[%Hplace Hdiscard]|[%Hplace Hstring]]";
    injection Hplace as -> -> -> ->; unfold pwin_ok in Hw; cbn [pw_obj pw_reg pw_base pw_ptr pw_end] in Hw.
  1: window_branch false; step; load_window "Hl" "Hbase" "Hwl"; step; load_window "Hl" "Hend" "Hwl".
  1: step; step; step; window_branch false; step; step; load_window "Hl" "Hend" "Hwl"; step.
  1: lazymatch goal with |- context [put (TAtom "v40") (WPtr (mkPtr ?a _)) _] =>
       replace a with (db+1023) by (cbn [ptr_addr pw_end]; Z.div_mod_to_equations; lia) end.
  2: window_branch true; iEval (rewrite /pw_lo; cbn [pw_obj pw_base pw_end];
       replace ((bb+40) mod 8) with 0 by (Z.div_mod_to_equations; lia); rewrite Z.sub_0_r) in "Hwin";
       iRename "Hwin" into "Hdiscard".
  1: (
    iEval (rewrite /pw_lo /= (proj1 (proj2 Hw)) Z.sub_0_r) in "Hwin";
    iDestruct (report_terminate db dr 1023 with "Hwin") as (x) "[Hx Hstring]"; try lia;
    unfold win_live; cbn [pw_obj pw_reg]; destruct (numbers.Z.eq_dec db bb); [contradiction|];
    check "Hwl"; rule2 "Hwl" "Hx" ltac:(eapply wp_raw_store_byte; inst; [vx|vx|reflexivity|a2|wi_store]);
    iDestruct ("Hstring" with "Hx Hwl") as "Hstring";
    step; step; step; check "Hl"; store "Hl" "Hbase"; step; check "Hl"; store "Hl" "Hptr";
    step; step; check "Hl"; store "Hl" "Hend"; step).
  all: step; step; check "Hl"; store "Hl" "Hbase"; step; check "Hl"; store "Hl" "Hptr"; iApply wp_ret_void; iNext.
  all: iApply ("HK" with "[Hl Hbase Hptr Hend Hwr Hmode Hdiscard] [He Hstring]");
    last (iSplit; [done|]; iFrame "He"; iRight; by iFrame).
  all: unfold printf_buf, win_live, pw_lo; cbn [pw_obj pw_reg pw_end pw_base pw_ptr];
    destruct (numbers.Z.eq_dec bb bb); [|contradiction];
    replace ((bb+40) mod 8) with 0 by (Z.div_mod_to_equations; lia); rewrite Z.sub_0_r; iFrame "Hdiscard";
    iSplit; [iPureIntro; unfold pwin_ok; cbn [pw_base pw_ptr pw_obj pw_end pw_reg]; lia|];
    iSplitL "Hl"; [struct_live_close "Hl"|]; iSplitL; [|done]; iEval (struct_cells);
    cbn [pw_base pw_ptr pw_end pw_obj ptr_addr ptr_cap]; iFrame "Hwr Hmode"; unwrap2;
    try replace (bb+40+128) with (bb+168) by lia; iFrame.
Qed.

(** The dispatcher returns zero immediately for a failed buffer. For
    mode 2 it calls the snprintf flush, checks that the new write
    pointer has room, and returns one. *)
Lemma report_flush_has_spec `{!Defines ge "__printf_buffer_flush_snprintf" report_flush}
    `{!Defines ge "__printf_buffer_flush" Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush") (flush_spec 2 snprintf_R).
Proof using Type*.
  intros bb. exists Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush. split; [exact defines|]. split; [eexists; reflexivity|].
  intros cf Φ Hcf. injection Hcf as <-. iIntros "(%br & %w & %written & %mode & %Hmd & Hbuf & HR) HK".
  buf_open "Hbuf". step. step. check "Hl". load_mode "Hl" "Hmode". step. destruct Hmd as [-> | ->]; branch.
  - step. iApply wp_ret; [reflexivity|vx|]. iNext. iApply "HK".
    iExists 0, br, w, written, mode_failed. iFrame "HR". iSplit; [iPureIntro; intuition lia|]. buf_close. exact Hw.
  - clear Hmode_range. step. step. load_mode "Hl" "Hmode". step. branch.
    do 4 (step; step; branch). step.
    iApply wp_call_bind; [vx|exact (defines (n:="__printf_buffer_flush_snprintf"))|reflexivity|]. iNext.
    iApply (wp_report_flush _ bb br w written with "[Hl Hbase Hptr Hend Hwr Hmode Hwl Hwin] HR");
      [reflexivity|buf_close; exact Hw|].
    iNext. iIntros (n) "HB HR". iExists _. iSplit; [done|]. iNext.
    clear Hmode_range Hbb Hw. buf_open "HB". step. step. step. check "Hl". load_mode "Hl" "Hmode". step. branch.
    step. step. check "Hl". load_window "Hl" "Hptr" "Hwl". step. load_window "Hl" "Hend" "Hwl".
    step. step. step. unfold pwin_ok in Hw. cbn [pw_obj pw_reg pw_base pw_ptr pw_end] in Hw. window_branch false.
    step. iApply wp_ret; [reflexivity|vx|]. iNext. iApply "HK".
    iExists 1, br, (PWin bb br (bb+40) (bb+40) (bb+168)), n, 2. iFrame "HR".
    iSplit; [iPureIntro; cbn [pw_ptr pw_end]; intuition lia|]. buf_close. exact Hw.
Qed.
End flush.
