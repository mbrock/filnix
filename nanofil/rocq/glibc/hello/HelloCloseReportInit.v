(** Snprintf sets up its output window before it reads the format. The
    write pointer starts at the caller's array, whose first byte glibc
    sets to zero. The 128-byte discard array in the printf buffer is
    not part of the caller's string. *)

From Glibc Require Import Unit_libio_vsnprintf_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  ExternalMachine Pieces Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import Fix FileInv OsWorld OsBlocks LibioLogic CStruct PrintfLayout PrintfOut PrintfSpec
  FormatterStringArg CodePrelude HelloImageModule HelloCloseReportFlush.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic StringVL.
Open Scope Z_scope.

Definition report_init := Unit_libio_vsnprintf_os.fn___printf_buffer_snprintf_init.

Section init.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The array can contain any bytes before the call. Its base and the
    new printf buffer are both 16-aligned, so the array cannot start
    at offset 40 in the new buffer. *)
Lemma wp_report_init cf bb db dr eb Φ :
  0 < bb -> bb mod 16 = 0 -> bb+176 <= 2^48 ->
  0 < db -> db mod 16 = 0 -> db+1024 <= r_end dr -> r_end dr <= 2^48 ->
  call_frame report_init [WPtr (mkPtr bb (Obj bb)); WPtr (mkPtr db (Obj db)); WInt 1024] = Some cf ->
  obj bb (heap_req 8 168) -∗ live db dr -∗ win_own db db (db+1024) -∗ errno_any eb -∗
  ▷ (printf_out 2 (snprintf_R db dr eb) bb -∗ Φ RetVoid) -∗ WP (ERun cf : sexpr) {{ Φ }}.
Proof using Type.
  intros Hb Hb16 Hbe Hd Hd16 Hde Hspace Hcf. injection Hcf as <-. iIntros "HB Hd Hwin He HK".
  set (br := mkRegion bb (bb+176) Heap Live).
  assert (Hb8 : bb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hd8 : db mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "HB") as "(Hl & Hx & Ha)"; [compute; discriminate|].
  change (Z.to_nat (req_extent (heap_req 8 168))) with 176%nat.
  iAssert (live bb br) with "Hl" as "Hl". assert (Ebr : r_end br = bb+176) by reflexivity.
  iAssert (⌜db <> bb⌝)%I as %Hne.
  { iDestruct "Hd" as "[H1 _]". iDestruct "Hl" as "[H2 _]". iDestruct (pointsto_ne with "H1 H2") as %H.
    iPureIntro. cbn [fst] in H. congruence. }
  change (replicate 176 0) with (replicate (8+(8+(8+(8+(4+4+(128+8)))))) 0).
  change (replicate 176 CNone) with (replicate (8+(8+(8+(8+(8+(128+8)))))) CNone).
  iDestruct (zero_cell_prefix with "Hx Ha") as "(Hbase & Hx & Ha)".
  iDestruct (zero_cell_prefix with "Hx Ha") as "(Hptr & Hx & Ha)".
  iDestruct (zero_cell_prefix with "Hx Ha") as "(Hend & Hx & Ha)".
  iDestruct (zero_cell_prefix with "Hx Ha") as "(Hwr & Hx & Ha)".
  iEval (rewrite /pcell /pts big_sepL_cons) in "Hwr". iDestruct "Hwr" as "[_ Hwr]".
  iEval (rewrite (replicate_add (4+4)) (replicate_add 4) (replicate_add 128) !byte_ps_app !pts_app) in "Hx".
  iDestruct "Hx" as "[[Hmode _] [Hx _]]".
  iEval (rewrite (replicate_add 8) (replicate_add 128) !aux_ps_app !pts_app) in "Ha". iDestruct "Ha" as "[_ [Ha _]]".
  cbn [length replicate app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. cbn [Z.add Pos.add Pos.succ Pos.add_carry].
  set (w := PWin db dr db db (db+1024)). assert (Hw : pwin_ok w) by (unfold w, pwin_ok; cbn; lia).
  iAssert (win_own (pw_obj w) (pw_lo w) (pw_end w)) with "[Hwin]" as "Hwin".
  { unfold w, pw_lo. cbn [pw_obj pw_base pw_end]. rewrite Hd8 Z.sub_0_r. iExact "Hwin". }
  step. step. check "Hl". store "Hl" "Hbase". step. check "Hl". store "Hl" "Hptr".
  step. check "Hl". store "Hl" "Hend". step. check "Hl". store_long "Hl" "Hwr".
  step. check "Hl". store_int "Hl" "Hmode". step. branch. step.
  iDestruct (window_byte w Hw with "Hwin") as (x) "[Hx0 Hback]"; [unfold w; cbn; lia|].
  iEval (unfold w; cbn [pw_obj pw_ptr]; rewrite Z.sub_diag) in "Hx0".
  check "Hd". rule2 "Hd" "Hx0" ltac:(eapply wp_raw_store_byte; inst; [vx|vx|reflexivity|a2|wi_store]).
  iDestruct ("Hback" $! 0 with "[%] [Hx0]") as "Hwin"; [lia|unfold w; cbn [pw_obj pw_ptr]; by rewrite Z.sub_diag|].
  step. step. iApply wp_ret_void. iNext. iApply "HK". iExists br,w,0,2. iSplit; [by iPureIntro; right|].
  iSplitR "Hx Ha He".
  - iSplit; [done|]. iSplitL "Hl"; [struct_live_close "Hl"|]. iSplitR "Hd Hwin".
    + iEval (struct_cells). unfold w. cbn [pw_obj pw_base pw_ptr pw_end ptr_addr ptr_cap]. unwrap2. iFrame. done.
    + iFrame "Hwin". unfold win_live, w. cbn [pw_obj pw_reg]. destruct (numbers.Z.eq_dec db bb); done.
  - iSplit; [iPureIntro; split_and!; first [assumption|Z.div_mod_to_equations; lia]|]. iFrame "He". iLeft. iSplit; [done|].
    iExists (replicate 128 0), (replicate 128 CNone). replace (bb+40-bb) with 40 by lia. iFrame "Hx Ha".
    iPureIntro. rewrite !length_replicate. split_and!; [lia|reflexivity|by apply Forall_replicate].
Qed.
End init.
