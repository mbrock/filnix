(** When printf writes straight into a stream's heap buffer, flushing
    publishes the new write pointer to the stream. If room remains,
    printf continues there. A full buffer makes printf select its
    one-byte stage instead. Neither branch calls libio or writes any
    character bytes. *)

From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic CStruct PrintfLayout PrintfOut
  PrintfFlushStage PrintfBufferFlushDirect PrintfBufferFlushFull.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** A direct window always started with room. Flushing it leaves the
    next window empty, even when the write pointer has reached the end
    and the new window lies in a different object. *)
Definition published_window bb br w :=
  if Z.eq_dec (pw_ptr w) (pw_end w) then staged bb br 0 1
  else PWin (pw_obj w) (pw_reg w) (pw_ptr w) (pw_ptr w) (pw_end w).

Lemma published_room bb br w : pwin_ok w ->
  let next := published_window bb br w in pw_base next = pw_ptr next /\ pw_ptr next < pw_end next.
Proof. intros Hok. unfold published_window, pwin_ok in *. destruct (Z.eq_dec _ _); cbn [staged pw_ptr pw_end pw_base]; lia. Qed.

Section publish.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The stream lends its two fields while printf publishes its write
    pointer. The write end stays fixed. The caller recovers the old
    window's bytes and slots, even when the new window points elsewhere. *)
Lemma wp_flush_publish fr bb br fb freg w written Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  bb+176 <= r_end br -> pw_obj w <> bb -> pw_end w <= bb \/ bb+176 < pw_end w ->
  let fp := mkPtr fb (Obj fb) in
  let dp a := mkPtr a (Obj (pw_obj w)) in
  let fields a := file_cells fb [("_IO_write_ptr", VPtr (dp a)); ("_IO_write_end", VPtr (dp (pw_end w)))] in
  let next := published_window bb br w in
  let total := (written+(pw_ptr w - pw_base w)) mod 2^64 in
  printf_buf bb br w written 4 -∗ pbuf_file bb [("fp", VPtr fp)] -∗
  file_liveq (DfracOwn 1%Qp) fb freg -∗ fields (pw_base w) -∗
  (pbuf_file_live bb br -∗ pbuf bb (pbuf_vals next total 4) -∗ pbuf_file bb [("fp", VPtr fp)] -∗
   file_liveq (DfracOwn 1%Qp) fb freg -∗ fields (pw_ptr w) -∗ live (pw_obj w) (pw_reg w) -∗
   win_own (pw_obj w) (pw_lo w) (pw_end w) -∗ Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  cbn zeta. intros Hfr Hsize Hdb Hapart. iIntros "Hbuf Hfp Hfile Hfields HK". buf_open "Hbuf".
  struct_live_open "Hfile" as "[%Hfb Hf]". struct_open "Hfields" as "(Hwp & Hwe & _)".
  struct_open "Hfp" as "[Hfp _]". unfold win_live. destruct (numbers.Z.eq_dec (pw_obj w) bb); [contradiction|].
  iEval (rewrite /icell -flush_count_repr -/icell) in "Hwr".
  set (v := written mod 2^64). set (used := pw_ptr w - pw_base w). set (bo := pw_base w - pw_obj w).
  set (eo := pw_end w - pw_obj w). assert (Hv : 0 <= v < 2^64) by (apply Z.mod_pos_bound; lia).
  assert (Htotal : (written+used) mod 2^64 = (v+used) mod 2^64) by (unfold v; by rewrite Z.add_mod_idemp_l).
  rewrite Htotal. fold v. unfold published_window. destruct (Z.eq_dec (pw_ptr w) (pw_end w)) as [Hfull|Hroom].
  - pose proof (wp_printf_buffer_flush_full fr bb br fb freg (pw_obj w) (pw_reg w) bo used v
      (DfracOwn 1%Qp) (mkPtr (pw_base w) (Obj (pw_obj w))) Φ) as Hstep.
    replace (pw_obj w+bo+used) with (pw_ptr w) in Hstep by (unfold bo, used; lia).
    replace (pw_obj w+bo) with (pw_base w) in Hstep by (unfold bo; lia).
    rewrite -Hfull. unfold pwin_ok in Hw.
    iApply (Hstep with "Hl Hf Hwl Hfp Hwp Hwe Hbase Hptr Hend Hwr"); try assumption; try (unfold bo, used; lia).
    iNext. iIntros "Hl Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hwr".
    iApply ("HK" with "[Hl] [Hbase Hptr Hend Hwr Hmode] [Hfp] [Hf] [Hwp Hwe] Hd [Hwin]").
    + iEval (struct_sizes). iFrame. iPureIntro. lia.
    + iEval (struct_cells; cbn [staged pw_base pw_ptr pw_end pw_obj]). rewrite Z.add_0_r.
      replace (bb+48+1) with (bb+49) by lia. iFrame.
    + iEval (struct_cells). iFrame.
    + iEval (struct_sizes). iFrame. done.
    + iEval (struct_cells). iFrame.
    + iExact "Hwin".
  - pose proof (wp_printf_buffer_flush_direct fr bb br fb freg (pw_obj w) (pw_reg w) bo used eo v
      (DfracOwn 1%Qp) (mkPtr (pw_base w) (Obj (pw_obj w))) Φ) as Hstep.
    replace (pw_obj w+bo+used) with (pw_ptr w) in Hstep by (unfold bo, used; lia).
    replace (pw_obj w+bo) with (pw_base w) in Hstep by (unfold bo; lia).
    replace (pw_obj w+eo) with (pw_end w) in Hstep by (unfold eo; lia). unfold pwin_ok in Hw.
    iApply (Hstep with "Hl Hf Hwl Hfp Hwp Hwe Hbase Hptr Hend Hwr"); try assumption; try (unfold bo, eo, used; lia).
    iNext. iIntros "Hl Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hwr".
    iApply ("HK" with "[Hl] [Hbase Hptr Hend Hwr Hmode] [Hfp] [Hf] [Hwp Hwe] Hd Hwin").
    + iEval (struct_sizes). iFrame. iPureIntro. lia.
    + iEval (struct_cells). iFrame.
    + iEval (struct_cells). iFrame.
    + iEval (struct_sizes). iFrame. done.
    + iEval (struct_cells). iFrame.
Qed.

End publish.
