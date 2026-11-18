(** A nonempty string write to an input-only stream first finds no
    space and then calls the overflow slot. That slot reports EBADF. The
    string writer returns zero bytes written and never reads the string.
    An empty string returns zero without even setting the error bit. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileIdle FileTidy PrintfStreamInv LibioFputsSpec LibioLogic
  LibioReadCode LibioDoWriteCode LibioXsputnCode LibioPutsInv LibioFflushIdle LibioOverflowBase LibioOverflowNoWrite.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Section nowrite.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Even with line buffering, a stream outside write mode skips the
    newline scan. Glibc compares the pointer addresses next. The write
    end may lie below the write pointer, so equality is not required. *)
Lemma wp_xs_nowrite_enter fr fb freg src n st nb Φ :
  call_frame glibc__IO_new_file_xsputn [WPtr (mkPtr fb (Obj fb)); WPtr src; WInt n] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb+file_size <= r_end freg -> r_end freg <= 2^63 -> 0 < n < 2^63 ->
  has (fs_flags st) io_currently_putting = false -> ptr_addr (fs_ptr st 5) <= ptr_addr (fs_ptr st 4) ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> live fb freg -∗ file_fields fb st -∗ buf_idle nb -∗
  ▷ (∀ e, ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
       lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
       lookup (TAtom "v4") e = Some (WInt n) /\ lookup (TAtom "pr.5") e = Some (WInt n)⌝ -∗
     live fb freg -∗ file_fields fb st -∗ buf_idle nb -∗
     WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Enter (TAtom "L120") (Some (TAtom "L96")))) : gexpr) {{ Φ }}) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hrend Hn Hnp Hroom Hb. injection Hfr as <-. unfold file_size in Hend.
  unfold has, io_currently_putting in Hnp. apply negb_false_iff, Z.eqb_eq in Hnp.
  iIntros "Hl (%Hlen & [%Hfl Hflags] & Hps & Hrest) Hb HK".
  pose proof (buf_ptrs_in fb nb _ 4 Hb Hlen ltac:(lia)) as H4. pose proof (buf_ptrs_in fb nb _ 5 Hb Hlen ltac:(lia)) as H5.
  unfold fs_ptr in Hroom. remember (fs_ptrs st) as ps eqn:Eps.
  destruct ps as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 ps]]]]]]; try discriminate Hlen. cbn [nth] in H4, H5, Hroom.
  iEval (cbn [big_opL]) in "Hps". iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & Prest)".
  iAssert (⌜0 <= ptr_addr p4 < 2^64⌝)%I as %Hr4. { iApply (in_buf_range fb nb with "Hb"); first [assumption | lia]. }
  iAssert (⌜0 <= ptr_addr p5 < 2^64⌝)%I as %Hr5. { iApply (in_buf_range fb nb with "Hb"); first [assumption | lia]. }
  assert (H512 : 0 <= Z.land (fs_flags st) 512 < 2^32) by (apply land_lt32; lia).
  step. step. branch_as true. adv. load_s32 "Hl" "Hflags". adv.
  destruct (Z.eq_dec (Z.land (fs_flags st) 512) 0) as [Hline | Hline].
  1: branch_as true; adv; branch_as true.
  2: branch_as false; adv; load_s32 "Hl" "Hflags"; adv; branch_as true.
  all: adv; iApply (wp_load_buf_ptr with "Hl P5 Hb"); [reflexivity | vx | reflexivity | a2 | a2 | lia | lia | exact H5 |].
  all: iNext; iIntros "Hl P5 Hb"; adv; iApply (wp_load_buf_ptr with "Hl P4 Hb"); [reflexivity | vx | reflexivity | a2 | a2 | lia | lia | exact H4 |].
  all: iNext; iIntros "Hl P4 Hb"; adv; branch_as true; adv; branch_as true; adv; branch_as false;
    iApply ("HK" with "[%] Hl [Hflags P0 P1 P2 P3 P4 P5 Prest Hrest] Hb").
  1,3: split_and!; first [lk_prove | lookups; repeat f_equal; unwrap2; lia].
  all: unfold file_fields; rewrite -Eps; cbn [big_opL]; iFrame; done.
Qed.

Context (Hov : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow).

(** A refused flush leaves the entire source available to the caller.
    The stream keeps its original orientation because this call goes
    straight to the file method rather than through the overflow wrapper. *)
Lemma wp_xsputn_nowrite fr vb self fb freg st nb flags2 held dq b reg o c ys eb Φ :
  let fp := mkPtr fb (Obj fb) in let n := Z.of_nat (length ys) in let fd := fs_fileno st in
  call_frame glibc__IO_new_file_xsputn [WPtr fp; WPtr (mkPtr (b+o) c); WInt n] = Some fr ->
  fb mod 8 = 0 -> 0 < fb -> fb+file_size <= r_end freg -> r_end freg <= 2^63 -> flags_ok st ->
  idle_ok fd (fs_with_flags2 st 0) -> fs_flags2 st = flags2 -> fs_vtable st = mkPtr (vb+vt_file) (Ro vb) ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> short_idle nb st -> has (fs_flags st) io_no_writes = true ->
  has (fs_flags st) io_currently_putting = false ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  (c = Obj b \/ c = Ro b) -> 0 < b -> 0 <= o -> b+o+n <= r_end reg -> r_end reg <= 2^63 -> Forall (fun y => 0 <= y < 256) ys ->
  fputs_ro vb -∗ live fb freg -∗ file_fields fb st -∗ lock_inv self (fs_lock st) held -∗ buf_idle nb -∗
  wide_idle vb (fs_wide st) (fs_codecvt st) -∗ errno_any eb -∗ liveq dq b reg -∗ bytesq dq b o ys -∗
  ▷ (∀ r, ⌜r = 2^64-1 \/ 0 <= r <= n⌝ -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗
     liveq dq b reg -∗ bytesq dq b o ys -∗ Φ (Ret (WInt r))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros fp n fd Hfr Hal Hfb Hend Hrend Hok Hi Hf2 Hvt Hb Hshort Hnw Hnp He Hin Hg Hc Hb0 Ho Hen Hr Hy. subst fp fd.
  iIntros "#Hro Hl Hf Hlk Hb Hw Herr Hbl Hys HK". iDestruct "Hro" as (vr sb sr) "[#Hvt _]".
  destruct (Z.eq_dec n 0) as [H0 | Hn].
  { injection Hfr as <-. step. step. branch_as false. step. iApply wp_ret; [reflexivity|vx|]. iNext.
    iApply ("HK" $! 0 with "[%] [Hl Hf Hlk Hb Hw] Herr Hbl Hys"); [right; lia|].
    iExists fb, freg, st, nb. iFrame. done. }
  pose proof Hi as (_ & _ & Hmd & _ & _ & _ & _ & _ & _ & Hput & _).
  cbn [fs_with_flags2 fs_mode fs_flags] in Hmd, Hput.
  assert (Hpos : 0 < n < 2^63) by (unfold n in *; lia).
  iApply (wp_xs_nowrite_enter fr fb freg (mkPtr (b+o) c) n st nb with "Hl Hf Hb"); try assumption.
  { apply Z.le_ngt. intros Hp. specialize (Hput (or_intror Hp)). congruence. }
  iNext. iIntros (e (Hv0 & Hc0 & Hv4 & Hp5)) "Hl Hf Hb".
  iDestruct (nowrite_fields with "Hf") as "(Hfl & Hmd & Hvtp & Hclose)". iEval (rewrite Hvt) in "Hvtp".
  iPoseProof (vtables_slot ge vb vr slot_overflow "_IO_new_file_overflow" with "Hvt") as "#Hslot"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_overflow")) vr) as "Hfc". { rewrite (ge_fn_cap _ _ _ Hov). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvr) & Hvl & _)". unfold io_vtables_size in Hvend. unfold file_size in Hend.
  adv. iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl"); [reflexivity|vx|left; reflexivity|ar|ar|cbn; unfold vt_file in *; lia|].
  iNext. iIntros "Hl Hvtp #Hvl'". do 5 step. branch_as true. step. step. norm. check_read_dq "Hvl'" by ar. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hslot Hfc"); [reflexivity|vx|right; reflexivity|ar|ar|apply (ge_fn_addr _ _ _ Hov)|].
  iNext. iIntros "_ _ _". iApply wp_check_function; [vx|apply (ge_fn_check _ _ _ Hov)|]. iNext.
  iApply wp_raw_call_bind; [vx|apply (ge_fn_cap _ _ _ Hov)|apply (ge_fn_check _ _ _ Hov)|vx|apply (ge_fn_find _ _ _ Hov)|reflexivity|reflexivity|]. iNext.
  iApply (wp_file_overflow_nowrite _ fb freg (2^32-1) (fs_flags st) eb with "Hl Hfl Herr"); try first [assumption|reflexivity].
  iNext. iIntros "Hl Hfl Herr". iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  adv. branch_as false. adv. branch_as true. adv. iApply wp_ret; [reflexivity|vx|]. iNext.
  replace (((n mod 2^64 - n mod 2^64) mod 2^64) mod 2^64) with 0 by (unwrap2; lia).
  iApply ("HK" $! 0 with "[%] [Hl Hfl Hmd Hvtp Hclose Hlk Hb Hw] [Herr] Hbl Hys"); [right; lia| |iExists _; iExact "Herr"].
  iEval (rewrite -Hvt) in "Hvtp". iDestruct ("Hclose" with "Hfl Hmd Hvtp") as "Hf".
  iExists fb, freg, (nowrite_after st (fs_mode st)), nb. iFrame "Hl Hf Hlk Hb Hw".
  iPureIntro. destruct (nowrite_idle st nb (fs_fileno st) (fs_mode st) Hok Hi Hshort Hmd) as (A & B & C). intuition.
Qed.
End nowrite.
