(** This file proves block `c: L33` of `c: _IO_new_file_overflow`
    (LibioOverflowBase.v describes the function), reached on the first
    call, when the stream has no buffer: `c: _IO_doallocbuf` installs
    one, as LibioDoAllocBuf.v proves, and `c: _IO_setg` points the
    read pointers at its base ([wp_ovf_L33]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv LibioLogic
  SysWrappers LibioSetb LibioOverflowBase.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Clearing `c: _IO_USER_BUF`, as `c: _IO_setb(fp, b, e, 1)` does,
    leaves every other masked bit as it was. *)
Lemma setb1_land fl m : Z.land 4294967294 m = m -> Z.land (setb_flags fl 1) m = Z.land fl m.
Proof. intros H. unfold setb_flags. cbn. rewrite -Z.land_assoc H. reflexivity. Qed.

(** The flags fl' a first `c: _IO_new_file_overflow` leaves from fl:
    `c: _IO_file_doallocate` may set `c: _IO_LINE_BUF`, `c: _IO_setb`
    clears `c: _IO_USER_BUF`, the switch to putting sets
    `c: _IO_CURRENTLY_PUTTING`, and a failed flush sets
    `c: _IO_ERR_SEEN`. *)
Definition ovf_alloc_flags (fl fl' : Z) : Prop :=
  exists fl1, (fl1 = fl \/ fl1 = Z.lor fl io_line_buf) /\
    (fl' = Z.lor (setb_flags fl1 1) 2048 \/ fl' = Z.lor (Z.lor (setb_flags fl1 1) 2048) io_err_seen).

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioOverflowAllocSetgOn (R : Runtime) (LG0 : LogicSig R).
Module OB := LibioOverflowBaseOn R LG0.
Import OB OB.SW OB.SW.FI.ML OB.SW.FI.LG OB.SW.FI.L OB.SW.OW OB.SW.FI OB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

Local Instance overflow_alloc_setg_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The genv defines `c: _IO_doallocbuf`. *)
Context (Hdabf : find_fn ge (TAtom "__GI__IO_doallocbuf") = Some (Defined glibc__IO_doallocbuf)).
(** The allocator's state, which `c: malloc` takes and gives back. *)
Context (Mres : iProp Σ).

(** `c: _IO_doallocbuf` on a stream without a buffer, as
    LibioDoAllocBuf.v's [wp_glibc__IO_doallocbuf_alloc] proves it with
    LibioDoAllocBase.v's [doalloc_k] and [new_buf] unfolded. *)
Context (Hdab : forall fr fb freg fl fd eb oe vb vreg Φ,
  call_frame glibc__IO_doallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 -> Z.land fl io_unbuffered = 0 ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  Mres -∗
  ▷ (pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     ∀ fl1 bb sz, ⌜(fl1 = fl \/ fl1 = Z.lor fl io_line_buf) /\ 0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     live fb freg -∗ int_cell fb off_flags (setb_flags fl1 1) -∗ int_cell fb off_fileno fd -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     (∃ breg, ⌜r_kind breg = Heap /\ bb + sz <= r_end breg /\ r_end breg <= 2 ^ 48⌝ ∗
       live bb breg ∗ bytes bb 0 (replicate (Z.to_nat sz) 0) ∗ auxes bb 0 (replicate (Z.to_nat sz) CNone)) -∗
     errno_any eb -∗ Mres -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}).
(** Block `c: L35`, as LibioOverflowSetpEnd.v proves it ([wp_ovf_L35]). *)
Context (HL35 : forall fb freg ch f2 fd eb mode vb vreg bb breg sz xs fl tw off wb0 wp0 we0 from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  Z.land fl 256 = 0 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  0 < bb -> bb + sz <= r_end breg -> r_end breg <= 2 ^ 63 -> 0 < sz -> length xs = Z.to_nat sz ->
  Forall (fun x => 0 <= x < 256) xs ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk6") e = Some (WPtr (mkPtr (fb + off_write_base) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  live bb breg -∗ bytes bb 0 xs -∗ int_cell fb off_flags fl -∗ icell fb off_total_written tw -∗
  icell fb off_offset off -∗ pcell fb off_read_ptr (mkPtr bb (Obj bb)) -∗ pcell fb 16 (mkPtr bb (Obj bb)) -∗
  pcell fb 24 (mkPtr bb (Obj bb)) -∗ pcell fb off_write_base wb0 -∗ pcell fb off_write_ptr wp0 -∗
  pcell fb off_write_end we0 -∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗
  pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ (fl' = Z.lor fl 2048 \/ fl' = Z.lor (Z.lor fl 2048) io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L35") (Some from))) : sexpr) {{ Φ }}).

(** Block `c: L33`: `c: _IO_doallocbuf` installs a buffer, and its
    base becomes every read pointer; then block `c: L35`. *)
Lemma wp_ovf_L33 fb freg ch f2 fd eb mode vb vreg fl tw off rp re rb wp0 we0 oe from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  Z.land fl io_is_appending = 0 -> Z.land fl 8 = 0 -> Z.land fl 2048 = 0 -> Z.land fl 256 = 0 ->
  Z.land fl io_unbuffered = 0 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk6") e = Some (WPtr (mkPtr (fb + off_write_base) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  int_cell fb off_flags fl -∗ icell fb off_total_written tw -∗ icell fb off_offset off -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb off_write_base null -∗
  pcell fb off_write_ptr wp0 -∗ pcell fb off_write_end we0 -∗ pcell fb off_buf_base null -∗
  pcell fb off_buf_end oe -∗ Mres -∗
  ▷ (∀ r bb breg sz k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ 0 < sz <= 8192 /\ ovf_alloc_flags fl fl'⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗ Mres -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L33") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hch Hf2 Hf2r Hfd Hfd31 Happ Hnw Hnp Hbk Hub He Hmd Hv0 Hv2 Hc0 Hc6.
  iIntros "#Hvt Hl Hfx [%Hflr Hflb] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend HM HK". unfold file_size in Hend.
  iDestruct "Hfx" as "(Hf2 & Hfd & Herr & Hcol & Hmode & Hvtp)". adv.
  iApply wp_call_bind; [vx | exact Hdabf | reflexivity |]. iNext.
  iApply (Hdab with "Hvt Hl [$Hflb //] Hfd Herr Hbase Hbend Hvtp HM"); try first [reflexivity | side].
  iNext. iIntros "Hvtp". iIntros (fl1 bb sz (Hfl1 & Hsz & Hbb & Hbbe)) "Hl Hflb Hfd Hbase Hbend Hnb Herr HM".
  iDestruct "Hnb" as (breg) "(%Hbr & Hbl & Hxs & _)". destruct Hbr as (Hbk' & Hbe & Hbreg).
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  adv. iApply (wp_raw_load_pointer with "Hl Hbase Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hbase Hbl". adv.
  iApply (wp_raw_store_pointer with "Hl Hrb"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hrb". adv.
  iApply (wp_raw_load_pointer with "Hl Hbase Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hbase Hbl". adv.
  iApply (wp_raw_store_pointer with "Hl Hrp"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hrp". adv.
  iApply (wp_raw_load_pointer with "Hl Hbase Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hbase Hbl". adv.
  iApply (wp_raw_store_pointer with "Hl Hre"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hre". st.
  assert (Hfa : Z.land (setb_flags fl1 1) io_is_appending = 0 /\ Z.land (setb_flags fl1 1) 256 = 0).
  { rewrite !setb1_land; try reflexivity. unfold io_is_appending, io_line_buf in *.
    destruct Hfl1 as [-> | ->]; [split; assumption | rewrite !land_lor_const; try reflexivity; split; assumption]. }
  destruct Hfa as [Happ' Hbk2].
  iApply (HL35 with "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp] Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend");
    try first [side | lk_prove | rewrite length_replicate; lia | apply Forall_replicate; lia].
  iNext. iIntros (r k' we' xs' fl' tw' off' [Hr Hfl']) "Hl Hfx Hst".
  iApply ("HK" with "[%] Hl Hfx Hst HM"). split; [exact Hr | split; [exact Hsz | exists fl1; tauto]].
Qed.

End rules.
End LibioOverflowAllocSetgOn.
