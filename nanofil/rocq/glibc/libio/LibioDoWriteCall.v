(** The call of `c: _IO_new_do_write` (LibioDoWrite.v) through the
    jump table, from block `c: iw_1.L9` on ([wp_do_write_call]).

    The triple of `c: _IO_new_do_write` (LibioDoWriteCode.v), which
    hands the n bytes from the write base to the jump table's write and
    empties the buffer: `c: new_do_write` inlined.

    The stream is not appending, so `c: _offset` is not reset; its
    read end is its write base, as `c: _IO_setg` leaves them, so no
    seek is made; its `c: _cur_column` is 0, as nothing in glibc's
    narrow path makes it other, so `c: _IO_adjust_column` is not
    called. The write is [wp_glibc__IO_new_file_write], reached
    through `c: _IO_file_jumps`' write slot. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers LibioDoWriteRet.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDoWriteCallOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write).

(** The caller chooses which cancellation flags its proved write rule accepts.
    This block forwards that condition without inspecting the flags itself. *)
Context (write_ready : Z -> Prop).

Local Instance do_write_call_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The jump table's write, as LibioWrite.v proves it
    ([wp_glibc__IO_new_file_write]). *)
Context (Hfw_spec : forall fr fb freg fl f2 fd tw off b reg o xs eb Φ,
  call_frame glibc__IO_new_file_write
    [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) (Obj b)); WInt (Z.of_nat (length xs))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  write_ready f2 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live b reg -∗ bytes b o xs -∗ errno_any eb -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post (Z.of_nat (length xs)) fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live b reg -∗ bytes b o xs -∗ errno_any eb -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}).

(** The rest of the block once the write returned, as
    LibioDoWriteRet.v proves it ([wp_do_write_ret]). *)
Context (Hret_spec : forall fb freg fl bb breg rp re rb wb wp we be n r e mode Φ,
  let base := mkPtr bb (Obj bb) in
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= fl < 2 ^ 32 ->
  0 < bb < 2 ^ 63 -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 <= r <= n -> n < 2 ^ 63 ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "iw_1.v67") e = Some (WInt r) ->
  live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗
  ▷ (live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗ bytes fb off_column [0; 0] -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None
              (Exec (TAtom "iw_1.iw_2.join") (skipn 5 (b_insts dw_join)) (b_jump dw_join))) : sexpr) {{ Φ }}).

(** Block `c: iw_1.L9` of `c: _IO_new_do_write` on: the jump table
    validated, its write slot called, and the end of the call. *)
Lemma wp_do_write_call fb freg fl f2 fd tw off bb breg i xs rp rb wp we be eb vb vreg e from mode Φ :
  let n := Z.of_nat (length xs) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  0 < n ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  write_ready f2 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr wb) -> lookup (TAtom "v4") e = Some (WInt n) ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode mode -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl' 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode mode -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None (Enter (TAtom "iw_1.L9") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros n wb base Hn0 Hfb Hal Hend Hfreg Hf2 Hf2r Hfd Hflr Happ He Hb Hi Hbend Hbreg Hy
    Hbe Hbec Hmd Hv0 Hc0 Hv2 Hv4.
  iIntros "#Hvt Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp HK".
  unfold file_size in Hend. unfold io_is_appending in Happ.
  iPoseProof (vtables_slot ge vb vreg slot_write "_IO_new_file_write" with "Hvt") as "#Hsw"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_write")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfw). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  assert (Hn : n < 2 ^ 63) by lia.
  iDestruct "Hfl" as "[%Hfl0 Hfl]".
  st. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl"); [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file, io_vtables_size in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". st. st. st. st. st. brv true.
  st. st. norm.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hvl'"); [reflexivity | vx | right; reflexivity | ar | ar | ar |].
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsw Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hfw) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfw) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfw) | apply (ge_fn_check _ _ _ Hfw) | vx |
    apply (ge_fn_find _ _ _ Hfw) | reflexivity | reflexivity |].
  iNext. rewrite (Z.mod_small n (2 ^ 64)); [|lia].
  iApply (Hfw_spec with "Hl [$Hfl //] Hfl2 Hfd Htw Hoff Hbl Hxs Herr"); try side.
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  assert (Hr : 0 <= r <= n) by (destruct Hpost as [[-> _] | [? _]]; lia).
  rewrite (Z.mod_small r (2 ^ 64)); [|lia].
  iApply (Hret_spec with "Hl Hbl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol");
    try side.
  iNext. iIntros "Hl Hbl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol".
  iApply ("HK" with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp").
  split; [exact Hpost | exact Hfl'].
Qed.

End rules.
End LibioDoWriteCallOn.
