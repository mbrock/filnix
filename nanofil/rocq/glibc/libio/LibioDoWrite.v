(** The triple of `c: _IO_new_do_write` (LibioDoWriteCode.v), which
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
  LibioLogic SysWrappers.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDoWriteOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

Local Instance do_write_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The call through the jump table and the rest, as
    LibioDoWriteCall.v proves them ([wp_do_write_call]). *)
Context (Hcall_spec : forall fb freg fl f2 fd tw off bb breg i xs rp rb wp we be eb vb vreg e from Φ,
  let n := Z.of_nat (length xs) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  0 < n ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr wb) -> lookup (TAtom "v4") e = Some (WInt n) ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode 0 -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl' 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode 0 -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None (Enter (TAtom "iw_1.L9") (Some from))) : sexpr) {{ Φ }}).

(** `c: _IO_new_do_write(fp, wb, n)` of the n bytes xs from the write
    base wb, offset i of the heap buffer bb: they go to
    [wp_glibc__IO_new_file_write], r of them written ([fw_post]); the
    read and write pointers are then the buffer's base, the write end
    the base when the stream is line-buffered or unbuffered, else the
    buffer's end; the result is 0 if all were written, else
    `c: EOF`. *)
Lemma wp_glibc__IO_new_do_write fr fb freg fl f2 fd tw off bb breg i xs rp rb wp we be eb vb vreg Φ :
  let n := Z.of_nat (length xs) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  call_frame glibc__IO_new_do_write [WPtr (mkPtr fb (Obj fb)); WPtr wb; WInt n] = Some fr -> 0 < n ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode 0 -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl' 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode 0 -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros n wb base Hfr. injection Hfr as <-. intros Hn0 Hfb Hal Hend Hfreg Hf2 Hf2r Hfd Hflr Happ He Hb Hi Hbend Hbreg Hy
    Hbe Hbec.
  iIntros "#Hvt Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp HK".
  unfold file_size in Hend. enter. unfold io_is_appending in Happ.
  assert (Hn : n < 2 ^ 63) by lia.
  st. brv true. st. chk "Hl". iDestruct "Hfl" as "[%Hfl0 Hfl]". load_int "Hl Hfl". st. brv true.
  st. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer with "Hl Hre Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hre Hbl". st. norm. chk "Hl".
  iApply (wp_raw_load_pointer with "Hl Hwb Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwb Hbl". st. st. st. brv true.
  iApply (Hcall_spec with "Hvt Hl [$Hfl //] Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp HK");
    try side.
Qed.

End rules.
End LibioDoWriteOn.
