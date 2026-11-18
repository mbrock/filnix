(** An unbuffered stream stores one byte inside its FILE and sends it
    immediately. After the write, glibc must leave the stream empty and
    with no room, even if the system call failed. The buffer pointers in
    this proof use the stream's own [[capability]] and lifetime. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysCode FileInv LibioLogic LibioPutsInv
  LibioReadCode LibioDoWriteCode LibioWriteDq LibioDoWriteRet LibioOverflowBase SysWrappers.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

(** The short buffer is a field of the stream, not a separate allocation. *)
Definition short_ptr (fb : Z) := mkPtr (fb + off_shortbuf) (Obj fb).

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The read end and write base coincide, so the stream need not seek
    before a write. Its write end is always the short buffer's base.
    Only the read base and current write pointer can differ from it. *)
Definition short_ptrs fb rb wp : iProp Σ :=
  let sb := short_ptr fb in
  pcell fb off_read_ptr sb ∗ pcell fb 16 sb ∗ pcell fb 24 rb ∗
  pcell fb off_write_base sb ∗ pcell fb off_write_ptr wp ∗ pcell fb off_write_end sb ∗
  pcell fb off_buf_base sb ∗ pcell fb off_buf_end (mkPtr (fb + 132) (Obj fb)).

(** The reset after a nonempty write puts all six cursors at the short
    buffer's base. It does the same on a short write as on success. *)
Lemma wp_short_reset fb freg fl mode rb wp n r e from Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  0 <= fl < 2^32 -> Z.land fl 514 <> 0 -> (mode = 0 \/ mode = 2^32 - 1) -> 0 <= r <= n -> n < 2^63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "iw_1.v67") e = Some (WInt r) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗ short_ptrs fb rb wp -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
     short_ptrs fb (short_ptr fb) (short_ptr fb) -∗ Φ (Ret (WInt (if r =? n then 0 else 2^32 - 1)))) -∗
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None (Enter (TAtom "iw_1.L70") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfb Hal Hend Hfreg Hfl Hub Hmd Hr Hn Hv0 Hc0 Hv4 Hv67. unfold file_size in Hend.
  iIntros "Hl [%Hflr Hfl] [%Hmr Hmode] (Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend) HK".
  unfold short_ptr, off_shortbuf. adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hrb". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hrp". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hre". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hwp". adv. store "Hl" "Hwb". adv.
  load_s32 "Hl" "Hmode". adv. brm Hmd. adv. load_s32 "Hl" "Hfl". adv.
  assert (0 <= Z.land fl 514 < 2^32) by (apply land_lt32; lia). branch_as false. adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hwe". adv.
  destruct (Z.eq_dec r n) as [-> | Hrn];
    [rewrite Z.eqb_refl; branch_as false | rewrite (proj2 (Z.eqb_neq _ _) Hrn); branch_as true]; adv.
  all: iApply wp_ret; [reflexivity | vx |]; iNext;
    iApply ("HK" with "Hl [$Hfl //] [$Hmode //] [$Hrp $Hre $Hrb $Hwb $Hwp $Hwe $Hbase $Hbend]").
Qed.

Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__GI___write" glibc___libc_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write).

(** A character overflow calls `c: _IO_new_do_write` after it has placed
    the byte in the short buffer. The read end matches the write base, so
    glibc calls the write slot without seeking. Both return paths restore
    the field pointers, and an incomplete write reports EOF. *)
Lemma wp_short_do_write fr fb freg fl f2 fd tw off mode ch rb eb vb vreg Φ :
  let sb := short_ptr fb in
  call_frame glibc__IO_new_do_write [WPtr (mkPtr fb (Obj fb)); WPtr sb; WInt 1] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  (Z.land f2 2 = 0 \/
    Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  0 <= f2 < 2^32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 -> Z.land fl 514 <> 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2^32 - 1) -> 0 <= ch < 256 ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ short_ptrs fb rb (mkPtr (fb + 132) (Obj fb)) -∗
  int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ int_cell fb off_mode mode -∗
  pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ bytes fb off_column [0;0] -∗
  bytes fb off_shortbuf [ch] -∗ errno_any eb -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post 1 fl r fl'⌝ -∗ live fb freg -∗ short_ptrs fb sb sb -∗
     int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ int_cell fb off_mode mode -∗
     pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ bytes fb off_column [0;0] -∗
     bytes fb off_shortbuf [ch] -∗ errno_any eb -∗ Φ (Ret (WInt (if r =? 1 then 0 else 2^32 - 1)))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  cbn zeta. intros Hfr Hfb Hal Hend Hrend Hready Hf2 Hin Happ Hub He Hmd Hch. injection Hfr as <-.
  iIntros "#Hvt Hl (Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend) [%Hfl Hflags] Hf2 Hfd Htw Hoff Hmode Hvtp Hcol Hch Herr HK".
  iPoseProof (vtables_slot ge vb vreg slot_write "_IO_new_file_write" with "Hvt") as "#Hslot"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_write")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfw). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)".
  unfold file_size in Hend. unfold io_is_appending in Happ. unfold io_vtables_size in Hvend.
  unfold short_ptr, off_shortbuf. step. step. branch_as true. adv. load_s32 "Hl" "Hflags". adv. branch_as true.
  adv. load_self_using wp_raw_load_pointer_self "Hl Hre". adv. load_self_using wp_raw_load_pointer_self "Hl Hwb".
  adv. branch_as true. adv.
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". do 5 step. branch_as true. step. step. norm.
  check_read_dq "Hvl'" by ar. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hslot Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hfw) |].
  iNext. iIntros "_ _ _". iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfw) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfw) | apply (ge_fn_check _ _ _ Hfw) | vx |
    apply (ge_fn_find _ _ _ Hfw) | reflexivity | reflexivity |]. iNext.
  iApply (wp_file_write_short Hreg Hext with "Hl [$Hflags //] Hf2 Hfd Htw Hoff Hch Herr");
    try first [reflexivity | assumption].
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hflags Hf2 Hfd Htw Hoff Hch Herr".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  assert (Hr : 0 <= r <= 1) by (destruct Hpost as [[-> _] | [? _]]; lia).
  assert (Hub' : Z.land fl' 514 <> 0) by
    (destruct Hpost as [[_ ->] | [_ ->]]; [exact Hub | rewrite land_lor_const; [exact Hub | reflexivity]]).
  rewrite (Z.mod_small r (2^64)); [|lia]. adv. load_bytes_dq "Hl Hcol" decode (reflexivity) by ar.
  iNext. iIntros "Hl Hcol". branch. step. branch.
  iApply (wp_short_reset fb freg fl' mode rb (mkPtr (fb+132) (Obj fb)) 1 r with
    "Hl Hflags Hmode [$Hrp $Hre $Hrb $Hwb $Hwp $Hwe $Hbase $Hbend]"); try first [assumption | lia | lk_prove].
  iNext. iIntros "Hl Hflags Hmode Hptrs".
  iApply ("HK" with "[%] Hl Hptrs Hflags Hf2 Hfd Htw Hoff Hmode Hvtp Hcol Hch Herr"). exact Hpost.
Qed.

End rules.
