(** `c: _IO_file_doallocate` gives a stream its narrow buffer, and it
    asks the stream's jump table for the stat function first, to learn
    what kind of file the stream writes to. A wide stream points to the
    wide jump table, so the same function reads a different table when
    `c: _IO_wfile_doallocate` calls it. This file proves the function
    for that table. The proof in [LibioDoAlloc](LibioDoAlloc.v) covers
    a narrow stream, and the two differ only in the slot they load. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsFstat OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  LibioSetb LibioDoAllocBase LibioDoAlloc LibioWIdle.
From Glibc Require FileInv LibioDoAllocBase LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import LibioDoAllocBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The genv defines `c: _IO_file_stat` at the symbol that the stat
    slot of the wide jump table holds. Both tables name the same stat
    function. *)
Context (Hstatf : ge_fn ge "__GI__IO_file_stat" glibc__IO_file_stat).

Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The function on a wide stream

    The function has two parts. The first part asks the kernel about
    the file, through the stat function that the stream's jump table
    names. The second part chooses a size and allocates the buffer,
    and it does not read the jump table. The narrow proof already
    covers the second part, so this section assumes it and proves the
    first part for the wide table. *)


(** The proposition Mres stands for the allocator's state. A call of
    `c: malloc` takes it and gives it back. *)
Context (Mres : iProp Σ).
(** After a successful stat, block `c: L5` chooses the buffer's size
    from the file's kind and block size. The proof assumes the contract
    of that block, which [LibioDoAllocMode](LibioDoAllocMode.v) proves
    as [wp_doalloc_L5]. The block does not read the jump table. *)
Context (HL5 : forall fb freg fl fd eb oe sb sreg bs1 bs2 bs3 e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < sb -> sb mod 16 = 0 -> sb + 144 <= r_end sreg -> r_end sreg <= 2 ^ 48 ->
  length bs1 = 4%nat -> length bs2 = 8%nat -> length bs3 = 8%nat ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_fileno) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  live sb sreg -∗ bytes sb 24 bs1 -∗ bytes sb 40 bs2 -∗ bytes sb 56 bs3 -∗
  ▷ doalloc_k Mres fb freg fl fd eb Φ -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L5") (Some (TAtom "L13")))) : sexpr)
    {{ Φ }}).

(** Block `c: L7` allocates the buffer and installs it. The proof
    assumes the contract of that block, which
    [LibioDoAllocTail](LibioDoAllocTail.v) proves as
    [wp_doalloc_L7]. *)
Context (HL7 : forall fb freg fl oe sz from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 < sz <= 8192 ->
  (from = TAtom "L59" /\ (exists v, lookup (TAtom "v73") e = Some (WInt v) /\ v mod 2 ^ 64 = sz)) \/
  ((from = TAtom "L66" \/ from = TAtom "L13") /\ sz = 8192) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  ▷ (∀ bb, ⌜0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     live fb freg -∗ int_cell fb off_flags (setb_flags fl 1) -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ Mres -∗ Φ (Ret (WInt 1))) -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L7") (Some from))) : sexpr) {{ Φ }}).

(** `c: _IO_file_stat` asks the kernel about the stream's file. The
    call fills the stat buffer and returns 0, or it fails and returns
    -1. The proof assumes this contract, which
    [LibioRead](LibioRead.v) proves. *)
Context (Hstat_spec : forall fr fb freg fd b reg o eb Φ,
  call_frame glibc__IO_file_stat [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) (Obj b))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> b + o + stat_size <= r_end reg ->
  live fb freg -∗ int_cell fb off_fileno fd -∗ live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live fb freg -∗ int_cell fb off_fileno fd -∗ live b reg -∗
     blk_any b o stat_size -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}).

(** `c: _IO_file_doallocate (fp)` on a wide stream without a narrow
    buffer installs a fresh one and returns 1. The predicate
    [doalloc_k] says what the caller receives, as it does for a narrow
    stream. The function reads the stat slot through the wide table, so
    the caller also lends the shares of that table. *)
Lemma wp_glibc__IO_file_doallocate_wide fr fb freg fl fd eb oe vb vreg Φ :
  call_frame glibc__IO_file_doallocate [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
  Mres -∗
  ▷ (pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ doalloc_k Mres fb freg fl fd eb Φ) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using HL5 HL7 Hstat_spec Hstatf.
  intros Hfr Hfb Hal Hend Hfreg He Hfd Hfd31. injection Hfr as <-.
  iIntros "#Hvt #Hwvt Hl Hfl [%Hfdr Hfdb] Herr Hb Hbe Hvtp HM HK". unfold file_size in Hend.
  iPoseProof (wvtables_slot ge vb slot_stat "__GI__IO_file_stat" with "Hwvt") as "#Hss"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "__GI__IO_file_stat")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hstatf). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
                    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (sb (Hsb0 & Hsb16 & Hsb48)) "Ho".
  iDestruct (obj_blk with "Ho") as "[Hsl Hsk]"; [vm_compute; congruence|]. cbn [req_extent req_kind heap_req] in *.
  replace ((144 + 15) / 16 * 16) with 144 in * by reflexivity.
  step. norm. check "Hl". load_s32_group "Hl Hfdb". step. branch_as false.
  step. step. norm. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_wfile in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true.
  step. step. norm.
  check_read_dq "Hvl'" by ar.
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hss Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hstatf) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hstatf) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hstatf) | apply (ge_fn_check _ _ _ Hstatf) | vx |
    apply (ge_fn_find _ _ _ Hstatf) | reflexivity | reflexivity |].
  iNext.
  iApply (Hstat_spec _ fb freg fd sb _ 0 eb with "Hl [$Hfdb //] Hsl [Hsk] Herr");
    try first [rewrite Z.add_0_r; reflexivity | libio_side | unfold stat_size; cbn; lia].
  { unfold stat_size. iExact "Hsk". }
  iNext. iIntros (k Hk) "Hl [_ Hfdb] Hsl Hsk Herr". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step. step. step. step. destruct Hk as [-> | ->]; branch.
  - iDestruct "Hsk" as (xs cs [Hxl Hcl]) "Hps". rewrite pts_app. iDestruct "Hps" as "[Hxs _]".
    iDestruct (stat_fields with "Hxs") as "(Hb1 & Hb2 & Hb3)"; [exact Hxl|].
    iApply (HL5 with "Hl Hfl [$Hfdb //] Herr Hb Hbe HM Hsl Hb1 Hb2 Hb3 [HK Hvtp]"); try libio_side;
      try (rewrite length_take length_drop Hxl; reflexivity).
    iNext. iApply ("HK" with "Hvtp").
  - iApply (HL7 _ _ _ _ 8192 with "Hl Hfl Hb Hbe HM"); try libio_side.
    + right. auto.
    + iNext. iIntros (bb Hbb) "Hl Hfl Hb Hbe Hbo HM".
      iApply ("HK" with "Hvtp [%] Hl Hfl [$Hfdb //] Hb Hbe Hbo Herr HM"). split; [left; reflexivity | lia].
Qed.

End rules.
