(** This file proves the triple of `c: _IO_doallocbuf` (LibioReadCode.v) on a stream
    with no buffer that is not unbuffered: it calls the jump table's
    doallocate, `c: _IO_file_doallocate`, whose result is the buffer
    LibioDoAlloc.v proves it installs. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  LibioSetb LibioDoAllocBase.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDoAllocBufOn (R : Runtime) (LG0 : LogicSig R).
Module DB := LibioDoAllocBaseOn R LG0.
Import DB DB.SW DB.SW.FI.ML DB.SW.FI.LG DB.SW.FI.L DB.SW.OW DB.SW.FI DB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The genv defines `c: _IO_file_doallocate` at the symbol the jump
    table's doallocate slot holds. *)
Context (Hdaf : ge_fn ge "__GI__IO_file_doallocate" glibc__IO_file_doallocate).
(** The genv defines `c: _IO_setb`. *)
Context (Hsetbf : find_fn ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb)).

Local Instance doallocbuf_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_setb` on a stream with no buffer, as LibioSetb.v's
    [wp_glibc__IO_setb] proves it with the old buffer null. *)
Context (Hsetb_null : forall fr fb freg fl oe nb ne a Φ,
  call_frame glibc__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Φ }}).
(** The allocator's state, which `c: malloc` takes and gives back. *)
Context (Mres : iProp Σ).
(** `c: _IO_file_doallocate`, as LibioDoAlloc.v proves it
    ([wp_glibc__IO_file_doallocate]). *)
Context (Hda_spec : forall fr fb freg fl fd eb oe vb vreg Φ,
  call_frame glibc__IO_file_doallocate [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  Mres -∗
  ▷ (pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ doalloc_k Mres fb freg fl fd eb Φ) -∗
  WP (ERun fr : sexpr) {{ Φ }}).

(** `c: _IO_doallocbuf(fp)` on a stream with no buffer that is not
    unbuffered ends as `c: _IO_file_doallocate` does. *)
Lemma wp_glibc__IO_doallocbuf_alloc fr fb freg fl fd eb oe vb vreg Φ :
  call_frame glibc__IO_doallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 -> Z.land fl io_unbuffered = 0 ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  Mres -∗
  ▷ (pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ doalloc_k Mres fb freg fl fd eb (fun _ => Φ RetVoid)) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg He Hfd Hfd31 Hub. injection Hfr as <-.
  iIntros "#Hvt Hl Hfl Hfd Herr Hb Hbe Hvtp HM HK". unfold file_size in Hend. unfold io_unbuffered in Hub.
  iPoseProof (vtables_slot ge vb vreg slot_doallocate "__GI__IO_file_doallocate" with "Hvt") as "#Hsd"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "__GI__IO_file_doallocate")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hdaf). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  enter. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer with "Hl Hb [//]"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hb _". st. st. br.
  st. chk "Hl". iDestruct "Hfl" as "[%Hfl Hflb]". load_int "Hl Hflb". st. st. brv false.
  st. br. st. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". st. st. st. st. st. brv true.
  st. st. norm.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hvl'"); [reflexivity | vx | right; reflexivity | ar | ar | ar |].
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsd Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hdaf) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hdaf) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hdaf) | apply (ge_fn_check _ _ _ Hdaf) | vx |
    apply (ge_fn_find _ _ _ Hdaf) | reflexivity | reflexivity |].
  iNext.
  iApply (Hda_spec _ fb freg fl fd eb oe vb vreg with "[] Hl [$Hflb //] Hfd Herr Hb Hbe Hvtp HM"); try side.
  { iFrame "Hvl Hslots". iPureIntro. unfold io_vtables_size. auto. }
  iNext. iIntros "Hvtp" (fl1 bb sz Hc) "Hl Hfl Hfd Hb Hbe Hbo Herr HM".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  st. br. st. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hvtp [%] Hl Hfl Hfd Hb Hbe Hbo Herr HM"). exact Hc.
  Unshelve. exact freg.
Qed.

End rules.
End LibioDoAllocBufOn.
