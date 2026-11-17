From Glibc Require Import GlibcProgram.
(** After handling pending output, close_it discards markers and closes the
    descriptor through the stream's jump table. These blocks then reset the
    stream using the supplied buffer contract. Like fclose, this path passes
    zero for unlink; removing the stream from a list belongs to its caller. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioCloseItCode FileInv LibioLogic
  SysWrappers LibioSetb LibioCloseSteps LibioCloseItEnd.
From Glibc Require FileInv LibioCloseItEnd LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCloseItEnd SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance close_it_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition close_spec : Prop := forall fr fb freg fd eb Φ,
  call_frame glibc__IO_file_close [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  live fb freg -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live fb freg -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
     Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Definition unsave_spec (fum : func) : Prop := forall fb, exists fr,
  call_frame fum [WPtr (mkPtr fb (Obj fb))] = Some fr /\
  forall freg Φ, 0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg ->
    ⊢ live fb freg -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
      ▷ (live fb freg -∗ pcell fb 80 null -∗ pcell fb 96 null -∗ Φ RetVoid) -∗
      WP (ERun fr : sexpr) {{ Φ }}.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close).
Context `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}.

(** Expressions use the caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The descriptor-close rule preserves the stream and returns either result. *)
Context (Hclose : (close_spec w0 registry ge)).


(** The setb rule receives the old buffer resource without inspecting it here. *)
Context (B : Z -> Z -> ptr -> iProp Σ)
  (Hsetb_spec : LibioCloseItEnd.setb_spec_with w0 registry ge B).
(** Marker cleanup preserves null marker and backup pointers.
    LibioGenLeaves proves this contract for the captured glibc function. *)
Context (fum : func)
  `{Hfum : !Defines ge "__GI__IO_unsave_markers" fum}.
Context (Hum : (unsave_spec w0 registry ge) fum).


(** The descriptor close determines the result when it fails; otherwise the
    saved write result determines it. Both paths reset buffer pointers,
    flags, descriptor and offset, while preserving errno ownership. *)
Lemma wp_close_it_L18_with e e' from a0 p3 fb freg fl f2 fd off md ob oe p8 p16 p24 p32 p40 p48 vb vreg eb Φ :
  let fp := mkPtr fb (Obj fb) in
  (forall b, find_block (TAtom "L18") (fn_blocks glibc__IO_file_close_maybe_unlink) = Some b ->
             phis_env ge (b_phis b) (Some from) e = Some e') ->
  lookup (TAtom "v0") e' = Some (WPtr fp) ->
  lookup (TAtom "chk0") e' = Some (WPtr (mkPtr a0 (Obj fb))) -> a0 = fb + off_fileno ->
  lookup (TAtom "chk1") e' = Some (WPtr fp) ->
  lookup (TAtom "v2") e' = Some (WInt 0) -> lookup (TAtom "pr.3") e' = Some (WInt p3) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> 0 <= f2 < 2 ^ 32 -> Z.land f2 32 = 0 -> md = 0 \/ md = 2 ^ 32 - 1 -> 0 <= p3 < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_offset off -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  errno_any eb -∗
  pcell fb 8 p8 -∗ pcell fb 16 p16 -∗ pcell fb 24 p24 -∗ pcell fb 32 p32 -∗ pcell fb 40 p40 -∗ pcell fb 48 p48 -∗
  pcell fb off_buf_base ob -∗ pcell fb off_buf_end oe -∗ B fb fl ob -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗
     live fb freg -∗ int_cell fb off_flags (closed_flags fl) -∗ int_cell fb off_flags2 f2 -∗
     int_cell fb off_fileno (2 ^ 32 - 1) -∗ icell fb off_offset (2 ^ 64 - 1) -∗ int_cell fb off_mode md -∗
     pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ errno_any eb -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     pcell fb 80 null -∗ pcell fb 96 null -∗
     Φ (Ret (WInt (if k =? 0 then p3 else k)))) -∗
  WP (ERun (mkFrame glibc__IO_file_close_maybe_unlink e [] None (Enter (TAtom "L18") (Some from))) : sexpr)
    {{ Φ }}.
Proof using Type*.
  intros fp Hphi Hv0 Hc0 Ha0 Hc1 Hv2 Hp3 Hfb Hfal Hfend Hfreg Hfl Hf2r Hf2 Hmd Hp3r He. subst fp a0.
  iIntros "#Hvt Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe Hob H80 H96 HK".
  unfold file_size in Hfend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply wp_enter; [reflexivity | apply Hphi; reflexivity |]. iNext. cbn [b_insts b_jump].
  (* L18: `c: _IO_unsave_markers`, then `c: _flags2 & _IO_FLAGS2_NOCLOSE`. *)
  destruct (Hum fb) as (frm & Hfrm & Hspec).
  iApply wp_call_bind; [vx | exact Hfum | exact Hfrm |]. iNext.
  iApply (Hspec with "Hl H80 H96"); [exact Hfb | exact Hfal | unfold file_size; lia |]. iNext. iIntros "Hl H80 H96". resume.
  iDestruct "Hfl2" as "[_ Hfl2]".
  step. check "Hl". load_s32 "Hl" "Hfl2". step. step. step. step.
  rewrite (flags2_mask f2 32 5); [|reflexivity | lia | exact Hf2r]. rewrite Hf2. branch.
  (* L202: the jump table's `c: __close`. *)
  iPoseProof (vtables_slot ge vb vreg slot_close "__GI__IO_file_close" with "Hvt") as "#Hsc"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "__GI__IO_file_close")) vreg) as "Hcap".
  { rewrite (ge_fn_cap _ _ _ Hfc). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)". unfold io_vtables_size in Hvend.
  step. step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true. step. step.
  check_read_dq "Hvl'" by a2.
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsc Hcap");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hfc) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfc) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfc) | apply (ge_fn_check _ _ _ Hfc) | vx |
    apply (ge_fn_find _ _ _ Hfc) | reflexivity | reflexivity |].
  iNext.
  iApply (Hclose with "Hl Hfd Herr"); try close_side.
  iNext. iIntros (k Hk) "Hl Hfd Herr". resume.
  (* L204, L223: `c: _IO_setb`, and the pointers null. *)
  step. step. step. check "Hl". iDestruct "Hmode" as "[%Hmr Hmode]". load_s32 "Hl" "Hmode". step.
  assert (Esx : (sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32) <? sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32))
                = false) by (destruct Hmd as [-> | ->]; reflexivity).
  rewrite Esx. clear Esx. branch.
  assert (Hkr : 0 <= k < 2 ^ 32) by (destruct Hk as [-> | ->]; lia).
  rewrite (Z.mod_small k (2 ^ 32)); [|exact Hkr]. rewrite (Z.mod_small k (2 ^ 32)); [|exact Hkr].
  iApply (LibioCloseItEnd.wp_close_it_L223_with B Hsetb_spec
            with "Hl Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe Hob"); try close_side.
  iNext. iIntros "Hl Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe".
  iAssert (int_cell fb off_mode md) with "[Hmode]" as "Hmode"; [iSplit; [done | iExact "Hmode"]|].
  iAssert (int_cell fb off_flags2 f2) with "[Hfl2]" as "Hfl2"; [iSplit; [done | iExact "Hfl2"]|].
  iApply ("HK" $! k with "[%] Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96").
  exact Hk.
Qed.

End rules.

Section legacy.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close).
Context `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}.
(** Existing callers still supply the original heap-buffer setb contract. *)
Definition wp_close_it_L18 (Hclose : close_spec w0 registry ge)
    (Hsetb_spec : LibioCloseItEnd.setb_spec w0 registry ge) (fum : func)
    `{Hfum : !Defines ge "__GI__IO_unsave_markers" fum} (Hum : unsave_spec w0 registry ge fum) :=
  wp_close_it_L18_with Hfc Hclose (fun _ => LibioCloseItEnd.old_base) Hsetb_spec fum Hum.
End legacy.
