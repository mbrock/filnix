(** The end of `c: _IO_new_fclose(fp)` (LibioFcloseCode.v,
    libio/iofclose.c) for stdout, from block `c: L8`, after
    `c: _IO_file_close_it` and the unlock: `c: _IO_un_link(fp)`
    (LibioUnlink.v's [wp_glibc__IO_un_link], whose triple is
    [unlink_spec]), the jump table's `c: __finish`
    (LibioFinish.v's [wp_glibc__IO_new_file_finish_closed]), no backup
    area to free, and, since fp is `c: _IO_2_1_stdout_`, no
    `c: free(fp)`: the result is `c: pr.1`, the close's
    ([wp_fclose_L8]). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioUnlinkCode LibioFcloseCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFinish.
From Glibc Require FileInv LibioCloseSteps LibioFinish LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioFinish SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hunl : find_fn ge (TAtom "__GI__IO_un_link") = Some (Defined glibc__IO_un_link)).
Context (Hdf : find_fn ge (TAtom "__GI__IO_default_finish") = Some (Defined glibc__IO_default_finish)).
Context (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance fclose_tail_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [stream_life] g, as LibioUnlinkMid.v's: the life of the stream g. *)
Definition stream_life (g : ptr) : iProp Σ :=
  ∃ gb greg, ⌜g = mkPtr gb (Obj gb) /\ 0 < gb /\ gb mod 8 = 0 /\ gb + file_size <= r_end greg /\
              r_end greg <= 2 ^ 63⌝ ∗ live gb greg.

(** `c: _IO_un_link`'s triple on a linked stream, as LibioUnlink.v's
    [wp_glibc__IO_un_link] states it (4294967167 is `c: ~_IO_LINKED`). *)
Definition unlink_spec : Prop := forall fr pre post fb freg fl lb lbreg sb sreg fcp Φ,
  let fp := mkPtr fb (Obj fb) in
  call_frame glibc__IO_un_link [WPtr fp] = Some fr ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_user_lock = false -> has fl io_linked = true ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ live fb freg -∗ int_cell fb off_flags (Z.land fl 4294967167) -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ c p, pcell fb off_chain c ∗ pcell fb off_prevchain p) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

(** The triples the tail calls. *)
Context (Hunl_spec : unlink_spec) (Hunl_unlinked : unlink_unlinked_spec w0 registry ge).

(** Clearing `c: _IO_LINKED` leaves a stream unlinked. *)
Lemma unlink_has fl : has (Z.land fl 4294967167) io_linked = false.
Proof.
  unfold has, io_linked. rewrite <- Z.land_assoc. change (Z.land 4294967167 128) with 0.
  rewrite Z.land_0_r. reflexivity.
Qed.

(** Block `c: L8` of `c: _IO_new_fclose(fp)` for stdout (the symbol
    `c: _IO_2_1_stdout_`, not `c: _IO_2_1_stdin_`), whose close gave
    p1, to its return: fp leaves the list pre ++ fp :: post, its
    `c: __finish` runs, and since fp is stdout it is not freed. The
    stream is un-oriented or narrow, `c: _mode` md 0 or -1, so the
    wide part is skipped. *)
Lemma wp_fclose_L8 e from p1 pre post fb freg fl lb lbreg sb sreg fcp vb vreg pin md Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  lookup (TAtom "pr.1") e = Some (WInt p1) -> 0 <= p1 < 2 ^ 32 ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_user_lock = false -> has fl io_linked = true -> 0 < lb ->
  md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  int_cell fb off_fileno (2 ^ 32 - 1) -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb off_buf_base null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ live fb freg -∗ int_cell fb off_flags (Z.land fl 4294967167) -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ c p, pcell fb off_chain c ∗ pcell fb off_prevchain p) -∗
     int_cell fb off_fileno (2 ^ 32 - 1) -∗ int_cell fb off_mode md -∗
     pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     pcell fb off_buf_base null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗ Φ (Ret (WInt p1))) -∗
  WP (ERun (mkFrame glibc__IO_new_fclose e [] None (Enter (TAtom "L8") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hv0 Hc0 Hp1 Hp1r Hgout Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk Hlb Hmd. subst fp.
  iIntros "#Hvt #Hs Htcb Hl Hfl Hlp Hlb Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 HK".
  unfold file_size in Hfend.
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* `c: _IO_un_link(fp)`. *)
  step. iApply wp_call_bind; [vx | exact Hunl | reflexivity |]. iNext.
  iApply (Hunl_spec with "Hs Htcb Hl Hfl Hlp Hlb Hio Hlives"); try close_side.
  iNext. iIntros "Htcb Hl Hfl Hlp Hlb Hio Hlives Hlinks". resume.
  (* The jump table's `c: __finish`. *)
  iPoseProof (vtables_slot ge vb vreg slot_finish "_IO_new_file_finish" with "Hvt") as "#Hsf"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_finish")) vreg) as "Hcap".
  { rewrite (ge_fn_cap _ _ _ Hff). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)". unfold io_vtables_size in Hvend.
  step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true. step. step.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hvl'"); [reflexivity | vx | right; reflexivity | a2 | a2 | a2 |].
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsf Hcap");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hff) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hff) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hff) | apply (ge_fn_check _ _ _ Hff) | vx |
    apply (ge_fn_find _ _ _ Hff) | reflexivity | reflexivity |].
  iNext.
  iDestruct "Hlb" as "(%Hb & Hbl & Hb0 & Hb4 & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 w0 registry ge with "Hbl"). iIntros ([Hb0' Hb48]) "Hbl".
  pose proof (unlink_has fl) as Hun. assert (0 <= Z.land fl 4294967167 < 2 ^ 32) by (apply land_lt32; lia).
  iApply (LibioFinish.wp_glibc__IO_new_file_finish_closed w0 registry ge Hunl Hdf Hunl_unlinked
            with "Hl Hfd Hfl Hbb H80 H96 Hlp Hbl"); try close_side.
  iNext. iIntros "Hl Hfd Hfl Hbb H80 H96 Hlp Hbl". resume.
  (* `c: _mode` 0 or -1, not wide; no backup area; fp is stdout. *)
  iDestruct "Hmode" as "[%Hmr Hmode]".
  step. check "Hl". load_s32 "Hl" "Hmode". step.
  assert (Esx : (sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32) <? sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32))
                = false) by (destruct Hmd as [-> | ->]; reflexivity).
  rewrite Esx. clear Esx. branch.
  step. step. check "Hl". load_null "Hl" "H80". step. step. step. branch.
  step. step. step. step. step. branch_as true. step. step. step. step. step. step. branch_as false. step. branch. step.
  iApply wp_ret; [reflexivity | vx |]. iNext. rewrite (Z.mod_small p1 (2 ^ 32)); [|lia].
  iApply ("HK" with "Htcb Hl Hfl Hlp [Hbl Hb0 Hb4 Hbo] Hio Hlives Hlinks Hfd [Hmode] Hvtp Hbb H80 H96").
  - iFrame. iPureIntro. split_and!; assumption.
  - iSplit; [done | iExact "Hmode"].
Qed.

End rules.
