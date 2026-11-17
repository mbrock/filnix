From Glibc Require Import GlibcProgram.
(** Closing a standard output stream must remove it from glibc's list
    without freeing the static stream object. This proof follows the
    end of fclose after the buffer has been released and the lock freed.
    It runs the unlink and finish calls, checks the standard-stream
    addresses, and returns the saved close result, including failure.
    Both stdout and stderr use the same instruction proof. *)

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
Local Instance fclose_tail_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition stream_life (g : ptr) : iProp Σ :=
  ∃ gb greg, ⌜g = mkPtr gb (Obj gb) /\ 0 < gb /\ gb mod 8 = 0 /\ gb + file_size <= r_end greg /\
              r_end greg <= 2 ^ 63⌝ ∗ live gb greg.
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
Lemma unlink_has fl : has (Z.land fl 4294967167) io_linked = false.
Proof using Type*.
  unfold has, io_linked. rewrite <- Z.land_assoc. change (Z.land 4294967167 128) with 0.
  rewrite Z.land_0_r. reflexivity.
Qed.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}.
Context `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}.
Context (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish).


Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The unlink call removes the stream from the list. The finish call
    may invoke unlink again, when the stream is already unlinked. *)
Context (Hunl_spec : (unlink_spec w0 registry ge))
  (Hunl_unlinked : unlink_unlinked_spec w0 registry ge).

(** Each rule application repeats the whole current frame, so a long proof
    walks the same environment and instruction list once per step. These
    tactics keep both behind local definitions: the environment is named
    after every step, the remaining instructions are a chain of definitions
    whose bodies hold one instruction each, and only the next instruction is
    shown. The block's final jump stays named until no instruction is left. The rules see the same frame up to unfolding those definitions. *)
Local Ltac chain_tail L :=
  lazymatch L with
  | _ :: ?R => first [lazymatch R with _ :: _ => chain_tail R end | let X := fresh "I" in set (X := L)]
  end.
Local Ltac tidy :=
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ ?L _))) _) => is_var L; unfold L
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ [] ?J))) _) => is_var J; unfold J
  end;
  repeat lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ (_ :: ?R) _))) _) =>
      lazymatch R with _ :: _ => chain_tail R end
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ (_ :: _) ?J))) _) =>
      first [is_var J | let X := fresh "J" in set (X := J)]
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ ?e _ _ _)) _) =>
      lazymatch e with put _ _ _ => let E := fresh "Env" in set (E := e) end
  end.

(** Closing either static output stream removes it from the stream list
    but does not free its object. The stdout case stops before looking up
    stderr; the stderr case compares all three standard-stream addresses.
    The stream is narrow or unoriented, and its buffer is already gone. *)
Lemma wp_fclose_L8_static_output e from p1 pre post fb freg fl lb lbreg sb sreg fcp vb vreg pin pout md Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  lookup (TAtom "pr.1") e = Some (WInt p1) -> 0 <= p1 < 2 ^ 32 ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some pout ->
  (pout = fp \/ (ptr_addr pout <> fb /\ 0 <= ptr_addr pout < 2 ^ 64 /\
    lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fp)) ->
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
  intros fp Hv0 Hc0 Hp1 Hp1r Hgout Hstatic Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk Hlb Hmd. subst fp.
  iIntros "#Hvt #Hs Htcb Hl Hfl Hlp Hlb Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 HK".
  unfold file_size in Hfend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* `c: _IO_un_link(fp)`. *)
  step; tidy. iApply wp_call_bind; [vx | exact Hunl | reflexivity |]. iNext.
  iApply (Hunl_spec with "Hs Htcb Hl Hfl Hlp Hlb Hio Hlives"); try close_side.
  iNext. iIntros "Htcb Hl Hfl Hlp Hlb Hio Hlives Hlinks". resume; tidy.
  (* The jump table's `c: __finish`. *)
  iPoseProof (vtables_slot ge vb vreg slot_finish "_IO_new_file_finish" with "Hvt") as "#Hsf"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_finish")) vreg) as "Hcap".
  { rewrite (ge_fn_cap _ _ _ Hff). done. }
  set (fin := "_IO_new_file_finish").
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)". unfold io_vtables_size in Hvend.
  step; tidy. check "Hl"; tidy.
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". tidy. step; tidy. step; tidy. step; tidy. step; tidy. step; tidy. branch_as true; tidy. step; tidy. step; tidy.
  check_read_dq "Hvl'" by a2.
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsf Hcap");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hff) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hff) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hff) | apply (ge_fn_check _ _ _ Hff) | vx |
    apply (ge_fn_find _ _ _ Hff) | reflexivity | reflexivity |].
  iNext.
  iDestruct "Hlb" as "(%Hb & Hbl & Hb0 & Hb4 & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hb0' Hb48]) "Hbl".
  pose proof (unlink_has fl) as Hun. assert (0 <= Z.land fl 4294967167 < 2 ^ 32) by (apply land_lt32; lia).
  iApply (LibioFinish.wp_glibc__IO_new_file_finish_closed Hunl_unlinked
            with "Hl Hfd Hfl Hbb H80 H96 Hlp Hbl"); try close_side.
  iNext. iIntros "Hl Hfd Hfl Hbb H80 H96 Hlp Hbl". resume; tidy.
  (* Narrow or unoriented streams have no wide cleanup here. *)
  iDestruct "Hmode" as "[%Hmr Hmode]".
  step; tidy. check "Hl"; tidy. load_s32 "Hl" "Hmode"; tidy. step.
  assert (Esx : (sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32) <? sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32))
                = false) by (destruct Hmd as [-> | ->]; reflexivity).
  rewrite Esx. clear Esx. branch; tidy.
  step; tidy. step; tidy. check "Hl"; tidy. load_null "Hl" "H80"; tidy. step; tidy. step; tidy. step; tidy. branch; tidy.
  destruct Hstatic as [-> | (Hout & Houtr & Hgerr)].
  all: repeat first [step; tidy | branch_as true; tidy | branch_as false; tidy].
  all: iApply wp_ret; [reflexivity | vx |]; iNext; rewrite (Z.mod_small p1 (2 ^ 32)); [|lia].
  all: iApply ("HK" with "Htcb Hl Hfl Hlp [Hbl Hb0 Hb4 Hbo] Hio Hlives Hlinks Hfd [Hmode] Hvtp Hbb H80 H96").
  all: first [iFrame; iPureIntro; split_and!; assumption | iSplit; [done | iExact "Hmode"]].
Qed.

(** The original stdout rule needs no stderr lookup because its address
    comparison succeeds before execution reaches that lookup. *)
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
Proof using Type*.
  intros fp Hv0 Hc0 Hp1 Hp1r Hgout Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk Hlb Hmd.
  apply (wp_fclose_L8_static_output e from p1 pre post fb freg fl lb lbreg sb sreg fcp vb vreg pin fp md Φ);
    try assumption. left. reflexivity.
Qed.

(** Stderr takes the third static-object comparison, after failing the
    stdin and stdout comparisons. The saved close result is returned
    unchanged, even when closing failed. Errno and other caller memory
    can remain framed throughout this tail. *)
Lemma wp_fclose_L8_stderr e from p1 pre post fb freg fl lb lbreg sb sreg fcp vb vreg pin pout md Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  lookup (TAtom "pr.1") e = Some (WInt p1) -> 0 <= p1 < 2 ^ 32 ->
  lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some pout -> ptr_addr pout <> fb ->
  0 <= ptr_addr pout < 2 ^ 64 ->
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
  intros fp Hv0 Hc0 Hp1 Hp1r Hgerr Hgout Hout Houtr Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk Hlb Hmd.
  apply (wp_fclose_L8_static_output e from p1 pre post fb freg fl lb lbreg sb sreg fcp vb vreg pin pout md Φ);
    try assumption. right. auto.
Qed.

End rules.
