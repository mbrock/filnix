(** `c: _IO_un_link(fp)` (LibioUnlinkCode.v, libio/genops.c), which
    `c: fclose` calls to take a stream off `c: _IO_list_all`.

    An unlinked stream (`c: _IO_LINKED`, 128, clear in `c: _flags`)
    is left alone ([wp_glibc__IO_un_link_unlinked]). A linked one, one
    of the streams [io_list_inv] lists ([wp_glibc__IO_un_link]): the
    call pushes a cleanup buffer (SysCleanup.v), takes
    `c: list_all_lock` and the stream's lock, both free, as the single
    thread ([single_ro]), sets `c: run_fp`, splices the stream out of
    the list (LibioUnlinkMid.v), clears `c: _IO_LINKED`, and releases
    and pops everything again (LibioUnlinkTail.v). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioUnlinkCode FileInv LibioLogic
  SysWrappers SysCleanup LibioCloseSteps LibioUnlinkTail LibioUnlinkMid LibioUnlinkLock.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioUnlinkLock LibioUnlinkMid LibioUnlinkTail OsThread OsWorld SysCleanup SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioUnlinkLock LibioUnlinkMid LibioUnlinkTail SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hpush : find_fn ge (TAtom "__GI___libc_cleanup_push_defer") =
                 Some (Defined glibc___libc_cleanup_push_defer)).
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance unlink_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** A call of `c: zthread_self_cookie`, whose result is the thread's
    cookie, not null (H). *)
Ltac self H := iApply (OsThread.wp_zthread_self_cookie w0 registry ge); try self_side; [exact H|]; iNext.

(** `c: _IO_un_link(fp)` of a stream whose `c: _flags` lacks
    `c: _IO_LINKED`: the cleanup buffer is allocated, the flag read,
    and the call returns. *)
Lemma wp_glibc__IO_un_link_unlinked fr fb freg fl Φ :
  call_frame glibc__IO_un_link [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_linked = false ->
  live fb freg -∗ int_cell fb off_flags fl -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hfal Hfend Hfreg Hfl Hlnk. injection Hfr as <-. unfold file_size in Hfend.
  unfold has, io_linked in Hlnk. apply negb_false_iff, Z.eqb_eq in Hlnk.
  assert (0 <= Z.land fl 128 < 2 ^ 32) by (rewrite Hlnk; lia).
  iIntros "Hl [_ Hfl] HK". iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (cb _) "_". check "Hl". load_s32 "Hl" "Hfl". step. branch_as true. step.
  iApply wp_ret_void. iNext. iApply ("HK" with "Hl"). iSplit; [done|]. iExact "Hfl".
Qed.

(** `c: _IO_un_link(fp)` of the stream fb in [io_list_inv]'s list
    pre ++ fp :: post, linked, its lock free, with the lives of the
    other streams: afterwards the list is pre ++ post, `c: _flags`
    lacks `c: _IO_LINKED` ([unlinked_flags]), the lock is free again,
    fb's own links are fb's, and [tcb_cleanup_inv] holds again. The
    cleanup routine's pointer, `c: flush_cleanup`, is ge's symbol. *)
Lemma wp_glibc__IO_un_link fr pre post fb freg fl lb lbreg sb sreg fcp Φ :
  let fp := mkPtr fb (Obj fb) in
  call_frame glibc__IO_un_link [WPtr fp] = Some fr ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_user_lock = false -> has fl io_linked = true ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ live fb freg -∗ int_cell fb off_flags (unlinked_flags fl) -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ c p, pcell fb off_chain c ∗ pcell fb off_prevchain p) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros fp Hfr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk. injection Hfr as <-. unfold file_size in Hfend.
  subst fp.
  unfold has, io_linked, io_user_lock in Hlnk, Hul.
  apply negb_true_iff, Z.eqb_neq in Hlnk. apply negb_false_iff, Z.eqb_eq in Hul.
  assert (0 <= Z.land fl 128 < 2 ^ 32) by (split; [apply Z.land_nonneg; lia | apply land_lt32; lia]).
  assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul; lia).
  iIntros "#Hs Htcb Hl [_ Hfl] Hlp Hlb Hio Hlives HK".
  iDestruct "Hio" as (la lareg lk lkreg rf rfreg Hio) "(Hla & Hlah & Hch & Hlk & Hrl & Hrc)".
  destruct Hio as (Hgla & Hglk & Hgrf & Hlaal & Hlaend & Hral & Hrend).
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Htcb" as (tb treg jb Ht) "Htcb". pose proof Ht as (Hself & Htb & _).
  iAssert (tcb_cleanup_inv (ow_self w0)) with "[Htcb]" as "Htcb".
  { iExists tb, treg, jb. iSplit; [iPureIntro; exact Ht | iExact "Htcb"]. }
  assert (Hsz : ptr_addr (ow_self w0) <> 0) by (rewrite Hself; cbn; lia).
  iDestruct "Hlk" as "(%Hk & Hkl & [%Hk0r Hk0] & [%Hk4r Hk4] & Hko)". destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hla"). iIntros ([Hla0 Hla48]) "Hla".
  iApply (wp_live_fit1 w0 registry ge with "Hkl"). iIntros ([Hlk0 Hlk48]) "Hkl".
  iApply (wp_live_fit1 w0 registry ge with "Hrl"). iIntros ([Hrf0 Hrf48]) "Hrl".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* start: the cleanup buffer, and `c: _IO_LINKED`. *)
  step. iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (cb [Hcb [Hcal Hcend]]) "Hobj". cbn in Hcal, Hcend.
  change (Z.pos (32 + 15) / 16 * 16) with 32 in Hcend.
  assert (Hcal8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj32 with "Hobj") as "(Hcl & Hc0 & Hc8 & Hc16 & Hc24)".
  set (creg := mkRegion cb (cb + 32) Heap Live). assert (Hcre : r_end creg = cb + 32) by reflexivity.
  check "Hl". load_s32 "Hl" "Hfl". step. branch_as false.
  (* L2: push the cleanup buffer; L31, L32, L25: take `c: list_all_lock`. *)
  step. step. step. check "Hcl". store "Hcl" "Hc8". check "Hcl". store "Hcl" "Hc0".
  iApply wp_call_bind; [vx | exact Hpush | reflexivity |]. iNext.
  iApply (SysCleanup.wp_glibc___libc_cleanup_push_defer w0 registry ge Hreg Hext _ cb _ 0 with "Htcb Hcl Hc24 Hc16");
    [rewrite Z.add_0_r; reflexivity | lia | lia | rewrite Z.add_0_r; exact Hcal8 | lia | lia |
     reflexivity |].
  iNext. iIntros "Htcb Hcl Hc24 Hc16". iEval (rewrite Z.add_0_r) in "Htcb". resume.
  self Hsz. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. step. check "Hkl". load_null "Hkl" "Hko". step. step. step. step. step. branch.
  step. step. check "Hkl". store_int "Hkl" "Hk0". step. step. check "Hkl". store "Hkl" "Hko". step.
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done|]; iExact "Hfl"|].
  iAssert (lock_state lk lkreg 1 0 (ow_self w0)) with "[Hkl Hk0 Hk4 Hko]" as "Hlk".
  { iFrame. iPureIntro. unfold int_bytes. split_and!; try lia. }
  iApply (wp_unlink_L22 w0 registry ge Hreg Hext Hpop with
            "Hs Htcb Hl Hfl Hlp Hlb Hla Hlah Hch Hlk Hrl Hrc Hlives Hcl Hc24 Hc16"); try close_side.
  iNext. iIntros "Htcb Hl Hfl Hlp Hlb Hla Hlah Hch Hlk Hrl Hrc Hlives Hf".
  iApply ("HK" with "Htcb Hl Hfl Hlp Hlb [Hla Hlah Hch Hlk Hrl Hrc] Hlives Hf").
  iExists la, lareg, lk, lkreg, rf, rfreg. iFrame. iPureIntro. split_and!; assumption.
Qed.

End rules.
