(** getopt prints its diagnostics with glibc's __fxprintf_nocancel. The
    wrapper takes the stream's recursive lock, sets bit 2 of the
    `c: _flags2` bitfield while the formatter __vfprintf_internal runs,
    then restores the bitfield and releases the lock. This module proves
    the wrapper's entry, which copies the variadic arguments and checks
    the stream, and composes it with FxprintfLock.v, FxprintfTail.v and
    FxprintfJoin.v into one rule for the whole call.

    The rule applies when the stream is a real narrow stream whose lock is
    free or already held by this thread. It does not apply when the caller
    passes a null stream, which the wrapper replaces by stderr. It also
    does not apply when the stream is wide or another thread holds its
    lock. The formatter's own behavior remains a premise that the caller
    supplies, so this module does not prove formatting. *)
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  PrintfStreamInv FxprintfCode FxprintfStream FxprintfLock.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsThread OsWorld SysWrappers PrintfStreamInv.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Module FxVL := VariadicLogicOn R LG0.
Import PrintfStreamInv SysWrappers LibioCloseSteps FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic FxVL.


(** The checked function binds its two named parameters and snapshots
    every argument, including the named ones, before its first block. *)
Definition fx_frame (fp fmt : ptr) (ys : list word) : frame :=
  mkFrame glibc_fxprintf_nocancel (put (TAtom "v2") (WPtr fmt) (put (TAtom "v0") (WPtr fp) [])) [] None
    (Snapshot (WPtr fp :: WPtr fmt :: ys) (TAtom "start")).

(** Binding the call's arguments gives exactly this frame. *)
Lemma fx_call_frame fp fmt ys :
  call_frame glibc_fxprintf_nocancel (WPtr fp :: WPtr fmt :: ys) = Some (fx_frame fp fmt ys).
Proof. reflexivity. Qed.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Instance fx_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The thread-cookie call needs the registry contract and an external name. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** Taking the lock needs the current thread's identity, which the wrapper
    asks the OS for. This tactic proves that request when H shows that the
    identity is not null. *)
Ltac self H := iApply (OsThread.wp_zthread_self_cookie); try self_side; [exact H|]; iNext.

(** The wrapper preserves the stream's flags2 word and lock state, and the
    caller's share of the format string's lifetime. The formatter may leave
    the stream at another mode, which the formatter's result resource Q
    can record, and the wrapper returns its result reduced
    to a C int. The thread cookie must be a nonnull 64-bit address, and a
    held lock count must leave room for one more acquisition. *)
Lemma wp_fxprintf_at vb sb sreg fp fmt ys mode flags2 held dqf regf (R : iProp Σ) (Q : Z -> Z -> iProp Σ) Φ :
  forallb snapshot_word ys = true -> ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  0 <= ptr_addr fmt < 2 ^ 64 ->
  mode = 0 \/ mode = 2 ^ 32 - 1 -> (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32) ->
  fx_vfprintf_rule_at vb fp fmt (WPtr fp :: WPtr fmt :: ys) mode flags2 held R Q ->
  single_ro ge sb sreg -∗ printf_stream vb (ow_self w0) fp mode flags2 held -∗
  fx_owner (ow_self w0) held -∗ live_capq dqf (ptr_cap fmt) regf -∗ R -∗
  ▷ (∀ x mode', printf_stream vb (ow_self w0) fp mode' flags2 held -∗ fx_owner (ow_self w0) held -∗
     live_capq dqf (ptr_cap fmt) regf -∗ Q x mode' -∗ Φ (Ret (WInt (x mod 2 ^ 32)))) -∗
  WP (ERun (fx_frame fp fmt ys) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hys Hself Hselfr Hfmtr Hmode Hcnt Hfmt.
  iIntros "#Hs Hst Ho Hfc HR HK".
  iDestruct (printf_stream_fx with "Hst") as (fb freg fl lp Hp) "(Hl & Hfl & Hf2 & Hmd & Hlp & Hk & Hclose)".
  destruct Hp as (-> & Hal & Hfb & Hend & Hfreg & Hflr & Hul & Hnl & Hf2r & Hmdr).
  unfold file_size in Hend.
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  unfold fx_frame.
  iApply FxVL.wp_snapshot; [discriminate | cbn; exact Hys | intros ? ? ? ? Hf Hw; exact (os_wi_snapshot _ _ _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (sb' [Hsb [Hsmod Hsend']]) "Hsnap".
  change (sb' mod 16 = 0) in Hsmod.
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length (WPtr (mkPtr fb (Obj fb)) :: WPtr fmt :: ys)))) as Hext0.
  step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (cb [Hcb [Hcmod Hcend]]) "Hobj".
  change (cb mod 16 = 0) in Hcmod. change (cb + 32 <= 2 ^ 48) in Hcend.
  assert (Hc8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hx & Ha)"; [compute; discriminate |].
  iAssert (live cb (mkRegion cb (cb + 32) Heap Live)) with "Hcl" as "Hcl".
  set (creg := mkRegion cb (cb + 32) Heap Live) in *. assert (Hcre : r_end creg = cb + 32) by reflexivity.
  iDestruct (zero_cell_prefix cb 0 24 with "Hx Ha") as "(Hcc & _ & _)".
  iApply FxVL.wp_va_args; [reflexivity |]. iNext.
  step. step. step.
  assert (Hnn : ((if fb mod 2 ^ 64 =? (0 mod 2 ^ 64) mod 2 ^ 64 then 1 else 0) mod 2 ^ 32 =? 0) = true).
  { change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0. rewrite (Z.mod_small fb); [|lia].
    destruct (Z.eqb_spec fb 0); [lia | reflexivity]. }
  branch_symbolic. rewrite Hnn. cbn [edge_label].
  step. check "Hcl". store "Hcl" "Hcc".
  assert (Hva : (ptr_addr (mkPtr sb' (Ro sb')) + 16) mod 2 ^ 64 = sb' + 16) by (cbn; apply Z.mod_small; lia).
  iEval (rewrite Hva) in "Hcc".
  assert (Hok : fx_snap_ok sb' (WPtr (mkPtr fb (Obj fb)) :: WPtr fmt :: ys)) by (split_and!; assumption).
  clear Hsb Hsmod Hsend' Hext0 Hva.
  iAssert (pts (va_cursor_ps cb creg (mkPtr (sb' + 16) (Ro sb')))) with "[Hcl Hcc]" as "Hcur".
  { replace (va_cursor_ps cb creg (mkPtr (sb' + 16) (Ro sb'))) with
      ([(PLive cb, VLive creg)] ++ ((PAux cb 0, VAux (Ro sb')) :: cell cb 0 (sb' + 16)))%list by reflexivity.
    rewrite pts_app. iFrame "Hcl Hcc". }
  iDestruct "Hfl" as "[_ Hfl]".
  check "Hl". load_s32 "Hl" "Hfl". step. step. unfold io_user_lock in Hul. branch_as false.
  step. self Hself. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  iDestruct ("Hclose" $! flags2 held with "[%] Hl [Hfl] Hf2 Hmd Hlp Hk") as "Hst".
  { exact Hnl. }
  { iSplit; [done | iExact "Hfl"]. }
  iApply (wp_fx_lock _ vb sb sreg fb cb sb' fmt ys mode flags2 held dqf regf R Q with "Hs Hst Ho Hcur Hsnap Hfc HR HK");
    first [exact Hself | exact Hselfr | exact Hok | exact Hfmtr | exact Hmode | exact Hcnt | exact Hfmt | lk_prove].
Qed.

(** The same holds when the result resource ignores the returned mode. *)
Lemma wp_fxprintf vb sb sreg fp fmt ys mode flags2 held dqf regf (R : iProp Σ) (Q : Z -> iProp Σ) Φ :
  forallb snapshot_word ys = true -> ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  0 <= ptr_addr fmt < 2 ^ 64 ->
  mode = 0 \/ mode = 2 ^ 32 - 1 -> (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32) ->
  fx_vfprintf_rule vb fp fmt (WPtr fp :: WPtr fmt :: ys) mode flags2 held R Q ->
  single_ro ge sb sreg -∗ printf_stream vb (ow_self w0) fp mode flags2 held -∗
  fx_owner (ow_self w0) held -∗ live_capq dqf (ptr_cap fmt) regf -∗ R -∗
  ▷ (∀ x mode', printf_stream vb (ow_self w0) fp mode' flags2 held -∗ fx_owner (ow_self w0) held -∗
     live_capq dqf (ptr_cap fmt) regf -∗ Q x -∗ Φ (Ret (WInt (x mod 2 ^ 32)))) -∗
  WP (ERun (fx_frame fp fmt ys) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hys Hself Hselfr Hfmtr Hmode Hcnt Hfmt.
  exact (wp_fxprintf_at vb sb sreg fp fmt ys mode flags2 held dqf regf R (fun x _ => Q x) Φ
    Hys Hself Hselfr Hfmtr Hmode Hcnt (fx_vfprintf_rule_at_of _ _ _ _ _ _ _ _ _ Hfmt)).
Qed.

(** A caller that executes `c: __fxprintf_nocancel (fp, fmt, ...)` resumes
    with the same resources and the wrapper's result in its destination. *)
Lemma wp_call_fxprintf_at f e ls l d args rest j vb sb sreg fp fmt ys mode flags2 held dqf regf
    (R : iProp Σ) (Q : Z -> Z -> iProp Σ) Φ :
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr fmt :: ys) ->
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined glibc_fxprintf_nocancel) ->
  forallb snapshot_word ys = true -> ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  0 <= ptr_addr fmt < 2 ^ 64 ->
  mode = 0 \/ mode = 2 ^ 32 - 1 -> (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32) ->
  fx_vfprintf_rule_at vb fp fmt (WPtr fp :: WPtr fmt :: ys) mode flags2 held R Q ->
  single_ro ge sb sreg -∗ printf_stream vb (ow_self w0) fp mode flags2 held -∗
  fx_owner (ow_self w0) held -∗ live_capq dqf (ptr_cap fmt) regf -∗ R -∗
  ▷ (∀ x mode', printf_stream vb (ow_self w0) fp mode' flags2 held -∗ fx_owner (ow_self w0) held -∗
     live_capq dqf (ptr_cap fmt) regf -∗ Q x mode' -∗
     WP (ERun (mkFrame f (put d (WInt (x mod 2 ^ 32)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hargs Hfn Hys Hself Hselfr Hfmtr Hmode Hcnt Hfmt.
  iIntros "#Hs Hst Ho Hfc HR HK".
  iApply (wp_call_bind registry (os_wi w0) ge); [exact Hargs | exact Hfn | apply fx_call_frame |].
  iNext. iApply (wp_fxprintf_at with "Hs Hst Ho Hfc HR"); try eassumption.
  iNext. iIntros (x md) "Hst Ho Hfc HQ".
  iExists (mkFrame f (put d (WInt ((x mod 2 ^ 32) mod 2 ^ 32)) e) ls None (Exec l rest j)).
  iSplit; [done|]. iNext. rewrite Z.mod_mod; [|lia]. iApply ("HK" with "Hst Ho Hfc HQ").
Qed.

(** The call-site rule also holds when the result resource ignores the mode. *)
Lemma wp_call_fxprintf f e ls l d args rest j vb sb sreg fp fmt ys mode flags2 held dqf regf
    (R : iProp Σ) (Q : Z -> iProp Σ) Φ :
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr fmt :: ys) ->
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined glibc_fxprintf_nocancel) ->
  forallb snapshot_word ys = true -> ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  0 <= ptr_addr fmt < 2 ^ 64 ->
  mode = 0 \/ mode = 2 ^ 32 - 1 -> (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32) ->
  fx_vfprintf_rule vb fp fmt (WPtr fp :: WPtr fmt :: ys) mode flags2 held R Q ->
  single_ro ge sb sreg -∗ printf_stream vb (ow_self w0) fp mode flags2 held -∗
  fx_owner (ow_self w0) held -∗ live_capq dqf (ptr_cap fmt) regf -∗ R -∗
  ▷ (∀ x mode', printf_stream vb (ow_self w0) fp mode' flags2 held -∗ fx_owner (ow_self w0) held -∗
     live_capq dqf (ptr_cap fmt) regf -∗ Q x -∗
     WP (ERun (mkFrame f (put d (WInt (x mod 2 ^ 32)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hargs Hfn Hys Hself Hselfr Hfmtr Hmode Hcnt Hfmt.
  exact (wp_call_fxprintf_at f e ls l d args rest j vb sb sreg fp fmt ys mode flags2 held dqf regf R
    (fun x _ => Q x) Φ Hargs Hfn Hys Hself Hselfr Hfmtr Hmode Hcnt (fx_vfprintf_rule_at_of _ _ _ _ _ _ _ _ _ Hfmt)).
Qed.

End rules.
