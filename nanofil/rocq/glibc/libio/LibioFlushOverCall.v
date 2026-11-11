(** This file proves the call that a pass of `c: _IO_flush_all`'s
    loop (LibioFlushCode.v) makes for a narrow stream that still
    buffers output. Block `c: L240` checks the stream's jump table against
    `c: __io_vtables` and calls its `c: __overflow` slot,
    `c: _IO_new_file_overflow (fp, EOF)`, whose triple is the premise
    [overflow_spec]. If the call returns EOF, so does the pass. The
    sync test after it calls nothing (LibioFlushClean.v's
    [wp_flush_L192]). LibioFlushOver.v reaches block `c: L240` and
    makes the whole pass. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean
  LibioFlushStart LibioFlushTail LibioFlushBody.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioFlushOverCallOn (R : Runtime) (LG0 : LogicSig R).
Module FB := LibioFlushBodyOn R LG0.
Import FB FB.FT FB.FT.FS FB.FT.FS.FC FB.FT.FS.FC.FU FB.FT.FS.FC.FU.FL FB.FT.FS.FC.FU.FL.CS
  FB.FT.FS.FC.FU.FL.CS.SW FB.FT.FS.FC.FU.FL.CS.SW.FI.ML FB.FT.FS.FC.FU.FL.CS.SW.FI.LG
  FB.FT.FS.FC.FU.FL.CS.SW.FI.L FB.FT.FS.FC.FU.FL.CS.SW.OW FB.FT.FS.FC.FU.FL.CS.SW.FI FB.FT.FS.FC.FU.FL.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hovf : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance flush_over_call_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_new_file_overflow (fp, EOF)`'s triple for the stream fb
    and the caller's resource Rest: from the cells the flush reads,
    the narrow file jump table and Rest, it returns some k with the
    flags fl', the mode, `c: _flags2` and the descriptor kept, and the
    four buffer pointers sharing a capability c' again, the write
    pointer not above the write base and the read pointer not below
    the read end. `c: _IO_USER_LOCK` stays clear, and the mode keeps
    the buffer as [exit_stream] says. *)
Definition overflow_spec (Rest : Z -> iProp Σ) : Prop :=
  forall fr fb freg fl f2 fd md c breg arp are awb awp vb Φ,
  call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt (2 ^ 32 - 1)] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ⊢ live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
    int_cell fb off_mode md -∗ pcell fb 8 (mkPtr arp c) -∗ pcell fb 16 (mkPtr are c) -∗
    pcell fb 32 (mkPtr awb c) -∗ pcell fb 40 (mkPtr awp c) -∗ live_cap c breg -∗
    pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ Rest fb -∗
    ▷ (∀ k fl' c' breg' arp' are' awb' awp',
       ⌜0 <= k < 2 ^ 32 /\ 0 <= fl' < 2 ^ 32 /\ Z.land fl' 32768 = 0 /\ (Z.land fl' io_unbuffered <> 0 \/ md = 0) /\
        0 <= awp' <= awb' /\ awb' < 2 ^ 64 /\ 0 <= are' <= arp' /\ arp' < 2 ^ 64⌝ -∗
       live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
       int_cell fb off_mode md -∗ pcell fb 8 (mkPtr arp' c') -∗ pcell fb 16 (mkPtr are' c') -∗
       pcell fb 32 (mkPtr awb' c') -∗ pcell fb 40 (mkPtr awp' c') -∗ live_cap c' breg' -∗
       pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ Φ (Ret (WInt k))) -∗
    WP (ERun fr : sexpr) {{ Φ }}.

(** [overflow_spec] Rest holds. *)
Context (Rest : Z -> iProp Σ) (Hov : overflow_spec Rest).

(** Block `c: L240` of `c: _IO_flush_all`, entered from `c: L211`,
    to block `c: L182`, for the stream fb in `c: pr.5` and
    `c: chk13`: the jump table is checked against `c: __io_vtables`,
    `c: _IO_new_file_overflow (fp, EOF)` is called through its
    `c: __overflow` slot, and `c: L182` is entered from `c: L257`
    with the result so far r, or EOF if the call returned EOF, in
    `c: pr.2`. The sync test between reads `c: chk31`, which block
    `c: L180` bound to the mode's address. *)
Lemma wp_flush_L240 e fb freg fl f2 fd md c breg arp are awb awp vb vreg r cb a31 Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "pr.5") e = Some (WPtr fp) -> lookup (TAtom "chk13") e = Some (WPtr fp) ->
  lookup (TAtom "chk31") e = Some (WPtr (mkPtr a31 (Obj fb))) ->
  lookup (TAtom "pr.4") e = Some (WInt r) -> lookup (TAtom "v3") e = Some (WPtr cb) -> 0 <= r < 2 ^ 32 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  md = 0 \/ md = 2 ^ 32 - 1 -> fd < 2 ^ 31 ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗
  int_cell fb off_mode md -∗ int_cell fb off_fileno fd -∗
  pcell fb 8 (mkPtr arp c) -∗ pcell fb 16 (mkPtr are c) -∗ pcell fb 32 (mkPtr awb c) -∗
  pcell fb 40 (mkPtr awp c) -∗ live_cap c breg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ Rest fb -∗
  ▷ (∀ e' r2 fl' c' breg' arp' are' awb' awp',
     ⌜lookup (TAtom "pr.5") e' = Some (WPtr fp) /\ lookup (TAtom "chk13") e' = Some (WPtr fp) /\
      lookup (TAtom "pr.2") e' = Some (WInt r2) /\ lookup (TAtom "v3") e' = Some (WPtr cb) /\
      0 <= r2 < 2 ^ 32 /\ (r2 = r \/ r2 = 2 ^ 32 - 1) /\
      0 <= fl' < 2 ^ 32 /\ Z.land fl' 32768 = 0 /\ (Z.land fl' io_unbuffered <> 0 \/ md = 0) /\
      0 <= awp' <= awb' /\ awb' < 2 ^ 64 /\ 0 <= are' <= arp' /\ arp' < 2 ^ 64⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_mode md -∗
     int_cell fb off_fileno fd -∗ pcell fb 8 (mkPtr arp' c') -∗ pcell fb 16 (mkPtr are' c') -∗
     pcell fb 32 (mkPtr awb' c') -∗ pcell fb 40 (mkPtr awp' c') -∗ live_cap c' breg' -∗
     pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     WP (ERun (mkFrame glibc__IO_flush_all e' [] None (Enter (TAtom "L182") (Some (TAtom "L257")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L240") (Some (TAtom "L211")))) : sexpr)
    {{ Φ }}.
Proof.
  intros fp Hp5 Hc13 Hc31 Hp4 Hv3 Hr Hfb Hfal Hfend Hfreg Hmd Hfd. subst fp.
  pose proof Hfend as Hfend'. unfold file_size in Hfend.
  iIntros "#Hvt Hl Hfl Hf2 Hmd Hfd Hrp Hre Hwb Hwp Hbc Hvtp HR HK".
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* L240, iw_1.join: the jump table's `c: __overflow`. *)
  iPoseProof (vtables_slot ge vb vreg slot_overflow "_IO_new_file_overflow" with "Hvt") as "#Hso"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_overflow")) vreg) as "Hcap".
  { rewrite (ge_fn_cap _ _ _ Hovf). done. }
  iPoseProof "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)". unfold io_vtables_size in Hvend.
  fs. fs. fchk "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". fs. fs. fs. fs. fs. fbrv true. fs. fs.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hvl'"); [reflexivity | vx | right; reflexivity | a2 | a2 | a2 |].
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hso Hcap");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hovf) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hovf) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hovf) | apply (ge_fn_check _ _ _ Hovf) | vx |
    apply (ge_fn_find _ _ _ Hovf) | reflexivity | reflexivity |].
  iNext.
  iAssert (live fb freg) with "[Hl]" as "Hl"; [rewrite /live pts_ptsq; iExact "Hl"|].
  iApply (Hov _ fb freg fl f2 fd md c breg arp are awb awp vb with "Hl Hfl Hf2 Hfd Hmd Hrp Hre Hwb Hwp Hbc Hvtp HR");
    [reflexivity | exact Hfb | exact Hfal | exact Hfend' | exact Hfreg |].
  iNext. iIntros (k fl' c' breg' arp' are' awb' awp' Hk) "Hl Hfl Hf2 Hfd Hmd Hrp Hre Hwb Hwp Hbc Hvtp". resume.
  destruct Hk as (Hk & Hfl' & Hfu' & Hmu' & Hw' & Hwb' & Hrd' & Hrp').
  (* iw_1.join, L241, L191: EOF or not. *)
  fs. fs. fs. rewrite (Z.mod_small k (2 ^ 32)); [|exact Hk].
  iAssert (live fb freg) with "[Hl]" as "Hl"; [rewrite /live pts_ptsq; iExact "Hl"|].
  destruct (Z.eq_dec k (2 ^ 32 - 1)) as [-> | Hk1].
  - br. iApply (wp_flush_L192 w0 registry ge _ (TAtom "L241") (2 ^ 32 - 1) with "Hl Hmd Hfd Hrp Hre Hbc");
      try first [lk_prove | right; split; reflexivity | lia | exact Hmd | exact Hfd | exact Hfal | exact Hfreg
                | unfold file_size; lia].
    iNext. iIntros (e' He') "Hl Hmd Hfd Hrp Hre Hbc".
    iApply ("HK" $! e' (2 ^ 32 - 1) fl' c' breg' arp' are' awb' awp' with "[%] Hl Hfl Hf2 Hmd Hfd Hrp Hre Hwb Hwp
              Hbc Hvtp").
    destruct He' as (? & ? & ? & ?). split_and!; auto; lia.
  - brv true. fs. iApply wp_goto. iNext.
    iApply (wp_flush_L192 w0 registry ge _ (TAtom "L191") r with "Hl Hmd Hfd Hrp Hre Hbc");
      try first [lk_prove | left; split; [reflexivity | lk_prove] | lia | exact Hmd | exact Hfd | exact Hfal
                | exact Hfreg | unfold file_size; lia].
    iNext. iIntros (e' He') "Hl Hmd Hfd Hrp Hre Hbc".
    iApply ("HK" $! e' r fl' c' breg' arp' are' awb' awp' with "[%] Hl Hfl Hf2 Hmd Hfd Hrp Hre Hwb Hwp Hbc Hvtp").
    destruct He' as (? & ? & ? & ?). split_and!; auto; lia.
Qed.


End rules.
End LibioFlushOverCallOn.
