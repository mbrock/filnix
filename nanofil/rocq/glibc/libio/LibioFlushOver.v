(** This file proves a pass of `c: _IO_flush_all`'s loop
    (LibioFlushCode.v) over a narrow stream that still buffers output,
    whose `c: _IO_write_ptr` is above its `c: _IO_write_base`. The pass takes the stream's lock
    (LibioFlushFpLock.v) and finds the write pointer above the base.
    It then calls `c: _IO_new_file_overflow (fp, EOF)` through the
    stream's jump table, which writes the buffer out
    (LibioFlushOverCall.v). The result becomes EOF if that call
    returns EOF. Afterwards the read pointer is not below the read
    end, so `c: _IO_SYNC` is not called, and the pass releases the
    lock (LibioFlushFpUnlock.v).

    `c: _IO_new_file_overflow` is a premise (LibioFlushOverCall.v's
    [overflow_spec]): a triple over the cells the pass reads and a
    resource Rest of the caller's choosing, such as the buffer and
    the descriptor's world. [flush_body_over] is the pass from
    [over_stream] to [exit_stream], and [flush_body_or] joins it with
    [flush_body_exit] for a list holding both kinds of stream. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean
  LibioFlushStart LibioFlushTail LibioFlushBody LibioFlushOverCall.
From Glibc Require FileInv LibioCloseSteps LibioFlushBody LibioFlushClean LibioFlushFpLock LibioFlushFpUnlock LibioFlushOverCall LibioFlushStart LibioFlushTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioFlushOverCall LibioFlushBody LibioFlushTail LibioFlushStart LibioFlushClean LibioFlushFpUnlock LibioFlushFpLock SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hovf : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance flush_over_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A branch on a mode test, decided by the equation E, as in
    LibioFlushClean.v. *)


(** [over_stream] Rest g: the narrow stream g with output to flush.
    It is as an [exit_stream] not yet unbuffered, except that the
    write pointer is above the write base; its jump table is the
    narrow file table of [vtables_ro], and Rest is what
    `c: _IO_new_file_overflow` needs besides. *)
Definition over_stream (Rest : Z -> iProp Σ) (g : ptr) : iProp Σ :=
  ∃ fb fl f2 fd md lb lbreg c breg arp are awb awp vb vreg,
    ⌜g = mkPtr fb (Obj fb) /\ 0 <= fl < 2 ^ 32 /\ Z.land fl 32768 = 0 /\ Z.land f2 32 = 0 /\ fd < 2 ^ 31 /\
     0 <= awb < awp /\ awp < 2 ^ 64 /\ 0 <= are <= arp /\ arp < 2 ^ 64 /\ (md = 0 \/ md = 2 ^ 32 - 1)⌝ ∗
    int_cell fb off_flags fl ∗ int_cell fb off_flags2 f2 ∗ int_cell fb off_fileno fd ∗ int_cell fb off_mode md ∗
    pcell fb off_lock (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
    pcell fb 8 (mkPtr arp c) ∗ pcell fb 16 (mkPtr are c) ∗ pcell fb 32 (mkPtr awb c) ∗
    pcell fb 40 (mkPtr awp c) ∗ live_cap c breg ∗ pcell fb 80 null ∗
    pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗ vtables_ro ge vb vreg ∗ Rest fb.

(** [overflow_spec] Rest holds. *)
Context (Rest : Z -> iProp Σ) (Hov : overflow_spec w0 registry ge Rest).

(** Block `c: L94` of `c: _IO_flush_all` to block `c: L182` for the
    stream fb in `c: pr.5` and `c: chk13`, whose write pointer is
    above its write base: `c: _IO_new_file_overflow (fp, EOF)` is
    called through the jump table, and `c: L182` is entered from
    `c: L257` with the result so far r, or EOF if the call returned
    EOF, in `c: pr.2`. *)
Lemma wp_flush_L94_over e from fb freg fl f2 fd md c breg arp are awb awp vb vreg r cb Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "pr.5") e = Some (WPtr fp) -> lookup (TAtom "chk13") e = Some (WPtr fp) ->
  lookup (TAtom "pr.4") e = Some (WInt r) -> lookup (TAtom "v3") e = Some (WPtr cb) -> 0 <= r < 2 ^ 32 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 32 = 0 -> md = 0 \/ md = 2 ^ 32 - 1 -> fd < 2 ^ 31 -> 0 <= awb < awp -> awp < 2 ^ 64 ->
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
  WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L94") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hp5 Hc13 Hp4 Hv3 Hr Hfb Hfal Hfend Hfreg Hf2 Hmd Hfd Hw Hwp. subst fp.
  pose proof Hfend as Hfend'. unfold file_size in Hfend.
  iIntros "#Hvt Hl Hfl [%Hf2r Hf2] [%Hmdr Hmd] Hfd Hrp Hre Hwb Hwp Hbc Hvtp HR HK".
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* L94: `c: _flags2` lacks bit 32. *)
  step. step. check "Hl". load_s32 "Hl" "Hf2". step. step. step. step.
  rewrite (flags2_mask f2 32 5); [|reflexivity | lia | exact Hf2r]. rewrite Hf2. branch.
  (* L180, L197, L198, L211: narrow, and the write pointer above the base. *)
  step. step. check "Hl". load_s32 "Hl" "Hmd". step. branch_rewrite (narrow_sle md Hmd).
  step. step. check "Hl". load "Hl" "Hwp" "Hbc". step. check "Hl". load "Hl" "Hwb" "Hbc". step. step. step. step. step. branch_as false.
  step. branch.
  (* L240 to L182: the call. *)
  iAssert (live fb freg) with "[Hl]" as "Hl"; [rewrite /live pts_ptsq; iExact "Hl"|].
  iApply (wp_flush_L240 w0 registry ge Hovf Rest Hov _ fb freg fl f2 fd md c breg arp are awb awp vb vreg r cb
            with "Hvt Hl Hfl [Hf2] [Hmd] Hfd Hrp Hre Hwb Hwp Hbc Hvtp HR");
    try first [lk_prove | exact Hr | exact Hfb | exact Hfal | exact Hfend' | exact Hfreg | exact Hmd | exact Hfd
              | iSplit; [done | first [iExact "Hf2" | rewrite /bytes pts_ptsq; iExact "Hf2"]]
              | iSplit; [done | first [iExact "Hmd" | rewrite /bytes pts_ptsq; iExact "Hmd"]]].
  iExact "HK".
Qed.

(** A pass over an [over_stream] writes its buffer out and leaves an
    [exit_stream] not yet unbuffered, the result r or EOF. *)
Lemma flush_body_over : flush_body w0 registry ge (over_stream Rest) (exit_stream false).
Proof.
  intros e fb freg rf rfreg sb sreg x r cb nx nreg Φ fp Hgrf Hp5 Hp4 Hv3 Hv88 Hsz Hr Hnx Hfb Hfal Hfend Hfreg
    Hral Hrend.
  iIntros "#Hs Hl HP Hrl Hrc Hch Hnl HK".
  iDestruct "HP" as (fb' fl f2 fd md lb lbreg c breg arp are awb awp vb vreg Hc)
    "(Hfl & Hf2 & Hfd & Hmd & Hlp & Hlb & Hrp & Hre & Hwb & Hwp & Hbc & H80 & Hvtp & #Hvt & HR)".
  destruct Hc as (Heq & Hfl & Hul & Hf2 & Hfd & Hw & Hwp' & Hrd & Hrp & Hmd). injection Heq as <-.
  iApply (wp_flush_L83 w0 registry ge Hreg Hext with "Hs Hl Hfl Hlp Hlb Hrl Hrc"); try close_side.
  iNext. iIntros (e1 (H1p5 & H1c13 & H1p4 & H1v3)) "Hl Hfl Hlp Hlb Hrl Hrc".
  iApply (wp_flush_L94_over with "Hvt Hl Hfl Hf2 Hmd Hfd Hrp Hre Hwb Hwp Hbc Hvtp HR"); try close_side.
  iNext. iIntros (e2 r2 fl' c' breg' arp' are' awb' awp' Hc2) "Hl Hfl Hf2 Hmd Hfd Hrp Hre Hwb Hwp Hbc Hvtp".
  destruct Hc2 as (H2p5 & H2c13 & H2p2 & H2v3 & Hr2 & Hrr2 & Hfl' & Hfu' & Hmu' & Hw' & Hwb' & Hrd' & Hrp').
  iApply (wp_flush_L182 w0 registry ge with "Hs Hl Hfl Hlp Hlb Hrl Hrc Hch Hnl"); try close_side.
  iNext. iIntros (e3 (H3v413 & H3p1 & H3v3)) "Hl Hfl Hlp Hlb Hrl Hrc Hch Hnl".
  iApply ("HK" $! e3 r2 with "[%] Hl [-Hrl Hrc Hch Hnl] Hrl Hrc Hch Hnl").
  - split_and!; try assumption; lia.
  - iExists fb, fl', f2, fd, md, lb, lbreg, c', breg'. iExists arp', are', awb', awp'. iFrame. iPureIntro.
    split_and!; auto; lia.
Qed.

End rules.

Section join.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Passes from P1 and from P2 to Q are a pass from either to Q, so
    one list can hold streams of both kinds. *)
Lemma flush_body_or (P1 P2 Q : ptr -> iProp Σ) :
  flush_body w0 registry ge P1 Q -> flush_body w0 registry ge P2 Q ->
  flush_body w0 registry ge (fun g => P1 g ∨ P2 g)%I Q.
Proof.
  intros H1 H2 e fb freg rf rfreg sb sreg x r cb nx nreg Φ fp ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
  iIntros "Hs Hl [HP | HP]".
  - iApply (H1 with "Hs Hl HP"); assumption.
  - iApply (H2 with "Hs Hl HP"); assumption.
Qed.

End join.
