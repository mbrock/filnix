(** One pass of `c: _IO_flush_all`'s loop (LibioFlushCode.v), from
    the loop's head `c: L83` to its next entry of `c: L82`, stated as
    a triple over two predicates on a stream ([flush_body]). The pass
    runs from P of the stream to Q of it, given the stream's life,
    the list's `c: run_fp` and the stream's `c: _chain`. LibioFlush.v
    runs the loop over every stream of `c: _IO_list_all` from any
    [flush_body].

    [exit_stream] is the state at exit of a narrow stream with
    nothing to flush, as an unused `c: stdin` or an unused
    `c: stderr` is after `c: close_stdout` has closed `c: stdout`.
    Its fields are those the two loops of `c: _IO_flush_all` and
    `c: _IO_unbuffer_all` read. [flush_body_exit] proves that a pass
    over such a stream calls nothing and changes nothing, by
    LibioFlushFpLock.v, LibioFlushClean.v and LibioFlushFpUnlock.v. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean
  LibioFlushStart LibioFlushTail LibioFlushInv.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioFlushBodyOn (R : Runtime) (LG0 : LogicSig R).
Module FT := LibioFlushTailOn R LG0.
Import FT FT.FS FT.FS.FC FT.FS.FC.FU FT.FS.FC.FU.FL FT.FS.FC.FU.FL.CS FT.FS.FC.FU.FL.CS.SW
  FT.FS.FC.FU.FL.CS.SW.FI.ML FT.FS.FC.FU.FL.CS.SW.FI.LG FT.FS.FC.FU.FL.CS.SW.FI.L FT.FS.FC.FU.FL.CS.SW.OW
  FT.FS.FC.FU.FL.CS.SW.FI FT.FS.FC.FU.FL.CS.SW.ST.

(** The stream predicates retain their public names and definitions
    without importing the flush proofs into clients that only need ownership. *)
Include LibioFlushInvOn R LG0.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance flush_body_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [flush_body] P Q: a pass of the loop over the stream fb, from
    `c: L83` with fb in `c: pr.5`, the result so far r in `c: pr.4`,
    the cleanup buffer in `c: v3` and the null address in `c: v88`,
    runs from P to Q: it enters the loop's head from `c: L329` with
    fb's `c: _chain` nx in `c: v413`, and in `c: pr.1` r or, after a
    failed flush, EOF. `c: run_fp` ends null, and the life of nx is
    lent for the load of the chain. *)
Definition flush_body (P Q : ptr -> iProp Σ) : Prop :=
  forall e fb freg rf rfreg sb sreg x r cb nx nreg Φ,
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "pr.5") e = Some (WPtr fp) -> lookup (TAtom "pr.4") e = Some (WInt r) ->
  lookup (TAtom "v3") e = Some (WPtr cb) -> lookup (TAtom "v88") e = Some (WInt 0) ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= r < 2 ^ 32 -> 0 <= ptr_addr nx < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  ⊢ single_ro ge sb sreg -∗ live fb freg -∗ P fp -∗ live rf rfreg -∗ pcell rf 0 x -∗
    pcell fb off_chain nx -∗ live_cap (ptr_cap nx) nreg -∗
    ▷ (∀ e' r', ⌜lookup (TAtom "v413") e' = Some (WPtr nx) /\ lookup (TAtom "pr.1") e' = Some (WInt r') /\
                 lookup (TAtom "v3") e' = Some (WPtr cb) /\ 0 <= r' < 2 ^ 32 /\ (r' = r \/ r' = 2 ^ 32 - 1)⌝ -∗
       live fb freg -∗ Q fp -∗ live rf rfreg -∗ pcell rf 0 null -∗ pcell fb off_chain nx -∗
       live_cap (ptr_cap nx) nreg -∗
       WP (ERun (mkFrame glibc__IO_flush_all e' [] None (Enter (TAtom "L82") (Some (TAtom "L329")))) : sexpr)
         {{ Φ }}) -∗
    WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L83") (Some (TAtom "L82")))) : sexpr)
      {{ Φ }}.

(** A pass over an [exit_stream] calls nothing and leaves the stream
    as it was, the result unchanged. *)
Lemma flush_body_exit : flush_body (exit_stream false) (exit_stream false).
Proof.
  intros e fb freg rf rfreg sb sreg x r cb nx nreg Φ fp Hgrf Hp5 Hp4 Hv3 Hv88 Hsz Hr Hnx Hfb Hfal Hfend Hfreg
    Hral Hrend.
  iIntros "#Hs Hl HP Hrl Hrc Hch Hnl HK".
  iDestruct "HP" as (fb' fl f2 fd md lb lbreg c breg arp are awb awp Hc)
    "(Hfl & Hf2 & Hfd & Hmd & Hlp & Hlb & Hrp & Hre & Hwb & Hwp & Hbc & H80)".
  destruct Hc as (Heq & Hfl & Hul & Hf2 & Hfd & Hw & Hwb & Hrd & Hrp & Hmd & Hub).
  injection Heq as <-.
  iApply (wp_flush_L83 w0 registry ge Hreg Hext with "Hs Hl Hfl Hlp Hlb Hrl Hrc"); try side.
  iNext. iIntros (e1 (H1p5 & H1c13 & H1p4 & H1v3)) "Hl Hfl Hlp Hlb Hrl Hrc".
  iApply (wp_flush_L94_clean w0 registry ge with "Hl Hf2 Hmd Hfd Hrp Hre Hwb Hwp Hbc"); try side.
  iNext. iIntros (e2 (H2p5 & H2c13 & H2p2 & H2v3)) "Hl Hf2 Hmd Hfd Hrp Hre Hwb Hwp Hbc".
  iApply (wp_flush_L182 w0 registry ge with "Hs Hl Hfl Hlp Hlb Hrl Hrc Hch Hnl"); try side.
  iNext. iIntros (e3 (H3v413 & H3p1 & H3v3)) "Hl Hfl Hlp Hlb Hrl Hrc Hch Hnl".
  iApply ("HK" $! e3 r with "[%] Hl [-Hrl Hrc Hch Hnl] Hrl Hrc Hch Hnl").
  - split_and!; try assumption; lia.
  - iExists fb, fl, f2, fd, md, lb, lbreg, c, breg. iExists arp, are, awb, awp. iFrame. iPureIntro.
    split_and!; auto; lia.
Qed.

End rules.
End LibioFlushBodyOn.
