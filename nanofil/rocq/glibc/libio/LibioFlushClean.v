(** The test in one pass of `c: _IO_flush_all`'s loop
    (LibioFlushCode.v), from block `c: L94` to block `c: L182`, for a
    narrow stream with nothing to flush. The pass would call
    `c: _IO_OVERFLOW (fp, EOF)` if `c: _IO_write_ptr` were above
    `c: _IO_write_base`, and `c: _IO_SYNC (fp)` if the stream had a
    descriptor and `c: _IO_read_ptr` were below `c: _IO_read_end`.
    Here neither holds, so it calls neither and keeps the result so
    far. That is the state of an unused `c: stdin` and of an unused
    `c: stderr` at exit.

    The four buffer pointers it reads share one capability c, null or
    a buffer object whose life [live_cap] gives, since loading a
    pointer needs the life of what it points to. The stream's
    `c: _flags2` lacks bit 32 (otherwise block `c: L94` skips the
    tests), its mode is narrow (0 or -1) and its descriptor is not
    negative. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry LibioFlushCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** A narrow mode, 0 or -1, is not above 0 as a signed `c: int`. *)
Lemma narrow_sle md :
  md = 0 \/ md = 2 ^ 32 - 1 ->
  (sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32) <=? sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32)) = true.
Proof. intros [-> | ->]; reflexivity. Qed.

(** The same, as the strict test the other way. *)
Lemma narrow_sgt md :
  md = 0 \/ md = 2 ^ 32 - 1 ->
  (sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32) <? sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32)) = false.
Proof. intros [-> | ->]; reflexivity. Qed.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioFlushCleanOn (R : Runtime) (LG0 : LogicSig R).
Module FU := LibioFlushFpUnlockOn R LG0.
Import FU FU.FL FU.FL.CS FU.FL.CS.SW FU.FL.CS.SW.FI.ML FU.FL.CS.SW.FI.LG FU.FL.CS.SW.FI.L FU.FL.CS.SW.OW
  FU.FL.CS.SW.FI FU.FL.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance flush_clean_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A branch on a mode test, decided by the equation E. *)
Ltac fbrm E :=
  eapply step_wand; [eapply wp_branch; inst; vx |]; rewrite E;
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := vm_of c in change c with c' end; cbn [edge_label].

(** Block `c: L192` of `c: _IO_flush_all` to block `c: L182`, for
    the stream fb in `c: pr.5` and `c: chk13`, entered from
    `c: L191` with the result so far in `c: pr.4` or from `c: L241`
    after a failed overflow with EOF: the stream has a descriptor, a
    narrow mode and a read pointer not below its read end, so
    `c: _IO_SYNC` is not called, and `c: L182` is entered from
    `c: L257` with that result r2 in `c: pr.2`. *)
Lemma wp_flush_L192 e from r2 fb freg md fd c breg arp are cb a31 Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "pr.5") e = Some (WPtr fp) -> lookup (TAtom "chk13") e = Some (WPtr fp) ->
  lookup (TAtom "chk31") e = Some (WPtr (mkPtr a31 (Obj fb))) -> lookup (TAtom "v3") e = Some (WPtr cb) ->
  (from = TAtom "L191" /\ lookup (TAtom "pr.4") e = Some (WInt r2)) \/ (from = TAtom "L241" /\ r2 = 2 ^ 32 - 1) ->
  0 <= r2 < 2 ^ 32 -> 0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  md = 0 \/ md = 2 ^ 32 - 1 -> fd < 2 ^ 31 -> 0 <= are <= arp -> arp < 2 ^ 64 ->
  live fb freg -∗ int_cell fb off_mode md -∗ int_cell fb off_fileno fd -∗
  pcell fb 8 (mkPtr arp c) -∗ pcell fb 16 (mkPtr are c) -∗ live_cap c breg -∗
  ▷ (∀ e', ⌜lookup (TAtom "pr.5") e' = Some (WPtr fp) /\ lookup (TAtom "chk13") e' = Some (WPtr fp) /\
            lookup (TAtom "pr.2") e' = Some (WInt r2) /\ lookup (TAtom "v3") e' = Some (WPtr cb)⌝ -∗
     live fb freg -∗ int_cell fb off_mode md -∗ int_cell fb off_fileno fd -∗
     pcell fb 8 (mkPtr arp c) -∗ pcell fb 16 (mkPtr are c) -∗ live_cap c breg -∗
     WP (ERun (mkFrame glibc__IO_flush_all e' [] None (Enter (TAtom "L182") (Some (TAtom "L257")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L192") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hp5 Hc13 Hc31 Hv3 Hph Hr Hfb Hfal Hfend Hfreg Hmd Hfd Hrd Hrp. subst fp.
  unfold file_size in Hfend.
  iIntros "Hl [%Hmdr Hmd] [%Hfdr Hfd] Hrp Hre Hbc HK".
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* L192, L263, L269, L270: a descriptor, narrow, and the read pointer not below the end. *)
  destruct Hph as [(-> & Hp4) | (-> & ->)]; fs.
  all: fs; fchk "Hl"; fldi "Hl" "Hfd"; fs; fbrv false.
  all: fs; fs; fchk "Hl"; fldi "Hl" "Hmd"; fs; fbrm (narrow_sle md Hmd).
  all: fs; fs; fchk "Hl"; fldp "Hl" "Hrp" "Hbc"; fs; fldp "Hl" "Hre" "Hbc"; fs; fs; fs; fs; fs; fbrv true.
  (* L285, L264, L314, L257: not wide, so no sync. *)
  all: fs; fs; fldi "Hl" "Hmd"; fs; fbrm (narrow_sgt md Hmd); fs; fbr; fs; fbr; fs; iApply wp_goto; iNext.
  all: iAssert (live fb freg) with "[Hl]" as "Hl"; [rewrite /live pts_ptsq; iExact "Hl"|].
  all: iApply ("HK" with "[%] Hl [Hmd] [Hfd] Hrp Hre Hbc");
    [split_and!; try lk_prove; try (rewrite (Z.mod_small r2 (2 ^ 32)); [lk_prove | exact Hr]) | iSplit; [done | iExact "Hmd"]
                                                        | iSplit; [done | iExact "Hfd"]].
Qed.

(** Block `c: L94` of `c: _IO_flush_all` to block `c: L182` for the
    stream fb in `c: pr.5` and `c: chk13`, whose write pointer is not
    above its write base and whose read pointer is not below its read
    end: nothing is called, and `c: L182` is entered from `c: L257`
    with the result so far, r in `c: pr.4`, in `c: pr.2`. *)
Lemma wp_flush_L94_clean e from fb freg f2 md fd c breg arp are awb awp r cb Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "pr.5") e = Some (WPtr fp) -> lookup (TAtom "chk13") e = Some (WPtr fp) ->
  lookup (TAtom "pr.4") e = Some (WInt r) -> lookup (TAtom "v3") e = Some (WPtr cb) -> 0 <= r < 2 ^ 32 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 32 = 0 -> md = 0 \/ md = 2 ^ 32 - 1 -> fd < 2 ^ 31 ->
  0 <= awp <= awb -> awb < 2 ^ 64 -> 0 <= are <= arp -> arp < 2 ^ 64 ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_mode md -∗ int_cell fb off_fileno fd -∗
  pcell fb 8 (mkPtr arp c) -∗ pcell fb 16 (mkPtr are c) -∗ pcell fb 32 (mkPtr awb c) -∗
  pcell fb 40 (mkPtr awp c) -∗ live_cap c breg -∗
  ▷ (∀ e', ⌜lookup (TAtom "pr.5") e' = Some (WPtr fp) /\ lookup (TAtom "chk13") e' = Some (WPtr fp) /\
            lookup (TAtom "pr.2") e' = Some (WInt r) /\ lookup (TAtom "v3") e' = Some (WPtr cb)⌝ -∗
     live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_mode md -∗ int_cell fb off_fileno fd -∗
     pcell fb 8 (mkPtr arp c) -∗ pcell fb 16 (mkPtr are c) -∗ pcell fb 32 (mkPtr awb c) -∗
     pcell fb 40 (mkPtr awp c) -∗ live_cap c breg -∗
     WP (ERun (mkFrame glibc__IO_flush_all e' [] None (Enter (TAtom "L182") (Some (TAtom "L257")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L94") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hp5 Hc13 Hp4 Hv3 Hr Hfb Hfal Hfend Hfreg Hf2 Hmd Hfd Hw Hwb Hrd Hrp. subst fp.
  unfold file_size in Hfend.
  iIntros "Hl [%Hf2r Hf2] [%Hmdr Hmd] [%Hfdr Hfd] Hrp Hre Hwb Hwp Hbc HK".
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* L94: `c: _flags2` lacks bit 32. *)
  fs. fs. fchk "Hl". fldi "Hl" "Hf2". fs. fs. fs. fs.
  rewrite (flags2_mask f2 32 5); [|reflexivity | lia | exact Hf2r]. rewrite Hf2. fbr.
  (* L180, L197, L198: narrow, and the write pointer not above the base. *)
  fs. fs. fchk "Hl". fldi "Hl" "Hmd". fs. fbrm (narrow_sle md Hmd).
  fs. fs. fchk "Hl". fldp "Hl" "Hwp" "Hbc". fs. fchk "Hl". fldp "Hl" "Hwb" "Hbc". fs. fs. fs. fs. fs. fbrv true.
  (* L213, L211, L241, L191: not wide, so no overflow. *)
  fs. fs. fldi "Hl" "Hmd". fs. fbrm (narrow_sgt md Hmd). fs. fbr. fs. fbr. fs. iApply wp_goto. iNext.
  (* L192 to L182: no sync. *)
  iAssert (live fb freg) with "[Hl]" as "Hl"; [rewrite /live pts_ptsq; iExact "Hl"|].
  iApply (wp_flush_L192 _ (TAtom "L191") r with "Hl [Hmd] [Hfd] Hrp Hre Hbc");
    [lk_prove | lk_prove | lk_prove | lk_prove | left; split; [reflexivity | lk_prove] | exact Hr | lia | exact Hfal
    | unfold file_size; lia | exact Hfreg | exact Hmd | exact Hfd | lia | exact Hrp
    | iSplit; [done | iExact "Hmd"] | iSplit; [done | iExact "Hfd"] |].
  iNext. iIntros (e' He') "Hl Hmd Hfd Hrp Hre Hbc".
  iApply ("HK" $! e' He' with "Hl [Hf2] Hmd Hfd Hrp Hre Hwb Hwp Hbc"). iSplit; [done | iExact "Hf2"].
Qed.

End rules.
End LibioFlushCleanOn.
