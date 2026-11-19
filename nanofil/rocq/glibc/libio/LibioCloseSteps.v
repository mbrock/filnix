From Glibc Require Import GlibcProgram.
(** What the proofs of the close, flush and exit path share
    (LibioUnlink.v to ExitRun.v): checks at a share of an object's
    life, as the read-only jump tables and `c: __libc_single_threaded`
    are owned (LibioLogic.v's [wp_check_read_dq]); the bounds every live object has
    ([wp_live_fit]); a stream's life, opened from FileInv.v's
    [file_inv] and closed again ([file_inv_live]); the cleanup buffer
    a fresh allocation holds ([obj32]); and the step tactics.

    Each is stated over the [os_world] of [OsWorld](../zsys/OsWorld.v),
    as the triples of SysWrappers.v are. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry  FileInv LibioLogic .
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## Rule application

    As stdlib/LeavesLogic.v does: a step rule applied as a plain
    entailment, not by [iApply] and [iNext], whose proof-mode searches
    cost most of a step. *)

(** Apply a step rule ⊢ ▷ P -∗ Q to the goal Q, leaving P. *)


(** Apply a step rule R -∗ ▷ (R' -∗ P) -∗ Q, over one resource, to
    the goal R -∗ Q, leaving R' -∗ P. *)


(** [step_res1] over two resources. *)


(** [step_res1] over three resources. *)


(** Apply a rule over the resource H by the tactic t. *)


(** Apply a rule over the resources H1 and H2 by the tactic t. *)


(** Apply a rule over the resources H1, H2 and H3 by the tactic t. *)


(** Drop each wrap to 64 or 32 bits of the goal that arithmetic shows
    the identity, as LibioLogic.v's [unwrap], without clearing
    hypotheses first. *)



Import  Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section streams.
Context `{!gen_heapGS piece pval Σ}.

(** A stream's life, from its [file_inv], and the stream back from it:
    the stream is the 224-byte object gb, 8-aligned. *)
Lemma file_inv_live vb self g :
  file_inv vb self g ⊢
  ∃ gb greg, ⌜g = mkPtr gb (Obj gb) /\ 0 < gb /\ gb mod 8 = 0 /\ gb + file_size <= r_end greg /\
              r_end greg <= 2 ^ 63⌝ ∗ live gb greg ∗ (live gb greg -∗ file_inv vb self g).
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %vt & %held & %Hp & Hl & Hrest)".
  destruct Hp as (-> & Hal & Hfb & Hend & Hreg & Hp).
  iExists fb, freg. iFrame "Hl". iSplit; [iPureIntro; repeat split; assumption|]. iIntros "Hl".
  iExists fb, freg, st, nb, vt, held. iFrame. iPureIntro. exact (conj eq_refl (conj Hal (conj Hfb (conj Hend (conj Hreg Hp))))).
Qed.

(** Eight zero bytes and an empty slot are a null pointer's cell. *)
Lemma byte_ps_cell0 b o : byte_ps b o (replicate 8 0) = cell b o 0.
Proof using Type*. unfold byte_ps, cell, seqZ. rewrite Nat2Z.id. simpl. repeat (f_equal; try lia; try reflexivity). Qed.

(** A null pointer's cell, from an empty slot and eight zero bytes. *)
Lemma pcell_null_of b o : auxes b o [CNone] ∗ bytes b o (replicate 8 0) ⊢ pcell b o null.
Proof using Type.
  rewrite /bytes byte_ps_cell0 /auxes /pcell /aux_ps /pts. cbn -[cell]. unfold seqZ. simpl. rewrite ?Z.add_0_l.
  iIntros "[[$ _] $]".
Qed.

(** A fresh 32-byte heap object, as libio's
    `c: _IO_cleanup_region_start_noarg` allocates its
    `c: struct _pthread_cleanup_buffer`: its life, the null pointers
    at 0 (`c: __routine`), 8 (`c: __arg`) and 24 (`c: __prev`), and
    the four zero bytes of `c: __canceltype` at 16. *)
Lemma obj32 b : obj b (heap_req 8 32) ⊢
  live b (mkRegion b (b + 32) Heap Live) ∗ pcell b 0 null ∗ pcell b 8 null ∗ bytes b 16 [0; 0; 0; 0] ∗
  pcell b 24 null.
Proof using Type.
  rewrite obj_zero_block; [|vm_compute; congruence]. cbn [req_extent req_kind heap_req].
  replace ((32 + 15) / 16 * 16) with 32 by reflexivity.
  change (replicate (Z.to_nat 32) 0) with
    (replicate 8 0 ++ replicate 8 0 ++ ([0; 0; 0; 0] ++ [0; 0; 0; 0]) ++ replicate 8 0)%list.
  change (replicate (Z.to_nat 32) CNone) with
    ([CNone] ++ replicate 7 CNone ++ [CNone] ++ replicate 7 CNone ++ replicate 8 CNone ++ [CNone] ++
     replicate 7 CNone)%list.
  rewrite !bytes_app !auxes_app. cbn [length replicate].
  iIntros "($ & (H0 & H8 & (H16 & _) & H24) & (A0 & _ & A8 & _ & _ & A24 & _))".
  iSplitL "H0 A0"; [iApply pcell_null_of; iFrame|].
  iSplitL "H8 A8"; [iApply pcell_null_of; iFrame|].
  iSplitL "H16"; [iFrame|]. iApply pcell_null_of. iFrame.
Qed.

End streams.

(** ## Step tactics *)

(** A signed 32-bit load of an [int_cell]'s bytes, its life and bytes
    in H. *)


(** A one-byte load, its life and byte in H, at any shares. *)


(** A 32-bit store over the four bytes in H. *)


(** A pointer load, the base's life, the cell and the loaded
    capability's life in H. *)


(** A pointer store, the base's life and the cell in H. *)


(** A read check at a share of the object's life H. *)


(** [ldb] and [chkq] of persistent shares, handed back to the
    persistent context. *)



(** Close the instance premise a rule's eapply leaves. *)


(** An address fact about FileInv.v's offsets, by arithmetic, as
    LibioLogic.v's [ar] without clearing hypotheses. *)


(** One step whose premises reduce, applied as an entailment: a pure
    let, a flight, entering a block, or a goto. *)


(** The normal form of x by the virtual machine. *)
Local Ltac vm_of x := eval vm_compute in x.

(** A branch on a closed condition, computed. *)


(** A branch whose condition is b, by [decide_ints]. *)


(** A check, half check or renew, over the object's life H. *)


(** A signed 32-bit load of an [int_cell]'s bytes Hb, the life Hl. *)


(** A 32-bit store over the four bytes Hb, the life Hl. *)


(** A pointer load: the base's life Hl, the cell Hc and the loaded
    capability's life Hk. *)


(** A load of a null pointer: the base's life Hl and the cell Hc. *)


(** A 64-bit store over the [icell] Hc, the life Hl. *)


(** A pointer store: the base's life Hl and the cell Hc. *)


(** A side premise of a block lemma: a hypothesis, a lookup through
    the environment's [put]s, or arithmetic. *)
Ltac close_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- call_frame _ _ = _ => reflexivity
  | |- lookup _ _ = _ => lk_prove
  | |- _ => first [assumption | unfold file_size; lia | Z.div_mod_to_equations; lia | a2]
  end.

(** The rest of a caller after a callee's triple: resume it. *)
Ltac resume := iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].

