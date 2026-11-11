(** What the libio proofs share (SysWrappers.v, LibioRead.v): a store
    keeps OsWorld.v's [os_wi] when it writes back only the life token
    the program owned ([os_wi_store_life]), the lists of pieces that
    hold no life token ([no_life]), and the tactics that keep a
    symbolic run's addresses small.

    A store rule of Logic.v or MemLogic.v asks that the store keep the
    world interpretation, given that the old pieces, the object's life
    token first, are in the ghost heap: [os_wi_store] gives it when
    every life token written is the one the heap holds, and the new
    pieces of a store are the same life token and pieces with none
    ([wi_store]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From iris.program_logic Require Import language weakestpre.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Pieces Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld FileInv.
Import ListNotations.
Open Scope Z_scope.

(** ## Pieces with no life token *)

(** No piece of ps is a life token. *)
Definition no_life (ps : list (piece * pval)) : Prop :=
  forall l v, (l, v) ∈ ps -> match l with PLive _ => False | _ => True end.

(** A long's cell has none. *)
Lemma no_life_cell b o x : no_life (cell b o x).
Proof.
  intros l v Hin. unfold cell in Hin. cbn in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]; [injection Hin as -> _; exact I|]).
  by apply not_elem_of_nil in Hin.
Qed.

(** Bytes have none. *)
Lemma no_life_byte_ps b o xs : no_life (byte_ps b o xs).
Proof. intros l v Hin. apply byte_ps_elem in Hin as (i & x & _ & -> & _). exact I. Qed.

(** A pointer's cell, its aux slot and its bytes, has none. *)
Lemma no_life_pcell b o c a : no_life ((PAux b o, VAux c) :: cell b o a).
Proof.
  intros l v Hin. apply elem_of_cons in Hin as [[= -> _] | Hin]; [exact I|]. exact (no_life_cell _ _ _ _ _ Hin).
Qed.

(** One byte has none. *)
Lemma no_life_byte b o x : no_life [(PByte b o, VByte x)].
Proof. intros l v Hin. apply list_elem_of_singleton in Hin. injection Hin as -> _. exact I. Qed.

(** A store into the object b that keeps every region, whose new
    pieces are b's life token, as owned, and pieces with no life
    token, keeps [os_wi]. *)
Lemma os_wi_store_life w0 b reg ps ps' m m' wd h :
  m_regions m' = m_regions m -> no_life ps' ->
  (forall l v, (l, v) ∈ (PLive b, VLive reg) :: ps -> h !! l = Some v) -> os_wi w0 m wd h ->
  os_wi w0 m' wd (overwrite ((PLive b, VLive reg) :: ps') h).
Proof.
  intros Er Hn Hh Hw. apply (os_wi_store w0 m m' wd h); [exact Er | | exact Hw].
  intros l v Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin].
  - apply Hh. left.
  - pose proof (Hn l v Hin) as H. destruct l; [contradiction | exact I | exact I | exact I].
Qed.

(** The premise of a store rule over [os_wi]: by [os_wi_store_life]. *)
Ltac wi_store :=
  let Hh := fresh "Hh" in let Hw := fresh "Hw" in
  intros ? ? ? Hh Hw; eapply os_wi_store_life; [reflexivity | | exact Hh | exact Hw];
  first [apply no_life_cell | apply no_life_byte_ps | apply no_life_pcell | apply no_life_byte].

(** ## Arithmetic *)

(** Keep only arithmetic hypotheses, so lia does not read the rest. *)
Ltac clear_junk :=
  repeat match goal with
    H : ?T |- _ =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | and (Z.le _ _) _ => fail
      | and (Z.lt _ _) _ => fail | not (@eq Z _ _) => fail
      | _ => clear H
      end
    end.

(** Drop each wrap to 64 or 32 bits of the goal that arithmetic shows
    the identity. *)
Ltac unwrap :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)); [|clear_junk; lia]
    | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616); [|clear_junk; lia]
    | |- context [?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)); [|clear_junk; lia]
    | |- context [?x mod 4294967296] => rewrite (Z.mod_small x 4294967296); [|clear_junk; lia]
    end.

(** An address or integer fact, by arithmetic. *)
Ltac arith := cbn [ptr_addr ptr_cap]; unfold raw_address; unwrap; clear_junk;
  first [lia | Z.div_mod_to_equations; lia].

(** An address fact about FileInv.v's offsets, by arithmetic. *)
Ltac ar := unfold off_cleanup, off_cleanup_jmp, off_cancelhandling, off_lk_lock, off_lk_cnt, off_lk_owner,
  off_flags, off_read_ptr, off_write_base, off_write_ptr, off_write_end, off_buf_base, off_buf_end,
  off_chain, off_fileno, off_flags2, off_lock, off_wide, off_prevchain, off_mode, off_vtable, off_ptr; arith.

(** Write each address of the goal's environment without wraps. *)
Ltac norm := cbn [ptr_addr ptr_cap]; unwrap.

(** The term X has a variable in it. *)
Ltac has_var X := match X with context [?v] => is_var v end.

(** Compute each closed integer of the goal's words: a value glibc
    computes from constants, such as a flag test of a field known to
    be 0, becomes its numeral. *)
Ltac closed_ints :=
  repeat match goal with
    |- context [WInt ?X] =>
      tryif has_var X then fail else
      let v := eval vm_compute in X in tryif constr_eq X v then fail else change X with v
    end.

(** ## Steps over a Logic instance *)

(** The step tactics over the [[runtime]] R and [LogicSig] LG0: each
    takes one instruction of a run whose values are symbolic, by its
    rule from Logic.v, every premise computed or shown by arithmetic. *)
Module LibioStepOn (R : Runtime) (LG0 : LogicSig R).
Import LG0.

(** Enter the start block of a frame. *)
Ltac enter := iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]].

(** A check, its bounds by arithmetic, with the object's life H. *)
Ltac chk H :=
  first [ iApply (wp_check with H); [reflexivity | reflexivity | reflexivity | ar | ar | ar |]
        | iApply (wp_half_check with H);
            [reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | lia | ar | ar |]
        | iApply (wp_renew with H); [reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | ar |] ];
  iNext; iIntros H.

(** A branch on a closed condition: computed. *)
Ltac br :=
  iApply wp_branch; [reflexivity | iNext];
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** One step whose premises reduce: a pure let, a flight, entering a
    block, or a goto. The values stay symbolic. *)
Ltac st :=
  first
    [ iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; cbn; reflexivity | iNext]
    | iApply wp_flight; [reflexivity | reflexivity | reflexivity | iNext]
    | iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]
    | iApply wp_goto; iNext ].

End LibioStepOn.
