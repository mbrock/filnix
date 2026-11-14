(** Host preparation changes a finite set of fields after registering
    its fresh thread object. This file states that footprint explicitly
    and proves that bytes and capabilities outside it are preserved.
    The statement concerns this modeled preparation, not the footprint
    of all real libc startup routines. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Values Memory Runtime Run Pieces.
From Glibc Require Import HiAtexitPrepare.
Open Scope Z_scope.

(** Preparation leaves an address untouched when it lies outside the
    single-thread flag, cancellation field and listed pointer fields. *)
Definition hi_entry_untouched tb jb a : Prop :=
  ~ (73808 <= a < 73809) /\ ~ (tb + 792 <= a < tb + 796) /\
  Forall (fun ap => ~ (ap.1 <= a < ap.1 + 8)) (hi_entry_ptrs tb jb).

(** A bounded byte store leaves every address outside its span alone. *)
Lemma hi_bytes_outside m a n x p : ~ (a <= p < a + n) ->
  m_bytes (store_bytes m a n x) p = m_bytes m p.
Proof.
  intros H. unfold store_bytes. cbn.
  destruct ((a <=? p) && (p <? a + n)) eqn:E; [|reflexivity].
  apply Bool.andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.

(** A pointer store changes only its eight bytes and its capability
    at the first byte of that span. *)
Lemma hi_host_ptr_outside m ap p : ~ (ap.1 <= p < ap.1 + 8) ->
  m_bytes (hi_host_ptr m ap) p = m_bytes m p /\
  m_aux (hi_host_ptr m ap) p = m_aux m p.
Proof.
  intros H. unfold hi_host_ptr, store_aux. cbn [m_bytes m_aux]. split.
  - apply hi_bytes_outside. exact H.
  - assert (E : (p =? ap.1) = false) by (apply Z.eqb_neq; lia).
    rewrite E. reflexivity.
Qed.

(** The finite pointer-store sequence preserves an address outside
    every one of its fields. *)
Lemma hi_host_ptrs_outside aps m p :
  Forall (fun ap => ~ (ap.1 <= p < ap.1 + 8)) aps ->
  m_bytes (fold_left hi_host_ptr aps m) p = m_bytes m p /\
  m_aux (fold_left hi_host_ptr aps m) p = m_aux m p.
Proof.
  revert m. induction aps as [|ap aps IH]; intros m H; [split; reflexivity|].
  inversion H as [|? ? Hhead Htail]; subst. cbn [fold_left].
  destruct (IH (hi_host_ptr m ap) Htail) as [Hb Ha].
  rewrite Hb, Ha. apply hi_host_ptr_outside. exact Hhead.
Qed.

(** The complete preparation preserves unrelated bytes and shadow
    capabilities. Region registration is specified separately. *)
Lemma hi_entry_writes_preserve m tb jb a : hi_entry_untouched tb jb a ->
  m_bytes (hi_entry_writes m tb jb) a = m_bytes m a /\
  m_aux (hi_entry_writes m tb jb) a = m_aux m a.
Proof.
  intros (Hflag & Hcancel & Hptr). unfold hi_entry_writes.
  destruct (hi_host_ptrs_outside _
    (store_bytes (store_bytes m 73808 1 1) (tb + 792) 4 0) _ Hptr) as [Hb Ha].
  rewrite Hb, Ha. split; [|reflexivity].
  rewrite hi_bytes_outside by (replace (tb + 792 + 4) with (tb + 796) by lia; exact Hcancel).
  apply hi_bytes_outside. exact Hflag.
Qed.
