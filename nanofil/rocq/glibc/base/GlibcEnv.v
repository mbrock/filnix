(** A glibc block often changes temporary variables while its caller still
    needs other variables. This file describes which lookups survive the
    block, independently of its memory resources or [[separation-logic]]
    instance. Shared lemmas let block proofs introduce this condition and
    callers recover the lookup of any listed name. *)

From iris.proofmode Require Import proofmode.
From stdpp Require Import list.
From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Values Semantics Symbolic.
Import ListNotations.

(** The list names the variables whose lookups the block preserves. *)
Definition atoms (ss : list string) : list name := List.map TAtom ss.

(** The final environment answers every listed name as the initial environment does. *)
Definition keeps (ks : list name) (e e' : env) : Prop :=
  Forall (fun k => lookup k e' = lookup k e) ks.

(** A block may assign names in W without changing any name in ks. *)
Definition avoids (ks W : list name) : bool :=
  forallb (fun k => forallb (fun w => negb (name_eqb k w)) W) ks.

(** Every environment preserves its own lookups. *)
Lemma keeps_refl ks e : keeps ks e e.
Proof. apply Forall_forall. reflexivity. Qed.

(** Assigning a name outside the list preserves every listed lookup. *)
Lemma keeps_put ks k v e e' :
  forallb (fun k' => negb (name_eqb k' k)) ks = true -> keeps ks e e' -> keeps ks e (put k v e').
Proof.
  intros Hks Hk. apply Forall_forall. intros x Hx.
  rewrite (Symbolic.lookup_after_put_other _ x k v e'); [exact (proj1 (Forall_forall _ _) Hk x Hx)|].
  apply forallb_forall with (x := x) in Hks; [|exact Hx]. by destruct (name_eqb x k).
Qed.

(** Two successive blocks preserve the names that both blocks keep. *)
Lemma keeps_trans ks e e1 e2 : keeps ks e e1 -> keeps ks e1 e2 -> keeps ks e e2.
Proof.
  unfold keeps. rewrite !Forall_forall. intros H1 H2 k Hk. rewrite H2; [|done]. by apply H1.
Qed.

(** Assigning a name from an avoided write set preserves every listed lookup. *)
Lemma keeps_put_avoid ks W k v e e' :
  existsb (name_eqb k) W = true -> avoids ks W = true -> keeps ks e e' -> keeps ks e (put k v e').
Proof.
  intros Hk Ha. apply keeps_put. apply forallb_forall. intros k' Hk'.
  apply existsb_exists in Hk as (w & Hw & Ekw). apply term_eqb_eq in Ekw. subst w.
  unfold avoids in Ha. rewrite forallb_forall in Ha. specialize (Ha k' Hk').
  rewrite forallb_forall in Ha. by apply Ha.
Qed.

(** A caller may separate the preserved names into two lists. *)
Lemma keeps_app ks1 ks2 e e' : keeps (ks1 ++ ks2) e e' -> keeps ks1 e e' /\ keeps ks2 e e'.
Proof. unfold keeps. by rewrite Forall_app. Qed.

(** A caller recovers the original lookup of any preserved name. *)
Lemma keeps_in ks k e e' : keeps ks e e' -> In k ks -> lookup k e' = lookup k e.
Proof. unfold keeps. rewrite List.Forall_forall. auto. Qed.

(** A block proof may establish preservation by considering each name in the list. *)
Lemma keeps_forall ks e e' :
  keeps ks e e' <-> (forall x, In x ks -> lookup x e' = lookup x e).
Proof.
  unfold keeps. apply List.Forall_forall.
Qed.
