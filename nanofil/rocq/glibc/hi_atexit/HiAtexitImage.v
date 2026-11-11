(** The loader image must leave the interpreter's allocation cursor
    above every static object and every initialized byte. This file
    checks those physical facts for the actual linked image. It also
    checks that static objects do not overlap, before host preparation
    allocates the thread object. *)

From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Values Memory Runtime Run Pieces.
From Glibc Require Import HiAtexitInitial.
Import ListNotations.
Open Scope Z_scope.

(** Looking up an object returns a region with that object's identity
    from the region table, not an unrelated region. *)
Lemma hi_object_member b rs reg : object_region b rs = Some reg ->
  b = r_base reg /\ In reg rs.
Proof.
  induction rs as [|r rs IH]; cbn; [discriminate|].
  destruct (Z.eqb (r_base r) b) eqn:E.
  - intros [= <-]. apply Z.eqb_eq in E. split; [congruence|left; reflexivity].
  - intros H. destruct (IH H) as [Hb Hin]. split; [exact Hb|right; exact Hin].
Qed.

(** The computed table is exactly the loader image's table. *)
Definition hi_image_regions : list region := Eval vm_compute in m_regions hi_m0.

(** Every recorded object lies below the initial cursor and is live. *)
Lemma hi_image_bounds reg : In reg hi_image_regions ->
  0 <= r_base reg < InterpRuntime.start /\ r_end reg <= InterpRuntime.start /\ r_life reg = Live.
Proof.
  assert (Hcheck : forallb (fun r =>
    (0 <=? r_base r) && (r_base r <? InterpRuntime.start) &&
    (r_end r <=? InterpRuntime.start) &&
    match r_life r with Live => true | Freed => false end) hi_image_regions = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hcheck. intros Hin. specialize (Hcheck reg Hin).
  repeat rewrite Bool.andb_true_iff in Hcheck.
  destruct Hcheck as (((Hb & Hs) & He) & Hl).
  apply Z.leb_le in Hb. apply Z.ltb_lt in Hs. apply Z.leb_le in He.
  destruct (r_life reg); [auto|discriminate].
Qed.

(** The finite pairwise check covers all objects, not only the ones
    whose fields the main proof happens to own. *)
Lemma hi_image_apart r1 r2 : In r1 hi_image_regions -> In r2 hi_image_regions ->
  r_base r1 <> r_base r2 -> r_end r1 <= r_base r2 \/ r_end r2 <= r_base r1.
Proof.
  assert (Hcheck : forallb (fun r => forallb (fun s =>
    (r_base r =? r_base s) || (r_end r <=? r_base s) || (r_end s <=? r_base r))
    hi_image_regions) hi_image_regions = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hcheck. intros H1 H2 Hne.
  specialize (Hcheck r1 H1). rewrite forallb_forall in Hcheck.
  specialize (Hcheck r2 H2). repeat rewrite Bool.orb_true_iff in Hcheck.
  destruct Hcheck as [[Heq|He]|He];
    [apply Z.eqb_eq in Heq; contradiction|left; apply Z.leb_le; exact He|right; apply Z.leb_le; exact He].
Qed.

(** No two live objects in the loader image overlap. *)
Lemma hi_image_live_disjoint : live_disjoint hi_m0.
Proof.
  intros b1 r1 b2 r2 [H1 _] [H2 _] Hne.
  apply hi_object_member in H1 as [Hb1 H1]. apply hi_object_member in H2 as [Hb2 H2].
  rewrite Hb1, Hb2. apply hi_image_apart; [exact H1|exact H2|congruence].
Qed.

(** No byte or capability at or above the cursor has been written. *)
Definition hi_image_high (m : mem) : Prop :=
  forall a, InterpRuntime.start <= a -> m_bytes m a = 0 /\ m_aux m a = CNone.

(** A byte store wholly below the cursor preserves that condition. *)
Lemma hi_image_high_bytes m a n x : a + n <= InterpRuntime.start ->
  hi_image_high m -> hi_image_high (store_bytes m a n x).
Proof.
  intros Hend H a' Ha'. unfold store_bytes. cbn.
  assert (Houtside : (a' <? a + n) = false) by (apply Z.ltb_ge; lia).
  rewrite Houtside, Bool.andb_false_r. exact (H a' Ha').
Qed.

(** A capability store below the cursor preserves the same condition. *)
Lemma hi_image_high_aux m a c : a < InterpRuntime.start ->
  hi_image_high m -> hi_image_high (store_aux m a c).
Proof.
  intros Hend H a' Ha'. unfold store_aux. cbn.
  assert (Houtside : (a' =? a) = false) by (apply Z.eqb_neq; lia).
  rewrite Houtside. exact (H a' Ha').
Qed.

(** The store checks share earlier memories instead of copying them
    into each later proof step. These continuations keep that sharing
    explicit in the generated proof term. *)
Ltac hi_image_byte_step a n x k m H :=
  let next := fresh "image" in let Hnext := fresh "Himage" in
  pose (next := store_bytes m a n x);
  assert (Hnext : hi_image_high next) by
    (apply hi_image_high_bytes; [vm_compute; congruence|exact H]);
  k next Hnext.

Ltac hi_image_aux_step a c k m H :=
  let next := fresh "image" in let Hnext := fresh "Himage" in
  pose (next := store_aux m a c);
  assert (Hnext : hi_image_high next) by
    (apply hi_image_high_aux; [vm_compute; congruence|exact H]);
  k next Hnext.

Ltac hi_image_build tree k :=
  lazymatch tree with
  | store_bytes ?inner ?a ?n ?x =>
      let next := hi_image_byte_step a n x k in hi_image_build inner next
  | store_aux ?inner ?a ?c =>
      let next := hi_image_aux_step a c k in hi_image_build inner next
  | _ =>
      let base := fresh "image" in let Hbase := fresh "Himage" in
      pose (base := tree);
      assert (Hbase : hi_image_high base) by (intros a Ha; split; reflexivity);
      k base Hbase
  end.

Ltac hi_image_finish m H := exact H.

(** The loader writes nothing where the first allocation will occur.
    Every source store passes its address check. *)
Lemma hi_image_high_initial : hi_image_high hi_m0.
Proof.
  let image := eval cbv -[store_bytes store_aux] in hi_m0 in
  hi_image_build image hi_image_finish.
Qed.

(** The runtime can allocate safely above the static image: every
    existing object ends below its cursor, and higher memory is unwritten. *)
Lemma hi_image_ready : InterpRuntime.ready InterpRuntime.start hi_m0.
Proof.
  split; [unfold InterpRuntime.start, InterpRuntime.address_end; lia|]. split.
  - intros b reg H. apply hi_object_member in H as [Hb Hin].
    destruct (hi_image_bounds reg Hin) as (Hbnd & Hend & Hlive).
    rewrite Hb. split; [exact Hbnd|]. split; [exact Hend|].
    intros Hfree. congruence.
  - exact hi_image_high_initial.
Qed.
