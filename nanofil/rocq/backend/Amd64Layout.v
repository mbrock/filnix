(** The theorems of Amd64Frame.v assume that the slots of a frame lie
    inside the frame and start at multiples of eight bytes. This
    module proves that assumption for the contexts that the backend
    builds, so a theorem about a compiled function does not carry it
    as a hypothesis.

    The function `plan_ctx` of Layout.v computes the offsets in three
    passes. The first pass places the payload keys one after another
    from the top of the frame. The second pass places the roots that
    the collector scans in a table below the payload. The third pass
    gives each aliased key the offset of the key that it aliases. The
    proof follows the same three passes with one invariant: every
    offset assigned so far is a multiple of eight between eight and
    the number of bytes used so far.

    The result needs one hypothesis about the plan, which is that no
    named local has a negative size. A negative size would move the
    next payload key up, above the top of the frame. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Asm Plan PlanTerm Layout.
From Backend Require Import Amd64Word Amd64Memory Amd64Machine Amd64Step Amd64Asm
  Amd64Total Amd64Frame.
Import ListNotations.
Local Open Scope Z_scope.

(** ## The invariant of the passes

    Each pass of `plan_ctx` adds offsets to a table. This section
    names the property that every pass preserves and proves that each
    of the three passes preserves it. *)

(** A table of offsets is [bounded_by] a byte count when every offset
    in it is a multiple of eight between eight and that count. *)
Definition bounded_by (slots : nmap Z) (limit : Z) : Prop :=
  forall n off, nm_find n slots = Some off -> 8 <= off <= limit /\ off mod 8 = 0.

(** A plan has its [locals_sized] when no named local among its
    payload keys has a negative size. *)
Definition locals_sized (p : plan) : Prop :=
  forall x size, In (KLocal x size) (fr_plain (pl_frame p)) -> 0 <= size.

(** Rounding up to a multiple of sixteen does not decrease an integer,
    and the result is a multiple of sixteen. *)
Lemma round16_bounds (n : Z) : n <= round16 n /\ round16 n mod 16 = 0.
Proof.
  unfold round16, fifteen, sixteen.
  split.
  - pose proof (Z.div_mod (n + 15) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)). lia.
  - apply Z.mod_mul. lia.
Qed.

(** Rounding to sixteen bytes also aligns a payload to eight bytes.
    The first pass uses this fact when it places a named local. *)
Lemma round16_mod8 (n : Z) : round16 n mod 8 = 0.
Proof.
  unfold round16, fifteen, sixteen.
  replace ((n + 15) / 16 * 16) with (((n + 15) / 16 * 2) * 8) by ring.
  apply Z.mod_mul. lia.
Qed.

(** A table that is bounded by a count is bounded by every larger
    count. *)
Lemma bounded_by_weaken (slots : nmap Z) (limit limit' : Z) :
  limit <= limit' -> bounded_by slots limit -> bounded_by slots limit'.
Proof.
  intros Hle Hslots n off Hfind.
  specialize (Hslots n off Hfind). lia.
Qed.

(** Adding an offset that satisfies the bound keeps a table bounded. *)
Lemma bounded_by_add (slots : nmap Z) (limit : Z) (n : name) (off : Z) :
  8 <= off <= limit -> off mod 8 = 0 ->
  bounded_by slots limit -> bounded_by (nm_add n off slots) limit.
Proof.
  intros Hbound Hmod Hslots k value Hfind.
  rewrite nm_find_add in Hfind. destruct (name_eqb k n).
  - injection Hfind as <-. auto.
  - exact (Hslots k value Hfind).
Qed.

(** The first pass places one payload key at a time. Placing a key
    does not decrease the count of used bytes, the count stays a
    multiple of eight, and every offset in the table stays within the
    count. This holds for every key except a named local of negative
    size. *)
Lemma plain_slot_bounded (slots : nmap Z) (locals : nmap local_slot) (off : Z)
    (k : key) :
  (forall x size, k = KLocal x size -> 0 <= size) ->
  0 <= off -> off mod 8 = 0 -> bounded_by slots off ->
  let '(slots', _, off') := plain_slot (slots, locals, off) k in
  off <= off' /\ off' mod 8 = 0 /\ bounded_by slots' off'.
Proof.
  intros Hsize Hoff Hmod Hslots.
  destruct k as [n | n | [| |] i | | | | x size | k | x];
    cbn [plain_slot]; unfold eight, sixteen;
    try (assert (Halign : (off + 8) mod 8 = 0)
           by (rewrite Z.add_mod, Hmod by lia; reflexivity);
         split; [lia |]; split; [exact Halign |];
         apply bounded_by_add; try assumption; try lia;
         apply (bounded_by_weaken slots off); [lia | exact Hslots]).
  - assert (Halign : (off + 16) mod 8 = 0)
      by (rewrite Z.add_mod, Hmod by lia; reflexivity).
    split; [lia |]. split; [exact Halign |].
    apply bounded_by_add; try assumption; try lia.
    apply (bounded_by_weaken slots off); [lia | exact Hslots].
  - specialize (Hsize x size eq_refl).
    pose proof (round16_bounds size) as Hpad.
    pose proof (round16_bounds (off + round16 size)) as Hpayload.
    assert (Halign : (round16 (off + round16 size) + round16 size + 8) mod 8 = 0).
    { rewrite Z.add_mod by lia.
      rewrite (Z.add_mod (round16 (off + round16 size))) by lia.
      rewrite !round16_mod8. reflexivity. }
    split; [lia |]. split; [exact Halign |].
    apply (bounded_by_weaken slots off); [lia | exact Hslots].
Qed.

(** The first pass places a list of payload keys one after another.
    If no named local in the list has a negative size, the pass keeps
    the table bounded by the bytes used so far, and that count stays a
    nonnegative multiple of eight. *)
Lemma plain_slots_bounded (ks : list key) (slots : nmap Z) (locals : nmap local_slot)
    (off : Z) :
  (forall x size, In (KLocal x size) ks -> 0 <= size) ->
  0 <= off -> off mod 8 = 0 -> bounded_by slots off ->
  let '(slots', _, off') := fold_left plain_slot ks (slots, locals, off) in
  off <= off' /\ off' mod 8 = 0 /\ bounded_by slots' off'.
Proof.
  revert slots locals off. induction ks as [|k ks IH];
    intros slots locals off Hsize Hoff Hmod Hslots; cbn [fold_left].
  - split; [lia | auto].
  - pose proof (plain_slot_bounded slots locals off k
      ltac:(intros x size E; apply Hsize with x; subst k; now left)
      Hoff Hmod Hslots) as Hstep.
    destruct (plain_slot (slots, locals, off) k) as [[slots1 locals1] off1].
    destruct Hstep as [Hle [Hmod1 Hslots1]].
    specialize (IH slots1 locals1 off1
      ltac:(intros x size Hin; apply Hsize with x; now right)
      ltac:(lia) Hmod1 Hslots1).
    destruct (fold_left plain_slot ks (slots1, locals1, off1))
      as [[slots2 locals2] off2].
    destruct IH as [Hle2 [Hmod2 Hslots2]]. split; [lia | auto].
Qed.

(** A function keeps the pointers that the collector must scan in a
    table of roots, which lies in the frame below the payload. The
    second pass gives each root one entry of eight bytes in that
    table. Every entry lies inside the frame. The statement starts at
    the root with the index i, so that an induction over the list of
    roots can use it. *)
Lemma lower_slots_bounded (ks : list key) (base plain : Z) (slots : nmap Z) (i : Z) :
  0 <= plain -> plain mod 8 = 0 -> 0 <= i ->
  base = plain + 16 + 8 * (i + Zlength ks) ->
  bounded_by slots base ->
  bounded_by (fst (fold_left (lower_slot base) ks (slots, i))) base.
Proof.
  revert slots i. induction ks as [|k ks IH];
    intros slots i Hplain Hmod Hi Hbase Hslots; cbn [fold_left fst].
  - exact Hslots.
  - rewrite Zlength_correct in Hbase. cbn [List.length] in Hbase.
    rewrite Nat2Z.inj_succ in Hbase.
    pose proof (Nat2Z.is_nonneg (List.length ks)) as Hlen.
    cbn [lower_slot]. apply IH; try assumption; try lia.
    + rewrite Zlength_correct. lia.
    + apply bounded_by_add; [unfold sixteen, eight; lia | | exact Hslots].
      replace (base - sixteen - eight * i)
        with (plain + 8 * (1 + Z.of_nat (List.length ks)))
        by (unfold sixteen, eight; lia).
      rewrite Z.add_mod, Z.mul_mod, Hmod by lia. reflexivity.
Qed.

(** The third pass copies offsets that are already in the table, so it
    keeps the table bounded. *)
Lemma alias_slots_bounded (aliases : list (key * key)) (slots0 slots : nmap Z)
    (limit : Z) :
  bounded_by slots0 limit -> bounded_by slots limit ->
  bounded_by
    (fold_left (fun m a => match nm_find (key_term (snd a)) slots0 with
                           | Some off => nm_add (key_term (fst a)) off m
                           | None => m
                           end)
               aliases slots)
    limit.
Proof.
  intros Hsource. revert slots.
  induction aliases as [|[k target] aliases IH]; intros slots Hslots;
    cbn [fold_left fst snd]; [exact Hslots |].
  apply IH. destruct (nm_find (key_term target) slots0) as [off|] eqn:Hfind;
    [|exact Hslots].
  destruct (Hsource _ _ Hfind) as [Hbound Hmod].
  now apply bounded_by_add.
Qed.

(** ## The layout of a plan

    The backend builds the context of a function by running the three
    passes one after another. The theorem of this section is the
    result that Amd64Frame.v needs: every slot of such a context lies
    inside the function's frame. *)

(** The context of a plan whose locals have nonnegative sizes has its
    slots laid out: every slot lies within the frame's size and starts
    at a multiple of eight bytes below `%rbp`. *)
Theorem plan_slots_laid_out (p : plan) :
  locals_sized p -> slots_laid_out (plan_ctx p).
Proof.
  intros Hsize.
  assert (Hempty : bounded_by nm_empty 0).
  { intros n off Hfind. rewrite nm_find_empty in Hfind. discriminate. }
  pose proof (plain_slots_bounded (fr_plain (pl_frame p)) nm_empty nm_empty 0
    Hsize ltac:(lia) eq_refl Hempty) as Hplain.
  unfold plan_ctx.
  destruct (fold_left plain_slot (fr_plain (pl_frame p)) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain].
  destruct Hplain as [Hnonneg [Hmod Hslots1]].
  set (base := plain + sixteen + eight * Zlength (fr_roots (pl_frame p))).
  assert (Hle : plain <= base).
  { unfold base, sixteen, eight. rewrite Zlength_correct.
    pose proof (Nat2Z.is_nonneg (List.length (fr_roots (pl_frame p)))). lia. }
  assert (Hslots1base : bounded_by slots1 base).
  { eapply bounded_by_weaken; eassumption. }
  pose proof (lower_slots_bounded (fr_roots (pl_frame p)) base plain slots1 0
    Hnonneg Hmod ltac:(lia) ltac:(unfold base, sixteen, eight; lia)
    Hslots1base) as Hroots.
  destruct (fold_left (lower_slot base) (fr_roots (pl_frame p)) (slots1, 0))
    as [slots2 i]. cbn [fst] in Hroots.
  pose proof (alias_slots_bounded (fr_aliases (pl_frame p)) slots2 slots2 base
    Hroots Hroots) as Halias.
  pose proof (round16_bounds base) as Hround.
  intros k off Hfind. unfold slot in Hfind. cbn [cx_slots] in Hfind.
  specialize (Halias (key_term k) off Hfind). cbn [cx_size]. lia.
Qed.
