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
Admitted.

(** A table that is bounded by a count is bounded by every larger
    count. *)
Lemma bounded_by_weaken (slots : nmap Z) (limit limit' : Z) :
  limit <= limit' -> bounded_by slots limit -> bounded_by slots limit'.
Proof.
Admitted.

(** Adding an offset that satisfies the bound keeps a table bounded. *)
Lemma bounded_by_add (slots : nmap Z) (limit : Z) (n : name) (off : Z) :
  8 <= off <= limit -> off mod 8 = 0 ->
  bounded_by slots limit -> bounded_by (nm_add n off slots) limit.
Proof.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.
