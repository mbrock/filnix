(** When a C program calls a system-call wrapper in libpizlo, such as
    `c: fstat`, `c: ioctl`, or any failing call that sets `c: errno`, the
    wrapper writes its results into memory that belongs to the caller.
    While the system call is running, the kernel or runtime overwrites the
    bytes in that buffer. To reason about the call in
    [OsWorld](OsWorld.v), the caller needs a way to lend an output buffer
    to an [[external call]] at entry, let the call write into it, and
    receive the buffer back when the call returns.

    ## Why a borrowed block includes both bytes and aux slots

    In Fil-C, every byte in an allocated object has a matching shadow slot
    in the object's [[aux]] allocation that holds a pointer [[capability]]
    whenever a pointer is stored at that address. In our memory model
    ([Heap](../../theories/logic/Heap.v)), each offset of an object
    therefore has two entries: a data byte and a capability slot. When an
    external call has permission to write to an address range, the frame
    rule in [ContractFrame](../../theories/logic/ContractFrame.v) requires
    the caller to hand over both the data bytes and the capability slots
    across that range. This module packages those two lists together as a
    single borrowable block.

    Live objects in Fil-C memory never overlap, so a system call that
    writes only within its borrowed buffers cannot overwrite any other
    live object owned by the caller. When the call returns, the caller's
    other buffers still hold their previous values, and [blks_return]
    updates the borrowed buffers to reflect the bytes and capabilities
    written by the call. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
Import ListNotations.
Open Scope Z_scope.

(** ## Blocks a call borrows

    We represent a contiguous buffer range by a triple `(b, o, n)`: `n`
    bytes starting at byte offset `o` inside the object with [[identity]]
    `b`. Before introducing ownership assertions, this first section
    defines the plain bookkeeping on a block: which byte and capability
    slots belong to it, when a physical address falls inside it, and how
    to read its current contents from memory. *)

(** A block of length `n` at offset `o` of object `b` covers offsets `o`
    through `o + n - 1`. Its key list [blk_keys] collects the byte key and
    the capability-slot key for each of those offsets. *)
Definition blk_keys (b o n : Z) : list piece := (PByte b <$> seqZ o n) ++ (PAux b <$> seqZ o n).

(** A system call may write into more than one buffer at once; for
    instance, `c: fstat` can write both a `c: struct stat` buffer and
    `c: errno`. Given a list of blocks, [blks_keys] concatenates the keys
    of each block in order. *)
Fixpoint blks_keys (bl : list (Z * Z * Z)) : list piece :=
  match bl with [] => [] | x :: bl' => blk_keys x.1.1 x.1.2 x.2 ++ blks_keys bl' end.

(** In physical memory, offset `o` of object `b` sits at address `b + o`.
    An address satisfies [blk_out] when it falls inside the byte range of
    at least one block in the borrowed list. *)
Definition blk_out (bl : list (Z * Z * Z)) (a : Z) : Prop :=
  exists b o n, In (b, o, n) bl /\ b + o <= a < b + o + n.

(** A block satisfies [blk_live] when its offset and length are
    non-negative and its byte range lies entirely inside a live object in
    memory. *)
Definition blk_live (m : mem) (x : Z * Z * Z) : Prop :=
  exists reg, live_at m x.1.1 reg /\ 0 <= x.1.2 /\ 0 <= x.2 /\ x.1.1 + x.1.2 + x.2 <= r_end reg.

(** From physical memory, [blk_bytes] and [blk_caps] read the current byte
    values and stored capabilities across a block's offset range. *)
Definition blk_bytes (m : mem) (b o n : Z) : list Z := (fun i => m_bytes m (b + i)) <$> seqZ o n.
Definition blk_caps (m : mem) (b o n : Z) : list cap := (fun i => m_aux m (b + i)) <$> seqZ o n.

(** Pairing each key of a block with the byte or capability currently
    stored at that offset in memory produces [blk_now]. When a system call
    returns, [blk_now] gives the new contents that we record for the
    borrowed buffer. *)
Definition blk_now (m : mem) (b o n : Z) : list (piece * pval) :=
  byte_ps b o (blk_bytes m b o n) ++ aux_ps b o (blk_caps m b o n).

(** To update a borrowed buffer's recorded contents after a call, we must
    show that the new entry list has the exact same keys as the old one.
    When the byte list and capability list both have length `n`, their
    combined keys equal [blk_keys]. *)
Lemma blk_ps_keys b o n xs cs :
  0 <= n -> length xs = Z.to_nat n -> length cs = Z.to_nat n ->
  (byte_ps b o xs ++ aux_ps b o cs).*1 = blk_keys b o n.
Proof.
  intros Hn Hx Hc. rewrite fmap_app byte_ps_keys aux_ps_keys Hx Hc Z2Nat.id; [reflexivity|exact Hn].
Qed.

(** In particular, for any non-negative block length, the keys of [blk_now]
    equal [blk_keys]. *)
Lemma blk_now_keys m b o n : 0 <= n -> (blk_now m b o n).*1 = blk_keys b o n.
Proof.
  intros Hn. apply blk_ps_keys; [exact Hn | |]; unfold blk_bytes, blk_caps;
    rewrite length_fmap length_seqZ; reflexivity.
Qed.

(** Lending a buffer to a system call lets the call overwrite the buffer's
    bytes and capabilities, but never lets it free the underlying object.
    Accordingly, [blk_keys] contains only byte and capability-slot keys,
    never an object liveness token. *)
Lemma blk_keys_live b o n b' : PLive b' ∉ blk_keys b o n.
Proof.
  intros Hin. apply elem_of_app in Hin as [Hin|Hin]; apply list_elem_of_fmap in Hin as (i & [=] & _).
Qed.

(** Any byte offset inside one of the borrowed buffers has both its byte
    entry and its capability-slot entry listed in [blks_keys]. *)
Lemma blks_keys_in bl b o n o' :
  In (b, o, n) bl -> o <= o' < o + n -> PByte b o' ∈ blks_keys bl /\ PAux b o' ∈ blks_keys bl.
Proof.
  intros Hin Ho. assert (Hs : o' ∈ seqZ o n) by (apply elem_of_seqZ; lia).
  induction bl as [|x bl IH]; [destruct Hin|]. cbn [blks_keys].
  destruct Hin as [->|Hin].
  - cbn. split; apply elem_of_app; left; apply elem_of_app; [left|right]; exact (list_elem_of_fmap_2 _ _ _ Hs).
  - destruct (IH Hin) as [H1 H2]. split; apply elem_of_app; right; assumption.
Qed.

(** Just as for a single block, [blks_keys] never includes an object
    liveness token. *)
Lemma blks_keys_live bl b' : PLive b' ∉ blks_keys bl.
Proof.
  induction bl as [|x bl IH]; cbn [blks_keys]; [apply not_elem_of_nil|].
  intros Hin. apply elem_of_app in Hin as [Hin|Hin]; [exact (blk_keys_live _ _ _ _ Hin) | exact (IH Hin)].
Qed.

(** Live objects in Fil-C memory do not overlap, so an address inside a
    live borrowed buffer cannot belong to any other live object. Every
    in-bounds byte and capability slot at a borrowed address is therefore
    covered by [blks_keys]. *)
Lemma blks_pieces_off m h bl :
  live_disjoint m -> Forall (blk_live m) bl -> pieces_off (blks_keys bl) h m (blk_out bl).
Proof.
  intros Hd Hl l v _ Hk.
  assert (Hc : forall b' o', (forall b o n, In (b, o, n) bl -> o <= o' < o + n -> b' <> b) ->
            forall reg', live_at m b' reg' -> 0 <= o' -> b' + o' < r_end reg' -> ~ blk_out bl (b' + o')).
  { intros b' o' Hb reg' Hlive Ho He (b & o & n & Hin & Hr).
    rewrite Forall_forall in Hl. destruct (Hl _ Hin) as (reg & Hlv & Ho0 & Hn0 & Hend). cbn in Ho0, Hn0, Hend, Hlv.
    destruct (Z.eq_dec b' b) as [->|Hne].
    - exact (Hb b o n Hin ltac:(lia) eq_refl).
    - destruct (Hd b' reg' b reg Hlive Hlv Hne); lia. }
  destruct l as [b'|b' o'|b' o'|k]; try exact I; apply Hc; intros b o n Hin Ho <-; apply Hk;
    apply (blks_keys_in _ _ _ _ _ Hin Ho).
Qed.

(** ## Owning errno and blocks

    In ordinary logic, a definition of type `Prop` (such as [blk_live]
    above) states a fact about the whole machine's memory. Proving C
    programs directly with whole-memory facts is painful because of
    aliasing: every time a function writes through a pointer, you would
    have to prove that the write did not clobber any other variable in the
    program.

    [[separation-logic|Separation logic]] (implemented here in
    [[iris|Iris]]) solves that by treating memory as a resource that parts
    of a proof own. A definition of type `iProp` is called an assertion:
    instead of just stating a fact about memory, it claims exclusive
    ownership of a specific set of memory pieces
    ([[ghost-state|ghost state]]). When two assertions are joined with `∗`,
    they own disjoint pieces of memory. Lending an assertion to a system
    call gives the call temporary permission to overwrite those pieces,
    while everything the caller keeps is guaranteed to remain untouched. *)

(** The definitions in this section construct separation-logic assertions
    for borrowed buffers and for `c: errno`. *)
Section own.
Context `{!gen_heapGS piece pval Σ}.

(** When lending an output buffer to a system call, the caller does not
    care what bytes or capabilities sit in the buffer before the call, or
    what values the call writes into it. The assertion [blk_any] hides
    those values behind existential quantifiers (`∃ xs cs`) and claims
    ownership of all `n` bytes and `n` capability slots of the block. *)
Definition blk_any (b o n : Z) : iProp Σ :=
  ∃ xs cs, ⌜length xs = Z.to_nat n /\ length cs = Z.to_nat n⌝ ∗ pts (byte_ps b o xs ++ aux_ps b o cs).

(** For a list of borrowed buffers, [blks] claims separate ownership of
    every block in the list. *)
Definition blks (bl : list (Z * Z * Z)) : iProp Σ := [∗ list] x ∈ bl, blk_any x.1.1 x.1.2 x.2.

(** Owning the empty list of blocks requires no resources. *)
Lemma blks_nil : ⊢ blks [].
Proof. unfold blks. by rewrite big_sepL_nil. Qed.

(** Owning a non-empty list of blocks splits into owning the first block
    and separately owning the remaining blocks. *)
Lemma blks_cons b o n bl : blks ((b, o, n) :: bl) ⊣⊢ blk_any b o n ∗ blks bl.
Proof. unfold blks. by rewrite big_sepL_cons. Qed.

(** In userland glibc, the calling thread's `c: int errno` variable is a
    4-byte integer at offset 0 of its thread-local object. When a proof
    tracks the exact 4-byte value stored in `c: errno`, [errno_own] claims
    those four bytes together with their four shadow capability slots. *)
Definition errno_own (eb : Z) (bs : list Z) : iProp Σ :=
  ∃ cs, ⌜length bs = 4%nat /\ length cs = 4%nat⌝ ∗ pts (byte_ps eb 0 bs ++ aux_ps eb 0 cs).

(** Most callers only need to lend `c: errno` to a system call that might
    overwrite it on failure, without caring what number was in `c: errno`
    before. The assertion [errno_any] hides the 4-byte value behind `∃ bs`. *)
Definition errno_any (eb : Z) : iProp Σ := ∃ bs, errno_own eb bs.

(** Owning `c: errno` with an unknown value is equivalent to owning the
    4-byte block at offset 0 of its object. This lets the call rules in
    [OsWorld](OsWorld.v) treat `c: errno` just like any other borrowed
    output buffer. *)
Lemma errno_any_blk eb : errno_any eb ⊣⊢ blk_any eb 0 4.
Proof.
  iSplit.
  - iIntros "(%bs & %cs & %Hl & Hp)". iExists bs, cs. iFrame. done.
  - iIntros "(%xs & %cs & %Hl & Hp)". iExists xs, cs. iFrame. done.
Qed.

(** When an external call finishes, the caller's unborrowed memory already
    matches the new physical memory, while the borrowed buffer still
    records its pre-call contents. Using Iris's
    [[update-modality|update modality]] (`==∗`), [blk_return] refreshes
    the borrowed block to the bytes and capabilities now in physical
    memory and hands [blk_any] back to the caller. *)
Lemma blk_return h m' b o n K :
  agrees_except (blk_keys b o n ++ K) m' h -> blk_live m' (b, o, n) ->
  gen_heap_interp h -∗ blk_any b o n ==∗
  gen_heap_interp (overwrite (blk_now m' b o n) h) ∗ blk_any b o n ∗
  ⌜agrees_except K m' (overwrite (blk_now m' b o n) h)⌝.
Proof.
  intros Ha (reg & [E L] & Ho & Hn & Hend). cbn in E, Ho, Hn, Hend.
  iIntros "Hh (%xs & %cs & [%Hx %Hc] & Hp)".
  iMod (pts_update _ _ (blk_now m' b o n) with "Hh Hp") as "[Hh Hp]".
  { rewrite blk_now_keys; [|exact Hn]. symmetry. exact (blk_ps_keys _ _ _ _ _ Hn Hx Hc). }
  iModIntro. iFrame "Hh". iSplitL "Hp".
  { iExists _, _. iFrame "Hp". iPureIntro. unfold blk_bytes, blk_caps.
    split; rewrite length_fmap length_seqZ; reflexivity. }
  iPureIntro. intros l v Hl HK. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [Hnot Hh]].
  - assert (Hreg : registered m' b) by (unfold registered; congruence).
    apply elem_of_app in Hin as [Hin|Hin].
    + apply byte_ps_elem in Hin as (i & x & Hxi & -> & ->). unfold blk_bytes in Hxi.
      rewrite list_lookup_fmap in Hxi. destruct (seqZ o n !! i) as [k|] eqn:Ei; [|discriminate].
      apply lookup_seqZ in Ei as [-> Hi]. injection Hxi as <-.
      split; [exact Hreg|]. intros reg' E' _. rewrite E in E'. injection E' as <-. lia.
    + apply aux_ps_elem in Hin as (i & c & Hci & -> & ->). unfold blk_caps in Hci.
      rewrite list_lookup_fmap in Hci. destruct (seqZ o n !! i) as [k|] eqn:Ei; [|discriminate].
      apply lookup_seqZ in Ei as [-> Hi]. injection Hci as <-.
      split; [exact Hreg|]. intros reg' E' _. rewrite E in E'. injection E' as <-.
      split; [lia|]. split; [lia|]. left. reflexivity.
  - apply Ha; [exact Hh|]. rewrite blk_now_keys in Hnot; [|exact Hn].
    intros Hin. apply elem_of_app in Hin as [Hin|Hin]; [exact (Hnot Hin) | exact (HK Hin)].
Qed.

(** Writing new bytes or capabilities into a buffer never frees an object.
    Updating byte and capability entries in the separation-logic state
    therefore leaves every object's liveness record unchanged. *)
Lemma overwrite_live ps h b :
  PLive b ∉ ps.*1 -> overwrite ps h !! PLive b = h !! PLive b.
Proof.
  induction ps as [|[l v] ps IH]; intros Hn; [reflexivity|]. cbn [overwrite fst snd].
  cbn [fmap list_fmap fst] in Hn. apply not_elem_of_cons in Hn as [Hne Hn].
  rewrite lookup_insert_ne; [exact (IH Hn) | congruence].
Qed.

(** By repeating [blk_return] for each block in the list, [blks_return]
    refreshes all of the call's borrowed buffers to their post-call
    contents in physical memory while leaving all object liveness tokens
    unchanged. *)
Lemma blks_return bl h m' K :
  agrees_except (blks_keys bl ++ K) m' h -> Forall (blk_live m') bl ->
  gen_heap_interp h -∗ blks bl ==∗ ∃ h', gen_heap_interp h' ∗ blks bl ∗
    ⌜agrees_except K m' h' /\ forall b, h' !! PLive b = h !! PLive b⌝.
Proof.
  revert h. induction bl as [|x bl IH]; intros h Ha Hl; iIntros "Hh Hb".
  - iModIntro. iExists h. iFrame "Hh Hb". done.
  - destruct x as [[b o] n]. iDestruct (big_sepL_cons with "Hb") as "[Hb Hbs]". cbn [fst snd].
    inversion_clear Hl as [|? ? Hl0 Hl1]. rename Hl1 into Hl. cbn [blks_keys fst snd] in Ha. rewrite <- app_assoc in Ha.
    iMod (blk_return h m' b o n _ Ha Hl0 with "Hh Hb") as "(Hh & Hb & %Ha')".
    iMod (IH _ Ha' Hl with "Hh Hbs") as (h') "(Hh & Hbs & %Ha'' & %Hlive)".
    iModIntro. iExists h'. iFrame "Hh". iSplitL "Hb Hbs"; [iApply big_sepL_cons; iFrame|].
    iPureIntro. split; [exact Ha''|].
    intros b'. rewrite Hlive. apply overwrite_live. rewrite blk_now_keys; [apply blk_keys_live|].
    destruct Hl0 as (? & _ & _ & ? & _). assumption.
Qed.

End own.
