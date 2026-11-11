(** Blocks of memory a `zsys_*` call borrows from the program
    ([OsWorld](OsWorld.v)): the bytes and [[aux]] slots of a byte range
    of one object, owned whatever they hold ([blk_any]), and
    `c: errno` as such a block ([errno_own], [errno_any]).

    A call's writable roots may touch the program's objects only inside
    the blocks it borrows: ContractFrame.v's [pieces_off] then holds of
    the blocks' keys ([blks_pieces_off]), since live objects do not
    overlap. After the call, each block's pieces are given whatever
    memory holds there ([blk_return], [blks_return]), through Heap.v's
    [pts_update], and every other piece keeps its value. A block has an
    aux piece at every offset, as Heap.v's [obj_ps] has, so the aux
    slots of `c: errno` are lent with its bytes. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
Import ListNotations.
Open Scope Z_scope.

(** ## Blocks a call borrows *)

(** A block is a triple (b, o, n): the n bytes from offset o of the
    object of identity b. Its keys are the byte and aux pieces at those
    offsets. *)
Definition blk_keys (b o n : Z) : list piece := (PByte b <$> seqZ o n) ++ (PAux b <$> seqZ o n).

(** The keys of a list of blocks. *)
Fixpoint blks_keys (bl : list (Z * Z * Z)) : list piece :=
  match bl with [] => [] | x :: bl' => blk_keys x.1.1 x.1.2 x.2 ++ blks_keys bl' end.

(** The address a is in one of the blocks bl. *)
Definition blk_out (bl : list (Z * Z * Z)) (a : Z) : Prop :=
  exists b o n, In (b, o, n) bl /\ b + o <= a < b + o + n.

(** The block x lies inside its object, which is live in m. *)
Definition blk_live (m : mem) (x : Z * Z * Z) : Prop :=
  exists reg, live_at m x.1.1 reg /\ 0 <= x.1.2 /\ 0 <= x.2 /\ x.1.1 + x.1.2 + x.2 <= r_end reg.

(** The bytes and capabilities of memory m in the block (b, o, n). *)
Definition blk_bytes (m : mem) (b o n : Z) : list Z := (fun i => m_bytes m (b + i)) <$> seqZ o n.
Definition blk_caps (m : mem) (b o n : Z) : list cap := (fun i => m_aux m (b + i)) <$> seqZ o n.

(** The pieces of the block (b, o, n) holding what memory m holds. *)
Definition blk_now (m : mem) (b o n : Z) : list (piece * pval) :=
  byte_ps b o (blk_bytes m b o n) ++ aux_ps b o (blk_caps m b o n).

(** Bytes and slots of length n from o have the block's keys. *)
Lemma blk_ps_keys b o n xs cs :
  0 <= n -> length xs = Z.to_nat n -> length cs = Z.to_nat n ->
  (byte_ps b o xs ++ aux_ps b o cs).*1 = blk_keys b o n.
Proof.
  intros Hn Hx Hc. rewrite fmap_app byte_ps_keys aux_ps_keys Hx Hc Z2Nat.id; [reflexivity|exact Hn].
Qed.

(** The block's current pieces have its keys. *)
Lemma blk_now_keys m b o n : 0 <= n -> (blk_now m b o n).*1 = blk_keys b o n.
Proof.
  intros Hn. apply blk_ps_keys; [exact Hn | |]; unfold blk_bytes, blk_caps;
    rewrite length_fmap length_seqZ; reflexivity.
Qed.

(** No life token is a block key. *)
Lemma blk_keys_live b o n b' : PLive b' ∉ blk_keys b o n.
Proof.
  intros Hin. apply elem_of_app in Hin as [Hin|Hin]; apply list_elem_of_fmap in Hin as (i & [=] & _).
Qed.

(** The byte and aux keys at offset o' of a block of bl, o' inside it,
    are keys of bl. *)
Lemma blks_keys_in bl b o n o' :
  In (b, o, n) bl -> o <= o' < o + n -> PByte b o' ∈ blks_keys bl /\ PAux b o' ∈ blks_keys bl.
Proof.
  intros Hin Ho. assert (Hs : o' ∈ seqZ o n) by (apply elem_of_seqZ; lia).
  induction bl as [|x bl IH]; [destruct Hin|]. cbn [blks_keys].
  destruct Hin as [->|Hin].
  - cbn. split; apply elem_of_app; left; apply elem_of_app; [left|right]; exact (list_elem_of_fmap_2 _ _ _ Hs).
  - destruct (IH Hin) as [H1 H2]. split; apply elem_of_app; right; assumption.
Qed.

(** No life token is a key of a list of blocks. *)
Lemma blks_keys_live bl b' : PLive b' ∉ blks_keys bl.
Proof.
  induction bl as [|x bl IH]; cbn [blks_keys]; [apply not_elem_of_nil|].
  intros Hin. apply elem_of_app in Hin as [Hin|Hin]; [exact (blk_keys_live _ _ _ _ Hin) | exact (IH Hin)].
Qed.

(** Every byte or aux piece of a live object at an address in the live
    blocks bl is a key of bl ([pieces_off] of ContractFrame.v): another
    live object does not overlap a block's object ([live_disjoint]). *)
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

(** ## Owning errno and blocks *)

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** [blk_any] b o n: owning the block (b, o, n), its bytes and aux
    slots, whatever they hold. *)
Definition blk_any (b o n : Z) : iProp Σ :=
  ∃ xs cs, ⌜length xs = Z.to_nat n /\ length cs = Z.to_nat n⌝ ∗ pts (byte_ps b o xs ++ aux_ps b o cs).

(** [blks] bl: owning every block of bl. *)
Definition blks (bl : list (Z * Z * Z)) : iProp Σ := [∗ list] x ∈ bl, blk_any x.1.1 x.1.2 x.2.

(** Owning no blocks is free. *)
Lemma blks_nil : ⊢ blks [].
Proof. unfold blks. by rewrite big_sepL_nil. Qed.

(** Owning a list of blocks is owning its first and the rest. *)
Lemma blks_cons b o n bl : blks ((b, o, n) :: bl) ⊣⊢ blk_any b o n ∗ blks bl.
Proof. unfold blks. by rewrite big_sepL_cons. Qed.

(** [errno_own] eb bs: owning the `c: int errno` at the base of the
    object eb, its 4 bytes bs and its 4 aux slots, whatever they hold. *)
Definition errno_own (eb : Z) (bs : list Z) : iProp Σ :=
  ∃ cs, ⌜length bs = 4%nat /\ length cs = 4%nat⌝ ∗ pts (byte_ps eb 0 bs ++ aux_ps eb 0 cs).

(** [errno_any] eb: owning `c: errno`, whatever it holds. *)
Definition errno_any (eb : Z) : iProp Σ := ∃ bs, errno_own eb bs.

(** Owning errno is owning the block (eb, 0, 4). *)
Lemma errno_any_blk eb : errno_any eb ⊣⊢ blk_any eb 0 4.
Proof.
  iSplit.
  - iIntros "(%bs & %cs & %Hl & Hp)". iExists bs, cs. iFrame. done.
  - iIntros "(%xs & %cs & %Hl & Hp)". iExists xs, cs. iFrame. done.
Qed.

(** A block handed back: the block's pieces are given what memory m'
    holds, which they agree with while the block lies in a live object
    of m' ([blk_live]); every other piece of h keeps its value, and h's
    other pieces that agreed with m' still do. *)
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

(** Pieces written over h, none of them a life token, leave every life
    token as it was. *)
Lemma overwrite_live ps h b :
  PLive b ∉ ps.*1 -> overwrite ps h !! PLive b = h !! PLive b.
Proof.
  induction ps as [|[l v] ps IH]; intros Hn; [reflexivity|]. cbn [overwrite fst snd].
  cbn [fmap list_fmap fst] in Hn. apply not_elem_of_cons in Hn as [Hne Hn].
  rewrite lookup_insert_ne; [exact (IH Hn) | congruence].
Qed.

(** Every block of bl handed back ([blk_return]), with the life tokens
    of h unchanged. *)
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
