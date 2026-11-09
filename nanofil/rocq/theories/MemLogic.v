(** Blocks of memory in the program logic of Logic.v, and the triple of
    libc's memset derived from [[campaign|Campaign]] 4's contract.

    A block is owned piece by piece: [bytes] b o xs, the bytes xs from
    offset o of the object b, and [auxes] b o cs, the capabilities cs
    in its [[aux]] slots from the same offset. A write by libc into a
    block needs both: memset clears every pointer slot it touches, and
    a pointer slot is an aux piece.

    [wp_memset] is memset's [memset_contract] read as a rule: owning the
    object's life and a block of n bytes from an 8-aligned offset, with
    their aux slots, the call fills the bytes with c's low byte and
    empties every slot that starts in the block ([clear_slots]),
    and binds its result to the block's pointer. The contract's exact
    frame ([memset_frame]) keeps every other piece: a byte or slot it
    may change lies in the owned block ([fill_after], through Heap.v's
    [frame_within]). The block's offset is 8-aligned so that the slots
    memset touches start inside it; the contract also allows an
    unaligned start, whose first touched slot begins before it. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Aux pieces *)

(** The pieces of the aux slots holding cs from offset o of the object
    b. *)
Definition aux_ps (b o : Z) (cs : list cap) : list (piece * pval) :=
  zip_with (fun i c => (PAux b i, VAux c)) (seqZ o (Z.of_nat (length cs))) cs.

(** The first slot's piece, then the rest's. *)
Lemma aux_ps_cons b o c cs : aux_ps b o (c :: cs) = (PAux b o, VAux c) :: aux_ps b (o + 1) cs.
Proof.
  unfold aux_ps. cbn [length]. rewrite Nat2Z.inj_succ seqZ_cons; [|lia].
  rewrite Z.pred_succ. reflexivity.
Qed.

(** The pieces of cs are aux pieces at the offsets from o. *)
Lemma aux_ps_keys b o cs : (aux_ps b o cs).*1 = PAux b <$> seqZ o (Z.of_nat (length cs)).
Proof.
  revert o. induction cs as [|c cs IH]; intros o; [reflexivity|].
  rewrite aux_ps_cons. cbn [fmap list_fmap fst]. rewrite IH.
  cbn [length]. rewrite Nat2Z.inj_succ (seqZ_cons o); [|lia]. rewrite Z.pred_succ. reflexivity.
Qed.

(** A byte piece of xs is the i-th byte's, at offset o + i. *)
Lemma byte_ps_elem b o xs l v :
  (l, v) ∈ byte_ps b o xs -> exists i x, xs !! i = Some x /\ l = PByte b (o + Z.of_nat i) /\ v = VByte x.
Proof.
  intros H. apply list_elem_of_lookup in H as [k Hk]. unfold byte_ps in Hk.
  apply lookup_zip_with_Some in Hk as (i & x & E & Hi & Hx). apply lookup_seqZ in Hi as [-> _].
  injection E as -> ->. eauto.
Qed.

(** An aux piece of cs is the i-th slot's, at offset o + i. *)
Lemma aux_ps_elem b o cs l v :
  (l, v) ∈ aux_ps b o cs -> exists i c, cs !! i = Some c /\ l = PAux b (o + Z.of_nat i) /\ v = VAux c.
Proof.
  intros H. apply list_elem_of_lookup in H as [k Hk]. unfold aux_ps in Hk.
  apply lookup_zip_with_Some in Hk as (i & c & E & Hi & Hc). apply lookup_seqZ in Hi as [-> _].
  injection E as -> ->. eauto.
Qed.

(** The i-th slot's piece is among the keys of cs's pieces. *)
Lemma aux_ps_key b o cs i : 0 <= i < Z.of_nat (length cs) -> PAux b (o + i) ∈ (aux_ps b o cs).*1.
Proof.
  intros Hi. rewrite aux_ps_keys. apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
Qed.

(** The i-th byte's piece is among the keys of xs's pieces. *)
Lemma byte_ps_key b o xs i : 0 <= i < Z.of_nat (length xs) -> PByte b (o + i) ∈ (byte_ps b o xs).*1.
Proof.
  intros Hi. rewrite byte_ps_keys. apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
Qed.

(** ## Blocks *)

(** The pieces of a block: the life of the object b with the region
    reg, the bytes xs and the aux slots cs from offset o. *)
Definition block_ps (b : Z) (reg : region) (o : Z) (xs : list Z) (cs : list cap) : list (piece * pval) :=
  (PLive b, VLive reg) :: byte_ps b o xs ++ aux_ps b o cs.

(** Blocks of the same lengths have the same keys. *)
Lemma block_ps_keys b reg o xs cs ys ds :
  length ys = length xs -> length ds = length cs ->
  (block_ps b reg o ys ds).*1 = (block_ps b reg o xs cs).*1.
Proof.
  intros Hy Hd. unfold block_ps. cbn [fmap list_fmap fst]. rewrite !fmap_app.
  rewrite !byte_ps_keys !aux_ps_keys Hy Hd. reflexivity.
Qed.

(** The slots cs from offset o once memset has touched each: those
    that start at a multiple of 8 are empty, the rest are as they were.
    For an object at a multiple of 8, these are the slots the contract
    clears. *)
Definition clear_slots (o : Z) (cs : list cap) : list cap :=
  zip_with (fun i c => if i mod 8 =? 0 then CNone else c) (seqZ o (Z.of_nat (length cs))) cs.

(** Clearing keeps the number of slots. *)
Lemma length_clear_slots o cs : length (clear_slots o cs) = length cs.
Proof. unfold clear_slots. rewrite length_zip_with length_seqZ Nat2Z.id. lia. Qed.

(** The i-th cleared slot. *)
Lemma lookup_clear_slots o cs i c :
  clear_slots o cs !! i = Some c ->
  exists c0, cs !! i = Some c0 /\ c = if (o + Z.of_nat i) mod 8 =? 0 then CNone else c0.
Proof.
  unfold clear_slots. intros H. apply lookup_zip_with_Some in H as (k & c0 & -> & Hk & Hc).
  apply lookup_seqZ in Hk as [-> _]. eauto.
Qed.

(** A memset of the n bytes xs of the block at offset o of the live
    object b, at a multiple of 8, with its slots cs: afterwards its
    bytes are c's low byte and its slots [clear_slots], and every piece
    outside it keeps its agreement ([frame_ok]). *)
Lemma fill_after m m' b reg o xs cs c :
  live_disjoint m -> live_at m b reg -> b mod 8 = 0 -> o mod 8 = 0 -> length cs = length xs ->
  all_agree m (byte_ps b o xs ++ aux_ps b o cs) ->
  memset_result m (mkPtr (b + o) (Obj b)) c (Z.of_nat (length xs)) m' ->
  all_agree m' (byte_ps b o (replicate (length xs) (c mod 256)) ++ aux_ps b o (clear_slots o cs)) /\
  frame_ok (byte_ps b o xs ++ aux_ps b o cs).*1 m m'.
Proof.
  intros Hd Hl Hb8 Ho8 Hlen Ha ((Hr & Hbytes & Haux) & Hfill & Hclear).
  apply all_agree_app in Ha as [Hx Hc].
  set (n := Z.of_nat (length xs)).
  assert (Hregs : forall b', registered m b' -> registered m' b') by (unfold registered; rewrite Hr; auto).
  (* The i-th byte and slot lie in b's bounds. *)
  assert (Hbyte : forall i, (i < length xs)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (_ & H1 & H2). lia. }
  assert (Hslot : forall i c0, cs !! i = Some c0 -> registered m b /\ 0 <= o + Z.of_nat i /\
            b + (o + Z.of_nat i) < r_end reg /\ aux_holds m (b + (o + Z.of_nat i)) c0).
  { intros i c0 Hci. destruct Hl as [E L].
    assert (Hin : (aux_ps b o cs) !! i = Some (PAux b (o + Z.of_nat i), VAux c0)).
    { unfold aux_ps. apply lookup_zip_with_Some. exists (o + Z.of_nat i), c0. split; [reflexivity|].
      split; [|exact Hci]. apply lookup_seqZ. split; [reflexivity|]. apply lookup_lt_Some in Hci. lia. }
    destruct (all_agree_elem _ _ _ _ Hc (list_elem_of_lookup_2 _ _ _ Hin)) as [Hreg Hin'].
    destruct (Hin' reg E L) as (Ho & He & Hh). auto. }
  assert (Hmod : forall i, (b + (o + i)) mod 8 = (o + i) mod 8).
  { intros i. rewrite Z.add_mod; [|lia]. rewrite Hb8 Z.add_0_l Z.mod_mod; [reflexivity|lia]. }
  split.
  - apply all_agree_app. split; apply all_agree_intro; intros l v Hin.
    + apply byte_ps_elem in Hin as (i & x & Hxi & -> & ->).
      apply lookup_replicate in Hxi as [-> Hi].
      destruct (lookup_lt_is_Some_2 xs i Hi) as [x0 Hx0].
      pose proof (all_agree_elem _ _ _ _ Hx (list_elem_of_lookup_2 _ _ _ (byte_ps_lookup b o xs i x0 Hx0)))
        as [Hreg _].
      cbn [agree_piece]. split; [exact (Hregs _ Hreg)|]. intros reg' E L.
      destruct Hl as [E0 _]. rewrite Hr E0 in E. injection E as <-.
      destruct (Hbyte i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
      apply Hfill. unfold span_contains. cbn. lia.
    + apply aux_ps_elem in Hin as (i & c' & Hci & -> & ->).
      destruct (lookup_clear_slots o cs i c' Hci) as (c0 & Hc0 & ->).
      destruct (Hslot i c0 Hc0) as (Hreg & H1 & H2 & Hh).
      cbn [agree_piece]. split; [exact (Hregs _ Hreg)|]. intros reg' E L.
      destruct Hl as [E0 _]. rewrite Hr E0 in E. injection E as <-.
      split; [exact H1|]. split; [exact H2|].
      assert (Hi : (i < length xs)%nat) by (rewrite <- Hlen; exact (lookup_lt_Some _ _ _ Hc0)).
      destruct (Z.eqb_spec ((o + Z.of_nat i) mod 8) 0) as [Hz|Hz].
      * left. apply Hclear. apply memset_touched_spec. cbn [ptr_addr]. rewrite Hmod. lia.
      * unfold aux_holds in *. rewrite Hr. rewrite Haux; [exact Hh|].
        destruct (memset_touched _ _ _) eqn:Ht; [|reflexivity].
        apply memset_touched_spec in Ht as (_ & Ht & _). rewrite Hmod in Ht. contradiction.
  - apply (frame_within _ _ _ b reg); [exact Hr | exact Hd | exact Hl | |].
    + intros a H. apply Hbytes. intros Hs. unfold span_contains in Hs. cbn in Hs.
      destruct (Hbyte (Z.to_nat (a - b - o)) ltac:(lia)) as [H1 H2].
      apply H; [lia|]. rewrite fmap_app. apply elem_of_app. left.
      replace (a - b) with (o + (a - b - o)) by lia. apply byte_ps_key. lia.
    + intros a H. apply Haux. destruct (memset_touched _ _ _) eqn:Ht; [|reflexivity]. exfalso.
      apply memset_touched_spec in Ht as (Hn & Ha8 & Hhi & Hlo). cbn [ptr_addr] in Hhi, Hlo.
      assert (Hab : b + o <= a).
      { pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod (b + o) 8 ltac:(lia)).
        pose proof (Hmod 0) as Hm0. rewrite Z.add_0_r in Hm0. rewrite Ho8 in Hm0. lia. }
      assert (Hi : (Z.to_nat (a - b - o) < length cs)%nat) by lia.
      destruct (lookup_lt_is_Some_2 cs _ Hi) as [c0 Hc0].
      destruct (Hslot _ c0 Hc0) as (_ & H1 & H2 & _).
      apply H; [lia|]. rewrite fmap_app. apply elem_of_app. right.
      replace (a - b) with (o + (a - b - o)) by lia. apply aux_ps_key. lia.
Qed.

(** The memory and aux triples over any [[runtime]] R. *)
Module MemLogic (R : Runtime).
Module SL := StringLogic R.
Module LG := SL.LG.
Module L := LG.L.
Import L LG SL.

Section mem.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** [bytes] b o xs: owning the bytes xs from offset o of the object b. *)
Definition bytes (b o : Z) (xs : list Z) : iProp Σ := pts (byte_ps b o xs).

(** [auxes] b o cs: owning the aux slots holding cs from offset o of
    the object b. *)
Definition auxes (b o : Z) (cs : list cap) : iProp Σ := pts (aux_ps b o cs).

(** A block's pieces are its life, bytes and slots. *)
Lemma block_pts b reg o xs cs : pts (block_ps b reg o xs cs) ⊣⊢ live b reg ∗ bytes b o xs ∗ auxes b o cs.
Proof. rewrite /block_ps /live /bytes /auxes /pts big_sepL_cons big_sepL_app big_sepL_singleton. done. Qed.

Section calls.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Local Instance mem_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

(** memset's triple, from [memset_contract]: owning the life of the
    object b, at a multiple of 8, with the region reg, and the block of
    the bytes xs and the slots cs from the 8-aligned offset o, inside
    its bounds, where vp reads as the block's pointer, vc as the int c
    and vn as its length, and where the fill keeps the world
    interpretation: the call fills the bytes with c's low byte, clears
    the slots it touches, and binds d to the block's pointer. *)
Lemma wp_memset f e ls lab d vp vc vn rest j b reg o xs cs c Φ :
  registry (TAtom "memset") = Some (memset_contract world) ->
  find_fn ge (TAtom "memset") = None -> lookup (TAtom "memset") (ge_globals ge) = None ->
  arg_x ge e (Arg P vp) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg W vc) = Some (WInt c) ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  0 <= c < 2 ^ 32 -> b mod 8 = 0 -> o mod 8 = 0 -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg ->
  length cs = length xs ->
  (forall m m' wd h, memset_result m (mkPtr (b + o) (Obj b)) c (Z.of_nat (length xs)) m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (replicate (length xs) (c mod 256)) (clear_slots o cs)) h)) ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗
  ▷ (live b reg -∗ bytes b o (replicate (length xs) (c mod 256)) -∗ auxes b o (clear_slots o cs) -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o) (Obj b))) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memset")) [Arg P vp; Arg W vc; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hp Hc Hn Hc32 Hb8 Ho8 Ho Hend Hlen Hwi. iIntros "Hl Hx Hcs HK".
  iDestruct (block_pts b reg o xs cs with "[$Hl $Hx $Hcs]") as "Hps".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memset_contract world)
            [WPtr (mkPtr (b + o) (Obj b)); WInt c; WInt (Z.of_nat (length xs))] (pts (block_ps b reg o xs cs)) with "Hps [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hp Hc Hn; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hps". iDestruct (pts_facts with "Hσ Hps") as %(Ha & _ & Hfit). iPureIntro.
    destruct Ha as [[E L] _]. cbn [fst snd] in E, L.
    destruct (Hfit b reg E) as [Hb0 Hfit'].
    eexists _, c, _. split; [reflexivity|]. split; [exact Hc32|]. split; [lia|]. split.
    + unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
      split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
      apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
    + right. exists b. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hps".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.memset_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & p' & c' & n' & Hx & _ & Hres & He).
    injection Hx as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hps") as %Hlk.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg o xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    destruct Hold as [Hlv Hold]. cbn [agree_piece fst snd] in Hlv.
    destruct (fill_after (ls_mem σ) m' b reg o xs cs c Hd Hlv Hb8 Ho8 Hlen Hold Hres) as [Hnew Hfr].
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    iMod (pts_update _ _ (block_ps b reg o (replicate (length xs) (c mod 256)) (clear_slots o cs))
            with "Hh Hps") as "[Hh Hps]".
    { apply block_ps_keys; [apply length_replicate | apply length_clear_slots]. }
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hnk Hh]].
        -- apply elem_of_cons in Hin as [Hin|Hin].
           ++ injection Hin as -> ->. cbn [agree_piece]. exact (live_at_regions _ _ _ _ Hregs Hlv).
           ++ exact (all_agree_elem _ _ _ _ Hnew Hin).
        -- apply Hfr; [|exact (Ha l v Hh)]. intros Hk. apply Hnk.
           rewrite (block_ps_keys b reg o xs cs) ; [|apply length_replicate | apply length_clear_slots].
           cbn [fmap list_fmap fst block_ps]. right. exact Hk.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hres Hlk Hw).
    + rewrite block_pts. iDestruct "Hps" as "(Hl & Hx & Hcs)". iApply ("HK" with "Hl Hx Hcs").
Qed.

(** malloc's triple, from [malloc_contract]: for a size n that v reads
    as, where an allocation keeps the world interpretation, the call
    binds d to the base pointer of a fresh heap object of n bytes,
    rounded up to 16, whose pieces it owns ([obj]). The selected malloc
    never returns null: a refusal is a resource ending, which is not a
    return, so the triple has no null case. *)
Lemma wp_malloc f e ls lab d v rest j n Φ :
  registry (TAtom "malloc") = Some (malloc_contract world) ->
  find_fn ge (TAtom "malloc") = None -> lookup (TAtom "malloc") (ge_globals ge) = None ->
  arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  (forall m wd h base, fresh m (heap_req 16 n) base -> wi m wd h ->
     wi (allocated m (heap_req 16 n) base) wd (overwrite (obj_ps base (heap_req 16 n)) h)) ->
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48 /\
               n <= max_allocation_size⌝ -∗
       obj base (heap_req 16 n) -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j)) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j)) : mexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hn Hwi. iIntros "HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (malloc_contract world) [WInt n] True%I with "[//] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "_ _". iPureIntro. exists n. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) _".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hp).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
    destruct (M.E.malloc_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & n' & Hx & _ & [(base & Hres & He) | (why & born' & He & _)]); [|discriminate He].
    injection Hx as <-. injection He as ->. destruct Hres as (Hmax & Hfr & ->).
    assert (Hex : 0 <= req_extent (heap_req 16 n)).
    { cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
    pose proof Hfr as (Hpos & Hmod & _ & Hnone & _).
    iMod (pts_alloc h (obj_ps base (heap_req 16 n)) with "Hh") as "[Hh Hps]".
    { apply obj_ps_nodup. }
    { intros l' v' Hin. destruct (h !! l') as [v0|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (Ha l' v0 E)) as Hreg'.
      rewrite (obj_ps_id _ _ _ _ Hin) in Hreg'. exact (Hreg' Hnone). }
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l' v' Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]].
        -- exact (obj_ps_agree _ _ _ _ _ Hfr Hex Hin).
        -- exact (agree_piece_allocated _ _ _ _ _ Hnone (Ha l' v' Hh)).
      * exact (live_disjoint_allocated _ _ _ Hd Hfr Hex).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hfr Hw).
    + iApply ("HK" with "[%] Hps"). split; [exact Hpos|]. split; [exact Hmod|]. split; [|exact (proj2 Hmax)].
      destruct (R.address_space _ _ Hr' base
                  (mkRegion base (base + req_extent (heap_req 16 n)) (req_kind (heap_req 16 n)) Live))
        as [_ Hend]; [rewrite object_region_allocated Z.eqb_refl; reflexivity|].
      cbn [r_end] in Hend. exact Hend.
Qed.

End calls.
End mem.
End MemLogic.
