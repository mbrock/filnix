(** The earlier Hello proof assumes contracts for allocating, copying, and
    searching memory instead of proving those libc implementations.
    This module keeps the corresponding calling rules as a reference.
    Buffer ownership comes from [MemLogic](../logic/MemLogic.v). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic MemLogic LibcCalls LibcStringLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** A scalar string copy replaces destination bytes through the NUL,
    preserves every shadow slot, and needs no pointer-slot alignment.
    The lemma [copy_string_after] records the copied bytes and keeps
    every owned piece outside the destination byte range valid. *)
Lemma copy_string_after m m' b reg o xs src b' reg' ys :
  live_disjoint m -> live_at m b reg -> all_agree m (byte_ps b o xs) -> length xs = S (length ys) ->
  string_ok src b' reg' ys -> all_agree m (string_ps src b' reg' ys) ->
  string_copy_result m (mkPtr (b + o) (Obj b)) src (Z.of_nat (length ys) + 1) m' ->
  all_agree m' (byte_ps b o (ys ++ [0])) /\ frame_ok (byte_ps b o xs).*1 m m'.
Proof.
  intros Hd Hl Hx Hlen Hok Hs ((Hr & Haux & Hbytes) & Hcopy).
  assert (Hbyte : forall i, (i < length xs)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (_ & H1 & H2). lia. }
  split.
  - apply all_agree_intro. intros l v Hin.
    apply byte_ps_elem in Hin as (i & x & Hxi & -> & ->).
    assert (Hi : (i < length xs)%nat).
    { apply lookup_lt_Some in Hxi. rewrite length_app in Hxi. cbn in Hxi. lia. }
    destruct (lookup_lt_is_Some_2 xs i Hi) as [x0 Hx0].
    pose proof (all_agree_elem _ _ _ _ Hx (list_elem_of_lookup_2 _ _ _ (byte_ps_lookup b o xs i x0 Hx0)))
      as [Hreg _].
    cbn [agree_piece]. split; [unfold registered in *; rewrite Hr; exact Hreg|]. intros reg0 E L.
    destruct Hl as [E0 _]. rewrite Hr E0 in E. injection E as <-.
    destruct (Hbyte i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
    rewrite Hcopy; [|unfold span_contains; cbn; lia]. cbn [ptr_addr].
    replace (ptr_addr src + (b + (o + Z.of_nat i) - (b + o))) with (ptr_addr src + Z.of_nat i) by lia.
    exact (string_bytes _ _ _ _ _ Hok Hs i x Hxi).
  - apply (frame_within _ _ _ b reg); [exact Hr | exact Hd | exact Hl | | intros a _; apply Haux].
    intros a H. apply Hbytes. intros Hsp. unfold span_contains in Hsp. cbn in Hsp.
    destruct (Hbyte (Z.to_nat (a - b - o)) ltac:(lia)) as [H1 H2].
    apply H; [lia|]. replace (a - b) with (o + (a - b - o)) by lia. apply byte_ps_key. lia.
Qed.

(** ## Searching a string for its NUL

    A search for zero stops at the first NUL and need not read the
    rest of the caller's stated search range.
    The following facts let a caller use string ownership even when
    that range extends beyond the string's enclosing object. *)

(** Searching a bounded string for zero reads through its NUL or the
    bound, whichever comes first, and never requires bytes after a match.
    The lemma [memchr_input_bounded] turns that readable prefix into the
    memory-search contract's precondition for a zero low byte. *)
Lemma memchr_input_bounded m p c n k :
  0 <= c < 2 ^ 32 -> c mod 256 = 0 -> bounded_length m p n k -> memchr_input m p c n.
Proof.
  intros Hc H0 (Hn & Hk & Hlife & Ha & Hpos & Hnul).
  split; [exact Hc|]. split; [exact Hn|]. exists k. split; [exact Hk|]. rewrite H0. split.
  - split; [destruct (k <? n) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia|].
    split; [exact Hlife|]. split; [exact Ha|].
    destruct (k <? n) eqn:E; intros i Hi.
    + apply Z.ltb_lt in E. destruct (Z.lt_ge_cases i k) as [Hik|Hik]; [specialize (Hpos i ltac:(lia)); lia|].
      replace i with k by lia. rewrite (Hnul E). lia.
    + specialize (Hpos i ltac:(lia)). lia.
  - split; [|exact Hnul]. intros i Hi. specialize (Hpos i Hi). lia.
Qed.

(** A bounded zero search returns the terminator with the string's
    capability only when the terminator lies strictly before the bound.
    The function [nul_found] returns null otherwise, including when the
    bound equals the number of nonzero string bytes. *)
Definition nul_found (p : ptr) (bytes : list Z) (n : Z) : ptr :=
  if Z.of_nat (length bytes) <? n then mkPtr (ptr_addr p + Z.of_nat (length bytes)) (ptr_cap p)
  else mkPtr 0 CNone.

(** No byte before a string's terminator matches zero, so any contracted
    zero-search result must equal [nul_found] for the supplied bound. *)
Lemma memchr_result_string m p b reg bytes c n q :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) -> c mod 256 = 0 ->
  memchr_result m p c n q -> q = nul_found p bytes n.
Proof.
  intros Hok Ha H0 Hq. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  pose proof Hok as (_ & _ & _ & _ & _ & Hf). unfold memchr_result in Hq. rewrite H0 in Hq. unfold nul_found.
  assert (Hnz : forall i, 0 <= i < Z.of_nat (length bytes) -> m_bytes m (ptr_addr p + i) <> 0).
  { intros i Hi. destruct (lookup_lt_is_Some_2 bytes (Z.to_nat i) ltac:(lia)) as [x Hx].
    rewrite <- (Z2Nat.id i) by lia. rewrite (Hb (Z.to_nat i) x); [|by apply lookup_app_l_Some].
    pose proof (Forall_lookup_1 _ _ _ _ Hf Hx) as Hx0. cbv beta in Hx0. lia. }
  assert (Hz : m_bytes m (ptr_addr p + Z.of_nat (length bytes)) = 0).
  { apply (Hb (length bytes) 0). rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity. }
  destruct Hq as [(k & Hk & Hvk & Hbefore & ->) | (Hmiss & ->)].
  - assert (Hkl : k = Z.of_nat (length bytes)).
    { destruct (Z.lt_trichotomy k (Z.of_nat (length bytes))) as [Hl|[Hl|Hl]].
      - exfalso. apply (Hnz k); [lia | exact Hvk].
      - exact Hl.
      - exfalso. apply (Hbefore (Z.of_nat (length bytes))); [lia | exact Hz]. }
    subst k. rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hk)). reflexivity.
  - destruct (Z.of_nat (length bytes) <? n) eqn:E; [|reflexivity].
    apply Z.ltb_lt in E. exfalso. apply (Hmiss (Z.of_nat (length bytes))); [lia | exact Hz].
Qed.

Module LibcMemLogicOn (R : Runtime) (LG0 : LogicSig R).
Include MemLogicOn R LG0.
Module Export CSL := LibcStringLogicOn R LG0.
Module CE := LibcCallsOn R LG0.L.M.
Import L LG SL.

Section mem.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

Section calls.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The instance [libc_mem_irisGS] equips these memory rules with the chosen
    contract registry and the interpretation of external-library state. *)
Local Instance libc_mem_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The notation [mexpr] names expressions in this language, keeping
    the selected contract registry implicit in the memory rules below. *)
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

(** Calling memset fills an owned block with the character's low byte,
    clears touched pointer capabilities, and returns the destination pointer.
    The rule [wp_memset] requires an eight-byte-aligned base and offset,
    ownership of the bytes and shadow slots, and sufficient object bounds.
    The caller must also show that this fill preserves the chosen
    interpretation of external-library state. *)
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
    destruct (CE.memset_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & p' & c' & n' & Hx & _ & Hres & He).
    injection Hx as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hps") as %Hlk.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg o xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    destruct Hold as [Hlv Hold]. cbn [agree_piece fst snd] in Hlv.
    destruct (fill_after (ls_mem σ) m' b reg o xs cs c Hd Hlv Hb8 Ho8 Hlen Hold Hres) as [Hnew Hfr].
    destruct (CE.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (CE.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
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

(** Calling malloc returns ownership of a fresh heap object whose
    requested size is rounded up to a multiple of sixteen bytes.
    The rule [wp_malloc] has no null-return case because this contract
    treats allocation refusal as a resource ending, not a return.
    The caller must show that adding the allocated object's owned
    pieces preserves its interpretation of external-library state. *)
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
    destruct (CE.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hp).
    destruct (CE.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
    destruct (CE.malloc_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & n' & Hx & _ & [(base & Hres & He) | (why & born' & He & _)]); [|discriminate He].
    injection Hx as <-. injection He as ->. destruct Hres as (Hmax & Hfr & ->).
    assert (Hex : 0 <= req_extent (heap_req 16 n)).
    { cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
    pose proof Hfr as (Hpos & Hmod & _ & Hnone & _).
    iMod (pts_alloc h (obj_ps base (heap_req 16 n)) with "Hh") as "[Hh Hps]".
    { apply obj_ps_nodup. }
    { intros l' v' Hin. destruct (h !! l') as [v0|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (obj_ps_mem _ _ _ _ Hin) (Ha l' v0 E)) as Hreg'.
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

(** Calling memcpy copies bytes and complete pointer capabilities into
    an owned destination, returns its pointer, and preserves the source ownership.
    The rule [wp_memcpy] requires distinct objects and equally sized
    blocks, with both bases and offsets aligned to eight bytes.
    Partially copied pointer slots become empty, and the caller must
    show that the destination update preserves the external-world interpretation. *)
Lemma wp_memcpy f e ls lab d vd vs vn rest j b reg o xs cs b' reg' o' c' ys ds Φ :
  registry (TAtom "memcpy") = Some (memcpy_contract world) ->
  find_fn ge (TAtom "memcpy") = None -> lookup (TAtom "memcpy") (ge_globals ge) = None ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  arg_x ge e (Arg P vs) = Some (WPtr (mkPtr (b' + o') c')) -> c' = Obj b' \/ c' = Ro b' ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  b <> b' -> b mod 8 = 0 -> o mod 8 = 0 -> b' mod 8 = 0 -> o' mod 8 = 0 -> 0 <= o -> 0 <= o' ->
  b + o + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length xs) <= r_end reg' ->
  length ys = length xs -> length cs = length xs -> length ds = length xs ->
  Forall (fun y => 0 <= y < 256) ys ->
  (forall m m' wd h, copy_result m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') (Z.of_nat (length xs)) m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o ys (copy_slots (Z.of_nat (length xs)) ds cs)) h)) ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗ live b' reg' -∗ bytes b' o' ys -∗ auxes b' o' ds -∗
  ▷ (live b reg -∗ bytes b o ys -∗ auxes b o (copy_slots (Z.of_nat (length xs)) ds cs) -∗
     live b' reg' -∗ bytes b' o' ys -∗ auxes b' o' ds -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o) (Obj b))) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memcpy")) [Arg P vd; Arg P vs; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hpd Hps Hc' Hn Hne Hb8 Ho8 Hb8' Ho8' Ho Ho' Hend Hend' Hly Hlc Hld Hy Hwi.
  iIntros "Hl Hx Hcs Hl' Hy Hds HK".
  iDestruct (block_pts b reg o xs cs with "[$Hl $Hx $Hcs]") as "Hdst".
  iDestruct (block_pts b' reg' o' ys ds with "[$Hl' $Hy $Hds]") as "Hsrc".
  iCombine "Hdst Hsrc" as "Hps".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memcpy_contract world)
            [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))]
            (pts (block_ps b reg o xs cs) ∗ pts (block_ps b' reg' o' ys ds)) with "Hps [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hpd Hps Hn; done | | |].
  - split; [right; eexists; reflexivity | exists vd, vs, vn; reflexivity].
  - iIntros (σ) "Hσ [Hdst Hsrc]". iDestruct (pts_facts with "Hσ Hdst") as %(Ha & Hd & Hfit).
    iDestruct (pts_facts with "Hσ Hsrc") as %(Ha' & _ & _). iPureIntro.
    destruct Ha as [[E L] _]. destruct Ha' as [[E' L'] Hsrc]. cbn [fst snd] in E, L, E', L'.
    apply all_agree_app in Hsrc as [Hys _].
    destruct (Hfit b reg E) as [Hb0 Hfit']. destruct (Hfit b' reg' E') as [Hb0' Hfit''].
    eexists _, _, _. split; [reflexivity|]. split; [|split; [|split]].
    + split; [lia|]. split; [lia|]. split.
      * unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
        split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
        apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
      * right. exists b. auto.
    + split; [lia|]. split; [exists b', reg'; auto|]. split.
      * apply (access_read _ b' reg'); [exact Hc' | exact E' | cbn; lia | cbn; lia | apply Z.mod_1_r].
      * intros i Hi. cbn [ptr_addr]. destruct (lookup_lt_is_Some_2 ys (Z.to_nat i) ltac:(lia)) as [y Hyi].
        destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E' L') Hys Hyi) as (Hv & _ & _).
        replace (b' + o' + i) with (b' + (o' + Z.of_nat (Z.to_nat i))) by lia. rewrite Hv.
        exact (Forall_lookup_1 _ _ _ _ Hy Hyi).
    + right. exists b'. auto.
    + right. right. cbn [ptr_addr].
      destruct (Hd b reg b' reg' (conj E L) (conj E' L') Hne); [left | right]; lia.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) [Hdst Hsrc]".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (CE.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & d' & s0 & n' & Hx & _ & Hres & He).
    injection Hx as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hdst") as %Hlk.
    iDestruct (pts_lookup with "Hh Hsrc") as %Hlk'.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg o xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    assert (Hold' : all_agree (ls_mem σ) (block_ps b' reg' o' ys ds)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk' l v Hin)). }
    destruct Hold as [Hlv Hold]. destruct Hold' as [Hlv' Hold']. cbn [agree_piece fst snd] in Hlv, Hlv'.
    destruct (copy_after (ls_mem σ) m' b reg o xs cs b' reg' o' ys ds c' Hd Hlv Hlv' Hb8 Ho8 Hb8' Ho8'
                Hly Hlc Hld Hold Hold' Hres) as [Hnew Hfr].
    destruct (CE.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (CE.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    assert (Hk : (block_ps b reg o ys (copy_slots (Z.of_nat (length xs)) ds cs)).*1 = (block_ps b reg o xs cs).*1).
    { apply block_ps_keys; [exact Hly | rewrite length_copy_slots; lia]. }
    iMod (pts_update _ _ (block_ps b reg o ys (copy_slots (Z.of_nat (length xs)) ds cs)) with "Hh Hdst")
      as "[Hh Hdst]"; [exact Hk|].
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hnk Hh]].
        -- apply elem_of_cons in Hin as [Hin|Hin].
           ++ injection Hin as -> ->. cbn [agree_piece]. exact (live_at_regions _ _ _ _ Hregs Hlv).
           ++ exact (all_agree_elem _ _ _ _ Hnew Hin).
        -- apply Hfr; [|exact (Ha l v Hh)]. intros Hk'. apply Hnk. rewrite Hk.
           cbn [fmap list_fmap fst block_ps]. right. exact Hk'.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hres Hlk Hw).
    + rewrite !block_pts. iDestruct "Hdst" as "(Hl & Hx & Hcs)". iDestruct "Hsrc" as "(Hl' & Hy & Hds)".
      iApply ("HK" with "Hl Hx Hcs Hl' Hy Hds").
Qed.

(** Calling strdup returns an owned string in a fresh heap object and
    hands the original string back unchanged; allocation refusal does not return.
    The rule [wp_strdup] requires the source object's base to be
    eight-byte aligned and the allocation to preserve the external-world interpretation.
    Its result owns the copied string and object lifetime, but not
    the fresh object's remaining bytes or shadow slots. *)
Lemma wp_strdup f e ls lab d v rest j p b reg bytes Φ :
  registry (TAtom "strdup") = Some (strdup_contract world) ->
  find_fn ge (TAtom "strdup") = None -> lookup (TAtom "strdup") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> b mod 8 = 0 ->
  (forall m m' wd h base k, strdup_result m p k base m' -> wi m wd h ->
     wi m' wd (overwrite (string_ps (mkPtr base (Obj base)) base
                            (mkRegion base (base + req_extent (heap_req 16 k)) Heap Live) bytes) h)) ->
  string p b reg bytes -∗
  ▷ (∀ base reg', string p b reg bytes -∗ string (mkPtr base (Obj base)) base reg' bytes -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j)) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "strdup")) [Arg P v] :: rest) j)) : mexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hb8 Hwi. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strdup_contract world) [WPtr p] (string p b reg bytes)
            with "Hs [HK]"); [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[Ht _].
    iDestruct "Hs" as "[%Hok _]". iPureIntro. destruct Hok as (Hc & _).
    exists p, (Z.of_nat (length bytes)). split; [reflexivity|]. split; [exact Ht|]. exists b. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) [%Hok Hs]".
    destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Hs") as %Hlk.
    assert (Hold : all_agree (ls_mem σ) (string_ps p b reg bytes)).
    { apply all_agree_intro. intros l v' Hin. exact (Ha l v' (Hlk l v' Hin)). }
    pose proof (string_terminated _ _ _ _ _ Hok Hold) as Ht.
    pose proof (string_bytes _ _ _ _ _ Hok Hold) as Hbs.
    destruct (CE.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hp).
    destruct (CE.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
    destruct (CE.strdup_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & p' & k & Hx & (Hk & _) & [(base & Hres & He) | (why & born' & He & _)]); [|discriminate He].
    injection Hx as <-. injection He as ->. rewrite <- (terminated_length_unique _ _ _ _ Ht Hk) in Hres.
    set (n := Z.of_nat (length bytes)) in *.
    pose proof (malloc_extent (n + 1) ltac:(unfold n; lia)) as Hext.
    assert (Hn0 : 0 <= n) by (unfold n; lia).
    set (q := heap_req 16 (n + 1)) in *.
    set (reg' := mkRegion base (base + req_extent q) Heap Live).
    destruct Hres as [(Hmax & Hfr & _) Hcopy].
    pose proof Hfr as (Hpos & Hmod & _ & Hnone & _).
    pose proof Hcopy as ((Hregs & Hbytes & Haux) & Hcb & _).
    set (m1 := allocated (ls_mem σ) q base) in *.
    assert (Hl1 : live_at m1 base reg').
    { split; [|reflexivity]. unfold m1. rewrite object_region_allocated Z.eqb_refl. reflexivity. }
    assert (Hd1 : live_disjoint m1).
    { apply live_disjoint_allocated; [exact Hd | exact Hfr | lia]. }
    assert (Hout : forall a, ~ (base <= a < r_end reg') ->
              m_bytes m' a = m_bytes m1 a /\ m_aux m' a = m_aux m1 a).
    { intros a Ha'. cbn [r_end reg'] in Ha'. split.
      - apply Hbytes. unfold span_contains. cbn. lia.
      - apply Haux. destruct (memset_touched _ _ a) eqn:Ht'; [|reflexivity]. exfalso.
        apply memset_touched_spec in Ht' as (_ & Ha8 & Hhi & Hlo). cbn [ptr_addr] in Hhi, Hlo.
        assert (Hb16 : base mod 8 = 0) by exact (fresh_heap_aligned8 _ _ _ Hfr).
        pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod base 8 ltac:(lia)). lia. }
    iMod (pts_alloc h (string_ps (mkPtr base (Obj base)) base reg' bytes) with "Hh") as "[Hh Hnew]".
    { apply string_ps_nodup. }
    { intros l' v' Hin. destruct (h !! l') as [v0|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (string_ps_mem _ _ _ _ _ _ Hin) (Ha l' v0 E)) as Hreg'.
      rewrite (string_ps_id _ _ _ _ _ _ Hin) in Hreg'. exact (Hreg' Hnone). }
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l' v' Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]].
        -- apply elem_of_cons in Hin as [Hin|Hin].
           ++ injection Hin as -> ->. cbn [agree_piece]. unfold live_at. rewrite Hregs. exact Hl1.
           ++ cbn [ptr_addr] in Hin. rewrite Z.sub_diag in Hin.
              apply byte_ps_elem in Hin as (i & x & Hxi & -> & ->). cbn [agree_piece].
              assert (Hi : (i <= length bytes)%nat).
              { apply lookup_lt_Some in Hxi. rewrite length_app in Hxi. cbn in Hxi. lia. }
              split; [unfold registered; rewrite Hregs; destruct Hl1 as [E _]; rewrite E; discriminate|].
              intros reg0 E L. rewrite Hregs in E. destruct Hl1 as [E1 _]. rewrite E1 in E.
              injection E as <-. cbn [r_end reg']. split; [lia|]. split; [lia|].
              rewrite Hcb; [|unfold span_contains; cbn; lia]. cbn [ptr_addr].
              replace (base + (0 + Z.of_nat i) - base) with (Z.of_nat i) by lia.
              exact (Hbs i x Hxi).
        -- apply (frame_other m1 m' base reg'); [exact Hregs | exact Hd1 | exact Hl1 | exact Hout | |].
           ++ intros Hm Hid. pose proof (agree_piece_registered _ _ _ Hm (Ha l' v' Hh)) as Hreg'.
              rewrite Hid in Hreg'. exact (Hreg' Hnone).
           ++ exact (agree_piece_allocated _ _ _ _ _ Hnone (Ha l' v' Hh)).
      * exact (live_disjoint_regions _ _ Hregs Hd1).
      * exact Hr'.
      * exact (Hwi _ _ _ _ _ _ (conj (conj Hmax (conj Hfr eq_refl)) Hcopy) Hw).
    + iApply ("HK" with "[Hs] [Hnew]").
      * iSplit; [iPureIntro; exact Hok | iExact "Hs"].
      * iSplit; [|iExact "Hnew"]. iPureIntro. unfold string_ok. cbn [ptr_cap ptr_addr r_end reg'].
        destruct Hok as (_ & _ & _ & _ & _ & Hf).
        destruct (R.address_space _ _ Hr' base reg') as [_ Hend];
          [rewrite Hregs; exact (proj1 Hl1)|].
        cbn [r_end reg'] in Hend. split; [left; reflexivity|]. repeat split; try lia. exact Hf.
Qed.

(** A scalar string copy turns destination byte ownership into an
    owned string, including its terminator, and preserves the source string.
    The rule [wp_string_copy] returns either the destination pointer or
    its terminating NUL pointer, according to the selected copy contract.
    Owning both object lifetimes forces distinct objects, while preserving
    every shadow slot removes the need for shadow ownership or alignment.
    The caller supplies enough destination bytes and proves that the
    copy preserves its interpretation of external-library state. *)
Lemma wp_string_copy end_return g f e ls lab d vd vs rest j b reg o xs src b' reg' ys Φ :
  registry g = Some (string_copy_contract end_return world) ->
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg P vs) = Some (WPtr src) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> length xs = S (length ys) ->
  (forall m m' wd h, string_copy_result m (mkPtr (b + o) (Obj b)) src (Z.of_nat (length ys) + 1) m' ->
     (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (byte_ps b o (ys ++ [0])) h)) ->
  live b reg -∗ bytes b o xs -∗ string src b' reg' ys -∗
  ▷ (string (mkPtr (b + o) (Obj b)) b reg ys -∗ string src b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WPtr (copy_return end_return (mkPtr (b + o) (Obj b))
                                         (Z.of_nat (length ys)))) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global g) [Arg P vd; Arg P vs] :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hfree Hpd Hps Hb0 Ho Hend Hlen Hwi. iIntros "Hl Hx Hs HK".
  iDestruct (live_string_ne with "Hl Hs") as %Hne.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (string_copy_contract end_return world)
            [WPtr (mkPtr (b + o) (Obj b)); WPtr src] (live b reg ∗ bytes b o xs ∗ string src b' reg' ys)
            with "[$Hl $Hx $Hs] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hpd Hps; done | | |].
  - split; [right; eexists; reflexivity | exists vd, vs; reflexivity].
  - iIntros (σ) "Hσ (Hl & _ & [%Hok Hs])".
    iDestruct (pts_facts with "Hσ Hl") as %(Hal & Hd & _).
    iDestruct (pts_facts with "Hσ Hs") as %(Has & _ & _). iPureIntro.
    pose proof (string_terminated _ _ _ _ _ Hok Has) as Ht.
    destruct Hal as [[E L] _]. destruct Has as [[E' L'] _]. cbn [fst snd] in E, L, E', L'.
    exists (mkPtr (b + o) (Obj b)), src, (Z.of_nat (length ys)). split; [reflexivity|].
    split; [exact Ht|]. split.
    + unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
      split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
      apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
    + cbn [ptr_addr]. destruct Hok as (_ & _ & Hs1 & Hs2 & _).
      destruct (Hd b reg b' reg' (conj E L) (conj E' L') Hne); [left | right]; lia.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) (Hl & Hx & [%Hok Hs])".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (CE.string_copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & d' & src' & k & Hx' & Hdom & Hres & He).
    injection Hx' as <- <-.
    iDestruct (pts_lookup with "Hh Hl") as %Hll.
    iDestruct (pts_lookup with "Hh Hx") as %Hlx.
    iDestruct (pts_lookup with "Hh Hs") as %Hls.
    assert (Hlv : live_at (ls_mem σ) b reg).
    { apply (Ha (PLive b) (VLive reg)). apply Hll. apply elem_of_cons. left. reflexivity. }
    assert (Hx0 : all_agree (ls_mem σ) (byte_ps b o xs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlx l v Hin)). }
    assert (Hs0 : all_agree (ls_mem σ) (string_ps src b' reg' ys)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hls l v Hin)). }
    pose proof (string_terminated _ _ _ _ _ Hok Hs0) as Ht.
    assert (k = Z.of_nat (length ys)) as ->.
    { exact (terminated_length_unique _ _ _ _ (proj1 Hdom) Ht). }
    injection He as ->.
    destruct (copy_string_after (ls_mem σ) m' b reg o xs src b' reg' ys Hd Hlv Hx0 Hlen Hok Hs0 Hres)
      as [Hnew Hfr].
    destruct (CE.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (CE.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    destruct (R.address_space _ _ Hr b reg (proj1 Hlv)) as [_ Hfit].
    assert (Hok' : string_ok (mkPtr (b + o) (Obj b)) b reg ys).
    { unfold string_ok. cbn [ptr_cap ptr_addr]. destruct Hok as (_ & _ & _ & _ & _ & Hf).
      split; [left; reflexivity|]. repeat split; try lia. exact Hf. }
    assert (Hk : (byte_ps b o (ys ++ [0])).*1 = (byte_ps b o xs).*1).
    { rewrite !byte_ps_keys length_app Hlen. cbn [length]. rewrite Nat.add_1_r. reflexivity. }
    iMod (pts_update _ (byte_ps b o xs) (byte_ps b o (ys ++ [0])) Hk with "Hh Hx") as "[Hh Hx]".
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hnk Hh']].
        -- exact (all_agree_elem _ _ _ _ Hnew Hin).
        -- apply Hfr; [|exact (Ha l v Hh')]. rewrite <- Hk. exact Hnk.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hres Hlx Hw).
    + iApply ("HK" with "[Hl Hx] [Hs]").
      * iApply (block_string _ _ _ _ Hok' with "Hl Hx").
      * iSplit; [iPureIntro; exact Hok | iExact "Hs"].
Qed.

(** Calling strcpy uses the scalar string-copy rule and binds the
    result to the destination pointer, as [wp_strcpy] specializes the general contract. *)
Lemma wp_strcpy f e ls lab d vd vs rest j b reg o xs src b' reg' ys Φ :
  registry (TAtom "strcpy") = Some (strcpy_contract world) ->
  find_fn ge (TAtom "strcpy") = None -> lookup (TAtom "strcpy") (ge_globals ge) = None ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg P vs) = Some (WPtr src) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> length xs = S (length ys) ->
  (forall m m' wd h, string_copy_result m (mkPtr (b + o) (Obj b)) src (Z.of_nat (length ys) + 1) m' ->
     (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (byte_ps b o (ys ++ [0])) h)) ->
  live b reg -∗ bytes b o xs -∗ string src b' reg' ys -∗
  ▷ (string (mkPtr (b + o) (Obj b)) b reg ys -∗ string src b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o) (Obj b))) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "strcpy")) [Arg P vd; Arg P vs] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hpd Hps Hb0 Ho Hend Hlen Hwi. iIntros "Hl Hx Hs HK".
  iApply (wp_string_copy false (TAtom "strcpy") with "Hl Hx Hs HK"); done.
Qed.

(** Calling stpcpy uses the scalar string-copy rule but returns the
    copied terminator's pointer, as [wp_stpcpy] specializes the general contract. *)
Lemma wp_stpcpy f e ls lab d vd vs rest j b reg o xs src b' reg' ys Φ :
  registry (TAtom "stpcpy") = Some (stpcpy_contract world) ->
  find_fn ge (TAtom "stpcpy") = None -> lookup (TAtom "stpcpy") (ge_globals ge) = None ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg P vs) = Some (WPtr src) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> length xs = S (length ys) ->
  (forall m m' wd h, string_copy_result m (mkPtr (b + o) (Obj b)) src (Z.of_nat (length ys) + 1) m' ->
     (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (byte_ps b o (ys ++ [0])) h)) ->
  live b reg -∗ bytes b o xs -∗ string src b' reg' ys -∗
  ▷ (string (mkPtr (b + o) (Obj b)) b reg ys -∗ string src b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o + Z.of_nat (length ys)) (Obj b))) e) ls None
                 (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "stpcpy")) [Arg P vd; Arg P vs] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hpd Hps Hb0 Ho Hend Hlen Hwi. iIntros "Hl Hx Hs HK".
  iApply (wp_string_copy true (TAtom "stpcpy") with "Hl Hx Hs HK"); done.
Qed.

(** Calling memcmp preserves both owned byte ranges and returns an
    integer, but [wp_memcmp] does not specify that integer's sign or value.
    This rule requires equally sized readable ranges and supports
    safety proofs that handle every comparison result without assuming an ordering. *)
Lemma wp_memcmp f e ls lab d vp vq vn rest j b reg o xs c b' reg' o' ys c' Φ :
  registry (TAtom "memcmp") = Some (memcmp_contract world) ->
  find_fn ge (TAtom "memcmp") = None -> lookup (TAtom "memcmp") (ge_globals ge) = None ->
  arg_x ge e (Arg P vp) = Some (WPtr (mkPtr (b + o) c)) -> c = Obj b \/ c = Ro b ->
  arg_x ge e (Arg P vq) = Some (WPtr (mkPtr (b' + o') c')) -> c' = Obj b' \/ c' = Ro b' ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) -> length ys = length xs ->
  0 <= o -> 0 <= o' -> b + o + Z.of_nat (length xs) <= r_end reg ->
  b' + o' + Z.of_nat (length xs) <= r_end reg' ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
  live b reg -∗ bytes b o xs -∗ live b' reg' -∗ bytes b' o' ys -∗
  ▷ (∀ bits, live b reg -∗ bytes b o xs -∗ live b' reg' -∗ bytes b' o' ys -∗
     WP (ERun (mkFrame f (put d (WInt bits) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "memcmp")) [Arg P vp; Arg P vq; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hp Hc Hq Hc' Hn Hlen Ho Ho' Hend Hend' Hx Hy.
  iIntros "Hl Hx Hl' Hy HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memcmp_contract world)
            [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))]
            (live b reg ∗ bytes b o xs ∗ live b' reg' ∗ bytes b' o' ys) with "[$Hl $Hx $Hl' $Hy] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hp Hq Hn; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ (Hl & Hx & Hl' & Hy)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit).
    iDestruct (pts_facts with "Hσ Hx") as %(Hxa & _).
    iDestruct (pts_facts with "Hσ Hl'") as %([Hlv' _] & _ & _).
    iDestruct (pts_facts with "Hσ Hy") as %(Hya & _). iPureIntro. cbn [fst snd agree_piece] in Hlv, Hlv'.
    exists (mkPtr (b + o) c), (mkPtr (b' + o') c'), (Z.of_nat (length xs)). split; [reflexivity|].
    split; [exact (proj1 (block_readable _ _ _ _ _ _ Hlv Hxa Hfit Hc Ho Hend Hx))|].
    rewrite <- Hlen. rewrite <- Hlen in Hend'.
    exact (proj1 (block_readable _ _ _ _ _ _ Hlv' Hya Hfit Hc' Ho' Hend' Hy)).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ (Hl & Hx & Hl' & Hy)".
    destruct (CE.memcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & q' & n' & bits & Hxs & _ & He). injection He as ->.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ". iApply ("HK" with "Hl Hx Hl' Hy").
Qed.

(** Calling memchr preserves the owned byte range and returns its first
    match for the argument's low byte, or null when no match exists.
    The rule [wp_memchr] retains the input capability in a matching
    pointer and accepts either writable or read-only access to the range. *)
Lemma wp_memchr f e ls lab d vp vk vn rest j b reg o xs c k Φ :
  registry (TAtom "memchr") = Some (memchr_contract world) ->
  find_fn ge (TAtom "memchr") = None -> lookup (TAtom "memchr") (ge_globals ge) = None ->
  arg_x ge e (Arg P vp) = Some (WPtr (mkPtr (b + o) c)) -> c = Obj b \/ c = Ro b ->
  arg_x ge e (Arg W vk) = Some (WInt k) -> 0 <= k < 2 ^ 32 ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> Forall (fun x => 0 <= x < 256) xs ->
  live b reg -∗ bytes b o xs -∗
  ▷ (∀ q, ⌜strchr_found (mkPtr (b + o) c) xs k q⌝ -∗ live b reg -∗ bytes b o xs -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memchr")) [Arg P vp; Arg W vk; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hp Hc Hk Hk32 Hn Ho Hend Hx. iIntros "Hl Hx HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memchr_contract world)
            [WPtr (mkPtr (b + o) c); WInt k; WInt (Z.of_nat (length xs))]
            (live b reg ∗ bytes b o xs) with "[$Hl $Hx] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hp Hk Hn; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ (Hl & Hx)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit).
    iDestruct (pts_facts with "Hσ Hx") as %(Hxa & _). iPureIntro. cbn [fst snd agree_piece] in Hlv.
    do 3 eexists. split; [reflexivity|]. apply memchr_input_full; [exact Hk32|].
    exact (proj1 (block_readable _ _ _ _ _ _ Hlv Hxa Hfit Hc Ho Hend Hx)).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ (Hl & Hx)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit).
    iDestruct (pts_facts with "Hσ Hx") as %(Hxa & _). cbn [fst snd agree_piece] in Hlv.
    destruct (block_readable _ _ _ _ _ _ Hlv Hxa Hfit Hc Ho Hend Hx) as [_ Hv].
    destruct (CE.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & k' & n' & q & Hxs & Hq & He). injection Hxs as <- <- <-. injection He as ->.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ".
    iApply ("HK" with "[%] Hl Hx"). cbn [ptr_addr ls_mem] in Hq, Hv.
    destruct Hq as [(i & Hi & Hvi & Hbefore & ->) | (Hnone & ->)].
    + left. destruct (lookup_lt_is_Some_2 xs (Z.to_nat i) ltac:(lia)) as [x Hxi].
      exists (Z.to_nat i), x. split; [exact Hxi|]. split.
      * rewrite <- Hvi. rewrite <- (Hv _ _ Hxi). rewrite Z2Nat.id; [reflexivity|lia].
      * split; [|cbn [ptr_addr ptr_cap]; rewrite Z2Nat.id; [reflexivity|lia]].
        intros i' x' Hlt Hx'. rewrite <- (Hv _ _ Hx'). apply Hbefore. lia.
    + right. split; [|reflexivity]. intros i' x' Hx'. rewrite <- (Hv _ _ Hx').
      apply Hnone. split; [lia|]. apply lookup_lt_Some in Hx'. lia.
Qed.

(** Searching an owned string for zero returns its NUL before the
    bound, or null when the bound excludes that byte.
    The rule [wp_memchr_string] preserves string ownership and permits
    a bound beyond the enclosing object because no read follows the first match. *)
Lemma wp_memchr_string f e ls lab d vp vk vn rest j p b reg bytes k n Φ :
  registry (TAtom "memchr") = Some (memchr_contract world) ->
  find_fn ge (TAtom "memchr") = None -> lookup (TAtom "memchr") (ge_globals ge) = None ->
  arg_x ge e (Arg P vp) = Some (WPtr p) ->
  arg_x ge e (Arg W vk) = Some (WInt k) -> 0 <= k < 2 ^ 32 -> k mod 256 = 0 ->
  arg_x ge e (Arg L vn) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  string p b reg bytes -∗
  ▷ (string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WPtr (nul_found p bytes n)) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memchr")) [Arg P vp; Arg W vk; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hp Hk Hk32 H0 Hn Hn64. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memchr_contract world)
            [WPtr p; WInt k; WInt n] (string p b reg bytes) with "Hs [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hp Hk Hn; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ [%Hok Hs]". iDestruct (pts_facts with "Hσ Hs") as %(Ha & _). iPureIntro.
    do 3 eexists. split; [reflexivity|].
    exact (memchr_input_bounded _ _ _ _ _ Hk32 H0 (string_bounded _ _ _ _ _ n Hok Ha Hn64)).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ [%Hok Hs]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _).
    destruct (CE.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & k' & n' & q & Hxs & Hq & He). injection Hxs as <- <- <-. injection He as ->.
    rewrite (memchr_result_string _ _ _ _ _ _ _ _ Hok Ha H0 Hq).
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ". iApply "HK". by iSplit.
Qed.

End calls.
End mem.
End LibcMemLogicOn.

Module LibcMemLogic (R : Runtime).
Module LG0 := Logic R.
Include LibcMemLogicOn R LG0.
End LibcMemLogic.
