(** In glibc under Fil-C, `c: memset`, `c: memcpy`, `c: mempcpy`, and
    `c: strdup` delegate bulk memory operations to libpizlo's runtime
    primitives `c: zmemset` and `c: zmemmove`. This module proves
    [[weakest-precondition]] call specifications for all four functions
    over [os_world] and any registry holding the OS contracts for those
    two primitives.

    Each function updates or allocates memory in a straightforward way.
    First, `c: memset` fills an owned byte block and returns the
    destination pointer. Next, `c: memcpy` and `c: mempcpy` copy bytes
    from a source owned at any share into an owned destination, returning
    either the destination or the pointer just past it. Because the
    caller supplies only byte ownership for the source, the destination's
    [[aux]] capability slots afterward hold whatever the copy wrote.
    Finally, `c: strdup` combines `c: strlen`, `c: malloc`, and
    `c: memcpy` to duplicate a [word_string] into a [[fresh]] object,
    assuming a `c: malloc` contract that returns null or a fresh
    16-aligned allocation. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenWord OsWorld OsRegistry MemFwdCode.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The effects

    When `c: memcpy` copies bytes from a source buffer whose capability
    slots are not tracked, the destination's [[aux]] slots afterward
    cannot be predicted from the source's logical value. We record the
    actual post-copy capability slots directly from physical memory so
    the caller keeps full ownership of the destination block. *)

(** Function [aux_now] reads the n physical [[aux]] capability slots
    starting at offset o of object b in memory m. *)
Definition aux_now (m : mem) (b o : Z) (n : nat) : list cap :=
  map (fun i => m_aux m (b + (o + Z.of_nat i))) (seq 0 n).

(** The list returned by [aux_now] always has length n. *)
Lemma length_aux_now m b o n : length (aux_now m b o n) = n.
Proof. unfold aux_now. by rewrite length_map length_seq. Qed.

(** Copying n bytes ys into an 8-aligned destination block overwrites
    its bytes with ys, leaves its capability slots at [aux_now], and
    preserves memory agreement for every piece outside the block. *)
Lemma copy_after_any m m' b reg o xs cs b' reg' o' ys c' :
  live_disjoint m -> live_at m b reg -> live_at m b' reg' -> b mod 8 = 0 -> o mod 8 = 0 ->
  length ys = length xs -> length cs = length xs ->
  all_agree m (byte_ps b o xs ++ aux_ps b o cs) -> all_agree m (byte_ps b' o' ys) ->
  copy_result m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') (Z.of_nat (length xs)) m' ->
  all_agree m' (byte_ps b o ys ++ aux_ps b o (aux_now m' b o (length xs))) /\
  frame_ok (byte_ps b o xs ++ aux_ps b o cs).*1 m m'.
Proof.
  intros Hd Hl Hl' Hb8 Ho8 Hly Hlc Hdst Hy Hres.
  pose proof Hres as (Hfr & Hcb & _). pose proof Hfr as (Hr & _ & _).
  split; [|exact (block_frame _ _ _ _ _ _ _ Hd Hl Hb8 Ho8 Hlc Hdst Hfr)].
  apply all_agree_app in Hdst as [Hx _]. destruct Hl as [E0 L0].
  assert (Hreg : registered m' b) by (unfold registered; rewrite Hr E0; discriminate).
  assert (Hbyte : forall i, (i < length xs)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E0 L0) Hx Hxi) as (_ & H1 & H2). lia. }
  apply all_agree_app. split; apply all_agree_intro; intros l v Hin.
  - apply byte_ps_elem in Hin as (i & y & Hyi & -> & ->).
    assert (Hi : (i < length xs)%nat) by (rewrite <- Hly; exact (lookup_lt_Some _ _ _ Hyi)).
    destruct (Hbyte i Hi) as [H1 H2]. cbn [agree_piece]. split; [exact Hreg|].
    intros reg0 E L. rewrite Hr E0 in E. injection E as <-. split; [exact H1|]. split; [exact H2|].
    rewrite Hcb; [|unfold span_contains; cbn; lia]. cbn [ptr_addr].
    replace (b' + o' + (b + (o + Z.of_nat i) - (b + o))) with (b' + (o' + Z.of_nat i)) by lia.
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl' Hy Hyi) as (Hv & _ & _). exact Hv.
  - apply aux_ps_elem in Hin as (i & c & Hci & -> & ->).
    unfold aux_now in Hci. change (map ?f ?l) with (f <$> l) in Hci.
    apply list_lookup_fmap_Some in Hci as (k & -> & Hk).
    pose proof (lookup_lt_Some _ _ _ Hk) as Hi. rewrite length_seq in Hi.
    rewrite lookup_seq_lt in Hk; [injection Hk as <- | exact Hi]. cbn [agree_piece]. split; [exact Hreg|].
    destruct (Hbyte i ltac:(lia)) as [H1 H2].
    intros reg0 E L. rewrite Hr E0 in E. injection E as <-. split; [exact H1|]. split; [exact H2|].
    left. reflexivity.
Qed.

(** ## World invariant preservation

    Because `c: zmemset` and `c: zmemmove` only overwrite bytes and
    capability slots inside a live object without altering [[region]]
    registrations, they preserve the OS world invariant [os_wi]. This
    section proves that preservation lemma along with two small
    alignment and arithmetic facts needed by `c: strdup`. *)

(** When `c: memset` or `c: memcpy` updates a single object's bytes and
    capability slots without changing any [[region]] registrations,
    [os_wi_block] shows that the OS world invariant still holds. *)
Lemma os_wi_block w0 m m' w h b reg o xs cs ys ds :
  m_regions m' = m_regions m -> (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) ->
  os_wi w0 m w h -> os_wi w0 m' w (overwrite (block_ps b reg o ys ds) h).
Proof.
  intros E Hlk. apply os_wi_store; [exact E|]. intros l v Hin. unfold block_ps in Hin.
  apply elem_of_cons in Hin as [[= -> ->] | Hin].
  - apply Hlk. unfold block_ps. apply elem_of_cons. by left.
  - apply elem_of_app in Hin as [Hin|Hin];
      [apply byte_ps_elem in Hin as (? & ? & _ & -> & _) | apply aux_ps_elem in Hin as (? & ? & _ & -> & _)];
      exact I.
Qed.

(** Any integer divisible by 16 is also divisible by 8, which lets
    `c: strdup` pass a 16-aligned `c: malloc` buffer to `c: memcpy`. *)
Lemma mod16_mod8 z : z mod 16 = 0 -> z mod 8 = 0.
Proof.
  intros H. rewrite (Z.div_mod z 16); [|lia]. rewrite H Z.add_0_r.
  replace (16 * (z / 16)) with (2 * (z / 16) * 8) by lia. apply Z_mod_mult.
Qed.

(** Adding two non-negative integers whose sum fits below `2 ^ 64`
    matches modular 64-bit pointer addition. *)
Lemma add_small a n : 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> (a mod 2 ^ 64 + n mod 2 ^ 64) mod 2 ^ 64 = a + n.
Proof. intros. rewrite !Z.mod_small; lia. Qed.

(** ## A string's bytes

    String-search functions read a [word_string] as 8-byte [[word|words]],
    whereas `c: memcpy` operates on a byte-indexed slice. We bridge the
    two representations by showing that word pieces and byte pieces
    describe the exact same locations in memory. *)

(** Splitting each 8-byte word into its eight bytes turns [words_ps]
    into [byte_ps] at the same offset. *)
Lemma words_ps_bytes b o ws : words_ps b o ws = byte_ps b o (wbytes ws).
Proof.
  revert o. induction ws as [|w ws IH]; intros o; [reflexivity|].
  cbn [words_ps]. rewrite wbytes_cons byte_ps_app IH.
  unfold cell. cbn [List.map]. rewrite !byte_ps_cons. unfold byte_ps. cbn. repeat (f_equal; try lia).
Qed.

(** ## Over a Logic instance

    To connect the physical memory lemmas above to C call sites, we
    instantiate the program logic over `os_world` and prove
    specifications for `c: zmemset` and `c: zmemmove`. We then compose
    those primitives to verify `c: memset`, `c: memcpy`, `c: mempcpy`,
    and `c: strdup`. *)

(** This functor packages the forward memory-function specifications
    over a [[runtime]] R and a program logic instance LG0. *)
Module MemFwdLogicOn (R : Runtime) (LG0 : LogicSig R).
Module ML := MemLogicOn R LG0.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Module OW := OsWorldOn R LG0.
Module SW := StrlenWordOn R LG0.
Import L LG SL ML.

(** Wrapping a contract with [void_only] restricts its ABI to void
    calls, so any invocation of the wrapped contract also satisfies the
    original contract c. *)
Lemma invoke_void_only {world} (c : contract world) r args xs s m w trace en s' m' w' :
  M.E.invoke (void_only c) r args xs s m w trace en s' m' w' -> M.E.invoke c r args xs s m w trace en s' m' w'.
Proof.
  intros H. destruct H as [trace en s' m' w' born Habi Hpre Hp Hpost Hr Hv Hx
                         | why trace s' m' w' born Habi Hpre Hp Hf Hres].
  - eapply M.E.invoke_normal; [exact (proj2 Habi) | exact Hpre | exact Hp | exact Hpost | exact Hr | exact Hv | exact Hx].
  - eapply M.E.invoke_resource; [exact (proj2 Habi) | exact Hpre | exact Hp | exact Hf | exact Hres].
Qed.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The functor assumes the external registry provides void-only OS
    contracts for `c: zmemset` and `c: zmemmove` and that neither name
    collides with an internal function or global. *)
Context (Hset : registry (TAtom "zmemset") = Some (void_only (memset_contract os_world)))
  (Hset_fn : find_fn ge (TAtom "zmemset") = None) (Hset_sym : lookup (TAtom "zmemset") (ge_globals ge) = None)
  (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None) (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).

(** The OS world invariant `os_wi w0` remains stable across runtime
    safepoints. *)
Local Instance memfwd_stable : SafepointStable (os_wi w0) := OW.os_wi_stable w0.
(** To step through IR instructions in [[separation-logic|separation logic]],
    [memfwd_irisGS] connects the contract registry and the OS world
    invariant to the Iris program logic. *)
Local Instance memfwd_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry (os_wi w0) ge.
(** This shorthand names the expression type of the instantiated
    language. *)
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

(** To pass a string to `c: memcpy`, [word_string_bytes] extracts the
    fractional live [[region]] and byte pieces for `s ++ [0]` from a
    [word_string] and returns a wand that reassembles them. *)
Lemma word_string_bytes dq p s :
  word_string dq p s ⊢ ∃ b reg ws, ⌜str_shape p b reg ws s⌝ ∗ liveq dq b reg ∗
    bytesq dq b (ptr_addr p - b) (s ++ [0]) ∗
    (liveq dq b reg -∗ bytesq dq b (ptr_addr p - b) (s ++ [0]) -∗ word_string dq p s).
Proof.
  iIntros "(%b & %reg & %ws & %Hs & Hl & Hw)". iExists b, reg, ws. iSplit; [done|].
  pose proof Hs as [_ _ _ _ _ _ Hlen _ Hby _].
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)) as Hk.
  set (k := Z.to_nat (ptr_addr p mod 8)) in *. set (W := wbytes ws).
  assert (Hlk : length (take k W) = k).
  { apply length_take_le. unfold W. rewrite wbytes_length. apply Nat2Z.inj_le. rewrite Nat2Z.inj_mul Hlen.
    pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). unfold k. lia. }
  assert (E : W = take k W ++ (s ++ [0]) ++ drop (S (length s)) (drop k W)).
  { rewrite -Hby take_drop take_drop. reflexivity. }
  assert (Ho : wstart p - b + Z.of_nat k = ptr_addr p - b) by (unfold wstart, k; lia).
  iEval (rewrite words_ps_bytes -/W E (byte_ps_app _ _ (take k W)) (byte_ps_app _ _ (s ++ [0])) ptsq_app ptsq_app Hlk Ho) in "Hw".
  iDestruct "Hw" as "(Hpre & Hx & Hpost)". iFrame "Hl Hx". iIntros "Hl Hx".
  iExists b, reg, ws. iSplit; [done|]. rewrite /wwin.
  iEval (rewrite words_ps_bytes -/W E (byte_ps_app _ _ (take k W)) (byte_ps_app _ _ (s ++ [0])) ptsq_app ptsq_app
           Hlk Ho). iFrame.
Qed.

(** Calling `c: zmemset` on an 8-aligned owned block fills its bytes
    with `c mod 256` and clears any touched capability slots via
    [clear_slots]. *)
Lemma wp_zmemset f e ls lab vp vc vn rest j b reg o xs cs c Φ :
  arg_x ge e (Arg P vp) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg W vc) = Some (WInt c) ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  0 <= c < 2 ^ 32 -> b mod 8 = 0 -> o mod 8 = 0 -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg ->
  length cs = length xs ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗
  ▷ (live b reg -∗ bytes b o (replicate (length xs) (c mod 256)) -∗ auxes b o (clear_slots o cs) -∗
     WP (ERun (mkFrame f e ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zmemset")) [Arg P vp; Arg W vc; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hp Hc Hn Hc32 Hb8 Ho8 Ho Hend Hlen. iIntros "Hl Hx Hcs HK".
  iDestruct (block_pts b reg o xs cs with "[$Hl $Hx $Hcs]") as "Hps".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (void_only (memset_contract os_world))
            [WPtr (mkPtr (b + o) (Obj b)); WInt c; WInt (Z.of_nat (length xs))] (pts (block_ps b reg o xs cs))
            with "Hps [HK]");
    [exact Hset_fn | exact Hset_sym | reflexivity | exact Hset | cbn [map_option]; rewrite Hp Hc Hn; done | | |].
  - split; [reflexivity|]. split; [left; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hps". iDestruct (pts_facts with "Hσ Hps") as %(Ha & _ & Hfit). iPureIntro.
    destruct Ha as [[E L] _]. cbn [fst snd] in E, L. destruct (Hfit b reg E) as [Hb0 Hfit'].
    eexists _, c, _. split; [reflexivity|]. split; [exact Hc32|]. split; [lia|]. split.
    + unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
      split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
      apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
    + right. exists b. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hps".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.memset_invocation _ _ _ _ _ _ _ _ _ _ _ _ (invoke_void_only _ _ _ _ _ _ _ _ _ _ _ _ Hinv))
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
           rewrite (block_ps_keys b reg o xs cs); [|apply length_replicate | apply length_clear_slots].
           cbn [fmap list_fmap fst block_ps]. right. exact Hk.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (os_wi_block _ _ _ _ _ _ _ _ _ _ _ _ Hregs Hlk Hw).
    + rewrite block_pts. iDestruct "Hps" as "(Hl & Hx & Hcs)". iApply ("HK" with "Hl Hx Hcs").
Qed.

(** Calling `c: zmemmove` from a fractionally owned source slice `ys`
    into a distinct 8-aligned owned destination block overwrites the
    destination bytes with `ys`, leaves its capability slots as an
    arbitrary list of the same length, and restores the source
    resources. *)
Lemma wp_zmemmove f e ls lab vd vs vn rest j b reg o xs cs dq b' reg' o' c' ys Φ :
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  arg_x ge e (Arg P vs) = Some (WPtr (mkPtr (b' + o') c')) -> c' = Obj b' \/ c' = Ro b' ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  b mod 8 = 0 -> o mod 8 = 0 -> b' mod 8 = 0 -> 0 <= o -> 0 <= o' ->
  b + o + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length xs) <= r_end reg' ->
  length ys = length xs -> length cs = length xs -> Forall (fun y => 0 <= y < 256) ys ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
  ▷ (live b reg -∗ bytes b o ys -∗ (∃ cs', ⌜length cs' = length xs⌝ ∗ auxes b o cs') -∗
     liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
     WP (ERun (mkFrame f e ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zmemmove")) [Arg P vd; Arg P vs; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hpd Hps Hc' Hn Hb8 Ho8 Hb8' Ho Ho' Hend Hend' Hly Hlc Hy. iIntros "Hl Hx Hcs Hl' Hy HK".
  iAssert (⌜b <> b'⌝)%I as %Hne.
  { rewrite /live /liveq /pts /ptsq !big_sepL_singleton. cbn [fst snd].
    iDestruct (pointsto_ne with "Hl Hl'") as %Hne. iPureIntro. intros <-. apply Hne. reflexivity. }
  iDestruct (block_pts b reg o xs cs with "[$Hl $Hx $Hcs]") as "Hdst".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (void_only (memmove_contract os_world))
            [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))]
            (pts (block_ps b reg o xs cs) ∗ liveq dq b' reg' ∗ bytesq dq b' o' ys) with "[$Hdst $Hl' $Hy] [HK]");
    [exact Hmove_fn | exact Hmove_sym | reflexivity | exact Hmove | cbn [map_option]; rewrite Hpd Hps Hn; done | | |].
  - split; [reflexivity|]. split; [left; reflexivity | exists vd, vs, vn; reflexivity].
  - iIntros (σ) "Hσ (Hdst & Hl' & Hy)". iDestruct (pts_facts with "Hσ Hdst") as %(Ha & Hd & Hfit).
    iDestruct (ptsq_facts with "Hσ Hl'") as %([[E' L'] _] & _).
    iDestruct (ptsq_facts with "Hσ Hy") as %(Hys & _). iPureIntro.
    destruct Ha as [[E L] _]. cbn [fst snd] in E, L.
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
    + left. reflexivity.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) (Hdst & Hl' & Hy)".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ (invoke_void_only _ _ _ _ _ _ _ _ _ _ _ _ Hinv))
      as (_ & -> & d' & s0 & n' & Hx & _ & Hres & He).
    injection Hx as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hdst") as %Hlk.
    iDestruct (ptsq_lookup with "Hh Hl'") as %Hlk1. iDestruct (ptsq_lookup with "Hh Hy") as %Hlk2.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg o xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    assert (Hold' : all_agree (ls_mem σ) (byte_ps b' o' ys)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk2 l v Hin)). }
    assert (Hlv' : live_at (ls_mem σ) b' reg').
    { exact (Ha _ _ (Hlk1 _ _ ltac:(apply elem_of_cons; by left))). }
    destruct Hold as [Hlv Hold]. cbn [agree_piece fst snd] in Hlv.
    destruct (copy_after_any (ls_mem σ) m' b reg o xs cs b' reg' o' ys c' Hd Hlv Hlv' Hb8 Ho8 Hly Hlc
                Hold Hold' Hres) as [Hnew Hfr].
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    set (cs' := aux_now m' b o (length xs)).
    assert (Hk : (block_ps b reg o ys cs').*1 = (block_ps b reg o xs cs).*1).
    { apply block_ps_keys; [exact Hly | unfold cs'; rewrite length_aux_now; lia]. }
    iMod (pts_update _ _ (block_ps b reg o ys cs') with "Hh Hdst") as "[Hh Hdst]"; [exact Hk|].
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
      * exact (os_wi_block _ _ _ _ _ _ _ _ _ _ _ _ Hregs Hlk Hw).
    + rewrite block_pts. iDestruct "Hdst" as "(Hl & Hx & Hcs)".
      iApply ("HK" with "Hl Hx [Hcs] Hl' Hy"). iExists cs'. iFrame "Hcs". iPureIntro. apply length_aux_now.
Qed.

(** Calling a global function g bound to [glibc_memset] fills an owned
    8-aligned block with `c mod 256`, clears touched capability slots,
    and resumes the caller with the destination pointer. *)
Lemma wp_call_glibc_memset f e ls lab r g args rest j b reg o xs cs c cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr (mkPtr (b + o) (Obj b)); WInt c; WInt (Z.of_nat (length xs))] ->
  find_fn ge g = Some (Defined glibc_memset) ->
  resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None) (Ret (WPtr (mkPtr (b + o) (Obj b))))
    = Some cf' ->
  0 <= c < 2 ^ 32 -> Z.of_nat (length xs) < 2 ^ 64 -> b mod 8 = 0 -> o mod 8 = 0 -> 0 <= o ->
  b + o + Z.of_nat (length xs) <= r_end reg -> length cs = length xs ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗
  ▷ (live b reg -∗ bytes b o (replicate (length xs) (c mod 256)) -∗ auxes b o (clear_slots o cs) -∗
     WP (ERun cf' : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hx Hg Hres Hc Hn Hb8 Ho8 Ho Hend Hlen. iIntros "Hl Hx Hcs HK".
  iApply (wp_call_bind with "[-]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (wp_zmemset with "Hl Hx Hcs");
    [reflexivity | cbn; rewrite Z.mod_small; [reflexivity | lia] | cbn; rewrite Z.mod_small; [reflexivity | lia]
    | exact Hc | exact Hb8 | exact Ho8 | exact Ho | exact Hend | exact Hlen |].
  iNext. iIntros "Hl Hx Hcs". iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hl Hx Hcs").
Qed.

(** Calling a global function g bound to [glibc_memcpy] copies bytes `ys`
    from a shared source into an owned 8-aligned destination block,
    resumes the caller with the destination pointer, and restores the
    source. *)
Lemma wp_call_glibc_memcpy f e ls lab r g args rest j b reg o xs cs dq b' reg' o' c' ys cf' Φ :
  map_option (arg_x ge e) args =
    Some [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))] ->
  find_fn ge g = Some (Defined glibc_memcpy) ->
  resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None) (Ret (WPtr (mkPtr (b + o) (Obj b))))
    = Some cf' ->
  c' = Obj b' \/ c' = Ro b' -> Z.of_nat (length xs) < 2 ^ 64 ->
  b mod 8 = 0 -> o mod 8 = 0 -> b' mod 8 = 0 -> 0 <= o -> 0 <= o' ->
  b + o + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length xs) <= r_end reg' ->
  length ys = length xs -> length cs = length xs -> Forall (fun y => 0 <= y < 256) ys ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
  ▷ (live b reg -∗ bytes b o ys -∗ (∃ cs', ⌜length cs' = length xs⌝ ∗ auxes b o cs') -∗
     liveq dq b' reg' -∗ bytesq dq b' o' ys -∗ WP (ERun cf' : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hx Hg Hres Hc' Hn Hb8 Ho8 Hb8' Ho Ho' Hend Hend' Hly Hlc Hy. iIntros "Hl Hx Hcs Hl' Hy HK".
  iApply (wp_call_bind with "[-]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (wp_zmemmove with "Hl Hx Hcs Hl' Hy");
    [reflexivity | reflexivity | exact Hc' | cbn; rewrite Z.mod_small; [reflexivity | lia]
    | exact Hb8 | exact Ho8 | exact Hb8' | exact Ho | exact Ho' | exact Hend | exact Hend'
    | exact Hly | exact Hlc | exact Hy |].
  iNext. iIntros "Hl Hx Hcs Hl' Hy". iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hl Hx Hcs Hl' Hy").
Qed.

(** Calling a global function g bound to [glibc_mempcpy] delegates to
    `__GI_memcpy` and resumes the caller with the pointer just past the
    end of the destination block. *)
Lemma wp_call_glibc_mempcpy f e ls lab r g args rest j b reg o xs cs dq b' reg' o' c' ys cf' Φ :
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy) ->
  map_option (arg_x ge e) args =
    Some [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))] ->
  find_fn ge g = Some (Defined glibc_mempcpy) ->
  resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None)
    (Ret (WPtr (mkPtr (b + o + Z.of_nat (length xs)) (Obj b)))) = Some cf' ->
  c' = Obj b' \/ c' = Ro b' -> 0 <= b -> b + o + Z.of_nat (length xs) < 2 ^ 64 ->
  b mod 8 = 0 -> o mod 8 = 0 -> b' mod 8 = 0 -> 0 <= o -> 0 <= o' ->
  b + o + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length xs) <= r_end reg' ->
  length ys = length xs -> length cs = length xs -> Forall (fun y => 0 <= y < 256) ys ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
  ▷ (live b reg -∗ bytes b o ys -∗ (∃ cs', ⌜length cs' = length xs⌝ ∗ auxes b o cs') -∗
     liveq dq b' reg' -∗ bytesq dq b' o' ys -∗ WP (ERun cf' : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hcpy Hx Hg Hres Hc' Hb0 Hn Hb8 Ho8 Hb8' Ho Ho' Hend Hend' Hly Hlc Hy. iIntros "Hl Hx Hcs Hl' Hy HK".
  iApply (wp_call_bind with "[-]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (wp_call_glibc_memcpy with "Hl Hx Hcs Hl' Hy");
    [cbn; rewrite (Z.mod_small (Z.of_nat _)); [reflexivity | lia] | exact Hcpy | reflexivity | exact Hc' | lia
    | exact Hb8 | exact Ho8 | exact Hb8' | exact Ho | exact Ho' | exact Hend | exact Hend'
    | exact Hly | exact Hlc | exact Hy |].
  iNext. iIntros "Hl Hx Hcs Hl' Hy".
  iApply wp_flight; [reflexivity | reflexivity | reflexivity |]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iExists cf'. iSplit; [|iNext; iApply ("HK" with "Hl Hx Hcs Hl' Hy")]. iPureIntro.
  rewrite -Hres. cbn. rewrite (Z.mod_small (b + o)); [|lia]. rewrite (Z.mod_small (Z.of_nat _)); [|lia].
  rewrite (Z.mod_small (b + o + _)); [reflexivity | lia].
Qed.

(** Predicate [malloc_out] describes the result of allocating n bytes:
    either null or a fresh 16-aligned heap object whose ownership is
    transferred to the caller via [obj]. *)
Definition malloc_out (n : Z) (q : ptr) : iProp Σ :=
  ⌜ptr_addr q = 0⌝ ∨
  ∃ base, ⌜q = mkPtr base (Obj base) /\ 0 < base /\ base mod 16 = 0 /\
           base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ ∗ obj base (heap_req 16 n).

(** Predicate [malloc_triple] characterizes any `c: malloc`
    implementation whose calls return [malloc_out], covering both
    [wp_malloc] and glibc's own allocator. *)
Definition malloc_triple : Prop :=
  forall f e ls lab d v rest j n Φ, arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  ⊢ ▷ (∀ q, malloc_out n q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j))
          : mexpr) {{ Φ }}.

(** Executing [glibc_strdup] on a [word_string] at any share calls
    `__GI_strlen`, `malloc`, and `__GI_memcpy`. It returns null if
    allocation fails, or a fresh object holding the string and its NUL
    terminator, while restoring the input string. *)
Lemma wp_glibc_strdup dq p s Φ :
  malloc_triple ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy) ->
  word_string dq p s -∗
  ▷ (∀ q, word_string dq p s -∗
       (⌜q = mkPtr 0 CNone⌝ ∨
        ∃ base reg', ⌜q = mkPtr base (Obj base) /\ 0 < base /\ base mod 16 = 0 /\
                       base + Z.of_nat (length s) + 1 <= r_end reg' /\ r_end reg' <= 2 ^ 48⌝ ∗
          live base reg' ∗ bytes base 0 (s ++ [0])) -∗
       Φ (Ret (WPtr q))) -∗
  WP (ERun (mkFrame glibc_strdup [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)) : mexpr) {{ Φ }}.
Proof.
  intros Hm Hsl Hcpy. iIntros "Hs HK".
  iDestruct "Hs" as "(%b & %reg & %ws & %Hs & Hw)".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hr Hby Hch].
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)) as Hk.
  assert (Hend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end reg).
  { unfold wstart in Hf. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hs|].
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (SW.wp_call_glibc_strlen registry (os_wi w0) ge with "Hs"); [reflexivity | exact Hsl | reflexivity |].
  iNext. iIntros "Hs".
  iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | iNext].
  iApply (Hm _ _ _ _ _ _ _ _ (Z.of_nat (length s) + 1)); [cbn; rewrite !Z.mod_small; first [reflexivity | lia] | lia |].
  iNext. iIntros (q) "Hq". cbn [fr_fn fr_env fr_locals fr_at].
  iDestruct "Hq" as "[%Hq0 | (%base & %Hbase & Hobj)]".
  - destruct q as [qa qc]. cbn in Hq0. subst qa.
    do 3 (iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | iNext]).
    iApply wp_branch; [reflexivity|]. iNext. cbn.
    iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
    iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "Hs"). by iLeft.
  - destruct Hbase as (-> & Hb0p & Hb16 & Hbend).
    match type of Hbend with context [req_extent ?Q] => set (q := Q) in * end.
    assert (Hq : Z.of_nat (length s) + 1 <= req_extent q).
    { unfold q, heap_req, req_extent. cbn. pose proof (Z.div_mod (Z.of_nat (length s) + 1 + 15) 16 ltac:(lia)).
      pose proof (Z.mod_pos_bound (Z.of_nat (length s) + 1 + 15) 16 ltac:(lia)). lia. }
    do 3 (iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | iNext]).
    iApply wp_branch; [reflexivity|]. iNext. cbn [ptr_addr].
    rewrite Zmod_0_l (Z.mod_small base); [|lia]. replace (base =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [Z.eqb edge_label]. rewrite Zmod_0_l. cbn [Z.eqb edge_label].
    iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
    iDestruct (obj_zero_block with "Hobj") as "(Hl & Hx & Hcs)"; [lia|].
    rewrite (bytes_take_drop _ _ _ (S (length s))); [|rewrite length_replicate; lia].
    rewrite (auxes_take_drop _ _ _ (S (length s))); [|rewrite length_replicate; lia].
    rewrite !take_replicate. iDestruct "Hx" as "[Hx _]". iDestruct "Hcs" as "[Hcs _]".
    replace (Nat.min (S (length s)) (Z.to_nat (req_extent q))) with (S (length s)) by lia.
    iDestruct (word_string_bytes with "Hs") as (b2 reg2 ws2) "(%Hs2 & Hl' & Hy & Hback)".
    pose proof Hs2 as [Hc2 Hb02 Hb82 Hst2 Hf2 Hsp2 Hlen2 Hr2 Hby2 Hch2].
    assert (Hend2 : ptr_addr p + Z.of_nat (length s) + 1 <= r_end reg2).
    { unfold wstart in Hf2. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
    iApply (wp_call_glibc_memcpy _ _ _ _ _ _ _ _ _ base _ 0 (replicate (S (length s)) 0)
              (replicate (S (length s)) CNone) dq b2 reg2 (ptr_addr p - b2) (ptr_cap p) (s ++ [0])
              with "Hl Hx Hcs Hl' Hy"); [ | exact Hcpy | reflexivity | exact Hc2 | rewrite length_replicate; lia
      | exact (mod16_mod8 _ Hb16) | reflexivity | exact Hb82 | lia | lia | cbn [r_end]; rewrite length_replicate; lia
      | rewrite length_replicate; lia | rewrite length_app length_replicate; cbn; lia
      | rewrite !length_replicate; reflexivity
      | apply Forall_app; split; [eapply Forall_impl; [|exact Hch2]; cbn; intros; lia | repeat constructor; lia] |].
    { cbn. rewrite length_replicate Z.add_0_r. replace (b2 + (ptr_addr p - b2)) with (ptr_addr p) by lia.
      replace (Z.of_nat (S (length s))) with (Z.of_nat (length s) + 1) by lia.
      rewrite !(Z.mod_small (Z.of_nat (length s))); try lia. rewrite (Z.mod_small 1); [|lia].
      rewrite !(Z.mod_small (Z.of_nat (length s) + 1)); try lia. destruct p; reflexivity. }
    iNext. iIntros "Hl Hx Hcs Hl' Hy". iDestruct ("Hback" with "Hl' Hy") as "Hs".
    cbn [fr_fn fr_env fr_locals fr_at]. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    rewrite Z.add_0_r. iApply ("HK" with "Hs"). iRight. iExists base, _. iFrame "Hl Hx". iPureIntro.
    split; [reflexivity|]. cbn [r_end]. repeat split; lia.
Qed.

End rules.
End MemFwdLogicOn.
