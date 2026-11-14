From Glibc Require Import GlibcProgram.
(** Stream output copies bytes into a buffer whose write pointer need
    not be aligned. This module verifies those copies through glibc's
    memcpy and mempcpy implementations.

    A copy clears the [[aux|capability slot]] of every word it touches.
    The first slot may therefore begin before the destination pointer.
    The caller owns the whole buffer, including those earlier slots,
    so it can account for every change. After the copy, it recovers
    the buffer's bytes and slots and retains its share of the source. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode MemFwdLogic FileInv LibioLogic SysWrappers
  LibioCloseSteps.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
From Glibc Require Import GlibcSpec.
Import ListNotations.
Open Scope Z_scope.

(** ## The buffer after a copy *)

(** A copy changes only part of the destination buffer. The following
    definitions describe the whole buffer afterwards and preserve ownership
    of memory outside it. *)

(** This function reads the first n bytes of object b from memory. *)
Definition bytes_now (m : mem) (b : Z) (n : nat) : list Z :=
  map (fun i => m_bytes m (b + (0 + Z.of_nat i))) (seq 0 n).

(** [bytes_now] has n bytes. *)
Lemma length_bytes_now m b n : length (bytes_now m b n) = n.
Proof. unfold bytes_now. by rewrite length_map length_seq. Qed.

(** Copying into an aligned buffer preserves memory agreement outside the buffer.
    The destination retains valid bytes even when the write pointer is unaligned. *)
Lemma copy_in_after m m' b reg xs cs o b' reg' o' ys c' :
  live_disjoint m -> live_at m b reg -> live_at m b' reg' -> b mod 8 = 0 -> length cs = length xs ->
  0 <= o -> o + Z.of_nat (length ys) <= Z.of_nat (length xs) ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  all_agree m (byte_ps b 0 xs ++ aux_ps b 0 cs) -> all_agree m (byte_ps b' o' ys) ->
  copy_result m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') (Z.of_nat (length ys)) m' ->
  all_agree m' (byte_ps b 0 (bytes_now m' b (length xs)) ++ aux_ps b 0 (aux_now m' b 0 (length xs))) /\
  Forall (fun x => 0 <= x < 256) (bytes_now m' b (length xs)) /\
  frame_ok (byte_ps b 0 xs ++ aux_ps b 0 cs).*1 m m'.
Proof.
  intros Hd Hl Hl' Hb8 Hlc Ho Hon Hx Hy Hdst Hsrc Hres.
  pose proof Hres as (Hfr & _ & _). pose proof Hfr as (Hr & Hbo & Hao).
  apply all_agree_app in Hdst as [Hxa Hca]. destruct Hl as [E0 L0].
  assert (Hreg : registered m' b) by (unfold registered; rewrite Hr E0; discriminate).
  assert (Hbyte : forall i, (i < length xs)%nat -> b + Z.of_nat i < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E0 L0) Hxa Hxi) as (_ & H1 & H2). lia. }
  assert (Hnow : forall i, (i < length xs)%nat -> 0 <= m_bytes m' (b + Z.of_nat i) < 256).
  { intros i Hi. destruct (copy_result_cells _ _ _ _ _ (b + Z.of_nat i) Hres) as [Hc _]. rewrite Hc.
    cbn [ptr_addr].
    destruct ((b + o <=? b + Z.of_nat i) && (b + Z.of_nat i <? b + o + Z.of_nat (length ys))) eqn:Hin.
    - apply andb_true_iff in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      destruct (lookup_lt_is_Some_2 ys (Z.to_nat (Z.of_nat i - o)) ltac:(lia)) as [y Hyk].
      destruct (byte_ps_agree _ _ _ _ _ _ _ Hl' Hsrc Hyk) as (Hv & _ & _).
      replace (b' + o' + (b + Z.of_nat i - (b + o))) with (b' + (o' + Z.of_nat (Z.to_nat (Z.of_nat i - o))))
        by lia.
      rewrite Hv. exact (Forall_lookup_1 _ _ _ _ Hy Hyk).
    - destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
      destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E0 L0) Hxa Hxi) as (Hv & _ & _).
      rewrite Z.add_0_l in Hv. rewrite Hv. exact (Forall_lookup_1 _ _ _ _ Hx Hxi). }
  split; [|split].
  - apply all_agree_app. split; apply all_agree_intro; intros l v Hin.
    + apply byte_ps_elem in Hin as (i & y & Hyi & -> & ->). unfold bytes_now in Hyi.
      apply list_lookup_fmap_Some in Hyi as (k & -> & Hk).
      pose proof (lookup_lt_Some _ _ _ Hk) as Hi. rewrite length_seq in Hi.
      rewrite lookup_seq_lt in Hk; [injection Hk as <- | exact Hi]. cbn [agree_piece]. split; [exact Hreg|].
      intros reg0 E L. rewrite Hr E0 in E. injection E as <-. specialize (Hbyte i Hi). lia.
    + apply aux_ps_elem in Hin as (i & c & Hci & -> & ->).
      unfold aux_now in Hci. change (map ?f ?l) with (f <$> l) in Hci.
      apply list_lookup_fmap_Some in Hci as (k & -> & Hk).
      pose proof (lookup_lt_Some _ _ _ Hk) as Hi. rewrite length_seq in Hi.
      rewrite lookup_seq_lt in Hk; [injection Hk as <- | exact Hi]. cbn [agree_piece]. split; [exact Hreg|].
      intros reg0 E L. rewrite Hr E0 in E. injection E as <-. specialize (Hbyte i Hi).
      split; [lia|]. split; [lia|]. left. reflexivity.
  - apply Forall_forall. intros x Hin. unfold bytes_now in Hin. apply in_map_iff in Hin as (i & <- & Hi).
    apply in_seq in Hi. rewrite Z.add_0_l. apply Hnow. lia.
  - apply (frame_within _ _ _ b reg); [exact Hr | exact Hd | exact (conj E0 L0) | |].
    + intros a H. apply Hbo. intros Hs. unfold span_contains in Hs. cbn in Hs.
      assert (Hlt : (Z.to_nat (a - b) < length xs)%nat) by lia.
      apply H; [split; [lia|]; specialize (Hbyte _ Hlt); lia|]. rewrite fmap_app. apply elem_of_app. left.
      replace (a - b) with (0 + (a - b)) by lia. apply byte_ps_key. lia.
    + intros a H. apply Hao. destruct (memset_touched _ _ _) eqn:Ht; [|reflexivity]. exfalso.
      apply memset_touched_spec in Ht as (Hn & Ha8 & Hhi & Hlo). cbn [ptr_addr] in Hhi, Hlo.
      assert (Hab : b <= a).
      { pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)). lia. }
      assert (Hlt : (Z.to_nat (a - b) < length xs)%nat) by lia.
      apply H; [split; [lia|]; specialize (Hbyte _ Hlt); lia|]. rewrite fmap_app. apply elem_of_app. right.
      replace (a - b) with (0 + (a - b)) by lia. apply aux_ps_key. lia.
Qed.

(** ## Over a Logic instance *)

(** The remaining proofs connect physical copies to the caller's memory ownership.
    They use the same [[separation-logic]] interpretation as the surrounding stream code. *)

Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** Restricting a runtime contract to void calls does not change the memory effects it permits. *)
Lemma invoke_void {world} (c : contract world) r args xs s m w trace en s' m' w' :
  M.E.invoke (void_only c) r args xs s m w trace en s' m' w' -> M.E.invoke c r args xs s m w trace en s' m' w'.
Proof.
  intros H. destruct H as [trace en s' m' w' born Habi Hpre Hp Hpost Hr Hv Hx
                         | why trace s' m' w' born Habi Hpre Hp Hf Hres].
  - eapply M.E.invoke_normal; [exact (proj2 Habi) | exact Hpre | exact Hp | exact Hpost | exact Hr | exact Hv | exact Hx].
  - eapply M.E.invoke_resource; [exact (proj2 Habi) | exact Hpre | exact Hp | exact Hf | exact Hres].
Qed.

Import ProgramAbbreviations.
Section rules_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}.
Existing Instance gen_heapGS0.
(** The destination retains its original size and valid bytes after a copy. *)
Definition buf_after (b : Z) (n : nat) : iProp Σ :=
  ∃ xs' cs', ⌜length xs' = n /\ length cs' = n /\ Forall (fun x => 0 <= x < 256) xs'⌝ ∗
    bytes b 0 xs' ∗ auxes b 0 cs'.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The registry holds [OsRegistry](../zsys/OsRegistry.v)'s contract
    for `c: zmemmove`, which is no function or symbol of the genv. *)
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).

(** Garbage collection preserves the OS state used to interpret this caller's memory. *)
Local Instance copy_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This abbreviation selects expressions in the caller's linked program. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The runtime move preserves the source's ownership share and returns the whole destination buffer.
    The destination's bytes remain valid, and its size does not change. *)
Lemma wp_zmemmove_in f e ls lab vd vs vn rest j b reg xs cs o dq b' reg' o' c' ys Φ :
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  arg_x ge e (Arg P vs) = Some (WPtr (mkPtr (b' + o') c')) -> c' = Obj b' \/ c' = Ro b' ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length ys))) ->
  b mod 8 = 0 -> b' mod 8 = 0 -> 0 <= o -> 0 <= o' -> o + Z.of_nat (length ys) <= Z.of_nat (length xs) ->
  b + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length ys) <= r_end reg' ->
  length cs = length xs -> Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
  ▷ (live b reg -∗ buf_after b (length xs) -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
     WP (ERun (mkFrame f e ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zmemmove")) [Arg P vd; Arg P vs; Arg L vn] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hpd Hps Hc' Hn Hb8 Hb8' Ho Ho' Hon Hend Hend' Hlc Hx Hy. iIntros "Hl Hx Hcs Hl' Hy HK".
  iAssert (⌜b <> b'⌝)%I as %Hne.
  { rewrite /live /liveq /pts /ptsq !big_sepL_singleton. cbn [fst snd].
    iDestruct (pointsto_ne with "Hl Hl'") as %Hne. iPureIntro. intros <-. apply Hne. reflexivity. }
  iDestruct (block_pts b reg 0 xs cs with "[$Hl $Hx $Hcs]") as "Hdst".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (void_only (memmove_contract os_world))
            [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length ys))]
            (pts (block_ps b reg 0 xs cs) ∗ liveq dq b' reg' ∗ bytesq dq b' o' ys) with "[$Hdst $Hl' $Hy] [HK]");
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
    destruct (M.E.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ (invoke_void _ _ _ _ _ _ _ _ _ _ _ _ Hinv))
      as (_ & -> & d' & s0 & n' & Hxs & _ & Hres & He).
    injection Hxs as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hdst") as %Hlk.
    iDestruct (ptsq_lookup with "Hh Hl'") as %Hlk1. iDestruct (ptsq_lookup with "Hh Hy") as %Hlk2.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg 0 xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    assert (Hold' : all_agree (ls_mem σ) (byte_ps b' o' ys)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk2 l v Hin)). }
    assert (Hlv' : live_at (ls_mem σ) b' reg').
    { exact (Ha _ _ (Hlk1 _ _ ltac:(apply elem_of_cons; by left))). }
    destruct Hold as [Hlv Hold]. cbn [agree_piece fst snd] in Hlv.
    destruct (copy_in_after (ls_mem σ) m' b reg xs cs o b' reg' o' ys c' Hd Hlv Hlv' Hb8 Hlc Ho Hon Hx Hy
                Hold Hold' Hres) as (Hnew & Hby & Hfr).
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    set (xs' := bytes_now m' b (length xs)). set (cs' := aux_now m' b 0 (length xs)).
    assert (Hk : (block_ps b reg 0 xs' cs').*1 = (block_ps b reg 0 xs cs).*1).
    { apply block_ps_keys; [unfold xs'; apply length_bytes_now | unfold cs'; rewrite length_aux_now; lia]. }
    iMod (pts_update _ _ (block_ps b reg 0 xs' cs') with "Hh Hdst") as "[Hh Hdst]"; [exact Hk|].
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
      iApply ("HK" with "Hl [Hx Hcs] Hl' Hy"). iExists xs', cs'. iFrame "Hx Hcs". iPureIntro.
      split; [apply length_bytes_now|]. split; [unfold cs'; apply length_aux_now | exact Hby].
Qed.

(** A stream copy owns its whole destination buffer, including slots before
    an unaligned write pointer. Both copy functions preserve this ownership. *)
Definition copy_in_spec (past : bool) : fspec Σ :=
  FSpec (Z * region * Z * list Z * list cap * dfrac * Z * region * Z * cap * list Z)
    (fun '(b, _, o, _, _, _, b', _, o', c', ys) =>
      [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length ys))])
    (fun '(b, reg, o, xs, cs, dq, b', reg', o', c', ys) =>
      ⌜(c' = Obj b' \/ c' = Ro b') /\ Z.of_nat (length ys) < 2 ^ 64 /\
        b mod 8 = 0 /\ b' mod 8 = 0 /\ 0 <= o /\ 0 <= o' /\
        o + Z.of_nat (length ys) <= Z.of_nat (length xs) /\
        b + Z.of_nat (length xs) <= r_end reg /\ b' + o' + Z.of_nat (length ys) <= r_end reg' /\
        length cs = length xs /\ Forall (fun x => 0 <= x < 256) xs /\ Forall (fun y => 0 <= y < 256) ys /\
        (if past then 0 <= b /\ b + Z.of_nat (length xs) < 2 ^ 64 else True)⌝ ∗
      live b reg ∗ bytes b 0 xs ∗ auxes b 0 cs ∗ liveq dq b' reg' ∗ bytesq dq b' o' ys)%I
    (fun '(b, reg, o, xs, cs, dq, b', reg', o', c', ys) v =>
      ⌜v = Ret (WPtr (mkPtr (if past then (b + o + Z.of_nat (length ys))%Z else (b + o)%Z) (Obj b)))⌝ ∗
      live b reg ∗ buf_after b (length xs) ∗ liveq dq b' reg' ∗ bytesq dq b' o' ys)%I.

(** The whole-buffer move rule establishes memcpy's stream-copy contract. *)
Lemma memcpy_in_spec_valid g : find_fn ge g = Some (Defined glibc_memcpy) ->
  HasSpec registry (os_wi w0) ge g (copy_in_spec false).
Proof.
  intros Hg [[[[[[[[[[b reg] o] xs] cs] dq] b'] reg'] o'] c'] ys].
  exists glibc_memcpy. split; [exact Hg|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. cbn in Hfr. injection Hfr as <-. cbn [fs_pre fs_post copy_in_spec].
  iIntros "(%Hp & Hl & Hx & Hcs & Hl' & Hy) HK".
  destruct Hp as (Hc' & Hn & Hb8 & Hb8' & Ho & Ho' & Hon & Hend & Hend' & Hlc & Hx & Hy & _).
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (wp_zmemmove_in with "Hl Hx Hcs Hl' Hy");
    [reflexivity | reflexivity | exact Hc' | cbn; rewrite Z.mod_small; [reflexivity | lia]
    | exact Hb8 | exact Hb8' | exact Ho | exact Ho' | exact Hon | exact Hend | exact Hend' | exact Hlc | exact Hx | exact Hy |].
  iNext. iIntros "Hl Hx Hl' Hy". iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply "HK". by iFrame.
Qed.

(** Calling memcpy preserves the whole buffer and resumes the caller with the destination pointer. *)
Lemma wp_call_memcpy_in f e ls lab r g args rest j b reg xs cs o dq b' reg' o' c' ys cf' Φ :
  map_option (arg_x ge e) args =
    Some [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length ys))] ->
  find_fn ge g = Some (Defined glibc_memcpy) ->
  resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None) (Ret (WPtr (mkPtr (b + o) (Obj b))))
    = Some cf' ->
  c' = Obj b' \/ c' = Ro b' -> Z.of_nat (length ys) < 2 ^ 64 ->
  b mod 8 = 0 -> b' mod 8 = 0 -> 0 <= o -> 0 <= o' -> o + Z.of_nat (length ys) <= Z.of_nat (length xs) ->
  b + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length ys) <= r_end reg' ->
  length cs = length xs -> Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
  ▷ (live b reg -∗ buf_after b (length xs) -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
     WP (ERun cf' : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hxa Hg Hres Hc' Hn Hb8 Hb8' Ho Ho' Hon Hend Hend' Hlc Hx Hy. iIntros "Hl Hx Hcs Hl' Hy HK".
  pose proof (memcpy_in_spec_valid g Hg) as Hspec.
  call_spec.
  { done. }
  iDestruct "Hpost" as "(-> & Hl & Hx & Hl' & Hy)".
  iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hl Hx Hl' Hy").
Qed.

(** Mempcpy's frame uses the whole-buffer memcpy contract before advancing its result pointer. *)
Lemma mempcpy_in_spec_valid g : find_fn ge g = Some (Defined glibc_mempcpy) ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy) ->
  HasSpec registry (os_wi w0) ge g (copy_in_spec true).
Proof.
  intros Hg Hcpy [[[[[[[[[[b reg] o] xs] cs] dq] b'] reg'] o'] c'] ys].
  exists glibc_mempcpy. split; [exact Hg|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. cbn in Hfr. injection Hfr as <-. cbn [fs_pre fs_post copy_in_spec].
  iIntros "(%Hp & Hl & Hx & Hcs & Hl' & Hy) HK".
  destruct Hp as (Hc' & Hn & Hb8 & Hb8' & Ho & Ho' & Hon & Hend & Hend' & Hlc & Hx & Hy & Hb0 & Hbound).
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  pose proof (memcpy_in_spec_valid (TAtom "__GI_memcpy") Hcpy) as Hspec.
  call_spec with (b, reg, o, xs, cs, dq, b', reg', o', c', ys).
  { cbn; rewrite (Z.mod_small (Z.of_nat _)); [reflexivity | lia]. }
  { repeat split; try assumption; lia. }
  iDestruct "Hpost" as "(-> & Hl & Hx & Hl' & Hy)".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply wp_flight; [reflexivity | reflexivity | reflexivity |]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply "HK". iFrame. iPureIntro. cbn.
  rewrite (Z.mod_small (b + o)); [|lia]. rewrite (Z.mod_small (Z.of_nat _)); [|lia].
  rewrite (Z.mod_small (b + o + _)); [reflexivity | lia].
Qed.

(** Calling mempcpy preserves the whole buffer and returns the pointer just after the copied bytes. *)
Lemma wp_call_mempcpy_in f e ls lab r g args rest j b reg xs cs o dq b' reg' o' c' ys cf' Φ :
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy) ->
  map_option (arg_x ge e) args =
    Some [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length ys))] ->
  find_fn ge g = Some (Defined glibc_mempcpy) ->
  resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None)
    (Ret (WPtr (mkPtr (b + o + Z.of_nat (length ys)) (Obj b)))) = Some cf' ->
  c' = Obj b' \/ c' = Ro b' -> 0 <= b -> b + Z.of_nat (length xs) < 2 ^ 64 ->
  b mod 8 = 0 -> b' mod 8 = 0 -> 0 <= o -> 0 <= o' -> o + Z.of_nat (length ys) <= Z.of_nat (length xs) ->
  b + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length ys) <= r_end reg' ->
  length cs = length xs -> Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
  ▷ (live b reg -∗ buf_after b (length xs) -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
     WP (ERun cf' : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hcpy Hxa Hg Hres Hc' Hb0 Hn Hb8 Hb8' Ho Ho' Hon Hend Hend' Hlc Hx Hy. iIntros "Hl Hx Hcs Hl' Hy HK".
  pose proof (mempcpy_in_spec_valid g Hg Hcpy) as Hspec.
  call_spec with (b, reg, o, xs, cs, dq, b', reg', o', c', ys).
  { repeat split; try assumption; lia. }
  iDestruct "Hpost" as "(-> & Hl & Hx & Hl' & Hy)".
  iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hl Hx Hl' Hy").
Qed.

End rules.
