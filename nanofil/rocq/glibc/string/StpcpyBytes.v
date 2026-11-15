From Glibc Require Import GlibcProgram.
(** glibc's `c: stpcpy` copies a string into a caller's buffer one byte or
    one 64-bit word at a time. A proof of it must say which bytes of the
    buffer change after each store, and it needs a rule for storing a whole
    word into bytes that the caller owns. This module supplies both.

    The buffer is a list of bytes, and a copy replaces a stretch of that
    list. The function [splice] performs the replacement, and the lemmas
    below show that two adjacent replacements form one, and that the
    ownership of a buffer splits around the replaced stretch. The rule
    [wp_raw_store_l_bytes] stores a 64-bit integer into eight owned bytes,
    in the same way as the rule for 32-bit stores in MemLogic.v. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld FileInv LibioLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** ## Replacing part of a buffer *)

(** [splice ys k zs] replaces the bytes of ys from index k on with zs and
    keeps the rest of ys. *)
Definition splice (ys : list Z) (k : nat) (zs : list Z) : list Z :=
  take k ys ++ zs ++ drop (k + length zs) ys.

(** A replacement that fits inside the buffer keeps its length. *)
Lemma length_splice ys k zs : (k + length zs <= length ys)%nat -> length (splice ys k zs) = length ys.
Proof.
  intros H. unfold splice. rewrite !length_app length_take length_drop. lia.
Qed.

(** Replacing nothing leaves the buffer unchanged. *)
Lemma splice_nil ys k : (k <= length ys)%nat -> splice ys k [] = ys.
Proof. intros H. unfold splice. cbn. rewrite Nat.add_0_r. apply take_drop. Qed.

(** Copying the first i bytes of S and then the next m bytes is the same
    as copying the first i + m bytes at once. *)
Lemma splice_more xs k S i m : (k + i + m <= length xs)%nat -> (i + m <= length S)%nat ->
  splice (splice xs k (take i S)) (k + i) (take m (drop i S)) = splice xs k (take (i + m) S).
Proof.
  intros H1 H2. unfold splice.
  assert (Lk : length (take k xs) = k) by (rewrite length_take; lia).
  assert (Li : length (take i S) = i) by (rewrite length_take; lia).
  assert (Lm : length (take m (drop i S)) = m) by (rewrite length_take length_drop; lia).
  assert (Lim : length (take (i + m) S) = (i + m)%nat) by (rewrite length_take; lia).
  rewrite Lm Li Lim.
  set (D := drop (k + i) xs).
  assert (T1 : take (k + i) (take k xs ++ take i S ++ D) = take k xs ++ take i S).
  { rewrite (app_assoc (take k xs)). apply take_app_length'. rewrite length_app. lia. }
  assert (T2 : drop (k + i + m) (take k xs ++ take i S ++ D) = drop (k + i + m) xs).
  { rewrite (app_assoc (take k xs)). rewrite drop_app_ge; [|rewrite length_app; lia].
    rewrite length_app Lk Li. unfold D. rewrite drop_drop. f_equal. lia. }
  rewrite T1 T2 -(take_take_drop S i m). rewrite -!app_assoc. do 3 f_equal. f_equal. lia.
Qed.

(** Copying the whole of S is copying its first length S bytes. *)
Lemma splice_all xs k S : splice xs k (take (length S) S) = splice xs k S.
Proof. rewrite take_ge; [reflexivity | lia]. Qed.

(** The copy has written the first i bytes of S into xs at offset o. *)
Definition stp_dst (xs : list Z) (o i : Z) (S : list Z) : list Z := splice xs (Z.to_nat o) (take (Z.to_nat i) S).

(** Before the copy starts, the buffer is unchanged. *)
Lemma stp_dst_0 xs o S : 0 <= o <= Z.of_nat (length xs) -> stp_dst xs o 0 S = xs.
Proof. intros H. unfold stp_dst. cbn. apply splice_nil. lia. Qed.

(** The partly copied buffer keeps its length. *)
Lemma length_stp_dst xs o i S : 0 <= o -> 0 <= i <= Z.of_nat (length S) -> o + i <= Z.of_nat (length xs) ->
  length (stp_dst xs o i S) = length xs.
Proof. intros. unfold stp_dst. apply length_splice. rewrite length_take. lia. Qed.

(** Writing byte i of S after the first i bytes copies i + 1 bytes. *)
Lemma stp_dst_byte xs o i S : 0 <= o -> 0 <= i < Z.of_nat (length S) -> o + i + 1 <= Z.of_nat (length xs) ->
  splice (stp_dst xs o i S) (Z.to_nat (o + i)) [nth (Z.to_nat i) S 0] = stp_dst xs o (i + 1) S.
Proof.
  intros Ho Hi Hx. unfold stp_dst.
  replace [nth (Z.to_nat i) S 0] with (take 1 (drop (Z.to_nat i) S)).
  - replace (Z.to_nat (o + i)) with (Z.to_nat o + Z.to_nat i)%nat by lia.
    rewrite splice_more; [|lia|lia]. f_equal. f_equal. lia.
  - rewrite -{2}(take_drop (Z.to_nat i) S). rewrite app_nth2; [|rewrite length_take; lia].
    rewrite length_take. replace (Z.to_nat i - Nat.min (Z.to_nat i) (length S))%nat with 0%nat by lia.
    destruct (drop (Z.to_nat i) S) eqn:D; [|reflexivity].
    apply (f_equal (@length Z)) in D. rewrite length_drop in D. cbn in D. lia.
Qed.

(** Writing the eight bytes of S from index i copies i + 8 bytes. *)
Lemma stp_dst_word xs o i S : 0 <= o -> 0 <= i -> i + 8 <= Z.of_nat (length S) -> o + i + 8 <= Z.of_nat (length xs) ->
  splice (stp_dst xs o i S) (Z.to_nat (o + i)) (take 8 (drop (Z.to_nat i) S)) = stp_dst xs o (i + 8) S.
Proof.
  intros Ho Hi HS Hx. unfold stp_dst.
  replace (Z.to_nat (o + i)) with (Z.to_nat o + Z.to_nat i)%nat by lia.
  rewrite splice_more; [|lia|lia]. f_equal. f_equal. lia.
Qed.

(** Once all of S is copied, the buffer holds S at offset o. *)
Lemma stp_dst_all xs o S : stp_dst xs o (Z.of_nat (length S)) S = splice xs (Z.to_nat o) S.
Proof. unfold stp_dst. rewrite Nat2Z.id. apply splice_all. Qed.

(** A word whose eight bytes are the next eight bytes of S stores exactly
    those bytes. *)
Lemma le_bytes_word w S i : (i + 8 <= length S)%nat ->
  (forall t : nat, (t < 8)%nat -> byte_of w (Z.of_nat t) = nth (i + t) S 0) -> le_bytes w 8 = take 8 (drop i S).
Proof.
  intros HS Hb. apply list_eq. intros j. unfold le_bytes. rewrite list_lookup_fmap.
  destruct (decide (j < 8)%nat) as [Hj|Hj].
  - rewrite lookup_seq_lt; [|lia]. cbn. rewrite lookup_take_lt; [|lia]. rewrite lookup_drop.
    destruct (lookup_lt_is_Some_2 S (i + j)) as [x Hx]; [lia|]. rewrite Hx. f_equal.
    rewrite Hb; [|lia]. exact (nth_lookup_Some _ _ _ _ Hx).
  - rewrite lookup_seq_ge; [|lia]. rewrite lookup_take_ge; [reflexivity | lia].
Qed.

Section bytes.
Context `{!gen_heapGS piece pval Σ}.

(** A buffer's ownership splits into the n bytes at index k and a wand
    that takes back any n bytes in their place. *)
Lemma bytes_splice b ys k n : (k + n <= length ys)%nat ->
  bytes b 0 ys ⊢ bytes b (Z.of_nat k) (take n (drop k ys)) ∗
    (∀ zs, ⌜length zs = n⌝ -∗ bytes b (Z.of_nat k) zs -∗ bytes b 0 (splice ys k zs)).
Proof.
  intros H.
  assert (E : ys = take k ys ++ take n (drop k ys) ++ drop (k + n) ys).
  { rewrite -{1}(take_drop k ys). f_equal. rewrite -{1}(take_drop n (drop k ys)) drop_drop. reflexivity. }
  assert (Lk : length (take k ys) = k) by (rewrite length_take; lia).
  assert (Ln : length (take n (drop k ys)) = n) by (rewrite length_take length_drop; lia).
  rewrite {1}E !bytes_app Lk Ln. cbn [Z.add]. iIntros "(Hp & Hm & Hs)". iFrame "Hm".
  iIntros (zs Hzs) "Hz". unfold splice. rewrite !bytes_app Lk Hzs. cbn [Z.add]. iFrame.
Qed.

(** One byte of a buffer can be replaced on its own. *)
Lemma bytes_store1 b ys k : (k < length ys)%nat ->
  bytes b 0 ys ⊢ ∃ x, ibyte b (Z.of_nat k) x ∗ (∀ y, ibyte b (Z.of_nat k) y -∗ bytes b 0 (splice ys k [y])).
Proof.
  intros H. rewrite (bytes_splice b ys k 1); [|lia]. iIntros "[Hb HK]".
  destruct (take 1 (drop k ys)) as [|x [|x' r]] eqn:E.
  - apply (f_equal (@length Z)) in E. rewrite length_take length_drop in E. cbn [length] in E. lia.
  - iExists x. iFrame "Hb". iIntros (y) "Hy". iApply ("HK" $! [y] with "[//] Hy").
  - apply (f_equal (@length Z)) in E. rewrite length_take length_drop in E. cbn [length] in E. lia.
Qed.
End bytes.

(** ## Storing a word into owned bytes *)

Section store.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance store_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A 64-bit store replaces eight owned bytes with the little-endian bytes
    of the stored integer. The bytes before the store may hold anything,
    so the rule asks for ownership of the bytes rather than of an integer
    cell. *)
Lemma wp_raw_store_l_bytes f e ls l off v a rest j p b reg o xs y Φ :
  value_x ge e L v = Some (WInt y) -> value_x ge e A a = Some (WPtr p) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> length xs = 8%nat ->
  (forall m wd h, (forall l v, (l, v) ∈ (PLive b, VLive reg) :: byte_ps b o xs -> h !! l = Some v) ->
     wi m wd h ->
     wi (store_bytes m (b + o) 8 y) wd (overwrite ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 8)) h)) ->
  live b reg -∗ bytes b o xs -∗
  ▷ (live b reg -∗ bytes b o (le_bytes y 8) -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Wl off v a :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hv Ha Hp Hoff Hlen Hwi. iIntros "Hl Hx HK".
  iApply (wp_write _ _ _ ((PLive b, VLive reg) :: byte_ps b o xs) ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 8))
            _ _ [] (fun m => store_bytes m (b + o) 8 y) with "[Hl Hx] [HK]");
    [cbn [fmap list_fmap fst]; rewrite !byte_ps_keys length_le_bytes Hlen; reflexivity | | exact Hwi |
     rewrite /live /bytes /pts !big_sepL_cons big_sepL_nil; iFrame; iDestruct "Hl" as "[$ _]" |].
  - intros m fuel (Hf & Hd & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [Hlv Hx].
    destruct (store_after m b reg o xs y Hd Hlv Hx) as [Hag Hfr]. rewrite Hlen in Hag Hfr. cbn in Hag, Hfr.
    assert (Hb : forall i, (i < 8)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
    { intros i Hi. rewrite <- Hlen in Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
      destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hx Hxi) as (_ & H1 & H2). lia. }
    destruct (Hb 0%nat ltac:(lia)) as [H0 _]. destruct (Hb 7%nat ltac:(lia)) as [_ H7]. cbn in H0, H7.
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_raw_store with (vk := L) (x := WInt y) (p := p); [reflexivity | exact Hv | exact Ha |].
      rewrite Hoff. apply store_res_long. rewrite Hp.
      apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
    + apply store_bytes_kept. intros a' Ha'. exists b, reg. split; [exact (proj1 Hlv)|lia].
    + cbn [all_agree agree_piece fst snd]. split; [exact Hlv | exact Hag].
    + intros l' v' Hn Ha'. apply Hfr; [|exact Ha'].
      intros Hin. apply Hn. cbn [fmap list_fmap fst]. apply elem_of_cons. right.
      rewrite byte_ps_keys length_le_bytes. rewrite byte_ps_keys Hlen in Hin. exact Hin.
  - iNext. iIntros "H".
    iDestruct (pts_app [(PLive b, VLive reg)] (byte_ps b o (le_bytes y 8)) with "H") as "[Hl Hx]".
    iApply ("HK" with "Hl Hx").
Qed.
End store.
