(** A call of an outside function may write a few bytes in the middle
    of an object, and the program logic then wants exactly those bytes
    lent to it. The frame of [AbsSound](AbsSound.v) owns the contents
    of its state as one list of pieces, which [AbsOwn](AbsOwn.v)
    defines. This module splits that list into the pieces of one
    window and the rest. The rest is the same list whatever the window
    holds, so the window can be given back with new contents.

    Several windows may lie in one object. The module therefore also
    describes the pieces of a state without a set of keys. A window is
    taken out of what is left after the earlier windows, and the
    lemmas at the end say when that works. *)

From Stdlib Require Import ssreflect ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap StringLogic MemLogic
  AbsRun AbsDen AbsMem AbsStep AbsOwn.
Import ListNotations.
Open Scope Z_scope.

(** * One window *)

Lemma list_set_twice {A : Type} o (x y : A) : forall l, list_set o y (list_set o x l) = list_set o y l.
Proof using Type. induction o as [|o IH]; intros [|z l]; cbn [list_set]; try reflexivity. by rewrite IH. Qed.

(** The pieces of a state are the pieces of one of its objects
    together with the pieces of the state without that object. *)
Lemma all_ps_take B : forall X o pl xs cs,
  nth_error B o = Some pl -> nth_error X o = Some (Some (xs, cs)) ->
  all_ps B X ≡ₚ place_ps pl xs cs ++ all_ps B (list_set o None X).
Proof using Type.
  induction B as [|pl0 B IH]; intros X o pl xs cs Hp Hx; [by destruct o|].
  destruct X as [|x X]; [by destruct o|]. destruct o as [|o]; cbn [nth_error list_set] in *.
  - injection Hp as ->. injection Hx as ->. reflexivity.
  - cbn [all_ps]. pose proof (IH X o pl xs cs Hp Hx) as E. destruct x as [[xs0 cs0]|]; [|exact E].
    rewrite E !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
Qed.

(** The pieces of a window are its bytes and its shadow slots, and
    their keys depend only on where the window is and how wide it is. *)
Definition win_ps (b k : Z) (ys : list Z) (ds : list cap) : list (piece * pval) :=
  byte_ps b k ys ++ aux_ps b k ds.

Definition win_keys (b k n : Z) : list piece := (PByte b <$> seqZ k n) ++ (PAux b <$> seqZ k n).

Lemma win_ps_keys b k ys ds n :
  Z.of_nat (length ys) = n -> Z.of_nat (length ds) = n -> (win_ps b k ys ds).*1 = win_keys b k n.
Proof using Type. intros <- E. rewrite /win_ps /win_keys fmap_app byte_ps_keys aux_ps_keys E. reflexivity. Qed.

(** The list [rest_ps] holds everything that an object owns outside a
    window. It holds the lifetime of the object, and the bytes and
    shadow slots that come before and after the window. *)
Definition rest_ps (pl : place) (k n : nat) (xs : list Z) (cs : list cap) : list (piece * pval) :=
  (PLive (pl_base pl), VLive (pl_reg pl)) ::
  (byte_ps (pl_base pl) 0 (take k xs) ++ byte_ps (pl_base pl) (Z.of_nat (k + n)) (drop (k + n) xs)) ++
  (aux_ps (pl_base pl) 0 (take k cs) ++ aux_ps (pl_base pl) (Z.of_nat (k + n)) (drop (k + n) cs)).

Lemma place_ps_splice pl k xs cs ys ds :
  0 <= k -> k + Z.of_nat (length ys) <= Z.of_nat (length xs) -> length ds = length ys -> length cs = length xs ->
  place_ps pl (splice k ys xs) (splice k ds cs) ≡ₚ
  win_ps (pl_base pl) k ys ds ++ rest_ps pl (Z.to_nat k) (length ys) xs cs.
Proof using Type.
  intros Hk Hn Ld Lc. rewrite /place_ps /block_ps /splice /win_ps /rest_ps Ld.
  rewrite !byte_ps_app !aux_ps_app !length_take.
  replace (0 + Z.of_nat (Z.to_nat k `min` length xs)) with k by lia.
  replace (0 + Z.of_nat (Z.to_nat k `min` length cs)) with k by lia.
  replace (k + Z.of_nat (length ys)) with (Z.of_nat (Z.to_nat k + length ys)) by lia.
  replace (k + Z.of_nat (length ds)) with (Z.of_nat (Z.to_nat k + length ys)) by lia.
  set (A := byte_ps _ 0 _). set (W := byte_ps _ k _). set (C := byte_ps _ _ (drop _ _)).
  set (A' := aux_ps _ 0 _). set (W' := aux_ps _ k _). set (C' := aux_ps _ _ (drop _ _)).
  set (lv := (PLive _, _)). change (lv :: ?l) with ([lv] ++ l). solve_Permutation.
Qed.

Lemma splice_window {A : Type} k n (l : list A) :
  0 <= k -> k + Z.of_nat n <= Z.of_nat (length l) -> splice k (window k (Z.of_nat n) l) l = l.
Proof using Type.
  intros Hk Hn. rewrite /splice /window Nat2Z.id length_take length_drop.
  replace (Z.to_nat k + n `min` (length l - Z.to_nat k))%nat with (Z.to_nat k + n)%nat by lia.
  rewrite -drop_drop take_drop. apply take_drop.
Qed.

Lemma length_window' {A : Type} k n (l : list A) :
  0 <= k -> k + Z.of_nat n <= Z.of_nat (length l) -> length (window k (Z.of_nat n) l) = n.
Proof using Type. intros Hk Hn. rewrite /window Nat2Z.id length_take length_drop. lia. Qed.

(** One window of one object splits the pieces of a state. The second
    part of the lemma says that the state with new contents in the
    window has the same pieces outside it. *)
Lemma all_ps_window B X o pl xs cs k n :
  nth_error B o = Some pl -> nth_error X o = Some (Some (xs, cs)) ->
  0 <= k -> k + Z.of_nat n <= Z.of_nat (length xs) -> length cs = length xs ->
  exists R,
    all_ps B X ≡ₚ win_ps (pl_base pl) k (window k (Z.of_nat n) xs) (window k (Z.of_nat n) cs) ++ R /\
    forall ys ds, length ys = n -> length ds = n ->
      all_ps B (list_set o (Some (splice k ys xs, splice k ds cs)) X) ≡ₚ win_ps (pl_base pl) k ys ds ++ R.
Proof using Type.
  intros Hp Hx Hk Hn Lc. exists (rest_ps pl (Z.to_nat k) n xs cs ++ all_ps B (list_set o None X)). split.
  - rewrite (all_ps_take B X o pl xs cs Hp Hx) app_assoc. apply Permutation_app_tail.
    rewrite -{1}(splice_window k n xs Hk Hn) -{1}(splice_window k n cs Hk ltac:(lia)).
    rewrite place_ps_splice ?length_window'; try lia. done.
  - intros ys ds Ly Ld.
    rewrite (all_ps_take B _ o pl (splice k ys xs) (splice k ds cs) Hp).
    + rewrite list_set_twice app_assoc. apply Permutation_app_tail.
      rewrite place_ps_splice; [by rewrite Ly | lia..].
    + rewrite nth_error_list_set Nat.eqb_refl Hx. done.
Qed.

(** * Pieces without a set of keys

    The list [but K ps] holds the pieces of ps whose key is not in K,
    and [only K ps] holds the others. *)

Fixpoint but (K : list piece) (ps : list (piece * pval)) : list (piece * pval) :=
  match ps with
  | [] => []
  | lv :: ps' => match decide (lv.1 ∈ K) with left _ => but K ps' | right _ => lv :: but K ps' end
  end.

Fixpoint only (K : list piece) (ps : list (piece * pval)) : list (piece * pval) :=
  match ps with
  | [] => []
  | lv :: ps' => match decide (lv.1 ∈ K) with left _ => lv :: only K ps' | right _ => only K ps' end
  end.

Lemma but_nil ps : but [] ps = ps.
Proof using Type.
  induction ps as [|lv ps IH]; [done|]. cbn [but]. case_decide as H; [by apply elem_of_nil in H | by rewrite IH].
Qed.

Lemma only_but_perm K ps : ps ≡ₚ only K ps ++ but K ps.
Proof using Type.
  induction ps as [|lv ps IH]; [done|]. cbn [only but]. case_decide.
  - cbn [app]. by rewrite -IH.
  - rewrite -Permutation_middle. by rewrite -IH.
Qed.

Lemma but_but K1 K2 ps : but K1 (but K2 ps) = but (K1 ++ K2) ps.
Proof using Type.
  induction ps as [|lv ps IH]; [done|]. cbn [but]. case_decide as H2.
  - rewrite IH. case_decide as H; [done|]. exfalso. apply H, elem_of_app. by right.
  - cbn [but]. rewrite IH. case_decide as H1; case_decide as H; try done.
    + exfalso. apply H, elem_of_app. by left.
    + exfalso. apply elem_of_app in H as [?|?]; done.
Qed.

Lemma but_app K ps qs : but K (ps ++ qs) = but K ps ++ but K qs.
Proof using Type. induction ps as [|lv ps IH]; [done|]. cbn [app but]. case_decide; by rewrite IH. Qed.

Lemma only_app K ps qs : only K (ps ++ qs) = only K ps ++ only K qs.
Proof using Type. induction ps as [|lv ps IH]; [done|]. cbn [app only]. case_decide; by rewrite IH. Qed.

Lemma but_perm K ps qs : ps ≡ₚ qs -> but K ps ≡ₚ but K qs.
Proof using Type.
  induction 1 as [|lv ps qs _ IH|a b ps|ps qs rs _ IH1 _ IH2]; [done| | |by rewrite IH1].
  - cbn [but]. case_decide; by rewrite IH.
  - cbn [but]. repeat case_decide; try done. apply perm_swap.
Qed.

Lemma only_perm K ps qs : ps ≡ₚ qs -> only K ps ≡ₚ only K qs.
Proof using Type.
  induction 1 as [|lv ps qs _ IH|a b ps|ps qs rs _ IH1 _ IH2]; [done| | |by rewrite IH1].
  - cbn [only]. case_decide; by rewrite IH.
  - cbn [only]. repeat case_decide; try done. apply perm_swap.
Qed.

Lemma but_in K ps : (forall lv, lv ∈ ps -> lv.1 ∈ K) -> but K ps = [].
Proof using Type.
  induction ps as [|lv ps IH]; [done|]. intros H. cbn [but]. case_decide as Hd; [|exfalso; apply Hd, H; by left].
  apply IH. intros lv' Hin. apply H. by right.
Qed.

Lemma only_in K ps : (forall lv, lv ∈ ps -> lv.1 ∈ K) -> only K ps = ps.
Proof using Type.
  induction ps as [|lv ps IH]; [done|]. intros H. cbn [only]. case_decide as Hd; [|exfalso; apply Hd, H; by left].
  f_equal. apply IH. intros lv' Hin. apply H. by right.
Qed.

Lemma only_out K ps : (forall lv, lv ∈ ps -> lv.1 ∉ K) -> only K ps = [].
Proof using Type.
  induction ps as [|lv ps IH]; [done|]. intros H. cbn [only].
  case_decide as Hd; [exfalso; exact (H lv ltac:(by left) Hd)|].
  apply IH. intros lv' Hin. apply H. by right.
Qed.

Lemma only_of_but Kw K ps : (forall l, l ∈ Kw -> l ∉ K) -> only Kw (but K ps) = only Kw ps.
Proof using Type.
  intros Hd. induction ps as [|lv ps IH]; [done|]. cbn [but only]. case_decide as HK.
  - rewrite IH. case_decide as Hw; [exfalso; exact (Hd _ Hw HK) | done].
  - cbn [only]. by rewrite IH.
Qed.

Lemma elem_of_but K ps lv : lv ∈ ps -> lv.1 ∉ K -> lv ∈ but K ps.
Proof using Type.
  induction ps as [|lv' ps IH]; [by intros H; apply elem_of_nil in H|]. intros Hin Hn.
  cbn [but]. apply elem_of_cons in Hin as [->|Hin].
  - case_decide; [done | by left].
  - case_decide; [by apply IH|]. right. by apply IH.
Qed.

(** A window whose keys are not among the keys already taken can be
    taken next, when no key occurs twice in the list. *)
Lemma but_take K Kw ps W R :
  ps ≡ₚ W ++ R -> NoDup ps.*1 -> W.*1 = Kw -> (forall l, l ∈ Kw -> l ∉ K) ->
  but K ps ≡ₚ W ++ but (Kw ++ K) ps.
Proof using Type.
  intros Hp Hnd HW Hd. rewrite {1}(only_but_perm Kw (but K ps)) but_but. apply Permutation_app_tail.
  rewrite (only_of_but Kw K ps Hd) (only_perm Kw _ _ Hp) only_app.
  assert (E1 : only Kw W = W).
  { apply only_in. intros lv Hin. rewrite -HW. by apply list_elem_of_fmap_2. }
  assert (E2 : only Kw R = []).
  { apply only_out. intros lv Hin Hk. rewrite Hp fmap_app in Hnd. apply NoDup_app in Hnd as (_ & Hno & _).
    apply (Hno lv.1); [by rewrite HW|]. by apply list_elem_of_fmap_2. }
  by rewrite E1 E2 app_nil_r.
Qed.

(** Two lists that differ only in pieces whose keys were taken are the
    same without those keys. *)
Lemma but_same K ps ps' W W' R :
  ps ≡ₚ W ++ R -> ps' ≡ₚ W' ++ R -> (forall lv, lv ∈ W -> lv.1 ∈ K) -> (forall lv, lv ∈ W' -> lv.1 ∈ K) ->
  but K ps ≡ₚ but K ps'.
Proof using Type.
  intros Hp Hp' HW HW'. rewrite (but_perm K _ _ Hp) (but_perm K _ _ Hp') !but_app.
  by rewrite (but_in K W HW) (but_in K W' HW').
Qed.

(** * Taking windows in turn

    The two lemmas below are what a proof uses. The first takes a
    window out of a state from which the keys K are already gone. The
    second puts a window with new contents into the state, and it also
    says that no key occurs twice afterwards. *)

Lemma win_take K B X o pl xs cs k n :
  nth_error B o = Some pl -> nth_error X o = Some (Some (xs, cs)) ->
  0 <= k -> k + Z.of_nat n <= Z.of_nat (length xs) -> length cs = length xs ->
  NoDup (all_ps B X).*1 -> (forall l, l ∈ win_keys (pl_base pl) k (Z.of_nat n) -> l ∉ K) ->
  but K (all_ps B X) ≡ₚ
  win_ps (pl_base pl) k (window k (Z.of_nat n) xs) (window k (Z.of_nat n) cs) ++
  but (win_keys (pl_base pl) k (Z.of_nat n) ++ K) (all_ps B X).
Proof using Type.
  intros Hp Hx Hk Hn Lc Hnd Hd. destruct (all_ps_window B X o pl xs cs k n Hp Hx Hk Hn Lc) as (R & H1 & _).
  apply (but_take K _ _ _ R H1 Hnd); [|exact Hd].
  apply win_ps_keys; rewrite length_window'; lia.
Qed.

Lemma win_give K B X o pl xs cs k n ys ds :
  nth_error B o = Some pl -> nth_error X o = Some (Some (xs, cs)) ->
  0 <= k -> k + Z.of_nat n <= Z.of_nat (length xs) -> length cs = length xs ->
  length ys = n -> length ds = n ->
  NoDup (all_ps B X).*1 -> (forall l, l ∈ win_keys (pl_base pl) k (Z.of_nat n) -> l ∉ K) ->
  NoDup (all_ps B (list_set o (Some (splice k ys xs, splice k ds cs)) X)).*1 /\
  but K (all_ps B (list_set o (Some (splice k ys xs, splice k ds cs)) X)) ≡ₚ
  win_ps (pl_base pl) k ys ds ++ but (win_keys (pl_base pl) k (Z.of_nat n) ++ K) (all_ps B X).
Proof using Type.
  intros Hp Hx Hk Hn Lc Ly Ld Hnd Hd.
  destruct (all_ps_window B X o pl xs cs k n Hp Hx Hk Hn Lc) as (R & H1 & H2). specialize (H2 ys ds Ly Ld).
  set (W := win_ps _ k (window _ _ xs) _) in H1. set (W' := win_ps _ k ys ds) in *.
  set (Kw := win_keys _ _ _) in *.
  assert (EW : W.*1 = Kw) by (apply win_ps_keys; rewrite length_window'; lia).
  assert (EW' : W'.*1 = Kw) by (apply win_ps_keys; lia).
  assert (Hnd' : NoDup (all_ps B (list_set o (Some (splice k ys xs, splice k ds cs)) X)).*1).
  { rewrite H2 fmap_app EW' -EW -fmap_app -H1. exact Hnd. }
  split; [exact Hnd'|]. rewrite (but_take K Kw _ W' R H2 Hnd' EW' Hd). apply Permutation_app_head.
  apply (but_same _ _ _ W' W R H2 H1); intros lv Hin; apply elem_of_app; left.
  - rewrite -EW'. by apply list_elem_of_fmap_2.
  - rewrite -EW. by apply list_elem_of_fmap_2.
Qed.

(** Two windows have no key in common when they lie in different
    objects or at offsets that do not overlap. *)
Lemma win_keys_apart b k n b' k' n' l :
  b <> b' \/ k + n <= k' \/ k' + n' <= k -> l ∈ win_keys b k n -> l ∉ win_keys b' k' n'.
Proof using Type.
  intros Ha H1 H2. unfold win_keys in *.
  apply elem_of_app in H1 as [H1|H1]; apply list_elem_of_fmap in H1 as (i & -> & Hi);
    apply elem_of_app in H2 as [H2|H2]; apply list_elem_of_fmap in H2 as (i' & [=] & Hi');
    subst; apply elem_of_seqZ in Hi; apply elem_of_seqZ in Hi'; lia.
Qed.

(** The lifetime of an object with contents is among the pieces of
    the state, and it stays when windows are taken. *)
Lemma all_ps_live K B X o pl xs cs kn :
  nth_error B o = Some pl -> nth_error X o = Some (Some (xs, cs)) ->
  (forall l, l ∈ K -> exists b k, l ∈ win_keys b k kn) ->
  (PLive (pl_base pl), VLive (pl_reg pl)) ∈ but K (all_ps B X).
Proof using Type.
  intros Hp Hx HK. apply elem_of_but.
  - rewrite (all_ps_take B X o pl xs cs Hp Hx). apply elem_of_app. left. by left.
  - cbn [fst]. intros Hin. destruct (HK _ Hin) as (b & k & Hw). unfold win_keys in Hw.
    apply elem_of_app in Hw as [Hw|Hw]; by apply list_elem_of_fmap in Hw as (i & [=] & _).
Qed.

(** Two objects with contents have different bases when no key
    occurs twice, because each contributes the key of its lifetime. *)
Lemma all_ps_bases B X o pl xs cs o' pl' xs' cs' :
  nth_error B o = Some pl -> nth_error X o = Some (Some (xs, cs)) ->
  nth_error B o' = Some pl' -> nth_error X o' = Some (Some (xs', cs')) ->
  o <> o' -> NoDup (all_ps B X).*1 -> pl_base pl <> pl_base pl'.
Proof using Type.
  intros Hp Hx Hp' Hx' Hne Hnd E.
  rewrite (all_ps_take B X o pl xs cs Hp Hx) in Hnd.
  assert (Hx2 : nth_error (list_set o None X) o' = Some (Some (xs', cs'))).
  { rewrite nth_error_list_set. destruct (Nat.eqb_spec o' o); [congruence | exact Hx']. }
  rewrite (all_ps_take B (list_set o None X) o' pl' xs' cs' Hp' Hx2) in Hnd.
  rewrite fmap_app in Hnd. apply NoDup_app in Hnd as (_ & Hno & _). apply (Hno (PLive (pl_base pl))).
  - by left.
  - rewrite fmap_app. apply elem_of_app. left. rewrite E. by left.
Qed.
