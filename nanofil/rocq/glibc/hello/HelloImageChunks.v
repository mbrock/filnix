(** The linked Hello image is too large for one Rocq file to hold or to
    decode, so its term arrives as many lists of items that are joined in
    order. A proof about the whole image needs its decoded module, the
    erasure of that module, and the check that no zero run is negative.
    This file shows that each of these can be computed one list at a time
    and then joined, so no single file has to decode the whole term. The
    lemmas are generic and say nothing about any particular image. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Semantics Transport.
From Glibc Require Import HelloImageErase HelloImageEraseMem.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Decoding a list of items *)

(** The module decoder decodes each item term, fails when any one fails,
    and drops the context annotations. These are the same steps applied
    to a bare list of item terms. *)
Definition decode_items (l : list term) : option module :=
  match map_option ditem l with
  | Some its => Some (flat_map (fun o => match o with Some i => [i] | None => [] end) its)
  | None => None
  end.

(** Decoding a module term is decoding its list of items. *)
Lemma decode_module_items l : decode_module (TApp "module" [TList l]) = decode_items l.
Proof. reflexivity. Qed.

(** Decoding a joined list succeeds when decoding each part does, and
    gives the joined parts. *)
Lemma map_option_app {X Y : Type} (f : X -> option Y) xs ys a b :
  map_option f xs = Some a -> map_option f ys = Some b -> map_option f (xs ++ ys) = Some (a ++ b).
Proof.
  revert a. induction xs as [|x xs IH]; intros a Hx Hy; cbn [map_option app] in *.
  - injection Hx as <-. exact Hy.
  - destruct (f x) as [y|]; [|discriminate Hx]. destruct (map_option f xs) as [a'|] eqn:E; [|discriminate Hx].
    injection Hx as <-. rewrite (IH a' eq_refl Hy). reflexivity.
Qed.

Lemma decode_items_app xs ys a b :
  decode_items xs = Some a -> decode_items ys = Some b -> decode_items (xs ++ ys) = Some (a ++ b).
Proof.
  unfold decode_items. destruct (map_option ditem xs) as [ia|] eqn:Ex; [|discriminate].
  destruct (map_option ditem ys) as [ib|] eqn:Ey; [|discriminate]. intros Ha Hb. injection Ha as <-. injection Hb as <-.
  rewrite (map_option_app _ _ _ _ _ Ex Ey). rewrite flat_map_app. reflexivity.
Qed.

(** ## Erasing and checking a joined module *)

(** The erasure works item by item, so it erases each part on its own. *)
Lemma erase_app keep a b : erase keep (a ++ b) = erase keep a ++ erase keep b.
Proof. apply map_app. Qed.

(** The zero-run check holds for a joined module when it holds for each part. *)
Lemma zero_nonneg_app a b : zero_nonneg (a ++ b) = zero_nonneg a && zero_nonneg b.
Proof. apply forallb_app. Qed.

(** ## Controls

    Two item lists decode separately, and the decoded parts join into the
    module that decoding the joined term gives. A list with a term that is
    not an item fails to decode, and so does every list that contains it. *)

Local Definition part1 : list term :=
  [TApp "data" [TAtom "x"; TAtom "export"; TInt 8; TList [TApp "zero" [TInt 8]]]].
Local Definition part2 : list term :=
  [TApp "alias" [TAtom "a"; TAtom "export"; TAtom "x"]; TApp "context" [TAtom "c"; TAtom "d"]].
Local Definition bad : list term := [TAtom "not_an_item"].

Lemma parts_join : exists a b, decode_items part1 = Some a /\ decode_items part2 = Some b /\
  decode_module (TApp "module" [TList (part1 ++ part2)]) = Some (a ++ b) /\ length (a ++ b) = 2%nat.
Proof.
  do 2 eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  rewrite decode_module_items. split; [apply decode_items_app; vm_compute; reflexivity|]. reflexivity.
Qed.

Lemma bad_refused : decode_items bad = None /\ decode_items (part1 ++ bad ++ part2) = None.
Proof. split; vm_compute; reflexivity. Qed.
