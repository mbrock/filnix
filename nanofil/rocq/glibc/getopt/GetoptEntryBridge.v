(** Every call of glibc's getopt first sets up its private object: a
    fresh call fills it in, and a later call picks up where the last one
    stopped. Then the call either looks for the next argument or goes on
    with a group of short options that it had started. Two parts of the
    proof meet here. One part treats the object as a whole, and the
    other reads its fields one at a time. This file turns one view into
    the other, and it also keeps what is known about the saved position
    inside the current word. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv WordString GetoptBytes GetoptState GetoptEntry GetoptLongSession.
Import ListNotations.
Open Scope Z_scope.

(** These controls show the two ways the entry blocks set the index. A
    fresh object with index 0 starts at index 1, and both ends of the
    nonoption interval start there too. *)
Lemma entry_ctl_init_zero : gs_ind (init_state (mkGetoptState 0 1 0 null 0 null 0 0 0) 1) = 1 /\
  gs_first (init_state (mkGetoptState 0 1 0 null 0 null 0 0 0) 1) = 1.
Proof. split; reflexivity. Qed.

(** An object that has not been initialized keeps a nonzero index. *)
Lemma entry_ctl_init_keep : gs_ind (init_state (mkGetoptState 3 1 0 null 0 null 0 0 0) 0) = 3.
Proof. reflexivity. Qed.

(** A resumed call clears the returned argument but keeps the cursor. *)
Lemma entry_ctl_clear : gs_arg (clear_arg (mkGetoptState 2 1 0 (mkPtr 9 CNone) 1 (mkPtr 7 CNone) 0 1 1)) = null /\
  gs_next (clear_arg (mkGetoptState 2 1 0 (mkPtr 9 CNone) 1 (mkPtr 7 CNone) 0 1 1)) = mkPtr 7 CNone.
Proof. split; reflexivity. Qed.

(** In the word "-ab" with the prefix "-a", the cursor sits at byte 2,
    which holds "b". A cursor at byte 3 would sit on the terminator,
    which the condition on the offset rules out. *)
Lemma entry_ctl_offset : (2 < length [45; 97; 98])%nat /\ sbyte [45; 97; 98] 2 = 98 /\
  ~ (3 < length [45; 97; 98])%nat.
Proof. unfold sbyte. cbn. repeat split; lia. Qed.

(** An element that [nth_error] finds is the element at that index. *)
Lemma entry_nth_error (l : list ptr) k x : nth_error l k = Some x -> l !! k = Some x.
Proof. revert k. induction l as [|y l IH]; intros [|k] H; cbn in *; try discriminate; auto. Qed.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptEntryBridgeOn (R : Runtime) (LG0 : LogicSig R).
(** The session module supplies the state, the byte rules and the byte agreement of two views. *)
Module LSS := GetoptLongSessionOn R LG0.
Import LSS LSS.S LSS.S.FI LSS.S.FI.ML LSS.S.FI.LG LSS.S.FI.L.

Section bridge.
Context `{!gen_heapGS piece pval Σ}.

(** The cursor relation holds only shared strings and pure facts, so it may be used twice. *)
Local Instance entry_cursor_persistent ps i s : Persistent (getopt_cursor ps i s).
Proof. unfold getopt_cursor. apply _. Qed.

(** A caller that wants to call getopt again holds what the previous
    call left behind, called a session. The first blocks of the call
    need the private object, a bound on its index, and the text after
    the saved position. This lemma hands them over and keeps the rest of
    what the session knew, so that the later steps can still use it. *)
Lemma entry_pre b r av ar ps i :
  getopt_session b r av ar ps i ⊢ ∃ s tail,
    ⌜0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ ∗
    getopt_state_own b r s ∗ ⌜getopt_bounds (Z.of_nat (length ps)) i s /\ 0 <= gs_ind s <= Z.of_nat (length ps)⌝ ∗
    (⌜s = getopt_zero /\ i = 1⌝ ∨ (⌜gs_initialized s = 1 /\ gs_ind s = i /\ 0 <= gs_order s <= 2⌝ ∗ getopt_cursor ps i s)) ∗
    (⌜gs_next s = null⌝ ∨ word_string DfracDiscarded (gs_next s) tail).
Proof.
  iIntros "[%Hav (%s & Hs & %Hbd & Hk)]".
  iDestruct "Hk" as "[[%Hz %Hi] | [%Hin #Hcu]]".
  - iExists s, []. iFrame "Hs". iSplit; [done|]. iSplit; [iPureIntro; subst; split; [exact Hbd | unfold getopt_bounds in Hbd; cbn in *; lia]|].
    iSplit; [by iLeft|]. iLeft. by subst.
  - iDestruct "Hcu" as "[%Hn | [#H0 | (%q & %prefix & %suffix & %Hc & #Hw)]]".
    + iExists s, []. iFrame "Hs". iSplit; [done|]. iSplit; [iPureIntro; split; [exact Hbd | unfold getopt_bounds in Hbd; lia]|].
      iSplit; [iRight; iSplit; [done|]; by iLeft|]. by iLeft.
    + iExists s, []. iFrame "Hs". iSplit; [done|]. iSplit; [iPureIntro; split; [exact Hbd | unfold getopt_bounds in Hbd; lia]|].
      iSplit; [iRight; iSplit; [done|]; iRight; by iLeft|]. by iRight.
    + iExists s, suffix. iFrame "Hs". iSplit; [done|]. iSplit; [iPureIntro; split; [exact Hbd | unfold getopt_bounds in Hbd; lia]|].
      iSplit; [iRight; iSplit; [done|]; iRight; iRight; iExists q, prefix, suffix; by iSplit|].
      iRight. destruct Hc as (_ & _ & _ & -> & _). by iApply word_string_suffix.
Qed.

(** When the call goes on to look for the next argument, the code that
    does so reads the fields of the object one by one. This lemma splits
    the object into those fields. It also says that the object is set
    up, that its mode is one of three, that its limits hold, that the
    returned argument is cleared, and that the saved position is null or
    sits at the end of a string. *)
Lemma entry_select b r (ps : list ptr) i s s' (tail : list Z) :
  getopt_bounds (Z.of_nat (length ps)) i s ->
  (s = getopt_zero /\ i = 1 \/ gs_initialized s = 1 /\ gs_ind s = i /\ 0 <= gs_order s <= 2) ->
  entry_state s s' -> gs_next s' = null \/ tail = [] ->
  (⌜gs_next s = null⌝ ∨ word_string DfracDiscarded (gs_next s) tail) -∗ getopt_state_own b r s' -∗
  ⌜0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\ gs_initialized s' = 1 /\
    0 <= gs_order s' <= 2 /\ getopt_bounds (Z.of_nat (length ps)) (gs_ind s') s' /\ gs_arg s' = null /\
    gs_ind s' = (if i =? 0 then 1 else i)⌝ ∗
  live b r ∗ int_cell b 0 (gs_ind s') ∗ int_cell b 4 (gs_err s') ∗ int_cell b 8 (gs_opt s') ∗
  pcell b 16 (gs_arg s') ∗ int_cell b 24 (gs_initialized s') ∗ pcell b 32 (gs_next s') ∗
  int_cell b 40 (gs_order s') ∗ int_cell b 44 (gs_first s') ∗ int_cell b 48 (gs_last s') ∗
  (⌜gs_next s' = null⌝ ∨ word_string DfracDiscarded (gs_next s') []).
Proof.
  intros Hbd Hk Hst Hnt. iIntros "#Hc (%Hb & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla)". iFrame.
  unfold getopt_bounds in Hbd. destruct Hst as [(Hni & o & Ho & ->) | (Hni & ->)].
  - iSplit; [|by iLeft]. iPureIntro. destruct Hk as [[-> ->] | (Hin & Hi & Hor)].
    + unfold init_state, getopt_bounds; cbn. repeat split; try reflexivity; lia.
    + unfold init_state. rewrite Hi. destruct (Z.eqb_spec i 0); unfold getopt_bounds; cbn; repeat split; try reflexivity; lia.
  - destruct Hk as [[-> _] | (Hin & Hi & Hor)]; [exfalso; apply Hni; left; reflexivity|].
    iSplit.
    + iPureIntro. unfold needs_init in Hni. unfold clear_arg, getopt_bounds; cbn.
      destruct (Z.eqb_spec i 0); subst; repeat split; try reflexivity; lia.
    + cbn. destruct Hnt as [Hn0 | ->]; [by iLeft|]. iDestruct "Hc" as "[%Hn0 | Hw]"; [by iLeft | by iRight].
Qed.

(** When the call goes on with a group of short options, it needs to
    know where it is in the current word. The call did not start over,
    so the object is the one the caller had, with the returned argument
    cleared. The session then says which word of the argument list holds
    the saved position, how many bytes into it the position lies, and
    that the byte there is not the end of the word. The session's case
    with an empty text cannot occur here, because the text after the
    saved position is not empty. *)
Lemma entry_cluster b r ps i s s' (tail : list Z) :
  getopt_bounds (Z.of_nat (length ps)) i s ->
  entry_state s s' -> ~ needs_init s -> gs_next s' <> null -> tail <> [] ->
  (⌜s = getopt_zero /\ i = 1⌝ ∨ (⌜gs_initialized s = 1 /\ gs_ind s = i /\ 0 <= gs_order s <= 2⌝ ∗ getopt_cursor ps i s)) -∗
  word_string DfracDiscarded (gs_next s) tail -∗ getopt_state_own b r s' -∗
  ∃ q sq k0, ⌜s' = clear_arg s /\ gs_ind s = i /\ gs_initialized s = 1 /\ 0 <= gs_order s <= 2 /\
      0 <= i < Z.of_nat (length ps) /\ ps !! Z.to_nat i = Some q /\ (k0 < length sq)%nat /\ sbyte sq k0 <> 0 /\
      gs_next s = ptr_add q (Z.of_nat k0) /\ gs_last s <= i /\
      0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48⌝ ∗
    word_string DfracDiscarded q sq ∗ word_string DfracDiscarded (gs_next s) (drop k0 sq) ∗
    live b r ∗ int_cell b 0 i ∗ int_cell b 4 (gs_err s) ∗ int_cell b 8 (gs_opt s) ∗ pcell b 16 null ∗
    int_cell b 24 1 ∗ pcell b 32 (gs_next s) ∗ int_cell b 40 (gs_order s) ∗ int_cell b 44 (gs_first s) ∗
    int_cell b 48 (gs_last s).
Proof.
  intros Hbd Hst Hni Hnn Htn. iIntros "Hk #Ht (%Hb & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla)".
  destruct Hst as [(Hni' & _) | (_ & ->)]; [done|].
  iDestruct "Hk" as "[[%Hz _] | [(%Hin & %Hi & %Hor) #Hcu]]".
  { exfalso. apply Hni. subst. left. reflexivity. }
  iDestruct (GB.ws_shape with "Ht") as %(Htc & _ & _).
  iDestruct "Hcu" as "[%Hn | [#H0 | (%q & %prefix & %suffix & %Hc & #Hw)]]".
  - exfalso. apply Hnn. exact Hn.
  - iDestruct (short_byte_agree _ [] tail 0 with "H0 Ht") as %E; [cbn; lia | lia |].
    exfalso. destruct tail as [|t0 tl]; [done|]. inversion Htc as [|? ? Ht0 _]; subst.
    unfold sbyte in E. cbn in E. lia.
  - destruct Hc as (Hi0 & Hq & Hsne & Hnx & Hla').
    iDestruct (GB.ws_shape with "Hw") as %(Hwc & _ & _).
    iExists q, (prefix ++ suffix), (length prefix).
    assert (Hd : drop (length prefix) (prefix ++ suffix) = suffix) by (by rewrite drop_app_length).
    iSplit.
    + iPureIntro. destruct suffix as [|c0 rest]; [done|].
      split; [reflexivity|]. split; [exact Hi|]. split; [exact Hin|]. split; [exact Hor|]. split; [exact Hi0|].
      split; [by apply entry_nth_error|].
      split; [rewrite length_app; cbn; lia|].
      split; [|split; [exact Hnx|]; split; [exact Hla'|]; exact Hb].
      unfold sbyte. rewrite app_nth1; [|rewrite length_app; cbn; lia]. rewrite app_nth2; [|lia].
      rewrite Nat.sub_diag. cbn. rewrite Forall_app in Hwc. destruct Hwc as [_ Hwc]. inversion Hwc. lia.
    + rewrite Hd. iFrame "Hw". iSplit; [rewrite Hnx; by iApply word_string_suffix|].
      cbn [clear_arg gs_ind gs_err gs_opt gs_arg gs_initialized gs_next gs_order gs_first gs_last].
      rewrite Hi Hin. iFrame.
Qed.

End bridge.
End GetoptEntryBridgeOn.
