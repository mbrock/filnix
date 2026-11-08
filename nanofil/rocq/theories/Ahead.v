(** Campaign 3's scheduled checks: what the validator's backward pass
    for `check_ahead` computes, point by point (docs/formal.md,
    Campaign 3; docs/rocq.md, "Scheduled checks"; docs/schedule.md).

    `ahead_justified/3` walks a function's blocks once, from the last,
    and each block's instructions from its jump. At each point it keeps
    *needs*: a single-definition base N with an offset H, meaning that
    every path from the point reaches, through ahead-transparent
    instructions only and before any poll edge, edge back or end, a raw
    access through N whose bytes reach N + H. A `check_ahead` is
    accepted where its access is followed by a need that covers the
    bytes it checks early. This file states those needs as functions of
    the point (`block_exit`, `facts_from`) and proves that the pass's
    one sweep computes them: every block's entry facts are what its
    instructions make of its exit facts, read from the final table
    (`ahead_entry`), and every accepted proof is accepted there
    (`ahead_accepted`).

    | Name | Says |
    |---|---|
    | `block_exit`, `facts_from` | the facts at a block's jump, from the final table, and before a suffix of its instructions |
    | `ahead_insts_after`, `ahead_insts_js` | one block's walk: the facts before it, and the proofs it accepts with the facts after each one's access |
    | `ahead_fold_suffix` | over the blocks from any one to the last, the table holds each block's entry facts and the accepted proofs are accepted at their exits, read from the table as it stands |
    | `ahead_entry`, `ahead_accepted` | the same for the whole function, from the final table |

    ## Decisions

    | Decision | Why |
    |---|---|
    | the facts are read from the final table | an edge reads its target's entry facts only for a later block, which the sweep has finished; no later step puts that label again, labels being unique |
    | `ahead_justified` is split into `ahead_fold`, `ahead_block`, `ahead_edge` and `ahead_accepts` | as ir.pl's `ahead_block/6` and `ahead_edge/5` are; the proofs read each part on its own | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Validate Walk Dominance Evidence.
Import ListNotations.
Open Scope Z_scope.

(** ## Facts at a point *)

(** `exit_in ord ins b`: the facts at b's jump, the meet over its edges
    (`ahead_meet/2`), each reading its target's entry facts from the
    table ins if the target comes later in the block order ord
    (`ahead_edge/5`). *)
Definition exit_in (ord : list name) (ins : list (name * facts)) (b : block) : facts :=
  ahead_meet (map (ahead_edge ord (index_of (b_label b) ord 0) ins) (jump_targets (b_jump b))).

(** The final table of a function's entry facts. *)
Definition ahead_entries (f : func) : list (name * facts) := fst (ahead_fold f (single_definitions f)).

(** `block_exit f b`: the facts at b's jump, from the final table. *)
Definition block_exit (f : func) (b : block) : facts :=
  exit_in (map b_label (fn_blocks f)) (ahead_entries f) b.

(** `facts_from f is out`: the facts before the instructions `is`, whose
    jump has the facts `out` (`ahead_step/5`, walked backward). *)
Definition facts_from (f : func) (is : list inst) (out : facts) : facts :=
  fold_right (ahead_step (single_definitions f) (proof_pointers f (single_definitions f))) out is.

(** ## One block *)

Definition step_back (once : list (name * def)) (ptrs : list (name * value)) (fs : facts) (i : inst) : facts :=
  ahead_step once ptrs i fs.

(** `ahead_insts_after`: a block's walk leaves the facts before its
    first instruction. *)
Lemma ahead_insts_after : forall once ptrs ris after next js,
  fst (ahead_insts once ptrs ris after next js) = fold_left (step_back once ptrs) ris after.
Proof.
  intros once ptrs ris. induction ris as [|i ris IH]; intros after next js; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

(** A need is never read from no facts. *)
Lemma ahead_accepts_nil : forall once i, ahead_accepts once [] i = None.
Proof.
  intros once i. destruct i as [q k o args | | | | | | |]; try reflexivity.
  destruct k; try reflexivity. destruct o; try reflexivity.
  destruct args as [|p [|a args]]; try reflexivity.
  cbn beta iota delta [ahead_accepts]. generalize (guard_chain once p) as es. intros es.
  cbn [lookup].
  match goal with |- context [existsb ?g es] =>
    replace (existsb g es) with false by
      (induction es as [|e es IH]; [reflexivity|]; simpl; rewrite <- IH;
       destruct (exact_base once e) as [[n kk]|]; [rewrite andb_false_r|]; reflexivity) end.
  rewrite andb_false_r. reflexivity.
Qed.

(** `ahead_insts_js`: a proof the walk accepts was accepted before it,
    or at an instruction followed by another, with the facts the walk
    had after that one. *)
Lemma ahead_insts_js : forall once ptrs ris after next js q,
  In q (snd (ahead_insts once ptrs ris after next js)) ->
  In q js \/ (exists i post, ris = i :: post /\ ahead_accepts once next i = Some q) \/
  exists pre i1 i post, ris = pre ++ i1 :: i :: post /\
    ahead_accepts once (fold_left (step_back once ptrs) pre after) i = Some q.
Proof.
  intros once ptrs ris. induction ris as [|i ris IH]; intros after next js q H; [left; exact H|].
  simpl in H. destruct (IH _ _ _ _ H) as [Hj | [(i' & post & -> & Ha) | (pre & i1 & i' & post & -> & Ha)]].
  - destruct (ahead_accepts once next i) as [q'|] eqn:Ea; [|left; exact Hj].
    destruct Hj as [<- | Hj]; [right; left; eauto | left; exact Hj].
  - right. right. exists [], i, i', post. auto.
  - right. right. exists (i :: pre), i1, i', post. auto.
Qed.

(** `block_accepts`: a proof one block's walk accepts, with nothing
    after its jump but `out`, is a `check_ahead` at some index k, not the
    last, accepted with the facts before the instructions after k + 1. *)
Lemma block_accepts : forall once ptrs is out js q,
  In q (snd (ahead_insts once ptrs (rev is) out [] js)) ->
  In q js \/ exists k i, nth_error is k = Some i /\ (S k < length is)%nat /\
    ahead_accepts once (fold_right (ahead_step once ptrs) out (skipn (S (S k)) is)) i = Some q.
Proof.
  intros once ptrs is out js q H.
  destruct (ahead_insts_js _ _ _ _ _ _ _ H) as [Hj | [(i & post & _ & Ha) | (pre & i1 & i & post & E & Ha)]].
  - left. exact Hj.
  - rewrite ahead_accepts_nil in Ha. discriminate Ha.
  - right. assert (Eis : is = rev post ++ i :: i1 :: rev pre).
    { rewrite <- (rev_involutive is), E. rewrite rev_app_distr. simpl. rewrite <- !app_assoc. reflexivity. }
    exists (length post), i. rewrite Eis. split; [|split].
    + rewrite nth_error_app2 by (rewrite length_rev; lia). rewrite length_rev, Nat.sub_diag. reflexivity.
    + rewrite length_app, length_rev. simpl. lia.
    + replace (skipn (S (S (length post))) (rev post ++ i :: i1 :: rev pre)) with (rev pre).
      * rewrite fold_left_rev_right. exact Ha.
      * rewrite skipn_app, length_rev. replace (S (S (length post)) - length post)%nat with 2%nat by lia.
        rewrite skipn_all2 by (rewrite length_rev; lia). reflexivity.
Qed.

(** ## The sweep over the blocks *)

Lemma index_of_S : forall l ls n, index_of l ls (S n) = option_map S (index_of l ls n).
Proof.
  intros l ls. induction ls as [|l' ls IH]; intros n; [reflexivity|].
  simpl. destruct (name_eqb l l'); [reflexivity | apply IH].
Qed.

(** In a list without duplicates, a name's index is its position. *)
Lemma index_of_nth : forall ls j l, no_dups ls = true -> nth_error ls j = Some l -> index_of l ls 0 = Some j.
Proof.
  induction ls as [|l0 ls IH]; intros j l Hnd Hj; [destruct j; discriminate Hj|].
  simpl in Hnd. apply andb_true_iff in Hnd as [Hn Hnd]. apply negb_true_iff in Hn.
  destruct j as [|j]; simpl in Hj |- *.
  - injection Hj as <-. rewrite name_eqb_refl. reflexivity.
  - assert (E : name_eqb l l0 = false).
    { apply name_eqb_false. intros ->. pose proof (mem_false _ _ Hn _ (nth_error_In _ _ Hj)) as E.
      rewrite name_eqb_refl in E. discriminate E. }
    rewrite E, index_of_S, (IH _ _ Hnd Hj). reflexivity.
Qed.


Section Sweep.

Variables (once : list (name * def)) (ptrs : list (name * value)) (bs : list block).
Hypothesis Hnd : no_dups (map b_label bs) = true.

Let ord := map b_label bs.

(** The state after the sweep has walked the blocks S, from the last. *)
Definition sweep (S : list block) : list (name * facts) * list name :=
  fold_left (ahead_block ord once ptrs) (rev S) ([], []).

Lemma ahead_block_eq : forall ins js b,
  ahead_block ord once ptrs (ins, js) b =
  (put (b_label b) (phis_end_needs (b_phis b) (fold_right (ahead_step once ptrs) (exit_in ord ins b) (b_insts b))) ins,
   snd (ahead_insts once ptrs (rev (b_insts b)) (exit_in ord ins b) [] js)).
Proof.
  intros ins js b. unfold ahead_block.
  pose proof (ahead_insts_after once ptrs (rev (b_insts b)) (exit_in ord ins b) [] js) as E.
  unfold exit_in in E |- *.
  destruct (ahead_insts _ _ _ _ _ _) as [entry0 js'] eqn:Ea. simpl in E |- *. rewrite E.
  unfold step_back. rewrite <- fold_left_rev_right, rev_involutive. reflexivity.
Qed.

(** A table entry for a label put earlier in the block order does not
    change the facts at a later block's jump: its edges read only the
    labels after it. *)
Lemma exit_put : forall lb jb e ins b p,
  index_of lb ord 0 = Some jb -> index_of (b_label b) ord 0 = Some p -> (jb <= p)%nat ->
  exit_in ord (put lb e ins) b = exit_in ord ins b.
Proof.
  intros lb jb e ins b p Hj Hp Hle. unfold exit_in. rewrite Hp. f_equal. apply map_ext. intros [l | l]; [|reflexivity].
  cbn beta iota delta [ahead_edge]. destruct (index_of l ord 0) as [tp|] eqn:Et; [|reflexivity].
  destruct (p <? tp)%nat eqn:Elt.
  - apply Nat.ltb_lt in Elt. rewrite lookup_put_other; [reflexivity|].
    apply name_eqb_false. intros ->. rewrite Hj in Et. injection Et as <-. lia.
  - destruct (lookup l (put lb e ins)), (lookup l ins); reflexivity.
Qed.

(** `ahead_fold_suffix`: after the sweep has walked the blocks from the
    j-th to the last, each of them has its entry facts in the table, and
    each accepted proof was accepted in one of them, both read from the
    table as it stands. *)
Lemma ahead_fold_suffix : forall j,
  (forall b, In b (skipn j bs) ->
     lookup (b_label b) (fst (sweep (skipn j bs))) =
     Some (phis_end_needs (b_phis b)
             (fold_right (ahead_step once ptrs) (exit_in ord (fst (sweep (skipn j bs))) b) (b_insts b)))) /\
  (forall q, In q (snd (sweep (skipn j bs))) ->
     exists b k i, In b (skipn j bs) /\ nth_error (b_insts b) k = Some i /\ (S k < length (b_insts b))%nat /\
       ahead_accepts once (fold_right (ahead_step once ptrs) (exit_in ord (fst (sweep (skipn j bs))) b)
                                      (skipn (S (S k)) (b_insts b))) i = Some q).
Proof.
  intros j. remember (skipn j bs) as S eqn:ES. revert j ES.
  induction S as [|b S IH]; intros j ES.
  - split; [intros b []|]. intros q Hq. destruct Hq.
  - assert (Hb : nth_error bs j = Some b) by (rewrite <- (Nat.add_0_r j), <- nth_error_skipn, <- ES; reflexivity).
    assert (ES' : S = skipn (Datatypes.S j) bs).
    { rewrite <- (skipn_skipn 1 j). rewrite <- ES. reflexivity. }
    destruct (IH _ ES') as [IHe IHj].
    assert (Hpos : index_of (b_label b) ord 0 = Some j)
      by (apply index_of_nth; [exact Hnd | unfold ord; rewrite nth_error_map, Hb; reflexivity]).
    assert (Hlater : forall b', In b' S -> exists p, index_of (b_label b') ord 0 = Some p /\ (j < p)%nat).
    { intros b' Hin. rewrite ES' in Hin. destruct (In_nth_error _ _ Hin) as [t Ht].
      rewrite nth_error_skipn in Ht. exists (Datatypes.S j + t)%nat. split; [|lia].
      apply index_of_nth; [exact Hnd | unfold ord; rewrite nth_error_map, Ht; reflexivity]. }
    unfold sweep. simpl rev. rewrite fold_left_app. fold (sweep S). simpl fold_left.
    destruct (sweep S) as [ins js] eqn:Esw. rewrite ahead_block_eq. simpl fst. simpl snd.
    set (e := phis_end_needs _ _).
    assert (Hx : forall b', In b' (b :: S) -> exit_in ord (put (b_label b) e ins) b' = exit_in ord ins b').
    { intros b' [<- | Hin]; [exact (exit_put _ _ _ _ _ _ Hpos Hpos (le_n _))|].
      destruct (Hlater _ Hin) as (p & Hp & Hlt). exact (exit_put _ _ _ _ _ _ Hpos Hp ltac:(lia)). }
    split.
    + intros b' Hin. rewrite (Hx _ Hin). destruct Hin as [<- | Hin].
      * rewrite lookup_put_same. reflexivity.
      * destruct (Hlater _ Hin) as (p & Hp & Hlt).
        rewrite lookup_put_other; [exact (IHe _ Hin)|].
        apply name_eqb_false. intros E. rewrite E, Hpos in Hp. injection Hp as ->. lia.
    + intros q Hq. destruct (block_accepts _ _ _ _ _ _ Hq) as [Hj | (k & i & Hk & Hlen & Ha)].
      * destruct (IHj _ Hj) as (b' & k & i & Hin & Hk & Hlen & Ha).
        exists b', k, i. rewrite (Hx _ (or_intror Hin)). split; [right; exact Hin | auto].
      * exists b, k, i. rewrite (Hx _ (or_introl eq_refl)). split; [left; reflexivity | auto].
Qed.

End Sweep.

(** `ahead_entry`: each block's entry facts are what its instructions
    make of its exit facts, with its phis' names ended. *)
Theorem ahead_entry : forall f b,
  no_dups (map b_label (fn_blocks f)) = true -> In b (fn_blocks f) ->
  lookup (b_label b) (ahead_entries f) =
  Some (phis_end_needs (b_phis b) (facts_from f (b_insts b) (block_exit f b))).
Proof.
  intros f b Hnd Hin.
  destruct (ahead_fold_suffix (single_definitions f) (proof_pointers f (single_definitions f)) _ Hnd 0) as [He _].
  exact (He b Hin).
Qed.

(** `ahead_accepted`: a proof `ahead_justified/3` accepts is a
    `check_ahead` at some index k of a block, not the last, accepted
    with the facts before the instructions after its access. *)
Theorem ahead_accepted : forall f q,
  no_dups (map b_label (fn_blocks f)) = true -> In q (ahead_justified f (single_definitions f)) ->
  exists b k i, In b (fn_blocks f) /\ nth_error (b_insts b) k = Some i /\ (S k < length (b_insts b))%nat /\
    ahead_accepts (single_definitions f) (facts_from f (skipn (S (S k)) (b_insts b)) (block_exit f b)) i = Some q.
Proof.
  intros f q Hnd Hq.
  destruct (ahead_fold_suffix (single_definitions f) (proof_pointers f (single_definitions f)) _ Hnd 0) as [_ Hj].
  exact (Hj q Hq).
Qed.
