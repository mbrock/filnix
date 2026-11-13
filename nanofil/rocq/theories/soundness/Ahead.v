(** A [[check_ahead|scheduled check]] verifies a pointer's bounds early,
    before the memory access that uses it. If the early check fails on
    bytes beyond the access's own range, the frame becomes a
    [[doomed frame]] (see Doomed.v). From that point on, the frame must
    reach a failing memory access before hitting a [[poll edge]], a
    return, or a non-transparent instruction.

    To justify hoisting a check, the compiler must know that the program
    will soon perform a real memory access on the same pointer. It runs a
    backward pass over each function, walking from the last block to the
    first and from each block's jump back to its entry. At every program
    point it records [[need|needs]] for
    [[single definition|single-definition]] base pointers, where a pair of
    pointer N and offset H means every path ahead reaches a raw access
    through N of at least N + H bytes through [[ahead-transparent]]
    instructions.

    A scheduled check is accepted when a need after its paired access
    covers the entire range checked early. This file defines those needs
    as functions of the program point and proves that the validator's
    single backward sweep computes them (see
    [formal.md](../../../docs/formal.md#campaign-3-the-soundness-theorem)
    and [rocq.md](../../../docs/rocq.md#facts-ahead)).

    ## Decisions

    When a function jumps to a later basic block, the compiler has already
    analyzed that destination block. Because block labels are unique, later
    steps never overwrite finished entries, so reading from the final table
    gives the same answer as reading during the walk.

    Second, the compiler checks edges, blocks, and instructions in separate
    steps. Factoring [ahead_justified] into [ahead_fold] and its helper
    functions mirrors that structure so each lemma reasons about one step. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Validate Walk Dominance Evidence.
Import ListNotations.
Open Scope Z_scope.

(** ## Facts at a point

    To reason about a running frame, we need to look up the validator's
    needs at any block entry, block exit, or instruction index. The
    definitions in this section express those needs directly in terms of the
    final table computed by the backward pass. *)

(** At the jump of a block b, [exit_in] computes the needs by taking the
    meet over all outgoing edges. Each forward edge reads its target's entry
    facts from the table, while a [[poll edge]] or backward edge
    contributes no needs. *)
Definition exit_in (ord : list name) (ins : list (name * facts)) (b : block) : facts :=
  ahead_meet (map (ahead_edge ord (index_of (b_label b) ord 0) ins) (jump_targets (b_jump b))).

(** Folding the backward pass over a function's blocks yields
    [ahead_entries], the final table mapping each block label to the needs
    that hold before its first instruction. *)
Definition ahead_entries (f : func) : list (name * facts) := fst (ahead_fold f (single_definitions f)).

(** For a block b in function f, [block_exit] computes the needs at its
    jump by reading target entry facts from the function's final table
    [ahead_entries]. *)
Definition block_exit (f : func) (b : block) : facts :=
  exit_in (map b_label (fn_blocks f)) (ahead_entries f) b.

(** Given the facts out after the last instruction of a list,
    [facts_from] computes the needs before the first instruction by
    applying [ahead_step] backward from right to left. *)
Definition facts_from (f : func) (is : list inst) (out : facts) : facts :=
  fold_right (ahead_step (single_definitions f) (proof_pointers f (single_definitions f))) out is.

(** ## One block

    A basic block runs its instructions from first to last, while the
    validator checks each scheduled bounds test against the memory accesses
    that follow it. To verify that backward pass, the lemmas below connect
    the validator's reversed-list fold back to forward instruction indices. *)

(** Wrapping [ahead_step] in [step_back] puts its accumulator argument
    first so [fold_left] can step backward over a reversed instruction
    list. *)
Definition step_back (once : list (name * def)) (ptrs : list (name * value)) (fs : facts) (i : inst) : facts :=
  ahead_step once ptrs i fs.

(** Walking a block's instructions in reverse leaves the same entry facts as
    a plain left fold of [step_back] from the block's exit facts, as
    [ahead_insts_after] shows. *)
Lemma ahead_insts_after : forall once ptrs ris after next js,
  fst (ahead_insts once ptrs ris after next js) = fold_left (step_back once ptrs) ris after.
Proof.
  intros once ptrs ris. induction ris as [|i ris IH]; intros after next js; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

(** When no facts follow an instruction, [ahead_accepts] accepts nothing,
    because every `check_ahead` requires a downstream [[need]] covering
    its early bytes. *)
Lemma ahead_accepts_nil : forall once i, ahead_accepts once [] i = None.
Proof.
  intros once i. destruct i as [q k o args | | | | | | | | ]; try reflexivity.
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

(** Every scheduled check accepted during a block's backward walk must be
    justified by the facts after its paired access. Lemma [ahead_insts_js]
    shows that an accepted proof q was either already in js, or sits at the
    head of the reversed list against next, or precedes an instruction i1
    and is accepted against the facts after i1. *)
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

(** Every scheduled check inside a block must pair with a later instruction
    in the same block, because a check at the end has no following access.
    Lemma [block_accepts] converts the reversed walk back to forward order
    and places each accepted proof q at some non-final index k. *)
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

(** ## The sweep over the blocks

    Across a whole function, the pass visits blocks from last to first
    assuming their labels are unique. Because edges only consult blocks that
    appear later in the order, adding an earlier block never changes the exit
    facts of any block already processed. *)

(** Searching for a label starting at position n + 1 yields one more than
    searching from position n. *)
Lemma index_of_S : forall l ls n, index_of l ls (S n) = option_map S (index_of l ls n).
Proof.
  intros l ls. induction ls as [|l' ls IH]; intros n; [reflexivity|].
  simpl. destruct (name_eqb l l'); [reflexivity | apply IH].
Qed.

(** In a list without duplicate names, [index_of] maps the element at
    position j to index j. *)
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


(** To prove that the whole-function pass computes the right table, we fix
    a block list bs with unique labels, together with the function's
    single-definition map once and its proof-pointer map ptrs. *)
Section Sweep.

Variables (once : list (name * def)) (ptrs : list (name * value)) (bs : list block).
Hypothesis Hnd : no_dups (map b_label bs) = true.

Let ord := map b_label bs.

(** Walking a suffix of blocks S from last to first with [sweep] returns
    the accumulated entry-fact table and accepted-proof list. *)
Definition sweep (S : list block) : list (name * facts) * list name :=
  fold_left (ahead_block ord once ptrs) (rev S) ([], []).

(** One block step of the pass updates the entry table and records newly
    accepted checks. Unfolding [ahead_block] in [ahead_block_eq] shows that
    it stores the block's entry facts with its [[phi|phis']] names ended and
    appends any proofs accepted during its instruction walk. *)
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

(** Inserting an entry for a label at or before block b in the block order
    does not change [exit_in] for b, because forward edges only read
    labels after b. *)
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

(** Because forward edges only read blocks later in the function, the pass
    can settle each block's entry facts in a single reverse sweep without
    revisiting earlier blocks. Lemma [ahead_fold_suffix] proves by
    induction on the suffix from index j to the end that every visited
    block has its exact entry facts in the table and every accepted proof
    satisfies [block_accepts] against that table. *)
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

(** Each block's entry in the final table matches the needs computed by
    walking its instructions backward from its exit and ending the names
    defined by its [[phi|phis]]. Theorem [ahead_entry] establishes this
    fixed-point property for any function with unique block labels. *)
Theorem ahead_entry : forall f b,
  no_dups (map b_label (fn_blocks f)) = true -> In b (fn_blocks f) ->
  lookup (b_label b) (ahead_entries f) =
  Some (phis_end_needs (b_phis b) (facts_from f (b_insts b) (block_exit f b))).
Proof.
  intros f b Hnd Hin.
  destruct (ahead_fold_suffix (single_definitions f) (proof_pointers f (single_definitions f)) _ Hnd 0) as [He _].
  exact (He b Hin).
Qed.

(** Whenever the compiler accepts a scheduled check, the program has a
    guaranteed memory access later in the same block whose downstream needs
    cover the early check range. Theorem [ahead_accepted] turns the pass's
    output [ahead_justified] into that guarantee for any function with
    unique block labels, giving Doomed.v the starting point for its
    [[doomed frame]] invariant. *)
Theorem ahead_accepted : forall f q,
  no_dups (map b_label (fn_blocks f)) = true -> In q (ahead_justified f (single_definitions f)) ->
  exists b k i, In b (fn_blocks f) /\ nth_error (b_insts b) k = Some i /\ (S k < length (b_insts b))%nat /\
    ahead_accepts (single_definitions f) (facts_from f (skipn (S (S k)) (b_insts b)) (block_exit f b)) i = Some q.
Proof.
  intros f q Hnd Hq.
  destruct (ahead_fold_suffix (single_definitions f) (proof_pointers f (single_definitions f)) _ Hnd 0) as [_ Hj].
  exact (Hj q Hq).
Qed.
