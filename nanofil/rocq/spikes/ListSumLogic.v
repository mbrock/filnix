(** This spike verifies the C list-building and summation program
    `spikes/listsum.c` using the [[separation-logic|separation logic]]
    rules of `Logic.v`. Rather than stepping through concrete machine
    states, the proof assigns a [[hoare-triple|Hoare triple]] to the
    summation function and checks each instruction with symbolic
    tactics.

    When `sum` walks the list, it promises to return the sum of all node
    values modulo 2^64 and to hand the list back to its caller
    ([sum_spec]). The list-building function `listsum` allocates nodes
    one by one, invokes `sum` through that specification via
    [wp_call_bind], and then discards the list.

    Proving a loop in separation logic requires an invariant that holds
    across every iteration. We establish both loop invariants by
    [[later-modality|Löb induction]] right after their [[phi]] nodes,
    using a list segment ([lseg]) to track the already-walked prefix. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic Pieces Heap Language Logic.
From Spike Require Import ListSum.
Open Scope Z_scope.
Open Scope list_scope.

(** Folding integer arithmetic prevents Rocq from expanding symbolic
    addition, subtraction, and multiplication when a premise is
    evaluated (`Symbolic.v`). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## The blocks, computed once

    Looking up a basic block inside a compiled function on every proof
    step would slow down symbolic execution. Instead, this section
    extracts each block of `sum` and `listsum` once by computation and
    proves its lookup lemma upfront. *)

(** This helper fetches block l from function f, returning an empty
    unreachable block when the label is absent. *)
Definition blk (f : func) (l : string) : block :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** This constant holds the entry block of `sum`. *)
Definition sum_start : block := Eval vm_compute in blk (ls_fn "sum") "start".
(** This constant holds the loop header of `sum`. *)
Definition sum_L3 : block := Eval vm_compute in blk (ls_fn "sum") "L3".
(** This constant holds the loop body of `sum`. *)
Definition sum_L4 : block := Eval vm_compute in blk (ls_fn "sum") "L4".
(** This constant holds the exit block of `sum`. *)
Definition sum_L5 : block := Eval vm_compute in blk (ls_fn "sum") "L5".
(** This constant holds the entry block of `listsum`. *)
Definition ls_start : block := Eval vm_compute in blk (ls_fn "listsum") "start".
(** This constant holds the loop header of `listsum`. *)
Definition ls_L4 : block := Eval vm_compute in blk (ls_fn "listsum") "L4".
(** This constant holds the loop body of `listsum`. *)
Definition ls_L5 : block := Eval vm_compute in blk (ls_fn "listsum") "L5".
(** This constant holds the exit block of `listsum`, which calls `sum`. *)
Definition ls_L7 : block := Eval vm_compute in blk (ls_fn "listsum") "L7".

(** Looking up `"start"` in `sum` returns [sum_start]. *)
Lemma sum_find_start : find_block (TAtom "start") (fn_blocks (ls_fn "sum")) = Some sum_start.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `"L3"` in `sum` returns [sum_L3]. *)
Lemma sum_find_L3 : find_block (TAtom "L3") (fn_blocks (ls_fn "sum")) = Some sum_L3.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `"L4"` in `sum` returns [sum_L4]. *)
Lemma sum_find_L4 : find_block (TAtom "L4") (fn_blocks (ls_fn "sum")) = Some sum_L4.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `"L5"` in `sum` returns [sum_L5]. *)
Lemma sum_find_L5 : find_block (TAtom "L5") (fn_blocks (ls_fn "sum")) = Some sum_L5.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `"start"` in `listsum` returns [ls_start]. *)
Lemma ls_find_start : find_block (TAtom "start") (fn_blocks (ls_fn "listsum")) = Some ls_start.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `"L4"` in `listsum` returns [ls_L4]. *)
Lemma ls_find_L4 : find_block (TAtom "L4") (fn_blocks (ls_fn "listsum")) = Some ls_L4.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `"L5"` in `listsum` returns [ls_L5]. *)
Lemma ls_find_L5 : find_block (TAtom "L5") (fn_blocks (ls_fn "listsum")) = Some ls_L5.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `"L7"` in `listsum` returns [ls_L7]. *)
Lemma ls_find_L7 : find_block (TAtom "L7") (fn_blocks (ls_fn "listsum")) = Some ls_L7.
Proof. vm_compute. reflexivity. Qed.
(** The function `sum` returns a 64-bit `long`. *)
Lemma sum_ret : fn_ret (ls_fn "sum") = RClass L.
Proof. vm_compute. reflexivity. Qed.
(** The function `listsum` also returns a 64-bit `long`. *)
Lemma listsum_ret : fn_ret (ls_fn "listsum") = RClass L.
Proof. vm_compute. reflexivity. Qed.

(** ## Environments

    Each IR instruction binds a new variable in the frame's local
    environment. If those updates pile up as nested `put` terms, variable
    lookups become huge and slow down the proof. This tactic keeps the
    environment abstract by replacing each update with a fresh variable
    and recording its lookup facts in the context. *)

(** This tactic replaces every `put k v e` in the goal with a fresh
    variable and records what each variable name maps to in the new
    environment. *)
Ltac gen_env :=
  repeat match goal with
  | |- context[put ?k ?v ?e] =>
      is_var e;
      let H := fresh "Hput" in
      assert (H : lookup k (put k v e) = Some v) by apply lookup_after_put_same;
      repeat match goal with
        | H' : lookup ?x e = Some ?w |- _ =>
            first [ assert (lookup x (put k v e) = Some w)
                      by (rewrite lookup_after_put_other; [exact H'|reflexivity])
                  | idtac ];
            clear H'
        end;
      let e' := fresh "e" in set (e' := put k v e) in *; clearbody e'; try clear e
  end.

(** ## Nodes

    Each list node in C holds an 8-byte next pointer followed by an
    8-byte `long` value. In Fil-C's memory model, that 16-byte struct
    becomes a live heap [[region]] whose base pointer is 16-byte aligned
    and carries an object [[capability]]. *)

(** Every node occupies a 16-byte live heap region starting at base b. *)
Definition node_reg (b : Z) : region := mkRegion b (b + 16) Heap Live.

(** A pointer p is a valid node pointer at base b when it carries the
    object's own capability and b is positive, 16-byte aligned, and
    within the 48-bit address space. *)
Definition node_ok (p : ptr) (b : Z) : Prop :=
  p = mkPtr b (Obj b) /\ 0 < b /\ b + 16 <= 2 ^ 48 /\ b mod 16 = 0.

(** ## Taking a step

    Applying a weakest-precondition rule generates small side
    conditions about pointer alignment, block lookups, return classes,
    and integer bounds. The tactics in this section discharge those
    pure goals automatically so the main loop proofs stay concise. *)

(** Memory operations require showing that raw addresses stay within
    bounds and meet alignment rules. This tactic strips trivial
    1-alignments and modular wraps from [raw_address], then solves the
    resulting linear inequalities. *)
Ltac addr :=
  unfold raw_address; cbn [ptr_addr ptr_cap r_end node_reg]; rewrite ?Z.mod_1_r;
  drop_wraps_goal; arith.

(** Block-entry and return rules need facts about the module's blocks
    and return types in the context. This tactic poses those precomputed
    lemmas so later steps can match them directly. *)
Ltac ls_facts :=
  pose proof sum_find_start; pose proof sum_find_L3; pose proof sum_find_L4; pose proof sum_find_L5;
  pose proof ls_find_start; pose proof ls_find_L4; pose proof ls_find_L5; pose proof ls_find_L7;
  pose proof sum_ret; pose proof listsum_ret.

(** This tactic unfolds the precomputed basic blocks named by a frame's
    current program point. *)
Ltac unfold_blocks :=
  cbn [b_insts b_jump sum_start sum_L3 sum_L4 sum_L5 ls_start ls_L4 ls_L5 ls_L7 edge_label].

(** This tactic discharges one pure side condition of a logic rule by
    computation, context lookup, [addr], [compute_premise], or linear
    arithmetic. *)
Ltac side :=
  lazymatch goal with
  | |- forall (_ : mem) (_ : unit), _ => intros; exact I
  | |- general_op _ = true => reflexivity
  | |- op_arg_classes _ _ = _ => reflexivity
  | |- find_block _ _ = _ => eassumption
  | |- fn_ret _ = _ => eassumption
  | |- find_fn _ _ = _ => eassumption
  | |- call_frame (ls_fn "sum") _ = _ => apply sum_call_frame
  | |- _ <= max_allocation_size => apply Z.leb_le; reflexivity
  | |- forall m : mem, _ => intros ?; compute_premise
  | |- ptr_cap _ = _ => reflexivity
  | |- context[raw_address] => addr
  | |- _ = _ => first [ compute_premise | arith ]
  | |- _ => cbn [ptr_addr ptr_cap r_end node_reg]; arith
  end.

(** ## Sums

    In C, `sum` accumulates node values into an unsigned 64-bit integer,
    wrapping on overflow. This section defines the mathematical
    specification of that wrapping sum and proves the append lemma
    needed when the loop advances by one node. *)

(** This function computes the sum of the integers xs modulo 2^64,
    matching how `sum` adds 64-bit `long` values. *)
Definition list_sum (xs : list Z) : Z := fold_right Z.add 0 xs mod 2 ^ 64.

(** Every modular sum fits inside an unsigned 64-bit integer. *)
Lemma list_sum_range xs : 0 <= list_sum xs < 2 ^ 64.
Proof. apply Z.mod_pos_bound. lia. Qed.

(** Appending one node value y updates [list_sum] by adding y modulo
    2^64, matching one iteration of the summation loop. *)
Lemma list_sum_snoc ys y : list_sum (ys ++ [y]) = (list_sum ys + y mod 2 ^ 64) mod 2 ^ 64.
Proof.
  unfold list_sum. rewrite fold_right_app. cbn [fold_right].
  assert (E : forall zs a, fold_right Z.add a zs = fold_right Z.add 0 zs + a).
  { induction zs as [|z zs IH]; intros a; cbn [fold_right]; [lia|]. rewrite IH. lia. }
  rewrite E. rewrite <- Zplus_mod. f_equal. lia.
Qed.

(** ## Over any runtime

    The verification should not depend on one particular allocator
    implementation. This functor parameterizes the entire proof over an
    arbitrary [Runtime] R so the safety theorem holds for any conforming
    allocator. *)

(** This module proves the safety and functional correctness of
    `listsum.c` over an abstract runtime R. *)
Module ListSumLogic (R : Runtime).
Module LG := Logic R.
Module L := LG.L.
Module P := LG.P.
Import L LG.

(** This notation abbreviates the module's global environment using R's
    allocator. *)
Local Notation lge := (P.program_genv ls_module ls_globals).
(** This notation names the Iris expression type for the program. *)
Local Notation lexpr := (language.expr (nanofil_lang no_contracts lge)).

(** ## The rules as tactics

    Stepping through basic blocks by hand requires applying a logic rule
    and immediately discharging its side conditions. These wrapper
    tactics bundle each rule with the [side] tactic and environment
    simplification so the loop proofs read like straight-line code. *)

(** This tactic steps past a `let` instruction whose operation reads no
    memory by applying [wp_let]. *)
Ltac wp_let_ := iApply wp_let; first [side | iNext; gen_env].

(** This tactic steps across a conditional branch by applying [wp_branch]
    and computing the target label. *)
Ltac wp_branch_ := iApply wp_branch; first [side | iNext; cbn [edge_label Z.eqb Pos.eqb]].

(** This tactic enters a basic block by applying [wp_enter] and
    unfolding the block's instructions. *)
Ltac wp_enter_ := iApply wp_enter; first [side | iNext; unfold_blocks; gen_env].

(** This tactic steps across an unconditional jump by applying [wp_goto]
    and unfolding the target block. *)
Ltac wp_goto_ := iApply wp_goto; iNext; unfold_blocks.

(** This tactic steps past a [[flight]] instruction by applying
    [wp_flight]. *)
Ltac wp_flight_ := iApply wp_flight; first [side | iNext; gen_env].

(** Calling `sum` with pointer p builds this entry frame. *)
Definition sum_frame (p : ptr) : frame :=
  mkFrame (ls_fn "sum") [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).

Section proof.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** A linked list starting at pointer p represents the sequence of
    integers xs. An empty list requires p to be null; otherwise p must
    be a valid node pointer ([node_ok]) whose live 16-byte object holds
    the next pointer at offset 0, the value at offset 8, and the
    remaining list. *)
Fixpoint lst (p : ptr) (xs : list Z) : iProp Σ :=
  match xs with
  | [] => ⌜p = null⌝
  | x :: xs' => ∃ b nx, ⌜node_ok p b⌝ ∗ live b (node_reg b) ∗ pcell b 0 nx ∗ icell b 8 x ∗ lst nx xs'
  end%I.

(** The list segment from p to q holds the values ys: the nodes of
    [lst], ending at q instead of null. *)
Fixpoint lseg (p q : ptr) (ys : list Z) : iProp Σ :=
  match ys with
  | [] => ⌜p = q⌝
  | y :: ys' => ∃ b nx, ⌜node_ok p b⌝ ∗ live b (node_reg b) ∗ pcell b 0 nx ∗ icell b 8 y ∗ lseg nx q ys'
  end%I.

(** Unfolding a non-empty list exposes the head node's liveness, next
    pointer, value, and tail predicate. *)
Lemma lst_cons p x xs :
  lst p (x :: xs) ⊣⊢ ∃ b nx, ⌜node_ok p b⌝ ∗ live b (node_reg b) ∗ pcell b 0 nx ∗ icell b 8 x ∗ lst nx xs.
Proof. reflexivity. Qed.

(** Extending a list segment ending at q with the node at q yields a
    segment ending at that node's next pointer. *)
Lemma lseg_snoc p q ys b nx y :
  node_ok q b -> lseg p q ys -∗ live b (node_reg b) -∗ pcell b 0 nx -∗ icell b 8 y -∗
  lseg p nx (ys ++ [y]).
Proof.
  intros Hq. revert p. induction ys as [|y' ys IH]; intros p; cbn [lseg app].
  - iIntros (->) "Hl Hp Hi". iExists b, nx. by iFrame.
  - iIntros "Hs Hl Hp Hi". iDestruct "Hs" as (b' nx') "(% & Hl' & Hp' & Hi' & Hs)".
    iExists b', nx'. iFrame "Hl' Hp' Hi'". iSplit; [done|]. iApply (IH with "Hs Hl Hp Hi").
Qed.

(** A segment to q and the list from q make the list from p. *)
Lemma lseg_lst p q ys zs : lseg p q ys -∗ lst q zs -∗ lst p (ys ++ zs).
Proof.
  revert p. induction ys as [|y ys IH]; intros p; cbn [lseg app].
  - iIntros (->) "Hl". iExact "Hl".
  - iIntros "Hs Hl". iDestruct "Hs" as (b nx) "(% & Hlv & Hp & Hi & Hs)".
    cbn [lst]. iExists b, nx. iFrame "Hlv Hp Hi". iSplit; [done|]. iApply (IH with "Hs Hl").
Qed.

(** If a pointer heads a list, its address lies in the 64-bit range and
    the liveness of its target object can be borrowed for a load. *)
Lemma lst_cap p xs :
  lst p xs -∗ ⌜0 <= ptr_addr p < 2 ^ 64⌝ ∗ live_cap (ptr_cap p) (node_reg (ptr_addr p)) ∗
  (live_cap (ptr_cap p) (node_reg (ptr_addr p)) -∗ lst p xs).
Proof.
  destruct xs as [|x xs]; cbn [lst].
  - iIntros (->). cbn. iSplit; [iPureIntro; lia|]. iSplit; [done|]. by iIntros "_".
  - iIntros "H". iDestruct "H" as (b nx Hn) "(Hlv & Hp & Hi & Hl)".
    destruct Hn as (-> & Hb0 & Hb1 & Hb2). cbn [ptr_addr ptr_cap live_cap].
    iSplit; [iPureIntro; lia|]. iFrame "Hlv". iIntros "Hlv". iExists b, nx. iFrame. done.
Qed.

(** Walking a linked list in a loop requires splitting the list into
    the nodes already visited and the nodes still ahead. At block `L3`,
    the visited prefix ys forms a segment from p to q, while the
    remaining suffix zs forms a list from q. Given q in `pr.1` and the
    prefix sum in `pr.2`, Löb induction proves that the loop returns the
    total sum and hands the whole list back. *)
Lemma sum_loop p Φ :
  ⊢ ∀ e q ys zs,
      ⌜lookup (TAtom "pr.1") e = Some (WPtr q) /\ lookup (TAtom "pr.2") e = Some (WInt (list_sum ys))⌝ -∗
      lseg p q ys -∗ lst q zs -∗ (lst p (ys ++ zs) -∗ Φ (Ret (WInt (list_sum (ys ++ zs))))) -∗
      WP (ERun (mkFrame (ls_fn "sum") e [] None (Exec (TAtom "L3") (b_insts sum_L3) (b_jump sum_L3)))
           : lexpr) {{ Φ }}.
Proof.
  iLöb as "IH". iIntros (e q ys zs [Hq Hs]) "Hs Hl HΦ".
  pose proof (list_sum_range ys).
  destruct zs as [|z zs].
  - iDestruct "Hl" as %->. cbn [sum_L3 b_insts b_jump].
    ls_facts. rewrite app_nil_r.
    wp_let_. wp_let_. wp_branch_. wp_enter_.
    iApply wp_ret; first [side | iNext].
    iApply "HΦ". iDestruct (lseg_lst _ _ _ [] with "Hs [//]") as "H". rewrite app_nil_r. iExact "H".
  - rewrite lst_cons. iDestruct "Hl" as (b nx (-> & Hb0 & Hb1 & Hb2)) "(Hlv & Hp & Hi & Hl)".
    ls_facts. cbn [sum_L3 b_insts b_jump].
    wp_let_. wp_let_. wp_branch_. wp_enter_.
    wp_flight_.
    iApply (wp_check with "Hlv"); first [side | iNext; iIntros "Hlv"; gen_env].
    iApply (wp_raw_load with "Hlv Hi"); first [side | iNext; iIntros "Hlv Hi"; gen_env].
    wp_let_.
    iApply (wp_half_check with "Hlv"); first [side | iNext; iIntros "Hlv"; gen_env].
    iDestruct (lst_cap with "Hl") as (Hnr) "[Hcap Hl]".
    iApply (wp_raw_load_pointer with "Hlv Hp Hcap");
      first [side | iNext; iIntros "Hlv Hp Hcap"; iSpecialize ("Hl" with "Hcap"); gen_env].
    wp_goto_. wp_enter_.
    iApply ("IH" $! _ nx (ys ++ [z]) zs with "[%] [Hs Hlv Hp Hi] Hl [HΦ]").
    + split; [eassumption|]. rewrite list_sum_snoc. eassumption.
    + iApply (lseg_snoc with "Hs Hlv Hp Hi"). unfold node_ok. auto.
    + rewrite -app_assoc. iExact "HΦ".
Qed.

(** `sum`'s specification: called with the list from p holding xs, it
    returns their sum modulo 2^64 and hands the list back. *)
Lemma sum_spec p xs :
  ⊢ {{{ lst p xs }}} (ERun (sum_frame p) : lexpr) {{{ RET (Ret (WInt (list_sum xs))); lst p xs }}}.
Proof.
  iIntros (Φ) "!> Hl HΦ". ls_facts. unfold sum_frame.
  wp_enter_. wp_goto_. wp_enter_.
  iApply (sum_loop p Φ $! _ p [] xs with "[%] [//] Hl HΦ").
  split; reflexivity.
Qed.


(** Allocating a fresh 16-byte object produces the pieces of a new list
    node: its live region, a null next pointer at offset 0, and a zero
    value at offset 8, while discarding unused auxiliary slots. *)
Lemma obj_node base :
  obj base (heap_req 16 16) -∗ live base (node_reg base) ∗ pcell base 0 null ∗ icell base 8 0.
Proof.
  rewrite /obj /live /pcell /icell.
  assert (E : obj_ps base (heap_req 16 16) =
     [(PLive base, VLive (node_reg base))] ++ cell base 0 0 ++ cell base 8 0 ++
     [(PAux base 0, VAux CNone)] ++ ((fun i => (PAux base i, VAux CNone)) <$> seqZ 1 15)) by reflexivity.
  rewrite E !pts_app. iIntros "(Hl & H0 & H8 & Ha & _)". iFrame "Hl H8".
  rewrite (pts_app [_] (cell base 0 0)). iFrame.
Qed.

(** Building a linked list in a loop requires tracking the partial list
    constructed on earlier iterations. At block `L4`, the loop holds
    counter i, head pointer h, and bound n alongside the list built so
    far. By Löb induction, it allocates nodes until i reaches n and then
    calls `sum` via [sum_spec]. *)
Lemma ls_loop n :
  ⊢ ∀ e i h xs,
      ⌜lookup (TAtom "pr.2") e = Some (WInt i) /\ 0 <= i < 2 ^ 31 /\
       lookup (TAtom "pr.1") e = Some (WPtr h) /\ lookup (TAtom "v0") e = Some (WInt n)⌝ -∗
      lst h xs -∗
      WP (ERun (mkFrame (ls_fn "listsum") e [] None (Exec (TAtom "L4") (b_insts ls_L4) (b_jump ls_L4)))
           : lexpr) {{ _, True }}.
Proof.
  iLöb as "IH". iIntros (e i h xs (Hi & Hir & Hh & Hn)) "Hl".
  ls_facts. pose proof (ls_find_sum R.free). cbn [ls_L4 b_insts b_jump].
  wp_let_.
  match goal with H : lookup (TAtom "v10") _ = Some (WInt (if ?c then 1 else 0)) |- _ =>
    destruct c eqn:Hc end.
  - assert (Hi1 : i + 1 < 2 ^ 31).
    { apply Z.ltb_lt in Hc. revert Hc.
      destruct (2 ^ 31 <=? n mod 2 ^ 32) eqn:Hs; [apply Z.leb_le in Hs | apply Z.leb_gt in Hs];
        intros; pose proof (Z.mod_pos_bound n (2 ^ 32) ltac:(lia)); lia. }
    wp_branch_. wp_enter_.
    iApply wp_alloc; first [side | iNext; iIntros (base (Hb0 & Hb1 & Hb2)) "Hobj"; gen_env].
    change (req_align (heap_req 16 16)) with 16 in Hb1.
    change (req_extent (heap_req 16 16)) with 16 in Hb2.
    iDestruct (obj_node with "Hobj") as "(Hlv & Hp & Hi)".
    iApply (wp_check with "Hlv"); first [side | iNext; iIntros "Hlv"; gen_env].
    iApply (wp_raw_store_pointer with "Hlv Hp"); first [side | iNext; iIntros "Hlv Hp"; gen_env].
    wp_flight_. wp_let_.
    iApply (wp_half_check with "Hlv"); first [side | iNext; iIntros "Hlv"; gen_env].
    iApply (wp_raw_store with "Hlv Hi"); first [side | iNext; iIntros "Hlv Hi"; gen_env].
    wp_let_. wp_goto_. wp_enter_.
    iApply ("IH" $! _ (i + 1) (mkPtr base (Obj base)) (i :: xs) with "[%] [Hlv Hp Hi Hl]").
    + split; [eassumption|]. split; [lia|]. split; eassumption.
    + rewrite lst_cons. iExists base, h. iFrame. iPureIntro. unfold node_ok. auto with zarith.
  - wp_branch_. wp_enter_.
    iApply wp_call_bind; try side.
    iNext. iApply (sum_spec with "Hl"). iNext. iIntros "_".
    iExists _. iSplit; [iPureIntro; reflexivity|].
    iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
    iApply wp_ret; first [side | done].
Qed.

(** `listsum` called with the int n is safe. *)
Lemma listsum_spec n :
  ⊢ WP (ERun (mkFrame (ls_fn "listsum") [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
         : lexpr) {{ _, True }}.
Proof.
  ls_facts. wp_enter_. wp_goto_. wp_enter_.
  iApply (ls_loop n $! _ 0 null [] with "[%] [//]").
  split; [reflexivity|]. split; [lia|]. split; reflexivity.
Qed.

End proof.

(** To run the Iris program logic, the proof needs both invariants and a
    [[ghost-state|ghost heap]] of memory pieces. This functor bundle
    supplies those two resources. *)
Definition lsΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** The resource bundle [lsΣ] provides Iris invariants. *)
Global Instance lsΣ_inv : invGpreS lsΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** Allocating and updating list nodes in separation logic requires
    ownership of individual memory pieces. This instance supplies that
    ghost-heap capability for [lsΣ]. *)
Global Instance lsΣ_heap : gen_heapGpreS piece pval lsΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** Calling `listsum` with any integer argument never panics, regardless
    of fuel or allocator placement. Applying Iris [[adequacy]] via
    [heap_never_panics] lifts [listsum_spec] into this concrete safety
    theorem. *)
Theorem listsum_never_panics :
  P.never_panics ls_module (TAtom "listsum") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply (heap_never_panics lsΣ ls_module (TAtom "listsum") _ ls_globals ListSum.ls_mem (ls_fn "listsum")).
  - exact ls_initial.
  - exact (ls_find_listsum R.free).
  - intros b1 r1 b2 r2 [E _]. vm_compute in E. discriminate E.
  - intros xs (n & rest & ->). eexists. split; [apply listsum_call_frame|].
    intros HinvG HheapG. apply listsum_spec.
Qed.

End ListSumLogic.

(** Instantiating the functor with [InterpRuntime] yields the concrete
    safety theorem for the interpreter's allocator. *)
Module InterpListSumLogic := ListSumLogic InterpRuntime.

(** The program `listsum.c` never panics under the interpreter's runtime. *)
Theorem interp_listsum_never_panics :
  InterpListSumLogic.P.never_panics ls_module (TAtom "listsum")
    (fun xs => exists n rest, xs = WInt n :: rest).
Proof. exact InterpListSumLogic.listsum_never_panics. Qed.
