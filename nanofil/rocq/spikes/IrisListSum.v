(** Spike: spikes/listsum.c proved never to panic through Iris, with the
    ghost heap and rules of IrisHeap.v, the same theorem the hand-rolled
    spike proves.

    A node is the life of its 16-byte heap object, the aux slot of its
    next pointer and the 16 bytes of the next pointer's address and its
    value ([node_ps]); a list is a [Fixpoint] over the values ([lst]).
    `sum` gets one specification ([sum_spec]): from [lst] p xs, a call
    with any caller frame and callers stack is safe if the caller,
    resumed with any result and any fuel, is; that continuation is a
    resource the callee carries to its return (the rule for a call that
    the language, having no evaluation contexts, does not give). Each
    loop is a Löb induction at the point after its head's phis. Each
    step is computed as Symbolic.v computes one, without splitting a
    comparison and without generalising a wrap, so that the next
    configuration is a term the rule's existential frame can take. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  Symbolic.
From Spike Require Import Pieces ListSum IrisLang IrisHeap.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a step is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## The blocks, computed once *)

(** Block l of the function f, or an empty one. *)
Definition blk (f : func) (l : string) : block :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** `sum`'s entry block. *)
Definition sum_start : block := Eval vm_compute in blk (ls_fn "sum") "start".
(** `sum`'s loop head. *)
Definition sum_L3 : block := Eval vm_compute in blk (ls_fn "sum") "L3".
(** `sum`'s loop body. *)
Definition sum_L4 : block := Eval vm_compute in blk (ls_fn "sum") "L4".
(** `sum`'s exit. *)
Definition sum_L5 : block := Eval vm_compute in blk (ls_fn "sum") "L5".
(** `listsum`'s entry block. *)
Definition ls_start : block := Eval vm_compute in blk (ls_fn "listsum") "start".
(** `listsum`'s loop head. *)
Definition ls_L4 : block := Eval vm_compute in blk (ls_fn "listsum") "L4".
(** `listsum`'s loop body. *)
Definition ls_L5 : block := Eval vm_compute in blk (ls_fn "listsum") "L5".
(** `listsum`'s exit, the call of `sum`. *)
Definition ls_L7 : block := Eval vm_compute in blk (ls_fn "listsum") "L7".

(** `sum` has its entry block. *)
Lemma sum_find_start : find_block (TAtom "start") (fn_blocks (ls_fn "sum")) = Some sum_start.
Proof. vm_compute. reflexivity. Qed.
(** `sum` has its loop head. *)
Lemma sum_find_L3 : find_block (TAtom "L3") (fn_blocks (ls_fn "sum")) = Some sum_L3.
Proof. vm_compute. reflexivity. Qed.
(** `sum` has its loop body. *)
Lemma sum_find_L4 : find_block (TAtom "L4") (fn_blocks (ls_fn "sum")) = Some sum_L4.
Proof. vm_compute. reflexivity. Qed.
(** `sum` has its exit. *)
Lemma sum_find_L5 : find_block (TAtom "L5") (fn_blocks (ls_fn "sum")) = Some sum_L5.
Proof. vm_compute. reflexivity. Qed.
(** `listsum` has its entry block. *)
Lemma ls_find_start : find_block (TAtom "start") (fn_blocks (ls_fn "listsum")) = Some ls_start.
Proof. vm_compute. reflexivity. Qed.
(** `listsum` has its loop head. *)
Lemma ls_find_L4 : find_block (TAtom "L4") (fn_blocks (ls_fn "listsum")) = Some ls_L4.
Proof. vm_compute. reflexivity. Qed.
(** `listsum` has its loop body. *)
Lemma ls_find_L5 : find_block (TAtom "L5") (fn_blocks (ls_fn "listsum")) = Some ls_L5.
Proof. vm_compute. reflexivity. Qed.
(** `listsum` has its exit. *)
Lemma ls_find_L7 : find_block (TAtom "L7") (fn_blocks (ls_fn "listsum")) = Some ls_L7.
Proof. vm_compute. reflexivity. Qed.
(** `sum` returns a `long`. *)
Lemma sum_ret : fn_ret (ls_fn "sum") = RClass L.
Proof. vm_compute. reflexivity. Qed.
(** `listsum` returns a `long`. *)
Lemma listsum_ret : fn_ret (ls_fn "listsum") = RClass L.
Proof. vm_compute. reflexivity. Qed.

(** ## Computing a step *)

(** Drop the wraps in E that arithmetic over the context proves are the
    identity, innermost first; leave every other wrap as it is. *)
Ltac drop_safe E :=
  repeat match type of E with
  | context[?x mod ?m] =>
      assert_fails (has_if x); assert_fails (has_mod x);
      let H := fresh in assert (H : x mod m = x) by (apply Z.mod_small; clear E; arith);
      rewrite H in E; clear H
  end.

(** Decide the integer comparisons in E that arithmetic over the
    context decides; leave every other one as it is. *)
Ltac decide_safe E :=
  repeat match type of E with
  | context[?a <? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ let H := fresh in assert (H : (a <? b) = true) by (apply Z.ltb_lt; clear E; arith);
              rewrite H in E; clear H
            | let H := fresh in assert (H : (a <? b) = false) by (apply Z.ltb_ge; clear E; arith);
              rewrite H in E; clear H ]
  | context[?a <=? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ let H := fresh in assert (H : (a <=? b) = true) by (apply Z.leb_le; clear E; arith);
              rewrite H in E; clear H
            | let H := fresh in assert (H : (a <=? b) = false) by (apply Z.leb_gt; clear E; arith);
              rewrite H in E; clear H ]
  | context[?a =? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ let H := fresh in assert (H : (a =? b) = true) by (apply Z.eqb_eq; clear E; arith);
              rewrite H in E; clear H
            | let H := fresh in assert (H : (a =? b) = false) by (apply Z.eqb_neq; clear E; arith);
              rewrite H in E; clear H ]
  end.

(** Rewrite in E what the context knows of memory (a load or an aux
    slot at an address arithmetic identifies), the module's function
    `sum` and its call frame. *)
Ltac ls_rewrites E :=
  repeat match goal with
  | H : forall a, a = _ -> load_bytes ?mm a 8 = _ |- _ =>
      match type of E with context[load_bytes mm ?a 8] =>
        let Hx := fresh in assert (Hx := H a ltac:(clear E; lia)); rewrite Hx in E; clear Hx end
  | H : forall a, a = _ -> m_aux ?mm a = _ |- _ =>
      match type of E with context[m_aux mm ?a] =>
        let Hx := fresh in assert (Hx := H a ltac:(clear E; lia)); rewrite Hx in E; clear Hx end
  | H : find_fn _ _ = _ |- _ => rewrite H in E
  | H : forall x rest, call_frame _ (x :: rest) = _ |- _ => rewrite H in E
  end.

(** Reduce E, an equation r = step g c, as far as the facts and
    arithmetic allow, keeping the module, its functions, memory
    operations and calls folded. *)
Ltac reduce_step E :=
  repeat progress (
    cbn -[load_bytes store_bytes store_aux ls_fn ls_module ls_globals find_fn call_frame] in E;
    try unfold sign_extension in E; try unfold raw_address in E; try unfold aligned_res in E;
    try unfold continue_at in E; try unfold with_point in E;
    try unfold int_load_res in E; try unfold access_res in E; try unfold cap_access_res in E;
    try unfold aux_at in E; try unfold max_allocation_size in E;
    use_facts E; ls_rewrites E;
    cbn [r_base r_end r_kind r_life ptr_addr ptr_cap] in E;
    drop_safe E; decide_safe E).

(** Replace each environment put k v e of the goal, e a variable, by a
    new variable, with what each name looks up to in it. *)
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

(** ## Over any runtime *)

Module IrisListSum (R : Runtime).
Module IH := IrisHeap R.
Module IM := IH.IM.
Module P := IM.P.
Module SS := IH.SS.
Import IM IH.

(** The genv of the module, whose free is R's. *)
Local Notation lge := (P.program_genv ls_module ls_globals).

(** Put the facts about the module's blocks, return classes, `sum` and
    its call frame in the context. *)
Ltac ls_facts :=
  pose proof sum_find_start; pose proof sum_find_L3; pose proof sum_find_L4; pose proof sum_find_L5;
  pose proof ls_find_start; pose proof ls_find_L4; pose proof ls_find_L5; pose proof ls_find_L7;
  pose proof sum_ret; pose proof listsum_ret; pose proof (ls_find_sum R.free); pose proof sum_call_frame.

(** Prove a goal step g c = r', with r' possibly holding existential
    variables, by computing the step. *)
Ltac compute_eq :=
  ls_facts;
  match goal with |- ?L = _ =>
    let r := fresh "r" in let E := fresh "E" in remember L as r eqn:E; reduce_step E; subst r
  end;
  reflexivity.

(** A one-instruction step that changes no memory. *)
Ltac wp_emp HK :=
  iApply (wpc_next _ emp%I with "[//]");
  [ exact HK
  | let m := fresh "m" in let s := fresh "s" in iIntros (m s) "_ _"; iPureIntro; compute_eq
  | iNext; iIntros "_"; gen_env ].

(** Entering a block: when the fuel F is 0 the run ends with
    [OutOfFuel]; otherwise the goal is left with F not 0. *)
Ltac wp_fuel HK :=
  match goal with |- environments.envs_entails _ (wpc _ (EConf _ _ ?F)) =>
    let Hz := fresh "Hz" in
    destruct (Z.eq_dec F 0) as [Hz|Hz];
    [ iApply (wpc_done _ emp%I _ _ _ OutOfFuel with "[//]");
      [ exact HK | intros []
      | let m := fresh "m" in let s := fresh "s" in iIntros (m s) "_ _"; iPureIntro; compute_eq ]
    | ]
  end.

Section proof.
Context {hlc : has_lc} {Σ : gFunctors} {HinvG : invGS_gen hlc Σ} {HheapG : gen_heapGS piece pval Σ}.

(** The pieces of a node at b: its life as a 16-byte heap object, the
    aux slot holding the next pointer nx's capability, the bytes of
    nx's address, and the bytes of the value x. *)
Definition node_ps (b : Z) (nx : ptr) (x : Z) : list (piece * pval) :=
  [(PLive b, VLive (mkRegion b (b + 16) Heap Live))] ++ [(PAux b 0, VAux (ptr_cap nx))] ++
  cell b 0 (ptr_addr nx) ++ cell b 8 x.

(** The list from p holds the values xs: null for none; otherwise p is
    its object's own pointer, at a positive, 16-aligned base that fits
    the address space, and the node there points to the rest. *)
Fixpoint lst (p : ptr) (xs : list Z) : iProp Σ :=
  match xs with
  | [] => ⌜p = null⌝
  | x :: xs' => ∃ b nx, ⌜p = mkPtr b (Obj b) /\ 0 < b /\ b + 16 <= 2 ^ 48 /\ b mod 16 = 0⌝ ∗
                pts (node_ps b nx x) ∗ lst nx xs'
  end%I.

(** The head of a list is null or a live object. *)
Lemma lst_head m s p xs : heap_interp (m, s) -∗ lst p xs -∗
  ⌜(ptr_cap p = CNone /\ ptr_addr p = 0) \/
   (exists b, p = mkPtr b (Obj b) /\ 0 < b /\ b + 16 <= 2 ^ 48 /\ live_at m b (mkRegion b (b + 16) Heap Live))⌝.
Proof.
  destruct xs as [|x xs]; cbn [lst].
  - iIntros "_ ->". iPureIntro. left. split; reflexivity.
  - iIntros "Hσ Hl". iDestruct "Hl" as (b nx (-> & Hb0 & Hb1 & _)) "[Hn _]".
    iDestruct (pts_facts with "Hσ Hn") as %(Hf & _). iPureIntro. right. exists b.
    split; [reflexivity|]. split; [exact Hb0|]. split; [exact Hb1|].
    unfold node_ps in Hf. apply all_agree_app in Hf as [Hf _].
    cbn [all_agree fst snd agree_piece] in Hf. exact (proj1 Hf).
Qed.

(** What a node at b and the list after it tell a step: b's region,
    the value's and the next address's bytes, and the next pointer's
    capability in the aux slot, exactly, since its object is live. *)
Lemma node_view m s b nx x xs : heap_interp (m, s) -∗ pts (node_ps b nx x) -∗ lst nx xs -∗
  ⌜object_region b (m_regions m) = Some (mkRegion b (b + 16) Heap Live) /\
   (forall a : Z, a = (b + 8)%Z -> load_bytes m a 8 = (x mod 2 ^ 64)%Z) /\
   (forall a : Z, a = b -> load_bytes m a 8 = ptr_addr nx) /\
   (forall a : Z, a = b -> m_aux m a = ptr_cap nx)⌝.
Proof.
  iIntros "Hσ Hn Hl". iDestruct (pts_facts with "Hσ Hn") as %(Hf & _).
  iDestruct (lst_head with "Hσ Hl") as %Hh. iPureIntro.
  unfold node_ps in Hf. apply all_agree_app in Hf as [Hla Hf].
  apply all_agree_app in Hf as [Hax Hf]. apply all_agree_app in Hf as [Hc0 Hc8].
  cbn [all_agree fst snd agree_piece] in Hla, Hax. destruct Hla as [Hlive _].
  destruct Hax as [(_ & Hax) _]. pose proof Hlive as [E L].
  split; [exact E|]. split; [|split].
  - intros a ->. exact (cell_load m b _ 8 x (b + 8) Hlive Hc8 eq_refl).
  - intros a ->. rewrite (cell_load m b _ 0 (ptr_addr nx) b Hlive Hc0); [|lia].
    apply Z.mod_small. destruct Hh as [[_ ->] | (nb & -> & ? & ? & _)]; cbn; lia.
  - intros a ->. destruct (Hax _ E L) as (_ & _ & Hx). replace (b + 0) with b in Hx by lia.
    apply aux_holds_live; [exact Hx|].
    destruct Hh as [[-> _] | (nb & -> & _ & _ & Hl)]; [left; reflexivity|].
    right. exists nb, (mkRegion nb (nb + 16) Heap Live). split; [reflexivity | exact Hl].
Qed.

(** A step of `sum`'s loop body that may read the node at b. *)
Ltac wp_node HK b nx x xs :=
  iApply (wpc_next _ (pts (node_ps b nx x) ∗ lst nx xs)%I with "[$Hn $Hl]");
  [ exact HK
  | let m := fresh "m" in let s := fresh "s" in
    iIntros (m s) "Hσ [Hn Hl]";
    iDestruct (node_view with "Hσ Hn Hl") as %(? & ? & ? & ?); iPureIntro; compute_eq
  | iNext; iIntros "[Hn Hl]"; gen_env ].

(** The continuation of a call of `sum` from the caller frame cf, whose
    result is bound to d: cf resumed with any result and any fuel. *)
Local Notation cont cf d callers :=
  (∀ y fuel', wpc lge (EConf (mkFrame (fr_fn cf) (put d (WInt y) (fr_env cf)) (fr_locals cf)
                                       (fr_doomed cf) (fr_at cf)) callers fuel'))%I.

(** `sum`'s loop, from the point after its head's phis: with `pr.1` the
    list's pointer p and `pr.2` an integer, owning the list and the
    continuation, the run is safe. By Löb induction. *)
Lemma sum_loop (HK : SS.keeps_live) cf d callers :
  ⊢ ∀ e p xs fuel, ⌜lookup (TAtom "pr.1") e = Some (WPtr p)⌝ -∗
      ⌜exists s, lookup (TAtom "pr.2") e = Some (WInt s)⌝ -∗ lst p xs -∗ cont cf d callers -∗
      wpc lge (EConf (mkFrame (ls_fn "sum") e [] None
                        (Exec (TAtom "L3") (b_insts sum_L3) (b_jump sum_L3)))
                     ((cf, mkPending (CResult d L) None) :: callers) fuel).
Proof.
  iLöb as "IH". iIntros (e p xs fuel Hp [s0 Hs]) "Hl HK".
  destruct xs as [|x xs].
  - iDestruct "Hl" as %->.
    wp_emp HK. wp_emp HK. wp_emp HK.
    wp_fuel HK. wp_emp HK.
    iApply (wpc_next _ emp%I with "[//]");
      [ exact HK
      | let m := fresh "m" in let s := fresh "s" in iIntros (m s) "_ _"; iPureIntro; compute_eq
      | iNext; iIntros "_"; iApply "HK" ].
  - iDestruct "Hl" as (b [na nc] (-> & Hb0 & Hb1 & Hb2)) "[Hn Hl]".
    wp_node HK b (mkPtr na nc) x xs. wp_node HK b (mkPtr na nc) x xs.
    wp_node HK b (mkPtr na nc) x xs.
    wp_fuel HK. wp_node HK b (mkPtr na nc) x xs.
    wp_node HK b (mkPtr na nc) x xs. wp_node HK b (mkPtr na nc) x xs.
    wp_node HK b (mkPtr na nc) x xs. wp_node HK b (mkPtr na nc) x xs.
    wp_node HK b (mkPtr na nc) x xs. wp_node HK b (mkPtr na nc) x xs.
    wp_node HK b (mkPtr na nc) x xs.
    wp_fuel HK. wp_node HK b (mkPtr na nc) x xs.
    iApply ("IH" $! _ (mkPtr na nc) xs with "[%] [%] Hl HK");
      [eassumption | eexists; eassumption].
Qed.

(** `sum`'s specification, the rule for calling it: from any caller
    frame cf whose call binds the result to d, over any callers stack,
    owning the list from p and the continuation, the call is safe. *)
Lemma sum_spec (HK : SS.keeps_live) cf d callers p xs fuel :
  ⊢ lst p xs -∗ cont cf d callers -∗
    wpc lge (EConf (mkFrame (ls_fn "sum") [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None))
                   ((cf, mkPending (CResult d L) None) :: callers) fuel).
Proof.
  iIntros "Hl HK".
  wp_fuel HK. wp_emp HK. wp_emp HK. wp_fuel HK. wp_emp HK.
  iApply (sum_loop HK with "[%] [%] Hl HK"); [reflexivity | eexists; reflexivity].
Qed.

(** A new node's object, split into the pieces the loop body uses: its
    life, its first aux slot, and its two cells; the other aux slots
    are dropped. *)
Lemma obj_split base :
  pts (obj_ps base (heap_req 16 16)) -∗
  pts [(PLive base, VLive (mkRegion base (base + 16) Heap Live))] ∗ pts [(PAux base 0, VAux CNone)] ∗
  pts (cell base 0 0) ∗ pts (cell base 8 0).
Proof.
  assert (E : obj_ps base (heap_req 16 16) =
     [(PLive base, VLive (mkRegion base (base + 16) Heap Live))] ++ cell base 0 0 ++ cell base 8 0 ++
     [(PAux base 0, VAux CNone)] ++ ((fun i => (PAux base i, VAux CNone)) <$> seqZ 1 15)) by reflexivity.
  rewrite E !pts_app. iIntros "(Hl & H0 & H8 & Ha & _)". iFrame.
Qed.

(** A step of `listsum`'s loop body that may read the new object's
    region. *)
Ltac wp_live HK :=
  iApply (wpc_next _ (pts _) with "Hlv");
  [ exact HK
  | let m := fresh "m" in let s := fresh "s" in
    iIntros (m s) "Hσ Hlv"; iDestruct (pts_facts with "Hσ Hlv") as %?; iPureIntro;
    match goal with H : owned_facts _ _ |- _ =>
      let H1 := fresh in destruct H as [H1 _]; cbn [all_agree fst snd agree_piece] in H1;
      destruct H1 as [[? _] _] end;
    compute_eq
  | iNext; iIntros "Hlv"; gen_env ].

(** `listsum`'s loop, from the point after its head's phis: with `pr.2`
    an int i in range, `pr.1` the list's pointer h and `v0` the input,
    owning the list, the run is safe. By Löb induction; each iteration
    allocates a node, stores h and i in it, and the loop goes on with
    i + 1 and the longer list; at the end `sum` is called with the
    list. *)
Lemma ls_loop (HK : SS.keeps_live) n :
  ⊢ ∀ e i h xs fuel,
      ⌜lookup (TAtom "pr.2") e = Some (WInt i) /\ 0 <= i < 2 ^ 31 /\
       lookup (TAtom "pr.1") e = Some (WPtr h) /\ lookup (TAtom "v0") e = Some (WInt n)⌝ -∗
      lst h xs -∗
      wpc lge (EConf (mkFrame (ls_fn "listsum") e [] None
                        (Exec (TAtom "L4") (b_insts ls_L4) (b_jump ls_L4))) [] fuel).
Proof.
  iLöb as "IH". iIntros (e i h xs fuel (Hi & Hir & Hh & Hn)) "Hl".
  wp_emp HK.
  match goal with H : lookup (TAtom "v10") _ = Some (WInt (if ?c then 1 else 0)) |- _ =>
    destruct c eqn:Hc end.
  - assert (Hi1 : i + 1 < 2 ^ 31).
    { apply Z.ltb_lt in Hc. revert Hc.
      repeat match goal with |- context[if ?b then _ else _] =>
        let Hb := fresh in destruct b eqn:Hb; [apply Z.leb_le in Hb | apply Z.leb_gt in Hb] end;
      intros; pose proof (Z.mod_pos_bound n (2 ^ 32) ltac:(lia));
      pose proof (Z.mod_pos_bound (n mod 2 ^ 32) (2 ^ 32) ltac:(lia)); lia. }
    wp_emp HK. wp_fuel HK. wp_emp HK.
    iApply (wpc_alloc _ (heap_req 16 16));
      [ exact HK | vm_compute; reflexivity | vm_compute; discriminate
      | let m := fresh "m" in intros m; compute_eq | ].
    iNext. iIntros (base (Hb0 & Hb1 & Hb2)) "Hobj". cbv beta.
    change (req_align (heap_req 16 16)) with 16 in Hb1.
    change (req_extent (heap_req 16 16)) with 16 in Hb2.
    iDestruct (obj_split with "Hobj") as "(Hlv & Hax & Hc0 & Hc8)".
    gen_env.
    wp_live HK.
    iApply (wpc_write _ ([(PLive base, VLive (mkRegion base (base + 16) Heap Live))] ++
                         [(PAux base 0, VAux CNone)] ++ cell base 0 0)
                        ([(PLive base, VLive (mkRegion base (base + 16) Heap Live))] ++
                         [(PAux base 0, VAux (ptr_cap h))] ++ cell base 0 (ptr_addr h))
              with "[Hlv Hax Hc0]");
      [ exact HK | reflexivity | reflexivity
      | let m := fresh "m" in intros m (Hf & Hd & _);
        apply all_agree_app in Hf as [Hf _]; cbn [all_agree fst snd agree_piece] in Hf;
        destruct Hf as [Hlive _]; pose proof Hlive as [Hor _];
        split; [compute_eq|]; cbv beta; eapply ptr_store_ok; [exact Hd | exact Hlive | cbn; lia | lia]
      | rewrite !pts_app; iFrame
      | iNext; iIntros "Hps"; iDestruct (pts_app with "Hps") as "[Hlv Hps]";
        iDestruct (pts_app with "Hps") as "[Hax Hc0]"; gen_env ].
    wp_emp HK. wp_emp HK. wp_live HK.
    iApply (wpc_write _ ([(PLive base, VLive (mkRegion base (base + 16) Heap Live))] ++ cell base 8 0)
                        ([(PLive base, VLive (mkRegion base (base + 16) Heap Live))] ++ cell base 8 i)
              with "[Hlv Hc8]");
      [ exact HK | reflexivity | reflexivity
      | let m := fresh "m" in intros m (Hf & Hd & _);
        apply all_agree_app in Hf as [Hf _]; cbn [all_agree fst snd agree_piece] in Hf;
        destruct Hf as [Hlive _]; pose proof Hlive as [Hor _];
        split; [compute_eq|]; cbv beta; split; [reflexivity|];
        match goal with |- context[store_bytes m ?a 8 _] =>
          destruct (cell_store_ok m base _ 8 a i Hd Hlive ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as [Hcs Hfr]
        end;
        split;
        [ apply all_agree_app; split; [|exact Hcs]; cbn [all_agree fst snd agree_piece];
          split; [apply (live_at_regions m); [reflexivity|exact Hlive] | exact I]
        | eapply frame_ok_mono; [|exact Hfr]; intros l Hin; rewrite fmap_app; apply elem_of_app;
          right; exact Hin ]
      | rewrite !pts_app; iFrame
      | iNext; iIntros "Hps"; iDestruct (pts_app with "Hps") as "[Hlv Hc8]"; gen_env ].
    wp_emp HK. wp_emp HK. wp_fuel HK. wp_emp HK.
    iApply ("IH" $! _ (i + 1) (mkPtr base (Obj base)) (i :: xs) with "[%] [Hlv Hax Hc0 Hc8 Hl]").
    { split; [eassumption|]. split; [lia|]. split; eassumption. }
    { cbn [lst]. iExists base, h. iSplitR; [iPureIntro; split; [reflexivity|]; lia|].
      iFrame "Hl". rewrite /node_ps !pts_app. iFrame. }
  - wp_emp HK. wp_fuel HK. wp_emp HK. wp_emp HK.
    iApply (sum_spec HK with "Hl"). iIntros (y fuel').
    cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
    iApply (wpc_done _ emp%I _ _ _ (Ret _) with "[//]");
      [ exact HK | intros []
      | let m := fresh "m" in let s := fresh "s" in iIntros (m s) "_ _"; iPureIntro; compute_eq ].
Qed.

(** `listsum` called with the int n is safe, with any fuel. *)
Lemma listsum_spec (HK : SS.keeps_live) n fuel :
  ⊢ wpc lge (EConf (mkFrame (ls_fn "listsum") [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
                   [] fuel).
Proof.
  iStartProof.
  wp_fuel HK. wp_emp HK. wp_emp HK. wp_fuel HK. wp_emp HK.
  iApply (ls_loop HK n $! _ _ _ [] with "[%] []").
  - split; [reflexivity|]. split; [lia|]. split; reflexivity.
  - cbn [lst]. done.
Qed.

End proof.

(** The resources the proof uses: invariants and the ghost heap. *)
Definition lsΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** [lsΣ] has invariants. *)
Global Instance lsΣ_inv : invGpreS lsΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** [lsΣ] has the ghost heap of pieces. *)
Global Instance lsΣ_heap : gen_heapGpreS piece pval lsΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** `listsum` never panics: if R frees no live object at a safepoint,
    then for every input whose first word is an int, with any fuel, no
    state of its run [fails], whatever bases its nodes get. Proved by
    Iris adequacy ([heap_never_panics]) from [listsum_spec]. *)
Theorem listsum_never_panics : SS.keeps_live ->
  P.never_panics ls_module (TAtom "listsum") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  intros HK.
  apply (heap_never_panics lsΣ ls_module (TAtom "listsum") _ ls_globals ls_mem (ls_fn "listsum")).
  - exact ls_initial.
  - exact (ls_find_listsum R.free).
  - intros b1 r1 b2 r2 [E _]. vm_compute in E. discriminate E.
  - intros xs (n & rest & ->). eexists. split; [apply listsum_call_frame|].
    intros fuel HinvG HheapG. apply listsum_spec, HK.
Qed.

End IrisListSum.
