(** Spike: spikes/listsum.c through the program logic of Logic.v.

    `sum` gets an Iris Hoare triple that hands the list back and states
    its result ([sum_spec]): from [lst] p xs, its run returns the sum of
    xs modulo 2^64 ([list_sum]) and the list is still there. `listsum`
    builds the list and calls `sum` through that triple
    ([wp_call_bind]), then drops the list. Each loop is a Löb induction
    at the point after its head's phis; `sum`'s carries the walked
    prefix as a list segment ([lseg]). Every step is taken by its rule
    from Logic.v, its premises discharged by Symbolic.v's tactics on
    the premise alone; [step] is never reduced on a whole
    configuration. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic.
From Spike Require Import Pieces ListSum IrisHeap Language Logic.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
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

(** ## Environments *)

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

(** ## Nodes *)

(** A node's region: a 16-byte live heap object at b. *)
Definition node_reg (b : Z) : region := mkRegion b (b + 16) Heap Live.

(** p is the own pointer of a node at b: positive, 16-aligned, and
    fitting the address space. *)
Definition node_ok (p : ptr) (b : Z) : Prop :=
  p = mkPtr b (Obj b) /\ 0 < b /\ b + 16 <= 2 ^ 48 /\ b mod 16 = 0.

(** ## Taking a step *)

(** Prove an address premise: an alignment to 1 holds at once; the
    wraps of [raw_address] are dropped where arithmetic proves them the
    identity, then arithmetic. *)
Ltac addr :=
  unfold raw_address; cbn [ptr_addr ptr_cap r_end node_reg]; rewrite ?Z.mod_1_r;
  drop_wraps_goal; arith.

(** Put the facts about the module's blocks and return classes in the
    context, for the side goals of [wp_enter] and [wp_ret]. *)
Ltac ls_facts :=
  pose proof sum_find_start; pose proof sum_find_L3; pose proof sum_find_L4; pose proof sum_find_L5;
  pose proof ls_find_start; pose proof ls_find_L4; pose proof ls_find_L5; pose proof ls_find_L7;
  pose proof sum_ret; pose proof listsum_ret.

(** Unfold the blocks of the module that a frame's point names. *)
Ltac unfold_blocks :=
  cbn [b_insts b_jump sum_start sum_L3 sum_L4 sum_L5 ls_start ls_L4 ls_L5 ls_L7 edge_label].

(** Prove one pure premise of a rule of Logic.v, HK being the runtime's
    premise: by computation for the op's classes, by a fact for a block
    and a return class, by [addr] for an address, by
    [compute_premise] for a word, and by arithmetic for a bound. *)
Ltac side HK :=
  first
  [ exact HK
  | lazymatch goal with
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
    end ].

(** ## Sums *)

(** The sum of the values xs modulo 2^64, as `sum` adds longs. *)
Definition list_sum (xs : list Z) : Z := fold_right Z.add 0 xs mod 2 ^ 64.

(** A sum is a 64-bit unsigned integer. *)
Lemma list_sum_range xs : 0 <= list_sum xs < 2 ^ 64.
Proof. apply Z.mod_pos_bound. lia. Qed.

(** Adding one more value, wrapped as `sum`'s loop adds it. *)
Lemma list_sum_snoc ys y : list_sum (ys ++ [y]) = (list_sum ys + y mod 2 ^ 64) mod 2 ^ 64.
Proof.
  unfold list_sum. rewrite fold_right_app. cbn [fold_right].
  assert (E : forall zs a, fold_right Z.add a zs = fold_right Z.add 0 zs + a).
  { induction zs as [|z zs IH]; intros a; cbn [fold_right]; [lia|]. rewrite IH. lia. }
  rewrite E. rewrite <- Zplus_mod. f_equal. lia.
Qed.

(** ## Over any runtime *)

(** The proof over the runtime R. *)
Module ListSumLogic (R : Runtime).
Module LG := Logic R.
Module L := LG.L.
Module P := LG.P.
Module SS := LG.SS.
Import L LG.

(** The genv of the module, whose free is R's. *)
Local Notation lge := (P.program_genv ls_module ls_globals).
(** The expressions of its language. *)
Local Notation lexpr := (language.expr (nanofil_lang lge)).

(** ## The rules as tactics *)

(** A [let] of an op that reads no memory, by [wp_let]. *)
Ltac wp_let_ HK := iApply wp_let; first [side HK | iNext; gen_env].

(** A branch, by [wp_branch], its target computed. *)
Ltac wp_branch_ HK := iApply wp_branch; first [side HK | iNext; cbn [edge_label Z.eqb Pos.eqb]].

(** Entering a block, by [wp_enter], its body unfolded. *)
Ltac wp_enter_ HK := iApply wp_enter; first [side HK | iNext; unfold_blocks; gen_env].

(** A goto, by [wp_goto]. *)
Ltac wp_goto_ HK := iApply wp_goto; [side HK | iNext; unfold_blocks].

(** A [[flight]], by [wp_flight]. *)
Ltac wp_flight_ HK := iApply wp_flight; first [side HK | iNext; gen_env].

(** `sum` called with the pointer p: its entry frame. *)
Definition sum_frame (p : ptr) : frame :=
  mkFrame (ls_fn "sum") [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).

Section proof.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The list from p holds the values xs: null for none; otherwise p is
    its node's own pointer ([node_ok]), and the node is live, holds the
    next pointer at offset 0 and the value at offset 8, and the rest of
    the list follows from the next pointer. *)
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

(** A list of one value or more, unfolded once. *)
Lemma lst_cons p x xs :
  lst p (x :: xs) ⊣⊢ ∃ b nx, ⌜node_ok p b⌝ ∗ live b (node_reg b) ∗ pcell b 0 nx ∗ icell b 8 x ∗ lst nx xs.
Proof. reflexivity. Qed.

(** A segment to q and the node at q make a segment to the node's next
    pointer. *)
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

(** The head of a list: its address is in range, and the life of the
    object its capability names, if any, can be lent out. *)
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

(** `sum`'s loop, from the point after its head's phis, with the walked
    prefix ys as a segment from p to q, the rest zs as the list from q,
    `pr.1` holding q and `pr.2` the prefix's sum: the run returns the
    whole list's sum and hands the list back. By Löb induction. *)
Lemma sum_loop (HK : SS.keeps_live) p Φ :
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
    wp_let_ HK. wp_let_ HK. wp_branch_ HK. wp_enter_ HK.
    iApply wp_ret; first [side HK | iNext].
    iApply "HΦ". iDestruct (lseg_lst _ _ _ [] with "Hs [//]") as "H". rewrite app_nil_r. iExact "H".
  - rewrite lst_cons. iDestruct "Hl" as (b nx (-> & Hb0 & Hb1 & Hb2)) "(Hlv & Hp & Hi & Hl)".
    ls_facts. cbn [sum_L3 b_insts b_jump].
    wp_let_ HK. wp_let_ HK. wp_branch_ HK. wp_enter_ HK.
    wp_flight_ HK.
    iApply (wp_check with "Hlv"); first [side HK | iNext; iIntros "Hlv"; gen_env].
    iApply (wp_raw_load with "Hlv Hi"); first [side HK | iNext; iIntros "Hlv Hi"; gen_env].
    wp_let_ HK.
    iApply (wp_half_check with "Hlv"); first [side HK | iNext; iIntros "Hlv"; gen_env].
    iDestruct (lst_cap with "Hl") as (Hnr) "[Hcap Hl]".
    iApply (wp_raw_load_pointer with "Hlv Hp Hcap");
      first [side HK | iNext; iIntros "Hlv Hp Hcap"; iSpecialize ("Hl" with "Hcap"); gen_env].
    wp_goto_ HK. wp_enter_ HK.
    iApply ("IH" $! _ nx (ys ++ [z]) zs with "[%] [Hs Hlv Hp Hi] Hl [HΦ]").
    + split; [eassumption|]. rewrite list_sum_snoc. eassumption.
    + iApply (lseg_snoc with "Hs Hlv Hp Hi"). unfold node_ok. auto.
    + rewrite -app_assoc. iExact "HΦ".
Qed.

(** `sum`'s specification: called with the list from p holding xs, it
    returns their sum modulo 2^64 and hands the list back. *)
Lemma sum_spec (HK : SS.keeps_live) p xs :
  ⊢ {{{ lst p xs }}} (ERun (sum_frame p) : lexpr) {{{ RET (Ret (WInt (list_sum xs))); lst p xs }}}.
Proof.
  iIntros (Φ) "!> Hl HΦ". ls_facts. unfold sum_frame.
  wp_enter_ HK. wp_goto_ HK. wp_enter_ HK.
  iApply (sum_loop HK p Φ $! _ p [] xs with "[%] [//] Hl HΦ").
  split; reflexivity.
Qed.


(** A new node's object, split into the pieces a node owns: its life,
    a null next pointer and a zero value; the other aux slots are
    dropped. *)
Lemma obj_node base :
  obj base (heap_req 16 16) -∗ live base (node_reg base) ∗ pcell base 0 null ∗ icell base 8 0.
Proof.
  rewrite /obj /live /pcell /icell.
  assert (E : obj_ps base (heap_req 16 16) =
     [(PLive base, VLive (node_reg base))] ++ cell base 0 0 ++ cell base 8 0 ++
     [(PAux base 0, VAux CNone)] ++ ((fun i => (PAux base i, VAux CNone)) <$> seqZ 1 15)) by reflexivity.
  rewrite E !IH.pts_app. iIntros "(Hl & H0 & H8 & Ha & _)". iFrame "Hl H8".
  rewrite (IH.pts_app [_] (cell base 0 0)). iFrame.
Qed.

(** `listsum`'s loop, from the point after its head's phis: with
    `pr.2` an int i in range, `pr.1` the list's pointer h and `v0` the
    input n, owning the list, the run is safe. By Löb induction; each
    iteration allocates a node, stores h and i in it, and the loop goes
    on with i + 1 and the longer list; at the end `sum` is called with
    the list through its triple, and the list it hands back is
    dropped. *)
Lemma ls_loop (HK : SS.keeps_live) n :
  ⊢ ∀ e i h xs,
      ⌜lookup (TAtom "pr.2") e = Some (WInt i) /\ 0 <= i < 2 ^ 31 /\
       lookup (TAtom "pr.1") e = Some (WPtr h) /\ lookup (TAtom "v0") e = Some (WInt n)⌝ -∗
      lst h xs -∗
      WP (ERun (mkFrame (ls_fn "listsum") e [] None (Exec (TAtom "L4") (b_insts ls_L4) (b_jump ls_L4)))
           : lexpr) {{ _, True }}.
Proof.
  iLöb as "IH". iIntros (e i h xs (Hi & Hir & Hh & Hn)) "Hl".
  ls_facts. pose proof (ls_find_sum R.free). cbn [ls_L4 b_insts b_jump].
  wp_let_ HK.
  match goal with H : lookup (TAtom "v10") _ = Some (WInt (if ?c then 1 else 0)) |- _ =>
    destruct c eqn:Hc end.
  - assert (Hi1 : i + 1 < 2 ^ 31).
    { apply Z.ltb_lt in Hc. revert Hc.
      destruct (2 ^ 31 <=? n mod 2 ^ 32) eqn:Hs; [apply Z.leb_le in Hs | apply Z.leb_gt in Hs];
        intros; pose proof (Z.mod_pos_bound n (2 ^ 32) ltac:(lia)); lia. }
    wp_branch_ HK. wp_enter_ HK.
    iApply wp_alloc; first [side HK | iNext; iIntros (base (Hb0 & Hb1 & Hb2)) "Hobj"; gen_env].
    change (req_align (heap_req 16 16)) with 16 in Hb1.
    change (req_extent (heap_req 16 16)) with 16 in Hb2.
    iDestruct (obj_node with "Hobj") as "(Hlv & Hp & Hi)".
    iApply (wp_check with "Hlv"); first [side HK | iNext; iIntros "Hlv"; gen_env].
    iApply (wp_raw_store_pointer with "Hlv Hp"); first [side HK | iNext; iIntros "Hlv Hp"; gen_env].
    wp_flight_ HK. wp_let_ HK.
    iApply (wp_half_check with "Hlv"); first [side HK | iNext; iIntros "Hlv"; gen_env].
    iApply (wp_raw_store with "Hlv Hi"); first [side HK | iNext; iIntros "Hlv Hi"; gen_env].
    wp_let_ HK. wp_goto_ HK. wp_enter_ HK.
    iApply ("IH" $! _ (i + 1) (mkPtr base (Obj base)) (i :: xs) with "[%] [Hlv Hp Hi Hl]").
    + split; [eassumption|]. split; [lia|]. split; eassumption.
    + rewrite lst_cons. iExists base, h. iFrame. iPureIntro. unfold node_ok. auto with zarith.
  - wp_branch_ HK. wp_enter_ HK.
    iApply wp_call_bind; try side HK.
    iNext. iApply (sum_spec HK with "Hl"). iNext. iIntros "_".
    iExists _. iSplit; [iPureIntro; reflexivity|].
    iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
    iApply wp_ret; first [side HK | done].
Qed.

(** `listsum` called with the int n is safe. *)
Lemma listsum_spec (HK : SS.keeps_live) n :
  ⊢ WP (ERun (mkFrame (ls_fn "listsum") [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
         : lexpr) {{ _, True }}.
Proof.
  ls_facts. wp_enter_ HK. wp_goto_ HK. wp_enter_ HK.
  iApply (ls_loop HK n $! _ 0 null [] with "[%] [//]").
  split; [reflexivity|]. split; [lia|]. split; reflexivity.
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
    Iris [[adequacy]] ([heap_never_panics]) from [listsum_spec]. *)
Theorem listsum_never_panics : SS.keeps_live ->
  P.never_panics ls_module (TAtom "listsum") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  intros HK.
  apply (heap_never_panics lsΣ ls_module (TAtom "listsum") _ ls_globals ListSum.ls_mem (ls_fn "listsum")).
  - exact ls_initial.
  - exact (ls_find_listsum R.free).
  - intros b1 r1 b2 r2 [E _]. vm_compute in E. discriminate E.
  - intros xs (n & rest & ->). eexists. split; [apply listsum_call_frame|].
    intros HinvG HheapG. apply listsum_spec. exact HK.
Qed.

End ListSumLogic.

(** The theorem for the interpreter's runtime. *)
Module InterpListSumLogic := ListSumLogic InterpRuntime.

(** The interpreter's runtime frees nothing at a safepoint, so
    listsum.c never panics under it, with no premise. *)
Theorem interp_listsum_never_panics :
  InterpListSumLogic.P.never_panics ls_module (TAtom "listsum")
    (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply InterpListSumLogic.listsum_never_panics.
  intros s m s' m' b reg [_ ->] Hr _. exact Hr.
Qed.
