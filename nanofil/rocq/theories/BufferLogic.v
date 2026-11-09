(** rocq/programs/buffer.c through the program logic of Logic.v.

    Buffer.v proves `buffer` never panics by an assertion at each of
    its 32 points, checked one symbolic step at a time. This file
    proves the same theorem ([buffer_never_panics]) in Iris: the
    allocation hands the program the new object's pieces ([obj]),
    which [obj_buf] splits into its life and four 8-byte cells
    ([cells]); each loop is a Löb induction at the point after its
    head's phis, carrying the life and the cells; each check lends the
    life back for one step, and each access takes the one cell it
    reaches ([cells_at]). The values the cells hold play no part. Every
    step is taken by its rule from Logic.v, its premises discharged by
    Symbolic.v's tactics on the premise alone. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic Pieces Heap Language Logic Buffer.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## The blocks, computed once *)

(** Block l of `buffer`, or an empty one. *)
Definition bblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks buffer_fn) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** The entry block, which allocates the buffer. *)
Definition b_start : block := Eval vm_compute in bblk "start".
(** The fill loop's head. *)
Definition b_L6 : block := Eval vm_compute in bblk "L6".
(** The fill loop's body. *)
Definition b_L7 : block := Eval vm_compute in bblk "L7".
(** The sum loop's head. *)
Definition b_L24 : block := Eval vm_compute in bblk "L24".
(** The sum loop's body. *)
Definition b_L25 : block := Eval vm_compute in bblk "L25".
(** The exit. *)
Definition b_L27 : block := Eval vm_compute in bblk "L27".

(** `buffer` has its entry block. *)
Lemma find_start : find_block (TAtom "start") (fn_blocks buffer_fn) = Some b_start.
Proof. vm_compute. reflexivity. Qed.
(** `buffer` has the fill loop's head. *)
Lemma find_L6 : find_block (TAtom "L6") (fn_blocks buffer_fn) = Some b_L6.
Proof. vm_compute. reflexivity. Qed.
(** `buffer` has the fill loop's body. *)
Lemma find_L7 : find_block (TAtom "L7") (fn_blocks buffer_fn) = Some b_L7.
Proof. vm_compute. reflexivity. Qed.
(** `buffer` has the sum loop's head. *)
Lemma find_L24 : find_block (TAtom "L24") (fn_blocks buffer_fn) = Some b_L24.
Proof. vm_compute. reflexivity. Qed.
(** `buffer` has the sum loop's body. *)
Lemma find_L25 : find_block (TAtom "L25") (fn_blocks buffer_fn) = Some b_L25.
Proof. vm_compute. reflexivity. Qed.
(** `buffer` has its exit. *)
Lemma find_L27 : find_block (TAtom "L27") (fn_blocks buffer_fn) = Some b_L27.
Proof. vm_compute. reflexivity. Qed.
(** `buffer` returns a `long`. *)
Lemma buffer_ret : fn_ret buffer_fn = RClass L.
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

(** ## The buffer *)

(** The buffer's region: a 32-byte live heap object at b. *)
Definition buf_reg (b : Z) : region := mkRegion b (b + 32) Heap Live.

(** ## Taking a step *)

(** Prove an address premise: an alignment to 1 holds at once; the
    wraps of [raw_address] are dropped where arithmetic proves them the
    identity, then arithmetic. *)
Ltac addr :=
  unfold raw_address; cbn [ptr_addr ptr_cap r_end buf_reg]; rewrite ?Z.mod_1_r;
  drop_wraps_goal; arith.

(** Put the facts about the blocks and the return class in the
    context, for the side goals of [wp_enter] and [wp_ret]. *)
Ltac buf_facts :=
  pose proof find_start; pose proof find_L6; pose proof find_L7; pose proof find_L24;
  pose proof find_L25; pose proof find_L27; pose proof buffer_ret.

(** Unfold the blocks that a frame's point names. *)
Ltac unfold_blocks :=
  cbn [b_insts b_jump b_start b_L6 b_L7 b_L24 b_L25 b_L27 edge_label].

(** Prove one pure premise of a rule of Logic.v: by computation for
    the op's classes, by a fact for a block and a return class, by
    [addr] for an address, by [compute_premise] for a word, and by
    arithmetic for a bound. *)
Ltac side :=
  lazymatch goal with
  | |- general_op _ = true => reflexivity
  | |- op_arg_classes _ _ = _ => reflexivity
  | |- find_block _ _ = _ => eassumption
  | |- fn_ret _ = _ => eassumption
  | |- _ <= max_allocation_size => apply Z.leb_le; reflexivity
  | |- forall m : mem, _ => intros ?; compute_premise
  | |- ptr_cap _ = _ => reflexivity
  | |- context[raw_address] => addr
  | |- _ = _ => first [ compute_premise | arith ]
  | |- _ => cbn [ptr_addr ptr_cap r_end buf_reg]; arith
  end.

(** ## Over any runtime *)

(** The proof over the runtime R. *)
Module BufferLogic (R : Runtime).
Module LG := Logic R.
Module L := LG.L.
Module P := LG.P.
Import L LG.

(** The genv of the module, whose free is R's. *)
Local Notation bge := (P.program_genv buffer_module buffer_globals).
(** The expressions of its language. *)
Local Notation bexpr := (language.expr (nanofil_lang bge)).

(** ## The rules as tactics *)

(** A [let] of an op that reads no memory, by [wp_let]. *)
Ltac wp_let_ := iApply wp_let; first [side | iNext; gen_env].

(** A branch, by [wp_branch], its target computed. *)
Ltac wp_branch_ := iApply wp_branch; first [side | iNext; cbn [edge_label Z.eqb Pos.eqb]].

(** Entering a block, by [wp_enter], its body unfolded. *)
Ltac wp_enter_ := iApply wp_enter; first [side | iNext; unfold_blocks; gen_env].

(** A goto, by [wp_goto]. *)
Ltac wp_goto_ := iApply wp_goto; iNext; unfold_blocks.

(** A [[flight]], by [wp_flight]. *)
Ltac wp_flight_ := iApply wp_flight; first [side | iNext; gen_env].

Section proof.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The buffer's four 8-byte cells at b, holding any values. *)
Definition cells (b : Z) : iProp Σ :=
  ∃ v0 v1 v2 v3, icell b 0 v0 ∗ icell b 8 v1 ∗ icell b 16 v2 ∗ icell b 24 v3.

(** The cell at offset 8 k, for k from 0 to 3, can be taken from the
    cells and given back holding anything. *)
Lemma cells_at b k :
  0 <= k < 4 -> cells b -∗ ∃ v, icell b (8 * k) v ∗ (∀ w, icell b (8 * k) w -∗ cells b).
Proof.
  intros Hk. iIntros "(%v0 & %v1 & %v2 & %v3 & H0 & H1 & H2 & H3)".
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [-> | [-> | [-> | ->]]] by lia; cbn [Z.mul];
    [iExists v0; iFrame "H0" | iExists v1; iFrame "H1" | iExists v2; iFrame "H2" | iExists v3; iFrame "H3"];
    iIntros (w) "Hw"; rewrite /cells; iExists _, _, _, _; iFrame.
Qed.

(** A new 32-byte object, split into its life and its four cells,
    which hold zero; the aux slots are dropped. *)
Lemma obj_buf base :
  obj base (heap_req 16 32) -∗ live base (buf_reg base) ∗ cells base.
Proof.
  rewrite /obj /live /cells /icell.
  assert (E : obj_ps base (heap_req 16 32) =
     [(PLive base, VLive (buf_reg base))] ++ cell base 0 0 ++ cell base 8 0 ++ cell base 16 0 ++
     cell base 24 0 ++ ((fun i => (PAux base i, VAux CNone)) <$> seqZ 0 32)) by reflexivity.
  rewrite E !pts_app. iIntros "(Hl & H0 & H8 & H16 & H24 & _)". iFrame "Hl".
  iExists 0, 0, 0, 0. iFrame.
Qed.

(** What both loops know of the environment e: `v4` holds the
    buffer's own pointer, its base b positive, 16-aligned and ending
    within the address space. *)
Definition holds (e : env) (b : Z) : Prop :=
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b (Obj b))) /\
  0 < b /\ b mod 16 = 0 /\ b + 32 <= 2 ^ 48.

(** The sum loop, from the point after its head's phis: with `pr.3` an
    int j from 0 below 2^31, `pr.2` any long, `v0` the input n, owning
    the buffer, the run is safe. By Löb induction; each iteration reads
    the cell j mod 4. *)
Lemma sum_loop n b :
  ⊢ ∀ e j s,
      ⌜holds e b /\ lookup (TAtom "pr.3") e = Some (WInt j) /\ 0 <= j < 2 ^ 31 /\
       lookup (TAtom "pr.2") e = Some (WInt s) /\ lookup (TAtom "v0") e = Some (WInt n)⌝ -∗
      live b (buf_reg b) -∗ cells b -∗
      WP (ERun (mkFrame buffer_fn e [] None (Exec (TAtom "L24") (b_insts b_L24) (b_jump b_L24)))
           : bexpr) {{ _, True }}.
Proof.
  iLöb as "IH". iIntros (e j s ((Hv4 & Hb0 & Hb1 & Hb2) & Hj & Hjr & Hs & Hn)) "Hlv Hc".
  buf_facts. cbn [b_L24 b_insts b_jump].
  wp_let_.
  match goal with H : lookup (TAtom "v30") _ = Some (WInt (if ?c then 1 else 0)) |- _ =>
    destruct c eqn:Hc end.
  - assert (Hj1 : j + 1 < 2 ^ 31).
    { apply Z.ltb_lt in Hc. revert Hc.
      destruct (2 ^ 31 <=? n mod 2 ^ 32) eqn:Hsg; [apply Z.leb_le in Hsg | apply Z.leb_gt in Hsg];
        intros; pose proof (Z.mod_pos_bound n (2 ^ 32) ltac:(lia)); lia. }
    wp_branch_. wp_enter_.
    wp_let_. wp_let_. wp_let_. wp_flight_.
    iDestruct (cells_at b (j mod 4) with "Hc") as (v) "[Hv Hc]"; [apply Z.mod_pos_bound; lia|].
    iApply (wp_check with "Hlv"); first [side | iNext; iIntros "Hlv"; gen_env].
    iApply (wp_raw_load with "Hlv Hv"); first [side | iNext; iIntros "Hlv Hv"; gen_env].
    iSpecialize ("Hc" with "Hv").
    wp_let_. wp_let_. wp_goto_. wp_enter_.
    iApply ("IH" $! _ (j + 1) with "[%] Hlv Hc").
    repeat split; try eassumption; lia.
  - wp_branch_. wp_enter_.
    iApply wp_ret; first [side | done].
Qed.

(** The fill loop, from the point after its head's phi: with `pr.1` an
    int i from 0 to 4 and `v0` the input n, owning the buffer, the run
    is safe. By Löb induction; each iteration writes the cell i; when i
    reaches 4 the sum loop starts with j and the sum 0. *)
Lemma fill_loop n b :
  ⊢ ∀ e i,
      ⌜holds e b /\ lookup (TAtom "pr.1") e = Some (WInt i) /\ 0 <= i <= 4 /\
       lookup (TAtom "v0") e = Some (WInt n)⌝ -∗
      live b (buf_reg b) -∗ cells b -∗
      WP (ERun (mkFrame buffer_fn e [] None (Exec (TAtom "L6") (b_insts b_L6) (b_jump b_L6)))
           : bexpr) {{ _, True }}.
Proof.
  iLöb as "IH". iIntros (e i ((Hv4 & Hb0 & Hb1 & Hb2) & Hi & Hir & Hn)) "Hlv Hc".
  buf_facts. cbn [b_L6 b_insts b_jump].
  wp_let_.
  match goal with H : lookup (TAtom "v11") _ = Some (WInt (if ?c then 1 else 0)) |- _ =>
    destruct c eqn:Hc end.
  - assert (Hi4 : i < 4) by (apply Z.ltb_lt in Hc; lia).
    wp_branch_. wp_enter_.
    wp_let_. wp_let_. wp_flight_. wp_let_. wp_let_.
    iDestruct (cells_at b i with "Hc") as (v) "[Hv Hc]"; [lia|].
    iApply (wp_check with "Hlv"); first [side | iNext; iIntros "Hlv"; gen_env].
    iApply (wp_raw_store with "Hlv Hv"); first [side | iNext; iIntros "Hlv Hv"; gen_env].
    iSpecialize ("Hc" with "Hv").
    wp_goto_. wp_enter_.
    iApply ("IH" $! _ (i + 1) with "[%] Hlv Hc").
    repeat split; try eassumption; lia.
  - assert (Hi4 : i = 4) by (apply Z.ltb_ge in Hc; lia).
    wp_branch_. wp_enter_.
    iApply (sum_loop n b $! _ 0 0 with "[%] Hlv Hc").
    repeat split; try eassumption; lia.
Qed.

(** `buffer` called with the int n is safe. *)
Lemma buffer_spec n :
  ⊢ WP (ERun (mkFrame buffer_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
         : bexpr) {{ _, True }}.
Proof.
  buf_facts. wp_enter_.
  iApply wp_alloc; first [side | iNext; iIntros (base (Hb0 & Hb1 & Hb2)) "Hobj"; gen_env].
  change (req_align (heap_req 16 32)) with 16 in Hb1.
  change (req_extent (heap_req 16 32)) with 32 in Hb2.
  iDestruct (obj_buf with "Hobj") as "[Hlv Hc]".
  wp_goto_. wp_enter_.
  iApply (fill_loop n base $! _ 0 with "[%] Hlv Hc").
  repeat split; try eassumption; lia.
Qed.

End proof.

(** The resources the proof uses: invariants and the ghost heap. *)
Definition bufΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** [bufΣ] has invariants. *)
Instance bufΣ_inv : invGpreS bufΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** [bufΣ] has the ghost heap of pieces. *)
Instance bufΣ_heap : gen_heapGpreS piece pval bufΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** `buffer` never panics: for every input whose first word is an int,
    with any fuel, no state of its run [fails], whatever base its
    buffer gets. Proved by Iris [[adequacy]] ([heap_never_panics]) from
    [buffer_spec]. *)
Theorem buffer_never_panics :
  P.never_panics buffer_module (TAtom "buffer") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply (heap_never_panics bufΣ buffer_module (TAtom "buffer") _ buffer_globals buffer_mem buffer_fn).
  - exact buffer_initial.
  - exact (buffer_find R.free).
  - intros b1 r1 b2 r2 [E _]. vm_compute in E. discriminate E.
  - intros xs (n & rest & ->). eexists. split; [apply buffer_call_frame|].
    intros HinvG HheapG. apply buffer_spec.
Qed.

End BufferLogic.

(** The theorem for the interpreter's runtime. *)
Module InterpBufferLogic := BufferLogic InterpRuntime.

(** buffer.c never panics under the interpreter's runtime, by the
    program logic. *)
Theorem interp_buffer_never_panics_logic :
  InterpBufferLogic.P.never_panics buffer_module (TAtom "buffer")
    (fun xs => exists n rest, xs = WInt n :: rest).
Proof. exact InterpBufferLogic.buffer_never_panics. Qed.
