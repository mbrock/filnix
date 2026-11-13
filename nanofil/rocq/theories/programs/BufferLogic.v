(** This module proves that the C function `c: buffer` in `buffer.c` never
    panics, using the [[iris|Iris]] program logic in `Logic.v` instead of a
    point-by-point transition table. The function allocates a four-long
    buffer on the collected heap, fills it with values, and sums its elements
    modulo four for any integer trip count.

    Each loop needs to know that the four-long buffer is still live and that
    all four slots are owned. In Iris, we represent the allocation as a
    region permission together with four 8-byte cells. Every bounds
    [[check]] uses the region permission to prove the buffer is live, and
    each load or store borrows only the single cell it accesses.

    Because the sum loop only reads the buffer as integers, the values stored
    in the four cells never affect memory safety. Each instruction step uses
    a weakest-precondition rule from `Logic.v`, and the symbolic tactics in
    `Symbolic.v` discharge the arithmetic and address side conditions. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic Pieces Heap Language Logic Buffer.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on symbolic values stays folded during premise
    reduction so bounds remain readable. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## The blocks, computed once

    Looking up each basic block of `buffer` on every symbolic step would
    slow down the proof. Instead, we extract all six basic blocks once at
    compile time and record lookup lemmas that the tactics can apply
    immediately. *)

(** Extracting block l from `buffer` returns its instruction list and jump,
    or a dummy unreachable block if missing. *)
Definition bblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks buffer_fn) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** The entry block allocates the four-long heap buffer. *)
Definition b_start : block := Eval vm_compute in bblk "start".
(** Block `L6` holds the header and condition check of the fill loop. *)
Definition b_L6 : block := Eval vm_compute in bblk "L6".
(** Block `L7` holds the body of the fill loop. *)
Definition b_L7 : block := Eval vm_compute in bblk "L7".
(** Block `L24` holds the header and condition check of the sum loop. *)
Definition b_L24 : block := Eval vm_compute in bblk "L24".
(** Block `L25` holds the body of the sum loop. *)
Definition b_L25 : block := Eval vm_compute in bblk "L25".
(** Block `L27` returns the computed sum. *)
Definition b_L27 : block := Eval vm_compute in bblk "L27".

(** Looking up `start` in `buffer` returns the precomputed entry block. *)
Lemma find_start : find_block (TAtom "start") (fn_blocks buffer_fn) = Some b_start.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L6` returns the precomputed fill-loop header. *)
Lemma find_L6 : find_block (TAtom "L6") (fn_blocks buffer_fn) = Some b_L6.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L7` returns the precomputed fill-loop body. *)
Lemma find_L7 : find_block (TAtom "L7") (fn_blocks buffer_fn) = Some b_L7.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L24` returns the precomputed sum-loop header. *)
Lemma find_L24 : find_block (TAtom "L24") (fn_blocks buffer_fn) = Some b_L24.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L25` returns the precomputed sum-loop body. *)
Lemma find_L25 : find_block (TAtom "L25") (fn_blocks buffer_fn) = Some b_L25.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L27` returns the precomputed exit block. *)
Lemma find_L27 : find_block (TAtom "L27") (fn_blocks buffer_fn) = Some b_L27.
Proof. vm_compute. reflexivity. Qed.
(** The compiled `buffer` function returns a 64-bit `long` value. *)
Lemma buffer_ret : fn_ret buffer_fn = RClass L.
Proof. vm_compute. reflexivity. Qed.



(** ## The buffer

    Allocating 32 bytes creates a live heap [[region]] starting at the
    returned address b. Defining that region shape in one place lets both
    loops refer to the same allocated object. *)

(** The allocated buffer forms a live 32-byte heap [[region]] starting at
    address b. *)
Definition buf_reg (b : Z) : region := mkRegion b (b + 32) Heap Live.

(** ## Taking a step

    Each IR instruction generates small side conditions about opcode kinds,
    block targets, and pointer arithmetic. Grouping those checks into
    tactics keeps the loop proofs focused on memory ownership rather than
    boilerplate. *)

(** This tactic proves address alignment and bounds conditions by simplifying
    [raw_address], dropping proven-safe wraps, and calling arithmetic. *)
Ltac addr :=
  unfold raw_address; cbn [ptr_addr ptr_cap r_end buf_reg]; rewrite ?Z.mod_1_r;
  drop_wraps_goal; arith.

(** Putting the six block lemmas and the return type into the context lets
    jump and return rules finish without repeated lookups. *)
Ltac buf_facts :=
  pose proof find_start; pose proof find_L6; pose proof find_L7; pose proof find_L24;
  pose proof find_L25; pose proof find_L27; pose proof buffer_ret.

(** This tactic unfolds the precomputed block definitions so the current
    instruction list becomes visible. *)
Ltac unfold_blocks :=
  cbn [b_insts b_jump b_start b_L6 b_L7 b_L24 b_L25 b_L27 edge_label].

(** This tactic discharges pure side goals from program-logic rules by
    computing opcode classes, reusing block facts, solving word equalities,
    and checking address bounds. *)
Ltac side :=
  lazymatch goal with
  | |- forall (_ : mem) (_ : unit), _ => intros; exact I
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

(** ## Over any runtime

    We parameterize the Iris proof by any [[runtime]] R so the resulting
    safety theorem holds for every implementation of the runtime interface.
    The module defines step tactics, splits the allocated buffer into cells,
    and verifies both loops before applying Iris [[adequacy]]. *)

(** This functor constructs the Iris safety proof for `buffer` over any
    runtime satisfying [Runtime]. *)
Module BufferLogic (R : Runtime).
Module LG := Logic R.
Module L := LG.L.
Module P := LG.P.
Import L LG.

(** The global environment links `buffer` against R's `free` handler. *)
Local Notation bge := (P.program_genv buffer_module buffer_globals).
(** Expressions in this language run over `buffer` with no external calls. *)
Local Notation bexpr := (language.expr (nanofil_lang no_contracts bge)).

(** ## The rules as tactics

    Proofs of individual instructions follow a repeating pattern of applying
    a rule and discharging its arithmetic side conditions. We wrap each rule
    with our side-condition solver so the loop proofs read almost like the
    instruction stream itself. *)

(** This tactic steps through a pure `let` binding and updates the local
    environment. *)
Ltac wp_let_ := iApply wp_let; first [side | iNext; gen_env].

(** This tactic steps through a conditional branch to the target block. *)
Ltac wp_branch_ := iApply wp_branch; first [side | iNext; cbn [edge_label Z.eqb Pos.eqb]].

(** This tactic enters a basic block and unfolds its instruction list. *)
Ltac wp_enter_ := iApply wp_enter; first [side | iNext; unfold_blocks; gen_env].

(** This tactic steps across an unconditional jump to the next block. *)
Ltac wp_goto_ := iApply wp_goto; iNext; unfold_blocks.

(** This tactic steps through a [[flight]] pointer-arithmetic instruction. *)
Ltac wp_flight_ := iApply wp_flight; first [side | iNext; gen_env].

Section proof.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The four 8-byte cells at base b represent the buffer's mutable storage,
    holding arbitrary integer values. *)
Definition cells (b : Z) : iProp Σ :=
  ∃ v0 v1 v2 v3, icell b 0 v0 ∗ icell b 8 v1 ∗ icell b 16 v2 ∗ icell b 24 v3.

(** For any index k from 0 to 3, the proof can borrow cell k from the buffer
    and return it with any updated value after a load or store. *)
Lemma cells_at b k :
  0 <= k < 4 -> cells b -∗ ∃ v, icell b (8 * k) v ∗ (∀ w, icell b (8 * k) w -∗ cells b).
Proof.
  intros Hk. iIntros "(%v0 & %v1 & %v2 & %v3 & H0 & H1 & H2 & H3)".
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [-> | [-> | [-> | ->]]] by lia; cbn [Z.mul];
    [iExists v0; iFrame "H0" | iExists v1; iFrame "H1" | iExists v2; iFrame "H2" | iExists v3; iFrame "H3"];
    iIntros (w) "Hw"; rewrite /cells; iExists _, _, _, _; iFrame.
Qed.

(** Splitting a freshly allocated 32-byte object yields its liveness token
    and four zero-initialized cells, discarding unused [[aux]] slots. *)
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

(** Throughout both loops, `v4` holds a 16-byte-aligned heap pointer to
    base b, whose 32-byte allocation fits inside the address space. *)
Definition holds (e : env) (b : Z) : Prop :=
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b (Obj b))) /\
  0 < b /\ b mod 16 = 0 /\ b + 32 <= 2 ^ 48.

(** Inside the sum loop, owning the array and its four slots guarantees
    safe execution as long as index j stays below 2^31. Each iteration
    checks the pointer and loads slot `j mod 4`. *)
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

(** Inside the fill loop, owning the array and its four elements guarantees
    safe execution for indices 0 through 3. When index i reaches 4, control
    moves to the sum loop with index 0 and sum 0. *)
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

(** Entering `buffer` with any integer argument n satisfies the Iris
    weakest precondition for safe execution. *)
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

(** To track heap ownership across execution steps, the proof combines Iris
    invariants with a ghost map of memory pieces. *)
Definition bufΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** The resource bundle [bufΣ] provides Iris invariants. *)
Instance bufΣ_inv : invGpreS bufΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** The ghost heap stores ownership of individual bytes and liveness tokens
    for the program. *)
Instance bufΣ_heap : gen_heapGpreS piece pval bufΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** Applying Iris [[adequacy]] to the weakest-precondition specification
    proves that `buffer` never panics for any integer input or fuel. *)
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

(** Instantiating the Iris functor with the [[interpreter]]'s runtime gives
    a concrete program-logic safety theorem. *)
Module InterpBufferLogic := BufferLogic InterpRuntime.

(** Under the interpreter's runtime, `buffer.c` never panics for any
    integer first argument. *)
Theorem interp_buffer_never_panics_logic :
  InterpBufferLogic.P.never_panics buffer_module (TAtom "buffer")
    (fun xs => exists n rest, xs = WInt n :: rest).
Proof. exact InterpBufferLogic.buffer_never_panics. Qed.
