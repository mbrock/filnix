(** A compiled function is a graph of blocks, and its proof has one
    lemma for each block. The older proofs join these lemmas by hand:
    each lemma assumes the lemma of the next block as a hypothesis, and
    a separate file composes them. This module joins them once. With
    it, the proof of a function is a table of block specifications and
    one lemma that closes the table.

    A block specification says what holds when the function reaches a
    label. It names the label, it gives the values of the C variables
    there in the way [CFrame](CFrame.v) defines, and it gives the
    memory that the function owns there. A proof shows each block
    correct, and for the blocks that this block jumps to it may assume
    the specifications in the table. The lemma [blocks_close] then
    proves every specification of the table. The lemma holds for a
    loop as well as for a straight chain of blocks. A jump takes one
    step of the program, and the proof needs the assumption only after
    that step.

    The functions that the blocks call are given as one list of
    contracts, the class [Callees]. A proof finds a callee's contract
    in the list by its name. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics CFrame.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap ExternalCalls Runtime Logic.
From Glibc Require Import OsWorld Fix.
Import ListNotations ProgramAbbreviations Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section blocks.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## Block specifications *)

(** A block specification has a label, a signature for the label's
    live temporaries, and a logical input. The input determines the
    values of the C variables, the memory owned at the label and what
    the function's caller gets back. *)
Record bspec : Type := BSpec {
  bs_label : string;
  bs_from : option string;
  bs_sig : cut_sig;
  bs_binder : Type;
  bs_vals : bs_binder -> list (string * word);
  bs_pre : bs_binder -> iProp Σ;
  bs_post : bs_binder -> outcome -> iProp Σ
}.

(** Compiled code can reach a block from several other blocks. A
    variable may then have a different value on each way in, and the
    block starts with phi nodes that pick the value for the way that
    was taken. The start of a loop is the usual case, because the
    function reaches it once from before the loop and again from the
    end of every round. A row for such a block therefore names the
    block that the function comes from, and the table has one row for
    each way in. A row that names no block is for a block without phi
    nodes, and it covers every way in. *)
Definition edge_fits (edge : option string) (from : option name) : Prop :=
  match edge with None => True | Some l => from = Some (TAtom l) end.

(** A block meets its specification when the function runs safely from
    the block's entry, along the row's edge, in every environment that
    fits the signature. *)
Definition block_triple (f : func) (b : bspec) : iProp Σ :=
  □ ∀ x e from Φ, ⌜edge_fits (bs_from b) from⌝ -∗ ⌜c_env (bs_sig b) e (bs_vals b x)⌝ -∗ bs_pre b x -∗
      (∀ r, bs_post b x r -∗ Φ r) -∗
      WP (ERun (mkFrame f e [] None (Enter (TAtom (bs_label b)) from)) : sexpr) {{ Φ }}.

(** Every block of a table meets its specification. *)
Definition blocks_hold (f : func) (bs : list bspec) : iProp Σ :=
  [∗ list] b ∈ bs, block_triple f b.

#[global] Instance blocks_hold_persistent f bs : Persistent (blocks_hold f bs).
Proof using Type. apply _. Qed.

(** A table is closed by proving every block under the assumption that
    the whole table holds after one more step. *)
Lemma blocks_close f bs :
  (⊢ ▷ blocks_hold f bs -∗ blocks_hold f bs) -> ⊢ blocks_hold f bs.
Proof using Type.
  intros H. iLöb as "IH". iApply H. iExact "IH".
Qed.

(** One block's specification can be taken out of a table that holds. *)
Lemma blocks_at f bs i b :
  bs !! i = Some b -> blocks_hold f bs ⊢ block_triple f b.
Proof using Type.
  intros Hb. iIntros "#H". iApply (big_sepL_lookup with "H"). exact Hb.
Qed.

(** A jump to a block of the table uses that block's specification. *)
Lemma wp_block f bs i b x e from Φ :
  bs !! i = Some b -> edge_fits (bs_from b) from -> c_env (bs_sig b) e (bs_vals b x) ->
  blocks_hold f bs -∗ bs_pre b x -∗ (∀ r, bs_post b x r -∗ Φ r) -∗
  WP (ERun (mkFrame f e [] None (Enter (TAtom (bs_label b)) from)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hb Hfrom He. iIntros "#H HP HK". iPoseProof (blocks_at f bs i b Hb with "H") as "#Hb".
  iApply ("Hb" $! x e from Φ with "[] [] HP HK"); iPureIntro; [exact Hfrom | exact He].
Qed.

(** ## A block's body *)

(** A block with several ways in has one row for each, and the rows
    differ only in what the phi nodes read. What the function does
    after the phi nodes is the same on every way in. A proof states
    that part once as the block's body and derives each row from it by
    the step into the block. *)

(** The function [body_at] gives the point of a function just after
    the phi nodes of the block l. *)
Definition body_at (f : func) (l : string) : point :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => Exec (TAtom l) (b_insts b) (b_jump b)
  | None => Enter (TAtom l) None
  end.

(** A body meets its specification when the function runs safely from
    the point after the phi nodes, in every environment that fits the
    signature. The signature names the temporaries that the phi nodes
    define, as [cut_body] computes it. *)
Definition body_triple (f : func) (l : string) (sig : cut_sig) (B : Type) (vals : B -> list (string * word))
    (pre : B -> iProp Σ) (post : B -> outcome -> iProp Σ) : iProp Σ :=
  □ ∀ x e Φ, ⌜c_env sig e (vals x)⌝ -∗ pre x -∗ (∀ r, post x r -∗ Φ r) -∗
      WP (ERun (mkFrame f e [] None (body_at f l)) : sexpr) {{ Φ }}.

(** ## From the entry block to the function's contract *)

(** A function meets a contract when the first row of its table
    covers the contract. That row names no edge, because a call
    enters the function from no block. The frame that a call builds
    must start at that row's block with an environment that fits its
    signature. The
    contract's precondition must give the row's precondition, and the
    row's postcondition must give the contract's. *)
Lemma blocks_has_spec n f s bs b :
  find_fn ge n = Some (Defined f) -> bs !! 0%nat = Some b -> bs_from b = None ->
  (forall x, exists e y,
      call_frame f (fs_args s x) = Some (mkFrame f e [] None (Enter (TAtom (bs_label b)) None)) /\
      c_env (bs_sig b) e (bs_vals b y) /\
      (fs_pre s x ⊢ bs_pre b y ∗ ∀ r, bs_post b y r -∗ fs_post s x r)) ->
  (⊢ blocks_hold f bs) ->
  HasSpec registry (os_wi w0) ge n s.
Proof using Type.
  intros Hf Hrow Hedge Hentry Hbs x. destruct (Hentry x) as (e & y & Hfr & He & Hpre).
  exists f. split; [exact Hf|]. split; [eexists; exact Hfr|].
  intros fr Φ Hfr'. rewrite Hfr in Hfr'. injection Hfr' as <-.
  iIntros "HP HK". iDestruct (Hpre with "HP") as "[HP HQ]".
  iPoseProof (blocks_at f bs 0%nat b Hrow with "[]") as "#Hb"; [iApply Hbs|].
  iApply ("Hb" $! y e None Φ with "[] [] HP"); [iPureIntro; rewrite Hedge; exact I | iPureIntro; exact He |].
  iIntros (r) "Hr". iApply "HK". iApply ("HQ" with "Hr").
Qed.

(** ## Callees *)

(** The functions that a body calls are given as one list of names
    with contracts. *)
Class Callees (cs : list (name * fspec Σ)) : Prop :=
  callees : Forall (fun c => HasSpec registry (os_wi w0) ge c.1 c.2) cs.

(** A contract in the list holds of its function. *)
Lemma callee_spec cs n s `{!Callees cs} : In (n, s) cs -> HasSpec registry (os_wi w0) ge n s.
Proof using Type.
  intros Hin. pose proof callees as H. rewrite Forall_forall in H. exact (H (n, s) Hin).
Qed.

(** A call to a function with a contract takes the contract's
    precondition and resumes the caller with its postcondition. This is
    [wp_call_spec] with the two resources joined, so that a proof names
    the hypotheses the callee gets and keeps the rest. *)
Lemma wp_call_callee n s `{!HasSpec registry (os_wi w0) ge n s} x f e ls lab r args rest j Ψ :
  map_option (arg_x ge e) args = Some (fs_args s x) ->
  fs_pre s x ∗
  (∀ v, fs_post s x v -∗ ∃ cf',
    ⌜resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None) v = Some cf'⌝ ∗
    ▷ WP (ERun cf' : sexpr) {{ Ψ }}) ⊢
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global n) args :: rest) j)) : sexpr) {{ Ψ }}.
Proof using Type.
  intros Hx. iIntros "[HP HK]". iApply (wp_call_spec with "HP HK"). exact Hx.
Qed.

End blocks.

(** Call-spec search finds a callee's contract in the section's list. *)
Ltac callee_member :=
  cbn [In]; repeat first [left; reflexivity | right].

#[global] Hint Extern 5 (HasSpec _ _ _ ?n _) =>
  (eapply callee_spec; [typeclasses eauto | callee_member]) : call_specs.

(** The tactic [call_callee] proves a call to a function that the
    callee list names. The proof gives the input x of the callee's
    contract, and it lists in Hs the hypotheses that the callee's
    precondition needs. The tactic leaves two goals. The first goal is
    the callee's precondition. In the second goal the callee has
    returned, and the hypothesis Hpost holds its postcondition. The
    proof reads the returned value from Hpost, and then the tactic
    [block_resume] continues the caller. *)
Tactic Notation "call_callee" "with" uconstr(x) "giving" constr(Hs) :=
  lazymatch goal with
  | P : @GlibcProgram ?hlc ?Σ |- context [mkFrame _ _ _ None (Exec _ (Call _ (Global ?n) _ :: _) _)] =>
      let s := open_constr:(_ : fspec Σ) in
      let H := constr:(ltac:(typeclasses eauto with typeclass_instances call_specs) :
        HasSpec (@program_registry hlc Σ P) (os_wi (@program_world hlc Σ P)) (@program_ge hlc Σ P) n s) in
      iApply (wp_call_callee n s (HasSpec0 := H) x);
        [vxu
        | iSplitL Hs;
            [cbn [fs_pre]
            | cbn [fs_post]; let v := fresh "v" in iIntros (v) "Hpost"]]
  end.

Ltac block_resume :=
  iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].

(** The tactic [block_enter] takes the step into a block of a row
    without an edge. Such a block is entered from any earlier block,
    so the tactic works only for a block without phi nodes. *)
Ltac block_enter :=
  iApply wp_enter;
    [reflexivity
    | lazymatch goal with |- phis_env _ _ ?from _ = _ => first [reflexivity | destruct from; reflexivity] end
    | iNext; cbn [b_insts b_jump]].

(** The tactic [block_enter_from] takes the step into a block of a row
    with an edge. The hypothesis H says which block the function came
    from, and the phi nodes read their values along that edge. *)
Ltac block_enter_from H :=
  cbn [edge_fits bs_from] in H; lazymatch type of H with ?from = _ => subst from end;
  iApply wp_enter; [reflexivity | vx | iNext; cbn [b_insts b_jump]].

(** The tactic [body_start] f l shows the instructions of the body of
    the block l of the function f, at the start of a proof of that
    body. *)
Ltac body_start f l :=
  let v := eval vm_compute in (body_at f l) in change (body_at f l) with v.

(** The tactic [branch_eqn] takes a conditional jump and leaves one
    goal for each edge, with the condition's value as the hypothesis E. *)
Ltac branch_eqn E :=
  iStartProof;
  eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    destruct (n =? 0) eqn:E end; cbn [edge_label].

(** The condition of a jump is an integer that the compiled code
    computed from comparisons, so the hypothesis E that [branch_eqn]
    leaves is hard to read. The tactic [branch_fact] replaces E with
    the comparisons themselves, as hypotheses about the integers that
    were compared. It closes the goal when E cannot hold. *)
Ltac branch_flag :=
  change (1 mod 2 ^ 32) with 1; change (0 mod 2 ^ 32) with 0;
  change (1 mod 2 ^ 64) with 1; change (0 mod 2 ^ 64) with 0.

Ltac branch_fact E :=
  revert E; unwrap2; branch_flag;
  repeat match goal with
    | |- context [?x =? ?y] => innermost x; innermost y; destruct (Z.eqb_spec x y); branch_flag
    | |- context [?x <? ?y] => innermost x; innermost y; destruct (Z.ltb_spec x y); branch_flag
    | |- context [?x <=? ?y] => innermost x; innermost y; destruct (Z.leb_spec x y); branch_flag
    end;
  intros E; try discriminate E; try (exfalso; lia); clear E.

(** The tactic [c_env_close] proves that the current environment fits a
    signature, by looking up each temporary and comparing addresses
    with arithmetic. *)
Ltac c_env_close := c_env_close_with ltac:(lk_prove) ltac:(a2).

(** The tactic [goto_block] finishes a block at a jump whose target is
    row i of the table. The hypothesis K is the block's continuation,
    which must accept the target's postcondition. The tactic proves
    that the environment fits the target's signature, and it leaves
    the target's precondition to the caller. *)
Tactic Notation "goto_block" constr(IH) constr(K) constr(i) "with" uconstr(x) :=
  lazymatch goal with
  | |- context [blocks_hold ?f ?bs] =>
      let b := eval hnf in (bs !! i) in
      lazymatch b with
      | Some ?b' =>
          iRevert K; iApply (wp_block f bs i b' x with IH);
            [reflexivity | first [exact I | reflexivity] | cbn [bs_sig bs_vals]; c_env_close | cbn [bs_pre]]
      | _ => fail "goto_block: the table has no row" i
      end
  end.
