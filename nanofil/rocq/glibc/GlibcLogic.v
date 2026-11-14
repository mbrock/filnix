(** When a C program is compiled together with user-space glibc functions
    as module IR, a proof steps through glibc's instructions using the
    same [[separation-logic]] rules from [Logic](../theories/logic/Logic.v)
    that it uses for the program's own code. This module collects the
    shared proof rule, [[adequacy]] theorem, and step-automation tactics
    used by proofs of programs linked with user-space glibc.

    ## Stepping through glibc on concrete data

    String routines in glibc, such as `c: strlen`, load whole 64-bit
    words from string literals that carry read-only
    [[capability|capabilities]]. Rule [wp_raw_load_read] extends raw
    64-bit loads to work through both read-write and read-only
    capabilities, and theorem [pieces_never_panics] proves adequacy for
    programs whose initial memory already holds global literals at entry.

    When a program runs on fixed input data such as a constant string,
    every intermediate value in the [[frame]] environment reduces to a
    concrete integer or pointer. The [step] tactic applies the next
    instruction's proof rule, solves its pure premises by virtual-machine
    computation, and uses [norm_env] to evaluate the updated environment
    into concrete literals so symbolic expressions do not build up across
    steps. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap Language Logic.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Over a Logic instance

    Every program proof instantiates the separation logic over a concrete
    [[runtime]] and shares that instance across library modules. This
    section parameterizes the user-glibc tactics and proof rules over an
    arbitrary [Runtime] and [LogicSig] instance so any program proof can
    import them directly. *)


Module LG := LG0.
Module L := LG.L.
Module P := LG.P.
Import L LG.

(** ## Tactics

    When a proof steps through glibc IR on concrete inputs, every
    instruction's operands and branch conditions evaluate to constants.
    This section defines tactics that discharge pure instruction premises
    by virtual-machine computation and keep the frame environment
    normalized after each step. *)

(** To solve an equality goal whose right-hand side may still be an
    existential variable, [vm_eq] computes the left-hand side with the
    virtual machine, unifies the right-hand side with that normal form,
    and closes the equation by computation. *)


(** When a step rule asks for a pure fact about concrete numbers or
    pointers, [side] proves that fact by running the virtual machine. *)


(** To keep a frame's environment from accumulating unevaluated updates,
    [replace_env] proves by computation that the current environment
    equals a normalized environment and rewrites the goal to use the
    normalized form. *)


(** After an instruction updates a [[temporary]] variable, [norm_env]
    evaluates the frame's environment with the virtual machine and
    replaces it in place with a list of concrete values. *)


(** When a function executes on concrete values, [step] advances the
    current basic block by one instruction and normalizes the resulting
    frame environment. It handles pure bindings, pointer-arithmetic
    [[flight]] instructions, conditional branches, unconditional jumps,
    and block entries. *)


Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** Inside this section, [rules_irisGS] registers the Iris program-logic
    instance for the active contract registry and world interpretation. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.

(** The notation [gexpr] abbreviates an Iris language expression for the
    current contract registry and global environment. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** String functions in glibc, such as `c: strlen`, read 8-byte words
    from constant string literals whose pointers carry read-only
    [[capability|capabilities]]. Rule [wp_raw_load_read] steps a 64-bit
    raw load through a read-write or read-only capability and binds the
    destination variable to the loaded 64-bit integer. *)
Lemma wp_raw_load_read f e ls l d k off args rest j classes p b reg o v Φ :
  op_arg_classes (RawLoad LdL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
  live b reg -∗ icell b o v -∗
  ▷ (live b reg -∗ icell b o v -∗
     WP (ERun (mkFrame f (put d (WInt (v mod 2 ^ 64)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha. iIntros "Hl Hc HK".
  iApply (wp_read registry wi ge ([(PLive b, VLive reg)] ++ cell b o v) _ _ [] with "[Hl Hc] [HK]").
  - intros m fuel (Hf & _). apply all_agree_app in Hf as [[Hlv _] Hcl]. cbn [agree_piece fst snd] in Hlv.
    destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load m k p off).
    + rewrite Ha (cell_load m b reg o v (b + o) Hlv Hcl eq_refl). reflexivity.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - rewrite pts_app. iFrame.
  - iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

End rules.

(** A program that contains global constants or string literals begins
    execution with those objects already allocated in initial memory.
    Theorem [pieces_never_panics] proves [[adequacy]] for such a module:
    if owning a list of distinct initial memory pieces suffices to prove
    the weakest precondition of the entry function for every admissible
    input, then the program never panics. *)
Theorem pieces_never_panics Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    md entry (input : list word -> Prop) globals m f (ps : list (piece * pval)) :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  live_disjoint m -> all_agree m ps -> NoDup ps.*1 ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\
     forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
       pts ps ⊢ WP (ERun fr : language.expr (nanofil_lang no_contracts (P.program_genv md globals)))
                  {{ _, True }}) ->
  P.never_panics md entry input.
Proof.
  intros Hm Hf Hd Ha Hn Hwp. apply (L.wp_never_panics HasNoLc Σ md entry input globals m f Hm Hf).
  intros xs Hxs. destruct (Hwp xs Hxs) as (fr & Hfr & Hw). exists fr. split; [exact Hfr|].
  intros Hready fuel Hinv.
  iMod (gen_heap_init (list_to_map ps : gmap piece pval)) as (HheapG) "(Hh & Hpts & _)".
  iModIntro. iExists (heap_interp no_world).
  iSplitL "Hh".
  - iExists _. iFrame "Hh". iPureIntro. split; [|split; [exact Hd | split; [exact Hready | exact I]]].
    intros l v Hl. exact (all_agree_elem _ _ _ _ Ha (elem_of_list_to_map_2 _ _ _ Hl)).
  - iApply (Hw Hinv HheapG). rewrite /pts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v));
      [iExact "Hpts" | exact Hn].
Qed.


(** When a program proof finishes, it closes its logical assumptions by
    supplying a state bundle that tracks invariants and memory ownership.
    The definition [glibcΣ] packages both of those components for
    user-glibc proofs. *)
Definition glibcΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** The instance [glibcΣ_inv] registers invariant support inside the
    [glibcΣ] resource bundle. *)
Instance glibcΣ_inv : invGpreS glibcΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** The instance [glibcΣ_heap] registers memory-ownership support inside
    the [glibcΣ] resource bundle. *)
Instance glibcΣ_heap : gen_heapGpreS piece pval glibcΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.
