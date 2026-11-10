(** What the proofs of programs linked with user glibc's IR share
    (docs/glibc-ir.md): a raw load through a read-only capability,
    Iris [[adequacy]] for a program that starts owning pieces of its
    initial memory, and tactics that take a step whose values are all
    known by computing it.

    glibc's functions are module code here, so their runs are walked
    with Logic.v's rules like the program's own. When the program's
    data is fixed, as a literal is, every value of such a run is a
    numeral: [step] takes the next instruction by its rule, every
    premise computed by the virtual machine, and [norm_env] keeps the
    frame's environment a list of numerals, so values do not grow into
    the expressions that made them. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap Language Logic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Over a Logic instance *)

(** The shared rules and tactics over the [[runtime]] R and the Logic instance LG. *)
Module GlibcLogicOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Module P := LG.P.
Import L LG.

(** ## Tactics *)

(** An equation whose right side may be unknown: the left side
    computed, the right side made it, and the two checked by the
    virtual machine, so the kernel checks it the same way. *)
Ltac vm_eq :=
  match goal with |- ?l = ?r => let v := eval vm_compute in l in unify r v end;
  vm_compute; reflexivity.

(** A pure premise of a step, all of whose values are known: by
    computation. *)
Ltac side :=
  lazymatch goal with
  | |- forall _ : mem, _ => intros ?; vm_eq
  | |- ptr_cap _ = _ \/ ptr_cap _ = _ => right; reflexivity
  | |- _ <= _ => vm_compute; congruence
  | |- _ = _ => vm_eq
  end.

(** Replace the environment e of the goal by e', which the virtual
    machine shows equal. *)
Ltac replace_env e e' :=
  assert (Henv : e = e') by (vm_compute; reflexivity); try rewrite Henv; clear Henv.

(** Compute the environment of the goal's frame to a list of numerals. *)
Ltac norm_env :=
  match goal with
  | |- context [mkFrame ?f ?e ?ls ?d ?pt] => let e' := eval vm_compute in e in replace_env e e'
  end.

(** One step of a block by its rule, or fail: a pure let, a flight, a
    branch, a goto, or entering a block, whose instructions are then
    unfolded. *)
Ltac step :=
  first
    [ iApply wp_let; [side | side | side | side | iNext; norm_env]
    | iApply wp_flight; [side | side | side | iNext; norm_env]
    | iApply wp_branch; [side | iNext; cbn [edge_label Z.eqb Pos.eqb]]
    | iApply wp_goto; iNext
    | iApply wp_enter; [side | side | iNext; norm_env; cbn [b_insts b_jump]] ].

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** [wp_raw_load] through a read-write or read-only capability: a raw
    load of a long at offset off from the proven pointer p, which
    addresses offset o of the live object b, where the cell holds v: d
    is bound to v modulo 2^64. glibc's strlen reads a string literal's
    words through its read-only capability. *)
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

(** Iris [[adequacy]] where the program starts owning the pieces ps of
    its initial memory, distinct and agreeing with it: if, for every
    admissible input, owning ps gives the entry's frame a weakest
    precondition with no contracts under any invariant and ghost heap
    instance, the module never panics. [heap_never_panics] with ps for
    its empty ghost heap. *)
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

End GlibcLogicOn.

(** The resources the proofs use: invariants and the ghost heap. *)
Definition glibcΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** [glibcΣ] has invariants. *)
Instance glibcΣ_inv : invGpreS glibcΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** [glibcΣ] has the ghost heap of pieces. *)
Instance glibcΣ_heap : gen_heapGpreS piece pval glibcΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.
