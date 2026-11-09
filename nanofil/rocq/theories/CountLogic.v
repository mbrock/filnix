(** rocq/programs/count.c through the program logic of Logic.v: a
    helper with its own specification, called in a loop, with memory
    read after each call.

    `next_l` is strchr for `l`. Its triple ([next_l_spec]) is proved
    once, from [wp_strchr], and `count_l` uses it at both of its calls
    through [wp_call_bind]: once on the whole string, then in the loop
    on the suffix just past each hit, which the string lends
    ([string_suffix]) and takes back after the call. The loop is a
    Löb induction at the point after its head's phis ([count_loop]):
    it owns the string, and the pointer it holds is null or a hit
    before the NUL ([found_from]). Each iteration reads the byte the
    pointer lands on through the string's capability ([wp_check_read],
    [wp_raw_load_byte]), so the read comes after a call and depends on
    the callee's postcondition: a hit is before the NUL, because `l` is
    not 0.

    [count_logic_safe] is the labelled machine's safety from any memory
    holding the string; [interp_count_logic_safe] instantiates it on
    Hi.v's fixture, whose literal "hello" has two `l`s. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap ContractFrame Language Logic
  StringLogic CountCode Hi HiLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The module *)

(** The checked module nanofil makes of count.c ([count_term]). *)
Definition count_module : module :=
  match decode_module count_term with Some md => md | None => [] end.

(** The fixture decodes to [count_module]. *)
Lemma count_decodes : decode_module count_term = Some count_module.
Proof. vm_compute. reflexivity. Qed.

(** The module's i-th function, or an empty one. *)
Definition count_nth (i : nat) : func :=
  match nth_error count_module i with
  | Some (IFunc f) => f
  | _ => mkFunc (TAtom "none") (TAtom "export") RVoid [] []
  end.

(** `next_l`: strchr for `l`. *)
Definition next_l_fn : func := Eval vm_compute in count_nth 0.
(** `count_l`: the loop. *)
Definition count_fn : func := Eval vm_compute in count_nth 1.

(** The module's symbols. *)
Definition count_globals : list (name * ptr) :=
  [(TAtom "count_l", mkPtr 65552 (Fn (TAtom "count_l")));
   (TAtom "next_l", mkPtr 65536 (Fn (TAtom "next_l")))].

(** Laying out the module gives [count_globals]. *)
Lemma count_layout : option_map fst (initial_memory count_module) = Some count_globals.
Proof. vm_compute. reflexivity. Qed.

(** Block l of f, or an empty one. *)
Definition cblk (f : func) (l : String.string) : block :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** `next_l`'s one block: strchr, then return its result. *)
Definition n_start : block := Eval vm_compute in cblk next_l_fn "start".
(** `count_l`'s entry: the first call of `next_l`. *)
Definition c_start : block := Eval vm_compute in cblk count_fn "start".
(** The loop's head: is the pointer null? *)
Definition c_L6 : block := Eval vm_compute in cblk count_fn "L6".
(** The loop's body: read the byte, count it, call `next_l` past it. *)
Definition c_L7 : block := Eval vm_compute in cblk count_fn "L7".
(** The exit: return the count. *)
Definition c_L9 : block := Eval vm_compute in cblk count_fn "L9".

(** `next_l` has its block. *)
Lemma find_n_start : find_block (TAtom "start") (fn_blocks next_l_fn) = Some n_start.
Proof. vm_compute. reflexivity. Qed.
(** `count_l` has its entry. *)
Lemma find_c_start : find_block (TAtom "start") (fn_blocks count_fn) = Some c_start.
Proof. vm_compute. reflexivity. Qed.
(** `count_l` has the loop's head. *)
Lemma find_c_L6 : find_block (TAtom "L6") (fn_blocks count_fn) = Some c_L6.
Proof. vm_compute. reflexivity. Qed.
(** `count_l` has the loop's body. *)
Lemma find_c_L7 : find_block (TAtom "L7") (fn_blocks count_fn) = Some c_L7.
Proof. vm_compute. reflexivity. Qed.
(** `count_l` has the exit. *)
Lemma find_c_L9 : find_block (TAtom "L9") (fn_blocks count_fn) = Some c_L9.
Proof. vm_compute. reflexivity. Qed.

(** A function called with the pointer p, at its entry. *)
Definition entry (f : func) (p : ptr) : frame :=
  mkFrame f [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).

(** `count_l`'s contracts: strchr's alone, over no world. *)
Definition count_registry (symbol : name) : option (contract unit) :=
  if name_eqb symbol (TAtom "strchr") then Some (strchr_contract unit) else None.

(** ## What the loop holds *)

(** The pointer q, for the string p with contents bytes, is null or
    points into it before its NUL, with its capability. *)
Definition found_from (p : ptr) (bytes : list Z) (q : ptr) : Prop :=
  q = mkPtr 0 CNone \/
  exists j, (j < length bytes)%nat /\ q = mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p).

(** Prove an address premise: drop the wraps of [raw_address] and of a
    flight's sum where arithmetic shows them the identity, then
    arithmetic. *)
Ltac addr_premise := cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; arith.

(** Prove a premise that names words: by computation, with the
    environment's facts. *)
Ltac word_premise := first [ reflexivity | compute_premise ].

(** `count.c` over any [[runtime]] R. *)
Module CountLogic (R : Runtime).
Module SL := StringLogic R.
Module LG := SL.LG.
Module L := LG.L.
Import L LG SL.

(** What strchr finds of a nonzero byte is null or before the NUL. *)
Lemma found_first p bytes c q : strchr_found p bytes c q -> found_from p bytes q.
Proof.
  intros [(i & x & Hx & _ & _ & ->) | (_ & ->)]; [right | left; reflexivity].
  exists i. split; [exact (lookup_lt_Some _ _ _ Hx) | reflexivity].
Qed.

(** What strchr finds in the suffix just past the j-th byte of the
    string, before its NUL, is null or before the string's NUL. *)
Lemma found_next p bytes c q j : (j < length bytes)%nat ->
  strchr_found (mkPtr (ptr_addr p + Z.of_nat (S j)) (ptr_cap p)) (drop (S j) bytes) c q ->
  found_from p bytes q.
Proof.
  intros Hj [(i & x & Hx & _ & _ & ->) | (_ & ->)]; [right | left; reflexivity].
  rewrite lookup_drop in Hx. exists (S j + i)%nat. split; [exact (lookup_lt_Some _ _ _ Hx)|].
  cbn [ptr_addr ptr_cap]. f_equal. lia.
Qed.

(** The linked genv: the module, its symbols, R's free. *)
Definition count_ge : genv := mkGenv count_module count_globals R.free.

(** `next_l` is a function of the module. *)
Lemma find_next_l : find_fn count_ge (TAtom "next_l") = Some (Defined next_l_fn).
Proof. vm_compute. reflexivity. Qed.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris instance of `count.c`: strchr's contract, no world. *)
Local Instance count_irisGS : irisGS_gen hlc (nanofil_lang count_registry count_ge) Σ :=
  nanofil_irisGS count_registry no_world count_ge.

(** The expressions of `count.c`'s language. *)
Local Notation cexpr := (language.expr (nanofil_lang count_registry count_ge)).

(** `next_l`'s triple: owning the string at p, it returns what strchr
    finds of `l`, and hands the string back. *)
Lemma next_l_spec p b reg bytes Φ :
  string p b reg bytes -∗
  ▷ (∀ q, ⌜strchr_found p bytes 108 q⌝ -∗ string p b reg bytes -∗ Φ (Ret (WPtr q))) -∗
  WP (ERun (entry next_l_fn p) : cexpr) {{ Φ }}.
Proof.
  iIntros "Hs HΦ". iApply wp_enter; [exact find_n_start | reflexivity |]. iNext.
  cbn [b_insts b_jump n_start].
  iApply (wp_strchr with "Hs");
    [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |
     vm_compute; intuition congruence | vm_compute; intuition congruence |].
  iNext. iIntros (q Hq) "Hs".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HΦ" with "[%] Hs"). exact Hq.
Qed.

(** The loop, from the point after its head's phis: with `pr.2` a
    pointer null or before the NUL of the string at p, which it owns,
    and `pr.1` an int, the run is safe and returns an int. By Löb
    induction; each iteration reads the byte at the pointer and calls
    `next_l` on the suffix past it. *)
Lemma count_loop p b reg bytes :
  ⊢ ∀ e q n, ⌜lookup (TAtom "pr.2") e = Some (WPtr q) /\ lookup (TAtom "pr.1") e = Some (WInt n) /\
               found_from p bytes q⌝ -∗
    string p b reg bytes -∗
    WP (ERun (mkFrame count_fn e [] None (Exec (TAtom "L6") (b_insts c_L6) (b_jump c_L6))) : cexpr)
      {{ o, ⌜exists k, o = Ret (WInt k)⌝ }}.
Proof.
  iLöb as "IH". iIntros (e q n (Hq & Hn & Hf)) "Hs".
  iDestruct "Hs" as "[%Hok Hps]". iAssert (string p b reg bytes) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hc & Hb0 & Hb1 & Hb2 & Hb3 & _). cbn [b_insts b_jump c_L6].
  destruct Hf as [-> | (j & Hj & ->)].
  - (* Null: the loop ends and returns the count. *)
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_c_L9 | reflexivity |]. iNext. cbn [b_insts b_jump c_L9].
    iApply wp_ret; [reflexivity | word_premise |]. iNext. iPureIntro. eexists. reflexivity.
  - (* A hit at j: read its byte, count it, and call next_l past it. *)
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_c_L7 | reflexivity |]. iNext. cbn [b_insts b_jump c_L7].
    destruct (lookup_lt_is_Some_2 bytes j Hj) as [x Hx].
    iDestruct (string_byte _ _ _ _ j x with "Hs") as "(_ & Hl & Hb & Hk)"; [by apply lookup_app_l_Some|].
    iApply (wp_check_read with "Hl");
      [reflexivity | word_premise | exact Hc | addr_premise | addr_premise | apply Z.mod_1_r |].
    iNext. iIntros "Hl". gen_env.
    iApply (wp_raw_load_byte with "Hl Hb");
      [reflexivity | word_premise | reflexivity | reflexivity | exact Hc | addr_premise |].
    iNext. iIntros "Hl Hb". iDestruct ("Hk" with "Hl Hb") as "Hs". gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat (S j)));
      [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
    iNext. gen_env.
    iApply wp_call_bind; [word_premise | exact find_next_l | reflexivity |]. iNext.
    iDestruct (string_suffix _ _ _ _ (S j) with "Hs") as "[Hs Hback]"; [lia|].
    iApply (next_l_spec with "Hs"). iNext. iIntros (q' Hq') "Hs".
    iDestruct ("Hback" with "Hs") as "Hs".
    iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
    iApply wp_goto. iNext.
    iApply wp_enter; [exact find_c_L6 | word_premise |]. iNext.
    iApply ("IH" with "[%] Hs"). split; [reflexivity|]. split; [reflexivity|].
    exact (found_next p bytes 108 q' j Hj Hq').
Qed.

(** `count_l`, owning the string at p, is safe and returns an int: it
    calls `next_l` on the whole string and enters the loop. *)
Lemma count_spec p b reg bytes :
  string p b reg bytes -∗ WP (ERun (entry count_fn p) : cexpr) {{ o, ⌜exists k, o = Ret (WInt k)⌝ }}.
Proof.
  iIntros "Hs". iApply wp_enter; [exact find_c_start | reflexivity |]. iNext.
  cbn [b_insts b_jump c_start].
  iApply wp_call_bind; [reflexivity | exact find_next_l | reflexivity |]. iNext.
  iApply (next_l_spec with "Hs"). iNext. iIntros (q Hq) "Hs".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_goto. iNext.
  iApply wp_enter; [exact find_c_L6 | reflexivity |]. iNext.
  iApply (count_loop p b reg bytes with "[%] Hs"). split; [reflexivity|]. split; [reflexivity|].
  exact (found_first p bytes 108 q Hq).
Qed.

End wp.

(** `count_l` is safe: from a ready runtime, live objects apart, and a
    string at p, with any fuel, no labelled run stops with a
    [failure_ending], and a run that returns returns an int. By
    [heap_labelled_safe] from [count_spec], the ghost heap starting
    with the string's pieces. *)
Theorem count_logic_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    m s fuel p b reg bytes :
  R.ready s m -> live_disjoint m -> string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
  labelled_safe count_registry count_ge (entry count_fn p) m s tt fuel
    (fun o => exists k, o = Ret (WInt k)).
Proof.
  intros Hr Hd Hok Ha.
  apply (heap_labelled_safe Σ count_registry no_world count_ge (entry count_fn p) m s tt
           (list_to_map (string_ps p b reg bytes))).
  - exact Hr.
  - exact Hd.
  - intros l v Hl. exact (all_agree_elem _ _ _ _ Ha (elem_of_list_to_map_2 _ _ _ Hl)).
  - exact I.
  - intros HinvG HheapG. rewrite big_sepM_list_to_map; [|exact (string_ps_nodup p b reg bytes)].
    iIntros "Hs". iApply (count_spec p b reg bytes with "[$Hs]"). done.
Qed.

End CountLogic.

(** ## The interpreter's runtime *)

(** `count.c` over the interpreter's runtime. *)
Module InterpCountLogic := CountLogic InterpRuntime.

(** `count_l` is safe under the interpreter's runtime, called with
    Hi.v's literal "hello" in Hi.v's fixture memory. *)
Theorem interp_count_logic_safe : forall fuel,
  InterpCountLogic.L.labelled_safe count_registry InterpCountLogic.count_ge
    (entry count_fn hi_literal) HiChecks.memory InterpRuntime.start tt fuel
    (fun o => exists k, o = Ret (WInt k)).
Proof.
  intros fuel. destruct HiChecks.entry_pre as (_ & _ & Hv).
  apply (InterpCountLogic.count_logic_safe hiΣ _ _ _ _ 65552 lit_reg hello_bytes).
  - exact hi_memory_ready.
  - exact hi_memory_disjoint.
  - exact lit_ok.
  - apply all_agree_intro. intros l v Hl. exact (InterpHiLogic.lit_valid_agrees _ Hv l v Hl).
Qed.
