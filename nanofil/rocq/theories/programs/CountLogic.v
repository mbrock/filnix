(** This module proves that the C program `count.c` never panics and
    always returns an integer when given a valid NUL-terminated string. The
    program defines a helper `c: next_l` that searches for the character `l`
    via `c: strchr`, and a loop `c: count_l` that counts how many `l` bytes
    occur by reading each matched byte and calling `c: next_l` on the rest of
    the string.

    Because `c: count_l` calls `c: next_l` both before and inside its loop, we
    first give `c: next_l` a reusable specification from `c: strchr`. At each
    call site, `c: count_l` passes either the whole string or the unread tail
    to `c: next_l`, then recovers the string when it returns. Because
    `c: strchr` never matches the NUL byte for a nonzero character, every
    non-null result points to a readable byte.

    The loop proof uses induction at the loop header, keeping the string
    intact while ensuring the cursor is either null or a match before NUL.
    We lift that specification to any [[runtime]] R and test it on the
    `"hello"` literal from `Hi.v` under the [[interpreter]]'s runtime. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import LibcCallFixtures Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls LibcCalls ExternalMachine Transport Pieces Heap ContractFrame Language Logic
  StringLogic LibcStringLogic CountCode Hi HiLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on symbolic values stays folded during premise
    reduction so pointer offsets remain readable. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The module

    The proof verifies the checked IR emitted by `nanofil -O` for `count.c`.
    We decode the compiled module, precompute the basic blocks of both
    functions, and link the `c: strchr` contract into the call table. *)

(** Decoding [count_term] extracts the compiled module for `count.c`. *)
Definition count_module : module :=
  match decode_module count_term with Some md => md | None => [] end.

(** The saved compiler fixture decodes cleanly into [count_module]. *)
Lemma count_decodes : decode_module count_term = Some count_module.
Proof. vm_compute. reflexivity. Qed.

(** Selecting the i-th function from the module returns its IR definition,
    or a dummy function if the index is out of range. *)
Definition count_nth (i : nat) : func :=
  match nth_error count_module i with
  | Some (IFunc f) => f
  | _ => mkFunc (TAtom "none") (TAtom "export") RVoid [] []
  end.

(** The helper function `next_l` searches a string for the byte `l`. *)
Definition next_l_fn : func := Eval vm_compute in count_nth 0.
(** The main function `count_l` loops over hits from `next_l` and counts
    them. *)
Definition count_fn : func := Eval vm_compute in count_nth 1.

(** The global table places `count_l` at address 65552 and `next_l` at
    address 65536. *)
Definition count_globals : list (name * ptr) :=
  [(TAtom "count_l", mkPtr 65552 (Fn (TAtom "count_l")));
   (TAtom "next_l", mkPtr 65536 (Fn (TAtom "next_l")))].

(** Laying out the module's globals produces the expected symbol table. *)
Lemma count_layout : option_map fst (initial_memory count_module) = Some count_globals.
Proof. vm_compute. reflexivity. Qed.

(** Extracting block l from function f returns its instruction list and
    terminator, or an empty unreachable block if missing. *)
Definition cblk (f : func) (l : String.string) : block :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** The single block of `next_l` calls `c: strchr` and returns its pointer. *)
Definition n_start : block := Eval vm_compute in cblk next_l_fn "start".
(** The entry block of `count_l` performs the initial call to `next_l`. *)
Definition c_start : block := Eval vm_compute in cblk count_fn "start".
(** Block `L6` checks whether the current search pointer is null. *)
Definition c_L6 : block := Eval vm_compute in cblk count_fn "L6".
(** Block `L7` loads the matched byte, increments the count, and searches the
    remaining suffix. *)
Definition c_L7 : block := Eval vm_compute in cblk count_fn "L7".
(** Block `L9` returns the accumulated match count. *)
Definition c_L9 : block := Eval vm_compute in cblk count_fn "L9".

(** Looking up `start` in `next_l` returns its precomputed block. *)
Lemma find_n_start : find_block (TAtom "start") (fn_blocks next_l_fn) = Some n_start.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `start` in `count_l` returns its precomputed entry block. *)
Lemma find_c_start : find_block (TAtom "start") (fn_blocks count_fn) = Some c_start.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L6` in `count_l` returns its precomputed loop header. *)
Lemma find_c_L6 : find_block (TAtom "L6") (fn_blocks count_fn) = Some c_L6.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L7` in `count_l` returns its precomputed loop body. *)
Lemma find_c_L7 : find_block (TAtom "L7") (fn_blocks count_fn) = Some c_L7.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L9` in `count_l` returns its precomputed exit block. *)
Lemma find_c_L9 : find_block (TAtom "L9") (fn_blocks count_fn) = Some c_L9.
Proof. vm_compute. reflexivity. Qed.

(** Calling function f with pointer p constructs an entry frame binding
    parameter `v0` to p. *)
Definition entry (f : func) (p : ptr) : frame :=
  mkFrame f [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).

(** The external call registry links `c: strchr` with an empty world state
    and leaves all other external names undefined. *)
Definition count_registry (symbol : name) : option (contract unit) :=
  if name_eqb symbol (TAtom "strchr") then Some (strchr_contract unit) else None.

(** ## What the loop holds

    Each iteration of `count_l` receives a pointer returned by `next_l` on
    some suffix of the string. We show that any match returned by `c: strchr`
    on a suffix is either null or points to a byte strictly before the
    terminating NUL, and then prove the Iris loop specification over any
    [[runtime]] R. *)

(** A pointer q satisfies [found_from] when it is either null or points to
    some byte index strictly before the string's terminating NUL. *)
Definition found_from (p : ptr) (bytes : list Z) (q : ptr) : Prop :=
  q = mkPtr 0 CNone \/
  exists j, (j < length bytes)%nat /\ q = mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p).

(** This tactic solves address bounds by simplifying [raw_address], dropping
    proven-safe wraps, and running integer arithmetic. *)
Ltac addr_premise := cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; arith.

(** This tactic solves word equalities by reflexivity or by looking up
    known values in the local environment. *)
Ltac word_premise := first [ reflexivity | compute_premise ].

(** This functor constructs the Iris safety proof for `count.c` over any
    [[runtime]] R. *)
Module CountLogic (R : Runtime).
Module SL := LibcStringLogic R.
Module LG := SL.LG.
Module L := LG.L.
Import L LG SL.

(** Any result returned by `c: strchr` on the whole string is either null or
    points within the string's content bytes. *)
Lemma found_first p bytes c q : strchr_found p bytes c q -> found_from p bytes q.
Proof.
  intros [(i & x & Hx & _ & _ & ->) | (_ & ->)]; [right | left; reflexivity].
  exists i. split; [exact (lookup_lt_Some _ _ _ Hx) | reflexivity].
Qed.

(** Any result returned by `c: strchr` on the suffix past index j is either
    null or points within the original string's content bytes. *)
Lemma found_next p bytes c q j : (j < length bytes)%nat ->
  strchr_found (mkPtr (ptr_addr p + Z.of_nat (S j)) (ptr_cap p)) (drop (S j) bytes) c q ->
  found_from p bytes q.
Proof.
  intros Hj [(i & x & Hx & _ & _ & ->) | (_ & ->)]; [right | left; reflexivity].
  rewrite lookup_drop in Hx. exists (S j + i)%nat. split; [exact (lookup_lt_Some _ _ _ Hx)|].
  cbn [ptr_addr ptr_cap]. f_equal. lia.
Qed.

(** The global environment links `count.c`'s symbols with R's `free`
    handler. *)
Definition count_ge : genv := mkGenv count_module count_globals R.free.

(** Looking up `next_l` in [count_ge] resolves to the compiled helper
    function. *)
Lemma find_next_l : find_fn count_ge (TAtom "next_l") = Some (Defined next_l_fn).
Proof. vm_compute. reflexivity. Qed.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris language instance pairs the external call table with an empty
    world and the module's symbols. *)
Local Instance count_irisGS : irisGS_gen hlc (nanofil_lang count_registry count_ge) Σ :=
  nanofil_irisGS count_registry no_world count_ge.

(** Expressions in this language run over `count.c` with `c: strchr` linked. *)
Local Notation cexpr := (language.expr (nanofil_lang count_registry count_ge)).

(** Calling `next_l` with ownership of the string at p returns a pointer
    satisfying `strchr_found` for `l` and restores full ownership of the
    string. *)
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

(** Starting from the loop header with a valid cursor q, owning the string
    guarantees safe execution and an integer return value. Each iteration
    loads the byte at q and calls `next_l` on the remaining suffix. *)
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

(** Calling `count_l` on an owned string searches from the start, enters
    the loop, and safely returns an integer count. *)
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

(** Applying Iris [[adequacy]] to [count_spec] proves that `count_l` never
    fails on any ready runtime holding a valid string in memory, and any
    returning run yields an integer. *)
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

(** ## The interpreter's runtime

    To show that the safety theorem applies to a real memory state, we
    instantiate it with the [[interpreter]]'s runtime. Calling `c: count_l`
    on the `"hello"` literal from `Hi.v` runs safely for any amount of
    fuel. *)

(** Instantiating the Iris functor with the interpreter's runtime yields a
    concrete safety theorem for `count.c`. *)
Module InterpCountLogic := CountLogic InterpRuntime.

(** Under the interpreter's runtime and `Hi.v`'s fixture memory, calling
    `count_l` on `"hello"` is safe for any fuel and returns an integer. *)
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
