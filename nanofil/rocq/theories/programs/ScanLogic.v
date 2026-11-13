(** This module proves that the C function `c: scan` in `scan.c` never
    panics and always returns an integer when called on a valid
    NUL-terminated string. The function measures the length of its input s
    with `c: strlen`, searches for the first `l` with `c: strchr`, prints
    the suffix starting at that `l` with `c: puts`, and then reads the byte
    immediately following the `l`.

    Reading memory after a `c: puts` call requires knowing that the call did
    not free or overwrite the caller's string. In our proof, `c: scan`
    hands the matched suffix to `c: puts` and takes it back upon return,
    while the external-call frame rule shields the string from any writes to
    standard output. Because `c: strchr` never matches the NUL terminator, at
    least one byte always follows a match.

    The safety proof works for any [[runtime]] R and any stream
    representation whose buffers stay disjoint from the string. We also test
    the theorem on the `"hello"` literal from `Hi.v` under the
    [[interpreter]]'s runtime. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import LibcCallFixtures Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls LibcCalls ExternalMachine Transport Pieces Heap ContractFrame Language Logic
  StringLogic LibcStringLogic ScanCode Hi HiLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The module

    The proof verifies the checked IR emitted by `nanofil -O` for `scan.c`.
    We decode the compiled module, precompute its three basic blocks, and
    link `c: strlen`, `c: strchr`, and `c: puts` into the external call
    table. *)

(** Decoding [scan_term] extracts the compiled module for `scan.c`. *)
Definition scan_module : module :=
  match decode_module scan_term with Some md => md | None => [] end.

(** The saved compiler fixture decodes cleanly into [scan_module]. *)
Lemma scan_decodes : decode_module scan_term = Some scan_module.
Proof. vm_compute. reflexivity. Qed.

(** The compiled function `scan` is the only definition in the module. *)
Definition scan_fn : func :=
  match scan_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "scan") (TAtom "export") (RClass W) [] []
  end.

(** The global table lists only `scan` at address 65536, while the three
    libc functions remain external. *)
Definition scan_globals : list (name * ptr) := [(TAtom "scan", mkPtr 65536 (Fn (TAtom "scan")))].

(** Laying out the module's globals produces the expected symbol table. *)
Lemma scan_layout : option_map fst (initial_memory scan_module) = Some scan_globals.
Proof. vm_compute. reflexivity. Qed.

(** Extracting block l from `scan` returns its instruction list and
    terminator, or an empty unreachable block if missing. *)
Definition sblk (l : String.string) : block :=
  match find_block (TAtom l) (fn_blocks scan_fn) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** The entry block calls `c: strlen` and `c: strchr`, then branches on
    whether `l` was found. *)
Definition s_start : block := Eval vm_compute in sblk "start".
(** Block `L8` handles the miss case by returning zero. *)
Definition s_L8 : block := Eval vm_compute in sblk "L8".
(** Block `L10` handles the hit case by calling `c: puts` and loading the
    following byte. *)
Definition s_L10 : block := Eval vm_compute in sblk "L10".

(** Looking up `start` in `scan` returns its precomputed entry block. *)
Lemma find_start : find_block (TAtom "start") (fn_blocks scan_fn) = Some s_start.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L8` returns the precomputed miss block. *)
Lemma find_L8 : find_block (TAtom "L8") (fn_blocks scan_fn) = Some s_L8.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L10` returns the precomputed hit block. *)
Lemma find_L10 : find_block (TAtom "L10") (fn_blocks scan_fn) = Some s_L10.
Proof. vm_compute. reflexivity. Qed.
(** The compiled `scan` function returns a 32-bit `int` value. *)
Lemma scan_ret : fn_ret scan_fn = RClass W.
Proof. reflexivity. Qed.

(** Calling `scan` with pointer p constructs an entry frame binding
    parameter `v0` to p. *)
Definition scan_entry (p : ptr) : frame :=
  mkFrame scan_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).

(** Passing a single pointer argument to `scan` enters the function at
    [scan_entry]. *)
Lemma scan_call_frame p : call_frame scan_fn [WPtr p] = Some (scan_entry p).
Proof. reflexivity. Qed.

(** The external call registry links `c: strlen`, `c: strchr`, and
    `c: puts` over the stdio world, using the given stream representation
    and allocation predicate. *)
Definition scan_registry (rep : mem -> stdio_world -> Prop)
    (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop)
    (symbol : name) : option (contract stdio_world) :=
  if name_eqb symbol (TAtom "strlen") then Some (strlen_contract stdio_world)
  else if name_eqb symbol (TAtom "strchr") then Some (strchr_contract stdio_world)
  else if name_eqb symbol (TAtom "puts") then Some (puts_contract rep requests)
  else None.

(** Adding offset 0 to an address inside the 64-bit address space leaves the
    address unchanged. *)
Lemma raw_address_0 a : 0 <= a < 2 ^ 64 -> raw_address a 0 = a.
Proof. intros H. unfold raw_address. rewrite Z.add_0_r. apply Z.mod_small. exact H. Qed.

(** This tactic solves address bounds by simplifying [raw_address], dropping
    proven-safe wraps, and running integer arithmetic. *)
Ltac addr_premise := cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; arith.

(** This functor constructs the Iris safety proof for `scan.c` over any
    [[runtime]] R. *)
Module ScanLogic (R : Runtime).
Module SL := LibcStringLogic R.
Module LG := SL.LG.
Module L := LG.L.
Import L LG SL.

(** The global environment links `scan.c`'s symbols with R's `free`
    handler. *)
Definition scan_ge : genv := mkGenv scan_module scan_globals R.free.

Section proof.
(** The stream representation and allocation predicate are parameters of the
    trusted `c: puts` contract. *)
Variable rep : mem -> stdio_world -> Prop.
Variable requests : list word -> mem -> stdio_world -> Z -> Z -> Prop.

(** Garbage-collector pauses must preserve both the trusted stream
    representation and stdio readiness. *)
Hypothesis stdio_stable : forall s m s' m' w,
  R.safepoint s m s' m' -> rep m w -> stdio_ready m w -> rep m' w /\ stdio_ready m' w.

(** Because `stdio_stable` keeps stream invariants intact, garbage-collector
    pauses preserve the world interpretation. *)
Local Instance scan_wi_stable : SafepointStable (stdio_wi rep) := stdio_wi_safepoint rep stdio_stable.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris language instance pairs the external call table with the stdio
    world interpretation and `scan`'s symbols. *)
Local Instance scan_irisGS : irisGS_gen hlc (nanofil_lang (scan_registry rep requests) scan_ge) Σ :=
  nanofil_irisGS (scan_registry rep requests) (stdio_wi rep) scan_ge.

(** Expressions in this language run over `scan.c` with all three libc
    functions linked. *)
Local Notation sexpr := (language.expr (nanofil_lang (scan_registry rep requests) scan_ge)).

(** Calling `scan` with ownership of the string at p executes safely across
    all three libc calls and returns an integer. *)
Lemma scan_spec p b reg bytes :
  string p b reg bytes -∗ WP (ERun (scan_entry p) : sexpr) {{ o, ⌜exists n, o = Ret (WInt n)⌝ }}.
Proof.
  iIntros "Hs". iDestruct "Hs" as "[%Hok Hps]".
  iAssert (string p b reg bytes) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hc & Hb0 & Hb1 & Hb2 & Hb3 & _).
  iApply wp_enter; [exact find_start | reflexivity |]. iNext. cbn [b_insts b_jump s_start].
  iApply (wp_strlen with "Hs"); [reflexivity | reflexivity | reflexivity | reflexivity |]. iNext. iIntros "Hs".
  iApply (wp_strchr with "Hs");
    [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |
     vm_compute; intuition congruence | vm_compute; intuition congruence |].
  iNext. iIntros (q Hq) "Hs".
  destruct Hq as [(i & x & Hx & Hxc & _ & ->) | (_ & ->)].
  - (* A hit at i, before the NUL. *)
    assert (Hi : (i < length bytes)%nat) by (apply lookup_lt_Some in Hx; exact Hx).
    assert (Hz : (ptr_addr p + Z.of_nat i =? 0) = false) by (apply Z.eqb_neq; lia).
    iApply wp_let; [reflexivity | reflexivity | reflexivity | intros m; reflexivity |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | reflexivity | intros m; reflexivity |]. iNext.
    iApply wp_branch; [reflexivity|]. iNext.
    rewrite (Z.mod_small (ptr_addr p + Z.of_nat i)); [|lia]. rewrite Hz. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_L10 | reflexivity |]. iNext. cbn [b_insts b_jump s_L10].
    iDestruct (string_suffix _ _ _ _ i with "Hs") as "[Hq _]"; [lia|].
    iApply (wp_puts with "Hq"); [reflexivity | reflexivity | reflexivity | reflexivity |]. iNext. iIntros (n) "Hq".
    iApply wp_flight; [reflexivity | reflexivity | reflexivity |]. iNext.
    destruct (drop i bytes) as [|x0 rest] eqn:Ed.
    { exfalso. apply (f_equal length) in Ed. rewrite length_drop in Ed. cbn in Ed. lia. }
    iDestruct (string_byte _ _ _ _ 1 (nth 0 (rest ++ [0]) 0) with "Hq") as "(%Hok' & Hl & Hb & _)".
    { destruct rest; reflexivity. }
    iApply (wp_check_read with "Hl");
      [reflexivity | reflexivity | exact Hc | addr_premise | addr_premise | apply Z.mod_1_r |].
    iNext. iIntros "Hl".
    iApply (wp_raw_load_byte with "Hl Hb"); [reflexivity | reflexivity | reflexivity | reflexivity |
      exact Hc | addr_premise |].
    iNext. iIntros "_ _".
    iApply wp_let; [reflexivity | reflexivity | reflexivity | intros m; reflexivity |]. iNext.
    iApply wp_ret; [exact scan_ret | reflexivity |]. iNext. iPureIntro. eexists. reflexivity.
  - (* A miss: return 0. *)
    iApply wp_let; [reflexivity | reflexivity | reflexivity | intros m; reflexivity |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | reflexivity | intros m; reflexivity |]. iNext.
    iApply wp_branch; [reflexivity|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_L8 | reflexivity |]. iNext. cbn [b_insts b_jump s_L8].
    iApply wp_ret; [exact scan_ret | reflexivity |]. iNext. iPureIntro. eexists. reflexivity.
Qed.

End wp.

(** Whenever the runtime is ready, the string is disjoint from stdio roots,
    and memory matches the string's pieces, `scan` runs safely for any fuel
    and returns an integer if it finishes. *)
Theorem scan_logic_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    m s w fuel p b reg bytes :
  R.ready s m -> live_disjoint m -> rep m w -> stdio_ready m w ->
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
  (forall sp a, In sp (stdio_roots w) -> span_contains sp a -> ~ (b <= a < r_end reg)) ->
  labelled_safe (scan_registry rep requests) scan_ge (scan_entry p) m s w fuel
    (fun o => exists n, o = Ret (WInt n)).
Proof.
  intros Hr Hd Hrep Hw Hok Ha Hapart.
  apply (heap_labelled_safe Σ (scan_registry rep requests) (stdio_wi rep) scan_ge (scan_entry p) m s w
           (list_to_map (string_ps p b reg bytes))).
  - exact Hr.
  - exact Hd.
  - intros l v Hl. exact (all_agree_elem _ _ _ _ Ha (elem_of_list_to_map_2 _ _ _ Hl)).
  - split; [exact Hrep|]. split; [exact Hw|].
    intros sp a Hin Hs (l & v & reg' & Hl & _ & [E _] & Hb). apply elem_of_list_to_map_2 in Hl.
    rewrite (string_ps_id _ _ _ _ _ _ Hl) in E, Hb. destruct Ha as [[E' _] _].
    cbn [fst snd] in E'. rewrite E' in E. injection E as <-. exact (Hapart sp a Hin Hs Hb).
  - intros HinvG HheapG. rewrite big_sepM_list_to_map; [|exact (string_ps_nodup p b reg bytes)].
    iIntros "Hs". iApply (scan_spec p b reg bytes with "[$Hs]"). done.
Qed.

End proof.
End ScanLogic.

(** ## The interpreter's runtime

    To check that a concrete memory state satisfies the theorem's
    preconditions, we instantiate the proof with the [[interpreter]]'s
    runtime. Calling `c: scan` on the `"hello"` literal in `Hi.v`'s fixture
    memory runs safely for any fuel. *)

(** Instantiating the Iris functor with the interpreter's runtime yields a
    concrete safety theorem for `scan.c`. *)
Module InterpScanLogic := ScanLogic InterpRuntime.

(** Under the interpreter's runtime and `Hi.v`'s fixture memory, calling
    `scan` on `"hello"` runs safely for any fuel and returns an integer. *)
Theorem interp_scan_logic_safe : forall fuel,
  InterpScanLogic.L.labelled_safe (scan_registry fixture_rep fixture_requests) InterpScanLogic.scan_ge
    (scan_entry hi_literal) HiChecks.memory InterpRuntime.start hello_world fuel
    (fun o => exists n, o = Ret (WInt n)).
Proof.
  intros fuel. destruct HiChecks.entry_pre as (Hrep & Hw & Hv).
  apply (InterpScanLogic.scan_logic_safe fixture_rep fixture_requests
    (HiChecks.interpreter_stdio_stable fixture_rep) hiΣ _ _ _ _ _ 65552 lit_reg hello_bytes).
  - exact hi_memory_ready.
  - exact hi_memory_disjoint.
  - exact Hrep.
  - exact Hw.
  - unfold string_ok. cbn. split; [right; reflexivity|]. repeat split; try lia.
    repeat constructor; lia.
  - apply all_agree_intro. intros l v Hl. exact (InterpHiLogic.lit_valid_agrees _ Hv l v Hl).
  - intros sp a [<-|[]] Hs. unfold span_contains in Hs. cbn in Hs. lia.
Qed.
