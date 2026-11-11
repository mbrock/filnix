(** rocq/theories/programs/scan.c through the program logic of Logic.v, with
    strlen, strchr and puts called through [[campaign|Campaign]] 4's
    contracts.

    `scan` reads memory after a libc call: it takes the length of its
    string s, finds the first `l` in it, prints the rest of s from
    there, and then reads the byte after that `l` through the pointer
    strchr returned. Each call is a triple of StringLogic.v, used as a
    rule: [wp_strlen] and [wp_strchr] hand the string back unchanged,
    [wp_puts] hands back the suffix it was lent ([string_suffix]),
    which the frame for external calls keeps through puts's writes.
    The read after puts takes the object's life and the one byte from
    the suffix ([string_byte]) for a read check through the string's
    capability, read-write or read-only ([wp_check_read]), and a byte
    load ([wp_raw_load_byte]). That the `l` is not the NUL is what puts
    the byte after it inside the string.

    [scan_logic_safe] is the labelled machine's safety from any memory
    holding the string, with its object apart from the stdio world's
    roots; [interp_scan_logic_safe] instantiates it on Hi.v's fixture,
    whose literal is "hello". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap ContractFrame Language Logic
  StringLogic ScanCode Hi HiLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The module *)

(** The checked module nanofil makes of scan.c ([scan_term]). *)
Definition scan_module : module :=
  match decode_module scan_term with Some md => md | None => [] end.

(** The fixture decodes to [scan_module]. *)
Lemma scan_decodes : decode_module scan_term = Some scan_module.
Proof. vm_compute. reflexivity. Qed.

(** The module's one function, `scan`. *)
Definition scan_fn : func :=
  match scan_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "scan") (TAtom "export") (RClass W) [] []
  end.

(** The module's symbols: `scan` alone; strlen, strchr and puts are
    external. *)
Definition scan_globals : list (name * ptr) := [(TAtom "scan", mkPtr 65536 (Fn (TAtom "scan")))].

(** Laying out the module gives [scan_globals]. *)
Lemma scan_layout : option_map fst (initial_memory scan_module) = Some scan_globals.
Proof. vm_compute. reflexivity. Qed.

(** Block l of `scan`, or an empty one. *)
Definition sblk (l : String.string) : block :=
  match find_block (TAtom l) (fn_blocks scan_fn) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** The entry block: strlen, strchr, and the test for a miss. *)
Definition s_start : block := Eval vm_compute in sblk "start".
(** The miss: return 0. *)
Definition s_L8 : block := Eval vm_compute in sblk "L8".
(** The hit: puts, then the read after it. *)
Definition s_L10 : block := Eval vm_compute in sblk "L10".

(** `scan` has its entry block. *)
Lemma find_start : find_block (TAtom "start") (fn_blocks scan_fn) = Some s_start.
Proof. vm_compute. reflexivity. Qed.
(** `scan` has its miss block. *)
Lemma find_L8 : find_block (TAtom "L8") (fn_blocks scan_fn) = Some s_L8.
Proof. vm_compute. reflexivity. Qed.
(** `scan` has its hit block. *)
Lemma find_L10 : find_block (TAtom "L10") (fn_blocks scan_fn) = Some s_L10.
Proof. vm_compute. reflexivity. Qed.
(** `scan` returns an int. *)
Lemma scan_ret : fn_ret scan_fn = RClass W.
Proof. reflexivity. Qed.

(** `scan` called with the pointer p. *)
Definition scan_entry (p : ptr) : frame :=
  mkFrame scan_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).

(** A call of `scan` with p starts it at [scan_entry]. *)
Lemma scan_call_frame p : call_frame scan_fn [WPtr p] = Some (scan_entry p).
Proof. reflexivity. Qed.

(** The contracts `scan` is linked with: strlen, strchr and puts, the
    last with the trusted stream representation rep. *)
Definition scan_registry (rep : mem -> stdio_world -> Prop)
    (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop)
    (symbol : name) : option (contract stdio_world) :=
  if name_eqb symbol (TAtom "strlen") then Some (strlen_contract stdio_world)
  else if name_eqb symbol (TAtom "strchr") then Some (strchr_contract stdio_world)
  else if name_eqb symbol (TAtom "puts") then Some (puts_contract rep requests)
  else None.

(** The raw address of a at offset 0 is a, inside the address space. *)
Lemma raw_address_0 a : 0 <= a < 2 ^ 64 -> raw_address a 0 = a.
Proof. intros H. unfold raw_address. rewrite Z.add_0_r. apply Z.mod_small. exact H. Qed.

(** Prove an address premise: drop the wraps of [raw_address] and of
    the flight's sum where arithmetic shows them the identity, then
    arithmetic. *)
Ltac addr_premise := cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; arith.

(** `scan` over any [[runtime]] R. *)
Module ScanLogic (R : Runtime).
Module SL := StringLogic R.
Module LG := SL.LG.
Module L := LG.L.
Import L LG SL.

(** The linked genv: the module, its symbol, R's free. *)
Definition scan_ge : genv := mkGenv scan_module scan_globals R.free.

Section proof.
(** puts's trusted stream representation and allocation requests. *)
Variable rep : mem -> stdio_world -> Prop.
Variable requests : list word -> mem -> stdio_world -> Z -> Z -> Prop.

(** Hi.v's premise: a safepoint keeps rep and readiness. *)
Hypothesis stdio_stable : forall s m s' m' w,
  R.safepoint s m s' m' -> rep m w -> stdio_ready m w -> rep m' w /\ stdio_ready m' w.

(** [stdio_wi] survives safepoints, by [stdio_stable]. *)
Local Instance scan_wi_stable : SafepointStable (stdio_wi rep) := stdio_wi_safepoint rep stdio_stable.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris instance of `scan`: its contracts and [stdio_wi]. *)
Local Instance scan_irisGS : irisGS_gen hlc (nanofil_lang (scan_registry rep requests) scan_ge) Σ :=
  nanofil_irisGS (scan_registry rep requests) (stdio_wi rep) scan_ge.

(** The expressions of `scan`'s language. *)
Local Notation sexpr := (language.expr (nanofil_lang (scan_registry rep requests) scan_ge)).

(** `scan`, owning the string at p, is safe and returns an int. *)
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

(** `scan` is safe: from a ready runtime, live objects apart, puts's
    rep and readiness of the world, and a string at p, in an object no
    root of the world reaches into, with any fuel, no labelled run
    stops with a [failure_ending], and a run that returns returns an
    int. By [heap_labelled_safe] from [scan_spec], the ghost heap
    starting with the string's pieces. *)
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

(** ## The interpreter's runtime *)

(** `scan` over the interpreter's runtime. *)
Module InterpScanLogic := ScanLogic InterpRuntime.

(** `scan` is safe under the interpreter's runtime, called with Hi.v's
    literal "hello" in Hi.v's fixture memory, with the fixture's stream
    representation. *)
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
