(** This module verifies the C program `hi.c` using the [[iris|Iris]]
    program logic in `Logic.v` and the `c: puts` contract. The program
    contains a single `c: main` function that passes the string literal
    `"hello"` to `c: puts` and returns zero.

    While `Hi.v` proves `c: main` safe by hand with a four-phase state
    invariant, this module steps through each instruction with Iris rules.
    The program owns its six-byte string literal at its laid-out global
    address, while the stdio world interpretation tracks the trusted stream
    representation and keeps writable stdio buffers disjoint from the
    literal.

    When `c: main` runs, it enters its start block, copies the literal
    pointer, calls `c: puts`, and returns zero regardless of whether
    `c: puts` succeeds or returns EOF. Applying Iris [[adequacy]] lifts that
    specification to any [[runtime]] R, and we instantiate it on `Hi.v`'s
    fixture memory under the [[interpreter]]'s runtime. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import LibcCallFixtures Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic Hi.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The literal

    The compiled `hi.c` module places the string literal `"hello"` in
    read-only global data at address 65552. We describe that 8-byte global
    [[region]], list its six bytes including the NUL terminator, and show
    that no writable stdio buffer overlaps it. *)

(** The global [[region]] for `str.10` spans 8 bytes of live global data at
    address 65552. *)
Definition lit_reg : region := mkRegion 65552 65560 GlobalData Live.

(** The literal's byte contents consist of `"hello"` followed by a zero NUL
    byte. *)
Definition lit_bytes : list Z := hello_bytes ++ [0].

(** The program owns the string literal's object bounds and all six of its
    bytes. *)
Definition lit_ps : list (piece * pval) := string_ps hi_literal 65552 lit_reg hello_bytes.

(** The global object at address 65552 forms a valid NUL-terminated
    string. *)
Lemma lit_ok : string_ok hi_literal 65552 lit_reg hello_bytes.
Proof. unfold string_ok. cbn. split; [right; reflexivity|]. repeat split; try lia. repeat constructor; lia. Qed.

(** Every piece in [lit_ps] is either the object's liveness token or one of
    its six bytes. *)
Lemma lit_ps_cases l v : (l, v) ∈ lit_ps ->
  (l, v) = (PLive 65552, VLive lit_reg) \/
  exists i, 0 <= i < 6 /\ l = PByte 65552 i /\ v = VByte (nth (Z.to_nat i) lit_bytes 0).
Proof.
  cbn. rewrite !elem_of_cons elem_of_nil.
  intros [Hp|Hp]; [left; exact Hp | right].
  repeat destruct Hp as [Hp|Hp]; try contradiction;
    injection Hp as -> ->; eexists; (split; [|split; reflexivity]); lia.
Qed.

(** The stdio world satisfies [literal_apart] when none of its writable
    root spans overlap the literal's 8-byte global region. *)
Definition literal_apart (w : stdio_world) : Prop :=
  forall sp a, In sp (stdio_roots w) -> span_contains sp a -> ~ (65552 <= a < 65560).

(** This functor constructs the Iris safety proof for `hi.c` over any
    [[runtime]] R. *)
Module HiLogic (R : Runtime).
Module SL := LibcStringLogic R.
Module LG := SL.LG.
Module L := LG.L.
Module HB := Hi R.
Import L LG SL.

(** Whenever the literal is valid in physical memory, every piece in
    [lit_ps] agrees with that memory state. *)
Lemma lit_valid_agrees m : HB.hi_literal_valid m -> forall l v, (l, v) ∈ lit_ps -> agree_piece m l v.
Proof.
  intros [Hreg Hs] l v Hin. destruct (lit_ps_cases l v Hin) as [Hp|(i & Hi & -> & ->)].
  - injection Hp as -> ->. split; [exact Hreg | reflexivity].
  - cbn in Hs. split; [unfold registered; rewrite Hreg; discriminate|].
    intros reg E _. rewrite Hreg in E. injection E as <-. cbn. split; [lia|]. split; [lia|].
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia;
      cbn; tauto.
Qed.

Section proof.
(** The `c: puts` contract takes a stream representation and an allocation
    predicate as parameters. *)
Variable rep : mem -> stdio_world -> Prop.
Variable requests : list word -> mem -> stdio_world -> Z -> Z -> Prop.

(** Garbage-collector pauses must preserve both the trusted stream
    representation and stdio readiness. *)
Hypothesis stdio_stable : forall s m s' m' w,
  R.safepoint s m s' m' -> rep m w -> stdio_ready m w -> rep m' w /\ stdio_ready m' w.

(** Because `stdio_stable` keeps stream invariants intact, garbage-collector
    pauses preserve the world interpretation. *)
Local Instance hi_wi_stable : SafepointStable (stdio_wi rep) := stdio_wi_safepoint rep stdio_stable.

(** Calling `c: main` starts at its entry block with no local
    temporaries. *)
Definition hi_main : frame := mkFrame hi_function [] [] None (Enter (TAtom "start") None).

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris language instance pairs the external call table with the stdio
    world interpretation and `hi.c`'s symbols. *)
Local Instance hi_irisGS : irisGS_gen hlc (nanofil_lang (HB.hi_registry rep requests) HB.hi_genv) Σ :=
  nanofil_irisGS (HB.hi_registry rep requests) (stdio_wi rep) HB.hi_genv.

(** Expressions in this language run over `hi.c` with `c: puts` linked. *)
Local Notation hexpr := (language.expr (nanofil_lang (HB.hi_registry rep requests) HB.hi_genv)).

(** Calling `c: main` with ownership of the `"hello"` literal executes
    `c: puts` safely and returns zero regardless of what `c: puts` returns. *)
Lemma main_spec :
  string hi_literal 65552 lit_reg hello_bytes -∗ WP (ERun hi_main : hexpr) {{ o, ⌜o = Ret (WInt 0)⌝ }}.
Proof.
  iIntros "Hs". iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply wp_let; [reflexivity | reflexivity | reflexivity | intros m; reflexivity |]. iNext.
  iApply (wp_puts with "Hs"); [reflexivity | reflexivity | reflexivity | reflexivity |]. iNext. iIntros (n) "_".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. done.
Qed.

End wp.

(** Whenever the runtime is ready, live objects are disjoint, and the
    literal is valid and apart from stdio roots, `c: main` executes safely
    for any fuel and returns zero if it finishes. *)
Theorem hi_logic_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ} m s w fuel :
  R.ready s m -> live_disjoint m -> HB.hi_before_call rep m w -> literal_apart w ->
  labelled_safe (HB.hi_registry rep requests) HB.hi_genv hi_main m s w fuel (fun o => o = Ret (WInt 0)).
Proof.
  intros Hr Hd (Hrep & Hw & Hv) Hapart.
  apply (heap_labelled_safe Σ (HB.hi_registry rep requests) (stdio_wi rep) HB.hi_genv hi_main m s w
           (list_to_map lit_ps)).
  - exact Hr.
  - exact Hd.
  - intros l v Hl. exact (lit_valid_agrees m Hv l v (elem_of_list_to_map_2 _ _ _ Hl)).
  - split; [exact Hrep|]. split; [exact Hw|].
    intros sp a Hin Hs (l & v & reg & Hl & _ & [E _] & Hb). apply elem_of_list_to_map_2 in Hl.
    rewrite (string_ps_id _ _ _ _ l v Hl) in E, Hb. rewrite (proj1 Hv) in E. injection E as <-.
    exact (Hapart sp a Hin Hs Hb).
  - intros HinvG HheapG. rewrite big_sepM_list_to_map; [|exact (string_ps_nodup _ _ _ _)].
    iIntros "Hl". iApply main_spec. iSplit; [iPureIntro; exact lit_ok | iExact "Hl"].
Qed.

End proof.
End HiLogic.

(** To track heap ownership across execution steps, the proof combines Iris
    invariants with a ghost map of memory pieces. *)
Definition hiΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** The resource bundle [hiΣ] provides Iris invariants. *)
Instance hiΣ_inv : invGpreS hiΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** The ghost heap stores ownership of individual bytes and liveness tokens
    for the program. *)
Instance hiΣ_heap : gen_heapGpreS piece pval hiΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** ## The interpreter's runtime

    To check that `c: main` runs safely from a concrete memory state, we
    instantiate the theorem with the [[interpreter]]'s runtime. The libc
    root at 2048 and the literal at 65552 do not overlap and sit below the
    heap allocation threshold at 2^32. *)

(** Instantiating the Iris functor with the interpreter's runtime yields a
    concrete safety theorem for `hi.c`. *)
Module InterpHiLogic := HiLogic InterpRuntime.

(** Above 2^32, where the interpreter allocates new heap objects, `Hi.v`'s
    fixture memory contains only zero bytes and empty [[aux]] slots. *)
Lemma hi_memory_high : forall a, 2 ^ 32 <= a ->
  m_bytes HiChecks.memory a = 0 /\ m_aux HiChecks.memory a = CNone.
Proof.
  intros a Ha. unfold HiChecks.memory, hi_memory.
  lazy -[Z.eqb Z.leb Z.ltb Z.add Z.sub Z.mul Z.div Z.modulo Z.pow].
  repeat match goal with
  | |- context[a <? ?x] =>
      let E := fresh in
      assert (E : (a <? x) = false) by
        (apply Z.ltb_ge; apply Z.le_trans with (2 ^ 32); [vm_compute; discriminate | exact Ha]);
      rewrite E
  | |- context[?x <=? a] => destruct (x <=? a)
  end.
  all: split; reflexivity.
Qed.

(** The interpreter runtime is [[ready]] in `Hi.v`'s fixture memory because
    both the libc root and the literal lie below 2^32. *)
Lemma hi_memory_ready : InterpRuntime.ready InterpRuntime.start HiChecks.memory.
Proof.
  split; [vm_compute; split; congruence|]. split; [|exact hi_memory_high].
  intros b reg E. change (object_region b [mkRegion 2048 2064 Heap Live; lit_reg] = Some reg) in E.
  cbn -[Z.eqb] in E. destruct (2048 =? b) eqn:E1; [|destruct (65552 =? b) eqn:E2; [|discriminate E]];
    apply Z.eqb_eq in E1 || apply Z.eqb_eq in E2; subst b; injection E as <-;
    (split; [vm_compute; split; congruence|]); (split; [vm_compute; congruence | discriminate]).
Qed.

(** The libc root at 2048 and the string literal at 65552 occupy disjoint
    address ranges. *)
Lemma hi_memory_disjoint : live_disjoint HiChecks.memory.
Proof.
  intros b1 r1 b2 r2 [E1 _] [E2 _] Hne.
  change (object_region b1 [mkRegion 2048 2064 Heap Live; lit_reg] = Some r1) in E1.
  change (object_region b2 [mkRegion 2048 2064 Heap Live; lit_reg] = Some r2) in E2.
  cbn -[Z.eqb] in E1, E2.
  destruct (2048 =? b1) eqn:F1; [|destruct (65552 =? b1) eqn:G1; [|discriminate E1]];
  (destruct (2048 =? b2) eqn:F2; [|destruct (65552 =? b2) eqn:G2; [|discriminate E2]]);
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end;
  injection E1 as <-; injection E2 as <-; cbn; lia.
Qed.

(** Under the interpreter's runtime and `Hi.v`'s fixture memory, calling
    `c: main` executes safely for any amount of fuel and returns zero if it
    finishes. *)
Theorem interp_hi_logic_safe : forall fuel,
  InterpHiLogic.L.labelled_safe (InterpHiLogic.HB.hi_registry fixture_rep fixture_requests)
    InterpHiLogic.HB.hi_genv
    InterpHiLogic.hi_main HiChecks.memory InterpRuntime.start hello_world fuel
    (fun o => o = Ret (WInt 0)).
Proof.
  intros fuel. apply (InterpHiLogic.hi_logic_safe fixture_rep fixture_requests
    (HiChecks.interpreter_stdio_stable fixture_rep) hiΣ).
  - exact hi_memory_ready.
  - exact hi_memory_disjoint.
  - exact HiChecks.entry_pre.
  - intros sp a [<-|[]] Hs. unfold span_contains in Hs. cbn in Hs. lia.
Qed.
