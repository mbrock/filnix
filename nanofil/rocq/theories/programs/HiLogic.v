(** tests/c/prog/hi.c through the program logic of Logic.v, with puts
    called through [[campaign|Campaign]] 4's contract
    ([puts_contract]).

    Hi.v proves hi's body safe by hand: an invariant over the labelled
    machine's states with a case for each of main's four points, and a
    lemma for each kind of labelled step at each. This file proves the
    same body in Iris, by one rule per instruction and StringLogic.v's
    triple for puts ([wp_puts]):
    - the program owns its literal `str.10` as a [string]: its life and
      its six bytes ([lit_ps]);
    - the world interpretation is [stdio_wi]: puts's rep and
      [stdio_ready], and the world's writable roots apart from the
      program's live objects; a safepoint keeps it under Hi.v's
      premise that it keeps rep and readiness;
    - main enters, copies the literal, calls puts and returns 0
      ([main_spec]), and Iris [[adequacy]] for the labelled machine
      ([heap_labelled_safe]) makes that [hi_logic_safe].

    The theorem's premises beyond Hi.v's [hi_before_call] are the
    logic's own: the runtime [[ready]], the live objects apart, and the
    world's roots apart from the literal ([literal_apart]). Its
    conclusion is the logic's: no run stops with a [failure_ending],
    and main returns 0; Hi.v's [hi_ending] lists the stops that remain
    by name. docs/logic.md compares the two proofs. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic Hi.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The literal *)

(** The literal's object, `str.10`'s region in the module's layout. *)
Definition lit_reg : region := mkRegion 65552 65560 GlobalData Live.

(** The literal's bytes: hello and its NUL. *)
Definition lit_bytes : list Z := hello_bytes ++ [0].

(** The pieces of the literal the program owns, as a string: its life
    and its six bytes. *)
Definition lit_ps : list (piece * pval) := string_ps hi_literal 65552 lit_reg hello_bytes.

(** The literal is a string in its object. *)
Lemma lit_ok : string_ok hi_literal 65552 lit_reg hello_bytes.
Proof. unfold string_ok. cbn. split; [right; reflexivity|]. repeat split; try lia. repeat constructor; lia. Qed.

(** The six byte pieces, one by one. *)
Lemma lit_ps_cases l v : (l, v) ∈ lit_ps ->
  (l, v) = (PLive 65552, VLive lit_reg) \/
  exists i, 0 <= i < 6 /\ l = PByte 65552 i /\ v = VByte (nth (Z.to_nat i) lit_bytes 0).
Proof.
  cbn. rewrite !elem_of_cons elem_of_nil.
  intros [Hp|Hp]; [left; exact Hp | right].
  repeat destruct Hp as [Hp|Hp]; try contradiction;
    injection Hp as -> ->; eexists; (split; [|split; reflexivity]); lia.
Qed.

(** No writable root of the world w reaches into the literal's
    object. *)
Definition literal_apart (w : stdio_world) : Prop :=
  forall sp a, In sp (stdio_roots w) -> span_contains sp a -> ~ (65552 <= a < 65560).

(** hi over any [[runtime]] R. *)
Module HiLogic (R : Runtime).
Module SL := StringLogic R.
Module LG := SL.LG.
Module L := LG.L.
Module HB := Hi R.
Import L LG SL.

(** Where the literal is valid (Hi.v's [hi_literal_valid]: its region
    and its string), every piece of the literal agrees. *)
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
(** puts's trusted stream representation and allocation requests. *)
Variable rep : mem -> stdio_world -> Prop.
Variable requests : list word -> mem -> stdio_world -> Z -> Z -> Prop.

(** Hi.v's premise: a safepoint keeps rep and readiness. *)
Hypothesis stdio_stable : forall s m s' m' w,
  R.safepoint s m s' m' -> rep m w -> stdio_ready m w -> rep m' w /\ stdio_ready m' w.

(** [stdio_wi] survives safepoints, by [stdio_stable]. *)
Local Instance hi_wi_stable : SafepointStable (stdio_wi rep) := stdio_wi_safepoint rep stdio_stable.

(** main's frame at its entry. *)
Definition hi_main : frame := mkFrame hi_function [] [] None (Enter (TAtom "start") None).

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris instance of hi: puts's contract and [stdio_wi]. *)
Local Instance hi_irisGS : irisGS_gen hlc (nanofil_lang (HB.hi_registry rep requests) HB.hi_genv) Σ :=
  nanofil_irisGS (HB.hi_registry rep requests) (stdio_wi rep) HB.hi_genv.

(** The expressions of hi's language. *)
Local Notation hexpr := (language.expr (nanofil_lang (HB.hi_registry rep requests) HB.hi_genv)).

(** main, owning the literal, is safe and returns 0: it enters its
    block, copies the literal's pointer, calls puts and returns 0,
    whatever puts returned. *)
Lemma main_spec :
  string hi_literal 65552 lit_reg hello_bytes -∗ WP (ERun hi_main : hexpr) {{ o, ⌜o = Ret (WInt 0)⌝ }}.
Proof.
  iIntros "Hs". iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply wp_let; [reflexivity | reflexivity | reflexivity | intros m; reflexivity |]. iNext.
  iApply (wp_puts with "Hs"); [reflexivity | reflexivity | reflexivity | reflexivity |]. iNext. iIntros (n) "_".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. done.
Qed.

End wp.

(** hi's body is safe: from a ready runtime, live objects apart, Hi.v's
    [hi_before_call] and the world's roots apart from the literal, with
    any fuel, no labelled run stops with a [failure_ending], and a run
    that returns returns 0. By [heap_labelled_safe] from [main_spec],
    the ghost heap starting with the literal's pieces. *)
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

(** The resources the proof uses: invariants and the ghost heap. *)
Definition hiΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** [hiΣ] has invariants. *)
Instance hiΣ_inv : invGpreS hiΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** [hiΣ] has the ghost heap of pieces. *)
Instance hiΣ_heap : gen_heapGpreS piece pval hiΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** ## The interpreter's runtime *)

(** hi over the interpreter's runtime. *)
Module InterpHiLogic := HiLogic InterpRuntime.

(** Above 2^32, where the interpreter allocates, Hi.v's fixture memory
    holds no byte and no capability. *)
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

(** The interpreter is [[ready]] in Hi.v's fixture memory: the libc
    root at 2048 and the literal at 65552, both below its first
    allocation at 2^32. *)
Lemma hi_memory_ready : InterpRuntime.ready InterpRuntime.start HiChecks.memory.
Proof.
  split; [vm_compute; split; congruence|]. split; [|exact hi_memory_high].
  intros b reg E. change (object_region b [mkRegion 2048 2064 Heap Live; lit_reg] = Some reg) in E.
  cbn -[Z.eqb] in E. destruct (2048 =? b) eqn:E1; [|destruct (65552 =? b) eqn:E2; [|discriminate E]];
    apply Z.eqb_eq in E1 || apply Z.eqb_eq in E2; subst b; injection E as <-;
    (split; [vm_compute; split; congruence|]); (split; [vm_compute; congruence | discriminate]).
Qed.

(** The fixture's two live objects are apart. *)
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

(** hi's body is safe under the interpreter's runtime, from Hi.v's
    fixture: the libc root at 2048 and the initialized literal, with
    the fixture's stream representation. *)
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
