(** tests/c/prog/hi.c through the program logic of Logic.v, with puts
    called through [[campaign|Campaign]] 4's contract
    ([puts_contract]).

    Hi.v proves hi's body safe by hand: an invariant over the labelled
    machine's states with a case for each of main's four points, and a
    lemma for each kind of labelled step at each. This file proves the
    same body in Iris, by one rule per instruction and a triple for
    puts derived from its contract:
    - the program owns the pieces of its literal `str.10`, its life and
      its six bytes ([lit_ps]); owning them in an interpreted state
      gives puts its [c_string] ([lit_agree_valid]);
    - the world interpretation [hi_wi] is what puts needs of the world:
      the representation rep, [stdio_ready], and the world's writable
      roots apart from the program's live objects ([roots_apart]). A
      safepoint keeps it, under Hi.v's premise that it keeps rep and
      readiness, by [collector_live];
    - after a puts call that returns, the state is interpreted again
      with the same ghost heap ([puts_return_frame]): the literal by the
      frame for external calls (Logic.v's [prefix_agrees]), the world by
      puts's prefix and the roots it delegates ([delegates_apart]);
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
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic Hi.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The literal's pieces *)

(** The literal's object, `str.10`'s region in the module's layout. *)
Definition lit_reg : region := mkRegion 65552 65560 GlobalData Live.

(** The literal's bytes: hello and its NUL. *)
Definition lit_bytes : list Z := hello_bytes ++ [0].

(** The pieces of the literal the program owns: its life and its six
    bytes. *)
Definition lit_ps : list (piece * pval) :=
  (PLive 65552, VLive lit_reg) :: zip_with (fun i x => (PByte 65552 i, VByte x)) (seqZ 0 6) lit_bytes.

(** The ghost heap hi starts with: the literal's pieces. *)
Definition lit_heap : gmap piece pval := list_to_map lit_ps.

(** No piece of the literal is listed twice. *)
Lemma lit_ps_nodup : NoDup lit_ps.*1.
Proof.
  cbn. repeat apply NoDup_cons_2; try apply NoDup_nil_2;
    rewrite ?elem_of_cons ?elem_of_nil; intuition discriminate.
Qed.

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

(** Every piece of the literal is of its object. *)
Lemma lit_ps_id l v : (l, v) ∈ lit_ps -> piece_id l = 65552.
Proof.
  intros Hin. destruct (lit_ps_cases l v Hin) as [Hp|(i & _ & -> & _)]; [injection Hp as -> _|]; reflexivity.
Qed.

(** ## The world *)

(** hi's world interpretation: puts's representation rep and
    [stdio_ready] of the world w in m, and the world's writable roots
    apart from the live objects owning pieces of h. *)
Definition hi_wi (rep : mem -> stdio_world -> Prop) (m : mem) (w : stdio_world)
    (h : gmap piece pval) : Prop :=
  rep m w /\ stdio_ready m w /\ roots_apart (stdio_roots w) h m.

(** No writable root of the world w reaches into the literal's
    object. *)
Definition literal_apart (w : stdio_world) : Prop :=
  forall sp a, In sp (stdio_roots w) -> span_contains sp a -> ~ (65552 <= a < 65560).

(** hi over any [[runtime]] R. *)
Module HiLogic (R : Runtime).
Module LG := Logic R.
Module L := LG.L.
Module HB := Hi R.
Import L LG.

(** Where the literal is valid (Hi.v's [hi_literal_valid]: its region
    and its string), every piece of the literal agrees. *)
Lemma lit_valid_agrees m : HB.hi_literal_valid m -> forall l v, (l, v) ∈ lit_ps -> agree_piece m l v.
Proof.
  intros [Hreg Hs] l v Hin. destruct (lit_ps_cases l v Hin) as [Hp|(i & Hi & -> & ->)].
  - injection Hp as -> ->. split; [exact Hreg | reflexivity].
  - cbn in Hs. split; [unfold registered; rewrite Hreg; discriminate|].
    intros reg E _. rewrite Hreg in E. injection E as <-. cbn. split; [lia|]. split; [lia|].
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as [->|[->|[->|[->|[->| ->]]]]] by lia;
      cbn; tauto.
Qed.

(** Where every piece of the literal agrees, the literal is valid. *)
Lemma lit_agree_valid m : (forall l v, (l, v) ∈ lit_ps -> agree_piece m l v) -> HB.hi_literal_valid m.
Proof.
  intros Ha.
  destruct (Ha (PLive 65552) (VLive lit_reg) ltac:(left)) as [Hreg _].
  assert (Hb : forall i, 0 <= i < 6 -> m_bytes m (65552 + i) = nth (Z.to_nat i) lit_bytes 0).
  { intros i Hi. assert (Hin : (PByte 65552 i, VByte (nth (Z.to_nat i) lit_bytes 0)) ∈ lit_ps).
    { assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as [->|[->|[->|[->|[->| ->]]]]] by lia;
        cbn; rewrite !elem_of_cons; tauto. }
    destruct (Ha _ _ Hin) as [_ Hl]. exact (proj2 (proj2 (Hl _ Hreg eq_refl))). }
  split; [exact Hreg|]. cbn.
  pose proof (Hb 0 ltac:(lia)) as B0. pose proof (Hb 1 ltac:(lia)) as B1.
  pose proof (Hb 2 ltac:(lia)) as B2. pose proof (Hb 3 ltac:(lia)) as B3.
  pose proof (Hb 4 ltac:(lia)) as B4. pose proof (Hb 5 ltac:(lia)) as B5.
  cbn in B0, B1, B2, B3, B4, B5. rewrite B0 B1 B2 B3 B4 B5. repeat split; lia.
Qed.

Section proof.
(** puts's trusted stream representation and allocation requests. *)
Variable rep : mem -> stdio_world -> Prop.
Variable requests : list word -> mem -> stdio_world -> Z -> Z -> Prop.

(** Hi.v's premise: a safepoint keeps rep and readiness. *)
Hypothesis stdio_stable : forall s m s' m' w,
  R.safepoint s m s' m' -> rep m w -> stdio_ready m w -> rep m' w /\ stdio_ready m' w.

(** A safepoint keeps [hi_wi]: rep and readiness by [stdio_stable],
    the roots apart since no region changes ([collector_live]). *)
Local Instance hi_wi_stable : SafepointStable (hi_wi rep).
Proof.
  split. intros s m s' m' w h Hsp (Hr & Hw & Ha).
  destruct (stdio_stable _ _ _ _ _ Hsp Hr Hw) as [Hr' Hw'].
  split; [exact Hr'|]. split; [exact Hw'|].
  intros sp a Hin Hs (l & v & reg & Hl & [E Hlive] & Hb). apply (Ha sp a Hin Hs).
  rewrite (R.collector_live _ _ _ _ Hsp) in E. exists l, v, reg. split; [exact Hl|]. split; [|exact Hb].
  split; [exact E | exact Hlive].
Qed.

(** A puts call returns one int. *)
Lemma puts_returns_int r args xs s m w trace values s' m' w' :
  M.E.invoke (puts_contract rep requests) r args xs s m w trace (CallReturn values) s' m' w' ->
  exists n, values = [WInt n].
Proof.
  intros H. remember (CallReturn values) as en eqn:Een. destruct H as [? ? ? ? ? ? _ _ _ Hp | ? ? ? ? ? ? _ _ _ _ _];
    [|discriminate Een].
  destruct Hp as (p & bytes & acc & tail & n & _ & _ & _ & _ & _ & Hend & _).
  subst. injection Hend as ->. eauto.
Qed.

(** After a puts call that returns, from a state the logic interprets
    with the ghost heap h, the state is interpreted with h again:
    puts's prefix keeps the runtime ready, the frame keeps h agreeing
    and live objects apart, and the prefix gives rep and readiness of
    the new world, whose roots it delegated from the old roots and its
    born objects, so they stay apart from h. *)
Lemma puts_return_frame r args xs s m w trace values s' m' w' h :
  M.E.invoke (puts_contract rep requests) r args xs s m w trace (CallReturn values) s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> hi_wi rep m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ hi_wi rep m' w' h.
Proof.
  intros Hi Ha Hd Hr (Hrep & Hw & Hapart).
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  destruct (prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hp Hr Hd Ha Hapart ltac:(intros ? ? ? []))
    as (Ha' & Hd' & Hb & Hapart').
  destruct Hp as [_ (Hrep' & Hw' & Hdel & _)].
  change (roots_apart (stdio_roots w) h m') in Hapart'.
  split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|]. split; [exact Hrep'|]. split; [exact Hw'|].
  exact (delegates_apart _ _ _ _ h Hdel Hapart' Hb Hd').
Qed.

(** ## main *)

(** main's frame at its entry. *)
Definition hi_main : frame := mkFrame hi_function [] [] None (Enter (TAtom "start") None).

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris instance of hi: puts's contract and [hi_wi]. *)
Local Instance hi_irisGS : irisGS_gen hlc (nanofil_lang (HB.hi_registry rep requests) HB.hi_genv) Σ :=
  nanofil_irisGS (HB.hi_registry rep requests) (hi_wi rep) HB.hi_genv.

(** The expressions of hi's language. *)
Local Notation hexpr := (language.expr (nanofil_lang (HB.hi_registry rep requests) HB.hi_genv)).

(** Owning the literal's pieces in an interpreted state, the literal is
    valid there. *)
Lemma lit_owned σ : heap_interp (hi_wi rep) σ -∗ pts lit_ps -∗ ⌜HB.hi_literal_valid (ls_mem σ)⌝.
Proof.
  iIntros "(%h & Hh & %Hf) Hl". iDestruct (pts_lookup with "Hh Hl") as %Hl.
  iPureIntro. apply lit_agree_valid. intros l v Hin. exact (proj1 Hf l v (Hl l v Hin)).
Qed.

(** puts's triple at main's call: owning the literal, the call is
    admissible, and the rest of main runs with the literal still owned
    and v1 bound to the int puts returns. *)
Lemma puts_spec e (Φ : outcome -> iProp Σ) :
  lookup (TAtom "v0") e = Some (WPtr hi_literal) ->
  pts lit_ps -∗
  ▷ (∀ n, pts lit_ps -∗
        WP (ERun (mkFrame hi_function (put (TAtom "v1") (WInt (n mod 2 ^ 32)) e) [] None
                   (Exec (TAtom "start") [] (JRet (Const 0)))) : hexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame hi_function e [] None
             (Exec (TAtom "start") [Call (site_result hi_site) (Global (TAtom "puts")) (site_args hi_site)]
                (JRet (Const 0)))) : hexpr) {{ Φ }}.
Proof.
  intros He. iIntros "Hl HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (puts_contract rep requests) [WPtr hi_literal] (pts lit_ps)
            with "Hl [HK]").
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn. rewrite He. reflexivity.
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ Hl". iDestruct (lit_owned with "Hσ Hl") as %Hv.
    iDestruct "Hσ" as (h) "[_ %Hf]". destruct Hf as (_ & _ & _ & Hrep & Hw & _).
    iPureIntro. split; [exact Hrep|]. split; [exact Hw|].
    exists hi_literal, hello_bytes. split; [reflexivity | exact (HB.hi_literal_checked _ Hv)].
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hl".
    destruct Hf as (Ha & Hd & Hr & Hwi).
    destruct (puts_return_frame _ _ _ _ _ _ _ _ _ _ _ h Hinv Ha Hd Hr Hwi) as (Ha' & Hd' & Hr' & Hwi').
    destruct (puts_returns_int _ _ _ _ _ _ _ _ _ _ _ Hinv) as (n & ->).
    iModIntro. iExists _. iSplit; [iPureIntro; cbn; reflexivity|].
    iSplitL "Hh"; [iExists h; iFrame "Hh"; iPureIntro; auto|].
    iApply ("HK" with "Hl").
Qed.

(** main, owning the literal, is safe and returns 0: it enters its
    block, copies the literal's pointer, calls puts and returns 0,
    whatever puts returned. *)
Lemma main_spec :
  pts lit_ps -∗ WP (ERun hi_main : hexpr) {{ o, ⌜o = Ret (WInt 0)⌝ }}.
Proof.
  iIntros "Hl". iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply wp_let; [reflexivity | reflexivity | reflexivity | intros m; reflexivity |]. iNext.
  iApply (puts_spec with "Hl"); [reflexivity|]. iNext. iIntros (n) "_".
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
  apply (heap_labelled_safe Σ (HB.hi_registry rep requests) (hi_wi rep) HB.hi_genv hi_main m s w lit_heap).
  - exact Hr.
  - exact Hd.
  - intros l v Hl. exact (lit_valid_agrees m Hv l v (elem_of_list_to_map_2 _ _ _ Hl)).
  - split; [exact Hrep|]. split; [exact Hw|].
    intros sp a Hin Hs (l & v & reg & Hl & [E _] & Hb). apply elem_of_list_to_map_2 in Hl.
    rewrite (lit_ps_id l v Hl) in E, Hb. rewrite (proj1 Hv) in E. injection E as <-.
    exact (Hapart sp a Hin Hs Hb).
  - intros HinvG HheapG. rewrite big_sepM_list_to_map; [|exact lit_ps_nodup].
    iIntros "Hl". iApply (main_spec with "Hl").
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
