(** The program logic of nanofil's core [[machine]] on the
    language of Language.v, whose evaluation context is the stack of
    callers: a ghost heap of pieces as Iris's state interpretation, a
    small assertion vocabulary over it, and one weakest-precondition
    rule per instruction form, each the lifted reading of its rule in
    StepRules.v.

    The ghost heap is Heap.v's: Iris's [gen_heap] from Pieces.v's
    pieces to their values, which [heap_interp] keeps in agreement with
    the memory. The vocabulary is [live] (an object's life), [icell] (an
    8-byte integer in an object), [pcell] (a pointer stored in an
    object, its address bytes and its [[aux]] capability), [obj] (a new
    object's pieces) and [live_cap] (the life of the object a
    capability names, if any).

    The logic is over Language.v's contract registry and its world of
    libc state. [heap_interp] also holds a world interpretation wi:
    what the world requires of the memory, given the program's ghost
    heap. A [[poll|safepoint]] must keep it ([SafepointStable]), and a
    rule that writes memory or the ghost heap has a pure premise that
    the write keeps it ([wp_write], the stores, [wp_alloc]). With
    [no_contracts] and [no_world] every such premise is trivial, and
    [closed_irisGS] is the Iris instance of a closed module.

    Every rule for a running frame comes from one lifting lemma,
    [wp_lift_run]. A safepoint and a stall (out of [[fuel]], a refusal
    trap, an allocation the runtime refuses, an admissible external
    call) step [ERun fr] to itself, the first changing memory only as
    [SS.safepoint_shape] allows (no region, by Runtime.v's
    [collector_live]), which keeps [heap_interp] with the same ghost
    heap: the lemma closes both by Löb induction, so a rule speaks only
    of the step its instruction takes. A call is [wp_bind] over the
    caller ([wp_call_bind]), so a function's specification is an
    ordinary Hoare triple. An external call ([wp_external]) asks for
    its contract's precondition and, after every return the contract
    allows, for the state interpretation of the call's memory and world.
    [heap_never_panics] is Language.v's [[adequacy]] with the ghost heap
    allocated, for a closed module; [heap_labelled_safe] is the
    labelled machine's, from a ghost heap the caller provides. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language ectx_language ectxi_language weakestpre lifting
  ectx_lifting adequacy.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls Ops Semantics Run
  Machine Panics StepRules Pieces Heap Identity ContractFrame ExternalMachine Language.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Pure facts about cells *)

(** A cell agrees with a memory where its object is live: its eight
    bytes lie inside the object's bounds. *)
Lemma cell_bounds m b reg o x :
  live_at m b reg -> all_agree m (cell b o x) -> 0 <= o /\ b + o + 8 <= r_end reg.
Proof.
  intros [E L] Hc. rewrite all_agree_cell in Hc.
  destruct (Hc 0 ltac:(lia)) as [_ H0]. destruct (Hc 7 ltac:(lia)) as [_ H7].
  destruct (H0 reg E L) as (? & _). destruct (H7 reg E L) as (_ & ? & _). lia.
Qed.

(** An aux piece of a live object holds what the slot holds, up to
    [aux_holds]. *)
Lemma aux_piece_holds m b reg o c :
  live_at m b reg -> agree_piece m (PAux b o) (VAux c) -> aux_holds m (b + o) c.
Proof. intros [E L] [_ H]. destruct (H reg E L) as (_ & _ & Hx). exact Hx. Qed.

(** The bytes from a to a + 8, inside the live object b, are inside an
    object. *)
Lemma in_object_live m b reg a :
  live_at m b reg -> b <= a -> a + 8 <= r_end reg -> forall x, a <= x < a + 8 -> in_object m x.
Proof. intros [E _] H1 H2 x Hx. exists b, reg. split; [exact E | lia]. Qed.

(** A pointer store at offset o of the live object b (aux, then the
    address bytes): its aux slot and its cell hold the pointer, and
    nothing else changes. Heap.v's [ptr_store_ok] at any offset. *)
Lemma pcell_store_ok m b reg o a c x :
  live_disjoint m -> live_at m b reg -> 0 <= o -> b + o + 8 <= r_end reg -> a = b + o ->
  all_agree (store_bytes (store_aux m a c) a 8 x) ((PAux b o, VAux c) :: cell b o x) /\
  frame_ok ((PAux b o, VAux c) :: cell b o x).*1 m (store_bytes (store_aux m a c) a 8 x).
Proof.
  intros Hd Hl Ho He ->. set (m1 := store_aux m (b + o) c).
  assert (Hd1 : live_disjoint m1) by (apply (live_disjoint_regions m); [reflexivity|exact Hd]).
  assert (Hl1 : live_at m1 b reg) by (apply (live_at_regions m); [reflexivity|exact Hl]).
  destruct (cell_store_ok m1 b reg o (b + o) x Hd1 Hl1 Ho He eq_refl) as [Hc Hf].
  split.
  - cbn [all_agree fst snd]. split; [|exact Hc]. cbn [agree_piece].
    unfold registered, in_live. rewrite regions_store_bytes regions_store_aux.
    destruct Hl as [E L]. split; [congruence|]. intros reg' E' _. rewrite E in E'.
    injection E' as <-. split; [lia|]. split; [lia|].
    left. rewrite aux_store_bytes aux_store_aux Z.eqb_refl. reflexivity.
  - eapply frame_ok_trans.
    + eapply frame_store_aux; [exact Hd|exact Hl|exact Ho|lia|reflexivity|].
      apply elem_of_cons. by left.
    + eapply frame_ok_mono; [|exact Hf]. intros k Hk. cbn. apply elem_of_cons. by right.
Qed.

(** ## The logic over a runtime *)

(** The memory after a free of the live heap object b: the same bytes
    and aux slots, b's region empty and freed, every other object as it
    was. Such a change is [kept]. *)
Lemma free_heap_kept m b reg rs :
  live_at m b reg -> r_kind reg = Heap ->
  replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs ->
  kept m (mkMem (m_bytes m) rs (m_aux m)).
Proof.
  intros [E L] Hk Hr. split; [|intros a _; split; reflexivity].
  intros b' reg' E'. cbn [m_regions] in E'. rewrite (object_region_replace _ _ _ _ b' Hr eq_refl) in E'.
  destruct (Z.eqb_spec b' b) as [->|Hne].
  - injection E' as <-. exists reg. split; [exact E|]. right. split; [exact L|]. rewrite Hk. reflexivity.
  - exists reg'. split; [exact E'|]. left. reflexivity.
Qed.

(** A free of the live heap object b keeps the agreement of every piece
    but b's life: other objects keep their regions, b's bytes and aux
    slots agree vacuously once it is not live, and a capability freed
    before is freed after. *)
Lemma agree_piece_free m b reg rs l v :
  live_at m b reg -> r_kind reg = Heap ->
  replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs ->
  l <> PLive b -> agree_piece m l v -> agree_piece (mkMem (m_bytes m) rs (m_aux m)) l v.
Proof.
  intros Hl Hk Hr Hn Ha. set (m' := mkMem (m_bytes m) rs (m_aux m)).
  assert (Hs : region_step m m') by exact (proj1 (free_heap_kept m b reg rs Hl Hk Hr)).
  assert (Ho : forall b', object_region b' (m_regions m') =
                          if Z.eqb b' b then Some (mkRegion b b Heap Freed) else object_region b' (m_regions m))
    by (intros b'; exact (object_region_replace _ _ _ _ b' Hr eq_refl)).
  assert (Hi : ids m m').
  { intros b' reg' E. rewrite Ho. destruct (Z.eqb b' b); [eexists; reflexivity | exists reg'; exact E]. }
  assert (Hreg : forall b', registered m b' -> registered m' b').
  { unfold registered. intros b' H. rewrite Ho. destruct (Z.eqb b' b); [discriminate | exact H]. }
  assert (Hlive : forall b' o P, in_live m b' o P -> in_live m' b' o P).
  { intros b' o P H reg' E L. rewrite Ho in E. destruct (Z.eqb_spec b' b) as [->|Hne].
    - injection E as <-. discriminate L.
    - exact (H reg' E L). }
  destruct l as [b'|b' o|b' o|k], v as [reg'|y|c| |q t]; cbn [agree_piece] in Ha |- *; try contradiction;
    try exact I.
  - destruct Ha as [E L]. split; [|exact L]. rewrite Ho. destruct (Z.eqb_spec b' b) as [->|]; [congruence|exact E].
  - exact (Hreg _ Ha).
  - destruct Ha as [Hr' Hin]. split; [exact (Hreg _ Hr')|]. exact (Hlive _ _ _ Hin).
  - destruct Ha as [Hr' Hin]. split; [exact (Hreg _ Hr')|]. apply Hlive.
    intros reg0 E L. destruct (Hin reg0 E L) as (Hlo & Hhi & Hx). split; [exact Hlo|]. split; [exact Hhi|].
    unfold aux_holds in *. cbn [m_aux m'].
    destruct Hx as [Hx | [Hf Ht]]; [left; exact Hx | right].
    split; [exact (freed_in_step m m' _ Hi Hs Hf) | exact (traps_as_freed_step m m' _ Hi Hs Ht)].
Qed.

(** Live objects stay apart after a free, which ends one. *)
Lemma live_disjoint_free m b rs :
  replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs ->
  live_disjoint m -> live_disjoint (mkMem (m_bytes m) rs (m_aux m)).
Proof.
  intros Hr Hd b1 r1 b2 r2 [E1 L1] [E2 L2]. cbn [m_regions] in E1, E2.
  rewrite (object_region_replace _ _ _ _ b1 Hr eq_refl) in E1.
  rewrite (object_region_replace _ _ _ _ b2 Hr eq_refl) in E2.
  destruct (Z.eqb b1 b); [injection E1 as <-; discriminate L1|].
  destruct (Z.eqb b2 b); [injection E2 as <-; discriminate L2|].
  exact (Hd b1 r1 b2 r2 (conj E1 L1) (conj E2 L2)).
Qed.

(** The ghost heap, the assertions and the rules over the runtime R. *)
Module Logic (R : Runtime).
Module L := Language R.
Module SS := SafepointShape R.
Module P := L.P.
Module RM := L.RM.
Import L.

(** The world interpretation wi, what the world of libc state requires
    of the memory given the program's ghost heap, survives what R does
    at a [[poll|safepoint]]. Every rule needs it, since a safepoint may
    come before any step; a class, so that a rule finds it for the wi
    it is used at. *)
Class SafepointStable {world : Type} (wi : mem -> world -> gmap piece pval -> Prop) : Prop := {
  wi_safepoint : forall s m s' m' w h, R.safepoint s m s' m' -> wi m w h -> wi m' w h
}.

(** The logic for the contracts of registry over the world type world,
    with the world interpretation wi. *)
Section logic.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi}.

(** The state interpretation of the Iris state σ: the authoritative
    ghost heap h, which [agrees] with σ's memory, the live objects
    apart, the runtime ready, and σ's world interpreted by wi in the
    memory, given h. The [[fuel]] is unconstrained. *)
Definition heap_interp (σ : lstate world) : iProp Σ :=
  ∃ h : gmap piece pval, gen_heap_interp h ∗
    ⌜agrees (ls_mem σ) h /\ live_disjoint (ls_mem σ) /\ R.ready (ls_rt σ) (ls_mem σ) /\
     wi (ls_mem σ) (ls_world σ) h⌝.

(** The Iris instance of the genv ge: [heap_interp] as the state
    interpretation, no forks to speak of, one later per step. *)
Local Instance nanofil_irisGS (ge : genv) : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  IrisG _ (fun σ _ _ _ => heap_interp σ) (fun _ => True%I) (fun _ => 0%nat)
        (fun _ _ _ _ => fupd_intro _ _).

(** ## The assertions *)

(** [live] b reg: owning the life of the object of identity b, which is
    live with the region reg ([[live]]). *)
Definition live (b : Z) (reg : region) : iProp Σ := pts [(PLive b, VLive reg)].

(** [icell] b o v: owning the 8 bytes at offset o of the object b,
    which hold the 64-bit integer v, little-endian. *)
Definition icell (b o v : Z) : iProp Σ := pts (cell b o v).

(** [ibyte] b o x: owning the byte at offset o of the object b, which
    holds x. *)
Definition ibyte (b o x : Z) : iProp Σ := pts [(PByte b o, VByte x)].

(** [pcell] b o x: owning the pointer x stored at offset o of the
    object b: the 8 bytes of its address and the [[aux]] slot holding
    its capability. *)
Definition pcell (b o : Z) (x : ptr) : iProp Σ :=
  pts ((PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)).

(** [obj] b q: owning every piece of the object of identity b just
    allocated for the request q: its life, a zero byte and an empty aux
    slot at each offset. *)
Definition obj (b : Z) (q : alloc_req) : iProp Σ := pts (obj_ps b q).

(** [live_cap] c reg: owning the life of the object c names, with the
    region reg, if c names one; nothing if c is no capability. A
    pointer load needs it to know the loaded capability is the one
    stored ([aux_holds_live]). *)
Definition live_cap (c : cap) (reg : region) : iProp Σ :=
  match c with
  | CNone => True
  | Obj b => live b reg
  | _ => False
  end.

(** What owned pieces tell about the memory of σ: [owned_facts]. *)
Lemma pts_facts σ ps : heap_interp σ -∗ pts ps -∗ ⌜owned_facts ps (ls_mem σ)⌝.
Proof.
  iIntros "Hσ Hps". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr & _).
  iDestruct (pts_lookup with "Hh Hps") as %Hl. iPureIntro.
  split; [|split; [exact Hd | exact (R.address_space _ _ Hr)]].
  apply all_agree_intro. intros l v Hin. apply Ha. apply Hl. exact Hin.
Qed.

(** The object a [live_cap] names is live in the memory of σ, or the
    capability is none: what [aux_holds_live] needs. *)
Lemma live_cap_facts σ c reg : heap_interp σ -∗ live_cap c reg -∗
  ⌜c = CNone \/ exists b reg, c = Obj b /\ live_at (ls_mem σ) b reg⌝.
Proof.
  destruct c; cbn [live_cap]; iIntros "Hσ H"; try done; [iPureIntro; by left|].
  iDestruct (pts_facts with "Hσ H") as %(Hf & _). iPureIntro. right.
  cbn [all_agree agree_piece fst snd] in Hf. eexists _, _. split; [reflexivity | exact (proj1 Hf)].
Qed.

(** What R does at a safepoint keeps the state interpretation, with
    the same ghost heap and world. *)
Lemma heap_interp_safepoint m s fuel w m' s' :
  R.safepoint s m s' m' ->
  heap_interp (mkLstate m s fuel w) -∗ heap_interp (mkLstate m' s' fuel w).
Proof.
  intros Hsp. iIntros "Hσ". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr & Hw).
  iExists h. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world] in *.
  destruct (SS.safepoint_shape _ _ _ _ Hsp) as (Hreg & Hb & Haux).
  split; [|split; [|split]].
  - intros l v Hl. exact (agree_piece_safepoint _ _ _ _ Hreg Hb Haux (Ha l v Hl)).
  - exact (SS.live_disjoint_safepoint _ _ _ _ Hsp Hd).
  - exact (R.safepoint_ready _ _ _ _ Hsp Hr).
  - exact (wi_safepoint _ _ _ _ _ _ Hsp Hw).
Qed.

(** Owned pieces written over the ghost heap with the values it holds
    leave it as it is. *)
Lemma overwrite_id ps (h : gmap piece pval) :
  (forall l v, (l, v) ∈ ps -> h !! l = Some v) -> overwrite ps h = h.
Proof.
  induction ps as [|[l v] ps IH]; intros Hl; [reflexivity|]. cbn [overwrite fst snd].
  rewrite IH; [|intros l' v' Hin; apply Hl; apply elem_of_cons; by right].
  apply insert_id. apply Hl. apply elem_of_cons. by left.
Qed.

Section wp.
Context (ge : genv).
Implicit Types Φ : outcome -> iProp Σ.

(** The expressions of the language of ge. *)
Local Notation lexpr := (language.expr (nanofil_lang registry ge)).

(** The steps of [ERun fr] in σ that move on, to e2 and σ2: a step to
    the next configuration, an allocation R grants, a return, or an
    external call's return ([returned_expr]: the frame resumed with the
    call's memory, runtime state and world, or [EBad]); the cases of
    [head_step_run_inv] that are neither a stall nor a safepoint. *)
Definition moves (fr : frame) (σ : lstate world) (e2 : expr) (σ2 : lstate world) : Prop :=
  let c0 := mkConfig fr [] (ls_mem σ) (ls_fuel σ) in
  (exists c', Semantics.step ge c0 = Next c' /\ e2 = conf_expr c' /\
     σ2 = conf_state c' (ls_rt σ) (ls_world σ)) \/
  (exists q k base s', Semantics.step ge c0 = Fresh q k /\ 0 <= req_extent q /\
     R.alloc (ls_rt σ) q = Some (base, s') /\ e2 = conf_expr (k base) /\
     σ2 = conf_state (k base) s' (ls_world σ)) \/
  (exists o m', Semantics.step ge c0 = Done o /\ returning o /\
     invalidate_locals (fr_locals fr) (ls_mem σ) = Some m' /\
     e2 = EEnd o /\ σ2 = mkLstate m' (ls_rt σ) (ls_fuel σ) (ls_world σ)) \/
  (exists site spec xs trace values s' m' w', external_site ge c0 site /\
     registry (site_name site) = Some spec /\
     map_option (arg_x ge (fr_env fr)) (site_args site) = Some xs /\
     M.E.invoke spec (site_result site) (site_args site) xs (ls_rt σ) (ls_mem σ) (ls_world σ)
       trace (CallReturn values) s' m' w' /\
     e2 = returned_expr fr spec site values /\ σ2 = mkLstate m' s' (ls_fuel σ) w').

(** A step that [moves] where the frame alone is not stuck is a core
    one: an external call is stuck to the core [step]. *)
Lemma moves_core fr σ e2 σ2 :
  moves fr σ e2 σ2 ->
  (forall why, Semantics.step ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) <> Stuck why) ->
  let c0 := mkConfig fr [] (ls_mem σ) (ls_fuel σ) in
  (exists c', Semantics.step ge c0 = Next c' /\ e2 = conf_expr c' /\
     σ2 = conf_state c' (ls_rt σ) (ls_world σ)) \/
  (exists q k base s', Semantics.step ge c0 = Fresh q k /\ 0 <= req_extent q /\
     R.alloc (ls_rt σ) q = Some (base, s') /\ e2 = conf_expr (k base) /\
     σ2 = conf_state (k base) s' (ls_world σ)) \/
  (exists o m', Semantics.step ge c0 = Done o /\ returning o /\
     invalidate_locals (fr_locals fr) (ls_mem σ) = Some m' /\
     e2 = EEnd o /\ σ2 = mkLstate m' (ls_rt σ) (ls_fuel σ) (ls_world σ)).
Proof.
  intros [H | [H | [H | (site & _ & _ & _ & _ & _ & _ & _ & Hs & _)]]] Hns; auto.
  exfalso. exact (Hns _ (external_site_stuck _ _ _ Hs)).
Qed.

(** The lifting lemma every rule for a running frame comes from. [ERun
    fr] is safe, given Q, if Q and the state interpretation show fr
    [proceeds] (it does not [fails], or its external call is
    admissible), and if, after any step that [moves], they give the
    state interpretation and the weakest precondition of what follows.
    A stall (an admissible call's included) leaves the expression and
    the state as they are; a safepoint leaves the expression and the
    state interpretation: these cases are closed by Löb induction,
    keeping Q. *)
Lemma wp_lift_run (Q : iProp Σ) fr Φ :
  (forall σ, heap_interp σ -∗ Q -∗ ⌜proceeds registry ge fr σ⌝) ->
  (forall σ, heap_interp σ -∗ Q -∗
     ▷ ∀ e2 σ2, ⌜moves fr σ e2 σ2⌝ ==∗ heap_interp σ2 ∗ WP (e2 : lexpr) {{ Φ }}) ->
  Q -∗ WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros Hnf Hst. iLöb as "IH". iIntros "HQ".
  iApply wp_lift_base_step; [done|].
  iIntros (σ ns κ κs nt) "Hσ".
  iDestruct (Hnf with "Hσ HQ") as %Hnf'.
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplitR; [iPureIntro; by apply proceeds_reducible|].
  iAssert ((▷ ∀ e2 σ2, ⌜moves fr σ e2 σ2⌝ ==∗ heap_interp σ2 ∗ WP (e2 : lexpr) {{ Φ }})
           ∧ (heap_interp σ ∗ Q))%I with "[Hσ HQ]" as "H".
  { iSplit; [iApply (Hst with "Hσ HQ") | iFrame]. }
  iNext. iIntros (e2 σ2 efs Hstep) "_". iMod "Hclose" as "_".
  destruct (head_step_run_inv _ _ _ _ _ _ _ _ Hstep) as (_ & -> & Hc).
  destruct Hc as [Hn | [Ha | [(q & k & _ & _ & _ & -> & ->) | [Hr | [(o & _ & _ & _ & -> & ->) |
    [(s' & m' & _ & _ & Hsp & -> & ->) | [Hx | (_ & -> & ->)]]]]]]].
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by left|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by (right; left)|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. iFrame "Hσ". iSplitL; [iApply ("IH" with "HQ")|done].
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by (right; right; left)|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. iFrame "Hσ". iSplitL; [iApply ("IH" with "HQ")|done].
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. destruct σ as [m s fuel w].
    iSplitL "Hσ"; [iApply (heap_interp_safepoint with "Hσ"); exact Hsp|].
    iSplitL; [iApply ("IH" with "HQ")|done].
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by (right; right; right)|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. iFrame "Hσ". iSplitL; [iApply ("IH" with "HQ")|done].
Qed.

(** A step to the next configuration, with the callers cs' below its
    frame, that writes memory: owning the pieces ps, where every memory
    m those pieces agree with steps to [upd] m, keeping its regions,
    [kept], agreeing with the new values ps' (the same keys) and
    changing nothing outside them, and where the write keeps the world
    interpretation, for a ghost heap that holds ps, with ps' written
    over it. The new pieces are handed on. *)
Lemma wp_write ps ps' fr fr' cs' (upd : mem -> mem) Φ :
  ps'.*1 = ps.*1 ->
  (forall m fuel, owned_facts ps m ->
     Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' (upd m) fuel) /\
     m_regions (upd m) = m_regions m /\ kept m (upd m) /\
     all_agree (upd m) ps' /\ frame_ok ps'.*1 m (upd m)) ->
  (forall m w h, (forall l v, (l, v) ∈ ps -> h !! l = Some v) -> wi m w h ->
     wi (upd m) w (overwrite ps' h)) ->
  pts ps -∗ ▷ (pts ps' -∗ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }}) -∗
  WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros Hk Hs Hwi. iIntros "Hps HK". iCombine "Hps HK" as "H".
  iApply (wp_lift_run with "H").
  - iIntros (σ) "Hσ [Hps _]". iDestruct (pts_facts with "Hσ Hps") as %Hf. iPureIntro.
    destruct (Hs _ (ls_fuel σ) Hf) as (E & _). left. unfold fails. rewrite E. auto.
  - iIntros ([m s fuel w]) "Hσ [Hps HK]". iDestruct (pts_facts with "Hσ Hps") as %Hf.
    cbn [ls_mem ls_rt ls_fuel ls_world] in *.
    destruct (Hs m fuel Hf) as (E & Hreg & Hkept & Hag & Hfr). iNext. iIntros (e2 σ2 Hm).
    destruct (moves_core _ _ _ _ Hm ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite E; discriminate))
      as [(c' & E' & -> & ->) | [(q & k & b & s' & E' & _) | (o & m' & E' & _)]];
      cbn [ls_mem ls_fuel ls_rt] in E'; rewrite E in E'; try discriminate E'.
    injection E' as <-. cbn [conf_expr conf_state c_frame c_callers c_mem c_fuel].
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr & Hw).
    cbn [ls_mem ls_rt ls_world] in Ha, Hd, Hr, Hw.
    iDestruct (pts_lookup with "Hh Hps") as %Hl.
    iMod (pts_update with "Hh Hps") as "[Hh Hps]"; [exact Hk|].
    iModIntro. iSplitL "Hh".
    + iExists (overwrite ps' h). iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world].
      split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hn Hh]].
        -- exact (all_agree_elem _ _ _ _ Hag Hin).
        -- exact (Hfr l v Hn (Ha l v Hh)).
      * exact (live_disjoint_regions _ _ Hreg Hd).
      * exact (R.ready_kept _ _ _ Hr Hkept).
      * exact (Hwi m w h Hl Hw).
    + iApply ("HK" with "Hps").
Qed.

(** A step to the next configuration, with the callers cs' below its
    frame, that reads the pieces ps and changes no memory: they are
    handed back. *)
Lemma wp_read ps fr fr' cs' Φ :
  (forall m fuel, owned_facts ps m ->
     Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' m fuel)) ->
  pts ps -∗ ▷ (pts ps -∗ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }}) -∗
  WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros Hs. apply (wp_write ps ps fr fr' cs' (fun m => m)); [reflexivity| |].
  - intros m fuel Hf. split; [exact (Hs m fuel Hf)|]. split; [reflexivity|]. split; [apply kept_refl|].
    split; [exact (proj1 Hf)|]. intros l v _ H. exact H.
  - intros m w h Hl Hw. rewrite overwrite_id; [exact Hw | exact Hl].
Qed.

(** A step to the next configuration, with the callers cs' below its
    frame, that needs no resource and changes no memory. *)
Lemma wp_pure_next fr fr' cs' Φ :
  (forall m fuel, Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' m fuel)) ->
  ▷ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }} -∗ WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros Hs. iIntros "H". iApply (wp_read [] fr fr' cs' with "[] [H]"); [|by rewrite /pts|].
  - intros m fuel _. apply Hs.
  - iNext. iIntros "_". iExact "H".
Qed.

(** ## The rules *)

(** A [let] of a general op o whose arguments read as xs and whose
    [op_res] is the word w in any memory, leaving it: d is bound to w. *)
Lemma wp_let f e ls l d k o args rest j classes xs w Φ :
  general_op o = true -> op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal w) m)) ->
  ▷ WP (ERun (mkFrame f (put d w e) ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hg Hc Hx Ho. apply (wp_pure_next _ _ []).
  intros m fuel. exact (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hc Hx (Ho m)).
Qed.

(** A [[check]] of the pointer p, through the capability of the live
    object b with the region reg, whose checked bytes lie in its bounds
    and are aligned: d is bound to p, proven. *)
Lemma wp_check f e ls l d lo hi r al args rest j classes p b reg Φ :
  op_arg_classes (Check lo hi r al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg -> raw_address (ptr_addr p) lo mod al = 0 ->
  live b reg -∗
  ▷ (live b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi r al) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp H1 H2 H3. apply (wp_read _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_check. rewrite Hp. exact (access_obj _ _ _ _ _ _ _ E H1 H2 H3).
Qed.

(** A [[check]] for reading of the pointer p, through a read-write or
    read-only capability for the live object b with the region reg,
    whose checked bytes lie in its bounds and are aligned: d is bound
    to p, proven. *)
Lemma wp_check_read f e ls l d lo hi al args rest j classes p b reg Φ :
  op_arg_classes (Check lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg -> raw_address (ptr_addr p) lo mod al = 0 ->
  live b reg -∗
  ▷ (live b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi Read al) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp H1 H2 H3. apply (wp_read _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_check. exact (access_read _ _ _ _ _ _ _ Hp E H1 H2 H3).
Qed.

(** A [[half_check]] of the pointer p, against the proof p1 of the same
    capability, at the live object b with the region reg, ending at or
    below 2^63, whose checked bytes lie in its bounds and are aligned:
    d is bound to p, proven. *)
Lemma wp_half_check f e ls l d bd lo hi r al args rest j classes p1 p b reg Φ :
  op_arg_classes (HalfCheck bd lo hi r al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = Obj b -> ptr_cap p = Obj b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  live b reg -∗
  ▷ (live b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (HalfCheck bd lo hi r al) args :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hc Hx Hp1 Hp H1 H2 H3 H4 H5. apply (wp_read _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E Lv] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]);
    [reflexivity | exact Hc | exact Hx |].
  exact (op_half_check _ _ _ _ _ _ _ _ _ _ Hp1 Hp E Lv H1 H2 H3 H4 H5).
Qed.

(** A read half check of the pointer p against the proof p1 of the same
    capability, an object's or a read-only object's, at the live object
    b, ending at or below 2^63 and holding the aligned bytes: d is bound
    to p. Hello's string scans half check read-only literals. *)
Lemma wp_half_check_read f e ls l d bd lo hi al args rest j classes p1 p b reg Φ :
  op_arg_classes (HalfCheck bd lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  live b reg -∗
  ▷ (live b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (HalfCheck bd lo hi Read al) args :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hc Hx Hp1 Hp H1 H2 H3 H4 H5. apply (wp_read _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E Lv] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]);
    [reflexivity | exact Hc | exact Hx |].
  exact (op_half_check_read _ _ _ _ _ _ _ _ _ Hp1 Hp E Lv H1 H2 H3 H4 H5).
Qed.

(** A renew of the pointer p, an object's, against the proof p1 of the
    same capability, inside the live object b and aligned: d is bound to
    p. The renews Hello reaches reuse the check of a stack slot. *)
Lemma wp_renew f e ls l d lo hi r al args rest j classes p1 p b reg Φ :
  op_arg_classes (Renew lo hi r al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b -> b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg -> raw_address (ptr_addr p) lo mod al = 0 ->
  live b reg -∗
  ▷ (live b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Renew lo hi r al) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp1 Hp H1 H2 H3. apply (wp_read _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]);
    [reflexivity | exact Hc | exact Hx |].
  apply op_renew; [exact Hp1|]. rewrite Hp. exact (access_obj _ _ _ _ _ _ _ E H1 H2 H3).
Qed.

(** A raw load of a long at offset off from the proven pointer p, which
    addresses offset o of the live object b, where the cell holds v: d
    is bound to v modulo 2^64. *)
Lemma wp_raw_load f e ls l d k off args rest j classes p b reg o v Φ :
  op_arg_classes (RawLoad LdL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o ->
  live b reg -∗ icell b o v -∗
  ▷ (live b reg -∗ icell b o v -∗
     WP (ERun (mkFrame f (put d (WInt (v mod 2 ^ 64)) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha. iIntros "Hl Hc HK".
  iApply (wp_read ([(PLive b, VLive reg)] ++ cell b o v) _ _ [] with "[Hl Hc] [HK]").
  - intros m fuel (Hf & _). apply all_agree_app in Hf as [[Hlv _] Hcl]. cbn [agree_piece fst snd] in Hlv.
    destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load m k p off).
    + rewrite Ha (cell_load m b reg o v (b + o) Hlv Hcl eq_refl). reflexivity.
    + rewrite Hp Ha. apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - rewrite pts_app. iFrame.
  - iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A raw load of the one-byte narrow type n at offset off from the
    proven pointer p, through a read-write or read-only capability for
    the live object b, at offset o, where the byte is x: d is bound to
    x extended to the class k, y. *)
Lemma wp_raw_load_byte f e ls l d k n off args rest j classes p b reg o x y Φ :
  op_arg_classes (RawLoad (LdNarrow n) off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  fst (narrow_type n) = 1 -> extended n k x = Some y ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
  live b reg -∗ ibyte b o x -∗
  ▷ (live b reg -∗ ibyte b o x -∗
     WP (ERun (mkFrame f (put d y e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad (LdNarrow n) off) args :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hc Hx Hn Hy Hp Ha. iIntros "Hl Hb HK".
  iApply (wp_read ([(PLive b, VLive reg)] ++ [(PByte b o, VByte x)]) _ _ [] with "[Hl Hb] [HK]").
  - intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd app] in Hf.
    destruct Hf as [[E Lv] [[_ Hin] _]]. destruct (Hin reg E Lv) as (Ho & He & Hv).
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load_byte m k n p off Hn).
    + rewrite Ha Hv Hy. reflexivity.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact E | lia | lia | apply Z.mod_1_r].
  - rewrite pts_app. iFrame.
  - iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hb]". iApply ("HK" with "Hl Hb").
Qed.

(** A step to the next configuration, with the callers cs' below its
    frame, that changes no memory, where Q, with the state
    interpretation, shows the memory has the property F, and every
    memory with F steps there: Q is handed back. *)
Lemma wp_read_with (Q : iProp Σ) (F : mem -> Prop) fr fr' cs' Φ :
  (forall σ, heap_interp σ -∗ Q -∗ ⌜F (ls_mem σ)⌝) ->
  (forall m fuel, F m -> Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' m fuel)) ->
  Q -∗ ▷ (Q -∗ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }}) -∗ WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros HF Hs. iIntros "HQ HK". iCombine "HQ HK" as "H".
  iApply (wp_lift_run with "H").
  - iIntros (σ) "Hσ [HQ _]". iDestruct (HF with "Hσ HQ") as %Hf. iPureIntro.
    left. unfold fails. rewrite (Hs _ _ Hf). auto.
  - iIntros ([m s fuel w]) "Hσ [HQ HK]". iDestruct (HF with "Hσ HQ") as %Hf. cbn [ls_mem] in Hf.
    iNext. iIntros (e2 σ2 Hm).
    destruct (moves_core _ _ _ _ Hm ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite (Hs _ _ Hf); discriminate))
      as [(c' & E' & -> & ->) | [(q & k & b & s' & E' & _) | (o & m' & E' & _)]];
      cbn [ls_mem ls_fuel ls_rt] in E'; rewrite (Hs _ _ Hf) in E'; try discriminate E'.
    injection E' as <-. cbn [conf_expr conf_state c_frame c_callers c_mem c_fuel].
    iModIntro. iFrame "Hσ". iApply ("HK" with "HQ").
Qed.

(** A raw pointer load by the plain protocol at offset off from the
    proven pointer p, which addresses the 8-aligned offset o of the live
    object b, where the pointer x is stored: d is bound to x, given the
    life of the object x's capability names, if any ([live_cap]), and
    x's address in range. *)
Lemma wp_raw_load_pointer f e ls l d off args rest j classes p b reg o x reg' Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 ->
  live b reg -∗ pcell b o x -∗ live_cap (ptr_cap x) reg' -∗
  ▷ (live b reg -∗ pcell b o x -∗ live_cap (ptr_cap x) reg' -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
       : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hrange. iIntros "Hl Hc Hcap HK".
  iApply (wp_read_with (live b reg ∗ pcell b o x ∗ live_cap (ptr_cap x) reg')
            (fun m => live_at m b reg /\ agree_piece m (PAux b o) (VAux (ptr_cap x)) /\
                      all_agree m (cell b o (ptr_addr x)) /\
                      (ptr_cap x = CNone \/ exists b' reg', ptr_cap x = Obj b' /\ live_at m b' reg'))
            _ _ [] with "[$Hl $Hc $Hcap] [HK]").
  - iIntros (σ) "Hσ (Hl & Hc & Hcap)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (pts_facts with "Hσ Hc") as %([Hax Hcl] & _).
    iDestruct (live_cap_facts with "Hσ Hcap") as %Hcf. iPureIntro. auto.
  - intros m fuel (Hlv & Hax & Hcl & Hcf). destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    apply op_raw_load_pointer.
    + rewrite Hp Ha. apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | exact Hal].
    + rewrite pointer_load_plain Ha (cell_load m b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl).
      rewrite Z.mod_small; [|exact Hrange]. unfold aux_at.
      rewrite (aux_holds_live _ _ _ (aux_piece_holds _ _ _ _ _ Hlv Hax) Hcf).
      destruct x; reflexivity.
  - iNext. iIntros "(Hl & Hc & Hcap)". iApply ("HK" with "Hl Hc Hcap").
Qed.

(** A raw store of the long v', which v reads as, through the proven
    pointer p, which a reads as and which addresses offset o of the live
    object b at offset off, where the store keeps the world
    interpretation: the cell there now holds v'. *)
Lemma wp_raw_store f e ls l off v a rest j p b reg o w w' Φ :
  value_x ge e L v = Some (WInt w') -> value_x ge e A a = Some (WPtr p) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o ->
  (forall m wd h, (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ cell b o w -> h !! l = Some v) ->
     wi m wd h -> wi (store_bytes m (b + o) 8 w') wd (overwrite ([(PLive b, VLive reg)] ++ cell b o w') h)) ->
  live b reg -∗ icell b o w -∗
  ▷ (live b reg -∗ icell b o w' -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Wl off v a :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hv Ha Hp Hoff Hwi. iIntros "Hl Hc HK".
  iApply (wp_write ([(PLive b, VLive reg)] ++ cell b o w) ([(PLive b, VLive reg)] ++ cell b o w')
            _ _ [] (fun m => store_bytes m (b + o) 8 w') with "[Hl Hc] [HK]");
    [reflexivity | | exact Hwi | rewrite pts_app; iFrame |].
  - intros m fuel (Hf & Hd & _). apply all_agree_app in Hf as [[Hlv _] Hcl].
    cbn [agree_piece fst snd] in Hlv. destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    destruct (cell_store_ok m b reg o (b + o) w' Hd Hlv Ho He eq_refl) as [Hcs Hfr].
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_raw_store with (vk := L) (x := WInt w') (p := p); [reflexivity | exact Hv | exact Ha |].
      rewrite Hoff. apply store_res_long. rewrite Hp.
      apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
    + apply store_bytes_kept. exact (in_object_live _ _ _ (b + o) Hlv ltac:(lia) ltac:(lia)).
    + apply all_agree_app. split; [|exact Hcs]. cbn [all_agree agree_piece fst snd].
      split; [apply (live_at_regions m); [reflexivity|exact Hlv] | exact I].
    + eapply frame_ok_mono; [|exact Hfr]. intros k Hin. rewrite fmap_app. apply elem_of_app. by right.
  - iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A raw pointer store by the plain protocol of the pointer xp, which
    v reads as, through the proven pointer p, which a reads as and
    which addresses the 8-aligned offset o of the live object b at
    offset off, where the store keeps the world interpretation: the
    pointer cell there now holds xp. *)
Lemma wp_raw_store_pointer f e ls l off v a rest j xp p b reg o x Φ :
  value_x ge e P v = Some (WPtr xp) -> value_x ge e A a = Some (WPtr p) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  (forall m wd h,
     (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
        h !! l = Some v) ->
     wi m wd h ->
     wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
       (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)) ->
  live b reg -∗ pcell b o x -∗
  ▷ (live b reg -∗ pcell b o xp -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
                :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hv Ha Hp Hoff Hal Hwi. iIntros "Hl Hc HK".
  iApply (wp_write ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x))
            ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp))
            _ _ [] (fun m => store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp))
            with "[Hl Hc] [HK]");
    [reflexivity | | exact Hwi | rewrite pts_app; iFrame |].
  - intros m fuel (Hf & Hd & _). apply all_agree_app in Hf as [[Hlv _] [_ Hcl]].
    cbn [agree_piece fst snd] in Hlv. destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    destruct (pcell_store_ok m b reg o (b + o) (ptr_cap xp) (ptr_addr xp) Hd Hlv Ho He eq_refl)
      as [Hcs Hfr].
    assert (Hin := in_object_live _ _ _ (b + o) Hlv ltac:(lia) ltac:(lia)).
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_raw_store_pointer with (xp := xp) (p := p); [exact Hv | exact Ha | |].
      * rewrite Hoff Hp. apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | exact Hal].
      * rewrite Hoff. apply pointer_store_plain.
    + exact (pointer_store_effects_kept _ _ _ _ _ Hin (pointer_store_plain m (b + o) xp)).
    + apply all_agree_app. split; [|exact Hcs]. cbn [all_agree agree_piece fst snd].
      split; [apply (live_at_regions m); [reflexivity|exact Hlv] | exact I].
    + eapply frame_ok_mono; [|exact Hfr]. intros k Hin'. rewrite fmap_app. apply elem_of_app. by right.
  - iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A call of `free` on null, which v reads as: nothing happens. *)
Lemma wp_free_null f e ls l v rest j Φ :
  frees_heap (ge_free ge) -> find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr null) ->
  ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros [Hnull _] Hfn Hdata Hx. apply (wp_pure_next _ _ []). intros m fuel.
  exact (rule_free _ _ _ _ _ _ _ _ _ _ _ _ _ Hfn Hdata Hx (Hnull m)).
Qed.

(** A call of `free` on the base pointer of the live heap object b,
    which v reads as, where the genv's free [frees_heap] (R's does,
    by [R.free_succeeds]), and where the
    free keeps the world interpretation: b's life is given up, its
    token ending as [VFreed] in the ghost heap. Its bytes and aux
    slots, if still owned, agree vacuously from then on. *)
Lemma wp_free f e ls l v rest j b reg Φ :
  frees_heap (ge_free ge) -> find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr (mkPtr b (Obj b))) -> r_kind reg = Heap -> b <> 0 ->
  (forall m wd h rs, h !! PLive b = Some (VLive reg) ->
     replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs -> wi m wd h ->
     wi (mkMem (m_bytes m) rs (m_aux m)) wd (overwrite [(PLive b, VFreed)] h)) ->
  live b reg -∗ ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros [_ Hfh] Hfn Hdata Hx Hk Hb Hwi. iIntros "Hl HK". iCombine "Hl HK" as "H".
  iApply (wp_lift_run with "H").
  - iIntros (σ) "Hσ [Hl _]". iDestruct (pts_facts with "Hσ Hl") as %(Hf & _). iPureIntro.
    cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [Hlv _].
    destruct (Hfh _ _ _ Hlv Hk Hb) as (rs & _ & Hfree). left. unfold fails.
    rewrite (rule_free _ _ _ _ _ _ _ _ [] _ (ls_fuel σ) _ _ Hfn Hdata Hx Hfree). auto.
  - iIntros ([m s fuel w]) "Hσ [Hl HK]". iDestruct (pts_facts with "Hσ Hl") as %(Hf & _).
    cbn [ls_mem ls_rt ls_fuel ls_world all_agree agree_piece fst snd] in *. destruct Hf as [Hlv _].
    destruct (Hfh _ _ _ Hlv Hk Hb) as (rs & Hrs & Hfree).
    pose proof (rule_free ge f e ls l v rest j [] m fuel _ _ Hfn Hdata Hx Hfree) as E.
    iNext. iIntros (e2 σ2 Hm).
    destruct (moves_core _ _ _ _ Hm ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite E; discriminate))
      as [(c' & E' & -> & ->) | [(q & k & b' & s' & E' & _) | (o & m' & E' & _)]];
      cbn [ls_mem ls_fuel ls_rt] in E'; rewrite E in E'; try discriminate E'.
    injection E' as <-. cbn [conf_expr conf_state stack_expr c_frame c_callers c_mem c_fuel].
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr & Hw).
    cbn [ls_mem ls_rt ls_world] in Ha, Hd, Hr, Hw.
    iDestruct (pts_lookup with "Hh Hl") as %Hlk.
    iMod (pts_update _ _ [(PLive b, VFreed)] with "Hh Hl") as "[Hh _]"; [reflexivity|].
    iModIntro. iSplitL "Hh"; [|iExact "HK"].
    iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
    + intros l' v' Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hn Hh]].
      * apply list_elem_of_singleton in Hin. injection Hin as -> ->. cbn [agree_piece]. unfold registered.
        cbn [m_regions]. rewrite (object_region_replace _ _ _ _ b Hrs eq_refl) Z.eqb_refl. discriminate.
      * apply (agree_piece_free m b reg rs); [exact Hlv | exact Hk | exact Hrs | | exact (Ha l' v' Hh)].
        intros ->. apply Hn. cbn. left.
    + exact (live_disjoint_free _ _ _ Hrs Hd).
    + exact (R.ready_kept _ _ _ Hr (free_heap_kept _ _ _ _ Hlv Hk Hrs)).
    + apply (Hwi m w h rs); [apply Hlk; left | exact Hrs | exact Hw].
Qed.

(** A raw byte store of the int y, which v reads as, through the proven
    pointer p, which a reads as and which addresses offset o of the live
    object b at offset off, where the store keeps the world
    interpretation: the byte there now holds y's low byte. *)
Lemma wp_raw_store_byte f e ls l off v a rest j p b reg o x y Φ :
  value_x ge e W v = Some (WInt y) -> value_x ge e A a = Some (WPtr p) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o ->
  (forall m wd h, (forall l v, (l, v) ∈ [(PLive b, VLive reg); (PByte b o, VByte x)] -> h !! l = Some v) ->
     wi m wd h ->
     wi (store_bytes m (b + o) 1 y) wd (overwrite [(PLive b, VLive reg); (PByte b o, VByte (y mod 256))] h)) ->
  live b reg -∗ ibyte b o x -∗
  ▷ (live b reg -∗ ibyte b o (y mod 256) -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Wb off v a :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hv Ha Hp Hoff Hwi. iIntros "Hl Hc HK".
  iApply (wp_write [(PLive b, VLive reg); (PByte b o, VByte x)] [(PLive b, VLive reg); (PByte b o, VByte (y mod 256))]
            _ _ [] (fun m => store_bytes m (b + o) 1 y) with "[Hl Hc] [HK]");
    [reflexivity | | exact Hwi | rewrite /live /ibyte /pts !big_sepL_cons; iDestruct "Hl" as "[$ _]"; iFrame |].
  - intros m fuel (Hf & Hd & _). cbn [all_agree agree_piece fst snd] in Hf.
    destruct Hf as [Hlv [[Hreg Hin] _]]. destruct (Hin reg (proj1 Hlv) (proj2 Hlv)) as (Ho & He & _).
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_raw_store with (vk := W) (x := WInt y) (p := p); [reflexivity | exact Hv | exact Ha |].
      rewrite Hoff. cbn - [access_res store_bytes]. rewrite Hp.
      rewrite (access_obj _ _ reg); [reflexivity | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
    + apply store_bytes_kept. intros a' Ha'. exists b, reg. split; [exact (proj1 Hlv)|lia].
    + cbn [all_agree agree_piece fst snd]. split; [exact Hlv|]. split; [|exact I].
      split; [exact Hreg|]. intros reg' E L. rewrite regions_store_bytes in E. destruct Hlv as [E' _].
      rewrite E in E'. injection E' as <-. split; [exact Ho|]. split; [exact He|]. cbn.
      rewrite Z.leb_refl. replace (b + o <? b + o + 1) with true by (symmetry; apply Z.ltb_lt; lia).
      unfold byte_of. rewrite Z.sub_diag Z.mul_0_r Z.pow_0_r Z.div_1_r. reflexivity.
    + apply (frame_within _ _ _ b reg); [reflexivity | exact Hd | exact Hlv | |].
      * intros a' H. cbn. destruct ((b + o <=? a') && (a' <? b + o + 1)) eqn:Hr; [|reflexivity].
        exfalso. apply andb_true_iff in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
        apply H; [lia|]. replace (a' - b) with o by lia. cbn. right. left.
      * intros a' _. reflexivity.
  - iNext. iIntros "H". rewrite /live /ibyte /pts !big_sepL_cons. iDestruct "H" as "(Hl & Hc & _)".
    iApply ("HK" with "[Hl] [Hc]"); iFrame; done.
Qed.

(** A heap allocation of size bytes, size read as the only argument,
    from 0 to Fil-C's limit: for every base the runtime may grant, d is
    bound to the new object's own pointer and its pieces are owned
    ([obj]); the base is positive, aligned and the object ends within
    the address space. The allocation of any [fresh] base, with the new
    object's pieces added to the ghost heap, must keep the world
    interpretation. A refusal stalls. *)
Lemma wp_alloc f e ls l d k al args rest j size Φ :
  map2_option (value_x ge e) [L] args = Some [WInt size] -> 0 <= size -> size <= max_allocation_size ->
  (forall m wd h base, fresh m (heap_req al size) base -> wi m wd h ->
     wi (allocated m (heap_req al size) base) wd (overwrite (obj_ps base (heap_req al size)) h)) ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align (heap_req al size) = 0 /\
              base + req_extent (heap_req al size) <= 2 ^ 48⌝ -∗ obj base (heap_req al size) -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec l rest j)) : lexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hx Hs0 Hs Hwi. set (q := heap_req al size).
  assert (Hex : 0 <= req_extent q).
  { cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
  assert (Hal : 0 < req_align q) by (cbn; lia).
  pose proof (fun m fuel => rule_alloc ge f e ls l d k al args rest j [] m fuel size Hx Hs) as Hst.
  iIntros "HK". iApply (wp_lift_run with "HK").
  - iIntros (σ) "_ _". iPureIntro. left. unfold fails. rewrite Hst. fold q. lia.
  - iIntros ([m s fuel w]) "Hσ HK". iNext. iIntros (e2 σ2 Hm).
    destruct (moves_core _ _ _ _ Hm ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite Hst; discriminate))
      as [(c' & E' & _) | [(q' & kk & base & s' & E' & _ & Ha & -> & ->) | (o & m' & E' & _)]];
      cbn [ls_mem ls_fuel ls_rt] in E'; rewrite Hst in E'; try discriminate E'.
    injection E' as <- <-. cbn [conf_expr conf_state stack_expr c_frame c_callers c_mem c_fuel].
    fold q in Ha |- *.
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Hag & Hd & Hr & Hw).
    cbn [ls_mem ls_rt ls_world] in Hag, Hd, Hr, Hw.
    destruct (R.fresh_allocation _ _ _ _ _ Hr Hal Hex Ha) as [Hf Hr'].
    pose proof Hf as (Hpos & Hmod & _ & Hn & _).
    iMod (pts_alloc h (obj_ps base q) with "Hh") as "[Hh Hps]".
    { apply obj_ps_nodup. }
    { intros l' v Hin. destruct (h !! l') as [v'|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (obj_ps_mem _ _ _ _ Hin) (Hag l' v' E)) as Hreg.
      rewrite (obj_ps_id _ _ _ _ Hin) in Hreg. exact (Hreg Hn). }
    iModIntro. iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l' v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]].
        -- exact (obj_ps_agree _ _ _ _ _ Hf Hex Hin).
        -- exact (agree_piece_allocated _ _ _ _ _ Hn (Hag l' v Hh)).
      * exact (live_disjoint_allocated _ _ _ Hd Hf Hex).
      * exact Hr'.
      * exact (Hwi m w h base Hf Hw).
    + iApply ("HK" with "[%] Hps"). split; [exact Hpos|]. split; [exact Hmod|].
      destruct (R.address_space _ _ Hr' base (mkRegion base (base + req_extent q) (req_kind q) Live))
        as [_ Hend]; [rewrite object_region_allocated Z.eqb_refl; reflexivity|].
      cbn [r_end] in Hend. exact Hend.
Qed.

(** A [[flight]] whose arguments read as xs, whose address [alu]
    computes as n, and whose capability source gives c: d is bound to
    the pointer of n and c. *)
Lemma wp_flight f e ls l d o args lw rest j xs n c Φ :
  map_option (flight_arg_x ge e) args = Some xs -> alu o L xs = Some (WInt n) ->
  flight_cap ge e lw = Some c ->
  ▷ WP (ERun (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hx Ha Hc. apply (wp_pure_next _ _ []).
  intros m fuel. exact (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Ha Hc).
Qed.

(** The state interpretation does not read the [[fuel]]. *)
Lemma heap_interp_fuel m s fuel fuel' w :
  heap_interp (mkLstate m s fuel w) -∗ heap_interp (mkLstate m s fuel' w).
Proof. rewrite /heap_interp /=. iIntros "H". iExact "H". Qed.

(** Entering the block l of f, found as b, from the edge from: its phis
    bind the environment e', and the frame goes on at its instructions.
    With no [[fuel]] left the run stops there, a stall. *)
Lemma wp_enter f e ls l from b e' Φ :
  find_block l (fn_blocks f) = Some b -> phis_env ge (b_phis b) from e = Some e' ->
  ▷ WP (ERun (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Enter l from)) : lexpr) {{ Φ }}.
Proof.
  intros Hb Hp. iIntros "H". iApply (wp_lift_run with "H").
  - iIntros (σ) "_ _". iPureIntro. left. unfold fails.
    destruct (Z.eq_dec (ls_fuel σ) 0) as [Hz|Hz].
    + rewrite Hz rule_out_of_fuel. cbn. tauto.
    + rewrite (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hz Hb Hp). auto.
  - iIntros ([m s fuel w]) "Hσ H". iNext. iIntros (e2 σ2 Hm).
    destruct (Z.eq_dec fuel 0) as [->|Hz].
    + exfalso.
      destruct (moves_core _ _ _ _ Hm
                  ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite rule_out_of_fuel; discriminate))
        as [(c' & E' & _) | [(q & k & base & s' & E' & _) | (o & m' & E' & Hr & _)]];
        try discriminate E'. injection E' as <-. exact Hr.
    + pose proof (rule_enter ge f e ls l from [] m fuel b e' Hz Hb Hp) as E.
      destruct (moves_core _ _ _ _ Hm ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite E; discriminate))
        as [(c' & E' & -> & ->) | [(q & k & base & s' & E' & _) | (o & m' & E' & _)]];
        cbn [ls_mem ls_fuel] in E'; rewrite E in E'; try discriminate E'.
      injection E' as <-. cbn [conf_expr conf_state stack_expr c_frame c_callers c_mem c_fuel].
      iModIntro. iSplitL "Hσ"; [iApply (heap_interp_fuel with "Hσ") | iExact "H"].
Qed.

(** A goto to the target t, polling or not, enters its block from l. *)
Lemma wp_goto f e ls l t Φ :
  ▷ WP (ERun (mkFrame f e ls None (Enter (edge_label t) (Some l))) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l [] (JGoto t))) : lexpr) {{ Φ }}.
Proof. apply (wp_pure_next _ _ []). intros m fuel. apply rule_goto. Qed.

(** A branch on v, which reads as the integer n, enters t2's block from
    l if n is 0, else t1's. *)
Lemma wp_branch f e ls l v t1 t2 n Φ :
  value_x ge e W v = Some (WInt n) ->
  ▷ WP (ERun (mkFrame f e ls None (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) : lexpr)
      {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) : lexpr) {{ Φ }}.
Proof.
  intros Hv. apply (wp_pure_next _ _ []).
  intros m fuel. exact (rule_branch _ _ _ _ _ _ _ _ _ _ _ _ Hv).
Qed.

(** A return of v, which reads as x at f's return class k, from an
    invocation with no named locals: the invocation's value is [Ret]
    x, and the postcondition holds of it. *)
Lemma wp_ret f e l v k x Φ :
  fn_ret f = RClass k -> value_x ge e k v = Some x ->
  ▷ Φ (Ret x) -∗ WP (ERun (mkFrame f e [] None (Exec l [] (JRet v))) : lexpr) {{ Φ }}.
Proof.
  intros Hk Hv.
  assert (Hs : forall m fuel,
             Semantics.step ge (mkConfig (mkFrame f e [] None (Exec l [] (JRet v))) [] m fuel)
             = Done (Ret x)).
  { intros m fuel. rewrite (rule_ret _ _ _ _ _ _ _ _ _ _ _ Hk Hv).
    exact (rule_return_top (mkFrame f e [] None (Exec l [] (JRet v))) m fuel _ m (invalidate_none m)). }
  iIntros "H". iApply (wp_lift_run with "H").
  - iIntros (σ) "_ _". iPureIntro. left. unfold fails. rewrite Hs. cbn. tauto.
  - iIntros ([m s fuel w]) "Hσ H". iNext. iIntros (e2 σ2 Hm).
    destruct (moves_core _ _ _ _ Hm ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite Hs; discriminate))
      as [(c' & E' & _) | [(q & kk & base & s' & E' & _) | (o & m' & E' & _ & Hi & -> & ->)]];
      cbn [ls_mem ls_fuel] in E'; rewrite Hs in E'; try discriminate E'.
    injection E' as <-. cbn in Hi. injection Hi as <-. iModIntro. iFrame "Hσ".
    iApply (wp_value' _ _ _ (Ret x)). iExact "H".
Qed.

(** A return from a `void` function, from an invocation with no named
    locals: the invocation's value is [RetVoid], and the postcondition
    holds of it. *)
Lemma wp_ret_void f e l Φ :
  ▷ Φ RetVoid -∗ WP (ERun (mkFrame f e [] None (Exec l [] JRetVoid)) : lexpr) {{ Φ }}.
Proof.
  assert (Hs : forall m fuel,
             Semantics.step ge (mkConfig (mkFrame f e [] None (Exec l [] JRetVoid)) [] m fuel)
             = Done RetVoid).
  { intros m fuel. rewrite rule_ret_void.
    exact (rule_return_top (mkFrame f e [] None (Exec l [] JRetVoid)) m fuel _ m (invalidate_none m)). }
  iIntros "H". iApply (wp_lift_run with "H").
  - iIntros (σ) "_ _". iPureIntro. left. unfold fails. rewrite Hs. cbn. tauto.
  - iIntros ([m s fuel w]) "Hσ H". iNext. iIntros (e2 σ2 Hm).
    destruct (moves_core _ _ _ _ Hm ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite Hs; discriminate))
      as [(c' & E' & _) | [(q & kk & base & s' & E' & _) | (o & m' & E' & _ & Hi & -> & ->)]];
      cbn [ls_mem ls_fuel] in E'; rewrite Hs in E'; try discriminate E'.
    injection E' as <-. cbn in Hi. injection Hi as <-. iModIntro. iFrame "Hσ".
    iApply (wp_value' _ _ _ RetVoid). iExact "H".
Qed.

(** A direct call of the function g, defined in the module, with
    arguments that read as xs and make its frame callee: the callee
    runs as the callee of the caller, which waits at the rest of its
    block for the result r. *)
Lemma wp_call f e ls l r g args rest j xs gf callee Φ :
  map_option (arg_x ge e) args = Some xs -> find_fn ge g = Some (Defined gf) ->
  call_frame gf xs = Some callee ->
  ▷ WP (EWait (ERun callee) (mkFrame f e ls None (Exec l rest j)) (mkPending r None) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hx Hf Hc.
  apply (wp_pure_next _ callee [(mkFrame f e ls None (Exec l rest j), mkPending r None)]).
  intros m fuel. exact (rule_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Hf Hc).
Qed.

(** A returned outcome o resumes the caller cf waiting on it, which
    reads it as pd says: the caller goes on as cf'. *)
Lemma wp_resume o cf pd cf' Φ :
  resume cf pd o = Some cf' ->
  ▷ WP (ERun cf' : lexpr) {{ Φ }} -∗ WP (EWait (EEnd o) cf pd : lexpr) {{ Φ }}.
Proof.
  intros Hr. iIntros "H". iApply wp_lift_base_step; [done|].
  iIntros (σ ns κ κs nt) "Hσ". iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplitR; [iPureIntro; exists [], (ERun cf'), σ, []; exact (hs_resume registry ge o cf pd cf' σ Hr)|].
  iNext. iIntros (e2 σ2 efs Hs) "_". iMod "Hclose" as "_".
  inversion Hs; subst.
  match goal with H : resume cf pd o = Some ?c |- _ => assert (c = cf') as -> by congruence end. iModIntro. iFrame "Hσ". iSplitL; [iExact "H"|done].
Qed.

(** The caller cf waiting on its callee is an evaluation context. *)
Local Instance wait_ctx cf pd : LanguageCtx (Λ := nanofil_lang registry ge) (fun e => EWait e cf pd).
Proof. exact (ectxi_lang_ctx_item (Λ := nanofil_ectxi_lang registry ge) (KWait cf pd)). Qed.

(** A direct call, as [wp_call], whose callee's run ends with an
    outcome the caller resumes with: the callee's weakest precondition
    is the caller's, through [wp_bind] and [wp_resume]. A caller uses a
    callee's Hoare triple here. *)
Lemma wp_call_bind f e ls l r g args rest j xs gf callee Φ :
  map_option (arg_x ge e) args = Some xs -> find_fn ge g = Some (Defined gf) ->
  call_frame gf xs = Some callee ->
  ▷ WP (ERun callee : lexpr) {{ o, ∃ cf', ⌜resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) o
                                             = Some cf'⌝ ∗ ▷ WP (ERun cf' : lexpr) {{ Φ }} }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hx Hf Hc. iIntros "H". iApply (wp_call with "[H]"); [exact Hx|exact Hf|exact Hc|].
  iNext. iApply (wp_bind (fun ex => EWait ex (mkFrame f e ls None (Exec l rest j)) (mkPending r None))
                   NotStuck ⊤ (ERun callee : lexpr)).
  iApply (wp_mono with "H"). iIntros (o) "H". iDestruct "H" as (cf') "[%Hr H]".
  iApply (wp_resume _ _ _ _ _ Hr with "H").
Qed.

(** A call of the global g that is not a function of the module, nor
    global data, nor free: an [external_site], whose contract spec the
    registry holds, with arguments that read as xs and the contract's
    ABI. Given Q:
    - Q and the state interpretation show the contract's precondition,
      in the memory and the world of the call;
    - after any return the contract allows from that state (an
      [M.E.invoke] ending in [CallReturn] values), Q and the state
      interpretation give, under a modality that may update the ghost
      heap, the caller's environment e' the site's result binds
      ([external_env]: a return the site cannot take is ruled out
      here), the state interpretation of the call's memory, runtime
      state and world, and the weakest precondition of the rest of the
      block.
    The call's exit and resource endings, blocking, and an admissible
    call with no completed invocation need nothing: they are stalls. A
    safepoint before the call keeps Q, and the precondition is shown
    again after it. *)
Lemma wp_external f e ls lab r g args rest j spec xs (Q : iProp Σ) Φ :
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> name_eqb g free_name = false ->
  registry g = Some spec -> map_option (arg_x ge e) args = Some xs -> contract_abi spec r args ->
  (forall σ, heap_interp σ -∗ Q -∗ ⌜contract_pre spec xs (ls_mem σ) (ls_world σ)⌝) ->
  Q -∗
  ▷ (∀ σ trace values s' m' w',
       ⌜M.E.invoke spec r args xs (ls_rt σ) (ls_mem σ) (ls_world σ) trace (CallReturn values) s' m' w'⌝ -∗
       heap_interp σ -∗ Q ==∗
       ∃ e', ⌜external_env spec (mkCallSite lab r g args rest j) values e = Some e'⌝ ∗
         heap_interp (mkLstate m' s' (ls_fuel σ) w') ∗
         WP (ERun (mkFrame f e' ls None (Exec lab rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hfn Hdata Hfree Hreg Hx Habi Hpre. iIntros "HQ HK".
  set (site := mkCallSite lab r g args rest j).
  set (fr := mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)).
  assert (Hsite : forall m fuel, external_site ge (mkConfig fr [] m fuel) site).
  { intros m fuel. unfold external_site. cbv zeta. cbn. auto. }
  iCombine "HQ HK" as "H". iApply (wp_lift_run with "H").
  - iIntros (σ) "Hσ [HQ _]". iDestruct (Hpre with "Hσ HQ") as %Hp. iPureIntro. right.
    exists site. split; [apply Hsite|]. exists spec, xs. auto.
  - iIntros (σ) "Hσ [HQ HK]". iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & E' & _) | [(q & k & b & s' & E' & _) | [(o & m' & E' & _) |
      (site' & spec' & xs' & tr & vs & s' & m' & w' & Hs' & Hreg' & Hx' & Hi & -> & ->)]]];
      try (rewrite (external_site_stuck _ _ _ (Hsite _ _)) in E'; discriminate E').
    assert (site' = site) as ->.
    { eapply (external_site_unique ge); [|exact Hs'|apply (Hsite (ls_mem σ) (ls_fuel σ))]. reflexivity. }
    cbn [site_name site_args site_result] in Hreg', Hx', Hi.
    rewrite Hreg in Hreg'. injection Hreg' as <-.
    cbn [fr fr_env] in Hx'. rewrite Hx in Hx'. injection Hx' as <-.
    iMod ("HK" $! σ tr vs s' m' w' with "[%] Hσ HQ") as (e') "(%He & Hσ & Hwp)"; [exact Hi|].
    iModIntro. iFrame "Hσ". unfold returned_expr. cbn [fr fr_env]. rewrite He. iExact "Hwp".
Qed.

End wp.
End logic.

(** ## A call's whole effect on the ghost heap

    ContractFrame.v's frame for one [local_effect] or allocation,
    carried along the language's own call relations ([M.E]). *)

(** Along an [effects] path from a [[ready]] state, a ghost heap h
    whose live objects the roots avoid, none of whose identities the
    call releases or was born with, keeps agreeing with memory; live
    objects stay apart, the born objects are none of h's, and the roots
    still avoid h's live objects. born0 is [] at the start of a call. *)
Theorem effects_agrees : forall sources roots releases requests s m born0 s' m' born h,
  M.E.effects sources roots releases requests s m born0 s' m' born ->
  R.ready s m -> live_disjoint m -> agrees m h -> roots_apart roots h m ->
  ids_apart releases h -> ids_apart born0 h ->
  agrees m' h /\ live_disjoint m' /\ ids_apart born h /\ roots_apart roots h m'.
Proof.
  intros sources roots releases requests s m born0 s' m' born h H.
  induction H as [s m born0 | s m born0 m1 s' m' born Hl H IH
                 | s m born0 align size base s1 s' m' born Hq Hsize Halloc H IH];
    intros Hr Hd Ha Hra Hrel Hb.
  - auto.
  - apply IH.
    + exact (R.ready_kept _ _ _ Hr (local_effect_kept _ _ _ _ _ _ Hl)).
    + exact (local_live_disjoint _ _ _ _ _ _ Hl Hd).
    + exact (local_agrees _ _ _ _ _ _ h Hl Hd Ha Hra Hrel Hb).
    + intros sp a Hin Hs Ho. exact (Hra sp a Hin Hs (local_owned_back _ _ _ _ _ _ h Hl a Ho)).
    + exact Hrel.
    + exact Hb.
  - assert (Hal : 0 < req_align (heap_req align size)) by (cbn; lia).
    assert (He : 0 <= req_extent (heap_req align size)).
    { cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia]. }
    destruct (R.fresh_allocation _ _ _ _ _ Hr Hal He Halloc) as [Hf Hr1].
    pose proof Hf as (_ & _ & _ & Hn & _).
    apply IH.
    + exact Hr1.
    + exact (live_disjoint_allocated _ _ _ Hd Hf He).
    + intros l v Hh. exact (agree_piece_allocated _ _ _ _ _ Hn (Ha l v Hh)).
    + intros sp a Hin Hs Ho. exact (Hra sp a Hin Hs (allocated_owned_back _ _ _ _ _ Hn Ha Ho)).
    + exact Hrel.
    + exact (unregistered_apart _ _ _ _ Hn Ha Hb).
Qed.

(** The same for a whole call [prefix] of the contract spec: its
    writable roots avoid h's live objects and it releases none of h's
    identities. *)
Corollary prefix_agrees : forall world (spec : contract world) xs s m w born trace s' m' w' h,
  M.E.prefix spec xs s m w born trace s' m' w' -> R.ready s m -> live_disjoint m -> agrees m h ->
  roots_apart (contract_writes spec xs m w) h m -> ids_apart (contract_releases spec xs m w) h ->
  agrees m' h /\ live_disjoint m' /\ ids_apart born h /\ roots_apart (contract_writes spec xs m w) h m'.
Proof.
  intros world spec xs s m w born trace s' m' w' h [He _] Hr Hd Ha Hra Hrel.
  apply (effects_agrees _ _ _ _ _ _ _ _ _ _ h He Hr Hd Ha Hra Hrel). intros b l v [].
Qed.

(** The same for a completed call ([invoke]), normal or resource, for
    the born objects of its prefix. *)
Corollary invoke_agrees : forall world (spec : contract world) r args xs s m w trace ending s' m' w' h,
  M.E.invoke spec r args xs s m w trace ending s' m' w' -> R.ready s m -> live_disjoint m -> agrees m h ->
  roots_apart (contract_writes spec xs m w) h m -> ids_apart (contract_releases spec xs m w) h ->
  exists born, agrees m' h /\ live_disjoint m' /\ ids_apart born h /\
    roots_apart (contract_writes spec xs m w) h m'.
Proof.
  intros world spec r args xs s m w trace ending s' m' w' h H Hr Hd Ha Hra Hrel.
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (born & Hp).
  exists born. exact (prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hp Hr Hd Ha Hra Hrel).
Qed.

(** No world: over the world unit, the interpretation that requires
    nothing of the memory. With [no_contracts] it is the core
    machine's logic. *)
Definition no_world : mem -> unit -> gmap piece pval -> Prop := fun _ _ _ => True.

(** [no_world] survives every safepoint. *)
Instance no_world_stable : SafepointStable no_world.
Proof. split. intros s m s' m' w h _ _. exact I. Qed.

(** The Iris instance of a module that calls no external function, in
    the genv ge: no contracts and no world. *)
Instance closed_irisGS `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (ge : genv) :
  irisGS_gen hlc (nanofil_lang no_contracts ge) Σ := nanofil_irisGS no_contracts no_world ge.

(** Iris [[adequacy]] with the ghost heap: if, for every admissible
    input, the entry's frame has a weakest precondition with no
    contracts under any invariant and ghost heap instance, the module
    never panics. The initial memory's live objects must not overlap
    (it holds none for a module with no data). *)
Theorem heap_never_panics Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    md entry (input : list word -> Prop) globals m f :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  live_disjoint m ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\
     forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
       ⊢ WP (ERun fr : language.expr (nanofil_lang no_contracts (P.program_genv md globals)))
           {{ _, True }}) ->
  P.never_panics md entry input.
Proof.
  intros Hm Hf Hd Hwp. apply (L.wp_never_panics HasNoLc Σ md entry input globals m f Hm Hf).
  intros xs Hxs. destruct (Hwp xs Hxs) as (fr & Hfr & Hw). exists fr. split; [exact Hfr|].
  intros Hready fuel Hinv.
  iMod (gen_heap_init (∅ : gmap piece pval)) as (HheapG) "(Hh & _ & _)".
  iModIntro. iExists (heap_interp no_world).
  iSplitL "Hh".
  - iExists ∅. iFrame "Hh". iPureIntro. split; [|split; [exact Hd | split; [exact Hready | exact I]]].
    intros l v Hl. rewrite lookup_empty in Hl. discriminate.
  - iApply (Hw Hinv HheapG).
Qed.

(** Iris [[adequacy]] with the ghost heap for the labelled machine
    (Language.v's [wp_labelled_safe]), with the contracts of registry
    and the world interpretation wi. From the memory m, the runtime
    state s and the world w, where R is [[ready]], the live objects are
    apart, and the caller's initial ghost heap h0 agrees with m and
    satisfies wi with w: if, under any invariant and ghost heap
    instance, owning h0's pieces gives a weakest precondition of [ERun
    fr] with the postcondition φ, then for every fuel the run is
    [labelled_safe]: no labelled run stops with a [failure_ending], and
    a top-level return's value satisfies φ. *)
Theorem heap_labelled_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    {world : Type} (registry : name -> option (contract world))
    (wi : mem -> world -> gmap piece pval -> Prop)
    ge fr m s (w : world) (h0 : gmap piece pval) (φ : outcome -> Prop) :
  R.ready s m -> live_disjoint m -> agrees m h0 -> wi m w h0 ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
     ([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
       let _ : irisGS_gen HasNoLc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge in
       WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ o, ⌜φ o⌝ }}) ->
  forall fuel, labelled_safe registry ge fr m s w fuel φ.
Proof.
  intros Hr Hd Ha Hw Hwp fuel. apply (L.wp_labelled_safe HasNoLc Σ registry ge fr m s w fuel φ).
  intros Hinv. iMod (gen_heap_init h0) as (HheapG) "(Hh & Hpts & _)".
  iModIntro. iExists (heap_interp wi). iSplitL "Hh".
  - iExists h0. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. auto.
  - iPoseProof (Hwp Hinv HheapG with "Hpts") as "H". iExact "H".
Qed.

End Logic.
