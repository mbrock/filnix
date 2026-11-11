(** A C proof should describe the object and bytes an instruction
    uses, without repeating the safety argument for the whole interpreter.
    This module gives [[iris|Iris]] rules for nanofil instructions,
    using [[separation-logic|separation logic]] to track ownership of memory and object lifetimes.
    It builds on [Language](Language.v) for calls and [Heap](Heap.v)
    for the logical record of memory pieces.

    Reading a stored pointer requires both its address bytes and the
    hidden capability that gives the address its authority.
    A proof must also establish that the containing object remains
    alive, and a writer needs exclusive permission to change its bytes.
    The assertion [heap_interp] connects these permissions to actual
    memory, including the shadow [[aux]] storage, and requires a ready [[runtime]].

    External libraries also maintain state in memory, such as stream
    buffers or errno, whose representation must survive the program's operations.
    A world interpretation describes that relationship using the current
    memory, library world, and program-owned pieces.
    Every write rule requires proof that its update preserves this
    relationship, and [[poll|safepoints]] must preserve it too.
    A closed program with no external contracts can use [no_world],
    which imposes no additional conditions on memory.

    Collection or a permitted stall may intervene before an instruction
    executes, but each instruction proof should not repeat the argument for these interruptions.
    The rule [wp_lift_run] handles those cases once, leaving each
    instruction rule to describe its own execution step and resulting ownership.

    Calling another C function requires the caller to supply the
    memory and value conditions that the callee needs for safe execution.
    A [[hoare-triple|Hoare triple]] records those conditions and the
    promised result, allowing the caller to use the function without repeating its proof.

    Proving individual instructions safe matters only if the complete
    machine run also avoids panic and respects the promised return property.
    The final [[adequacy]] theorems establish that connection, carrying
    the logical guarantees over to the machine's actual executions. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language ectx_language ectxi_language weakestpre lifting
  ectx_lifting adequacy.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls Ops Semantics Run
  Machine Panics StepRules Pieces Heap Identity ContractFrame ExternalMachine Language.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Pure facts about cells

    Before reasoning about instruction ownership, we need ordinary facts
    about the bytes and shadow slots inside a live object.
    The following lemmas establish cell bounds and show that storing a
    pointer updates only its address bytes and capability slot. *)

(** An integer cell agreeing with a live object's memory occupies eight
    bytes entirely within that object's bounds, as [cell_bounds] proves. *)
Lemma cell_bounds m b reg o x :
  live_at m b reg -> all_agree m (cell b o x) -> 0 <= o /\ b + o + 8 <= r_end reg.
Proof.
  intros [E L] Hc. rewrite all_agree_cell in Hc.
  destruct (Hc 0 ltac:(lia)) as [_ H0]. destruct (Hc 7 ltac:(lia)) as [_ H7].
  destruct (H0 reg E L) as (? & _). destruct (H7 reg E L) as (_ & ? & _). lia.
Qed.

(** A stored capability may change after its target object is freed,
    but it must still reject the accesses that the old capability rejected.
    The lemma [aux_piece_holds] relates an owned shadow entry to its
    actual slot through [aux_holds], which allows that restricted replacement. *)
Lemma aux_piece_holds m b reg o c :
  live_at m b reg -> agree_piece m (PAux b o) (VAux c) -> aux_holds m (b + o) c.
Proof. intros [E L] [_ H]. destruct (H reg E L) as (_ & _ & Hx). exact Hx. Qed.

(** Every byte of an eight-byte range bounded by a live object's
    region belongs to an object, as [in_object_live] establishes. *)
Lemma in_object_live m b reg a :
  live_at m b reg -> b <= a -> a + 8 <= r_end reg -> forall x, a <= x < a + 8 -> in_object m x.
Proof. intros [E _] H1 H2 x Hx. exists b, reg. split; [exact E | lia]. Qed.

(** Storing a pointer writes its capability slot and eight address
    bytes, leaving agreement for all other owned pieces unchanged.
    The lemma [pcell_store_ok] establishes this update at any offset
    whose complete address cell lies inside the live object. *)
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

(** ## The logic over a runtime

    Deallocation ends an object's lifetime without overwriting its bytes
    or shadow slots, so proofs must update lifetime ownership separately.
    The following facts prepare that update before the logic introduces
    its runtime requirements and connection between ownership and physical memory. *)

(** Freeing one live heap object empties its bounds and marks it freed,
    while preserving every byte, shadow slot, and other object's region.
    The lemma [free_heap_kept] shows that this change satisfies the
    runtime's restriction on ordinary memory updates. *)
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

(** Freeing a heap object preserves agreement for every piece except
    its lifetime, which must change from live to freed.
    Its byte and shadow assertions require matching values only while
    the object is live, so they remain valid without authorizing further access. *)
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
  destruct l as [b'|b' o|b' o|k], v as [reg'|y|c| |q t|cd|sq sp|ga gi|op]; cbn [agree_piece] in Ha |- *; try contradiction;
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

(** Ending one object's lifetime cannot make the remaining live objects
    overlap, as [live_disjoint_free] proves from their previously disjoint regions. *)
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

(** The module [Logic] supplies memory ownership and instruction rules
    for the chosen runtime R and its language of function calls. *)
Module Logic (R : Runtime).
Module L := Language R.
Module SS := SafepointShape R.
Module P := L.P.
Module RM := L.RM.
Import L.

(** Garbage collection must preserve the relationship between library
    state and memory, because a safepoint may precede any instruction.
    The class [SafepointStable] records that requirement for the chosen
    world interpretation, leaving the external world and ownership map unchanged. *)
Class SafepointStable {world : Type} (wi : mem -> world -> gmap piece pval -> Prop) : Prop := {
  wi_safepoint : forall s m s' m' w h, R.safepoint s m s' m' -> wi m w h -> wi m' w h
}.

(** Library calls need consistent assumptions about their permitted
    effects and the memory holding their private state.
    The following rules fix one registry of those call contracts and
    one description of how library state relates to memory and ownership. *)
Section logic.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi}.

(** The logical record of owned pieces must agree with actual memory,
    whose live objects remain disjoint and whose runtime remains ready.
    The assertion [heap_interp] combines those requirements with the
    external-world interpretation, without constraining the remaining execution [[fuel]]. *)
Definition heap_interp (σ : lstate world) : iProp Σ :=
  ∃ h : gmap piece pval, gen_heap_interp h ∗
    ⌜agrees (ls_mem σ) h /\ live_disjoint (ls_mem σ) /\ R.ready (ls_rt σ) (ls_mem σ) /\
     wi (ls_mem σ) (ls_world σ) h⌝.

(** The instance [nanofil_irisGS] connects Iris execution to [heap_interp]
    for this global environment, with no forked threads or additional step credits. *)
Local Instance nanofil_irisGS (ge : genv) : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  IrisG _ (fun σ _ _ _ => heap_interp σ) (fun _ => True%I) (fun _ => 0%nat)
        (fun _ _ _ _ => fupd_intro _ _).

(** ## The assertions

    Instruction rules describe memory through ownership of object
    lifetimes, integer cells, individual bytes, and stored pointers.
    The following assertions package those pieces, with fractional
    variants for readers that do not need exclusive write permission. *)

(** An object's [[live|lifetime]] belongs to the assertion [live], which
    records its identity b and the region reg while it remains alive. *)
Definition live (b : Z) (reg : region) : iProp Σ := pts [(PLive b, VLive reg)].

(** An eight-byte integer cell belongs to [icell], which records its
    little-endian value v at offset o within object b. *)
Definition icell (b o v : Z) : iProp Σ := pts (cell b o v).

(** One data byte belongs to [ibyte], which records value x at offset
    o within object b without owning adjacent bytes. *)
Definition ibyte (b o x : Z) : iProp Σ := pts [(PByte b o, VByte x)].

(** A stored pointer belongs to [pcell], which owns its eight address
    bytes and the shadow slot holding its [[capability]]. *)
Definition pcell (b o : Z) (x : ptr) : iProp Σ :=
  pts ((PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)).

(** A newly allocated object belongs to [obj], including its lifetime,
    zero-initialized bytes, and empty shadow entries at every offset. *)
Definition obj (b : Z) (q : alloc_req) : iProp Σ := pts (obj_ps b q).

(** Loading a pointer exactly requires knowing that its target object
    has not been freed, so collection cannot rewrite its stored capability.
    The assertion [live_cap] owns a writable target's lifetime, accepts
    an empty capability without resources, and rejects other capability forms. *)
Definition live_cap (c : cap) (reg : region) : iProp Σ :=
  match c with
  | CNone => True
  | Obj b => live b reg
  | _ => False
  end.

(** Readers can share an object's lifetime through [liveq], whose
    fraction records their permission without granting exclusive authority to free the object. *)
Definition liveq (dq : dfrac) (b : Z) (reg : region) : iProp Σ := ptsq dq [(PLive b, VLive reg)].

(** Readers can share an eight-byte integer cell through [icellq],
    retaining its little-endian value without requiring exclusive ownership of its bytes. *)
Definition icellq (dq : dfrac) (b o v : Z) : iProp Σ := ptsq dq (cell b o v).

(** Readers can share a stored pointer through [pcellq], retaining
    fractional ownership of both its address bytes and its shadow capability slot. *)
Definition pcellq (dq : dfrac) (b o : Z) (x : ptr) : iProp Σ :=
  ptsq dq ((PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)).

(** Shared target-lifetime ownership prevents collection from rewriting
    a stored object capability, whether that capability is writable or read-only.
    The assertion [live_capq] requires that share for object capabilities
    and no resources for empty, function, or external-symbol capabilities. *)
Definition live_capq (dq : dfrac) (c : cap) (reg : region) : iProp Σ :=
  match c with
  | Obj b | Ro b => liveq dq b reg
  | _ => True
  end.

(** Owned pieces describe real memory values and bounds through
    [pts_facts], which also supplies live-object separation and the runtime's address-space restriction. *)
Lemma pts_facts σ ps : heap_interp σ -∗ pts ps -∗ ⌜owned_facts ps (ls_mem σ)⌝.
Proof.
  iIntros "Hσ Hps". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr & _).
  iDestruct (pts_lookup with "Hh Hps") as %Hl. iPureIntro.
  split; [|split; [exact Hd | exact (R.address_space _ _ Hr)]].
  apply all_agree_intro. intros l v Hin. apply Ha. apply Hl. exact Hin.
Qed.

(** Even a shared piece records the same memory facts as exclusive
    ownership, which [ptsq_facts] derives without granting permission to change that piece. *)
Lemma ptsq_facts σ dq ps : heap_interp σ -∗ ptsq dq ps -∗ ⌜owned_facts ps (ls_mem σ)⌝.
Proof.
  iIntros "Hσ Hps". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr & _).
  iDestruct (ptsq_lookup with "Hh Hps") as %Hl. iPureIntro.
  split; [|split; [exact Hd | exact (R.address_space _ _ Hr)]].
  apply all_agree_intro. intros l v Hin. apply Ha. apply Hl. exact Hin.
Qed.

(** A capability covered by shared target-lifetime ownership cannot
    name a freed object, so its stored shadow representation remains exact. *)
Lemma live_capq_facts σ dq c reg : heap_interp σ -∗ live_capq dq c reg -∗ ⌜~ freed_in (m_regions (ls_mem σ)) c⌝.
Proof.
  iIntros "Hσ H". iAssert (⌜forall b, c = Obj b \/ c = Ro b -> live_at (ls_mem σ) b reg⌝)%I with "[Hσ H]" as %Hl.
  - destruct c as [|b|b|g|n]; cbn [live_capq];
      try (iPureIntro; intros b' [Hc|Hc]; discriminate Hc);
      iDestruct (ptsq_facts with "Hσ H") as %([Hlv _] & _); iPureIntro;
      intros b' [Hc|Hc]; inversion Hc; subst; exact Hlv.
  - iPureIntro. intros (b & reg' & Hc & E & L). destruct (Hl b Hc) as [E' L'].
    rewrite E' in E. injection E as <-. congruence.
Qed.

(** Exclusive target-lifetime ownership establishes either an empty
    capability or a writable capability naming a live object in actual memory. *)
Lemma live_cap_facts σ c reg : heap_interp σ -∗ live_cap c reg -∗
  ⌜c = CNone \/ exists b reg, c = Obj b /\ live_at (ls_mem σ) b reg⌝.
Proof.
  destruct c; cbn [live_cap]; iIntros "Hσ H"; try done; [iPureIntro; by left|].
  iDestruct (pts_facts with "Hσ H") as %(Hf & _). iPureIntro. right.
  cbn [all_agree agree_piece fst snd] in Hf. eexists _, _. split; [reflexivity | exact (proj1 Hf)].
Qed.

(** A safepoint preserves the connection between owned pieces and
    memory, retaining the same logical map and external world despite allowed runtime changes. *)
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

(** Rewriting a logical map entry with the value it already contains
    leaves the map unchanged, as [overwrite_id] proves for a piece list. *)
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

(** The notation [lexpr] names expressions for the chosen global
    environment and contract registry, keeping those parameters implicit in instruction rules. *)
Local Notation lexpr := (language.expr (nanofil_lang registry ge)).

(** Some language steps execute an instruction or return a result,
    rather than merely stall or run a safepoint.
    The predicate [moves] selects ordinary next steps, granted
    allocations, function returns, and external returns, including incompatible external results. *)
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

(** If the core machine is not stuck, any step selected by [moves]
    must be a core step rather than an external return. *)
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

(** To prove an instruction safe, show that it can proceed and that
    each actual execution step leaves a safe continuation.
    The rule [wp_lift_run] handles intervening safepoints and stalls
    itself, preserving the supplied ownership Q through those repeated steps.
    After any step selected by [moves], the proof must restore the
    memory interpretation and establish the continuation's [[weakest-precondition|weakest precondition]]. *)
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

(** A write rule replaces the values of owned pieces while preserving
    their locations and leaving unrelated pieces valid.
    The rule [wp_write_with] also carries an additional assertion Q,
    which can supply memory facts needed to justify the instruction.
    The caller proves the machine update, unchanged regions, agreement
    with the new pieces, and preservation of the external-world interpretation.
    The continuation receives the updated pieces and the additional
    assertion, with any resulting caller stack surrounding the next frame. *)
Lemma wp_write_with (Q : iProp Σ) (F : mem -> Prop) ps ps' fr fr' cs' (upd : mem -> mem) Φ :
  ps'.*1 = ps.*1 ->
  (forall σ, heap_interp σ -∗ Q -∗ ⌜F (ls_mem σ)⌝) ->
  (forall m fuel, owned_facts ps m -> F m ->
     Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' (upd m) fuel) /\
     m_regions (upd m) = m_regions m /\ kept m (upd m) /\
     all_agree (upd m) ps' /\ frame_ok ps'.*1 m (upd m)) ->
  (forall m w h, (forall l v, (l, v) ∈ ps -> h !! l = Some v) -> wi m w h ->
     wi (upd m) w (overwrite ps' h)) ->
  pts ps -∗ Q -∗ ▷ (pts ps' -∗ Q -∗ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }}) -∗
  WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros Hk HF Hs Hwi. iIntros "Hps HQ HK". iCombine "Hps HQ HK" as "H".
  iApply (wp_lift_run with "H").
  - iIntros (σ) "Hσ [Hps [HQ _]]". iDestruct (pts_facts with "Hσ Hps") as %Hf.
    iDestruct (HF with "Hσ HQ") as %HFm. iPureIntro.
    destruct (Hs _ (ls_fuel σ) Hf HFm) as (E & _). left. unfold fails. rewrite E. auto.
  - iIntros ([m s fuel w]) "Hσ [Hps [HQ HK]]". iDestruct (pts_facts with "Hσ Hps") as %Hf.
    iDestruct (HF with "Hσ HQ") as %HFm.
    cbn [ls_mem ls_rt ls_fuel ls_world] in *.
    destruct (Hs m fuel Hf HFm) as (E & Hreg & Hkept & Hag & Hfr). iNext. iIntros (e2 σ2 Hm).
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
    + iApply ("HK" with "Hps HQ").
Qed.

(** When the owned pieces alone justify a write, [wp_write] applies the
    general write rule without carrying an additional assertion. *)
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
  intros Hk Hs Hwi. iIntros "Hps HK".
  iApply (wp_write_with True (fun _ => True) ps ps' fr fr' cs' upd with "Hps [//] [HK]");
    [exact Hk | auto | intros m fuel Hf _; exact (Hs m fuel Hf) | exact Hwi |].
  iNext. iIntros "Hps _". iApply ("HK" with "Hps").
Qed.

(** A read-only step preserves all memory and returns the same owned
    pieces to its continuation, as [wp_read] packages for instruction proofs. *)
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

(** An instruction needing no owned memory can use [wp_pure_next] when
    its next configuration is fixed and memory remains unchanged. *)
Lemma wp_pure_next fr fr' cs' Φ :
  (forall m fuel, Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' m fuel)) ->
  ▷ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }} -∗ WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros Hs. iIntros "H". iApply (wp_read [] fr fr' cs' with "[] [H]"); [|by rewrite /pts|].
  - intros m fuel _. apply Hs.
  - iNext. iIntros "_". iExact "H".
Qed.

(** ## The rules

    Each rule connects one instruction to the ownership and ordinary
    value facts that justify its execution.
    The continuation receives the resulting register values and any
    preserved or updated memory ownership, without repeating the shared safepoint argument. *)

(** A general operation whose result is the same in every memory can
    bind that result directly through [wp_let], without memory ownership. *)
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

(** A pointer [[check]] succeeds when lifetime ownership establishes a
    live object and the requested bytes satisfy its bounds and alignment.
    The rule [wp_check] binds the same pointer as proven and returns
    the lifetime ownership for subsequent instructions. *)
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

(** A read check accepts either a writable or read-only object
    capability when the requested bytes lie within aligned live-object bounds.
    The rule [wp_check_read] returns the proven pointer and preserves
    ownership of the enclosing object's lifetime. *)
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

(** A [[half_check|half check]] reuses a proof with the same writable
    capability while checking a nonempty aligned range within the live object.
    The rule [wp_half_check] also requires the object's end below or
    at the signed-address limit, and preserves lifetime ownership. *)
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

(** A read half check also accepts a read-only capability, as needed
    when GNU Hello scans string literals using an earlier proof.
    The rule [wp_half_check_read] requires matching capabilities, live
    object bounds, alignment, and an object end within the signed-address limit. *)
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

(** Renewing a pointer proof reuses an earlier proof with the same
    writable capability while lifetime ownership establishes that the object remains live.
    The rule [wp_renew] requires the requested range and alignment;
    GNU Hello uses this operation when reusing a checked stack slot. *)
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

(** Loading an owned integer cell through a proven writable pointer
    returns its low 64 bits and preserves both cell and lifetime ownership. *)
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

(** A one-byte raw load reads an owned byte and extends it according
    to the narrow type and destination class.
    The rule [wp_raw_load_byte] accepts writable or read-only capabilities
    and returns both the byte ownership and the object's lifetime. *)
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

(** An integer-cell load can also use a read-only capability, as
    glibc's strlen does when reading whole words from a string literal.
    The rule [wp_raw_load_read] returns the cell's low 64 bits and
    preserves the cell and lifetime ownership. *)
Lemma wp_raw_load_read f e ls l d k off args rest j classes p b reg o v Φ :
  op_arg_classes (RawLoad LdL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
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
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - rewrite pts_app. iFrame.
  - iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A narrow load from an owned integer cell reads its low bytes and
    extends them according to the selected type and destination class.
    The rule [wp_raw_load_sub_read] preserves the complete cell ownership
    and accepts either writable or read-only object capabilities. *)
Lemma wp_raw_load_sub_read f e ls l d k n off args rest j classes p b reg o v y Φ :
  op_arg_classes (RawLoad (LdNarrow n) off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  extended n k (v mod 2 ^ (8 * fst (narrow_type n))) = Some y ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
  live b reg -∗ icell b o v -∗
  ▷ (live b reg -∗ icell b o v -∗
     WP (ERun (mkFrame f (put d y e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad (LdNarrow n) off) args :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hc Hx Hy Hp Ha. iIntros "Hl Hc HK".
  assert (Hs : 0 <= fst (narrow_type n) <= 8) by (destruct n; cbn; lia).
  iApply (wp_read ([(PLive b, VLive reg)] ++ cell b o v) _ _ [] with "[Hl Hc] [HK]").
  - intros m fuel (Hf & _). apply all_agree_app in Hf as [[Hlv _] Hcl]. cbn [agree_piece fst snd] in Hlv.
    destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load_narrow m k n p off).
    + rewrite Ha (cell_load_low m b reg o v (b + o) _ Hlv Hcl eq_refl Hs) Hy. reflexivity.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - rewrite pts_app. iFrame.
  - iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A read-only step can use any supplied assertion to establish the
    memory facts needed for its next configuration.
    The rule [wp_read_with] preserves that assertion Q and all memory,
    rather than requiring ownership in one particular piece-list form. *)
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

(** A plain pointer load reads both the address and capability from an
    aligned owned cell, returning exactly the recorded pointer.
    The rule [wp_raw_load_pointer] also needs target-lifetime ownership
    and an address within 64 bits, preventing collection from changing the loaded capability. *)
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

(** An instruction may read library-owned memory when the world
    interpretation determines its result from tokens already owned by the program.
    The rule [wp_world_let_with] preserves those tokens and all memory,
    without incorrectly claiming ownership of the library's private cells. *)
Lemma wp_world_let_with ps f e ls l d k o args rest j classes xs x Φ :
  general_op o = true -> op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some xs ->
  (forall m w h, wi m w h -> (forall l v, (l, v) ∈ ps -> h !! l = Some v) ->
     op_res o k xs m = Some (OpRes (RVal x) m)) ->
  pts ps -∗
  ▷ (pts ps -∗ WP (ERun (mkFrame f (put d x e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hg Hc Hargs Hop. iIntros "Hps HK".
  iApply (wp_read_with (pts ps) (fun m => op_res o k xs m = Some (OpRes (RVal x) m)) _ _ []
            with "Hps [HK]").
  - iIntros (σ) "(%h & Hh & %Hf) Hps". destruct Hf as (_ & _ & _ & Hw).
    iDestruct (pts_lookup with "Hh Hps") as %Hl. iPureIntro. exact (Hop _ _ _ Hw Hl).
  - intros m fuel Hm. exact (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hc Hargs Hm).
  - iNext. iExact "HK".
Qed.

(** A pointer load can obtain target-lifetime evidence from pieces the
    caller already owns, accepting writable or read-only cell and target capabilities.
    The rule [wp_raw_load_pointer_in] prevents collection from changing
    object capabilities and also handles empty, function, and external capabilities, which collection never rewrites. *)
Lemma wp_raw_load_pointer_in f e ls l d off args rest j classes p b reg o x ps Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 ->
  (forall xb, ptr_cap x = Obj xb \/ ptr_cap x = Ro xb -> exists xr, (PLive xb, VLive xr) ∈ ps) ->
  live b reg -∗ pcell b o x -∗ pts ps -∗
  ▷ (live b reg -∗ pcell b o x -∗ pts ps -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
       : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hrange Hlife. iIntros "Hl Hc Hps HK".
  iApply (wp_read_with (live b reg ∗ pcell b o x ∗ pts ps)
            (fun m => live_at m b reg /\ agree_piece m (PAux b o) (VAux (ptr_cap x)) /\
                      all_agree m (cell b o (ptr_addr x)) /\ all_agree m ps)
            _ _ [] with "[$Hl $Hc $Hps] [HK]").
  - iIntros (σ) "Hσ (Hl & Hc & Hps)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (pts_facts with "Hσ Hc") as %([Hax Hcl] & _).
    iDestruct (pts_facts with "Hσ Hps") as %(Hps & _). iPureIntro. auto.
  - intros m fuel (Hlv & Hax & Hcl & Hps). destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    assert (Hkept : ~ freed_in (m_regions m) (ptr_cap x)).
    { intros (xb & xr' & Hcx & Hreg & Hfr). destruct (Hlife xb Hcx) as [xr Hin].
      destruct (all_agree_elem _ _ _ _ Hps Hin) as [E L].
      rewrite E in Hreg. injection Hreg as <-. congruence. }
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    apply op_raw_load_pointer.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | exact Hal].
    + rewrite pointer_load_plain Ha (cell_load m b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl).
      rewrite Z.mod_small; [|exact Hrange]. unfold aux_at.
      rewrite (aux_holds_kept _ _ _ (aux_piece_holds _ _ _ _ _ Hlv Hax) Hkept).
      destruct x; reflexivity.
  - iNext. iIntros "(Hl & Hc & Hps)". iApply ("HK" with "Hl Hc Hps").
Qed.

(** ## Reads at a share

    Reading does not require exclusive ownership because it leaves the
    stored bytes and capabilities unchanged.
    The following rules accept fractional shares of object lifetimes
    and cells, then return those same shares alongside the loaded result. *)

(** A memory-preserving step can use shared piece ownership through
    [wp_read_dq], returning the same share to the continuation after the step. *)
Lemma wp_read_dq dq ps fr fr' cs' Φ :
  (forall m fuel, owned_facts ps m ->
     Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' m fuel)) ->
  ptsq dq ps -∗ ▷ (ptsq dq ps -∗ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }}) -∗
  WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros Hs. apply (wp_read_with _ (owned_facts ps)); [|exact Hs].
  iIntros (σ) "Hσ Hps". iApply (ptsq_facts with "Hσ Hps").
Qed.

(** A shared integer-cell load returns the recorded value's low 64
    bits while preserving separate shares of the cell and object lifetime.
    The rule [wp_raw_load_read_dq] accepts either a writable or read-only
    capability for the cell's enclosing object. *)
Lemma wp_raw_load_read_dq f e ls l d k off args rest j classes p b reg o v dq1 dq2 Φ :
  op_arg_classes (RawLoad LdL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
  liveq dq1 b reg -∗ icellq dq2 b o v -∗
  ▷ (liveq dq1 b reg -∗ icellq dq2 b o v -∗
     WP (ERun (mkFrame f (put d (WInt (v mod 2 ^ 64)) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha. iIntros "Hl Hc HK".
  iApply (wp_read_with (liveq dq1 b reg ∗ icellq dq2 b o v)
            (fun m => live_at m b reg /\ all_agree m (cell b o v)) _ _ [] with "[$Hl $Hc] [HK]").
  - iIntros (σ) "Hσ [Hl Hc]".
    iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hc") as %(Hcl & _). iPureIntro. auto.
  - intros m fuel (Hlv & Hcl). destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load m k p off).
    + rewrite Ha (cell_load m b reg o v (b + o) Hlv Hcl eq_refl). reflexivity.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A narrow load needs only shared ownership of its integer cell and
    object lifetime, even though it returns an extended register value.
    The rule [wp_raw_load_sub_read_dq] preserves both shares and accepts
    writable or read-only access to the cell's object. *)
Lemma wp_raw_load_sub_read_dq f e ls l d k n off args rest j classes p b reg o v y dq1 dq2 Φ :
  op_arg_classes (RawLoad (LdNarrow n) off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  extended n k (v mod 2 ^ (8 * fst (narrow_type n))) = Some y ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
  liveq dq1 b reg -∗ icellq dq2 b o v -∗
  ▷ (liveq dq1 b reg -∗ icellq dq2 b o v -∗
     WP (ERun (mkFrame f (put d y e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad (LdNarrow n) off) args :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hc Hx Hy Hp Ha. iIntros "Hl Hc HK".
  assert (Hs : 0 <= fst (narrow_type n) <= 8) by (destruct n; cbn; lia).
  iApply (wp_read_with (liveq dq1 b reg ∗ icellq dq2 b o v)
            (fun m => live_at m b reg /\ all_agree m (cell b o v)) _ _ [] with "[$Hl $Hc] [HK]").
  - iIntros (σ) "Hσ [Hl Hc]".
    iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hc") as %(Hcl & _). iPureIntro. auto.
  - intros m fuel (Hlv & Hcl). destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load_narrow m k n p off).
    + rewrite Ha (cell_load_low m b reg o v (b + o) _ Hlv Hcl eq_refl Hs) Hy. reflexivity.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A pointer load needs only shared ownership of its cell, enclosing
    object lifetime, and any target-object lifetime that protects the stored capability.
    The rule [wp_raw_load_pointer_dq] returns the exact recorded pointer
    and all three shares, accepting writable or read-only object capabilities. *)
Lemma wp_raw_load_pointer_dq f e ls l d off args rest j classes p b reg o x reg' dq1 dq2 dq3 Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 ->
  liveq dq1 b reg -∗ pcellq dq2 b o x -∗ live_capq dq3 (ptr_cap x) reg' -∗
  ▷ (liveq dq1 b reg -∗ pcellq dq2 b o x -∗ live_capq dq3 (ptr_cap x) reg' -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
       : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hrange. iIntros "Hl Hc Hcap HK".
  iApply (wp_read_with (liveq dq1 b reg ∗ pcellq dq2 b o x ∗ live_capq dq3 (ptr_cap x) reg')
            (fun m => live_at m b reg /\ agree_piece m (PAux b o) (VAux (ptr_cap x)) /\
                      all_agree m (cell b o (ptr_addr x)) /\ ~ freed_in (m_regions m) (ptr_cap x))
            _ _ [] with "[$Hl $Hc $Hcap] [HK]").
  - iIntros (σ) "Hσ (Hl & Hc & Hcap)".
    iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hc") as %([Hax Hcl] & _).
    iDestruct (live_capq_facts with "Hσ Hcap") as %Hkept. iPureIntro. auto.
  - intros m fuel (Hlv & Hax & Hcl & Hkept). destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    apply op_raw_load_pointer.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | exact Hal].
    + rewrite pointer_load_plain Ha (cell_load m b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl).
      rewrite Z.mod_small; [|exact Hrange]. unfold aux_at.
      rewrite (aux_holds_kept _ _ _ (aux_piece_holds _ _ _ _ _ Hlv Hax) Hkept).
      destruct x; reflexivity.
  - iNext. iIntros "(Hl & Hc & Hcap)". iApply ("HK" with "Hl Hc Hcap").
Qed.

(** ## Compare-exchange

    Compare-exchange always returns the old value and writes a new
    value only when the comparison succeeds.
    The following rules require exclusive ownership of the destination
    cell, distinguishing integer bit comparisons from pointer address comparisons. *)

(** Integer [[cas|compare-exchange]] compares the stored and expected
    values modulo 64 bits, replacing the cell only when those bit patterns match.
    The rule [wp_raw_cas_l] requires an eight-byte-aligned address and
    proves the external-world condition only for the successful write case.
    The continuation receives the old value and ownership describing
    either the new cell contents or the unchanged old contents. *)
Lemma wp_raw_cas_l f e ls l d k off args rest j classes p b reg o v ev nv Φ :
  op_arg_classes (RawCas CasL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p; WInt ev; WInt nv] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  (v mod 2 ^ 64 = ev mod 2 ^ 64 -> forall m wd h,
     (forall l v', (l, v') ∈ [(PLive b, VLive reg)] ++ cell b o v -> h !! l = Some v') ->
     wi m wd h -> wi (store_bytes m (b + o) 8 nv) wd (overwrite ([(PLive b, VLive reg)] ++ cell b o nv) h)) ->
  live b reg -∗ icell b o v -∗
  ▷ (live b reg -∗ icell b o (if v mod 2 ^ 64 =? ev mod 2 ^ 64 then nv else v) -∗
     WP (ERun (mkFrame f (put d (WInt (v mod 2 ^ 64)) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawCas CasL off) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hwi. iIntros "Hl Hc HK".
  assert (Hop : forall m, live_at m b reg -> all_agree m (cell b o v) ->
    op_res (RawCas CasL off) k [WPtr p; WInt ev; WInt nv] m =
    Some (OpRes (RVal (WInt (v mod 2 ^ 64)))
      (if v mod 2 ^ 64 =? ev mod 2 ^ 64 then store_bytes m (b + o) 8 nv else m))).
  { intros m Hlv Hcl. destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    rewrite (op_raw_cas_int m CasL k p off ev nv (WInt (v mod 2 ^ 64))); [| discriminate | |].
    - rewrite Ha (cell_load m b reg o v (b + o) Hlv Hcl eq_refl). reflexivity.
    - rewrite Hp Ha. apply (access_obj _ _ reg); [exact (proj1 Hlv) | cbn; lia | cbn; lia | exact Hal].
    - rewrite Ha (cell_load m b reg o v (b + o) Hlv Hcl eq_refl). reflexivity. }
  destruct (v mod 2 ^ 64 =? ev mod 2 ^ 64) eqn:Eq.
  - iApply (wp_write ([(PLive b, VLive reg)] ++ cell b o v) ([(PLive b, VLive reg)] ++ cell b o nv)
              _ _ [] (fun m => store_bytes m (b + o) 8 nv) with "[Hl Hc] [HK]");
      [reflexivity | | exact (Hwi (proj1 (Z.eqb_eq _ _) Eq)) | rewrite pts_app; iFrame |].
    + intros m fuel (Hf & Hd & _). apply all_agree_app in Hf as [[Hlv _] Hcl].
      cbn [agree_piece fst snd] in Hlv. destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
      destruct (cell_store_ok m b reg o (b + o) nv Hd Hlv Ho He eq_refl) as [Hcs Hfr].
      split; [|split; [reflexivity|split; [|split]]].
      * apply rule_let with (classes := classes) (xs := [WPtr p; WInt ev; WInt nv]);
          [reflexivity | exact Hc | exact Hx |]. rewrite (Hop m Hlv Hcl); rewrite ?Eq; reflexivity.
      * apply store_bytes_kept. exact (in_object_live _ _ _ (b + o) Hlv ltac:(lia) ltac:(lia)).
      * apply all_agree_app. split; [|exact Hcs]. cbn [all_agree agree_piece fst snd].
        split; [apply (live_at_regions m); [reflexivity|exact Hlv] | exact I].
      * eapply frame_ok_mono; [|exact Hfr]. intros key Hin. rewrite fmap_app. apply elem_of_app. by right.
    + iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
  - iApply (wp_read ([(PLive b, VLive reg)] ++ cell b o v) _ _ [] with "[Hl Hc] [HK]").
    + intros m fuel (Hf & _). apply all_agree_app in Hf as [[Hlv _] Hcl]. cbn [agree_piece fst snd] in Hlv.
      apply rule_let with (classes := classes) (xs := [WPtr p; WInt ev; WInt nv]);
        [reflexivity | exact Hc | exact Hx |]. rewrite (Hop m Hlv Hcl); rewrite ?Eq; reflexivity.
    + rewrite pts_app. iFrame.
    + iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** Pointer compare-exchange compares addresses alone, ignoring capability
    differences, and returns the complete old pointer whether the comparison succeeds or fails.
    On success, [wp_raw_cas_ptr] installs the new address and capability;
    otherwise, it leaves both parts of the old pointer unchanged.
    The rule needs an aligned owned cell, shared target-lifetime evidence
    for the old pointer, and preservation of the world on success. *)
Lemma wp_raw_cas_ptr f e ls l d off args rest j classes p b reg o x ep np reg' dq Φ :
  op_arg_classes (RawCas CasP off) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p; WPtr ep; WPtr np] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 ->
  (ptr_addr x = ptr_addr ep -> forall m wd h,
     (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
        h !! l = Some v) ->
     wi m wd h ->
     wi (store_bytes (store_aux m (b + o) (ptr_cap np)) (b + o) 8 (ptr_addr np)) wd
       (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap np)) :: cell b o (ptr_addr np)) h)) ->
  live b reg -∗ pcell b o x -∗ live_capq dq (ptr_cap x) reg' -∗
  ▷ (live b reg -∗ pcell b o (if ptr_addr x =? ptr_addr ep then np else x) -∗ live_capq dq (ptr_cap x) reg' -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d P (RawCas CasP off) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hrange Hwi. iIntros "Hl Hc Hcap HK".
  assert (Hop : forall m, live_at m b reg -> agree_piece m (PAux b o) (VAux (ptr_cap x)) ->
    all_agree m (cell b o (ptr_addr x)) -> ~ freed_in (m_regions m) (ptr_cap x) ->
    op_res (RawCas CasP off) P [WPtr p; WPtr ep; WPtr np] m =
    Some (OpRes (RVal (WPtr x))
      (if ptr_addr x =? ptr_addr ep
       then store_bytes (store_aux m (b + o) (ptr_cap np)) (b + o) 8 (ptr_addr np) else m))).
  { intros m Hlv Hax Hcl Hkept. destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    rewrite op_raw_cas_ptr.
    - rewrite Ha (cell_load m b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl) Z.mod_small; [|exact Hrange].
      unfold aux_at. rewrite (aux_holds_kept _ _ _ (aux_piece_holds _ _ _ _ _ Hlv Hax) Hkept).
      destruct x; reflexivity.
    - rewrite Hp Ha. apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | exact Hal]. }
  destruct (ptr_addr x =? ptr_addr ep) eqn:Eq.
  - iApply (wp_write_with (live_capq dq (ptr_cap x) reg') (fun m => ~ freed_in (m_regions m) (ptr_cap x))
              ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x))
              ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap np)) :: cell b o (ptr_addr np))
              _ _ [] (fun m => store_bytes (store_aux m (b + o) (ptr_cap np)) (b + o) 8 (ptr_addr np))
              with "[Hl Hc] Hcap [HK]");
      [reflexivity | | | exact (Hwi (proj1 (Z.eqb_eq _ _) Eq)) | rewrite pts_app; iFrame |].
    + iIntros (σ) "Hσ Hcap". iApply (live_capq_facts with "Hσ Hcap").
    + intros m fuel (Hf & Hd & _) Hkept. apply all_agree_app in Hf as [[Hlv _] [Hax Hcl]].
      cbn [agree_piece fst snd] in Hlv. destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
      destruct (pcell_store_ok m b reg o (b + o) (ptr_cap np) (ptr_addr np) Hd Hlv Ho He eq_refl)
        as [Hcs Hfr].
      assert (Hin := in_object_live _ _ _ (b + o) Hlv ltac:(lia) ltac:(lia)).
      split; [|split; [reflexivity|split; [|split]]].
      * apply rule_let with (classes := classes) (xs := [WPtr p; WPtr ep; WPtr np]);
          [reflexivity | exact Hc | exact Hx |]. rewrite (Hop m Hlv Hax Hcl Hkept); rewrite ?Eq; reflexivity.
      * exact (pointer_store_effects_kept _ _ _ _ _ Hin (pointer_store_plain m (b + o) np)).
      * apply all_agree_app. split; [|exact Hcs]. cbn [all_agree agree_piece fst snd].
        split; [apply (live_at_regions m); [reflexivity|exact Hlv] | exact I].
      * eapply frame_ok_mono; [|exact Hfr]. intros key Hin'. rewrite fmap_app. apply elem_of_app. by right.
    + iNext. iIntros "H Hcap". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc Hcap").
  - iApply (wp_read_with (live b reg ∗ pcell b o x ∗ live_capq dq (ptr_cap x) reg')
              (fun m => live_at m b reg /\ agree_piece m (PAux b o) (VAux (ptr_cap x)) /\
                        all_agree m (cell b o (ptr_addr x)) /\ ~ freed_in (m_regions m) (ptr_cap x))
              _ _ [] with "[$Hl $Hc $Hcap] [HK]").
    + iIntros (σ) "Hσ (Hl & Hc & Hcap)".
      iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
      iDestruct (pts_facts with "Hσ Hc") as %([Hax Hcl] & _).
      iDestruct (live_capq_facts with "Hσ Hcap") as %Hkept. iPureIntro. auto.
    + intros m fuel (Hlv & Hax & Hcl & Hkept).
      apply rule_let with (classes := classes) (xs := [WPtr p; WPtr ep; WPtr np]);
        [reflexivity | exact Hc | exact Hx |]. rewrite (Hop m Hlv Hax Hcl Hkept); rewrite ?Eq; reflexivity.
    + iNext. iIntros "(Hl & Hc & Hcap)". iApply ("HK" with "Hl Hc Hcap").
Qed.

(** A raw long store replaces an owned integer cell and returns
    ownership of the updated eight bytes through [wp_raw_store].
    The caller also supplies the object's lifetime and proves that
    this update preserves the external-world interpretation. *)
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

(** A plain pointer store replaces both the address bytes and shadow
    capability of an aligned owned pointer cell.
    The rule [wp_raw_store_pointer] returns ownership of the newly stored
    pointer and requires the update to preserve the external-world interpretation. *)
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

(** Freeing null changes no memory for either deallocation symbol
    recognized by the model, as [wp_free_null_sym] proves from the deallocator's contract. *)
Lemma wp_free_null_sym fnm f e ls l v rest j Φ :
  is_free_name fnm = true ->
  frees_heap (ge_free ge) -> find_fn ge fnm = None -> lookup fnm (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr null) ->
  ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global fnm) [Arg P v] :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hfnm [Hnull _] Hfn Hdata Hx. apply (wp_pure_next _ _ []). intros m fuel.
  exact (rule_free_sym _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfnm Hfn Hdata Hx (Hnull m)).
Qed.

(** Freeing a nonnull heap object's base consumes its lifetime
    ownership and records the object as freed in the logical memory map.
    The rule [wp_free_sym] covers either recognized deallocation symbol
    and requires the deallocator's contract plus preservation of the external-world interpretation.
    Any retained byte or shadow assertions remain valid, but without
    live-object ownership they cannot justify further accesses to that object. *)
Lemma wp_free_sym fnm f e ls l v rest j b reg Φ :
  is_free_name fnm = true ->
  frees_heap (ge_free ge) -> find_fn ge fnm = None -> lookup fnm (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr (mkPtr b (Obj b))) -> r_kind reg = Heap -> b <> 0 ->
  (forall m wd h rs, h !! PLive b = Some (VLive reg) ->
     replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs -> wi m wd h ->
     wi (mkMem (m_bytes m) rs (m_aux m)) wd (overwrite [(PLive b, VFreed)] h)) ->
  live b reg -∗ ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global fnm) [Arg P v] :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hfnm [_ Hfh] Hfn Hdata Hx Hk Hb Hwi. iIntros "Hl HK". iCombine "Hl HK" as "H".
  iApply (wp_lift_run with "H").
  - iIntros (σ) "Hσ [Hl _]". iDestruct (pts_facts with "Hσ Hl") as %(Hf & _). iPureIntro.
    cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [Hlv _].
    destruct (Hfh _ _ _ Hlv Hk Hb) as (rs & _ & Hfree). left. unfold fails.
    rewrite (rule_free_sym _ _ _ _ _ _ _ _ _ [] _ (ls_fuel σ) _ _ Hfnm Hfn Hdata Hx Hfree). auto.
  - iIntros ([m s fuel w]) "Hσ [Hl HK]". iDestruct (pts_facts with "Hσ Hl") as %(Hf & _).
    cbn [ls_mem ls_rt ls_fuel ls_world all_agree agree_piece fst snd] in *. destruct Hf as [Hlv _].
    destruct (Hfh _ _ _ Hlv Hk Hb) as (rs & Hrs & Hfree).
    pose proof (rule_free_sym ge fnm f e ls l v rest j [] m fuel _ _ Hfnm Hfn Hdata Hx Hfree) as E.
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

(** A call to the ordinary free symbol on null uses [wp_free_null],
    which specializes the symbol-independent rule without requiring memory ownership. *)
Lemma wp_free_null f e ls l v rest j Φ :
  frees_heap (ge_free ge) -> find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr null) ->
  ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j)) : lexpr)
    {{ Φ }}.
Proof. apply wp_free_null_sym. reflexivity. Qed.

(** After freeing a heap object, a caller loses permission to access
    it because the object is no longer alive.
    The rule [wp_free] consumes lifetime ownership for the ordinary
    free symbol, using the more general deallocation rule. *)
Lemma wp_free f e ls l v rest j b reg Φ :
  frees_heap (ge_free ge) -> find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr (mkPtr b (Obj b))) -> r_kind reg = Heap -> b <> 0 ->
  (forall m wd h rs, h !! PLive b = Some (VLive reg) ->
     replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs -> wi m wd h ->
     wi (mkMem (m_bytes m) rs (m_aux m)) wd (overwrite [(PLive b, VFreed)] h)) ->
  live b reg -∗ ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j)) : lexpr)
    {{ Φ }}.
Proof. apply wp_free_sym. reflexivity. Qed.

(** A raw byte store replaces one owned byte with the integer's low
    byte and returns the updated ownership through [wp_raw_store_byte].
    The caller retains the object's lifetime and proves that changing
    this byte preserves the interpretation of external-library state. *)
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

(** A successful heap allocation returns ownership of the fresh object
    and its base pointer, together with positive-base, alignment, and address-space bounds.
    The rule [wp_alloc] covers nonnegative sizes within Fil-C's limit
    and every [[fresh]] base that the runtime may choose.
    Adding the new object's pieces must preserve the external-world
    interpretation; an allocator refusal stalls without requiring a returning continuation. *)
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

(** An oversized allocation ends with a permitted refusal rather than
    a safety failure, so [wp_alloc_any] needs no upper size bound.
    Nonnegative sizes that can return still provide fresh-object
    ownership, while requests beyond Fil-C's limit require no returning continuation. *)
Lemma wp_alloc_any f e ls l d k al args rest j size Φ :
  map2_option (value_x ge e) [L] args = Some [WInt size] -> 0 <= size ->
  (forall m wd h base, fresh m (heap_req al size) base -> wi m wd h ->
     wi (allocated m (heap_req al size) base) wd (overwrite (obj_ps base (heap_req al size)) h)) ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align (heap_req al size) = 0 /\
              base + req_extent (heap_req al size) <= 2 ^ 48⌝ -∗ obj base (heap_req al size) -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec l rest j)) : lexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hx Hs0 Hwi. iIntros "HK".
  destruct (Z_le_gt_dec size max_allocation_size) as [Hs | Hs];
    [iApply (wp_alloc with "HK"); assumption|].
  pose proof (fun m fuel => rule_alloc_too_big ge f e ls l d k al args rest j [] m fuel size Hx
    ltac:(lia)) as Hst.
  iApply (wp_lift_run with "HK").
  - iIntros (σ) "_ _". iPureIntro. left. unfold fails. rewrite Hst. cbn. intros H. apply H. by right.
  - iIntros (σ) "_ _". iNext. iIntros (e2 σ2 Hm). exfalso.
    destruct (moves_core _ _ _ _ Hm ltac:(intros ?; rewrite Hst; discriminate))
      as [(c' & E' & _) | [(q & kk & base & s' & E' & _) | (o & m' & E' & Hr & _)]];
      rewrite Hst in E'; try discriminate E'. injection E' as <-. exact Hr.
Qed.

(** A [[flight]] computes its address from integer arguments and takes
    its capability from a separate source, as [wp_flight] records in the result. *)
Lemma wp_flight f e ls l d o args lw rest j xs n c Φ :
  map_option (flight_arg_x ge e) args = Some xs -> alu o L xs = Some (WInt n) ->
  flight_cap ge e lw = Some c ->
  ▷ WP (ERun (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hx Ha Hc. apply (wp_pure_next _ _ []).
  intros m fuel. exact (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Ha Hc).
Qed.

(** Changing the execution budget leaves memory ownership valid because
    [heap_interp_fuel] shows that the memory interpretation does not inspect fuel. *)
Lemma heap_interp_fuel m s fuel fuel' w :
  heap_interp (mkLstate m s fuel w) -∗ heap_interp (mkLstate m s fuel' w).
Proof. rewrite /heap_interp /=. iIntros "H". iExact "H". Qed.

(** Entering a block selects its [[phi|phi arguments]] from the incoming
    edge and starts its instructions in the resulting environment.
    The rule [wp_enter] handles exhausted fuel as a permitted stall,
    so the continuation describes only execution that enters the block. *)
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

(** An unconditional jump enters its target block from the current
    label, with [wp_goto] handling both polling and nonpolling target edges. *)
Lemma wp_goto f e ls l t Φ :
  ▷ WP (ERun (mkFrame f e ls None (Enter (edge_label t) (Some l))) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l [] (JGoto t))) : lexpr) {{ Φ }}.
Proof. apply (wp_pure_next _ _ []). intros m fuel. apply rule_goto. Qed.

(** A conditional branch selects the second target for zero and the
    first otherwise, as [wp_branch] records using the evaluated integer condition. *)
Lemma wp_branch f e ls l v t1 t2 n Φ :
  value_x ge e W v = Some (WInt n) ->
  ▷ WP (ERun (mkFrame f e ls None (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) : lexpr)
      {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) : lexpr) {{ Φ }}.
Proof.
  intros Hv. apply (wp_pure_next _ _ []).
  intros m fuel. exact (rule_branch _ _ _ _ _ _ _ _ _ _ _ _ Hv).
Qed.

(** Returning a value from a function with no named stack locals
    produces that value's outcome once the promised postcondition is established. *)
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

(** Returning from a void function with no named stack locals produces
    [RetVoid], provided that the continuation's postcondition holds for that outcome. *)
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

(** Calling a function defined in the module creates its frame from
    the evaluated arguments and suspends the caller at its continuation.
    The rule [wp_call] places that callee beneath a waiting caller
    that records where to bind the returned result. *)
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

(** An accepted return resumes its waiting caller with the converted
    result, as [wp_resume] reduces the proof to that caller's continuation. *)
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

(** A caller waiting for its callee forms an evaluation context,
    allowing Iris's binding rule to focus on the callee's execution. *)
Local Instance wait_ctx cf pd : LanguageCtx (Λ := nanofil_lang registry ge) (fun e => EWait e cf pd).
Proof. exact (ectxi_lang_ctx_item (Λ := nanofil_ectxi_lang registry ge) (KWait cf pd)). Qed.

(** A caller can use the callee's specification and then prove its
    own continuation for every returned outcome that it accepts.
    The rule [wp_call_bind] combines these proofs through the waiting
    caller, so function specifications need not mention the entire caller stack. *)
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

(** Checking a function pointer confirms the exact function address and
    binds the proven pointer, as [wp_check_function] packages the successful check. *)
Lemma wp_check_function f e ls l d v rest j p Φ :
  value_x ge e P v = Some (WPtr p) -> function_check_res ge p = Some ok ->
  ▷ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d F CheckFunction [v] :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hv Hc. apply (wp_pure_next _ _ []).
  intros m fuel. exact (rule_check_function _ _ _ _ _ _ _ _ _ _ _ _ _ Hv Hc).
Qed.

(** Calling through a proven function pointer converts the arguments
    for the [[fast-generic-convention|generic entry]] and saves any required return conversion.
    The rule [wp_raw_call] then runs the constructed callee beneath
    the suspended caller, preserving extra arguments for a variadic function. *)
Lemma wp_raw_call f e ls l r callee args rest j p g xs gf ys words fr' Φ :
  value_x ge e F callee = Some (WPtr p) -> ptr_cap p = Fn g -> function_check_res ge p = Some ok ->
  map_option (arg_x ge e) args = Some xs -> find_fn ge g = Some (Defined gf) ->
  indirect_call_conv gf r args xs = Some (Converted ys words) ->
  call_frame gf (ys ++ (if variadic_func gf then skipn (length (fn_params gf)) xs else [])) = Some fr' ->
  ▷ WP (EWait (ERun fr') (mkFrame f e ls None (Exec l rest j)) (mkPending r words) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawCall r callee args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hv Hp Hc Hx Hf Hcv Hfr.
  apply (wp_pure_next _ fr' [(mkFrame f e ls None (Exec l rest j), mkPending r words)]).
  intros m fuel. exact (rule_raw_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv Hp Hc Hx Hf Hcv Hfr).
Qed.

(** An indirect caller can use its callee's specification just like a
    direct caller, while accounting for argument and result conversions.
    The rule [wp_raw_call_bind] combines the callee's proof with a
    continuation for every accepted, converted result. *)
Lemma wp_raw_call_bind f e ls l r callee args rest j p g xs gf ys words fr' Φ :
  value_x ge e F callee = Some (WPtr p) -> ptr_cap p = Fn g -> function_check_res ge p = Some ok ->
  map_option (arg_x ge e) args = Some xs -> find_fn ge g = Some (Defined gf) ->
  indirect_call_conv gf r args xs = Some (Converted ys words) ->
  call_frame gf (ys ++ (if variadic_func gf then skipn (length (fn_params gf)) xs else [])) = Some fr' ->
  ▷ WP (ERun fr' : lexpr) {{ o, ∃ cf', ⌜resume (mkFrame f e ls None (Exec l rest j)) (mkPending r words) o
                                         = Some cf'⌝ ∗ ▷ WP (ERun cf' : lexpr) {{ Φ }} }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawCall r callee args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros Hv Hp Hc Hx Hf Hcv Hfr. iIntros "H".
  iApply (wp_raw_call with "[H]"); [exact Hv|exact Hp|exact Hc|exact Hx|exact Hf|exact Hcv|exact Hfr|].
  iNext. iApply (wp_bind (fun ex => EWait ex (mkFrame f e ls None (Exec l rest j)) (mkPending r words))
                   NotStuck ⊤ (ERun fr' : lexpr)).
  iApply (wp_mono with "H"). iIntros (o) "H". iDestruct "H" as (cf') "[%Hr H]".
  iApply (wp_resume _ _ _ _ _ Hr with "H").
Qed.

(** An [[external-call|external call]] uses a registered contract rather
    than a function body, provided its arguments and calling convention match.
    The rule [wp_external] requires the supplied ownership Q to
    establish the contract's precondition together with the memory interpretation.

    A returning library call may change memory or allocate an object,
    and its proof must account for every result the contract permits.
    The proof updates the ownership map to match those effects and
    reestablishes the relationship between memory and library state.
    It must then show that the caller accepts the returned words and
    can safely execute its remaining instructions.

    A call that exits the process, blocks, or refuses a resource does
    not return, so the proof need not establish a safe continuation.
    The language represents these permitted endings as stalls, as it
    does for a permitted call with no completed invocation.
    A safepoint before the call preserves Q, and the proof establishes
    the precondition again in the resulting memory. *)
Lemma wp_external f e ls lab r g args rest j spec xs (Q : iProp Σ) Φ :
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
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

    A library call may perform many writes and allocations, but it
    must preserve program-owned memory outside the buffers explicitly lent to it.
    The following lemmas extend the single-effect restrictions from
    [ContractFrame](ContractFrame.v) across an entire call, retaining ownership of untouched pieces. *)

(** Every memory piece in the logical map must name an already
    registered object, which [ids_registered] requires even for pieces lent to a call. *)
Definition ids_registered (h : gmap piece pval) (m : mem) : Prop :=
  forall l v, h !! l = Some v -> mem_piece l -> registered m (piece_id l).

(** A call may write buffers explicitly lent by the program, while
    every other owned piece must continue to match memory.
    The theorem [effects_agrees_out] tracks those exceptions through
    the effect path, retaining their object identities rather than their previous contents.
    Writable roots must touch program-owned objects only at the lent
    addresses, and the call may release none of the program's owned identities. *)
Theorem effects_agrees_out : forall sources roots releases requests s m born0 s' m' born h ks out,
  M.E.effects sources roots releases requests s m born0 s' m' born ->
  R.ready s m -> live_disjoint m -> agrees_except ks m h -> ids_registered h m ->
  roots_out roots h m out -> pieces_off ks h m out -> ids_apart releases h -> ids_apart born0 h ->
  agrees_except ks m' h /\ ids_registered h m' /\ live_disjoint m' /\ ids_apart born h /\
  roots_out roots h m' out.
Proof.
  intros sources roots releases requests s m born0 s' m' born h ks out H.
  induction H as [s m born0 | s m born0 m1 s' m' born Hl H IH
                 | s m born0 align size base s1 s' m' born Hq Hsize Halloc H IH];
    intros Hr Hd Ha Hids Hra Hoff Hrel Hb.
  - auto.
  - apply IH.
    + exact (R.ready_kept _ _ _ Hr (local_effect_kept _ _ _ _ _ _ Hl)).
    + exact (local_live_disjoint _ _ _ _ _ _ Hl Hd).
    + exact (local_agrees_out _ _ _ _ _ _ h Hl ks out Hd Ha Hra Hoff Hrel Hb).
    + intros l v Hh Hm. pose proof (Hids l v Hh Hm) as Hreg. unfold registered in *.
      destruct (object_region (piece_id l) (m_regions m)) as [reg|] eqn:E; [|contradiction].
      destruct (proj1 Hl _ _ E) as [reg' ->]. discriminate.
    + intros sp a Hin Hs Ho. exact (Hra sp a Hin Hs (local_owned_back _ _ _ _ _ _ h Hl a Ho)).
    + intros l v Hh Hk. pose proof (Hoff l v Hh Hk) as Ho.
      destruct l as [b|b o|b o|k]; try exact I;
        intros reg Hlive; exact (Ho reg (local_live_back _ _ _ _ _ _ Hl _ _ Hlive)).
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
    + intros l v Hh Hk. exact (agree_piece_allocated _ _ _ _ _ Hn (Ha l v Hh Hk)).
    + intros l v Hh Hm.
      exact (agree_piece_allocated _ _ _ (PLive (piece_id l)) VFreed Hn (Hids l v Hh Hm)).
    + intros sp a Hin Hs (l & v & reg & Hh & Hm & Hlive & Hrr). apply (Hra sp a Hin Hs).
      exists l, v, reg. split; [exact Hh|]. split; [exact Hm|]. split; [|exact Hrr].
      apply (allocated_live_back m (heap_req align size) base); [|exact Hlive].
      intros E. apply (Hids l v Hh Hm). rewrite <- E. exact Hn.
    + intros l v Hh Hk. pose proof (Hoff l v Hh Hk) as Ho.
      destruct l as [b|b o|b o|k]; try exact I; intros reg Hlive;
        assert (Hne : base <> b) by (intros E; apply (Hids _ v Hh I); cbn [piece_id]; rewrite <- E; exact Hn);
        exact (Ho reg (allocated_live_back _ _ _ _ _ Hne Hlive)).
    + exact Hrel.
    + intros b l v [<- | Hin] Hh Hm.
      * intros E. apply (Hids l v Hh Hm). rewrite E. exact Hn.
      * exact (Hb b l v Hin Hh Hm).
Qed.

(** A library cannot disturb the caller's objects if its writable
    arguments cannot reach them and it has no permission to release them.
    The theorem [effects_agrees] preserves ownership under those
    restrictions, keeping live objects disjoint and newly allocated identities separate from existing pieces.
    Any objects allocated earlier during the call must already be
    separate; at the start of a call, that list is empty. *)
Theorem effects_agrees : forall sources roots releases requests s m born0 s' m' born h,
  M.E.effects sources roots releases requests s m born0 s' m' born ->
  R.ready s m -> live_disjoint m -> agrees m h -> roots_apart roots h m ->
  ids_apart releases h -> ids_apart born0 h ->
  agrees m' h /\ live_disjoint m' /\ ids_apart born h /\ roots_apart roots h m'.
Proof.
  intros sources roots releases requests s m born0 s' m' born h H Hr Hd Ha Hra Hrel Hb.
  assert (Hx : agrees_except [] m h) by (intros l v Hh _; exact (Ha l v Hh)).
  assert (Hids : ids_registered h m) by (intros l v Hh Hm; exact (agree_piece_registered m l v Hm (Ha l v Hh))).
  assert (Hoff : pieces_off [] h m (fun _ => False)) by (intros l v _ _; destruct l; auto).
  destruct (effects_agrees_out _ _ _ _ _ _ _ _ _ _ h [] (fun _ => False) H Hr Hd Hx Hids
              (roots_out_apart _ _ _ Hra) Hoff Hrel Hb) as (Ha' & _ & Hd' & Hb' & Hra').
  split; [intros l v Hh; exact (Ha' l v Hh (not_elem_of_nil _))|].
  split; [exact Hd'|]. split; [exact Hb'|]. intros sp a Hin Hs Ho. exact (Hra' sp a Hin Hs Ho).
Qed.

(** A whole contract prefix preserves program ownership when its writes
    avoid owned live objects and its releases avoid their identities.
    The corollary [prefix_agrees] also keeps newly allocated objects
    separate and preserves the separation of writable roots from program objects. *)
Corollary prefix_agrees : forall world (spec : contract world) xs s m w born trace s' m' w' h,
  M.E.prefix spec xs s m w born trace s' m' w' -> R.ready s m -> live_disjoint m -> agrees m h ->
  roots_apart (contract_writes spec xs m w) h m -> ids_apart (contract_releases spec xs m w) h ->
  agrees m' h /\ live_disjoint m' /\ ids_apart born h /\ roots_apart (contract_writes spec xs m w) h m'.
Proof.
  intros world spec xs s m w born trace s' m' w' h [He _] Hr Hd Ha Hra Hrel.
  apply (effects_agrees _ _ _ _ _ _ _ _ _ _ h He Hr Hd Ha Hra Hrel). intros b l v [].
Qed.

(** A contract prefix that writes explicitly lent buffers preserves
    every other owned piece and keeps the lent objects' identities registered.
    The corollary [prefix_agrees_out] requires writable roots to touch
    program-owned objects only at those permitted addresses. *)
Corollary prefix_agrees_out : forall world (spec : contract world) xs s m w born trace s' m' w' h ks out,
  M.E.prefix spec xs s m w born trace s' m' w' -> R.ready s m -> live_disjoint m ->
  agrees_except ks m h -> ids_registered h m ->
  roots_out (contract_writes spec xs m w) h m out -> pieces_off ks h m out ->
  ids_apart (contract_releases spec xs m w) h ->
  agrees_except ks m' h /\ ids_registered h m' /\ live_disjoint m' /\ ids_apart born h.
Proof.
  intros world spec xs s m w born trace s' m' w' h ks out [He _] Hr Hd Ha Hids Hra Hoff Hrel.
  destruct (effects_agrees_out _ _ _ _ _ _ _ _ _ _ h ks out He Hr Hd Ha Hids Hra Hoff Hrel
              ltac:(intros ? ? ? [])) as (Ha' & Hids' & Hd' & Hb & _).
  auto.
Qed.

(** A completed invocation preserves separated program ownership for
    every permitted ending, with [invoke_agrees] identifying its newly allocated objects as separate too. *)
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

(** A program with no external-library state can use [no_world], whose
    interpretation places no extra requirements on memory or the logical ownership map. *)
Definition no_world : mem -> unit -> gmap piece pval -> Prop := fun _ _ _ => True.

(** A closed program has no library state to protect when garbage
    collection runs, so this additional safepoint obligation is immediate.
    The instance [no_world_stable] supplies that fact to the instruction
    rules using the empty interpretation of external state. *)
Instance no_world_stable : SafepointStable no_world.
Proof. split. intros s m s' m' w h _ _. exact I. Qed.

(** A closed module uses [closed_irisGS] to select an empty external
    contract registry and a world interpretation with no additional memory requirements. *)
Instance closed_irisGS `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (ge : genv) :
  irisGS_gen hlc (nanofil_lang no_contracts ge) Σ := nanofil_irisGS no_contracts no_world ge.

(** A closed module never panics when its entry proof covers every
    admitted input without assuming ownership of any initial memory pieces.
    The theorem [heap_never_panics] allocates an empty logical ownership
    map and requires the initial memory's live objects to be disjoint.
    The entry proof must work for every Iris invariant and heap
    instance, with no external contracts available. *)
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

(** A program reading initialized global data needs ownership of those
    bytes before its entry function can prove the loads safe.
    The theorem [pieces_never_panics] provides selected initial memory
    pieces, provided their keys are distinct and their recorded values match memory.
    The entry proof must cover every admitted input and use no
    external contracts, while initial live objects must be disjoint.
    It must also work with every choice of Iris invariant and heap
    instance, so the result does not depend on a particular logical allocation. *)
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

(** A program using external contracts is safe when its entry proof
    establishes safe execution and the promised return property from its initial ownership.
    The theorem [heap_labelled_safe] supplies a logical map matching
    initial memory, a [[ready]] runtime, disjoint live objects, and a valid external-world interpretation.
    Given the entry proof for every Iris invariant and heap instance,
    it excludes failure endings for every execution budget.
    Whenever a run returns normally at the top level, its returned
    outcome also satisfies the entry proof's promised postcondition. *)
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

(** All higher proof layers must share one program-logic instance so
    their expressions, states, and assertions refer to the same types.
    The signature [LogicSig] lets a program supply that instance rather
    than have each layer construct a distinct one. *)
Module Type LogicSig (R : Runtime).
Include Logic R.
End LogicSig.
