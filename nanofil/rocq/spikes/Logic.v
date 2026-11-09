(** Spike: the program logic of nanofil's core [[machine]] on the
    language of Language.v, whose evaluation context is the stack of
    callers: a ghost heap of pieces as Iris's state interpretation, a
    small assertion vocabulary over it, and one weakest-precondition
    rule per instruction form, each the lifted reading of its rule in
    StepRules.v.

    The ghost heap is IrisHeap.v's: Iris's [gen_heap] from Pieces.v's
    pieces to their values, which [heap_interp] keeps in agreement with
    the memory. The vocabulary is [live] (an object's life), [icell] (an
    8-byte integer in an object), [pcell] (a pointer stored in an
    object, its address bytes and its [[aux]] capability), [obj] (a new
    object's pieces) and [live_cap] (the life of the object a
    capability names, if any).

    Every rule for a running frame comes from one lifting lemma,
    [wp_lift_run]. A [[poll|safepoint]] and a stall (out of [[fuel]], a
    refusal trap, an allocation the runtime refuses) step [ERun fr] to
    itself,
    the first changing memory only as [SS.keeps_live] allows, which
    keeps [heap_interp] with the same ghost heap: the lemma closes both
    by Löb induction, so a rule speaks only of the step its instruction
    takes. A call is [wp_bind] over the caller ([wp_call_bind]), so a
    function's specification is an ordinary Hoare triple.
    [heap_never_panics] is Language.v's [[adequacy]] with the ghost heap
    allocated. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language ectx_language ectxi_language weakestpre lifting
  ectx_lifting adequacy.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls Ops Semantics Run
  Machine Panics StepRules.
From Spike Require Import Pieces IrisHeap Language.
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
    nothing else changes. IrisHeap.v's [ptr_store_ok] at any offset. *)
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

(** The ghost heap, the assertions and the rules over the runtime R. *)
Module Logic (R : Runtime).
Module L := Language R.
Module SS := SafepointShape R.
Module IH := IrisHeap R.
Module P := L.P.
Module RM := L.RM.
Import L.

(** The Iris state is inhabited, as the lifting lemmas of an
    evaluation-context language ask. *)
Global Instance lstate_inhabited : Inhabited lstate := populate (mkLstate empty_mem R.start 0).

Section logic.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The state interpretation of the Iris state σ: the authoritative
    ghost heap h, which [agrees] with σ's memory, the live objects
    apart, and the runtime ready. The [[fuel]] is unconstrained. *)
Definition heap_interp (σ : lstate) : iProp Σ :=
  ∃ h : gmap piece pval, gen_heap_interp h ∗
    ⌜agrees (ls_mem σ) h /\ live_disjoint (ls_mem σ) /\ R.ready (ls_rt σ) (ls_mem σ)⌝.

(** The Iris instance of the genv ge: [heap_interp] as the state
    interpretation, no forks to speak of, one later per step. *)
Global Instance nanofil_irisGS (ge : genv) : irisGS_gen hlc (nanofil_lang ge) Σ :=
  IrisG _ (fun σ _ _ _ => heap_interp σ) (fun _ => True%I) (fun _ => 0%nat)
        (fun _ _ _ _ => fupd_intro _ _).

(** ## The assertions *)

(** [live] b reg: owning the life of the object of identity b, which is
    live with the region reg ([[live]]). *)
Definition live (b : Z) (reg : region) : iProp Σ := IH.pts [(PLive b, VLive reg)].

(** [icell] b o v: owning the 8 bytes at offset o of the object b,
    which hold the 64-bit integer v, little-endian. *)
Definition icell (b o v : Z) : iProp Σ := IH.pts (cell b o v).

(** [pcell] b o x: owning the pointer x stored at offset o of the
    object b: the 8 bytes of its address and the [[aux]] slot holding
    its capability. *)
Definition pcell (b o : Z) (x : ptr) : iProp Σ :=
  IH.pts ((PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)).

(** [obj] b q: owning every piece of the object of identity b just
    allocated for the request q: its life, a zero byte and an empty aux
    slot at each offset. *)
Definition obj (b : Z) (q : alloc_req) : iProp Σ := IH.pts (obj_ps b q).

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
Lemma pts_facts σ ps : heap_interp σ -∗ IH.pts ps -∗ ⌜owned_facts ps (ls_mem σ)⌝.
Proof.
  iIntros "Hσ Hps". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr).
  iDestruct (IH.pts_lookup with "Hh Hps") as %Hl. iPureIntro.
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

(** What R does at a safepoint, under [keeps_live], keeps the state
    interpretation, with the same ghost heap. *)
Lemma heap_interp_safepoint m s fuel m' s' :
  SS.keeps_live -> R.safepoint s m s' m' ->
  heap_interp (mkLstate m s fuel) -∗ heap_interp (mkLstate m' s' fuel).
Proof.
  intros HK Hsp. iIntros "Hσ". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr).
  iExists h. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt] in *.
  destruct (SS.safepoint_shape HK _ _ _ _ Hsp) as (Hreg & Hb & Haux).
  split; [|split].
  - intros l v Hl. exact (agree_piece_safepoint _ _ _ _ Hreg Hb Haux (Ha l v Hl)).
  - exact (SS.live_disjoint_safepoint HK _ _ _ _ Hsp Hd).
  - exact (R.safepoint_ready _ _ _ _ Hsp Hr).
Qed.

Section wp.
Context (ge : genv).
Implicit Types Φ : outcome -> iProp Σ.

(** The expressions of the language of ge. *)
Local Notation lexpr := (language.expr (nanofil_lang ge)).

(** The steps of [ERun fr] in σ that move on, to e2 and σ2: a step to
    the next configuration, an allocation R grants, or a return, the
    cases of [head_step_run_inv] that are neither a stall nor a
    safepoint. *)
Definition moves (fr : frame) (σ : lstate) (e2 : expr) (σ2 : lstate) : Prop :=
  let c0 := mkConfig fr [] (ls_mem σ) (ls_fuel σ) in
  (exists c', Semantics.step ge c0 = Next c' /\ e2 = conf_expr c' /\ σ2 = conf_state c' (ls_rt σ)) \/
  (exists q k base s', Semantics.step ge c0 = Fresh q k /\ 0 <= req_extent q /\
     R.alloc (ls_rt σ) q = Some (base, s') /\ e2 = conf_expr (k base) /\ σ2 = conf_state (k base) s') \/
  (exists o m', Semantics.step ge c0 = Done o /\ returning o /\
     invalidate_locals (fr_locals fr) (ls_mem σ) = Some m' /\
     e2 = EEnd o /\ σ2 = mkLstate m' (ls_rt σ) (ls_fuel σ)).

(** The lifting lemma every rule for a running frame comes from. [ERun
    fr] is safe, given Q, if Q and the state interpretation show fr
    does not [fails], and if, after any step that [moves], they give
    the state interpretation and the weakest precondition of what
    follows. A stall leaves the expression and the state as they are; a
    safepoint leaves the expression and, under [keeps_live], the state
    interpretation: both cases are closed by Löb induction, keeping Q. *)
Lemma wp_lift_run (Q : iProp Σ) fr Φ :
  SS.keeps_live ->
  (forall σ, heap_interp σ -∗ Q -∗ ⌜~ fails ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ))⌝) ->
  (forall σ, heap_interp σ -∗ Q -∗
     ▷ ∀ e2 σ2, ⌜moves fr σ e2 σ2⌝ ==∗ heap_interp σ2 ∗ WP (e2 : lexpr) {{ Φ }}) ->
  Q -∗ WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros HK Hnf Hst. iLöb as "IH". iIntros "HQ".
  iApply wp_lift_base_step; [done|].
  iIntros (σ ns κ κs nt) "Hσ".
  iDestruct (Hnf with "Hσ HQ") as %Hnf'.
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplitR; [iPureIntro; by apply run_reducible|].
  iAssert ((▷ ∀ e2 σ2, ⌜moves fr σ e2 σ2⌝ ==∗ heap_interp σ2 ∗ WP (e2 : lexpr) {{ Φ }})
           ∧ (heap_interp σ ∗ Q))%I with "[Hσ HQ]" as "H".
  { iSplit; [iApply (Hst with "Hσ HQ") | iFrame]. }
  iNext. iIntros (e2 σ2 efs Hstep) "_". iMod "Hclose" as "_".
  destruct (head_step_run_inv _ _ _ _ _ _ _ Hstep) as (_ & -> & Hc).
  destruct Hc as [Hn | [Ha | [(q & k & _ & _ & _ & -> & ->) | [Hr | [(o & _ & _ & _ & -> & ->) |
    (s' & m' & _ & _ & Hsp & -> & ->)]]]]].
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by left|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by (right; left)|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. iFrame "Hσ". iSplitL; [iApply ("IH" with "HQ")|done].
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by (right; right)|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. iFrame "Hσ". iSplitL; [iApply ("IH" with "HQ")|done].
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. destruct σ as [m s fuel].
    iSplitL "Hσ"; [iApply (heap_interp_safepoint with "Hσ"); [exact HK|exact Hsp]|].
    iSplitL; [iApply ("IH" with "HQ")|done].
Qed.

(** A step to the next configuration, with the callers cs' below its
    frame, that writes memory: owning the pieces ps, where every memory
    m those pieces agree with steps to [upd] m, keeping its regions,
    [kept], agreeing with the new values ps' (the same keys) and
    changing nothing outside them. The new pieces are handed on. *)
Lemma wp_write ps ps' fr fr' cs' (upd : mem -> mem) Φ :
  SS.keeps_live -> ps'.*1 = ps.*1 ->
  (forall m fuel, owned_facts ps m ->
     Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' (upd m) fuel) /\
     m_regions (upd m) = m_regions m /\ kept m (upd m) /\
     all_agree (upd m) ps' /\ frame_ok ps'.*1 m (upd m)) ->
  IH.pts ps -∗ ▷ (IH.pts ps' -∗ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }}) -∗
  WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros HK Hk Hs. iIntros "Hps HK". iCombine "Hps HK" as "H".
  iApply (wp_lift_run with "H"); [exact HK| |].
  - iIntros (σ) "Hσ [Hps _]". iDestruct (pts_facts with "Hσ Hps") as %Hf. iPureIntro.
    destruct (Hs _ (ls_fuel σ) Hf) as (E & _). unfold fails. rewrite E. auto.
  - iIntros ([m s fuel]) "Hσ [Hps HK]". iDestruct (pts_facts with "Hσ Hps") as %Hf.
    cbn [ls_mem ls_rt ls_fuel] in *.
    destruct (Hs m fuel Hf) as (E & Hreg & Hkept & Hag & Hfr). iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & E' & -> & ->) | [(q & k & b & s' & E' & _) | (o & m' & E' & _)]];
      cbn [ls_mem ls_fuel ls_rt] in E'; rewrite E in E'; try discriminate E'.
    injection E' as <-. cbn [conf_expr conf_state c_frame c_callers c_mem c_fuel].
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr). cbn [ls_mem ls_rt] in Ha, Hd, Hr.
    iMod (IH.pts_update with "Hh Hps") as "[Hh Hps]"; [exact Hk|].
    iModIntro. iSplitL "Hh".
    + iExists (overwrite ps' h). iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt]. split; [|split].
      * intros l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [Hn Hh]].
        -- exact (all_agree_elem _ _ _ _ Hag Hin).
        -- exact (Hfr l v Hn (Ha l v Hh)).
      * exact (live_disjoint_regions _ _ Hreg Hd).
      * exact (R.ready_kept _ _ _ Hr Hkept).
    + iApply ("HK" with "Hps").
Qed.

(** A step to the next configuration, with the callers cs' below its
    frame, that reads the pieces ps and changes no memory: they are
    handed back. *)
Lemma wp_read ps fr fr' cs' Φ :
  SS.keeps_live ->
  (forall m fuel, owned_facts ps m ->
     Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' m fuel)) ->
  IH.pts ps -∗ ▷ (IH.pts ps -∗ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }}) -∗
  WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros HK Hs. apply (wp_write ps ps fr fr' cs' (fun m => m)); [exact HK|reflexivity|].
  intros m fuel Hf. split; [exact (Hs m fuel Hf)|]. split; [reflexivity|]. split; [apply kept_refl|].
  split; [exact (proj1 Hf)|]. intros l v _ H. exact H.
Qed.

(** A step to the next configuration, with the callers cs' below its
    frame, that needs no resource and changes no memory. *)
Lemma wp_pure_next fr fr' cs' Φ :
  SS.keeps_live ->
  (forall m fuel, Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' m fuel)) ->
  ▷ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }} -∗ WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros HK Hs. iIntros "H". iApply (wp_read [] fr fr' cs' with "[] [H]"); [exact HK| |by rewrite /IH.pts|].
  - intros m fuel _. apply Hs.
  - iNext. iIntros "_". iExact "H".
Qed.

(** ## The rules *)

(** A [let] of a general op o whose arguments read as xs and whose
    [op_res] is the word w in any memory, leaving it: d is bound to w. *)
Lemma wp_let f e ls l d k o args rest j classes xs w Φ :
  SS.keeps_live ->
  general_op o = true -> op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal w) m)) ->
  ▷ WP (ERun (mkFrame f (put d w e) ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hg Hc Hx Ho. apply (wp_pure_next _ _ []); [exact HK|].
  intros m fuel. exact (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hc Hx (Ho m)).
Qed.

(** A [[check]] of the pointer p, through the capability of the live
    object b with the region reg, whose checked bytes lie in its bounds
    and are aligned: d is bound to p, proven. *)
Lemma wp_check f e ls l d lo hi r al args rest j classes p b reg Φ :
  SS.keeps_live ->
  op_arg_classes (Check lo hi r al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg -> raw_address (ptr_addr p) lo mod al = 0 ->
  live b reg -∗
  ▷ (live b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi r al) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hc Hx Hp H1 H2 H3. apply (wp_read _ _ _ []); [exact HK|].
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_check. rewrite Hp. exact (access_obj _ _ _ _ _ _ _ E H1 H2 H3).
Qed.

(** A [[half_check]] of the pointer p, against the proof p1 of the same
    capability, at the live object b with the region reg, ending at or
    below 2^63, whose checked bytes lie in its bounds and are aligned:
    d is bound to p, proven. *)
Lemma wp_half_check f e ls l d bd lo hi r al args rest j classes p1 p b reg Φ :
  SS.keeps_live ->
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
  intros HK Hc Hx Hp1 Hp H1 H2 H3 H4 H5. apply (wp_read _ _ _ []); [exact HK|].
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E Lv] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]);
    [reflexivity | exact Hc | exact Hx |].
  exact (op_half_check _ _ _ _ _ _ _ _ _ _ Hp1 Hp E Lv H1 H2 H3 H4 H5).
Qed.

(** A raw load of a long at offset off from the proven pointer p, which
    addresses offset o of the live object b, where the cell holds v: d
    is bound to v modulo 2^64. *)
Lemma wp_raw_load f e ls l d k off args rest j classes p b reg o v Φ :
  SS.keeps_live ->
  op_arg_classes (RawLoad LdL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o ->
  live b reg -∗ icell b o v -∗
  ▷ (live b reg -∗ icell b o v -∗
     WP (ERun (mkFrame f (put d (WInt (v mod 2 ^ 64)) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hc Hx Hp Ha. iIntros "Hl Hc HK".
  iApply (wp_read ([(PLive b, VLive reg)] ++ cell b o v) _ _ [] with "[Hl Hc] [HK]"); [exact HK| | |].
  - intros m fuel (Hf & _). apply all_agree_app in Hf as [[Hlv _] Hcl]. cbn [agree_piece fst snd] in Hlv.
    destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load m k p off).
    + rewrite Ha (cell_load m b reg o v (b + o) Hlv Hcl eq_refl). reflexivity.
    + rewrite Hp Ha. apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - rewrite IH.pts_app. iFrame.
  - iNext. iIntros "H". rewrite IH.pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A step to the next configuration, with the callers cs' below its
    frame, that changes no memory, where Q, with the state
    interpretation, shows the memory has the property F, and every
    memory with F steps there: Q is handed back. *)
Lemma wp_read_with (Q : iProp Σ) (F : mem -> Prop) fr fr' cs' Φ :
  SS.keeps_live ->
  (forall σ, heap_interp σ -∗ Q -∗ ⌜F (ls_mem σ)⌝) ->
  (forall m fuel, F m -> Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' cs' m fuel)) ->
  Q -∗ ▷ (Q -∗ WP (stack_expr (ERun fr') cs' : lexpr) {{ Φ }}) -∗ WP (ERun fr : lexpr) {{ Φ }}.
Proof.
  intros HK HF Hs. iIntros "HQ HK". iCombine "HQ HK" as "H".
  iApply (wp_lift_run with "H"); [exact HK| |].
  - iIntros (σ) "Hσ [HQ _]". iDestruct (HF with "Hσ HQ") as %Hf. iPureIntro.
    unfold fails. rewrite (Hs _ _ Hf). auto.
  - iIntros ([m s fuel]) "Hσ [HQ HK]". iDestruct (HF with "Hσ HQ") as %Hf. cbn [ls_mem] in Hf.
    iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & E' & -> & ->) | [(q & k & b & s' & E' & _) | (o & m' & E' & _)]];
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
  SS.keeps_live ->
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
  intros HK Hc Hx Hp Ha Hal Hrange. iIntros "Hl Hc Hcap HK".
  iApply (wp_read_with (live b reg ∗ pcell b o x ∗ live_cap (ptr_cap x) reg')
            (fun m => live_at m b reg /\ agree_piece m (PAux b o) (VAux (ptr_cap x)) /\
                      all_agree m (cell b o (ptr_addr x)) /\
                      (ptr_cap x = CNone \/ exists b' reg', ptr_cap x = Obj b' /\ live_at m b' reg'))
            _ _ [] with "[$Hl $Hc $Hcap] [HK]"); [exact HK| | |].
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
    object b at offset off: the cell there now holds v'. *)
Lemma wp_raw_store f e ls l off v a rest j p b reg o w w' Φ :
  SS.keeps_live ->
  value_x ge e L v = Some (WInt w') -> value_x ge e A a = Some (WPtr p) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o ->
  live b reg -∗ icell b o w -∗
  ▷ (live b reg -∗ icell b o w' -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Wl off v a :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hv Ha Hp Hoff. iIntros "Hl Hc HK".
  iApply (wp_write ([(PLive b, VLive reg)] ++ cell b o w) ([(PLive b, VLive reg)] ++ cell b o w')
            _ _ [] (fun m => store_bytes m (b + o) 8 w') with "[Hl Hc] [HK]");
    [exact HK | reflexivity | | rewrite IH.pts_app; iFrame |].
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
  - iNext. iIntros "H". rewrite IH.pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A raw pointer store by the plain protocol of the pointer xp, which
    v reads as, through the proven pointer p, which a reads as and
    which addresses the 8-aligned offset o of the live object b at
    offset off: the pointer cell there now holds xp. *)
Lemma wp_raw_store_pointer f e ls l off v a rest j xp p b reg o x Φ :
  SS.keeps_live ->
  value_x ge e P v = Some (WPtr xp) -> value_x ge e A a = Some (WPtr p) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  live b reg -∗ pcell b o x -∗
  ▷ (live b reg -∗ pcell b o xp -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
                :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hv Ha Hp Hoff Hal. iIntros "Hl Hc HK".
  iApply (wp_write ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x))
            ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp))
            _ _ [] (fun m => store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp))
            with "[Hl Hc] [HK]");
    [exact HK | reflexivity | | rewrite IH.pts_app; iFrame |].
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
  - iNext. iIntros "H". rewrite IH.pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** A heap allocation of size bytes, size read as the only argument,
    from 0 to Fil-C's limit: for every base the runtime may grant, d is
    bound to the new object's own pointer and its pieces are owned
    ([obj]); the base is positive, aligned and the object ends within
    the address space. A refusal stalls. *)
Lemma wp_alloc f e ls l d k al args rest j size Φ :
  SS.keeps_live ->
  map2_option (value_x ge e) [L] args = Some [WInt size] -> 0 <= size -> size <= max_allocation_size ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align (heap_req al size) = 0 /\
              base + req_extent (heap_req al size) <= 2 ^ 48⌝ -∗ obj base (heap_req al size) -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec l rest j)) : lexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hx Hs0 Hs. set (q := heap_req al size).
  assert (Hex : 0 <= req_extent q).
  { cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
  assert (Hal : 0 < req_align q) by (cbn; lia).
  pose proof (fun m fuel => rule_alloc ge f e ls l d k al args rest j [] m fuel size Hx Hs) as Hst.
  iIntros "HK". iApply (wp_lift_run with "HK"); [exact HK| |].
  - iIntros (σ) "_ _". iPureIntro. unfold fails. rewrite Hst. fold q. lia.
  - iIntros ([m s fuel]) "Hσ HK". iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & E' & _) | [(q' & kk & base & s' & E' & _ & Ha & -> & ->) | (o & m' & E' & _)]];
      cbn [ls_mem ls_fuel ls_rt] in E'; rewrite Hst in E'; try discriminate E'.
    injection E' as <- <-. cbn [conf_expr conf_state stack_expr c_frame c_callers c_mem c_fuel].
    fold q in Ha |- *.
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Hag & Hd & Hr). cbn [ls_mem ls_rt] in Hag, Hd, Hr.
    destruct (R.fresh_allocation _ _ _ _ _ Hr Hal Hex Ha) as [Hf Hr'].
    pose proof Hf as (Hpos & Hmod & _ & Hn & _).
    iMod (IH.pts_alloc h (obj_ps base q) with "Hh") as "[Hh Hps]".
    { apply obj_ps_nodup. }
    { intros l' v Hin. destruct (h !! l') as [v'|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (Hag l' v' E)) as Hreg.
      rewrite (obj_ps_id _ _ _ _ Hin) in Hreg. exact (Hreg Hn). }
    iModIntro. iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt]. split; [|split].
      * intros l' v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]].
        -- exact (obj_ps_agree _ _ _ _ _ Hf Hex Hin).
        -- exact (agree_piece_allocated _ _ _ _ _ Hn (Hag l' v Hh)).
      * exact (live_disjoint_allocated _ _ _ Hd Hf Hex).
      * exact Hr'.
    + iApply ("HK" with "[%] Hps"). split; [exact Hpos|]. split; [exact Hmod|].
      destruct (R.address_space _ _ Hr' base (mkRegion base (base + req_extent q) (req_kind q) Live))
        as [_ Hend]; [rewrite object_region_allocated Z.eqb_refl; reflexivity|].
      cbn [r_end] in Hend. exact Hend.
Qed.

(** A [[flight]] whose arguments read as xs, whose address [alu]
    computes as n, and whose capability source gives c: d is bound to
    the pointer of n and c. *)
Lemma wp_flight f e ls l d o args lw rest j xs n c Φ :
  SS.keeps_live ->
  map_option (flight_arg_x ge e) args = Some xs -> alu o L xs = Some (WInt n) ->
  flight_cap ge e lw = Some c ->
  ▷ WP (ERun (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hx Ha Hc. apply (wp_pure_next _ _ []); [exact HK|].
  intros m fuel. exact (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Ha Hc).
Qed.

(** The state interpretation does not read the [[fuel]]. *)
Lemma heap_interp_fuel m s fuel fuel' :
  heap_interp (mkLstate m s fuel) -∗ heap_interp (mkLstate m s fuel').
Proof. rewrite /heap_interp /=. iIntros "H". iExact "H". Qed.

(** Entering the block l of f, found as b, from the edge from: its phis
    bind the environment e', and the frame goes on at its instructions.
    With no [[fuel]] left the run stops there, a stall. *)
Lemma wp_enter f e ls l from b e' Φ :
  SS.keeps_live ->
  find_block l (fn_blocks f) = Some b -> phis_env ge (b_phis b) from e = Some e' ->
  ▷ WP (ERun (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Enter l from)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hb Hp. iIntros "H". iApply (wp_lift_run with "H"); [exact HK| |].
  - iIntros (σ) "_ _". iPureIntro. unfold fails.
    destruct (Z.eq_dec (ls_fuel σ) 0) as [Hz|Hz].
    + rewrite Hz rule_out_of_fuel. cbn. tauto.
    + rewrite (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hz Hb Hp). auto.
  - iIntros ([m s fuel]) "Hσ H". iNext. iIntros (e2 σ2 Hm).
    unfold moves in Hm. cbn [ls_mem ls_fuel ls_rt] in Hm.
    destruct (Z.eq_dec fuel 0) as [->|Hz].
    + exfalso. rewrite rule_out_of_fuel in Hm.
      destruct Hm as [(c' & E' & _) | [(q & k & base & s' & E' & _) | (o & m' & E' & Hr & _)]];
        try discriminate E'. injection E' as <-. exact Hr.
    + rewrite (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hz Hb Hp) in Hm.
      destruct Hm as [(c' & E' & -> & ->) | [(q & k & base & s' & E' & _) | (o & m' & E' & _)]];
        try discriminate E'.
      injection E' as <-. cbn [conf_expr conf_state stack_expr c_frame c_callers c_mem c_fuel].
      iModIntro. iSplitL "Hσ"; [iApply (heap_interp_fuel with "Hσ") | iExact "H"].
Qed.

(** A goto to the target t, polling or not, enters its block from l. *)
Lemma wp_goto f e ls l t Φ :
  SS.keeps_live ->
  ▷ WP (ERun (mkFrame f e ls None (Enter (edge_label t) (Some l))) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l [] (JGoto t))) : lexpr) {{ Φ }}.
Proof. intros HK. apply (wp_pure_next _ _ []); [exact HK|]. intros m fuel. apply rule_goto. Qed.

(** A branch on v, which reads as the integer n, enters t2's block from
    l if n is 0, else t1's. *)
Lemma wp_branch f e ls l v t1 t2 n Φ :
  SS.keeps_live -> value_x ge e W v = Some (WInt n) ->
  ▷ WP (ERun (mkFrame f e ls None (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) : lexpr)
      {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) : lexpr) {{ Φ }}.
Proof.
  intros HK Hv. apply (wp_pure_next _ _ []); [exact HK|].
  intros m fuel. exact (rule_branch _ _ _ _ _ _ _ _ _ _ _ _ Hv).
Qed.

(** A return of v, which reads as x at f's return class k, from an
    invocation with no named locals: the invocation's value is [Ret]
    x, and the postcondition holds of it. *)
Lemma wp_ret f e l v k x Φ :
  SS.keeps_live -> fn_ret f = RClass k -> value_x ge e k v = Some x ->
  ▷ Φ (Ret x) -∗ WP (ERun (mkFrame f e [] None (Exec l [] (JRet v))) : lexpr) {{ Φ }}.
Proof.
  intros HK Hk Hv.
  assert (Hs : forall m fuel,
             Semantics.step ge (mkConfig (mkFrame f e [] None (Exec l [] (JRet v))) [] m fuel)
             = Done (Ret x)).
  { intros m fuel. rewrite (rule_ret _ _ _ _ _ _ _ _ _ _ _ Hk Hv).
    exact (rule_return_top (mkFrame f e [] None (Exec l [] (JRet v))) m fuel _ m (invalidate_none m)). }
  iIntros "H". iApply (wp_lift_run with "H"); [exact HK| |].
  - iIntros (σ) "_ _". iPureIntro. unfold fails. rewrite Hs. cbn. tauto.
  - iIntros ([m s fuel]) "Hσ H". iNext. iIntros (e2 σ2 Hm).
    unfold moves in Hm. cbn [ls_mem ls_fuel ls_rt] in Hm.
    destruct Hm as [(c' & E' & _) | [(q & kk & base & s' & E' & _) | (o & m' & E' & _ & Hi & -> & ->)]];
      rewrite Hs in E'; try discriminate E'.
    injection E' as <-. cbn in Hi. injection Hi as <-. iModIntro. iFrame "Hσ".
    iApply (wp_value' _ _ _ (Ret x)). iExact "H".
Qed.

(** A direct call of the function g, defined in the module, with
    arguments that read as xs and make its frame callee: the callee
    runs as the callee of the caller, which waits at the rest of its
    block for the result r. *)
Lemma wp_call f e ls l r g args rest j xs gf callee Φ :
  SS.keeps_live ->
  map_option (arg_x ge e) args = Some xs -> find_fn ge g = Some (Defined gf) ->
  call_frame gf xs = Some callee ->
  ▷ WP (EWait (ERun callee) (mkFrame f e ls None (Exec l rest j)) (mkPending r None) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hx Hf Hc.
  apply (wp_pure_next _ callee [(mkFrame f e ls None (Exec l rest j), mkPending r None)]); [exact HK|].
  intros m fuel. exact (rule_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Hf Hc).
Qed.

(** A returned outcome o resumes the caller cf waiting on it, which
    reads it as pd says: the caller goes on as cf'. *)
Lemma wp_resume o cf pd cf' Φ :
  resume cf pd o = Some cf' ->
  ▷ WP (ERun cf' : lexpr) {{ Φ }} -∗ WP (EWait (EEnd o) cf pd : lexpr) {{ Φ }}.
Proof.
  intros Hr. iIntros "H". iApply (wp_lift_pure_det_base_step_no_fork' _ (ERun cf')); [done | | |].
  - intros σ. exists [], (ERun cf'), σ, []. exact (hs_resume ge o cf pd cf' σ Hr).
  - intros σ κ e2 σ2 efs Hs. inversion Hs; subst. split; [done|]. split; [done|]. split; [|done].
    congruence.
  - iNext. iIntros "_". iExact "H".
Qed.

(** The caller cf waiting on its callee is an evaluation context. *)
Local Instance wait_ctx cf pd : LanguageCtx (Λ := nanofil_lang ge) (fun e => EWait e cf pd).
Proof. exact (ectxi_lang_ctx_item (Λ := nanofil_ectxi_lang ge) (KWait cf pd)). Qed.

(** A direct call, as [wp_call], whose callee's run ends with an
    outcome the caller resumes with: the callee's weakest precondition
    is the caller's, through [wp_bind] and [wp_resume]. A caller uses a
    callee's Hoare triple here. *)
Lemma wp_call_bind f e ls l r g args rest j xs gf callee Φ :
  SS.keeps_live ->
  map_option (arg_x ge e) args = Some xs -> find_fn ge g = Some (Defined gf) ->
  call_frame gf xs = Some callee ->
  ▷ WP (ERun callee : lexpr) {{ o, ∃ cf', ⌜resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) o
                                             = Some cf'⌝ ∗ ▷ WP (ERun cf' : lexpr) {{ Φ }} }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : lexpr) {{ Φ }}.
Proof.
  intros HK Hx Hf Hc. iIntros "H". iApply (wp_call with "[H]"); [exact HK|exact Hx|exact Hf|exact Hc|].
  iNext. iApply (wp_bind (fun ex => EWait ex (mkFrame f e ls None (Exec l rest j)) (mkPending r None))
                   NotStuck ⊤ (ERun callee : lexpr)).
  iApply (wp_mono with "H"). iIntros (o) "H". iDestruct "H" as (cf') "[%Hr H]".
  iApply (wp_resume _ _ _ _ _ Hr with "H").
Qed.

End wp.
End logic.

(** Iris [[adequacy]] with the ghost heap: if, for every admissible
    input, the entry's frame has a weakest precondition under any
    invariant and ghost heap instance, the module never panics. The
    initial memory's live objects must not overlap (it holds none for a
    module with no data). *)
Theorem heap_never_panics Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    md entry (input : list word -> Prop) globals m f :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  live_disjoint m ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\
     forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
       ⊢ WP (ERun fr : language.expr (nanofil_lang (P.program_genv md globals))) {{ _, True }}) ->
  P.never_panics md entry input.
Proof.
  intros Hm Hf Hd Hwp. apply (L.wp_never_panics HasNoLc Σ md entry input globals m f Hm Hf).
  intros xs Hxs. destruct (Hwp xs Hxs) as (fr & Hfr & Hw). exists fr. split; [exact Hfr|].
  intros Hready fuel Hinv.
  iMod (gen_heap_init (∅ : gmap piece pval)) as (HheapG) "(Hh & _ & _)".
  iModIntro. iExists (@heap_interp Σ HheapG).
  iSplitL "Hh".
  - iExists ∅. iFrame "Hh". iPureIntro. split; [|split; [exact Hd | exact Hready]].
    intros l v Hl. rewrite lookup_empty in Hl. discriminate.
  - iApply (Hw Hinv HheapG).
Qed.

End Logic.
