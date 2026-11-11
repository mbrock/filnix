(** # Invariants, parallel-move soundness and frame proofs for Regs.v

    Kernel-checked proofs for the interval primitives, live
    register-and-frame-slot state updates, 3-address immediate
    selection, whole-scheduler parallel moves and concrete frame
    separation in Regs.v (M7 of docs/gallina-backend.md):

    1. **Interval and call-point tests** ([hreg_eqb_spec],
       [ivals_disjoint_sound], [ivals_hit_points_sound]): under
       [ivals_wf] and [pts_wf], disjoint interval lists share no program
       point, and an interval list that misses the sorted call points
       contains none of them.
    2. **Live-only register and shared-slot state steps**
       ([clobber_preserves_agrees], [poll_edge_clobber_sound],
       [write_mach_step_sound], [write_mach_list_sound],
       [check_rinst_step_sound]): [state_agrees] relates live
       temporaries to hardware registers and physical shared frame slots
       (`Z -> Z` indexed by `slot_of`, allowing expired spill-slot reuse
       as in [ex_shared_spill_slot]), across caller-saved clobbers,
       single and simultaneous destination writes, and one abstract
       instruction step.
    3. **3-address `lea` and immediate selection** ([imm32_congruent],
       [imm32_add_mod_sound], [imm32_sub_lea_w_sound],
       [imm32_sub_lea_l_sound]): [integer_immediate] and negated `lea`
       displacements compute the exact modular sum and difference at
       both 32-bit (`w`, including `-2^31`) and 64-bit (`l`) widths.
    4. **Whole-scheduler parallel-move soundness**
       ([compile_pmoves_no_todo], [compile_pmoves_sound],
       [ready_pmove_step_sound]): for any well-formed parallel-move list
       with distinct non-scratch destinations and canonical source
       widths, [compile_pmoves] never exhausts its `2n + 1` fuel or
       emits [todo], keeps `%rcx` unread before every cycle break across
       any number of disjoint cycles, and emits x86-64 instructions
       whose sequential execution produces [simul_pmoves] on every
       allocatable register and frame slot under any global symbol map.
    5. **Concrete [build_rctx] callee-save and root-slot invariants**
       ([build_rctx_save_slots_disjoint],
       [build_rctx_used_callee_saved], [build_rctx_callee_saves_sound],
       [build_rctx_root_lower_slot], [lower_key_never_hreg]):
       callee-save slots in [rc_saves] are disjoint from every plain,
       root and aliased frame slot, cover every callee-saved register in
       `rm`, restore all five callee-saved registers via
       [callee_save_stores] and [callee_save_restores], and keep pointer
       lowers in concrete `lowers[]` GC root slots. *)

From Stdlib Require Import String ZArith List Bool Arith Lia SetoidList.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Asm Plan PlanTerm Layout Emit Regs.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## 1. Hardware register equality and interval disjointness *)

Lemma hreg_eqb_refl : forall r, hreg_eqb r r = true.
Proof. destruct r; reflexivity. Qed.

Theorem hreg_eqb_spec : forall a b, hreg_eqb a b = true <-> a = b.
Proof.
  intros a b. split; intro H.
  - destruct a, b; simpl in H; try discriminate; reflexivity.
  - subst b. apply hreg_eqb_refl.
Qed.

Lemma nat_ltb_spec : forall a b, nat_ltb a b = true <-> (a < b)%nat.
Proof.
  intros a b. unfold nat_ltb.
  destruct (Nat.compare_spec a b); split; intro Hc; try discriminate; lia.
Qed.

Lemma nat_ltb_false_spec : forall a b, nat_ltb a b = false <-> (b <= a)%nat.
Proof.
  intros a b. unfold nat_ltb.
  destruct (Nat.compare_spec a b); split; intro Hc; try discriminate; lia.
Qed.

Lemma nat_eqb_spec : forall a b, nat_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold nat_eqb.
  destruct (Nat.compare_spec a b); split; intro Hc; try discriminate; lia.
Qed.

(** Whether point `p` lies in some closed interval `[lo, hi]` of `ivs`. *)
Fixpoint in_ivals (p : nat) (ivs : list ival) : Prop :=
  match ivs with
  | [] => False
  | (lo, hi) :: ivs' => ((lo <= p)%nat /\ (p <= hi)%nat) \/ in_ivals p ivs'
  end.

(** Strictly ordered interval list: each interval ends before the next
    begins, and every interval satisfies `lo <= hi`. *)
Fixpoint ivals_wf (bound : nat) (ivs : list ival) : Prop :=
  match ivs with
  | [] => True
  | (lo, hi) :: ivs' =>
      (bound <= lo)%nat /\ (lo <= hi)%nat /\ ivals_wf (S hi) ivs'
  end.

Lemma in_ivals_ge_bound : forall ivs bound p,
  ivals_wf bound ivs -> in_ivals p ivs -> (bound <= p)%nat.
Proof.
  induction ivs as [|[lo hi] ivs' IH]; intros bound p Hwf Hin; simpl in *.
  - contradiction.
  - destruct Hwf as [Hb [Hlh Hwf']].
    destruct Hin as [[H1 _] | Hin'].
    + lia.
    + specialize (IH (S hi) p Hwf' Hin'). lia.
Qed.

Lemma ivals_wf_weaken : forall ivs b1 b2,
  (b1 <= b2)%nat -> ivals_wf b2 ivs -> ivals_wf b1 ivs.
Proof.
  destruct ivs as [|[lo hi] ivs']; intros b1 b2 Hle Hwf; simpl in *; [exact I|].
  destruct Hwf as [H1 H2]. split; [lia | exact H2].
Qed.

Lemma ivals_disjoint_fuel_sound : forall fuel xs ys bx by0 p,
  ivals_wf bx xs -> ivals_wf by0 ys ->
  ivals_disjoint_fuel fuel xs ys = true ->
  in_ivals p xs -> in_ivals p ys -> False.
Proof.
  induction fuel as [|fuel' IH]; intros xs ys bx by0 p Hwx Hwy Hdisj Hx Hy.
  - destruct xs as [|[a1 b1] xs']; [simpl in Hx; exact Hx|].
    destruct ys as [|[a2 b2] ys']; [simpl in Hy; exact Hy|].
    simpl in Hdisj. discriminate.
  - destruct xs as [|[a1 b1] xs']; [simpl in Hx; exact Hx|].
    destruct ys as [|[a2 b2] ys']; [simpl in Hy; exact Hy|].
    simpl in Hdisj.
    destruct Hwx as [Hbx [Hab1 Hwx']].
    destruct Hwy as [Hby [Hab2 Hwy']].
    destruct (nat_ltb b1 a2) eqn:E1.
    + apply nat_ltb_spec in E1.
      simpl in Hx. destruct Hx as [[Hpa1 Hpb1] | Hx'].
      * assert (Hpge : (a2 <= p)%nat).
        { apply (in_ivals_ge_bound ((a2, b2) :: ys') a2 p); [|exact Hy].
          simpl. split; [lia | split; [exact Hab2 | exact Hwy']]. }
        lia.
      * eapply IH; [exact Hwx' | | exact Hdisj | exact Hx' | exact Hy].
        simpl. split; [exact Hby | split; [exact Hab2 | exact Hwy']].
    + destruct (nat_ltb b2 a1) eqn:E2; [|discriminate].
      apply nat_ltb_spec in E2.
      simpl in Hy. destruct Hy as [[Hpa2 Hpb2] | Hy'].
      * assert (Hpge : (a1 <= p)%nat).
        { apply (in_ivals_ge_bound ((a1, b1) :: xs') a1 p); [|exact Hx].
          simpl. split; [lia | split; [exact Hab1 | exact Hwx']]. }
        lia.
      * eapply IH; [| exact Hwy' | exact Hdisj | exact Hx | exact Hy'].
        simpl. split; [exact Hbx | split; [exact Hab1 | exact Hwx']].
Qed.

(** Disjoint well-formed interval lists share no program point. *)
Theorem ivals_disjoint_sound : forall xs ys p,
  ivals_wf O xs -> ivals_wf O ys ->
  ivals_disjoint xs ys = true ->
  in_ivals p xs -> in_ivals p ys -> False.
Proof.
  intros xs ys p Hwx Hwy Hdisj Hx Hy. unfold ivals_disjoint in Hdisj.
  eapply ivals_disjoint_fuel_sound; [exact Hwx | exact Hwy | exact Hdisj | exact Hx | exact Hy].
Qed.

Fixpoint pts_wf (bound : nat) (pts : list nat) : Prop :=
  match pts with
  | [] => True
  | q :: pts' => (bound <= q)%nat /\ pts_wf (S q) pts'
  end.

Lemma in_pts_ge_bound : forall pts bound p,
  pts_wf bound pts -> In p pts -> (bound <= p)%nat.
Proof.
  induction pts as [|q pts' IH]; intros bound p Hwf Hin; simpl in *.
  - contradiction.
  - destruct Hwf as [Hb Hwf']. destruct Hin as [<- | Hin'].
    + exact Hb.
    + specialize (IH (S q) p Hwf' Hin'). lia.
Qed.

Lemma ivals_hit_points_fuel_sound : forall fuel ivs pts bi bp p,
  ivals_wf bi ivs -> pts_wf bp pts ->
  ivals_hit_points_fuel fuel ivs pts = false ->
  in_ivals p ivs -> In p pts -> False.
Proof.
  induction fuel as [|fuel' IH]; intros ivs pts bi bp p Hwi Hwp Hhit Hin Hpt.
  - destruct ivs as [|[a b] ivs']; [simpl in Hin; exact Hin|].
    destruct pts as [|q pts']; [simpl in Hpt; exact Hpt|].
    simpl in Hhit. discriminate.
  - destruct ivs as [|[a b] ivs']; [simpl in Hin; exact Hin|].
    destruct pts as [|q pts']; [simpl in Hpt; exact Hpt|].
    simpl in Hhit.
    destruct Hwi as [Hbi [Hab Hwi']].
    destruct Hwp as [Hbp Hwp'].
    destruct (nat_ltb b q) eqn:E1.
    + apply nat_ltb_spec in E1.
      simpl in Hin. destruct Hin as [[_ Hpb] | Hin'].
      * assert (Hqle : (q <= p)%nat).
        { apply (in_pts_ge_bound (q :: pts') q p); [|exact Hpt].
          simpl. split; [lia | exact Hwp']. }
        lia.
      * eapply IH; [exact Hwi' | | exact Hhit | exact Hin' | exact Hpt].
        simpl. split; [exact Hbp | exact Hwp'].
    + destruct (nat_ltb q a) eqn:E2; [|discriminate].
      apply nat_ltb_spec in E2.
      simpl in Hpt. destruct Hpt as [<- | Hpt'].
      * assert (Hale : (a <= q)%nat).
        { apply (in_ivals_ge_bound ((a, b) :: ivs') a q); [|exact Hin].
          simpl. split; [lia | split; [exact Hab | exact Hwi']]. }
        lia.
      * eapply IH; [| exact Hwp' | exact Hhit | exact Hin | exact Hpt'].
        simpl. split; [exact Hbi | split; [exact Hab | exact Hwi']].
Qed.

(** When [ivals_hit_points] returns `false`, no call point in `pts`
    falls inside `ivs`. *)
Theorem ivals_hit_points_sound : forall ivs pts p,
  ivals_wf O ivs -> pts_wf O pts ->
  ivals_hit_points ivs pts = false ->
  in_ivals p ivs -> In p pts -> False.
Proof.
  intros ivs pts p Hwi Hwp Hhit Hin Hpt. unfold ivals_hit_points in Hhit.
  eapply ivals_hit_points_fuel_sound; [exact Hwi | exact Hwp | exact Hhit | exact Hin | exact Hpt].
Qed.

(** ## 2. Live register and shared-slot state preservation *)

(** Register file and physical stack-frame slots (indexed by frame
    offset `Z`, which disjoint lifetimes in FrameSlots.v may share). *)
Record mach_state : Type := mkMach {
  ms_reg : hreg -> Z;
  ms_slot : Z -> Z
}.

(** Read temporary `t` from its assigned [hreg] in `rm` or from its
    physical frame slot `slot_of t`. *)
Definition read_mach (rm : ZMap.t hreg) (slot_of : nat -> Z)
                     (ms : mach_state) (t : nat) : Z :=
  match zmap_find_nat t rm with
  | Some r => ms_reg ms r
  | None => ms_slot ms (slot_of t)
  end.

(** Write value `v` to temporary `t`'s assigned [hreg] in `rm` or to
    its physical frame slot `slot_of t`. *)
Definition write_mach (rm : ZMap.t hreg) (slot_of : nat -> Z)
                      (ms : mach_state) (t : nat) (v : Z) : mach_state :=
  match zmap_find_nat t rm with
  | Some r => mkMach (fun r' => if hreg_eqb r' r then v else ms_reg ms r') (ms_slot ms)
  | None => mkMach (ms_reg ms) (fun off => if Z.eqb off (slot_of t) then v else ms_slot ms off)
  end.

(** Write a list of destinations `ds` and values `vs` sequentially to
    registers and physical frame slots. *)
Fixpoint write_mach_list (rm : ZMap.t hreg) (slot_of : nat -> Z)
                         (ms : mach_state) (ds : list nat) (vs : list Z)
  : mach_state :=
  match ds, vs with
  | d :: ds', v :: vs' => write_mach_list rm slot_of (write_mach rm slot_of ms d v) ds' vs'
  | _, _ => ms
  end.

(** Write a list of destinations `ds` and values `vs` to the abstract
    temporary environment `tenv`. *)
Fixpoint write_abs_list (tenv : nat -> Z) (ds : list nat) (vs : list Z) : nat -> Z :=
  match ds, vs with
  | d :: ds', v :: vs' =>
      write_abs_list (fun t => if Nat.eqb t d then v else tenv t) ds' vs'
  | _, _ => tenv
  end.

(** A call clobbers caller-saved registers (`%r10`, `%r11`) with
    arbitrary values `arb` while preserving callee-saved registers and
    physical stack slots. *)
Definition clobber_call (arb : hreg -> Z) (ms : mach_state) : mach_state :=
  mkMach (fun r => if hreg_callee_saved r then ms_reg ms r else arb r) (ms_slot ms).

(** Live-only state agreement: every temporary `t` in `live` reads as
    `tenv t` in `ms` under `rm` and `slot_of`. Dead temporaries need
    not retain their values in shared physical slots. *)
Definition state_agrees (rm : ZMap.t hreg) (slot_of : nat -> Z) (live : list nat)
                        (tenv : nat -> Z) (ms : mach_state) : Prop :=
  forall t, In t live -> read_mach rm slot_of ms t = tenv t.

(** Witness that dead unmapped `0` (abstract value `1`) and live
    unmapped `1` (abstract value `2`) can share physical frame offset
    `16` while satisfying [state_agrees] on `[1]`. *)
Definition ex_shared_slot_of (_ : nat) : Z := 16.
Definition ex_shared_tenv (t : nat) : Z := if Nat.eqb t 0%nat then 1 else 2.
Definition ex_shared_ms : mach_state :=
  mkMach (fun _ => 0) (fun off => if Z.eqb off 16 then 2 else 0).

(** Shared physical spill slots satisfy [state_agrees] once an earlier
    occupant is dead. *)
Example ex_shared_spill_slot :
  state_agrees (ZMap.empty hreg) ex_shared_slot_of [1%nat] ex_shared_tenv ex_shared_ms.
Proof.
  intros t [<- | []]. reflexivity.
Qed.

(** [hreg_in_list] reflects list membership [In]. *)
Lemma hreg_in_list_spec : forall r rs,
  hreg_in_list r rs = true <-> In r rs.
Proof.
  intros r rs. induction rs as [|r' rs' IH]; simpl.
  - split; intro H; [discriminate | contradiction].
  - destruct (hreg_eqb r r') eqn:E.
    + apply hreg_eqb_spec in E. subst r'. split; auto.
    + rewrite IH. split; [right; exact H | intros [Heq | Hin]; [subst; rewrite hreg_eqb_refl in E; discriminate | exact Hin]].
Qed.

(** No temporary in `ts` maps to a register already present in `seen`
    when [no_dup_hregs_acc] accepts. *)
Lemma no_dup_hregs_acc_disjoint : forall rm ts seen t1 r,
  no_dup_hregs_acc rm ts seen = true ->
  In t1 ts -> In r seen -> zmap_find_nat t1 rm = Some r -> False.
Proof.
  intros rm ts. induction ts as [|t ts' IH]; intros seen t1 r Hnd Hin Hseen Hrm; simpl in *.
  - contradiction.
  - destruct (zmap_find_nat t rm) as [rt|] eqn:Ert.
    + destruct (hreg_in_list rt seen) eqn:Ein; [discriminate|].
      destruct Hin as [<- | Hin'].
      * rewrite Hrm in Ert. injection Ert as <-.
        pose proof (proj2 (hreg_in_list_spec r seen) Hseen) as Ht.
        rewrite Ht in Ein. discriminate.
      * eapply IH; [exact Hnd | exact Hin' | right; exact Hseen | exact Hrm].
    + destruct Hin as [<- | Hin'].
      * rewrite Hrm in Ert. discriminate.
      * eapply IH; [exact Hnd | exact Hin' | exact Hseen | exact Hrm].
Qed.

(** When [no_dup_hregs] accepts `ts`, distinct temporaries in `ts`
    never map to the same [hreg]. *)
Lemma no_dup_hregs_inj : forall rm ts,
  no_dup_hregs rm ts = true ->
  forall t1 t2 r, In t1 ts -> In t2 ts -> t1 <> t2 ->
  zmap_find_nat t1 rm = Some r -> zmap_find_nat t2 rm = Some r -> False.
Proof.
  unfold no_dup_hregs. intros rm ts.
  assert (Hgen : forall seen, no_dup_hregs_acc rm ts seen = true ->
            forall t1 t2 r, In t1 ts -> In t2 ts -> t1 <> t2 ->
            zmap_find_nat t1 rm = Some r -> zmap_find_nat t2 rm = Some r -> False).
  { induction ts as [|t ts' IH]; intros seen Hacc t1 t2 r Hin1 Hin2 Hneq Hr1 Hr2; simpl in *.
    - contradiction.
    - destruct (zmap_find_nat t rm) as [rt|] eqn:Ert.
      + destruct (hreg_in_list rt seen) eqn:Ein; [discriminate|].
        destruct Hin1 as [<- | Hin1']; destruct Hin2 as [<- | Hin2'].
        * congruence.
        * rewrite Hr1 in Ert. injection Ert as <-.
          eapply no_dup_hregs_acc_disjoint; [exact Hacc | exact Hin2' | left; reflexivity | exact Hr2].
        * rewrite Hr2 in Ert. injection Ert as <-.
          eapply no_dup_hregs_acc_disjoint; [exact Hacc | exact Hin1' | left; reflexivity | exact Hr1].
        * eapply IH; [exact Hacc | exact Hin1' | exact Hin2' | exact Hneq | exact Hr1 | exact Hr2].
      + destruct Hin1 as [<- | Hin1']; [rewrite Hr1 in Ert; discriminate|].
        destruct Hin2 as [<- | Hin2']; [rewrite Hr2 in Ert; discriminate|].
        eapply IH; [exact Hacc | exact Hin1' | exact Hin2' | exact Hneq | exact Hr1 | exact Hr2]. }
  intros Hacc. eapply Hgen; exact Hacc.
Qed.

(** Every mapped temporary in a list accepted by [all_callee_saved]
    holds a callee-saved register. *)
Lemma all_callee_saved_spec : forall rm ts t r,
  all_callee_saved rm ts = true ->
  In t ts -> zmap_find_nat t rm = Some r ->
  hreg_callee_saved r = true.
Proof.
  intros rm ts. induction ts as [|x ts' IH]; intros t r Hall Hin Hrm; simpl in *.
  - contradiction.
  - destruct Hin as [<- | Hin'].
    + rewrite Hrm in Hall. destruct (hreg_callee_saved r); [reflexivity | discriminate].
    + destruct (zmap_find_nat x rm) as [rx|].
      * destruct (hreg_callee_saved rx); [|discriminate].
        eapply IH; eauto.
      * eapply IH; eauto.
Qed.

(** Clobbering caller-saved registers preserves [state_agrees] on any
    live list `ts` accepted by [all_callee_saved]. *)
Theorem clobber_preserves_agrees : forall rm slot_of ts tenv ms arb,
  all_callee_saved rm ts = true ->
  state_agrees rm slot_of ts tenv ms ->
  state_agrees rm slot_of ts tenv (clobber_call arb ms).
Proof.
  intros rm slot_of ts tenv ms arb Hcs Hlive t Hin.
  specialize (Hlive t Hin). unfold read_mach in *.
  destruct (zmap_find_nat t rm) as [r|] eqn:Er; simpl.
  - rewrite (all_callee_saved_spec rm ts t r Hcs Hin Er). exact Hlive.
  - exact Hlive.
Qed.

(** Poll-edge corollary: when `header_live` is accepted by
    [all_callee_saved], a slow-path poll clobbering caller-saved
    registers preserves [state_agrees] on `header_live`. *)
Theorem poll_edge_clobber_sound : forall rm slot_of header_live tenv ms arb,
  all_callee_saved rm header_live = true ->
  state_agrees rm slot_of header_live tenv ms ->
  state_agrees rm slot_of header_live tenv (clobber_call arb ms).
Proof.
  intros. apply clobber_preserves_agrees; assumption.
Qed.

(** Temporary `d`'s home (register in `rm`, or physical slot in
    `slot_of` when unmapped) collides with no other temporary `t <> d`
    in `live`. *)
Definition dest_no_collision (rm : ZMap.t hreg) (slot_of : nat -> Z)
                             (d : nat) (live : list nat) : Prop :=
  (forall r t, In t live -> t <> d ->
     zmap_find_nat d rm = Some r -> zmap_find_nat t rm = Some r -> False) /\
  (forall t, In t live -> t <> d ->
     zmap_find_nat d rm = None -> zmap_find_nat t rm = None ->
     slot_of d = slot_of t -> False).

(** Filter `live` down to temporaries distinct from `d`. *)
Definition live_without (d : nat) (live : list nat) : list nat :=
  filter (fun t => negb (Nat.eqb t d)) live.

(** Update `tenv` at temporary `d` to `v`. *)
Definition tenv_set (tenv : nat -> Z) (d : nat) (v : Z) (t : nat) : Z :=
  if Nat.eqb t d then v else tenv t.

(** Writing temporary `d` preserves every other temporary `t <> d` in
    `live` whose home does not collide with `d`'s, and sets `d` to `v`. *)
Theorem write_mach_step_sound : forall rm slot_of live tenv ms d v,
  dest_no_collision rm slot_of d live ->
  state_agrees rm slot_of (live_without d live) tenv ms ->
  state_agrees rm slot_of live (tenv_set tenv d v) (write_mach rm slot_of ms d v).
Proof.
  intros rm slot_of live tenv ms d v [Hreg Hslot] Hlive t Hin.
  unfold read_mach, write_mach, tenv_set.
  destruct (Nat.eqb t d) eqn:Etd.
  - apply Nat.eqb_eq in Etd. subst t.
    destruct (zmap_find_nat d rm) as [rd|]; simpl.
    + rewrite hreg_eqb_refl. reflexivity.
    + rewrite Z.eqb_refl. reflexivity.
  - assert (Hin_filt : In t (live_without d live)).
    { unfold live_without. apply filter_In. split; [exact Hin | rewrite Etd; reflexivity]. }
    specialize (Hlive t Hin_filt). unfold read_mach in Hlive.
    apply Nat.eqb_neq in Etd.
    destruct (zmap_find_nat d rm) as [rd|] eqn:Erd;
    destruct (zmap_find_nat t rm) as [rt|] eqn:Ert; simpl.
    + destruct (hreg_eqb rt rd) eqn:Er; [|exact Hlive].
      apply hreg_eqb_spec in Er. subst rt.
      exfalso. eapply Hreg; [exact Hin | exact Etd | reflexivity | exact Ert].
    + exact Hlive.
    + exact Hlive.
    + destruct (Z.eqb (slot_of t) (slot_of d)) eqn:Es; [|exact Hlive].
      apply Z.eqb_eq in Es.
      exfalso. eapply Hslot; [exact Hin | exact Etd | reflexivity | exact Ert | symmetry; exact Es].
Qed.

(** Filter `live` down to temporaries not in `ds`. *)
Fixpoint live_without_list (ds : list nat) (live : list nat) : list nat :=
  match ds with
  | [] => live
  | d :: ds' => live_without d (live_without_list ds' live)
  end.

(** Pairwise and live non-collision across a multi-definition list `ds`. *)
Fixpoint list_no_collision (rm : ZMap.t hreg) (slot_of : nat -> Z)
                           (ds : list nat) (live : list nat) : Prop :=
  match ds with
  | [] => True
  | d :: ds' =>
      dest_no_collision rm slot_of d (live_without_list ds' live) /\
      list_no_collision rm slot_of ds' live
  end.

(** Simultaneous / sequential multi-destination writes [write_mach_list]
    and [write_abs_list] preserve [state_agrees] on `live` when
    [list_no_collision] holds and `length ds = length vs`. *)
Theorem write_mach_list_sound : forall ds vs rm slot_of live tenv ms,
  length ds = length vs ->
  list_no_collision rm slot_of ds live ->
  state_agrees rm slot_of (live_without_list ds live) tenv ms ->
  state_agrees rm slot_of live (write_abs_list tenv ds vs)
               (write_mach_list rm slot_of ms ds vs).
Proof.
  induction ds as [|d ds' IH]; intros [|v vs'] rm slot_of live tenv ms Hlen Hnc Hagree;
    simpl in *; try discriminate.
  - exact Hagree.
  - injection Hlen as Hlen'. destruct Hnc as [Hd Hds'].
    apply IH; [exact Hlen' | exact Hds' |].
    apply write_mach_step_sound; [exact Hd | exact Hagree].
Qed.

(** Mid-instruction call safety condition for [RCallAfterReads]. *)
Definition call_mid_ok (rm : ZMap.t hreg) (call : rcall) (live_mid : list nat) : Prop :=
  match call with
  | RCallAfterReads => all_callee_saved rm live_mid = true
  | _ => True
  end.

(** Pre-read call safety condition for [RCallDuringReads]. *)
Definition call_pre_ok (rm : ZMap.t hreg) (call : rcall) (live_before : list nat) : Prop :=
  match call with
  | RCallDuringReads => all_callee_saved rm live_before = true
  | _ => True
  end.

(** Machine state after any helper call that precedes operand reads. *)
Definition pre_call_state (call : rcall) (arb : hreg -> Z) (ms : mach_state) : mach_state :=
  match call with
  | RCallDuringReads => clobber_call arb ms
  | _ => ms
  end.

(** Machine state after any call that follows operand reads. *)
Definition post_call_state (call : rcall) (arb : hreg -> Z) (ms : mach_state) : mach_state :=
  match call with
  | RCallNone => ms
  | RCallAfterReads | RCallDuringReads => clobber_call arb ms
  end.

(** Single-destination abstract instruction step: under
    [dest_no_collision], [call_mid_ok] and [call_pre_ok], operand reads
    agree with `tenv` and writing `d` preserves [state_agrees] on
    `live_after`. *)
Theorem check_rinst_step_sound :
  forall rm slot_of live_after d uses call f arb1 arb2 tenv ms,
  dest_no_collision rm slot_of d live_after ->
  call_mid_ok rm call (live_without d live_after) ->
  call_pre_ok rm call (uses ++ live_without d live_after) ->
  state_agrees rm slot_of (uses ++ live_without d live_after) tenv ms ->
  map (read_mach rm slot_of (pre_call_state call arb1 ms)) uses = map tenv uses /\
  state_agrees rm slot_of live_after
    (tenv_set tenv d (f (map tenv uses)))
    (write_mach rm slot_of
      (post_call_state call arb2 (pre_call_state call arb1 ms))
      d (f (map (read_mach rm slot_of (pre_call_state call arb1 ms)) uses))).
Proof.
  intros rm slot_of live_after d uses call f arb1 arb2 tenv ms Hnodup Hca Hcd Hagree.
  set (live_mid := live_without d live_after) in *.
  set (live_before := uses ++ live_mid) in *.
  set (ms_pre := pre_call_state call arb1 ms).
  assert (Hagree_pre : state_agrees rm slot_of live_before tenv ms_pre).
  { unfold ms_pre, pre_call_state. destruct call; try exact Hagree.
    apply clobber_preserves_agrees; [exact Hcd | exact Hagree]. }
  assert (Hargs : map (read_mach rm slot_of ms_pre) uses = map tenv uses).
  { apply map_ext_in. intros u Hu.
    apply Hagree_pre. unfold live_before. apply in_or_app. left. exact Hu. }
  split; [exact Hargs|].
  rewrite Hargs.
  apply write_mach_step_sound; [exact Hnodup|].
  assert (Hagree_mid : state_agrees rm slot_of live_mid tenv ms_pre).
  { intros t Ht. apply Hagree_pre. unfold live_before. apply in_or_app. right. exact Ht. }
  unfold post_call_state. destruct call.
  - exact Hagree_mid.
  - apply clobber_preserves_agrees; [exact Hca | exact Hagree_mid].
  - apply clobber_preserves_agrees.
    + simpl in Hcd. clear -Hcd. unfold live_before in Hcd.
      induction uses as [|u uses' IH]; simpl in *; [exact Hcd|].
      destruct (zmap_find_nat u rm) as [ru|].
      * destruct (hreg_callee_saved ru); [exact (IH Hcd) | discriminate].
      * exact (IH Hcd).
    + exact Hagree_mid.
Qed.

(** ## 3. Soundness of 3-address `lea` and immediate selection *)

(** [integer_immediate] produces a value congruent to `n` modulo
    `2^32` (`half = true`) or `2^64` (`half = false`). *)
Theorem imm32_congruent : forall half n iv,
  integer_immediate half n = Some iv ->
  iv mod (if half then two32 else two64) = n mod (if half then two32 else two64).
Proof.
  intros [|] n iv H; unfold integer_immediate in H.
  - injection H as <-.
    unfold two31, two32.
    rewrite Zminus_mod_idemp_l.
    replace (n + 2147483648 - 2147483648) with n by lia.
    reflexivity.
  - cbv zeta in H.
    destruct ((- two31 <=? _) && (_ <=? two31 - 1)) eqn:E; [|discriminate].
    injection H as <-.
    destruct ((n mod two64) >=? two63) eqn:Ege.
    + rewrite Zminus_mod_idemp_l.
      replace (n - two64) with (n + (-1) * two64) by lia.
      apply Z_mod_plus_full.
    + apply Z.mod_mod. unfold two64. lia.
Qed.

(** Immediate `add` and `lea disp(%rx)` compute `(x + n) mod M` at both
    32-bit and 64-bit widths. *)
Theorem imm32_add_mod_sound : forall half x n iv,
  integer_immediate half n = Some iv ->
  (x + iv) mod (if half then two32 else two64)
  = (x + n) mod (if half then two32 else two64).
Proof.
  intros half x n iv H.
  pose proof (imm32_congruent half n iv H) as Hc.
  pose proof (Z.add_mod x iv (if half then two32 else two64)) as H1.
  pose proof (Z.add_mod x n (if half then two32 else two64)) as H2.
  assert (Hm : (if half then two32 else two64) <> 0) by (destruct half; unfold two32, two64; lia).
  rewrite H1, H2 by exact Hm. rewrite Hc. reflexivity.
Qed.

(** Reducing modulo `2^64` and then `2^32` equals reducing modulo `2^32`. *)
Lemma mod_two64_mod_two32 : forall a,
  (a mod two64) mod two32 = a mod two32.
Proof.
  intro a.
  pose proof (Z_div_mod_eq_full a two64) as Heq.
  replace (a mod two64) with (a + (- (a / two64) * two32) * two32)
    by (unfold two32, two64 in *; lia).
  apply Z_mod_plus_full.
Qed.

(** 32-bit `Sub` via `leal (-n)(%rx), %dst`: x86-64 adds the 64-bit
    sign-extended 32-bit displacement `iv` to the 64-bit base register
    `x` modulo `2^64`, then truncates to 32 bits (`mod 2^32`). Even at
    the boundary `n = -2^31` (where `-n = 2^31` wraps to `iv = -2^31`),
    the result equals `(x - n) mod 2^32`. *)
Theorem imm32_sub_lea_w_sound : forall x n iv,
  integer_immediate true (- n) = Some iv ->
  ((x + iv) mod two64) mod two32 = (x - n) mod two32.
Proof.
  intros x n iv H.
  rewrite mod_two64_mod_two32.
  replace (x - n) with (x + (- n)) by lia.
  exact (imm32_add_mod_sound true x (- n) iv H).
Qed.

(** 64-bit `Sub` via `leaq (-n)(%rx), %dst` computes `(x - n) mod 2^64`. *)
Theorem imm32_sub_lea_l_sound : forall x n iv,
  integer_immediate false (- n) = Some iv ->
  (x + iv) mod two64 = (x - n) mod two64.
Proof.
  intros x n iv H.
  replace (x - n) with (x + (- n)) by lia.
  exact (imm32_add_mod_sound false x (- n) iv H).
Qed.

(** ## 4. Whole-scheduler parallel-move soundness *)

(** Abstract valuation of parallel-move sources under global symbol
    addresses `sym_env` and location state `env`. *)
Definition eval_pm_src (sym_env : string -> Z) (env : pm_loc -> Z)
                       (half : bool) (s : pm_src) : Z :=
  let m := if half then two32 else two64 in
  match s with
  | PsLoc l => env l mod m
  | PsConst n => n mod m
  | PsGlobal g => sym_env g mod m
  end.

(** Execute one abstract parallel move `m` against `sym_env` and `env`. *)
Definition exec_pmove_abs (sym_env : string -> Z) (env : pm_loc -> Z)
                          (m : pmove) : pm_loc -> Z :=
  let v := eval_pm_src sym_env env (pmv_half m) (pmv_src m) in
  fun l => if pm_loc_eqb l (pmv_dst m) then v else env l.

(** Reflexivity of [pm_loc_eqb]. *)
Lemma pm_loc_eqb_refl : forall l, pm_loc_eqb l l = true.
Proof.
  destruct l as [r | off |]; simpl.
  - apply hreg_eqb_refl.
  - apply Z.eqb_refl.
  - reflexivity.
Qed.

(** [pm_loc_eqb] reflects equality on [pm_loc]. *)
Lemma pm_loc_eqb_spec : forall a b, pm_loc_eqb a b = true <-> a = b.
Proof.
  intros a b. destruct a as [r1 | o1 |], b as [r2 | o2 |]; simpl;
    try (split; intro H; [discriminate | congruence]).
  - rewrite hreg_eqb_spec. split; congruence.
  - rewrite Z.eqb_eq. split; congruence.
  - split; reflexivity.
Qed.

(** Symmetry of [pm_loc_eqb]. *)
Lemma pm_loc_eqb_sym : forall a b, pm_loc_eqb a b = pm_loc_eqb b a.
Proof.
  intros a b. destruct (pm_loc_eqb a b) eqn:E1; destruct (pm_loc_eqb b a) eqn:E2; auto.
  - apply pm_loc_eqb_spec in E1. subst b. rewrite pm_loc_eqb_refl in E2. discriminate.
  - apply pm_loc_eqb_spec in E2. subst a. rewrite pm_loc_eqb_refl in E1. discriminate.
Qed.

(** Executing `m` leaves the evaluated source of `m'` unchanged when
    `m'` does not read `pmv_dst m`. *)
Lemma loc_not_read_eval_unchanged : forall sym_env env m m',
  loc_read_in_pmoves (pmv_dst m) [m'] = false ->
  eval_pm_src sym_env (exec_pmove_abs sym_env env m) (pmv_half m') (pmv_src m')
  = eval_pm_src sym_env env (pmv_half m') (pmv_src m').
Proof.
  intros sym_env env m m' Hnr. simpl in Hnr.
  unfold eval_pm_src, exec_pmove_abs.
  destruct (pmv_src m') as [l' | n | g]; try reflexivity.
  destruct (pm_loc_eqb l' (pmv_dst m)) eqn:E.
  - apply pm_loc_eqb_spec in E. subst l'. rewrite pm_loc_eqb_refl in Hnr. discriminate.
  - reflexivity.
Qed.

(** Ready-move peeling step: if `m`'s destination is not read by any
    move `m'` in `rest`, executing `m` establishes `m`'s target value
    and leaves every source in `rest` unchanged. *)
Theorem ready_pmove_step_sound : forall sym_env env m rest,
  loc_read_in_pmoves (pmv_dst m) rest = false ->
  exec_pmove_abs sym_env env m (pmv_dst m)
    = eval_pm_src sym_env env (pmv_half m) (pmv_src m) /\
  (forall m', In m' rest ->
     eval_pm_src sym_env (exec_pmove_abs sym_env env m) (pmv_half m') (pmv_src m')
     = eval_pm_src sym_env env (pmv_half m') (pmv_src m')) /\
  (forall l, l <> pmv_dst m -> exec_pmove_abs sym_env env m l = env l).
Proof.
  intros sym_env env m rest Hnr. split; [|split].
  - unfold exec_pmove_abs. rewrite pm_loc_eqb_refl. reflexivity.
  - intros m' Hin. induction rest as [|r0 rs IH]; simpl in *.
    + contradiction.
    + destruct (match pmv_src r0 with PsLoc l' => pm_loc_eqb (pmv_dst m) l' | _ => false end) eqn:Eh;
        [discriminate|].
      destruct Hin as [<- | Hin'].
      * apply loc_not_read_eval_unchanged. simpl. rewrite Eh. reflexivity.
      * apply IH; assumption.
  - intros l Hneq. unfold exec_pmove_abs.
    destruct (pm_loc_eqb l (pmv_dst m)) eqn:E; [|reflexivity].
    apply pm_loc_eqb_spec in E. contradiction.
Qed.

(** Look up the move in `ms` whose destination is `l`, if any. *)
Fixpoint find_pmove_dst (l : pm_loc) (ms : list pmove) : option pmove :=
  match ms with
  | [] => None
  | m :: ms' => if pm_loc_eqb l (pmv_dst m) then Some m else find_pmove_dst l ms'
  end.

(** Simultaneous specification of a duplicate-free parallel-move list
    `ms`: each destination `pmv_dst m` receives `m`'s source evaluated
    in the initial state `env`, while untouched locations retain `env l`. *)
Definition simul_pmoves (sym_env : string -> Z) (env : pm_loc -> Z)
                        (ms : list pmove) (l : pm_loc) : Z :=
  match find_pmove_dst l ms with
  | Some m => eval_pm_src sym_env env (pmv_half m) (pmv_src m)
  | None => env l
  end.

(** Concrete x86-64 state for the move and prologue/epilogue subset:
    allocatable [hreg]s, cycle-breaker `%rcx`, scratch `%rax`, and
    `%rbp`-relative 8-byte frame slots (`pm_slot off` is `-off(%rbp)`). *)
Record pm_mach : Type := mkPmMach {
  pm_hreg : hreg -> Z;
  pm_rcx  : Z;
  pm_rax  : Z;
  pm_slot : Z -> Z
}.

(** Project [pm_loc] values from [pm_mach]. *)
Definition pm_mach_env (st : pm_mach) (l : pm_loc) : Z :=
  match l with
  | PmReg r => pm_hreg st r
  | PmSlot off => pm_slot st off
  | PmCycleTmp => pm_rcx st
  end.

(** Every register and frame slot holds a canonical unsigned 64-bit word. *)
Definition pm_mach_canonical (st : pm_mach) : Prop :=
  forall l, 0 <= pm_mach_env st l < two64.

(** Register identifiers touched by parallel-move and save/restore emission. *)
Inductive pm_reg_id : Type :=
| PrHReg (r : hreg)
| PrRcx
| PrRax.

(** Parse a 64-bit AT&T register name into [pm_reg_id]. *)
Definition pm_reg64_id (s : string) : option pm_reg_id :=
  if String.eqb s "r10" then Some (PrHReg HR10)
  else if String.eqb s "r11" then Some (PrHReg HR11)
  else if String.eqb s "rbx" then Some (PrHReg HRbx)
  else if String.eqb s "r12" then Some (PrHReg HR12)
  else if String.eqb s "r13" then Some (PrHReg HR13)
  else if String.eqb s "r14" then Some (PrHReg HR14)
  else if String.eqb s "r15" then Some (PrHReg HR15)
  else if String.eqb s "rcx" then Some PrRcx
  else if String.eqb s "rax" then Some PrRax
  else None.

(** Parse a 32-bit AT&T register name into [pm_reg_id]. *)
Definition pm_reg32_id (s : string) : option pm_reg_id :=
  if String.eqb s "r10d" then Some (PrHReg HR10)
  else if String.eqb s "r11d" then Some (PrHReg HR11)
  else if String.eqb s "ebx" then Some (PrHReg HRbx)
  else if String.eqb s "r12d" then Some (PrHReg HR12)
  else if String.eqb s "r13d" then Some (PrHReg HR13)
  else if String.eqb s "r14d" then Some (PrHReg HR14)
  else if String.eqb s "r15d" then Some (PrHReg HR15)
  else if String.eqb s "ecx" then Some PrRcx
  else if String.eqb s "eax" then Some PrRax
  else None.

(** Parse a 32-bit (`half = true`) or 64-bit (`half = false`) register name. *)
Definition pm_reg_id_at (half : bool) (s : string) : option pm_reg_id :=
  if half then pm_reg32_id s else pm_reg64_id s.

(** Read register `id` from `st`. *)
Definition pm_get_reg (st : pm_mach) (id : pm_reg_id) : Z :=
  match id with
  | PrHReg r => pm_hreg st r
  | PrRcx => pm_rcx st
  | PrRax => pm_rax st
  end.

(** Write 64-bit value `v` (already reduced to width) into register `id`. *)
Definition pm_set_reg (st : pm_mach) (id : pm_reg_id) (v : Z) : pm_mach :=
  match id with
  | PrHReg r =>
      mkPmMach (fun r' => if hreg_eqb r' r then v else pm_hreg st r')
               (pm_rcx st) (pm_rax st) (pm_slot st)
  | PrRcx => mkPmMach (pm_hreg st) v (pm_rax st) (pm_slot st)
  | PrRax => mkPmMach (pm_hreg st) (pm_rcx st) v (pm_slot st)
  end.

(** Write 64-bit value `v` into frame slot `off` (`-off(%rbp)`). *)
Definition pm_set_slot (st : pm_mach) (off v : Z) : pm_mach :=
  mkPmMach (pm_hreg st) (pm_rcx st) (pm_rax st)
           (fun off' => if Z.eqb off' off then v else pm_slot st off').

(** Operational semantics of one emitted x86-64 move/lea [line]; returns
    `None` on any unrecognized instruction, directive, label or [todo]. *)
Definition pm_exec_line (sym_env : string -> Z) (st : pm_mach) (ln : line)
  : option pm_mach :=
  match ln with
  | Ins op (Some suf) [src_op; dst_op] =>
      if String.eqb op "mov" then
        let o_half :=
          if String.eqb suf "l" then Some true
          else if String.eqb suf "q" then Some false
          else None in
        match o_half with
        | None => None
        | Some half =>
            let m := if half then two32 else two64 in
            let o_val :=
              match src_op with
              | OImm (ELit (LInt n)) => Some (n mod m)
              | OReg sr =>
                  option_map (fun id => pm_get_reg st id mod m) (pm_reg_id_at half sr)
              | OMem (LInt disp) base =>
                  if String.eqb base "rbp" then Some (pm_slot st (- disp) mod m) else None
              | _ => None
              end in
            match o_val, dst_op with
            | Some v, OReg dr =>
                option_map (fun id => pm_set_reg st id v) (pm_reg_id_at half dr)
            | Some v, OMem (LInt disp) base =>
                if negb half && String.eqb base "rbp"
                then Some (pm_set_slot st (- disp) v)
                else None
            | _, _ => None
            end
        end
      else if String.eqb op "movabs" && String.eqb suf "q" then
        match src_op, dst_op with
        | OImm (ELit (LInt n)), OReg dr =>
            option_map (fun id => pm_set_reg st id (n mod two64)) (pm_reg64_id dr)
        | _, _ => None
        end
      else if String.eqb op "lea" && String.eqb suf "q" then
        match src_op, dst_op with
        | ORip (ELit (LSym g)), OReg dr =>
            option_map (fun id => pm_set_reg st id (sym_env g mod two64)) (pm_reg64_id dr)
        | _, _ => None
        end
      else None
  | _ => None
  end.

(** Execute a sequence of emitted [line]s sequentially. *)
Fixpoint pm_exec_lines (sym_env : string -> Z) (st : pm_mach) (ls : list line)
  : option pm_mach :=
  match ls with
  | [] => Some st
  | ln :: ls' =>
      match pm_exec_line sym_env st ln with
      | Some st' => pm_exec_lines sym_env st' ls'
      | None => None
      end
  end.

(** [pm_reg64_id] recognizes every [hreg64]. *)
Lemma pm_reg64_hreg : forall r, pm_reg64_id (hreg64 r) = Some (PrHReg r).
Proof. destruct r; reflexivity. Qed.

(** [pm_reg32_id] recognizes every [hreg32]. *)
Lemma pm_reg32_hreg : forall r, pm_reg32_id (hreg32 r) = Some (PrHReg r).
Proof. destruct r; reflexivity. Qed.

(** [pm_reg_id_at] recognizes [hreg_at] at both widths. *)
Lemma pm_reg_id_hreg_at : forall half r,
  pm_reg_id_at half (hreg_at r half) = Some (PrHReg r).
Proof. destruct half, r; reflexivity. Qed.

(** [pm_reg_id_at] recognizes `%rcx` / `%ecx`. *)
Lemma pm_reg_id_rcx : forall half,
  pm_reg_id_at half (reg_name "c" half) = Some PrRcx.
Proof. destruct half; reflexivity. Qed.

(** [pm_reg_id_at] recognizes `%rax` / `%eax`. *)
Lemma pm_reg_id_rax : forall half,
  pm_reg_id_at half (reg_name "a" half) = Some PrRax.
Proof. destruct half; reflexivity. Qed.

(** Sequential execution chains across list concatenation. *)
Lemma pm_exec_lines_app : forall sym_env ls1 ls2 st st1,
  pm_exec_lines sym_env st ls1 = Some st1 ->
  pm_exec_lines sym_env st (ls1 ++ ls2) = pm_exec_lines sym_env st1 ls2.
Proof.
  intros sym_env ls1. induction ls1 as [|ln ls1' IH]; intros ls2 st st1 H1; simpl in *.
  - injection H1 as ->. reflexivity.
  - destruct (pm_exec_line sym_env st ln) as [st'|]; [exact (IH ls2 st' st1 H1) | discriminate].
Qed.

(** No [todo] line is ever accepted by [pm_exec_line]. *)
Lemma pm_exec_line_not_todo : forall sym_env st ln st',
  pm_exec_line sym_env st ln = Some st' -> is_todo ln = false.
Proof.
  intros sym_env st ln st' H.
  destruct ln as [| | op [suf|] ops | ]; simpl in *; try discriminate; reflexivity.
Qed.

(** Any line sequence accepted by [pm_exec_lines] has `first_todo ls = None`. *)
Lemma pm_exec_lines_no_todo : forall sym_env ls st st',
  pm_exec_lines sym_env st ls = Some st' -> first_todo ls = None.
Proof.
  intros sym_env ls. induction ls as [|ln ls' IH]; intros st st' H; simpl in *.
  - reflexivity.
  - destruct (pm_exec_line sym_env st ln) as [st1|] eqn:E; [|discriminate].
    rewrite (pm_exec_line_not_todo sym_env st ln st1 E).
    eapply IH; exact H.
Qed.

(** Moduli `two32` and `two64` keep values in `[0, two64)`. *)
Lemma mod_width_in_two64 : forall (half : bool) (x : Z),
  0 <= x mod (if half then two32 else two64) < two64.
Proof.
  intros [|] x; unfold two32, two64.
  - pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). lia.
  - apply Z.mod_pos_bound. lia.
Qed.

(** [load_const_reg] loads `n mod (if half then 2^32 else 2^64)` into target `id`. *)
Lemma load_const_reg_sound : forall sym_env st n half dst64 dst32 id,
  pm_reg64_id dst64 = Some id ->
  pm_reg32_id dst32 = Some id ->
  pm_exec_lines sym_env st (load_const_reg n half dst64 dst32) =
  Some (pm_set_reg st id (n mod (if half then two32 else two64))).
Proof.
  intros sym_env st n [|] dst64 dst32 id H64 H32; unfold load_const_reg.
  - simpl. rewrite H32. simpl.
    rewrite Z.mod_mod by (unfold two32; lia). reflexivity.
  - cbv zeta.
    set (u := n mod two64).
    set (s := if u >=? two63 then u - two64 else u).
    assert (Hu : 0 <= u < two64) by (unfold u, two64; apply Z.mod_pos_bound; lia).
    assert (Hs_mod : s mod two64 = u).
    { unfold s. destruct (u >=? two63) eqn:Ege.
      - replace (u - two64) with (u + (-1) * two64) by lia.
        rewrite Z_mod_plus_full. apply Z.mod_small. exact Hu.
      - apply Z.mod_small. exact Hu. }
    destruct ((0 <=? s) && (s <? two31)) eqn:E1.
    + apply Bool.andb_true_iff in E1. destruct E1 as [E1a E1b].
      apply Z.leb_le in E1a. apply Z.ltb_lt in E1b.
      simpl. rewrite H32. simpl.
      assert (Hs_eq : s = u).
      { unfold s in *. destruct (u >=? two63) eqn:Ege; [lia | reflexivity]. }
      rewrite Z.mod_small by (unfold two31, two32 in *; lia).
      rewrite Hs_eq. reflexivity.
    + destruct ((- two31 <=? s) && (s <? 0)) eqn:E2; simpl; rewrite H64; simpl;
        rewrite Hs_mod; reflexivity.
Qed.

(** [emit_save_cycle_tmp] copies `old` (`old <> PmCycleTmp`) into `%rcx`
    while preserving all other locations and [pm_mach_canonical]. *)
Lemma emit_save_cycle_tmp_sound : forall sym_env st old,
  pm_mach_canonical st ->
  old <> PmCycleTmp ->
  exists st1,
    pm_exec_lines sym_env st (emit_save_cycle_tmp old) = Some st1 /\
    pm_mach_canonical st1 /\
    pm_mach_env st1 PmCycleTmp = pm_mach_env st old /\
    (forall l, l <> PmCycleTmp -> pm_mach_env st1 l = pm_mach_env st l).
Proof.
  intros sym_env st [r | off |] Hcan Hneq; [| | contradiction].
  - eexists. split; [|split; [|split]].
    + simpl. rewrite pm_reg64_hreg. simpl. reflexivity.
    + intros [r' | off' |]; simpl.
      * exact (Hcan (PmReg r')).
      * exact (Hcan (PmSlot off')).
      * apply Z.mod_pos_bound. unfold two64; lia.
    + simpl. apply Z.mod_small. exact (Hcan (PmReg r)).
    + intros [r' | off' |] H; [reflexivity | reflexivity | contradiction].
  - eexists. split; [|split; [|split]].
    + simpl. reflexivity.
    + intros [r' | off' |]; simpl.
      * exact (Hcan (PmReg r')).
      * exact (Hcan (PmSlot off')).
      * apply Z.mod_pos_bound. unfold two64; lia.
    + simpl. replace (- - off) with off by lia.
      apply Z.mod_small. exact (Hcan (PmSlot off)).
    + intros [r' | off' |] H; [reflexivity | reflexivity | contradiction].
Qed.

(** Well-formedness of one [pmove] in location state `env`: non-scratch
    destination, 64-bit global addresses, and canonical 32-bit zero
    extension whenever `pmv_src_w m = true`. *)
Definition pmove_wf (env : pm_loc -> Z) (m : pmove) : Prop :=
  pmv_dst m <> PmCycleTmp /\
  match pmv_src m with
  | PsGlobal _ => pmv_half m = false
  | PsLoc l => pmv_src_w m = true -> env l < two32
  | PsConst _ => True
  end.

(** [emit_one_pmove] executes cleanly in [pm_exec_lines], preserves
    [pm_mach_canonical], sets `pmv_dst m` to [eval_pm_src], and preserves
    every other [pm_loc] (including `PmCycleTmp`, using `%rax` only as scratch). *)
Lemma emit_one_pmove_sound : forall sym_env st m,
  pm_mach_canonical st ->
  pmove_wf (pm_mach_env st) m ->
  exists st1,
    pm_exec_lines sym_env st (emit_one_pmove m) = Some st1 /\
    pm_mach_canonical st1 /\
    pm_mach_env st1 (pmv_dst m) = eval_pm_src sym_env (pm_mach_env st) (pmv_half m) (pmv_src m) /\
    (forall l, l <> pmv_dst m -> pm_mach_env st1 l = pm_mach_env st l).
Proof.
  intros sym_env st [half src_w [rd | off |] src] Hcan [Hdst Hsrc]; simpl in *; [| | contradiction].
  - destruct src as [[rs | soff |] | n | g].
    + destruct half; eexists; (split; [|split; [|split]]).
      * unfold emit_one_pmove; simpl. rewrite !pm_reg32_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 true) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
      * unfold emit_one_pmove; simpl. rewrite !pm_reg64_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 false) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
    + destruct half; eexists; (split; [|split; [|split]]).
      * unfold emit_one_pmove; simpl. rewrite pm_reg32_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 true) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. replace (- - soff) with soff by lia. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
      * unfold emit_one_pmove; simpl. rewrite pm_reg64_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 false) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. replace (- - soff) with soff by lia. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
    + destruct half; eexists; (split; [|split; [|split]]).
      * unfold emit_one_pmove; simpl. rewrite pm_reg32_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 true) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
      * unfold emit_one_pmove; simpl. rewrite pm_reg64_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 false) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
    + eexists. split; [|split; [|split]].
      * unfold emit_one_pmove; simpl.
        exact (load_const_reg_sound sym_env st n half (hreg64 rd) (hreg32 rd) (PrHReg rd)
                 (pm_reg64_hreg rd) (pm_reg32_hreg rd)).
      * intros [r' | off' |]; simpl.
        -- destruct (hreg_eqb r' rd); [apply mod_width_in_two64 | exact (Hcan (PmReg r'))].
        -- exact (Hcan (PmSlot off')).
        -- exact (Hcan PmCycleTmp).
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [|reflexivity].
        apply hreg_eqb_spec in E. subst r'. contradiction.
    + subst half. eexists. split; [|split; [|split]].
      * unfold emit_one_pmove; simpl. rewrite pm_reg64_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl.
        -- destruct (hreg_eqb r' rd); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmReg r'))].
        -- exact (Hcan (PmSlot off')).
        -- exact (Hcan PmCycleTmp).
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [|reflexivity].
        apply hreg_eqb_spec in E. subst r'. contradiction.
  - destruct src as [[rs | soff |] | n | g].
    + destruct half.
      * eexists. split; [|split; [|split]].
        -- unfold emit_one_pmove; simpl. rewrite pm_reg32_hreg; simpl; reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
           apply Z.mod_small. pose proof (Z.mod_pos_bound (pm_hreg st rs) two32 ltac:(unfold two32; lia)).
           unfold two32, two64 in *; lia.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
      * eexists. split; [|split; [|split]].
        -- unfold emit_one_pmove; simpl. rewrite pm_reg64_hreg; simpl; reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl. reflexivity.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
    + destruct half; eexists; (split; [|split; [|split]]).
      * unfold emit_one_pmove; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
      * simpl. replace (- - off) with off by lia; replace (- - soff) with soff by lia; rewrite Z.eqb_refl.
        apply Z.mod_small. pose proof (Z.mod_pos_bound (pm_slot st soff) two32 ltac:(unfold two32; lia)).
        unfold two32, two64 in *; lia.
      * intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
      * unfold emit_one_pmove; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
      * simpl. replace (- - off) with off by lia; replace (- - soff) with soff by lia; rewrite Z.eqb_refl.
        apply Z.mod_mod. unfold two64; lia.
      * intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
    + destruct half.
      * eexists. split; [|split; [|split]].
        -- unfold emit_one_pmove; simpl. reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
           apply Z.mod_small. pose proof (Z.mod_pos_bound (pm_rcx st) two32 ltac:(unfold two32; lia)).
           unfold two32, two64 in *; lia.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
      * eexists. split; [|split; [|split]].
        -- unfold emit_one_pmove; simpl. reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl. reflexivity.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
    + destruct half.
      * unfold emit_one_pmove; simpl.
        eexists. split; [|split; [|split]].
        -- reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
           rewrite Z.mod_mod by (unfold two32; lia).
           apply Z.mod_small. pose proof (Z.mod_pos_bound n two32 ltac:(unfold two32; lia)).
           unfold two32, two64 in *; lia.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
      * cbn [emit_one_pmove pmv_half pmv_dst pmv_src negb].
        destruct (integer_immediate false n) as [imm_v|] eqn:Eimm.
        -- eexists. split; [|split; [|split]].
           ++ simpl. reflexivity.
           ++ intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
              replace (- - off) with off by lia.
              destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
           ++ simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
              exact (imm32_congruent false n imm_v Eimm).
           ++ intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
              replace (- - off) with off by lia.
              destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
        -- pose proof (load_const_reg_sound sym_env st n false "rax" "eax" PrRax eq_refl eq_refl) as Hlc.
           rewrite (pm_exec_lines_app sym_env _ _ st _ Hlc). simpl.
           eexists. split; [reflexivity | split; [|split]].
           ++ intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
              replace (- - off) with off by lia.
              destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
           ++ simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
              apply Z.mod_mod. unfold two64; lia.
           ++ intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
              replace (- - off) with off by lia.
              destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
    + subst half. eexists. split; [|split; [|split]].
      * unfold emit_one_pmove; simpl. reflexivity.
      * intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
      * simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
        apply Z.mod_mod. unfold two64; lia.
      * intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
Qed.

(** Characterization of [find_pmove_dst] on duplicate-free destination lists. *)
Lemma find_pmove_dst_some : forall ms l m,
  find_pmove_dst l ms = Some m -> In m ms /\ pmv_dst m = l.
Proof.
  induction ms as [|m0 ms' IH]; intros l m H; simpl in *; [discriminate|].
  destruct (pm_loc_eqb l (pmv_dst m0)) eqn:E.
  - injection H as <-. apply pm_loc_eqb_spec in E. split; [left; reflexivity | symmetry; exact E].
  - destruct (IH l m H) as [Hin Hdst]. split; [right; exact Hin | exact Hdst].
Qed.

(** [find_pmove_dst] returns `None` iff `l` is not in `map pmv_dst ms`. *)
Lemma find_pmove_dst_none : forall ms l,
  find_pmove_dst l ms = None <-> ~ In l (map pmv_dst ms).
Proof.
  induction ms as [|m0 ms' IH]; intro l; simpl.
  - split; auto.
  - destruct (pm_loc_eqb l (pmv_dst m0)) eqn:E.
    + apply pm_loc_eqb_spec in E. subst l.
      split; [discriminate | intro H; exfalso; apply H; left; reflexivity].
    + rewrite IH. split.
      * intros Hnot [Heq | Hin]; [subst; rewrite pm_loc_eqb_refl in E; discriminate | contradiction].
      * intros Hnot. intro Hin. apply Hnot. right. exact Hin.
Qed.

(** Under `NoDup (map pmv_dst ms)`, membership determines [find_pmove_dst]. *)
Lemma find_pmove_dst_in : forall ms m,
  NoDup (map pmv_dst ms) ->
  In m ms ->
  find_pmove_dst (pmv_dst m) ms = Some m.
Proof.
  induction ms as [|m0 ms' IH]; intros m Hnd Hin; simpl in *; [contradiction|].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct Hin as [<- | Hin'].
  - rewrite pm_loc_eqb_refl. reflexivity.
  - destruct (pm_loc_eqb (pmv_dst m) (pmv_dst m0)) eqn:E.
    + apply pm_loc_eqb_spec in E. exfalso. apply Hnotin.
      rewrite <- E. apply in_map. exact Hin'.
    + apply IH; assumption.
Qed.

(** A well-formed no-op move evaluates to the destination's existing value. *)
Lemma pmove_nop_eval : forall sym_env st m,
  pm_mach_canonical st ->
  pmove_wf (pm_mach_env st) m ->
  pmove_is_nop m = true ->
  eval_pm_src sym_env (pm_mach_env st) (pmv_half m) (pmv_src m)
  = pm_mach_env st (pmv_dst m).
Proof.
  intros sym_env st [half src_w dst [l | n | g]] Hcan [_ Hsrc] Hnop;
    cbn [pmove_is_nop pmv_src pmv_dst pmv_half pmv_src_w] in Hnop; try discriminate.
  apply Bool.andb_true_iff in Hnop. destruct Hnop as [El Ew].
  apply pm_loc_eqb_spec in El. subst dst.
  pose proof (Hcan l) as Hbound.
  destruct half; simpl in *.
  - specialize (Hsrc Ew). apply Z.mod_small. split; [lia | exact Hsrc].
  - apply Z.mod_small. exact Hbound.
Qed.

(** [loc_read_in_pmoves] distributes over list concatenation. *)
Lemma loc_read_in_pmoves_app : forall l xs ys,
  loc_read_in_pmoves l (xs ++ ys) = loc_read_in_pmoves l xs || loc_read_in_pmoves l ys.
Proof.
  intros l xs ys. induction xs as [|m xs' IH]; simpl; [reflexivity|].
  destruct (match pmv_src m with PsLoc l' => pm_loc_eqb l l' | _ => false end);
    [reflexivity | exact IH].
Qed.

(** [loc_read_in_pmoves] is invariant under list reversal. *)
Lemma loc_read_in_pmoves_rev : forall l xs,
  loc_read_in_pmoves l (rev xs) = loc_read_in_pmoves l xs.
Proof.
  intros l xs. induction xs as [|m xs' IH]; simpl; [reflexivity|].
  rewrite loc_read_in_pmoves_app, IH. simpl.
  destruct (match pmv_src m with PsLoc l' => pm_loc_eqb l l' | _ => false end);
    [apply Bool.orb_true_r | apply Bool.orb_false_r].
Qed.

(** Helper characterization of [drop_nop_pmoves_acc]. *)
Lemma drop_nop_pmoves_acc_eq : forall ms acc,
  drop_nop_pmoves_acc ms acc = rev acc ++ filter (fun m => negb (pmove_is_nop m)) ms.
Proof.
  induction ms as [|m ms' IH]; intro acc; simpl.
  - unfold rev'. rewrite <- rev_alt, app_nil_r. reflexivity.
  - destruct (pmove_is_nop m).
    + apply IH.
    + rewrite IH. simpl. rewrite <- app_assoc. reflexivity.
Qed.

(** Sublist preservation of `NoDup (map f xs)` under `filter`. *)
Lemma nodup_map_filter : forall (A B : Type) (f : A -> B) (p : A -> bool) (xs : list A),
  NoDup (map f xs) -> NoDup (map f (filter p xs)).
Proof.
  intros A B f p xs. induction xs as [|x xs' IH]; intro Hnd; simpl in *; [constructor|].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct (p x).
  - simpl. constructor; [|apply IH; exact Hnd'].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [x' [Heq Hin']].
    apply filter_In in Hin'. apply Hnotin. rewrite <- Heq. apply in_map. exact (proj1 Hin').
  - apply IH. exact Hnd'.
Qed.

(** Dropping well-formed no-op moves preserves `NoDup`, unread locations,
    [pmove_wf], and [simul_pmoves]. *)
Lemma drop_nop_pmoves_sound : forall sym_env st ms,
  pm_mach_canonical st ->
  NoDup (map pmv_dst ms) ->
  loc_read_in_pmoves PmCycleTmp ms = false ->
  Forall (pmove_wf (pm_mach_env st)) ms ->
  NoDup (map pmv_dst (drop_nop_pmoves_acc ms [])) /\
  loc_read_in_pmoves PmCycleTmp (drop_nop_pmoves_acc ms []) = false /\
  Forall (pmove_wf (pm_mach_env st)) (drop_nop_pmoves_acc ms []) /\
  (forall l, simul_pmoves sym_env (pm_mach_env st) (drop_nop_pmoves_acc ms []) l
             = simul_pmoves sym_env (pm_mach_env st) ms l).
Proof.
  intros sym_env st ms Hcan Hnd Hunread Hwf.
  rewrite !drop_nop_pmoves_acc_eq. simpl.
  set (clean := filter (fun m => negb (pmove_is_nop m)) ms).
  split; [apply nodup_map_filter; exact Hnd | split; [|split]].
  - unfold clean. clear -Hunread.
    induction ms as [|m ms' IH]; [reflexivity|].
    cbn [loc_read_in_pmoves] in Hunread; cbv zeta in Hunread.
    destruct (match pmv_src m with PsLoc l' => pm_loc_eqb PmCycleTmp l' | _ => false end) eqn:Eh;
      [discriminate|].
    cbn [filter]. destruct (pmove_is_nop m); cbn [negb loc_read_in_pmoves]; cbv zeta.
    + exact (IH Hunread).
    + rewrite Eh. exact (IH Hunread).
  - apply Forall_forall. intros m Hm. unfold clean in Hm.
    apply filter_In in Hm. rewrite Forall_forall in Hwf. apply Hwf. exact (proj1 Hm).
  - intro l. unfold simul_pmoves.
    destruct (find_pmove_dst l clean) as [mc|] eqn:Ec.
    + destruct (find_pmove_dst_some clean l mc Ec) as [Hinc Hd].
      subst l. unfold clean in Hinc. apply filter_In in Hinc.
      rewrite (find_pmove_dst_in ms mc Hnd (proj1 Hinc)). reflexivity.
    + apply find_pmove_dst_none in Ec.
      destruct (find_pmove_dst l ms) as [mm|] eqn:Em; [|reflexivity].
      destruct (find_pmove_dst_some ms l mm Em) as [Hinm Hd]. subst l.
      destruct (pmove_is_nop mm) eqn:Enop.
      * rewrite Forall_forall in Hwf.
        symmetry. apply (pmove_nop_eval sym_env st mm Hcan (Hwf mm Hinm) Enop).
      * exfalso. apply Ec. apply in_map. unfold clean.
        apply filter_In. split; [exact Hinm | rewrite Enop; reflexivity].
Qed.

(** Helper: `NoDup (map f (xs ++ y :: zs))` implies `NoDup (map f ((y :: xs) ++ zs))`. *)
Lemma nodup_map_move_mid : forall (A B : Type) (f : A -> B) (xs zs : list A) (y : A),
  NoDup (map f (xs ++ y :: zs)) -> NoDup (map f ((y :: xs) ++ zs)).
Proof.
  intros A B f xs zs y Hnd. rewrite map_app in Hnd. simpl in Hnd.
  rewrite map_app. simpl.
  assert (Hy : ~ In (f y) (map f xs) /\ ~ In (f y) (map f zs) /\ NoDup (map f xs ++ map f zs)).
  { clear -Hnd. induction (map f xs) as [|a l IH]; simpl in *.
    - inversion Hnd as [| ? ? Hny Hnd']; subst. split; [auto | split; assumption].
    - inversion Hnd as [| ? ? Hna Hnd']; subst.
      destruct (IH Hnd') as [Hy1 [Hy2 Hnd'']].
      split.
      + intros [Heq | Hin]; [apply Hna; apply in_or_app; right; left; symmetry; exact Heq | contradiction].
      + split; [exact Hy2 |].
        constructor; [|exact Hnd''].
        intro Hin. apply Hna. apply in_or_app.
        apply in_app_or in Hin. destruct Hin as [H1 | H2]; [left; exact H1 | right; right; exact H2]. }
  destruct Hy as [Hy1 [Hy2 Hnd2]].
  constructor; [|exact Hnd2].
  intro Hin. apply in_app_or in Hin. destruct Hin; contradiction.
Qed.

(** When [pick_ready_pmove] returns `Some (m, rest)`, `m :: rest` is a
    permutation of `rev prefix_rev ++ rest0` and `pmv_dst m` is unread in `rest`. *)
Lemma pick_ready_pmove_some : forall rest0 prefix_rev m rest,
  pick_ready_pmove rest0 prefix_rev = Some (m, rest) ->
  loc_read_in_pmoves (pmv_dst m) rest = false /\
  In m rest0 /\
  (forall x, In x (rev prefix_rev ++ rest0) <-> x = m \/ In x rest) /\
  (NoDup (map pmv_dst (rev prefix_rev ++ rest0)) -> NoDup (map pmv_dst (m :: rest))) /\
  (length (rev prefix_rev ++ rest0) = S (length rest))%nat.
Proof.
  induction rest0 as [|r0 rs IH]; intros prefix_rev m rest H; simpl in *; [discriminate|].
  destruct (negb (loc_read_in_pmoves (pmv_dst r0) prefix_rev) &&
            negb (loc_read_in_pmoves (pmv_dst r0) rs)) eqn:Eok.
  - injection H as <- <-.
    apply Bool.andb_true_iff in Eok. destruct Eok as [Ep Er].
    apply Bool.negb_true_iff in Ep. apply Bool.negb_true_iff in Er.
    rewrite rev_append_rev.
    split; [|split; [|split; [|split]]].
    + rewrite loc_read_in_pmoves_app, loc_read_in_pmoves_rev, Ep, Er. reflexivity.
    + left. reflexivity.
    + intro x. rewrite !in_app_iff. simpl. intuition congruence.
    + intro Hnd. exact (nodup_map_move_mid pmove pm_loc pmv_dst (rev prefix_rev) rs r0 Hnd).
    + rewrite !length_app. simpl. lia.
  - assert (Heq_list : rev (r0 :: prefix_rev) ++ rs = rev prefix_rev ++ r0 :: rs).
    { simpl. rewrite <- app_assoc. reflexivity. }
    destruct (IH (r0 :: prefix_rev) m rest H) as [Hnr [Hin [Hiff [Hnd Hlen]]]].
    rewrite Heq_list in Hiff, Hnd, Hlen.
    split; [exact Hnr | split; [right; exact Hin | split; [exact Hiff | split; [exact Hnd | exact Hlen]]]].
Qed.

(** Extract all location operands read by `ms`. *)
Fixpoint pmove_src_locs (ms : list pmove) : list pm_loc :=
  match ms with
  | [] => []
  | m :: ms' =>
      match pmv_src m with
      | PsLoc l => l :: pmove_src_locs ms'
      | _ => pmove_src_locs ms'
      end
  end.

(** [loc_read_in_pmoves] reflects membership in [pmove_src_locs]. *)
Lemma loc_read_in_pmoves_iff : forall l ms,
  loc_read_in_pmoves l ms = true <-> In l (pmove_src_locs ms).
Proof.
  intros l ms. induction ms as [|m ms' IH]; simpl.
  - split; [discriminate | contradiction].
  - destruct (pmv_src m) as [l' | n | g].
    + simpl. destruct (pm_loc_eqb l l') eqn:E.
      * apply pm_loc_eqb_spec in E. subst l'. split; auto.
      * rewrite IH. split; [right; exact H | intros [Heq | Hin]; [subst; rewrite pm_loc_eqb_refl in E; discriminate | exact Hin]].
    + exact IH.
    + exact IH.
Qed.

(** [pmove_src_locs] has at most `length ms` elements. *)
Lemma pmove_src_locs_len : forall ms,
  (length (pmove_src_locs ms) <= length ms)%nat.
Proof.
  induction ms as [|m ms' IH]; simpl; [lia|].
  destruct (pmv_src m); simpl; lia.
Qed.

(** Remove the first occurrence of `x` from `ls`. *)
Fixpoint remove_one_loc (x : pm_loc) (ls : list pm_loc) : list pm_loc :=
  match ls with
  | [] => []
  | y :: ls' => if pm_loc_eqb x y then ls' else y :: remove_one_loc x ls'
  end.

(** Removing a present element strictly decreases length. *)
Lemma remove_one_loc_lt : forall x ls,
  In x ls -> (length (remove_one_loc x ls) < length ls)%nat.
Proof.
  intros x ls. induction ls as [|y ls' IH]; intro Hin; simpl in *; [contradiction|].
  destruct (pm_loc_eqb x y) eqn:E; [lia|].
  destruct Hin as [Heq | Hin']; [subst y; rewrite pm_loc_eqb_refl in E; discriminate|].
  specialize (IH Hin'). simpl. lia.
Qed.

(** Removing `x` preserves every `z <> x`. *)
Lemma remove_one_loc_in : forall x z ls,
  z <> x -> In z ls -> In z (remove_one_loc x ls).
Proof.
  intros x z ls Hneq. induction ls as [|y ls' IH]; intro Hin; simpl in *; [contradiction|].
  destruct (pm_loc_eqb x y) eqn:E.
  - apply pm_loc_eqb_spec in E. subst y.
    destruct Hin as [Heq | Hin']; [symmetry in Heq; contradiction | exact Hin'].
  - destruct Hin as [<- | Hin']; [left; reflexivity | right; apply IH; exact Hin'].
Qed.

(** Finite pigeonhole lemma on `pm_loc`: a duplicate-free list `ds`
    included in `ls` has `length ds <= length ls`. *)
Lemma nodup_locs_incl_le : forall (ds ls : list pm_loc),
  NoDup ds ->
  (forall x, In x ds -> In x ls) ->
  (length ds <= length ls)%nat.
Proof.
  induction ds as [|d ds' IH]; intros ls Hnd Hincl; simpl; [lia|].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  pose proof (remove_one_loc_lt d ls (Hincl d (or_introl eq_refl))) as Hlt.
  assert (Hsub : forall x, In x ds' -> In x (remove_one_loc d ls)).
  { intros x Hx. apply remove_one_loc_in.
    - intro Heq. subst x. contradiction.
    - apply Hincl. right. exact Hx. }
  specialize (IH (remove_one_loc d ls) Hnd' Hsub). lia.
Qed.

(** Helper: extract an explicit move reading `l` when [loc_read_in_pmoves] returns `true`. *)
Lemma loc_read_in_pmoves_exists : forall l xs,
  loc_read_in_pmoves l xs = true ->
  exists q, In q xs /\ pmv_src q = PsLoc l.
Proof.
  intros l xs. induction xs as [|x xs' IH]; intro Hlr; simpl in *; [discriminate|].
  destruct (pmv_src x) as [lx | | ] eqn:Ex.
  - destruct (pm_loc_eqb l lx) eqn:Elx.
    + apply pm_loc_eqb_spec in Elx. subst lx. exists x. split; [left; reflexivity | exact Ex].
    + destruct (IH Hlr) as [q [Hq1 Hq2]]. exists q. split; [right; exact Hq1 | exact Hq2].
  - destruct (IH Hlr) as [q [Hq1 Hq2]]. exists q. split; [right; exact Hq1 | exact Hq2].
  - destruct (IH Hlr) as [q [Hq1 Hq2]]. exists q. split; [right; exact Hq1 | exact Hq2].
Qed.

(** When [pick_ready_pmove] returns `None` on duplicate-free destinations,
    every move `m` in `prefix_rev ++ rest0` has its destination read by
    some move `q` with `pmv_dst q <> pmv_dst m`. *)
Lemma pick_ready_pmove_none : forall rest0 prefix_rev,
  pick_ready_pmove rest0 prefix_rev = None ->
  NoDup (map pmv_dst (prefix_rev ++ rest0)) ->
  (forall p, In p prefix_rev ->
     exists q, In q (prefix_rev ++ rest0) /\ pmv_dst q <> pmv_dst p /\ pmv_src q = PsLoc (pmv_dst p)) ->
  forall m, In m (prefix_rev ++ rest0) ->
    exists q, In q (prefix_rev ++ rest0) /\ pmv_dst q <> pmv_dst m /\ pmv_src q = PsLoc (pmv_dst m).
Proof.
  induction rest0 as [|r0 rs IH]; intros prefix_rev Hnone Hnd Hpref m Hm; simpl in *.
  - rewrite app_nil_r in *. apply Hpref. exact Hm.
  - destruct (negb (loc_read_in_pmoves (pmv_dst r0) prefix_rev) &&
              negb (loc_read_in_pmoves (pmv_dst r0) rs)) eqn:Eok; [discriminate|].
    assert (Hr0_disj : ~ In (pmv_dst r0) (map pmv_dst prefix_rev) /\ ~ In (pmv_dst r0) (map pmv_dst rs)).
    { pose proof (nodup_map_move_mid pmove pm_loc pmv_dst prefix_rev rs r0 Hnd) as Hnd'.
      simpl in Hnd'. inversion Hnd' as [| ? ? Hnot _]; subst.
      rewrite map_app in Hnot. split; intro Hin; apply Hnot; apply in_or_app; [left | right]; exact Hin. }
    assert (Hr0 : exists q, In q ((r0 :: prefix_rev) ++ rs) /\
                            pmv_dst q <> pmv_dst r0 /\ pmv_src q = PsLoc (pmv_dst r0)).
    { apply Bool.andb_false_iff in Eok.
      destruct Eok as [Ep | Er]; apply Bool.negb_false_iff in Ep + apply Bool.negb_false_iff in Er.
      - destruct (loc_read_in_pmoves_exists (pmv_dst r0) prefix_rev Ep) as [q [Hq1 Hq2]].
        exists q. split; [simpl; right; apply in_or_app; left; exact Hq1 | split; [|exact Hq2]].
        intro Heq. apply (proj1 Hr0_disj). rewrite <- Heq. apply in_map. exact Hq1.
      - destruct (loc_read_in_pmoves_exists (pmv_dst r0) rs Er) as [q [Hq1 Hq2]].
        exists q. split; [simpl; right; apply in_or_app; right; exact Hq1 | split; [|exact Hq2]].
        intro Heq. apply (proj2 Hr0_disj). rewrite <- Heq. apply in_map. exact Hq1. }
    assert (Hpref' : forall p, In p (r0 :: prefix_rev) ->
               exists q, In q ((r0 :: prefix_rev) ++ rs) /\
                         pmv_dst q <> pmv_dst p /\ pmv_src q = PsLoc (pmv_dst p)).
    { intros p [<- | Hp]; [exact Hr0|].
      destruct (Hpref p Hp) as [q [Hq_in [Hq_neq Hq_src]]].
      exists q. split; [|split; [exact Hq_neq | exact Hq_src]].
      simpl. apply in_app_or in Hq_in. destruct Hq_in as [H1 | [<- | H2]];
        [right; apply in_or_app; left; exact H1 | left; reflexivity | right; apply in_or_app; right; exact H2]. }
    pose proof (nodup_map_move_mid pmove pm_loc pmv_dst prefix_rev rs r0 Hnd) as Hnd'.
    assert (Hm' : In m ((r0 :: prefix_rev) ++ rs)).
    { simpl. apply in_app_or in Hm. destruct Hm as [H1 | [<- | H2]];
        [right; apply in_or_app; left; exact H1 | left; reflexivity | right; apply in_or_app; right; exact H2]. }
    destruct (IH (r0 :: prefix_rev) Hnone Hnd' Hpref' m Hm') as [q [Hq_in [Hq_neq Hq_src]]].
    exists q. split; [|split; [exact Hq_neq | exact Hq_src]].
    simpl in Hq_in. destruct Hq_in as [<- | Hq_rest].
    + apply in_or_app. right. left. reflexivity.
    + apply in_app_or in Hq_rest. destruct Hq_rest as [H1 | H2];
        apply in_or_app; [left; exact H1 | right; right; exact H2].
Qed.

(** Membership in `ms` with `pmv_src m = PsLoc l` implies membership in [pmove_src_locs]. *)
Lemma in_pmove_src_locs : forall m ms l,
  In m ms -> pmv_src m = PsLoc l -> In l (pmove_src_locs ms).
Proof.
  intros m ms l. induction ms as [|x xs IH]; intros Hm Hsrc; simpl in *; [contradiction|].
  destruct Hm as [<- | Hm']; [rewrite Hsrc; left; reflexivity|].
  destruct (pmv_src x); [right | |]; apply IH; assumption.
Qed.

(** Pigeonhole consequence at a cycle break: when [pick_ready_pmove] returns
    `None` on distinct non-`PmCycleTmp` destinations, `PmCycleTmp` is NOT
    read anywhere in `ms` (even after earlier cycles used `%rcx`), and
    every move in `ms` has its destination read by another move in `ms`. *)
Lemma no_ready_cycle_tmp_unread : forall ms,
  NoDup (map pmv_dst ms) ->
  (forall m, In m ms -> pmv_dst m <> PmCycleTmp) ->
  pick_ready_pmove ms [] = None ->
  loc_read_in_pmoves PmCycleTmp ms = false /\
  (forall m, In m ms ->
     exists q, In q ms /\ pmv_dst q <> pmv_dst m /\ pmv_src q = PsLoc (pmv_dst m)).
Proof.
  intros ms Hnd Hnot_tmp Hnone.
  assert (Hall : forall m, In m ms ->
            exists q, In q ms /\ pmv_dst q <> pmv_dst m /\ pmv_src q = PsLoc (pmv_dst m)).
  { intros m Hm.
    apply (pick_ready_pmove_none ms [] Hnone Hnd (fun p Hp => False_ind _ Hp) m Hm). }
  split; [|exact Hall].
  destruct (loc_read_in_pmoves PmCycleTmp ms) eqn:Etmp; [|reflexivity].
  exfalso.
  apply loc_read_in_pmoves_iff in Etmp.
  assert (Hincl : forall d, In d (map pmv_dst ms) -> In d (remove_one_loc PmCycleTmp (pmove_src_locs ms))).
  { intros d Hd. apply in_map_iff in Hd. destruct Hd as [m [<- Hm]].
    destruct (Hall m Hm) as [q [Hq_in [_ Hq_src]]].
    apply remove_one_loc_in.
    - apply Hnot_tmp. exact Hm.
    - exact (in_pmove_src_locs q ms (pmv_dst m) Hq_in Hq_src). }
  pose proof (nodup_locs_incl_le (map pmv_dst ms)
                (remove_one_loc PmCycleTmp (pmove_src_locs ms)) Hnd Hincl) as Hle.
  pose proof (remove_one_loc_lt PmCycleTmp (pmove_src_locs ms) Etmp) as Hlt.
  pose proof (pmove_src_locs_len ms) as Hlen.
  rewrite length_map in Hle. lia.
Qed.

(** Single-element source substitution used by [subst_pmove_src]. *)
Definition subst_pmove_one (old : pm_loc) (m : pmove) : pmove :=
  let src' :=
    match pmv_src m with
    | PsLoc l => if pm_loc_eqb l old then PsLoc PmCycleTmp else PsLoc l
    | s => s
    end in
  mkPMove (pmv_half m) (pmv_src_w m) (pmv_dst m) src'.

(** Helper characterization of [subst_pmove_src]. *)
Lemma subst_pmove_src_eq : forall old ms acc,
  subst_pmove_src old ms acc =
  rev acc ++ filter (fun m => negb (pmove_is_nop m)) (map (subst_pmove_one old) ms).
Proof.
  intros old ms. induction ms as [|m ms' IH]; intro acc; simpl.
  - unfold rev'. rewrite <- rev_alt, app_nil_r. reflexivity.
  - unfold subst_pmove_one at 1.
    destruct (pmove_is_nop (mkPMove (pmv_half m) (pmv_src_w m) (pmv_dst m)
                (match pmv_src m with
                 | PsLoc l => if pm_loc_eqb l old then PsLoc PmCycleTmp else PsLoc l
                 | s => s
                 end))).
    + apply IH.
    + rewrite IH. simpl. rewrite <- app_assoc. reflexivity.
Qed.

(** Cycle-breaking transformation [subst_pmove_src] after saving `old` into
    `PmCycleTmp`: preserves `NoDup`, [pmove_wf], and [simul_pmoves] on all
    non-scratch locations, does not grow `ms`, and marks `PmCycleTmp` read. *)
Lemma subst_pmove_src_sound : forall sym_env st st1 old ms,
  pm_mach_canonical st ->
  pm_mach_canonical st1 ->
  old <> PmCycleTmp ->
  loc_read_in_pmoves PmCycleTmp ms = false ->
  NoDup (map pmv_dst ms) ->
  Forall (pmove_wf (pm_mach_env st)) ms ->
  pm_mach_env st1 PmCycleTmp = pm_mach_env st old ->
  (forall l, l <> PmCycleTmp -> pm_mach_env st1 l = pm_mach_env st l) ->
  (exists q, In q ms /\ pmv_dst q <> old /\ pmv_src q = PsLoc old) ->
  NoDup (map pmv_dst (subst_pmove_src old ms [])) /\
  Forall (pmove_wf (pm_mach_env st1)) (subst_pmove_src old ms []) /\
  (length (subst_pmove_src old ms []) <= length ms)%nat /\
  loc_read_in_pmoves PmCycleTmp (subst_pmove_src old ms []) = true /\
  (forall l, l <> PmCycleTmp ->
     simul_pmoves sym_env (pm_mach_env st1) (subst_pmove_src old ms []) l
     = simul_pmoves sym_env (pm_mach_env st) ms l).
Proof.
  intros sym_env st st1 old ms Hcan Hcan1 Hold_neq Hunread Hnd Hwf Htmp Hother [q [Hq_in [Hq_dst Hq_src]]].
  rewrite !subst_pmove_src_eq. simpl.
  set (mapped := map (subst_pmove_one old) ms).
  set (ms' := filter (fun m => negb (pmove_is_nop m)) mapped).
  assert (Hmap_dst : map pmv_dst mapped = map pmv_dst ms).
  { unfold mapped. rewrite map_map. reflexivity. }
  assert (Hnd_mapped : NoDup (map pmv_dst mapped)) by (rewrite Hmap_dst; exact Hnd).
  assert (Hnot_tmp_src : forall m, In m ms -> pmv_src m <> PsLoc PmCycleTmp).
  { intros m Hm Heq.
    pose proof (proj2 (loc_read_in_pmoves_iff PmCycleTmp ms)
                  (in_pmove_src_locs m ms PmCycleTmp Hm Heq)) as Hrd.
    rewrite Hunread in Hrd. discriminate. }
  assert (Heval_one : forall m, In m ms ->
            eval_pm_src sym_env (pm_mach_env st1)
              (pmv_half (subst_pmove_one old m)) (pmv_src (subst_pmove_one old m)) =
            eval_pm_src sym_env (pm_mach_env st) (pmv_half m) (pmv_src m)).
  { intros m Hm. pose proof (Hnot_tmp_src m Hm) as Hnt.
    unfold subst_pmove_one, eval_pm_src. simpl.
    destruct (pmv_src m) as [l | n | g]; [|reflexivity | reflexivity].
    destruct (pm_loc_eqb l old) eqn:Elo.
    - apply pm_loc_eqb_spec in Elo. subst l. rewrite Htmp. reflexivity.
    - rewrite Hother; [reflexivity | congruence]. }
  assert (Hwf_mapped : Forall (pmove_wf (pm_mach_env st1)) mapped).
  { apply Forall_forall. intros m' Hm'. unfold mapped in Hm'.
    apply in_map_iff in Hm'. destruct Hm' as [m [<- Hm]].
    rewrite Forall_forall in Hwf.
    pose proof (Hwf m Hm) as [Hdst Hsrc].
    pose proof (Hnot_tmp_src m Hm) as Hnt.
    unfold subst_pmove_one, pmove_wf; simpl. split; [exact Hdst|].
    destruct (pmv_src m) as [l | n | g]; [|exact I | exact Hsrc].
    destruct (pm_loc_eqb l old) eqn:Elo.
    - apply pm_loc_eqb_spec in Elo. subst l. rewrite Htmp. exact Hsrc.
    - rewrite Hother by congruence. exact Hsrc. }
  split; [apply nodup_map_filter; exact Hnd_mapped | split; [|split; [|split]]].
  - apply Forall_forall. intros x Hx. unfold ms' in Hx.
    apply filter_In in Hx. rewrite Forall_forall in Hwf_mapped.
    apply Hwf_mapped. exact (proj1 Hx).
  - transitivity (length mapped).
    + unfold ms'. clear. induction mapped as [|x xs IH]; simpl; [lia|].
      destruct (negb (pmove_is_nop x)); simpl; lia.
    + unfold mapped. rewrite length_map. lia.
  - apply loc_read_in_pmoves_iff.
    assert (Hq'_in : In (subst_pmove_one old q) ms').
    { unfold ms'. apply filter_In. split.
      - unfold mapped. apply in_map. exact Hq_in.
      - unfold subst_pmove_one; rewrite Hq_src, pm_loc_eqb_refl;
          cbn [pmove_is_nop pmv_src pmv_dst pmv_half pmv_src_w negb].
        rewrite Forall_forall in Hwf. pose proof (proj1 (Hwf q Hq_in)) as Hqd.
        destruct (pm_loc_eqb (pmv_dst q) PmCycleTmp) eqn:Eb; [|reflexivity].
        apply pm_loc_eqb_spec in Eb. contradiction. }
    assert (Hq'_src : pmv_src (subst_pmove_one old q) = PsLoc PmCycleTmp).
    { unfold subst_pmove_one. rewrite Hq_src, pm_loc_eqb_refl. reflexivity. }
    exact (in_pmove_src_locs (subst_pmove_one old q) ms' PmCycleTmp Hq'_in Hq'_src).
  - intros l Hl_neq. unfold simul_pmoves.
    destruct (find_pmove_dst l ms') as [mc|] eqn:Ec.
    + destruct (find_pmove_dst_some ms' l mc Ec) as [Hinc Hd]. subst l.
      unfold ms' in Hinc. apply filter_In in Hinc. destruct Hinc as [Hin_map _].
      unfold mapped in Hin_map. apply in_map_iff in Hin_map.
      destruct Hin_map as [m [Heqm Hm_in]]. subst mc.
      change (pmv_dst (subst_pmove_one old m)) with (pmv_dst m) in *.
      rewrite (find_pmove_dst_in ms m Hnd Hm_in).
      exact (Heval_one m Hm_in).
    + apply find_pmove_dst_none in Ec.
      destruct (find_pmove_dst l ms) as [mm|] eqn:Em; [|exact (Hother l Hl_neq)].
      destruct (find_pmove_dst_some ms l mm Em) as [Hinm Hd]. subst l.
      destruct (pmove_is_nop (subst_pmove_one old mm)) eqn:Enop.
      * rewrite <- (Heval_one mm Hinm).
        rewrite Forall_forall in Hwf_mapped.
        assert (Hin_map : In (subst_pmove_one old mm) mapped) by (unfold mapped; apply in_map; exact Hinm).
        pose proof (pmove_nop_eval sym_env st1 (subst_pmove_one old mm) Hcan1 (Hwf_mapped _ Hin_map) Enop) as Hnop1.
        change (pmv_dst (subst_pmove_one old mm)) with (pmv_dst mm) in Hnop1.
        rewrite Hnop1. reflexivity.
      * exfalso. apply Ec.
        change (pmv_dst mm) with (pmv_dst (subst_pmove_one old mm)).
        apply in_map. unfold ms'. apply filter_In.
        split; [unfold mapped; apply in_map; exact Hinm | rewrite Enop; reflexivity].
Qed.

(** Potential measure strictly decreasing on every step of [compile_pmoves_fuel]. *)
Definition pmoves_measure (ms : list pmove) : nat :=
  (2 * length ms - (if loc_read_in_pmoves PmCycleTmp ms then 1 else 0))%nat.

(** Induction over [compile_pmoves_fuel]: whenever `pmoves_measure ms < fuel`,
    the emitted lines execute cleanly from `st` and realize [simul_pmoves]
    on every non-scratch location `l <> PmCycleTmp`. *)
Lemma compile_pmoves_fuel_sound : forall fuel sym_env ms acc st0 st,
  (pmoves_measure ms < fuel)%nat ->
  pm_exec_lines sym_env st0 (rev acc) = Some st ->
  pm_mach_canonical st ->
  NoDup (map pmv_dst ms) ->
  Forall (pmove_wf (pm_mach_env st)) ms ->
  exists st_end,
    pm_exec_lines sym_env st0 (compile_pmoves_fuel fuel ms acc) = Some st_end /\
    pm_mach_canonical st_end /\
    (forall l, l <> PmCycleTmp ->
       pm_mach_env st_end l = simul_pmoves sym_env (pm_mach_env st) ms l).
Proof.
  induction fuel as [|fuel' IH]; intros sym_env ms acc st0 st Hmeas Hacc Hcan Hnd Hwf.
  - lia.
  - destruct ms as [|m0 ms_tl].
    + simpl. unfold rev'. rewrite <- rev_alt.
      exists st. split; [exact Hacc | split; [exact Hcan | intros l _; reflexivity]].
    + cbn [compile_pmoves_fuel].
      set (ms := m0 :: ms_tl) in *.
      destruct (pick_ready_pmove ms []) as [[m rest]|] eqn:Epick.
      * destruct (pick_ready_pmove_some ms [] m rest Epick)
          as [Hnr [Hm_in [Hiff [Hnd_fn Hlen]]]].
        simpl in Hiff, Hnd_fn, Hlen.
        pose proof (Hnd_fn Hnd) as Hnd_mrest.
        inversion Hnd_mrest as [| ? ? Hnot_rest Hnd_rest]; subst.
        rewrite Forall_forall in Hwf.
        destruct (emit_one_pmove_sound sym_env st m Hcan (Hwf m Hm_in))
          as [st1 [Hexec1 [Hcan1 [Hdst1 Hother1]]]].
        assert (Hacc1 : pm_exec_lines sym_env st0 (rev (rev_append (emit_one_pmove m) acc)) = Some st1).
        { rewrite rev_append_rev, rev_app_distr, rev_involutive.
          rewrite (pm_exec_lines_app sym_env _ _ st0 st Hacc). exact Hexec1. }
        assert (Hmeas_rest : (pmoves_measure rest < fuel')%nat).
        { unfold pmoves_measure, ms in *; cbn [length] in *.
          destruct (loc_read_in_pmoves PmCycleTmp (m0 :: ms_tl));
          destruct (loc_read_in_pmoves PmCycleTmp rest); lia. }
        assert (Hnot_dst_src : forall m' l', In m' rest -> pmv_src m' = PsLoc l' -> l' <> pmv_dst m).
        { intros m' l' Hm' Hsrc Heq. subst l'.
          pose proof (proj2 (loc_read_in_pmoves_iff (pmv_dst m) rest)
                       (in_pmove_src_locs m' rest (pmv_dst m) Hm' Hsrc)) as Hrd.
          rewrite Hnr in Hrd. discriminate. }
        assert (Hwf_rest : Forall (pmove_wf (pm_mach_env st1)) rest).
        { apply Forall_forall. intros m' Hm'.
          assert (Hm'_ms : In m' ms) by (apply Hiff; right; exact Hm').
          pose proof (Hwf m' Hm'_ms) as [Hd' Hs'].
          split; [exact Hd'|].
          destruct (pmv_src m') as [l' | n | g] eqn:Es; [|exact I | exact Hs'].
          rewrite Hother1 by (exact (Hnot_dst_src m' l' Hm' Es)).
          exact Hs'. }
        destruct (IH sym_env rest (rev_append (emit_one_pmove m) acc) st0 st1
                    Hmeas_rest Hacc1 Hcan1 Hnd_rest Hwf_rest)
          as [st_end [Hend [Hcan_end Hsim_end]]].
        exists st_end. split; [exact Hend | split; [exact Hcan_end|]].
        intros l Hl_neq. rewrite (Hsim_end l Hl_neq).
        unfold simul_pmoves.
        destruct (pm_loc_eqb l (pmv_dst m)) eqn:Elm.
        -- apply pm_loc_eqb_spec in Elm. subst l.
           pose proof (proj2 (find_pmove_dst_none rest (pmv_dst m)) Hnot_rest) as Hnone_r.
           rewrite Hnone_r, (find_pmove_dst_in ms m Hnd Hm_in), Hdst1. reflexivity.
        -- assert (Hl_not_m : l <> pmv_dst m).
           { intro Heq. subst l. rewrite pm_loc_eqb_refl in Elm. discriminate. }
           destruct (find_pmove_dst l rest) as [mr|] eqn:Er.
           ++ destruct (find_pmove_dst_some rest l mr Er) as [Hmr_in Hmr_dst]. subst l.
              assert (Hmr_ms : In mr ms) by (apply Hiff; right; exact Hmr_in).
              rewrite (find_pmove_dst_in ms mr Hnd Hmr_ms).
              unfold eval_pm_src.
              destruct (pmv_src mr) as [l' | n | g] eqn:Es; [|reflexivity | reflexivity].
              rewrite Hother1 by (exact (Hnot_dst_src mr l' Hmr_in Es)).
              reflexivity.
           ++ apply find_pmove_dst_none in Er.
              destruct (find_pmove_dst l ms) as [mm|] eqn:Em; [|exact (Hother1 l Hl_not_m)].
              destruct (find_pmove_dst_some ms l mm Em) as [Hmm_in Hmm_dst]. subst l.
              apply Hiff in Hmm_in. destruct Hmm_in as [<- | Hmm_r]; [contradiction|].
              exfalso. apply Er. apply in_map. exact Hmm_r.
      * assert (Hnot_tmp : forall m, In m ms -> pmv_dst m <> PmCycleTmp).
        { intros m Hm. rewrite Forall_forall in Hwf. exact (proj1 (Hwf m Hm)). }
        destruct (no_ready_cycle_tmp_unread ms Hnd Hnot_tmp Epick) as [Hunread Hall].
        assert (Hm0_in : In m0 ms) by (unfold ms; left; reflexivity).
        pose proof (Hnot_tmp m0 Hm0_in) as Hm0_neq.
        destruct (emit_save_cycle_tmp_sound sym_env st (pmv_dst m0) Hcan Hm0_neq)
          as [st1 [Hexec1 [Hcan1 [Htmp1 Hother1]]]].
        assert (Hacc1 : pm_exec_lines sym_env st0 (rev (rev_append (emit_save_cycle_tmp (pmv_dst m0)) acc)) = Some st1).
        { rewrite rev_append_rev, rev_app_distr, rev_involutive.
          rewrite (pm_exec_lines_app sym_env _ _ st0 st Hacc). exact Hexec1. }
        destruct (subst_pmove_src_sound sym_env st st1 (pmv_dst m0) ms
                    Hcan Hcan1 Hm0_neq Hunread Hnd Hwf Htmp1 Hother1 (Hall m0 Hm0_in))
          as [Hnd' [Hwf' [Hlen' [Hread' Hsim']]]].
        assert (Hmeas' : (pmoves_measure (subst_pmove_src (pmv_dst m0) ms []) < fuel')%nat).
        { unfold pmoves_measure in *.
          change (loc_read_in_pmoves PmCycleTmp (m0 :: ms_tl)) with (loc_read_in_pmoves PmCycleTmp ms) in Hmeas.
          change (length (m0 :: ms_tl)) with (length ms) in Hmeas.
          rewrite Hunread in Hmeas. rewrite Hread'.
          assert (Hpos : (1 <= length ms)%nat) by (unfold ms; simpl; lia).
          assert (Hq_ex : exists x, In x (subst_pmove_src (pmv_dst m0) ms [])).
          { apply loc_read_in_pmoves_exists in Hread'.
            destruct Hread' as [x [Hx _]]. exists x. exact Hx. }
          destruct Hq_ex as [x Hx].
          assert (Hpos' : (1 <= length (subst_pmove_src (pmv_dst m0) ms []))%nat).
          { destruct (subst_pmove_src (pmv_dst m0) ms []); [contradiction | simpl; lia]. }
          lia. }
        destruct (IH sym_env (subst_pmove_src (pmv_dst m0) ms [])
                    (rev_append (emit_save_cycle_tmp (pmv_dst m0)) acc) st0 st1
                    Hmeas' Hacc1 Hcan1 Hnd' Hwf')
          as [st_end [Hend [Hcan_end Hsim_end]]].
        exists st_end. split; [exact Hend | split; [exact Hcan_end|]].
        intros l Hl_neq. rewrite (Hsim_end l Hl_neq).
        exact (Hsim' l Hl_neq).
Qed.

(** Well-formedness of a complete parallel-move list `ms` in initial state `st0`. *)
Definition pmove_list_wf (st0 : pm_mach) (ms : list pmove) : Prop :=
  pm_mach_canonical st0 /\
  NoDup (map pmv_dst ms) /\
  loc_read_in_pmoves PmCycleTmp ms = false /\
  Forall (pmove_wf (pm_mach_env st0)) ms.

(** Whole-scheduler parallel-move soundness: for any well-formed list
    `ms`, [compile_pmoves] emits x86-64 instructions that execute
    without error or fuel exhaustion in [pm_exec_lines] and establish
    [simul_pmoves] on every allocatable register and frame slot. *)
Theorem compile_pmoves_sound : forall sym_env st0 ms,
  pmove_list_wf st0 ms ->
  exists st_end,
    pm_exec_lines sym_env st0 (compile_pmoves ms) = Some st_end /\
    pm_mach_canonical st_end /\
    (forall l, l <> PmCycleTmp ->
       pm_mach_env st_end l = simul_pmoves sym_env (pm_mach_env st0) ms l).
Proof.
  intros sym_env st0 ms [Hcan [Hnd [Hunread Hwf]]].
  unfold compile_pmoves.
  destruct (drop_nop_pmoves_sound sym_env st0 ms Hcan Hnd Hunread Hwf)
    as [Hnd_c [Hunread_c [Hwf_c Hsim_c]]].
  set (clean := drop_nop_pmoves_acc ms []) in *.
  assert (Hmeas : (pmoves_measure clean < S (2 * length clean))%nat).
  { unfold pmoves_measure. rewrite Hunread_c. lia. }
  destruct (compile_pmoves_fuel_sound (S (2 * length clean)) sym_env clean [] st0 st0
              Hmeas eq_refl Hcan Hnd_c Hwf_c)
    as [st_end [Hexec [Hcan_end Hsim_end]]].
  exists st_end. split; [exact Hexec | split; [exact Hcan_end|]].
  intros l Hl_neq. rewrite (Hsim_end l Hl_neq). exact (Hsim_c l).
Qed.

(** Corollary: [compile_pmoves] never emits a [todo] line (`"parallel move fuel"`
    or `"cycle tmp dst"`) on any well-formed move list. *)
Corollary compile_pmoves_no_todo : forall st0 ms,
  pmove_list_wf st0 ms ->
  first_todo (compile_pmoves ms) = None.
Proof.
  intros st0 ms Hwf.
  destruct (compile_pmoves_sound (fun _ => 0) st0 ms Hwf) as [st_end [Hexec _]].
  exact (pm_exec_lines_no_todo (fun _ => 0) (compile_pmoves ms) st0 st_end Hexec).
Qed.

(** ## 5. Concrete [build_rctx] frame separation, callee-saves and root slots *)

(** Lookup in [ZMap] corresponds to pair membership in [ZMap.elements]. *)
Lemma zmap_find_in_elements : forall (A : Type) (k : Z) (v : A) (m : ZMap.t A),
  ZMap.find k m = Some v <-> In (k, v) (ZMap.elements m).
Proof.
  intros A k v m.
  rewrite <- ZF.find_mapsto_iff, ZF.elements_mapsto_iff, InA_alt.
  split.
  - intros [[k' v'] [[Hk Hv] Hin]]. simpl in Hk, Hv. subst. exact Hin.
  - intros Hin. exists (k, v). split; [split; reflexivity | exact Hin].
Qed.

(** [key_term] is injective, so distinct frame [key]s never collide in [nmap]. *)
Lemma key_term_inj : forall k1 k2,
  key_term k1 = key_term k2 -> k1 = k2.
Proof.
  induction k1 as [n1 | n1 | p1 i1 | | | | x1 s1 | k1' IH | x1];
    intros [n2 | n2 | p2 i2 | | | | x2 s2 | k2' | x2] H;
    simpl in H; try discriminate; try reflexivity.
  - injection H as ->. reflexivity.
  - injection H as ->. reflexivity.
  - injection H as Hp ->. destruct p1, p2; simpl in Hp; try discriminate; reflexivity.
  - injection H as -> ->. reflexivity.
  - injection H as H'. f_equal. apply IH. exact H'.
  - injection H as ->. reflexivity.
Qed.

(** [round16] is never less than its input. *)
Lemma round16_ge : forall n, n <= round16 n.
Proof.
  intro n. unfold round16, fifteen, sixteen.
  pose proof (Z_div_mod_eq_full (n + 15) 16) as Hdiv.
  pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)) as Hmod.
  lia.
Qed.

(** Non-negative size predicate on one frame [key]. *)
Definition key_local_nonneg (k : key) : Prop :=
  match k with
  | KLocal _ sz => 0 <= sz
  | _ => True
  end.

(** Every named local in `fr_plain fr` has non-negative byte size. *)
Definition frame_locals_nonneg (fr : frame) : Prop :=
  Forall key_local_nonneg (fr_plain fr).

(** Folding [plain_slot] keeps all plain-slot offsets in `(0, off1]`. *)
Lemma plain_slot_bounds : forall ks slots0 locals0 off0,
  Forall key_local_nonneg ks ->
  0 <= off0 ->
  (forall t o, nm_find t slots0 = Some o -> 0 < o <= off0) ->
  off0 <= snd (fold_left plain_slot ks (slots0, locals0, off0)) /\
  (forall t o,
     nm_find t (fst (fst (fold_left plain_slot ks (slots0, locals0, off0)))) = Some o ->
     0 < o <= snd (fold_left plain_slot ks (slots0, locals0, off0))).
Proof.
  induction ks as [|k ks' IH]; intros slots0 locals0 off0 Hfa Hoff Hsl; cbn [fold_left].
  - cbn [fst snd]. split; [lia | exact Hsl].
  - inversion Hfa as [| ? ? Hk Hfa']; subst.
    assert (Hstep :
              off0 < snd (plain_slot (slots0, locals0, off0) k) /\
              (forall t o,
                 nm_find t (fst (fst (plain_slot (slots0, locals0, off0) k))) = Some o ->
                 0 < o <= snd (plain_slot (slots0, locals0, off0) k))).
    { unfold key_local_nonneg in Hk.
      destruct k as [n | n | [| |] i | | | | x sz | k' | x]; cbn [plain_slot fst snd];
        try (split; [unfold eight; lia |
                     intros t o Hf; rewrite nm_find_add in Hf;
                     destruct (name_eqb t _);
                       [injection Hf as <-; unfold eight; lia | pose proof (Hsl t o Hf); unfold eight; lia]]).
      - split; [unfold sixteen; lia |].
        intros t o Hf. rewrite nm_find_add in Hf.
        destruct (name_eqb t _); [injection Hf as <-; unfold sixteen; lia | pose proof (Hsl t o Hf); unfold sixteen; lia].
      - pose proof (round16_ge sz) as Hpad.
        pose proof (round16_ge (off0 + round16 sz)) as Hpay.
        split; [unfold eight; lia |].
        intros t o Hf. pose proof (Hsl t o Hf). unfold eight; lia. }
    destruct (plain_slot (slots0, locals0, off0) k) as [[s1 l1] o1]; cbn [fst snd] in Hstep.
    destruct Hstep as [Hlt1 Hsl1].
    destruct (IH s1 l1 o1 Hfa' ltac:(lia) Hsl1) as [Hle2 Hsl2].
    split; [lia | exact Hsl2].
Qed.

(** Pure recursive specification of [place_callee_saves]. *)
Fixpoint saves_from (rs : list hreg) (off : Z) : list (hreg * Z) :=
  match rs with
  | [] => []
  | r :: rs' => (r, off + eight) :: saves_from rs' (off + eight)
  end.

(** [place_callee_saves] produces [saves_from] and `off + 8 * length rs`. *)
Lemma place_callee_saves_spec : forall rs off acc,
  place_callee_saves rs off acc =
  (rev acc ++ saves_from rs off, off + eight * Z.of_nat (length rs)).
Proof.
  induction rs as [|r rs' IH]; intros off acc; cbn [place_callee_saves saves_from length].
  - unfold rev'. rewrite <- rev_alt, app_nil_r. f_equal. unfold eight; lia.
  - rewrite IH; cbn [rev]; rewrite <- app_assoc; cbn [app]. f_equal. unfold eight; lia.
Qed.

(** Every offset in [saves_from] lies strictly above `off` and at most `off + 8 * length rs`. *)
Lemma saves_from_bounds : forall rs off r o,
  In (r, o) (saves_from rs off) ->
  off < o <= off + eight * Z.of_nat (length rs).
Proof.
  induction rs as [|r0 rs' IH]; intros off r o Hin; cbn [saves_from length In] in *; [contradiction|].
  destruct Hin as [Heq | Hin'].
  - injection Heq as <- <-. unfold eight; lia.
  - pose proof (IH (off + eight) r o Hin'). unfold eight in *; lia.
Qed.

(** Distinct offsets in [saves_from]. *)
Lemma saves_from_offs_gt : forall rs off r o,
  In (r, o) (saves_from rs off) -> off < o.
Proof.
  intros rs off r o H. exact (proj1 (saves_from_bounds rs off r o H)).
Qed.

(** Folding [lower_slot] keeps plain slots in `(0, plain_bytes0]` and places
    root slots in `[plain_bytes + 8, base - 16]`. *)
Lemma lower_slot_bounds : forall rks plain_bytes0 plain_bytes base i0 slots0,
  0 <= i0 ->
  plain_bytes0 <= plain_bytes ->
  plain_bytes + sixteen + eight * (i0 + Z.of_nat (length rks)) <= base ->
  (forall t o, nm_find t slots0 = Some o ->
     (0 < o <= plain_bytes0) \/ (plain_bytes + eight <= o <= base - sixteen)) ->
  forall t o,
    nm_find t (fst (fold_left (lower_slot base) rks (slots0, i0))) = Some o ->
    (0 < o <= plain_bytes0) \/ (plain_bytes + eight <= o <= base - sixteen).
Proof.
  induction rks as [|rk rks' IH]; intros plain_bytes0 plain_bytes base i0 slots0 Hi0 Hpb Hbase Hsl.
  - exact Hsl.
  - simpl length in Hbase. rewrite Nat2Z.inj_succ in Hbase.
    pose proof (Nat2Z.is_nonneg (length rks')) as Hlen_nn.
    cbn [fold_left]; unfold lower_slot at 1.
    apply (IH plain_bytes0 plain_bytes base (i0 + 1)
             (nm_add (key_term rk) (base - sixteen - eight * i0) slots0));
      [lia | exact Hpb | unfold eight, sixteen in *; lia |].
    intros t o Hfind. rewrite nm_find_add in Hfind.
    destruct (name_eqb t (key_term rk)).
    + assert (Ho : base - sixteen - eight * i0 = o) by congruence.
      rewrite <- Ho. right. unfold eight, sixteen in *; lia.
    + exact (Hsl t o Hfind).
Qed.

(** Membership of a duplicate-free root key in `fold_left (lower_slot base)`. *)
Lemma lower_slot_lookup : forall rks base i0 slots0 rk,
  NoDup rks ->
  In rk rks ->
  exists j, (j < length rks)%nat /\
    nm_find (key_term rk) (fst (fold_left (lower_slot base) rks (slots0, i0))) =
    Some (base - sixteen - eight * (i0 + Z.of_nat j)).
Proof.
  induction rks as [|r0 rks' IH]; intros base i0 slots0 rk Hnd Hin;
    cbn [fold_left Datatypes.length In] in *; [contradiction|].
  unfold lower_slot at 1.
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct Hin as [-> | Hin'].
  - exists O. split; [lia|].
    replace (i0 + Z.of_nat O) with i0 by lia.
    assert (Hpres : forall ks j sm,
              (~ In rk ks) ->
              nm_find (key_term rk) sm = Some (base - sixteen - eight * i0) ->
              nm_find (key_term rk) (fst (fold_left (lower_slot base) ks (sm, j))) =
              Some (base - sixteen - eight * i0)).
    { induction ks as [|k1 ks1 IHk]; intros j sm Hni Hsm; simpl; [exact Hsm|].
      apply IHk.
      - intro Hc. apply Hni. right. exact Hc.
      - rewrite nm_find_add. destruct (name_eqb (key_term rk) (key_term k1)) eqn:Ek; [|exact Hsm].
        apply term_eqb_eq in Ek. apply key_term_inj in Ek. subst k1.
        exfalso. apply Hni. left. reflexivity. }
    apply Hpres; [exact Hnotin|].
    rewrite nm_find_add, term_eqb_refl. reflexivity.
  - destruct (IH base (i0 + 1) (nm_add (key_term r0) (base - sixteen - eight * i0) slots0)
                rk Hnd' Hin') as [j [Hj Hfind]].
    exists (S j). split; [lia|].
    replace (i0 + Z.of_nat (S j)) with (i0 + 1 + Z.of_nat j) by lia.
    exact Hfind.
Qed.

(** [add_alias_slots] introduces no offsets outside `slots2` and `m`. *)
Lemma add_alias_slots_bounds : forall als slots2 m P,
  (forall t o, nm_find t slots2 = Some o -> P o) ->
  (forall t o, nm_find t m = Some o -> P o) ->
  forall t o, nm_find t (add_alias_slots als slots2 m) = Some o -> P o.
Proof.
  induction als as [|[k1 k2] als' IH]; intros slots2 m P Hs2 Hm t o Hfind; simpl in *.
  - exact (Hm t o Hfind).
  - destruct (nm_find (key_term k2) slots2) as [off|] eqn:Ek2.
    + eapply IH; [exact Hs2 | | exact Hfind].
      intros t' o' Hf'. rewrite nm_find_add in Hf'.
      destruct (name_eqb t' (key_term k1)).
      * injection Hf' as <-. exact (Hs2 (key_term k2) off Ek2).
      * exact (Hm t' o' Hf').
    + eapply IH; [exact Hs2 | exact Hm | exact Hfind].
Qed.

(** [add_alias_slots] maps `(k1, k2)` to `k2`'s offset when `map fst als` has `NoDup`. *)
Lemma add_alias_slots_lookup : forall als slots2 m k1 k2 off,
  NoDup (map fst als) ->
  In (k1, k2) als ->
  nm_find (key_term k2) slots2 = Some off ->
  nm_find (key_term k1) (add_alias_slots als slots2 m) = Some off.
Proof.
  induction als as [|[a1 a2] als' IH]; intros slots2 m k1 k2 off Hnd Hin Hk2; simpl in *; [contradiction|].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct Hin as [Heq | Hin'].
  - injection Heq as -> ->. rewrite Hk2.
    assert (Hpres : forall cs m1,
              (~ In k1 (map fst cs)) ->
              nm_find (key_term k1) m1 = Some off ->
              nm_find (key_term k1) (add_alias_slots cs slots2 m1) = Some off).
    { induction cs as [|[c1 c2] cs1 IHc]; intros m1 Hni Hm1; simpl; [exact Hm1|].
      destruct (nm_find (key_term c2) slots2) as [offc|].
      - apply IHc; [intro Hc; apply Hni; right; exact Hc|].
        rewrite nm_find_add. destruct (name_eqb (key_term k1) (key_term c1)) eqn:Ec; [|exact Hm1].
        apply term_eqb_eq in Ec. apply key_term_inj in Ec. subst c1.
        exfalso. apply Hni. left. reflexivity.
      - apply IHc; [intro Hc; apply Hni; right; exact Hc | exact Hm1]. }
    apply Hpres; [exact Hnotin|].
    rewrite nm_find_add, term_eqb_refl. reflexivity.
  - destruct (nm_find (key_term a2) slots2); eapply IH; eauto.
Qed.

(** Concrete save-slot separation: in [build_rctx], every callee-save
    slot `(r, save_off)` in [rc_saves] lies inside `(0, cx_base)` and
    never collides with any plain, root or aliased frame [slot]. *)
Theorem build_rctx_save_slots_disjoint : forall p names cmap rm r save_off,
  frame_locals_nonneg (pl_frame p) ->
  In (r, save_off) (rc_saves (build_rctx p names cmap rm)) ->
  0 < save_off < cx_base (rc_cx (build_rctx p names cmap rm)) /\
  (forall k, slot (rc_cx (build_rctx p names cmap rm)) k <> Some save_off).
Proof.
  intros p names cmap rm r save_off Hloc Hin.
  unfold build_rctx in *.
  set (fr := pl_frame p) in *.
  pose proof (plain_slot_bounds (fr_plain fr) nm_empty nm_empty 0 Hloc ltac:(lia)
                (fun t o H => ltac:(rewrite nm_find_empty in H; discriminate))) as Hpl.
  destruct (fold_left plain_slot (fr_plain fr) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain_bytes0] eqn:Epl.
  cbn [fst snd] in Hpl. destruct Hpl as [Hpb0_nonneg Hsl1].
  set (used_cs := collect_used_cs_acc callee_saved_hregs (ZMap.elements rm) []) in *.
  rewrite place_callee_saves_spec in *.
  cbn [rev app] in *.
  set (plain_bytes := plain_bytes0 + eight * Z.of_nat (length used_cs)) in *.
  set (base := plain_bytes + sixteen + eight * Zlength (fr_roots fr)) in *.
  assert (Hzlen : 0 <= Zlength (fr_roots fr)) by (rewrite Zlength_correct; lia).
  pose proof (Nat2Z.is_nonneg (length used_cs)) as Hcs_nn.
  pose proof (lower_slot_bounds (fr_roots fr) plain_bytes0 plain_bytes base 0 slots1
                ltac:(lia) ltac:(unfold plain_bytes, eight; lia)
                ltac:(rewrite <- Zlength_correct; unfold base; lia)
                (fun t o H => or_introl (Hsl1 t o H))) as Hlow.
  destruct (fold_left (lower_slot base) (fr_roots fr) (slots1, 0)) as [slots2 idx2] eqn:Elow.
  cbn [fst rc_saves rc_cx cx_base cx_slots] in *.
  pose proof (saves_from_bounds used_cs plain_bytes0 r save_off Hin) as Hsave_b.
  split; [unfold base, plain_bytes, sixteen, eight in *; lia|].
  intros k Hslot. unfold slot in Hslot; cbn [cx_slots] in Hslot.
  pose proof (add_alias_slots_bounds (fr_aliases fr) slots2 slots2
                (fun o => (0 < o <= plain_bytes0) \/ (plain_bytes + eight <= o <= base - sixteen))
                Hlow Hlow (key_term k) save_off Hslot) as Hbad.
  unfold plain_bytes, eight in *; lia.
Qed.

(** [hreg_in_pairs] detects any register `r` appearing in `els`. *)
Lemma hreg_in_pairs_spec : forall r els,
  hreg_in_pairs r els = true <-> exists k, In (k, r) els.
Proof.
  intros r els. induction els as [|[k r'] els' IH]; simpl.
  - split; [discriminate | intros [? []]].
  - destruct (hreg_eqb r r') eqn:E.
    + apply hreg_eqb_spec in E. subst r'.
      split; [intros _; exists k; left; reflexivity | auto].
    + rewrite IH. split.
      * intros [k' Hk']. exists k'. right. exact Hk'.
      * intros [k' [Heq | Hk']]; [injection Heq as _ ->; rewrite hreg_eqb_refl in E; discriminate | exists k'; exact Hk'].
Qed.

(** Characterization of [collect_used_cs_acc]. *)
Lemma collect_used_cs_acc_eq : forall cs els acc,
  collect_used_cs_acc cs els acc = rev acc ++ filter (fun r => hreg_in_pairs r els) cs.
Proof.
  induction cs as [|r cs' IH]; intros els acc; simpl.
  - unfold rev'. rewrite <- rev_alt, app_nil_r. reflexivity.
  - destruct (hreg_in_pairs r els); [rewrite IH; simpl; rewrite <- app_assoc; reflexivity | apply IH].
Qed.

(** Every callee-saved register assigned anywhere in `rm` has a dedicated
    save slot in `rc_saves (build_rctx p names cmap rm)`. *)
Theorem build_rctx_used_callee_saved : forall p names cmap rm t r,
  zmap_find_nat t rm = Some r ->
  hreg_callee_saved r = true ->
  In r (map fst (rc_saves (build_rctx p names cmap rm))).
Proof.
  intros p names cmap rm t r Hrm Hcs.
  unfold build_rctx.
  destruct (fold_left plain_slot (fr_plain (pl_frame p)) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain_bytes0].
  rewrite place_callee_saves_spec.
  destruct (fold_left (lower_slot _) (fr_roots (pl_frame p)) (slots1, 0)) as [slots2 _].
  cbn [rc_saves rev app].
  assert (Hfst : forall rs off, map fst (saves_from rs off) = rs).
  { induction rs as [|r0 rs' IH]; intro off; simpl; [reflexivity | rewrite IH; reflexivity]. }
  rewrite Hfst, collect_used_cs_acc_eq. cbn [rev app].
  apply filter_In. split.
  - destruct r; simpl in *; try discriminate; auto 6.
  - apply hreg_in_pairs_spec. exists (Z.of_nat t).
    apply zmap_find_in_elements. exact Hrm.
Qed.

(** Executing [callee_save_stores] over `saves_from rs off` stores each
    `r` in `rs` into its dedicated frame slot while leaving registers and
    all slots `<= off` untouched. *)
Lemma callee_save_stores_exec : forall sym_env rs off st,
  pm_mach_canonical st ->
  exists st_saved,
    pm_exec_lines sym_env st (callee_save_stores (saves_from rs off)) = Some st_saved /\
    pm_mach_canonical st_saved /\
    (forall r', pm_hreg st_saved r' = pm_hreg st r') /\
    (forall off', off' <= off -> pm_slot st_saved off' = pm_slot st off') /\
    (NoDup rs -> forall r o, In (r, o) (saves_from rs off) -> pm_slot st_saved o = pm_hreg st r).
Proof.
  induction rs as [|r0 rs' IH]; intros off st Hcan; simpl.
  - exists st. split; [reflexivity | split; [exact Hcan | split; [intro; reflexivity | split; [intros; reflexivity | intros _ r o []]]]].
  - unfold callee_save_stores in *; simpl.
    rewrite pm_reg64_hreg. simpl.
    set (st1 := pm_set_slot st (- - (off + eight)) (pm_hreg st r0 mod two64)).
    assert (Hcan1 : pm_mach_canonical st1).
    { intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
      destruct (Z.eqb off' (- - (off + eight)));
        [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))]. }
    destruct (IH (off + eight) st1 Hcan1) as [st_saved [Hexec [Hcan_s [Hreg_s [Hlow_s Hmem_s]]]]].
    exists st_saved. split; [exact Hexec | split; [exact Hcan_s | split; [exact Hreg_s | split]]].
    + intros off' Hoff'. rewrite (Hlow_s off' ltac:(unfold eight; lia)).
      unfold st1; simpl. replace (- - (off + eight)) with (off + eight) by lia.
      destruct (Z.eqb off' (off + eight)) eqn:E; [apply Z.eqb_eq in E; unfold eight in *; lia | reflexivity].
    + intros Hnd r o [Heq | Hin'].
      * injection Heq as -> <-.
        rewrite (Hlow_s (off + eight) ltac:(lia)).
        unfold st1; simpl. replace (- - (off + eight)) with (off + eight) by lia.
        rewrite Z.eqb_refl. apply Z.mod_small. exact (Hcan (PmReg r)).
      * inversion Hnd as [| ? ? Hnotin Hnd']; subst.
        exact (Hmem_s Hnd' r o Hin').
Qed.

(** Executing [callee_save_restores] over `saves_from rs off` loads each
    saved register from its slot while leaving registers outside `rs` unchanged. *)
Lemma callee_save_restores_exec : forall sym_env rs off st_body,
  pm_mach_canonical st_body ->
  NoDup rs ->
  exists st_exit,
    pm_exec_lines sym_env st_body (callee_save_restores (saves_from rs off)) = Some st_exit /\
    (forall r o, In (r, o) (saves_from rs off) -> pm_hreg st_exit r = pm_slot st_body o) /\
    (forall r, ~ In r rs -> pm_hreg st_exit r = pm_hreg st_body r).
Proof.
  induction rs as [|r0 rs' IH]; intros off st_body Hcan Hnd; simpl.
  - exists st_body. split; [reflexivity | split; [intros r o [] | auto]].
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    unfold callee_save_restores in *; simpl.
    rewrite pm_reg64_hreg. simpl.
    set (st1 := pm_set_reg st_body (PrHReg r0) (pm_slot st_body (- - (off + eight)) mod two64)).
    assert (Hcan1 : pm_mach_canonical st1).
    { intros [r' | off' |]; simpl; [| exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      destruct (hreg_eqb r' r0); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmReg r'))]. }
    destruct (IH (off + eight) st1 Hcan1 Hnd') as [st_exit [Hexec [Hin_s Hout_s]]].
    exists st_exit. split; [exact Hexec | split].
    + intros r o [Heq | Hin'].
      * injection Heq as -> <-.
        rewrite (Hout_s r Hnotin). unfold st1; simpl.
        rewrite hreg_eqb_refl. replace (- - (off + eight)) with (off + eight) by lia.
        apply Z.mod_small. exact (Hcan (PmSlot (off + eight))).
      * rewrite (Hin_s r o Hin'). reflexivity.
    + intros r Hnot. rewrite (Hout_s r ltac:(intro Hc; apply Hnot; right; exact Hc)).
      unfold st1; simpl. destruct (hreg_eqb r r0) eqn:E; [|reflexivity].
      apply hreg_eqb_spec in E. subst r. exfalso; apply Hnot; left; reflexivity.
Qed.

(** Concrete prologue/epilogue callee-save preservation for [build_rctx]:
    executing [callee_save_stores] on `st_entry`, running any body to
    `st_body` that preserves the disjoint save slots in [rc_saves] and
    leaves unused callee-saved registers untouched, and executing
    [callee_save_restores] restores all five callee-saved registers to
    their entry values. *)
Theorem build_rctx_callee_saves_sound : forall sym_env p names cmap rm st_entry,
  pm_mach_canonical st_entry ->
  exists st_saved,
    pm_exec_lines sym_env st_entry (callee_save_stores (rc_saves (build_rctx p names cmap rm)))
      = Some st_saved /\
    forall st_body,
      pm_mach_canonical st_body ->
      (forall r off, In (r, off) (rc_saves (build_rctx p names cmap rm)) ->
         pm_slot st_body off = pm_slot st_saved off) ->
      (forall r, hreg_callee_saved r = true ->
         ~ In r (map fst (rc_saves (build_rctx p names cmap rm))) ->
         pm_hreg st_body r = pm_hreg st_entry r) ->
      exists st_exit,
        pm_exec_lines sym_env st_body (callee_save_restores (rc_saves (build_rctx p names cmap rm)))
          = Some st_exit /\
        forall r, hreg_callee_saved r = true -> pm_hreg st_exit r = pm_hreg st_entry r.
Proof.
  intros sym_env p names cmap rm st_entry Hcan_e.
  unfold build_rctx.
  destruct (fold_left plain_slot (fr_plain (pl_frame p)) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain_bytes0].
  rewrite place_callee_saves_spec.
  destruct (fold_left (lower_slot _) (fr_roots (pl_frame p)) (slots1, 0)) as [slots2 _].
  cbn [rc_saves rev app].
  set (used_cs := collect_used_cs_acc callee_saved_hregs (ZMap.elements rm) []).
  assert (Hnd_cs : NoDup used_cs).
  { unfold used_cs. rewrite collect_used_cs_acc_eq. cbn [rev app].
    assert (Hnd5 : NoDup callee_saved_hregs).
    { unfold callee_saved_hregs.
      repeat (constructor; [simpl; intuition discriminate|]). constructor. }
    pose proof (nodup_map_filter hreg hreg (fun x => x)
                  (fun r => hreg_in_pairs r (ZMap.elements rm)) callee_saved_hregs) as Hmf.
    rewrite !map_id in Hmf. exact (Hmf Hnd5). }
  destruct (callee_save_stores_exec sym_env used_cs plain_bytes0 st_entry Hcan_e)
    as [st_saved [Hexec_s [_ [_ [_ Hmem_s]]]]].
  exists st_saved. split; [exact Hexec_s|].
  intros st_body Hcan_b Hpres_slots Huntouched.
  destruct (callee_save_restores_exec sym_env used_cs plain_bytes0 st_body Hcan_b Hnd_cs)
    as [st_exit [Hexec_r [Hin_r Hout_r]]].
  exists st_exit. split; [exact Hexec_r|].
  assert (Hfst : map fst (saves_from used_cs plain_bytes0) = used_cs).
  { clear. generalize plain_bytes0. induction used_cs as [|r0 rs IH]; intro off; simpl;
      [reflexivity | rewrite IH; reflexivity]. }
  intros r Hcs.
  destruct (hreg_in_list r used_cs) eqn:Ein.
  - apply hreg_in_list_spec in Ein.
    assert (Hex_off : exists off, In (r, off) (saves_from used_cs plain_bytes0)).
    { rewrite <- Hfst in Ein. apply in_map_iff in Ein.
      destruct Ein as [[r' off] [<- Hin']]. exists off. exact Hin'. }
    destruct Hex_off as [off Hoff].
    rewrite (Hin_r r off Hoff), (Hpres_slots r off Hoff), (Hmem_s Hnd_cs r off Hoff).
    reflexivity.
  - assert (Hnin_real : ~ In r used_cs).
    { intro Hc. apply hreg_in_list_spec in Hc. congruence. }
    rewrite (Hout_r r Hnin_real).
    apply (Huntouched r Hcs). rewrite Hfst. exact Hnin_real.
Qed.

(** Idealized register-indexed save map for `used`. *)
Definition exec_saves (used : list hreg) (entry_regs : hreg -> Z) (save_mem : hreg -> Z)
  : hreg -> Z :=
  fun r => if hreg_in_list r used then entry_regs r else save_mem r.

(** Idealized register-indexed restore map for `used`. *)
Definition exec_restores (used : list hreg) (save_mem : hreg -> Z) (body_regs : hreg -> Z)
  : hreg -> Z :=
  fun r => if hreg_in_list r used then save_mem r else body_regs r.

(** Algebraic round-trip identity on register-indexed maps. *)
Theorem callee_saves_restore_sound :
  forall (used : list hreg) (entry_regs body_regs save_mem0 : hreg -> Z) (r : hreg),
  (hreg_in_list r used = false -> body_regs r = entry_regs r) ->
  exec_restores used (exec_saves used entry_regs save_mem0) body_regs r = entry_regs r.
Proof.
  intros used entry_regs body_regs save_mem0 r Huntouched.
  unfold exec_restores, exec_saves.
  destruct (hreg_in_list r used) eqn:Ein; [reflexivity | apply Huntouched; reflexivity].
Qed.

(** Concrete GC root invariant for [build_rctx]: every pointer temporary
    whose lower key `(KLower (KTmp d), rk)` aliases a root `rk` in
    `fr_roots` resolves in [key_pm_loc] to `Some (PmSlot off)` for a
    positive frame offset inside the collector's `lowers[]` root array. *)
Theorem build_rctx_root_lower_slot : forall p names cmap rm d rk,
  frame_locals_nonneg (pl_frame p) ->
  NoDup (fr_roots (pl_frame p)) ->
  NoDup (map fst (fr_aliases (pl_frame p))) ->
  In rk (fr_roots (pl_frame p)) ->
  In (KLower (KTmp d), rk) (fr_aliases (pl_frame p)) ->
  exists off,
    key_pm_loc (build_rctx p names cmap rm) (KLower (KTmp d)) = Some (PmSlot off) /\
    cx_base (rc_cx (build_rctx p names cmap rm)) - sixteen - eight * Zlength (fr_roots (pl_frame p))
      < off <= cx_base (rc_cx (build_rctx p names cmap rm)) - sixteen.
Proof.
  intros p names cmap rm d rk Hloc Hnd_r Hnd_a Hin_r Hin_a.
  unfold build_rctx.
  set (fr := pl_frame p) in *.
  pose proof (plain_slot_bounds (fr_plain fr) nm_empty nm_empty 0 Hloc ltac:(lia)
                (fun t o H => ltac:(rewrite nm_find_empty in H; discriminate))) as [Hpb0 _].
  destruct (fold_left plain_slot (fr_plain fr) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain_bytes0].
  set (used_cs := collect_used_cs_acc callee_saved_hregs (ZMap.elements rm) []).
  rewrite place_callee_saves_spec. cbn [rev app].
  set (plain_bytes := plain_bytes0 + eight * Z.of_nat (length used_cs)).
  set (base := plain_bytes + sixteen + eight * Zlength (fr_roots fr)).
  destruct (lower_slot_lookup (fr_roots fr) base 0 slots1 rk Hnd_r Hin_r)
    as [j [Hj Hfind_rk]].
  destruct (fold_left (lower_slot base) (fr_roots fr) (slots1, 0)) as [slots2 idx2].
  cbn [fst rc_cx cx_base] in Hfind_rk |- *.
  pose proof (add_alias_slots_lookup (fr_aliases fr) slots2 slots2
                (KLower (KTmp d)) rk (base - sixteen - eight * (0 + Z.of_nat j))
                Hnd_a Hin_a Hfind_rk) as Halias.
  exists (base - sixteen - eight * (0 + Z.of_nat j)).
  split.
  - unfold key_pm_loc, slot; cbn [rc_cx cx_slots]. rewrite Halias. reflexivity.
  - rewrite Zlength_correct. unfold eight, sixteen; lia.
Qed.

(** Lookup of `KLower k` in [key_pm_loc] never returns a register
    location [PmReg]. *)
Theorem lower_key_never_hreg : forall rc k r,
  key_pm_loc rc (KLower k) <> Some (PmReg r).
Proof.
  intros rc k r. simpl.
  destruct (slot (rc_cx rc) (KLower k)); intro H; discriminate.
Qed.

(** ## 6. Executable rejection examples for [valid_alloc] *)

Definition ex_cmap2 : ZMap.t class :=
  zmap_add_nat 0%nat L (zmap_add_nat 1%nat L (zmap_add_nat 2%nat Double (ZMap.empty class))).

Definition ex_rm1 (t : nat) (r : hreg) : ZMap.t hreg :=
  zmap_add_nat t r (ZMap.empty hreg).

Definition ex_rb_collision : rblock :=
  mkRBlock 0%nat [] [] [mkRInst [0%nat; 1%nat] [] RCallNone] [].

Definition ex_rm_collision : ZMap.t hreg :=
  zmap_add_nat 0%nat HRbx (ex_rm1 1%nat HRbx).

(** Two live parameters mapped to the same register `HRbx` are rejected. *)
Example ex_rejects_collision :
  valid_alloc ex_cmap2 [0%nat; 1%nat] [ex_rb_collision] ex_rm_collision = false.
Proof. reflexivity. Qed.

Definition ex_rb_after_call : rblock :=
  mkRBlock 0%nat [] [] [mkRInst [] [] RCallAfterReads] [0%nat].

(** A caller-saved register `HR10` live across `RCallAfterReads` is rejected,
    while callee-saved `HRbx` is accepted. *)
Example ex_rejects_r10_call :
  valid_alloc ex_cmap2 [0%nat] [ex_rb_after_call] (ex_rm1 0%nat HR10) = false /\
  valid_alloc ex_cmap2 [0%nat] [ex_rb_after_call] (ex_rm1 0%nat HRbx) = true.
Proof. split; reflexivity. Qed.

Definition ex_rb_during_call : rblock :=
  mkRBlock 0%nat [] [] [mkRInst [0%nat] [] RCallDuringReads] [].

(** Input of `RCallDuringReads` (`AStorePointer` / `ADispatch`) in `HR11`
    is rejected even when dead after the instruction. *)
Example ex_rejects_r11_read_call :
  valid_alloc ex_cmap2 [0%nat] [ex_rb_during_call] (ex_rm1 0%nat HR11) = false /\
  valid_alloc ex_cmap2 [0%nat] [ex_rb_during_call] (ex_rm1 0%nat HR12) = true.
Proof. split; reflexivity. Qed.

Definition ex_rb_poll0 : rblock :=
  mkRBlock 0%nat [(1%nat, false)] [] [] [].

Definition ex_rb_poll1 : rblock :=
  mkRBlock 1%nat [(1%nat, true)] [(1%nat, [(0%nat, Some 0%nat); (1%nat, Some 1%nat)])] [] [1%nat].

(** A phi destination in `HR10` on a `Poll` loop back-edge is rejected,
    while `HR13` is accepted. *)
Example ex_rejects_r10_poll :
  valid_alloc ex_cmap2 [0%nat] [ex_rb_poll0; ex_rb_poll1] (ex_rm1 1%nat HR10) = false /\
  valid_alloc ex_cmap2 [0%nat] [ex_rb_poll0; ex_rb_poll1] (ex_rm1 1%nat HR13) = true.
Proof. split; reflexivity. Qed.

Definition ex_rb_float : rblock :=
  mkRBlock 0%nat [] [] [] [2%nat].

(** Assigning a float temporary (`Double`) to a general register is rejected. *)
Example ex_rejects_float :
  valid_alloc ex_cmap2 [2%nat] [ex_rb_float] (ex_rm1 2%nat HRbx) = false.
Proof. reflexivity. Qed.
