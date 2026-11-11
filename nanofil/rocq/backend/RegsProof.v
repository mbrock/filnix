(** # Local invariants and step lemmas for Regs.v

    Kernel-checked lemmas for the interval primitives, live
    register-and-frame-slot state updates, parallel-move transformations
    and 3-address immediate selection in Regs.v (M7 of
    docs/gallina-backend.md):

    1. **Interval and call-point tests** ([hreg_eqb_spec],
       [ivals_disjoint_sound], [ivals_hit_points_sound]): under
       [ivals_wf] and [pts_wf], disjoint interval lists share no program
       point, and an interval list that misses the sorted call points
       contains none of them.
    2. **Live-only register and shared-slot state steps**
       ([clobber_preserves_agrees], [poll_edge_clobber_sound],
       [write_mach_step_sound], [write_mach_list_sound],
       [check_rinst_step_sound], [callee_saves_restore_sound],
       [lower_key_never_hreg]): [state_agrees] relates live temporaries
       to hardware registers and physical shared frame slots (`Z -> Z`
       indexed by `slot_of`, allowing expired spill-slot reuse as in
       [ex_shared_spill_slot]), and is preserved across caller-saved
       clobbers (`%r10`, `%r11`), non-colliding single and simultaneous
       destination writes, and one abstract instruction step.
    3. **Parallel-move transformations** ([ready_pmove_step_sound],
       [cycle_break_step_sound]): parameterized over global symbol
       addresses `sym_env`, peeling an unread destination or saving a
       cycle head into fresh `PmCycleTmp` (`%rcx`) preserves abstract
       move sources.
    4. **3-address `lea` and immediate selection** ([imm32_congruent],
       [imm32_add_mod_sound], [imm32_sub_lea_w_sound],
       [imm32_sub_lea_l_sound]): [integer_immediate] and negated `lea`
       displacements compute the exact modular sum and difference at
       both 32-bit (`w`, including `-2^31`) and 64-bit (`l`) widths. *)

From Stdlib Require Import String ZArith List Bool Arith Lia.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Plan Layout Emit Regs.
Import ListNotations.
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

(** Idealized register-indexed save map for `used`. *)
Definition exec_saves (used : list hreg) (entry_regs : hreg -> Z) (save_mem : hreg -> Z)
  : hreg -> Z :=
  fun r => if hreg_in_list r used then entry_regs r else save_mem r.

(** Idealized register-indexed restore map for `used`. *)
Definition exec_restores (used : list hreg) (save_mem : hreg -> Z) (body_regs : hreg -> Z)
  : hreg -> Z :=
  fun r => if hreg_in_list r used then save_mem r else body_regs r.

(** Algebraic round-trip identity on register-indexed maps: every
    register `r` in `used` is restored from `exec_saves`, and every
    other register keeps `body_regs r = entry_regs r`. *)
Theorem callee_saves_restore_sound :
  forall (used : list hreg) (entry_regs body_regs save_mem0 : hreg -> Z) (r : hreg),
  (hreg_in_list r used = false -> body_regs r = entry_regs r) ->
  exec_restores used (exec_saves used entry_regs save_mem0) body_regs r = entry_regs r.
Proof.
  intros used entry_regs body_regs save_mem0 r Huntouched.
  unfold exec_restores, exec_saves.
  destruct (hreg_in_list r used) eqn:Ein.
  - reflexivity.
  - apply Huntouched. reflexivity.
Qed.

(** Lookup of `KLower k` in [key_pm_loc] never returns a register
    location [PmReg]. *)
Theorem lower_key_never_hreg : forall rc k r,
  key_pm_loc rc (KLower k) <> Some (PmReg r).
Proof.
  intros rc k r. simpl.
  destruct (slot (rc_cx rc) (KLower k)); intro H; discriminate.
Qed.

(** ## 3. Parallel-move step transformations *)

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

(** Save location `old` into `PmCycleTmp` (`%rcx`) in abstract state `env`. *)
Definition save_cycle_abs (env : pm_loc -> Z) (old : pm_loc) : pm_loc -> Z :=
  fun l => if pm_loc_eqb l PmCycleTmp then env old else env l.

(** Rewrite `old` to `PmCycleTmp` in a single [pmove] without dropping no-ops. *)
Definition subst_one_pmove (old : pm_loc) (m : pmove) : pmove :=
  let src' :=
    match pmv_src m with
    | PsLoc l => if pm_loc_eqb l old then PsLoc PmCycleTmp else PsLoc l
    | s => s
    end in
  mkPMove (pmv_half m) (pmv_src_w m) (pmv_dst m) src'.

(** Move `m` does not read `PmCycleTmp`. *)
Definition no_cycle_tmp_src (m : pmove) : Prop :=
  match pmv_src m with
  | PsLoc PmCycleTmp => False
  | _ => True
  end.

(** Single-move cycle-breaking step: saving `old` into fresh
    `PmCycleTmp` and rewriting reads of `old` preserves `m`'s evaluated
    source and eliminates `m`'s read of `old`. *)
Theorem cycle_break_step_sound : forall sym_env env old m,
  old <> PmCycleTmp ->
  no_cycle_tmp_src m ->
  eval_pm_src sym_env (save_cycle_abs env old)
              (pmv_half (subst_one_pmove old m))
              (pmv_src (subst_one_pmove old m))
  = eval_pm_src sym_env env (pmv_half m) (pmv_src m) /\
  loc_read_in_pmoves old [subst_one_pmove old m] = false.
Proof.
  intros sym_env env old m Hnot_tmp Hno_tmp.
  unfold no_cycle_tmp_src in Hno_tmp.
  unfold save_cycle_abs, subst_one_pmove, eval_pm_src. simpl.
  destruct (pmv_src m) as [l | n | g].
  - destruct (pm_loc_eqb l old) eqn:Elo.
    + apply pm_loc_eqb_spec in Elo. subst l. simpl.
      split; [reflexivity|].
      destruct (pm_loc_eqb old PmCycleTmp) eqn:Ebad; [|reflexivity].
      apply pm_loc_eqb_spec in Ebad. contradiction.
    + simpl.
      destruct (pm_loc_eqb l PmCycleTmp) eqn:Elt.
      * apply pm_loc_eqb_spec in Elt. subst l. contradiction.
      * split; [reflexivity|].
        destruct (pm_loc_eqb old l) eqn:Eol; [|reflexivity].
        apply pm_loc_eqb_spec in Eol. subst l. rewrite pm_loc_eqb_refl in Elo. discriminate.
  - split; reflexivity.
  - split; reflexivity.
Qed.

(** ## 4. Soundness of 3-address `lea` and immediate selection *)

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

(** ## 5. Executable rejection examples for [valid_alloc] *)

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
