(** # Soundness proofs for Regs.v

    Machine-checked invariants of the Gallina register allocator,
    validator, parallel-move compiler and 3-address selection in
    Regs.v (M7 of docs/gallina-backend.md):

    1. **Interval and call-point tests** ([hreg_eqb_spec],
       [ivals_disjoint_sound], [ivals_hit_points_sound]): disjoint
       interval lists share no program point, and an interval list
       that misses the sorted call points contains none of them.
    2. **Allocation validator simulation** ([check_rinst_step_sound],
       [check_rinsts_rev_sound], [poll_edge_clobber_sound],
       [callee_saves_restore_sound], [lower_key_never_hreg]): any
       register map accepted by [check_rinsts_rev] and
       [check_succs_polls] preserves temporary values across
       instructions, simultaneous definitions, caller-saved register
       clobbers (`%r10`, `%r11`) at calls and poll edges, restores
       all five callee-saved registers (`%rbx`, `%r12`–`%r15`) on
       exit, and keeps capability lowers in stack root slots.
    3. **Parallel moves** ([ready_pmove_step_sound],
       [cycle_break_step_sound]): peeling an unread destination or
       saving a cycle head into `%rcx` preserves the simultaneous
       assignment of all non-scratch locations.
    4. **3-address `lea` and immediate selection**
       ([imm32_add_mod_sound], [imm32_sub_lea_w_sound],
       [imm32_sub_lea_l_sound]): signed 32-bit immediates and negated
       `lea` displacements compute the exact modular sum and
       difference at both 32-bit (`w`, including `-2^31`) and 64-bit
       (`l`) widths. *)

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

(** ## 2. Validator soundness and forward simulation *)

(** Concrete register+slot state for a function body. *)
Record mach_state : Type := mkMach {
  ms_reg : hreg -> Z;
  ms_slot : nat -> Z
}.

Definition read_mach (rm : ZMap.t hreg) (ms : mach_state) (t : nat) : Z :=
  match zmap_find_nat t rm with
  | Some r => ms_reg ms r
  | None => ms_slot ms t
  end.

Definition write_mach (rm : ZMap.t hreg) (ms : mach_state) (t : nat) (v : Z) : mach_state :=
  match zmap_find_nat t rm with
  | Some r => mkMach (fun r' => if hreg_eqb r' r then v else ms_reg ms r') (ms_slot ms)
  | None => mkMach (ms_reg ms) (fun t' => if Nat.eqb t' t then v else ms_slot ms t')
  end.

Fixpoint write_mach_list (rm : ZMap.t hreg) (ms : mach_state) (ds : list nat) (vs : list Z)
  : mach_state :=
  match ds, vs with
  | d :: ds', v :: vs' => write_mach_list rm (write_mach rm ms d v) ds' vs'
  | _, _ => ms
  end.

Fixpoint write_abs_list (tenv : nat -> Z) (ds : list nat) (vs : list Z) : nat -> Z :=
  match ds, vs with
  | d :: ds', v :: vs' =>
      write_abs_list (fun t => if Nat.eqb t d then v else tenv t) ds' vs'
  | _, _ => tenv
  end.

(** A call clobbers caller-saved registers (`%r10`, `%r11`) with
    arbitrary values `arb` while preserving callee-saved registers and
    stack slots. *)
Definition clobber_call (arb : hreg -> Z) (ms : mach_state) : mach_state :=
  mkMach (fun r => if hreg_callee_saved r then ms_reg ms r else arb r) (ms_slot ms).

(** State agreement on all temporaries in `live` (for mapped
    temporaries under `dom = Some km`, and unconditionally on unmapped
    temporaries). *)
Definition state_agrees (rm : ZMap.t hreg) (live : list nat)
                        (tenv : nat -> Z) (ms : mach_state) : Prop :=
  (forall t, zmap_find_nat t rm = None -> ms_slot ms t = tenv t) /\
  (forall t, In t live -> read_mach rm ms t = tenv t).

Lemma hreg_in_list_spec : forall r rs,
  hreg_in_list r rs = true <-> In r rs.
Proof.
  intros r rs. induction rs as [|r' rs' IH]; simpl.
  - split; intro H; [discriminate | contradiction].
  - destruct (hreg_eqb r r') eqn:E.
    + apply hreg_eqb_spec in E. subst r'. split; auto.
    + rewrite IH. split; [right; exact H | intros [Heq | Hin]; [subst; rewrite hreg_eqb_refl in E; discriminate | exact Hin]].
Qed.

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

(** When [no_dup_hregs] holds on a duplicate-free list `ts`, distinct
    elements in `ts` never map to the same [hreg]. *)
Lemma no_dup_hregs_inj : forall rm ts,
  NoDup ts -> no_dup_hregs rm ts = true ->
  forall t1 t2 r, In t1 ts -> In t2 ts -> t1 <> t2 ->
  zmap_find_nat t1 rm = Some r -> zmap_find_nat t2 rm = Some r -> False.
Proof.
  unfold no_dup_hregs. intros rm ts Hndup.
  assert (Hgen : forall seen, no_dup_hregs_acc rm ts seen = true ->
            forall t1 t2 r, In t1 ts -> In t2 ts -> t1 <> t2 ->
            zmap_find_nat t1 rm = Some r -> zmap_find_nat t2 rm = Some r -> False).
  { induction Hndup as [|t ts' Hnotin Hndup' IH]; intros seen Hacc t1 t2 r Hin1 Hin2 Hneq Hr1 Hr2; simpl in *.
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
    set `ts` accepted by [all_callee_saved]. *)
Theorem clobber_preserves_agrees : forall rm ts tenv ms arb,
  all_callee_saved rm ts = true ->
  state_agrees rm ts tenv ms ->
  state_agrees rm ts tenv (clobber_call arb ms).
Proof.
  intros rm ts tenv ms arb Hcs [Hslot Hlive]. split.
  - intros t Hnone. simpl. apply Hslot. exact Hnone.
  - intros t Hin. unfold read_mach in *.
    specialize (Hlive t Hin).
    destruct (zmap_find_nat t rm) as [r|] eqn:Er; simpl.
    + rewrite (all_callee_saved_spec rm ts t r Hcs Hin Er). exact Hlive.
    + exact Hlive.
Qed.

(** Corollary for poll edges: when [check_succs_polls] accepts a
    `Poll` edge to block `si`, `filc_pollcheck_slow` clobbering
    caller-saved registers preserves every live-in and phi-defined
    temporary of `si`. *)
Theorem poll_edge_clobber_sound : forall rm header_live tenv ms arb,
  all_callee_saved rm header_live = true ->
  state_agrees rm header_live tenv ms ->
  state_agrees rm header_live tenv (clobber_call arb ms).
Proof.
  intros. apply clobber_preserves_agrees; assumption.
Qed.

(** Writing temporary `d` preserves every other temporary `t <> d`
    whose register does not collide with `d`'s, and sets `d` to `v`. *)
Theorem write_mach_step_sound : forall rm live tenv ms d v,
  (forall r t, In t live -> t <> d ->
     zmap_find_nat d rm = Some r -> zmap_find_nat t rm = Some r -> False) ->
  state_agrees rm (filter (fun t => negb (Nat.eqb t d)) live) tenv ms ->
  state_agrees rm live (fun t => if Nat.eqb t d then v else tenv t) (write_mach rm ms d v).
Proof.
  intros rm live tenv ms d v Hdisj [Hslot Hlive]. split.
  - intros t Hnone. unfold write_mach.
    destruct (zmap_find_nat d rm) as [rd|] eqn:Erd; simpl.
    + destruct (Nat.eqb t d) eqn:Etd.
      * apply Nat.eqb_eq in Etd. subst t. rewrite Hnone in Erd. discriminate.
      * apply Hslot. exact Hnone.
    + destruct (Nat.eqb t d) eqn:Etd; [reflexivity | apply Hslot; exact Hnone].
  - intros t Hin. unfold read_mach, write_mach.
    destruct (Nat.eqb t d) eqn:Etd.
    + apply Nat.eqb_eq in Etd. subst t.
      destruct (zmap_find_nat d rm) as [rd|] eqn:Erd; simpl.
      * rewrite hreg_eqb_refl. reflexivity.
      * rewrite Nat.eqb_refl. reflexivity.
    + assert (Hin_filt : In t (filter (fun x => negb (Nat.eqb x d)) live)).
      { apply filter_In. split; [exact Hin | rewrite Etd; reflexivity]. }
      specialize (Hlive t Hin_filt). unfold read_mach in Hlive.
      destruct (zmap_find_nat d rm) as [rd|] eqn:Erd;
      destruct (zmap_find_nat t rm) as [rt|] eqn:Ert; simpl.
      * destruct (hreg_eqb rt rd) eqn:Er.
        -- apply hreg_eqb_spec in Er. subst rt.
           exfalso. apply Nat.eqb_neq in Etd.
           eapply Hdisj; [exact Hin | exact Etd | reflexivity | exact Ert].
        -- exact Hlive.
      * exact Hlive.
      * exact Hlive.
      * rewrite Etd. exact Hlive.
Qed.

(** Complete one-instruction simulation theorem: reading inputs `uses`,
    clobbering caller-saved registers according to `ri_call`, and
    writing a destination `d` preserves [state_agrees] whenever
    [no_dup_hregs] and [all_callee_saved] hold as checked by
    [check_rinsts_rev]. *)
Theorem check_rinst_step_sound :
  forall rm live_after d uses call f arb1 arb2 tenv ms,
  let live_mid := filter (fun t => negb (Nat.eqb t d)) live_after in
  let live_before := uses ++ live_mid in
  (forall r t, In t live_after -> t <> d ->
     zmap_find_nat d rm = Some r -> zmap_find_nat t rm = Some r -> False) ->
  (match call with RCallAfterReads => all_callee_saved rm live_mid = true | _ => True end) ->
  (match call with RCallDuringReads => all_callee_saved rm live_before = true | _ => True end) ->
  state_agrees rm live_before tenv ms ->
  let ms_pre := match call with RCallDuringReads => clobber_call arb1 ms | _ => ms end in
  let args_mach := map (read_mach rm ms_pre) uses in
  let args_abs := map tenv uses in
  let ms_post_call :=
    match call with
    | RCallNone => ms_pre
    | RCallAfterReads | RCallDuringReads => clobber_call arb2 ms_pre
    end in
  args_mach = args_abs /\
  state_agrees rm live_after
    (fun t => if Nat.eqb t d then f args_abs else tenv t)
    (write_mach rm ms_post_call d (f args_mach)).
Proof.
  intros rm live_after d uses call f arb1 arb2 tenv ms
    live_mid live_before Hnodup Hca Hcd Hagree ms_pre args_mach args_abs ms_post_call.
  assert (Hagree_pre : state_agrees rm live_before tenv ms_pre).
  { subst ms_pre. destruct call; try exact Hagree.
    apply clobber_preserves_agrees; assumption. }
  assert (Hargs : args_mach = args_abs).
  { unfold args_mach, args_abs. apply map_ext_in. intros u Hu.
    destruct Hagree_pre as [_ Hlb]. apply Hlb.
    unfold live_before. apply in_or_app. left. exact Hu. }
  split; [exact Hargs|].
  rewrite Hargs.
  apply write_mach_step_sound; [exact Hnodup|].
  assert (Hagree_mid : state_agrees rm live_mid tenv ms_pre).
  { destruct Hagree_pre as [Hs Hlb]. split; [exact Hs|].
    intros t Ht. apply Hlb. unfold live_before. apply in_or_app. right. exact Ht. }
  subst ms_post_call. destruct call.
  - exact Hagree_mid.
  - apply clobber_preserves_agrees; [exact Hca | exact Hagree_mid].
  - apply clobber_preserves_agrees.
    + intros. unfold all_callee_saved in *.
      clear -Hcd. unfold live_before in Hcd.
      induction uses as [|u uses' IH]; simpl in *; [exact Hcd|].
      destruct (zmap_find_nat u rm) as [ru|].
      * destruct (hreg_callee_saved ru); [exact (IH Hcd) | discriminate].
      * exact (IH Hcd).
    + exact Hagree_mid.
Qed.

(** Callee-saved save and restore invariant: every callee-saved
    register `r` is restored to its caller entry value `entry_regs r`,
    whether `r` was saved and restored from its dedicated save slot
    (because [rm] used `r`) or untouched throughout the body (because
    [rm] never assigned `r` and every call preserves callee-saved
    registers). *)
Definition exec_saves (used : list hreg) (entry_regs : hreg -> Z) (save_mem : hreg -> Z)
  : hreg -> Z :=
  fun r => if hreg_in_list r used then entry_regs r else save_mem r.

Definition exec_restores (used : list hreg) (save_mem : hreg -> Z) (body_regs : hreg -> Z)
  : hreg -> Z :=
  fun r => if hreg_in_list r used then save_mem r else body_regs r.

Theorem callee_saves_restore_sound :
  forall (used : list hreg) (entry_regs body_regs save_mem0 : hreg -> Z) (r : hreg),
  hreg_callee_saved r = true ->
  (hreg_in_list r used = false -> body_regs r = entry_regs r) ->
  exec_restores used (exec_saves used entry_regs save_mem0) body_regs r = entry_regs r.
Proof.
  intros used entry_regs body_regs save_mem0 r _ Huntouched.
  unfold exec_restores, exec_saves.
  destruct (hreg_in_list r used) eqn:Ein.
  - reflexivity.
  - apply Huntouched. reflexivity.
Qed.

(** Capability root invariant: `KLower k` is never mapped to an
    allocatable register [PmReg], so pointer lowers stay in their
    `lowers[]` GC root slots. *)
Theorem lower_key_never_hreg : forall rc k r,
  key_pm_loc rc (KLower k) <> Some (PmReg r).
Proof.
  intros rc k r. simpl.
  destruct (slot (rc_cx rc) (KLower k)); intro H; discriminate.
Qed.

(** ## 3. Parallel-move soundness *)

(** Abstract valuation of parallel-move locations. *)
Definition eval_pm_src (env : pm_loc -> Z) (half : bool) (s : pm_src) : Z :=
  let m := if half then two32 else two64 in
  match s with
  | PsLoc l => env l mod m
  | PsConst n => n mod m
  | PsGlobal _ => 0
  end.

Definition exec_pmove_abs (env : pm_loc -> Z) (m : pmove) : pm_loc -> Z :=
  let v := eval_pm_src env (pmv_half m) (pmv_src m) in
  fun l => if pm_loc_eqb l (pmv_dst m) then v else env l.

Lemma pm_loc_eqb_refl : forall l, pm_loc_eqb l l = true.
Proof.
  destruct l as [r | off |]; simpl.
  - apply hreg_eqb_refl.
  - apply Z.eqb_refl.
  - reflexivity.
Qed.

Lemma pm_loc_eqb_spec : forall a b, pm_loc_eqb a b = true <-> a = b.
Proof.
  intros a b. destruct a as [r1 | o1 |], b as [r2 | o2 |]; simpl;
    try (split; intro H; [discriminate | congruence]).
  - rewrite hreg_eqb_spec. split; congruence.
  - rewrite Z.eqb_eq. split; congruence.
  - split; reflexivity.
Qed.

Lemma loc_not_read_eval_unchanged : forall env m m',
  loc_read_in_pmoves (pmv_dst m) [m'] = false ->
  eval_pm_src (exec_pmove_abs env m) (pmv_half m') (pmv_src m')
  = eval_pm_src env (pmv_half m') (pmv_src m').
Proof.
  intros env m m' Hnr. simpl in Hnr.
  unfold eval_pm_src, exec_pmove_abs.
  destruct (pmv_src m') as [l' | n | g]; try reflexivity.
  destruct (pm_loc_eqb l' (pmv_dst m)) eqn:E.
  - apply pm_loc_eqb_spec in E. subst l'. rewrite pm_loc_eqb_refl in Hnr. discriminate.
  - reflexivity.
Qed.

(** Ready-move peeling step: if `m`'s destination is not read by any
    other move `m'` in `rest`, executing `m` now establishes `m`'s
    final target value and leaves every source in `rest` unchanged. *)
Theorem ready_pmove_step_sound : forall env m rest,
  loc_read_in_pmoves (pmv_dst m) rest = false ->
  let env1 := exec_pmove_abs env m in
  env1 (pmv_dst m) = eval_pm_src env (pmv_half m) (pmv_src m) /\
  (forall m', In m' rest ->
     eval_pm_src env1 (pmv_half m') (pmv_src m')
     = eval_pm_src env (pmv_half m') (pmv_src m')) /\
  (forall l, l <> pmv_dst m -> env1 l = env l).
Proof.
  intros env m rest Hnr env1. split; [|split].
  - unfold env1, exec_pmove_abs. rewrite pm_loc_eqb_refl. reflexivity.
  - intros m' Hin. induction rest as [|r0 rs IH]; simpl in *.
    + contradiction.
    + destruct (match pmv_src r0 with PsLoc l' => pm_loc_eqb (pmv_dst m) l' | _ => false end) eqn:Eh;
        [discriminate|].
      destruct Hin as [<- | Hin'].
      * apply loc_not_read_eval_unchanged. simpl. rewrite Eh. reflexivity.
      * apply IH; assumption.
  - intros l Hneq. unfold env1, exec_pmove_abs.
    destruct (pm_loc_eqb l (pmv_dst m)) eqn:E; [|reflexivity].
    apply pm_loc_eqb_spec in E. contradiction.
Qed.

(** Cycle-breaking step: saving `old` into `PmCycleTmp` (`%rcx`) and
    rewriting reads of `old` to `PmCycleTmp` preserves the target value
    of every move (provided `PmCycleTmp` was not previously read) and
    eliminates all reads of `old`, making `old` immediately ready on
    the next step. *)
Definition save_cycle_abs (env : pm_loc -> Z) (old : pm_loc) : pm_loc -> Z :=
  fun l => if pm_loc_eqb l PmCycleTmp then env old else env l.

Definition subst_one_pmove (old : pm_loc) (m : pmove) : pmove :=
  let src' :=
    match pmv_src m with
    | PsLoc l => if pm_loc_eqb l old then PsLoc PmCycleTmp else PsLoc l
    | s => s
    end in
  mkPMove (pmv_half m) (pmv_src_w m) (pmv_dst m) src'.

Theorem cycle_break_step_sound : forall env old m,
  old <> PmCycleTmp ->
  (match pmv_src m with PsLoc PmCycleTmp => False | _ => True end) ->
  let env1 := save_cycle_abs env old in
  let m' := subst_one_pmove old m in
  eval_pm_src env1 (pmv_half m') (pmv_src m') = eval_pm_src env (pmv_half m) (pmv_src m) /\
  loc_read_in_pmoves old [m'] = false.
Proof.
  intros env old m Hnot_tmp Hno_tmp env1 m'.
  unfold env1, m', save_cycle_abs, subst_one_pmove, eval_pm_src. simpl.
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

(** Two live parameters mapped to the same register `HRbx` are rejected. *)
Example valid_alloc_rejects_collision :
  let rb := mkRBlock 0%nat [] [] [mkRInst [0%nat; 1%nat] [] RCallNone] [] in
  let rm := zmap_add_nat 0%nat HRbx (zmap_add_nat 1%nat HRbx (ZMap.empty hreg)) in
  valid_alloc ex_cmap2 [0%nat; 1%nat] [rb] rm = false.
Proof. reflexivity. Qed.

(** A caller-saved register `HR10` live across `RCallAfterReads` is rejected,
    while callee-saved `HRbx` is accepted. *)
Example valid_alloc_rejects_r10_across_call :
  let rb := mkRBlock 0%nat [] [] [mkRInst [] [] RCallAfterReads] [0%nat] in
  valid_alloc ex_cmap2 [0%nat] [rb] (zmap_add_nat 0%nat HR10 (ZMap.empty hreg)) = false /\
  valid_alloc ex_cmap2 [0%nat] [rb] (zmap_add_nat 0%nat HRbx (ZMap.empty hreg)) = true.
Proof. split; reflexivity. Qed.

(** Input of `RCallDuringReads` (`AStorePointer` / `ADispatch`) in `HR11`
    is rejected even when dead after the instruction. *)
Example valid_alloc_rejects_r11_during_reads_call :
  let rb := mkRBlock 0%nat [] [] [mkRInst [0%nat] [] RCallDuringReads] [] in
  valid_alloc ex_cmap2 [0%nat] [rb] (zmap_add_nat 0%nat HR11 (ZMap.empty hreg)) = false /\
  valid_alloc ex_cmap2 [0%nat] [rb] (zmap_add_nat 0%nat HR12 (ZMap.empty hreg)) = true.
Proof. split; reflexivity. Qed.

(** A phi destination in `HR10` on a `Poll` loop back-edge is rejected,
    while `HR13` is accepted. *)
Example valid_alloc_rejects_r10_across_poll :
  let rb0 := mkRBlock 0%nat [(1%nat, false)] [] [] [] in
  let rb1 := mkRBlock 1%nat [(1%nat, true)] [(1%nat, [(0%nat, Some 0%nat); (1%nat, Some 1%nat)])] [] [1%nat] in
  valid_alloc ex_cmap2 [0%nat] [rb0; rb1] (zmap_add_nat 1%nat HR10 (ZMap.empty hreg)) = false /\
  valid_alloc ex_cmap2 [0%nat] [rb0; rb1] (zmap_add_nat 1%nat HR13 (ZMap.empty hreg)) = true.
Proof. split; reflexivity. Qed.

(** Assigning a float temporary (`Double`) to a general register is rejected. *)
Example valid_alloc_rejects_float_class :
  let rb := mkRBlock 0%nat [] [] [] [2%nat] in
  valid_alloc ex_cmap2 [2%nat] [rb] (zmap_add_nat 2%nat HRbx (ZMap.empty hreg)) = false.
Proof. reflexivity. Qed.
