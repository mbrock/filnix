(** Campaign 3's scheduled checks along runs: a doomed frame never runs
    to `unchecked` (docs/formal.md, Campaign 3; docs/rocq.md, "The
    doomed frame"; docs/schedule.md).

    A `check_ahead` whose early bytes fail yields its pointer anyway and
    dooms the frame (`doomed_result/5`): from then on the frame must
    reach, through ahead-transparent instructions only, an access whose
    own check fails, which ends the run `trap(early(Why))`. The
    interpreter makes the run `unchecked(ahead(Why))` where it reaches a
    poll edge, a return or an instruction that is not transparent
    first; and a renew of another capability or a wrong limit stays
    `unchecked(alias)` or `unchecked(limit)` even when doomed. This file
    proves that none of that happens in a checked module's run.

    The argument follows the validator. Where the check was accepted,
    some base N of its pointer at offset K has a need at least K + Hi
    after its access (Ahead.v's `ahead_accepted`): every path ahead
    reaches an access through N whose bytes end at or past N + K + Hi.
    The frame carries that need (`doom_need`): at each step either the
    need stays, or the instruction is the access meeting it, which
    fails, because the check's start N + K + Lo lies in the object and
    the access ends at most 2^63 after it (`need_access_fails`). The
    single definitions in scope still replay, except a doomed proof,
    which holds its pointer though its check did not pass
    (`scope_weak`).

    | Name | Says |
    |---|---|
    | `ahead_holds`, `replays_weak`, `scope_weak` | a doomed frame's scope: each single definition replays, or is a `check_ahead` holding its pointer |
    | `raise_found`, `step_found`, `meet_found`, `phis_found` | where a need at a point comes from: the facts after, or an access through the base |
    | `doom_mem`, `need_access_fails` | the memory a doom leaves, and that an access meeting the need fails there |
    | `doomed_ok`, `dinv` | the invariant: a doomed frame's weak scope, and the need at its point |
    | `doomed_step_checked` | a doomed frame where `doomed_ok` holds never steps to `unchecked` |
    | `doom_start`, `mstep_dinv` | the check that dooms a frame starts the invariant, and every machine step keeps it |
    | `run_doomed_checked`, `interp_doomed_checked` | along a run of a checked module, a doomed frame never steps to `unchecked`; under the interpreter's runtime with no hypothesis about safepoints |

    ## Decisions

    | Decision | Why |
    |---|---|
    | a doomed proof holds its pointer, not a passed check | the check failed; what reuse rules read of it is only the pointer and its capability |
    | the need is carried as the validator's own facts at the frame's point | each step of the frame is a step of the backward walk read forward |
    | the access meeting the need is not located in advance | any access that raises the need past N + K + Hi fails; the need says one comes before the frame leaves the scheduled region | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Interval Sites Identity Coverage Walk Steps Invariant Persistence Single Evidence Chain Renew Guard Ahead.
Import ListNotations.
Open Scope Z_scope.

(** ## A doomed frame's scope *)

(** `ahead_holds ge once e n i`: n holds the pointer the `check_ahead` i
    read, in a frame that agrees with e on i's single-definition
    operands, as `doomed_result/5` leaves it. *)
Definition ahead_holds (ge : genv) (once : list (name * def)) (e : env) (n : name) (i : inst) : Prop :=
  exists lo hi r al ahi v fr0 pp,
    i = Let n A (CheckAhead lo hi r al ahi) [v] /\ value_x ge (fr_env fr0) P v = Some (WPtr pp) /\
    lookup n e = Some (WPtr pp) /\
    (forall a, In a (inst_uses i) -> once_has once a = true -> lookup a (fr_env fr0) = lookup a e).

Definition replays_weak (ge : genv) (once : list (name * def)) (e : env) (m : Memory.mem) (n : name) (i : inst)
  : Prop :=
  replays ge once e m n i \/ ahead_holds ge once e n i.

(** `scope_weak ge fr m`: each single definition in scope replays, or
    holds a doomed check's pointer. *)
Definition scope_weak (ge : genv) (fr : frame) (m : Memory.mem) : Prop :=
  scope_with (replays_weak ge) fr m.

Lemma replays_weak_moves : forall ge, moves (replays_weak ge).
Proof.
  intros ge once e e' m m' n i [H | (lo & hi & r & al & ahi & v & fr0 & pp & Ei & Hv & Hn0 & Ha)] Hn Ha' Hp.
  - left. exact (replays_change _ _ _ _ _ _ _ _ H Hn Ha' Hp).
  - right. exists lo, hi, r, al, ahi, v, fr0, pp. split; [exact Ei|]. split; [exact Hv|]. split; [congruence|].
    intros a Hu Ho. rewrite (Ha' _ Hu Ho). exact (Ha _ Hu Ho).
Qed.

Lemma scope_weak_of : forall ge fr m, scope_holds ge fr m -> scope_weak ge fr m.
Proof. intros ge fr m H l k n s i Hpt Hn Hr Hpos Hsd. left. exact (H _ _ _ _ _ Hpt Hn Hr Hpos Hsd). Qed.

Lemma scope_plain_weak : forall ge fr m, scope_weak ge fr m -> scope_plain ge fr m.
Proof.
  intros ge fr m H l k n s i Hpt Hn Hr Hpos Hsd Ha.
  destruct (H _ _ _ _ _ Hpt Hn Hr Hpos Hsd) as [Hrp | (lo & hi & r & al & ahi & v & fr0 & pp & -> & _)];
    [exact Hrp | discriminate Ha].
Qed.

(** ## Where a need comes from *)

Lemma lookup_del : forall n d fs, lookup n (del d fs) = if name_eqb n d then None else lookup n fs.
Proof.
  intros n d fs. unfold del. induction fs as [|[k v] fs IH]; simpl; [destruct (name_eqb n d); reflexivity|].
  destruct (name_eqb k d) eqn:Ekd; simpl.
  - rewrite IH. apply name_eqb_true in Ekd. subst k. destruct (name_eqb n d); reflexivity.
  - destruct (name_eqb n k) eqn:Enk; [|exact IH].
    apply name_eqb_true in Enk. subst k. rewrite Ekd. reflexivity.
Qed.

(** `raise_found`: after `raise_need/6` over a chain, a need is the one
    before, or the end of the access through an exact base on the
    chain. *)
Lemma raise_found : forall once off size chain fs n h,
  lookup n (fold_left (raise_need once off size) chain fs) = Some h ->
  lookup n fs = Some h \/
  exists k', In (Tmp n, (k', k')) chain /\ once_has once n = true /\ near_offset k' = true /\
    near_offset (k' + off + size) = true /\ h = k' + off + size.
Proof.
  intros once off size chain. induction chain as [|e chain IH]; intros fs n h H; [left; exact H|].
  simpl in H. destruct (IH _ _ _ H) as [H1 | (k' & Hin & Ho & Hk & Hh & ->)];
    [| right; exists k'; split; [right; exact Hin | auto]].
  unfold raise_need in H1.
  destruct (exact_base once e) as [[n' k]|] eqn:Eb; [|left; exact H1].
  destruct (near_offset k && near_offset (k + off + size)) eqn:En; [|left; exact H1].
  assert (Hput : lookup n (put n' (k + off + size) fs) = Some h -> lookup n fs = Some h \/
            (n = n' /\ h = k + off + size)).
  { rewrite lookup_put. destruct (name_eqb n n') eqn:E; [intros Hs | intros Hs; left; exact Hs].
    injection Hs as <-. right. split; [apply name_eqb_true; exact E | reflexivity]. }
  assert (Hfound : n = n' -> h = k + off + size -> lookup n fs = Some h \/ exists k'0, In (Tmp n, (k'0, k'0)) (e :: chain) /\
            once_has once n = true /\ near_offset k'0 = true /\ near_offset (k'0 + off + size) = true /\ h = k'0 + off + size).
  { intros -> ->. right. exists k. unfold exact_base in Eb.
    destruct e as [[n0 | c | g] [k1 k2]]; try discriminate Eb.
    destruct ((k1 =? k2) && once_has once n0) eqn:Ek; [|discriminate Eb]. injection Eb as -> ->.
    apply andb_true_iff in Ek as [Ek Ho]. apply Z.eqb_eq in Ek. subst k2.
    apply andb_true_iff in En as [En1 En2]. split; [left; reflexivity | auto]. }
  destruct (lookup n' fs) as [h0|] eqn:E0.
  - destruct (k + off + size <=? h0); [left; exact H1|].
    destruct (Hput H1) as [Hs | [Hn Hh]]; [left; exact Hs | exact (Hfound Hn Hh)].
  - destruct (Hput H1) as [Hs | [Hn Hh]]; [left; exact Hs | exact (Hfound Hn Hh)].
Qed.

(** A transparent instruction defines at most one name. *)
Lemma transparent_defs : forall i, ahead_transparent i = true ->
  inst_temp_defs i = [] \/ exists d k, inst_temp_defs i = [(d, k)].
Proof.
  intros i H. destruct i; simpl; eauto.
  unfold ahead_transparent, evidence_preserving in H. simpl in H. discriminate H.
  unfold ahead_transparent, evidence_preserving in H. simpl in H. discriminate H.
Qed.

(** `step_found`: a need before an instruction is the need after it, the
    instruction not defining the base, or the end of the instruction's
    own access through an exact base on its proof's chain; and the
    instruction is transparent (`ahead_step/5`). *)
Lemma step_found : forall once ptrs i fs n h,
  lookup n (ahead_step once ptrs i fs) = Some h ->
  ahead_transparent i = true /\
  ((lookup n fs = Some h /\ ~ In n (map fst (inst_temp_defs i))) \/
   exists q x off rs p k', raw_access i = Some (q, x, off, rs) /\ lookup q ptrs = Some p /\
     In (Tmp n, (k', k')) (guard_chain once p) /\ once_has once n = true /\ near_offset k' = true /\
     near_offset (k' + off + fst (access_size_align x)) = true /\ h = k' + off + fst (access_size_align x)).
Proof.
  intros once ptrs i fs n h H. unfold ahead_step in H.
  destruct (ahead_transparent i) eqn:Et; [|discriminate H]. split; [reflexivity|].
  set (fs1 := match first_some _ (inst_temp_defs i) with Some d => del d fs | None => fs end) in H.
  assert (Hfs1 : lookup n fs1 = Some h -> lookup n fs = Some h /\ ~ In n (map fst (inst_temp_defs i))).
  { unfold fs1. intros H1.
    destruct (transparent_defs _ Et) as [E | (d & k & E)]; rewrite E in H1 |- *; simpl in H1 |- *.
    - split; [exact H1 | tauto].
    - destruct (lookup d fs) as [hd|] eqn:Ed.
      + rewrite lookup_del in H1. destruct (name_eqb n d) eqn:End; [discriminate H1|].
        split; [exact H1|]. intros [<- | []]. rewrite name_eqb_refl in End. discriminate End.
      + split; [exact H1|]. intros [<- | []]. rewrite Ed in H1. discriminate H1. }
  destruct (raw_access i) as [[[[q x] off] rs]|] eqn:Er; [|left; exact (Hfs1 H)].
  destruct (lookup q ptrs) as [p|] eqn:Ep; [|left; exact (Hfs1 H)].
  destruct (raise_found _ _ _ _ _ _ _ H) as [H1 | (k' & Hin & Ho & Hk & Hh & ->)]; [left; exact (Hfs1 H1)|].
  right. exists q, x, off, rs, p, k'. auto 8.
Qed.

(** The least of a need over edges, through `ahead_meet/2`'s fold. *)
Definition meet_fold (n : name) (rest : list facts) (h0 : option Z) : option Z :=
  fold_left (fun acc f' => let* h := acc in let* h1 := lookup n f' in Some (Z.min h h1)) rest h0.

Lemma meet_fold_none : forall n rest, meet_fold n rest None = None.
Proof. intros n rest. unfold meet_fold. induction rest as [|f rest IH]; [reflexivity | exact IH]. Qed.

Lemma meet_fold_some : forall n rest h0 h,
  meet_fold n rest (Some h0) = Some h ->
  h <= h0 /\ forall f, In f rest -> exists h1, lookup n f = Some h1 /\ h <= h1.
Proof.
  intros n rest. induction rest as [|f rest IH]; intros h0 h H.
  - injection H as ->. split; [lia | intros f []].
  - unfold meet_fold in H. simpl in H. destruct (lookup n f) as [h1|] eqn:Ef.
    + destruct (IH _ _ H) as [Hle Hall]. split; [lia|].
      intros f' [<- | Hin]; [exists h1; split; [exact Ef | lia] | exact (Hall _ Hin)].
    + fold (meet_fold n rest None) in H. rewrite meet_fold_none in H. discriminate H.
Qed.

(** Whether the fold finds a need depends only on the base. *)
Lemma meet_fold_found : forall n rest h0 h1,
  meet_fold n rest (Some h0) = None -> meet_fold n rest (Some h1) = None.
Proof.
  intros n rest. induction rest as [|f rest IH]; intros h0 h1 H; [discriminate H|].
  unfold meet_fold in H |- *. simpl in H |- *. destruct (lookup n f) as [h|].
  - exact (IH _ _ H).
  - fold (meet_fold n rest None). apply meet_fold_none.
Qed.

(** `meet_found`: a need at a jump is at most the need on each edge
    (`ahead_meet/2`), and there is an edge. *)
Lemma meet_found : forall fss n h,
  lookup n (ahead_meet fss) = Some h ->
  fss <> [] /\ forall fs, In fs fss -> exists h1, lookup n fs = Some h1 /\ h <= h1.
Proof.
  intros [|f rest] n h H; [discriminate H|]. split; [discriminate|].
  simpl in H. fold (meet_fold n rest) in H.
  assert (Hf : exists h0, lookup n f = Some h0 /\ meet_fold n rest (Some h0) = Some h).
  { induction f as [|[k v] f IH]; simpl in H; [discriminate H|].
    change (fold_left _ rest (Some v)) with (meet_fold k rest (Some v)) in H.
    simpl. destruct (name_eqb n k) eqn:Enk.
    - apply name_eqb_true in Enk. subst k. exists v. split; [reflexivity|].
      destruct (meet_fold n rest (Some v)) as [hv|] eqn:Ev; simpl in H.
      + rewrite name_eqb_refl in H. exact H.
      + exfalso. destruct (IH H) as (h0 & _ & E0).
        rewrite (meet_fold_found _ _ _ h0 Ev) in E0. discriminate E0.
    - apply IH. destruct (meet_fold k rest (Some v)); simpl in H; [rewrite Enk in H|]; exact H. }
  destruct Hf as (h0 & Ef & Hm). destruct (meet_fold_some _ _ _ _ Hm) as [Hle Hall].
  intros fs [<- | Hin]; [exists h0; split; [exact Ef | lia] | exact (Hall _ Hin)].
Qed.

(** `phis_found`: a need at a block's entry is the need before its first
    instruction, of a base no phi defines (`phi_ends_need/3`). *)
Lemma phis_found : forall phs fs n h,
  lookup n (phis_end_needs phs fs) = Some h -> lookup n fs = Some h /\ ~ In n (map phi_name phs).
Proof.
  unfold phis_end_needs. intros phs. induction phs as [|[d kk pairs] phs IH]; intros fs n h H; simpl in H.
  - split; [exact H | tauto].
  - destruct (IH _ _ _ H) as [H1 Hn]. rewrite lookup_del in H1.
    destruct (name_eqb n d) eqn:E; [discriminate H1|]. split; [exact H1|].
    intros [Hd | Hin]; [simpl in Hd; subst d; rewrite name_eqb_refl in E; discriminate E | exact (Hn Hin)].
Qed.

(** ## The access that meets the need *)

(** `doom_mem m pn kl hreq`: the memory a doom leaves, seen from the
    base's pointer pn. pn's object is there; the check's start, pn + kl
    modulo 2^64, lies in it, below 2^48; and the object ends before
    pn + hreq. *)
Definition doom_mem (m : Memory.mem) (pn : ptr) (kl hreq : Z) : Prop :=
  exists base reg, (ptr_cap pn = Obj base \/ ptr_cap pn = Ro base) /\
    object_region base (m_regions m) = Some reg /\
    base <= raw_address (ptr_addr pn) kl <= 2 ^ 48 /\ kl < hreq /\
    r_end reg < raw_address (ptr_addr pn) kl + (hreq - kl).

(** The object is as it was, or freed and empty. *)
Lemma doom_mem_persists : forall m m' pn kl hreq, doom_mem m pn kl hreq -> persists m m' -> doom_mem m' pn kl hreq.
Proof.
  intros m m' pn kl hreq (base & reg & Hc & E & Hb & Hk & Hend) Hp.
  destruct (Hp _ _ E) as [E' | E'].
  - exists base, reg. auto.
  - exists base, (freed_region reg). split; [exact Hc|]. split; [exact E'|]. split; [exact Hb|]. split; [exact Hk|].
    simpl. rewrite (object_region_base _ _ _ E). lia.
Qed.

(** `need_access_fails`: an access through a pointer of pn's capability,
    at an exact near offset k' from pn, whose bytes end at or past
    pn + hreq with that end near, fails its test: its start and end lie
    at most 2^63 past the check's start, so they do not wrap below the
    object's end. *)
Lemma need_access_fails : forall m pn kl hreq x k' off size r al,
  doom_mem m pn kl hreq -> objects_fit (m_regions m) ->
  ptr_cap x = ptr_cap pn -> ptr_addr x mod 2 ^ 64 = (ptr_addr pn + k') mod 2 ^ 64 ->
  near_offset kl = true -> near_offset (k' + off + size) = true -> hreq <= k' + off + size -> 0 < size <= 16 ->
  exists why, access_res m (raw_address (ptr_addr x) off) (ptr_cap x) size r al = Some (RTrap why).
Proof.
  intros m pn kl hreq x k' off size r al (base & reg & Hc & E & Hb & Hk & Hend) Hfit Hcap Haddr Hkl Hh Hle Hs.
  unfold near_offset in Hkl, Hh. apply andb_true_iff in Hkl as [Hkl1 Hkl2]. apply andb_true_iff in Hh as [Hh1 Hh2].
  apply Z.leb_le in Hkl1, Hkl2, Hh1, Hh2.
  set (b := raw_address (ptr_addr pn) kl) in *.
  set (a := raw_address (ptr_addr x) off).
  (* a + size and b + D agree modulo 2^64, D = k' + off + size - kl. *)
  assert (Hmod : a mod 2 ^ 64 = (b + (k' + off + size - kl) - size) mod 2 ^ 64).
  { unfold a, b, raw_address. rewrite Z.mod_mod by lia.
    rewrite <- (Z.add_mod_idemp_l (ptr_addr x) off (2 ^ 64)), Haddr, Z.add_mod_idemp_l by lia.
    replace ((ptr_addr pn + kl) mod 2 ^ 64 + (k' + off + size - kl) - size)
      with ((ptr_addr pn + kl) mod 2 ^ 64 + (k' + off - kl)) by ring.
    rewrite Z.add_mod_idemp_l by lia. f_equal. ring. }
  assert (Ha : 0 <= a < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod (b + (k' + off + size - kl) - size) (2 ^ 64) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (b + (k' + off + size - kl) - size) (2 ^ 64) ltac:(lia)).
  rewrite Z.mod_small in Hmod by lia. rewrite <- Hmod in Hdm.
  destruct (Hfit _ _ E) as [_ Hend48].
  assert (Hout : ~ (base <= a /\ a + size <= r_end reg)) by nia.
  unfold access_res, cap_access_res. rewrite Hcap.
  destruct Hc as [Hc | Hc]; rewrite Hc, E; eexists.
  all: replace ((base <=? a) && (a + size <=? r_end reg)) with false; [reflexivity|].
  all: symmetry; apply andb_false_iff; destruct (Z.le_gt_cases base a);
         [right; apply Z.leb_gt | left; apply Z.leb_gt]; lia.
Qed.

(** ## A raw access that fails stops *)

(** `access_trap_stops`: a raw access whose own check traps at every
    rights and alignment does not continue: `raw_res/2` makes the trap
    `unchecked`. *)
Lemma access_trap_stops : forall ge fr m i q x off need p e1 l1 m1,
  raw_access i = Some (q, x, off, need) ->
  lookup q (fr_env fr) = Some (WPtr p) ->
  (forall r al, exists why, access_res m (raw_address (ptr_addr p) off) (ptr_cap p)
                                     (fst (access_size_align x)) r al = Some (RTrap why)) ->
  inst_step ge fr m i <> Some (IContinue e1 l1 m1).
Proof.
  intros ge fr m i q x off need p e1 l1 m1 Ei Hq Ha Hst.
  destruct i; simpl in Ei; cases Ei.
  all: try discriminate Ei.
  all: injection Ei as <- <- <- <-; subst.
  all: try (rewrite inst_step_let in Hst by reflexivity).
  all: cbn -[int_load_res access_res pointer_load_effects store_res pointer_store_effects raw_address] in Hst.
  all: rewrite Hq in Hst.
  - (* raw_load: the load traps, which `raw_res` makes unchecked. *)
    destruct (Ha Read 1) as [w Hw]. unfold int_load_res in Hst.
    destruct t; simpl in Hw; rewrite Hw in Hst; simpl in Hst; discriminate Hst.
  - (* raw_load_pointer: its check traps. *)
    destruct (Ha Read 8) as [w Hw]. simpl in Hw. rewrite Hw in Hst.
    destruct k; discriminate Hst.
  - (* raw_store: the store's check traps. *)
    destruct (width_value_class w); simpl in Hst; try discriminate Hst.
    destruct (value_x _ _ _ _) as [x|]; simpl in Hst; try discriminate Hst.
    unfold store_res in Hst.
    destruct w, x; simpl in Hst; try discriminate Hst;
      match type of Hst with context [access_res ?m ?a ?c ?s ?r ?al] =>
        destruct (Ha r al) as [w' Hw]; simpl in Hw; rewrite Hw in Hst; discriminate Hst end.
  - (* raw_store_pointer: its check traps. *)
    destruct (Ha Write 8) as [w Hw]. simpl in Hw.
    destruct (value_x _ _ _ _) as [x|]; simpl in Hst; try discriminate Hst.
    rewrite Hw in Hst. discriminate Hst.
Qed.

(** ## The memory a doom leaves *)

(** `doom_from_checks`: where a check of s1 bytes at b passes and one of
    s2 bytes at the same address, rights and alignment traps, b lies in
    the object, s1 bytes fit and s2 bytes do not. *)
Lemma doom_from_checks : forall m b c s1 s2 r al x1 w,
  access_res m b c s1 r al = Some x1 -> (forall w', x1 <> RTrap w') ->
  access_res m b c s2 r al = Some (RTrap w) ->
  exists base reg, (c = Obj base \/ c = Ro base) /\ object_region base (m_regions m) = Some reg /\
    base <= b /\ b + s1 <= r_end reg /\ r_end reg < b + s2.
Proof.
  unfold access_res, cap_access_res. intros m b c s1 s2 r al x1 w H1 Hn H2.
  destruct c as [| base | base | g | g];
    try (injection H1 as <-; exfalso; eapply Hn; reflexivity); try discriminate H1.
  all: destruct (object_region base (m_regions m)) as [reg|] eqn:Er; [|discriminate H1].
  all: exists base, reg; split; [auto|]; split; [exact Er|].
  all: destruct ((base <=? b) && (b + s1 <=? r_end reg)) eqn:E1;
         [|injection H1 as <-; exfalso; eapply Hn; reflexivity].
  all: apply andb_true_iff in E1 as [Eb Ee]; apply Z.leb_le in Eb, Ee.
  all: destruct ((base <=? b) && (b + s2 <=? r_end reg)) eqn:E2;
         [injection H1 as <-; injection H2 as E; exfalso; eapply Hn; exact E|].
  all: apply andb_false_iff in E2 as [E2 | E2]; apply Z.leb_gt in E2; lia.
Qed.

(** ## A need does not shrink *)

(** `raise_keeps`: `raise_need/6` only raises a need. *)
Lemma raise_keeps : forall once off size chain fs n h,
  lookup n fs = Some h ->
  exists h', lookup n (fold_left (raise_need once off size) chain fs) = Some h' /\ h <= h'.
Proof.
  intros once off size chain. induction chain as [|e chain IH]; intros fs n h H; simpl; [exists h; split; [exact H | lia]|].
  assert (Hstep : exists h1, lookup n (raise_need once off size fs e) = Some h1 /\ h <= h1).
  { unfold raise_need. destruct (exact_base once e) as [[n' k]|]; [|exists h; split; [exact H | lia]].
    destruct (near_offset k && near_offset (k + off + size)); [|exists h; split; [exact H | lia]].
    destruct (lookup n' fs) as [h0|] eqn:E0.
    - destruct (k + off + size <=? h0) eqn:Ele; [exists h; split; [exact H | lia]|].
      rewrite lookup_put. destruct (name_eqb n n') eqn:En; [|exists h; split; [exact H | lia]].
      apply name_eqb_true in En. subst n'. rewrite H in E0. injection E0 as <-.
      apply Z.leb_gt in Ele. exists (k + off + size). split; [reflexivity | lia].
    - rewrite lookup_put. destruct (name_eqb n n') eqn:En; [|exists h; split; [exact H | lia]].
      apply name_eqb_true in En. subst n'. rewrite H in E0. discriminate E0. }
  destruct Hstep as (h1 & H1 & Hle). destruct (IH _ _ _ H1) as (h' & H' & Hle'). exists h'. split; [exact H' | lia].
Qed.

(** `step_keeps`: before a transparent instruction that does not define
    the base, the need is at least what it is after. *)
Lemma step_keeps : forall once ptrs i fs n h,
  ahead_transparent i = true -> ~ In n (map fst (inst_temp_defs i)) -> lookup n fs = Some h ->
  exists h', lookup n (ahead_step once ptrs i fs) = Some h' /\ h <= h'.
Proof.
  intros once ptrs i fs n h Ht Hn H. unfold ahead_step. rewrite Ht.
  set (fs1 := match first_some _ (inst_temp_defs i) with Some d => del d fs | None => fs end).
  assert (H1 : lookup n fs1 = Some h).
  { unfold fs1. destruct (first_some _ (inst_temp_defs i)) as [d|] eqn:Ef; [|exact H].
    destruct (first_some_in _ _ _ _ _ Ef) as ([d' k] & Hin & Hd). simpl in Hd.
    destruct (lookup d' fs); [|discriminate Hd]. injection Hd as <-.
    rewrite lookup_del. destruct (name_eqb n d') eqn:E; [|exact H].
    apply name_eqb_true in E. subst. exfalso. apply Hn. apply in_map_iff. exists (d', k). auto. }
  destruct (raw_access i) as [[[[q x] off] rs]|]; [|exists h; split; [exact H1 | lia]].
  destruct (lookup q ptrs) as [p|]; [|exists h; split; [exact H1 | lia]].
  exact (raise_keeps _ _ _ _ _ _ _ H1).
Qed.

(** ## The base dominates the check *)

(** `chain_dominating`: a single-definition name on a guard chain whose
    start dominates a point dominates it too: each step of the chain is
    a flight's lower operand. *)
Lemma chain_dominating : forall md f l k fuel p lo hi n blo bhi,
  checked_module md -> In (IFunc f) md -> is_reachable (fn_doms f) l = true ->
  (forall y, p = Tmp y -> once_has (single_definitions f) y = true -> dominating f l k y) ->
  In (Tmp n, (blo, bhi)) (guard_chain_go (single_definitions f) fuel p lo hi) ->
  once_has (single_definitions f) n = true -> dominating f l k n.
Proof.
  intros md f l k fuel. induction fuel as [|fuel IH]; intros p lo hi n blo bhi Hmd Hin Hr Hdom Hb Ho; simpl in Hb.
  - destruct Hb as [E | []]. injection E as -> _ _. exact (Hdom n eq_refl Ho).
  - destruct Hb as [E | Hb]; [injection E as -> _ _; exact (Hdom n eq_refl Ho)|].
    destruct p as [x | c | g]; try contradiction.
    destruct (lookup x (single_definitions f)) as [[| ph | i]|] eqn:Ex; try contradiction.
    destruct i as [ | d o args lw | | | | | | ]; try contradiction.
    destruct lw as [| b']; try contradiction.
    destruct (flight_term o args b') as [[ov sign]|]; [|contradiction].
    destruct (offset_interval _ ov L) as [[olo ohi]|]; [|contradiction].
    assert (Hox : once_has (single_definitions f) x = true) by (unfold once_has; rewrite Ex; reflexivity).
    pose proof (Hdom x eq_refl Hox) as Hdx.
    assert (Hdb : forall y, b' = Tmp y -> once_has (single_definitions f) y = true -> dominating f l k y).
    { intros y -> Hoy. apply (operand_dominating _ _ _ _ _ _ _ Hmd Hin Hr Ex Hdx); [|exact Hoy].
      apply (value_temps_in (map flight_arg_value args ++ [Tmp y])). apply in_or_app. right. left. reflexivity. }
    destruct (sign =? 1); exact (IH _ _ _ _ _ _ Hmd Hin Hr Hdb Hb Ho).
Qed.

(** A `check_ahead` has its own access inside its early range:
    lo < ahi < hi (`valid_op/1`). *)
Lemma ahead_ok : forall md f b q lo hi r al ahi args,
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) ->
  In (Let q A (CheckAhead lo hi r al ahi) args) (b_insts b) -> lo < ahi < hi.
Proof.
  intros md f b q lo hi r al ahi args Hmd Hin Hb Hi. destruct (inst_valid _ _ _ _ Hmd Hin Hb Hi) as [cls Hvi].
  unfold valid_inst in Hvi. simpl in Hvi.
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
  repeat match goal with H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end. lia.
Qed.

(** ## No alias in a doomed frame *)

(** A renew's own failure is a trap or `unchecked(span)`, never an
    alias (`renew_res/4`). *)
Lemma renew_res_not_alias : forall chk p m rr,
  (forall w, chk <> RUnchecked w) ->
  renew_res chk p m = Some rr -> rr = RVal (WPtr p) \/ (exists w, rr = RTrap w) \/ rr = RUnchecked Span.
Proof.
  unfold renew_res. intros chk p m rr Hc H. cases H; injection H as <-; eauto. exfalso. exact (Hc _ eq_refl).
Qed.

(** An access check passes or traps; it is never `unchecked`. *)
Lemma access_res_checked : forall m a c size r al chk,
  access_res m a c size r al = Some chk -> forall w, chk <> RUnchecked w.
Proof.
  unfold access_res, cap_access_res, readonly_access_res, aligned_res. intros m a c size r al chk H w ->.
  destruct c; cases H; destruct r; cases H; discriminate H.
Qed.

(** An access check fails for an access reason: never an alias or a
    wrong limit. *)
Lemma access_res_reason : forall m a c size r al w,
  access_res m a c size r al = Some (RTrap w) -> w <> Alias /\ w <> WhyLimit.
Proof.
  unfold access_res, cap_access_res, readonly_access_res, aligned_res. intros m a c size r al w H.
  destruct c; cases H; try destruct r; cases H; try (injection H as <-); try (split; discriminate).
Qed.

Lemma renew_trap_reason : forall w p m r, renew_res (RTrap w) p m = Some (RUnchecked r) -> r = Span.
Proof. unfold renew_res. intros w p m r H. destruct w; cases H; congruence. Qed.

(** A raw load's own failure is its access check's. *)
Lemma int_load_reason : forall t k m a c r0 r,
  int_load_res t k m a c = Some r0 -> raw_res r0 = RUnchecked r -> r <> Alias /\ r <> WhyLimit.
Proof.
  unfold int_load_res. intros t k m a c r0 r H Hr.
  destruct (access_res m a c _ Read 1) as [chk|] eqn:Ea; [|discriminate H]. simpl in H.
  destruct chk as [u | w | w].
  - destruct t; cases H; injection H as <-; discriminate Hr.
  - injection H as <-. simpl in Hr. injection Hr as <-. exact (access_res_reason _ _ _ _ _ _ _ Ea).
  - exact (False_ind _ (access_res_checked _ _ _ _ _ _ _ Ea _ eq_refl)).
Qed.

(** A `va_arg` traps or reads; it is never `unchecked`. *)
Lemma va_arg_reason : forall k p m p0 r, va_arg_res k p m = Some p0 -> fst p0 = RUnchecked r -> False.
Proof.
  unfold va_arg_res. intros k p m p0 r H Hr. cases H; injection H as <-; discriminate Hr.
Qed.

(** `op_alias_source`: only a renew, a renew over a hull, a half check
    and a `check_limit` find an alias or a wrong limit. *)
Lemma op_alias_source : forall o k xs m r m',
  op_res o k xs m = Some (OpRes (RUnchecked r) m') -> r = Alias \/ r = WhyLimit ->
  k = A /\
  ((exists lo hi rs al x1 x2, o = Renew lo hi rs al /\ xs = [x1; x2] /\ r = Alias) \/
   (exists lo hi rs al x1 x2 x3, o = RenewHull lo hi rs al /\ xs = [x1; x2; x3] /\ r = Alias) \/
   (exists bd lo hi rs al x1 x2, o = HalfCheck bd lo hi rs al /\ xs = [x1; x2] /\ r = Alias) \/
   (exists lo hi rs al x1 x2, o = CheckLimit lo hi rs al /\ xs = [x1; x2] /\ r = WhyLimit)).
Proof.
  intros o k xs m r m' H Hr.
  unfold op_res, op_res_int in H. destruct o; cases H; try (injection H as <- _; destruct Hr; discriminate).
  all: try discriminate H.
  all: try (injection H as Hr3 _).
  all: try (subst; split; [reflexivity|]; do 3 right; do 6 eexists; split; [reflexivity | split; reflexivity]).
  all: try (subst; split; [reflexivity|]; do 2 right; left; do 7 eexists; split; [reflexivity | split; reflexivity]).
  all: try (subst; split; [reflexivity|]; right; left; do 7 eexists; split; [reflexivity | split; reflexivity]).
  all: try (subst; split; [reflexivity|]; left; do 6 eexists; split; [reflexivity | split; reflexivity]).
  all: exfalso.
  all: try (match goal with E : access_res _ _ _ _ _ _ = Some (RTrap ?w) |- _ =>
              destruct (access_res_reason _ _ _ _ _ _ _ E); destruct Hr; congruence end).
  all: try (match goal with E : access_res _ _ _ _ _ _ = Some (RUnchecked _) |- _ =>
              exact (access_res_checked _ _ _ _ _ _ _ E _ eq_refl) end).
  all: try (match goal with E : access_res _ _ _ _ _ _ = Some ?x, H3 : checked_res ?x _ = RUnchecked _ |- _ =>
              destruct x; simpl in H3; try discriminate H3; injection H3 as ->;
              exact (access_res_checked _ _ _ _ _ _ _ E _ eq_refl) end).
  all: repeat match goal with H3 : ?x = RUnchecked _ |- _ => is_var x; subst x end.
  all: try (match goal with E : renew_res (RTrap _) _ _ = Some (RUnchecked _) |- _ =>
              destruct (renew_res_not_alias _ _ _ _ ltac:(intros ? ?; discriminate) E) as [E' | [(w & E') | E']];
              try discriminate E'; injection E' as ->; destruct Hr; discriminate end).
  all: try (unfold float_integer in H; cases H; fail).
  all: try (match goal with E : renew_res (RTrap _) _ _ = Some (RUnchecked _) |- _ =>
              rewrite (renew_trap_reason _ _ _ _ E) in Hr; destruct Hr; discriminate end).
  all: try (match goal with E : int_load_res _ _ _ _ _ = Some ?r0, H3 : raw_res ?r0 = RUnchecked _ |- _ =>
              destruct (int_load_reason _ _ _ _ _ _ _ E H3); destruct Hr; contradiction end).
  all: try (match goal with E : va_arg_res _ _ _ = Some ?p0, H3 : fst ?p0 = RUnchecked _ |- _ =>
              exact (va_arg_reason _ _ _ _ _ E H3) end).
  all: try (match goal with Ea : access_res _ _ _ _ _ _ = Some ?x, E : renew_res ?x _ _ = Some (RUnchecked _) |- _ =>
              destruct (renew_res_not_alias _ _ _ _ (access_res_checked _ _ _ _ _ _ _ Ea) E) as [E' | [(w' & E') | E']];
              try discriminate E'; injection E' as ->; destruct Hr; discriminate end).
  all: match goal with E : half_res _ _ _ = RUnchecked _ |- _ =>
         unfold half_res in E; cases E; injection E as <-; destruct Hr; discriminate end.
Qed.

Lemma map2_option_length : forall (X Y Z : Type) (f : X -> Y -> option Z) xs ys zs,
  map2_option f xs ys = Some zs -> length ys = length zs.
Proof.
  intros X Y Z f xs. induction xs as [|x xs IH]; intros [|y ys] zs H; simpl in H; try discriminate H.
  - injection H as <-. reflexivity.
  - destruct (f x y); [|discriminate H]. simpl in H.
    destruct (map2_option f xs ys) as [zs'|] eqn:E; [|discriminate H]. injection H as <-.
    simpl. f_equal. exact (IH _ _ E).
Qed.

(** A store's own failure is its access check's. *)
Lemma store_reason : forall w m a c x r m' why,
  store_res w m a c x = Some (r, m') -> raw_res r = RUnchecked why -> why <> Alias /\ why <> WhyLimit.
Proof.
  unfold store_res. intros w m a c x r m' why H Hr.
  destruct w, x; try discriminate H.
  all: destruct (access_res _ _ _ _ _ _) as [chk|] eqn:Ea; try discriminate H; simpl in H; injection H as <- _.
  all: destruct chk; simpl in Hr; try discriminate Hr; injection Hr as <-.
  all: first [ exact (access_res_reason _ _ _ _ _ _ _ Ea) | exact (False_ind _ (access_res_checked _ _ _ _ _ _ _ Ea _ eq_refl)) ].
Qed.

(** `alias_source`: a transparent instruction finds an alias or a
    wrong limit only as a renew, a renew over a hull, a half check or a
    `check_limit`. *)
Lemma alias_source : forall ge fr m i w,
  ahead_transparent i = true ->
  inst_step ge fr m i = Some (IStop (Unchecked w)) -> w = Alias \/ w = WhyLimit ->
  (exists q lo hi rs al a1 a2, i = Let q A (Renew lo hi rs al) [a1; a2] /\ w = Alias) \/
  (exists q lo hi rs al a1 a2 a3, i = Let q A (RenewHull lo hi rs al) [a1; a2; a3] /\ w = Alias) \/
  (exists q bd lo hi rs al a1 a2, i = Let q A (HalfCheck bd lo hi rs al) [a1; a2] /\ w = Alias) \/
  (exists q lo hi rs al a1 a2, i = Let q A (CheckLimit lo hi rs al) [a1; a2] /\ w = WhyLimit).
Proof.
  intros ge fr m i w Ht H Hw.
  destruct i as [q k o args | d o args lw | wd off v a | off v a es | r cl args | r cl args | x size | x y].
  - destruct (special_let o) eqn:Es; [destruct o; try discriminate Es; destruct k; discriminate Ht|].
    rewrite inst_step_let in H by exact Es. cbv zeta in H.
    destruct (op_arg_classes o k) as [cls|]; [|discriminate H]. simpl in H.
    destruct (map2_option _ cls args) as [xs|] eqn:Ex; [|discriminate H]. simpl in H.
    destruct (op_res o k xs m) as [[rr m'|why|q0 kont]|] eqn:Eo; try discriminate H.
    unfold bind_res in H. destruct rr; try discriminate H. injection H as <-.
    pose proof (map2_option_length _ _ _ _ _ _ _ Ex) as Hl.
    destruct (op_alias_source _ _ _ _ _ _ Eo Hw) as (-> & [(lo & hi & rs & al & x1 & x2 & -> & -> & ->) |
      [(lo & hi & rs & al & x1 & x2 & x3 & -> & -> & ->) | [(bd & lo & hi & rs & al & x1 & x2 & -> & -> & ->) |
       (lo & hi & rs & al & x1 & x2 & -> & -> & ->)]]]).
    all: destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; simpl in Hl; try discriminate Hl.
    + left. do 7 eexists. split; reflexivity.
    + right. left. do 8 eexists. split; reflexivity.
    + right. right. left. do 8 eexists. split; reflexivity.
    + right. right. right. do 7 eexists. split; reflexivity.
  - exfalso. simpl in H. cases H.
  - exfalso. simpl in H. cases H. injection H as H.
    unfold store_out in H. destruct (raw_res r) eqn:Er; try discriminate H. injection H as ->.
    destruct (store_reason _ _ _ _ _ _ _ _ Heqo2 Er). destruct Hw; contradiction.
  - discriminate Ht.
  - discriminate Ht.
  - discriminate Ht.
  - discriminate Ht.
  - exfalso. simpl in H. discriminate H.
Qed.

Section Weak.

Variables (ge : genv) (md : module) (fr : frame) (m : Memory.mem) (l : name) (k : Z).
Hypothesis Hmd : checked_module md.
Hypothesis Hin : In (IFunc (fr_fn fr)) md.
Hypothesis Hr : is_reachable (fn_doms (fr_fn fr)) l = true.
Hypothesis Hs : scope_weak ge fr m.
Hypothesis Hpt : point_site (fr_fn fr) (fr_at fr) = Some (l, k).

(** `fact_holds`: a check-like single definition that dominates the
    point holds the pointer its pointer operand holds there, whether
    its check passed or it is a doomed `check_ahead`. *)
Lemma fact_holds : forall n i fa,
  lookup n (single_definitions (fr_fn fr)) = Some (DInst i) -> check_fact i = Some fa -> f_q fa = n ->
  dominating (fr_fn fr) l k n -> stable (single_definitions (fr_fn fr)) (f_p fa) ->
  exists pp, lookup n (fr_env fr) = Some (WPtr pp) /\ value_x ge (fr_env fr) P (f_p fa) = Some (WPtr pp).
Proof.
  intros n i fa Hn Hf Hq (s & D & Hn' & Hpos & Hsd) Hst. rewrite Hn in Hn'. injection Hn' as <-.
  assert (Hag : forall e0, (forall a, In a (inst_uses i) -> once_has (single_definitions (fr_fn fr)) a = true ->
                                  lookup a e0 = lookup a (fr_env fr)) ->
             value_x ge e0 P (f_p fa) = value_x ge (fr_env fr) P (f_p fa)).
  { intros e0 Ha. apply value_x_agree. intros y E. exact (Ha y (check_fact_uses _ _ _ Hf E) (Hst y E)). }
  destruct (Hs _ _ _ _ _ Hpt Hn (check_fact_replayable _ _ Hf) Hpos Hsd)
    as [(fr0 & m0 & e1 & l1 & m1 & Hst' & He1 & Hops & _) | (lo & hi & r & al & ahi & v & fr0 & pp & -> & Hv & Hn0 & Hops)].
  - destruct (access_fact_some _ _ Hf) as [fb Hfb].
    destruct (check_like_continue _ _ _ _ _ _ _ _ _ Hf Hfb Hst') as (_ & _ & _ & pp & -> & Hx & _).
    exists pp. rewrite Hq in He1. split; [rewrite <- He1; apply lookup_put_same | rewrite <- (Hag _ Hops); exact Hx].
  - exists pp. split; [exact Hn0|]. rewrite <- (Hag _ Hops). simpl in Hf. injection Hf as <-. exact Hv.
Qed.

(** `weak_operands`: a reuse form's source and its renewed pointer
    hold pointers of one capability. *)
Lemma weak_operands : forall b kk i n1 p p1 lo1 hi1 al1 d,
  find_block l (fn_blocks (fr_fn fr)) = Some b -> nth_error (b_insts b) kk = Some i -> k = Z.of_nat kk ->
  In n1 (inst_uses i) -> (forall y, p = Tmp y -> In y (inst_uses i)) ->
  lookup n1 (s_renews (fn_src md (fr_fn fr))) = Some (p1, lo1, hi1, al1) ->
  pointer_distance (single_definitions (fr_fn fr)) p (Tmp p1) = Some d ->
  exists pp1 pp, lookup n1 (fr_env fr) = Some (WPtr pp1) /\ value_x ge (fr_env fr) P p = Some (WPtr pp) /\
    ptr_cap pp = ptr_cap pp1.
Proof.
  intros b kk i n1 p p1 lo1 hi1 al1 d Hb Hk Hkk Hu1 Hu Esrc Ed.
  destruct (renew_source_def _ _ _ _ _ _ _ Esrc) as (i1 & r1 & En1 & Hcf & Hop1).
  assert (Hdn1 : dominating (fr_fn fr) l k n1)
    by (apply (operand_at md fr l k Hmd Hin Hr Hpt b kk i n1 Hb Hk Hkk Hu1); unfold once_has; rewrite En1; reflexivity).
  destruct (fact_holds n1 i1 _ En1 Hcf eq_refl Hdn1 ltac:(intros y E; injection E as <-; exact Hop1))
    as (pp1 & Hn1 & Hp1). simpl in Hp1.
  assert (Hdp1 : dominating (fr_fn fr) l k p1)
    by exact (operand_dominating _ _ _ _ _ _ _ Hmd Hin Hr En1 Hdn1 (check_fact_uses _ _ _ Hcf eq_refl) Hop1).
  assert (Hdp : forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y)
    by (intros y E Ho; exact (operand_at md fr l k Hmd Hin Hr Hpt b kk i y Hb Hk Hkk (Hu y E) Ho)).
  assert (Hdq : forall y, Tmp p1 = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y)
    by (intros y E _; injection E as <-; exact Hdp1).
  pose proof (scope_plain_weak _ _ _ Hs) as Hsp.
  destruct (distance_pointer ge md fr m l k Hmd Hin Hr Hsp Hpt p (Tmp p1) pp1 d Hp1 Hdp Hdq Ed) as [pp Hpp].
  destruct (pointer_distance_sound ge md fr m l k Hmd Hin Hr Hsp Hpt p (Tmp p1) pp pp1 d Hpp Hp1 Hdp Hdq Ed)
    as [Hcap _].
  exists pp1, pp. auto.
Qed.

Theorem renew_not_alias : forall b kk q lo hi r al n1 p rest live out,
  find_block l (fn_blocks (fr_fn fr)) = Some b ->
  nth_error (b_insts b) kk = Some (Let q A (Renew lo hi r al) [Tmp n1; p]) -> k = Z.of_nat kk ->
  checked_inst_rest (fn_src md (fr_fn fr)) (Let q A (Renew lo hi r al) [Tmp n1; p]) rest live = Some out ->
  inst_step ge fr m (Let q A (Renew lo hi r al) [Tmp n1; p]) <> Some (IStop (Unchecked Alias)).
Proof.
  intros b kk q lo hi r al n1 p rest live out Hb Hk Hkk H.
  unfold checked_inst_rest in H. cbn beta iota zeta in H.
  destruct (lookup n1 (s_renews (fn_src md (fr_fn fr)))) as [[[[p1 lo1] hi1] al1]|] eqn:Esrc; [|discriminate H].
  destruct (pointer_distance (s_once (fn_src md (fr_fn fr))) p (Tmp p1)) as [d|] eqn:Ed; [|discriminate H].
  destruct (weak_operands b kk _ n1 p p1 lo1 hi1 al1 d Hb Hk Hkk ltac:(simpl; auto)
              ltac:(intros y ->; simpl; auto) Esrc Ed) as (pp1 & pp & Hn1 & Hpp & Hcap).
  rewrite inst_step_let by reflexivity. cbn beta iota zeta delta [op_arg_classes map2_option].
  replace (value_x ge (fr_env fr) A (Tmp n1)) with (Some (WPtr pp1)) by (simpl; rewrite Hn1; reflexivity).
  rewrite Hpp. cbn beta iota. unfold op_res, op_res_int. cbn beta iota zeta delta [fmt_of].
  rewrite Hcap, cap_eqb_refl.
  destruct (access_res _ _ _ _ _ _) as [chk|] eqn:Ea; [|discriminate]. cbn beta iota.
  destruct (renew_res chk pp m) as [rr|] eqn:Er; [|discriminate]. cbn beta iota.
  destruct (renew_res_not_alias _ _ _ _ (access_res_checked _ _ _ _ _ _ _ Ea) Er) as [-> | [(w & ->) | ->]]; discriminate.
Qed.

(** `half_not_alias`: a half check the pass accepts gives no
    `unchecked(alias)` in a doomed frame. *)
Theorem half_not_alias : forall b kk q bd lo hi r al n1 p rest live out,
  find_block l (fn_blocks (fr_fn fr)) = Some b ->
  nth_error (b_insts b) kk = Some (Let q A (HalfCheck bd lo hi r al) [Tmp n1; p]) -> k = Z.of_nat kk ->
  checked_inst_rest (fn_src md (fr_fn fr)) (Let q A (HalfCheck bd lo hi r al) [Tmp n1; p]) rest live = Some out ->
  inst_step ge fr m (Let q A (HalfCheck bd lo hi r al) [Tmp n1; p]) <> Some (IStop (Unchecked Alias)).
Proof.
  intros b kk q bd lo hi r al n1 p rest live out Hb Hk Hkk H.
  unfold checked_inst_rest in H. cbn beta iota zeta in H.
  destruct (lookup n1 (s_renews (fn_src md (fr_fn fr)))) as [[[[p1 lo1] hi1] al1]|] eqn:Esrc;
    [|discriminate H].
  destruct (pointer_distance (s_once (fn_src md (fr_fn fr))) p (Tmp p1)) as [d|] eqn:Ed; [|discriminate H].
  destruct (weak_operands b kk _ n1 p p1 lo1 hi1 al1 d Hb Hk Hkk ltac:(simpl; auto)
              ltac:(intros y ->; simpl; auto) Esrc Ed) as (pp1 & pp & Hn1 & Hpp & Hcap).
  rewrite inst_step_let by reflexivity. cbn beta iota zeta delta [op_arg_classes map2_option].
  replace (value_x ge (fr_env fr) A (Tmp n1)) with (Some (WPtr pp1)) by (simpl; rewrite Hn1; reflexivity).
  rewrite Hpp. cbn beta iota. unfold op_res, op_res_int. cbn beta iota zeta delta [fmt_of].
  rewrite Hcap, cap_eqb_refl.
  destruct (access_res _ _ _ _ _ _) as [chk|]; [|discriminate]. cbn beta iota.
  destruct (half_passes _ _ _ _ _ _ _) as [[ok'|]|]; [| discriminate | discriminate]. cbn beta iota.
  unfold half_res. destruct chk, ok'; discriminate.
Qed.

(** `hull_not_alias`: a renew over a hull the pass accepts gives no
    `unchecked(alias)` in a doomed frame. *)
Theorem hull_not_alias : forall b kk q lo hi r al nl nh p rest live out,
  find_block l (fn_blocks (fr_fn fr)) = Some b ->
  nth_error (b_insts b) kk = Some (Let q A (RenewHull lo hi r al) [Tmp nl; Tmp nh; p]) -> k = Z.of_nat kk ->
  checked_inst_rest (fn_src md (fr_fn fr)) (Let q A (RenewHull lo hi r al) [Tmp nl; Tmp nh; p]) rest live
    = Some out ->
  inst_step ge fr m (Let q A (RenewHull lo hi r al) [Tmp nl; Tmp nh; p]) <> Some (IStop (Unchecked Alias)).
Proof.
  intros b kk q lo hi r al nl nh p rest live out Hb Hk Hkk H.
  unfold checked_inst_rest in H. cbn beta iota zeta in H.
  destruct (hull_renewable _ _ _ _ _ _ _ _) eqn:Ehr; [clear H | discriminate H].
  unfold hull_renewable in Ehr.
  destruct (lookup nl (s_renews (fn_src md (fr_fn fr)))) as [[[[pl lol] hil] all]|] eqn:El;
    [|discriminate Ehr].
  destruct (lookup nh (s_renews (fn_src md (fr_fn fr)))) as [[[[ph loh] hih] alh]|] eqn:Eh;
    [|discriminate Ehr].
  destruct (pointer_distance (s_once (fn_src md (fr_fn fr))) p (Tmp pl)) as [dl|] eqn:Edl; [|discriminate Ehr].
  destruct (pointer_distance (s_once (fn_src md (fr_fn fr))) p (Tmp ph)) as [dh|] eqn:Edh; [|discriminate Ehr].
  destruct (weak_operands b kk _ nl p pl lol hil all dl Hb Hk Hkk ltac:(simpl; auto)
              ltac:(intros y ->; simpl; auto) El Edl) as (ppl & pp & Hnl & Hpp & Hcapl).
  destruct (weak_operands b kk _ nh p ph loh hih alh dh Hb Hk Hkk ltac:(simpl; auto)
              ltac:(intros y ->; simpl; auto) Eh Edh) as (pph & pp' & Hnh & Hpp' & Hcaph).
  rewrite Hpp in Hpp'. injection Hpp' as <-.
  rewrite inst_step_let by reflexivity. cbn beta iota zeta delta [op_arg_classes map2_option].
  replace (value_x ge (fr_env fr) A (Tmp nl)) with (Some (WPtr ppl)) by (simpl; rewrite Hnl; reflexivity).
  replace (value_x ge (fr_env fr) A (Tmp nh)) with (Some (WPtr pph)) by (simpl; rewrite Hnh; reflexivity).
  rewrite Hpp. cbn beta iota. unfold op_res, op_res_int. cbn beta iota zeta delta [fmt_of].
  rewrite <- Hcapl, <- Hcaph, cap_eqb_refl. cbn beta iota delta [andb].
  destruct (access_res _ _ _ _ _ _) as [chk|] eqn:Ea; [|discriminate]. cbn beta iota.
  destruct (renew_res chk pp m) as [rr|] eqn:Er; [|discriminate]. cbn beta iota.
  destruct (renew_res_not_alias _ _ _ _ (access_res_checked _ _ _ _ _ _ _ Ea) Er) as [-> | [(w & ->) | ->]]; discriminate.
Qed.

End Weak.

(** ## The doomed frame's invariant *)

(** `dpos s is out`: where the pass is in a block, without its facts:
    before one of its steps, or between a check and the access it took
    with it. *)
Definition dpos (s : src) (is : list inst) (out : list fact) : Prop :=
  (exists live, walks s is live out) \/
  (exists access rest' live', is = access :: rest' /\ walks s rest' live' out /\
     (raw_access access <> None \/ exists r cl args, access = RawCall r cl args)).

(** `pass_after`: the pass takes one instruction, or a check and the
    raw access or raw call it took with it (`pass_live_after`). *)
Lemma pass_after : forall s i rest live rest' live',
  checked_inst_rest s i rest live = Some (rest', live') ->
  rest' = rest \/
  exists a, rest = a :: rest' /\ (raw_access a <> None \/ exists r cl args, a = RawCall r cl args).
Proof.
  intros s i rest live rest' live' Hc.
  assert (Hcov : forall a q lo hi r al, covered_access a q lo hi r al = true -> raw_access a <> None)
    by (unfold covered_access; intros a q lo hi r al H E; rewrite E in H; discriminate H).
  destruct (check_fact i) as [fa0|] eqn:Hf.
  - destruct (access_fact_some _ _ Hf) as [fb Hg].
    destruct (checked_inst_rest_check _ _ _ _ _ _ _ _ Hf Hg Hc) as (access & -> & Hu & _).
    apply andb_true_iff in Hu as [Hu _]. right. exists access. split; [reflexivity | left; exact (Hcov _ _ _ _ _ _ Hu)].
  - destruct (is_check_local i) eqn:Hcl.
    + destruct i as [q k o args | | | | | | |]; try discriminate Hcl.
      destruct k; try discriminate Hcl; destruct o; try discriminate Hcl;
        destruct args; try discriminate Hcl.
      destruct (checked_inst_rest_local_cov _ _ _ _ _ _ _ _ _ _ _ Hc) as (access & -> & Hu & _).
      right. exists access. split; [reflexivity | left; exact (Hcov _ _ _ _ _ _ Hu)].
    + destruct (is_check_function i) eqn:Hcf.
      * destruct i as [q k o args | | | | | | |]; try discriminate Hcf.
        destruct k; try discriminate Hcf; destruct o; try discriminate Hcf.
        destruct (checked_inst_rest_function_rest _ _ _ _ _ _ _ Hc) as (_ & r & cargs & ->).
        right. eexists. split; [reflexivity | right; eauto].
      * assert (Hs' : pass_special i = false).
        { destruct (pass_special i) eqn:Hp; [|reflexivity].
          destruct (pass_special_cases _ Hp Hf) as [E | E]; congruence. }
        rewrite (checked_inst_rest_generic _ _ _ _ Hs') in Hc.
        left. exact (proj1 (generic_rest_shape _ _ _ _ _ _ Hc)).
Qed.

(** `need_at f n hreq pt`: at the point pt, the validator's facts need
    n's bytes up to at least hreq: at a block's entry, its entry facts;
    within it, what its instructions from the point make of its exit
    facts. *)
Definition need_at (f : func) (n : name) (hreq : Z) (pt : point) : Prop :=
  match pt with
  | Snapshot _ _ => False
  | Enter l _ => exists fs h, lookup l (ahead_entries f) = Some fs /\ lookup n fs = Some h /\ hreq <= h
  | Exec l is _ =>
      exists b h, find_block l (fn_blocks f) = Some b /\
        lookup n (facts_from f is (block_exit f b)) = Some h /\ hreq <= h
  end.

(** `doomed_ok ge md m fr`: a doomed frame keeps its weak scope, is
    where the pass walked, and carries a need for a base whose object
    the doom left too short. *)
Definition doomed_ok (ge : genv) (md : module) (m : Memory.mem) (fr : frame) : Prop :=
  let f := fr_fn fr in
  scope_weak ge fr m /\
  (forall l is j, fr_at fr = Exec l is j ->
     exists E b out, pass_exits (fn_src md f) f = Some E /\ find_block l (fn_blocks f) = Some b /\
       lookup l E = Some out /\ dpos (fn_src md f) is out) /\
  exists n pn kl hreq, lookup n (fr_env fr) = Some (WPtr pn) /\ near_offset kl = true /\
    doom_mem m pn kl hreq /\ need_at f n hreq (fr_at fr).

(** `dinv ge md c`: the running frame, if doomed, is `doomed_ok`. *)
Definition dinv (ge : genv) (md : module) (c : config) : Prop :=
  fr_doomed (c_frame c) <> None -> doomed_ok ge md (c_mem c) (c_frame c).

(** ### Entering a block *)

(** `doomed_enter`: entering a block, the need is the entry's, of a
    base no phi defines, before the block's first instruction. *)
Lemma doomed_enter : forall ge md c c' l from,
  checked_module md -> fr_at (c_frame c) = Enter l from -> step ge c = Next c' ->
  shaped md (c_frame c) -> doomed_ok ge md (c_mem c) (c_frame c) -> doomed_ok ge md (c_mem c') (c_frame c').
Proof.
  intros ge md c c' l from Hmd Ha Hs Hsh (Hsc & _ & n & pn & kl & hreq & Hn & Hkl & Hdm & Hneed).
  destruct (step_enter _ _ _ _ _ Ha Hs) as (b & e & Hb & Hphi & ->). simpl.
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh. destruct Hsh as (Hin & Hr & _).
  destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & Hnd & Hdd).
  destruct (find_block_in _ _ _ Hb) as [Hbin Hl].
  split; [|split].
  - intros l' k n' s i Hpt Hn' Hrp Hpos Hsd. simpl in Hpt. rewrite Hb in Hpt.
    injection Hpt as <- <-. rewrite Nat.sub_diag in Hsd.
    pose proof (site_first _ _ _ _ _ _ Hpos Hsd) as Hsd0.
    assert (HX : forall x, In x (map phi_name (b_phis b)) ->
                   exists D, In (x, SAt l (-1), D) (def_positions (fr_fn (c_frame c))))
      by (rewrite <- Hl; exact (phi_defs_here _ _ Hbin)).
    destruct (scope_moves _ _ _ _ _ _ _ _ _ _ _ Hf Hd Hdd Hr HX
                (fun a Ha => phis_env_other _ _ _ _ _ _ Hphi Ha) Hn' Hpos Hsd0) as [Hn1 Ha1].
    exact (replays_weak_moves _ _ _ _ _ _ _ _
             (Hsc l (-1) n' s i ltac:(rewrite Ha; reflexivity) Hn' Hrp Hpos Hsd0) Hn1 Ha1 (persists_refl _)).
  - intros l' is j E. simpl in E. injection E as <- <- <-.
    destruct (module_func _ _ Hmd Hin) as (_ & (b1 & bs & Eb & Hnoin) & EE & HE).
    destruct (pass_fold _ _ _ _ _ HE Hnd (fun b _ => eq_refl) b Hbin)
      as (exits & out & _ & Hout & Hc).
    exists EE, b, out. split; [exact HE|]. split; [exact Hb|]. split; [rewrite <- Hl; exact Hout|].
    left. exists (entry_live (fr_fn (c_frame c)) exits b). exists (S (length (b_insts b))). exact Hc.
  - rewrite Ha in Hneed. destruct Hneed as (fs & h & Hfs & Hh & Hle).
    rewrite <- Hl, (ahead_entry _ _ Hnd Hbin) in Hfs. injection Hfs as <-.
    destruct (phis_found _ _ _ _ Hh) as [Hh' Hnp].
    exists n, pn, kl, hreq. split; [simpl; rewrite (phis_env_other _ _ _ _ _ _ Hphi Hnp); exact Hn|].
    split; [exact Hkl|]. split; [exact Hdm|]. simpl. exists b, h. auto.
Qed.

(** ## What a step of a doomed frame does *)

(** `doomed_result_cases`: `doomed_result/5` keeps the instruction's
    result and the frame's doom; or a `check_ahead` whose early bytes
    fail goes on with its pointer, dooming the frame; or, in a doomed
    frame, an `unchecked` result that is not an alias or a wrong limit
    is the early trap. *)
Lemma doomed_result_cases : forall ge fr m i out od,
  doomed_result ge fr m i out = Some od ->
  od = (out, fr_doomed fr) \/
  (exists d lo hi r al ahi v p w, i = Let d A (CheckAhead lo hi r al ahi) [v] /\ out = IStop (Trap (Early w)) /\
     value_x ge (fr_env fr) P v = Some p /\
     od = (IContinue (put d p (fr_env fr)) (fr_locals fr) m,
           Some (match fr_doomed fr with Some w0 => w0 | None => w end))) \/
  (exists w why, out = IStop (Unchecked w) /\ fr_doomed fr = Some why /\ od = (IStop (Trap (Early why)), Some why)).
Proof.
  intros ge fr m i out od H.
  assert (Hother : ahead_inst i = false -> od = (out, fr_doomed fr) \/
            (exists w why, out = IStop (Unchecked w) /\ fr_doomed fr = Some why /\
               od = (IStop (Trap (Early why)), Some why))).
  { intros Ea. rewrite (doomed_result_other _ _ _ _ _ Ea) in H.
    destruct out as [e l m' | oc | g xs pd | q k | x]; try (injection H as <-; left; reflexivity).
    destruct oc as [x | xs | | | t | why | why | ]; try (injection H as <-; left; reflexivity).
    destruct (fr_doomed fr) as [w0|] eqn:Ed; [|injection H as <-; left; reflexivity].
    destruct why; injection H as <-; first [left; reflexivity | right; eauto]. }
  destruct (ahead_inst i) eqn:Ea; [|destruct (Hother eq_refl) as [E | E]; [left; exact E | right; right; exact E]].
  destruct i as [d k o args | | | | | | |]; try discriminate Ea. destruct k; try discriminate Ea.
  destruct o; try discriminate Ea. destruct args as [|v [|v' args]]; try discriminate Ea.
  unfold doomed_result in H.
  destruct out as [e l m' | oc | g xs pd | q k | x]; try (injection H as <-; left; reflexivity).
  destruct oc as [x | xs | | | t | why | why | ]; try (injection H as <-; left; reflexivity).
  - destruct why; try (injection H as <-; left; reflexivity).
    destruct (value_x ge (fr_env fr) P v) as [p|] eqn:Ev; [|discriminate H]. simpl in H. injection H as <-.
    right. left. do 9 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [exact Ev|].
    destruct (fr_doomed fr); reflexivity.
  - destruct (fr_doomed fr) as [w0|] eqn:Ed; [|injection H as <-; left; reflexivity].
    destruct why; injection H as <-; first [left; reflexivity | right; right; eauto].
Qed.

(** `proof_pointers_def`: a proof the pass maps to its pointer is a
    single definition whose check-like instruction proves that pointer
    (`proof_pointer/3`). *)
Lemma proof_pointers_def : forall f q p,
  lookup q (proof_pointers f (single_definitions f)) = Some p ->
  exists i fa, lookup q (single_definitions f) = Some (DInst i) /\ check_fact i = Some fa /\
    f_q fa = q /\ f_p fa = p.
Proof.
  intros f q p H.
  destruct (lookup_some_in _ _ _ _ H) as (q' & Eq & Hin). apply name_eqb_true in Eq. subst q'.
  unfold proof_pointers in Hin. apply in_flat_map in Hin as (b & Hb & Hin). apply in_flat_map in Hin as (i & Hi & Hin).
  destruct i as [q0 k o args | | | | | | |]; try destruct Hin.
  destruct k; try destruct Hin.
  destruct (proof_pointer o args) as [p0|] eqn:Ep; [|destruct Hin].
  destruct (once_has (single_definitions f) q0) eqn:Ho; [|destruct Hin].
  destruct Hin as [E | []]. injection E as -> ->.
  unfold once_has in Ho. destruct (lookup q (single_definitions f)) as [D|] eqn:Ed; [|discriminate Ho].
  destruct (once_position _ _ _ Ed) as (s & _ & Hu).
  destruct (In_nth_error _ _ Hi) as [kk Hk].
  pose proof (inst_position f b kk (Let q A o args) (q, A) Hb Hk (or_introl eq_refl)) as Hpos.
  destruct (Hu _ _ Hpos) as [_ <-].
  exists (Let q A o args).
  destruct o; try discriminate Ep; destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; simpl in Ep; try discriminate Ep;
    injection Ep as <-; (eexists; split; [reflexivity|]; split; [reflexivity|]; split; reflexivity).
Qed.

(** An access is at most 16 bytes. *)
Lemma access_size_small : forall x, 0 < fst (access_size_align x) <= 16.
Proof. intros [[| | | | t] | w |]; try destruct t; try destruct w; simpl; lia. Qed.

(** An access check's trap is not an early one. *)
Lemma access_res_not_early : forall m a c size r al w w',
  access_res m a c size r al = Some (RTrap w) -> w <> Early w'.
Proof.
  unfold access_res, cap_access_res, readonly_access_res, aligned_res. intros m a c size r al w w' H.
  destruct c; cases H; try destruct r; cases H; try (injection H as <-); discriminate.
Qed.

(** `ahead_early`: a `check_ahead` traps early where its own bytes pass
    and its early ones fail, at its pointer's address plus lo. *)
Lemma ahead_early : forall ge fr m q lo hi r al ahi v w,
  inst_step ge fr m (Let q A (CheckAhead lo hi r al ahi) [v]) = Some (IStop (Trap (Early w))) ->
  exists pp x1, value_x ge (fr_env fr) P v = Some (WPtr pp) /\
    access_res m (raw_address (ptr_addr pp) lo) (ptr_cap pp) (ahi - lo) r al = Some x1 /\
    (forall w', x1 <> RTrap w') /\
    access_res m (raw_address (ptr_addr pp) lo) (ptr_cap pp) (hi - lo) r al = Some (RTrap w).
Proof.
  intros ge fr m q lo hi r al ahi v w H.
  rewrite inst_step_let in H by reflexivity. cbn beta iota zeta delta [op_arg_classes map2_option] in H.
  destruct (value_x ge (fr_env fr) P v) as [[u | pp | c s]|] eqn:Ev; simpl in H; try discriminate H.
  unfold op_res, op_res_int in H. cbn beta iota zeta delta [fmt_of] in H.
  destruct (access_res m (raw_address (ptr_addr pp) lo) (ptr_cap pp) (ahi - lo) r al) as [x1|] eqn:E1;
    [|discriminate H]. simpl in H.
  exists pp, x1. split; [reflexivity|]. split; [exact E1|].
  destruct x1 as [u | w1 | w1]; [| injection H as E; subst w1; exact (False_ind _ (access_res_not_early _ _ _ _ _ _ _ _ E1 eq_refl)) |].
  all: destruct (access_res m (raw_address (ptr_addr pp) lo) (ptr_cap pp) (hi - lo) r al) as [x2|] eqn:E2;
    [|discriminate H]; simpl in H.
  all: destruct x2 as [u2 | w2 | w2]; simpl in H; try discriminate H; injection H as <-.
  all: split; [intros w' E; discriminate E | reflexivity].
Qed.

(** A raw access reads its proof. *)
Lemma raw_access_uses : forall i q x off rs, raw_access i = Some (q, x, off, rs) -> In q (inst_uses i).
Proof.
  intros i q x off rs H. destruct i; simpl in H; cases H; inversion H; subst; simpl; auto.
  all: apply in_or_app; right; left; reflexivity.
Qed.

Lemma facts_from_cons : forall f i is out,
  facts_from f (i :: is) out =
  ahead_step (single_definitions f) (proof_pointers f (single_definitions f)) i (facts_from f is out).
Proof. reflexivity. Qed.

(** The name an instruction's single definition defines is its own. *)
Lemma once_inst_name : forall f n i, lookup n (single_definitions f) = Some (DInst i) -> In n (map fst (inst_temp_defs i)).
Proof.
  intros f n i H. destruct (once_position _ _ _ H) as (s & Hpos & _).
  destruct (dinst_site _ _ _ _ Hpos) as (d & j & ->).
  destruct (position_inst _ _ _ _ _ Hpos) as (_ & _ & _ & _ & _ & _ & Hn). exact Hn.
Qed.

(** `doomed_mem`: the runtime's action at a safepoint changes only the
    memory, which persists. *)
Lemma doomed_mem : forall ge md m m' fr,
  persists m m' -> doomed_ok ge md m fr -> doomed_ok ge md m' fr.
Proof.
  intros ge md m m' fr Hp (Hsc & Hpos & n & pn & kl & hreq & Hn & Hkl & Hdm & Hneed).
  split; [exact (scope_with_mem _ _ _ _ (replays_weak_moves ge) Hsc Hp)|]. split; [exact Hpos|].
  exists n, pn, kl, hreq. split; [exact Hn|]. split; [exact Hkl|].
  split; [exact (doom_mem_persists _ _ _ _ _ Hdm Hp) | exact Hneed].
Qed.

(** ## No `unchecked` in a doomed frame *)

(** In a doomed frame, `doomed_result/5` passes on only an alias or a
    wrong limit as `unchecked`. *)
Lemma doomed_unchecked : forall ge fr m i out od why w,
  fr_doomed fr = Some why -> doomed_result ge fr m i out = Some od -> fst od = IStop (Unchecked w) ->
  out = IStop (Unchecked w) /\ (w = Alias \/ w = WhyLimit).
Proof.
  intros ge fr m i out od why w Hd H Ho.
  assert (G : forall o', (match fr_doomed fr, o' with
                          | Some why0, (Alias | WhyLimit) => Some (IStop (Unchecked o'), fr_doomed fr)
                          | Some why0, _ => Some (IStop (Trap (Early why0)), fr_doomed fr)
                          | None, _ => Some (IStop (Unchecked o'), None)
                          end) = Some od -> fst od = IStop (Unchecked w) ->
                 IStop (Unchecked o') = IStop (Unchecked w) /\ (w = Alias \/ w = WhyLimit)).
  { intros o' Hg Hf. rewrite Hd in Hg. destruct o'; injection Hg as <-; simpl in Hf; try discriminate Hf;
      injection Hf as <-; auto. }
  destruct (ahead_inst i) eqn:Ea.
  - destruct i as [d k o args | | | | | | |]; try discriminate Ea. destruct k; try discriminate Ea.
    destruct o; try discriminate Ea. destruct args as [|v [|v' args]]; try discriminate Ea.
    unfold doomed_result in H.
    destruct out as [e l m' | oc | g xs pd | q k | x]; try (injection H as <-; discriminate Ho).
    destruct oc as [x | xs | | | t | r0 | r0 | ]; try (injection H as <-; discriminate Ho).
    + destruct r0; try (injection H as <-; discriminate Ho).
      destruct (value_x _ _ _ _); simpl in H; [injection H as <-; discriminate Ho | discriminate H].
    + exact (G r0 H Ho).
  - rewrite (doomed_result_other _ _ _ _ _ Ea) in H.
    destruct out as [e l m' | oc | g xs pd | q k | x]; try (injection H as <-; discriminate Ho).
    destruct oc as [x | xs | | | t | r0 | r0 | ]; try (injection H as <-; discriminate Ho).
    exact (G r0 H Ho).
Qed.

(** An instruction's step ends the run only with its own outcome. *)
Lemma inst_next_done : forall c l rest j out d o, inst_next c l rest j out d = Done o -> out = IStop o.
Proof.
  unfold inst_next. intros c l rest j out d o H.
  destruct out; try discriminate H; [injection H as <-; reflexivity | destruct (call_frame _ _); discriminate H].
Qed.

(** `exit_targets`: a need at a jump means the jump has edges, none of
    them polling (`meet_found`, `ahead_edge/5`). *)
Lemma exit_targets : forall f b n h,
  lookup n (block_exit f b) = Some h ->
  jump_targets (b_jump b) <> [] /\ forall t, In t (jump_targets (b_jump b)) -> is_poll t = false.
Proof.
  intros f b n h H. unfold block_exit, exit_in in H. destruct (meet_found _ _ _ H) as [Hne Hall].
  split.
  - intros E. rewrite E in Hne. exact (Hne eq_refl).
  - intros t Ht. destruct (Hall _ (in_map _ _ _ Ht)) as (h1 & Hh1 & _).
    destruct t; [reflexivity | discriminate Hh1].
Qed.

(** `doomed_step_checked`: a doomed frame's step never ends the run
    `unchecked`. It does not reach a poll edge, a return or an
    instruction that is not transparent, because the need is there
    (`exit_targets`, `step_found`); and a renew, renew over a hull, half
    check or `check_limit` there finds no alias or wrong limit
    (`renew_not_alias`, `hull_not_alias`, `half_not_alias`,
    `check_limit_not_unchecked`). *)
Theorem doomed_step_checked : forall ge md c w,
  checked_module md -> fr_doomed (c_frame c) <> None -> shaped md (c_frame c) ->
  doomed_ok ge md (c_mem c) (c_frame c) -> step ge c <> Done (Unchecked w).
Proof.
  intros ge md c w Hmd Hdm Hsh (Hsc & Hpos & n & pn & kl & hreq & _ & _ & _ & Hneed) E.
  destruct (fr_doomed (c_frame c)) as [why|] eqn:Ed; [|contradiction].
  unfold shaped in Hsh. cbv zeta in Hsh.
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - destruct Hneed.
  - unfold step in E. rewrite Ha in E. destruct (c_fuel c =? 0); [discriminate E|].
    unfold or_stuck in E. destruct (find_block l _); simpl in E; [|discriminate E].
    destruct (phis_env _ _ _ _); simpl in E; discriminate E.
  - unfold step in E. rewrite Ha in E. destruct Hsh as (Hin & Hr & b & k & Hb & Hk & Hnil & Hj).
    destruct Hneed as (b' & h & Hb' & Hh & _). rewrite Hb in Hb'. injection Hb' as <-.
    cbn [facts_from fold_right] in Hh.
    destruct (exit_targets _ _ _ _ Hh) as [Hne Hall]. subst j.
    unfold jump_step in E. rewrite Ed in E.
    destruct (b_jump b) as [t | v t1 t2 | v | vs | | ]; simpl in Hne, Hall; try contradiction.
    + unfold edge_step in E. rewrite Ed in E.
      destruct t; [discriminate E | discriminate (Hall _ (or_introl eq_refl))].
    + unfold or_stuck in E. destruct (value_x _ _ _ _) as [[u | | ]|]; simpl in E; try discriminate E.
      unfold edge_step in E. rewrite Ed in E.
      destruct (u =? 0).
      * destruct t2; [discriminate E | discriminate (Hall _ (or_intror (or_introl eq_refl)))].
      * destruct t1; [discriminate E | discriminate (Hall _ (or_introl eq_refl))].
  - unfold step in E. rewrite Ha, Ed in E. destruct Hsh as (Hin & Hr & b & k & Hb & Hk & Hsk & Hj).
    destruct (skipn_cons _ _ _ _ _ (eq_sym Hsk)) as (Hki & _ & _).
    assert (Hpt0 : point_site (fr_fn (c_frame c)) (fr_at (c_frame c)) = Some (l, Z.of_nat k))
      by (rewrite Ha, Hsk; exact (point_site_exec _ _ _ _ _ Hb Hk)).
    destruct Hneed as (b' & h & Hb' & Hh & _). rewrite Hb in Hb'. injection Hb' as <-.
    rewrite facts_from_cons in Hh. destruct (step_found _ _ _ _ _ _ Hh) as [Ht _].
    rewrite Ht in E. unfold or_stuck in E.
    destruct (inst_step ge (c_frame c) (c_mem c) i) as [out0|] eqn:Hi; simpl in E; [|discriminate E].
    destruct (doomed_result ge (c_frame c) (c_mem c) i out0) as [od|] eqn:Hdr; simpl in E; [|discriminate E].
    destruct (doomed_unchecked _ _ _ _ _ _ _ _ Ed Hdr (inst_next_done _ _ _ _ _ _ _ E)) as [-> Hw].
    destruct (Hpos _ _ _ eq_refl) as (E0 & b1 & out & _ & _ & _ & Hdp).
    assert (Hc : exists live rest' live',
               checked_inst_rest (fn_src md (fr_fn (c_frame c))) i rest live = Some (rest', live')).
    { destruct Hdp as [(live & Hw') | (acc & rest' & live' & Ea & _ & Hacc)].
      - destruct (walks_cons _ _ _ _ _ Hw') as (rest' & live' & Hc & _). eauto.
      - injection Ea as <- _. exfalso.
        destruct (alias_source _ _ _ _ _ Ht Hi Hw)
          as [(q & lo & hi & rs & al & a1 & a2 & -> & _) | [(q & lo & hi & rs & al & a1 & a2 & a3 & -> & _) |
              [(q & bd & lo & hi & rs & al & a1 & a2 & -> & _) | (q & lo & hi & rs & al & a1 & a2 & -> & _)]]];
          destruct Hacc as [Hacc | (r' & cl & args & Hacc)]; try exact (Hacc eq_refl); discriminate Hacc. }
    destruct Hc as (live & rest' & live' & Hc).
    destruct (alias_source _ _ _ _ _ Ht Hi Hw)
      as [(q & lo & hi & rs & al & a1 & a2 & -> & ->) | [(q & lo & hi & rs & al & a1 & a2 & a3 & -> & ->) |
          [(q & bd & lo & hi & rs & al & a1 & a2 & -> & ->) | (q & lo & hi & rs & al & a1 & a2 & -> & ->)]]].
    + destruct a1 as [n1 | c1 | g1]; [|discriminate Hc | discriminate Hc].
      exact (renew_not_alias ge md (c_frame c) (c_mem c) l (Z.of_nat k) Hmd Hin Hr Hsc Hpt0
               b k q lo hi rs al n1 a2 rest live _ Hb Hki eq_refl Hc Hi).
    + destruct a1 as [nl | c1 | g1]; [|discriminate Hc | discriminate Hc].
      destruct a2 as [nh | c2 | g2]; [|discriminate Hc | discriminate Hc].
      exact (hull_not_alias ge md (c_frame c) (c_mem c) l (Z.of_nat k) Hmd Hin Hr Hsc Hpt0
               b k q lo hi rs al nl nh a3 rest live _ Hb Hki eq_refl Hc Hi).
    + destruct a1 as [n1 | c1 | g1]; [|discriminate Hc | discriminate Hc].
      exact (half_not_alias ge md (c_frame c) (c_mem c) l (Z.of_nat k) Hmd Hin Hr Hsc Hpt0
               b k q bd lo hi rs al n1 a2 rest live _ Hb Hki eq_refl Hc Hi).
    + exact (check_limit_not_unchecked ge md (c_frame c) (c_mem c) l (Z.of_nat k) Hmd Hin Hr
               (scope_plain_weak _ _ _ Hsc) Hpt0 b k q lo hi rs al a1 a2 rest live _ WhyLimit Hb Hki eq_refl Hc Hi).
Qed.

(** ## Every step keeps it *)

Module Doom (R : Runtime).

Module P := Persistence R.
Module S := Single R.
Import S.ID.RM.

(** ### Taking an edge *)

(** `doomed_jump`: a doomed frame's jump takes an edge to a later
    block whose entry facts carry the need (`meet_found`): there is one,
    and it does not poll. *)
Lemma doomed_jump : forall ge md c c' l j,
  checked_module md -> fr_at (c_frame c) = Exec l [] j -> step ge c = Next c' ->
  fr_doomed (c_frame c) <> None -> shaped md (c_frame c) ->
  doomed_ok ge md (c_mem c) (c_frame c) -> doomed_ok ge md (c_mem c') (c_frame c').
Proof.
  intros ge md c c' l j Hmd Ha Hs Hdm Hsh (Hsc & _ & n & pn & kl & hreq & Hn & Hkl & Hdmem & Hneed).
  unfold step in Hs. rewrite Ha in Hs.
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh.
  destruct Hsh as (Hin & Hr & b & k & Hb & Hk & Hnil & Hj).
  destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & Hnd & Hdd).
  destruct (find_block_in _ _ _ Hb) as [Hbin Hl]. subst l.
  pose proof (skipn_nil_length _ _ _ (eq_sym Hnil) Hk) as Hkl'.
  destruct (P.I.jump_step_next _ _ _ _ _ Hs) as [(t & Ht & ->) | (Hdn & _)]; [|contradiction].
  simpl. pose proof (P.I.taken_target_in _ _ _ _ Ht) as Htin. rewrite Hj in Htin.
  assert (Hsucc : In (edge_label t) (jump_succs (b_jump b))) by exact (target_succ _ _ Htin).
  split; [|split].
  - intros l' k' n' s i Hpt Hn' Hrp Hpos Hsd. simpl in Hpt. injection Hpt as <- <-.
    pose proof (site_edge _ _ _ _ _ _ _ _ _ Hf Hd Hnd Hb Hr Hsucc Hpos Hsd) as Hsd0.
    refine (replays_weak_moves _ _ _ _ _ _ _ _ (Hsc _ _ _ _ _ _ Hn' Hrp Hpos Hsd0) eq_refl (fun _ _ _ => eq_refl)
              (persists_refl _)).
    rewrite Ha, Hnil, Hkl'. exact (point_site_exec _ _ _ _ _ Hb (le_n _)).
  - intros l' is j' E. discriminate E.
  - rewrite Ha in Hneed. destruct Hneed as (b' & h & Hb' & Hh & Hle).
    rewrite Hb in Hb'. injection Hb' as <-. simpl in Hh.
    unfold block_exit, exit_in in Hh. destruct (meet_found _ _ _ Hh) as [_ Hall].
    destruct (Hall (ahead_edge (map b_label (fn_blocks (fr_fn (c_frame c))))
                      (index_of (b_label b) (map b_label (fn_blocks (fr_fn (c_frame c)))) 0)
                      (ahead_entries (fr_fn (c_frame c))) t) (in_map _ _ _ Htin)) as (h1 & Hh1 & Hle1).
    exists n, pn, kl, hreq. split; [exact Hn|]. split; [exact Hkl|]. split; [exact Hdmem|].
    simpl. destruct t as [l2 | l2]; simpl in Hh1 |- *.
    + destruct (index_of l2 _ 0); [|discriminate Hh1].
      destruct (index_of (b_label b) _ 0); [|discriminate Hh1].
      destruct (lookup l2 (ahead_entries (fr_fn (c_frame c)))) as [fs|] eqn:El; [|discriminate Hh1].
      destruct (_ <? _)%nat; [|discriminate Hh1].
      exists fs, h1. split; [reflexivity|]. split; [exact Hh1 | lia].
    + discriminate Hh1.
Qed.

(** ### An instruction *)

(** `need_access_stops`: the access that meets the need does not
    continue. Its proof q holds a pointer of the base's capability, at
    an exact offset from it (`fact_holds`, `guard_chain_sound`), and its
    bytes end at or past the need, so its check fails
    (`need_access_fails`). *)
Lemma need_access_stops : forall ge md c l i b k n pn kl hreq q x off rs p k' e1 l1 m1,
  checked_module md -> In (IFunc (fr_fn (c_frame c))) md -> is_reachable (fn_doms (fr_fn (c_frame c))) l = true ->
  find_block l (fn_blocks (fr_fn (c_frame c))) = Some b -> nth_error (b_insts b) k = Some i ->
  point_site (fr_fn (c_frame c)) (fr_at (c_frame c)) = Some (l, Z.of_nat k) ->
  objects_fit (m_regions (c_mem c)) -> scope_weak ge (c_frame c) (c_mem c) ->
  lookup n (fr_env (c_frame c)) = Some (WPtr pn) -> near_offset kl = true -> doom_mem (c_mem c) pn kl hreq ->
  raw_access i = Some (q, x, off, rs) ->
  lookup q (proof_pointers (fr_fn (c_frame c)) (single_definitions (fr_fn (c_frame c)))) = Some p ->
  In (Tmp n, (k', k')) (guard_chain (single_definitions (fr_fn (c_frame c))) p) ->
  once_has (single_definitions (fr_fn (c_frame c))) n = true ->
  near_offset (k' + off + fst (access_size_align x)) = true -> hreq <= k' + off + fst (access_size_align x) ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IContinue e1 l1 m1).
Proof.
  intros ge md c l i b k n pn kl hreq q x off rs p k' e1 l1 m1
    Hmd Hin Hr Hb Hki Hpt Hfit Hsc Hn Hkl Hdmem Hra Hq Hch Hon Hkh Hle.
  set (f := fr_fn (c_frame c)) in *.
  destruct (proof_pointers_def _ _ _ Hq) as (iq & fa & Eq & Hcf & Hfq & Hfp).
  assert (Hoq : once_has (single_definitions f) q = true) by (unfold once_has; rewrite Eq; reflexivity).
  assert (Hdq : dominating f l (Z.of_nat k) q)
    by exact (operand_at md (c_frame c) l (Z.of_nat k) Hmd Hin Hr Hpt b k i q Hb Hki eq_refl
                (raw_access_uses _ _ _ _ _ Hra) Hoq).
  assert (Hstp : stable (single_definitions f) p).
  { rewrite guard_chain_eq in Hch. destruct (chain_go_head _ _ _ _ _ _ Hch) as [E | (y & d & o & args & bl & -> & Ey)].
    - injection E as <- _ _. intros y E. injection E as <-. exact Hon.
    - intros y' E. injection E as <-. unfold once_has. rewrite Ey. reflexivity. }
  rewrite <- Hfp in Hstp.
  destruct (fact_holds ge (c_frame c) (c_mem c) l (Z.of_nat k) Hsc Hpt q iq fa Eq Hcf Hfq Hdq Hstp) as (pp & Hqv & Hpv).
  rewrite Hfp in Hpv, Hstp.
  assert (Hdp : forall y, p = Tmp y -> once_has (single_definitions f) y = true -> dominating f l (Z.of_nat k) y).
  { intros y E Ho. apply (operand_dominating _ _ _ _ _ _ _ Hmd Hin Hr Eq Hdq); [|exact Ho].
    apply (check_fact_uses _ _ _ Hcf). rewrite Hfp. exact E. }
  destruct (guard_chain_sound ge md (c_frame c) (c_mem c) l (Z.of_nat k) Hmd Hin Hr (scope_plain_weak _ _ _ Hsc) Hpt
              p pp (Tmp n) k' k' Hpv Hdp Hch ltac:(intros y E; injection E as <-; exact Hon))
    as (pb & xo & Hpb & Hcap & Hxo & Haddr).
  simpl in Hpb. rewrite Hn in Hpb. injection Hpb as <-. assert (xo = k') by lia. subst xo.
  apply (access_trap_stops _ _ _ _ _ _ _ _ _ _ _ _ Hra Hqv).
  intros r al. exact (need_access_fails _ _ _ _ _ _ _ _ r al Hdmem Hfit (eq_sym Hcap) Haddr Hkl Hkh Hle
                        (access_size_small x)).
Qed.

(** `doomed_inst`: a doomed frame's instruction keeps the need, not
    defining its base; the access that would meet it does not continue
    (`need_access_stops`). *)
Lemma doomed_inst : forall ge md c c' l i rest j,
  checked_module md -> fr_at (c_frame c) = Exec l (i :: rest) j -> step ge c = Next c' ->
  fr_doomed (c_frame c) <> None -> persists (c_mem c) (c_mem c') ->
  objects_fit (m_regions (c_mem c)) -> objects_fit (m_regions (c_mem c')) ->
  shaped md (c_frame c) -> doomed_ok ge md (c_mem c) (c_frame c) -> doomed_ok ge md (c_mem c') (c_frame c').
Proof.
  intros ge md c c' l i rest j Hmd Ha Hs Hdm Hp Hfit Hfit' Hsh (Hsc & Hpos & n & pn & kl & hreq & Hn & Hkl & Hdmem & Hneed).
  destruct (step_exec_cons _ _ _ _ _ _ _ Ha Hs ltac:(discriminate) ltac:(discriminate))
    as (_ & out0 & od & Hi & Hdr & Hnx).
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh.
  destruct Hsh as (Hin & Hr & b & k & Hb & Hk & Hsk & Hj).
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hsk)) as (Hki & Hrest & Hlen).
  destruct (find_block_in _ _ _ Hb) as [Hbin Hl].
  destruct (func_facts _ _ Hmd Hin) as (b0 & rs0 & Hf & Hd & _ & Hdd).
  assert (Hpt0 : point_site (fr_fn (c_frame c)) (fr_at (c_frame c)) = Some (l, Z.of_nat k))
    by (rewrite Ha, Hsk; exact (point_site_exec _ _ _ _ _ Hb Hk)).
  assert (Hpt1 : point_site (fr_fn (c_frame c)) (Exec l rest j) = Some (l, Z.of_nat (S k)))
    by (rewrite <- Hrest; exact (point_site_exec _ _ _ _ _ Hb Hlen)).
  rewrite Ha in Hneed. destruct Hneed as (b' & h & Hb' & Hh & Hle). rewrite Hb in Hb'. injection Hb' as <-.
  rewrite facts_from_cons in Hh.
  destruct (step_found _ _ _ _ _ _ Hh) as [Ht [(Hh' & Hnd) | (q & x & off & rs & p & k' & Hra & Hq & Hch & Hon & _ & Hkh & ->)]].
  2: { (* the access that would meet the need stops *)
    exfalso.
    destruct (inst_next_next _ _ _ _ _ _ _ Hnx) as [(e1 & l1 & m1 & Ho & _) | (g & xs & pd & callee & Ho & _ & _)].
    - destruct (doomed_result_cases _ _ _ _ _ _ Hdr)
        as [Eod | [(d & lo & hi & r & al & ahi & v & pv & w & -> & _) | (w & why & -> & _ & Eod)]].
      + rewrite Eod in Ho. simpl in Ho. subst out0.
        exact (need_access_stops ge md c l i b k n pn kl hreq q x off rs p k' e1 l1 m1
                 Hmd Hin Hr Hb Hki Hpt0 Hfit Hsc Hn Hkl Hdmem Hra Hq Hch Hon Hkh Hle Hi).
      + discriminate Hra.
      + rewrite Eod in Ho. discriminate Ho.
    - destruct (doomed_result_cases _ _ _ _ _ _ Hdr)
        as [Eod | [(d & lo & hi & r & al & ahi & v & pv & w & -> & _) | (w & why & -> & _ & Eod)]].
      + rewrite Eod in Ho. simpl in Ho. subst out0.
        destruct (inst_step_call_shape _ _ _ _ _ _ _ Hi) as (_ & [(r & cl & args & ->) | (r & cl & args & ->)]);
          discriminate Hra.
      + discriminate Hra.
      + rewrite Eod in Ho. discriminate Ho. }
  destruct (inst_next_next _ _ _ _ _ _ _ Hnx) as [(e1 & l1 & m1 & Ho & ->) | (g & xs & pd & callee & Ho & _ & _)].
  2: { exfalso.
    destruct (doomed_result_cases _ _ _ _ _ _ Hdr)
      as [Eod | [(d & lo & hi & r & al & ahi & v & pv & w & -> & _ & _ & Eod) | (w & why & -> & _ & Eod)]];
      rewrite Eod in Ho; simpl in Ho; try discriminate Ho. subst out0.
    destruct (inst_step_call_shape _ _ _ _ _ _ _ Hi) as (_ & [(r & cl & args & ->) | (r & cl & args & ->)]);
      discriminate Ht. }
  simpl in Hp, Hfit' |- *.
  (* the pass's position after i *)
  assert (Hpos' : forall l' is j', Exec l rest j = Exec l' is j' ->
     exists E b out, pass_exits (fn_src md (fr_fn (c_frame c))) (fr_fn (c_frame c)) = Some E /\
       find_block l' (fn_blocks (fr_fn (c_frame c))) = Some b /\ lookup l' E = Some out /\
       dpos (fn_src md (fr_fn (c_frame c))) is out).
  { intros l' is j' E. injection E as <- <- <-.
    destruct (Hpos _ _ _ Ha) as (E & b1 & out & HE & Hb1 & Hout & Hdp).
    exists E, b1, out. split; [exact HE|]. split; [exact Hb1|]. split; [exact Hout|].
    destruct Hdp as [(live & Hw) | (access & rest' & live' & Ea & Hw & _)].
    - destruct (walks_cons _ _ _ _ _ Hw) as (rest' & live' & Hc & Hw').
      destruct (pass_after _ _ _ _ _ _ Hc) as [-> | (a & -> & Hacc)]; [left; eauto | right; eauto 6].
    - injection Ea as <- <-. left. eauto. }
  destruct (doomed_result_cases _ _ _ _ _ _ Hdr)
    as [Eod | [(d & lo & hi & r & al & ahi & v & pv & w & -> & -> & Hv & Eod) | (w & why & -> & _ & Eod)]];
    rewrite Eod in Ho |- *; simpl in Ho |- *; try discriminate Ho.
  - (* the instruction's own result *)
    subst out0.
    pose proof (inst_step_env _ _ _ _ _ _ _ Hi) as He.
    split; [|split; [exact Hpos'|]].
    + refine (scope_step_with (replays_weak ge) md (c_frame c) (mkFrame (fr_fn (c_frame c)) e1 l1 _ (Exec l rest j))
                (c_mem c) m1 l b k i (replays_weak_moves ge)
                Hmd Hin eq_refl Hr Hb Hki Hpt0 Hpt1 He Hp _ Hsc).
      intros n' Hrp Hn'. left. exists (c_frame c), (c_mem c), e1, l1, m1.
      split; [exact Hi|]. split; [reflexivity|]. split; [|exact (conj (persists_refl _) Hfit')].
      intros a Hu Ho1. symmetry. apply He.
      rewrite <- Hl in Hr. exact (operand_not_defined _ _ _ _ _ _ _ Hf Hd Hdd Hbin Hr Hki Hu Ho1).
    + exists n, pn, kl, hreq. split; [simpl; rewrite (He _ Hnd); exact Hn|]. split; [exact Hkl|].
      split; [exact (doom_mem_persists _ _ _ _ _ Hdmem Hp)|]. simpl. exists b, h. auto.
  - (* a check_ahead that fails early again: it holds its pointer *)
    injection Ho as <- <- <-.
    destruct (ahead_early _ _ _ _ _ _ _ _ _ _ _ Hi) as (pp & x1 & Hpp & _).
    rewrite Hv in Hpp. injection Hpp as ->.
    assert (He : forall a, ~ In a (map fst (inst_temp_defs (Let d A (CheckAhead lo hi r al ahi) [v]))) ->
                   lookup a (put d (WPtr pp) (fr_env (c_frame c))) = lookup a (fr_env (c_frame c)))
      by (intros a Ha'; apply lookup_put_ne; intros ->; apply Ha'; left; reflexivity).
    split; [|split; [exact Hpos'|]].
    + refine (scope_step_with (replays_weak ge) md (c_frame c)
                (mkFrame (fr_fn (c_frame c)) (put d (WPtr pp) (fr_env (c_frame c))) (fr_locals (c_frame c)) _ (Exec l rest j))
                (c_mem c) (c_mem c) l b k _ (replays_weak_moves ge)
                Hmd Hin eq_refl Hr Hb Hki Hpt0 Hpt1 He Hp _ Hsc).
      intros n' Hrp Hn'.
      pose proof (once_inst_name _ _ _ Hn') as Hnm. simpl in Hnm. destruct Hnm as [<- | []].
      right. exists lo, hi, r, al, ahi, v, (c_frame c), pp. split; [reflexivity|]. split; [exact Hv|].
      split; [apply lookup_put_same|].
      intros a Hu Ho1. symmetry. apply He.
      rewrite <- Hl in Hr. exact (operand_not_defined _ _ _ _ _ _ _ Hf Hd Hdd Hbin Hr Hki Hu Ho1).
    + exists n, pn, kl, hreq. split; [cbn [fr_env]; rewrite (He _ Hnd); exact Hn|]. split; [exact Hkl|].
      split; [exact Hdmem|]. simpl. exists b, h. auto.
Qed.

(** ### The doom *)

(** `doom_start`: a frame that is not doomed is doomed only by a
    `check_ahead` whose early bytes fail. The pass accepted it
    (`checked_inst_rest/4`), so the validator found it at its own site
    (`ahead_accepted`) with some exact base N of its pointer at offset
    K, K and K + Lo near, whose need after the access is at least
    K + Hi. N dominates the check (`chain_dominating`), so the access
    does not define it, and the need before the access is no less
    (`step_keeps`). Its own bytes passed and its early ones failed, so
    the check's start lies in the object and its end does not
    (`doom_from_checks`). *)
Lemma doom_start : forall ge md c c' l i rest j,
  checked_module md -> fr_at (c_frame c) = Exec l (i :: rest) j -> step ge c = Next c' ->
  fr_doomed (c_frame c) = None -> fr_doomed (c_frame c') <> None ->
  objects_fit (m_regions (c_mem c)) -> shaped md (c_frame c) ->
  scope_holds ge (c_frame c) (c_mem c) -> P.I.point_ok ge md (c_mem c) (c_frame c) ->
  doomed_ok ge md (c_mem c') (c_frame c').
Proof.
  intros ge md c c' l i rest j Hmd Ha Hs Hd0 Hd' Hfit Hsh Hsc Hpo.
  destruct (step_exec_cons _ _ _ _ _ _ _ Ha Hs ltac:(discriminate) ltac:(discriminate))
    as (_ & out0 & od & Hi & Hdr & Hnx).
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh.
  destruct Hsh as (Hin & Hr & b & k & Hb & Hk & Hsk & Hj).
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hsk)) as (Hki & Hrest & Hlen).
  destruct (find_block_in _ _ _ Hb) as [Hbin Hl].
  destruct (func_facts _ _ Hmd Hin) as (b0 & rs0 & Hf & Hd & Hnd & Hdd).
  set (f := fr_fn (c_frame c)) in *.
  set (once := single_definitions f) in *.
  assert (Hpt0 : point_site f (fr_at (c_frame c)) = Some (l, Z.of_nat k))
    by (rewrite Ha, Hsk; exact (point_site_exec _ _ _ _ _ Hb Hk)).
  assert (Hpt1 : point_site f (Exec l rest j) = Some (l, Z.of_nat (S k)))
    by (rewrite <- Hrest; exact (point_site_exec _ _ _ _ _ Hb Hlen)).
  (* The step dooms only at a check_ahead that fails early. *)
  destruct (inst_next_next _ _ _ _ _ _ _ Hnx) as [(e1 & l1 & m1 & Ho & ->) | (g & xs & pd & callee & Ho & Hcf & ->)].
  2: { exfalso. simpl in Hd'. destruct (call_frame_entry _ _ _ Hcf) as (_ & Hcd & _). exact (Hd' Hcd). }
  simpl in Hd' |- *.
  destruct (doomed_result_cases _ _ _ _ _ _ Hdr)
    as [Eod | [(d & lo & hi & r & al & ahi & v & pv & w & -> & -> & Hv & Eod) | (w & why & _ & Hw & _)]];
    [rewrite Eod in Hd'; simpl in Hd'; contradiction | | rewrite Hd0 in Hw; discriminate Hw].
  rewrite Eod in Ho. simpl in Ho. injection Ho as <- <- <-. simpl.
  destruct (ahead_early _ _ _ _ _ _ _ _ _ _ _ Hi) as (pp & x1 & Hpp & E1 & Hx1 & E2).
  rewrite Hv in Hpp. injection Hpp as ->.
  (* The pass took the check at the start of one of its steps. *)
  destruct (P.I.point_ok_exec_inv _ _ _ _ _ _ _ Hpo Ha) as (E & b' & out & k' & HE & Hb' & Hout & _ & _ & Hat).
  change (fr_fn (c_frame c)) with f in HE, Hb', Hout, Hat.
  rewrite Hb in Hb'. injection Hb' as <-.
  destruct Hat as [(live & Hw & _ & _) | (access & rest' & live' & Ea & _ & _ & Hpc)].
  2: { exfalso. injection Ea as <- _.
       destruct Hpc as [(fb & pre & Hcov & _) | (_ & r' & q' & args & p' & Eacc & _)];
         [unfold covered_access in Hcov; simpl in Hcov; discriminate Hcov | discriminate Eacc]. }
  destruct (walks_cons _ _ _ _ _ Hw) as (rest' & live' & Hc & Hw').
  cbn beta iota zeta delta [checked_inst_rest] in Hc.
  destruct (mem d (s_ahead (fn_src md f))) eqn:Em; [|discriminate Hc]. simpl in Hc.
  destruct rest as [|access rest2]; [discriminate Hc|].
  destruct (proof_use access d lo ahi r al && ahead_transparent access) eqn:Eu; [|discriminate Hc].
  injection Hc as <- _. apply andb_true_iff in Eu as [Hpu Hta].
  destruct (skipn_cons _ _ _ _ _ Hrest) as (Hka & Hrest2 & _).
  (* The validator accepted it here. *)
  apply mem_in in Em. unfold fn_src, stage_sources in Em. simpl in Em.
  destruct (ahead_accepted _ _ Hnd Em) as (b2 & k2 & i2 & Hb2 & Hk2 & _ & Hacc).
  change (fr_fn (c_frame c)) with f in Hb2, Hk2, Hacc. change (single_definitions f) with once in Hacc.
  unfold ahead_accepts in Hacc.
  destruct i2 as [q2 c2 o2 args2 | | | | | | |]; try discriminate Hacc.
  destruct c2; try discriminate Hacc. destruct o2; try discriminate Hacc.
  destruct args2 as [|p2 [|p3 args2]]; try discriminate Hacc.
  match type of Hacc with context [if ?cond then _ else _] => destruct cond eqn:Ex end;
    [|discriminate Hacc]. injection Hacc as ->.
  apply andb_true_iff in Ex as [Hod Hex].
  assert (Hsame : b2 = b /\ k2 = k /\ Let d A (CheckAhead lo0 hi0 r0 align ahi0) [p2] = Let d A (CheckAhead lo hi r al ahi) [v]).
  { unfold once_has in Hod. destruct (lookup d once) as [D|] eqn:ED; [|discriminate Hod].
    destruct (once_position _ _ _ ED) as (s0 & _ & Hu).
    pose proof (inst_position f b k _ (d, A) Hbin Hki (or_introl eq_refl)) as P1.
    pose proof (inst_position f b2 k2 _ (d, A) Hb2 Hk2 (or_introl eq_refl)) as P2.
    destruct (Hu _ _ P1) as [S1 D1]. destruct (Hu _ _ P2) as [S2 D2].
    rewrite <- S2 in S1. injection S1 as El Ek. rewrite <- D2 in D1.
    assert (k2 = k) by lia. subst k2.
    assert (b2 = b) by exact (find_block_unique _ _ _ _ Hnd Hb Hb2 (eq_trans (eq_sym El) Hl)). subst b2.
    split; [reflexivity|]. split; [reflexivity|]. congruence. }
  destruct Hsame as (-> & -> & Ei). injection Ei as -> -> -> -> -> ->.
  rewrite Hrest2 in Hex.
  apply existsb_exists in Hex as (e & He & Hee).
  destruct (exact_base once e) as [[n K]|] eqn:Eb; [|discriminate Hee].
  destruct (lookup n (facts_from f rest2 (block_exit f b))) as [h|] eqn:Eh;
    [|rewrite andb_false_r in Hee; discriminate Hee].
  repeat rewrite andb_true_iff in Hee. destruct Hee as ((HK & HKl) & Hle). apply Z.leb_le in Hle.
  unfold exact_base in Eb. destruct e as [[n0 | c0 | g0] [K1 K2]]; try discriminate Eb.
  destruct ((K1 =? K2) && once_has once n0) eqn:EK; [|discriminate Eb]. injection Eb as -> ->.
  apply andb_true_iff in EK as [EK Hon]. apply Z.eqb_eq in EK. subst K2.
  (* N dominates the check, and holds a pointer of the check's capability at K before it. *)
  assert (Hdv : forall y, v = Tmp y -> once_has once y = true -> dominating f l (Z.of_nat k) y)
    by (intros y -> Ho; exact (operand_at md (c_frame c) l (Z.of_nat k) Hmd Hin Hr Hpt0 b k _ y Hb Hki eq_refl
                                 ltac:(simpl; auto) Ho)).
  assert (Hdn : dominating f l (Z.of_nat k) n)
    by (rewrite guard_chain_eq in He; exact (chain_dominating md f l (Z.of_nat k) 64 v 0 0 n K K Hmd Hin Hr Hdv He Hon)).
  destruct (guard_chain_sound ge md (c_frame c) (c_mem c) l (Z.of_nat k) Hmd Hin Hr (scope_plain_of _ _ _ Hsc) Hpt0
              v pp (Tmp n) K K Hv Hdv He ltac:(intros y E'; injection E' as <-; exact Hon))
    as (pn & xo & Hpn & Hcap & Hxo & Haddr).
  assert (xo = K) by lia. subst xo. simpl in Hpn.
  assert (Hpn' : lookup n (fr_env (c_frame c)) = Some (WPtr pn))
    by (destruct (lookup n (fr_env (c_frame c))); [exact Hpn | discriminate Hpn]).
  (* Neither the check nor its access defines N. *)
  destruct Hdn as (sn & Dn & ESn & Hposn & Hsdn).
  destruct (once_position _ _ _ ESn) as (sn' & _ & Hun).
  assert (Hnot : forall kk ik, nth_error (b_insts b) kk = Some ik -> (k <= kk)%nat ->
                   ~ In n (map fst (inst_temp_defs ik))).
  { intros kk ik Hkk Hle' Hni. apply in_map_iff in Hni as ([n' kc] & En & Hdk). simpl in En. subst n'.
    pose proof (inst_position f b kk ik (n, kc) Hbin Hkk Hdk) as Pn.
    destruct (Hun _ _ Hposn) as [Sn _]. destruct (Hun _ _ Pn) as [Sk _]. rewrite <- Sk in Sn. subst sn.
    rewrite Hl in Hsdn. simpl in Hsdn. rewrite name_eqb_refl in Hsdn. apply Z.ltb_lt in Hsdn. lia. }
  assert (Hnd' : n <> d) by (intros ->; exact (Hnot k _ Hki (le_n _) (or_introl eq_refl))).
  (* The memory the doom leaves. *)
  destruct (doom_from_checks _ _ _ _ _ _ _ _ _ E1 Hx1 E2) as (base & reg & Hc & Hreg & Hbase & Hin_end & Hout_end).
  destruct (ahead_ok _ _ _ _ _ _ _ _ _ _ Hmd Hin Hbin (nth_error_In _ _ Hki)) as [Hla Hah].
  destruct (Hfit _ _ Hreg) as [_ H48].
  assert (Hraw : raw_address (ptr_addr pp) lo = raw_address (ptr_addr pn) (K + lo))
    by (unfold raw_address; rewrite <- Z.add_mod_idemp_l, Haddr, Z.add_mod_idemp_l by lia; f_equal; lia).
  assert (He1 : forall a, ~ In a (map fst (inst_temp_defs (Let d A (CheckAhead lo hi r al ahi) [v]))) ->
                  lookup a (put d (WPtr pp) (fr_env (c_frame c))) = lookup a (fr_env (c_frame c)))
    by (intros a Ha'; apply lookup_put_ne; intros ->; apply Ha'; left; reflexivity).
  split; [|split].
  - refine (scope_step_with (replays_weak ge) md (c_frame c)
              (mkFrame f (put d (WPtr pp) (fr_env (c_frame c))) (fr_locals (c_frame c)) _ (Exec l (access :: rest2) j))
              (c_mem c) (c_mem c) l b k _ (replays_weak_moves ge)
              Hmd Hin eq_refl Hr Hb Hki Hpt0 Hpt1 He1 (persists_refl _) _ (scope_weak_of _ _ _ Hsc)).
    intros n' Hrp Hn'.
    pose proof (once_inst_name _ _ _ Hn') as Hnm. simpl in Hnm. destruct Hnm as [<- | []].
    right. exists lo, hi, r, al, ahi, v, (c_frame c), pp. split; [reflexivity|]. split; [exact Hv|].
    split; [apply lookup_put_same|].
    intros a Hu Ho1. symmetry. apply He1.
    rewrite <- Hl in Hr. exact (operand_not_defined _ _ _ _ _ _ _ Hf Hd Hdd Hbin Hr Hki Hu Ho1).
  - intros l' is j' Ex. injection Ex as <- <- <-.
    exists E, b, out. split; [exact HE|]. split; [exact Hb|]. split; [exact Hout|].
    right. exists access, rest2, live'. split; [reflexivity|]. split; [exact Hw'|]. left.
    apply andb_true_iff in Hpu as [Hcov _]. unfold covered_access in Hcov. intros Er. rewrite Er in Hcov. discriminate Hcov.
  - destruct (step_keeps once (proof_pointers f once) access _ n h Hta (Hnot (S k) _ Hka (le_S _ _ (le_n _))) Eh)
      as (h' & Hh' & Hhh').
    exists n, pn, (K + lo), (K + hi). cbn [fr_env fr_at].
    split; [rewrite He1 by (simpl; intros [E' | []]; exact (Hnd' (eq_sym E'))); exact Hpn'|].
    split; [exact HKl|].
    split.
    + exists base, reg. split; [rewrite Hcap; exact Hc|]. split; [exact Hreg|].
      rewrite <- Hraw. split; [lia|]. split; [lia|]. replace (K + hi - (K + lo)) with (hi - lo) by lia. exact Hout_end.
    + exists b, h'. split; [exact Hb|]. split; [rewrite facts_from_cons; exact Hh' | lia].
Qed.

(** ### Every step *)

(** A doomed frame allocates nothing: an allocation is not transparent. *)
Lemma doomed_not_fresh : forall ge md c q k,
  fr_doomed (c_frame c) <> None -> doomed_ok ge md (c_mem c) (c_frame c) -> step ge c <> Fresh q k.
Proof.
  intros ge md c q k Hdm (_ & _ & n & pn & kl & hreq & _ & _ & _ & Hneed) Hs.
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - destruct Hneed.
  - exact (step_enter_fresh _ _ _ _ _ _ Ha Hs).
  - unfold step in Hs. rewrite Ha in Hs. exact (jump_step_not_fresh _ _ _ _ _ _ Hs).
  - destruct (step_exec_cons _ _ _ _ _ _ _ Ha Hs ltac:(discriminate) ltac:(discriminate))
      as ([Hd | Ht] & out0 & od & Hi & Hdr & Hnx); [contradiction|].
    destruct (inst_next_fresh _ _ _ _ _ _ _ _ Hnx) as (k0 & Ho & _).
    destruct (doomed_result_cases _ _ _ _ _ _ Hdr)
      as [Eod | [(d & lo & hi & r & al & ahi & v & pv & w & -> & _ & _ & Eod) | (w & why & -> & _ & Eod)]];
      rewrite Eod in Ho; simpl in Ho; try discriminate Ho. subst out0.
    destruct (inst_step_fresh_shape _ _ _ _ _ _ Hi) as [(d & cl & al & args & -> & _) | (x & size & -> & _)];
      [destruct cl|]; discriminate Ht.
Qed.

(** `next_dinv`: a step that allocates nothing keeps `dinv`. *)
Lemma next_dinv : forall ge md c c' s,
  checked_module md -> step ge c = Next c' -> persists (c_mem c) (c_mem c') ->
  objects_fit (m_regions (c_mem c)) -> objects_fit (m_regions (c_mem c')) ->
  sinv ge md c -> P.I.inv ge md (c, s) -> dinv ge md c -> dinv ge md c'.
Proof.
  intros ge md c c' s Hmd Hs Hp Hfit Hfit' [[Hsh Hsc] Hcall] [(_ & _ & Hpo) _] Hdi Hd'.
  destruct (fr_doomed (c_frame c)) as [w|] eqn:Ed.
  - assert (Hdm : fr_doomed (c_frame c) <> None) by (rewrite Ed; discriminate).
    specialize (Hdi Hdm).
    destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
    + destruct Hdi as (_ & _ & n & pn & kl & hreq & _ & _ & _ & Hneed). rewrite Ha in Hneed. destruct Hneed.
    + exact (doomed_enter _ _ _ _ _ _ Hmd Ha Hs Hsh Hdi).
    + exact (doomed_jump _ _ _ _ _ _ Hmd Ha Hs Hdm Hsh Hdi).
    + exact (doomed_inst _ _ _ _ _ _ _ _ Hmd Ha Hs Hdm Hp Hfit Hfit' Hsh Hdi).
  - destruct Hsc as [Hsc | Hsc]; [contradiction|]. destruct Hpo as [Hpo | Hpo]; [contradiction|].
    destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
    + destruct (step_snapshot _ _ _ _ _ Ha Hs) as (_ & _ & _ & Hd & _). rewrite Hd, Ed in Hd'. contradiction.
    + destruct (step_enter _ _ _ _ _ Ha Hs) as (b & e & _ & _ & ->). simpl in Hd'. contradiction.
    + unfold step in Hs. rewrite Ha in Hs.
      destruct (P.I.jump_step_next _ _ _ _ _ Hs) as [(t & _ & ->) | (_ & o & Hret)]; [simpl in Hd'; contradiction|].
      destruct (return_step_env _ _ _ Hret) as (caller & pd & callers & o' & e & Hcs & _ & Ec).
      rewrite Ec in Hd'. simpl in Hd'.
      rewrite Hcs in Hcall. inversion Hcall as [|fp fps (_ & Hdc & _) _]; subst. simpl in Hdc. contradiction.
    + exact (doom_start _ _ _ _ _ _ _ _ Hmd Ha Hs Ed Hd' Hfit Hsh Hsc Hpo).
Qed.

(** `mstep_dinv`: every machine step from a ready state keeps `dinv`,
    where Single.v's and Persistence.v's invariants hold. *)
Theorem mstep_dinv : forall ge md st st',
  checked_module md -> ge_free ge = R.free -> free_ids R.free ->
  ready_state st -> mstep ge st st' -> sinv ge md (fst st) -> P.I.inv ge md st ->
  dinv ge md (fst st) -> dinv ge md (fst st').
Proof.
  intros ge md st st' Hmd Hfree Hfi Hr Hs Hsi Hi Hdi.
  pose proof (S.ID.mstep_persists _ _ _ Hfree Hfi Hr Hs) as Hp.
  pose proof (R.address_space _ _ Hr) as Hfit.
  pose proof (R.address_space _ _ (mstep_ready _ _ _ Hfree Hs Hr)) as Hfit'.
  destruct Hs as [c c' s E | c q k s base s' E He Hal | c s s' m' Hd Hact]; simpl in *.
  - exact (next_dinv _ _ _ _ s Hmd E Hp Hfit Hfit' Hsi Hi Hdi).
  - intros Hd'. destruct (fr_doomed (c_frame c)) as [w|] eqn:Ed.
    + exfalso. assert (Hdm : fr_doomed (c_frame c) <> None) by (rewrite Ed; discriminate).
      exact (doomed_not_fresh _ _ _ _ _ Hdm (Hdi Hdm) E).
    + exfalso. destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
      * destruct (step_snapshot_fresh _ _ _ _ _ _ Ha E base) as (_ & _ & _ & Hdk & _). rewrite Hdk, Ed in Hd'. contradiction.
      * exact (step_enter_fresh _ _ _ _ _ _ Ha E).
      * unfold step in E. rewrite Ha in E. exact (jump_step_not_fresh _ _ _ _ _ _ E).
      * destruct (step_exec_cons _ _ _ _ _ _ _ Ha E ltac:(discriminate) ltac:(discriminate))
          as (_ & out0 & od & Hi' & Hdr & Hnx).
        destruct (inst_next_fresh _ _ _ _ _ _ _ _ Hnx) as (k0 & Ho & Hk).
        rewrite Hk in Hd'. destruct (k0 base) as [[e locals] m1]. simpl in Hd'.
        destruct (doomed_result_cases _ _ _ _ _ _ Hdr)
          as [Eod | [(d & lo & hi & r & al & ahi & v & pv & w & -> & _ & _ & Eod) | (w & why & -> & _ & Eod)]];
          rewrite Eod in Ho, Hd'; simpl in Ho, Hd'; try discriminate Ho; rewrite Ed in Hd'; contradiction.
  - intros Hd'. exact (doomed_mem _ _ _ _ _ Hp (Hdi Hd')).
Qed.

(** ### Along a run *)

(** Persistence.v's invariant and Single.v's each instantiate
    `Machine R` on their own, so a step of one is carried over to the
    other (as Chain.v's `Hull.mstep_same` does). *)
Lemma mstep_same : forall ge st st', P.I.RM.mstep ge st st' -> S.ID.RM.mstep ge st st'.
Proof. intros ge st st' H. destruct H; econstructor; eassumption. Qed.

(** `run_inv`: the three invariants together, single definitions
    (`sinv`), the pass's facts (`P.I.inv`) and the doomed frame's need
    (`dinv`), hold in every state a ready run reaches. *)
Lemma run_inv : forall ge md st st',
  ge_module ge = md -> checked_module md -> ge_free ge = R.free -> P.I.spares ge md -> free_ids R.free ->
  P.I.RM.mreachable ge st st' -> ready_state st ->
  sinv ge md (fst st) -> P.I.inv ge md st -> dinv ge md (fst st) ->
  sinv ge md (fst st') /\ P.I.inv ge md st' /\ dinv ge md (fst st').
Proof.
  intros ge md st st' Hge Hmd Hfree Hsp Hfi H.
  induction H as [st st' Hs | st | st1 st2 st3 H12 IH1 H23 IH2]; intros Hr Hsi Hi Hdi.
  - pose proof (mstep_same _ _ _ Hs) as Hs'.
    split; [exact (S.mstep_sinv _ _ _ _ Hge Hmd Hfree Hfi Hr Hs' Hsi)|].
    split; [exact (P.mstep_inv _ _ _ _ Hge Hmd Hsp Hr Hs Hi)|].
    subst md. exact (mstep_dinv _ _ _ _ Hmd Hfree Hfi Hr Hs' Hsi Hi Hdi).
  - auto.
  - destruct (IH1 Hr Hsi Hi Hdi) as (Hsi2 & Hi2 & Hdi2).
    exact (IH2 (P.I.RM.mreachable_ready _ _ _ Hfree H12 Hr) Hsi2 Hi2 Hdi2).
Qed.

(** `run_doomed_checked`: in every state of a run of a checked
    module's function that starts ready, a doomed frame never steps to
    an `unchecked` outcome, where the runtime spares the pass's facts at
    safepoints (`spares`) and its free keeps identities (`free_ids`). *)
Theorem run_doomed_checked : forall ge md f xs fr m fuel s0 c s w,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free -> P.I.spares ge md -> free_ids R.free ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) <> None -> step ge c <> Done (Unchecked w).
Proof.
  intros ge md f xs fr m fuel s0 c s w Hmd Hge Hfree Hsp Hfi Hin Hcf H0 Hreach Hd.
  destruct (run_inv _ _ _ _ Hge Hmd Hfree Hsp Hfi Hreach H0
              (S.start_sinv ge md f xs fr m fuel Hmd Hin Hcf)
              (P.start_inv ge md f xs fr m fuel s0 Hmd Hin Hcf)
              ltac:(intros Hd0; simpl in Hd0; destruct (call_frame_entry _ _ _ Hcf) as (_ & Hn & _); contradiction))
    as ([[Hsh _] _] & _ & Hdi).
  exact (doomed_step_checked ge md c w Hmd Hd Hsh (Hdi Hd)).
Qed.

End Doom.

(** ## The interpreter's runtime *)

Module InterpDoom := Doom InterpRuntime.

(** `interp_doomed_checked`: under the interpreter's runtime, in every
    state of a run of a checked module's function that starts ready, a
    doomed frame never steps to `unchecked`. *)
Corollary interp_doomed_checked : forall md globals f xs fr m fuel s0 c s w,
  let ge := mkGenv md globals InterpRuntime.free in
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpDoom.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) <> None -> step ge c <> Done (Unchecked w).
Proof.
  intros md globals f xs fr m fuel s0 c s w ge Hmd Hin Hcf H0 Hreach Hd.
  exact (InterpDoom.run_doomed_checked ge md f xs fr m fuel s0 c s w
           Hmd eq_refl eq_refl (interp_spares ge md) free_res_ids Hin Hcf H0 Hreach Hd).
Qed.
