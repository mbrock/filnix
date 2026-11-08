(** Campaign 3's [[evidence]] invariant, at one instruction
    (docs/formal.md, Campaign 3, Proof persistence;
    [docs/rocq.md, The evidence invariant, instruction by instruction](../../docs/rocq.md#the-evidence-invariant-instruction-by-instruction)).

    ir.pl's [[evidence pass]] (`checked_inst_rest/7`, Validate.v's
    [checked_inst_rest]) keeps a list of [[live facts]] as it walks a
    block: a fact `live(Q, P, Lo, Hi, Rights, Align)` is added where a
    check `let(Q, a, check(Lo, Hi, Rights, Align), [P])` passes, and a
    raw access through Q is accepted where a live fact of Q covers it
    (`covered_access/6`). This file says what a fact means at run time
    ([fact_holds]) and proves that the pass's bookkeeping keeps it true
    across one instruction or one edge. A check reads only the regions
    of memory, so a step that changes no region keeps it passing; and the
    facts the pass drops at a definition (`evidence_kill/3`) are exactly
    those whose Q or P it redefines.

    Persistence.v carries this along the runs of [Machine] R. A
    `check_ahead` whose wider check failed dooms its frame ([[doomed]]),
    and its fact then does not hold; that, and the [[reuse]] forms' own
    rules (that a renew finds its bounds, and `hull_covered/7`), are
    Campaign 3's corollaries. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine Validate Coverage.
Import ListNotations.
Open Scope Z_scope.

(** ## Names *)

(** Looking up the name k right after putting the value v for it gives
    v. *)
Lemma lookup_put_same : forall (A : Type) k (v : A) ps, lookup k (put k v ps) = Some v.
Proof. intros A k v ps. simpl. unfold name_eqb. rewrite term_eqb_refl. reflexivity. Qed.

(** Putting a value for the name d leaves the value of every other name
    k. *)
Lemma lookup_put_other : forall (A : Type) k d (v : A) ps,
  name_eqb k d = false -> lookup k (put d v ps) = lookup k ps.
Proof.
  intros A k d v ps H. simpl. rewrite H. induction ps as [|[k' v'] ps IH]; simpl; auto.
  destruct (name_eqb d k') eqn:E; simpl.
  - apply term_eqb_eq in E. subst k'. rewrite H. exact IH.
  - destruct (name_eqb k k'); auto.
Qed.

(** ## What a fact means *)

(** The environment e' gives every name but d what the environment e
    gives it, as after a step that defines only d. *)
Definition env_agree (d : name) (e e' : env) : Prop :=
  forall n, name_eqb n d = false -> lookup n e' = lookup n e.

(** The [[live fact]] fa, `live(Q, P, Lo, Hi, Rights, Align)`, holds in
    memory m and environment e: the [[temporary]] Q holds a pointer
    word, P evaluates to the same word (a check yields its operand), and
    the [[access]] check of that pointer from Lo up to Hi passes in m
    ([check_passes]). *)
Definition fact_holds (ge : genv) (m : Memory.mem) (e : env) (fa : fact) : Prop :=
  exists p,
    lookup (f_q fa) e = Some (WPtr p) /\
    value_x ge e P (f_p fa) = Some (WPtr p) /\
    check_passes m p (f_lo fa) (f_hi fa) (f_r fa) (f_al fa).

(** Every fact of the list fs holds. *)
Definition facts_hold (ge : genv) (m : Memory.mem) (e : env) (fs : list fact) : Prop :=
  forall fa, In fa fs -> fact_holds ge m e fa.

(** A check reads only the [[region]] list, so one that passes in m
    passes in any memory m' with the same regions. *)
Lemma check_passes_regions : forall m m' p lo hi r al,
  m_regions m' = m_regions m -> check_passes m p lo hi r al -> check_passes m' p lo hi r al.
Proof. unfold check_passes, access_res. intros m m' p lo hi r al E H. rewrite E. exact H. Qed.

(** A fact that names neither d as its Q nor the temporary d (`tmp(d)`)
    as its P survives a step that changes no region and no temporary
    but d ([env_agree]). *)
Lemma fact_holds_kill : forall ge m m' e e' d fa,
  m_regions m' = m_regions m -> env_agree d e e' ->
  name_eqb (f_q fa) d = false -> value_eqb (f_p fa) (Tmp d) = false ->
  fact_holds ge m e fa -> fact_holds ge m' e' fa.
Proof.
  intros ge m m' e e' d fa Hr He Hq Hp (p & Eq & Ep & Hc). exists p. split; [|split].
  - rewrite He by exact Hq. exact Eq.
  - destruct (f_p fa) as [n | c | g]; simpl in *; auto. rewrite He by exact Hp. exact Ep.
  - eapply check_passes_regions; eauto.
Qed.

(** So the facts the pass keeps when d is defined, those [kill] d
    leaves (`evidence_kill/3`), hold after such a step. *)
Lemma facts_hold_kill : forall ge m m' e e' d fs,
  m_regions m' = m_regions m -> env_agree d e e' ->
  facts_hold ge m e fs -> facts_hold ge m' e' (kill d fs).
Proof.
  unfold kill. intros ge m m' e e' d fs Hr He H fa Hin.
  apply filter_In in Hin as [Hin Hk]. apply negb_true_iff, orb_false_iff in Hk as [Hq Hp].
  eapply fact_holds_kill; eauto.
Qed.

(** Facts that hold in m hold in any memory with the same regions. *)
Lemma facts_hold_same : forall ge m m' e fs,
  m_regions m' = m_regions m -> facts_hold ge m e fs -> facts_hold ge m' e fs.
Proof.
  intros ge m m' e fs Hr H fa Hin. destruct (H fa Hin) as (p & Eq & Ep & Hc).
  exists p. repeat split; auto. eapply check_passes_regions; eauto.
Qed.

(** ## Steps that keep evidence *)

(** A store ([store_res], `store_res/7`) writes bytes but leaves the
    region list unchanged. *)
Lemma store_res_regions : forall w m a c x r m',
  store_res w m a c x = Some (r, m') -> m_regions m' = m_regions m.
Proof.
  unfold store_res. intros w m a c x r m' H.
  destruct w, x; try discriminate; cases H; inversion H; subst; reflexivity.
Qed.

(** Reading a variadic argument through the argument pointer p
    ([va_arg_res]) leaves the region list unchanged, though it may write
    memory. *)
Lemma va_arg_res_regions : forall k p m r m',
  va_arg_res k p m = Some (r, m') -> m_regions m' = m_regions m.
Proof.
  unfold va_arg_res. intros k p m r m' H. cases H;
    match type of H with Some (_, ?x) = Some (_, ?y) => assert (x = y) as <- by congruence end;
    first [ reflexivity
          | match goal with E : store_res _ _ _ _ _ = Some _ |- _ => exact (store_res_regions _ _ _ _ _ _ _ E) end ].
Qed.

(** No op with a result ([op_res] returning [OpRes]) changes a region:
    only alloc, free and the end of an invocation do. *)
Lemma op_res_regions : forall o k xs m r m',
  op_res o k xs m = Some (OpRes r m') -> m_regions m' = m_regions m.
Proof.
  unfold op_res, float_integer. intros o k xs m r m' H.
  destruct o; cases H; inversion H; subst;
    first [ reflexivity
          | match goal with E : op_res_int _ _ _ _ = Some _ |- _ =>
              rewrite (op_res_int_mem _ _ _ _ _ _ E); reflexivity end
          | match goal with E : va_arg_res _ _ _ = Some ?rm |- _ =>
              destruct rm; exact (va_arg_res_regions _ _ _ _ _ E) end ].
Qed.

(** Binding the result r to the name d ([bind_res]) continues only with
    a value x: the environment gains d bound to x, and memory is
    unchanged. *)
Lemma bind_res_continue : forall d r e l m e' l' m',
  bind_res d r e l m = IContinue e' l' m' -> exists x, r = RVal x /\ e' = put d x e /\ m' = m.
Proof. unfold bind_res. intros d r e l m e' l' m' H. destruct r; inversion H; subst; eauto. Qed.

(** Putting a value for d changes no other name. *)
Lemma env_agree_put : forall d x e, env_agree d e (put d x e).
Proof. intros d x e n H. apply lookup_put_other. exact H. Qed.

(** An [[evidence]]-preserving instruction i (`evidence_preserving/1`)
    that continues changes no region, and no temporary but the one it
    defines ([inst_def_first]); one that defines none leaves the
    environment as it was. *)
Lemma preserving_step : forall ge fr m i e' l' m',
  evidence_preserving i = true ->
  inst_step ge fr m i = Some (IContinue e' l' m') ->
  m_regions m' = m_regions m /\
  match inst_def_first i with
  | Some d => env_agree d (fr_env fr) e'
  | None => e' = fr_env fr
  end.
Proof.
  intros ge fr m i e' l' m' Hp H. destruct i; simpl in Hp; try discriminate Hp.
  - (* let *)
    destruct (special_let o) eqn:Es.
    + destruct o; try discriminate Es; destruct k; discriminate Hp.
    + rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H. simpl.
      cbn zeta in H. cases H. injection H as Hb.
      destruct (bind_res_continue _ _ _ _ _ _ _ _ Hb) as (x & -> & -> & ->).
      split; [eapply op_res_regions; eauto | apply env_agree_put].
  - (* flight *)
    simpl in H. cases H. injection H as <- <- <-. split; [reflexivity | apply env_agree_put].
  - (* raw_store, not of a pointer *)
    simpl in H. cases H. injection H as Hs.
    destruct (raw_res _) eqn:Er in Hs; inversion Hs; subst.
    split; [eapply store_res_regions; eauto | reflexivity].
  - (* loc *)
    simpl in H. injection H as <- <- <-. simpl. auto.
Qed.

(** ## The pass's bookkeeping *)

(** Where the facts fs hold before the instruction i of the frame fr
    and i continues, the facts `evidence_after/3` keeps after it hold: a
    preserving instruction kills what it redefines, any other keeps
    nothing. The pass's kill is exactly what the proof needs. *)
Theorem evidence_after_holds : forall ge fr m i e' l' m' fs,
  facts_hold ge m (fr_env fr) fs ->
  inst_step ge fr m i = Some (IContinue e' l' m') ->
  facts_hold ge m' e' (evidence_after i fs).
Proof.
  unfold evidence_after. intros ge fr m i e' l' m' fs H Hs.
  destruct (evidence_preserving i) eqn:Hp; [|intros fa []].
  destruct (preserving_step _ _ _ _ _ _ _ Hp Hs) as [Hr Hd].
  destruct (inst_def_first i) as [d|].
  - eapply facts_hold_kill; eauto.
  - subst e'. eapply facts_hold_same; eauto.
Qed.

(** ## Accesses through a live fact *)

(** The newest live fact of q ([fact_of]) is one of the facts, and is
    q's. *)
Lemma fact_of_in : forall q fs fa, fact_of q fs = Some fa -> In fa fs /\ f_q fa = q.
Proof.
  intros q fs fa. induction fs as [|f fs IH]; simpl; [discriminate|].
  destruct (name_eqb (f_q f) q) eqn:E.
  - intros H. injection H as <-. split; [left; reflexivity | apply term_eqb_eq; exact E].
  - intros H. destruct (IH H). split; [right|]; auto.
Qed.

(** Where objects fit the address space ([objects_fit]) and the facts fs
    hold, a raw access i that the newest live fact fa of its address
    operand q covers ([covered_access]), as the pass's reusing case
    asks, gives no [[unchecked]]. With [evidence_after_holds] and
    [check_like_holds] this is proof persistence within a block. *)
Theorem live_access_not_unchecked : forall ge fr m i q fs fa why,
  objects_fit (m_regions m) ->
  facts_hold ge m (fr_env fr) fs ->
  fact_of q fs = Some fa ->
  covered_access i q (f_lo fa) (f_hi fa) (f_r fa) (f_al fa) = true ->
  inst_step ge fr m i <> Some (IStop (Unchecked why)).
Proof.
  intros ge fr m i q fs fa why Hfit H Hf Hc.
  destruct (fact_of_in _ _ _ Hf) as [Hin Hq].
  destruct (H fa Hin) as (p & Eq & _ & Hp). rewrite Hq in Eq.
  exact (covered_access_not_unchecked _ _ _ _ _ _ _ _ _ _ _ Hfit Hc Eq Hp).
Qed.

(** A fact that holds, put before a list of facts that hold. *)
Lemma facts_hold_cons : forall ge m e fa fs,
  fact_holds ge m e fa -> facts_hold ge m e fs -> facts_hold ge m e (fa :: fs).
Proof. intros ge m e fa fs H Hs fb [<- | Hin]; auto. Qed.

(** ## Every form the pass adds a fact for

    Each check-like op, `check`, `check_ahead`, `renew`, `renew_hull`,
    `half_check`, `renew_if` and `check_limit`, continues only where
    the access check of its pointer operand passed: a renew's
    `renew_res/4`, a half check's `half_res/4` and a limit's checked
    result are values only then. So the fact the pass adds after any of
    them (`after_check`) holds, and so does the wider range a
    `check_ahead` asks of the access it is checked for. *)

(** The fact `checked_inst_rest/7` adds after the check-like instruction
    i, `live(Q, P, Lo, Hi, Rights, Align)`, read off its op and its
    pointer operand P; None for any other instruction. *)
Definition check_fact (i : inst) : option fact :=
  match i with
  | Let q A (Check lo hi r al) [p]
  | Let q A (CheckAhead lo hi r al _) [p]
  | Let q A (Renew lo hi r al) [_; p]
  | Let q A (RenewHull lo hi r al) [_; _; p]
  | Let q A (HalfCheck _ lo hi r al) [_; p]
  | Let q A (RenewIf lo hi r al) [p; _]
  | Let q A (CheckLimit lo hi r al) [p; _] => Some (mkFact q p lo hi r al)
  | _ => None
  end.

(** The range the access after the check-like instruction i must lie in
    (`proof_use/6`): its fact's, except that a [[check_ahead]]'s reaches
    to its wider end AHi. *)
Definition access_fact (i : inst) : option fact :=
  match i with
  | Let q A (CheckAhead lo _ r al ahi) [p] => Some (mkFact q p lo ahi r al)
  | _ => check_fact i
  end.

(** Where P evaluates to the pointer pp in e ([value_x]), it still does
    once Q is bound to pp too, even if P is the temporary Q itself. *)
Lemma value_x_put_same : forall ge e q p pp,
  value_x ge e P p = Some (WPtr pp) -> value_x ge (put q (WPtr pp) e) P p = Some (WPtr pp).
Proof.
  intros ge e q p pp Ex. destruct p as [n | c | g]; [|exact Ex|exact Ex].
  unfold value_x in *. destruct (name_eqb n q) eqn:E.
  - apply term_eqb_eq in E. subst n. rewrite lookup_put_same.
    destruct (lookup q e) as [w|]; simpl in Ex; [|discriminate Ex]. reflexivity.
  - rewrite lookup_put_other by exact E. exact Ex.
Qed.

(** Splits on every match a hypothesis is stuck on, and uses every
    equation between constructors: the case analysis behind
    [check_like_continue] and [let_step]. *)
Ltac crush :=
  repeat (match goal with
          | H : ?x = ?x |- _ => clear H
          | H : _ = _ |- _ => injection H; clear H; intros; subst
          | H : _ |- _ =>
              match type of H with
              | context [match ?x with _ => _ end] =>
                  destruct x eqn:?; try discriminate H; cbn beta iota zeta in *
              end
          end; try subst).

(** An access check ([cap_access_res], `cap_access_res/7`) traps or
    passes; it is never [[unchecked]]. *)
Lemma cap_access_res_checked : forall c rs a size r al why,
  cap_access_res c rs a size r al <> Some (RUnchecked why).
Proof.
  unfold cap_access_res, readonly_access_res, aligned_res. intros c rs a size r al why H.
  destruct c; try discriminate H;
    destruct (object_region _ _); try discriminate H;
    destruct (_ && _); try discriminate H; try destruct r; try discriminate H;
    destruct (_ =? 0); discriminate H.
Qed.

(** What every check-like op i that continues leaves: Q bound to P's
    pointer pp, memory as it was, and its checks passed: that of its
    fact fa ([check_fact]), and that of the range fb its access must lie
    in ([access_fact]), which has the same Q and P. *)
Lemma check_like_continue : forall ge fr m i fa fb e' l' m',
  check_fact i = Some fa -> access_fact i = Some fb ->
  inst_step ge fr m i = Some (IContinue e' l' m') ->
  m' = m /\ f_q fb = f_q fa /\ f_p fb = f_p fa /\
  exists pp,
    e' = put (f_q fa) (WPtr pp) (fr_env fr) /\
    value_x ge (fr_env fr) P (f_p fa) = Some (WPtr pp) /\
    check_passes m pp (f_lo fa) (f_hi fa) (f_r fa) (f_al fa) /\
    check_passes m pp (f_lo fb) (f_hi fb) (f_r fb) (f_al fb).
Proof.
  unfold check_passes, access_res.
  intros ge fr m i fa fb e' l' m' Hf Hg H.
  destruct i as [q k o args | | | | | | |]; try discriminate Hf.
  destruct k; try (destruct o; discriminate Hf).
  destruct o; try discriminate Hf;
    rewrite inst_step_let in H by reflexivity; cbn zeta in H.
  all: destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; simpl in Hf, Hg; try discriminate Hf;
    injection Hf as <-; injection Hg as <-; cbn [f_q f_p f_lo f_hi f_r f_al].
  all: simpl in H; unfold op_res, op_res_int, checked_res, renew_res, half_res, bind_res in H.
  all: crush.
  all: repeat match goal with u : unit |- _ => destruct u end; unfold access_res in *.
  all: try (refine (conj eq_refl (conj eq_refl (conj eq_refl _))); eexists;
       split; [reflexivity | split; [reflexivity | split; eassumption]]).
  all: exfalso; eapply cap_access_res_checked; eassumption.
Qed.

(** After a check-like op that continues, its fact fa holds, and so
    does fb, the range its access must lie in. *)
Theorem check_like_holds : forall ge fr m i fa fb e' l' m',
  check_fact i = Some fa -> access_fact i = Some fb ->
  inst_step ge fr m i = Some (IContinue e' l' m') ->
  fact_holds ge m' e' fa /\ fact_holds ge m' e' fb.
Proof.
  intros ge fr m i fa fb e' l' m' Hf Hg H.
  destruct (check_like_continue _ _ _ _ _ _ _ _ _ Hf Hg H)
    as (-> & Hq & Hp & pp & -> & Ex & Ha & Hb).
  split; exists pp; [|rewrite Hq, Hp]; (split; [apply lookup_put_same | split; [apply value_x_put_same; exact Ex | assumption]]).
Qed.

(** ## Every `let` *)

(** A `let` of the name d that continues changes no region and no
    temporary but d. *)
Lemma let_step : forall ge fr m d k o args e' l' m',
  inst_step ge fr m (Let d k o args) = Some (IContinue e' l' m') ->
  m_regions m' = m_regions m /\ env_agree d (fr_env fr) e'.
Proof.
  intros ge fr m d k o args e' l' m' H. destruct (special_let o) eqn:Es.
  - destruct o; try discriminate Es; unfold inst_step in H; cbn zeta in H; crush;
      unfold bind_res in *; crush; split; try reflexivity; apply env_agree_put.
  - rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H. cbn zeta in H. cases H. injection H as Hb.
    destruct (bind_res_continue _ _ _ _ _ _ _ _ Hb) as (x & -> & -> & ->).
    split; [eapply op_res_regions; eauto | apply env_agree_put].
Qed.

(** ## Block entry

    A block is entered by an edge from the block before it, and its
    phis bind their temporaries. An unpolled edge changes nothing; the
    entry facts of ir.pl's pass are the meet of the exit facts of the
    blocks it may come from, less those that name a phi's temporary
    (Validate.v's `evidence_pass`). *)

(** The facts fs less those that name a temporary of the [[phi]]s phs
    as Q or P: what Validate.v's [evidence_pass] keeps at a block's
    entry of the meet of the facts that reach it. *)
Definition entry_kill (phs : list phi) (fs : list fact) : list fact :=
  fold_left (fun (fs : list fact) (ph : phi) => match ph with Phi d _ _ =>
               filter (fun fa => negb (name_eqb (f_q fa) d
                                       || value_eqb (f_p fa) (Tmp d))) fs end) phs fs.

(** The temporary a phi defines. *)
Definition phi_dest (ph : phi) : name := match ph with Phi d _ _ => d end.

(** A fact [entry_kill] keeps is one of fs and names no phi's temporary,
    as Q or as P. *)
Lemma entry_kill_in : forall phs fs fa, In fa (entry_kill phs fs) ->
  In fa fs /\ forall ph, In ph phs ->
    name_eqb (f_q fa) (phi_dest ph) = false /\ value_eqb (f_p fa) (Tmp (phi_dest ph)) = false.
Proof.
  induction phs as [|[d k ps] phs IH]; simpl; intros fs fa H; [split; [exact H | tauto]|].
  destruct (IH _ _ H) as [Hin Hph]. apply filter_In in Hin as [Hin Hk].
  apply negb_true_iff, orb_false_iff in Hk. split; [exact Hin|].
  intros ph [<- | Hp]; [exact Hk | auto].
Qed.

(** Once one phi fails to find its value, the fold over the rest fails
    too. *)
Lemma phis_fold_none : forall ge phs pred e0,
  fold_left (fun acc ph =>
               let* e := acc in
               match ph with
               | Phi d k pairs =>
                   let* v := lookup pred pairs in
                   let* x := value_x ge e0 k v in
                   Some (put d x e)
               end) phs None = None.
Proof. intros ge phs pred e0. induction phs; simpl; auto. Qed.

(** Running the phis phs on entry from the block pred changes only their
    own temporaries: every other name n keeps its value. *)
Lemma phis_env_agree : forall ge phs pred e0 e1 e,
  fold_left (fun acc ph =>
               let* e := acc in
               match ph with
               | Phi d k pairs =>
                   let* v := lookup pred pairs in
                   let* x := value_x ge e0 k v in
                   Some (put d x e)
               end) phs (Some e1) = Some e ->
  forall n, (forall ph, In ph phs -> name_eqb n (phi_dest ph) = false) -> lookup n e = lookup n e1.
Proof.
  induction phs as [|[d k ps] phs IH]; simpl; intros pred e0 e1 e H n Hn.
  - injection H as <-. reflexivity.
  - destruct (lookup pred ps) as [v|]; simpl in H; [|rewrite phis_fold_none in H; discriminate H].
    destruct (value_x ge e0 k v) as [x|]; simpl in H; [|rewrite phis_fold_none in H; discriminate H].
    rewrite (IH _ _ _ _ H n) by auto. apply lookup_put_other. apply (Hn (Phi d k ps)). auto.
Qed.

(** Entering a block from the block pred, where its phis bind
    ([phis_env], `phis_env/6`) and the facts fs held before them, the
    facts that name no phi temporary ([entry_kill]) hold after. *)
Theorem phis_facts_hold : forall ge m phs pred e0 e fs,
  phis_env ge phs (Some pred) e0 = Some e ->
  facts_hold ge m e0 fs -> facts_hold ge m e (entry_kill phs fs).
Proof.
  unfold phis_env. intros ge m phs pred e0 e fs Hp H fa Hin.
  destruct (entry_kill_in _ _ _ Hin) as [Hin' Hph].
  destruct (H fa Hin') as (p & Eq & Ep & Hc). exists p. split; [|split; [|exact Hc]].
  - rewrite (phis_env_agree _ _ _ _ _ _ Hp); [exact Eq|]. intros ph Hi. apply (Hph ph Hi).
  - destruct (f_p fa) as [n | c | g] eqn:Ef; [|exact Ep|exact Ep]. simpl in *.
    rewrite (phis_env_agree _ _ _ _ _ _ Hp); [exact Ep|]. intros ph Hi.
    pose proof (proj2 (Hph ph Hi)) as Hv. simpl in Hv. exact Hv.
Qed.

(** [value_eqb] is equality of values. *)
Lemma value_eqb_eq : forall v w, value_eqb v w = true -> v = w.
Proof.
  intros [a | a | a] [b | b | b] H; simpl in H; try discriminate H;
    f_equal; first [apply Z.eqb_eq | apply term_eqb_eq]; exact H.
Qed.

(** [fact_eqb] is equality of facts. *)
Lemma fact_eqb_eq : forall a b, fact_eqb a b = true -> a = b.
Proof.
  intros [q p lo hi r al] [q' p' lo' hi' r' al'] H. unfold fact_eqb in H. simpl in H.
  repeat rewrite andb_true_iff in H.
  destruct H as (((((Hq & Hp) & Hl) & Hh) & Hr) & Ha).
  apply term_eqb_eq in Hq. apply value_eqb_eq in Hp.
  apply Z.eqb_eq in Hl, Hh, Ha. destruct r, r'; try discriminate Hr. all: subst; reflexivity.
Qed.

(** A fact of the meet ([evidence_meet], `evidence_meet/2`) of the sets
    of facts that reach a block is a fact of every set it meets. *)
Lemma evidence_meet_in : forall sets s fa, In fa (evidence_meet sets) -> In s sets -> In fa s.
Proof.
  unfold evidence_meet. intros [|s0 ss] s fa H Hs; [destruct H|].
  apply filter_In in H as [H0 Hall]. destruct Hs as [<- | Hs]; [exact H0|].
  rewrite forallb_forall in Hall. pose proof (Hall s Hs) as Ex. apply existsb_exists in Ex as (y & Hy & E).
  apply fact_eqb_eq in E. subst y. exact Hy.
Qed.

(** A taken edge t from the block from ([edge_step]) changes neither
    memory nor temporaries; it leaves the frame at the entry of t's
    label, entered from from. *)
Lemma edge_step_next : forall c from t c',
  edge_step c from t = Next c' ->
  c_mem c' = c_mem c /\ fr_env (c_frame c') = fr_env (c_frame c) /\
  fr_at (c_frame c') = Enter (edge_label t) (Some from).
Proof.
  unfold edge_step. intros c from t c' H.
  destruct t, (fr_doomed (c_frame c)); try discriminate H; injection H as <-; auto.
Qed.

(** Entering the block l from pred runs its phis on what the edge left:
    memory is unchanged, and the frame goes on to the block's
    instructions and jump. *)
Lemma enter_step : forall ge c l pred c',
  fr_at (c_frame c) = Enter l (Some pred) -> step ge c = Next c' ->
  c_mem c' = c_mem c /\
  exists b, find_block l (fn_blocks (fr_fn (c_frame c))) = Some b /\
    phis_env ge (b_phis b) (Some pred) (fr_env (c_frame c)) = Some (fr_env (c_frame c')) /\
    fr_at (c_frame c') = Exec l (b_insts b) (b_jump b).
Proof.
  intros ge c l pred c' Ha H. unfold step in H. rewrite Ha in H.
  destruct (c_fuel c =? 0); [discriminate H|]. apply or_stuck_next in H.
  destruct (find_block _ _) as [b|]; simpl in H; [|discriminate H].
  destruct (phis_env ge (b_phis b) (Some pred) (fr_env (c_frame c))) as [e|] eqn:Ep;
    unfold phis_env in Ep; rewrite Ep in H; simpl in H; [|discriminate H].
  injection H as <-. simpl. split; [reflexivity|]. exists b. auto.
Qed.

(** Where the facts fs hold as a block is left by the edge t
    ([edge_step]), and fs is one of the sets the pass meets at the entry
    of t's block b, the pass's entry facts of b ([entry_kill] of the
    meet) hold once its phis have run. *)
Theorem entry_holds : forall ge c c1 c2 from t sets fs b,
  edge_step c from t = Next c1 -> step ge c1 = Next c2 ->
  find_block (edge_label t) (fn_blocks (fr_fn (c_frame c1))) = Some b ->
  facts_hold ge (c_mem c) (fr_env (c_frame c)) fs -> In fs sets ->
  facts_hold ge (c_mem c2) (fr_env (c_frame c2)) (entry_kill (b_phis b) (evidence_meet sets)).
Proof.
  intros ge c c1 c2 from t sets fs b He Hs Hb H Hin.
  destruct (edge_step_next _ _ _ _ He) as (Hm1 & He1 & Ha1).
  destruct (enter_step _ _ _ _ _ Ha1 Hs) as (Hm2 & b' & Hb' & Hp & _).
  rewrite Hb in Hb'. injection Hb' as <-.
  rewrite Hm2, Hm1. eapply phis_facts_hold; [exact Hp|].
  rewrite He1. intros fa Hfa. apply H. eapply evidence_meet_in; eauto.
Qed.

(** ## The pass, instruction by instruction

    `checked_inst_rest/7` takes the check-like instructions together
    with the access they are checked for, ends the facts at a
    `check_local` or `check_function`, and otherwise keeps
    `evidence_after/3` of the facts (or kills a repeated getter's
    temporary). `pass_special` names the instructions it treats apart;
    `generic_rest` is its last case, copied. *)

(** The instructions `checked_inst_rest/7` treats apart: a
    `check_local`, a `check_function`, and every check-like op
    ([check_fact]). *)
Definition pass_special (i : inst) : bool :=
  match i with
  | Let _ A (CheckLocal _ _ _ _ _) [] | Let _ F CheckFunction _ => true
  | _ => match check_fact i with Some _ => true | None => false end
  end.

(** The last case of `checked_inst_rest/7`, copied for the proof. It
    gives the facts after the instruction i ([evidence_after], or a
    repeated [[getter]]'s temporary killed) and accepts i unless i is a
    raw access with no live fact of its operand that covers it
    ([covered_access] or [hull_covered]), a raw call, a call through a
    temporary, or pointer arithmetic or a pointer copy outside a
    [[flight]]. *)
Definition generic_rest (s : src) (i : inst) (rest : list inst) (live : list fact)
  : option (list inst * list fact) :=
  let once := s_once s in
    let live' := match i with
                 | Let d P Copy [Global g] =>
                     match lookup d (s_getters s) with
                     | Some g1 => if name_eqb g1 g then kill d live else evidence_after i live
                     | None => evidence_after i live
                     end
                 | _ => evidence_after i live
                 end in
    let ok :=
      match raw_access i with
      | Some (q, x, _, _) =>
          reusing_access i x &&
          match fact_of q live with
          | Some fa =>
              covered_access i q (f_lo fa) (f_hi fa) (f_r fa) (f_al fa)
              || hull_covered i q (f_p fa) (f_lo fa) (f_al fa) live once
          | None => false
          end
      | None =>
          match i with
          | RawCall _ _ _ => false
          | Call _ (Tmp _) _ => false                         (* unchecked_access *)
          | Let _ P (Add | Sub | Itop) _ => false              (* implicit_flight *)
          | Let _ P Copy [Tmp _] | Let _ P Copy [Const _] => false
          | _ => true
          end
      end in
    if ok then Some (rest, live') else None.

(** For an instruction it does not treat apart, `checked_inst_rest/7` is
    [generic_rest], by computation. So Validate.v, the transcription the
    gates compare, needs no refactoring for the proof. *)
Lemma checked_inst_rest_generic : forall s i rest live,
  pass_special i = false -> checked_inst_rest s i rest live = generic_rest s i rest live.
Proof.
  intros s i rest live H. destruct i as [q k o args | | | | | | |]; try reflexivity.
  destruct k; try reflexivity; destruct o; try reflexivity;
    destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; try reflexivity; discriminate H.
Qed.

(** What [generic_rest] answers: the same remaining instructions; the
    facts [evidence_after] keeps, or a getter copy's temporary killed;
    and, for a raw access through q, a live fact of q that covers it by
    [covered_access] or [hull_covered]. *)
Lemma generic_rest_shape : forall s i rest live rest' live',
  generic_rest s i rest live = Some (rest', live') ->
  rest' = rest /\
  (live' = evidence_after i live \/ exists d g, i = Let d P Copy [Global g] /\ live' = kill d live) /\
  forall q x off need, raw_access i = Some (q, x, off, need) ->
    exists fa, fact_of q live = Some fa /\
      (covered_access i q (f_lo fa) (f_hi fa) (f_r fa) (f_al fa) = true \/
       hull_covered i q (f_p fa) (f_lo fa) (f_al fa) live (s_once s) = true).
Proof.
  unfold generic_rest. intros s i rest live rest' live' H. cbn zeta in H.
  match type of H with (if ?b then _ else _) = _ => destruct b eqn:Hok; [|discriminate H] end.
  injection H as <- <-. split; [reflexivity|]. split.
  - destruct i as [d k o args | | | | | | |]; auto.
    destruct k, o; auto; destruct args as [|[n|c|g] [|a2 args]]; auto.
    destruct (lookup d (s_getters s)); auto. destruct (name_eqb _ _); eauto.
  - intros q x off need Hr. rewrite Hr in Hok. apply andb_true_iff in Hok as [_ Hok].
    destruct (fact_of q live) as [fa|]; [|discriminate Hok]. exists fa. split; [reflexivity|].
    apply orb_true_iff. exact Hok.
Qed.

(** A check-like instruction has an access range too. *)
Lemma access_fact_some : forall i fa, check_fact i = Some fa -> exists fb, access_fact i = Some fb.
Proof.
  intros i fa H. destruct i as [q k o args | | | | | | |]; try discriminate H.
  destruct k, o; try discriminate H;
    destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; simpl in *; try discriminate H; eauto.
Qed.

(** The pass takes a check-like instruction i together with the next
    instruction, its access: the access must lie in i's range
    ([proof_use], `proof_use/6`), and the facts after both are those
    [evidence_after] keeps across the access, from i's fact put before
    the facts kept across i. *)
Lemma checked_inst_rest_check : forall s i rest live rest' live' fa fb,
  check_fact i = Some fa -> access_fact i = Some fb ->
  checked_inst_rest s i rest live = Some (rest', live') ->
  exists access, rest = access :: rest' /\
    proof_use access (f_q fb) (f_lo fb) (f_hi fb) (f_r fb) (f_al fb) = true /\
    live' = evidence_after access (fa :: evidence_after i live).
Proof.
  intros s i rest live rest' live' fa fb Hf Hg H.
  destruct i as [q k o args | | | | | | |]; try discriminate Hf.
  destruct k; try (destruct o; discriminate Hf).
  destruct o; try discriminate Hf;
    destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; simpl in Hf, Hg; try discriminate Hf;
    injection Hf as <-; injection Hg as <-; cbn [f_q f_p f_lo f_hi f_r f_al].
  all: unfold checked_inst_rest in H; cbn zeta in H.
  all: repeat match type of H with
              | context [match ?x with _ => _ end] => destruct x eqn:?; try discriminate H
              end.
  all: injection H as <- <-; eexists; split; [reflexivity|].
  all: repeat match goal with E : (_ && _) = true |- _ => apply andb_true_iff in E as [? ?] end.
  all: split; [assumption | reflexivity].
Qed.

(** The pass takes a `check_local` with its access too, and keeps after
    the access the facts it had with q killed. *)
Lemma checked_inst_rest_local : forall s q x off bytes r al rest live rest' live',
  checked_inst_rest s (Let q A (CheckLocal x off bytes r al) []) rest live = Some (rest', live') ->
  exists access, rest = access :: rest' /\ live' = evidence_after access (kill q live).
Proof.
  intros s q x off bytes r al rest live rest' live' H. unfold checked_inst_rest in H. cbn zeta in H.
  repeat match type of H with
         | context [match ?y with _ => _ end] => destruct y eqn:?; try discriminate H
         end.
  injection H as <- <-. eauto.
Qed.

(** After a `check_function` and its call, the pass keeps no fact. *)
Lemma checked_inst_rest_function : forall s q args rest live rest' live',
  checked_inst_rest s (Let q F CheckFunction args) rest live = Some (rest', live') -> live' = [].
Proof.
  intros s q args rest live rest' live' H. unfold checked_inst_rest in H.
  destruct rest as [|[] rest]; try discriminate H; simpl in H;
    destruct callee; try discriminate H; destruct (name_eqb _ _); try discriminate H.
  injection H as _ <-. reflexivity.
Qed.

(** Where the facts live hold before an instruction i the pass accepts
    and i continues, the pass's facts after it hold; or, for an
    instruction the pass takes with its access, they hold after that
    access, whatever frame fr1 with i's environment runs it. *)
Theorem checked_inst_holds : forall ge s fr m i rest live rest' live' e1 l1 m1,
  facts_hold ge m (fr_env fr) live ->
  checked_inst_rest s i rest live = Some (rest', live') ->
  inst_step ge fr m i = Some (IContinue e1 l1 m1) ->
  (rest' = rest /\ facts_hold ge m1 e1 live') \/
  (exists access, rest = access :: rest' /\
     forall fr1 e2 l2 m2, fr_env fr1 = e1 ->
       inst_step ge fr1 m1 access = Some (IContinue e2 l2 m2) -> facts_hold ge m2 e2 live').
Proof.
  intros ge s fr m i rest live rest' live' e1 l1 m1 Hl Hc Hs.
  destruct (check_fact i) as [fa|] eqn:Hf.
  - assert (exists fb, access_fact i = Some fb) as [fb Hg]
      by (eapply access_fact_some; eauto).
    destruct (checked_inst_rest_check _ _ _ _ _ _ _ _ Hf Hg Hc) as (access & -> & _ & ->).
    right. exists access. split; [reflexivity|]. intros fr1 e2 l2 m2 He Ha.
    eapply evidence_after_holds; [|exact Ha]. rewrite He. apply facts_hold_cons.
    + exact (proj1 (check_like_holds _ _ _ _ _ _ _ _ _ Hf Hg Hs)).
    + eapply evidence_after_holds; eauto.
  - destruct (pass_special i) eqn:Hp.
    + right. unfold pass_special in Hp. rewrite Hf in Hp.
      destruct i as [q k o args | | | | | | |]; try discriminate Hp.
      destruct k; try discriminate Hp; destruct o; try discriminate Hp.
      * destruct args; [|discriminate Hp].
        destruct (checked_inst_rest_local _ _ _ _ _ _ _ _ _ _ _ Hc) as (access & -> & ->).
        exists access. split; [reflexivity|]. intros fr1 e2 l2 m2 He Ha.
        eapply evidence_after_holds; [|exact Ha]. rewrite He.
        destruct (let_step _ _ _ _ _ _ _ _ _ _ Hs) as [Hr Ha'].
        eapply facts_hold_kill; eauto.
      * rewrite (checked_inst_rest_function _ _ _ _ _ _ _ Hc).
        unfold checked_inst_rest in Hc. destruct rest as [|access rest0]; [discriminate Hc|].
        exists access. split.
        { destruct access; try discriminate Hc; destruct callee; try discriminate Hc;
            destruct (name_eqb _ _); try discriminate Hc; injection Hc as <- _; reflexivity. }
        intros fr1 e2 l2 m2 _ _ fa' [].
    + left. rewrite (checked_inst_rest_generic _ _ _ _ Hp) in Hc.
      destruct (generic_rest_shape _ _ _ _ _ _ Hc) as (-> & [-> | (d & g & -> & ->)] & _).
      * split; [reflexivity|]. eapply evidence_after_holds; eauto.
      * split; [reflexivity|]. destruct (let_step _ _ _ _ _ _ _ _ _ _ Hs) as [Hr He].
        eapply facts_hold_kill; eauto.
Qed.

(** The access a check-like instruction i is checked for, run right
    after it, gives no [[unchecked]], where objects fit the address
    space. *)
Theorem checked_access_not_unchecked : forall ge s fr m i rest live rest' live' e1 l1 m1
    fr1 access why,
  objects_fit (m_regions m1) ->
  check_fact i <> None ->
  checked_inst_rest s i (access :: rest) live = Some (rest', live') ->
  inst_step ge fr m i = Some (IContinue e1 l1 m1) ->
  fr_env fr1 = e1 ->
  inst_step ge fr1 m1 access <> Some (IStop (Unchecked why)).
Proof.
  intros ge s fr m i rest live rest' live' e1 l1 m1 fr1 access why Hfit Hf Hc Hs He.
  destruct (check_fact i) as [fa|] eqn:Ef; [|contradiction].
  assert (exists fb, access_fact i = Some fb) as [fb Hg]
    by (eapply access_fact_some; eauto).
  destruct (checked_inst_rest_check _ _ _ _ _ _ _ _ Ef Hg Hc) as (access' & E & Hu & _).
  injection E as <- _. apply andb_true_iff in Hu as [Hcov _].
  destruct (proj2 (check_like_holds _ _ _ _ _ _ _ _ _ Ef Hg Hs)) as (p & Eq & _ & Hp).
  rewrite <- He in Eq.
  exact (covered_access_not_unchecked _ _ _ _ _ _ _ _ _ _ _ Hfit Hcov Eq Hp).
Qed.

(** A raw access i that the pass accepts on its own (not with a check)
    gives no [[unchecked]] where the facts hold and objects fit the
    address space, unless the pass accepted it by `hull_covered/7`,
    whose case Chain.v's [hull_access_not_unchecked] closes. *)
Theorem generic_access_not_unchecked : forall ge s fr m i rest live rest' live' q x off need why,
  objects_fit (m_regions m) ->
  facts_hold ge m (fr_env fr) live ->
  pass_special i = false ->
  checked_inst_rest s i rest live = Some (rest', live') ->
  raw_access i = Some (q, x, off, need) ->
  inst_step ge fr m i <> Some (IStop (Unchecked why)) \/
  exists fa, fact_of q live = Some fa /\
    hull_covered i q (f_p fa) (f_lo fa) (f_al fa) live (s_once s) = true.
Proof.
  intros ge s fr m i rest live rest' live' q x off need why Hfit Hl Hp Hc Hr.
  rewrite (checked_inst_rest_generic _ _ _ _ Hp) in Hc.
  destruct (generic_rest_shape _ _ _ _ _ _ Hc) as (_ & _ & Ha).
  destruct (Ha _ _ _ _ Hr) as (fa & Hfa & [Hcov | Hh]); [left | right; eauto].
  eapply live_access_not_unchecked; eauto.
Qed.
