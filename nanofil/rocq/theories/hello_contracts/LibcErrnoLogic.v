(** Selected FILE calls with program-owned errno bytes. Private FILE
    storage remains separate; only the four scalar bytes are handed to
    close. Query frames restore those bytes without a ghost update. *)
From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Identity ExternalCalls
  ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams Pieces Heap
  ContractFrame Logic StringLogic MemLogic LentLogic LocaleLogic LibcStreamLogic HelloClose.
Open Scope Z_scope.
Open Scope list_scope.

Definition errno_span (b o : Z) : span := mkSpan (mkPtr (b + o) (Obj b)) 4.
Definition errno_keys (b o : Z) : list piece := (byte_ps b o (repeat 0 4)).*1.
Definition errno_bytes (m : mem) (b o : Z) : list Z :=
  map (fun i => m_bytes m (b + (o + Z.of_nat i))) (seq 0 4).

Lemma errno_bytes_keys : forall m b o,
  (byte_ps b o (errno_bytes m b o)).*1 = errno_keys b o.
Proof. intros. unfold errno_keys, errno_bytes. rewrite !byte_ps_keys length_map length_seq. reflexivity. Qed.

Lemma errno_bytes_agree : forall m b o,
  errno_cell m (mkPtr (b + o) (Obj b)) -> all_agree m (byte_ps b o (errno_bytes m b o)).
Proof.
  intros m b o (_ & (_ & base & reg & Hcap & E & L & Haccess) & _).
  injection Hcap as <-.
  destruct (access_region m (b + o) (Obj b) b 4 Write 1 (or_introl eq_refl) Haccess)
    as (reg0 & E0 & Hlo & Hhi). rewrite E in E0. injection E0 as <-.
  apply all_agree_intro. intros l v Hin.
  destruct (byte_ps_elem _ _ _ _ _ Hin) as (i & x & Hxi & -> & ->).
  assert (Hi : (i < 4)%nat).
  { apply lookup_lt_Some in Hxi. unfold errno_bytes in Hxi. rewrite length_map length_seq in Hxi. exact Hxi. }
  assert (Hx : x = m_bytes m (b + (o + Z.of_nat i))).
  { destruct i as [|[|[|[|i]]]]; try lia; injection Hxi as <-; reflexivity. }
  cbn [agree_piece]. split; [unfold registered; congruence|].
  intros reg' E' _. rewrite E in E'. injection E' as <-.
  split; [lia|]. split; [lia|symmetry; exact Hx].
Qed.

(** Other byte/aux pieces must not alias the four handed-over bytes.
    In particular no errno aux slot is handed over. FILE roots and
    release identities remain private, even though errno is owned. *)
Definition libc_errno_wi rep p b o m w (h : gmap piece pval) : Prop :=
  libc_stream_ready rep m w /\ libc_errno (fst w) = mkPtr (b + o) (Obj b) /\
  roots_apart (libc_stream_aux_roots w p) h m /\ ids_apart (libc_stream_releases w p) h /\
  pieces_off (errno_keys b o) h m (span_contains (errno_span b o)).

Lemma errno_roots_out : forall p b o m w h,
  libc_errno (fst w) = mkPtr (b + o) (Obj b) ->
  roots_apart (libc_stream_aux_roots w p) h m ->
  roots_out (libc_stream_writes w p) h m (span_contains (errno_span b o)).
Proof.
  intros p b o m w h He Hr root a Hin Hspan Hown.
  unfold libc_stream_writes in Hin. destruct (libc_file_at w p) as [file|] eqn:Hfile;
    [|contradiction]. apply in_app_or in Hin as [Hin|[<-|[]]].
  - exfalso. apply (Hr root a); [unfold libc_stream_aux_roots; rewrite Hfile; exact Hin|assumption|assumption].
  - rewrite He in Hspan. exact Hspan.
Qed.

(** An old registered object's live endpoint is its old region: an
    effects path cannot resurrect or replace the identity. *)
Lemma registered_live_back : forall m m' b reg,
  persists m m' -> registered m b -> live_at m' b reg -> live_at m b reg.
Proof.
  intros m m' b reg Hp Hreg [E L]. unfold registered in Hreg.
  destruct (object_region b (m_regions m)) as [old|] eqn:E0; [|contradiction].
  destruct (Hp b old E0) as [E'|E']; rewrite E in E'; injection E' as Hsame.
  - subst old. split; assumption.
  - apply (f_equal r_life) in Hsame. cbn [freed_region r_life] in Hsame. congruence.
Qed.

(** A ghost update may replace values of existing memory keys, but
    cannot introduce a new program-owned object identity. *)
Definition memory_keys_from (h' h : gmap piece pval) : Prop :=
  forall l v, h' !! l = Some v -> mem_piece l -> exists old, h !! l = Some old.

(** Separation depends on memory keys, not their stored ghost values.
    This transports it across sampled errno and stream-name updates. *)
Lemma errno_wi_heap : forall rep p b o m w h h',
  libc_errno_wi rep p b o m w h -> memory_keys_from h' h ->
  libc_errno_wi rep p b o m w h'.
Proof.
  intros rep p b o m w h h' (Hr & He & Hroots & Hrelease & Hoff) Hkeys.
  split; [exact Hr|]. split; [exact He|]. split; [|split].
  - intros root a Hin Hspan (l & v & reg & Hl & Hmem & Hlive & Hrange).
    destruct (Hkeys l v Hl Hmem) as [old Hold]. apply (Hroots root a Hin Hspan).
    exists l, old, reg. exact (conj Hold (conj Hmem (conj Hlive Hrange))).
  - intros base l v Hin Hl Hmem. destruct (Hkeys l v Hl Hmem) as [old Hold].
    exact (Hrelease base l old Hin Hold Hmem).
  - intros l v Hl Hnot. destruct l as [base|base off|base off|key]; try exact I.
    all: destruct (Hkeys _ _ Hl I) as [old Hold]; exact (Hoff _ old Hold Hnot).
Qed.

Lemma errno_wi_endpoint : forall rep requests wide p b o m w born m' w' h h',
  libc_errno_wi rep p b o m w h -> agrees m h -> persists m m' -> live_disjoint m' ->
  libc_stream_ready rep m' w' -> libc_errno (fst w') = libc_errno (fst w) ->
  stream_delegates (libc_stream_model rep requests wide) w p born m' w' ->
  ids_apart born h -> memory_keys_from h' h -> libc_errno_wi rep p b o m' w' h'.
Proof.
  intros rep requests wide p b o m w born m' w' h h'
    (Hready & He & Hroots & Hrel & Hoff) Ha Hp Hd Hready' Herrno
    (Hdelegate & _ & Hrelease) Hb Hkeys.
  assert (He' : libc_errno (fst w') = mkPtr (b + o) (Obj b)).
  { rewrite Herrno. exact He. }
  assert (Hown : forall a, owned_live h' m' a -> owned_live h m a /\ owned_live h m' a).
  { intros a (l & v & reg & Hl & Hmem & Hlive & Hrange).
    destruct (Hkeys l v Hl Hmem) as [old Hold].
    assert (Hreg : registered m (piece_id l)) by
      (eapply agree_piece_registered; [exact Hmem|exact (Ha l old Hold)]).
    assert (Hlive0 : live_at m (piece_id l) reg) by (eapply registered_live_back; eauto).
    split.
    - exists l, old, reg. exact (conj Hold (conj Hmem (conj Hlive0 Hrange))).
    - exists l, old, reg. exact (conj Hold (conj Hmem (conj Hlive Hrange))). }
  split; [exact Hready'|]. split; [exact He'|]. split; [|split].
  - intros root a Hroot Hspan Howned. destruct (Hown a Howned) as [Hentry Hend].
    unfold libc_stream_aux_roots in Hroot.
    destruct (libc_file_at w' p) as [file|] eqn:Hfile; [|contradiction].
    destruct (libc_file_at_ready rep m' w' p file Hready' Hfile)
      as (_ & _ & _ & _ & _ & _ & Hapart & _).
    assert (Hnoterrno : ~ span_contains (errno_span b o) a).
    { specialize (Hapart root Hroot). rewrite He' in Hapart.
      unfold spans_apart, span_contains, errno_span in *. simpl in *. lia. }
    assert (Hin : In root (libc_stream_writes w' p)).
    { unfold libc_stream_writes. rewrite Hfile. apply in_or_app. auto. }
    destruct (Hdelegate root Hin) as [_ Hauth].
    destruct (Hauth a Hspan) as [(old & Hold & _ & Haold)|Hborn].
    + change (In old (libc_stream_writes w p)) in Hold. unfold libc_stream_writes in Hold.
      destruct (libc_file_at w p) as [oldfile|] eqn:Holdfile; [|contradiction].
      apply in_app_or in Hold as [Hold|[<-|[]]].
      * apply (Hroots old a); [unfold libc_stream_aux_roots; rewrite Holdfile; exact Hold|assumption|assumption].
      * apply Hnoterrno. rewrite He in Haold. exact Haold.
    + exact (owned_not_authority [] born h m' a Hd
        (fun root a Hnil => match Hnil with end) Hb Hend (or_intror Hborn)).
  - intros base l v Hin Hl Hmem. destruct (Hkeys l v Hl Hmem) as [old Hold].
    destruct (Hrelease base Hin) as [Hprev|Hborn];
      [exact (Hrel base l old Hprev Hold Hmem)|exact (Hb base l old Hborn Hold Hmem)].
  - intros l v Hl Hnot. destruct l as [base|base off|base off|key]; try exact I.
    all: intros reg [E L] Ho Hend Hout;
      destruct (Hkeys _ _ Hl I) as [old Hold];
      pose proof (Ha _ old Hold) as Hreg;
      apply agree_piece_registered in Hreg; [|exact I];
      destruct (registered_live_back m m' base reg Hp Hreg (conj E L)) as [E0 L0];
      exact (Hoff _ old Hold Hnot reg (conj E0 L0) Ho Hend Hout).
Qed.

(** The unselected FILE keeps its inventory. Its private frame transports
    through old-object persistence even when the selected FILE writes. *)
Lemma errno_wi_fixed : forall rep p b o m w m' w' h,
  libc_errno_wi rep p b o m w h -> agrees m h -> persists m m' ->
  libc_stream_ready rep m' w' ->
  libc_errno (fst w') = libc_errno (fst w) ->
  libc_stream_aux_roots w' p = libc_stream_aux_roots w p ->
  libc_stream_releases w' p = libc_stream_releases w p ->
  libc_errno_wi rep p b o m' w' h.
Proof.
  intros rep p b o m w m' w' h (Hready & He & Hroots & Hrelease & Hoff)
    Ha Hp Hready' He' Hroots' Hrelease'.
  split; [exact Hready'|]. split; [congruence|]. split; [|split].
  - rewrite Hroots'. intros root a Hin Hspan (l & v & reg & Hl & Hmem & Hlive & Hrange).
    apply (Hroots root a Hin Hspan). exists l, v, reg.
    split; [exact Hl|]. split; [exact Hmem|]. split; [|exact Hrange].
    eapply registered_live_back; [exact Hp| |exact Hlive].
    eapply agree_piece_registered; [exact Hmem|exact (Ha l v Hl)].
  - rewrite Hrelease'. exact Hrelease.
  - intros l v Hl Hnot. destruct l as [base|base off|base off|key]; try exact I.
    all: intros reg Hlive Ho Hend Hout;
      apply (Hoff _ v Hl Hnot reg); [|exact Ho|exact Hend|exact Hout];
      pose proof (Ha _ v Hl) as Hreg;
      apply agree_piece_registered in Hreg; [|exact I];
      eapply registered_live_back; [exact Hp| |exact Hlive];
      exact Hreg.
Qed.

Lemma overwrite_app : forall ps qs h, overwrite (ps ++ qs) h = overwrite ps (overwrite qs h).
Proof. intros ps. induction ps as [|[l v] ps IH]; intros qs h; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Module LibcErrnoLogicOn (R : Runtime) (LG : StreamFrameLogic R).
Module M := LG.L.M.
Module S := StreamsOn R M.

(** This frame accepts owned errno, unlike the all-roots-apart frame.
    It applies to finite prefixes, not just successful close results. *)
Lemma errno_prefix_frame : forall rep p b o spec xs s m w born trace s' m' w' h,
  M.E.prefix spec xs s m w born trace s' m' w' ->
  contract_writes spec xs m w = libc_stream_writes w p ->
  contract_releases spec xs m w = [] \/
    contract_releases spec xs m w = libc_stream_releases w p ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_errno_wi rep p b o m w h ->
  agrees_except (errno_keys b o) m' h /\ LG.ids_registered h m' /\
    live_disjoint m' /\ ids_apart born h /\ R.ready s' m' /\ persists m m'.
Proof.
  intros rep p b o spec xs s m w born trace s' m' w' h Hp Hw Hrelease Ha Hd Hr
    (Hready & He & Hroots & Hrel & Hoff).
  destruct (LG.prefix_agrees_out _ _ _ _ _ _ _ _ _ _ _ h (errno_keys b o)
    (span_contains (errno_span b o)) Hp Hr Hd) as (Ha' & Hids' & Hd' & Hb).
  - intros l v Hl _. exact (Ha l v Hl).
  - intros l v Hl Hmem. eapply agree_piece_registered; [exact Hmem|exact (Ha l v Hl)].
  - rewrite Hw. eapply errno_roots_out; eauto.
  - exact Hoff.
  - destruct Hrelease as [-> | ->]; [intros base l v []|exact Hrel].
  - destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' Hpers].
    exact (conj Ha' (conj Hids' (conj Hd' (conj Hb (conj Hr' Hpers))))).
Qed.

(** The query's byte frame restores its original owned errno pieces.
    The rest of the heap was already preserved by the effects frame. *)
Lemma query_agrees : forall rep requests wide p b o spec r args s m w trace ending s' m' w' h,
  (spec = ferror_contract (libc_stream_model rep requests wide) \/
   spec = fpending_contract (libc_stream_model rep requests wide)) ->
  M.E.invoke spec r args [WPtr p] s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_errno_wi rep p b o m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m'.
Proof.
  intros rep requests wide p b o spec r args s m w trace ending s' m' w' h
    Hspec Hcall Ha Hd Hr Hwi.
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
  destruct Hspec as [-> | ->].
  all: (
    destruct (errno_prefix_frame rep p b o _ _ _ _ _ _ _ _ _ _ h Hp eq_refl
      (or_introl eq_refl) Ha Hd Hr Hwi) as (Hexcept & Hids & Hd' & Hb & Hr' & Hpers);
    split; [|auto];
    destruct Hwi as (Hready & He & Hroots & Hrel & Hoff);
    destruct Hp as (_ & p0 & info & Hxs & Hinfo & Hopen & Hframe & Hdelegate & Htrace & Haux & Hbytes);
    injection Hxs as <-;
    intros l v Hl;
    destruct (decide (l ∈ errno_keys b o)) as [Hkey|Hkey];
      [|exact (Hexcept l v Hl Hkey)];
    unfold errno_keys in Hkey;
    rewrite byte_ps_keys in Hkey;
    apply list_elem_of_fmap in Hkey as (i & -> & Hi);
    apply elem_of_seqZ in Hi;
    pose proof (Ha _ _ Hl) as Hag;
    destruct v; cbn [agree_piece] in Hag |- *; try contradiction;
    destruct Hag as [Hreg Hin];
    split; [exact (Hids _ _ Hl I)|];
    intros reg E L;
    destruct (registered_live_back m m' b reg Hpers Hreg (conj E L)) as [E0 L0];
    destruct (Hin reg E0 L0) as (Ho & Hend & Hval);
    split; [exact Ho|]; split; [exact Hend|];
    assert (Hobject : in_object m (b + i)) by (exists b, reg; split; [exact E0|lia]);
    assert (Hown : owned_live h m (b + i)) by
      (exists (PByte b i), (VByte v), reg; repeat split; try assumption; simpl; lia);
    assert (Houtside : ~ write_authority (libc_stream_aux_roots w p) [] m (b + i)) by
      (eapply owned_not_authority; [exact Hd|exact Hroots|intros base l0 v0 []|exact Hown]);
    rewrite (Hbytes (b + i) Hobject Houtside); exact Hval).
Qed.

(** Both queries re-establish the same owned-errno world interpretation,
    not merely the result shape or memory agreement. *)
Theorem query_frame : forall rep requests wide p b o spec r args s m w trace ending s' m' w' h,
  (spec = ferror_contract (libc_stream_model rep requests wide) \/
   spec = fpending_contract (libc_stream_model rep requests wide)) ->
  M.E.invoke spec r args [WPtr p] s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_errno_wi rep p b o m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ libc_errno_wi rep p b o m' w' h.
Proof.
  intros rep requests wide p b o spec r args s m w trace ending s' m' w' h
    Hspec Hcall Ha Hd Hr Hwi.
  destruct (query_agrees rep requests wide p b o spec r args s m w trace ending s' m' w' h
    Hspec Hcall Ha Hd Hr Hwi)
    as (Ha' & Hd' & Hr').
  split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|].
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
  destruct Hspec as [-> | ->].
  all: (
    destruct (errno_prefix_frame rep p b o _ _ _ _ _ _ _ _ _ _ h Hp eq_refl
      (or_introl eq_refl) Ha Hd Hr Hwi) as (_ & _ & _ & Hb & _ & Hpers);
    destruct Hp as (_ & p0 & info & Hxs & Hinfo & Hopen & Hframe & Hdelegate & _);
    injection Hxs as <-;
    eapply errno_wi_endpoint; [exact Hwi|exact Ha|exact Hpers|exact Hd'|
      exact (proj1 Hopen)|exact (proj1 (proj2 (proj2 (proj2 Hframe))))|exact Hdelegate|exact Hb|];
    intros l v Hl _; eauto).
Qed.

(** Close can write owned errno while framing everything else. The
    bytes returned to the logic are read from the actual final memory;
    no errno value is guessed from EOF or from a host syscall. *)
Theorem close_frame : forall rep requests wide p b o r args s m w trace ending s' m' w' h xs,
  M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
    r args [WPtr p] s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_errno_wi rep p b o m w h ->
  length xs = 4%nat ->
  (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) ->
  exists ys, length ys = 4%nat /\
    (byte_ps b o ys).*1 = (byte_ps b o xs).*1 /\
    agrees m' (overwrite (byte_ps b o ys) h) /\ live_disjoint m' /\ R.ready s' m' /\
    libc_errno_wi rep p b o m' w' (overwrite (byte_ps b o ys) h).
Proof.
  intros rep requests wide p b o r args s m w trace ending s' m' w' h xs
    Hcall Ha Hd Hr Hwi Hlen Howned.
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
  destruct (errno_prefix_frame rep p b o _ _ _ _ _ _ _ _ _ _ h Hp eq_refl
    (or_intror eq_refl) Ha Hd Hr Hwi) as (Hexcept & Hids & Hd' & Hb & Hr' & Hpers).
  destruct Hp as (_ & p0 & info & final & Hxs & Hinfo & Hsettle & Hstate &
    Hready & Hframe & Hdelegate & _). injection Hxs as <-.
  assert (He : libc_errno (fst w') = mkPtr (b + o) (Obj b)).
  { rewrite (proj1 (proj2 (proj2 (proj2 Hframe)))). exact (proj1 (proj2 Hwi)). }
  assert (Hbytes : all_agree m' (byte_ps b o (errno_bytes m' b o))).
  { apply errno_bytes_agree. rewrite <- He. exact (proj1 (proj2 (proj2 Hready))). }
  assert (Hkeys : (byte_ps b o (errno_bytes m' b o)).*1 = (byte_ps b o xs).*1).
  { rewrite !byte_ps_keys. unfold errno_bytes. rewrite length_map length_seq Hlen. reflexivity. }
  exists (errno_bytes m' b o). split; [unfold errno_bytes; rewrite length_map length_seq; reflexivity|].
  split; [exact Hkeys|]. split.
  - intros l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin|[Hnot Hold]].
    + exact (all_agree_elem _ _ _ _ Hbytes Hin).
    + apply Hexcept; [exact Hold|]. rewrite <- (errno_bytes_keys m' b o). exact Hnot.
  - split; [exact Hd'|]. split; [exact Hr'|].
    eapply errno_wi_endpoint; [exact Hwi|exact Ha|exact Hpers|exact Hd'|
      exact Hready|exact (proj1 (proj2 (proj2 (proj2 Hframe))))|exact Hdelegate|exact Hb|].
    intros l v Hl Hmem. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin|[_ Hold]]; [|eauto].
    assert (Hkey : l ∈ (byte_ps b o xs).*1).
    { rewrite <- Hkeys. apply list_elem_of_fmap. exists (l, v). auto. }
    apply list_elem_of_fmap in Hkey as ([l0 old] & E & Hinold). simpl in E. subst l0.
    exists old. apply Howned. exact Hinold.
Qed.

(** The stream assertion may also change logical values at close. Its
    memory pieces must remain the same, and its keys must not overlap
    errno. The supplied replacement law is pure ghost bookkeeping, not
    an assumption about what the native call did to memory. *)
Theorem close_stream_frame : forall rep requests wide p b o r args s m w trace values s' m' w' h xs before after,
  after.*1 = before.*1 ->
  (forall l, l ∈ before.*1 -> l ∉ errno_keys b o) ->
  (forall mm hh, agrees mm hh ->
    (forall l v, (l, v) ∈ before -> hh !! l = Some v) -> all_agree mm after) ->
  M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
    r args [WPtr p] s m w trace (CallReturn values) s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_errno_wi rep p b o m w h ->
  length xs = 4%nat ->
  (forall l v, (l, v) ∈ before ++ byte_ps b o xs -> h !! l = Some v) ->
  exists n ys, values = [WInt n] /\ 0 <= n < 2 ^ 32 /\ length ys = 4%nat /\
    (after ++ byte_ps b o ys).*1 = (before ++ byte_ps b o xs).*1 /\
    agrees m' (overwrite (after ++ byte_ps b o ys) h) /\ live_disjoint m' /\ R.ready s' m' /\
    libc_errno_wi rep p b o m' w' (overwrite (after ++ byte_ps b o ys) h).
Proof.
  intros rep requests wide p b o r args s m w trace values s' m' w' h xs before after
    Hsame Hapart Hreplace Hcall Ha Hd Hr Hwi Hlen Howned.
  destruct (close_frame rep requests wide p b o r args s m w trace (CallReturn values)
    s' m' w' h xs Hcall Ha Hd Hr Hwi Hlen) as (ys & Hys & Hkeys & Ha' & Hd' & Hr' & Hwi').
  - intros l v Hin. apply Howned, elem_of_app. auto.
  - assert (Hbefore : forall l v, (l, v) ∈ before -> overwrite (byte_ps b o ys) h !! l = Some v).
    { intros l v Hin. rewrite overwrite_out; [apply Howned, elem_of_app; auto|].
      rewrite Hkeys byte_ps_keys Hlen. change (l ∉ errno_keys b o).
      apply Hapart. apply list_elem_of_fmap. exists (l, v). auto. }
    assert (Hafter : all_agree m' after) by (eapply Hreplace; eauto).
    destruct (S.fclose_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as [(born & q & info & final & n & Hxs & _ & _ & _ & Hn & _ & _ & _ & _ & _ & Hvalues)
      |(why & Hbad & _)]; [|discriminate Hbad]. injection Hvalues as Hvalues.
    exists n, ys. split; [exact Hvalues|]. split; [destruct Hn as [-> | ->]; unfold stream_eof; lia|].
    split; [exact Hys|]. split; [rewrite !fmap_app Hsame Hkeys; reflexivity|].
    rewrite overwrite_app. split.
    + intros l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin|[_ Hold]];
        [exact (all_agree_elem _ _ _ _ Hafter Hin)|exact (Ha' l v Hold)].
    + split; [exact Hd'|]. split; [exact Hr'|].
      destruct Hwi' as (Hready & He & Hroots & Hrel & Hoff).
      assert (Hlookup : memory_keys_from (overwrite after (overwrite (byte_ps b o ys) h))
          (overwrite (byte_ps b o ys) h)).
      { intros l v Hl _. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin|[_ Hold]]; [|eauto].
        assert (Hkey : l ∈ before.*1).
        { rewrite <- Hsame. apply list_elem_of_fmap. exists (l, v). auto. }
        apply list_elem_of_fmap in Hkey as ([l0 old] & E & Hinold). simpl in E. subst l0.
        exists old. exact (Hbefore l old Hinold). }
      split; [exact Hready|]. split; [exact He|]. split; [|split].
      * intros root a Hin Hspan (l & v & reg & Hl & Hmem & Hlive & Hrange).
        destruct (Hlookup l v Hl Hmem) as [old Hold]. apply (Hroots root a Hin Hspan).
        exists l, old, reg. exact (conj Hold (conj Hmem (conj Hlive Hrange))).
      * intros base l v Hin Hl Hmem. destruct (Hlookup l v Hl Hmem) as [old Hold].
        exact (Hrel base l old Hin Hold Hmem).
      * intros l v Hl Hnot. destruct l as [base|base off|base off|key]; try exact I.
        all: destruct (Hlookup _ _ Hl I) as [old Hold]; exact (Hoff _ old Hold Hnot).
Qed.

End LibcErrnoLogicOn.

(** Nonvacuity through the actual HelloClose logic instance. This heap
    really owns errno, so the previous all-write-roots frame rejects it. *)
Module HelloErrnoChecks.
Module H := HelloClose InterpRuntime.
Module LG := H.LG.
Module E := LibcErrnoLogicOn InterpRuntime LG.
Module C := LibcStreamsOn InterpRuntime LG.L.M.
Module F := LibcStreamChecks.

Definition heap : gmap piece pval := list_to_map (byte_ps 5120 0 [0; 0; 0; 0]).

Lemma regions : forall b reg, object_region b (m_regions conversion_mem) = Some reg ->
  (b = 1024 /\ reg = mkRegion 1024 1056 GlobalData Live) \/
  (b = 2048 /\ reg = mkRegion 2048 2056 Stack Live) \/
  (b = 3072 /\ reg = mkRegion 3072 3080 Stack Live) \/
  (b = 4096 /\ reg = mkRegion 4096 4104 GlobalData Live) \/
  (b = 5120 /\ reg = mkRegion 5120 5128 Heap Live).
Proof.
  intros b reg Hreg. cbn [conversion_mem m_regions object_region r_base] in Hreg.
  repeat destruct (_ =? _) eqn:? in Hreg; try discriminate;
    injection Hreg as <-;
    repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end;
    subst; auto 10.
Qed.

Lemma disjoint : live_disjoint conversion_mem.
Proof.
  intros b1 r1 b2 r2 [E1 L1] [E2 L2] Hne.
  apply regions in E1, E2.
  repeat destruct E1 as [E1|E1]; destruct E1 as [-> ->];
    repeat destruct E2 as [E2|E2]; destruct E2 as [-> ->]; simpl in *; lia.
Qed.

Lemma ready : InterpRuntime.ready InterpRuntime.start conversion_mem.
Proof.
  split; [change (0 < 4294967296 <= 281474976710656); lia|]. split.
  - intros b reg E. apply regions in E.
    change (0 <= b < 4294967296 /\ r_end reg <= 4294967296 /\
      (r_life reg = Freed -> r_end reg = b)).
    repeat destruct E as [E|E]; destruct E as [-> ->]; simpl; intuition (try discriminate; lia).
  - intros a Ha. change (4294967296 <= a) in Ha.
    cbn [conversion_mem m_bytes m_aux].
    repeat match goal with |- context [a =? ?b] =>
      destruct (Z.eqb_spec a b); [subst; lia|] end; auto.
Qed.

Lemma heap_agrees : agrees conversion_mem heap.
Proof.
  intros l v Hl. apply elem_of_list_to_map_2 in Hl.
  eapply all_agree_elem; [|exact Hl].
  change (all_agree conversion_mem (byte_ps 5120 0 (errno_bytes conversion_mem 5120 0))).
  apply errno_bytes_agree. exact (proj1 (proj2 (proj2 (F.ready true)))).
Qed.

Lemma heap_wi : libc_errno_wi (fun _ _ => True) (file_handle F.out_file)
    5120 0 conversion_mem (F.world true) heap.
Proof.
  split; [apply F.ready|]. split; [reflexivity|].
  split; [intros root a []|]. split; [intros base l v []|].
  intros l v Hl Hnot. apply elem_of_list_to_map_2 in Hl. exfalso. apply Hnot.
  change (l ∈ (byte_ps 5120 0 [0; 0; 0; 0]).*1).
  apply list_elem_of_fmap. exists (l, v). auto.
Qed.

Example owned_errno_query :
  LG.L.M.E.invoke (fpending_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (file_handle F.out_file)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 7]) InterpRuntime.start conversion_mem (F.world true) /\
  agrees conversion_mem heap /\
  libc_errno_wi (fun _ _ => True) (file_handle F.out_file) 5120 0
    conversion_mem (F.world true) heap.
Proof.
  assert (Hcall : LG.L.M.E.invoke (fpending_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (file_handle F.out_file)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 7]) InterpRuntime.start conversion_mem (F.world true)).
  { apply C.fpending_unchanged with (file := F.out_file).
    - split; [left; reflexivity|]. exists (Const 0). reflexivity.
    - apply F.ready.
    - reflexivity. }
  split; [exact Hcall|].
  destruct (E.query_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) (file_handle F.out_file) 5120 0 _ _ _ _ _ _ _ _ _ _ _ heap
    (or_intror eq_refl) Hcall heap_agrees) as (Ha & _ & _ & Hw).
  - exact disjoint.
  - exact ready.
  - exact heap_wi.
  - auto.
Qed.

Example old_all_roots_frame_rejects_owned_errno :
  ~ libc_stream_wi (fun _ _ => True) (file_handle F.out_file)
    conversion_mem (F.world true) heap.
Proof.
  intros (_ & Hroots & _).
  apply (Hroots (mkSpan (mkPtr 5120 (Obj 5120)) 4) 5123).
  - left. reflexivity.
  - unfold span_contains. simpl. lia.
  - exists (PByte 5120 3), (VByte 0), (mkRegion 5120 5128 Heap Live).
    split.
    + unfold heap. apply elem_of_list_to_map_1.
      * change (base.NoDup [PByte 5120 0; PByte 5120 1; PByte 5120 2; PByte 5120 3]).
        repeat (apply base.NoDup_cons_2; [set_solver|]). apply base.NoDup_nil_2.
      * apply list_elem_of_In. simpl. auto 10.
    + split; [exact I|]. split; [split; reflexivity|simpl; lia].
Qed.

End HelloErrnoChecks.
