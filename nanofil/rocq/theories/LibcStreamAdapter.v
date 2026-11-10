(** World-owned callback snapshots, separate from locale string names.
    Main's output rules do not own/update these snapshots: callers must
    allocate or transfer them at callback entry. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Identity ExternalCalls
  ExternalMachine Stdio Shutdown Streams Libc LibcStreams Pieces Heap ContractFrame
  Logic StringLogic LentLogic LibcStreamLogic LibcErrnoLogic LibcStreamTokens.
Open Scope Z_scope.
Open Scope list_scope.

(** A stable native handle and a reserved ghost key. The life region is
    separate from the mutable observations of FILE state. *)
Record stream_token : Type := mkStreamToken {
  token_handle : ptr;
  token_base : Z;
  token_region : region;
  token_key : Z
}.

Definition stream_ps (d : stream_token) (pending : Z) (fifo : list Z) : list (piece * pval) :=
  [(PLive (token_base d), VLive (token_region d));
   (PName (token_key d), VStream (token_handle d) (Some (pending, fifo)))].

(** The actual argument is recorded, including its capability. This
    permission observes openness, not a fixed pending count or FIFO.
    Use distinct descriptors/keys from exact snapshots; the native life
    piece is still exclusive and cannot be owned twice. *)
Definition open_permission_ps (d : stream_token) (p : ptr) : list (piece * pval) :=
  [(PLive (token_base d), VLive (token_region d));
   (PName (token_key d), VStreamOpen p)].

(** Even the fallback contains the actual argument, never an empty
    assertion or an unchanged stdout token for an unrelated pointer. *)
Definition permission_descriptor (out err : stream_token) (p : ptr) : stream_token :=
  if same_file p (token_handle out) then out else err.

Definition permission_ps (out err : stream_token) (p : ptr) : list (piece * pval) :=
  open_permission_ps (permission_descriptor out err p) p.

(** Ordinary completed closure does not freeze orientation or error.
    A resource prefix is not enough to establish this observation. *)
Definition closed_ps (d : stream_token) : list (piece * pval) :=
  [(PLive (token_base d), VLive (token_region d));
   (PName (token_key d), VStream (token_handle d) None)].

Definition stream_observation (w : libc_world) (p : ptr)
    (snapshot : option (Z * list Z)) : Prop :=
  match snapshot with
  | Some (pending, fifo) => exists info, libc_stream_at w p = Some info /\
      stream_pending info = pending /\ outstanding (stream_protocol info) = fifo
  | None => libc_stream_at w p = None /\ outstanding (libc_stream_state w p) = []
  end.

(** Absent keys impose no snapshot requirement. A present key rejects
    wrong handles, malformed values and stale observations. This reads
    the current heap, never a fixed callback-entry snapshot. *)
Definition stream_current (d : stream_token) (w : libc_world) (h : gmap piece pval) : Prop :=
  match h !! PName (token_key d) with
  | None => True
  | Some (VStream p snapshot) => p = token_handle d /\ stream_observation w p snapshot
  | Some (VStreamOpen p) => p = token_handle d /\ exists info, libc_stream_at w p = Some info
  | Some _ => False
  end.

(** Both kinds preserve their meaning when the views they actually
    observe are unchanged. Open-only permissions do not observe FIFO. *)
Lemma stream_current_views : forall d w w' h,
  libc_stream_at w' (token_handle d) = libc_stream_at w (token_handle d) ->
  libc_stream_state w' (token_handle d) = libc_stream_state w (token_handle d) ->
  stream_current d w h -> stream_current d w' h.
Proof.
  intros d w w' h Hlookup Hstate Hc. unfold stream_current in *.
  destruct (h !! PName (token_key d)) as [v|]; [|exact I].
  destruct v; try contradiction.
  - destruct Hc as [-> Hobs]. split; [reflexivity|].
    unfold stream_observation in *. destruct pending as [[physical fifo]|];
      rewrite Hlookup; [exact Hobs|rewrite Hstate; exact Hobs].
  - destruct Hc as [-> Hopen]. split; [reflexivity|]. rewrite Hlookup. exact Hopen.
Qed.

(** Keys below the codec key (-1) do not overlap locale categories.
    Actual freshness against other adapters is still required by allocation. *)
Definition token_wf (d : stream_token) : Prop :=
  ptr_cap (token_handle d) = Obj (token_base d) /\ token_key d < -1.

Definition stream_tokens_wi rep out err b o m w (h : gmap piece pval) : Prop :=
  token_wf out /\ token_wf err /\ token_base out <> token_base err /\ token_key out <> token_key err /\
  libc_stdout w = token_handle out /\ libc_stderr w = token_handle err /\
  stream_current out w h /\ stream_current err w h /\
  forall d, d = out \/ d = err ->
    libc_errno_wi rep (token_handle d) b o m w
      (stream_data_heap (token_base out) (token_base err) h) /\
    ids_apart (libc_stream_releases w (token_handle d)) h.

Lemma stream_closed_keys : forall d pending fifo,
  (closed_ps d).*1 = (stream_ps d pending fifo).*1.
Proof. reflexivity. Qed.

Lemma stream_ps_agree : forall m d pending fifo,
  live_at m (token_base d) (token_region d) -> all_agree m (stream_ps d pending fifo).
Proof. intros. split; [exact H|]. split; exact I. Qed.

Lemma closed_ps_agree : forall m d,
  live_at m (token_base d) (token_region d) -> all_agree m (closed_ps d).
Proof. intros. split; [exact H|]. split; exact I. Qed.

Lemma stream_open_current : forall d w h pending fifo,
  stream_current d w h ->
  (forall l v, (l, v) ∈ stream_ps d pending fifo -> h !! l = Some v) ->
  exists info, libc_stream_at w (token_handle d) = Some info /\
    stream_pending info = pending /\ outstanding (stream_protocol info) = fifo.
Proof.
  intros d w h pending fifo Hcurrent Howned.
  assert (Hl : h !! PName (token_key d) = Some (VStream (token_handle d) (Some (pending, fifo)))).
  { apply Howned. unfold stream_ps. set_solver. }
  unfold stream_current in Hcurrent. rewrite Hl in Hcurrent. exact (proj2 Hcurrent).
Qed.

Lemma stream_closed_current : forall d w h,
  stream_current d w h ->
  (forall l v, (l, v) ∈ closed_ps d -> h !! l = Some v) ->
  libc_stream_at w (token_handle d) = None /\ outstanding (libc_stream_state w (token_handle d)) = [].
Proof.
  intros d w h Hcurrent Howned.
  assert (Hl : h !! PName (token_key d) = Some (VStream (token_handle d) None)).
  { apply Howned. unfold closed_ps. set_solver. }
  unfold stream_current in Hcurrent. rewrite Hl in Hcurrent. exact (proj2 Hcurrent).
Qed.

Lemma stream_permission_current : forall d p w h,
  stream_current d w h ->
  (forall l v, (l, v) ∈ open_permission_ps d p -> h !! l = Some v) ->
  p = token_handle d /\ exists info, libc_stream_at w p = Some info.
Proof.
  intros d p w h Hcurrent Howned.
  assert (Hl : h !! PName (token_key d) = Some (VStreamOpen p)).
  { apply Howned. unfold open_permission_ps. apply elem_of_cons. right. apply elem_of_cons. left. reflexivity. }
  unfold stream_current in Hcurrent. rewrite Hl in Hcurrent. exact Hcurrent.
Qed.

Lemma permission_selected : forall out err p,
  permission_descriptor out err p = out \/ permission_descriptor out err p = err.
Proof. intros. unfold permission_descriptor. destruct (same_file p (token_handle out)); auto. Qed.

(** Pure owned lookups already reject unknown and wrong-capability
    arguments, as required by HelloClose's pointer-universal premises. *)
Lemma permission_known : forall rep out err b o p m w h,
  stream_tokens_wi rep out err b o m w h ->
  (forall l v, (l, v) ∈ permission_ps out err p -> h !! l = Some v) ->
  p = token_handle (permission_descriptor out err p) /\
    (p = token_handle out \/ p = token_handle err).
Proof.
  intros rep out err b o p m w h (_ & _ & _ & _ & _ & _ & Ho & He & _) Hl.
  assert (Hc : stream_current (permission_descriptor out err p) w h).
  { destruct (permission_selected out err p) as [-> | ->]; assumption. }
  destruct (stream_permission_current _ _ _ _ Hc Hl) as [Hp _].
  split; [exact Hp|]. rewrite Hp. destruct (permission_selected out err p) as [-> | ->]; auto.
Qed.

(** Recording independently live handles and CURRENT observations preserves
    the complete entry envelope. It does not recover unavailable fragments
    or change the world interpretation used by an existing WP. *)
Lemma stream_entry_frame : forall rep out err b o m w h op oq ep eq,
  agrees m h -> stream_tokens_wi rep out err b o m w h ->
  live_at m (token_base out) (token_region out) ->
  live_at m (token_base err) (token_region err) ->
  stream_observation w (token_handle out) (Some (op, oq)) ->
  stream_observation w (token_handle err) (Some (ep, eq)) ->
  let h' := overwrite (stream_ps out op oq ++ stream_ps err ep eq) h in
  agrees m h' /\ stream_tokens_wi rep out err b o m w h'.
Proof.
  intros rep out err b o m w h op oq ep eq Ha
    (Howf & Hewf & Hbase & Hkey & Hout & Herr & _ & _ & Hprivate)
    Hol Hel Hoo Heo h'.
  assert (Hdata : memory_keys_from
    (stream_data_heap (token_base out) (token_base err) h')
    (stream_data_heap (token_base out) (token_base err) h)).
  { intros l v Hl Hmem. apply stream_data_lookup in Hl as (Hl & Hno & Hne).
    unfold h' in Hl. apply lookup_overwrite in Hl as [Hin|[_ Hold]].
    - apply list_elem_of_In in Hin. cbn [stream_ps app] in Hin.
      destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; contradiction.
    - exists v. rewrite stream_data_lookup_ne; assumption. }
  split.
  { intros l v Hl. unfold h' in Hl. apply lookup_overwrite in Hl as [Hin|[_ Hold]];
      [|exact (Ha l v Hold)].
    eapply all_agree_elem; [|exact Hin]. apply all_agree_app.
    split; apply stream_ps_agree; assumption. }
  split; [exact Howf|]. split; [exact Hewf|]. split; [exact Hbase|]. split; [exact Hkey|].
  split; [exact Hout|]. split; [exact Herr|]. split.
  { unfold stream_current, h'. cbn [stream_ps app overwrite fst snd].
    rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_eq. exact (conj eq_refl Hoo). }
  split.
  { unfold stream_current, h'. cbn [stream_ps app overwrite fst snd].
    rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_ne; [|congruence].
    rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_eq. exact (conj eq_refl Heo). }
  intros d Hd. destruct (Hprivate d Hd) as [Hwi Hrel].
  split; [eapply errno_wi_heap; eauto|]. intros base l v Hin Hl Hmem.
  unfold h' in Hl. apply lookup_overwrite in Hl as [Hnew|[_ Hold]];
    [|exact (Hrel base l v Hin Hold Hmem)].
  apply list_elem_of_In in Hnew. cbn [stream_ps app] in Hnew.
  destruct Hnew as [E|[E|[E|[E|[]]]]]; injection E as <- <-; try contradiction.
  - intros E. subst base. eapply libc_handle_not_released;
      [exact (proj1 Hwi)|left; reflexivity| |exact Hin]. rewrite Hout. exact (proj1 Howf).
  - intros E. subst base. eapply libc_handle_not_released;
      [exact (proj1 Hwi)|right; reflexivity| |exact Hin]. rewrite Herr. exact (proj1 Hewf).
Qed.

Section snapshot_allocation.
Context `{!gen_heapGS piece pval Σ}.

(** Fresh ghost recording is not native allocation: both live_at facts
    and both current observations are independent premises. Freshness is
    against the authoritative heap, so no existing life is duplicated. *)
Lemma stream_entry_alloc rep out err b o m w h op oq ep eq :
  agrees m h -> stream_tokens_wi rep out err b o m w h ->
  live_at m (token_base out) (token_region out) ->
  live_at m (token_base err) (token_region err) ->
  stream_observation w (token_handle out) (Some (op, oq)) ->
  stream_observation w (token_handle err) (Some (ep, eq)) ->
  (forall l v, (l, v) ∈ stream_ps out op oq ++ stream_ps err ep eq -> h !! l = None) ->
  gen_heap_interp h ==∗
    gen_heap_interp (overwrite (stream_ps out op oq ++ stream_ps err ep eq) h) ∗
    pts (stream_ps out op oq) ∗ pts (stream_ps err ep eq) ∗
    ⌜agrees m (overwrite (stream_ps out op oq ++ stream_ps err ep eq) h) /\
      stream_tokens_wi rep out err b o m w
        (overwrite (stream_ps out op oq ++ stream_ps err ep eq) h)⌝.
Proof.
  intros Ha Hw Hol Hel Hoo Heo Hfresh. iIntros "Hh".
  destruct Hw as (Howf & Hewf & Hbase & Hkey & Hrest) eqn:E.
  iMod (pts_alloc h (stream_ps out op oq ++ stream_ps err ep eq) with "Hh") as "[Hh Hps]".
  - clear -Hbase Hkey. cbn [stream_ps app fmap fst]. repeat constructor; set_solver.
  - exact Hfresh.
  - rewrite pts_app. iDestruct "Hps" as "[Ho He]". iModIntro. iFrame.
    iPureIntro. eapply stream_entry_frame; eauto.
Qed.

(** Callback entry allocates the reserved snapshot key, while retaining
    an already owned life piece. Neither the life nor a fresh ghost
    resource can be fabricated by the pure interpretation. *)
Lemma stream_snapshot_alloc d pending fifo w h :
  h !! PName (token_key d) = None ->
  stream_observation w (token_handle d) (Some (pending, fifo)) ->
  gen_heap_interp h ∗ pts [(PLive (token_base d), VLive (token_region d))] ==∗
    gen_heap_interp (<[PName (token_key d) := VStream (token_handle d) (Some (pending, fifo))]> h) ∗
    pts (stream_ps d pending fifo) ∗
    ⌜stream_current d w (<[PName (token_key d) := VStream (token_handle d) (Some (pending, fifo))]> h)⌝.
Proof.
  intros Hfresh Hobs. iIntros "[Hh Hlife]".
  iMod (gen_heap_alloc _ (PName (token_key d))
    (VStream (token_handle d) (Some (pending, fifo))) with "Hh") as "(Hh & Hname & _)";
    [exact Hfresh|].
  iModIntro. iSplitL "Hh"; [iExact "Hh"|]. iSplitL "Hlife Hname".
  - rewrite /stream_ps /pts /=. iDestruct "Hlife" as "[Hlife _]". iFrame.
  - iPureIntro. unfold stream_current. rewrite lookup_insert_eq. exact (conj eq_refl Hobs).
Qed.

End snapshot_allocation.

(** The other registered stream keeps its observable state and private
    inventory. Distinct addresses rule out stdout-priority aliasing. *)
Lemma stream_other_frame : forall p q w w',
  ((p = libc_stdout w /\ q = libc_stderr w) \/
   (p = libc_stderr w /\ q = libc_stdout w)) ->
  ptr_addr (libc_stdout w) <> ptr_addr (libc_stderr w) ->
  libc_stream_frame p w w' ->
  libc_file_at w' q = libc_file_at w q /\
  libc_stream_at w' q = libc_stream_at w q /\
  libc_stream_state w' q = libc_stream_state w q.
Proof.
  intros p q w w' Hwhich Hdistinct
    (Hout & Herr & _ & _ & _ & _ & _ & _ & Hother).
  assert (Hne : same_file (libc_stderr w) (libc_stdout w) = false).
  { unfold same_file. apply andb_false_iff. left. apply Z.eqb_neq. congruence. }
  destruct Hwhich as [[-> ->]|[-> ->]].
  - rewrite same_file_refl in Hother. destruct Hother as (Hfile & Hopen & Hstate).
    assert (Hlookup : libc_file_at w' (libc_stderr w) = libc_file_at w (libc_stderr w)).
    { unfold libc_file_at. rewrite Hout Herr Hne same_file_refl Hopen Hfile. reflexivity. }
    assert (Hprotocol : libc_stream_state w' (libc_stderr w) = libc_stream_state w (libc_stderr w)).
    { unfold libc_stream_state. rewrite Hout Herr Hne same_file_refl Hstate. reflexivity. }
    split; [exact Hlookup|]. split; [|exact Hprotocol].
    unfold libc_stream_at. rewrite Hlookup Hout Hprotocol. reflexivity.
  - rewrite Hne in Hother. destruct Hother as (Hfile & Hopen & Hstate).
    assert (Hlookup : libc_file_at w' (libc_stdout w) = libc_file_at w (libc_stdout w)).
    { unfold libc_file_at. rewrite Hout same_file_refl Hopen Hfile. reflexivity. }
    assert (Hprotocol : libc_stream_state w' (libc_stdout w) = libc_stream_state w (libc_stdout w)).
    { unfold libc_stream_state. rewrite Hout same_file_refl Hstate. reflexivity. }
    split; [exact Hlookup|]. split; [|exact Hprotocol].
    unfold libc_stream_at. rewrite Hlookup Hout Hprotocol. reflexivity.
Qed.

Module LibcStreamAdapterOn (R : Runtime) (LG : StreamFrameLogic R).
Module M := LG.L.M.
Module T := LibcStreamTokensOn R LG.

(** Query contracts permit no allocation; in particular delegation
    cannot add a newly born release identity to either FILE. *)
Lemma effects_no_alloc : forall sources roots releases s m born s' m' born',
  M.E.effects sources roots releases (fun _ _ => False) s m born s' m' born' ->
  born' = born.
Proof.
  intros sources roots releases s m born s' m' born' He.
  induction He; [reflexivity|exact IHHe|contradiction].
Qed.

(** Both mirrors and both private-memory frames survive either query.
    No unchanged-memory premise rules out the native locking writes. *)
Theorem query_frame : forall rep requests wide out err b o d spec r args
    s m w trace ending s' m' w' h,
  d = out \/ d = err ->
  (spec = ferror_contract (libc_stream_model rep requests wide) \/
   spec = fpending_contract (libc_stream_model rep requests wide)) ->
  M.E.invoke spec r args [WPtr (token_handle d)] s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> stream_tokens_wi rep out err b o m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ stream_tokens_wi rep out err b o m' w' h.
Proof.
  intros rep requests wide out err b o d spec r args s m w trace ending s' m' w' h
    Hd Hspec Hcall Ha Hdis Hr
    (Houtwf & Herrwf & Hbase & Hkey & Hout & Herr & Houtcurrent & Herrcurrent & Hprivate).
  destruct (Hprivate d Hd) as [Hselected Hrelease].
  destruct (T.query_frame rep requests wide (token_base out) (token_base err)
    (token_handle d) b o spec r args s m w trace ending s' m' w' h
    Hspec Hcall Ha Hdis Hr Hselected) as (Ha' & Hdis' & Hr' & Hselected').
  split; [exact Ha'|]. split; [exact Hdis'|]. split; [exact Hr'|].
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [_ Hpers].
  assert (Hborn : born = []).
  { destruct Hp as [He _]. destruct Hspec as [-> | ->]; eapply effects_no_alloc; exact He. }
  subst born.
  assert (Hprefix : query_prefix (libc_stream_model rep requests wide)
    [WPtr (token_handle d)] m w [] trace m' w').
  { destruct Hspec as [-> | ->]; exact (proj2 Hp). }
  destruct Hprefix as (p & info & Hxs & Hinfo & Hopen & Hframe & Hdelegate & _).
  injection Hxs as <-.
  cbn [stream_open stream_at stream_state_at stream_rep libc_stream_model] in Hinfo, Hopen.
  assert (Hready' := proj1 Hopen).
  assert (Hdistinct : ptr_addr (libc_stdout w) <> ptr_addr (libc_stderr w)).
  { destruct (proj1 Hselected) as (_ & _ & _ & _ & _ & _ & _ & _ & Hdistinct & _).
    exact Hdistinct. }
  assert (Hother : forall q, (q = out \/ q = err) -> q <> d ->
      libc_file_at w' (token_handle q) = libc_file_at w (token_handle q) /\
      libc_stream_at w' (token_handle q) = libc_stream_at w (token_handle q) /\
      libc_stream_state w' (token_handle q) = libc_stream_state w (token_handle q)).
  { intros q Hq Hne. apply stream_other_frame with (p := token_handle d); [|exact Hdistinct|exact Hframe].
    destruct Hd as [-> | ->]; destruct Hq as [-> | ->]; try contradiction;
      [left|right]; split; congruence. }
  assert (Hchoice : forall q, q = out \/ q = err -> q = d \/ q <> d).
  { intros q Hq. destruct Hd as [-> | ->]; destruct Hq as [-> | ->];
      try (left; reflexivity); right; intros Heq; apply Hbase; congruence. }
  assert (Hviews : forall q, q = out \/ q = err ->
      libc_stream_at w' (token_handle q) = libc_stream_at w (token_handle q) /\
      libc_stream_state w' (token_handle q) = libc_stream_state w (token_handle q)).
  { intros q Hq. destruct (Hchoice q Hq) as [->|Hne].
    - split; [rewrite Hinfo; exact (proj1 (proj2 Hopen))|].
      pose proof (proj1 (proj2 (proj2 Hopen))) as Hprotocol.
      change (stream_protocol info = libc_stream_state w' (token_handle d)) in Hprotocol.
      rewrite <- Hprotocol.
      unfold libc_stream_at in Hinfo.
      destruct (libc_file_at w (token_handle d)); [injection Hinfo as <-; reflexivity|discriminate].
    - exact (proj2 (Hother q Hq Hne)). }
  assert (Hcurrent : forall q, q = out \/ q = err -> stream_current q w' h).
  { intros q Hq. assert (Hc : stream_current q w h) by (destruct Hq as [-> | ->]; assumption).
    destruct (Hviews q Hq) as [Hlookup Hstate].
    eapply stream_current_views; eauto. }
  split; [exact Houtwf|]. split; [exact Herrwf|]. split; [exact Hbase|]. split; [exact Hkey|].
  split; [rewrite (proj1 Hframe); exact Hout|].
  split; [rewrite (proj1 (proj2 Hframe)); exact Herr|].
  split; [apply Hcurrent; left; reflexivity|]. split; [apply Hcurrent; right; reflexivity|].
  intros q Hq. destruct (Hchoice q Hq) as [->|Hne].
  - split; [exact Hselected'|]. intros base l v Hin Hl Hmem.
    destruct (proj2 (proj2 Hdelegate) base Hin) as [Hold|Hnil];
      [exact (Hrelease base l v Hold Hl Hmem)|contradiction].
  - destruct (Hother q Hq Hne) as [Hfile _].
    destruct (Hprivate q Hq) as [Hwi Hrel].
    assert (Hroots : libc_stream_aux_roots w' (token_handle q) = libc_stream_aux_roots w (token_handle q))
      by (unfold libc_stream_aux_roots; rewrite Hfile; reflexivity).
    assert (Hrels : libc_stream_releases w' (token_handle q) = libc_stream_releases w (token_handle q))
      by (unfold libc_stream_releases; rewrite Hfile; reflexivity).
    split; [|rewrite Hrels; exact Hrel].
    eapply errno_wi_fixed; [exact Hwi| |exact Hpers|exact Hready'| |exact Hroots|exact Hrels].
    + apply stream_data_agrees. exact Ha.
    + exact (proj1 (proj2 (proj2 (proj2 Hframe)))).
Qed.

(** Only an ordinary return establishes completed closure. Sample all
    four endpoint errno bytes, update the selected name, and retain the
    opposite snapshot and both native lives. This is a pure heap frame;
    updating an owned name in Iris still requires its points-to resource. *)
Theorem close_frame : forall rep requests wide out err b o d r args
    s m w trace values s' m' w' h xs,
  d = out \/ d = err ->
  M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
    r args [WPtr (token_handle d)] s m w trace (CallReturn values) s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> stream_tokens_wi rep out err b o m w h ->
  length xs = 4%nat ->
  (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) ->
  exists ys, length ys = 4%nat /\ (byte_ps b o ys).*1 = (byte_ps b o xs).*1 /\
    agrees m' (<[PName (token_key d) := VStream (token_handle d) None]>
      (overwrite (byte_ps b o ys) h)) /\ live_disjoint m' /\ R.ready s' m' /\
    stream_tokens_wi rep out err b o m' w'
      (<[PName (token_key d) := VStream (token_handle d) None]>
        (overwrite (byte_ps b o ys) h)).
Proof.
  intros rep requests wide out err b o d r args s m w trace values s' m' w' h xs
    Hd Hcall Ha Hdis Hr
    (Houtwf & Herrwf & Hbase & Hkey & Hout & Herr & Houtcurrent & Herrcurrent & Hprivate)
    Hlen Howned.
  destruct (Hprivate d Hd) as [Hselected Hrelease].
  destruct (T.close_frame rep requests wide (token_base out) (token_base err)
    (token_handle d) b o r args s m w trace (CallReturn values) s' m' w' h xs
    ltac:(rewrite Hout; exact (proj1 Houtwf))
    ltac:(rewrite Herr; exact (proj1 Herrwf)) Hcall Ha Hdis Hr Hselected Hlen Howned)
    as (ys & Hys & Hkeys & Ha' & Hdis' & Hr' & Hselected').
  set (h0 := overwrite (byte_ps b o ys) h) in *.
  set (h1 := <[PName (token_key d) := VStream (token_handle d) None]> h0).
  assert (Hkeys0 : memory_keys_from h0 h).
  { intros l v Hl Hmem. unfold h0 in Hl.
    destruct (lookup_overwrite _ _ _ _ Hl) as [Hin|[_ Hold]]; [|eauto].
    assert (Hkey0 : l ∈ (byte_ps b o xs).*1).
    { rewrite <- Hkeys. apply list_elem_of_fmap. exists (l, v). auto. }
    apply list_elem_of_fmap in Hkey0 as ([l0 old] & E & Hinold). simpl in E. subst l0.
    exists old. exact (Howned l old Hinold). }
  assert (Hkeys1 : memory_keys_from h1 h0).
  { intros l v Hl Hmem. unfold h1 in Hl.
    apply lookup_insert_Some in Hl as [[He Hv]|[_ Hold]]; [subst l; contradiction|eauto]. }
  assert (Hdata1 : memory_keys_from
      (stream_data_heap (token_base out) (token_base err) h1)
      (stream_data_heap (token_base out) (token_base err) h0)).
  { intros l v Hl Hmem. apply stream_data_lookup in Hl as (Hl & Hno & Hne).
    destruct (Hkeys1 l v Hl Hmem) as [old Hold].
    exists old. rewrite stream_data_lookup_ne; assumption. }
  assert (Hdata0 : memory_keys_from
      (stream_data_heap (token_base out) (token_base err) h1)
      (stream_data_heap (token_base out) (token_base err) h)).
  { intros l v Hl Hmem. apply stream_data_lookup in Hl as (Hl & Hno & Hne).
    destruct (Hkeys1 l v Hl Hmem) as [old Hold].
    destruct (Hkeys0 l old Hold Hmem) as [entry Hentry].
    exists entry. rewrite stream_data_lookup_ne; assumption. }
  exists ys. split; [exact Hys|]. split; [exact Hkeys|]. split.
  { intros l v Hl. unfold h1 in Hl.
    apply lookup_insert_Some in Hl as [[He Hv]|[_ Hold]];
      [subst l v; exact I|exact (Ha' l v Hold)]. }
  split; [exact Hdis'|]. split; [exact Hr'|].
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [_ Hpers].
  destruct Hp as (_ & p & info & final & Hxs & _ & _ & _ & Hready' & Hframe & _).
  injection Hxs as <-.
  destruct (T.EL.S.fclose_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as [(born0 & p & info0 & final0 & n & Hxs & _ & Hsettle & Hstate & _ & Hclosed & _)
      |(why & Hbad & _)]; [|discriminate Hbad].
  injection Hxs as <-.
  change (libc_stream_at w' (token_handle d) = None) in Hclosed.
  assert (Hfifo : outstanding (libc_stream_state w' (token_handle d)) = []).
  { change (libc_stream_state w' (token_handle d) = final0) in Hstate.
    rewrite Hstate. eapply stream_settlement_complete; exact Hsettle. }
  assert (Hdistinct : ptr_addr (libc_stdout w) <> ptr_addr (libc_stderr w)).
  { destruct (proj1 Hselected) as (_ & _ & _ & _ & _ & _ & _ & _ & Hdistinct & _).
    exact Hdistinct. }
  assert (Hchoice : forall q, q = out \/ q = err -> q = d \/ q <> d).
  { intros q Hq. destruct Hd as [-> | ->]; destruct Hq as [-> | ->];
      try (left; reflexivity); right; intros Heq; apply Hbase; congruence. }
  assert (Hother : forall q, (q = out \/ q = err) -> q <> d ->
      libc_file_at w' (token_handle q) = libc_file_at w (token_handle q) /\
      libc_stream_at w' (token_handle q) = libc_stream_at w (token_handle q) /\
      libc_stream_state w' (token_handle q) = libc_stream_state w (token_handle q)).
  { intros q Hq Hne. apply stream_other_frame with (p := token_handle d); [|exact Hdistinct|exact Hframe].
    destruct Hd as [-> | ->]; destruct Hq as [-> | ->]; try contradiction;
      [left|right]; split; congruence. }
  assert (Hcurrent : forall q, q = out \/ q = err -> stream_current q w' h1).
  { intros q Hq. destruct (Hchoice q Hq) as [->|Hne].
    - unfold stream_current, h1. rewrite lookup_insert_eq.
      exact (conj eq_refl (conj Hclosed Hfifo)).
    - assert (Hkeyne : token_key d <> token_key q).
      { destruct Hd as [-> | ->]; destruct Hq as [-> | ->]; congruence. }
      assert (Hc : stream_current q w h) by (destruct Hq as [-> | ->]; assumption).
      destruct (Hother q Hq Hne) as (_ & Hlookup & Hprotocol).
      pose proof (stream_current_views q w w' h Hlookup Hprotocol Hc) as Hafter.
      unfold stream_current in Hafter |- *. unfold h1. rewrite lookup_insert_ne; [|congruence].
      unfold h0. rewrite overwrite_out.
      + exact Hafter.
      + rewrite byte_ps_keys. intros Hin. apply list_elem_of_fmap in Hin as (i & E & _).
        discriminate E. }
  split; [exact Houtwf|]. split; [exact Herrwf|]. split; [exact Hbase|]. split; [exact Hkey|].
  split; [rewrite (proj1 Hframe); exact Hout|].
  split; [rewrite (proj1 (proj2 Hframe)); exact Herr|].
  split; [apply Hcurrent; left; reflexivity|]. split; [apply Hcurrent; right; reflexivity|].
  intros q Hq. destruct (Hchoice q Hq) as [->|Hne].
  - split; [eapply errno_wi_heap; [exact Hselected'|exact Hdata1]|].
    unfold libc_stream_at in Hclosed. unfold libc_stream_releases.
    destruct (libc_file_at w' (token_handle d)); [discriminate Hclosed|].
    intros base l v Hin. contradiction.
  - destruct (Hother q Hq Hne) as [Hfile _].
    destruct (Hprivate q Hq) as [Hwi Hrel].
    assert (Hroots : libc_stream_aux_roots w' (token_handle q) = libc_stream_aux_roots w (token_handle q))
      by (unfold libc_stream_aux_roots; rewrite Hfile; reflexivity).
    assert (Hrels : libc_stream_releases w' (token_handle q) = libc_stream_releases w (token_handle q))
      by (unfold libc_stream_releases; rewrite Hfile; reflexivity).
    split.
    + eapply errno_wi_heap; [|exact Hdata0].
      eapply errno_wi_fixed; [exact Hwi| |exact Hpers|exact Hready'| |exact Hroots|exact Hrels].
      * apply stream_data_agrees. exact Ha.
      * exact (proj1 (proj2 (proj2 (proj2 Hframe)))).
    + rewrite Hrels. intros base l v Hin Hl Hmem.
      destruct (Hkeys1 l v Hl Hmem) as [old Hold].
      destruct (Hkeys0 l old Hold Hmem) as [entry Hentry].
      exact (Hrel base l entry Hin Hentry Hmem).
Qed.

(** Token ownership plus the current world interpretation admits the
    concrete libc call; openness is not another consumer assumption. *)
Theorem open_admitted : forall rep requests wide out err b o d pending fifo m w h,
  d = out \/ d = err -> stream_tokens_wi rep out err b o m w h ->
  (forall l v, (l, v) ∈ stream_ps d pending fifo -> h !! l = Some v) ->
  stream_call_pre (libc_stream_model rep requests wide) [WPtr (token_handle d)] m w.
Proof.
  intros rep requests wide out err b o d pending fifo m w h Hd
    (_ & _ & _ & _ & _ & _ & Hout & Herr & Hprivate) Howned.
  pose proof (proj1 (proj1 (Hprivate d Hd))) as Hready.
  assert (Hcurrent : stream_current d w h) by (destruct Hd as [-> | ->]; assumption).
  destruct (stream_open_current d w h pending fifo Hcurrent Howned) as (info & Hinfo & _).
  unfold libc_stream_at in Hinfo. destruct (libc_file_at w (token_handle d)) as [file|] eqn:Hfile;
    [eapply libc_stream_admitted; eauto|discriminate].
Qed.

(** This is pointer-universal admission from owned permission pieces,
    not an assumed choice of a registered handle. *)
Theorem permission_admitted : forall rep requests wide out err b o p m w h,
  stream_tokens_wi rep out err b o m w h ->
  (forall l v, (l, v) ∈ permission_ps out err p -> h !! l = Some v) ->
  stream_call_pre (libc_stream_model rep requests wide) [WPtr p] m w.
Proof.
  intros rep requests wide out err b o p m w h Hw Hl.
  pose proof (permission_selected out err p) as Hd.
  destruct Hw as (_ & _ & _ & _ & _ & _ & Ho & He & Hprivate).
  assert (Hc : stream_current (permission_descriptor out err p) w h)
    by (destruct Hd as [-> | ->]; assumption).
  destruct (stream_permission_current _ _ _ _ Hc Hl) as [Hp [info Hinfo]].
  pose proof (proj1 (proj1 (Hprivate _ Hd))) as Hready.
  unfold libc_stream_at in Hinfo. destruct (libc_file_at w p) as [file|] eqn:Hfile;
    [eapply libc_stream_admitted; eauto|discriminate].
Qed.

(** The native representation's poll stability remains an explicit
    realization premise. Everything else follows from unchanged regions. *)
Lemma errno_wi_safepoint : forall rep p b o,
  (forall s m s' m' w, R.safepoint s m s' m' ->
    libc_stream_ready rep m w -> libc_stream_ready rep m' w) ->
  LG.SafepointStable (libc_errno_wi rep p b o).
Proof.
  intros rep p b o Hstable. split. intros s m s' m' w h Hsp
    (Hready & He & Hroots & Hrelease & Hoff).
  split; [eapply Hstable; eauto|]. split; [exact He|]. split; [|split; [exact Hrelease|]].
  - intros root a Hin Hspan (l & v & reg & Hl & Hmem & [E Hlive] & Hrange).
    apply (Hroots root a Hin Hspan). exists l, v, reg.
    split; [exact Hl|]. split; [exact Hmem|]. split; [|exact Hrange].
    split; [|exact Hlive]. rewrite (R.collector_live _ _ _ _ Hsp) in E. exact E.
  - intros l v Hl Hnot. destruct l as [base|base off|base off|key]; try exact I.
    all: intros reg [E Hlive] Ho Hend Hout;
      rewrite (R.collector_live _ _ _ _ Hsp) in E;
      exact (Hoff _ v Hl Hnot reg (conj E Hlive) Ho Hend Hout).
Qed.

Theorem tokens_safepoint : forall rep out err b o,
  (forall s m s' m' w, R.safepoint s m s' m' ->
    libc_stream_ready rep m w -> libc_stream_ready rep m' w) ->
  LG.SafepointStable (stream_tokens_wi rep out err b o).
Proof.
  intros rep out err b o Hstable. split. intros s m s' m' w h Hsp
    (Houtwf & Herrwf & Hbase & Hkey & Hout & Herr & Houtcurrent & Herrcurrent & Hprivate).
  split; [exact Houtwf|]. split; [exact Herrwf|]. split; [exact Hbase|]. split; [exact Hkey|].
  split; [exact Hout|]. split; [exact Herr|]. split; [exact Houtcurrent|]. split; [exact Herrcurrent|].
  intros d Hd. destruct (Hprivate d Hd) as [Hwi Hrelease]. split; [|exact Hrelease].
  pose proof (errno_wi_safepoint rep (token_handle d) b o Hstable) as Hpoll.
  exact (@LG.wi_safepoint _ _ Hpoll s m s' m' w _ Hsp Hwi).
Qed.

End LibcStreamAdapterOn.

(** Discriminating world observations: physical pending is seven, the
    logical FIFO has two bytes, and a completed close consumes both. *)
Module StreamTokenChecks.
Module F := LibcStreamChecks.
Module A := LibcStreamAdapterOn InterpRuntime StreamHandleChecks.LG.

Definition out := mkStreamToken (file_handle F.out_file) 1024
  (mkRegion 1024 1056 GlobalData Live) (-2).
Definition err := mkStreamToken (file_handle F.err_file) 2048
  (mkRegion 2048 2056 Stack Live) (-3).
Definition open_heap : gmap piece pval :=
  <[PName (-2) := VStream (token_handle out) (Some (7, [65; 66]))]>
    (<[PName (-3) := VStream (token_handle err) (Some (3, []))]> StreamHandleChecks.heap).

Example open_snapshots_current :
  stream_current out (F.world true) open_heap /\ stream_current err (F.world true) open_heap.
Proof.
  unfold stream_current, open_heap. cbn [out err token_key].
  rewrite lookup_insert_eq. rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_eq.
  split; (split; [reflexivity|]).
  - exists (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7). repeat split; reflexivity.
  - exists (mkStreamInfo 2 stdout_initial 3). repeat split; reflexivity.
Qed.

Example stale_physical_count_rejected :
  ~ stream_current out (F.world true)
    (<[PName (-2) := VStream (token_handle out) (Some (2, [65; 66]))]> open_heap).
Proof.
  unfold stream_current. cbn [out token_key]. rewrite lookup_insert_eq.
  intros (_ & info & Hinfo & Hpending & _).
  change (Some (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7) = Some info) in Hinfo.
  injection Hinfo as <-. discriminate Hpending.
Qed.

Example stale_fifo_rejected :
  ~ stream_current out (F.world true)
    (<[PName (-2) := VStream (token_handle out) (Some (7, [66; 65]))]> open_heap).
Proof.
  unfold stream_current. cbn [out token_key]. rewrite lookup_insert_eq.
  intros (_ & info & Hinfo & _ & Hfifo).
  change (Some (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7) = Some info) in Hinfo.
  injection Hinfo as <-. discriminate Hfifo.
Qed.

Example completed_closed_snapshot :
  stream_current out (F.world false)
    (<[PName (-2) := VStream (token_handle out) None]> open_heap).
Proof.
  unfold stream_current. cbn [out token_key]. rewrite lookup_insert_eq.
  split; [reflexivity|]. split; reflexivity.
Qed.

Example closed_token_rejected_while_open :
  ~ stream_current out (F.world true)
    (<[PName (-2) := VStream (token_handle out) None]> open_heap).
Proof.
  unfold stream_current. cbn [out token_key]. rewrite lookup_insert_eq.
  intros (_ & Hclosed & _). discriminate Hclosed.
Qed.

Example malformed_snapshot_rejected :
  ~ stream_current out (F.world true) (<[PName (-2) := VName (token_handle out) [65]]> open_heap).
Proof. unfold stream_current. cbn [out token_key]. rewrite lookup_insert_eq. exact (fun H => H). Qed.

(** The entire interpretation has an inhabitant with both open tokens,
    both native lives and owned errno, not merely each mirror alone. *)
Lemma private_lookup : forall l v,
  mem_piece l -> stream_data_heap 1024 2048 open_heap !! l = Some v ->
  HelloErrnoChecks.heap !! l = Some v.
Proof.
  intros l v Hmem Hl. apply stream_data_lookup in Hl as (Hl & Hout & Herr).
  unfold open_heap in Hl.
  apply lookup_insert_Some in Hl as [[He Hv]|[_ Hl]]; [subst l; contradiction|].
  apply lookup_insert_Some in Hl as [[He Hv]|[_ Hl]]; [subst l; contradiction|].
  unfold StreamHandleChecks.heap in Hl.
  apply lookup_insert_Some in Hl as [[He Hv]|[_ Hl]]; [subst l; contradiction|].
  apply lookup_insert_Some in Hl as [[He Hv]|[_ Hl]]; [subst l; contradiction|].
  exact Hl.
Qed.

Lemma full_wi : stream_tokens_wi (fun _ _ => True) out err 5120 0
    conversion_mem (F.world true) open_heap.
Proof.
  assert (Hkeys : forall l v, stream_data_heap 1024 2048 open_heap !! l = Some v ->
      mem_piece l -> l ∈ errno_keys 5120 0).
  { intros l v Hl Hmem. apply (private_lookup l v Hmem) in Hl.
    unfold HelloErrnoChecks.heap in Hl. apply elem_of_list_to_map_2 in Hl.
    change (l ∈ (byte_ps 5120 0 [0; 0; 0; 0]).*1).
    apply list_elem_of_fmap. exists (l, v). auto. }
  split; [split; [reflexivity|simpl; lia]|]. split; [split; [reflexivity|simpl; lia]|].
  split; [discriminate|]. split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (proj1 open_snapshots_current)|]. split; [exact (proj2 open_snapshots_current)|].
  intros d [-> | ->].
  all: split; [|intros base l v Hin; change (In base []) in Hin; contradiction].
  all: split; [apply F.ready|].
  all: split; [reflexivity|].
  all: split; [intros root a Hin; change (In root []) in Hin; contradiction|].
  all: split; [intros base l v Hin; change (In base []) in Hin; contradiction|].
  all: intros l v Hl Hnot; destruct l as [base|base off|base off|key]; try exact I.
  all: exfalso; apply Hnot; eapply Hkeys; [exact Hl|exact I].
Qed.

Example full_open_admitted : stream_call_pre F.model [WPtr (token_handle out)]
    conversion_mem (F.world true).
Proof.
  eapply A.open_admitted with (out := out) (err := err) (b := 5120) (o := 0)
    (pending := 7) (fifo := [65; 66]) (h := open_heap); [left; reflexivity|exact full_wi|].
  intros l v Hin. unfold stream_ps in Hin. apply elem_of_cons in Hin as [He|Hin].
  - injection He as He Hv. subst l v. unfold open_heap, StreamHandleChecks.heap.
    rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_ne; [|discriminate].
    apply lookup_insert_eq.
  - apply elem_of_cons in Hin as [He|Hin]; [|apply not_elem_of_nil in Hin; contradiction].
    injection He as He Hv. subst l v.
    unfold open_heap. apply lookup_insert_eq.
Qed.

Lemma open_heap_agrees : agrees conversion_mem open_heap.
Proof.
  intros l v Hl. unfold open_heap in Hl.
  apply lookup_insert_Some in Hl as [[He Hv]|[_ Hl]]; [subst l v; exact I|].
  apply lookup_insert_Some in Hl as [[He Hv]|[_ Hl]]; [subst l v; exact I|].
  exact (StreamHandleChecks.heap_agrees l v Hl).
Qed.

(** An actual stderr query frames the paired interpretation even though
    stdout's physical count and outstanding FIFO differ from stderr's. *)
Example stderr_query_preserves_pair :
  A.M.E.invoke (fpending_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (token_handle err)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 3]) InterpRuntime.start conversion_mem (F.world true) /\
  stream_tokens_wi (fun _ _ => True) out err 5120 0 conversion_mem (F.world true) open_heap.
Proof.
  assert (Hcall : A.M.E.invoke (fpending_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (token_handle err)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 3]) InterpRuntime.start conversion_mem (F.world true)).
  { apply StreamHandleChecks.C.fpending_unchanged with (file := F.err_file).
    - split; [left; reflexivity|]. exists (Const 0). reflexivity.
    - apply F.ready.
    - reflexivity. }
  split; [exact Hcall|].
  destruct (A.query_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) out err 5120 0 err _ _ _ _ _ _ _ _ _ _ _ open_heap
    (or_intror eq_refl) (or_intror eq_refl) Hcall open_heap_agrees
    HelloErrnoChecks.disjoint HelloErrnoChecks.ready full_wi) as (_ & _ & _ & Hw).
  exact Hw.
Qed.

(** The other query contract and stdout selection use the same frame. *)
Example stdout_error_preserves_pair :
  A.M.E.invoke (ferror_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (token_handle out)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 1]) InterpRuntime.start conversion_mem (F.world true) /\
  stream_tokens_wi (fun _ _ => True) out err 5120 0 conversion_mem (F.world true) open_heap.
Proof.
  assert (Hcall : A.M.E.invoke (ferror_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (token_handle out)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 1]) InterpRuntime.start conversion_mem (F.world true)).
  { apply StreamHandleChecks.C.ferror_unchanged with (file := F.out_file).
    - split; [left; reflexivity|]. exists (Const 0). reflexivity.
    - apply F.ready.
    - reflexivity. }
  split; [exact Hcall|].
  destruct (A.query_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) out err 5120 0 out _ _ _ _ _ _ _ _ _ _ _ open_heap
    (or_introl eq_refl) (or_introl eq_refl) Hcall open_heap_agrees
    HelloErrnoChecks.disjoint HelloErrnoChecks.ready full_wi) as (_ & _ & _ & Hw).
  exact Hw.
Qed.

(** An actual authorized scalar write changes every errno byte, including
    the last one. It changes neither FILE storage nor locale strings. *)
Definition changed_errno : mem := store_bytes conversion_mem 5120 4 16909060.

Lemma changed_files_ready :
  libc_file_ready changed_errno (mkPtr 5120 (Obj 5120)) F.out_file /\
  libc_file_ready changed_errno (mkPtr 5120 (Obj 5120)) F.err_file.
Proof.
  destruct F.files_ready as [Hout Herr]. split; [clear Herr|clear Hout].
  all: (destruct Hout as (Hnon & (Hn & Hreg & Haccess & Hbytes) & Hrest)
    || destruct Herr as (Hnon & (Hn & Hreg & Haccess & Hbytes) & Hrest)).
  all: split; [exact Hnon|].
  all: split; [|destruct Hrest as (Hp & _ & _ & _ & Ha);
    split; [exact Hp|]; split; [constructor|]; split; [constructor|];
    split; [constructor|exact Ha]].
  all: split; [exact Hn|].
  all: split; [exact Hreg|].
  all: split; [exact Haccess|].
  all: intros i Hi; assert (i = 0) as -> by lia; vm_compute; split; congruence.
Qed.

Lemma changed_ready : forall opened,
  libc_stream_ready (fun _ _ => True) changed_errno (F.world opened).
Proof.
  intros opened. destruct (F.ready opened)
    as (Hrep & Hlocale & He & Hout & Herr & Hu & Hstatus & Hphase & Hdistinct & Hroots & _).
  split; [exact Hrep|]. split.
  - destruct Hlocale as (_ & _ & _ & _ & _ & Haligned).
    split; [exact I|]. split; [constructor|]. split.
    + intros category _. vm_compute. repeat split; congruence.
    + split; [constructor|]. split; [constructor|exact Haligned].
  - split; [exact He|]. split; [exact Hout|]. split; [exact Herr|].
    split; [exact Hu|]. split; [exact Hstatus|]. split; [exact Hphase|].
    split; [exact Hdistinct|]. split; [exact Hroots|].
    split; [intros _; exact (proj1 changed_files_ready)|].
    split; [intros _; exact (proj2 changed_files_ready)|].
    intros p file Hfile base Hin. unfold libc_file_at in Hfile.
    destruct (same_file p (libc_stdout (F.world opened)));
      [destruct opened|destruct (same_file p (libc_stderr (F.world opened)))];
      try discriminate; injection Hfile as <-; contradiction.
Qed.

(** The contract allows success or EOF after settling the old FIFO.
    Both controls use the supplied HelloClose machine, not F.M. *)
Lemma changed_close : forall n, n = 0 \/ n = stream_eof ->
  A.M.E.invoke (fclose_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (token_handle out)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt n]) InterpRuntime.start changed_errno (F.world false).
Proof.
  intros n Hn. eapply A.M.E.invoke_normal with (born := []).
  - split; [left; reflexivity|]. exists (Const 0). reflexivity.
  - apply full_open_admitted.
  - split.
    + eapply A.M.E.effects_local; [apply local_store_bytes|constructor].
      intros a Ha. left. exists (errno_span 5120 0).
      split; [left; reflexivity|]. split.
      * exact (proj1 (proj2 (proj1 (proj2 (proj2 (F.ready true)))))).
      * unfold span_contains, errno_span. simpl. lia.
    + exists (token_handle out),
        (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7), (mkStream ByteOriented [] true).
      split; [reflexivity|]. split; [reflexivity|]. split; [apply F.close_settles|].
      split; [reflexivity|]. split; [apply changed_ready|]. split; [apply F.close_frame|].
      split; [split; [intros root []|split; intros x []; contradiction]|].
      split; [reflexivity|]. split; [left; reflexivity|]. intros a Hin Houtside. reflexivity.
  - exists (token_handle out), (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7),
      (mkStream ByteOriented [] true), n.
    split; [reflexivity|]. split; [reflexivity|]. split; [apply F.close_settles|].
    split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
    split; [intros base []|]. split; [apply changed_ready|]. split; [apply F.close_frame|]. auto.
  - intros why Hbad. discriminate.
  - intros values Hvalues. injection Hvalues as <-. split.
    + exists (WInt n). split; [reflexivity|]. destruct Hn as [-> | ->]; reflexivity.
    + repeat constructor.
  - intros status Hbad. discriminate.
Qed.

Example completed_close_preserves_pair : forall n, n = 0 \/ n = stream_eof ->
  exists ys, ys = [4; 3; 2; 1] /\
    stream_tokens_wi (fun _ _ => True) out err 5120 0 changed_errno (F.world false)
      (<[PName (-2) := VStream (token_handle out) None]>
        (overwrite (byte_ps 5120 0 ys) open_heap)).
Proof.
  intros n Hn.
  destruct (A.close_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) out err 5120 0 out _ _ _ _ _ _ _ _ _ _ open_heap [0; 0; 0; 0]
    (or_introl eq_refl) (changed_close n Hn) open_heap_agrees
    HelloErrnoChecks.disjoint HelloErrnoChecks.ready full_wi eq_refl)
    as (ys & Hlen & Hkeys & Hagree & _ & _ & Hwi).
  - intros l v Hin. unfold open_heap, StreamHandleChecks.heap.
    pose proof (MemLogic.byte_ps_elem _ _ _ _ _ Hin) as (i & x & Hi & El & Ev).
    subst l v.
    rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_ne; [|discriminate].
    rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_ne; [|discriminate].
    unfold HelloErrnoChecks.heap. apply elem_of_list_to_map_1; [|exact Hin].
    change (base.NoDup [PByte 5120 0; PByte 5120 1; PByte 5120 2; PByte 5120 3]).
    repeat (apply base.NoDup_cons_2; [set_solver|]). apply base.NoDup_nil_2.
  - exists ys. split; [|exact Hwi].
    destruct ys as [|a [|b [|c [|d rest]]]]; try discriminate Hlen.
    assert (rest = []) as -> by (destruct rest; [reflexivity|discriminate Hlen]).
    assert (Hbyte : forall i x, (PByte 5120 i, VByte x) ∈ byte_ps 5120 0 [a; b; c; d] ->
        x = m_bytes changed_errno (5120 + i)).
    { intros i x Hin. assert (Hl :
        (<[PName (-2) := VStream (token_handle out) None]>
          (overwrite (byte_ps 5120 0 [a; b; c; d]) open_heap)) !! PByte 5120 i = Some (VByte x)).
      { rewrite lookup_insert_ne; [|discriminate].
        change ((PByte 5120 i, VByte x) ∈
          [(PByte 5120 0, VByte a); (PByte 5120 1, VByte b);
           (PByte 5120 2, VByte c); (PByte 5120 3, VByte d)]) in Hin.
        repeat (apply elem_of_cons in Hin as [E|Hin];
          [injection E as Ei Ex; subst i x; cbn [byte_ps overwrite fst snd];
           repeat (rewrite lookup_insert_ne; [|discriminate]); apply lookup_insert_eq|]).
        apply not_elem_of_nil in Hin. contradiction. }
      destruct (Hagree _ _ Hl) as [_ Hvalue].
      destruct (Hvalue (mkRegion 5120 5128 Heap Live) eq_refl eq_refl) as (_ & _ & Hv).
      symmetry. exact Hv. }
    assert (Ha : a = 4) by (apply (Hbyte 0 a); change ((PByte 5120 0, VByte a) ∈
      [(PByte 5120 0, VByte a); (PByte 5120 1, VByte b); (PByte 5120 2, VByte c); (PByte 5120 3, VByte d)]);
      apply list_elem_of_In; simpl; auto 10).
    assert (Hb : b = 3) by (apply (Hbyte 1 b); change ((PByte 5120 1, VByte b) ∈
      [(PByte 5120 0, VByte a); (PByte 5120 1, VByte b); (PByte 5120 2, VByte c); (PByte 5120 3, VByte d)]);
      apply list_elem_of_In; simpl; auto 10).
    assert (Hc : c = 2) by (apply (Hbyte 2 c); change ((PByte 5120 2, VByte c) ∈
      [(PByte 5120 0, VByte a); (PByte 5120 1, VByte b); (PByte 5120 2, VByte c); (PByte 5120 3, VByte d)]);
      apply list_elem_of_In; simpl; auto 10).
    assert (Hd : d = 1) by (apply (Hbyte 3 d); change ((PByte 5120 3, VByte d) ∈
      [(PByte 5120 0, VByte a); (PByte 5120 1, VByte b); (PByte 5120 2, VByte c); (PByte 5120 3, VByte d)]);
      apply list_elem_of_In; simpl; auto 10).
    subst. reflexivity.
Qed.

(** Updating only the stream name would leave stale owned errno. The
    last byte alone distinguishes that incorrect replacement. *)
Example stale_errno_close_heap_rejected :
  ~ agrees changed_errno (<[PName (-2) := VStream (token_handle out) None]> open_heap).
Proof.
  intros Ha.
  assert (Hl : (<[PName (-2) := VStream (token_handle out) None]> open_heap) !!
    PByte 5120 3 = Some (VByte 0)).
  { unfold open_heap, StreamHandleChecks.heap, HelloErrnoChecks.heap.
    repeat (rewrite lookup_insert_ne; [|discriminate]). apply lookup_insert_eq. }
  destruct (Ha _ _ Hl) as [_ Hbyte].
  destruct (Hbyte (mkRegion 5120 5128 Heap Live) eq_refl eq_refl) as (_ & _ & Hvalue).
  discriminate Hvalue.
Qed.

(** Entry begins with actual errno ownership, but no recorded FILE lives
    or observations. The observations are selected from the current world. *)
Lemma entry_keys : forall l v,
  HelloErrnoChecks.heap !! l = Some v -> exists i, l = PByte 5120 i.
Proof.
  intros l v Hl. unfold HelloErrnoChecks.heap in Hl. apply elem_of_list_to_map_2 in Hl.
  destruct (MemLogic.byte_ps_elem _ _ _ _ _ Hl) as (i & x & _ & -> & _). eauto.
Qed.

Lemma entry_wi : stream_tokens_wi (fun _ _ => True) out err 5120 0
    conversion_mem (F.world true) HelloErrnoChecks.heap.
Proof.
  assert (Hkeys : forall l v, stream_data_heap 1024 2048 HelloErrnoChecks.heap !! l = Some v ->
      mem_piece l -> l ∈ errno_keys 5120 0).
  { intros l v Hl _. apply stream_data_lookup in Hl as [Hl _].
    unfold HelloErrnoChecks.heap in Hl. apply elem_of_list_to_map_2 in Hl.
    change (l ∈ (byte_ps 5120 0 [0; 0; 0; 0]).*1).
    apply list_elem_of_fmap. exists (l, v). auto. }
  split; [split; [reflexivity|simpl; lia]|]. split; [split; [reflexivity|simpl; lia]|].
  split; [discriminate|]. split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold stream_current. destruct (HelloErrnoChecks.heap !! PName (token_key out)) as [v|] eqn:E;
      [destruct (entry_keys _ _ E) as [i Hbad]; discriminate Hbad|exact I]. }
  split.
  { unfold stream_current. destruct (HelloErrnoChecks.heap !! PName (token_key err)) as [v|] eqn:E;
      [destruct (entry_keys _ _ E) as [i Hbad]; discriminate Hbad|exact I]. }
  intros d [-> | ->].
  all: split; [|intros base l v Hin; change (In base []) in Hin; contradiction].
  all: split; [apply F.ready|].
  all: split; [reflexivity|].
  all: split; [intros root a Hin; change (In root []) in Hin; contradiction|].
  all: split; [intros base l v Hin; change (In base []) in Hin; contradiction|].
  all: intros l v Hl Hnot; destruct l as [base|base off|base off|key]; try exact I.
  all: exfalso; apply Hnot; eapply Hkeys; [exact Hl|exact I].
Qed.

Lemma entry_fresh : forall l v,
  (l, v) ∈ stream_ps out 7 [65; 66] ++ stream_ps err 3 [] -> HelloErrnoChecks.heap !! l = None.
Proof.
  intros l v Hin. destruct (HelloErrnoChecks.heap !! l) as [old|] eqn:E; [|reflexivity].
  destruct (entry_keys _ _ E) as [i ->]. apply list_elem_of_In in Hin.
  cbn [stream_ps app out err token_base token_key] in Hin.
  destruct Hin as [Hbad|[Hbad|[Hbad|[Hbad|[]]]]]; discriminate Hbad.
Qed.

Section entry_iris.
Context `{!gen_heapGS piece pval Σ}.

(** Both real tokens are produced while independently owned errno is
    retained. This is not just a construction of a pure endpoint map. *)
Example entry_produces_pair :
  gen_heap_interp HelloErrnoChecks.heap ∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) ==∗
  ∃ h, gen_heap_interp h ∗ pts (stream_ps out 7 [65; 66]) ∗ pts (stream_ps err 3 []) ∗
    pts (byte_ps 5120 0 [0; 0; 0; 0]) ∗
    ⌜agrees conversion_mem h /\ stream_tokens_wi (fun _ _ => True) out err 5120 0
      conversion_mem (F.world true) h⌝.
Proof.
  iIntros "[Hh Herrno]".
  iMod (stream_entry_alloc (fun _ _ => True) out err 5120 0 conversion_mem (F.world true)
    HelloErrnoChecks.heap 7 [65; 66] 3 [] HelloErrnoChecks.heap_agrees entry_wi
    with "Hh") as "(Hh & Ho & He & %Hnew)".
  - split; reflexivity.
  - split; reflexivity.
  - exists (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7). repeat split; reflexivity.
  - exists (mkStreamInfo 2 stdout_initial 3). repeat split; reflexivity.
  - exact entry_fresh.
  - iModIntro. iExists _. iFrame. done.
Qed.

End entry_iris.

(** An existing key cannot be freshly recorded, even if its native
    object is live and the caller has no fragment for the old value. *)
Example occupied_life_not_fresh :
  ~ (forall l v, (l, v) ∈ stream_ps out 7 [65; 66] ++ stream_ps err 3 [] ->
    StreamHandleChecks.heap !! l = None).
Proof.
  intros Hfresh. specialize (Hfresh (PLive 1024) (VLive (token_region out))).
  assert (Hin : (PLive 1024, VLive (token_region out)) ∈
    stream_ps out 7 [65; 66] ++ stream_ps err 3 []) by
    (apply list_elem_of_In; simpl; auto).
  specialize (Hfresh Hin). unfold StreamHandleChecks.heap in Hfresh.
  rewrite lookup_insert_eq in Hfresh. discriminate Hfresh.
Qed.

Example occupied_name_not_fresh :
  ~ (forall l v, (l, v) ∈ stream_ps out 7 [65; 66] ++ stream_ps err 3 [] ->
    (<[PName (-2) := VCodec (TAtom "C")]> HelloErrnoChecks.heap) !! l = None).
Proof.
  intros Hfresh. specialize (Hfresh (PName (-2)) (VStream (token_handle out) (Some (7, [65; 66])))).
  assert (Hin : (PName (-2), VStream (token_handle out) (Some (7, [65; 66]))) ∈
    stream_ps out 7 [65; 66] ++ stream_ps err 3 []) by
    (apply list_elem_of_In; simpl; auto).
  specialize (Hfresh Hin). rewrite lookup_insert_eq in Hfresh. discriminate Hfresh.
Qed.

Example aliased_handles_rejected : forall rep b o m w h,
  ~ stream_tokens_wi rep out out b o m w h.
Proof. intros rep b o m w h (_ & _ & Hbad & _). apply Hbad. reflexivity. Qed.

Example completed_close_not_readmitted :
  ~ stream_call_pre F.model [WPtr (token_handle out)] changed_errno (F.world false).
Proof.
  intros (p & info & Hargs & _ & Hopen & _). injection Hargs as <-.
  discriminate Hopen.
Qed.

End StreamTokenChecks.

(** Open-only callback permissions use separate keys from the exact
    -2/-3 snapshots, codec -1, locale 0..12 and getopt 64. The fixture
    contains NO exact snapshot names; two interpretations must not be
    conjoined to hide stale observations after diagnostics. *)
Module StreamPermissionChecks.
Module T := StreamTokenChecks.
Module F := LibcStreamChecks.
Module A := T.A.

Definition out := mkStreamToken (token_handle T.out) (token_base T.out) (token_region T.out) (-4).
Definition err := mkStreamToken (token_handle T.err) (token_base T.err) (token_region T.err) (-5).
Definition heap : gmap piece pval :=
  <[PName (-4) := VStreamOpen (token_handle out)]>
    (<[PName (-5) := VStreamOpen (token_handle err)]> StreamHandleChecks.heap).

Lemma memory_lookup : forall l, mem_piece l -> heap !! l = T.open_heap !! l.
Proof.
  intros l Hmem. destruct l; try contradiction.
  all: unfold heap, T.open_heap; repeat (rewrite lookup_insert_ne; [|discriminate]); reflexivity.
Qed.

Lemma heap_agrees : agrees conversion_mem heap.
Proof.
  intros l v Hl. unfold heap in Hl.
  apply lookup_insert_Some in Hl as [[He Hv]|[_ Hl]]; [subst l v; exact I|].
  apply lookup_insert_Some in Hl as [[He Hv]|[_ Hl]]; [subst l v; exact I|].
  exact (StreamHandleChecks.heap_agrees l v Hl).
Qed.

Lemma currents : stream_current out (F.world true) heap /\ stream_current err (F.world true) heap.
Proof.
  unfold stream_current, heap. cbn [out err token_key].
  rewrite lookup_insert_eq. rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_eq.
  split; (split; [reflexivity|]).
  - exists (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7). reflexivity.
  - exists (mkStreamInfo 2 stdout_initial 3). reflexivity.
Qed.

Lemma full_wi : stream_tokens_wi (fun _ _ => True) out err 5120 0
    conversion_mem (F.world true) heap.
Proof.
  destruct T.full_wi as (_ & _ & _ & _ & _ & _ & _ & _ & Hprivate).
  assert (Hdata : memory_keys_from (stream_data_heap 1024 2048 heap)
      (stream_data_heap 1024 2048 T.open_heap)).
  { intros l v Hl Hmem. apply stream_data_lookup in Hl as (Hl & Ho & He).
    exists v. rewrite stream_data_lookup_ne; [rewrite <- memory_lookup; assumption|assumption|assumption]. }
  split; [split; [reflexivity|simpl; lia]|]. split; [split; [reflexivity|simpl; lia]|].
  split; [discriminate|]. split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (proj1 currents)|]. split; [exact (proj2 currents)|].
  intros d [-> | ->].
  - destruct (Hprivate T.out (or_introl eq_refl)) as [Hwi Hrel].
    split; [eapply errno_wi_heap; [exact Hwi|exact Hdata]|].
    intros base l v Hin Hl Hmem. apply (Hrel base l v Hin); [rewrite <- memory_lookup; assumption|exact Hmem].
  - destruct (Hprivate T.err (or_intror eq_refl)) as [Hwi Hrel].
    split; [eapply errno_wi_heap; [exact Hwi|exact Hdata]|].
    intros base l v Hin Hl Hmem. apply (Hrel base l v Hin); [rewrite <- memory_lookup; assumption|exact Hmem].
Qed.

(** Rejection follows from the PURE interface, without Iris falsehood. *)
Example unknown_argument_rejected : forall rep b o m w h,
  stream_tokens_wi rep out err b o m w h ->
  ~ (forall l v, (l, v) ∈ permission_ps out err (mkPtr 3072 (Obj 3072)) -> h !! l = Some v).
Proof.
  intros rep b o m w h Hw Hl.
  destruct (proj2 (permission_known _ _ _ _ _ _ _ _ _ Hw Hl)) as [Hbad|Hbad]; discriminate Hbad.
Qed.

Example wrong_capability_rejected : forall rep b o m w h,
  stream_tokens_wi rep out err b o m w h ->
  ~ (forall l v, (l, v) ∈ permission_ps out err (mkPtr 1024 (Ro 1024)) -> h !! l = Some v).
Proof.
  intros rep b o m w h Hw Hl.
  destruct (proj2 (permission_known _ _ _ _ _ _ _ _ _ Hw Hl)) as [Hbad|Hbad]; discriminate Hbad.
Qed.

(** A new pending count/FIFO invalidates the old exact snapshot, while
    the open-only permission is still current. This is a world-view
    control, not a native diagnostic execution. *)
Definition changed_world : libc_world :=
  (mkLibcPayload (libc_locale (fst (F.world true))) (libc_stdio (fst (F.world true)))
    (libc_errno (fst (F.world true)))
    (mkLibcStreams (mkLibcFile (token_handle out) 9 [] [] []) F.err_file true stdout_initial)
    (libc_getopt (fst (F.world true))),
   mkShutdown Handlers 0 [] [] (mkStream ByteOriented [65; 66; 67] true)).

Example open_permission_not_snapshot :
  stream_current out changed_world heap /\
  ~ stream_current out changed_world
    (<[PName (-4) := VStream (token_handle out) (Some (7, [65; 66]))]> heap).
Proof.
  split.
  - unfold stream_current, heap. cbn [out token_key]. rewrite lookup_insert_eq.
    split; [reflexivity|]. exists (mkStreamInfo 1 (mkStream ByteOriented [65; 66; 67] true) 9).
    reflexivity.
  - unfold stream_current. cbn [out token_key]. rewrite lookup_insert_eq.
    intros (_ & info & Hinfo & Hpending & _).
    change (Some (mkStreamInfo 1 (mkStream ByteOriented [65; 66; 67] true) 9) = Some info) in Hinfo.
    injection Hinfo as <-. discriminate Hpending.
Qed.

Example closed_permission_rejected : ~ stream_current out (F.world false) heap.
Proof.
  unfold stream_current, heap. cbn [out token_key]. rewrite lookup_insert_eq.
  intros (_ & info & Hinfo). discriminate Hinfo.
Qed.

Example query_preserves_permissions :
  stream_tokens_wi (fun _ _ => True) out err 5120 0 conversion_mem (F.world true) heap.
Proof.
  destruct T.stdout_error_preserves_pair as [Hcall _].
  destruct (A.query_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) out err 5120 0 out _ _ _ _ _ _ _ _ _ _ _ heap
    (or_introl eq_refl) (or_introl eq_refl) Hcall heap_agrees
    HelloErrnoChecks.disjoint HelloErrnoChecks.ready full_wi) as (_ & _ & _ & Hw).
  exact Hw.
Qed.

End StreamPermissionChecks.
