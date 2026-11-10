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
  | Some _ => False
  end.

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

Section snapshot_allocation.
Context `{!gen_heapGS piece pval Σ}.

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
    unfold stream_current in *. destruct (h !! PName (token_key q)) as [v|]; [|exact I].
    destruct v; try contradiction. destruct Hc as [-> Hobs]. split; [reflexivity|].
    unfold stream_observation in *. destruct pending as [[physical fifo]|];
      rewrite Hlookup; [exact Hobs|rewrite Hstate; exact Hobs]. }
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

End StreamTokenChecks.
