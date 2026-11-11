(** Callback stream tokens retain native handle lives but do not own
    private FILE bytes. The projection here is pure proof bookkeeping;
    it never deletes authoritative Iris resources. *)
From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Identity ExternalCalls
  ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams Pieces Heap
  ContractFrame Logic StringLogic LentLogic LibcStreamLogic LibcErrnoLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** Only designated life keys disappear. Byte and auxiliary pieces in
    either FILE object remain, so private-root separation still rejects
    caller ownership of FILE storage. *)
Definition stream_data_heap (out_base err_base : Z) (h : gmap piece pval) :=
  delete (PLive out_base) (delete (PLive err_base) h).

Lemma stream_data_lookup : forall out_base err_base h l v,
  stream_data_heap out_base err_base h !! l = Some v ->
  h !! l = Some v /\ l <> PLive out_base /\ l <> PLive err_base.
Proof.
  intros out_base err_base h l v Hl. unfold stream_data_heap in Hl.
  apply lookup_delete_Some in Hl as [Hout Hl].
  apply lookup_delete_Some in Hl as [Herr Hl]. auto.
Qed.

Lemma stream_data_lookup_ne : forall out_base err_base h l,
  l <> PLive out_base -> l <> PLive err_base ->
  stream_data_heap out_base err_base h !! l = h !! l.
Proof.
  intros out_base err_base h l Hout Herr. unfold stream_data_heap.
  rewrite !lookup_delete_ne; congruence.
Qed.

Lemma stream_data_agrees : forall out_base err_base m h,
  agrees m h -> agrees m (stream_data_heap out_base err_base h).
Proof.
  intros out_base err_base m h Ha l v Hl.
  apply stream_data_lookup in Hl as [Hl _]. exact (Ha l v Hl).
Qed.

(** Restore exactly the removed lives, including their original region.
    Registration/persistence alone would also permit a freed handle. *)
Lemma stream_data_restore : forall out_base err_base m m' h h',
  agrees m h -> agrees m' (stream_data_heap out_base err_base h') -> persists m m' ->
  h' !! PLive out_base = h !! PLive out_base ->
  h' !! PLive err_base = h !! PLive err_base ->
  (forall reg, live_at m out_base reg -> live_at m' out_base reg) ->
  (forall reg, live_at m err_base reg -> live_at m' err_base reg) -> agrees m' h'.
Proof.
  intros out_base err_base m m' h h' Ha Hdata Hp Houtkey Herrkey Hout Herr l v Hl.
  destruct (decide (l = PLive out_base)) as [->|Hneout].
  - rewrite Houtkey in Hl. pose proof (Ha _ _ Hl) as Hag. destruct v; cbn [agree_piece] in Hag |- *;
      try contradiction; [apply Hout; exact Hag|].
    unfold registered in *. destruct (object_region out_base (m_regions m)) as [reg|] eqn:E;
      [destruct (Hp _ _ E) as [E'|E']; rewrite E'; discriminate|contradiction].
  - destruct (decide (l = PLive err_base)) as [->|Hneerr].
    + rewrite Herrkey in Hl. pose proof (Ha _ _ Hl) as Hag. destruct v; cbn [agree_piece] in Hag |- *;
        try contradiction; [apply Herr; exact Hag|].
      unfold registered in *. destruct (object_region err_base (m_regions m)) as [reg|] eqn:E;
        [destruct (Hp _ _ E) as [E'|E']; rewrite E'; discriminate|contradiction].
    + apply Hdata. rewrite stream_data_lookup_ne; assumption.
Qed.

(** Updating data/ghost values commutes with the pure life projection,
    but updating one of the two erased life keys does not. *)
Lemma stream_data_overwrite : forall ps out_base err_base h,
  PLive out_base ∉ ps.*1 -> PLive err_base ∉ ps.*1 ->
  stream_data_heap out_base err_base (overwrite ps h) =
  overwrite ps (stream_data_heap out_base err_base h).
Proof.
  induction ps as [|[l v] ps IH]; intros out_base err_base h Hout Herr; [reflexivity|].
  cbn [fmap fst] in Hout, Herr. apply not_elem_of_cons in Hout as [Hout Houts].
  apply not_elem_of_cons in Herr as [Herr Herrs].
  cbn [overwrite]. unfold stream_data_heap at 1.
  rewrite !delete_insert_ne; try congruence.
  change (<[l := v]> (stream_data_heap out_base err_base (overwrite ps h)) =
    <[l := v]> (overwrite ps (stream_data_heap out_base err_base h))).
  rewrite IH; auto.
Qed.

(** Native readiness excludes BOTH stable FILE identities from every
    active release pool, not just the selected handle's identity. *)
Lemma libc_handle_not_released : forall rep m w p q base,
  libc_stream_ready rep m w -> (q = libc_stdout w \/ q = libc_stderr w) ->
  ptr_cap q = Obj base -> ~ In base (libc_stream_releases w p).
Proof.
  intros rep m w p q base (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsep)
    Hq Hcap Hin.
  unfold libc_stream_releases in Hin. destruct (libc_file_at w p) as [file|] eqn:Hfile;
    [|contradiction].
  destruct (Hsep p file Hfile base Hin) as (_ & _ & Hnot & _).
  apply Hnot. right. left. exists (mkSpan q 0). split.
  - destruct Hq as [-> | ->]; [left; reflexivity|right; left; reflexivity].
  - simpl. symmetry. exact Hcap.
Qed.

Module LibcStreamTokensOn (R : Runtime) (LG : StreamFrameLogic R).
Module M := LG.L.M.
Module EL := LibcErrnoLogicOn R LG.

(** The existing effects frame proves stable handle life independently
    of byte-write roots. It may mutate locks inside the FILE object;
    only releasing that object's identity is excluded. Fresh allocation
    cannot turn the old handle into a born identity. *)
Lemma prefix_handle_live : forall world (spec : contract world) xs s m w born trace s' m' w' b reg,
  M.E.prefix spec xs s m w born trace s' m' w' ->
  R.ready s m -> live_disjoint m -> live_at m b reg ->
  ~ In b (contract_releases spec xs m w) -> live_at m' b reg.
Proof.
  intros world spec xs s m w born trace s' m' w' b reg Hp Hr Hd Hlive Hrelease.
  assert (Ha : agrees m (singletonM (PLive b) (VLive reg) : gmap piece pval)).
  { intros l v Hl. apply lookup_singleton_Some in Hl as [Hl Hv]. subst l v. exact Hlive. }
  destruct (LG.prefix_agrees_out _ _ _ _ _ _ _ _ _ _ _
    (singletonM (PLive b) (VLive reg) : gmap piece pval) [] (fun _ => True) Hp Hr Hd)
    as (Hafter & _).
  - intros l v Hl _. exact (Ha l v Hl).
  - intros l v Hl Hmem. eapply agree_piece_registered; [exact Hmem|exact (Ha l v Hl)].
  - intros root a Hin Hspan Howned. exact I.
  - intros l v Hl _. apply lookup_singleton_Some in Hl as [Hl Hv]. subst l v. exact I.
  - intros base l v Hin Hl Hmem.
    apply lookup_singleton_Some in Hl as [Hl Hv]. subst l v. simpl. intros ->. contradiction.
  - apply (Hafter (PLive b) (VLive reg)); [apply lookup_singleton_Some; auto|].
    intros Hnil. inversion Hnil.
Qed.

(** A query may write private locks inside either stable handle. The
    data frame deliberately omits only their life keys, then the
    no-release effects frame restores those exact original regions. *)
Theorem query_frame : forall rep requests wide out_base err_base p b o spec r args
    s m w trace ending s' m' w' h,
  (spec = ferror_contract (libc_stream_model rep requests wide) \/
   spec = fpending_contract (libc_stream_model rep requests wide)) ->
  M.E.invoke spec r args [WPtr p] s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m ->
  libc_errno_wi rep p b o m w (stream_data_heap out_base err_base h) ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\
  libc_errno_wi rep p b o m' w' (stream_data_heap out_base err_base h).
Proof.
  intros rep requests wide out_base err_base p b o spec r args
    s m w trace ending s' m' w' h Hspec Hcall Ha Hd Hr Hwi.
  pose proof (stream_data_agrees out_base err_base m h Ha) as Hdata.
  destruct (EL.query_frame rep requests wide p b o spec r args s m w trace ending s' m' w'
    (stream_data_heap out_base err_base h) Hspec Hcall Hdata Hd Hr Hwi)
    as (Hdata' & Hd' & Hr' & Hwi').
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [_ Hpers].
  assert (Hrelease : forall base, ~ In base (contract_releases spec [WPtr p] m w)).
  { intros base. destruct Hspec as [-> | ->]; cbn [ferror_contract fpending_contract contract_releases]; tauto. }
  split; [|auto]. eapply stream_data_restore;
    [exact Ha|exact Hdata'|exact Hpers|reflexivity|reflexivity| |].
  all: intros reg Hlive; eapply prefix_handle_live; eauto.
Qed.

(** Close updates actual endpoint errno bytes and retains both native
    handle lives, including on a resource-ending prefix. This theorem
    deliberately makes no closed-token claim on that prefix. *)
Theorem close_frame : forall rep requests wide out_base err_base p b o r args
    s m w trace ending s' m' w' h xs,
  ptr_cap (libc_stdout w) = Obj out_base -> ptr_cap (libc_stderr w) = Obj err_base ->
  M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
    r args [WPtr p] s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m ->
  libc_errno_wi rep p b o m w (stream_data_heap out_base err_base h) ->
  length xs = 4%nat ->
  (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) ->
  exists ys, length ys = 4%nat /\ (byte_ps b o ys).*1 = (byte_ps b o xs).*1 /\
    agrees m' (overwrite (byte_ps b o ys) h) /\ live_disjoint m' /\ R.ready s' m' /\
    libc_errno_wi rep p b o m' w'
      (stream_data_heap out_base err_base (overwrite (byte_ps b o ys) h)).
Proof.
  intros rep requests wide out_base err_base p b o r args
    s m w trace ending s' m' w' h xs Houtcap Herrcap Hcall Ha Hd Hr Hwi Hlen Howned.
  assert (Hlife_off : forall base zs, PLive base ∉ (byte_ps b o zs).*1).
  { intros base zs Hkey. rewrite byte_ps_keys in Hkey.
    apply list_elem_of_fmap in Hkey as (i & E & _). discriminate E. }
  destruct (EL.close_frame rep requests wide p b o r args s m w trace ending s' m' w'
    (stream_data_heap out_base err_base h) xs Hcall
    (stream_data_agrees out_base err_base m h Ha) Hd Hr Hwi Hlen)
    as (ys & Hys & Hkeys & Hdata' & Hd' & Hr' & Hwi').
  - intros l v Hin. rewrite stream_data_lookup_ne; [exact (Howned l v Hin)| |].
    + intros Hbad. apply (Hlife_off out_base xs). rewrite <- Hbad.
      apply list_elem_of_fmap. exists (l, v). auto.
    + intros Hbad. apply (Hlife_off err_base xs). rewrite <- Hbad.
      apply list_elem_of_fmap. exists (l, v). auto.
  - assert (Hcommute := stream_data_overwrite (byte_ps b o ys) out_base err_base h
      (Hlife_off out_base ys) (Hlife_off err_base ys)).
    rewrite <- Hcommute in Hdata', Hwi'.
    exists ys. split; [exact Hys|]. split; [exact Hkeys|]. split; [|auto].
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [_ Hpers].
    eapply stream_data_restore; [exact Ha|exact Hdata'|exact Hpers| | | |].
    + apply overwrite_out, Hlife_off.
    + apply overwrite_out, Hlife_off.
    + intros reg Hlive. eapply prefix_handle_live; [exact Hp|exact Hr|exact Hd|exact Hlive|].
      change (~ In out_base (libc_stream_releases w p)).
      eapply libc_handle_not_released; [exact (proj1 Hwi)|left; reflexivity|exact Houtcap].
    + intros reg Hlive. eapply prefix_handle_live; [exact Hp|exact Hr|exact Hd|exact Hlive|].
      change (~ In err_base (libc_stream_releases w p)).
      eapply libc_handle_not_released; [exact (proj1 Hwi)|right; reflexivity|exact Herrcap].
Qed.

End LibcStreamTokensOn.

(** Logical controls use HelloClose's actual machine. The tiny fixture
    objects are not claimed to be native FILE representations. *)
Module StreamHandleChecks.
Module LG := HelloErrnoChecks.LG.
Module T := LibcStreamTokensOn InterpRuntime LG.
Module C := LibcStreamsOn InterpRuntime LG.L.M.
Module F := LibcStreamChecks.
Module E := HelloErrnoChecks.

Definition heap : gmap piece pval :=
  <[PLive 1024 := VLive (mkRegion 1024 1056 GlobalData Live)]>
    (<[PLive 2048 := VLive (mkRegion 2048 2056 Stack Live)]> E.heap).

Lemma data_heap : stream_data_heap 1024 2048 heap = E.heap.
Proof.
  assert (Hnone : forall base, E.heap !! PLive base = None).
  { intros base. apply eq_None_not_Some. intros [v Hl]. unfold E.heap in Hl.
    apply elem_of_list_to_map_2 in Hl.
    destruct (MemLogic.byte_ps_elem _ _ _ _ _ Hl) as (i & x & Hi & He & Hv). discriminate He. }
  unfold stream_data_heap, heap. rewrite delete_insert_ne; [|discriminate].
  rewrite !delete_insert_eq. rewrite !delete_id; auto.
Qed.

Lemma heap_agrees : agrees conversion_mem heap.
Proof.
  intros l v Hl. unfold heap in Hl.
  apply lookup_insert_Some in Hl as [[He Hv]|[Hne Hl]]; [subst l v; split; reflexivity|].
  apply lookup_insert_Some in Hl as [[He Hv]|[Hne' Hl]]; [subst l v; split; reflexivity|].
  exact (E.heap_agrees l v Hl).
Qed.

(** Owned errno plus BOTH stable native lives coexist with the query
    frame; this is not an empty ghost heap or a sibling logic. *)
Example held_handles_query :
  LG.L.M.E.invoke (fpending_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (file_handle F.out_file)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 7]) InterpRuntime.start conversion_mem (F.world true) /\
  agrees conversion_mem heap /\
  libc_errno_wi (fun _ _ => True) (file_handle F.out_file) 5120 0
    conversion_mem (F.world true) (stream_data_heap 1024 2048 heap).
Proof.
  assert (Hcall : LG.L.M.E.invoke (fpending_contract F.model) CVoid [Arg P (Const 0)]
    [WPtr (file_handle F.out_file)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 7]) InterpRuntime.start conversion_mem (F.world true)).
  { apply C.fpending_unchanged with (file := F.out_file).
    - split; [left; reflexivity|]. exists (Const 0). reflexivity.
    - apply F.ready.
    - reflexivity. }
  split; [exact Hcall|].
  destruct (T.query_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) 1024 2048 (file_handle F.out_file) 5120 0
    _ _ _ _ _ _ _ _ _ _ _ heap (or_intror eq_refl) Hcall heap_agrees E.disjoint E.ready)
    as (Ha & _ & _ & Hw).
  - rewrite data_heap. exact E.heap_wi.
  - auto.
Qed.

(** Erasing a life is not erasing caller ownership of the FILE's bytes
    or auxiliary slots. Either kind still excludes a private root. *)
Example private_byte_rejected : forall m h v,
  h !! PByte 1024 0 = Some v -> live_at m 1024 (mkRegion 1024 1056 GlobalData Live) ->
  ~ roots_apart [mkSpan (mkPtr 1024 (Obj 1024)) 1] (stream_data_heap 1024 2048 h) m.
Proof.
  intros m h v Hl Hlive Hr. apply (Hr (mkSpan (mkPtr 1024 (Obj 1024)) 1) 1024).
  - left. reflexivity.
  - unfold span_contains. simpl. lia.
  - exists (PByte 1024 0), v, (mkRegion 1024 1056 GlobalData Live).
    split; [rewrite stream_data_lookup_ne; congruence|].
    split; [exact I|]. split; [exact Hlive|]. simpl. lia.
Qed.

Example private_aux_rejected : forall m h v,
  h !! PAux 1024 0 = Some v -> live_at m 1024 (mkRegion 1024 1056 GlobalData Live) ->
  ~ roots_apart [mkSpan (mkPtr 1024 (Obj 1024)) 1] (stream_data_heap 1024 2048 h) m.
Proof.
  intros m h v Hl Hlive Hr. apply (Hr (mkSpan (mkPtr 1024 (Obj 1024)) 1) 1024).
  - left. reflexivity.
  - unfold span_contains. simpl. lia.
  - exists (PAux 1024 0), v, (mkRegion 1024 1056 GlobalData Live).
    split; [rewrite stream_data_lookup_ne; congruence|].
    split; [exact I|]. split; [exact Hlive|]. simpl. lia.
Qed.

End StreamHandleChecks.
