(** Program-memory and selected-FILE world frames over the logic's exact
    machine. Private FILE representation is trusted; separation from
    program pieces is explicit and propagated, not assumed at return. *)
From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls LibcCalls
  ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams
  Pieces Heap ContractFrame Logic.
Open Scope Z_scope.
Open Scope list_scope.

(** A fixed FILE handle's authority is apart from the program heap.
    This predicate intentionally does not promise that the handle is
    open: errno and hard-exit boundaries must remain usable after close. *)
Definition libc_stream_wi rep (p : ptr) m w (h : gmap piece pval) : Prop :=
  libc_stream_ready rep m w /\ roots_apart (libc_stream_writes w p) h m /\
  ids_apart (libc_stream_releases w p) h.

(** A close-callback boundary may have a closed FILE, but must not yet
    have handed control to the host. Readiness alone does not say this. *)
Definition libc_closing_wi rep p m w h : Prop :=
  libc_stream_wi rep p m w h /\
  forall kind, shutdown_at (snd w) <> HandedOff kind.

Lemma stream_delegates_apart : forall world (model : stream_model world) w p born m w' h,
  stream_delegates model w p born m w' ->
  roots_apart (stream_writes model w p) h m ->
  ids_apart (stream_releases model w p) h ->
  ids_apart born h -> live_disjoint m ->
  roots_apart (stream_writes model w' p) h m /\ ids_apart (stream_releases model w' p) h.
Proof.
  intros world model w p born m w' h (Hroots & _ & Hrelease) Hra Hrel Hb Hd.
  split.
  - intros root a Hin Hspan Hown. destruct (Hroots root Hin) as [_ Hauth].
    exact (owned_not_authority _ _ _ _ _ Hd Hra Hb Hown (Hauth a Hspan)).
  - intros base l v Hin Hlookup Hmem. destruct (Hrelease base Hin) as [Hold|Hnew].
    + exact (Hrel base l v Hold Hlookup Hmem).
    + exact (Hb base l v Hnew Hlookup Hmem).
Qed.

(** Use the consumer's logic and its inductive call relations, not a
    separately instantiated sibling machine. No new runtime law. *)
Module Type StreamFrameLogic (R : Runtime).
Include Logic R.
End StreamFrameLogic.

Module LibcStreamLogicOn (R : Runtime) (LG : StreamFrameLogic R).
Module L := LG.L.
Module M := L.M.
Module S := LibcStreamsOn R M.

(** Native represented readiness at a collector poll is an explicit
    realization law. Region identity then proves the heap-separation
    part, rather than requiring a separate separation assumption. *)
Lemma stream_wi_safepoint : forall rep p,
  (forall s m s' m' w, R.safepoint s m s' m' ->
    libc_stream_ready rep m w -> libc_stream_ready rep m' w) ->
  LG.SafepointStable (libc_stream_wi rep p).
Proof.
  intros rep p Hstable. split. intros s m s' m' w h Hsp (Hr & Hapart & Hrel).
  split; [eapply Hstable; eauto|]. split; [|exact Hrel].
  intros root a Hin Hspan (l & v & reg & Hl & Hmem & [E Hlive] & Hrange).
  apply (Hapart root a Hin Hspan). exists l, v, reg.
  split; [exact Hl|]. split; [exact Hmem|]. split; [|exact Hrange].
  split; [|exact Hlive]. rewrite (R.collector_live _ _ _ _ Hsp) in E. exact E.
Qed.

(** Narrow actions cannot turn a non-wide stream into a wide one. *)
Lemma narrow_run : forall q actions q',
  stream_run q actions q' -> orientation q <> WideOriented -> orientation q' <> WideOriented.
Proof.
  intros q actions q' Hrun. induction Hrun; [auto|]. intros Hn. apply IHHrun.
  inversion H; subst; simpl; congruence.
Qed.

(** Active lookup is consistent with the sole authoritative protocol. *)
Lemma active_protocol : forall w p info,
  libc_stream_at w p = Some info -> libc_stream_state w p = stream_protocol info.
Proof.
  intros w p info Hinfo. unfold libc_stream_at in Hinfo.
  destruct (libc_file_at w p); [injection Hinfo as <-; reflexivity|discriminate].
Qed.

(** Output does not close its selected handle or switch it to wide.
    This holds even when the accepted prefix ends in a resource failure. *)
Theorem output_open_narrow : forall rep requests wide api r args xs p s m w trace ending s' m' w',
  p = output_target api libc_stdout w xs ->
  orientation (libc_stream_state w p) <> WideOriented ->
  M.E.invoke (output_contract api (libc_stream_model rep requests wide) libc_stdout)
    r args xs s m w trace ending s' m' w' ->
  (exists file, libc_file_at w' p = Some file) /\
  orientation (libc_stream_state w' p) <> WideOriented /\
  libc_stdout w' = libc_stdout w.
Proof.
  intros rep requests wide api r args xs p s m w trace ending s' m' w' -> Hn Hcall.
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (born & _ & info & info' & bytes & actions & tail &
      Hinfo & Htext & Hbytes & Hrun & Hready & Hinfo' & Hframe & _).
  destruct Hready as (_ & Hactive & Hstate & _).
  change (stream_protocol info' = libc_stream_state w' (output_target api libc_stdout w xs)) in Hstate.
  change (libc_stream_at w (output_target api libc_stdout w xs) = Some info) in Hinfo.
  split.
  - change (libc_stream_at w' (output_target api libc_stdout w xs) = Some info') in Hactive.
    unfold libc_stream_at in Hactive. destruct (libc_file_at w' _) as [file|];
      [exists file; reflexivity|discriminate].
  - split.
    + rewrite <- Hstate. eapply narrow_run; [exact Hrun|].
      rewrite <- (active_protocol _ _ _ Hinfo). exact Hn.
    + exact (proj1 Hframe).
Qed.

(** Returning or resource-ending output preserves the program heap
    and re-establishes selected-FILE separation for the next call. *)
Theorem output_frame : forall rep requests wide api r args xs p s m w trace ending s' m' w' h,
  p = output_target api libc_stdout w xs ->
  M.E.invoke (output_contract api (libc_stream_model rep requests wide) libc_stdout)
    r args xs s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_stream_wi rep p m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ libc_stream_wi rep p m' w' h.
Proof.
  intros rep requests wide api r args xs p s m w trace ending s' m' w' h
    -> Hcall Ha Hd Hr (Hready & Hra & Hrel).
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  destruct (LG.prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hp Hr Hd Ha Hra
    ltac:(intros base l v [])) as (Ha' & Hd' & Hb & Hra').
  destruct Hp as (_ & info & info' & bytes & actions & tail &
    Hinfo & Htext & Hbytes & Hrun & Hopen & Hid & Hframe & Hdelegate & Htrace & Haux).
  split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|].
  split; [exact (proj1 Hopen)|].
  exact (stream_delegates_apart libc_world (libc_stream_model rep requests wide)
    w _ born m' w' h Hdelegate Hra' Hrel Hb Hd').
Qed.

(** The result part of HelloVersion's frame is obtained independently
    from the normal contract result; no output-success premise is used. *)
Theorem output_return_frame : forall rep requests wide api r args xs p s m w trace values s' m' w' h,
  p = output_target api libc_stdout w xs ->
  M.E.invoke (output_contract api (libc_stream_model rep requests wide) libc_stdout)
    r args xs s m w trace (CallReturn values) s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_stream_wi rep p m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ libc_stream_wi rep p m' w' h /\
    exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32.
Proof.
  intros. destruct (output_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4)
    as (Ha & Hd & Hr & Hw). split; [exact Ha|]. split; [exact Hd|]. split; [exact Hr|].
  split; [exact Hw|]. eapply S.output_returned; eauto.
Qed.

(** Close may consume its own heaps, but never program-owned identities.
    Endpoint readiness and retired authority come from the close prefix,
    including on EOF and resource stops. *)
Theorem close_frame : forall rep requests wide r args p s m w trace ending s' m' w' h,
  M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
    r args [WPtr p] s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_stream_wi rep p m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ libc_stream_wi rep p m' w' h.
Proof.
  intros rep requests wide r args p s m w trace ending s' m' w' h
    Hcall Ha Hd Hr (Hready & Hra & Hrel).
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  destruct (LG.prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hp Hr Hd Ha Hra Hrel)
    as (Ha' & Hd' & Hb & Hra').
  destruct Hp as (_ & p0 & info & final & Hxs & Hinfo & Hsettled & Hstate &
    Hready' & Hframe & Hdelegate & Htrace & Hclosed & Haux).
  injection Hxs as <-. split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|].
  split; [exact Hready'|].
  exact (stream_delegates_apart libc_world (libc_stream_model rep requests wide)
    w p born m' w' h Hdelegate Hra' Hrel Hb Hd').
Qed.

(** Both pure queries can lock/mutate private metadata; their actual
    effects, rather than an assumed unchanged memory, carry the frame. *)
Theorem query_frame : forall rep requests wide spec r args p s m w trace ending s' m' w' h,
  (spec = ferror_contract (libc_stream_model rep requests wide) \/
   spec = fpending_contract (libc_stream_model rep requests wide)) ->
  M.E.invoke spec r args [WPtr p] s m w trace ending s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> libc_stream_wi rep p m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ libc_stream_wi rep p m' w' h.
Proof.
  intros rep requests wide spec r args p s m w trace ending s' m' w' h
    Hspec Hcall Ha Hd Hr (Hready & Hra & Hrel).
  destruct Hspec as [-> | ->].
  all: (
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & Hp);
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _];
    destruct (LG.prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hp Hr Hd Ha Hra
      ltac:(intros base l v [])) as (Ha' & Hd' & Hb & Hra');
    destruct Hp as (_ & p0 & info & Hxs & Hinfo & Hopen & Hframe & Hdelegate & Htrace & Haux);
    injection Hxs as <-;
    split; [exact Ha'|]; split; [exact Hd'|]; split; [exact Hr'|];
    split; [exact (proj1 Hopen)|];
    exact (stream_delegates_apart libc_world (libc_stream_model rep requests wide)
      w p born m' w' h Hdelegate Hra' Hrel Hb Hd')).
Qed.

End LibcStreamLogicOn.
