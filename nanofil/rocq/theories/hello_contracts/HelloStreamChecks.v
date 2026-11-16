(** These checks follow stream permissions from callback entry through close and query calls.
    They also check that the standalone logic instance uses one machine for output and close operations. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run
  ExternalCalls LibcCalls ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams LibcExit
  Pieces Heap ContractFrame Logic StringLogic LibcStringLogic LentLogic LibcStreamLogic LibcErrnoLogic
  LibcStreamTokens LibcStreamAdapter LibcDiagnosticLogic
  HelloModule HelloLeaf HelloVersion HelloClose HelloStdio.
From Nanofil Require Export HelloStdioChecks.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
(** Main supplies one instance beneath output and callback triples. *)
Module HelloStdioSharedChecks.
Module LG := Logic InterpRuntime.
Module H := HelloStdioOn InterpRuntime LG.

Example version_expr_identity : H.V.L.expr = LG.L.expr.
Proof. reflexivity. Qed.

Example close_expr_identity : H.C.L.expr = LG.L.expr.
Proof. reflexivity. Qed.

Example shared_invoke_identity : @H.M.E.invoke = @H.C.L.M.E.invoke.
Proof. reflexivity. Qed.

End HelloStdioSharedChecks.

(** A single fixed interpretation admits allocation only before its
    owned stage is consumed. No assumption supplies either compatibility
    premise of the wrapper. Native safepoints are identity in this fixture. *)
Module HelloTransferChecks.
Import HelloCallbackChecks.
Module LG := StreamHandleChecks.LG.
Module F := LibcStreamChecks.
Module T := StreamTokenChecks.
Module P := StreamPermissionChecks.
Import LG LG.L.

Definition stage : Z := -6.
Definition before := VCodec (TAtom "callback-before").
Definition after := VCodec (TAtom "callback-entered").
Definition unrelated := [(PName (-7), VCodec (TAtom "unrelated"))].
Definition pair_ps := open_permission_ps P.out (token_handle P.out) ++
  open_permission_ps P.err (token_handle P.err).
Definition pair_wi := stream_tokens_wi (fun _ _ => True) P.out P.err 5120 0.
Definition entry_heap : gmap piece pval :=
  <[PName stage := before]> (<[PName (-7) := VCodec (TAtom "unrelated")]> HelloErrnoChecks.heap).
Definition admission m w (h : gmap piece pval) :=
  live_at m (token_base P.out) (token_region P.out) /\
  live_at m (token_base P.err) (token_region P.err) /\
  (exists info, libc_stream_at w (token_handle P.out) = Some info) /\
  (exists info, libc_stream_at w (token_handle P.err) = Some info) /\
  (forall l v, (l, v) ∈ pair_ps -> h !! l = None).
Definition callback_wi m w h := pair_wi m w h /\
  ((h !! PName stage = Some before /\ admission m w h) \/ h !! PName stage = Some after).

Global Instance callback_stable : SafepointStable callback_wi.
Proof. split. intros s m s' m' w h [-> ->] Hw. exact Hw. Qed.

Lemma entry_admitted : forall m w h,
  callback_wi m w h -> h !! PName stage = Some before -> pair_wi m w h /\ admission m w h.
Proof.
  intros m w h [Hpair [[_ Hadmit]|Hafter]] Hbefore; [exact (conj Hpair Hadmit)|].
  rewrite Hbefore in Hafter. discriminate Hafter.
Qed.

Lemma entry_restored : forall m w h,
  callback_wi m w h -> h !! PName stage = Some before ->
  pair_wi m w (<[PName stage := after]> (overwrite pair_ps h)) ->
  callback_wi m w (<[PName stage := after]> (overwrite pair_ps h)).
Proof.
  intros m w h _ _ Hpair. split; [exact Hpair|]. right. apply lookup_insert_eq.
Qed.

Lemma errno_pair : pair_wi conversion_mem (F.world true) HelloErrnoChecks.heap.
Proof.
  destruct T.entry_wi as (_ & _ & _ & _ & _ & _ & Ho & He & Hprivate).
  split; [split; [reflexivity|simpl; lia]|]. split; [split; [reflexivity|simpl; lia]|].
  split; [discriminate|]. split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold stream_current. destruct (HelloErrnoChecks.heap !! PName (token_key P.out)) as [v|] eqn:E;
      [destruct (T.entry_keys _ _ E) as [i Hbad]; discriminate Hbad|exact I]. }
  split.
  { unfold stream_current. destruct (HelloErrnoChecks.heap !! PName (token_key P.err)) as [v|] eqn:E;
      [destruct (T.entry_keys _ _ E) as [i Hbad]; discriminate Hbad|exact I]. }
  intros d [-> | ->]; [exact (Hprivate T.out (or_introl eq_refl))|exact (Hprivate T.err (or_intror eq_refl))].
Qed.

Lemma entry_agrees : agrees conversion_mem entry_heap.
Proof.
  intros l v Hl. unfold entry_heap in Hl.
  apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]]; [subst l v; exact I|].
  apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]]; [subst l v; exact I|].
  exact (HelloErrnoChecks.heap_agrees l v Hl).
Qed.

Lemma entry_fresh : forall l v, (l, v) ∈ pair_ps -> entry_heap !! l = None.
Proof.
  intros l v Hin. destruct (entry_heap !! l) as [old|] eqn:E; [|reflexivity].
  unfold entry_heap in E. apply list_elem_of_In in Hin.
  cbn [pair_ps open_permission_ps app P.out P.err token_base token_key] in Hin.
  destruct Hin as [El|[El|[El|[El|[]]]]]; injection El as <- <-.
  all: repeat (rewrite lookup_insert_ne in E; [|discriminate]).
  all: rewrite lookup_empty in E; discriminate E.
Qed.

Lemma entry_inhabited : callback_wi conversion_mem (F.world true) entry_heap.
Proof.
  split.
  - eapply stream_tokens_name_update; [discriminate|discriminate|].
    eapply stream_tokens_name_update; [discriminate|discriminate|exact errno_pair].
  - left. split; [apply lookup_insert_eq|].
    split; [split; reflexivity|]. split; [split; reflexivity|].
    split; [exists (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7); reflexivity|].
    split; [exists (mkStreamInfo 2 stdout_initial 3); reflexivity|exact entry_fresh].
Qed.

(** The endpoint has the after lookup, not another allocation ticket.
    The native state, errno and unrelated name have not changed. *)
Example transfer_endpoint :
  let h := <[PName stage := after]> (overwrite pair_ps entry_heap) in
  agrees conversion_mem h /\ callback_wi conversion_mem (F.world true) h /\
  h !! PName stage = Some after /\ h !! PName stage <> Some before /\
  h !! PByte 5120 3 = Some (VByte 0) /\
  h !! PName (-7) = Some (VCodec (TAtom "unrelated")).
Proof.
  intro h. destruct entry_inhabited as [Hpair [[Hs Hadmit]|Hs]];
    [|unfold entry_heap in Hs; rewrite lookup_insert_eq in Hs; discriminate Hs].
  destruct Hadmit as (Hol & Hel & Hoo & Heo & Hfresh).
  destruct (permission_entry_frame (fun _ _ => True) P.out P.err 5120 0 _ _ _
    entry_agrees Hpair Hol Hel Hoo Heo) as [HaA HwA].
  assert (Hfinal : pair_wi conversion_mem (F.world true) h).
  { eapply stream_tokens_name_update; [discriminate|discriminate|exact HwA]. }
  split.
  - intros l v Hl. apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]].
    + subst l v. exact I.
    + exact (HaA _ _ Hl).
  - split; [apply entry_restored; [exact entry_inhabited|exact Hs|exact Hfinal]|].
    split; [apply lookup_insert_eq|]. split.
    + rewrite lookup_insert_eq. discriminate.
    + unfold h, pair_ps, entry_heap.
      cbn [open_permission_ps P.out P.err token_base token_key overwrite app fst snd].
      split; repeat (rewrite lookup_insert_ne; [|discriminate]); apply lookup_insert_eq.
Qed.

Example occupied_life_rejected :
  live_at conversion_mem (token_base P.out) (token_region P.out) /\
  ~ admission conversion_mem (F.world true)
    (<[PLive (token_base P.out) := VLive (token_region P.out)]> entry_heap).
Proof.
  split; [split; reflexivity|]. intros (_ & _ & _ & _ & Hfresh).
  assert (Hin : (PLive (token_base P.out), VLive (token_region P.out)) ∈ pair_ps).
  { apply elem_of_app. left. apply elem_of_cons. left. reflexivity. }
  specialize (Hfresh _ _ Hin). rewrite lookup_insert_eq in Hfresh. discriminate Hfresh.
Qed.

Example occupied_name_rejected :
  live_at conversion_mem (token_base P.out) (token_region P.out) /\
  ~ admission conversion_mem (F.world true)
    (<[PName (token_key P.out) := VCodec (TAtom "occupied")]> entry_heap).
Proof.
  split; [split; reflexivity|]. intros (_ & _ & _ & _ & Hfresh).
  assert (Hin : (PName (token_key P.out), VStreamOpen (token_handle P.out)) ∈ pair_ps).
  { apply elem_of_app. left. apply elem_of_cons. right. apply elem_of_cons. left. reflexivity. }
  specialize (Hfresh _ _ Hin). rewrite lookup_insert_eq in Hfresh. discriminate Hfresh.
Qed.

Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** Apply the wrapper with actual authoritative and owned resources,
    not abstract Hentry/Kentry assumptions. Both independent frames stay. *)
Example callback_transfer_resources :
  gen_heap_interp entry_heap ∗ pts [(PName stage, before)] ∗
    pts (byte_ps 5120 0 [0; 0; 0; 0]) ∗ pts unrelated ==∗
  heap_interp callback_wi (mkLstate conversion_mem InterpRuntime.start 64 (F.world true)) ∗
    pts [(PName stage, after)] ∗ pts (open_permission_ps P.out (token_handle P.out)) ∗
    pts (open_permission_ps P.err (token_handle P.err)) ∗
    pts (byte_ps 5120 0 [0; 0; 0; 0]) ∗ pts unrelated.
Proof.
  iIntros "(Hh & Hstage & Herrno & Hother)".
  iAssert (heap_interp callback_wi
    (mkLstate conversion_mem InterpRuntime.start 64 (F.world true))) with "[Hh]" as "Hσ".
  { iExists entry_heap. iFrame. iPureIntro.
    exact (conj entry_agrees (conj HelloErrnoChecks.disjoint
      (conj HelloErrnoChecks.ready entry_inhabited))). }
  iMod (H.hello_callback_transfer callback_wi (fun _ _ => True) P.out P.err 5120 0
    stage before after entry_admitted entry_restored with "Hσ Hstage") as "(Hσ & Hstage & Ho & He)".
  - unfold stage. lia.
  - discriminate.
  - discriminate.
  - discriminate.
  - intros m. exact I.
  - iModIntro. iFrame.
Qed.

End iris.
End HelloTransferChecks.

(** Consume the entry ticket INSIDE WP, use the resulting permission
    for an actual fclose instruction and retain all independent frames. *)
Module HelloTransferWPChecks.
Import HelloCallbackChecks HelloTransferChecks.
Module P := StreamPermissionChecks.
Import LG LG.L.

Lemma close_restored : forall m w h m' w' ys,
  (forall l v, (l, v) ∈ permission_ps P.out P.err (token_handle P.out) ++
    byte_ps 5120 0 [0; 0; 0; 0] -> h !! l = Some v) ->
  callback_wi m w h ->
  pair_wi m' w' (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) h) ->
  callback_wi m' w' (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) h).
Proof.
  intros m w h m' w' ys Hl [_ [[Hs (_ & _ & _ & _ & Hfresh)]|Hs]] Hw.
  - exfalso.
    assert (Hin : (PLive (token_base P.out), VLive (token_region P.out)) ∈ pair_ps).
    { apply elem_of_app. left. apply elem_of_cons. left. reflexivity. }
    specialize (Hfresh _ _ Hin).
    assert (Hold : h !! PLive (token_base P.out) = Some (VLive (token_region P.out))).
    { apply Hl, elem_of_app. left. change ((PLive (token_base P.out), VLive (token_region P.out)) ∈
        open_permission_ps P.out (token_handle P.out)). apply elem_of_cons. left. reflexivity. }
    congruence.
  - split; [exact Hw|]. right. rewrite overwrite_app.
    cbn [closed_ps overwrite fst snd].
    rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_ne; [|discriminate].
    rewrite overwrite_out; [exact Hs|].
    rewrite byte_ps_keys. intros Hin. apply list_elem_of_fmap in Hin as (i & E & _). discriminate E.
Qed.

Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Local Instance test_stable : SafepointStable callback_wi := callback_stable.
Local Instance test_irisGS : irisGS_gen hlc
    (nanofil_lang HelloPermissionChecks.registry HelloPermissionChecks.ge) Σ :=
  nanofil_irisGS HelloPermissionChecks.registry callback_wi HelloPermissionChecks.ge.

Example transfer_close_return :
  pts [(PName stage, before)] -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗ pts unrelated -∗
  WP (ERun (mkFrame HelloPermissionChecks.stub HelloPermissionChecks.entry_env [] None
    (Exec (TAtom "body")
      [Call (CResult (TAtom "r") W) (Global (TAtom "fclose")) [Arg P (Tmp (TAtom "p"))]]
      (JRet (Tmp (TAtom "r"))))) : language.expr
    (nanofil_lang HelloPermissionChecks.registry HelloPermissionChecks.ge))
  {{ result, ∃ n ys, ⌜result = Ret (WInt n) /\ length ys = 4%nat⌝ ∗
    pts [(PName stage, after)] ∗ pts (closed_ps P.out) ∗
    pts (open_permission_ps P.err (token_handle P.err)) ∗
    pts (byte_ps 5120 0 ys) ∗ pts unrelated }}.
Proof.
  iIntros "Hstage Herrno Hother".
  iApply (H.wp_callback_transfer HelloPermissionChecks.registry callback_wi HelloPermissionChecks.ge
    (pts [(PName stage, before)])
    (pts [(PName stage, after)] ∗ pts (open_permission_ps P.out (token_handle P.out)) ∗
      pts (open_permission_ps P.err (token_handle P.err)))%I _ _ with "Hstage [Herrno Hother]").
  - intros σ. iApply (H.hello_callback_transfer callback_wi (fun _ _ => True) P.out P.err 5120 0
      stage before after entry_admitted entry_restored).
    + unfold stage. lia.
    + discriminate.
    + discriminate.
    + discriminate.
    + intros m. exact I.
  - iIntros "(Hstage & Ho & He)".
    iApply (H.wp_permission_fclose HelloPermissionChecks.registry callback_wi HelloPermissionChecks.ge
      (fun _ _ => True) (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
      P.out P.err 5120 0 (token_handle P.out) [0; 0; 0; 0]
      HelloPermissionChecks.stub HelloPermissionChecks.entry_env [] (TAtom "body") (TAtom "r")
      (Tmp (TAtom "p")) [] (JRet (Tmp (TAtom "r"))) _ with "Ho Herrno [Hstage He Hother]").
    + intros m w h Hw. exact (proj1 Hw).
    + intros s m w h tr vs s' m' w' ys Hi Hl Hw Hlen Hnew.
      eapply close_restored; eauto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + iNext. iIntros (n ys) "%Hgood Ho Herrno". destruct Hgood as [Hn Hys].
      iApply (wp_ret HelloPermissionChecks.registry callback_wi HelloPermissionChecks.ge
        HelloPermissionChecks.stub _ (TAtom "body") (Tmp (TAtom "r")) W (WInt n));
        [reflexivity| |].
      * change (Some (WInt (n mod 2 ^ 32)) = Some (WInt n)).
        rewrite Z.mod_small; [reflexivity|exact Hn].
      * iNext. iExists n, ys. iFrame. auto.
Qed.

End iris.
End HelloTransferWPChecks.

(** Pointer-universal queries on the same callback interpretation and
    supplied machine. These are logical contract/resource controls. *)
Module HelloQueryChecks.
Import HelloCallbackChecks HelloTransferChecks.
Module P := StreamPermissionChecks.
Module F := LibcStreamChecks.
Import LG LG.L.

Definition spec g := if name_eqb g (TAtom "ferror") then ferror_contract F.model else fpending_contract F.model.
Definition registry := libc_stream_registry (fun _ _ => True) (fun _ _ _ _ => False)
  (fun _ _ _ _ _ => False) (fun _ => None).
Definition ge := HelloPermissionChecks.ge.
Definition stub k := mkFunc (TAtom "query-control") (TAtom "local") (RClass k) [] [].
Definition entry_env p := [(TAtom "p", WPtr p)].

Lemma spec_choice : forall g k,
  (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
  (spec g = ferror_contract F.model /\ k = W) \/ (spec g = fpending_contract F.model /\ k = L).
Proof. intros g k [[-> ->]|[-> ->]]; [right|left]; split; reflexivity. Qed.

Lemma query_restored : forall p m w h m' w',
  callback_wi m w h ->
  (forall l v, (l, v) ∈ permission_ps P.out P.err p -> h !! l = Some v) ->
  pair_wi m' w' h -> callback_wi m' w' h.
Proof.
  intros p m w h m' w' [_ [[Hs (_ & _ & _ & _ & Hfresh)]|Hs]] Hl Hw.
  - exfalso.
    assert (Hlife : (PLive (token_base (permission_descriptor P.out P.err p)),
        VLive (token_region (permission_descriptor P.out P.err p))) ∈ permission_ps P.out P.err p).
    { apply elem_of_cons. left. reflexivity. }
    assert (Hpair : (PLive (token_base (permission_descriptor P.out P.err p)),
        VLive (token_region (permission_descriptor P.out P.err p))) ∈ pair_ps).
    { destruct (permission_selected P.out P.err p) as [-> | ->]; apply elem_of_app;
        [left|right]; apply elem_of_cons; left; reflexivity. }
    specialize (Hfresh _ _ Hpair). specialize (Hl _ _ Hlife). congruence.
  - split; [exact Hw|]. right. exact Hs.
Qed.

Definition query_heap : gmap piece pval :=
  <[PName stage := after]> (overwrite pair_ps entry_heap).
Definition query_handle (stdout : bool) := if stdout then token_handle P.out else token_handle P.err.
Definition query_name (error : bool) := if error then TAtom "ferror" else TAtom "__fpending".
Definition query_class (error : bool) := if error then W else L.
Definition query_result (error stdout : bool) : Z := if error then (if stdout then 17 else 0)
  else (if stdout then 7 else 3).

Lemma query_lookups : forall stdout l v,
  (l, v) ∈ permission_ps P.out P.err (query_handle stdout) -> query_heap !! l = Some v.
Proof.
  intros stdout l v Hin. destruct stdout;
    [change ((l, v) ∈ open_permission_ps P.out (token_handle P.out)) in Hin|
     change ((l, v) ∈ open_permission_ps P.err (token_handle P.err)) in Hin].
  all: apply list_elem_of_In in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-.
  all: unfold query_heap, pair_ps, entry_heap;
    cbn [open_permission_ps overwrite app fst snd P.out P.err token_base token_key];
    repeat (rewrite lookup_insert_ne; [|discriminate]); apply lookup_insert_eq.
Qed.

(** Non-one sticky error, rather than normalizing every nonzero result. *)
Lemma stdout_error_seventeen :
  H.M.E.invoke (ferror_contract F.model) (CResult (TAtom "r") W) [Arg P (Tmp (TAtom "p"))]
    [WPtr (token_handle P.out)] InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt 17]) InterpRuntime.start conversion_mem (F.world true).
Proof.
  destruct (libc_stream_open (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) conversion_mem (F.world true) (token_handle P.out) F.out_file
    (F.ready true) eq_refl) as [info Ho].
  eapply H.SL.S.S.ferror_return with (born := []).
  - split; [right; eexists; reflexivity|eexists; reflexivity].
  - exists (token_handle P.out), info. auto.
  - split; [constructor|]. exists (token_handle P.out), info.
    split; [reflexivity|]. split; [exact (proj1 (proj2 Ho))|]. split; [exact Ho|].
    split; [apply libc_stream_frame_refl|].
    split; [apply libc_stream_delegates_refl; apply F.ready|]. split; [reflexivity|].
    split; [unfold stream_aux_frame|]; intros; reflexivity.
  - exists (token_handle P.out), info, 17.
    split; [reflexivity|]. split; [exact (proj1 (proj2 Ho))|]. split; [exact Ho|].
    split; [apply libc_stream_frame_refl|].
    split; [apply libc_stream_delegates_refl; apply F.ready|].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    destruct Ho as (_ & _ & Hstate & _). rewrite Hstate. cbn. split; discriminate.
Qed.

Lemma query_invocation : forall error stdout,
  H.M.E.invoke (spec (query_name error)) (CResult (TAtom "r") (query_class error))
    [Arg P (Tmp (TAtom "p"))] [WPtr (query_handle stdout)]
    InterpRuntime.start conversion_mem (F.world true) []
    (CallReturn [WInt (query_result error stdout)]) InterpRuntime.start conversion_mem (F.world true).
Proof.
  intros error stdout. destruct error, stdout.
  - exact stdout_error_seventeen.
  - apply H.SL.S.ferror_unchanged with (file := F.err_file).
    + split; [right; eexists; reflexivity|eexists; reflexivity].
    + apply F.ready.
    + reflexivity.
  - apply H.SL.S.fpending_unchanged with (file := F.out_file).
    + split; [right; eexists; reflexivity|eexists; reflexivity].
    + apply F.ready.
    + reflexivity.
  - apply H.SL.S.fpending_unchanged with (file := F.err_file).
    + split; [right; eexists; reflexivity|eexists; reflexivity].
    + apply F.ready.
    + reflexivity.
Qed.

(** Both contract/classes on both handles, with current admission and
    inhabited after-stage ownership. Pending seven differs from FIFO two. *)
Example query_matrix : forall error stdout,
  stream_call_pre F.model [WPtr (query_handle stdout)] conversion_mem (F.world true) /\
  exists n, n = query_result error stdout /\
    0 <= n < 2 ^ (if class_eqb (query_class error) W then 32 else 64) /\
    agrees conversion_mem query_heap /\ callback_wi conversion_mem (F.world true) query_heap.
Proof.
  intros error stdout.
  destruct transfer_endpoint as (Ha & Hw & Hrest).
  assert (Hwhich : (spec (query_name error) = ferror_contract F.model /\ query_class error = W) \/
      (spec (query_name error) = fpending_contract F.model /\ query_class error = L)).
  { destruct error; [left|right]; split; reflexivity. }
  split.
  - eapply H.A.permission_admitted; [exact (proj1 Hw)|exact (query_lookups stdout)].
  - destruct (H.permission_query_frame (fun _ _ => True) (fun _ _ _ _ => False)
      (fun _ _ _ _ _ => False) P.out P.err 5120 0 (spec (query_name error)) (query_class error)
      (query_handle stdout) (TAtom "r") (Tmp (TAtom "p")) _ _ _ _ _ _ _ _ query_heap
      Hwhich Ha HelloErrnoChecks.disjoint HelloErrnoChecks.ready (proj1 Hw)
      (query_lookups stdout) (query_invocation error stdout)) as (n & Heq & Hn & Ha' & _ & _ & Hpair).
    injection Heq as <-. exists (query_result error stdout).
    split; [reflexivity|]. split; [exact Hn|]. split; [exact Ha'|].
    eapply query_restored; [exact Hw|exact (query_lookups stdout)|exact Hpair].
Qed.

Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Local Instance test_stable : SafepointStable callback_wi := callback_stable.
Local Instance test_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry callback_wi ge.

(** Use the existing contract bridge, with actual outside/unbound facts
    for this empty ge, not an assumed full Hello linkage. *)
Example query_return g k p other :
  (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
  pts (permission_ps P.out P.err p) -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗
  pts [(PName stage, after)] -∗ pts other -∗
  WP (ERun (mkFrame (stub k) (entry_env p) [] None
    (Exec (TAtom "body") [Call (CResult (TAtom "r") k) (Global g) [Arg P (Tmp (TAtom "p"))]]
      (JRet (Tmp (TAtom "r"))))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ n, ⌜result = Ret (WInt n) /\ 0 <= n < 2 ^ (if class_eqb k W then 32 else 64)⌝ ∗
    pts (permission_ps P.out P.err p) ∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) ∗
    pts [(PName stage, after)] ∗ pts other }}.
Proof.
  intros Hwhich. iIntros "Ho Herrno Hstage Hother".
  iApply (H.C.wp_close_contract registry callback_wi ge (stub k) (entry_env p) [] (TAtom "body")
    (TAtom "r") k g [Arg P (Tmp (TAtom "p"))] [] (JRet (Tmp (TAtom "r"))) (spec g) [WPtr p]
    (permission_ps P.out P.err p ++ byte_ps 5120 0 [0; 0; 0; 0])
    (fun _ => permission_ps P.out P.err p ++ byte_ps 5120 0 [0; 0; 0; 0])
    (fun n _ => 0 <= n < 2 ^ (if class_eqb k W then 32 else 64)) with "[Ho Herrno] [Hstage Hother]").
  - reflexivity.
  - reflexivity.
  - destruct Hwhich as [[-> ->]|[-> ->]]; reflexivity.
  - destruct Hwhich as [[-> ->]|[-> ->]]; reflexivity.
  - destruct Hwhich as [[-> ->]|[-> ->]]; reflexivity.
  - destruct Hwhich as [[_ ->]|[_ ->]]; auto.
  - reflexivity.
  - destruct Hwhich as [[-> ->]|[-> ->]];
      (split; [right; eexists; reflexivity|eexists; reflexivity]).
  - intros m w h Hw Hl.
    assert (Hpre : stream_call_pre F.model [WPtr p] m w).
    { eapply H.A.permission_admitted; [exact (proj1 Hw)|].
      intros l v Hin. apply Hl, elem_of_app. left. exact Hin. }
    destruct Hwhich as [[-> ->]|[-> ->]]; exact Hpre.
  - intros s m w h tr vs s' m' w' Ha Hd Hr Hw Hl Hi.
    assert (Howned : forall l v, (l, v) ∈ permission_ps P.out P.err p -> h !! l = Some v).
    { intros l v Hin. apply Hl, elem_of_app. left. exact Hin. }
    destruct (H.permission_query_frame (fun _ _ => True) (fun _ _ _ _ => False)
      (fun _ _ _ _ _ => False) P.out P.err 5120 0 (spec g) k p (TAtom "r") (Tmp (TAtom "p"))
      s m w tr vs s' m' w' h (spec_choice g k Hwhich) Ha Hd Hr (proj1 Hw) Howned Hi)
      as (n & Hvs & Hn & Ha' & Hd' & Hr' & Hpair).
    exists n, [0; 0; 0; 0]. rewrite (overwrite_id _ h Hl).
    split; [exact Hvs|]. split; [exact Hn|]. split; [exact Hn|]. split; [reflexivity|].
    split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|].
    eapply query_restored; eauto.
  - rewrite pts_app. iFrame.
  - iNext. iIntros (n ys Hn) "Hps". rewrite pts_app. iDestruct "Hps" as "[Ho Herrno]".
    iApply (wp_ret registry callback_wi ge (stub k) _ (TAtom "body") (Tmp (TAtom "r")) k (WInt n));
      [reflexivity| |].
    + destruct Hwhich as [[_ ->]|[_ ->]].
      * change (Some (WInt (n mod 2 ^ 64)) = Some (WInt n)).
        rewrite Z.mod_small; [reflexivity|exact Hn].
      * change (Some (WInt (n mod 2 ^ 32)) = Some (WInt n)).
        rewrite Z.mod_small; [reflexivity|exact Hn].
    + iNext. iExists n. iFrame. auto.
Qed.

(** Entry supplies the selected and opposite permissions; the query
    returns both, along with consumed stage, errno and unrelated name. *)
Example transfer_query_return (error stdout : bool) :
  let opposite := if stdout then P.err else P.out in
  pts [(PName stage, before)] -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗ pts unrelated -∗
  WP (ERun (mkFrame (stub (query_class error)) (entry_env (query_handle stdout)) [] None
    (Exec (TAtom "body")
      [Call (CResult (TAtom "r") (query_class error)) (Global (query_name error)) [Arg P (Tmp (TAtom "p"))]]
      (JRet (Tmp (TAtom "r"))))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ n, ⌜result = Ret (WInt n) /\ 0 <= n < 2 ^ (if class_eqb (query_class error) W then 32 else 64)⌝ ∗
    pts (permission_ps P.out P.err (query_handle stdout)) ∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) ∗
    pts [(PName stage, after)] ∗ pts (open_permission_ps opposite (token_handle opposite) ++ unrelated) }}.
Proof.
  intro opposite. iIntros "Hstage Herrno Hother".
  iApply (H.wp_callback_transfer registry callback_wi ge (pts [(PName stage, before)])
    (pts [(PName stage, after)] ∗ pts (open_permission_ps P.out (token_handle P.out)) ∗
      pts (open_permission_ps P.err (token_handle P.err)))%I _ _ with "Hstage [Herrno Hother]").
  - intros σ. iApply (H.hello_callback_transfer callback_wi (fun _ _ => True) P.out P.err 5120 0
      stage before after entry_admitted entry_restored).
    + unfold stage. lia.
    + discriminate.
    + discriminate.
    + discriminate.
    + intros m. exact I.
  - iIntros "(Hstage & Ho & He)". destruct stdout.
    + iApply (query_return (query_name error) (query_class error) (query_handle true) _
        with "Ho Herrno Hstage [He Hother]").
      * destruct error; [right|left]; split; reflexivity.
      * rewrite pts_app. iFrame.
    + iApply (query_return (query_name error) (query_class error) (query_handle false) _
        with "He Herrno Hstage [Ho Hother]").
      * destruct error; [right|left]; split; reflexivity.
      * rewrite pts_app. iFrame.
Qed.

End iris.
End HelloQueryChecks.
