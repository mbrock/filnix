(** Admission of Hello's actual version/footer literals. The bytes and
    object bounds come from the linked fixture, but current memory is
    read from program-owned pieces, not assumed to equal startup memory. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run
  ExternalCalls LibcCalls ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams LibcExit
  Pieces Heap ContractFrame Logic StringLogic LibcStringLogic LentLogic LibcStreamLogic LibcErrnoLogic
  LibcStreamTokens LibcStreamAdapter LibcDiagnosticLogic
  HelloModule HelloLeaf HelloVersion HelloClose.
From Nanofil Require HelloStdioLiterals.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Include HelloStdioLiterals.HelloStdioLiterals.

(** Class-only admission of the selected promoted ABI, independent of
    argument expressions and their evaluated values. *)
Lemma promoted_classes : forall args,
  Forall (fun k => k = P \/ k = W) (map (fun a => match a with Arg k _ => k end) args) ->
  Forall promoted_argument args.
Proof.
  intros args H. induction args as [|[k v] args IH]; [constructor|].
  inversion H as [|? ? Hk Hrest]; subst. constructor; [exists v; destruct Hk; subst; auto|auto].
Qed.

Lemma output_abi_classes : forall api d args,
  (match api with
  | NarrowPrintf => exists rest,
      map (fun a => match a with Arg k _ => k end) args = P :: rest /\
      Forall (fun k => k = P \/ k = W) rest
  | NarrowFprintf => exists rest,
      map (fun a => match a with Arg k _ => k end) args = P :: P :: rest /\
      Forall (fun k => k = P \/ k = W) rest
  | NarrowFputs => map (fun a => match a with Arg k _ => k end) args = [P; P]
  end) -> output_abi api (CResult d W) args.
Proof.
  intros api d args H. split; [right; exists d; reflexivity|]. destruct api.
  - destruct H as (rest & Hargs & Hrest).
    destruct args as [|[k fmt] args]; [discriminate|]. injection Hargs as -> Hargs.
    exists fmt, args. split; [reflexivity|]. apply promoted_classes. rewrite Hargs. exact Hrest.
  - destruct H as (rest & Hargs & Hrest).
    destruct args as [|[k file] [|[k' fmt] args]]; try discriminate.
    injection Hargs as -> -> Hargs. exists file, fmt, args. split; [reflexivity|].
    apply promoted_classes. rewrite Hargs. exact Hrest.
  - destruct args as [|[k text] [|[k' file] [|extra args]]]; try discriminate.
    injection H as -> ->. exists text, file. reflexivity.
Qed.

Lemma hello_version_registry : forall rep requests wide fallback stream g xs,
  In (g, xs) (version_output_args stream) ->
  libc_stream_registry rep requests wide fallback g = Some (hello_output_spec rep requests wide g).
Proof.
  intros rep requests wide fallback stream g xs Hin.
  repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-; reflexivity.
Qed.

Lemma hello_footer_registry : forall rep requests wide fallback stream g xs,
  In (g, xs) (emit_output_args stream) ->
  libc_stream_registry rep requests wide fallback g = Some (hello_output_spec rep requests wide g).
Proof.
  intros rep requests wide fallback stream g xs Hin.
  repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-; reflexivity.
Qed.

Lemma hello_output_return_class : forall rep requests wide g,
  contract_returns (hello_output_spec rep requests wide g) = RClass W.
Proof. reflexivity. Qed.

Lemma hello_version_abi : forall stream g xs d args,
  In (g, xs) (version_output_args stream) ->
  map (fun a => match a with Arg k _ => k end) args = version_output_classes xs ->
  output_abi (hello_output_api g) (CResult d W) args.
Proof.
  intros stream g xs d args Hin Hclasses. apply output_abi_classes.
  repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-;
    cbn [hello_output_api name_eqb]; try exact Hclasses.
  all: (eexists; split; [exact Hclasses|repeat (apply Forall_cons; [auto|]); constructor]).
Qed.

Lemma hello_footer_abi : forall stream g xs d args,
  In (g, xs) (emit_output_args stream) ->
  map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
  output_abi (hello_output_api g) (CResult d W) args.
Proof.
  intros stream g xs d args Hin Hclasses. apply output_abi_classes.
  repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-;
    cbn [hello_output_api name_eqb]; try exact Hclasses.
  all: (eexists; split; [exact Hclasses|repeat (apply Forall_cons; [auto|]); constructor]).
Qed.

(** Actual stdout-facing version/footer calls keep their stream open
    and non-wide. The fixed handle is a world fact, not a second token. *)
Definition hello_stdio_wi rep stream m w h : Prop :=
  libc_stream_wi rep stream m w h /\ libc_stdout w = stream /\
  (exists file, libc_file_at w stream = Some file) /\
  orientation (libc_stream_state w stream) <> WideOriented.

Lemma hello_version_target : forall stream g xs w,
  In (g, xs) (version_output_args stream) ->
  output_target (hello_output_api g) libc_stdout w xs = stream.
Proof.
  intros stream g xs w Hin.
  repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-; reflexivity.
Qed.

Lemma hello_footer_target : forall stream g xs w,
  In (g, xs) (emit_output_args stream) -> libc_stdout w = stream ->
  output_target (hello_output_api g) libc_stdout w xs = stream.
Proof.
  intros stream g xs w Hin Hstdout.
  repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-; auto.
Qed.

Lemma hello_version_admitted : forall rep requests wide stream g xs m w h,
  In (g, xs) (version_output_args stream) ->
  (forall l v, (l, v) ∈ hello_output_pieces -> h !! l = Some v) ->
  agrees m h -> hello_stdio_wi rep stream m w h ->
  contract_pre (hello_output_spec rep requests wide g) xs m w.
Proof.
  intros rep requests wide stream g xs m w h Hin Howned Ha ((Hr & _) & Hstdout & Hfile & Hn).
  destruct (hello_version_text stream g xs m h Hin Howned Ha) as [bytes Htext].
  unfold hello_output_spec. destruct Hfile as [file Hfile].
  apply libc_output_admitted with (file := file) (bytes := bytes); [exact Hr| | |exact Htext];
    rewrite (hello_version_target _ _ _ _ Hin); assumption.
Qed.

Lemma hello_footer_admitted : forall rep requests wide stream g xs m w h,
  In (g, xs) (emit_output_args stream) ->
  (forall l v, (l, v) ∈ hello_output_pieces -> h !! l = Some v) ->
  agrees m h -> hello_stdio_wi rep stream m w h ->
  contract_pre (hello_output_spec rep requests wide g) xs m w.
Proof.
  intros rep requests wide stream g xs m w h Hin Howned Ha ((Hr & _) & Hstdout & Hfile & Hn).
  destruct (hello_footer_text stream g xs m h Hin Howned Ha) as [bytes Htext].
  unfold hello_output_spec. destruct Hfile as [file Hfile].
  apply libc_output_admitted with (file := file) (bytes := bytes); [exact Hr| | |exact Htext];
    rewrite (hello_footer_target _ _ _ _ Hin Hstdout); assumption.
Qed.

(** The actual author life-token premise, with fixture-derived regions. *)
Lemma hello_author_live : forall s,
  In s ["hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75"] ->
  (PLive (ptr_addr (version_literal s)), VLive (hello_literal_region s)) ∈ hello_output_pieces.
Proof.
  intros s Hin. apply list_elem_of_In. unfold hello_output_pieces. apply in_flat_map.
  exists s. split; [simpl in *; tauto|]. left. reflexivity.
Qed.

(** Bind the very machine used by HelloVersion's triples. The proofs
    below type-check invocation transport across the helper aliases. *)
Module HelloStdioOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module V. Include HelloVersionOn R LG0. End V.
Module M := V.L.M.
Module SL := LibcStreamLogicOn R LG0.
Module C. Include HelloCloseOn R LG0. End C.
Module X := LibcExitOn R C.L.M.
Module A := LibcStreamAdapterOn R LG0.
Module D := LibcDiagnosticLogicOn R LG0.

(** The ordinary endpoint has exactly the overwrite shape consumed by
    HelloClose. The life insertion is redundant only because it is OWNED
    at entry; the name and errno updates still need their Iris fragments. *)
Theorem hello_fclose_frame : forall rep requests wide out err b o dt pending fifo xs
    r args s m w trace values s' m' w' h,
  dt = out \/ dt = err -> length xs = 4%nat ->
  agrees m h -> live_disjoint m -> R.ready s m -> stream_tokens_wi rep out err b o m w h ->
  (forall l v, (l, v) ∈ stream_ps dt pending fifo ++ byte_ps b o xs -> h !! l = Some v) ->
  M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
    r args [WPtr (token_handle dt)] s m w trace (CallReturn values) s' m' w' ->
  exists n ys, values = [WInt n] /\ 0 <= n < 2 ^ 32 /\ length ys = 4%nat /\
    (closed_ps dt ++ byte_ps b o ys).*1 = (stream_ps dt pending fifo ++ byte_ps b o xs).*1 /\
    agrees m' (overwrite (closed_ps dt ++ byte_ps b o ys) h) /\
    live_disjoint m' /\ R.ready s' m' /\
    stream_tokens_wi rep out err b o m' w' (overwrite (closed_ps dt ++ byte_ps b o ys) h).
Proof.
  intros rep requests wide out err b o dt pending fifo xs r args s m w trace values s' m' w' h
    Hdt Hxs Ha Hd Hr Hw Howned Hcall.
  destruct (A.close_frame rep requests wide out err b o dt r args s m w trace values s' m' w' h xs
    Hdt Hcall Ha Hd Hr Hw Hxs) as (ys & Hys & Hkeys & Ha' & Hd' & Hr' & Hw').
  { intros l v Hin. apply Howned, elem_of_app. right. exact Hin. }
  assert (Heq : overwrite (closed_ps dt ++ byte_ps b o ys) h =
    <[PName (token_key dt) := VStream (token_handle dt) None]> (overwrite (byte_ps b o ys) h)).
  { rewrite overwrite_app. cbn [closed_ps overwrite]. apply fin_maps.insert_id.
    rewrite lookup_insert_ne; [|discriminate]. rewrite overwrite_out.
    - apply Howned, elem_of_app. left. unfold stream_ps. apply elem_of_cons. left. reflexivity.
    - rewrite byte_ps_keys. intros Hin. apply list_elem_of_fmap in Hin as (i & E & _). discriminate E. }
  destruct (A.T.EL.S.fclose_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as [(born & p & info & final & n & _ & _ & _ & _ & Hn & _ & _ & _ & _ & _ & Hend)
      |(why & Hbad & _)]; [|discriminate Hbad].
  injection Hend as Hvalues. subst values. exists n, ys. split; [reflexivity|]. split.
  { destruct Hn as [-> | ->]; unfold stream_eof; lia. }
  split; [exact Hys|]. split.
  { rewrite !fmap_app (stream_closed_keys dt pending fifo) Hkeys. reflexivity. }
  rewrite Heq. auto.
Qed.

(** Match HelloClose's pointer-universal query postcondition. Owned
    lookups select the actual full handle; the supplied machine gives
    canonical results. Preserve h, not necessarily native memory, and
    do not identify physical pending output with the logical FIFO. *)
Theorem permission_query_frame : forall rep requests wide out err b o spec k p
    d v s m w trace values s' m' w' h,
  ((spec = ferror_contract (libc_stream_model rep requests wide) /\ k = W) \/
   (spec = fpending_contract (libc_stream_model rep requests wide) /\ k = L)) ->
  agrees m h -> live_disjoint m -> R.ready s m -> stream_tokens_wi rep out err b o m w h ->
  (forall l v, (l, v) ∈ permission_ps out err p -> h !! l = Some v) ->
  M.E.invoke spec (CResult d k) [Arg P v] [WPtr p] s m w trace (CallReturn values) s' m' w' ->
  exists n, values = [WInt n] /\ 0 <= n < 2 ^ (if class_eqb k W then 32 else 64) /\
    agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ stream_tokens_wi rep out err b o m' w' h.
Proof.
  intros rep requests wide out err b o spec k p d v s m w tr vs s' m' w' h
    Hwhich Ha Hd Hr Hw Hl Hi.
  destruct (permission_known _ _ _ _ _ _ _ _ _ Hw Hl) as [Hp _].
  assert (Hspec : spec = ferror_contract (libc_stream_model rep requests wide) \/
    spec = fpending_contract (libc_stream_model rep requests wide)) by tauto.
  pose proof Hi as Hcall. rewrite Hp in Hcall.
  destruct (A.query_frame rep requests wide out err b o (permission_descriptor out err p)
    spec (CResult d k) [Arg P v] s m w tr (CallReturn vs) s' m' w' h
    (permission_selected out err p) Hspec Hcall Ha Hd Hr Hw) as (Ha' & Hd' & Hr' & Hw').
  assert (Hresult : exists n, vs = [WInt n] /\ 0 <= n < 2 ^ (if class_eqb k W then 32 else 64)).
  { destruct Hwhich as [[-> ->]|[-> ->]].
    - destruct (SL.S.S.ferror_invocation libc_world (libc_stream_model rep requests wide)
        (CResult d W) [Arg P v] [WPtr p] s m w tr (CallReturn vs) s' m' w' Hi)
        as (born & p0 & info & n & _ & _ & _ & _ & _ & _ & Hend & Hrange & _).
      injection Hend as ->. exists n. split; [reflexivity|exact Hrange].
    - destruct (SL.S.S.fpending_invocation libc_world (libc_stream_model rep requests wide)
        (CResult d L) [Arg P v] [WPtr p] s m w tr (CallReturn vs) s' m' w' Hi)
        as (born & p0 & info & _ & _ & Hopen & _ & _ & _ & Hend).
      destruct Hopen as (_ & _ & _ & [_ Hrange] & _).
      injection Hend as ->. exists (stream_pending info). split; [reflexivity|exact Hrange]. }
  destruct Hresult as (n & -> & Hn). exists n. split; [reflexivity|]. split; [exact Hn|].
  exact (conj Ha' (conj Hd' (conj Hr' Hw'))).
Qed.

(** The actual argument is checked by the permission value before
    selecting the paired frame. The returned token replaces that SAME
    permission key; no fixed pending/FIFO snapshot is needed. *)
Theorem permission_fclose_frame : forall rep requests wide out err b o p xs
    r args s m w trace values s' m' w' h,
  length xs = 4%nat ->
  agrees m h -> live_disjoint m -> R.ready s m -> stream_tokens_wi rep out err b o m w h ->
  (forall l v, (l, v) ∈ permission_ps out err p ++ byte_ps b o xs -> h !! l = Some v) ->
  M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
    r args [WPtr p] s m w trace (CallReturn values) s' m' w' ->
  exists n ys, values = [WInt n] /\ 0 <= n < 2 ^ 32 /\ length ys = 4%nat /\
    (closed_ps (permission_descriptor out err p) ++ byte_ps b o ys).*1 =
      (permission_ps out err p ++ byte_ps b o xs).*1 /\
    agrees m' (overwrite (closed_ps (permission_descriptor out err p) ++ byte_ps b o ys) h) /\
    live_disjoint m' /\ R.ready s' m' /\
    stream_tokens_wi rep out err b o m' w'
      (overwrite (closed_ps (permission_descriptor out err p) ++ byte_ps b o ys) h).
Proof.
  intros rep requests wide out err b o p xs r args s m w trace values s' m' w' h
    Hxs Ha Hd Hr Hw Howned Hcall.
  assert (Hps : forall l v, (l, v) ∈ permission_ps out err p -> h !! l = Some v).
  { intros l v Hin. apply Howned, elem_of_app. left. exact Hin. }
  destruct (permission_known _ _ _ _ _ _ _ _ _ Hw Hps) as [Hp _].
  set (dt := permission_descriptor out err p) in *.
  assert (Hcall' : M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
    r args [WPtr (token_handle dt)] s m w trace (CallReturn values) s' m' w').
  { rewrite <- Hp. exact Hcall. }
  destruct (A.close_frame rep requests wide out err b o dt r args s m w trace values s' m' w' h xs
    (permission_selected out err p) Hcall' Ha Hd Hr Hw Hxs) as (ys & Hys & Hkeys & Ha' & Hd' & Hr' & Hw').
  { intros l v Hin. apply Howned, elem_of_app. right. exact Hin. }
  assert (Heq : overwrite (closed_ps dt ++ byte_ps b o ys) h =
    <[PName (token_key dt) := VStream (token_handle dt) None]> (overwrite (byte_ps b o ys) h)).
  { rewrite overwrite_app. cbn [closed_ps overwrite]. apply fin_maps.insert_id.
    rewrite lookup_insert_ne; [|discriminate]. rewrite overwrite_out.
    - apply Hps. unfold permission_ps, open_permission_ps. fold dt.
      apply elem_of_cons. left. reflexivity.
    - rewrite byte_ps_keys. intros Hin. apply list_elem_of_fmap in Hin as (i & E & _). discriminate E. }
  destruct (A.T.EL.S.fclose_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as [(born & q & info & final & n & _ & _ & _ & _ & Hn & _ & _ & _ & _ & _ & Hend)
      |(why & Hbad & _)]; [|discriminate Hbad].
  injection Hend as Hvalues. subst values. exists n, ys. split; [reflexivity|]. split.
  { destruct Hn as [-> | ->]; unfold stream_eof; lia. }
  split; [exact Hys|]. split.
  { rewrite !fmap_app Hkeys. reflexivity. }
  rewrite Heq. auto.
Qed.

Section callback_rules.
Import LG LG.L.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance callback_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation cexpr := (language.expr (nanofil_lang registry ge)).

(** Instantiate the repaired HelloClose rule, with actual diagnostic
    strings and the supplied machine. Kerror restores the consumer's
    other pools; it does not assume the diagnostic postcondition. *)
Lemma wp_hello_error rep requests wide native out err b o f e ls lab v fmtv txtv rest j n xs Φ
    (Hdiagnostic : forall m w h, wi m w h ->
      libc_diagnostic_wi rep native out err b o m w h /\ diagnostic_ready native m w /\
      Forall (writable_span m) (diagnostic_writes native w) /\
      (exists file, libc_file_at w (libc_stderr w) = Some file) /\
      orientation (libc_stream_state w (libc_stderr w)) <> WideOriented)
    (Kerror : forall args words s m w trace values s' m' w' h ys,
      M.E.invoke (libc_error_contract rep requests wide native) CVoid args words
        s m w trace (CallReturn values) s' m' w' ->
      wi m w h -> length ys = 4%nat ->
      libc_diagnostic_wi rep native out err b o m' w'
        (overwrite (hello_diagnostic_pieces ++ byte_ps b o ys) h) ->
      wi m' w' (overwrite (hello_diagnostic_pieces ++ byte_ps b o ys) h)) :
  hello_linked ge -> b <> 65680 -> b <> 65744 ->
  registry (TAtom "error") = Some (libc_error_contract rep requests wide native) ->
  arg_x ge e (Arg W v) = Some (WInt n) ->
  arg_x ge e (Arg P fmtv) = Some (WPtr (mkPtr 65744 (Ro 65744))) ->
  arg_x ge e (Arg P txtv) = Some (WPtr (mkPtr 65680 (Ro 65680))) ->
  0 <= n < 2 ^ 32 -> length xs = 4%nat ->
  pts hello_diagnostic_pieces -∗ C.ML.bytes b o xs -∗
  ▷ (∀ ys, ⌜length ys = 4%nat⌝ -∗ pts hello_diagnostic_pieces -∗ C.ML.bytes b o ys -∗
    WP (ERun (mkFrame f e ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Call CVoid (Global (TAtom "error")) [Arg W (Const 0); Arg W v; Arg P fmtv; Arg P txtv] :: rest) j))
    : cexpr) {{ Φ }}.
Proof.
  intros Hlinked Hb Hf Hreg Hv Hfmt Htext Hn Hlen. iIntros "Hps Hx HK".
  iApply (C.wp_close_error registry wi ge b o Hlinked hello_diagnostic_pieces
    (libc_error_contract rep requests wide native) Hreg with "Hps Hx HK").
  - reflexivity.
  - intros. split; [reflexivity|]. split.
    + split; [reflexivity|]. do 4 eexists. split; [reflexivity|].
      constructor; [eexists; left; reflexivity|constructor].
    + do 4 eexists. reflexivity.
  - intros nn old m w h Hnn Hold Ha Hw Hl.
    destruct (Hdiagnostic _ _ _ Hw) as (Ht & Hnative & Hwrites & [file Hfile] & Hnarrow).
    eapply hello_diagnostic_admitted; [exact Hnn|exact Ha| |exact Hnative|
      |exact Hwrites|exact Hfile|exact Hnarrow].
    + intros l u Hin. apply Hl, elem_of_app. left. exact Hin.
    + destruct (proj1 Ht) as (_ & _ & _ & _ & _ & _ & _ & _ & Hprivate).
      exact (proj1 (proj1 (Hprivate out (or_introl eq_refl)))).
  - intros vv ff tt nn old s m w h tr vs s' m' w' Hold Ha Hd Hr Hw Hl Hi.
    destruct (Hdiagnostic _ _ _ Hw) as (Ht & _).
    destruct (D.error_pieces_frame rep requests wide native out err b o hello_diagnostic_pieces
      _ _ _ s m w tr vs s' m' w' h old Hi Ha Hd Hr Ht Hold Hl
      (hello_diagnostic_errno_keys b o Hb Hf)) as (ys & Hvs & Hys & Hkeys & Ha' & Hd' & Hr' & Ht').
    exists ys. split; [exact Hvs|]. split; [exact Hys|]. split; [exact Hkeys|].
    split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|].
    eapply Kerror; eauto.
  - exact Hv.
  - exact Hfmt.
  - exact Htext.
  - exact Hn.
  - exact Hlen.
Qed.

(** Expose the CURRENT authoritative heap at this boundary, not a saved
    main-entry heap. Freshness belongs only to this one allocation: it is
    not an invariant the post-state must re-establish. Unneeded main
    resources frame through. Kentry supplies compatibility with the
    consumer's other private pools without switching its interpretation. *)
Lemma hello_callback_entry rep out err b o σ h op oq ep eq
    (Kentry : wi (ls_mem σ) (ls_world σ) h ->
      stream_tokens_wi rep out err b o (ls_mem σ) (ls_world σ)
        (overwrite (stream_ps out op oq ++ stream_ps err ep eq) h) ->
      wi (ls_mem σ) (ls_world σ) (overwrite (stream_ps out op oq ++ stream_ps err ep eq) h)) :
  agrees (ls_mem σ) h -> live_disjoint (ls_mem σ) -> R.ready (ls_rt σ) (ls_mem σ) ->
  wi (ls_mem σ) (ls_world σ) h -> stream_tokens_wi rep out err b o (ls_mem σ) (ls_world σ) h ->
  live_at (ls_mem σ) (token_base out) (token_region out) ->
  live_at (ls_mem σ) (token_base err) (token_region err) ->
  stream_observation (ls_world σ) (token_handle out) (Some (op, oq)) ->
  stream_observation (ls_world σ) (token_handle err) (Some (ep, eq)) ->
  (forall l v, (l, v) ∈ stream_ps out op oq ++ stream_ps err ep eq -> h !! l = None) ->
  gen_heap_interp h ==∗ heap_interp wi σ ∗
    pts (stream_ps out op oq) ∗ pts (stream_ps err ep eq).
Proof.
  intros Ha Hd Hr Hw Htokens Hol Hel Hoo Heo Hfresh. iIntros "Hh".
  iMod (stream_entry_alloc rep out err b o _ _ h op oq ep eq Ha Htokens Hol Hel Hoo Heo Hfresh
    with "Hh") as "(Hh & Ho & He & %Hnew)".
  iModIntro. iFrame "Ho He". iExists _. iFrame "Hh".
  iPureIntro. destruct Hnew as [Ha' Hw']. repeat split; try assumption.
  exact (Kentry Hw Hw').
Qed.

(** The before-stage fragment is consumed at this boundary. Allocation
    need not preserve wi at its intermediate heap: Kentry restores the
    same interpretation only after the actual stage-key update. *)
Lemma hello_callback_transfer rep out err b o stage before after
    (Hentry : forall m w h, wi m w h -> h !! PName stage = Some before ->
      stream_tokens_wi rep out err b o m w h /\
      live_at m (token_base out) (token_region out) /\
      live_at m (token_base err) (token_region err) /\
      (exists info, libc_stream_at w (token_handle out) = Some info) /\
      (exists info, libc_stream_at w (token_handle err) = Some info) /\
      (forall l v, (l, v) ∈ open_permission_ps out (token_handle out) ++
        open_permission_ps err (token_handle err) -> h !! l = None))
    (Kentry : forall m w h, wi m w h -> h !! PName stage = Some before ->
      stream_tokens_wi rep out err b o m w
        (<[PName stage := after]>
          (overwrite (open_permission_ps out (token_handle out) ++
            open_permission_ps err (token_handle err)) h)) ->
      wi m w (<[PName stage := after]>
        (overwrite (open_permission_ps out (token_handle out) ++
          open_permission_ps err (token_handle err)) h))) :
  (stage < -1)%Z -> stage <> token_key out -> stage <> token_key err ->
  before <> after -> (forall m, agree_piece m (PName stage) after) ->
  forall σ, heap_interp wi σ -∗ pts [(PName stage, before)] ==∗
    heap_interp wi σ ∗ pts [(PName stage, after)] ∗
    pts (open_permission_ps out (token_handle out)) ∗
    pts (open_permission_ps err (token_handle err)).
Proof.
  intros Hstage Hso Hse Hneq Hagree σ. iIntros "Hσ Hstage".
  iDestruct "Hσ" as (h) "(Hh & %Ha & %Hd & %Hr & %Hw)".
  iDestruct (pts_lookup with "Hh Hstage") as %Howned.
  assert (Hs : h !! PName stage = Some before).
  { apply Howned. apply elem_of_cons. left. reflexivity. }
  destruct (Hentry _ _ _ Hw Hs) as (Ht & Hol & Hel & Hoo & Heo & Hfresh).
  iMod (permission_entry_alloc rep out err b o _ _ h Ha Ht Hol Hel Hoo Heo Hfresh
    with "Hh") as "(Hh & Ho & He & %Hnew)".
  destruct Hnew as [HaA HwA].
  iEval (rewrite /pts /=) in "Hstage". iDestruct "Hstage" as "[Hstage _]".
  iMod (gen_heap_update _ (PName stage) before after with "Hh Hstage")
    as "[Hh Hstage]".
  assert (HaF : agrees (ls_mem σ) (<[PName stage := after]>
      (overwrite (open_permission_ps out (token_handle out) ++
        open_permission_ps err (token_handle err)) h))).
  { intros l v Hl. apply lookup_insert_Some in Hl as [[El Ev] | [_ Hl]].
    - subst l v. apply Hagree.
    - exact (HaA _ _ Hl). }
  pose proof (stream_tokens_name_update _ _ _ _ _ _ _ _ stage after Hso Hse HwA) as HwF.
  iModIntro. iFrame "Ho He". iSplitL "Hh".
  - iExists _. iFrame "Hh". iPureIntro. repeat split; try assumption.
    exact (Kentry _ _ _ Hw Hs HwF).
  - rewrite /pts /=. iFrame.
Qed.

(** Lift a proved state-interpretation transfer at a nonvalue frame.
    The continuation has the SAME expression and Iris instance: it
    supplies reducibility and every step obligation. No callback
    selection, extra program step or progress is inferred here. *)
Lemma wp_callback_transfer (P Q : iProp Σ) fr Φ :
  (forall σ, heap_interp wi σ -∗ P ==∗ heap_interp wi σ ∗ Q) ->
  P -∗ (Q -∗ WP (ERun fr : cexpr) {{ Φ }}) -∗ WP (ERun fr : cexpr) {{ Φ }}.
Proof.
  intros Htransfer. iIntros "HP HK".
  iEval (rewrite wp_unfold /wp_pre /=). iIntros (σ ns κ κs nt) "Hσ".
  iMod (Htransfer with "Hσ HP") as "[Hσ HQ]".
  iSpecialize ("HK" with "HQ").
  iEval (rewrite wp_unfold /wp_pre /=) in "HK".
  iApply ("HK" $! σ ns κ κs nt with "Hσ").
Qed.

(** A designated-handle fclose rule, not a dispatcher for arbitrary
    pointers. The consumer keeps its abstract wi and supplies its local
    K premise for the rest of that interpretation, as for conversion. *)
Lemma wp_hello_fclose rep requests wide out err b o dt pending fifo xs
    f e ls lab result v rest j Φ
    (Htokens : forall m w h, wi m w h -> stream_tokens_wi rep out err b o m w h)
    (Kclose : forall s m w h trace values s' m' w' ys,
      M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
        (CResult result W) [Arg P v] [WPtr (token_handle dt)] s m w trace (CallReturn values) s' m' w' ->
      (forall l u, (l, u) ∈ stream_ps dt pending fifo ++ byte_ps b o xs -> h !! l = Some u) ->
      wi m w h -> length ys = 4%nat ->
      stream_tokens_wi rep out err b o m' w' (overwrite (closed_ps dt ++ byte_ps b o ys) h) ->
      wi m' w' (overwrite (closed_ps dt ++ byte_ps b o ys) h)) :
  dt = out \/ dt = err -> length xs = 4%nat ->
  find_fn ge (TAtom "fclose") = None -> lookup (TAtom "fclose") (ge_globals ge) = None ->
  registry (TAtom "fclose") = Some (fclose_contract (libc_stream_model rep requests wide)) ->
  arg_x ge e (Arg P v) = Some (WPtr (token_handle dt)) ->
  pts (stream_ps dt pending fifo) -∗ pts (byte_ps b o xs) -∗
  ▷ (∀ n ys, ⌜0 <= n < 2 ^ 32 /\ length ys = 4%nat⌝ -∗
    pts (closed_ps dt) -∗ pts (byte_ps b o ys) -∗
    WP (ERun (mkFrame f (put result (WInt n) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Call (CResult result W) (Global (TAtom "fclose")) [Arg P v] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hdt Hxs Hfn Hg Hreg Hv. iIntros "Hs Hx HK".
  iApply (C.wp_close_contract registry wi ge f e ls lab result W (TAtom "fclose") _ _ _
    (fclose_contract (libc_stream_model rep requests wide)) [WPtr (token_handle dt)]
    (stream_ps dt pending fifo ++ byte_ps b o xs) (fun ys => closed_ps dt ++ byte_ps b o ys)
    (fun n ys => 0 <= n < 2 ^ 32 /\ length ys = 4%nat) with "[Hs Hx] [HK]").
  - exact Hfn.
  - exact Hg.
  - reflexivity.
  - exact Hreg.
  - reflexivity.
  - left. reflexivity.
  - cbn [map_option]. rewrite Hv. reflexivity.
  - split; [right; eexists; reflexivity|eexists; reflexivity].
  - intros m w h Hw Hl. eapply A.open_admitted; [exact Hdt|apply Htokens; exact Hw|].
    intros l u Hin. apply Hl, elem_of_app. left. exact Hin.
  - intros s m w h tr vs s' m' w' Ha Hd Hr Hw Hl Hi.
    destruct (hello_fclose_frame rep requests wide out err b o dt pending fifo xs _ _
      s m w tr vs s' m' w' h Hdt Hxs Ha Hd Hr (Htokens _ _ _ Hw) Hl Hi)
      as (n & ys & -> & Hn & Hys & Hkeys & Ha' & Hd' & Hr' & Htokens').
    exists n, ys. split; [reflexivity|]. split; [exact Hn|]. split; [auto|].
    split; [exact Hkeys|]. split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|].
    eapply Kclose; eauto.
  - rewrite pts_app. iFrame.
  - iNext. iIntros (n ys) "%Hgood Hps". rewrite pts_app. iDestruct "Hps" as "[Hs Hx]".
    iApply ("HK" with "[%] Hs Hx"). exact Hgood.
Qed.

(** The pointer-universal variant consumes an open-only permission and
    updates its own key. Admission rejects unknown pointers through the
    pure lookup premise, before invoking libc. *)
Lemma wp_permission_fclose rep requests wide out err b o p xs
    f e ls lab result v rest j Φ
    (Htokens : forall m w h, wi m w h -> stream_tokens_wi rep out err b o m w h)
    (Kclose : forall s m w h trace values s' m' w' ys,
      M.E.invoke (fclose_contract (libc_stream_model rep requests wide))
        (CResult result W) [Arg P v] [WPtr p] s m w trace (CallReturn values) s' m' w' ->
      (forall l u, (l, u) ∈ permission_ps out err p ++ byte_ps b o xs -> h !! l = Some u) ->
      wi m w h -> length ys = 4%nat ->
      stream_tokens_wi rep out err b o m' w'
        (overwrite (closed_ps (permission_descriptor out err p) ++ byte_ps b o ys) h) ->
      wi m' w' (overwrite (closed_ps (permission_descriptor out err p) ++ byte_ps b o ys) h)) :
  length xs = 4%nat ->
  find_fn ge (TAtom "fclose") = None -> lookup (TAtom "fclose") (ge_globals ge) = None ->
  registry (TAtom "fclose") = Some (fclose_contract (libc_stream_model rep requests wide)) ->
  arg_x ge e (Arg P v) = Some (WPtr p) ->
  pts (permission_ps out err p) -∗ pts (byte_ps b o xs) -∗
  ▷ (∀ n ys, ⌜0 <= n < 2 ^ 32 /\ length ys = 4%nat⌝ -∗
    pts (closed_ps (permission_descriptor out err p)) -∗ pts (byte_ps b o ys) -∗
    WP (ERun (mkFrame f (put result (WInt n) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Call (CResult result W) (Global (TAtom "fclose")) [Arg P v] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hxs Hfn Hg Hreg Hv. iIntros "Hs Hx HK".
  iApply (C.wp_close_contract registry wi ge f e ls lab result W (TAtom "fclose") _ _ _
    (fclose_contract (libc_stream_model rep requests wide)) [WPtr p]
    (permission_ps out err p ++ byte_ps b o xs)
    (fun ys => closed_ps (permission_descriptor out err p) ++ byte_ps b o ys)
    (fun n ys => 0 <= n < 2 ^ 32 /\ length ys = 4%nat) with "[Hs Hx] [HK]").
  - exact Hfn.
  - exact Hg.
  - reflexivity.
  - exact Hreg.
  - reflexivity.
  - left. reflexivity.
  - cbn [map_option]. rewrite Hv. reflexivity.
  - split; [right; eexists; reflexivity|eexists; reflexivity].
  - intros m w h Hw Hl. eapply A.permission_admitted; [apply Htokens; exact Hw|].
    intros l u Hin. apply Hl, elem_of_app. left. exact Hin.
  - intros s m w h tr vs s' m' w' Ha Hd Hr Hw Hl Hi.
    destruct (permission_fclose_frame rep requests wide out err b o p xs _ _
      s m w tr vs s' m' w' h Hxs Ha Hd Hr (Htokens _ _ _ Hw) Hl Hi)
      as (n & ys & -> & Hn & Hys & Hkeys & Ha' & Hd' & Hr' & Htokens').
    exists n, ys. split; [reflexivity|]. split; [exact Hn|]. split; [auto|].
    split; [exact Hkeys|]. split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|].
    eapply Kclose; eauto.
  - rewrite pts_app. iFrame.
  - iNext. iIntros (n ys) "%Hgood Hps". rewrite pts_app. iDestruct "Hps" as "[Hs Hx]".
    iApply ("HK" with "[%] Hs Hx"). exact Hgood.
Qed.

End callback_rules.

Theorem hello_output_frame : forall rep requests wide stream g r args xs s m w trace values s' m' w' h,
  output_target (hello_output_api g) libc_stdout w xs = stream ->
  agrees m h -> live_disjoint m -> R.ready s m -> hello_stdio_wi rep stream m w h ->
  M.E.invoke (hello_output_spec rep requests wide g) r args xs s m w trace
    (CallReturn values) s' m' w' ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ hello_stdio_wi rep stream m' w' h /\
    exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32.
Proof.
  intros rep requests wide stream g r args xs s m w trace values s' m' w' h
    Htarget Ha Hd Hr (Hw & Hstdout & Hfile & Hn) Hcall.
  destruct (SL.output_return_frame rep requests wide (hello_output_api g)
    r args xs stream s m w trace values s' m' w' h (eq_sym Htarget) Hcall Ha Hd Hr Hw)
    as (Ha' & Hd' & Hr' & Hw' & Hresult).
  destruct (SL.output_open_narrow rep requests wide (hello_output_api g)
    r args xs stream s m w trace (CallReturn values) s' m' w'
    (eq_sym Htarget) Hn Hcall) as (Hfile' & Hn' & Hstdout').
  split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|]. split; [|exact Hresult].
  split; [exact Hw'|]. split; [congruence|]. auto.
Qed.

(** These statements are HelloVersion's two output-frame premises,
    specialized to the concrete registry/spec and represented world. *)
Theorem hello_version_frame : forall rep requests wide stream g xs r args s m w h trace values s' m' w',
  In (g, xs) (version_output_args stream) ->
  agrees m h -> live_disjoint m -> R.ready s m -> hello_stdio_wi rep stream m w h ->
  M.E.invoke (hello_output_spec rep requests wide g) r args xs s m w trace
    (CallReturn values) s' m' w' ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ hello_stdio_wi rep stream m' w' h /\
    exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32.
Proof.
  intros. eapply hello_output_frame; eauto. eapply hello_version_target; eauto.
Qed.

Theorem hello_footer_frame : forall rep requests wide stream g xs r args s m w h trace values s' m' w',
  In (g, xs) (emit_output_args stream) ->
  agrees m h -> live_disjoint m -> R.ready s m -> hello_stdio_wi rep stream m w h ->
  M.E.invoke (hello_output_spec rep requests wide g) r args xs s m w trace
    (CallReturn values) s' m' w' ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ hello_stdio_wi rep stream m' w' h /\
    exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32.
Proof.
  intros rep requests wide stream g xs r args s m w h trace values s' m' w'
    Hin Ha Hd Hr Hw Hcall. eapply hello_output_frame; eauto.
  eapply hello_footer_target; [exact Hin|exact (proj1 (proj2 Hw))].
Qed.

(** HelloClose's complete ordinary _exit interface over its actual
    invocation relation. It requires no successful host completion to
    establish admission or absence of ordinary returns. *)
Theorem hello_close_exit_contract : forall rep requests wide host fallback p,
  hello_stdio_registry rep requests wide host fallback (TAtom "_exit") =
    Some (libc_hard_exit_contract rep host) /\
  contract_returns (libc_hard_exit_contract rep host) = RVoid /\
  (forall v, contract_abi (libc_hard_exit_contract rep host) CVoid [Arg W v]) /\
  (forall n m w h, 0 <= n < 2 ^ 32 -> libc_closing_wi rep p m w h ->
    contract_pre (libc_hard_exit_contract rep host) [WInt n] m w) /\
  (forall args n s m w trace values s' m' w',
    C.L.M.E.invoke (libc_hard_exit_contract rep host) CVoid args [WInt n]
      s m w trace (CallReturn values) s' m' w' -> False).
Proof.
  intros rep requests wide host fallback p.
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros; split; [reflexivity|eexists; reflexivity]|]. split.
  - intros n m w h Hn ((Hready & _) & Hphase).
    apply hard_exit_admitted with (bits := n).
    + apply libc_stream_ready_libc. exact Hready.
    + split; [reflexivity|exact Hn].
    + exact Hphase.
  - intros. eapply X.hard_exit_no_return; eauto.
Qed.

End HelloStdioOn.

(** Standalone users retain the original functor and theorem paths. *)
Module HelloStdio (R : Runtime).
Module LG0 := Logic R.
Include HelloStdioOn R LG0.
End HelloStdio.
