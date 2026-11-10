(** Admission of Hello's actual version/footer literals. The bytes and
    object bounds come from the linked fixture, but current memory is
    read from program-owned pieces, not assumed to equal startup memory. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run
  ExternalCalls ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams LibcExit
  Pieces Heap ContractFrame Logic StringLogic LentLogic LibcStreamLogic LibcErrnoLogic
  LibcStreamTokens LibcStreamAdapter
  HelloModule HelloLeaf HelloVersion HelloClose.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Definition hello_literal_memory : mem :=
  match initial_memory hello_module with
  | Some (_, m) => m | None => mkMem (fun _ => 0) [] (fun _ => CNone)
  end.

Definition hello_literal_bytes (s : String.string) : list Z :=
  map (fun i => m_bytes hello_literal_memory (ptr_addr (version_literal s) + Z.of_nat i))
    (seq 0 (Z.to_nat (string_length hello_literal_memory (version_literal s)))).

Definition hello_literal_region (s : String.string) : region :=
  match object_region (ptr_addr (version_literal s)) (m_regions hello_literal_memory) with
  | Some reg => reg | None => mkRegion 0 0 GlobalData Freed
  end.

(** Includes the author life tokens used by the variadic wrapper. *)
Definition hello_output_literals : list String.string :=
  ["version-etc#str.41"; "version_etc_copyright"; "version-etc#str.43";
   "version-etc#str.44"; "version-etc#str.45"; "version-etc#str.46";
   "version-etc#str.47"; "version-etc#str.51"; "version-etc#str.58";
   "version-etc#str.59"; "version-etc#str.60"; "version-etc#str.61";
   "version-etc#str.62"; "version-etc#str.63"; "version-etc#str.64";
   "hello#str.70"; "hello#str.63"; "hello#str.71";
   "hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75"].

(** Compute the closed fixture strings once, then rewrite by a checked
    equality instead of repeatedly reducing the linked initializer. *)
Local Definition hello_literal_cache : list (String.string * list Z) := Eval vm_compute in
  map (fun s => (s, hello_literal_bytes s)) hello_output_literals.

Local Lemma hello_literal_cache_valid :
  List.Forall (fun sb => hello_literal_bytes (fst sb) = snd sb) hello_literal_cache.
Proof.
  repeat (apply List.Forall_cons; [vm_compute; reflexivity|]). constructor.
Qed.

Local Lemma hello_literal_cached : forall s bytes,
  In (s, bytes) hello_literal_cache -> hello_literal_bytes s = bytes.
Proof.
  intros s bytes Hin. pose proof hello_literal_cache_valid as Hcache.
  rewrite List.Forall_forall in Hcache. exact (Hcache (s, bytes) Hin).
Qed.

Local Ltac hello_cached_format :=
  erewrite hello_literal_cached; [|vm_compute; eauto 30].

Definition hello_literal_pieces (s : String.string) : list (piece * pval) :=
  string_ps (version_literal s) (ptr_addr (version_literal s))
    (hello_literal_region s) (hello_literal_bytes s).

Definition hello_output_pieces : list (piece * pval) :=
  flat_map hello_literal_pieces hello_output_literals.

Lemma hello_literal_shape : forall s, In s hello_output_literals ->
  string_ok (version_literal s) (ptr_addr (version_literal s))
    (hello_literal_region s) (hello_literal_bytes s).
Proof.
  intros s Hin. repeat destruct Hin as [<-|Hin]; try contradiction;
    vm_compute; repeat split; try (right; reflexivity); repeat constructor; congruence.
Qed.

(** This is the exact lookup/agreement interface used by HelloVersion;
    no condition on the current world or output result supplies bytes. *)
Lemma hello_owned_literal : forall s m h,
  In s hello_output_literals ->
  (forall l v, (l, v) ∈ hello_output_pieces -> h !! l = Some v) ->
  agrees m h -> c_string m (version_literal s) (hello_literal_bytes s).
Proof.
  intros s m h Hin Howned Ha. apply string_c_string with
    (b := ptr_addr (version_literal s)) (reg := hello_literal_region s).
  - apply hello_literal_shape. exact Hin.
  - apply all_agree_intro. intros l v Hlv. apply Ha, Howned.
    apply list_elem_of_In. unfold hello_output_pieces. apply in_flat_map.
    exists s. split; [exact Hin|]. apply list_elem_of_In. exact Hlv.
Qed.

(** The default branch is used only for printf sites; registry facts
    below are restricted to actual footer/version call lists. *)
Definition hello_output_api (g : name) : narrow_api :=
  if name_eqb g (TAtom "fputs") then NarrowFputs else
  if name_eqb g (TAtom "fprintf") then NarrowFprintf else NarrowPrintf.

Definition hello_output_spec rep requests wide g : contract libc_world :=
  output_contract (hello_output_api g) (libc_stream_model rep requests wide) libc_stdout.

(** Hard aliases and the six stream entries compose without replacing
    the remaining libc contracts supplied by the caller. *)
Definition hello_stdio_registry rep requests wide host fallback :=
  libc_hard_exit_registry rep host (libc_stream_registry rep requests wide fallback).

(** Tactics mirror the selected format constructors, not a second
    executable parser. Every %s must prove its owned C string. *)
Local Ltac hello_format Hstring :=
  first [apply format_end |
    eapply format_string; [apply Hstring; simpl; tauto | hello_format Hstring] |
    eapply format_signed with (text := [50; 48; 50; 54]);
      [vm_compute; repeat split; repeat constructor; congruence | hello_format Hstring] |
    apply format_percent; hello_format Hstring |
    apply format_literal; [lia | discriminate | hello_format Hstring]].

Lemma hello_version_text : forall stream g xs m h,
  In (g, xs) (version_output_args stream) ->
  (forall l v, (l, v) ∈ hello_output_pieces -> h !! l = Some v) ->
  agrees m h -> exists bytes, output_text (hello_output_api g) m xs bytes.
Proof.
  intros stream g xs m h Hin Howned Ha.
  assert (Hstring := fun s Hin => hello_owned_literal s m h Hin Howned Ha).
  repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-.
  all: (
    match goal with |- exists bytes, output_text ?api ?m ?xs bytes =>
      let actual := eval vm_compute in api in
      change (exists bytes, output_text actual m xs bytes) end;
    eexists; unfold output_text;
    eexists; eexists; eexists; split; [reflexivity|];
    split; [apply Hstring; simpl; tauto|]; cbv beta iota zeta;
    try reflexivity;
    hello_cached_format; hello_format Hstring).
Qed.

Lemma hello_footer_text : forall stream g xs m h,
  In (g, xs) (emit_output_args stream) ->
  (forall l v, (l, v) ∈ hello_output_pieces -> h !! l = Some v) ->
  agrees m h -> exists bytes, output_text (hello_output_api g) m xs bytes.
Proof.
  intros stream g xs m h Hin Howned Ha.
  assert (Hstring := fun s Hin => hello_owned_literal s m h Hin Howned Ha).
  repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-.
  all: (
    match goal with |- exists bytes, output_text ?api ?m ?xs bytes =>
      let actual := eval vm_compute in api in
      change (exists bytes, output_text actual m xs bytes) end;
    eexists; unfold output_text;
    eexists; eexists; eexists; split; [reflexivity|];
    split; [apply Hstring; simpl; tauto|]; cbv beta iota zeta;
    try reflexivity;
    hello_cached_format; hello_format Hstring).
Qed.

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
Module V := HelloVersionOn R LG0.
Module M := V.L.M.
Module SL := LibcStreamLogicOn R LG0.
Module C := HelloCloseOn R LG0.
Module X := LibcExitOn R C.L.M.
Module A := LibcStreamAdapterOn R LG0.

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

(** Exercise the Iris rule, not just its pure replacement map: an actual
    fclose call instruction returns closed-token and sampled-byte resources
    through the following return instruction, on the fixture's exact LG. *)
Module HelloCallbackChecks.
Module LG := StreamHandleChecks.LG.
Module H := HelloStdioOn InterpRuntime LG.
Module F := LibcStreamChecks.
Module T := StreamTokenChecks.
Import LG LG.L.

Definition close_wi := stream_tokens_wi (fun _ _ => True) T.out T.err 5120 0.
Definition registry : name -> option (contract libc_world) := fun _ => Some (fclose_contract F.model).
Definition ge := mkGenv [] [] (fun _ _ => None).
Definition stub := mkFunc (TAtom "close-control") (TAtom "local") (RClass W) [] [].
Definition entry_env := [(TAtom "p", WPtr (token_handle T.out))].

Global Instance close_stable : SafepointStable close_wi.
Proof.
  apply H.A.tokens_safepoint. intros s m s' m' w [-> ->] Hw. exact Hw.
Qed.

Example fixture_invoke_identity : @H.M.E.invoke = @T.A.M.E.invoke.
Proof. reflexivity. Qed.

Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Local Instance test_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry close_wi ge.

(** Instantiate the entry wrapper itself, retaining separately owned
    errno. Freshness is true before allocation, not after it. *)
Example callback_entry_resources :
  gen_heap_interp HelloErrnoChecks.heap ∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) ==∗
    heap_interp close_wi (mkLstate conversion_mem InterpRuntime.start 64 (F.world true)) ∗
    pts (stream_ps T.out 7 [65; 66]) ∗ pts (stream_ps T.err 3 []) ∗
    pts (byte_ps 5120 0 [0; 0; 0; 0]).
Proof.
  iIntros "[Hh Herrno]".
  iMod (H.hello_callback_entry close_wi (fun _ _ => True) T.out T.err 5120 0
    (mkLstate conversion_mem InterpRuntime.start 64 (F.world true)) HelloErrnoChecks.heap
    7 [65; 66] 3 [] with "Hh") as "(Hσ & Ho & He)".
  - intros _ Hnew. exact Hnew.
  - exact HelloErrnoChecks.heap_agrees.
  - exact HelloErrnoChecks.disjoint.
  - exact HelloErrnoChecks.ready.
  - exact T.entry_wi.
  - exact T.entry_wi.
  - split; reflexivity.
  - split; reflexivity.
  - exists (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7). repeat split; reflexivity.
  - exists (mkStreamInfo 2 stdout_initial 3). repeat split; reflexivity.
  - exact T.entry_fresh.
  - iModIntro. iFrame.
Qed.

Example close_then_return_resources :
  pts (stream_ps T.out 7 [65; 66]) -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗
  WP (ERun (mkFrame stub entry_env [] None (Exec (TAtom "body")
    [Call (CResult (TAtom "r") W) (Global (TAtom "fclose")) [Arg P (Tmp (TAtom "p"))]]
    (JRet (Tmp (TAtom "r"))))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ n ys, ⌜result = Ret (WInt n) /\ length ys = 4%nat⌝ ∗
      pts (closed_ps T.out) ∗ pts (byte_ps 5120 0 ys) }}.
Proof.
  iIntros "Ho Herrno".
  iApply (H.wp_hello_fclose registry close_wi ge (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ _ => False) T.out T.err 5120 0 T.out 7 [65; 66]
    [0; 0; 0; 0] stub entry_env [] (TAtom "body") (TAtom "r") (Tmp (TAtom "p")) []
    (JRet (Tmp (TAtom "r"))) _ with "Ho Herrno []").
  - intros m w h Hw. exact Hw.
  - intros s m w h tr vs s' m' w' ys Hi Hl Hw Hlen Hnew. exact Hnew.
  - left. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - iNext. iIntros (n ys) "%Hgood Ho Herrno". destruct Hgood as [Hn Hys].
    iApply (wp_ret registry close_wi ge stub _ (TAtom "body") (Tmp (TAtom "r")) W (WInt n));
      [reflexivity| |].
    + change (Some (WInt (n mod 2 ^ 32)) = Some (WInt n)).
      rewrite Z.mod_small; [reflexivity|exact Hn].
    + iNext. iExists n, ys. iFrame. auto.
Qed.

End iris.
End HelloCallbackChecks.

(** The open-only rule is exercised on the very same logic as the
    callback controls, with an inhabited paired interpretation. *)
Module HelloPermissionChecks.
Module P := StreamPermissionChecks.
Module T := StreamTokenChecks.
Module F := LibcStreamChecks.
Module LG := StreamHandleChecks.LG.
Module H := HelloStdioOn InterpRuntime LG.
Import LG LG.L.

Definition close_wi := stream_tokens_wi (fun _ _ => True) P.out P.err 5120 0.
Definition registry := HelloCallbackChecks.registry.
Definition ge := HelloCallbackChecks.ge.
Definition stub := HelloCallbackChecks.stub.
Definition entry_env := HelloCallbackChecks.entry_env.

Global Instance close_stable : SafepointStable close_wi.
Proof.
  apply H.A.tokens_safepoint. intros s m s' m' w [-> ->] Hw. exact Hw.
Qed.

(** The real changed-errno call closes -4 and leaves stderr's open-only
    -5 permission, rather than manufacturing a fixed stderr snapshot. *)
Example permission_close_endpoint : forall n, n = 0 \/ n = stream_eof ->
  exists ys, length ys = 4%nat /\
    stream_tokens_wi (fun _ _ => True) P.out P.err 5120 0 T.changed_errno (F.world false)
      (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) P.heap) /\
    (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) P.heap) !! PName (-4) =
      Some (VStream (token_handle P.out) None) /\
    (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) P.heap) !! PName (-5) =
      Some (VStreamOpen (token_handle P.err)) /\
    (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) P.heap) !! PByte 5120 3 = Some (VByte 1).
Proof.
  intros n Hn.
  destruct (H.permission_fclose_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) P.out P.err 5120 0 (token_handle P.out) [0; 0; 0; 0]
    CVoid [Arg P (Const 0)] InterpRuntime.start conversion_mem (F.world true) [] [WInt n]
    InterpRuntime.start T.changed_errno (F.world false) P.heap eq_refl P.heap_agrees
    HelloErrnoChecks.disjoint HelloErrnoChecks.ready P.full_wi)
      as (result & ys & Hresult & _ & Hlen & _ & Hag & _ & _ & Hw).
  - intros l v Hin. apply elem_of_app in Hin as [Hin|Hin].
    + change ((l, v) ∈ open_permission_ps P.out (token_handle P.out)) in Hin.
      unfold open_permission_ps in Hin. apply list_elem_of_In in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-.
      * unfold P.heap, StreamHandleChecks.heap.
        repeat (rewrite lookup_insert_ne; [|discriminate]). apply lookup_insert_eq.
      * unfold P.heap. apply lookup_insert_eq.
    + destruct (MemLogic.byte_ps_elem _ _ _ _ _ Hin) as (i & x & Hi & El & Ev). subst l v.
      unfold P.heap, StreamHandleChecks.heap.
      repeat (rewrite lookup_insert_ne; [|discriminate]).
      unfold HelloErrnoChecks.heap. apply elem_of_list_to_map_1; [|exact Hin].
      change (base.NoDup [PByte 5120 0; PByte 5120 1; PByte 5120 2; PByte 5120 3]).
      repeat (apply base.NoDup_cons_2; [set_solver|]). apply base.NoDup_nil_2.
  - exact (T.changed_close n Hn).
  - exists ys. split; [exact Hlen|]. split; [exact Hw|]. split.
    + rewrite overwrite_app. cbn [closed_ps overwrite P.out token_key token_base].
      rewrite lookup_insert_ne; [|discriminate]. apply lookup_insert_eq.
    + split.
      * rewrite overwrite_app. cbn [closed_ps overwrite P.out token_key token_base].
        rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_ne; [|discriminate].
        rewrite overwrite_out.
        -- unfold P.heap. rewrite lookup_insert_ne; [|discriminate]. apply lookup_insert_eq.
        -- rewrite byte_ps_keys. intros Hin. apply list_elem_of_fmap in Hin as (i & E & _). discriminate E.
      * destruct ys as [|a [|b [|c [|d rest]]]]; try discriminate Hlen.
        assert (rest = []) as -> by (destruct rest; [reflexivity|discriminate Hlen]).
        assert (Hl : (overwrite (closed_ps P.out ++ byte_ps 5120 0 [a; b; c; d]) P.heap) !!
          PByte 5120 3 = Some (VByte d)).
        { rewrite overwrite_app. cbn [closed_ps byte_ps overwrite].
          repeat (rewrite lookup_insert_ne; [|discriminate]). apply lookup_insert_eq. }
        destruct (Hag _ _ Hl) as [_ Hvalue].
        destruct (Hvalue (mkRegion 5120 5128 Heap Live) eq_refl eq_refl) as (_ & _ & Hv).
        change (1 = d) in Hv. rewrite Hv. exact Hl.
Qed.

Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Local Instance test_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry close_wi ge.

Example permission_close_then_return :
  pts (permission_ps P.out P.err (token_handle P.out)) -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗
  WP (ERun (mkFrame stub entry_env [] None (Exec (TAtom "body")
    [Call (CResult (TAtom "r") W) (Global (TAtom "fclose")) [Arg P (Tmp (TAtom "p"))]]
    (JRet (Tmp (TAtom "r"))))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ n ys, ⌜result = Ret (WInt n) /\ length ys = 4%nat⌝ ∗
      pts (closed_ps P.out) ∗ pts (byte_ps 5120 0 ys) }}.
Proof.
  iIntros "Ho Herrno".
  iApply (H.wp_permission_fclose registry close_wi ge (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ _ => False) P.out P.err 5120 0 (token_handle P.out)
    [0; 0; 0; 0] stub entry_env [] (TAtom "body") (TAtom "r") (Tmp (TAtom "p")) []
    (JRet (Tmp (TAtom "r"))) _ with "Ho Herrno []").
  - intros m w h Hw. exact Hw.
  - intros s m w h tr vs s' m' w' ys Hi Hl Hw Hlen Hnew. exact Hnew.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - iNext. iIntros (n ys) "%Hgood Ho Herrno". destruct Hgood as [Hn Hys].
    iApply (wp_ret registry close_wi ge stub _ (TAtom "body") (Tmp (TAtom "r")) W (WInt n));
      [reflexivity| |].
    + change (Some (WInt (n mod 2 ^ 32)) = Some (WInt n)).
      rewrite Z.mod_small; [reflexivity|exact Hn].
    + iNext. iExists n, ys. iFrame. auto.
Qed.

End iris.
End HelloPermissionChecks.

(** A single fixed interpretation admits allocation only before its
    owned stage is consumed. No assumption supplies either compatibility
    premise of the wrapper. Native safepoints are identity in this fixture. *)
Module HelloTransferChecks.
Module LG := StreamHandleChecks.LG.
Module H := HelloStdioOn InterpRuntime LG.
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
Module X := HelloTransferChecks.
Module LG := X.LG.
Module H := X.H.
Module P := StreamPermissionChecks.
Import LG LG.L.

Lemma close_restored : forall m w h m' w' ys,
  (forall l v, (l, v) ∈ permission_ps P.out P.err (token_handle P.out) ++
    byte_ps 5120 0 [0; 0; 0; 0] -> h !! l = Some v) ->
  X.callback_wi m w h ->
  X.pair_wi m' w' (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) h) ->
  X.callback_wi m' w' (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) h).
Proof.
  intros m w h m' w' ys Hl [_ [[Hs (_ & _ & _ & _ & Hfresh)]|Hs]] Hw.
  - exfalso.
    assert (Hin : (PLive (token_base P.out), VLive (token_region P.out)) ∈ X.pair_ps).
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
Local Instance test_stable : SafepointStable X.callback_wi := X.callback_stable.
Local Instance test_irisGS : irisGS_gen hlc
    (nanofil_lang HelloPermissionChecks.registry HelloPermissionChecks.ge) Σ :=
  nanofil_irisGS HelloPermissionChecks.registry X.callback_wi HelloPermissionChecks.ge.

Example transfer_close_return :
  pts [(PName X.stage, X.before)] -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗ pts X.unrelated -∗
  WP (ERun (mkFrame HelloPermissionChecks.stub HelloPermissionChecks.entry_env [] None
    (Exec (TAtom "body")
      [Call (CResult (TAtom "r") W) (Global (TAtom "fclose")) [Arg P (Tmp (TAtom "p"))]]
      (JRet (Tmp (TAtom "r"))))) : language.expr
    (nanofil_lang HelloPermissionChecks.registry HelloPermissionChecks.ge))
  {{ result, ∃ n ys, ⌜result = Ret (WInt n) /\ length ys = 4%nat⌝ ∗
    pts [(PName X.stage, X.after)] ∗ pts (closed_ps P.out) ∗
    pts (open_permission_ps P.err (token_handle P.err)) ∗
    pts (byte_ps 5120 0 ys) ∗ pts X.unrelated }}.
Proof.
  iIntros "Hstage Herrno Hother".
  iApply (H.wp_callback_transfer HelloPermissionChecks.registry X.callback_wi HelloPermissionChecks.ge
    (pts [(PName X.stage, X.before)])
    (pts [(PName X.stage, X.after)] ∗ pts (open_permission_ps P.out (token_handle P.out)) ∗
      pts (open_permission_ps P.err (token_handle P.err)))%I _ _ with "Hstage [Herrno Hother]").
  - intros σ. iApply (H.hello_callback_transfer X.callback_wi (fun _ _ => True) P.out P.err 5120 0
      X.stage X.before X.after X.entry_admitted X.entry_restored).
    + unfold X.stage. lia.
    + discriminate.
    + discriminate.
    + discriminate.
    + intros m. exact I.
  - iIntros "(Hstage & Ho & He)".
    iApply (H.wp_permission_fclose HelloPermissionChecks.registry X.callback_wi HelloPermissionChecks.ge
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
      iApply (wp_ret HelloPermissionChecks.registry X.callback_wi HelloPermissionChecks.ge
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
Module X := HelloTransferChecks.
Module LG := X.LG.
Module H := X.H.
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
  X.callback_wi m w h ->
  (forall l v, (l, v) ∈ permission_ps P.out P.err p -> h !! l = Some v) ->
  X.pair_wi m' w' h -> X.callback_wi m' w' h.
Proof.
  intros p m w h m' w' [_ [[Hs (_ & _ & _ & _ & Hfresh)]|Hs]] Hl Hw.
  - exfalso.
    assert (Hlife : (PLive (token_base (permission_descriptor P.out P.err p)),
        VLive (token_region (permission_descriptor P.out P.err p))) ∈ permission_ps P.out P.err p).
    { apply elem_of_cons. left. reflexivity. }
    assert (Hpair : (PLive (token_base (permission_descriptor P.out P.err p)),
        VLive (token_region (permission_descriptor P.out P.err p))) ∈ X.pair_ps).
    { destruct (permission_selected P.out P.err p) as [-> | ->]; apply elem_of_app;
        [left|right]; apply elem_of_cons; left; reflexivity. }
    specialize (Hfresh _ _ Hpair). specialize (Hl _ _ Hlife). congruence.
  - split; [exact Hw|]. right. exact Hs.
Qed.

Definition query_heap : gmap piece pval :=
  <[PName X.stage := X.after]> (overwrite X.pair_ps X.entry_heap).
Definition query_handle (stdout : bool) := if stdout then token_handle P.out else token_handle P.err.
Definition query_name (error : bool) := if error then TAtom "ferror" else TAtom "__fpending".
Definition query_class (error : bool) := if error then W else L.
Definition query_result (error stdout : bool) : Z := if error then (if stdout then 17 else 0)
  else (if stdout then 7 else 3).

Lemma query_lookups : forall stdout l v,
  (l, v) ∈ permission_ps P.out P.err (query_handle stdout) -> query_heap !! l = Some v.
Proof.
  intros stdout l v Hin. destruct stdout.
  - change ((l, v) ∈ open_permission_ps P.out (token_handle P.out)) in Hin.
    apply list_elem_of_In in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
    all: unfold query_heap, X.pair_ps, X.entry_heap;
      cbn [open_permission_ps overwrite app fst snd P.out P.err token_base token_key];
      repeat (rewrite lookup_insert_ne; [|discriminate]); apply lookup_insert_eq.
  - change ((l, v) ∈ open_permission_ps P.err (token_handle P.err)) in Hin.
    apply list_elem_of_In in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
    all: unfold query_heap, X.pair_ps, X.entry_heap;
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
    agrees conversion_mem query_heap /\ X.callback_wi conversion_mem (F.world true) query_heap.
Proof.
  intros error stdout.
  destruct X.transfer_endpoint as (Ha & Hw & Hrest).
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
Local Instance test_stable : SafepointStable X.callback_wi := X.callback_stable.
Local Instance test_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry X.callback_wi ge.

(** Use the existing contract bridge, with actual outside/unbound facts
    for this empty ge, not an assumed full Hello linkage. *)
Example query_return g k p other :
  (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
  pts (permission_ps P.out P.err p) -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗
  pts [(PName X.stage, X.after)] -∗ pts other -∗
  WP (ERun (mkFrame (stub k) (entry_env p) [] None
    (Exec (TAtom "body") [Call (CResult (TAtom "r") k) (Global g) [Arg P (Tmp (TAtom "p"))]]
      (JRet (Tmp (TAtom "r"))))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ n, ⌜result = Ret (WInt n) /\ 0 <= n < 2 ^ (if class_eqb k W then 32 else 64)⌝ ∗
    pts (permission_ps P.out P.err p) ∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) ∗
    pts [(PName X.stage, X.after)] ∗ pts other }}.
Proof.
  intros Hwhich. iIntros "Ho Herrno Hstage Hother".
  iApply (H.C.wp_close_contract registry X.callback_wi ge (stub k) (entry_env p) [] (TAtom "body")
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
    iApply (wp_ret registry X.callback_wi ge (stub k) _ (TAtom "body") (Tmp (TAtom "r")) k (WInt n));
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
  pts [(PName X.stage, X.before)] -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗ pts X.unrelated -∗
  WP (ERun (mkFrame (stub (query_class error)) (entry_env (query_handle stdout)) [] None
    (Exec (TAtom "body")
      [Call (CResult (TAtom "r") (query_class error)) (Global (query_name error)) [Arg P (Tmp (TAtom "p"))]]
      (JRet (Tmp (TAtom "r"))))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ n, ⌜result = Ret (WInt n) /\ 0 <= n < 2 ^ (if class_eqb (query_class error) W then 32 else 64)⌝ ∗
    pts (permission_ps P.out P.err (query_handle stdout)) ∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) ∗
    pts [(PName X.stage, X.after)] ∗ pts (open_permission_ps opposite (token_handle opposite) ++ X.unrelated) }}.
Proof.
  intro opposite. iIntros "Hstage Herrno Hother".
  iApply (H.wp_callback_transfer registry X.callback_wi ge (pts [(PName X.stage, X.before)])
    (pts [(PName X.stage, X.after)] ∗ pts (open_permission_ps P.out (token_handle P.out)) ∗
      pts (open_permission_ps P.err (token_handle P.err)))%I _ _ with "Hstage [Herrno Hother]").
  - intros σ. iApply (H.hello_callback_transfer X.callback_wi (fun _ _ => True) P.out P.err 5120 0
      X.stage X.before X.after X.entry_admitted X.entry_restored).
    + unfold X.stage. lia.
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
