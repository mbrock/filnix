(** Admission of Hello's actual version/footer literals. The bytes and
    object bounds come from the linked fixture, but current memory is
    read from program-owned pieces, not assumed to equal startup memory. *)
From iris.proofmode Require Import proofmode.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run
  ExternalCalls ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams LibcExit
  Pieces Heap ContractFrame Logic StringLogic LibcStreamLogic HelloModule HelloLeaf HelloVersion HelloClose.
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
Module HelloStdio (R : Runtime).
Module V := HelloVersion R.
Module M := V.L.M.
Module SL := LibcStreamLogicOn R V.LG.
Module C := HelloClose R.
Module X := LibcExitOn R C.L.M.

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

End HelloStdio.
