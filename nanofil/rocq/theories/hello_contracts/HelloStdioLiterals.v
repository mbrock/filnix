(** This module checks the literal bytes and formats used by Hello's output
    calls. HelloStdio includes these definitions to retain their public paths. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run
  ExternalCalls LibcCalls ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams LibcExit
  Pieces Heap ContractFrame Logic StringLogic LibcStringLogic LentLogic LibcStreamLogic LibcErrnoLogic
  LibcStreamTokens LibcStreamAdapter LibcDiagnosticLogic
  HelloModule HelloLeaf HelloVersion HelloClose.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Module HelloStdioLiterals.
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

(** A separate bundle avoids strengthening the version/footer callers.
    These are distinct objects, not duplicate ownership of equal text. *)
Definition hello_diagnostic_literals : list String.string :=
  ["closeout#str.55"; "closeout#str.53"].
Definition hello_diagnostic_pieces : list (piece * pval) := Eval vm_compute in
  flat_map hello_literal_pieces hello_diagnostic_literals.

Local Lemma hello_diagnostic_pieces_unfold :
  hello_diagnostic_pieces = flat_map hello_literal_pieces hello_diagnostic_literals.
Proof. vm_compute. reflexivity. Qed.

Lemma hello_diagnostic_shape : forall s, In s hello_diagnostic_literals ->
  string_ok (version_literal s) (ptr_addr (version_literal s))
    (hello_literal_region s) (hello_literal_bytes s).
Proof.
  intros s [<- | [<- | []]]; vm_compute;
    repeat split; try (right; reflexivity); repeat constructor; congruence.
Qed.

Lemma hello_diagnostic_owned : forall s m h,
  In s hello_diagnostic_literals ->
  (forall l v, (l, v) ∈ hello_diagnostic_pieces -> h !! l = Some v) ->
  agrees m h -> c_string m (version_literal s) (hello_literal_bytes s).
Proof.
  intros s m h Hin Howned Ha. apply string_c_string with
    (b := ptr_addr (version_literal s)) (reg := hello_literal_region s).
  - apply hello_diagnostic_shape. exact Hin.
  - apply all_agree_intro. intros l v Hlv. apply Ha, Howned.
    apply list_elem_of_In. rewrite hello_diagnostic_pieces_unfold. apply in_flat_map.
    exists s. split; [exact Hin|]. apply list_elem_of_In. exact Hlv.
Qed.

Lemma hello_diagnostic_fixture :
  version_literal "closeout#str.55" = mkPtr 65744 (Ro 65744) /\
  version_literal "closeout#str.53" = mkPtr 65680 (Ro 65680) /\
  hello_literal_bytes "closeout#str.55" = [37; 115] /\
  hello_literal_bytes "closeout#str.53" = [119; 114; 105; 116; 101; 32; 101; 114; 114; 111; 114].
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma hello_diagnostic_keys : NoDup hello_diagnostic_pieces.*1.
Proof. vm_compute. repeat (apply NoDup_cons; [simpl; intuition congruence|]). apply NoDup_nil. Qed.

Lemma hello_diagnostic_errno_keys : forall b o,
  b <> 65680 -> b <> 65744 ->
  forall l v, (l, v) ∈ hello_diagnostic_pieces -> l ∉ errno_keys b o.
Proof.
  intros b o Hb Hf l v Hin Hkey.
  unfold errno_keys in Hkey. rewrite byte_ps_keys in Hkey.
  apply list_elem_of_fmap in Hkey as (i & E & _).
  apply list_elem_of_In in Hin. vm_compute in Hin.
  repeat destruct Hin as [Hin|Hin]; try contradiction;
    injection Hin as <- <-; simpl in E; try discriminate E;
    injection E; congruence.
Qed.

(** Current owned pieces establish the strings, not equality with the
    startup memory. Native diagnostic readiness remains independent. *)
Lemma hello_diagnostic_admitted : forall rep requests wide native n m w h file,
  0 <= n < 2 ^ 32 -> agrees m h ->
  (forall l v, (l, v) ∈ hello_diagnostic_pieces -> h !! l = Some v) ->
  diagnostic_ready native m w -> libc_stream_ready rep m w ->
  Forall (writable_span m) (diagnostic_writes native w) ->
  libc_file_at w (libc_stderr w) = Some file ->
  orientation (libc_stream_state w (libc_stderr w)) <> WideOriented ->
  contract_pre (libc_error_contract rep requests wide native)
    [WInt 0; WInt n; WPtr (mkPtr 65744 (Ro 65744)); WPtr (mkPtr 65680 (Ro 65680))] m w.
Proof.
  intros rep requests wide native n m w h file Hn Ha Hl Hnative Hr Hwrites Hfile Hnarrow.
  pose proof (hello_diagnostic_owned "closeout#str.55" m h (or_introl eq_refl) Hl Ha) as Hfmt.
  pose proof (hello_diagnostic_owned "closeout#str.53" m h (or_intror (or_introl eq_refl)) Hl Ha) as Htext.
  destruct hello_diagnostic_fixture as (Hfp & Htp & Hfb & Htb).
  rewrite Hfp Hfb in Hfmt. rewrite Htp Htb in Htext.
  destruct (libc_stream_open rep requests wide m w _ file Hr Hfile) as [info Hopen].
  assert (Hprotocol : stream_protocol info = libc_stream_state w (libc_stderr w)).
  { exact (proj1 (proj2 (proj2 Hopen))). }
  assert (Hdistinct : libc_stdout w <> libc_stderr w).
  { destruct Hr as (_ & _ & _ & _ & _ & _ & _ & _ & Hd & _).
    intros E. apply Hd. rewrite E. reflexivity. }
  split.
  - split.
    + exists 0, n, (mkPtr 65744 (Ro 65744)), [WPtr (mkPtr 65680 (Ro 65680))],
        [37; 115], [119; 114; 105; 116; 101; 32; 101; 114; 114; 111; 114], info.
      split; [reflexivity|]. split; [lia|]. split; [exact Hn|]. split; [exact Hfmt|]. split.
      * rewrite <- (app_nil_r [119; 114; 105; 116; 101; 32; 101; 114; 114; 111; 114]).
        apply format_string; [exact Htext|constructor].
      * split; [exact (conj Hnative Hr)|]. split; [exact Hwrites|].
        split; [exact Hopen|]. split; [rewrite Hprotocol; exact Hnarrow|exact Hdistinct].
    + exists 0, n, (mkPtr 65744 (Ro 65744)), [WPtr (mkPtr 65680 (Ro 65680))]. auto with zarith.
  - exists n, (mkPtr 65744 (Ro 65744)), [WPtr (mkPtr 65680 (Ro 65680))]. auto with zarith.
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
End HelloStdioLiterals.
