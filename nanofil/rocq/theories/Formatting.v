(** Hello's reached plain formatting calls, not the older fortified-symbol
    census. HelloCode's usage and version_etc use strings, %% and promoted
    integers; its wide path uses L"%ls\n". Admission is independent of
    output success. No %n is selected, so no %n write authority is granted.
    Translated formats outside this grammar need a further contract or a
    proved translation restriction, not an invented successful parse. *)
From Stdlib Require Import ZArith List Bool Lia.
From Nanofil Require Import Syntax Values Memory Runtime ExternalCalls ExternalMachine Stdio Streams.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Decimal digits with no redundant leading zero, interpreted in base
    ten. This specifies decimal output independently of a printer. *)
Definition decimal_digits (digits : list Z) (n : Z) : Prop :=
  digits <> [] /\ Forall (fun d => 48 <= d <= 57) digits /\
  (hd 48 digits = 48 -> digits = [48]) /\
  fold_left (fun acc d => 10 * acc + d - 48) digits 0 = n.

(** The default-promoted int/unsigned int argument is a canonical W.
    Negative int words print a minus sign and the absolute signed value. *)
Definition formatted_int (signed : bool) (n : Z) (bytes : list Z) : Prop :=
  0 <= n < 2 ^ 32 /\
  let value := if signed && (2 ^ 31 <=? n) then n - 2 ^ 32 else n in
  if value <? 0 then exists digits, bytes = 45 :: digits /\ decimal_digits digits (- value)
  else decimal_digits bytes value.

(** Selected format interpretation, with exact consumed varargs. Each
    %s needs its whole in-object NUL-terminated string even on failure.
    Literals and %% consume no argument. Floats, lengths, positional
    conversions, precision, and %n are deliberately not admitted here. *)
Inductive narrow_format (m : mem) : list Z -> list word -> list Z -> Prop :=
| format_end : narrow_format m [] [] []
| format_literal : forall c fmt args bytes,
    0 < c < 256 -> c <> 37 -> narrow_format m fmt args bytes ->
    narrow_format m (c :: fmt) args (c :: bytes)
| format_percent : forall fmt args bytes,
    narrow_format m fmt args bytes ->
    narrow_format m (37 :: 37 :: fmt) args (37 :: bytes)
| format_string : forall fmt args bytes p text,
    c_string m p text -> narrow_format m fmt args bytes ->
    narrow_format m (37 :: 115 :: fmt) (WPtr p :: args) (text ++ bytes)
| format_signed : forall fmt args bytes n text,
    formatted_int true n text -> narrow_format m fmt args bytes ->
    narrow_format m (37 :: 100 :: fmt) (WInt n :: args) (text ++ bytes)
| format_unsigned : forall fmt args bytes n text,
    formatted_int false n text -> narrow_format m fmt args bytes ->
    narrow_format m (37 :: 117 :: fmt) (WInt n :: args) (text ++ bytes).

(** Read spans for the format and pointer varargs, through their NULs.
    Integer words grant no capability source; no source becomes a write
    root or an owned release. Exact lengths follow from admission. *)
Definition format_sources (m : mem) (format : ptr) (args : list word) : list span :=
  mkSpan format (string_length m format + 1) ::
  flat_map (fun arg => match arg with
    | WPtr p => [mkSpan p (string_length m p + 1)] | _ => [] end) args.

(** The selected variadic ABI permits only P and promoted W, not L or
    unpromoted byte/half classes. The format interpretation independently
    requires matching pointer or integer words at every conversion. *)
Definition promoted_argument (a : arg) : Prop :=
  exists v, a = Arg P v \/ a = Arg W v.

(** The three reached narrow entry points share interpretation and FIFO
    effects, but retain their distinct fixed argument positions. *)
Inductive narrow_api : Type := NarrowPrintf | NarrowFprintf | NarrowFputs.

(** The stream handle selected by each entry point. *)
Definition output_target {world} (api : narrow_api) (stdout : world -> ptr)
    (w : world) (xs : list word) : ptr :=
  match api, xs with
  | NarrowPrintf, _ => stdout w
  | NarrowFprintf, WPtr p :: _ => p
  | NarrowFputs, [WPtr _; WPtr p] => p
  | _, _ => mkPtr 0 CNone
  end.

(** The readable input pointer and remaining varargs, excluding FILE. *)
Definition output_inputs (api : narrow_api) (xs : list word) : option (ptr * list word) :=
  match api, xs with
  | NarrowPrintf, WPtr fmt :: args => Some (fmt, args)
  | NarrowFprintf, WPtr _ :: WPtr fmt :: args => Some (fmt, args)
  | NarrowFputs, [WPtr text; WPtr _] => Some (text, [])
  | _, _ => None
  end.

(** Plain fputs accepts the string unchanged; formatting calls interpret
    a readable format and its exact varargs before selecting a result. *)
Definition output_text (api : narrow_api) (m : mem) (xs : list word) (bytes : list Z) : Prop :=
  exists p args text, output_inputs api xs = Some (p, args) /\ c_string m p text /\
    match api with
    | NarrowFputs => bytes = text
    | _ => narrow_format m text args bytes
    end.

(** The complete fixed and promoted argument ABI. *)
Definition output_abi (api : narrow_api) (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\
  match api with
  | NarrowPrintf => exists fmt rest, args = Arg P fmt :: rest /\ Forall promoted_argument rest
  | NarrowFprintf => exists file fmt rest,
      args = Arg P file :: Arg P fmt :: rest /\ Forall promoted_argument rest
  | NarrowFputs => exists text file, args = [Arg P text; Arg P file]
  end.

(** Complete admission: represented open non-wide stream and readable,
    well-typed format inputs. A negative result does not weaken this. *)
Definition output_pre {world} (api : narrow_api) (model : stream_model world)
    (stdout : world -> ptr) (xs : list word) (m : mem) (w : world) : Prop :=
  exists info bytes, stream_open model m w (output_target api stdout w xs) info /\
    orientation (stream_protocol info) <> WideOriented /\ output_text api m xs bytes.

(** Formatted results count all output bytes on success; fputs promises
    only a nonnegative int. Every negative result may follow partial OR
    full acceptance, including an encoding or count-overflow failure. *)
Definition output_result (api : narrow_api) (bytes accepted : list Z) (result : Z) : Prop :=
  (accepted = bytes /\ 0 <= result < 2 ^ 31 /\
    (api = NarrowFputs \/ result = Z.of_nat (length bytes))) \/ negative_int result.

(** A finite output prefix reuses Stdio's ordered obligations. Stream
    identifiers distinguish stdout from stderr. Delivery is not another
    acceptance event. Physical pending may differ from outstanding. *)
Definition output_prefix {world} (api : narrow_api) (model : stream_model world)
    (stdout : world -> ptr) (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (m' : mem) (w' : world) : Prop :=
  exists info info' bytes actions tail,
    stream_at model w (output_target api stdout w xs) = Some info /\
    output_text api m xs bytes /\ bytes = accepted actions ++ tail /\
    stream_run (stream_protocol info) actions (stream_protocol info') /\
    stream_open model m' w' (output_target api stdout w xs) info' /\
    stream_identifier info' = stream_identifier info /\
    stream_frame model (output_target api stdout w xs) w w' /\
    stream_delegates model w (output_target api stdout w xs) born m' w' /\
    ((trace = [] /\ accepted actions = []) \/
      trace = [StreamBytes (stream_identifier info) (accepted actions)]).

(** A completed output call includes the cumulative acceptance event,
    even on failure, but does not promise descriptor delivery. *)
Definition output_post {world} (api : narrow_api) (model : stream_model world)
    (stdout : world -> ptr) (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : world) : Prop :=
  exists info info' bytes actions tail result,
    stream_at model w (output_target api stdout w xs) = Some info /\
    output_text api m xs bytes /\ bytes = accepted actions ++ tail /\
    stream_run (stream_protocol info) actions (stream_protocol info') /\
    stream_open model m' w' (output_target api stdout w xs) info' /\
    stream_identifier info' = stream_identifier info /\
    stream_frame model (output_target api stdout w xs) w w' /\
    stream_delegates model w (output_target api stdout w xs) born m' w' /\
    output_result api bytes (accepted actions) result /\
    trace = [StreamBytes (stream_identifier info) (accepted actions)] /\
    ending = CallReturn [WInt result].

(** The common contract retains readable inputs only as sources; its
    writable roots are solely the stream's, and it releases no caller
    object. Native temporary allocations remain explicit requests. *)
Definition output_contract {world} (api : narrow_api) (model : stream_model world)
    (stdout : world -> ptr) : contract world :=
  mkContract world (RClass W) (output_abi api) (output_pre api model stdout)
    (fun xs m w => stream_sources model w (output_target api stdout w xs) ++
      match output_inputs api xs with Some (p, args) => format_sources m p args | None => [] end)
    (fun xs _ w => stream_writes model w (output_target api stdout w xs))
    (fun _ _ _ => [])
    (fun xs _ w => stream_requests model w (output_target api stdout w xs))
    (output_prefix api model stdout) (output_post api model stdout) resource_reason puts_panic.

(** Plain printf uses the supplied stdout-handle projection. *)
Definition printf_contract {world} (model : stream_model world) (stdout : world -> ptr) : contract world :=
  output_contract NarrowPrintf model stdout.

(** Plain fprintf takes its FILE as the first P argument. *)
Definition fprintf_contract {world} (model : stream_model world) : contract world :=
  output_contract NarrowFprintf model (fun _ => mkPtr 0 CNone).

(** Plain fputs takes its FILE as the second P argument. *)
Definition fputs_contract {world} (model : stream_model world) : contract world :=
  output_contract NarrowFputs model (fun _ => mkPtr 0 CNone).

(** A readable wchar_t string, including its aligned four-byte NUL.
    Invalid encoding values are not excluded: output may fail on them. *)
Definition wchar_string (m : mem) (p : ptr) (chars : list Z) : Prop :=
  access_res m (ptr_addr p) (ptr_cap p) (4 * (Z.of_nat (length chars) + 1)) Read 4 = Some ok /\
  Forall (fun c => 0 < c < 2 ^ 32) chars /\
  (forall i c, nth_error chars i = Some c -> load_bytes m (ptr_addr p + 4 * Z.of_nat i) 4 = c) /\
  load_bytes m (ptr_addr p + 4 * Z.of_nat (length chars)) 4 = 0.

(** A bounded scan in wchar_t units, solely to compute the readable
    source footprint. As for [string_length], admission grants reads. *)
Definition wchar_length (m : mem) (p : ptr) : Z :=
  nul_count (fun i => load_bytes m (ptr_addr p + 4 * i) 4) 0
    (Z.to_nat (string_capacity m p / 4)).

(** Selected wide realization: conversion, native buffering and its
    observations must be supplied independently. It is not byte Accept
    on a wide stream and does not create another stdout queue. *)
Record wide_output_context (world : Type) : Type := mkWideOutputContext {
  wide_realization : world -> ptr -> list Z -> list Z -> stream_info -> option Z -> Prop
}.
Arguments wide_realization {world}.

(** Admission to Hello's sole wide format L"%ls\n", with one readable
    wchar_t-string P argument and a non-byte-oriented stdout. *)
Definition wprintf_pre {world} (model : stream_model world) (stdout : world -> ptr)
    (xs : list word) (m : mem) (w : world) : Prop :=
  exists fmt text chars info, xs = [WPtr fmt; WPtr text] /\
    wchar_string m fmt [37; 108; 115; 10] /\ wchar_string m text chars /\
    stream_open model m w (stdout w) info /\ orientation (stream_protocol info) <> ByteOriented.

(** Wide prefixes preserve the authoritative orientation/error state;
    the realization relation accounts for encoded bytes accepted and
    ties successful results to complete conversion. None is a finite
    prefix, Some result an ordinary completion. *)
Definition wprintf_effect {world} (model : stream_model world) (stdout : world -> ptr)
    (wide : wide_output_context world) (result : option Z)
    (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (m' : mem) (w' : world) : Prop :=
  exists fmt text chars info info' bytes,
    xs = [WPtr fmt; WPtr text] /\ wchar_string m text chars /\
    stream_at model w (stdout w) = Some info /\ stream_open model m' w' (stdout w) info' /\
    wide_realization wide w (stdout w) (chars ++ [10]) bytes info' result /\
    orientation (stream_protocol info') <> ByteOriented /\
    (result <> None -> orientation (stream_protocol info') = WideOriented) /\
    (orientation (stream_protocol info) = WideOriented ->
      orientation (stream_protocol info') = WideOriented) /\
    (stream_error (stream_protocol info) = true -> stream_error (stream_protocol info') = true) /\
    stream_identifier info' = stream_identifier info /\
    stream_frame model (stdout w) w w' /\ stream_delegates model w (stdout w) born m' w' /\
    ((trace = [] /\ bytes = [] /\ result = None) \/
      trace = [StreamBytes (stream_identifier info) bytes]).

(** The selected wprintf contract has a separate native realization
    premise. Success counts wchar_t output, not encoded bytes. Resources
    never inherit its normal-return postcondition. *)
Definition wprintf_contract {world} (model : stream_model world) (stdout : world -> ptr)
    (wide : wide_output_context world) : contract world :=
  mkContract world (RClass W)
    (fun r args => (r = CVoid \/ exists d, r = CResult d W) /\
      exists fmt text, args = [Arg P fmt; Arg P text])
    (wprintf_pre model stdout)
    (fun xs m w => stream_sources model w (stdout w) ++
      match xs with [WPtr fmt; WPtr text] =>
        [mkSpan fmt 20; mkSpan text (4 * (wchar_length m text + 1))]
      | _ => [] end)
    (fun _ _ w => stream_writes model w (stdout w)) (fun _ _ _ => [])
    (fun _ _ w => stream_requests model w (stdout w))
    (wprintf_effect model stdout wide None)
    (fun xs m w born trace ending m' w' =>
      exists result, wprintf_effect model stdout wide (Some result) xs m w born trace m' w' /\
        ending = CallReturn [WInt result] /\
        ((0 <= result < 2 ^ 31 /\ exists fmt text chars,
            xs = [WPtr fmt; WPtr text] /\ wchar_string m text chars /\
            result = Z.of_nat (length chars) + 1) \/ negative_int result))
    resource_reason puts_panic.

(** Selected error() decoration and internal state authority. Readiness
    excludes a user error_print_progname callback, supplies initialized
    counter/TLS/program-name state and all selected strerror dependencies.
    Segments include the program prefix, formatted body, optional errno
    text and newline. Each native formatting stage can fail independently.
    The frame must preserve phase, status, pending/consumed callback
    inventories, and permit only the explicitly described stream changes. *)
Record diagnostic_context (world : Type) : Type := mkDiagnosticContext {
  diagnostic_ready : mem -> world -> Prop;
  diagnostic_sources : mem -> world -> list span;
  diagnostic_writes : world -> list span;
  diagnostic_requests : world -> Z -> Z -> Prop;
  diagnostic_segments : mem -> world -> Z -> list Z -> list (list Z) -> Prop;
  diagnostic_frame : world -> world -> Prop
}.
Arguments diagnostic_ready {world}.
Arguments diagnostic_sources {world}.
Arguments diagnostic_writes {world}.
Arguments diagnostic_requests {world}.
Arguments diagnostic_segments {world}.
Arguments diagnostic_frame {world}.

(** Flushing stdout does not accept diagnostic bytes. An already closed
    static stdout stays closed; its selected safe fflush behavior is part
    of native representation coverage, not valid arbitrary FILE use. *)
Definition diagnostic_flush {world} (model : stream_model world) (stdout : world -> ptr)
    (w w' : world) : Prop :=
  match stream_at model w (stdout w) with
  | None => stream_at model w' (stdout w) = None /\
      stream_state_at model w' (stdout w) = stream_state_at model w (stdout w)
  | Some info => exists info', stream_at model w' (stdout w) = Some info' /\
      stream_protocol info = stream_state_at model w (stdout w) /\
      stream_protocol info' = stream_state_at model w' (stdout w) /\
      stream_identifier info' = stream_identifier info /\
      stream_settlement model w (stdout w) (stream_protocol info) (stream_protocol info') false
  end.

(** Admission to the formatting part of error, before any exit request.
    The selected stderr path is narrow; wide stderr needs separate fxprintf
    conversion coverage. Status/errno are promoted canonical W words. *)
Definition error_format_pre {world} (model : stream_model world)
    (stdout stderr : world -> ptr) (diagnostic : diagnostic_context world)
    (xs : list word) (m : mem) (w : world) : Prop :=
  exists status errnum fmt args text body info,
    xs = WInt status :: WInt errnum :: WPtr fmt :: args /\
    0 <= status < 2 ^ 32 /\ 0 <= errnum < 2 ^ 32 /\
    c_string m fmt text /\ narrow_format m text args body /\
    diagnostic_ready diagnostic m w /\
    Forall (writable_span m) (diagnostic_writes diagnostic w) /\
    stream_open model m w (stderr w) info /\
    orientation (stream_protocol info) <> WideOriented /\ stdout w <> stderr w.

(** A diagnostic can accept a prefix of EACH stage, not necessarily a
    prefix of the concatenation: a failed body may be followed by errno
    text or a newline. Nothing is labeled as stdout acceptance. *)
Definition error_format_prefix {world} (model : stream_model world)
    (stdout stderr : world -> ptr) (diagnostic : diagnostic_context world)
    (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (m' : mem) (w' : world) : Prop :=
  exists status errnum fmt args text body info info' segments pieces actions,
    xs = WInt status :: WInt errnum :: WPtr fmt :: args /\
    c_string m fmt text /\ narrow_format m text args body /\
    diagnostic_segments diagnostic m w errnum body segments /\
    Forall2 (fun whole part => exists tail, whole = part ++ tail) segments pieces /\
    stream_at model w (stderr w) = Some info /\
    stream_open model m' w' (stderr w) info' /\
    stream_identifier info = 2 /\ stream_identifier info' = 2 /\
    stream_run (stream_protocol info) actions (stream_protocol info') /\
    accepted actions = concat pieces /\ diagnostic_flush model stdout w w' /\
    diagnostic_ready diagnostic m' w' /\ diagnostic_frame diagnostic w w' /\
    stream_delegates model w (stdout w) born m' w' /\
    stream_delegates model w (stderr w) born m' w' /\
    (forall root, In root (diagnostic_writes diagnostic w') ->
      available_cap (diagnostic_sources diagnostic m w) born m' (ptr_cap (span_ptr root)) /\
      forall a, span_contains root a -> write_authority (diagnostic_writes diagnostic w) born m' a) /\
    ((trace = [] /\ accepted actions = []) \/ trace = [StreamBytes 2 (accepted actions)]).

(** error's formatting stage has the actual W,W,P variadic ABI and void
    return. It NEVER emits ProcessExit: the separate ending protocol owns
    the exit request after this stage's current-world completion. *)
Definition error_format_contract {world} (model : stream_model world)
    (stdout stderr : world -> ptr) (diagnostic : diagnostic_context world) : contract world :=
  mkContract world RVoid
    (fun r args => r = CVoid /\ exists status errnum fmt rest,
      args = Arg W status :: Arg W errnum :: Arg P fmt :: rest /\ Forall promoted_argument rest)
    (error_format_pre model stdout stderr diagnostic)
    (fun xs m w => stream_sources model w (stdout w) ++ stream_sources model w (stderr w) ++
      diagnostic_sources diagnostic m w ++
      match xs with WInt _ :: WInt _ :: WPtr fmt :: args => format_sources m fmt args | _ => [] end)
    (fun _ _ w => stream_writes model w (stdout w) ++ stream_writes model w (stderr w) ++
      diagnostic_writes diagnostic w)
    (fun _ _ _ => [])
    (fun _ _ w align size => stream_requests model w (stdout w) align size \/
      stream_requests model w (stderr w) align size \/ diagnostic_requests diagnostic w align size)
    (error_format_prefix model stdout stderr diagnostic)
    (fun xs m w born trace ending m' w' =>
      error_format_prefix model stdout stderr diagnostic xs m w born trace m' w' /\
      ending = CallReturn []) resource_reason puts_panic.

(** Inversion over the supplied machine keeps ordinary returns and
    resource stops apart without a sibling invocation relation. *)
Module FormattingOn (R : Runtime) (M : ExternalMachineSig R).
Module E := M.E.

(** Construct an ordinary output completion from the independently
    witnessed prefix/effects and complete result relation. *)
Theorem output_return : forall world api (model : stream_model world) stdout
    r args xs s m w born trace result s' m' w',
  output_abi api r args -> output_pre api model stdout xs m w ->
  E.prefix (output_contract api model stdout) xs s m w born trace s' m' w' ->
  output_post api model stdout xs m w born trace (CallReturn [WInt result]) m' w' ->
  E.invoke (output_contract api model stdout) r args xs s m w trace
    (CallReturn [WInt result]) s' m' w'.
Proof.
  intros world api model stdout r args xs s m w born trace result s' m' w' Habi Hpre Hprefix Hpost.
  eapply E.invoke_normal with (born := born); try exact Habi; try exact Hpre;
    try exact Hprefix; try exact Hpost; try discriminate.
  intros values Heq. injection Heq as <-. split; [|constructor; [exact I|constructor]].
  exists (WInt result). split; [reflexivity|]. simpl.
  destruct Hpost as (info & info' & bytes & actions & tail & n & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _ & Hend).
  injection Hend as <-. rewrite Z.mod_small; [reflexivity|].
  destruct Hr as [(_ & Hn & _) | Hn]; unfold negative_int in *; lia.
Qed.

(** All three narrow contracts share this ordinary/resource disjunction. *)
Theorem output_invocation : forall world api (model : stream_model world) stdout
    r args xs s m w trace ending s' m' w',
  E.invoke (output_contract api model stdout) r args xs s m w trace ending s' m' w' ->
  (exists born, output_post api model stdout xs m w born trace ending m' w') \/
  (exists why, ending = CallResource why /\ resource_reason why).
Proof.
  intros world api model stdout r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - left. match goal with Hpost : contract_post _ _ _ _ ?born _ _ _ _ |- _ =>
      exists born; exact Hpost end.
  - right. eauto.
Qed.

(** Hello's output frames need a canonical W, not successful output or
    an exact fputs byte count. Negative results remain canonical too. *)
Theorem output_returned : forall world api (model : stream_model world) stdout
    r args xs s m w trace values s' m' w',
  E.invoke (output_contract api model stdout) r args xs s m w trace
    (CallReturn values) s' m' w' ->
  exists result, values = [WInt result] /\ 0 <= result < 2 ^ 32.
Proof.
  intros world api model stdout r args xs s m w trace values s' m' w' Hcall.
  destruct (output_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as [(born & info & info' & bytes & actions & tail & result &
      _ & _ & _ & _ & _ & _ & _ & _ & Hr & _ & Hend) | (why & Hbad & _)];
    [|discriminate Hbad].
  injection Hend as ->. exists result. split; [reflexivity|].
  destruct Hr as [(_ & Hrange & _) | Hrange]; unfold negative_int in *; lia.
Qed.

End FormattingOn.

(** Standalone compatibility wrapper; logic clients use [FormattingOn]
    with their actual exported machine instance. *)
Module Formatting (R : Runtime).
Module M := ExternalMachine R.
Include FormattingOn R M.
End Formatting.

(** %n is not silently admitted as a read-only conversion. *)
Example no_selected_percent_n : forall m args bytes,
  ~ narrow_format m [37; 110] args bytes.
Proof. intros m args bytes H. inversion H; subst; try lia. Qed.

(** Decimal signedness distinguishes canonical negative one from the
    corresponding unsigned integer. *)
Example signed_negative_one : formatted_int true (2 ^ 32 - 1) [45; 49].
Proof.
  split; [lia|]. change (exists digits, [45; 49] = 45 :: digits /\ decimal_digits digits 1).
  exists [49]. split; [reflexivity|]. unfold decimal_digits.
  split; [discriminate|]. split; [repeat constructor; lia|].
  split; [simpl; discriminate|reflexivity].
Qed.

(** Even full acceptance may be followed by a negative format result. *)
Example output_full_negative : output_result NarrowPrintf [65; 66] [65; 66] stream_eof.
Proof. right. unfold negative_int, stream_eof. lia. Qed.

(** A nonnegative formatted result counts bytes; fputs alone may return
    an arbitrary nonnegative int. *)
Example wrong_printf_count_rejected : ~ output_result NarrowPrintf [65; 66] [65; 66] 1.
Proof. intros [(_ & _ & [Hapi | Hcount]) | Hnegative]; simpl in *; unfold negative_int in *; congruence || lia. Qed.

(** Missing or integer-class %s arguments fail admission, not just a
    particular successful output result. *)
Example string_vararg_class_rejected : forall m bytes,
  ~ narrow_format m [37; 115] [WInt 0] bytes.
Proof. intros m bytes H. inversion H; subst; try lia. Qed.
