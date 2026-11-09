(** Retained void callbacks at the labelled program boundary. Entry is
    independently admitted AFTER the exit-registry pop; execution uses
    ordinary [ExternalMachine] steps. A stopped return snapshot precedes
    local teardown, so the shutdown endpoint reconstructs that memory.
    This slice does not intercept exit requests or claim native coverage. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine
  Identity ExternalCalls Startup Stdio Shutdown ExitMemory Walk ExternalMachine.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** A detached installed slot retains its callable address AND capability.
    Free/reserved slots cannot select callback code. *)
Definition callback_target (slot : exit_slot) : option (name * ptr) :=
  match slot with
  | AtSlot _ symbol function | OnSlot _ symbol function _ |
      CxaSlot _ symbol function _ _ => Some (symbol, function)
  | _ => None
  end.

(** Native argument classes, not re-evaluated IR operands. The dummy
    constants are immaterial to [indirect_call_conv], which reads only
    these classes and the separately retained words. *)
Definition callback_args (slot : exit_slot) : list arg :=
  match slot with
  | OnSlot _ _ _ _ => [Arg W (Const 0); Arg P (Const 0)]
  | CxaSlot _ _ _ _ _ => [Arg P (Const 0); Arg W (Const 0)]
  | _ => []
  end.

(** The current signed status is passed as full canonical int bits,
    not the host's low-byte wait status. This pin calls cxa(arg,status). *)
Definition callback_words (slot : exit_slot) (status : Z) : list word :=
  match slot with
  | OnSlot _ _ _ argument => [WInt (status mod 2 ^ 32); WPtr argument]
  | CxaSlot _ _ _ argument _ => [WPtr argument; WInt (status mod 2 ^ 32)]
  | _ => []
  end.

(** The exact selected defined code and generic calling convention.
    Module checking and semantic admission are not consequences of a
    retained Fn capability or of a successful [call_frame]. Only void,
    nonvariadic callbacks are covered by this first bridge. *)
Definition callback_code ge slot entry status fr : Prop :=
  exit_slot_pending slot = [entry] /\ checked_module (ge_module ge) /\
  exists symbol function f converted,
    callback_target slot = Some (symbol, function) /\ ptr_cap function = Fn symbol /\
    function_check_res ge function = Some ok /\ find_fn ge symbol = Some (Defined f) /\
    fn_ret f = RVoid /\ variadic_func f = false /\
    indirect_call_conv f CVoid (callback_args slot) (callback_words slot status) =
      Some (Converted converted None) /\ call_frame f converted = Some fr.

(** Local teardown changes only region lifetimes, never bytes or aux,
    including a global slot retaining a pointer into the ended frame. *)
Lemma callback_locals_contents : forall locals m m',
  invalidate_locals locals m = Some m' -> m_bytes m' = m_bytes m /\ m_aux m' = m_aux m.
Proof.
  unfold invalidate_locals. intros locals. induction locals as [|[x slot] locals IH];
    simpl; intros m m' H.
  - injection H as <-. auto.
  - destruct slot as [base|]; [|exact (IH _ _ H)].
    destruct (object_region base (m_regions m)) as [reg|] eqn:Er;
      [|rewrite fold_left_none in H; discriminate H].
    destruct (r_kind reg), (r_life reg); simpl in H;
      try (rewrite fold_left_none in H; discriminate H).
    destruct (replace_region base _ (m_regions m)) as [rs|] eqn:Ers;
      [|rewrite fold_left_none in H; discriminate H].
    exact (IH _ _ H).
Qed.

(** This additive boundary changes neither machine nor runtime. *)
Module Linked (R : Runtime).
Module M := ExternalMachine R.
Module RM := M.P.I.RM.
Import RM.

Section World.
Variable payload : Type.

(** One authoritative shutdown inventory accompanies arbitrary libc state.
    Callback effects update this very world; return never restores a
    registration-time snapshot. *)
Definition callback_world : Type := (payload * shutdown_state)%type.

(** Entry is checked at the current post-pop memory/runtime/world. The
    physical pop/mark and its effects remain ExitMemory's separate boundary;
    this relation does not claim them from a decoded slot alone. No run,
    successful callback or return is hidden inside admission. *)
Definition callback_entry
    (admitted : registration -> R.state -> mem -> callback_world -> Prop)
    ge slot entry s m w fuel c : Prop :=
  R.ready s m /\ shutdown_at (snd w) = InCallback entry /\
  shutdown_unique (snd w) /\ In (registration_token entry) (shutdown_consumed (snd w)) /\
  -(2 ^ 31) <= shutdown_status (snd w) < 2 ^ 31 /\
  admitted entry s m w /\ exists fr,
    callback_code ge slot entry (shutdown_status (snd w)) fr /\
    c = mkConfig fr [] m fuel.

(** Successful return reconstructs the memory that Semantics computed
    but did not retain in Done. It keeps the CURRENT libc payload, status,
    pending list, consumed history, output state, runtime and fuel. Other
    terminals, including an already completed ExternalExit, do not resume. *)
Inductive callback_return (entry : registration) :
    M.state callback_world -> mstate -> callback_world -> Prop :=
| callback_return_void : forall c s data status pending consumed q m_return,
    c_callers c = [] ->
    shutdown_unique (mkShutdown (InCallback entry) status pending consumed q) ->
    In (registration_token entry) consumed ->
    invalidate_locals (fr_locals (c_frame c)) (c_mem c) = Some m_return ->
    callback_return entry
      (M.Stopped (CoreEnd RetVoid) (c, s)
        (data, mkShutdown (InCallback entry) status pending consumed q))
      (with_mem c m_return, s) (data, mkShutdown Handlers status pending consumed q).

(** The endpoint exposes the very same m_return needed by the handler's
    Iris return postcondition, not merely an existential outcome state. *)
Theorem callback_return_endpoint : forall entry st ms' w',
  callback_return entry st ms' w' ->
  exists c s w m_return,
    st = M.Stopped (CoreEnd RetVoid) (c, s) w /\ c_callers c = [] /\
    invalidate_locals (fr_locals (c_frame c)) (c_mem c) = Some m_return /\
    ms' = (with_mem c m_return, s) /\ fst w' = fst w /\
    shutdown_step (snd w) ReturnCallback (snd w').
Proof.
  intros entry st ms' w' H. destruct H.
  exists c, s, (data, mkShutdown (InCallback entry) status pending consumed q), m_return.
  repeat split; auto. constructor.
Qed.

(** Readiness and object persistence along ordinary labelled callback
    prefixes; this makes no return, termination or failure-freedom claim. *)
Theorem callback_prefix_preserve : forall (registry : name -> option (contract callback_world)) ge st trace st',
  ge_free ge = R.free -> M.run registry ge st trace st' -> M.state_ready _ st ->
  M.state_ready _ st' /\
  persists (c_mem (fst (M.machine_of _ st))) (c_mem (fst (M.machine_of _ st'))).
Proof.
  intros registry ge st trace st' Hfree H. induction H; intros Hr.
  - split; [exact Hr|apply persists_refl].
  - pose proof (M.step_ready _ _ _ _ _ _ Hfree H Hr) as Hr1.
    destruct (IHrun Hr1) as [Hr' Hp]. split; [exact Hr'|].
    eapply persists_trans; [eapply M.step_persists; eauto|exact Hp].
Qed.

(** A return remains ready and retains every identity after invalidating
    locals; exact byte/aux preservation is stronger than mere keptness. *)
Theorem callback_return_preserve : forall entry st ms' w',
  callback_return entry st ms' w' -> M.state_ready _ st ->
  ready_state ms' /\ persists (c_mem (fst (M.machine_of _ st))) (c_mem (fst ms')) /\
  m_bytes (c_mem (fst ms')) = m_bytes (c_mem (fst (M.machine_of _ st))) /\
  m_aux (c_mem (fst ms')) = m_aux (c_mem (fst (M.machine_of _ st))).
Proof.
  intros entry st ms' w' H. destruct H as
    [c s data status pending consumed q m_return Hcallers Hunique Htoken Hlocals].
  simpl. intros Hr.
  pose proof (invalidate_locals_kept _ _ _ Hlocals) as Hkept.
  split; [eapply R.ready_kept; eauto|]. split.
  - eapply kept_ids_persists; [exact Hkept|]. eapply invalidate_locals_ids; eauto.
  - eapply callback_locals_contents; eauto.
Qed.

(** Existing stopped outcomes cannot silently become returned callbacks. *)
Theorem callback_return_only_void : forall entry why ms w ms' w',
  callback_return entry (M.Stopped why ms w) ms' w' -> why = CoreEnd RetVoid.
Proof. intros. inversion H. reflexivity. Qed.

(** A completed ordinary run followed by local teardown preserves readiness
    and every starting identity, with no reset of the runtime or fuel. *)
Theorem callback_run_preserve : forall registry ge start trace stopped entry ms' w',
  ge_free ge = R.free -> M.run registry ge start trace stopped ->
  callback_return entry stopped ms' w' -> M.state_ready _ start ->
  ready_state ms' /\ persists (c_mem (fst (M.machine_of _ start))) (c_mem (fst ms')).
Proof.
  intros registry ge start trace stopped entry ms' w' Hfree Hrun Hreturn Hr.
  destruct (callback_prefix_preserve _ _ _ _ _ Hfree Hrun Hr) as [Hr1 Hp1].
  destruct (callback_return_preserve _ _ _ _ Hreturn Hr1) as (Hr2 & Hp2 & _).
  split; [exact Hr2|]. eapply persists_trans; eauto.
Qed.

End World.
End Linked.

(** Independent execution controls, not native exit-registry memory. *)
Module LinkedChecks.
Module L := Linked InterpRuntime.
Module M := L.M.
Module RM := L.RM.

(** Adversarial core code makes a local escape into a global, calls
    another ordinary function, then returns. It deliberately uses an A
    word as P: it is NOT claimed to pass checking or callback admission.
    Finalization must still invalidate its locals, not restore a live
    pre-return snapshot. Checked code selection is exercised separately. *)
Definition escape_function : func := mkFunc (TAtom "escape") (TAtom "local") RVoid []
  [mkBlock (TAtom "entry") []
    [LocalAlloc (TAtom "local") 8;
     Let (TAtom "p") A (CheckLocal (TAtom "local") 0 1 Read 1) [];
     Let (TAtom "dst") A (Check 0 8 Write 8) [Global (TAtom "sink")];
     RawStorePointer 0 (Tmp (TAtom "p")) (Tmp (TAtom "dst"))
       [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite];
     Call CVoid (Global (TAtom "helper")) []] JRetVoid].

(** A genuine nested call, with its own enter and return steps. Its
    harmless null-pointer flight makes the separate module checked-stage. *)
Definition escape_helper : func := mkFunc (TAtom "helper") (TAtom "local") RVoid []
  [mkBlock (TAtom "entry") [] [Flight (TAtom "unused") Copy [FValue (Const 0)] LowerNone] JRetVoid].

(** The handwritten symbol map supplies callable addresses and a writable
    global cell. Checking code is separate from that memory image. *)
Definition escape_module : Syntax.module :=
  [IFunc escape_function; IFunc escape_helper; IData (TAtom "sink") LLocal 8 [Zero 8]].

(** All three bindings are deliberately independent of the allocator. *)
Definition escape_ge : genv := mkGenv escape_module
  [(TAtom "escape", mkPtr 1024 (Fn (TAtom "escape")));
   (TAtom "helper", mkPtr 1040 (Fn (TAtom "helper")));
   (TAtom "sink", mkPtr 2048 (Obj 2048))] InterpRuntime.free.

(** The writable global cell initially stores canonical null. *)
Definition escape_memory : mem :=
  mkMem (fun _ => 0) [mkRegion 2048 2056 GlobalData Live] (fun _ => CNone).

(** Registration instances, not callback names, determine consumption. *)
Definition escape_registration : registration :=
  mkRegistration 7 (CxaExit (TAtom "escape") (WPtr (mkPtr 0 CNone))).

(** The current world already contains a consumed active token and an
    older pending handler. Payload and signed status must survive return. *)
Definition escape_world : L.callback_world nat :=
  (19%nat, mkShutdown (InCallback escape_registration) (-257) [exit_first] [7%nat] stdout_initial).

(** Entry retains the shared memory and an explicit finite fuel budget. *)
Definition escape_start : config := mkConfig
  (mkFrame escape_function [] [(TAtom "local", None)] None (Enter (TAtom "entry") None))
  [] escape_memory 23.

(** The actual allocation and pointer-store endpoint, before return. *)
Definition escape_written : mem := store_bytes
  (store_aux (allocated escape_memory (local_req 8) 4294967296) 2048 (Obj 4294967296))
  2048 8 4294967296.

(** Parent entry and helper entry each consumed one unit of fuel. *)
Definition escape_terminal : config := mkConfig
  (mkFrame escape_function
    [(TAtom "dst", WPtr (mkPtr 2048 (Obj 2048)));
     (TAtom "p", WPtr (mkPtr 4294967296 (Obj 4294967296)))]
    [(TAtom "local", Some 4294967296)] None (Exec (TAtom "entry") [] JRetVoid))
  [] escape_written 21.

(** This independently named memory is NOT the stopped observation snapshot. *)
Definition escape_returned : mem := mkMem (m_bytes escape_written)
  [mkRegion 4294967296 4294967296 Stack Freed; mkRegion 2048 2056 GlobalData Live]
  (m_aux escape_written).

(** A separately checked handler makes address rejection nonvacuous. *)
Definition void_ge : genv := mkGenv [IFunc escape_helper]
  [(TAtom "helper", mkPtr 1040 (Fn (TAtom "helper")))] InterpRuntime.free.

(** Cxa's unused extras go through generic conversion before call_frame
    in a separately checked module; they do not add parameters to the
    public void(void) handler. The adversarial escape code is excluded. *)
Example callback_void_code_selected : forall status,
  callback_code void_ge
    (CxaSlot 8 (TAtom "helper") (mkPtr 1040 (Fn (TAtom "helper"))) (mkPtr 0 CNone) (mkPtr 0 CNone))
    (mkRegistration 8 (CxaExit (TAtom "helper") (WPtr (mkPtr 0 CNone)))) status
    (mkFrame escape_helper [] [] None (Enter (TAtom "entry") None)).
Proof.
  intros status.
  split; [reflexivity|]. split; [vm_compute; auto|].
  exists (TAtom "helper"), (mkPtr 1040 (Fn (TAtom "helper"))), escape_helper, [].
  repeat split; reflexivity.
Qed.

(** The adversarial entry-to-return core run really allocates the local
    and stores its pointer. No opaque callback-success action is used;
    no validation or native reachability is claimed for this control. *)
Example escape_runs :
  M.run (fun _ => None) escape_ge
    (M.Running (escape_start, InterpRuntime.start) escape_world) []
    (M.Stopped (CoreEnd RetVoid) (escape_terminal, 4294967328) escape_world).
Proof.
  eapply M.run_cons with (trace := []) (tail := []);
    [apply M.step_core; eapply RM.mstep_next; reflexivity|].
  eapply M.run_cons with (trace := []) (tail := []);
    [apply M.step_core; eapply RM.mstep_alloc with (base := 4294967296) (q := local_req 8);
      [reflexivity|simpl; lia|reflexivity]|].
  (* Normalize each endpoint, but keep symbolic byte/aux functions folded. *)
  do 7 (cbv -[store_bytes store_aux];
    eapply M.run_cons with (trace := []) (tail := []);
      [apply M.step_core; eapply RM.mstep_next; cbv -[store_bytes store_aux]; reflexivity|]).
  eapply M.run_cons with (trace := []) (tail := []).
  - apply M.step_core_end.
    + intros site (_ & Hpoint & _). discriminate Hpoint.
    + reflexivity.
  - constructor.
Qed.

(** The escaped identity is live in the stopped snapshot, freed at the
    reconstructed endpoint, and still present in the global's aux slot. *)
Example escape_lifetime_boundary :
  object_region 4294967296 (m_regions (c_mem escape_terminal)) =
    Some (mkRegion 4294967296 4294967304 Stack Live) /\
  invalidate_locals (fr_locals (c_frame escape_terminal)) (c_mem escape_terminal) = Some escape_returned /\
  pointer_slot escape_returned 2048 (mkPtr 4294967296 (Obj 4294967296)) /\
  object_region 4294967296 (m_regions escape_returned) =
    Some (mkRegion 4294967296 4294967296 Stack Freed) /\
  access_res escape_returned 4294967296 (Obj 4294967296) 1 Read 1 = Some (RTrap OutOfBounds).
Proof. repeat split; try reflexivity; simpl; lia. Qed.

(** Normal finalization resumes Handlers with the current pending list,
    status, payload, consumed token and remaining fuel, not the entry frame. *)
Example escape_resumes :
  L.callback_return nat escape_registration
    (M.Stopped (CoreEnd RetVoid) (escape_terminal, 4294967328) escape_world)
    (RM.with_mem escape_terminal escape_returned, 4294967328)
    (19%nat, mkShutdown Handlers (-257) [exit_first] [7%nat] stdout_initial).
Proof.
  constructor; [reflexivity| |left; reflexivity|reflexivity].
  unfold shutdown_unique. simpl. repeat constructor; simpl; intuition discriminate.
Qed.

(** Correct Fn authority with a wrong callable address cannot be admitted. *)
Example callback_wrong_address :
  function_check_res void_ge (mkPtr 1041 (Fn (TAtom "helper"))) = Some (RTrap NotAFunction) /\
  forall fr, ~ callback_code void_ge
    (CxaSlot 8 (TAtom "helper") (mkPtr 1041 (Fn (TAtom "helper"))) (mkPtr 0 CNone) (mkPtr 0 CNone))
    (mkRegistration 8 (CxaExit (TAtom "helper") (WPtr (mkPtr 0 CNone)))) (-257) fr.
Proof.
  split; [reflexivity|]. intros fr (_ & _ & symbol & function & f & converted & Htarget & _ & Hcheck & _).
  injection Htarget as <- <-. discriminate Hcheck.
Qed.

(** Native flavor order and signed status differ from the host wait byte. *)
Example callback_native_words :
  callback_words (AtSlot 8 (TAtom "helper") (mkPtr 1040 (Fn (TAtom "helper")))) (-257) = [] /\
  callback_words (OnSlot 8 (TAtom "helper") (mkPtr 1040 (Fn (TAtom "helper"))) (mkPtr 2049 (Ro 2048))) (-257) =
    [WInt 4294967039; WPtr (mkPtr 2049 (Ro 2048))] /\
  callback_words (CxaSlot 8 (TAtom "helper") (mkPtr 1040 (Fn (TAtom "helper")))
      (mkPtr 2049 (Ro 2048)) (mkPtr 4096 (Obj 4096))) (-257) =
    [WPtr (mkPtr 2049 (Ro 2048)); WInt 4294967039].
Proof. repeat split; reflexivity. Qed.

(** Already completed external exits and fuel/resource endings do not
    acquire a normal callback return edge. *)
Example callback_terminal_controls : forall ms' w',
  ~ L.callback_return nat escape_registration
    (M.Stopped (ExternalExit 9) (escape_terminal, 4294967328) escape_world) ms' w' /\
  ~ L.callback_return nat escape_registration
    (M.Stopped (CoreEnd OutOfFuel) (escape_terminal, 4294967328) escape_world) ms' w'.
Proof. intros. split; intro H; inversion H. Qed.

End LinkedChecks.
