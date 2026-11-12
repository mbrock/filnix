(** These fixtures check the retained libc contracts against the interpreter
    runtime. They cover admitted calls and rejected boundary cases without
    adding dependencies to the live external-call framework. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine Identity ExternalCalls LibcCalls.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** The call relations over the interpreter's runtime, for the
    examples below. *)
Module InterpExternal := LibcCalls InterpRuntime.

(** The list-string bridge instantiated with the interpreter's ready memory. *)
Module InterpStrings := StringLengths InterpRuntime.

(** The bytes of hello. *)
Definition hello_bytes : list Z := [104; 101; 108; 108; 111].
(** A read-only pointer to the string, at address 1024. *)
Definition hello_ptr : ptr := mkPtr 1024 (Ro 1024).
(** The fixture's one libc root: 16 writable bytes at 2048 standing for
    stdout's state. *)
Definition stdout_span : span := mkSpan (mkPtr 2048 (Obj 2048)) 16.
(** A usable stdout whose only root is [stdout_span]. *)
Definition hello_world : stdio_world := mkStdioWorld true [stdout_span].
(** An abstract stream-state fixture, not a native FILE implementation:
    hello and its NUL in a global object at 1024, the libc state at
    2048, and an unrelated caller heap object at 3072. String, libc
    state and caller object are asymmetric. *)
Definition hello_mem : mem :=
  mkMem (fun a => if a =? 1024 then 104 else if a =? 1025 then 101 else
                   if a =? 1026 then 108 else if a =? 1027 then 108 else
                   if a =? 1028 then 111 else 0)
    [mkRegion 1024 1030 GlobalData Live; mkRegion 2048 2064 Heap Live;
     mkRegion 3072 3080 Heap Live] (fun _ => CNone).

(** Use the fixture's libc object as represented errno storage. Both P
    and discarded calls construct an exact, unchanged-state endpoint. *)
Example errno_location_fixture : Forall (fun r =>
  InterpExternal.invoke (errno_location_contract ptr (fun p => p) (fun _ _ => True))
    r [] [] (2 ^ 32) hello_mem (mkPtr 2048 (Obj 2048))
    [] (CallReturn [WPtr (mkPtr 2048 (Obj 2048))])
    (2 ^ 32) hello_mem (mkPtr 2048 (Obj 2048))) [CResult (TAtom "errno") P; CVoid].
Proof.
  apply Forall_forall. intros r [<-|[<-|[]]];
    apply InterpExternal.errno_location_return;
    [split; [right; eexists; reflexivity|reflexivity]|exact I|
     |split; [left; reflexivity|reflexivity]|exact I|].
  all: (split; [discriminate|]; split; [|reflexivity];
    split; [simpl; lia|]; exists 2048, (mkRegion 2048 2064 Heap Live);
    repeat split; reflexivity).
Qed.

(** Invalid cells never invoke: null, read-only, misaligned, too short,
    missing, and freed. The freed case keeps a former object's bytes. *)
Example errno_location_invalid_cells :
  Forall (fun p => forall r args s trace ending s' m' w',
    ~ InterpExternal.invoke (errno_location_contract ptr (fun q => q) (fun _ _ => True))
      r args [] s hello_mem p trace ending s' m' w')
    [mkPtr 0 (Obj 2048); mkPtr 2048 (Ro 2048); mkPtr 2049 (Obj 2048);
     mkPtr 2064 (Obj 2048); mkPtr 4096 (Obj 4096)] /\
  (forall r args s trace ending s' m' w',
    ~ InterpExternal.invoke (errno_location_contract ptr (fun q => q) (fun _ _ => True))
      r args [] s (mkMem (m_bytes hello_mem) [mkRegion 2048 2048 Heap Freed] (m_aux hello_mem))
      (mkPtr 2048 (Obj 2048)) trace ending s' m' w').
Proof.
  assert (Hreject : forall m p, ~ errno_cell m p -> forall r args s trace ending s' m' w',
    ~ InterpExternal.invoke (errno_location_contract ptr (fun q => q) (fun _ _ => True))
      r args [] s m p trace ending s' m' w').
  { intros m p Hbad r args s trace ending s' m' w' Hcall.
    destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as (_ & _ & _ & Hcell & _). exact (Hbad Hcell). }
  split.
  - repeat constructor; apply Hreject;
      intros (Hnz & (_ & base & reg & Hcap & Hr & Hl & Ha) & Halign);
      simpl in Hcap; try discriminate Hcap; injection Hcap as <-;
      try solve [vm_compute in Hr, Halign, Hnz; intuition congruence];
      vm_compute in Hr; injection Hr as <-; vm_compute in Ha; discriminate Ha.
  - apply Hreject. intros (_ & (_ & base & reg & Hcap & Hr & Hl & Ha) & _).
    injection Hcap as <-. vm_compute in Hr. injection Hr as <-. discriminate Hl.
Qed.

(** A writable live cell is not itself evidence of initialized TLS. *)
Example errno_location_unrepresented : forall r args s trace ending s' m' w',
  ~ InterpExternal.invoke (errno_location_contract ptr (fun p => p) (fun _ _ => False))
    r args [] s hello_mem (mkPtr 2048 (Obj 2048)) trace ending s' m' w'.
Proof.
  intros r args s trace ending s' m' w' Hcall.
  destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & Hrep & _). exact Hrep.
Qed.

(** The abstract model allows writable storage at zero. Reject it for
    being NULL independently of bounds, lifetime, alignment or TLS. *)
Example errno_location_live_null :
  let m := mkMem (fun _ => 0) [mkRegion 0 4 GlobalData Live] (fun _ => CNone) in
  let p := mkPtr 0 (Obj 0) in
  writable_span m (mkSpan p 4) /\ ptr_addr p mod 4 = 0 /\
  forall r args s trace ending s' m' w',
  ~ InterpExternal.invoke (errno_location_contract ptr (fun q => q) (fun _ _ => True))
    r args [] s m p trace ending s' m' w'.
Proof.
  split.
  - split; [simpl; lia|]. exists 0, (mkRegion 0 4 GlobalData Live).
    repeat split; reflexivity.
  - split; [reflexivity|]. intros r args s trace ending s' m' w' Hcall.
    destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as (_ & _ & _ & (Hnonnull & _) & _). apply Hnonnull. reflexivity.
Qed.

(** Even a readable same-address replacement cannot substitute a Ro
    capability for the exact Obj capability supplied by the thread. *)
Example errno_location_no_cap_substitution : forall r args s trace s' m' w',
  ~ InterpExternal.invoke (errno_location_contract ptr (fun p => p) (fun _ _ => True))
    r args [] s hello_mem (mkPtr 2048 (Obj 2048))
    trace (CallReturn [WPtr (mkPtr 2048 (Ro 2048))]) s' m' w'.
Proof.
  intros r args s trace s' m' w' Hcall.
  destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & _ & _ & _ & _ & _ & Hend). discriminate Hend.
Qed.

(** Width coincidence, extra native arguments and extra argument words
    are rejected through the public invocation, not just ABI inspection. *)
Example errno_location_invalid_abi :
  Forall (fun call => let '(r, args, xs) := call in
    forall s trace ending s' m' w',
    ~ InterpExternal.invoke (errno_location_contract ptr (fun p => p) (fun _ _ => True))
      r args xs s hello_mem (mkPtr 2048 (Obj 2048)) trace ending s' m' w')
    [(CResult (TAtom "n") L, [], []); (CVoid, [Arg W (Const 0)], []); (CVoid, [], [WInt 0])].
Proof.
  repeat constructor; intros s trace ending s' m' w' Hcall;
    destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as (([Hvoid|(d & Hr)] & Hargs) & Hxs & _); discriminate.
Qed.

(** The fixture's stream representation: the world is [hello_world]
    and the libc object at 2048 is a live heap object. *)
Definition fixture_rep (m : mem) (w : stdio_world) : Prop :=
  w = hello_world /\ object_region 2048 (m_regions m) = Some (mkRegion 2048 2064 Heap Live).

(** The fixture's one allowed allocation: 32 bytes, 16-aligned. *)
Definition fixture_requests (_ : list word) (_ : mem) (_ : stdio_world) (align size : Z) : Prop :=
  align = 16 /\ size = 32.

(** [hello_ptr] points at the C string hello in [hello_mem]. *)
Lemma hello_string : c_string hello_mem hello_ptr hello_bytes.
Proof. vm_compute. repeat split; lia. Qed.

(** The fixture's stdout is [stdio_ready] in [hello_mem]. *)
Lemma hello_stdio : stdio_ready hello_mem hello_world.
Proof.
  split; [reflexivity|]. constructor; [|constructor].
  split; [simpl; lia|]. exists 2048, (mkRegion 2048 2064 Heap Live).
  repeat split; reflexivity.
Qed.

(** puts of [hello_ptr] meets its precondition in the fixture. *)
Lemma hello_pre : puts_pre fixture_rep [WPtr hello_ptr] hello_mem hello_world.
Proof.
  split; [split; reflexivity|]. split; [exact hello_stdio|].
  exists hello_ptr, hello_bytes. split; [reflexivity|exact hello_string].
Qed.

(** puts of hello may complete having accepted any prefix, accepted, of
    hello and its newline: it returns 0 if that is all of them, and may
    return EOF (2^32 - 1) whatever the prefix. Success and both empty
    and nonempty partial EOF results use the same public call relation,
    [invoke]. No allocation or kernel write is required. *)
Lemma hello_return : forall accepted tail n,
  hello_bytes ++ [10] = accepted ++ tail ->
  ((tail = [] /\ n = 0) \/ n = 2 ^ 32 - 1) ->
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 accepted] (CallReturn [WInt n])
    InterpRuntime.start hello_mem hello_world.
Proof.
  intros accepted tail n Hb Hn.
  eapply InterpExternal.invoke_normal with (born := []).
  - split; [left; reflexivity|]. exists (Const 0). reflexivity.
  - exact hello_pre.
  - split; [constructor|]. split; [split; reflexivity|]. split; [exact hello_stdio|]. split.
    + apply stdio_delegates_refl; [reflexivity|exact (proj2 hello_stdio)].
    + right. exists hello_ptr, hello_bytes, accepted, tail. repeat split; auto using hello_string.
  - exists hello_ptr, hello_bytes, accepted, tail, n.
    split; [reflexivity|]. split; [exact hello_string|]. split; [exact Hb|]. split.
    + destruct Hn as [[Ht ->] | ->];
        [left; split; [exact Ht|change (0 <= 0 < 2147483648); lia] | right; reflexivity].
    + split; [reflexivity|]. split; [reflexivity|exact hello_stdio].
  - intros why H. discriminate H.
  - intros values H. injection H as <-. split.
    + exists (WInt n). split; [reflexivity|]. simpl.
      destruct Hn as [[_ ->] | ->]; reflexivity.
    + constructor; [exact I | constructor].
  - intros status H. discriminate H.
Qed.

(** puts of hello succeeds, accepting hello and a newline and
    returning 0. *)
Example hello_success :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 [104; 101; 108; 108; 111; 10]] (CallReturn [WInt 0])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ []); [reflexivity | left; auto]. Qed.

(** puts of hello may return EOF having accepted nothing. *)
Example hello_eof_empty :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 []] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ (hello_bytes ++ [10])); [reflexivity | right; reflexivity]. Qed.

(** puts of hello may return EOF having accepted only he. *)
Example hello_eof_partial :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 [104; 101]] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ [108; 108; 111; 10]); [reflexivity | right; reflexivity]. Qed.

(** puts of hello may return EOF even having accepted all of it and
    the newline. *)
Example hello_eof_full :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 (hello_bytes ++ [10])] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ []); [reflexivity | right; reflexivity]. Qed.

(** An allocation the contract requests is an [effects] step: the
    interpreter's runtime places it at 2^32 and adds it to born. *)
Example internal_allocation :
  InterpExternal.effects [stdout_span] [stdout_span] []
    (fixture_requests [] hello_mem hello_world)
    InterpRuntime.start hello_mem [] (2 ^ 32 + 48)
    (allocated hello_mem (heap_req 16 32) (2 ^ 32)) [2 ^ 32].
Proof.
  eapply InterpExternal.effects_alloc; [split; reflexivity |
    unfold max_allocation_size; simpl; lia | reflexivity | constructor].
Qed.

(** A call that writes libc state and accepts h, and whose allocation
    the runtime then refuses (its address space is used up), ends as
    [OutOfMemory] keeping that write and that observation. *)
Example refusal_keeps_prefix :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.address_end hello_mem hello_world
    [StreamBytes 1 [104]] (CallResource OutOfMemory)
    InterpRuntime.address_end (store_bytes hello_mem 2048 1 1) hello_world.
Proof.
  eapply InterpExternal.invoke_resource with (born := []).
  - split; [left; reflexivity|]. exists (Const 0). reflexivity.
  - exact hello_pre.
  - split.
    + eapply InterpExternal.effects_local; [apply local_store_bytes|constructor].
      intros b Hb. left. exists stdout_span. split; [left; reflexivity|].
      split; [exact (Forall_inv (proj2 hello_stdio))|]. unfold span_contains. simpl. lia.
    + split; [split; reflexivity|]. split; [exact hello_stdio|]. split.
      * apply stdio_delegates_refl; [reflexivity|exact (proj2 hello_stdio)].
      * right. exists hello_ptr, hello_bytes, ([104]), ([101; 108; 108; 111; 10]).
        split; [reflexivity|]. split; [exact hello_string|]. split; reflexivity.
  - eapply InterpExternal.failure_oom with (align := 16) (size := 32);
      [split; reflexivity | unfold max_allocation_size; simpl; lia | reflexivity].
  - left. reflexivity.
Qed.

(** The interpreter's runtime is [[ready]] in [hello_mem] with any next
    allocation address next from 4096 up to the end of the address
    space. *)
Lemma hello_ready : forall next,
  4096 <= next <= InterpRuntime.address_end -> InterpRuntime.ready next hello_mem.
Proof.
  intros next Hnext. split; [lia|]. split.
  - intros b reg E. cbn -[Z.eqb] in E.
    destruct (1024 =? b) eqn:E1.
    + apply Z.eqb_eq in E1. injection E as <-. simpl. split; [lia|]. split; [lia | discriminate].
    + destruct (2048 =? b) eqn:E2.
      * apply Z.eqb_eq in E2. injection E as <-. simpl. split; [lia|]. split; [lia | discriminate].
      * destruct (3072 =? b) eqn:E3; [|discriminate E].
        apply Z.eqb_eq in E3. injection E as <-. simpl. split; [lia|]. split; [lia | discriminate].
  - intros a Ha. simpl. split; [|reflexivity].
    destruct (a =? 1024) eqn:E1; [apply Z.eqb_eq in E1; lia|].
    destruct (a =? 1025) eqn:E2; [apply Z.eqb_eq in E2; lia|].
    destruct (a =? 1026) eqn:E3; [apply Z.eqb_eq in E3; lia|].
    destruct (a =? 1027) eqn:E4; [apply Z.eqb_eq in E4; lia|].
    destruct (a =? 1028) eqn:E5; [apply Z.eqb_eq in E5; lia|]. reflexivity.
Qed.

(** hello followed by an A is not the string at [hello_ptr], since the
    NUL comes first. This and the examples below are negative contract
    obligations, not invented native traps. *)
Example missing_nul : ~ c_string hello_mem hello_ptr (hello_bytes ++ [65]).
Proof. intros [H _]. discriminate H. Qed.

(** [hello_mem] with every byte A: all six bytes of the string object
    are readable, but the sixth is not a terminator. *)
Definition nonzero_mem : mem :=
  mkMem (fun _ => 65) (m_regions hello_mem) (m_aux hello_mem).

(** In [nonzero_mem], the six bytes at 1024 are readable. *)
Example nonzero_readable : access_res nonzero_mem 1024 (Ro 1024) 6 Read 1 = Some ok.
Proof. reflexivity. Qed.

(** Yet five As are not a C string there: readable bytes without a NUL
    do not satisfy [c_string]. *)
Example missing_nul_in_bounds : ~ c_string nonzero_mem hello_ptr [65; 65; 65; 65; 65].
Proof. intros [_ H]. vm_compute in H. intuition discriminate. Qed.

(** A call cannot add a zero-length root on the string's object to the
    world: its [Obj] capability is not available from stdout's root,
    even though the span has no bytes. *)
Example no_zero_span_root_injection :
  ~ stdio_delegates [stdout_span] [] hello_mem
    (mkStdioWorld true [stdout_span; mkSpan (mkPtr 1024 (Obj 1024)) 0]).
Proof.
  intros H. destruct (H (mkSpan (mkPtr 1024 (Obj 1024)) 0) (or_intror (or_introl eq_refl))) as [Ha _].
  destruct Ha as [Hc | [(s & [<- | []] & Hc) |
    [(s & a & [<- | []] & _ & _ & _ & Hc) | (b & [] & _)]]]; discriminate Hc.
Qed.

(** A call cannot widen stdout's root to cover the unrelated caller
    object at 3072, even with stdout's own capability. *)
Example no_unrelated_root_coverage :
  ~ stdio_delegates [stdout_span] [] hello_mem
    (mkStdioWorld true [mkSpan (mkPtr 2048 (Obj 2048)) 2048]).
Proof.
  intros H. destruct (H (mkSpan (mkPtr 2048 (Obj 2048)) 2048) (or_introl eq_refl)) as [_ Hw].
  assert (Hin : span_contains (mkSpan (mkPtr 2048 (Obj 2048)) 2048) 3072) by (unfold span_contains; simpl; lia).
  destruct (Hw 3072 Hin) as [(s & [<- | []] & _ & Ha) | (b & reg & [] & _)].
  unfold span_contains in Ha. simpl in Ha. lia.
Qed.

(** Writing a byte of the unrelated caller object is not a
    [local_effect] of a call whose only root is stdout's. *)
Example no_unrelated_write :
  ~ local_effect [stdout_span] [stdout_span] [] [] hello_mem (store_bytes hello_mem 3072 1 7).
Proof.
  intros (_ & _ & Hw & _).
  assert (Hn : ~ write_authority [stdout_span] [] hello_mem 3072).
  { intros [(s & [<- | []] & _ & Hin) | (b & reg & [] & _)]; unfold span_contains in Hin; simpl in Hin; lia. }
  destruct (Hw _ Hn) as [Hb _]. discriminate Hb.
Qed.

(** Storing a forged capability to the caller object into stdout's
    state is not a [local_effect]: it has no source. *)
Example no_forged_capability :
  ~ local_effect [stdout_span] [stdout_span] [] [] hello_mem (store_aux hello_mem 2048 (Obj 3072)).
Proof.
  intros (_ & _ & _ & Haux). destruct (Haux 2048) as [H | H]; [discriminate H|].
  destruct H as [H | [(s & [<- | []] & H) | [(s & a & [<- | []] & _ & _ & _ & H) | (b & [] & _)]]];
    discriminate H.
Qed.

(** A read-only source does not make [Obj] of the same address
    available. *)
Example no_readonly_upgrade :
  ~ available_cap [mkSpan hello_ptr 6] [] hello_mem (Obj 1024).
Proof.
  intros [H | [(s & [<- | []] & H) | [(s & a & [<- | []] & _ & _ & _ & H) | (b & [] & _)]]];
    discriminate H.
Qed.

(** Freeing the caller object is not a [local_effect] of a call that
    may release nothing. *)
Example no_unauthorized_release :
  ~ local_effect [stdout_span] [stdout_span] [] [] hello_mem
    (mkMem (m_bytes hello_mem)
      [mkRegion 1024 1030 GlobalData Live; mkRegion 2048 2064 Heap Live;
       mkRegion 3072 3072 Heap Freed] (m_aux hello_mem)).
Proof.
  intros (_ & Hr & _). destruct (Hr 3072 (mkRegion 3072 3072 Heap Freed) eq_refl)
    as (reg & Hreg & [H | ([] & _)]).
  change (Some (mkRegion 3072 3080 Heap Live) = Some reg) in Hreg.
  injection Hreg as <-. discriminate H.
Qed.

(** Once an object is freed, neither a root on it nor its having been
    born in this call gives [write_authority] over it. *)
Example no_write_after_release :
  ~ write_authority [mkSpan (mkPtr 3072 (Obj 3072)) 8] [3072]
    (mkMem (fun _ => 0) [mkRegion 3072 3072 Heap Freed] (fun _ => CNone)) 3072.
Proof.
  intros [(s & [<- | []] & (_ & b & reg & Hcap & Hr & Hl & _) & _) |
          (b & reg & [<- | []] & Hr & _ & Hl & _)]; simpl in *.
  - injection Hcap as <-. injection Hr as <-. discriminate Hl.
  - injection Hr as <-. discriminate Hl.
Qed.

(** High bytes are nonzero bytes, and the exact six-byte object has no
    required seventh byte or terminator for a bound of six. *)
Definition high_byte_mem : mem :=
  mkMem (fun a => if (1024 <=? a) && (a <? 1030)
    then if a =? 1024 then 128 else 255 else m_bytes hello_mem a)
    (m_regions hello_mem) (m_aux hello_mem).

(** High bytes are confined to the represented object, retaining the
    runtime's zeroed unused address space. *)
Example high_byte_ready : InterpRuntime.ready InterpRuntime.start high_byte_mem.
Proof.
  destruct (hello_ready InterpRuntime.start ltac:(unfold InterpRuntime.start, InterpRuntime.address_end; lia))
    as (Hnext & Hregions & Hunused).
  split; [exact Hnext|]. split; [exact Hregions|]. intros a Ha.
  specialize (Hunused a Ha). cbn -[Z.leb Z.ltb Z.eqb].
  assert (Hout : (1024 <=? a) && (a <? 1030) = false).
  { apply andb_false_iff. right. apply Z.ltb_ge. unfold InterpRuntime.start in Ha. lia. }
  rewrite Hout. exact Hunused.
Qed.

(** An actual permitted invocation returns the exhausted bound without
    modifying memory/world or producing observations. *)
Example strnlen_exact_bound :
  InterpExternal.invoke (strnlen_contract unit) CVoid [Arg P (Const 0); Arg L (Const 6)]
    [WPtr hello_ptr; WInt 6] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt 6]) InterpRuntime.start high_byte_mem tt.
Proof.
  apply InterpExternal.strnlen_return.
  - split; [left; reflexivity|]. exists (Const 0), (Const 6). reflexivity.
  - split; [vm_compute; split; congruence|]. split; [lia|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. split; [|lia]. intros i Hi.
      assert (Hinside : (1024 <=? 1024 + i) && (1024 + i <? 1030) = true).
      { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      change (0 < (if (1024 <=? 1024 + i) && (1024 + i <? 1030)
        then if 1024 + i =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + i)) < 256).
      rewrite Hinside.
      change (0 < (if 1024 + i =? 1024 then 128 else 255) < 256).
      destruct (1024 + i =? 1024); lia.
Qed.

(** A readable first NUL permits the largest size_t maximum, even
    though address+maximum would wrap; the sixth byte is the NUL. *)
Example strnlen_early_nul_huge : bounded_length hello_mem hello_ptr (2 ^ 64 - 1) 5.
Proof.
  split; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|]. split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split; [reflexivity|]. split; [|intros; reflexivity]. intros i Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; split; congruence.
Qed.

(** A returning invocation cannot pass the earlier NUL and return six,
    even with the largest bound and arbitrary proposed endpoints. *)
Example strnlen_wrong_result_rejected : forall s' m' w',
  ~ InterpExternal.invoke (strnlen_contract unit) CVoid [Arg P (Const 0); Arg L (Const 0)]
    [WPtr hello_ptr; WInt (2 ^ 64 - 1)] InterpRuntime.start hello_mem tt
    [] (CallReturn [WInt 6]) s' m' w'.
Proof.
  intros s' m' w' Hcall.
  destruct (InterpExternal.strnlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & n & k & Hargs & Hlength & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  pose proof (bounded_length_unique _ _ _ _ _ Hlength strnlen_early_nul_huge). lia.
Qed.

(** Zero count accepts a live read-only one-past pointer without a load. *)
Example strnlen_zero_one_past : bounded_length hello_mem (mkPtr 1030 (Ro 1024)) 0 0.
Proof.
  split; [vm_compute; split; congruence|]. split; [lia|]. split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split; [reflexivity|]. split; intros; lia.
Qed.

(** The same one-past pointer does not admit even one byte of scanning. *)
Example strnlen_positive_one_past_rejected : forall k,
  ~ bounded_length hello_mem (mkPtr 1030 (Ro 1024)) 1 k.
Proof.
  intros k (_ & Hk & _ & Ha & _). assert (k = 0 \/ k = 1) by lia.
  destruct H as [-> | ->]; discriminate Ha.
Qed.

(** Null and non-object capabilities remain failed obligations even
    for zero count, without claiming native zero-count calls trap. *)
Example strnlen_zero_null_rejected : forall m k,
  ~ bounded_length m (mkPtr 0 CNone) 0 k.
Proof. intros m k (_ & _ & (base & reg & [Hcap | Hcap] & _) & _); discriminate Hcap. Qed.

(** A freed empty object passes the raw zero-size access check but not
    the live-object requirement of the bounded scan contract. *)
Example strnlen_zero_freed_rejected : forall k,
  ~ bounded_length (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone))
    (mkPtr 1024 (Obj 1024)) 0 k.
Proof.
  intros k (_ & _ & (base & reg & [Hcap | Hcap] & Hreg & Hlife) & _);
    [injection Hcap as <-; injection Hreg as <-; discriminate Hlife|discriminate Hcap].
Qed.

(** A malformed byte 256 is not a nonzero character merely because
    memory uses Z-valued cells. The contract does not normalize it. *)
Example strnlen_malformed_byte_rejected :
  ~ bounded_length (mkMem (fun _ => 256) (m_regions hello_mem) (m_aux hello_mem)) hello_ptr 1 1.
Proof.
  intros (_ & _ & _ & _ & Hbytes & _). specialize (Hbytes 0 ltac:(lia)). simpl in Hbytes. lia.
Qed.

(** Both the return channel and count argument must have size_t width;
    same-word-count but class-W calls fail independently of behavior. *)
Example strnlen_wrong_abi_rejected :
  ~ strnlen_abi (CResult (TAtom "result") W) [Arg P (Const 0); Arg L (Const 0)] /\
  ~ strnlen_abi CVoid [Arg P (Const 0); Arg W (Const 0)].
Proof.
  split.
  - intros [[Hbad | (d & Hbad)] _]; discriminate Hbad.
  - intros [_ (p & n & Hbad)]. discriminate Hbad.
Qed.

(** An evaluated pointer is not an integer count, even with the right ABI. *)
Example strnlen_pointer_count_rejected :
  ~ contract_pre (strnlen_contract unit) [WPtr hello_ptr; WPtr hello_ptr] hello_mem tt.
Proof. intros (p & n & k & Hargs & _). discriminate Hargs. Qed.

(** The established puts string also meets strlen's explicit live domain. *)
Example strlen_hello_bridge : terminated_length hello_mem hello_ptr 5.
Proof.
  apply (InterpStrings.c_string_length InterpRuntime.start hello_mem hello_ptr hello_bytes).
  - apply hello_ready. unfold InterpRuntime.start, InterpRuntime.address_end. lia.
  - exact hello_string.
Qed.

(** An unaligned high-byte string whose NUL is the object's last byte. *)
Definition strlen_high_mem : mem := store_bytes high_byte_mem 1029 1 0.

(** Offsets zero and one consume high bytes, while offset five is a
    readable empty string. Each reaches the same final in-object NUL. *)
Lemma strlen_boundary_length : forall offset count,
  In (offset, count) [(0, 5); (1, 4); (5, 0)] ->
  terminated_length strlen_high_mem (mkPtr (1024 + offset) (Ro 1024)) count.
Proof.
  intros offset count Hcase. destruct Hcase as [Hcase|[Hcase|[Hcase|[]]]];
    injection Hcase as <- <-.
  all: split; [|vm_compute; congruence]; split; [vm_compute; split; congruence|];
    split; [lia|]; split.
  all: try (exists 1024, (mkRegion 1024 1030 GlobalData Live); split; [right; reflexivity|]; auto).
  all: split; [reflexivity|]; split; [|intros; reflexivity].
  - intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; split; congruence.
  - intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H as [-> | [-> | [-> | ->]]]; vm_compute; split; congruence.
  - intros i Hi. lia.
Qed.

(** The boundary inputs really admit pure size_t returns through the
    public call relation, including the empty and interior strings. *)
Example strlen_boundary_calls : forall offset count,
  In (offset, count) [(0, 5); (1, 4); (5, 0)] ->
  InterpExternal.invoke (strlen_contract unit) (CResult (TAtom "length") L) [Arg P (Const 0)]
    [WPtr (mkPtr (1024 + offset) (Ro 1024))] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WInt count]) InterpRuntime.start strlen_high_mem tt.
Proof.
  intros offset count Hcase. apply InterpExternal.strlen_return.
  - split; [right; exists (TAtom "length"); reflexivity|]. exists (Const 0). reflexivity.
  - apply strlen_boundary_length. exact Hcase.
Qed.

(** Incorrect lengths fail at an otherwise admitted public call,
    independently of the proposed return memory, runtime state or world. *)
Example strlen_wrong_result_rejected : forall bits s' m' w',
  bits <> 4 ->
  ~ InterpExternal.invoke (strlen_contract unit) CVoid [Arg P (Const 0)]
    [WPtr (mkPtr 1025 (Ro 1024))] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WInt bits]) s' m' w'.
Proof.
  intros bits s' m' w' Hwrong Hcall.
  destruct (InterpExternal.strlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & k & Hargs & Hlength & Hending).
  injection Hargs as <-. injection Hending as <-.
  apply Hwrong. eapply terminated_length_unique; [exact Hlength|].
  apply (strlen_boundary_length 1 4). simpl. auto.
Qed.

(** Numeric zeroes outside the high-byte object's bounds cannot satisfy
    strlen's existential admission premise: no in-object NUL exists. *)
Example strlen_missing_nul_rejected :
  ~ contract_pre (strlen_contract unit) [WPtr hello_ptr] high_byte_mem tt.
Proof.
  intros (p & k & Hargs & [(Hn & Hk & _ & Ha & Hbytes & Hnul) Hmax]).
  injection Hargs as <-.
  assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hlt in Ha.
  change (Some (if 1024 + (k + 1) <=? 1030 then ok else RTrap OutOfBounds) = Some ok) in Ha.
  destruct (1024 + (k + 1) <=? 1030) eqn:Hend; [|discriminate Ha].
  apply Z.leb_le in Hend.
  specialize (Hnul Hmax).
  assert (Hinside : (1024 <=? 1024 + k) && (1024 + k <? 1030) = true).
  { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  change ((if (1024 <=? 1024 + k) && (1024 + k <? 1030)
    then if 1024 + k =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + k)) = 0) in Hnul.
  rewrite Hinside in Hnul. destruct (1024 + k =? 1024); discriminate Hnul.
Qed.

(** Unlike zero-count strnlen, strlen needs a readable byte even for an
    empty result. One-past, null and freed pointers are not admitted. *)
Example strlen_bad_authority_rejected :
  ~ contract_pre (strlen_contract unit) [WPtr (mkPtr 1030 (Ro 1024))] hello_mem tt /\
  ~ contract_pre (strlen_contract unit) [WPtr (mkPtr 0 CNone)] hello_mem tt /\
  ~ contract_pre (strlen_contract unit) [WPtr (mkPtr 1024 (Obj 1024))]
    (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone)) tt.
Proof.
  split.
  - intros (p & k & Hargs & [(Hn & Hk & _ & Ha & _) Hmax]). injection Hargs as <-.
    assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
    rewrite Hlt in Ha.
    change (Some (if 1030 + (k + 1) <=? 1030 then ok else RTrap OutOfBounds) = Some ok) in Ha.
    destruct (1030 + (k + 1) <=? 1030) eqn:Hend; [|discriminate Ha].
    apply Z.leb_le in Hend. lia.
  - split; intros (p & k & Hargs & [(_ & _ & (base & reg & [Hcap|Hcap] & Hreg & Hlife) & _) _]);
      injection Hargs as <-; try discriminate Hcap.
    injection Hcap as <-. injection Hreg as <-. discriminate Hlife.
Qed.

(** The ready high-byte fixture admits any canonical int argument,
    including values whose unsigned-char conversion changes them. *)
Lemma memchr_high_input : forall c, 0 <= c < 2 ^ 32 ->
  memchr_input high_byte_mem hello_ptr c 6.
Proof.
  intros c Hc. apply memchr_input_full; [exact Hc|]. split; [vm_compute; split; congruence|]. split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split; [reflexivity|]. intros i Hi.
    assert (Hinside : (1024 <=? 1024 + i) && (1024 + i <? 1030) = true).
    { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
    change (0 <= (if (1024 <=? 1024 + i) && (1024 + i <? 1030)
      then if 1024 + i =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + i)) < 256).
    rewrite Hinside. destruct (1024 + i =? 1024); lia.
Qed.

(** 511 converts to byte 255, whose first match is at offset one even
    though four later bytes also match. Read-only authority is retained. *)
Lemma memchr_high_first :
  memchr_result high_byte_mem hello_ptr 511 6 (mkPtr 1025 (Ro 1024)).
Proof.
  left. exists 1. repeat split; try reflexivity; try lia.
  intros i Hi. assert (i = 0) by lia. subst. vm_compute. discriminate.
Qed.

(** The contract really admits a returning pointer invocation. *)
Example memchr_first_call :
  InterpExternal.invoke (memchr_contract unit) (CResult (TAtom "found") P)
    [Arg P (Const 0); Arg W (Const 511); Arg L (Const 6)]
    [WPtr hello_ptr; WInt 511; WInt 6] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WPtr (mkPtr 1025 (Ro 1024))]) InterpRuntime.start high_byte_mem tt.
Proof.
  apply InterpExternal.memchr_return.
  - split; [right; eexists; reflexivity|]. eexists _, _, _. reflexivity.
  - apply memchr_high_input. vm_compute; split; congruence.
  - exact memchr_high_first.
Qed.

(** Later matches, fabricated null and correct-address capability
    amplification/loss all fail through the public invocation relation. *)
Example memchr_wrong_pointer_rejected : forall q s' m' w',
  In q [mkPtr 1026 (Ro 1024); mkPtr 0 CNone; mkPtr 1025 (Obj 1024); mkPtr 1025 CNone] ->
  ~ InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 511); Arg L (Const 6)]
    [WPtr hello_ptr; WInt 511; WInt 6] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & n & result & Hargs & Hresult & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  pose proof (memchr_result_unique _ _ _ _ _ _ Hresult memchr_high_first) as Heq.
  destruct Hbad as [<- | [<- | [<- | [<- | []]]]]; discriminate Heq.
Qed.

(** No byte is zero in the same bounded binary region. *)
Example memchr_miss : memchr_result high_byte_mem hello_ptr 0 6 (mkPtr 0 CNone).
Proof.
  right. split; [|reflexivity]. intros i Hi.
  assert (Hinside : (1024 <=? 1024 + i) && (1024 + i <? 1030) = true).
  { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  change ((if (1024 <=? 1024 + i) && (1024 + i <? 1030)
    then if 1024 + i =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + i)) <> 0).
  rewrite Hinside. destruct (1024 + i =? 1024); discriminate.
Qed.

(** Zero is searchable binary data, not an implicit stopping condition. *)
Example memchr_zero_byte : memchr_result hello_mem hello_ptr 0 6 (mkPtr 1029 (Ro 1024)).
Proof.
  left. exists 5. repeat split; try reflexivity; try lia.
  intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; discriminate.
Qed.

(** Read-only live one-past is admitted at zero count and returns null. *)
Example memchr_zero_one_past :
  memchr_input hello_mem (mkPtr 1030 (Ro 1024)) (2 ^ 32 - 1) 0 /\
  memchr_result hello_mem (mkPtr 1030 (Ro 1024)) (2 ^ 32 - 1) 0 (mkPtr 0 CNone).
Proof.
  split.
  - apply memchr_input_full; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros; lia.
  - right. split; [intros; lia|reflexivity].
Qed.

(** An immediate match waives the unreadable suffix, not the hit byte. *)
Example memchr_early_hit :
  memchr_input high_byte_mem hello_ptr 128 (2 ^ 64 - 1).
Proof.
  split; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|].
  exists 0. split; [lia|]. split.
  - change (readable_bytes high_byte_mem hello_ptr 1).
    split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros i Hi. assert (i = 0) by lia. subst. vm_compute; split; congruence.
  - split; [intros; lia|intros; reflexivity].
Qed.

(** An immediate hit admits a real call even with an unreadable suffix. *)
Example memchr_early_call :
  InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 128); Arg L (Const (2 ^ 64 - 1))]
    [WPtr hello_ptr; WInt 128; WInt (2 ^ 64 - 1)] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WPtr hello_ptr]) InterpRuntime.start high_byte_mem tt.
Proof.
  apply InterpExternal.memchr_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - exact memchr_early_hit.
  - left. exists 0. split; [vm_compute; split; congruence|]. split; [reflexivity|].
    split; [intros; lia|reflexivity].
Qed.

(** The object's final NUL permits an oversized count without granting
    authority after the matching byte. The same proof covers SIZE_MAX. *)
Lemma memchr_final_nul_input : forall n,
  6 <= n < 2 ^ 64 -> memchr_input hello_mem hello_ptr 0 n.
Proof.
  intros n Hn. split; [vm_compute; split; congruence|]. split; [lia|].
  exists 5. split; [lia|]. split.
  - rewrite (proj2 (Z.ltb_lt 5 n) ltac:(lia)).
    split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
      destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; split; congruence.
  - split.
    + intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; discriminate.
    + intros. reflexivity.
Qed.

(** Exact-bound, oversized and SIZE_MAX calls return the same final byte. *)
Example memchr_final_nul_calls : forall n,
  In n [6; 12; 2 ^ 64 - 1] ->
  InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 0); Arg L (Const n)]
    [WPtr hello_ptr; WInt 0; WInt n] InterpRuntime.start hello_mem tt
    [] (CallReturn [WPtr (mkPtr 1029 (Ro 1024))]) InterpRuntime.start hello_mem tt.
Proof.
  intros n Hn. assert (Hbound : 6 <= n < 2 ^ 64).
  { destruct Hn as [<- | [<- | [<- | []]]]; vm_compute; split; congruence. }
  apply InterpExternal.memchr_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply memchr_final_nul_input. exact Hbound.
  - left. exists 5. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
    intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; discriminate.
Qed.

(** A null, a later matching byte in total memory, and same-address
    capability substitutions are rejected on an admitted early-stop call. *)
Example memchr_early_wrong_result : forall q s' m' w',
  In q [mkPtr 0 CNone; mkPtr 1030 (Ro 1024); mkPtr 1029 (Obj 1024); mkPtr 1029 CNone] ->
  ~ InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 0); Arg L (Const 12)]
    [WPtr hello_ptr; WInt 0; WInt 12] InterpRuntime.start hello_mem tt
    [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & n & result & Hargs & Hresult & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  destruct (InterpExternal.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _
    (memchr_final_nul_calls 12 ltac:(simpl; auto)))
    as (_ & _ & _ & p & c & n & result & Hargs & Hright & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  pose proof (memchr_result_unique _ _ _ _ _ _ Hresult Hright) as Heq.
  destruct Hbad as [<- | [<- | [<- | [<- | []]]]]; discriminate Heq.
Qed.

(** A match at offset n is ignored; the immediately larger bound above
    includes it. This five-byte miss still has full readable authority. *)
Example memchr_match_at_count_ignored :
  InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 0); Arg L (Const 5)]
    [WPtr hello_ptr; WInt 0; WInt 5] InterpRuntime.start hello_mem tt
    [] (CallReturn [WPtr (mkPtr 0 CNone)]) InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.memchr_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply memchr_input_full; [vm_compute; split; congruence|].
    split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; split; congruence.
  - right. split; [|reflexivity]. intros i Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; discriminate.
Qed.

(** Binary search crosses an earlier NUL to find a nonzero byte. *)
Example memchr_crosses_nul :
  InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 111); Arg L (Const 12)]
    [WPtr hello_ptr; WInt 111; WInt 12] InterpRuntime.start (store_bytes hello_mem 1025 1 0) tt
    [] (CallReturn [WPtr (mkPtr 1028 (Ro 1024))])
    InterpRuntime.start (store_bytes hello_mem 1025 1 0) tt.
Proof.
  apply InterpExternal.memchr_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - split; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|].
    exists 4. split; [lia|]. split.
    + change (readable_bytes (store_bytes hello_mem 1025 1 0) hello_ptr 5).
      split; [vm_compute; split; congruence|]. split.
      * exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
      * split; [reflexivity|]. intros i Hi.
        assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
        destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; split; congruence.
    + split; [|intros; reflexivity]. intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
      destruct H as [-> | [-> | [-> | ->]]]; vm_compute; discriminate.
  - left. exists 4. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
    intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H as [-> | [-> | [-> | ->]]]; vm_compute; discriminate.
Qed.

(** A zero in total memory just beyond the object cannot authorize a
    miss or a matching read there. All in-object bytes are nonzero. *)
Example memchr_unreadable_match_rejected : ~ memchr_input high_byte_mem hello_ptr 0 7.
Proof.
  intros (_ & _ & k & Hk & (_ & _ & Ha & _) & _ & Hmatch).
  change (Some (if 1024 + (k + (if k <? 7 then 1 else 0)) <=? 1030
    then ok else RTrap OutOfBounds) = Some ok) in Ha.
  destruct (1024 + (k + (if k <? 7 then 1 else 0)) <=? 1030) eqn:Hend; [|discriminate Ha].
  apply Z.leb_le in Hend.
  assert (Hlt : k < 7) by (destruct (k <? 7) eqn:E; [apply Z.ltb_lt; exact E|lia]).
  rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hend.
  specialize (Hmatch Hlt).
  destruct memchr_miss as [Hbad|[Hmiss _]].
  - destruct Hbad as (i & _ & _ & _ & Hptr). discriminate Hptr.
  - apply (Hmiss k ltac:(lia)). exact Hmatch.
Qed.

(** Null and freed authority are not admitted even at zero count. *)
Example memchr_zero_invalid_rejected :
  (forall m, ~ memchr_input m (mkPtr 0 CNone) 0 0) /\
  ~ memchr_input (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone))
    (mkPtr 1024 (Obj 1024)) 0 0.
Proof.
  split.
  - intros m (_ & _ & k & _ & (_ & (base & reg & [Hcap | Hcap] & _) & _) & _); discriminate Hcap.
  - intros (_ & _ & k & _ & (_ & (base & reg & [Hcap | Hcap] & Hreg & Hlife) & _) & _);
      [injection Hcap as <-; injection Hreg as <-; discriminate Hlife|discriminate Hcap].
Qed.

(** Wrong ABI classes and unnormalized scalar words fail independently
    of whether a finite search result can be described. *)
Example memchr_bad_domain_rejected :
  ~ memchr_abi (CResult (TAtom "found") L) [Arg P (Const 0); Arg W (Const 0); Arg L (Const 0)] /\
  ~ memchr_abi CVoid [Arg P (Const 0); Arg L (Const 0); Arg L (Const 0)] /\
  ~ memchr_input high_byte_mem hello_ptr (-1) 6 /\
  ~ memchr_input high_byte_mem hello_ptr 128 (2 ^ 64).
Proof.
  split; [intros [[H | (d & H)] _]; discriminate H|]. split.
  - intros [_ (p & c & n & H)]. discriminate H.
  - split.
    + intros (Hc & _). lia.
    + intros (_ & Hn & _). lia.
Qed.

(** Two overlapping five-byte spans of the ready high-byte fixture. *)
Lemma high_five_readable : forall offset, 0 <= offset <= 1 ->
  readable_bytes high_byte_mem (mkPtr (1024 + offset) (Ro 1024)) 5.
Proof.
  intros offset Hoffset. split; [vm_compute; split; congruence|]. split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split.
    + assert (Hlo : (1024 <=? 1024 + offset) = true) by (apply Z.leb_le; lia).
      assert (Hhi : (1024 + offset + 5 <=? 1030) = true) by (apply Z.leb_le; lia).
      unfold access_res, cap_access_res. cbn -[Z.add Z.leb Z.modulo].
      rewrite Hlo, Hhi. simpl. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
    + intros i Hi.
      assert (Hinside : (1024 <=? 1024 + offset + i) && (1024 + offset + i <? 1030) = true).
      { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      change (0 <= (if (1024 <=? 1024 + offset + i) && (1024 + offset + i <? 1030)
        then if 1024 + offset + i =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + offset + i)) < 256).
      rewrite Hinside. destruct (1024 + offset + i =? 1024); lia.
Qed.

(** The first unsigned-byte pair is 128 versus 255. *)
Lemma memcmp_high_less :
  memcmp_order high_byte_mem hello_ptr (mkPtr 1025 (Ro 1024)) 5 Datatypes.Lt.
Proof.
  right. exists 0. split; [lia|]. split; [intros; lia|]. split; [discriminate|reflexivity].
Qed.

(** Reversing the two overlapping spans reverses their order. *)
Lemma memcmp_high_greater :
  memcmp_order high_byte_mem (mkPtr 1025 (Ro 1024)) hello_ptr 5 Datatypes.Gt.
Proof.
  right. exists 0. split; [lia|]. split; [intros; lia|]. split; [discriminate|reflexivity].
Qed.

(** Distinct nonunit negative magnitudes, including one greater than
    255, are permitted; the byte difference itself need not be returned. *)
Example memcmp_negative_magnitudes : forall bits, In bits [2 ^ 32 - 2; 2 ^ 32 - 7; 2 ^ 32 - 512] ->
  InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const 5)]
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024)); WInt 5] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt bits]) InterpRuntime.start high_byte_mem tt.
Proof.
  intros bits Hbits. apply InterpExternal.memcmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply (high_five_readable 0). lia.
  - apply (high_five_readable 1). lia.
  - split.
    + destruct Hbits as [<- | [<- | [<- | []]]]; vm_compute; split; congruence.
    + exists Datatypes.Lt. split; [exact memcmp_high_less|].
      destruct Hbits as [<- | [<- | [<- | []]]]; reflexivity.
Qed.

(** Positive 2, 7 and 512 are also permitted through the public invocation. *)
Example memcmp_positive_magnitudes : forall bits, In bits [2; 7; 512] ->
  InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 1); Arg P (Const 0); Arg L (Const 5)]
    [WPtr (mkPtr 1025 (Ro 1024)); WPtr hello_ptr; WInt 5] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt bits]) InterpRuntime.start high_byte_mem tt.
Proof.
  intros bits Hbits. apply InterpExternal.memcmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply (high_five_readable 1). lia.
  - apply (high_five_readable 0). lia.
  - split.
    + destruct Hbits as [<- | [<- | [<- | []]]]; vm_compute; split; congruence.
    + exists Datatypes.Gt. split; [exact memcmp_high_greater|].
      destruct Hbits as [<- | [<- | [<- | []]]]; reflexivity.
Qed.

(** Wrong zero/positive signs are rejected at otherwise admitted calls. *)
Example memcmp_wrong_sign_rejected : forall bits s' m' w', In bits [0; 2; 7] ->
  ~ InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const 5)]
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024)); WInt 5] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt bits]) s' m' w'.
Proof.
  intros bits s' m' w' Hbad Hcall.
  destruct (InterpExternal.memcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & q & n & result & Hargs & (_ & ordering & Horder & Hsign) & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  pose proof (memcmp_order_unique _ _ _ _ _ _ Horder memcmp_high_less) as ->.
  destruct Hbad as [<- | [<- | [<- | []]]]; discriminate Hsign.
Qed.

(** Comparing an identical span is admitted and returns zero. *)
Example memcmp_identical :
  InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 5)]
    [WPtr hello_ptr; WPtr hello_ptr; WInt 5] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt 0]) InterpRuntime.start high_byte_mem tt.
Proof.
  apply InterpExternal.memcmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply (high_five_readable 0). lia.
  - apply (high_five_readable 0). lia.
  - split; [vm_compute; split; congruence|]. exists Datatypes.Eq.
    split; [left; split; reflexivity|reflexivity].
Qed.

(** A differing byte exactly at the bound is invisible until the count
    includes it. The two selected spans overlap in the ready hello memory. *)
Example memcmp_count_boundary :
  memcmp_order hello_mem (mkPtr 1026 (Ro 1024)) (mkPtr 1027 (Ro 1024)) 1 Datatypes.Eq /\
  memcmp_order hello_mem (mkPtr 1026 (Ro 1024)) (mkPtr 1027 (Ro 1024)) 2 Datatypes.Lt.
Proof.
  split.
  - left. split; [reflexivity|]. intros i Hi. assert (i = 0) by lia. subst. reflexivity.
  - right. exists 1. split; [lia|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
Qed.

(** Checking only the first span is insufficient, even with an immediate
    difference. The second span extends one byte past its object. *)
Example memcmp_second_span_required :
  ~ contract_pre (memcmp_contract unit)
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024)); WInt 6] high_byte_mem tt.
Proof.
  intros (p & q & n & Hargs & _ & _ & _ & Ha & _).
  injection Hargs as <- <- <-. discriminate Ha.
Qed.

(** Neither side's missing authority is waived by a zero count. *)
Example memcmp_zero_authority_required : forall m p q,
  ptr_cap p = CNone \/ ptr_cap q = CNone ->
  ~ contract_pre (memcmp_contract unit) [WPtr p; WPtr q; WInt 0] m tt.
Proof.
  intros m p q Hbad (left & right & n & Hargs & Hl & Hr).
  injection Hargs as <- <- <-.
  destruct Hbad as [Hbad | Hbad];
    destruct Hl as (_ & (bl & rl & [Hcl | Hcl] & _) & _);
    destruct Hr as (_ & (br & rr & [Hcr | Hcr] & _) & _);
    rewrite Hbad in *; discriminate.
Qed.

(** Both live one-past arguments remain admitted at zero count. *)
Example memcmp_zero_one_past :
  InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 0)]
    [WPtr (mkPtr 1030 (Ro 1024)); WPtr (mkPtr 1030 (Ro 1024)); WInt 0]
    InterpRuntime.start hello_mem tt [] (CallReturn [WInt 0]) InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.memcmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - destruct (proj1 memchr_zero_one_past) as (_ & _ & k & Hk & Hread & _).
    assert (k = 0) by lia. subst. exact Hread.
  - destruct (proj1 memchr_zero_one_past) as (_ & _ & k & Hk & Hread & _).
    assert (k = 0) by lia. subst. exact Hread.
  - split; [vm_compute; split; congruence|]. exists Datatypes.Eq. split; [|reflexivity].
    left. split; [reflexivity|intros; lia].
Qed.

(** Full-span admission rejects malformed cells and noncanonical counts. *)
Example readable_bytes_bad_domain :
  ~ readable_bytes (mkMem (fun _ => 256) (m_regions hello_mem) (m_aux hello_mem)) hello_ptr 1 /\
  ~ readable_bytes high_byte_mem hello_ptr (-1).
Proof.
  split.
  - intros (_ & _ & _ & Hbytes). specialize (Hbytes 0 ltac:(lia)). simpl in Hbytes. lia.
  - intros (Hn & _). lia.
Qed.

(** Same-width ABI shortcuts cannot change the result or count class. *)
Example memcmp_wrong_abi_rejected :
  ~ memcmp_abi (CResult (TAtom "compared") L) [Arg P (Const 0); Arg P (Const 0); Arg L (Const 0)] /\
  ~ memcmp_abi CVoid [Arg P (Const 0); Arg P (Const 0); Arg W (Const 0)].
Proof.
  split.
  - intros [[H | (d & H)] _]; discriminate H.
  - intros [_ (p & q & n & H)]. discriminate H.
Qed.

(** ## Bounded string comparison controls *)

(** Three short strings in existing represented objects: "a" followed
    by z, "a" followed by b, and "ab". Differences after a shared NUL
    must not affect strncmp, unlike a binary comparison. *)
Definition string_compare_mem : mem :=
  mkMem (fun a =>
    if a =? 1024 then 97 else if a =? 1025 then 0 else if a =? 1026 then 122 else
    if a =? 2048 then 97 else if a =? 2049 then 0 else if a =? 2050 then 98 else
    if a =? 2052 then 97 else if a =? 2053 then 98 else if a =? 2054 then 0 else
    m_bytes hello_mem a) (m_regions hello_mem) (m_aux hello_mem).

(** The fixture changes only bytes below the runtime's unused space. *)
Example string_compare_ready : InterpRuntime.ready InterpRuntime.start string_compare_mem.
Proof.
  destruct (hello_ready InterpRuntime.start ltac:(unfold InterpRuntime.start, InterpRuntime.address_end; lia))
    as (Hnext & Hregions & Hunused).
  split; [exact Hnext|]. split; [exact Hregions|]. intros a Ha.
  unfold string_compare_mem. cbn -[Z.eqb].
  repeat match goal with
  | |- context [a =? ?b] => destruct (a =? b) eqn:E;
    [apply Z.eqb_eq in E; unfold InterpRuntime.start in Ha; lia|clear E]
  end. split; reflexivity.
Qed.

(** Independent short-string witnesses remain valid with a huge bound. *)
Lemma string_compare_lengths : forall n, 3 <= n < 2 ^ 64 ->
  bounded_length string_compare_mem hello_ptr n 1 /\
  bounded_length string_compare_mem (mkPtr 2048 (Ro 2048)) n 1 /\
  bounded_length string_compare_mem (mkPtr 2052 (Ro 2048)) n 2.
Proof.
  intros n Hn. assert (Hone : (1 <? n) = true) by (apply Z.ltb_lt; lia).
  assert (Htwo : (2 <? n) = true) by (apply Z.ltb_lt; lia).
  split; [|split]; unfold bounded_length.
  all: split; [lia|]; split; [lia|]; split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split; [rewrite Hone; reflexivity|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. vm_compute. split; congruence.
    + intros _. reflexivity.
  - exists 2048, (mkRegion 2048 2064 Heap Live). split; [right; reflexivity|]. auto.
  - split; [rewrite Hone; reflexivity|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. vm_compute. split; congruence.
    + intros _. reflexivity.
  - exists 2048, (mkRegion 2048 2064 Heap Live). split; [right; reflexivity|]. auto.
  - split; [rewrite Htwo; reflexivity|]. split.
    + intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; vm_compute; split; congruence.
    + intros _. reflexivity.
Qed.

(** A shared NUL cuts off later differing bytes even at SIZE_MAX. *)
Example strncmp_shared_nul_huge :
  InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const (2 ^ 64 - 1))]
    [WPtr hello_ptr; WPtr (mkPtr 2048 (Ro 2048)); WInt (2 ^ 64 - 1)]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WInt 0])
    InterpRuntime.start string_compare_mem tt.
Proof.
  apply InterpExternal.strncmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - destruct (string_compare_lengths (2 ^ 64 - 1) ltac:(vm_compute; split; congruence)) as (Hl & Hr & _).
    exists 1, 1. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq. split; [|reflexivity].
    left. split; [reflexivity|].
    change (forall i, 0 <= i < 2 ->
      m_bytes string_compare_mem (1024 + i) = m_bytes string_compare_mem (2048 + i)).
    intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; reflexivity.
Qed.

(** The earlier terminator participates in the comparison. Both signs
    permit magnitude 512 through the public invocation relation. *)
Example strncmp_terminator_magnitudes : forall reverse : bool,
  InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const 3)]
    [WPtr (if reverse then mkPtr 2052 (Ro 2048) else hello_ptr);
     WPtr (if reverse then hello_ptr else mkPtr 2052 (Ro 2048)); WInt 3]
    InterpRuntime.start string_compare_mem tt
    [] (CallReturn [WInt (if reverse then 512 else 2 ^ 32 - 512)])
    InterpRuntime.start string_compare_mem tt.
Proof.
  intros reverse. destruct (string_compare_lengths 3 ltac:(vm_compute; split; congruence)) as (Hl & _ & Hr).
  destruct reverse; apply InterpExternal.strncmp_return.
  all: try solve [split; [left; reflexivity|]; eexists _, _, _; reflexivity].
  - exists 2, 1. split; [exact Hr|]. split; [exact Hl|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Gt. split; [|reflexivity].
    right. exists 1. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
  - exists 1, 2. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Lt. split; [|reflexivity].
    right. exists 1. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
Qed.

(** A wrong sign is rejected by the invocation relation at an admitted
    call; failure of some unrelated premise is not the explanation. *)
Example strncmp_wrong_sign_rejected : forall s' m' w',
  ~ InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const 3)]
    [WPtr hello_ptr; WPtr (mkPtr 2052 (Ro 2048)); WInt 3]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WInt 512]) s' m' w'.
Proof.
  intros s' m' w' Hcall.
  destruct (InterpExternal.strncmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & q & n & bits & Hargs & Hresult & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  destruct (InterpExternal.strncmp_invocation _ _ _ _ _ _ _ _ _ _ _ _
    (strncmp_terminator_magnitudes false))
    as (_ & _ & _ & p & q & n & bits & Hargs & Hgood & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  pose proof (strncmp_result_sign_unique _ _ _ _ _ _ Hresult Hgood) as Hsign.
  discriminate Hsign.
Qed.

(** Both one-past pointers are admitted at zero count and return zero. *)
Example strncmp_zero_one_past :
  InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 0)]
    [WPtr (mkPtr 1030 (Ro 1024)); WPtr (mkPtr 1030 (Ro 1024)); WInt 0]
    InterpRuntime.start hello_mem tt [] (CallReturn [WInt 0]) InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strncmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - exists 0, 0. split; [exact strnlen_zero_one_past|]. split; [exact strnlen_zero_one_past|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq. split; [|reflexivity].
    left. split; [reflexivity|intros i Hi; change (0 <= i < 0) in Hi; lia].
Qed.

(** A positive exact-bound call needs no NUL or following byte. *)
Example strncmp_exact_bound :
  InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 6)]
    [WPtr hello_ptr; WPtr hello_ptr; WInt 6] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt 0]) InterpRuntime.start high_byte_mem tt.
Proof.
  destruct (InterpExternal.strnlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ strnlen_exact_bound)
    as (_ & _ & _ & p & n & k & Hargs & Hlength & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  apply InterpExternal.strncmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - exists 6, 6. split; [exact Hlength|]. split; [exact Hlength|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq.
    split; [left; split; reflexivity|reflexivity].
Qed.

(** Mathematical successor before the minimum cannot wrap at SIZE_MAX. *)
Example strncmp_window_no_wrap :
  strncmp_window (2 ^ 64 - 1) (2 ^ 64 - 1) (2 ^ 64 - 1) = 2 ^ 64 - 1.
Proof. reflexivity. Qed.

(** Independent bounded-string obligations cannot be waived by an
    immediate difference or a missing capability at zero count. *)
Example strncmp_independent_inputs :
  ~ contract_pre (strncmp_contract unit)
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024)); WInt 6] high_byte_mem tt /\
  (forall m p q, ptr_cap p = CNone \/ ptr_cap q = CNone ->
    ~ contract_pre (strncmp_contract unit) [WPtr p; WPtr q; WInt 0] m tt).
Proof.
  split.
  - intros (p & q & n & left & right & Hargs & Hl & Hr). injection Hargs as <- <- <-.
    destruct Hr as (_ & Hk & _ & Ha & _ & Hnul).
    assert (Hlt : right < 6).
    { destruct (Z_lt_dec right 6); [assumption|]. assert (right = 6) by lia.
      subst. discriminate Ha. }
    assert (Hfive : right < 5).
    { destruct (Z_lt_dec right 5); [assumption|]. assert (right = 5) by lia.
      subst. discriminate Ha. }
    specialize (Hnul Hlt). change (m_bytes high_byte_mem (1025 + right) = 0) in Hnul.
    assert (Hinside : (1024 <=? 1025 + right) && (1025 + right <? 1030) = true)
      by (apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    change ((if (1024 <=? 1025 + right) && (1025 + right <? 1030)
      then if 1025 + right =? 1024 then 128 else 255 else m_bytes hello_mem (1025 + right)) = 0) in Hnul.
    rewrite Hinside in Hnul. destruct (1025 + right =? 1024); discriminate.
  - intros m p q Hbad (left & right & n & kl & kr & Hargs & Hl & Hr).
    injection Hargs as <- <- <-.
    destruct Hbad as [H | H];
      [destruct Hl as (_ & _ & (base & reg & [Hcap | Hcap] & _) & _) |
       destruct Hr as (_ & _ & (base & reg & [Hcap | Hcap] & _) & _)];
      rewrite H in Hcap; discriminate.
Qed.

(** ## Unbounded string comparison controls *)

(** The bounded fixtures are also complete terminated strings. *)
Lemma string_compare_terminated :
  terminated_length string_compare_mem hello_ptr 1 /\
  terminated_length string_compare_mem (mkPtr 2048 (Ro 2048)) 1 /\
  terminated_length string_compare_mem (mkPtr 2052 (Ro 2048)) 2.
Proof.
  destruct (string_compare_lengths (2 ^ 64 - 1) ltac:(vm_compute; split; congruence))
    as (Hl & Hr & Hab).
  split; [split; [exact Hl|vm_compute; congruence]|].
  split; split; try assumption; vm_compute; congruence.
Qed.

(** A shared NUL makes the strings equal despite different following bytes. *)
Example strcmp_shared_nul :
  InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr hello_ptr; WPtr (mkPtr 2048 (Ro 2048))] InterpRuntime.start string_compare_mem tt
    [] (CallReturn [WInt 0]) InterpRuntime.start string_compare_mem tt.
Proof.
  apply InterpExternal.strcmp_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct string_compare_terminated as (Hl & Hr & _).
    exists 1, 1. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq. split; [|reflexivity].
    left. split; [reflexivity|].
    change (forall i, 0 <= i < 2 ->
      m_bytes string_compare_mem (1024 + i) = m_bytes string_compare_mem (2048 + i)).
    intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; reflexivity.
Qed.

(** The earlier terminator decides strict-prefix order; neither sign is
    restricted to a unit or byte-difference magnitude. *)
Example strcmp_terminator_magnitudes : forall reverse : bool,
  InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr (if reverse then mkPtr 2052 (Ro 2048) else hello_ptr);
     WPtr (if reverse then hello_ptr else mkPtr 2052 (Ro 2048))]
    InterpRuntime.start string_compare_mem tt
    [] (CallReturn [WInt (if reverse then 512 else 2 ^ 32 - 512)])
    InterpRuntime.start string_compare_mem tt.
Proof.
  intros reverse. destruct string_compare_terminated as (Hl & _ & Hr).
  destruct reverse; apply InterpExternal.strcmp_return.
  all: try solve [split; [left; reflexivity|]; eexists _, _; reflexivity].
  - exists 2, 1. split; [exact Hr|]. split; [exact Hl|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Gt. split; [|reflexivity].
    right. exists 1. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
  - exists 1, 2. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Lt. split; [|reflexivity].
    right. exists 1. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
Qed.

(** Public wrong-sign rejection uses the same admitted strict-prefix call. *)
Example strcmp_wrong_sign_rejected : forall s' m' w',
  ~ InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr hello_ptr; WPtr (mkPtr 2052 (Ro 2048))] InterpRuntime.start string_compare_mem tt
    [] (CallReturn [WInt 512]) s' m' w'.
Proof.
  intros s' m' w' Hcall.
  destruct (InterpExternal.strcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & q & bits & Hargs & Hresult & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  destruct (InterpExternal.strcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _
    (strcmp_terminator_magnitudes false))
    as (_ & _ & _ & p & q & bits & Hargs & Hgood & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  pose proof (strcmp_result_sign_unique _ _ _ _ _ Hresult Hgood) as Hsign.
  discriminate Hsign.
Qed.

(** Unsigned 128 orders above the empty string, not below it as a signed
    char would. The final live NUL is a valid empty input in either slot. *)
Example strcmp_high_empty : forall reverse : bool,
  InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr (if reverse then mkPtr 1029 (Ro 1024) else hello_ptr);
     WPtr (if reverse then hello_ptr else mkPtr 1029 (Ro 1024))]
    InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WInt (if reverse then 2 ^ 32 - 512 else 512)])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros reverse.
  pose proof (strlen_boundary_length 0 5 ltac:(simpl; auto)) as Hl.
  pose proof (strlen_boundary_length 5 0 ltac:(simpl; auto)) as Hr.
  destruct reverse; apply InterpExternal.strcmp_return.
  all: try solve [split; [left; reflexivity|]; eexists _, _; reflexivity].
  - exists 0, 5. split; [exact Hr|]. split; [exact Hl|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Lt. split; [|reflexivity].
    right. exists 0. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. lia.
    + split; [discriminate|reflexivity].
  - exists 5, 0. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Gt. split; [|reflexivity].
    right. exists 0. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. lia.
    + split; [discriminate|reflexivity].
Qed.

(** Identical terminated spans, including empty and interior ones, admit
    zero without requiring separate objects or disjoint input authority. *)
Example strcmp_identical_calls : forall offset count,
  In (offset, count) [(0, 5); (1, 4); (5, 0)] ->
  InterpExternal.invoke (strcmp_contract unit) (CResult (TAtom "compared") W)
    [Arg P (Const 0); Arg P (Const 0)]
    [WPtr (mkPtr (1024 + offset) (Ro 1024)); WPtr (mkPtr (1024 + offset) (Ro 1024))]
    InterpRuntime.start strlen_high_mem tt [] (CallReturn [WInt 0])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros offset count Hcase. apply InterpExternal.strcmp_return.
  - split; [right; exists (TAtom "compared"); reflexivity|]. eexists _, _. reflexivity.
  - pose proof (strlen_boundary_length offset count Hcase) as Hl.
    exists count, count. split; [exact Hl|]. split; [exact Hl|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq.
    split; [left; split; [reflexivity|intros; reflexivity]|reflexivity].
Qed.

(** Overlap is admitted. An earlier 128-versus-255 difference wins over
    the opposite ordering of the final compared 255-versus-NUL pair. *)
Example strcmp_overlap :
  InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024))] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WInt (2 ^ 32 - 512)]) InterpRuntime.start strlen_high_mem tt.
Proof.
  apply InterpExternal.strcmp_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - exists 5, 4. split; [apply (strlen_boundary_length 0 5); simpl; auto|].
    split; [apply (strlen_boundary_length 1 4); simpl; auto|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Lt. split; [|reflexivity].
    right. exists 0. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. lia.
    + split; [discriminate|reflexivity].
Qed.

(** An immediate unequal byte cannot waive the other string's missing
    NUL, in either argument position. Both capabilities are live. *)
Example strcmp_independent_inputs :
  ~ contract_pre (strcmp_contract unit)
    [WPtr hello_ptr; WPtr (mkPtr 2048 (Ro 2048))] high_byte_mem tt /\
  ~ contract_pre (strcmp_contract unit)
    [WPtr (mkPtr 2048 (Ro 2048)); WPtr hello_ptr] high_byte_mem tt.
Proof.
  split; intros (p & q & left & right & Hargs & Hl & Hr); injection Hargs as <- <-;
    apply strlen_missing_nul_rejected.
  - exists hello_ptr, left. auto.
  - exists hello_ptr, right. auto.
Qed.

(** A numeric NUL at one-past is not a readable empty string in either
    argument position, even when the other input is an admitted string. *)
Example strcmp_one_past_rejected : forall reverse : bool,
  ~ contract_pre (strcmp_contract unit)
    [WPtr (if reverse then hello_ptr else mkPtr 1030 (Ro 1024));
     WPtr (if reverse then mkPtr 1030 (Ro 1024) else hello_ptr)] hello_mem tt.
Proof.
  intros reverse. destruct reverse;
    intros (p & q & left & right & Hargs & Hl & Hr); injection Hargs as <- <-;
    apply (proj1 strlen_bad_authority_rejected).
  - exists (mkPtr 1030 (Ro 1024)), right. auto.
  - exists (mkPtr 1030 (Ro 1024)), left. auto.
Qed.

(** No count belongs in the ABI, and size_t is not the int result channel. *)
Example strcmp_wrong_abi_rejected :
  ~ strcmp_abi (CResult (TAtom "compared") L) [Arg P (Const 0); Arg P (Const 1)] /\
  ~ strcmp_abi CVoid [Arg P (Const 0)] /\
  ~ strcmp_abi CVoid [Arg P (Const 0); Arg P (Const 1); Arg L (Const 0)].
Proof.
  split; [intros [[H | (d & H)] _]; discriminate H|].
  split; intros [_ (p & q & H)]; discriminate H.
Qed.

(** ## Unbounded character search controls *)

(** The first l of hello, not the repeated l, retains read-only authority. *)
Lemma strchr_hello_first : strchr_result hello_mem hello_ptr 108 (mkPtr 1026 (Ro 1024)).
Proof.
  exists 5. split; [exact strlen_hello_bridge|]. left. exists 2.
  repeat split; try reflexivity; try lia. intros i Hi.
  assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** The source-only capability permission constructs an actual P return. *)
Example strchr_first_call :
  InterpExternal.invoke (strchr_contract unit) (CResult (TAtom "found") P)
    [Arg P (Const 0); Arg W (Const 108)] [WPtr hello_ptr; WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr (mkPtr 1026 (Ro 1024))])
    InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strchr_return.
  - split; [right; eexists; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exact strchr_hello_first.
Qed.

(** At that admitted call, a later match, null, and correct-address
    capability amplification or loss fail regardless of the endpoint. *)
Example strchr_wrong_pointer_rejected : forall q s' m' w',
  In q [mkPtr 1027 (Ro 1024); mkPtr 0 CNone; mkPtr 1026 (Obj 1024); mkPtr 1026 CNone] ->
  ~ InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 108)] [WPtr hello_ptr; WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.strchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & result & Hargs & Hc & Hresult & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  pose proof (strchr_result_unique _ _ _ _ _ Hresult strchr_hello_first) as Heq.
  destruct Hbad as [<- | [<- | [<- | [<- | []]]]]; discriminate Heq.
Qed.

(** Both 511 and the canonical W representation of -1 select byte 255,
    whose repeated later occurrences do not replace the first match. *)
Example strchr_high_calls : forall c, In c [511; 2 ^ 32 - 1] ->
  InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const c)] [WPtr hello_ptr; WInt c]
    InterpRuntime.start strlen_high_mem tt [] (CallReturn [WPtr (mkPtr 1025 (Ro 1024))])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros c Hcase. apply InterpExternal.strchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct Hcase as [<- | [<- | []]]; vm_compute; split; congruence.
  - exists 5. split; [apply (strlen_boundary_length 0 5); simpl; auto|].
    left. exists 1. split; [lia|]. split.
    + destruct Hcase as [<- | [<- | []]]; reflexivity.
    + split; [|reflexivity]. intros i Hi. assert (i = 0) by lia. subst.
      destruct Hcase as [<- | [<- | []]]; discriminate.
Qed.

(** Searching 0 or 256 returns the final live NUL, including an empty
    input; a nonzero search in that empty string instead returns null. *)
Example strchr_nul_empty_calls : forall offset c,
  In (offset, c) [(0, 0); (0, 256); (5, 0); (5, 256); (5, 108)] ->
  InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const c)]
    [WPtr (mkPtr (1024 + offset) (Ro 1024)); WInt c] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WPtr (if c =? 108 then mkPtr 0 CNone else mkPtr 1029 (Ro 1024))])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros offset c Hcase.
  assert (Hlength : terminated_length strlen_high_mem (mkPtr (1024 + offset) (Ro 1024)) (5 - offset)).
  { apply strlen_boundary_length. destruct Hcase as [H|[H|[H|[H|[H|[]]]]]];
      injection H as <- <-; simpl; auto. }
  apply InterpExternal.strchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct Hcase as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-;
      vm_compute; split; congruence.
  - exists (5 - offset). split; [exact Hlength|].
    destruct Hcase as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-.
    + left. exists 5. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
      intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct H as [-> | [-> | [-> | [-> | ->]]]]; discriminate.
    + left. exists 5. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
      intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct H as [-> | [-> | [-> | [-> | ->]]]]; discriminate.
    + left. exists 0. repeat split; try reflexivity; lia.
    + left. exists 0. repeat split; try reflexivity; lia.
    + right. split; [|reflexivity]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
Qed.

(** A byte after the first NUL is not searched, even within the live
    object; this call is admitted and returns null, not the later z. *)
Example strchr_stops_at_nul :
  InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 122)] [WPtr hello_ptr; WInt 122]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WPtr (mkPtr 0 CNone)])
    InterpRuntime.start string_compare_mem tt.
Proof.
  apply InterpExternal.strchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exists 1. split; [exact (proj1 string_compare_terminated)|]. right. split; [|reflexivity].
    intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** Writable source authority is retained too: it is not universally
    downgraded to read-only authority by a successful search. *)
Example strchr_object_source :
  InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 108)] [WPtr (mkPtr 1024 (Obj 1024)); WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr (mkPtr 1026 (Obj 1024))])
    InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exists 5. split.
    + destruct strlen_hello_bridge as [(Hn & Hk & _ & Ha & Hbytes & Hnul) Hmax].
      split; [|exact Hmax]. split; [exact Hn|]. split; [exact Hk|]. split.
      * exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [left; reflexivity|]. auto.
      * split; [exact Ha|]. split; assumption.
    + left. exists 2. repeat split; try reflexivity; try lia.
      intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** An immediate matching byte cannot excuse a missing in-object NUL. *)
Example strchr_missing_nul_rejected :
  ~ contract_pre (strchr_contract unit) [WPtr hello_ptr; WInt 128] high_byte_mem tt.
Proof.
  intros (p & c & k & Hargs & _ & Hlength). injection Hargs as <- <-.
  apply strlen_missing_nul_rejected. exists hello_ptr, k. auto.
Qed.

(** No search argument rescues one-past, null or freed input authority. *)
Example strchr_bad_authority_rejected : forall c,
  ~ contract_pre (strchr_contract unit) [WPtr (mkPtr 1030 (Ro 1024)); WInt c] hello_mem tt /\
  ~ contract_pre (strchr_contract unit) [WPtr (mkPtr 0 CNone); WInt c] hello_mem tt /\
  ~ contract_pre (strchr_contract unit) [WPtr (mkPtr 1024 (Obj 1024)); WInt c]
    (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone)) tt.
Proof.
  intros c. destruct strlen_bad_authority_rejected as (Hpast & Hnull & Hfreed).
  split; [|split]; intros (p & value & k & Hargs & _ & Hlength); injection Hargs as <- <-.
  - apply Hpast. exists (mkPtr 1030 (Ro 1024)), k. auto.
  - apply Hnull. exists (mkPtr 0 CNone), k. auto.
  - apply Hfreed. exists (mkPtr 1024 (Obj 1024)), k. auto.
Qed.

(** Int words must already be canonical, even for a valid string. *)
Example strchr_noncanonical_rejected : forall c, c < 0 \/ 2 ^ 32 <= c ->
  ~ contract_pre (strchr_contract unit) [WPtr hello_ptr; WInt c] hello_mem tt.
Proof.
  intros c Hbad (p & value & k & Hargs & Hc & _). injection Hargs as <- <-. lia.
Qed.

(** Count-free P/W arguments and a pointer result are distinct ABI
    obligations; identical machine word counts cannot change classes. *)
Example strchr_wrong_abi_rejected :
  ~ strchr_abi (CResult (TAtom "found") L) [Arg P (Const 0); Arg W (Const 0)] /\
  ~ strchr_abi CVoid [Arg P (Const 0); Arg L (Const 0)] /\
  ~ strchr_abi CVoid [Arg P (Const 0)] /\
  ~ strchr_abi CVoid [Arg P (Const 0); Arg W (Const 0); Arg L (Const 0)].
Proof.
  split; [intros [[H | (d & H)] _]; discriminate H|].
  split; [|split]; intros [_ (p & c & H)]; discriminate H.
Qed.

(** ## Last-match character search controls *)

(** The second l in hello is the last match, with the original Ro. *)
Lemma strrchr_hello_last : strrchr_result hello_mem hello_ptr 108 (mkPtr 1027 (Ro 1024)).
Proof.
  exists 5. split; [exact strlen_hello_bridge|]. left. exists 3.
  split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
  intros j Hj. assert (j = 4 \/ j = 5) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** A last-match pointer is returned through the public P channel. *)
Example strrchr_last_call :
  InterpExternal.invoke (strrchr_contract unit) (CResult (TAtom "found") P)
    [Arg P (Const 0); Arg W (Const 108)] [WPtr hello_ptr; WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr (mkPtr 1027 (Ro 1024))])
    InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strrchr_return.
  - split; [right; eexists; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exact strrchr_hello_last.
Qed.

(** The first match, false null and correct-address capability
    amplification/loss fail at the same admitted call. *)
Example strrchr_wrong_pointer_rejected : forall q s' m' w',
  In q [mkPtr 1026 (Ro 1024); mkPtr 0 CNone; mkPtr 1027 (Obj 1024); mkPtr 1027 CNone] ->
  ~ InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 108)] [WPtr hello_ptr; WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.strrchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & result & Hargs & Hc & Hresult & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  pose proof (strrchr_result_unique _ _ _ _ _ Hresult strrchr_hello_last) as Heq.
  destruct Hbad as [<- | [<- | [<- | [<- | []]]]]; discriminate Heq.
Qed.

(** Conversion selects the last 255 at offset four, not its first
    occurrence at offset one, for 511 and canonical negative one. *)
Example strrchr_high_calls : forall c, In c [511; 2 ^ 32 - 1] ->
  InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const c)] [WPtr hello_ptr; WInt c]
    InterpRuntime.start strlen_high_mem tt [] (CallReturn [WPtr (mkPtr 1028 (Ro 1024))])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros c Hcase. apply InterpExternal.strrchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct Hcase as [<- | [<- | []]]; vm_compute; split; congruence.
  - exists 5. split; [apply (strlen_boundary_length 0 5); simpl; auto|].
    left. exists 4. split; [lia|]. split.
    + destruct Hcase as [<- | [<- | []]]; reflexivity.
    + split; [|reflexivity]. intros j Hj. assert (j = 5) by lia. subst.
      destruct Hcase as [<- | [<- | []]]; discriminate.
Qed.

(** Zero and 256 find the final NUL even for an empty input. Searching
    that empty suffix for 255 must not find earlier bytes of its object. *)
Example strrchr_nul_empty_calls : forall offset c,
  In (offset, c) [(0, 0); (0, 256); (5, 0); (5, 256); (5, 511)] ->
  InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const c)]
    [WPtr (mkPtr (1024 + offset) (Ro 1024)); WInt c] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WPtr (if c =? 511 then mkPtr 0 CNone else mkPtr 1029 (Ro 1024))])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros offset c Hcase.
  assert (Hlength : terminated_length strlen_high_mem (mkPtr (1024 + offset) (Ro 1024)) (5 - offset)).
  { apply strlen_boundary_length. destruct Hcase as [H|[H|[H|[H|[H|[]]]]]];
      injection H as <- <-; simpl; auto. }
  apply InterpExternal.strrchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct Hcase as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-;
      vm_compute; split; congruence.
  - exists (5 - offset). split; [exact Hlength|].
    destruct Hcase as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-.
    + left. exists 5. repeat split; try reflexivity; lia.
    + left. exists 5. repeat split; try reflexivity; lia.
    + left. exists 0. repeat split; try reflexivity; lia.
    + left. exists 0. repeat split; try reflexivity; lia.
    + right. split; [|reflexivity]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
Qed.

(** A matching byte after the first NUL is outside the search domain. *)
Example strrchr_stops_at_nul :
  InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 122)] [WPtr hello_ptr; WInt 122]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WPtr (mkPtr 0 CNone)])
    InterpRuntime.start string_compare_mem tt.
Proof.
  apply InterpExternal.strrchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exists 1. split; [exact (proj1 string_compare_terminated)|]. right. split; [|reflexivity].
    intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** A public miss cannot be replaced by an invented nonnull result,
    including the actual matching byte just beyond the logical string. *)
Example strrchr_false_hit_rejected : forall q s' m' w', q <> mkPtr 0 CNone ->
  ~ InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 122)] [WPtr hello_ptr; WInt 122]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.strrchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & result & Hargs & Hc & Hresult & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  destruct (InterpExternal.strrchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ strrchr_stops_at_nul)
    as (_ & _ & _ & p & c & result & Hargs & Hcanonical & Hgood & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  apply Hbad. eapply strrchr_result_unique; eauto.
Qed.

(** Obj source authority is retained rather than stripped or downgraded. *)
Example strrchr_object_source :
  InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 108)] [WPtr (mkPtr 1024 (Obj 1024)); WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr (mkPtr 1027 (Obj 1024))])
    InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strrchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exists 5. split.
    + destruct strlen_hello_bridge as [(Hn & Hk & _ & Ha & Hbytes & Hnul) Hmax].
      split; [|exact Hmax]. split; [exact Hn|]. split; [exact Hk|]. split.
      * exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [left; reflexivity|]. auto.
      * split; [exact Ha|]. split; assumption.
    + left. exists 3. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
      intros j Hj. assert (j = 4 \/ j = 5) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** Full terminated-string admission is the same independent premise
    as strchr's: an immediate match cannot rescue a missing terminator. *)
Example strrchr_missing_nul_rejected :
  ~ contract_pre (strrchr_contract unit) [WPtr hello_ptr; WInt 128] high_byte_mem tt.
Proof. exact strchr_missing_nul_rejected. Qed.

(** One-past, null and freed authority remain independently invalid. *)
Example strrchr_bad_authority_rejected : forall c,
  ~ contract_pre (strrchr_contract unit) [WPtr (mkPtr 1030 (Ro 1024)); WInt c] hello_mem tt /\
  ~ contract_pre (strrchr_contract unit) [WPtr (mkPtr 0 CNone); WInt c] hello_mem tt /\
  ~ contract_pre (strrchr_contract unit) [WPtr (mkPtr 1024 (Obj 1024)); WInt c]
    (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone)) tt.
Proof. exact strchr_bad_authority_rejected. Qed.

(** Canonical int admission is not weakened by the change to last match;
    strchr's independently tested P/W ABI is reused unchanged. *)
Example strrchr_noncanonical_rejected : forall c, c < 0 \/ 2 ^ 32 <= c ->
  ~ contract_pre (strrchr_contract unit) [WPtr hello_ptr; WInt c] hello_mem tt.
Proof. exact strchr_noncanonical_rejected. Qed.

(** ## Byte-fill boundary controls *)

(** An odd-sized writable object, nonuniform raw bytes and three
    stored pointer capabilities; the pointee is a separate object. *)
Definition memset_fixture : mem :=
  mkMem (fun a => a mod 256)
    [mkRegion 1024 1053 Heap Live; mkRegion 2048 2056 Heap Live]
    (fun a => if (a =? 1024) || (a =? 1032) || (a =? 1040) then Obj 2048 else CNone).

(** Independent authority for any in-bounds fixture destination. *)
Lemma memset_fixture_domain : forall offset c n,
  0 <= offset -> 0 <= n -> offset + n <= 29 -> 0 <= c < 2 ^ 32 ->
  memset_domain memset_fixture (mkPtr (1024 + offset) (Obj 1024)) c n.
Proof.
  intros offset c n Hoffset Hn Hend Hc. split; [exact Hc|]. split.
  - change (0 <= n < 18446744073709551616). lia.
  - split.
    + split; [exact Hn|]. exists 1024, (mkRegion 1024 1053 Heap Live).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      change (Some (if (1024 <=? 1024 + offset) && (1024 + offset + n <=? 1053)
        then aligned_res (1024 + offset) 1 else RTrap OutOfBounds) = Some ok).
      assert ((1024 <=? 1024 + offset) = true) as Hlo by (apply Z.leb_le; lia).
      assert ((1024 + offset + n <=? 1053) = true) as Hhi by (apply Z.leb_le; lia).
      rewrite Hlo, Hhi. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
    + right. exists 1024. split; reflexivity.
Qed.

(** Actual calls include partial, crossing and exact-word fills,
    canonical negative int conversion, and an unaligned one-past empty
    fill. The pointer return is the destination, never the hull start. *)
Example memset_boundary_calls : forall offset c n,
  In (offset, c, n) [(7, 511, 1); (7, 511, 2); (8, 256, 8);
    (7, 2 ^ 32 - 1, 2); (29, 511, 0)] ->
  InterpExternal.invoke (memset_contract unit) (CResult (TAtom "filled") P)
    [Arg P (Const 0); Arg W (Const c); Arg L (Const n)]
    [WPtr (mkPtr (1024 + offset) (Obj 1024)); WInt c; WInt n]
    InterpRuntime.start memset_fixture tt []
    (CallReturn [WPtr (mkPtr (1024 + offset) (Obj 1024))]) InterpRuntime.start
    (memset_memory memset_fixture (mkPtr (1024 + offset) (Obj 1024)) c n) tt.
Proof.
  intros offset c n Hcases. apply InterpExternal.memset_admitted.
  - split; [right; eexists; reflexivity|]. eexists _, _, _. reflexivity.
  - apply memset_fixture_domain;
      destruct Hcases as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <-;
      vm_compute; intuition congruence.
Qed.

(** Every public partial or crossing completion has these observable
    cells, independently of the constructed witness: repeated low bytes,
    a cleared preceding slot, and intact byte/capability neighbours. *)
Example memset_partial_observations : forall n trace ending s' m' w', In n [1; 2] ->
  InterpExternal.invoke (memset_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 511); Arg L (Const n)]
    [WPtr (mkPtr 1031 (Obj 1024)); WInt 511; WInt n]
    InterpRuntime.start memset_fixture tt trace ending s' m' w' ->
  ending = CallReturn [WPtr (mkPtr 1031 (Obj 1024))] /\
  m_bytes m' 1030 = 6 /\ m_bytes m' 1031 = 255 /\ m_bytes m' 1033 = 9 /\
  m_aux m' 1024 = CNone /\ m_aux m' 1040 = Obj 2048 /\
  (n = 1 -> m_bytes m' 1032 = 8 /\ m_aux m' 1032 = Obj 2048) /\
  (n = 2 -> m_bytes m' 1032 = 255 /\ m_aux m' 1032 = CNone).
Proof.
  intros n trace ending s' m' w' Hn Hcall.
  destruct (InterpExternal.memset_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & p & c & size & Hargs & Hdomain & (Hframe & Hfill & Hclear) & Hending).
  injection Hargs as <- <- <-. destruct Hframe as (Hregions & Hbytes & Haux).
  split; [exact Hending|]. split.
  - rewrite Hbytes; [reflexivity|]. unfold span_contains. simpl. lia.
  - split.
    + apply Hfill. unfold span_contains. simpl. destruct Hn as [<-|[<-|[]]]; lia.
    + split.
      * rewrite Hbytes; [reflexivity|]. unfold span_contains. simpl.
        destruct Hn as [<-|[<-|[]]]; lia.
      * split.
        -- apply Hclear. destruct Hn as [<-|[<-|[]]]; reflexivity.
        -- split.
           ++ rewrite Haux; [reflexivity|]. destruct Hn as [<-|[<-|[]]]; reflexivity.
           ++ split; intros ->; split.
              ** rewrite Hbytes; [reflexivity|]. unfold span_contains. simpl. lia.
              ** rewrite Haux; reflexivity.
              ** apply Hfill. unfold span_contains. simpl. lia.
              ** apply Hclear. reflexivity.
Qed.

(** A full-word endpoint excludes the next slot. Empty fills preserve
    the actual memory record even at an unaligned one-past address. *)
Example memset_exact_endpoint_and_zero :
  m_aux (memset_memory memset_fixture (mkPtr 1032 (Obj 1024)) 256 8) 1032 = CNone /\
  m_aux (memset_memory memset_fixture (mkPtr 1032 (Obj 1024)) 256 8) 1040 = Obj 2048 /\
  memset_memory memset_fixture (mkPtr 1053 (Obj 1024)) 511 0 = memset_fixture.
Proof. repeat split; reflexivity. Qed.

(** A writable hull alone is insufficient for native-relative slot
    correspondence: this interior call still has an unaligned base. *)
Example memset_unaligned_base_rejected :
  writable_span (mkMem (fun _ => 0) [mkRegion 1025 1053 Heap Live] (fun _ => CNone))
    (memset_root (mkPtr 1033 (Obj 1025)) 1) /\
  ~ contract_pre (memset_contract unit) [WPtr (mkPtr 1033 (Obj 1025)); WInt 0; WInt 1]
    (mkMem (fun _ => 0) [mkRegion 1025 1053 Heap Live] (fun _ => CNone)) tt.
Proof.
  split.
  - split; [vm_compute; congruence|]. exists 1025, (mkRegion 1025 1053 Heap Live).
    repeat split; reflexivity.
  - intros (p & c & n & Hargs & Hc & Hn & Hw & Halign).
    injection Hargs as <- <- <-. destruct Halign as [Hbad | (base & Hcap & Hmod)].
    + discriminate.
    + injection Hcap as <-. discriminate Hmod.
Qed.

(** Ro, null and freed destinations are outside even the conservative
    zero-count domain; positive one-past writes remain out of bounds. *)
Example memset_invalid_destinations : forall p m n,
  In (p, m, n) [(mkPtr 1024 (Ro 1024), memset_fixture, 0);
    (mkPtr 0 CNone, memset_fixture, 0);
    (mkPtr 1024 (Obj 1024),
      mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone), 0);
    (mkPtr 1053 (Obj 1024), memset_fixture, 1)] ->
  ~ contract_pre (memset_contract unit) [WPtr p; WInt 0; WInt n] m tt.
Proof.
  intros p m n Hcases (q & c & size & Hargs & Hc & Hsize & Hw & Halign).
  injection Hargs as <- <- <-.
  destruct Hcases as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-;
    destruct Hw as (_ & base & reg & Hcap & Hr & Hl & Ha); simpl in Hcap.
  - discriminate.
  - discriminate.
  - injection Hcap as <-. simpl in Hr. injection Hr as <-. discriminate.
  - injection Hcap as <-. simpl in Hr. injection Hr as <-. discriminate Ha.
Qed.

(** Canonical scalars and the exact P/W/L-to-P ABI are independent
    obligations, not consequences of the chosen write effect. *)
Example memset_invalid_scalars_and_abi :
  (forall c n, c < 0 \/ 2 ^ 32 <= c \/ n < 0 \/ 2 ^ 64 <= n ->
    ~ contract_pre (memset_contract unit)
      [WPtr (mkPtr 1024 (Obj 1024)); WInt c; WInt n] memset_fixture tt) /\
  ~ memset_abi (CResult (TAtom "bad") L) [Arg P (Const 0); Arg W (Const 0); Arg L (Const 1)] /\
  ~ memset_abi CVoid [Arg P (Const 0); Arg L (Const 0); Arg L (Const 1)] /\
  ~ memset_abi CVoid [Arg P (Const 0); Arg W (Const 0); Arg W (Const 1)] /\
  ~ memset_abi CVoid [Arg P (Const 0); Arg W (Const 0)] /\
  ~ memset_abi CVoid [Arg P (Const 0); Arg W (Const 0); Arg L (Const 1); Arg L (Const 1)].
Proof.
  split.
  - intros c n Hbad (p & v & size & Hargs & Hc & Hn & _).
    injection Hargs as <- <- <-. lia.
  - split; [intros [[H|(d & H)] _]; discriminate H|].
    repeat split; intros [_ (p & c & n & Hargs)]; discriminate Hargs.
Qed.

(** ## Snapshot-copy controls *)

(** Finite patterned bytes and distinct Ro/Obj stored capabilities.
    The odd-sized destination permits an unaligned one-past endpoint. *)
Definition copy_fixture : mem :=
  mkMem (fun a => if (1024 <=? a) && (a <? 1053) then a mod 256 else 0)
    (m_regions memset_fixture)
    (fun a => if a =? 1024 then Ro 2048 else if a =? 1032 then Obj 2048 else CNone).

(** This positive fixture is genuinely ready, so the generic effect
    preservation theorem has a concrete ready-start instance. *)
Example copy_fixture_ready : InterpRuntime.ready InterpRuntime.start copy_fixture.
Proof.
  split; [unfold InterpRuntime.start, InterpRuntime.address_end; lia|]. split.
  - intros b reg Hr. cbn -[Z.eqb] in Hr. destruct (1024 =? b) eqn:Hb.
    + apply Z.eqb_eq in Hb. injection Hr as <-. simpl.
      unfold InterpRuntime.start. repeat split; try discriminate; lia.
    + destruct (2048 =? b) eqn:Hb'; [|discriminate].
      apply Z.eqb_eq in Hb'. injection Hr as <-. simpl.
      unfold InterpRuntime.start. repeat split; try discriminate; lia.
  - intros a Ha. unfold InterpRuntime.start in Ha.
    change ((if (1024 <=? a) && (a <? 1053) then a mod 256 else 0) = 0 /\
      (if a =? 1024 then Ro 2048 else if a =? 1032 then Obj 2048 else CNone) = CNone).
    assert ((a <? 1053) = false) as He by (apply Z.ltb_ge; lia).
    assert ((a =? 1024) = false) as H1 by (apply Z.eqb_neq; lia).
    assert ((a =? 1032) = false) as H2 by (apply Z.eqb_neq; lia).
    rewrite He, H1, H2, andb_false_r. split; reflexivity.
Qed.

(** Input-only fixture authority for byte-disjoint or overlapping
    calls. A read-only source alias never licenses destination writes. *)
Lemma copy_fixture_domain : forall overlap d src n,
  0 <= d -> 0 <= src -> 0 <= n -> d + n <= 29 -> src + n <= 29 ->
  (overlap = true \/ n = 0 \/ d + n <= src \/ src + n <= d) ->
  copy_domain overlap copy_fixture (mkPtr (1024 + d) (Obj 1024))
    (mkPtr (1024 + src) (Ro 1024)) n.
Proof.
  intros overlap d src n Hd Hsrc Hn Hdend Hsend Hsep. split.
  - change (memset_domain memset_fixture (mkPtr (1024 + d) (Obj 1024)) 0 n).
    apply memset_fixture_domain; try assumption. change (0 <= 0 < 4294967296). lia.
  - split.
    + split; [change (0 <= n < 18446744073709551616); lia|]. split.
      * exists 1024, (mkRegion 1024 1053 Heap Live).
        split; [right; reflexivity|]. repeat split; reflexivity.
      * split.
        -- change (Some (if (1024 <=? 1024 + src) && (1024 + src + n <=? 1053)
             then aligned_res (1024 + src) 1 else RTrap OutOfBounds) = Some ok).
           assert ((1024 <=? 1024 + src) = true) as Hlo by (apply Z.leb_le; lia).
           assert ((1024 + src + n <=? 1053) = true) as Hhi by (apply Z.leb_le; lia).
           rewrite Hlo, Hhi. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
        -- intros i Hi.
           change (0 <= (if (1024 <=? 1024 + src + i) && (1024 + src + i <? 1053)
             then (1024 + src + i) mod 256 else 0) < 256).
           destruct ((1024 <=? 1024 + src + i) && (1024 + src + i <? 1053));
             [apply Z.mod_pos_bound|]; lia.
    + split.
      * right. exists 1024. split; [right; reflexivity|reflexivity].
      * change (overlap = true \/ n = 0 \/ 1024 + d + n <= 1024 + src \/
          1024 + src + n <= 1024 + d).
        destruct Hsep as [H|[H|[H|H]]]; [left|right; left|right; right; left|right; right; right];
          try assumption; lia.
Qed.

(** Actual public calls cover full and partial words, both overlap
    directions, self moves, out-of-phase moves, adjacent memcpy ranges,
    CNone source metadata, and an exact one-past mempcpy return. *)
Example copy_boundary_calls : forall overlap end_return d src n,
  In (overlap, end_return, d, src, n)
    [(false, false, 16, 0, 8); (false, true, 21, 0, 8);
     (true, false, 8, 0, 16); (true, false, 0, 8, 16);
     (false, false, 1, 2, 1); (true, false, 1, 1, 1);
     (true, false, 0, 0, 8); (true, false, 9, 1, 16);
     (true, false, 0, 1, 16); (false, false, 0, 16, 8); (false, true, 29, 29, 0)] ->
  InterpExternal.invoke (copy_contract overlap end_return unit) (CResult (TAtom "copied") P)
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const n)]
    [WPtr (mkPtr (1024 + d) (Obj 1024)); WPtr (mkPtr (1024 + src) (Ro 1024)); WInt n]
    InterpRuntime.start copy_fixture tt []
    (CallReturn [WPtr (copy_return end_return (mkPtr (1024 + d) (Obj 1024)) n)])
    InterpRuntime.start (copy_memory copy_fixture (mkPtr (1024 + d) (Obj 1024))
      (mkPtr (1024 + src) (Ro 1024)) n) tt.
Proof.
  intros overlap end_return d src n Hcases. apply InterpExternal.copy_admitted.
  - split; [right; eexists; reflexivity|]. eexists _, _, _. reflexivity.
  - apply copy_fixture_domain; destruct Hcases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]];
      injection H as <- <- <- <- <-; vm_compute; intuition congruence.
Qed.

(** Hand-derived cells distinguish original snapshots, exact Ro/Obj
    retention, smidgen and phase clearing, self-copy effects, empty
    copies and neighbours. They constrain every public completion. *)
Example copy_completion_cells : forall d src n a byte capability trace ending s' m' w',
  In (d, src, n, a, byte, capability)
    [(1040, 1024, 8, 1040, 0, Ro 2048);
     (1032, 1024, 16, 1040, 8, Obj 2048);
     (1024, 1032, 16, 1024, 8, Obj 2048);
     (1024, 1032, 16, 1032, 16, CNone);
     (1033, 1025, 16, 1032, 8, CNone);
     (1033, 1025, 16, 1040, 8, Obj 2048);
     (1024, 1025, 16, 1024, 1, CNone);
     (1024, 1040, 8, 1024, 16, CNone);
     (1025, 1025, 1, 1024, 0, CNone);
     (1024, 1024, 8, 1024, 0, Ro 2048);
     (1025, 1026, 1, 1024, 0, CNone);
     (1053, 1053, 0, 1024, 0, Ro 2048)] ->
  InterpExternal.invoke (memmove_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const n)]
    [WPtr (mkPtr d (Obj 1024)); WPtr (mkPtr src (Ro 1024)); WInt n]
    InterpRuntime.start copy_fixture tt trace ending s' m' w' ->
  m_bytes m' a = byte /\ m_aux m' a = capability.
Proof.
  intros d src n a byte capability trace ending s' m' w' Hcases Hcall.
  destruct (InterpExternal.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & dst & source & count & Hargs & Hdomain & Hresult & Hend).
  injection Hargs as <- <- <-.
  destruct (copy_result_cells _ _ _ _ _ a Hresult) as [Hb Ha]. rewrite Hb, Ha.
  destruct Hcases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]];
    injection H as <- <- <- <- <- <-; split; reflexivity.
Qed.

(** Positive overlapping bytes cannot be used under memcpy merely
    because the shared snapshot relation also supports memmove. *)
Example memcpy_overlap_rejected :
  ~ contract_pre (memcpy_contract unit)
    [WPtr (mkPtr 1032 (Obj 1024)); WPtr (mkPtr 1024 (Ro 1024)); WInt 16] copy_fixture tt.
Proof.
  intros (d & src & n & Hargs & _ & _ & _ & Hsep).
  injection Hargs as <- <- <-. simpl in Hsep. destruct Hsep as [H|[H|[H|H]]]; try discriminate; lia.
Qed.

(** The end-return expectation is a hand-written one-past pointer,
    not computed from the API's own return helper. *)
Example mempcpy_exact_return : forall trace ending s' m' w',
  InterpExternal.invoke (mempcpy_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 8)]
    [WPtr (mkPtr 1045 (Obj 1024)); WPtr (mkPtr 1024 (Ro 1024)); WInt 8]
    InterpRuntime.start copy_fixture tt trace ending s' m' w' ->
  ending = CallReturn [WPtr (mkPtr 1053 (Obj 1024))].
Proof.
  intros trace ending s' m' w' Hcall.
  destruct (InterpExternal.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & d & src & n & Hargs & Hdomain & Hresult & Hend).
  injection Hargs as <- <- <-. exact Hend.
Qed.

(** Destination writes require Obj independently of readable source
    authority. Null sources and incorrect P/P/L ABI shapes fail too. *)
Example copy_bad_domains_and_abi :
  (forall n, ~ contract_pre (memmove_contract unit)
    [WPtr (mkPtr 1024 (Ro 1024)); WPtr (mkPtr 1024 (Ro 1024)); WInt n] copy_fixture tt) /\
  (forall n, ~ contract_pre (memmove_contract unit)
    [WPtr (mkPtr 1024 (Obj 1024)); WPtr (mkPtr 0 CNone); WInt n] copy_fixture tt) /\
  ~ copy_abi (CResult (TAtom "bad") L) [Arg P (Const 0); Arg P (Const 0); Arg L (Const 8)] /\
  ~ copy_abi CVoid [Arg P (Const 0); Arg W (Const 0); Arg L (Const 8)] /\
  ~ copy_abi CVoid [Arg P (Const 0); Arg P (Const 0); Arg W (Const 8)] /\
  ~ copy_abi CVoid [Arg P (Const 0); Arg P (Const 0)] /\
  ~ copy_abi CVoid [Arg P (Const 0); Arg P (Const 0); Arg L (Const 8); Arg L (Const 8)].
Proof.
  split.
  - intros n (d & src & count & Hargs & (_ & _ & Hw & _) & _).
    injection Hargs as <- <- <-. destruct Hw as (_ & base & reg & Hcap & _). discriminate Hcap.
  - split.
    + intros n (d & src & count & Hargs & _ & (_ & (base & reg & Hcap & _) & _) & _).
      injection Hargs as <- <- <-. destruct Hcap as [H|H]; discriminate.
    + split; [intros [[H|(d & H)] _]; discriminate H|].
      repeat split; intros [_ (d & src & n & Hargs)]; discriminate Hargs.
Qed.

(** ## Fresh allocation controls *)

(** Empty and nonmultiple sizes are actual successful calls, not just
    satisfiable postconditions. The latter has 32 bytes of capacity. *)
Example malloc_boundary_calls : forall n, n = 0 \/ n = 17 ->
  InterpExternal.invoke (malloc_contract unit) (CResult (TAtom "buffer") P)
    [Arg L (Const n)] [WInt n] InterpRuntime.start hello_mem tt []
    (CallReturn [WPtr (mkPtr (2 ^ 32) (Obj (2 ^ 32)))])
    (2 ^ 32 + req_extent (heap_req 16 n) + 16)
    (allocated hello_mem (heap_req 16 n) (2 ^ 32)) tt.
Proof.
  intros n [-> | ->]; apply InterpExternal.malloc_return.
  all: try solve [split; [right; eexists; reflexivity|eexists; reflexivity]].
  all: try solve [apply hello_ready; unfold InterpRuntime.start, InterpRuntime.address_end; lia].
  all: try solve [vm_compute; intuition congruence].
Qed.

(** Refusal at the address-space end is OOM, including for a legal
    rounded request. Oversize is separately TooBig, not NULL/panic. *)
Example malloc_resource_calls :
  InterpExternal.invoke (malloc_contract unit) CVoid [Arg L (Const 17)] [WInt 17]
    InterpRuntime.address_end hello_mem tt [] (CallResource OutOfMemory)
    InterpRuntime.address_end hello_mem tt /\
  InterpExternal.invoke (malloc_contract unit) CVoid [Arg L (Const (2 ^ 48))] [WInt (2 ^ 48)]
    InterpRuntime.start hello_mem tt [] (CallResource TooBig) InterpRuntime.start hello_mem tt.
Proof.
  split; apply InterpExternal.malloc_refused.
  all: try solve [split; [left; reflexivity|eexists; reflexivity]].
  all: try solve [vm_compute; intuition congruence].
  - eapply InterpExternal.failure_oom with (align := 16) (size := 17).
    + exists 17. auto.
    + unfold max_allocation_size; lia.
    + reflexivity.
  - eapply InterpExternal.failure_big with (align := 16) (size := 2 ^ 48).
    + exists (2 ^ 48). auto.
    + unfold max_allocation_size; lia.
Qed.

(** Every successful public call returns positive, fresh aligned Obj
    authority and frames both old cell maps. A constant NULL answer or
    changing an old pointer's capability cannot satisfy this control. *)
Example malloc_success_frame : forall n trace p s' m' w',
  InterpExternal.invoke (malloc_contract unit) CVoid [Arg L (Const n)] [WInt n]
    InterpRuntime.start hello_mem tt trace (CallReturn [WPtr p]) s' m' w' ->
  0 < ptr_addr p /\ ptr_addr p mod 16 = 0 /\ ptr_cap p = Obj (ptr_addr p) /\
  object_region (ptr_addr p) (m_regions hello_mem) = None /\
  (forall a, m_bytes m' a = m_bytes hello_mem a /\ m_aux m' a = m_aux hello_mem a).
Proof.
  intros n trace p s' m' w' Hcall.
  destruct (InterpExternal.malloc_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & size & Hargs & _ & [(base & Hr & Hend)|(why & born & Hend & _)]).
  - injection Hargs as <-. injection Hend as Hp. subst p.
    destruct (malloc_old_cells _ _ _ _ Hr) as [Hcells _].
    destruct Hr as (_ & (Hpos & Halign & _ & Hnew & _) & _).
    simpl in Halign. simpl. auto.
  - discriminate Hend.
Qed.

(** Reject noncanonical size_t and wrong ABI classes independently of
    allocation availability. A huge canonical request remains admitted. *)
Example malloc_inputs :
  ~ contract_pre (malloc_contract unit) [WInt (-1)] hello_mem tt /\
  ~ contract_pre (malloc_contract unit) [WInt (2 ^ 64)] hello_mem tt /\
  contract_pre (malloc_contract unit) [WInt (2 ^ 64 - 1)] hello_mem tt /\
  ~ malloc_abi CVoid [Arg W (Const 1)] /\
  ~ malloc_abi (CResult (TAtom "wrong") L) [Arg L (Const 1)].
Proof.
  split; [intros (n & Hargs & Hn); injection Hargs as <-; lia|].
  split; [intros (n & Hargs & Hn); injection Hargs as <-; lia|].
  split; [exists (2 ^ 64 - 1); split; [reflexivity|lia]|].
  split; [intros (_ & n & Hargs); discriminate Hargs|].
  intros ([H|(d & H)] & _); discriminate H.
Qed.

(** ## String duplication controls *)

(** Sixteen nonzero bytes followed by NUL, with distinct stored
    capabilities beneath the first two words. Finite unused bytes are
    zero, so the fixture instantiates readiness. *)
Definition strdup_fixture : mem :=
  mkMem (fun a => if (1024 <=? a) && (a <? 1040) then 65 else 0)
    (m_regions copy_fixture) (fun a => if a =? 1040 then Ro 2048 else m_aux copy_fixture a).

Example strdup_fixture_ready : InterpRuntime.ready InterpRuntime.start strdup_fixture.
Proof.
  destruct copy_fixture_ready as (Hs & Hr & Hu). split; [exact Hs|]. split; [exact Hr|].
  intros a Ha. destruct (Hu a Ha) as [_ Haux]. split.
  - change ((if (1024 <=? a) && (a <? 1040) then 65 else 0) = 0).
    assert ((a <? 1040) = false) as E by (apply Z.ltb_ge; unfold InterpRuntime.start in Ha; lia).
    rewrite E, andb_false_r. reflexivity.
  - change ((if a =? 1040 then Ro 2048 else m_aux copy_fixture a) = CNone).
    assert ((a =? 1040) = false) as E by (apply Z.eqb_neq; unfold InterpRuntime.start in Ha; lia).
    rewrite E. exact Haux.
Qed.

(** Interior starts, a partial-word NUL and empty strings use one contract. *)
Lemma strdup_fixture_domain : forall off, 0 <= off <= 16 ->
  strdup_domain strdup_fixture (mkPtr (1024 + off) (Ro 1024)) (16 - off).
Proof.
  intros off Hoff. split; [|exists 1024; split; [right; reflexivity|reflexivity]].
  split; [|lia]. split; [lia|]. split; [lia|]. split.
  - exists 1024, (mkRegion 1024 1053 Heap Live). split; [right; reflexivity|]. auto.
  - split.
    + assert ((16 - off <? 2 ^ 64 - 1) = true) as Hlt by (apply Z.ltb_lt; lia).
      rewrite Hlt. change (access_res strdup_fixture (1024 + off) (Ro 1024) (16 - off + 1) Read 1 = Some ok).
      unfold access_res, cap_access_res. cbn -[Z.add Z.sub Z.leb Z.modulo].
      assert ((1024 <=? 1024 + off) && (1024 + off + (16 - off + 1) <=? 1053) = true) as E
        by (apply andb_true_iff; split; [apply Z.leb_le|apply Z.leb_le]; lia).
      rewrite E. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
    + split.
      * intros i Hi. change (0 < (if (1024 <=? 1024 + off + i) && (1024 + off + i <? 1040) then 65 else 0) < 256).
        assert ((1024 <=? 1024 + off + i) && (1024 + off + i <? 1040) = true) as E
          by (apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        rewrite E. lia.
      * intros _. change (m_bytes strdup_fixture (1024 + off + (16 - off)) = 0).
        replace (1024 + off + (16 - off)) with 1040 by lia. reflexivity.
Qed.

(** Actual successful calls of lengths 16, 15 and zero share the same
    unindexed registry entry, with an exact NUL-inclusive allocation. *)
Example strdup_different_lengths : forall off, off = 0 \/ off = 1 \/ off = 16 ->
  InterpExternal.invoke (strdup_contract unit) CVoid [Arg P (Const 0)]
    [WPtr (mkPtr (1024 + off) (Ro 1024))] InterpRuntime.start strdup_fixture tt []
    (CallReturn [WPtr (mkPtr (2 ^ 32) (Obj (2 ^ 32)))])
    (2 ^ 32 + req_extent (heap_req 16 (17 - off)) + 16)
    (copy_memory (allocated strdup_fixture (heap_req 16 (17 - off)) (2 ^ 32))
      (mkPtr (2 ^ 32) (Obj (2 ^ 32))) (mkPtr (1024 + off) (Ro 1024)) (17 - off)) tt.
Proof.
  intros off Hcases. replace (17 - off) with (16 - off + 1) by lia.
  eapply InterpExternal.strdup_return with (k := 16 - off).
  - split; [left; reflexivity|eexists; reflexivity].
  - apply strdup_fixture_domain. destruct Hcases as [-> | [-> | ->]]; lia.
  - destruct Hcases as [-> | [-> | ->]]; unfold max_allocation_size; lia.
  - exact strdup_fixture_ready.
  - destruct Hcases as [-> | [-> | ->]]; reflexivity.
  - apply copy_memory_result.
Qed.

(** Hand-derived cells constrain every public completion: exact
    capabilities for complete slots, phase clearing, final NUL and
    zero allocation padding. The source's own cells are unchanged. *)
Example strdup_completed_cells : forall off offset byte capability trace s' m' w',
  In (off, offset, byte, capability)
    [(0, 0, 65, Ro 2048); (0, 8, 65, Obj 2048); (0, 16, 0, CNone);
     (0, 31, 0, CNone); (1, 0, 65, CNone); (1, 15, 0, CNone); (16, 0, 0, CNone)] ->
  InterpExternal.invoke (strdup_contract unit) CVoid [Arg P (Const 0)]
    [WPtr (mkPtr (1024 + off) (Ro 1024))] InterpRuntime.start strdup_fixture tt trace
    (CallReturn [WPtr (mkPtr (2 ^ 32) (Obj (2 ^ 32)))]) s' m' w' ->
  m_bytes m' (2 ^ 32 + offset) = byte /\ m_aux m' (2 ^ 32 + offset) = capability /\
  m_bytes m' 1024 = 65 /\ m_aux m' 1024 = Ro 2048.
Proof.
  intros off offset byte capability trace s' m' w' Hcases Hcall.
  destruct (InterpExternal.strdup_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & p & k & Hargs & Hd & [(b & Hr & Hend)|(why & born & Hend & _)]); [|discriminate Hend].
  injection Hargs as <-. injection Hend as Hb. subst b.
  assert (Hoff : 0 <= off <= 16).
  { destruct Hcases as [C|[C|[C|[C|[C|[C|[C|[]]]]]]]]; injection C as <- <- <- <-; lia. }
  assert (Hk : k = 16 - off).
  { eapply terminated_length_unique; [exact (proj1 Hd)|exact (proj1 (strdup_fixture_domain off Hoff))]. }
  subst k. destruct Hr as [Hmalloc Hcopy].
  pose proof (strdup_prefix_old strdup_fixture (mkPtr (1024 + off) (Ro 1024)) (16 - off + 1)
    [2 ^ 32] m' ltac:(lia) ltac:(right; exists (2 ^ 32); split; [reflexivity|]; split; [exact Hmalloc|exact (proj1 Hcopy)]))
    as [_ Hold].
  destruct (Hold 1024 ltac:(exists 1024, (mkRegion 1024 1053 Heap Live); split; [reflexivity|simpl; lia])) as [Hsb Hsa].
  destruct (copy_result_cells _ _ _ _ _ (2 ^ 32 + offset) Hcopy) as [Hbytes Haux].
  rewrite Hbytes, Haux, Hsb, Hsa.
  destruct Hcases as [C|[C|[C|[C|[C|[C|[C|[]]]]]]]]; injection C as <- <- <- <-.
  all: repeat split; reflexivity.
Qed.

(** A fixed registry computes exact NUL-inclusive sources and request
    sizes, rather than the remainder of the source allocation. *)
Example strdup_exact_sources : forall off, 0 <= off <= 16 ->
  contract_sources (strdup_contract unit) [WPtr (mkPtr (1024 + off) (Ro 1024))] strdup_fixture tt =
    [mkSpan (mkPtr (1024 + off) (Ro 1024)) (17 - off)] /\
  contract_requests (strdup_contract unit) [WPtr (mkPtr (1024 + off) (Ro 1024))] strdup_fixture tt 16 (17 - off).
Proof.
  intros off Hoff. pose proof (terminated_string_length _ _ _ (proj1 (strdup_fixture_domain off Hoff))) as Hlen.
  split.
  - change ([mkSpan (mkPtr (1024 + off) (Ro 1024)) (string_length strdup_fixture (mkPtr (1024 + off) (Ro 1024)) + 1)] =
      [mkSpan (mkPtr (1024 + off) (Ro 1024)) (17 - off)]).
    rewrite Hlen. f_equal. f_equal. lia.
  - exists (mkPtr (1024 + off) (Ro 1024)). split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. lia.
Qed.

(** High bytes precede an early NUL; later bytes and another NUL do
    not enlarge the source span or allocation request. *)
Definition strdup_early : mem := store_bytes strlen_high_mem 1026 1 0.

Example strdup_early_span :
  contract_sources (strdup_contract unit) [WPtr hello_ptr] strdup_early tt = [mkSpan hello_ptr 3] /\
  contract_requests (strdup_contract unit) [WPtr hello_ptr] strdup_early tt 16 3 /\
  ~ contract_requests (strdup_contract unit) [WPtr hello_ptr] strdup_early tt 16 6.
Proof.
  split; [reflexivity|]. split; [exists hello_ptr; repeat split; reflexivity|].
  intros (p & Hargs & _ & Hsize). injection Hargs as <-. discriminate Hsize.
Qed.

(** Numeric exhaustion never grants string admission. Nor do null,
    one-past or expired authority become admitted empty strings. *)
Example strdup_bad_authority :
  ~ contract_pre (strdup_contract unit) [WPtr hello_ptr] high_byte_mem tt /\
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 1030 (Ro 1024))] hello_mem tt /\
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 0 CNone)] hello_mem tt /\
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 1024 (Obj 1024))]
    (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone)) tt.
Proof.
  destruct strlen_bad_authority_rejected as (Hpast & Hnull & Hfreed).
  split; [|split; [|split]]; intros (p & k & Hargs & Hlength & _).
  - apply strlen_missing_nul_rejected. exists p, k. auto.
  - apply Hpast. exists p, k. auto.
  - apply Hnull. exists p, k. auto.
  - apply Hfreed. exists p, k. auto.
Qed.

(** Refusal is constructible without a success assumption. *)
Example strdup_resource_call :
  InterpExternal.invoke (strdup_contract unit) CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.address_end hello_mem tt [] (CallResource OutOfMemory)
    InterpRuntime.address_end hello_mem tt.
Proof.
  eapply InterpExternal.strdup_refused with (k := 5).
  - split; [left; reflexivity|eexists; reflexivity].
  - split; [exact strlen_hello_bridge|]. exists 1024. split; [right; reflexivity|reflexivity].
  - eapply InterpExternal.failure_oom with (align := 16) (size := 6).
    + exists hello_ptr. repeat split; reflexivity.
    + unfold max_allocation_size; lia.
    + reflexivity.
Qed.

(** The same numeric address with another identity grants no string
    read. Aligned object bases are a separate conservative obligation;
    matching ABI width cannot replace a P argument with L. *)
Example strdup_identity_alignment_and_abi :
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 1024 (Ro 2048))] hello_mem tt /\
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 1025 (Ro 1025))]
    (mkMem (fun _ => 0) [mkRegion 1025 1030 Heap Live] (fun _ => CNone)) tt /\
  ~ strdup_abi CVoid [Arg L (Const 0)].
Proof.
  split.
  - intros (p & k & Hargs & [(Hn & Hk & _ & Ha & _) Hmax] & _). injection Hargs as <-.
    discriminate Ha.
  - split.
    + intros (p & k & Hargs & _ & b & [Hcap|Hcap] & Halign); injection Hargs as <-.
      * discriminate Hcap.
      * injection Hcap as <-. discriminate Halign.
    + intros (_ & p & Hargs). discriminate Hargs.
Qed.

(** ## Scalar string-copy controls *)

(** These calls use the ready duplication fixture: distinct source
    lengths in one registry, adjacent ranges in one object, unaligned
    operands, and a destination whose final byte receives the NUL. *)
Lemma string_copy_fixture_domain : forall d off,
  0 <= off <= 16 -> 0 <= d -> d + (17 - off) <= 29 ->
  (d + (17 - off) <= off \/ 17 <= d) ->
  string_copy_domain strdup_fixture (mkPtr (1024 + d) (Obj 1024))
    (mkPtr (1024 + off) (Ro 1024)) (16 - off).
Proof.
  intros d off Hoff Hd Hend Hsep. split.
  - exact (proj1 (strdup_fixture_domain off Hoff)).
  - split.
    + change (writable_span memset_fixture (mkSpan (mkPtr (1024 + d) (Obj 1024)) (16 - off + 1))).
      pose proof (memset_fixture_domain d 0 (16 - off + 1) Hd ltac:(lia) ltac:(lia) ltac:(lia))
        as (_ & _ & Hw & _). exact Hw.
    + change (1024 + d + (16 - off + 1) <= 1024 + off \/
        1024 + off + (16 - off + 1) <= 1024 + d).
      destruct Hsep; [left|right]; lia.
Qed.

Example string_copy_boundary_calls : forall end_return d off,
  In (d, off) [(0, 9); (1, 15); (8, 16); (21, 9)] ->
  InterpExternal.invoke (string_copy_contract end_return unit) CVoid
    [Arg P (Const 0); Arg P (Const 0)]
    [WPtr (mkPtr (1024 + d) (Obj 1024)); WPtr (mkPtr (1024 + off) (Ro 1024))]
    InterpRuntime.start strdup_fixture tt []
    (CallReturn [WPtr (copy_return end_return (mkPtr (1024 + d) (Obj 1024)) (16 - off))])
    InterpRuntime.start (string_copy_memory strdup_fixture (mkPtr (1024 + d) (Obj 1024))
      (mkPtr (1024 + off) (Ro 1024)) (16 - off + 1)) tt.
Proof.
  intros end_return d off Hcases. apply InterpExternal.string_copy_admitted.
  - split; [left; reflexivity|do 2 eexists; reflexivity].
  - apply string_copy_fixture_domain; destruct Hcases as [H|[H|[H|[H|[]]]]];
      injection H as <- <-; lia.
Qed.

(** Every completion, not just the witness: unchanged old destination
    Ro/Obj cells distinguish scalar stores from memset and memcpy.
    Source bytes, neighbours, the NUL and the exact stpcpy endpoint
    are independently fixed by this table. *)
Example string_copy_completion_cells : forall end_return d off a byte capability endpoint trace ending s' m' w',
  In (d, off, a, byte, capability, endpoint)
    [(1024, 9, 1024, 65, Ro 2048, 1031);
     (1024, 9, 1031, 0, CNone, 1031);
     (1024, 9, 1032, 65, Obj 2048, 1031);
     (1025, 15, 1024, 65, Ro 2048, 1026);
     (1025, 15, 1026, 0, CNone, 1026);
     (1025, 15, 1039, 65, CNone, 1026);
     (1032, 16, 1032, 0, Obj 2048, 1032);
     (1045, 9, 1040, 0, Ro 2048, 1052);
     (1045, 9, 1052, 0, CNone, 1052)] ->
  InterpExternal.invoke (string_copy_contract end_return unit) CVoid
    [Arg P (Const 0); Arg P (Const 0)]
    [WPtr (mkPtr d (Obj 1024)); WPtr (mkPtr (1024 + off) (Ro 1024))]
    InterpRuntime.start strdup_fixture tt trace ending s' m' w' ->
  m_bytes m' a = byte /\ m_aux m' a = capability /\
    ending = CallReturn [WPtr (if end_return then mkPtr endpoint (Obj 1024) else mkPtr d (Obj 1024))].
Proof.
  intros end_return d off a byte capability endpoint trace ending s' m' w' Hcases Hcall.
  destruct (InterpExternal.string_copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & dst & src & k & Hargs & Hd & Hresult & Hend).
  injection Hargs as <- <-.
  assert (Hoff : 0 <= off <= 16).
  { destruct Hcases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <- <- <- <-; lia. }
  assert (Hk : k = 16 - off).
  { eapply terminated_length_unique; [exact (proj1 Hd)|exact (proj1 (strdup_fixture_domain off Hoff))]. }
  subst k. destruct (string_copy_cells _ _ _ _ _ a Hresult) as [Hb Ha]. rewrite Hb, Ha, Hend.
  destruct Hcases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <- <- <- <-;
    destruct end_return; vm_compute; repeat split; reflexivity.
Qed.

(** Without auxiliary writes, neither object base needs alignment.
    A readable source is not a writable destination, even at equal bits. *)
Example string_copy_unaligned_bases :
  string_copy_domain
    (mkMem (fun _ => 0) [mkRegion 1025 1030 Heap Live; mkRegion 2049 2052 Heap Live] (fun _ => CNone))
    (mkPtr 2049 (Obj 2049)) (mkPtr 1025 (Ro 1025)) 0.
Proof.
  split.
  - split; [|lia]. split; [lia|]. split; [lia|]. split.
    + exists 1025, (mkRegion 1025 1030 Heap Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. split; [intros i Hi; lia|intros; reflexivity].
  - split.
    + split; [change (0 <= 1); lia|].
      exists 2049, (mkRegion 2049 2052 Heap Live). repeat split; reflexivity.
    + right. simpl. lia.
Qed.

Example string_copy_bad_destination_and_abi :
  ~ contract_pre (strcpy_contract unit)
    [WPtr (mkPtr 1024 (Ro 1024)); WPtr (mkPtr 1033 (Ro 1024))] strdup_fixture tt /\
  ~ contract_pre (stpcpy_contract unit)
    [WPtr (mkPtr 1024 (Obj 1024)); WPtr (mkPtr 1024 (Ro 1024))] strdup_fixture tt /\
  ~ string_copy_abi CVoid [Arg P (Const 0); Arg L (Const 0)].
Proof.
  split.
  - intros (d & src & k & Hargs & _ & (_ & b & reg & Hcap & _) & _).
    injection Hargs as <- <-. discriminate Hcap.
  - split.
    + intros (d & src & k & Hargs & Hlength & _ & Hsep). injection Hargs as <- <-.
      pose proof (terminated_length_unique _ _ _ _ Hlength
        (proj1 (strdup_fixture_domain 0 ltac:(lia)))) as Hk.
      change (k = 16) in Hk. subst k.
      change (1041 <= 1024 \/ 1041 <= 1024) in Hsep. destruct Hsep; lia.
    + intros (_ & d & src & Hargs). discriminate Hargs.
Qed.
