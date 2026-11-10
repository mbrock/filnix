(** Trusted getopt_long boundary. Admission describes memory independently
    of parsing success: arbitrary NUL-terminated argument contents are
    allowed. The result relation deliberately abstracts scanning order,
    abbreviations and diagnostics, not capability provenance. It is a
    safety contract, not a functional specification of GNU getopt.

    The client supplies a projection from its ONE libc world, initialized
    parser representation, in-progress representation and a frame relation
    preserving locale and authoritative shutdown/stdout state. Private
    roots include diagnostic stderr state when needed; they must
    not include caller-owned storage. Native adequacy and safepoint
    coverage remain trusted obligations, not new runtime axioms. *)

From Stdlib Require Import String ZArith List Bool Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Identity ExternalCalls Startup ExternalMachine.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** A selected x86-64 option record is 32 bytes: name at 0,
    has_arg at 8, flag at 16 and val at 24. Padding is not interpreted. *)
Record long_option : Type := mkLongOption {
  option_name : ptr;
  option_text : list Z;
  option_argument : Z;
  option_flag : ptr;
  option_value : Z
}.

(** Logical witnesses for one call family. Argument pointers include
    their exact capabilities; subsequent calls may permute only the tail.
    No bound on string contents is imposed beyond C termination. *)
Record getopt_input : Type := mkGetoptInput {
  getopt_argc : Z;
  getopt_argv : ptr;
  getopt_arguments : list (ptr * list Z);
  getopt_optstring : ptr;
  getopt_short_options : list Z;
  getopt_longopts : ptr;
  getopt_options : list long_option;
  getopt_longindex : ptr
}.

(** Physical cells are references supplied by startup/linking. The four
    values alone do NOT establish initialization of glibc's private parser.
    Reads, writes and release ownership are separate authorities. *)
Record getopt_world : Type := mkGetoptWorld {
  getopt_optarg_cell : ptr;
  getopt_optind_cell : ptr;
  getopt_opterr_cell : ptr;
  getopt_optopt_cell : ptr;
  getopt_errno_cell : ptr;
  getopt_optarg : ptr;
  getopt_optind : Z;
  getopt_opterr : Z;
  getopt_optopt : Z;
  getopt_errno : Z;
  getopt_reads : list span;
  getopt_roots : list span;
  getopt_owned : list Z
}.

(** Canonical signed C int, stored/returned as its unsigned W bits. *)
Definition getopt_int (z : Z) : Prop := -(2 ^ 31) <= z < 2 ^ 31.

(** Writable aligned int cell with an independently specified value. *)
Definition getopt_int_cell m p z : Prop :=
  getopt_int z /\ writable_span m (mkSpan p 4) /\
  access_res m (ptr_addr p) (ptr_cap p) 4 Read 4 = Some ok /\
  access_res m (ptr_addr p) (ptr_cap p) 4 Write 4 = Some ok /\
  load_bytes m (ptr_addr p) 4 = z mod 2 ^ 32.

(** Optional out-int: null is absence, not a writable null span. *)
Definition getopt_optional_int m p : Prop :=
  ptr_addr p = 0 \/ exists z, getopt_int_cell m p z.

(** Pointer slots, including the exact null sentinel. Each native byte
    is canonical independently of the aggregate pointer load; consumers
    can reconstruct exact byte pieces after argv permutation. *)
Fixpoint getopt_slots m a (ps : list ptr) : Prop :=
  match ps with
  | [] => pointer_slot m a (mkPtr 0 CNone) /\
      (forall k, 0 <= k < 8 -> 0 <= m_bytes m (a + k) < 256)
  | p :: rest => pointer_slot m a p /\
      (forall k, 0 <= k < 8 -> 0 <= m_bytes m (a + k) < 256) /\
      getopt_slots m (a + 8) rest
  end.

(** argv[0] is fixed; GNU permutation moves whole tail pointers, never
    merely their address bits. argc=0 admits just the sentinel. *)
Definition getopt_order (before after : list ptr) : Prop :=
  match before, after with
  | [], [] => True
  | p :: ps, q :: qs => p = q /\ Permutation ps qs
  | _, _ => False
  end.

(** Argument strings are borrowed, readable C strings. *)
Definition getopt_strings m input : Prop :=
  Forall (fun entry => c_string m (fst entry) (snd entry)) (getopt_arguments input).

(** A writable argv vector and one capability-exact permitted ordering. *)
Definition getopt_vector m input : Prop :=
  writable_span m (mkSpan (getopt_argv input) (8 * (getopt_argc input + 1))) /\
  access_res m (ptr_addr (getopt_argv input)) (ptr_cap (getopt_argv input))
    (8 * (getopt_argc input + 1)) Read 8 = Some ok /\
  access_res m (ptr_addr (getopt_argv input)) (ptr_cap (getopt_argv input))
    (8 * (getopt_argc input + 1)) Write 8 = Some ok /\
  exists ps, getopt_order (map fst (getopt_arguments input)) ps /\
    getopt_slots m (ptr_addr (getopt_argv input)) ps.

(** All records and names are readable; optional flag writes require
    their own authority. A null name terminates the table. *)
Fixpoint getopt_records m a (options : list long_option) : Prop :=
  match options with
  | [] => exists p, ptr_addr p = 0 /\ pointer_slot m a p
  | o :: rest =>
      pointer_slot m a (option_name o) /\ ptr_addr (option_name o) <> 0 /\
      c_string m (option_name o) (option_text o) /\
      0 <= option_argument o <= 2 /\
      load_bytes m (a + 8) 4 = option_argument o /\
      pointer_slot m (a + 16) (option_flag o) /\
      getopt_int (option_value o) /\
      load_bytes m (a + 24) 4 = option_value o mod 2 ^ 32 /\
      getopt_optional_int m (option_flag o) /\ getopt_records m (a + 32) rest
  end.

(** The five actual argument words, independent of any result. *)
Definition getopt_words input : list word :=
  [WInt (getopt_argc input); WPtr (getopt_argv input);
   WPtr (getopt_optstring input); WPtr (getopt_longopts input);
   WPtr (getopt_longindex input)].

(** Caller admission includes the entire sentinel-terminated table and
    every optional writable flag/index, even on an unknown option. *)
Definition getopt_input_at m input : Prop :=
  0 <= getopt_argc input < 2 ^ 31 /\
  getopt_argc input = Z.of_nat (length (getopt_arguments input)) /\
  getopt_vector m input /\ getopt_strings m input /\
  c_string m (getopt_optstring input) (getopt_short_options input) /\
  access_res m (ptr_addr (getopt_longopts input)) (ptr_cap (getopt_longopts input))
    (32 * (Z.of_nat (length (getopt_options input)) + 1)) Read 8 = Some ok /\
  getopt_records m (ptr_addr (getopt_longopts input)) (getopt_options input) /\
  getopt_optional_int m (getopt_longindex input) /\
  Z.of_nat (length (getopt_options input)) < 2 ^ 31.

(** Public exposed state is coherent with memory. A separate rep premise
    certifies initialized continuation or reset optind=0, including GNU
    ordering/environment and any interior nextchar borrow. *)
Definition getopt_state_at m w : Prop :=
  exposed_pointer_cell m (getopt_optarg_cell w) (getopt_optarg w) /\
  getopt_int_cell m (getopt_optind_cell w) (getopt_optind w) /\
  getopt_int_cell m (getopt_opterr_cell w) (getopt_opterr w) /\
  getopt_int_cell m (getopt_optopt_cell w) (getopt_optopt w) /\
  getopt_int_cell m (getopt_errno_cell w) (getopt_errno w).

(** A pointer borrow into any argv string, including its NUL, retains
    the original capability. Empty --greeting= is therefore admitted. *)
Definition getopt_borrow input p : Prop :=
  exists q text offset, In (q, text) (getopt_arguments input) /\
    0 <= offset <= Z.of_nat (length text) /\
    p = mkPtr (ptr_addr q + offset) (ptr_cap q).

(** Null or an argv borrow, never a fresh owned allocation. *)
Definition getopt_optarg_at input p : Prop :=
  ptr_addr p = 0 \/ getopt_borrow input p.

(** Spans protected against all writes, including private/errno roots.
    Separation is about storage, not restrictions on argument bytes. *)
Definition getopt_protected input : list span :=
  map (fun entry => mkSpan (fst entry) (Z.of_nat (length (snd entry)) + 1))
    (getopt_arguments input) ++
  [mkSpan (getopt_optstring input) (Z.of_nat (length (getopt_short_options input)) + 1);
   mkSpan (getopt_longopts input) (32 * (Z.of_nat (length (getopt_options input)) + 1))] ++
  map (fun o => mkSpan (option_name o) (Z.of_nat (length (option_text o)) + 1))
    (getopt_options input).

(** Optional writable output span. *)
Definition getopt_optional_span p : list span :=
  if ptr_addr p =? 0 then [] else [mkSpan p 4].

(** Exposed writable cells, distinct from private parser roots. *)
Definition getopt_cells w : list span :=
  [mkSpan (getopt_optarg_cell w) 8; mkSpan (getopt_optind_cell w) 4;
   mkSpan (getopt_opterr_cell w) 4; mkSpan (getopt_optopt_cell w) 4;
   mkSpan (getopt_errno_cell w) 4].

(** Caller-owned outputs remain separate from parser-private spans. *)
Definition getopt_public_writes input w : list span :=
  getopt_cells w ++
  [mkSpan (getopt_argv input) (8 * (getopt_argc input + 1))] ++
  getopt_optional_span (getopt_longindex input) ++
  flat_map (fun o => getopt_optional_span (option_flag o)) (getopt_options input).

(** No character-buffer writes are authorized by parsing. *)
Definition getopt_writes input w : list span :=
  getopt_roots w ++ getopt_public_writes input w.

(** The separate output pieces do not overlap. This intentionally
    excludes aliased flag/index/state outputs, whose last-write behavior
    is not specified here; it excludes no Hello argument contents. *)
Fixpoint getopt_disjoint (spans : list span) : Prop :=
  match spans with
  | [] => True
  | s :: rest =>
      (forall t a, In t rest -> span_contains s a -> ~ span_contains t a) /\
      getopt_disjoint rest
  end.

(** The argv slots and strings supply borrowed capabilities for optarg
    and permutation, but do not delegate private ownership. *)
Definition getopt_sources input w : list span :=
  getopt_reads w ++ getopt_writes input w ++ getopt_protected input.

(** Disjoint protected bytes and write spans. Representation must also
    keep private release rights exclusive of all caller objects. *)
Definition getopt_separated input w : Prop :=
  (forall source root a, In source (getopt_protected input) ->
    In root (getopt_writes input w) ->
    span_contains source a -> ~ span_contains root a) /\
  (forall public private a, In public (getopt_public_writes input w) ->
    In private (getopt_roots w) ->
    span_contains public a -> ~ span_contains private a).

(** Private releases name live heap objects and exclude every caller
    capability-bearing input/output object, not merely its byte span. *)
Definition getopt_private_owned m input w : Prop :=
  forall base, In base (getopt_owned w) ->
    (exists reg, object_region base (m_regions m) = Some reg /\
      r_kind reg = Heap /\ r_life reg = Live) /\
    forall source, In source (getopt_protected input ++ getopt_public_writes input w) ->
      ptr_cap (span_ptr source) <> Obj base /\ ptr_cap (span_ptr source) <> Ro base.

(** Normal outcomes preserve protected bytes AND shadow entries. *)
Definition getopt_frame input m m' : Prop :=
  forall source a, In source (getopt_protected input) -> span_contains source a ->
    m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a.

(** Physical public cell identities never change across a call. *)
Definition getopt_same_cells w w' : Prop :=
  getopt_optarg_cell w' = getopt_optarg_cell w /\
  getopt_optind_cell w' = getopt_optind_cell w /\
  getopt_opterr_cell w' = getopt_opterr_cell w /\
  getopt_optopt_cell w' = getopt_optopt_cell w /\
  getopt_errno_cell w' = getopt_errno_cell w.

(** Private projection capabilities come from explicitly enumerated
    private pointers or new objects, NOT complete pointer slots inside
    caches, which may contain a caller's optarg/nextchar borrow. *)
Definition getopt_private_cap w born c : Prop :=
  c = CNone \/
  (exists source, In source (getopt_reads w ++ getopt_roots w) /\
    c = ptr_cap (span_ptr source)) \/
  (exists base, In base born /\ (c = Obj base \/ c = Ro base)).

(** Private authority can only descend from old private authority or
    born objects. In particular storing optarg never makes its argv
    object a parser root or an owned allocation eligible for release. *)
Definition getopt_delegates w born m' w' : Prop :=
  (forall root, In root (getopt_roots w') ->
    getopt_private_cap w born (ptr_cap (span_ptr root)) /\
    forall a, span_contains root a -> write_authority (getopt_roots w) born m' a) /\
  (forall source, In source (getopt_reads w') ->
    getopt_private_cap w born (ptr_cap (span_ptr source))) /\
  (forall base, In base (getopt_owned w') -> In base (getopt_owned w ++ born)).

(** Drop GNU's leading ordering marker, then the error marker. *)
Definition getopt_short_body (options : list Z) : list Z :=
  let body := match options with
    | marker :: rest => if (marker =? 43) || (marker =? 45) then rest else options
    | [] => [] end in
  match body with marker :: rest => if marker =? 58 then rest else body | [] => [] end.

(** First occurrence of a short option selects its argument mode.
    Native char is signed on this target; high bytes are sign-extended. *)
Fixpoint getopt_short_mode (options : list Z) (byte : Z) : option Z :=
  match options with
  | [] => None
  | head :: rest => if head =? byte then
      Some (match rest with
        | 58 :: 58 :: _ => 2
        | 58 :: _ => 1
        | _ => 0 end)
    else getopt_short_mode rest byte
  end.

(** Mode zero has no optarg, mode one needs a nonnull argv borrow,
    and mode two permits either. No ownership is transferred. *)
Definition getopt_argument_at input p mode : Prop :=
  if mode =? 0 then ptr_addr p = 0 else
    getopt_optarg_at input p /\ (mode = 1 -> ptr_addr p <> 0).

(** Abstract result classification. Long success reports its table
    index and writes its flag, or returns val when the flag is absent.
    A required argument always yields a nonnull readable argv borrow.
    Errors and end-of-options have null optarg. Scanning order is left
    abstract; this relation promises no termination or exact diagnostics. *)
Definition getopt_result input m' w' code : Prop :=
  (code = -1 /\ ptr_addr (getopt_optarg w') = 0) \/
  ((code = 63 \/ code = 58) /\ ptr_addr (getopt_optarg w') = 0) \/
  (exists byte mode, 0 < byte < 256 /\ byte <> 58 /\ byte <> 59 /\
    code = (if byte <? 128 then byte else byte - 256) /\
    getopt_short_mode (getopt_short_body (getopt_short_options input)) byte = Some mode /\
    getopt_argument_at input (getopt_optarg w') mode) \/
  (exists rest, getopt_short_options input = 45 :: rest /\ code = 1 /\
    getopt_borrow input (getopt_optarg w') /\ ptr_addr (getopt_optarg w') <> 0) \/
  (exists i o, nth_error (getopt_options input) i = Some o /\
    (if ptr_addr (option_flag o) =? 0 then code = option_value o else
      code = 0 /\ getopt_int_cell m' (option_flag o) (option_value o)) /\
    (ptr_addr (getopt_longindex input) = 0 \/
      getopt_int_cell m' (getopt_longindex input) (Z.of_nat i)) /\
    getopt_argument_at input (getopt_optarg w') (option_argument o)).

(** GNU diagnostics are stderr acceptance only; the caller-owned errno
    cell may change even when no diagnostic is emitted. *)
Definition getopt_trace (trace : list event) : Prop :=
  Forall (fun e => exists bytes, e = StreamBytes 2 bytes /\
    Forall (fun b => 0 <= b < 256) bytes) trace.

(** Ready admission does not equate reset with arbitrary writable state.
    Private ownership/liveness and noninterference belong to rep. *)
Definition getopt_pre {W} input (view : W -> getopt_world) rep xs m w : Prop :=
  xs = getopt_words input /\ getopt_input_at m input /\ rep m w /\
  getopt_state_at m (view w) /\ 0 <= getopt_optind (view w) <= getopt_argc input /\
  Forall (writable_span m) (getopt_roots (view w)) /\
  Forall (fun s => readable_bytes m (span_ptr s) (span_size s)) (getopt_reads (view w)) /\
  getopt_separated input (view w) /\
  getopt_disjoint (getopt_public_writes input (view w)) /\
  getopt_private_owned m input (view w).

(** Logical prefix endpoints use an in-progress representation, not
    completed parser state at arbitrary native cutpoints. Resource ends
    inherit only this prefix relation, not the normal postcondition. *)
Definition getopt_prefix {W} input (view : W -> getopt_world)
    (inflight : mem -> W -> Prop) (stable : W -> W -> Prop)
    (xs : list word) (m : mem) w born trace m' w' : Prop :=
  inflight m' w' /\ stable w w' /\ getopt_trace trace /\
  getopt_same_cells (view w) (view w') /\
  getopt_delegates (view w) born m' (view w') /\ getopt_frame input m m'.

(** Normal completion restores represented option state and all input
    borrows for positive argc. The argc=0 early return exports private
    optarg/optopt, not necessarily their old public values or a borrow
    into this empty argv. optind is in range; opterr is unchanged.
    optopt is deliberately not overconstrained on successful paths. *)
Definition getopt_post {W} input (view : W -> getopt_world)
    (rep : mem -> W -> Prop) (xs : list word) (m : mem) (w : W)
    (born : list Z) (trace : list event) ending m' w' : Prop :=
  rep m' w' /\ getopt_input_at m' input /\ getopt_state_at m' (view w') /\
  getopt_opterr (view w') = getopt_opterr (view w) /\
  exists code, ending = CallReturn [WInt (code mod 2 ^ 32)] /\
    (if getopt_argc input =? 0 then code = -1 /\
      getopt_optind (view w') = getopt_optind (view w) else
      getopt_optarg_at input (getopt_optarg (view w')) /\
      (ptr_addr (getopt_optarg (view w')) = 0 \/
        exists bytes, c_string m' (getopt_optarg (view w')) bytes) /\
      0 <= getopt_optind (view w') <= getopt_argc input /\
      getopt_result input m' (view w') code).

(** Exact W/P/P/P/P arguments and W result, even when discarded. *)
Definition getopt_abi r args : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\
  exists a b c d e, args = [Arg W a; Arg P b; Arg P c; Arg P d; Arg P e].

(** Trusted family over a projection of the existing libc world.
    The supplied stable relation must preserve effective locale names,
    text, codec and epoch and the one shutdown/stdout inventory.
    requests accounts for diagnostic/private allocations; there is no
    promise of purity, ordinary malloc NULL, or native adequacy. *)
Definition getopt_contract {World} input (view : World -> getopt_world)
    (rep inflight : mem -> World -> Prop) (stable : World -> World -> Prop)
    (requests : list word -> mem -> World -> Z -> Z -> Prop) : contract World :=
  mkContract World (RClass W) getopt_abi (getopt_pre input view rep)
    (fun _ _ w => getopt_sources input (view w))
    (fun _ _ w => getopt_writes input (view w))
    (fun _ _ w => getopt_owned (view w)) requests
    (getopt_prefix input view inflight stable) (getopt_post input view rep)
    resource_reason
    (fun why => In why [NullCapability; OutOfBounds; Misaligned; Readonly; ArgumentSize; ReturnSize]).

(** The exact capability of a borrowed optarg is never replaced by a
    stronger Obj capability having the same address. *)
Lemma getopt_borrow_cap : forall input p,
  getopt_borrow input p -> exists q text,
    In (q, text) (getopt_arguments input) /\ ptr_cap p = ptr_cap q.
Proof.
  intros input p (q & text & offset & Hin & Hrange & ->).
  exists q, text. auto.
Qed.

(** Permutation preserves argv's full pointer inventory. *)
Lemma getopt_order_inventory : forall before after,
  getopt_order before after -> Permutation before after.
Proof.
  intros [|p ps] [|q qs] H; simpl in H; try contradiction.
  - apply Permutation_refl.
  - destruct H as [-> H]. apply perm_skip. exact H.
Qed.

(** Every option result is a normal W return, never an exit request. *)
Lemma getopt_post_return : forall W input view rep xs m w born trace ending m' w',
  @getopt_post W input view rep xs m w born trace ending m' w' ->
  exists code, ending = CallReturn [WInt (code mod 2 ^ 32)].
Proof.
  intros W input view rep xs m w born trace ending m' w'
    (_ & _ & _ & _ & code & H & _). eauto.
Qed.

(** Required arguments cannot be a null optarg, even for empty strings. *)
Lemma getopt_required_argument : forall input p,
  getopt_argument_at input p 1 -> getopt_borrow input p /\ ptr_addr p <> 0.
Proof.
  intros input p [Harg Hnonnull]. specialize (Hnonnull eq_refl).
  split; [destruct Harg; [contradiction|assumption]|assumption].
Qed.

(** The post exposes exactly the ordinary pointer-load protocol main
    uses: address bytes together with the original capability in aux. *)
Lemma getopt_post_optarg_load : forall World input view rep xs m w born trace ending m' w',
  @getopt_post World input view rep xs m w born trace ending m' w' ->
  pointer_load_effects m' (ptr_addr (getopt_optarg_cell (view w')))
    [AuxRead; LowerResolve; AddressRead] = Some (getopt_optarg (view w')).
Proof.
  intros World input view rep xs m w born trace ending m' w' (_ & _ & [Hcell _] & _).
  apply exposed_pointer_load. exact Hcell.
Qed.

(** Runtime-facing lemmas for this machine instance. Sibling functor
    applications are generative; using these inside Logic requires the
    separately reviewed exact-instance integration, not an alias claim. *)
Module Getopt (R : Runtime).
Module M := ExternalMachine R.
Module E := M.E.

(** Both normal and resource endpoints expose the actual finite effect
    path and stable composite world. Only normal endpoints restore the
    postcondition; a failed allocation does not imply parser completion. *)
Theorem getopt_invocation : forall World input view rep inflight stable requests
    r args xs s m (w : World) trace ending s' m' w',
  E.invoke (getopt_contract input view rep inflight stable requests)
    r args xs s m w trace ending s' m' w' ->
  getopt_pre input view rep xs m w /\ exists born,
    E.effects (getopt_sources input (view w)) (getopt_writes input (view w))
      (getopt_owned (view w)) (requests xs m w) s m [] s' m' born /\
    getopt_prefix input view inflight stable xs m w born trace m' w' /\
    (getopt_post input view rep xs m w born trace ending m' w' \/
      exists why, ending = CallResource why /\
        E.resource_failure (requests xs m w) s' why /\ resource_reason why).
Proof.
  intros World input view rep inflight stable requests r args xs s m w trace ending s' m' w' Hcall.
  destruct Hcall as [trace ending s' m' w' born Habi Hpre [He Hp] Hpost Hresource Hvalues Hexit
    |why trace s' m' w' born Habi Hpre [He Hp] Hfailure Hresource].
  - split; [exact Hpre|]. exists born. split; [exact He|]. split; [exact Hp|]. auto.
  - split; [exact Hpre|]. exists born. split; [exact He|]. split; [exact Hp|].
    right. exists why. auto.
Qed.

End Getopt.

(** Slot controls separate canonical bytes from their aggregate load.
    The noncanonical null encoding cancels 256 against -1 * 256. *)
Module GetoptSlotChecks.

(** Canonical zero bytes admit both an argv entry and its sentinel. *)
Example canonical_slots :
  getopt_slots (mkMem (fun _ => 0) [] (fun _ => CNone)) 0 [mkPtr 0 CNone].
Proof.
  cbn [getopt_slots]. repeat split; try reflexivity; try lia;
    intros k Hk; change (0 <= 0 < 256); lia.
Qed.

(** These integers decode to zero but are not native memory bytes. *)
Definition noncanonical : mem :=
  mkMem (fun a => if a =? 0 then 256 else if a =? 1 then -1 else 0)
    [] (fun _ => CNone).

(** Merely specifying the loaded pointer does not exclude this memory. *)
Example noncanonical_pointer : pointer_slot noncanonical 0 (mkPtr 0 CNone).
Proof. vm_compute. repeat split; congruence. Qed.

(** Bounds apply to the final null slot too, not only nonnull entries. *)
Example noncanonical_sentinel_rejected : ~ getopt_slots noncanonical 0 [].
Proof.
  intros [_ Hbytes]. specialize (Hbytes 0 ltac:(lia)).
  change (0 <= 256 < 256) in Hbytes. lia.
Qed.

End GetoptSlotChecks.
