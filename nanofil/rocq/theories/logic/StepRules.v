(** When verifying a compiled C function in Rocq, unfolding the
    interpreter's main [step] function at every IR instruction exposes the
    entire function body and memory state in the proof goal. Instead of
    reducing [step] directly, this module provides a forward stepping lemma
    for each instruction and control-flow jump in the [[core subset]]. Each
    lemma reduces [step] to its next configuration once a few small, local
    premises—such as reading a temporary or checking an address against an
    object's bounds—are discharged.

    ## From interpreter steps to program-logic rules

    Whereas [Steps](../core/Steps.v) works backward from a step that has
    already occurred, the lemmas here work forward from the current call
    [[frame]] and instruction list. The program logic in [Logic](Logic.v)
    lifts these forward stepping rules directly into
    [[weakest-precondition|weakest-precondition]] rules so that a function
    proof can step through arithmetic, pointer [[flight|flights]], memory
    loads and stores, atomic compare-exchanges, and calls one instruction at
    a time. Throughout this module, every stepping rule assumes that the
    active call frame is not [[doomed]] by an earlier ahead-of-time check
    failure. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics.
Import ListNotations.
Open Scope Z_scope.

(** ## Operations

    In nanofil IR, most `Let` instructions evaluate their operand list, run
    an operation on the resulting words, and bind the destination temporary
    to the result. This section defines the stepping rule for general `Let`
    operations and for heap allocations within Fil-C's size limit. *)

(** Arithmetic, bitwise, check, load, and allocation operations all
    evaluate through a single operation interpreter, whereas stack-local
    checks, function-pointer checks, and variadic snapshot reads are handled
    separately by the frame stepper. The boolean test [general_op]
    identifies the operations that use the common operation interpreter. *)
Definition general_op (o : op) : bool :=
  match o with CheckLocal _ _ _ _ _ | CheckFunction | VaArgs => false | _ => true end.

(** When an instruction in a non-[[doomed]] call frame continues normally to
    the next instruction, the frame remains non-doomed after the step. *)
Lemma doomed_result_continue : forall ge fr m i e ls m',
  fr_doomed fr = None -> doomed_result ge fr m i (IContinue e ls m') = Some (IContinue e ls m', None).
Proof.
  intros ge fr m i e ls m' Hd. unfold doomed_result. rewrite Hd.
  destruct i as [d k o args| | | | | | | |]; try reflexivity.
  destruct k; try reflexivity. destruct o; try reflexivity.
  destruct args as [|a [|a' args]]; reflexivity.
Qed.

(** When a call frame has no pending check failure, requesting a [[fresh]]
    heap allocation leaves the frame free of pending check failures. *)
Lemma doomed_result_fresh_none : forall ge fr m i q k,
  fr_doomed fr = None -> doomed_result ge fr m i (IFresh q k) = Some (IFresh q k, None).
Proof.
  intros ge fr m i q kk Hd. unfold doomed_result. rewrite Hd.
  destruct i as [d k o args| | | | | | | |]; try reflexivity.
  destruct k; try reflexivity. destruct o; try reflexivity.
  destruct args as [|a [|a' args]]; reflexivity.
Qed.

(** When an instruction in a non-doomed call frame invokes a function, the
    frame likewise remains non-doomed. *)
Lemma doomed_result_call : forall ge fr m i g xs pd,
  fr_doomed fr = None -> doomed_result ge fr m i (ICall g xs pd) = Some (ICall g xs pd, None).
Proof.
  intros ge fr m i g xs pd Hd. unfold doomed_result. rewrite Hd.
  destruct i as [d k o args| | | | | | | |]; try reflexivity.
  destruct k; try reflexivity. destruct o; try reflexivity.
  destruct args as [|a [|a' args]]; reflexivity.
Qed.

(** Every instruction rule in this module shares the same outer interpreter
    unfolding. When the active call frame has no pending check failure and
    its head instruction evaluates cleanly, [rule_inst] advances the
    configuration to that instruction's next state. *)
Lemma rule_inst : forall ge f e ls l i rest j cs m fuel out,
  inst_step ge (mkFrame f e ls None (Exec l (i :: rest) j)) m i = Some out ->
  doomed_result ge (mkFrame f e ls None (Exec l (i :: rest) j)) m i out = Some (out, None) ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (i :: rest) j)) cs m fuel) =
  inst_next (mkConfig (mkFrame f e ls None (Exec l (i :: rest) j)) cs m fuel) l rest j out None.
Proof.
  intros ge f e ls l i rest j cs m fuel out Hi Hd.
  unfold step; cbn [fr_at c_frame c_mem fr_doomed]. rewrite Hi.
  rewrite Hd. reflexivity.
Qed.

(** For any `Let` instruction with a general operation, if its arguments
    evaluate to words and [op_res] produces a result word and updated
    memory, [rule_let] binds the destination temporary to that word and
    advances to the next instruction. *)
Lemma rule_let : forall ge f e ls l d k o args rest j cs m fuel classes xs w m',
  general_op o = true ->
  op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some xs ->
  op_res o k xs m = Some (OpRes (RVal w) m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d w e) ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l d k o args rest j cs m fuel classes xs w m' Hg Hc Hx Ho.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) m
                 (Let d k o args) = Some (IContinue (put d w e) ls m')).
  { transitivity (let* classes := op_arg_classes o k in
                  let* xs := map2_option (value_x ge e) classes args in
                  let* out := op_res o k xs m in
                  match out with
                  | OpRes r m' => Some (bind_res d r e ls m')
                  | OpUB why => Some (IStop (UB why))
                  | OpAlloc q kont =>
                      Some (IFresh q (fun base => let (x, m') := kont base in (put d x e, ls, m')))
                  end).
    - destruct o; try discriminate Hg; destruct k; reflexivity.
    - rewrite Hc. cbn - [op_res map2_option]. rewrite Hx. cbn - [op_res]. rewrite Ho. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** When a heap allocation instruction requests a byte size within Fil-C's
    maximum allocation limit, [rule_alloc] steps to a [[fresh]] allocation
    request that binds the destination temporary to the new object's pointer
    for any granted base address. *)
Lemma rule_alloc : forall ge f e ls l d k al args rest j cs m fuel size,
  map2_option (value_x ge e) [L] args = Some [WInt size] ->
  size <= max_allocation_size ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) cs m fuel) =
  Fresh (heap_req al size)
        (fun base => mkConfig (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec l rest j))
                              cs (allocated m (heap_req al size) base) fuel).
Proof.
  intros ge f e ls l d k al args rest j cs m fuel size Hx Hs.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) m
                 (Let d k (Alloc al) args) =
               Some (IFresh (heap_req al size)
                       (fun base => (put d (WPtr (mkPtr base (Obj base))) e, ls,
                                     allocated m (heap_req al size) base)))).
  { destruct k; cbn - [map2_option heap_req allocated max_allocation_size]; rewrite Hx;
      cbn - [heap_req allocated max_allocation_size];
      replace (max_allocation_size <? size) with false by (symmetry; apply Z.ltb_ge; exact Hs);
      reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_fresh_none; reflexivity).
  reflexivity.
Qed.

(** ## Flights and stores

    In nanofil IR, pointer arithmetic is performed by a [[flight]]
    instruction that computes a new address while preserving the source
    pointer's [[capability]], and memory writes use raw store instructions
    after an access check has proven the pointer valid. This section gives
    the forward stepping rules for pointer flights, integer stores, and
    pointer stores. *)

(** A [[flight]] instruction computes a new 64-bit address from its operands
    using the arithmetic unit and pairs that address with the capability
    from its source operand. When both steps succeed, [rule_flight] binds
    the destination temporary to the resulting pointer. *)
Lemma rule_flight : forall ge f e ls l d o args lw rest j cs m fuel xs n c,
  map_option (flight_arg_x ge e) args = Some xs ->
  alu o L xs = Some (WInt n) ->
  flight_cap ge e lw = Some c ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j)) cs m fuel).
Proof.
  intros ge f e ls l d o args lw rest j cs m fuel xs n c Hx Ha Hc.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) m
                 (Flight d o args lw) = Some (IContinue (put d (WPtr (mkPtr n c)) e) ls m)).
  { cbn - [map_option alu flight_cap]. rewrite Hx, Ha, Hc. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** A raw integer store writes a value of width w at a byte offset from an
    already-checked pointer. When the value and pointer operands evaluate
    and the memory write succeeds, [rule_raw_store] advances the frame in
    the updated memory. *)
Lemma rule_raw_store : forall ge f e ls l w off v a rest j cs m fuel vk x p m',
  width_value_class w = Some vk ->
  value_x ge e vk v = Some x ->
  value_x ge e A a = Some (WPtr p) ->
  store_res w m (raw_address (ptr_addr p) off) (ptr_cap p) x = Some (ok, m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (RawStore w off v a :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l w off v a rest j cs m fuel vk x p m' Hw Hv Ha Hs.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (RawStore w off v a :: rest) j)) m
                 (RawStore w off v a) = Some (IContinue e ls m')).
  { cbn - [width_value_class value_x store_res raw_address]. rewrite Hw, Hv, Ha, Hs. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** In Fil-C, storing a pointer writes its capability into shadow [[aux]]
    memory and its 8-byte address into primary memory at an 8-byte-aligned
    address. When the write check and pointer-store steps succeed,
    [rule_raw_store_pointer] advances the frame in the updated memory. *)
Lemma rule_raw_store_pointer : forall ge f e ls l off v a es rest j cs m fuel xp p m',
  value_x ge e P v = Some (WPtr xp) ->
  value_x ge e A a = Some (WPtr p) ->
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 8 Write 8 = Some ok ->
  pointer_store_effects (raw_address (ptr_addr p) off) xp m es = Some m' ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (RawStorePointer off v a es :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l off v a es rest j cs m fuel xp p m' Hv Ha Hc Hs.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (RawStorePointer off v a es :: rest) j)) m
                 (RawStorePointer off v a es) = Some (IContinue e ls m')).
  { cbn - [value_x access_res pointer_store_effects raw_address]. rewrite Hv, Ha, Hc. cbn - [pointer_store_effects raw_address].
    rewrite Hs. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** ## Calls

    A direct `Call` instruction either invokes a C function defined in the
    current module or calls a runtime deallocator such as `c: free` or
    `c: zgc_free`. This section gives the stepping rules for pushing a new
    call [[frame]] onto the call stack and for executing a heap deallocation
    in place. *)

(** When a function calls another function defined in the same module,
    [rule_call] evaluates the argument list, builds the callee's initial
    frame, pushes the caller onto the call stack, and begins executing the
    callee. *)
Lemma rule_call : forall ge f e ls l r g args rest j cs m fuel xs gf callee,
  map_option (arg_x ge e) args = Some xs ->
  find_fn ge g = Some (Defined gf) ->
  call_frame gf xs = Some callee ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) cs m fuel) =
  Next (mkConfig callee ((mkFrame f e ls None (Exec l rest j), mkPending r None) :: cs) m fuel).
Proof.
  intros ge f e ls l r g args rest j cs m fuel xs gf callee Hx Hf Hc.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) m
                 (Call r (Global g) args) = Some (ICall gf xs (mkPending r None))).
  { cbn - [map_option find_fn]. rewrite Hx, Hf. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_call; reflexivity).
  cbn [inst_next c_frame fr_fn fr_env fr_locals c_callers c_mem c_fuel]. rewrite Hc. reflexivity.
Qed.

(** When a function calls an external deallocator name such as `c: free` or
    `c: zgc_free` that is not overridden in the module, [rule_free_sym] runs
    the environment's deallocation function on the pointer argument and
    advances the caller in the resulting memory. *)
Lemma rule_free_sym : forall ge fnm f e ls l v rest j cs m fuel x m',
  is_free_name fnm = true ->
  find_fn ge fnm = None -> lookup fnm (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some x -> ge_free ge x m = Some (ok, m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Call CVoid (Global fnm) [Arg P v] :: rest) j))
             cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge fnm f e ls l v rest j cs m fuel x m' Hn Hf Hd Hx Hfree.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Call CVoid (Global fnm) [Arg P v] :: rest) j))
                 m (Call CVoid (Global fnm) [Arg P v]) = Some (IContinue e ls m')).
  { cbn - [arg_x find_fn lookup ge_free is_free_name]. rewrite Hx, Hf. unfold external_call. rewrite Hd, Hn.
    cbn - [ge_free]. rewrite Hfree. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** Specializing [rule_free_sym] to standard C's `c: free` symbol gives the
    stepping rule [rule_free] for ordinary heap deallocation calls. *)
Lemma rule_free : forall ge f e ls l v rest j cs m fuel x m',
  find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some x -> ge_free ge x m = Some (ok, m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j))
             cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l v rest j cs m fuel x m' Hf Hd Hx Hfree.
  exact (rule_free_sym ge free_name f e ls l v rest j cs m fuel x m' eq_refl Hf Hd Hx Hfree).
Qed.

(** ## Blocks and jumps

    Control flow between basic [[block|blocks]] in nanofil IR is driven by
    block-entry steps and terminator jumps. Entering a block consumes one
    unit of execution [[fuel]] and evaluates its [[phi]] nodes, while
    terminator instructions jump to another block or return from the current
    function. *)

(** When a frame enters a basic block with nonzero [[fuel]], [rule_enter]
    looks up the block, evaluates its [[phi]] nodes for the incoming
    control-flow edge, decrements the fuel counter by one, and begins
    executing the block's instructions. *)
Lemma rule_enter : forall ge f e ls l from cs m fuel b e',
  fuel <> 0 ->
  find_block l (fn_blocks f) = Some b ->
  phis_env ge (b_phis b) from e = Some e' ->
  step ge (mkConfig (mkFrame f e ls None (Enter l from)) cs m fuel) =
  Next (mkConfig (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) cs m (fuel - 1)).
Proof.
  intros ge f e ls l from cs m fuel b e' Hf Hb Hp. unfold step; cbn [fr_at c_frame c_fuel fr_fn fr_env].
  replace (fuel =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf).
  rewrite Hb. cbn [b_phis]. rewrite Hp. reflexivity.
Qed.

(** If the execution [[fuel]] reaches zero when a frame attempts to enter a
    basic block, [rule_out_of_fuel] halts the run cleanly with an
    out-of-fuel outcome. *)
Lemma rule_out_of_fuel : forall ge f e ls l from cs m,
  step ge (mkConfig (mkFrame f e ls None (Enter l from)) cs m 0) = Done OutOfFuel.
Proof. reflexivity. Qed.

(** When a block finishes its instructions and reaches an unconditional
    `JGoto` terminator, [rule_goto] transitions the frame to enter the
    target block along the current block's outgoing edge. *)
Lemma rule_goto : forall ge f e ls l t cs m fuel,
  step ge (mkConfig (mkFrame f e ls None (Exec l [] (JGoto t))) cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Enter (edge_label t) (Some l))) cs m fuel).
Proof. intros. destruct t; reflexivity. Qed.

(** A conditional `JBranch` terminator inspects its integer condition
    operand and enters the second target block when the integer is zero, or
    the first target block when it is nonzero. *)
Lemma rule_branch : forall ge f e ls l v t1 t2 cs m fuel n,
  value_x ge e W v = Some (WInt n) ->
  step ge (mkConfig (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) cs m fuel).
Proof.
  intros ge f e ls l v t1 t2 cs m fuel n Hv. unfold step; cbn [fr_at c_frame fr_doomed jump_step fr_env].
  rewrite Hv. cbn [or_stuck]. destruct (n =? 0), t1, t2; reflexivity.
Qed.

(** When a function that returns a value reaches a return instruction,
    [rule_ret] evaluates the returned operand and hands that value to the
    frame-return step. *)
Lemma rule_ret : forall ge f e ls l v cs m fuel k x,
  fn_ret f = RClass k ->
  value_x ge e k v = Some x ->
  step ge (mkConfig (mkFrame f e ls None (Exec l [] (JRet v))) cs m fuel) =
  return_step (mkConfig (mkFrame f e ls None (Exec l [] (JRet v))) cs m fuel) (Ret x).
Proof.
  intros ge f e ls l v cs m fuel k x Hk Hv. unfold step; cbn [fr_at c_frame fr_doomed jump_step fr_env fr_fn].
  rewrite Hk, Hv. reflexivity.
Qed.

(** When a `c: void` function reaches a return instruction without a value,
    [rule_ret_void] finishes the function body and enters the frame-return
    step with no return value. *)
Lemma rule_ret_void : forall ge f e ls l cs m fuel,
  step ge (mkConfig (mkFrame f e ls None (Exec l [] JRetVoid)) cs m fuel) =
  return_step (mkConfig (mkFrame f e ls None (Exec l [] JRetVoid)) cs m fuel) RetVoid.
Proof. intros. reflexivity. Qed.

(** When the top-level entry function returns with an empty caller stack,
    [rule_return_top] invalidates the frame's stack-allocated locals in
    memory and finishes the run with the returned outcome. *)
Lemma rule_return_top : forall fr m fuel o m',
  invalidate_locals (fr_locals fr) m = Some m' ->
  return_step (mkConfig fr [] m fuel) o = Done o.
Proof. intros fr m fuel o m' H. unfold return_step; cbn [c_frame c_mem c_callers]. rewrite H. reflexivity. Qed.

(** When a called function returns to a waiting caller on the call stack,
    [rule_return] invalidates the callee's stack locals, binds the returned
    value in the caller's environment, and resumes the caller frame. *)
Lemma rule_return : forall fr cf pd cs m fuel o m' e',
  invalidate_locals (fr_locals fr) m = Some m' ->
  pd_conv pd = None ->
  returned_env (pd_res pd) o (fr_env cf) = Some e' ->
  return_step (mkConfig fr ((cf, pd) :: cs) m fuel) o =
  Next (mkConfig (mkFrame (fr_fn cf) e' (fr_locals cf) (fr_doomed cf) (fr_at cf)) cs m' fuel).
Proof.
  intros fr cf pd cs m fuel o m' e' H Hc He. unfold return_step; cbn [c_frame c_mem c_callers c_fuel].
  rewrite H, Hc, He. reflexivity.
Qed.

(** If a returning function allocated no named stack locals, invalidating
    its local list leaves memory unchanged. *)
Lemma invalidate_none : forall m, invalidate_locals [] m = Some m.
Proof. reflexivity. Qed.

(** ## Access checks

    Before a raw load or store can touch memory in Fil-C, a capability check
    instruction must verify that the accessed byte range lies within the
    target object's bounds and satisfies the required alignment. This
    section proves when full checks, [[half_check|half checks]], and
    [[renew]] operations succeed, and gives the evaluation rules for integer
    and pointer loads and stores. *)

(** A read or write access through a writable object capability succeeds
    whenever the target object is registered in memory, the accessed byte
    range lies within its bounds, and the address satisfies the required
    alignment. *)
Lemma access_obj : forall m b reg a size r al,
  object_region b (m_regions m) = Some reg ->
  b <= a -> a + size <= r_end reg -> a mod al = 0 ->
  access_res m a (Obj b) size r al = Some ok.
Proof.
  intros m b reg a size r al Hr H1 H2 H3. unfold access_res, cap_access_res. rewrite Hr.
  replace ((b <=? a) && (a + size <=? r_end reg)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  unfold aligned_res. rewrite H3. reflexivity.
Qed.

(** A read access succeeds under the same bounds and alignment conditions
    whether the pointer carries a writable object capability or a read-only
    capability. *)
Lemma access_read : forall m b reg c a size al,
  c = Obj b \/ c = Ro b ->
  object_region b (m_regions m) = Some reg ->
  b <= a -> a + size <= r_end reg -> a mod al = 0 ->
  access_res m a c size Read al = Some ok.
Proof.
  intros m b reg c a size al [->| ->] Hr H1 H2 H3; [exact (access_obj _ _ _ _ _ _ _ Hr H1 H2 H3)|].
  unfold access_res, cap_access_res. rewrite Hr.
  replace ((b <=? a) && (a + size <=? r_end reg)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  cbn [readonly_access_res]. unfold aligned_res. rewrite H3. reflexivity.
Qed.

(** When the byte range `[lo, hi)` from a pointer passes its capability
    access check, the full [[check]] operation returns that pointer as a
    proven access pointer without modifying memory. *)
Lemma op_check : forall m p lo hi r al,
  access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al = Some ok ->
  op_res (Check lo hi r al) A [WPtr p] m = Some (OpRes (RVal (WPtr p)) m).
Proof. intros m p lo hi r al H. cbn - [access_res raw_address]. rewrite H. reflexivity. Qed.

(** A [[half_check]] operation checks only one bound of a pointer by
    borrowing the other bound from an earlier proven pointer with the same
    writable object capability. When the target object is live, fits below
    2^63, and contains the aligned access range, [op_half_check] succeeds
    and returns the proven pointer. *)
Lemma op_half_check : forall m p1 p bd lo hi r al b reg,
  ptr_cap p1 = Obj b -> ptr_cap p = Obj b ->
  object_region b (m_regions m) = Some reg -> r_life reg = Live ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  op_res (HalfCheck bd lo hi r al) A [WPtr p1; WPtr p] m = Some (OpRes (RVal (WPtr p)) m).
Proof.
  intros m p1 p bd lo hi r al b reg H1 H2 Hr Hl Hlo Hhi Hlh Hend Hal.
  assert (Hacc : access_res m (raw_address (ptr_addr p) lo) (Obj b) (hi - lo) r al = Some ok)
    by (eapply access_obj; eauto).
  cbn - [access_res raw_address half_passes]. rewrite H1, H2.
  cbn [cap_eqb]. rewrite Z.eqb_refl, Hacc.
  unfold half_passes. rewrite Hr. cbn [option_map].
  replace (half_bound bd (raw_address (ptr_addr p) lo) (hi - lo) b (r_end reg) (r_life reg)) with true.
  - rewrite Hal, Z.eqb_refl. destruct r; reflexivity.
  - symmetry. unfold half_bound. rewrite Hl. destruct bd; [apply Z.leb_le; lia|].
    assert (Hn : 0 <= raw_address (ptr_addr p) lo < 2 ^ 63).
    { pose proof (Z.mod_pos_bound (ptr_addr p + lo) (2 ^ 64) ltac:(lia)) as Hm.
      fold (raw_address (ptr_addr p) lo) in Hm. lia. }
    replace (2 ^ 63 <=? raw_address (ptr_addr p) lo) with false by (symmetry; apply Z.leb_gt; lia).
    apply Z.leb_le; lia.
Qed.

(** For a read access, a [[half_check]] operation succeeds under the same
    live-object and bounds conditions whether the two pointers share a
    writable capability or a read-only capability. *)
Lemma op_half_check_read : forall m p1 p bd lo hi al b reg,
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  object_region b (m_regions m) = Some reg -> r_life reg = Live ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  op_res (HalfCheck bd lo hi Read al) A [WPtr p1; WPtr p] m = Some (OpRes (RVal (WPtr p)) m).
Proof.
  intros m p1 p bd lo hi al b reg E Hc Hr Hl Hlo Hhi Hlh Hend Hal.
  destruct Hc as [Hc | Hc]; [rewrite Hc in E; exact (op_half_check _ _ _ _ _ _ Read _ _ _ E Hc Hr Hl Hlo Hhi Hlh Hend Hal)|].
  assert (Hacc : access_res m (raw_address (ptr_addr p) lo) (Ro b) (hi - lo) Read al = Some ok)
    by (eapply access_read; eauto).
  cbn - [access_res raw_address half_passes]. rewrite E, Hc.
  cbn [cap_eqb]. rewrite Z.eqb_refl, Hacc.
  unfold half_passes. rewrite Hr. cbn [option_map].
  replace (half_bound bd (raw_address (ptr_addr p) lo) (hi - lo) b (r_end reg) (r_life reg)) with true.
  - rewrite Hal, Z.eqb_refl. reflexivity.
  - symmetry. unfold half_bound. rewrite Hl. destruct bd; [apply Z.leb_le; lia|].
    assert (Hn : 0 <= raw_address (ptr_addr p) lo < 2 ^ 63).
    { pose proof (Z.mod_pos_bound (ptr_addr p + lo) (2 ^ 64) ltac:(lia)) as Hm.
      fold (raw_address (ptr_addr p) lo) in Hm. lia. }
    replace (2 ^ 63 <=? raw_address (ptr_addr p) lo) with false by (symmetry; apply Z.leb_gt; lia).
    apply Z.leb_le; lia.
Qed.

(** A [[renew]] operation re-establishes a proven pointer after a safepoint
    or call by checking that it carries the same capability as an earlier
    proof and passes its access check. *)
Lemma op_renew : forall m p1 p lo hi r al,
  ptr_cap p1 = ptr_cap p ->
  access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al = Some ok ->
  op_res (Renew lo hi r al) A [WPtr p1; WPtr p] m = Some (OpRes (RVal (WPtr p)) m).
Proof.
  intros m p1 p lo hi r al E H. cbn - [access_res raw_address cap_eqb]. rewrite E.
  replace (cap_eqb (ptr_cap p) (ptr_cap p)) with true
    by (symmetry; destruct (ptr_cap p); cbn; try apply Z.eqb_refl; try apply term_eqb_refl; reflexivity).
  rewrite H. reflexivity.
Qed.

(** When an 8-byte read access at an offset from a proven pointer succeeds,
    a 64-bit raw load reads the 8 little-endian bytes at that address as an
    integer. *)
Lemma op_raw_load : forall m k p off,
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 8 Read 1 = Some ok ->
  op_res (RawLoad LdL off) k [WPtr p] m =
  Some (OpRes (RVal (WInt (load_bytes m (raw_address (ptr_addr p) off) 8))) m).
Proof.
  intros m k p off H.
  assert (E : op_res (RawLoad LdL off) k [WPtr p] m = op_res_int (RawLoad LdL off) k [WPtr p] m)
    by (destruct k; reflexivity).
  rewrite E. cbn - [access_res raw_address load_bytes]. unfold int_load_res. cbn - [access_res raw_address load_bytes]. rewrite H. reflexivity.
Qed.

(** For a 1-byte narrow integer type, when the 1-byte read access succeeds,
    a narrow raw load reads that single byte from memory and sign- or
    zero-extends it to the destination register class. *)
Lemma op_raw_load_byte : forall m k n p off,
  fst (narrow_type n) = 1 ->
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 1 Read 1 = Some ok ->
  op_res (RawLoad (LdNarrow n) off) k [WPtr p] m =
  option_map (fun y => OpRes (RVal y) m) (extended n k (m_bytes m (raw_address (ptr_addr p) off))).
Proof.
  intros m k n p off Hn H.
  assert (E : op_res (RawLoad (LdNarrow n) off) k [WPtr p] m =
              op_res_int (RawLoad (LdNarrow n) off) k [WPtr p] m) by (destruct k; reflexivity).
  assert (Hl : load_bytes m (raw_address (ptr_addr p) off) 1 = m_bytes m (raw_address (ptr_addr p) off)).
  { unfold load_bytes. change (Z.to_nat 1) with 1%nat. cbn - [raw_address]. now rewrite Z.add_0_r. }
  rewrite E. cbn - [access_res raw_address load_bytes narrow_type extended]. unfold int_load_res.
  rewrite Hn, H, Hl. destruct (extended n k _); reflexivity.
Qed.

(** When an 8-byte aligned read access from a proven pointer succeeds and
    the pointer-load micro-effects produce a pointer value, a raw pointer
    load returns that pointer. *)
Lemma op_raw_load_pointer : forall m p off es x,
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 8 Read 8 = Some ok ->
  pointer_load_effects m (raw_address (ptr_addr p) off) es = Some x ->
  op_res (RawLoadPointer off es) P [WPtr p] m = Some (OpRes (RVal (WPtr x)) m).
Proof.
  intros m p off es x H He. cbn - [access_res raw_address pointer_load_effects]. rewrite H.
  cbn - [raw_address pointer_load_effects]. rewrite He. reflexivity.
Qed.

(** The standard micro-effect sequence that nanofil emits for a plain
    pointer load reads the capability from shadow [[aux]] memory and the
    8-byte address from primary memory, combining them into a pointer. *)
Lemma pointer_load_plain : forall m a,
  pointer_load_effects m a [AuxRead; LowerResolve; AddressRead] =
  Some (mkPtr (load_bytes m a 8) (aux_at m a)).
Proof. reflexivity. Qed.

(** The standard micro-effect sequence that nanofil emits for a plain
    pointer store writes the pointer's capability into shadow [[aux]] memory
    and then writes its 8-byte address into primary memory. *)
Lemma pointer_store_plain : forall m a x,
  pointer_store_effects a x m [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] =
  Some (store_bytes (store_aux m a (ptr_cap x)) a 8 (ptr_addr x)).
Proof. reflexivity. Qed.

(** When a pointer carries a read-only capability for a registered object, a
    read access succeeds whenever the byte range lies within the object's
    bounds and the address is aligned. *)
Lemma access_ro_read : forall m b reg a size al,
  object_region b (m_regions m) = Some reg ->
  b <= a -> a + size <= r_end reg -> a mod al = 0 ->
  access_res m a (Ro b) size Read al = Some ok.
Proof.
  intros m b reg a size al Hr H1 H2 H3. unfold access_res, cap_access_res. rewrite Hr.
  replace ((b <=? a) && (a + size <=? r_end reg)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  unfold readonly_access_res, aligned_res. rewrite H3. reflexivity.
Qed.

(** When an 8-byte write access through a capability succeeds, storing a
    64-bit integer writes its 8 little-endian bytes into primary memory at
    the target address. *)
Lemma store_res_long : forall m a c v,
  access_res m a c 8 Write 1 = Some ok ->
  store_res Wl m a c (WInt v) = Some (ok, store_bytes m a 8 v).
Proof. intros m a c v H. cbn - [access_res store_bytes]. rewrite H. reflexivity. Qed.

(** Generalizing [op_raw_load_byte] to any narrow integer width, when the
    read access for the narrow type's byte width succeeds, a narrow raw load
    reads those bytes from memory and extends the integer to the destination
    class. *)
Lemma op_raw_load_narrow : forall m k n p off,
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) (fst (narrow_type n)) Read 1 = Some ok ->
  op_res (RawLoad (LdNarrow n) off) k [WPtr p] m =
  option_map (fun y => OpRes (RVal y) m)
    (extended n k (load_bytes m (raw_address (ptr_addr p) off) (fst (narrow_type n)))).
Proof.
  intros m k n p off H.
  assert (E : op_res (RawLoad (LdNarrow n) off) k [WPtr p] m =
              op_res_int (RawLoad (LdNarrow n) off) k [WPtr p] m) by (destruct k; reflexivity).
  rewrite E. cbn - [access_res raw_address load_bytes narrow_type extended]. unfold int_load_res.
  rewrite H. destruct (extended n k _); reflexivity.
Qed.

(** ## Compare-exchange

    Atomic compare-and-exchange ([[cas]]) instructions compare the value
    currently in memory against an expected value and overwrite it only when
    the two match. This section defines the evaluation rules for integer and
    pointer compare-exchange operations. *)

(** When an integer compare-exchange reads the old bytes from memory,
    [cas_old] formats that value for the destination register by returning a
    64-bit word directly or sign- or zero-extending a narrow integer. *)
Definition cas_old (t : cas_type) (k : class) (u : Z) : option word :=
  match t with CasNarrow nt => extended nt k u | _ => Some (WInt u) end.

(** When an aligned write access for an integer compare-exchange succeeds,
    [op_raw_cas_int] returns the old integer value from memory and writes
    the new integer's low bytes if and only if the old bytes matched the
    expected integer's low bytes. *)
Lemma op_raw_cas_int : forall m t k p off ev nv old,
  t <> CasP ->
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) (cas_bytes t) Write (cas_bytes t) = Some ok ->
  cas_old t k (load_bytes m (raw_address (ptr_addr p) off) (cas_bytes t)) = Some old ->
  op_res (RawCas t off) k [WPtr p; WInt ev; WInt nv] m =
  Some (OpRes (RVal old)
    (if load_bytes m (raw_address (ptr_addr p) off) (cas_bytes t) =? ev mod 2 ^ (8 * cas_bytes t)
     then store_bytes m (raw_address (ptr_addr p) off) (cas_bytes t) nv else m)).
Proof.
  intros m t k p off ev nv old Ht H Ho.
  assert (E : op_res (RawCas t off) k [WPtr p; WInt ev; WInt nv] m =
              op_res_int (RawCas t off) k [WPtr p; WInt ev; WInt nv] m) by (destruct k; reflexivity).
  rewrite E. cbn - [access_res raw_address load_bytes store_bytes cas_bytes extended].
  unfold cas_res. rewrite H. cbn - [raw_address load_bytes store_bytes cas_bytes extended].
  destruct t as [| |nt]; [| contradiction |]; cbn [cas_old] in Ho; [injection Ho as <- | rewrite Ho];
    cbn - [raw_address load_bytes store_bytes cas_bytes]; destruct (_ =? _); reflexivity.
Qed.

(** A pointer compare-exchange compares only the 8-byte address in memory
    against the expected pointer's address, ignoring capabilities. When its
    8-byte aligned write check passes, [op_raw_cas_ptr] returns the old
    pointer from memory and stores the new pointer's capability and address
    if the addresses matched. *)
Lemma op_raw_cas_ptr : forall m k p off ep np,
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 8 Write 8 = Some ok ->
  op_res (RawCas CasP off) k [WPtr p; WPtr ep; WPtr np] m =
  Some (OpRes (RVal (WPtr (mkPtr (load_bytes m (raw_address (ptr_addr p) off) 8)
                               (aux_at m (raw_address (ptr_addr p) off)))))
    (if load_bytes m (raw_address (ptr_addr p) off) 8 =? ptr_addr ep
     then store_bytes (store_aux m (raw_address (ptr_addr p) off) (ptr_cap np))
            (raw_address (ptr_addr p) off) 8 (ptr_addr np)
     else m)).
Proof.
  intros m k p off ep np H.
  assert (E : op_res (RawCas CasP off) k [WPtr p; WPtr ep; WPtr np] m =
              op_res_int (RawCas CasP off) k [WPtr p; WPtr ep; WPtr np] m) by (destruct k; reflexivity).
  rewrite E. cbn - [access_res raw_address load_bytes store_bytes store_aux aux_at].
  unfold cas_res. cbn - [access_res raw_address load_bytes store_bytes store_aux aux_at].
  rewrite H. cbn - [raw_address load_bytes store_bytes store_aux aux_at].
  destruct (_ =? _); reflexivity.
Qed.

(** ## Allocations Fil-C refuses

    Fil-C refuses any single heap allocation request larger than
    [max_allocation_size] by trapping with `TooBig`. As shown in
    [Panics](Panics.v), that trap is a benign resource refusal rather than a
    safety failure. *)

(** When a heap allocation instruction requests a byte size that exceeds
    Fil-C's maximum allocation limit, [rule_alloc_too_big] halts the run
    with the `TooBig` refusal trap. *)
Lemma rule_alloc_too_big : forall ge f e ls l d k al args rest j cs m fuel size,
  map2_option (value_x ge e) [L] args = Some [WInt size] ->
  max_allocation_size < size ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) cs m fuel) =
  Done (Trap TooBig).
Proof.
  intros ge f e ls l d k al args rest j cs m fuel size Hx Hs.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) m
                 (Let d k (Alloc al) args) = Some (IStop (Trap TooBig))).
  { destruct k; cbn - [map2_option max_allocation_size]; rewrite Hx; cbn - [max_allocation_size];
      replace (max_allocation_size <? size) with true by (symmetry; apply Z.ltb_lt; exact Hs);
      reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (destruct k; reflexivity).
  reflexivity.
Qed.

(** ## Calls through function pointers

    In Fil-C, calling a function through a function pointer first checks
    that the pointer carries a valid function capability at offset zero, and
    then marshals arguments through the
    [[fast-generic-convention|fast generic calling convention]]. This
    section gives the stepping rules for function-pointer checks and
    indirect calls within the module. *)

(** Before an indirect call can jump through a function pointer, it checks
    that the pointer points to the start of a valid function. When that
    check succeeds, [rule_check_function] binds the destination temporary to
    the verified function pointer. *)
Lemma rule_check_function : forall ge f e ls l d v rest j cs m fuel p,
  value_x ge e P v = Some (WPtr p) -> function_check_res ge p = Some ok ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d F CheckFunction [v] :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) cs m fuel).
Proof.
  intros ge f e ls l d v rest j cs m fuel p Hv Hc.
  apply (rule_inst ge f e ls l _ rest j cs m fuel (IContinue (put d (WPtr p) e) ls m)).
  - cbn [inst_step fr_env fr_locals]. rewrite Hv. cbn - [function_check_res]. rewrite Hc. reflexivity.
  - apply doomed_result_continue. reflexivity.
Qed.

(** When an indirect `RawCall` invokes a proven function pointer that names
    a function in the current module, [rule_raw_call] converts the call
    arguments to the callee's parameter types, appends any variadic trailing
    arguments, and pushes a new call frame onto the stack. *)
Lemma rule_raw_call : forall ge f e ls l r callee args rest j cs m fuel p g xs gf ys words fr',
  value_x ge e F callee = Some (WPtr p) -> ptr_cap p = Fn g -> function_check_res ge p = Some ok ->
  map_option (arg_x ge e) args = Some xs -> find_fn ge g = Some (Defined gf) ->
  indirect_call_conv gf r args xs = Some (Converted ys words) ->
  call_frame gf (ys ++ (if variadic_func gf then skipn (length (fn_params gf)) xs else [])) = Some fr' ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (RawCall r callee args :: rest) j)) cs m fuel) =
  Next (mkConfig fr' ((mkFrame f e ls None (Exec l rest j), mkPending r words) :: cs) m fuel).
Proof.
  intros ge f e ls l r callee args rest j cs m fuel p g xs gf ys words fr' Hv Hp Hc Hx Hf Hcv Hfr.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (RawCall r callee args :: rest) j)) m
                 (RawCall r callee args) =
               Some (ICall gf (ys ++ (if variadic_func gf then skipn (length (fn_params gf)) xs else []))
                       (mkPending r words))).
  { cbn - [value_x map_option function_check_res find_fn indirect_call_conv].
    rewrite Hv, Hx. cbn - [function_check_res find_fn indirect_call_conv].
    rewrite Hc. cbn - [find_fn indirect_call_conv]. rewrite Hp, Hf, Hcv. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_call; reflexivity).
  cbn [inst_next c_frame fr_fn fr_env fr_locals c_callers c_mem c_fuel]. rewrite Hfr. reflexivity.
Qed.

(** ## Variadic arguments

    In Fil-C, a variadic function receives its unnamed arguments in a hidden
    read-only argument [[snapshot]], while a `c: va_list` object in memory
    holds a mutable pointer cursor that steps through that snapshot. This
    section gives the stepping rules for reading the hidden snapshot pointer
    and advancing a `c: va_list` cursor with `c: va_arg`. *)

(** The `VaArgs` instruction reads the current frame's hidden variadic
    argument snapshot pointer and shifts its address by a constant byte
    offset while keeping its capability. Because the snapshot pointer lives
    in the call frame's environment, this step does not touch memory. *)
Lemma rule_va_args : forall ge f e ls l d off rest j cs m fuel p,
  lookup va_snapshot e = Some (WPtr p) ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d P VaArgs [Const off] :: rest) j)) cs m fuel) =
  Next (mkConfig
    (mkFrame f (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e)
      ls None (Exec l rest j)) cs m fuel).
Proof.
  intros ge f e ls l d off rest j cs m fuel p Hp.
  apply (rule_inst ge f e ls l (Let d P VaArgs [Const off]) rest j cs m fuel
    (IContinue (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e) ls m)).
  - cbn [inst_step fr_env fr_locals]. rewrite Hp. reflexivity.
  - apply doomed_result_continue. reflexivity.
Qed.

(** The `VaArg` instruction reads the next variadic argument of a given
    register class through a `c: va_list` pointer in memory, binds the
    destination temporary to that value, and advances the cursor stored at
    the `c: va_list` address. *)
Lemma rule_va_arg : forall ge f e ls l d k args rest j cs m fuel p x m',
  map2_option (value_x ge e) [P] args = Some [WPtr p] ->
  va_arg_res k p m = Some (RVal x, m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k VaArg args :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d x e) ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l d k args rest j cs m fuel p x m' Hargs Hread.
  apply rule_let with (classes := [P]) (xs := [WPtr p]); [reflexivity | reflexivity | exact Hargs |].
  cbn [op_res]. rewrite Hread. reflexivity.
Qed.

(** In the variadic argument convention, each argument slot is aligned to an
    8-byte boundary. Lemma [round8_aligned] shows that rounding an already
    8-byte-aligned address up to a multiple of 8 leaves the address
    unchanged. *)
Lemma round8_aligned : forall a, a mod 8 = 0 -> (a + 8 - 1) / 8 * 8 = a.
Proof.
  intros a Hal. pose proof (Z.div_mod a 8 ltac:(lia)) as Hdiv. rewrite Hal in Hdiv.
  replace (a + 8 - 1) with (7 + (a / 8) * 8) by lia.
  rewrite Z.div_add by lia. replace (7 / 8) with 0 by reflexivity. lia.
Qed.

(** When a `c: va_list` in memory holds an 8-byte-aligned cursor pointer,
    reading a pointer argument with `c: va_arg` checks both the `c: va_list`
    and the cursor slot, advances the cursor by 8 bytes in memory, and
    returns the pointer at the cursor address. *)
Lemma va_arg_pointer : forall m p a c m' x,
  access_res m (ptr_addr p) (ptr_cap p) 8 Read 8 = Some ok ->
  load_bytes m (ptr_addr p) 8 = a -> aux_at m (ptr_addr p) = c ->
  a mod 8 = 0 -> access_res m a c 8 Read 8 = Some ok ->
  store_res Wl m (ptr_addr p) (ptr_cap p) (WInt (a + 8)) = Some (ok, m') ->
  load_bytes m' a 8 = ptr_addr x -> aux_at m' a = ptr_cap x ->
  va_arg_res P p m = Some (RVal (WPtr x), m').
Proof.
  intros m p a c m' x Hp Ha Hc Hal Hcell Hstore Haddr Hcap.
  unfold va_arg_res. rewrite Hp, Ha, Hc. cbn [va_cell class_width width_bytes ptr_addr ptr_cap].
  rewrite (round8_aligned a Hal), Hcell, Hstore, Haddr, Hcap. destruct x. reflexivity.
Qed.

(** When reading an integer argument of width n bytes with `c: va_arg`,
    [va_arg_int] loads the current cursor from the `c: va_list`, rounds the
    cursor address up to an 8-byte boundary, advances the cursor by n bytes
    in memory, and returns the integer loaded from the aligned slot. *)
Lemma va_arg_int : forall m k w n p cur c a m',
  k <> P -> class_width k = Some w -> va_cell k = Some (n, 8) ->
  access_res m (ptr_addr p) (ptr_cap p) 8 Read 8 = Some ok ->
  load_bytes m (ptr_addr p) 8 = cur -> aux_at m (ptr_addr p) = c ->
  (cur + 8 - 1) / 8 * 8 = a -> access_res m a c n Read 8 = Some ok ->
  store_res Wl m (ptr_addr p) (ptr_cap p) (WInt (a + n)) = Some (ok, m') ->
  va_arg_res k p m = Some (RVal (WInt (load_bytes m' a (width_bytes w))), m').
Proof.
  intros m k w n p cur c a m' Hk Hw Hcl Hp Hcur Hc Ha Hcell Hstore.
  unfold va_arg_res. rewrite Hp, Hcur, Hc, Hcl, Hw. cbn [ptr_addr ptr_cap].
  rewrite Ha, Hcell, Hstore. destruct k; try reflexivity. contradiction.
Qed.
