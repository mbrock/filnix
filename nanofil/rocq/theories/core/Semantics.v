(** When a compiled C program runs in the [[stage|checked IR]],
    execution moves from basic [[block]] to basic block, evaluating
    instructions, checking pointer capabilities, allocating and
    freeing memory, and calling functions until the entry call
    finishes with an [[outcome]]. In the Prolog [[interpreter]], block
    evaluation is a big-step relation that runs the rest of the
    function and any nested calls inside a single step. To state and
    prove invariants that must hold between every pair of execution
    steps, this module defines a [[step|small-step]] operational
    semantics over an explicit machine [config].

    A machine [config] records four pieces of state: the running
    invocation [c_frame], the stack of suspended caller frames
    [c_callers] paired with how each caller reads its callee's return
    value, the current memory state [c_mem], and the remaining block
    [[fuel]] [c_fuel]. Each transition of [step] either takes the
    entry argument snapshot of a variadic function, enters a basic
    block by spending one unit of fuel and evaluating its [[phi]]
    nodes, executes a single instruction in [inst_step], or takes the
    block's terminating jump in [jump_step].

    When the outermost function finishes or a check fails, execution
    stops with an [outcome]. A run can return zero or more words, reach
    an unreachable jump, trigger undefined behavior on an out-of-range
    float-to-integer conversion, stop with a Fil-C safety [[trap]],
    fault as [[unchecked]] when a raw access violates its capability,
    or run out of block [[fuel]]. *)

From Stdlib Require Import String ZArith List Bool Relations.
From Nanofil Require Import Term Syntax Values Memory Ops.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** An [outcome] describes how a program run terminates. Normal
    returns produce one [word] with [Ret], several words with [Rets],
    or no value with [RetVoid], while abnormal terminations report an
    [Unreachable] jump, undefined behavior [UB], a safety [[trap]]
    [Trap], an [[unchecked]] fault [Unchecked], or exhausted [[fuel]]
    [OutOfFuel]. *)
Inductive outcome : Type :=
| Ret (x : word)
| Rets (xs : list word)
| RetVoid
| Unreachable
| UB (why : term)
| Trap (why : reason)
| Unchecked (why : reason)
| OutOfFuel.

(** ## The prepared module

    Before execution begins, the runner lays out the module's
    functions and global data objects in memory and builds the global
    environment [genv]. This section defines [fn_def] and [genv] along
    with the symbol lookup functions that resolve direct function
    names and symbol aliases. *)

(** A function definition [fn_def] in a module is either a [Defined]
    function whose body lies inside the [[core-subset|core subset]] or
    an [Outside] function kept only by its symbol name. *)
Inductive fn_def : Type := Defined (f : func) | Outside (n : name).

(** The global environment [genv] holds the decoded [module], the
    global symbol table mapping each top-level name to its allocated
    [ptr], and the [[runtime]] deallocator [ge_free] invoked when the
    program calls `c: free`. *)
Record genv : Type := mkGenv {
  ge_module : module;
  ge_globals : list (name * ptr);
  ge_free : word -> mem -> option (res unit * mem)
}.

(** Given a symbol [name] and a module's item list, [find_direct]
    searches for a [Defined] or [Outside] function with that exact
    name without following symbol aliases. *)
Fixpoint find_direct (n : name) (items : module) : option fn_def :=
  match items with
  | [] => None
  | IFunc f :: rest => if name_eqb (fn_name f) n then Some (Defined f) else find_direct n rest
  | IOutside f _ :: rest => if name_eqb f n then Some (Outside f) else find_direct n rest
  | _ :: rest => find_direct n rest
  end.

(** Given a symbol [name] and a module's item list, [find_alias]
    returns the target symbol name if the module declares an [IAlias]
    with that name, and `None` otherwise. *)
Fixpoint find_alias (n : name) (items : module) : option name :=
  match items with
  | [] => None
  | IAlias a _ t :: rest => if name_eqb a n then Some t else find_alias n rest
  | _ :: rest => find_alias n rest
  end.

(** Given the global environment and a symbol [name], [find_fn] looks
    up the function that a direct call to that name executes, checking
    [find_direct] first and following a single alias via [find_alias]
    if needed. *)
Definition find_fn (ge : genv) (n : name) : option fn_def :=
  match find_direct n (ge_module ge) with
  | Some d => Some d
  | None => let* t := find_alias n (ge_module ge) in find_direct t (ge_module ge)
  end.

(** ## Values

    When an instruction evaluates its operands, it reads temporary
    variables from the current frame's local environment, reduces
    integer constants modulo their register class width, and resolves
    global symbols to their pointers in the global environment. This
    section defines the local environment [env], the operand evaluator
    [value_x], and the helpers that evaluate call and [[flight]]
    arguments. *)

(** An environment [env] is an association list mapping each
    [[temporary]] assigned so far in the current function invocation
    to its run-time [word]. *)
Definition env := list (name * word).

(** Given the global environment, the current frame's [env], a
    register [[class]], and an IR [value], [value_x] evaluates the
    operand to a run-time [word] at that class. Integer constants at
    the pointer class carry [CNone], while global symbols not defined
    in the module resolve to address zero with an [External]
    [[capability]]. *)
Definition value_x (ge : genv) (e : env) (k : class) (v : value) : option word :=
  match v with
  | Tmp n => let* x := lookup n e in word_at_class k x
  | Const n =>
      let* m := modulus k in
      match k with
      | P => Some (WPtr (mkPtr (n mod m) CNone))
      | _ => Some (WInt (n mod m))
      end
  | Global s =>
      match lookup s (ge_globals ge) with
      | Some p => Some (WPtr p)
      | None => Some (WPtr (mkPtr 0 (External s)))
      end
  end.

(** Given a partial function and a list, [map_option] applies the
    function to each element in order and returns the list of results,
    or returns `None` if any element fails. *)
Fixpoint map_option {X Y : Type} (f : X -> option Y) (xs : list X) : option (list Y) :=
  match xs with
  | [] => Some []
  | x :: xs' => let* y := f x in let* ys := map_option f xs' in Some (y :: ys)
  end.

(** Given a two-argument partial function and two lists, [map2_option]
    applies the function pairwise to corresponding elements, or
    returns `None` if the lists differ in length or any pair fails. *)
Fixpoint map2_option {X Y Z : Type} (f : X -> Y -> option Z) (xs : list X) (ys : list Y)
  : option (list Z) :=
  match xs, ys with
  | [], [] => Some []
  | x :: xs', y :: ys' => let* z := f x y in let* zs := map2_option f xs' ys' in Some (z :: zs)
  | _, _ => None
  end.

(** Given the global environment, a local [env], and a call argument
    [arg], [arg_x] evaluates the argument's operand at its declared
    register [[class]] using [value_x]. *)
Definition arg_x (ge : genv) (e : env) (a : arg) : option word :=
  match a with Arg k v => value_x ge e k v end.

(** Given the global environment, a local environment, and a
    [[flight]] operand, [flight_arg_x] evaluates the operand for an
    address calculation. An address projection [FAddress] extracts the
    low 64 bits of a pointer's integer address, whereas a plain value
    [FValue] reads a 64-bit integer operand. *)
Definition flight_arg_x (ge : genv) (e : env) (a : flight_arg) : option word :=
  match a with
  | FAddress v =>
      let* x := value_x ge e P v in
      match x with WPtr p => Some (WInt (ptr_addr p mod 2 ^ 64)) | _ => None end
  | FValue v => value_x ge e L v
  end.

(** Given the global environment, a local environment, and a
    [[flight]] capability source, [flight_cap] returns [CNone] when no
    capability is attached and copies the source pointer's
    [[capability]] for [LowerOf], preserving its object [[identity]]. *)
Definition flight_cap (ge : genv) (e : env) (lw : flight_lower) : option cap :=
  match lw with
  | LowerNone => Some CNone
  | LowerOf v =>
      let* x := value_x ge e P v in
      match x with WPtr p => Some (ptr_cap p) | _ => None end
  end.

(** ## Frames and configurations

    Because the small-step semantics takes one instruction or
    control-flow step at a time, it represents the call stack
    explicitly as a running [frame] and a list of suspended callers
    inside a [config]. This section defines the program counter
    [point], the invocation [frame], the caller continuation
    [pending], and the initial frame constructor [call_frame]. *)

(** A [point] records where execution currently sits inside a function
    invocation. A variadic callee begins at [Snapshot] to copy its
    arguments into a read-only memory block before entering its entry
    block; [Enter] stands at the start of a basic [[block]] before
    spending one unit of [[fuel]] and binding [[phi]] nodes; and
    [Exec] steps through the remaining instructions and terminating
    jump of a block. *)
Inductive point : Type :=
| Snapshot (xs : list word) (l : name)
| Enter (l : name) (from : option name)
| Exec (l : name) (insts : list inst) (j : jump).

(** A [frame] represents one active function invocation. It holds the
    function definition, the local temporary environment, the named
    stack locals with their base addresses once allocated, any active
    [[doomed]] trap reason from an early [[check_ahead]], and the
    current execution [point]. *)
Record frame : Type := mkFrame {
  fr_fn : func;
  fr_env : env;
  fr_locals : list (name * option Z);
  fr_doomed : option reason;
  fr_at : point
}.

(** A [pending] record tells a suspended caller how to receive its
    callee's return value, storing the call site's [call_result]
    binding and, for an indirect call through the
    [[fast-generic-convention|generic entry]], the caller and callee
    word classes used to convert the returned words. *)
Record pending : Type := mkPending {
  pd_res : call_result;
  pd_conv : option (list class * list class)
}.

(** A machine configuration [config] packages the complete execution
    state between steps: the currently running [frame], the stack of
    suspended callers innermost first, the current memory [mem], and
    the remaining block [[fuel]]. *)
Record config : Type := mkConfig {
  c_frame : frame;
  c_callers : list (frame * pending);
  c_mem : mem;
  c_fuel : Z
}.

(** Given a [frame] and a new execution [point], [with_point] returns
    the same frame positioned at that point with its environment,
    locals, and doom state unchanged. *)
Definition with_point (fr : frame) (pt : point) : frame :=
  mkFrame (fr_fn fr) (fr_env fr) (fr_locals fr) (fr_doomed fr) pt.

(** Given a called [func] and the list of argument words passed to it,
    [call_frame] builds the callee's initial [frame] with its
    parameter temporaries bound to the leading arguments and its
    declared stack locals unallocated. A variadic function starts at
    [Snapshot] to record all of its arguments in memory, whereas a
    fixed-arity function starts directly at [Enter] on its entry
    block. *)
Definition call_frame (f : func) (xs : list word) : option frame :=
  let params := fn_params f in
  if (length xs <? length params)%nat then None else
  let e := fold_left (fun e px => put (snd (fst px)) (snd px) e)
                     (combine params (firstn (length params) xs)) [] in
  match fn_blocks f with
  | [] => None
  | b :: _ =>
      Some (mkFrame f e (map (fun xs => (fst xs, None)) (local_objects f)) None
                    (if variadic_func f then Snapshot xs (b_label b)
                     else Enter (b_label b) None))
  end.

(** ## The entry argument snapshot

    Entering and leaving a function or a basic block involves three
    pieces of frame housekeeping: storing a variadic call's arguments
    into a read-only snapshot block, binding incoming [[phi]] nodes
    when entering a block, and emptying stack-local regions when a
    function returns. This section defines those helpers so [step] and
    [return_step] can manage frame lifetimes and block entry. *)

(** The constant [va_snapshot] is the hidden environment key where a
    variadic function stores the read-only pointer to its entry
    argument snapshot for `va_args` to read. *)
Definition va_snapshot : name := TApp "hidden" [TAtom "va_snapshot"].

(** Given a list of argument words, a starting byte address, and a
    memory state, [snapshot_values] writes the arguments sequentially
    at 8-byte strides into a newly allocated snapshot block, storing
    both the address bytes and the shadow [[aux]] [[capability]] for
    each pointer argument. *)
Fixpoint snapshot_values (xs : list word) (a : Z) (m : mem) : mem :=
  match xs with
  | [] => m
  | WPtr p :: rest =>
      snapshot_values rest (a + 8) (store_aux (store_bytes m a 8 (ptr_addr p)) a (ptr_cap p))
  | WInt n :: rest => snapshot_values rest (a + 8) (store_bytes m a 8 n)
  | _ :: rest => snapshot_values rest (a + 8) m
  end.

(** Given a run-time [word], [snapshot_word] returns `true` when the
    word is an integer or pointer that [snapshot_values] can store in
    a variadic argument snapshot, and `false` for a limit snapshot. *)
Definition snapshot_word (x : word) : bool :=
  match x with WInt _ | WPtr _ => true | _ => false end.

(** Given a target block label and a list of basic blocks,
    [find_block] returns the first [block] with that label, or `None`
    if no block matches. *)
Fixpoint find_block (l : name) (bs : list block) : option block :=
  match bs with
  | [] => None
  | b :: bs' => if name_eqb (b_label b) l then Some b else find_block l bs'
  end.

(** Given the global environment, a block's [[phi]] list, the
    predecessor label from which the block was entered, and the
    environment on entry, [phis_env] evaluates every phi node's
    incoming operand in the pre-entry environment so that all phi
    temporaries bind simultaneously. Entering the function's entry
    block has no predecessor and requires an empty phi list. *)
Definition phis_env (ge : genv) (phis : list phi) (from : option name) (e0 : env)
  : option env :=
  match from with
  | None => match phis with [] => Some e0 | _ => None end
  | Some pred =>
      fold_left (fun acc ph =>
                   let* e := acc in
                   match ph with
                   | Phi d k pairs =>
                       let* v := lookup pred pairs in
                       let* x := value_x ge e0 k v in
                       Some (put d x e)
                   end) phis (Some e0)
  end.

(** Given a frame's list of named stack locals and the current memory
    state, [invalidate_locals] ends the lifetime of every allocated
    local when the function returns. Each local's object [[identity]],
    data bytes, and shadow capabilities remain in memory, while its
    region bounds become empty and its state becomes [Freed] so any
    later access through a dangling stack pointer traps. *)
Definition invalidate_locals (locals : list (name * option Z)) (m : mem) : option mem :=
  fold_left (fun acc l =>
               let* m := acc in
               match snd l with
               | None => Some m
               | Some base =>
                   let* reg := object_region base (m_regions m) in
                   match r_kind reg, r_life reg with
                   | Stack, Live =>
                       let* rs := replace_region base (mkRegion base base Stack Freed)
                                                 (m_regions m) in
                       Some (mkMem (m_bytes m) rs (m_aux m))
                   | _, _ => None
                   end
               end) locals (Some m).

(** ## Calls

    A direct call in Checked IR invokes a known symbol whose signature
    the validator has checked, whereas an indirect [RawCall] jumps
    through a checked function pointer using Fil-C's
    [[fast-generic-convention|fast generic calling convention]]. This
    section defines the function-pointer check [function_check_res],
    the word-class conversions for indirect arguments and return
    values, and the environment update [returned_env] when a call
    returns. *)

(** Given the global environment and a pointer, [function_check_res]
    checks whether the pointer carries a function [[capability]] [Fn]
    at that function's exact symbol address, trapping with
    [NotAFunction] on any other internal capability or mismatched
    offset and returning `None` for an external symbol capability. *)
Definition function_check_res (ge : genv) (p : ptr) : option (res unit) :=
  match ptr_cap p with
  | Fn f =>
      Some (match lookup f (ge_globals ge) with
            | Some fp => if ptr_addr fp =? ptr_addr p then ok else RTrap NotAFunction
            | None => RTrap NotAFunction
            end)
  | External _ => None
  | _ => Some (RTrap NotAFunction)
  end.

(** Given a call site's [call_result], [result_words] returns the list
    of register [[class|classes]] of the words that the caller reads
    from the return value. *)
Definition result_words (r : call_result) : list class :=
  match r with
  | CVoid => []
  | CResult _ k => [k]
  | CTuple rs => map snd rs
  end.

(** Given a function's [ret_type], [return_words] returns the list of
    register [[class|classes]] of the words that the function returns. *)
Definition return_words (t : ret_type) : list class :=
  match t with
  | RVoid => []
  | RTuple ks => ks
  | RClass k => [k]
  end.

(** The inductive type [word_kind] groups the register classes that
    can cross a function call into four storage kinds: integer words
    [IntWord], pointer words [PtrWord], 32-bit floats [SingleWord],
    and 64-bit floats [DoubleWord]. *)
Inductive word_kind : Type := IntWord | PtrWord | SingleWord | DoubleWord.

(** Given an IR [[class]], [word_class] maps both [W] and [L] to
    [IntWord], maps [P], [Single], and [Double] to their respective
    word kinds, and returns `None` for classes that cannot be passed
    or returned directly. *)
Definition word_class (k : class) : option word_kind :=
  match k with
  | W | L => Some IntWord
  | P => Some PtrWord
  | Single => Some SingleWord
  | Double => Some DoubleWord
  | _ => None
  end.

(** The function [word_kind_eqb] tests whether two call [word_kind]
    values are identical. *)
Definition word_kind_eqb (a b : word_kind) : bool :=
  match a, b with
  | IntWord, IntWord | PtrWord, PtrWord | SingleWord, SingleWord | DoubleWord, DoubleWord => true
  | _, _ => false
  end.

(** Given two lists of register classes, [same_words] returns `true`
    when both lists have the same length and matching [word_class]
    kinds at every position. *)
Definition same_words (ks ks' : list class) : bool :=
  match map_option word_class ks, map_option word_class ks' with
  | Some cs, Some cs' =>
      (length cs =? length cs')%nat && forallb (fun p => word_kind_eqb (fst p) (snd p)) (combine cs cs')
  | _, _ => false
  end.

(** Given a source class, a target class, and a run-time [word],
    [generic_word] converts the word across a mismatch between caller
    and callee signatures under the
    [[fast-generic-convention|generic calling convention]]. Reading an
    integer or float bit pattern as a pointer produces a pointer with
    [CNone], while reading a pointer as an integer or float extracts
    its raw 64-bit address. *)
Definition generic_word (from to : class) (x : word) : option word :=
  match from, to with
  | (W | L | Single | Double), (W | L) => Some x
  | (W | L | Single | Double), P => match x with WInt n => Some (WPtr (mkPtr n CNone)) | _ => None end
  | (W | L | Single | Double), (Single | Double) => word_at_class to x
  | P, (W | L) => let* a := pointer_address x in Some (WInt a)
  | P, P => Some x
  | P, (Single | Double) => let* a := pointer_address x in word_at_class to (WInt a)
  | _, _ => None
  end.

(** A [conv] value represents the result of checking and converting
    arguments for an indirect call: either a safety trap [ConvTrap] on
    an argument or return size mismatch, or [Converted] with the
    converted argument words and any return-value conversion classes. *)
Inductive conv : Type :=
| ConvTrap (why : reason)
| Converted (ys : list word) (words : option (list class * list class)).

(** Given a target [func], a call site's [call_result], the call
    arguments, and their evaluated words, [indirect_call_conv] checks
    that the caller passes enough arguments for the callee's
    parameters and does not read more return words than the callee
    provides, then converts each parameter word with [generic_word]. *)
Definition indirect_call_conv (f : func) (r : call_result) (args : list arg) (xs : list word)
  : option conv :=
  let params := map fst (fn_params f) in
  let np := length params in
  let caller_words := result_words r in
  let callee_words := return_words (fn_ret f) in
  if (length args <? np)%nat then Some (ConvTrap ArgumentSize)
  else if (length callee_words <? length caller_words)%nat then Some (ConvTrap ReturnSize)
  else
    let arg_classes := map (fun a => match a with Arg k _ => k end) (firstn np args) in
    let* ys := map2_option (fun ft x => generic_word (fst ft) (snd ft) x)
                           (combine arg_classes params) (firstn np xs) in
    Some (Converted ys (if same_words caller_words callee_words then None
                        else Some (caller_words, callee_words))).

(** Given a run [outcome], [outcome_words] extracts the list of
    returned words when the outcome is a normal return, and returns
    `None` for any non-returning outcome. *)
Definition outcome_words (o : outcome) : option (list word) :=
  match o with
  | RetVoid => Some []
  | Ret x => Some [x]
  | Rets xs => match xs with _ :: _ :: _ => Some xs | _ => None end
  | _ => None
  end.

(** Given a list of returned words, [words_outcome] packages them back
    into [RetVoid] when empty, [Ret] for a single word, or [Rets] for
    two or more words. *)
Definition words_outcome (ys : list word) : outcome :=
  match ys with
  | [] => RetVoid
  | [y] => Ret y
  | _ => Rets ys
  end.

(** Given the caller's expected return classes, the callee's declared
    return classes, and a callee [outcome], [converted_outcome]
    converts each returned word from the callee's class to the
    caller's class with [generic_word], leaving non-returning outcomes
    unchanged. *)
Definition converted_outcome (caller callee : list class) (o : outcome) : option outcome :=
  match outcome_words o with
  | None => Some o
  | Some xs =>
      let n := length caller in
      if (length xs <? n)%nat || (length callee <? n)%nat then None else
      let* ys := map2_option (fun ft x => generic_word (fst ft) (snd ft) x)
                             (combine (firstn n callee) caller) (firstn n xs) in
      Some (words_outcome ys)
  end.

(** Given a call site's [call_result], a returning [outcome], and the
    caller's [env], [returned_env] coerces each returned word to its
    destination class with [word_at_class] and binds the call's
    destination temporaries in the caller's environment. *)
Definition returned_env (r : call_result) (o : outcome) (e : env) : option env :=
  match o, r with
  | Ret x, CResult d k => let* y := word_at_class k x in Some (put d y e)
  | Ret _, CVoid => Some e
  | Rets xs, CTuple rs =>
      if negb (length xs =? length rs)%nat then None else
      fold_left (fun acc rx =>
                   let* e := acc in
                   let* y := word_at_class (snd (fst rx)) (snd rx) in
                   Some (put (fst (fst rx)) y e)) (combine rs xs) (Some e)
  | Rets _, CVoid => Some e
  | RetVoid, CVoid => Some e
  | _, _ => None
  end.

(** ## Instructions

    Each instruction inside a basic block either updates the current
    frame and memory, stops the run with an outcome, transfers control
    into a called function, or requests a [[fresh]] address from the
    allocator. This section defines the instruction result type
    [inst_out], the single-instruction evaluator [inst_step], and the
    [[doomed]] transition [doomed_result] for early [[check_ahead]]
    failures. *)

(** An [inst_out] describes the immediate effect of executing a single
    instruction: continuing to the next instruction with [IContinue],
    stopping the run with [IStop], invoking a defined function with
    [ICall], requesting a [[fresh]] allocation base with [IFresh], or
    halting on a call to a function outside the
    [[core-subset|core subset]] with [ICallOutside]. *)
Inductive inst_out : Type :=
| IContinue (e : env) (locals : list (name * option Z)) (m : mem)
| IStop (o : outcome)
| ICall (f : func) (xs : list word) (pd : pending)
| IFresh (q : alloc_req) (k : Z -> env * list (name * option Z) * mem)
| ICallOutside (f : name).

(** Given a destination temporary name, a partial operation result
    [res], and the current environment, locals, and memory, [bind_res]
    binds the temporary and continues on [RVal], or stops the run with
    [Trap] or [Unchecked] on failure. *)
Definition bind_res (d : name) (r : res word) (e : env) locals (m : mem) : inst_out :=
  match r with
  | RVal x => IContinue (put d x e) locals m
  | RTrap why => IStop (Trap why)
  | RUnchecked why => IStop (Unchecked why)
  end.

(** Given a partial unit result from a memory store and the current
    environment, locals, and memory, [store_out] continues with the
    updated memory on [RVal] and stops with [Trap] or [Unchecked] on
    failure. *)
Definition store_out (r : res unit) (e : env) locals (m : mem) : inst_out :=
  match r with
  | RVal _ => IContinue e locals m
  | RTrap why => IStop (Trap why)
  | RUnchecked why => IStop (Unchecked why)
  end.

(** Given a memory store [width], [width_value_class] returns the
    register [[class]] at which a [RawStore] evaluates its value
    operand before truncating and writing the bytes. *)
Definition width_value_class (w : width) : option class :=
  match w with
  | Wb | Wh | Ww => Some W
  | Wl => Some L
  | Wp => Some P
  | Ws => Some Single
  | Wd => Some Double
  | Wx => Some Extended
  end.

(** The constant [free_name] is the symbol name of the standard C
    deallocator `c: free`, which the semantics executes directly as a
    built-in [[external call]]. *)
Definition free_name : name := TAtom "free".

(** The constant [zgc_free_name] is the symbol name of libpizlo's
    `c: zgc_free` deallocator, which the semantics executes in the
    same way as [free_name]. *)
Definition zgc_free_name : name := TAtom "zgc_free".

(** Given a symbol [name], [is_free_name] returns `true` when the
    symbol is either [free_name] or [zgc_free_name]. *)
Definition is_free_name (f : name) : bool := name_eqb f free_name || name_eqb f zgc_free_name.

(** Given a call to a symbol not defined as a function in the module,
    [external_call] traps with [NotAFunction] if the symbol names a
    global data object, runs `ge_free` from the global environment
    when the symbol satisfies [is_free_name] with a single pointer
    argument, and returns `None` for any other external symbol. *)
Definition external_call (ge : genv) (f : name) (r : call_result) (args : list arg)
    (xs : list word) (e : env) locals (m : mem) : option inst_out :=
  match lookup f (ge_globals ge) with
  | Some _ => Some (IStop (Trap NotAFunction))
  | None =>
      if negb (is_free_name f) then None
      else match r, args, xs with
           | CVoid, [Arg P _], [x] =>
               let* rm := ge_free ge x m in
               let (r', m') := rm in
               Some (match r' with
                     | RVal _ => IContinue e locals m'
                     | RTrap why => IStop (Trap why)
                     | RUnchecked why => IStop (Unchecked why)
                     end)
           | _, _, _ => None
           end
  end.

(** Given the global environment, the active [frame], the current
    memory state, and an instruction in the
    [[core-subset|core subset]], [inst_step] evaluates the instruction
    to an [inst_out], or returns `None` when an operand is unassigned
    or ill-classed or accesses an external capability. *)
Definition inst_step (ge : genv) (fr : frame) (m : mem) (i : inst) : option inst_out :=
  let e := fr_env fr in
  let locals := fr_locals fr in
  match i with
  | Loc _ _ => Some (IContinue e locals m)
  | Touch _ => Some (IContinue e locals m)
  | LocalAlloc x size =>
      match lookup x locals with
      | Some None =>
          let q := local_req size in
          Some (IFresh q (fun base => (e, put x (Some base) locals, allocated m q base)))
      | _ => None
      end
  | Let d A (CheckLocal x off size r al) [] =>
      let* slot := lookup x locals in
      let* base := slot in
      let a := base + off in
      let* chk := access_res m a (Obj base) size r al in
      Some (bind_res d (checked_res chk (WPtr (mkPtr a (Obj base)))) e locals m)
  | Flight d o args lw =>
      let* xs := map_option (flight_arg_x ge e) args in
      let* a := alu o L xs in
      let* c := flight_cap ge e lw in
      match a with
      | WInt n => Some (IContinue (put d (WPtr (mkPtr n c)) e) locals m)
      | _ => None
      end
  | Let d P VaArgs [Const off] =>
      let* x := lookup va_snapshot e in
      match x with
      | WPtr p => Some (IContinue (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e)
                                  locals m)
      | _ => None
      end
  | Let d F CheckFunction [v] =>
      let* x := value_x ge e P v in
      match x with
      | WPtr p => let* chk := function_check_res ge p in
                  Some (bind_res d (checked_res chk x) e locals m)
      | _ => None
      end
  | Let d k o args =>
      match o with CheckLocal _ _ _ _ _ | CheckFunction | VaArgs => None | _ =>
      let* classes := op_arg_classes o k in
      let* xs := map2_option (value_x ge e) classes args in
      let* out := op_res o k xs m in
      match out with
      | OpRes r m' => Some (bind_res d r e locals m')
      | OpUB why => Some (IStop (UB why))
      | OpAlloc q kont =>
          Some (IFresh q (fun base => let (x, m') := kont base in (put d x e, locals, m')))
      end
      end
  | RawStore w off v a =>
      let* vk := width_value_class w in
      let* x := value_x ge e vk v in
      let* pa := value_x ge e A a in
      match pa with
      | WPtr p =>
          let* rm := store_res w m (raw_address (ptr_addr p) off) (ptr_cap p) x in
          let (r, m') := rm in
          Some (store_out (raw_res r) e locals m')
      | _ => None
      end
  | RawStorePointer off v a es =>
      let* x := value_x ge e P v in
      let* pa := value_x ge e A a in
      match pa with
      | WPtr p =>
          let b := raw_address (ptr_addr p) off in
          let* chk := access_res m b (ptr_cap p) 8 Write 8 in
          match chk with
          | RVal _ =>
              match x with
              | WPtr xp => let* m' := pointer_store_effects b xp m es in
                           Some (IContinue e locals m')
              | _ => None
              end
          | RTrap why | RUnchecked why => Some (IStop (Unchecked why))
          end
      | _ => None
      end
  | Call r (Global f) args =>
      let* xs := map_option (arg_x ge e) args in
      match find_fn ge f with
      | Some (Defined g) => Some (ICall g xs (mkPending r None))
      | Some (Outside g) => Some (ICallOutside g)
      | None => external_call ge f r args xs e locals m
      end
  | Call _ _ _ => None
  | RawCall r callee args =>
      let* x := value_x ge e F callee in
      let* xs := map_option (arg_x ge e) args in
      match x with
      | WPtr p =>
          let* chk := function_check_res ge p in
          match raw_res chk with
          | RTrap why | RUnchecked why => Some (IStop (Unchecked why))
          | RVal _ =>
              match ptr_cap p with
              | Fn g =>
                  match find_fn ge g with
                  | Some (Defined gf) =>
                      let* cv := indirect_call_conv gf r args xs in
                      match cv with
                      | ConvTrap why => Some (IStop (Trap why))
                      | Converted ys words =>
                          (* A variadic callee receives any extra arguments
                             unconverted after its fixed parameters. *)
                          let extra := if variadic_func gf
                                       then skipn (length (fn_params gf)) xs else [] in
                          Some (ICall gf (ys ++ extra) (mkPending r words))
                      end
                  | Some (Outside g') => Some (ICallOutside g')
                  | None => None
                  end
              | _ => None
              end
          end
      | _ => None
      end
  end.

(** Given the global environment, the active [frame], memory, the
    executed instruction, and its raw [inst_out], [doomed_result]
    updates the result and the frame's [[doomed]] state. When a
    [[check_ahead]] fails only on its lookahead bytes with [Early],
    the instruction still binds the checked pointer and marks the
    frame as doomed with that trap reason; when a later
    [[raw-access|raw access]] in that doomed frame fails its
    capability check, [doomed_result] turns that fault into the
    deferred [Early] [[trap]]. *)
Definition doomed_result (ge : genv) (fr : frame) (m : mem) (i : inst) (out : inst_out)
  : option (inst_out * option reason) :=
  match i, out with
  | Let d A (CheckAhead _ _ _ _ _) [v], IStop (Trap (Early why)) =>
      let* p := value_x ge (fr_env fr) P v in
      Some (IContinue (put d p (fr_env fr)) (fr_locals fr) m,
            match fr_doomed fr with Some w => Some w | None => Some why end)
  | _, IStop (Unchecked w) =>
      match fr_doomed fr, w with
      | Some why, (Alias | WhyLimit) => Some (out, fr_doomed fr)
      | Some why, _ => Some (IStop (Trap (Early why)), fr_doomed fr)
      | None, _ => Some (out, None)
      end
  | _, _ => Some (out, fr_doomed fr)
  end.

(** ## Steps

    We now combine frame entry, instruction execution, control-flow
    jumps, and function return into the single-step evaluator [step].
    This section defines the step outcome type [step_result] and the
    helper transitions for returns, edges, jumps, and instructions
    that [step] dispatches on. *)

(** A [step_result] is the outcome of taking one small [[step]] from a
    machine configuration: advancing to a new configuration with
    [Next], finishing the run with [Done], requesting a [[fresh]]
    allocation base with [Fresh], or halting with [Stuck] when
    execution reaches an unmodeled external symbol or an ill-formed
    state. *)
Inductive step_result : Type :=
| Next (c : config)
| Done (o : outcome)
| Fresh (q : alloc_req) (k : Z -> config)
| Stuck (why : string).

(** Given a diagnostic label and an optional [step_result], [or_stuck]
    unwraps a present result and turns `None` into [Stuck] with that
    label. *)
Definition or_stuck (why : string) (r : option step_result) : step_result :=
  match r with Some s => s | None => Stuck why end.

(** Given a configuration, an updated [frame], a memory state, and a
    remaining fuel count, [continue_at] builds the next [config] while
    keeping the suspended caller stack unchanged. *)
Definition continue_at (c : config) (fr : frame) (m : mem) (fuel : Z) : config :=
  mkConfig fr (c_callers c) m fuel.

(** Given the current configuration and a returning [outcome],
    [return_step] invalidates the returning frame's stack locals with
    [invalidate_locals] and either finishes the run with [Done] when
    the caller stack is empty, or converts and binds the return value
    in the top caller frame and resumes that caller. *)
Definition return_step (c : config) (o : outcome) : step_result :=
  let fr := c_frame c in
  or_stuck "return" (
    let* m := invalidate_locals (fr_locals fr) (c_mem c) in
    match c_callers c with
    | [] => Some (Done o)
    | (caller, pd) :: callers =>
        let* o' := match pd_conv pd with
                   | None => Some o
                   | Some (cw, kw) => converted_outcome cw kw o
                   end in
        let* e := returned_env (pd_res pd) o' (fr_env caller) in
        Some (Next (mkConfig (mkFrame (fr_fn caller) e (fr_locals caller)
                                      (fr_doomed caller) (fr_at caller))
                             callers m (c_fuel c)))
    end).

(** Given a configuration, the current block label, and a jump
    [target], [edge_step] transitions the active frame to [Enter] at
    the target block, or stops with an [[unchecked]] [Ahead] fault if
    a [[doomed]] frame reaches a [[poll|poll edge]] before the
    anticipated access. *)
Definition edge_step (c : config) (from : name) (t : target) : step_result :=
  let fr := c_frame c in
  match t, fr_doomed fr with
  | Poll _, Some why => Done (Unchecked (Ahead why))
  | _, _ => Next (continue_at c (with_point fr (Enter (edge_label t) (Some from)))
                              (c_mem c) (c_fuel c))
  end.

(** Given the global environment, the current configuration, the
    current block label, and the block's terminating [jump],
    [jump_step] takes an unconditional or conditional branch with
    [edge_step] or returns from the function with [return_step]. If
    the frame is currently [[doomed]], attempting to return or execute
    [JUnreachable] before the anticipated access fails stops with an
    [[unchecked]] [Ahead] fault. *)
Definition jump_step (ge : genv) (c : config) (l : name) (j : jump) : step_result :=
  let fr := c_frame c in
  let e := fr_env fr in
  match fr_doomed fr, j with
  | Some why, (JRet _ | JRets _ | JRetVoid | JUnreachable) =>
      Done (Unchecked (Ahead why))
  | _, JGoto t => edge_step c l t
  | _, JBranch v t1 t2 =>
      or_stuck "branch" (
        let* x := value_x ge e W v in
        match x with
        | WInt n => Some (edge_step c l (if n =? 0 then t2 else t1))
        | _ => None
        end)
  | _, JRet v =>
      or_stuck "ret" (
        match fn_ret (fr_fn fr) with
        | RClass k => let* x := value_x ge e k v in Some (return_step c (Ret x))
        | _ => None
        end)
  | _, JRets vs =>
      or_stuck "rets" (
        match fn_ret (fr_fn fr) with
        | RTuple ks => let* xs := map2_option (value_x ge e) ks vs in
                       Some (return_step c (Rets xs))
        | _ => None
        end)
  | _, JRetVoid => return_step c RetVoid
  | _, JUnreachable => Done Unreachable
  end.

(** Given the current configuration, the enclosing block label, the
    remaining instructions and terminating jump of the block, an
    instruction's [inst_out], and the updated doom state, [inst_next]
    constructs the resulting [step_result]. Depending on the
    instruction outcome, it advances to the rest of the block,
    finishes the run, suspends the caller to enter a callee frame, or
    requests a fresh allocation base. *)
Definition inst_next (c : config) (l : name) (rest : list inst) (j : jump)
    (out : inst_out) (doomed : option reason) : step_result :=
  let fr := c_frame c in
  let at_rest (e : env) locals := mkFrame (fr_fn fr) e locals doomed (Exec l rest j) in
  match out with
  | IContinue e locals m' => Next (mkConfig (at_rest e locals) (c_callers c) m' (c_fuel c))
  | IStop o => Done o
  | ICall g xs pd =>
      match call_frame g xs with
      | Some callee =>
          Next (mkConfig callee ((at_rest (fr_env fr) (fr_locals fr), pd) :: c_callers c)
                         (c_mem c) (c_fuel c))
      | None => Stuck "call"
      end
  | IFresh q k =>
      Fresh q (fun base =>
                 match k base with
                 | (e, locals, m') => mkConfig (at_rest e locals) (c_callers c) m' (c_fuel c)
                 end)
  | ICallOutside _ => Stuck "outside the core subset"
  end.

(** Given the global environment and a machine configuration, [step]
    executes one small step of the operational semantics according to
    the active frame's execution [point]. At [Snapshot] it allocates
    the read-only argument buffer for a variadic call, at [Enter] it
    spends one unit of [[fuel]] and binds the block's [[phi]] nodes,
    and at [Exec] it either runs the next instruction or takes the
    block's terminating jump once no instructions remain. *)
Definition step (ge : genv) (c : config) : step_result :=
  let fr := c_frame c in
  let m := c_mem c in
  match fr_at fr with
  | Snapshot xs l =>
      (* When a variadic call passes no arguments, its snapshot pointer
         is null; otherwise a fresh 16-byte-aligned read-only object
         holds the argument words. *)
      let enter e m' := mkConfig (mkFrame (fr_fn fr) (put va_snapshot e (fr_env fr)) (fr_locals fr)
                                          (fr_doomed fr) (Enter l None))
                                 (c_callers c) m' (c_fuel c) in
      match xs with
      | [] => Next (enter (WPtr (mkPtr 0 CNone)) m)
      | _ =>
          if negb (forallb snapshot_word xs) then Stuck "snapshot" else
          let q := heap_req 16 (8 * Z.of_nat (length xs)) in
          Fresh q (fun base => enter (WPtr (mkPtr base (Ro base)))
                                     (snapshot_values xs base (allocated m q base)))
      end
  | Enter l from =>
      (* Entering a basic block consumes one unit of fuel before
         evaluating the block's phi nodes. *)
      if c_fuel c =? 0 then Done OutOfFuel else
      or_stuck "block" (
        let* b := find_block l (fn_blocks (fr_fn fr)) in
        let* e := phis_env ge (b_phis b) from (fr_env fr) in
        Some (Next (mkConfig (mkFrame (fr_fn fr) e (fr_locals fr) (fr_doomed fr)
                                      (Exec l (b_insts b) (b_jump b)))
                             (c_callers c) m (c_fuel c - 1))))
  | Exec l [] j => jump_step ge c l j
  | Exec l (i :: rest) j =>
      (* A doomed frame faults immediately if it reaches an instruction
         that is not ahead-transparent before the anticipated access. *)
      let stop := match fr_doomed fr with
                  | Some why => if ahead_transparent i then None else Some why
                  | None => None
                  end in
      match stop with
      | Some why => Done (Unchecked (Ahead why))
      | None =>
          or_stuck "instruction" (
            let* out0 := inst_step ge fr m i in
            let* od := doomed_result ge fr m i out0 in
            Some (inst_next c l rest j (fst od) (snd od)))
      end
  end.

(** ## The step relation

    While [step] is a deterministic function for ordinary transitions,
    heap and stack allocations return a [Fresh] request that leaves
    the choice of the new object's base address open. This section
    turns [step] into the nondeterministic transition relation
    [step_rel], defines terminal configurations with [final], and
    takes the reflexive-transitive closure in [reachable]. *)

(** The inductive relation [step_rel] relates a configuration to any
    configuration that can follow it in one step, either
    deterministically via [Next] or by choosing any [fresh] base
    address in memory for a [Fresh] allocation request. *)
Inductive step_rel (ge : genv) : config -> config -> Prop :=
| step_next : forall c c', step ge c = Next c' -> step_rel ge c c'
| step_fresh : forall c q k base,
    step ge c = Fresh q k -> fresh (c_mem c) q base -> step_rel ge c (k base).

(** A configuration satisfies [final] for an [outcome] when [step]
    terminates immediately in that configuration with [Done]. *)
Definition final (ge : genv) (c : config) (o : outcome) : Prop := step ge c = Done o.

(** The relation [reachable] is the reflexive-transitive closure of
    [step_rel], relating an initial configuration to any configuration
    it can reach in zero or more steps. *)
Definition reachable (ge : genv) : config -> config -> Prop :=
  clos_refl_trans config (step_rel ge).
