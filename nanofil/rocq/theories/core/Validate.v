(** Before a compiled module runs, the [[validator]] checks that every
    [[raw-access|raw memory access]] in a [[stage|checked-IR]] function is
    covered by a dominating [[capability]] [[check]] or [[reuse]] form.
    This module transcribes the Prolog validator from `ir.pl` for the
    [[core-subset|core subset]] in Fil-C [[mode]]: [valid_func] accepts a
    function when every instruction, jump, and [[phi]] node is well typed,
    every temporary use is dominated by a definition, and every raw access
    is justified by live capability [[evidence]]. The companion functions
    [valid_data] and [valid_alias] check the module's global data objects
    and symbol aliases.

    In `ir.pl`, the validator stops at the first error by throwing a
    Prolog exception and fails on terms outside the grammar, whereas the
    boolean functions in this module return `false` in both cases. Because
    all checks are combined with boolean conjunction, the definitions
    below are grouped by topic rather than evaluation order. In the three
    places where Prolog's evaluation order or cuts affect the result,
    [oi], [op_interval], and [pointer_distance] follow the exact traversal
    and commitment order of `ir.pl`.

    After checking static single-assignment [[dominance]], register
    [[class|classes]], and stack-local declarations, the validator
    verifies memory safety on checked-IR functions. Every raw load or
    store must be authorized either by an immediately preceding capability
    [[check]] or by an earlier check whose capability bounds still cover
    the access on every incoming control-flow path, and every loop must
    pass through a garbage-collection [[poll]] safepoint. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Syntax Values Memory Ops Semantics Cfg.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Names, uses and definitions

    Before checking dominance or types, the validator needs to know which
    [[temporary|temporaries]] each instruction, [[phi]] node, and jump
    defines or reads, and which control-flow edges leave each block. This
    section defines those syntax queries along with basic equality tests
    on names and operand values. *)

(** Given a temporary name n and a list of names ns, [mem] returns `true`
    when n appears in ns. *)
Definition mem (n : name) (ns : list name) : bool := existsb (name_eqb n) ns.

(** Given two operand values v and w, [value_eqb] tests whether both name
    the same temporary, the same global symbol, or the same integer
    constant. *)
Definition value_eqb (v w : value) : bool :=
  match v, w with
  | Tmp a, Tmp b | Global a, Global b => name_eqb a b
  | Const a, Const b => Z.eqb a b
  | _, _ => false
  end.

(** Given a list of operand values vs, [value_temps] extracts the names of
    all [[temporary]] operands in order and drops constants and global
    symbols. *)
Definition value_temps (vs : list value) : list name :=
  flat_map (fun v => match v with Tmp n => [n] | _ => [] end) vs.

(** Given an instruction i, [inst_temp_defs] returns the list of
    [[temporary|temporaries]] that i defines paired with their register
    [[class]], covering `let` destinations, [[flight]] destinations, and
    call results. *)
Definition inst_temp_defs (i : inst) : list (name * class) :=
  match i with
  | Let d k _ _ => [(d, k)]
  | Flight d _ _ _ => [(d, P)]
  | Call r _ _ | RawCall r _ _ =>
      match r with CVoid => [] | CResult d k => [(d, k)] | CTuple rs => rs end
  | _ => []
  end.

(** Given an instruction i, [inst_def_first] returns the first
    [[temporary]] that i defines, or `None` when the instruction defines
    no temporary. *)
Definition inst_def_first (i : inst) : option name :=
  match inst_temp_defs i with (d, _) :: _ => Some d | [] => None end.

(** Given a typed call argument a, [arg_value] extracts its operand
    value. *)
Definition arg_value (a : arg) : value := match a with Arg _ v => v end.
(** Given a typed call argument a, [arg_class] extracts the register
    [[class]] at which the argument is passed. *)
Definition arg_class (a : arg) : class := match a with Arg k _ => k end.

(** Given a [[flight]] argument a, [flight_arg_value] extracts the
    underlying operand value whether a marks the address operand or a
    plain offset value. *)
Definition flight_arg_value (a : flight_arg) : value :=
  match a with FValue v => v | FAddress p => p end.

(** Given an instruction i, [inst_uses] returns all [[temporary]] names
    that i reads, including the [[lower]] donor of a [[flight]] and the
    callee and arguments of a call. *)
Definition inst_uses (i : inst) : list name :=
  match i with
  | Let _ _ _ args => value_temps args
  | Flight _ _ args lw =>
      value_temps (map flight_arg_value args
                   ++ match lw with LowerOf p => [p] | LowerNone => [] end)
  | RawStore _ _ v a | RawStorePointer _ v a _ => value_temps [v; a]
  | Call _ f args | RawCall _ f args => value_temps (f :: map arg_value args)
  | Touch q => [q]
  | LocalAlloc _ _ | Loc _ _ => []
  end.

(** Given a block-ending jump j, [jump_uses] returns the [[temporary]]
    names that j reads, such as a branch condition or return values. *)
Definition jump_uses (j : jump) : list name :=
  match j with
  | JBranch v _ _ | JRet v => value_temps [v]
  | JRets vs => value_temps vs
  | _ => []
  end.

(** Given a block-ending jump j, [jump_targets] lists the outgoing
    control-flow edges of j, returning one target for a `goto`, two for a
    `branch`, and none for a return. *)
Definition jump_targets (j : jump) : list target :=
  match j with JGoto t => [t] | JBranch _ t1 t2 => [t1; t2] | _ => [] end.

(** Given a block-ending jump j, [succ_labels] returns the target
    [[block]] labels of all outgoing edges of j, including [[poll]]
    edges. *)
Definition succ_labels (j : jump) : list name := map edge_label (jump_targets j).

(** Given a jump target edge t, [is_poll] returns `true` when t is a
    [[poll]] edge that passes through a garbage-collection safepoint
    before entering the target block. *)
Definition is_poll (t : target) : bool := match t with Poll _ => true | To _ => false end.

(** ## Dominance

    In [[ssa|strict SSA]] form, every use of a [[temporary]] must be
    reached only through control-flow paths that first pass a definition
    of that temporary. Using the dominator-tree intervals from
    [Cfg](Cfg.v), this section collects every [[site|definition site]] in
    a function and checks that each instruction, jump, and [[phi]] operand
    is [[dominance|dominated]] by at least one definition of the temporary
    it reads. *)

(** Given a list of blocks bs and a block label l, [preds_of] returns the
    labels of all blocks in bs whose jump targets include l, whether or
    not those predecessor blocks are reachable. *)
Definition preds_of (bs : list block) (l : name) : list name :=
  map b_label (filter (fun b => mem l (succ_labels (b_jump b))) bs).

(** Given two label lists a and b, [sets_eqb] tests whether every label in
    a appears in b and every label in b appears in a, regardless of order
    or duplicates. *)
Definition sets_eqb (a b : list name) : bool :=
  forallb (fun x => mem x b) a && forallb (fun x => mem x a) b.

(** Given the dominator-tree interval map doms computed by
    [block_intervals], [dominates] returns `true` when block a
    [[dominance|dominates]] block b. *)
Definition dominates (doms : nmap (Z * Z)) (a b : name) : bool := dominates_by_interval doms a b.

(** Given the dominator-tree interval map doms and a block label l,
    [is_reachable] returns `true` when l is reachable from the function's
    entry block and therefore has an interval in doms. *)
Definition is_reachable (doms : nmap (Z * Z)) (l : name) : bool := nm_mem l doms.

(** A [site] records where a [[temporary]] is defined in a function:
    [SParam] marks a function parameter, while [SAt] records a block label
    l and an instruction index i, using `-1` for [[phi]] nodes at the top
    of the block. *)
Inductive site : Type := SParam | SAt (l : name) (i : Z).

(** Given a function f, [temp_sites] builds a [[name-map|name map]] from
    each [[temporary]] name to the list of all [[site|definition sites]]
    where f defines that name. A temporary may have more than one
    definition site so long as at least one definition dominates every
    reachable use in [definitions_dominate]. *)
Definition temp_sites (f : func) : nmap (list site) :=
  let add (m : nmap (list site)) (n : name) (s : site) :=
    nm_add n (s :: match nm_find n m with Some ss => ss | None => [] end) m in
  let m0 := fold_left (fun m p => add m (snd p) SParam) (fn_params f) nm_empty in
  fold_left (fun m b =>
               let m1 := fold_left (fun m ph => match ph with Phi d _ _ => add m d (SAt (b_label b) (-1)) end)
                                   (b_phis b) m in
               fst (fold_left (fun (acc : nmap (list site) * Z) ins =>
                                 let (m, j) := acc in
                                 (fold_left (fun m dk => add m (fst dk) (SAt (b_label b) j))
                                            (inst_temp_defs ins) m, j + 1))
                              (b_insts b) (m1, 0)))
            (fn_blocks f) m0.

(** Given a dominator map doms, a block label l, an instruction position
    i, and a definition site s, [site_dominates] tests whether s precedes
    position i of block l on every path from the entry block. Function
    parameters dominate every position, definitions in block l itself
    dominate later positions with a larger index, and definitions in
    another block dominate position i when their block
    [[dominance|dominates]] l. *)
Definition site_dominates (doms : nmap (Z * Z)) (l : name) (i : Z) (s : site) : bool :=
  match s with
  | SParam => true
  | SAt d j => if name_eqb d l then j <? i else dominates doms d l
  end.

(** Given the definition-site map sites, the dominator map doms, a block
    label l, and an instruction index i, [dominated_use] checks that at
    least one definition site of temporary n dominates position i of block
    l. *)
Definition dominated_use (sites : nmap (list site)) (doms : nmap (Z * Z)) (l : name) (i : Z)
    (n : name) : bool :=
  match nm_find n sites with
  | Some defs => existsb (site_dominates doms l i) defs
  | None => false
  end.

(** Given a function f and its dominator intervals doms,
    [definitions_dominate] enforces the [[ssa|strict SSA]] rule across all
    reachable blocks of f. Every temporary read by an instruction or jump
    must be [[dominance|dominated]] at its use position by a definition,
    and every temporary read from a reachable predecessor by a [[phi]]
    node must be dominated at the end of that predecessor block. *)
Definition definitions_dominate (f : func) (doms : nmap (Z * Z)) : bool :=
  let sites := temp_sites f in
  let ends := nm_of_list (map (fun b => (b_label b, Z.of_nat (length (b_insts b)))) (fn_blocks f)) in
  let dominated_use := dominated_use sites in
  forallb (fun b =>
             if negb (is_reachable doms (b_label b)) then true else
             let l := b_label b in
             let fix insts (is : list inst) (i : Z) : bool :=
               match is with
               | [] => forallb (dominated_use doms l i) (jump_uses (b_jump b))
               | ins :: rest => forallb (dominated_use doms l i) (inst_uses ins)
                                && insts rest (i + 1)
               end in
             insts (b_insts b) 0 &&
             forallb (fun ph =>
                        match ph with
                        | Phi _ _ pairs =>
                            forallb (fun pv =>
                                       match snd pv with
                                       | Tmp n =>
                                           if is_reachable doms (fst pv) then
                                             match nm_find (fst pv) ends with
                                             | Some e => dominated_use doms (fst pv) e n
                                             | None => true
                                             end
                                           else true
                                       | _ => true
                                       end) pairs
                        end) (b_phis b))
          (fn_blocks f).

(** ## Classes of temporaries

    Every [[temporary]] in a function carries a register [[class]] that
    determines whether it holds an integer, a floating-point number, a
    Fil-C pointer, or a capability [[proof]]. This section verifies that
    every definition of a temporary assigns it the same class and that
    each operand is read at a class compatible with its definition. *)

(** Given a function f, [temp_defs] collects every temporary definition in
    f as a pair of temporary name and register [[class]], starting with
    the function parameters and continuing through each block's [[phi]]
    nodes and instructions. *)
Definition temp_defs (f : func) : list (name * class) :=
  map (fun p => (snd p, fst p)) (fn_params f) ++
  flat_map (fun b => map (fun ph => match ph with Phi d k _ => (d, k) end) (b_phis b)
                     ++ flat_map inst_temp_defs (b_insts b)) (fn_blocks f).

(** Given a list of temporary definitions defs, [temp_classes_ok] verifies
    that every definition of the same temporary name assigns it the exact
    same register [[class]] as its first definition. *)
Definition temp_classes_ok (defs : list (name * class)) : bool :=
  let first := fold_left (fun m d => if nm_mem (fst d) m then m else nm_add (fst d) (snd d) m)
                         defs nm_empty in
  forallb (fun d => match nm_find (fst d) first with
                    | Some k => class_eqb k (snd d)
                    | None => false
                    end) defs.

(** In checked IR, capability checks produce [[proof]] values that
    authorize memory accesses or calls and cannot be forged by arithmetic.
    The function [proof_class] returns `true` for the two proof classes:
    memory-access proofs and function-call proofs. *)
Definition proof_class (k : class) : bool := match k with A | F => true | _ => false end.

(** Given the temporary-class table classes, a required [[class]] k, and
    an operand value v, [valid_use] tests whether an instruction or jump
    may read v at class k. A [[proof]], floating-point, or pointer
    temporary may be read only at its own class, while a 64-bit long
    integer temporary may also be read as a 32-bit word. Integer and
    floating-point constants are allowed for non-proof classes when their
    bit patterns fit the class modulus, whereas global symbols are
    rejected here because only a pointer `copy` instruction may read a
    symbol directly in [valid_inst]. *)
Definition valid_use (classes : list (name * class)) (k : class) (v : value) : bool :=
  match v with
  | Tmp n =>
      match lookup n classes with
      | None => false
      | Some k0 =>
          if proof_class k || proof_class k0 then class_eqb k k0
          else if float_class k || float_class k0 then class_eqb k k0
          else if class_eqb k L && class_eqb k0 W then false
          else if class_eqb k0 P then class_eqb k P
          else if class_eqb k P then false
          else true
      end
  | Const n =>
      if float_class k then match modulus k with Some m => (0 <=? n) && (n <? m) | None => false end
      else negb (proof_class k)
  | Global _ => false
  end.

(** ## Ops

    Each `let` instruction runs an operation from [Syntax](Syntax.v) that
    carries immediate parameters, such as byte bounds, alignments, or
    memory effect lists, and produces a result of a specific [[class]].
    This section checks that those operation parameters are well formed
    and that the operation may define a temporary of the requested result
    class. *)

(** Given an alignment al in bytes, [check_align] tests whether al is one
    of the alignments that a capability [[check]] may prove: 1, 2, 4, 8,
    or 16 bytes. *)
Definition check_align (al : Z) : bool :=
  existsb (Z.eqb al) [1; 2; 4; 8; 16].

(** Given an alignment al in bytes, [alloc_align] tests whether al is a
    power of two between 4 and 4096, which are the alignments that a heap
    [[alloc]] instruction accepts. *)
Definition alloc_align (al : Z) : bool :=
  (4 <=? al) && (al <=? 4096) && (Z.land al (al - 1) =? 0).

(** Given a lower byte offset lo, an upper byte offset hi, and an
    alignment al, [check_ok] verifies that the span is non-empty and that
    al satisfies [check_align]. *)
Definition check_ok (lo hi al : Z) : bool := (lo <? hi) && check_align al.

(** Given a byte offset off, [local_offset] tests whether off fits in a
    signed 64-bit integer. *)
Definition local_offset (off : Z) : bool := (- 2 ^ 63 <=? off) && (off <? 2 ^ 63).

(** Storing a pointer into a heap object updates both primary memory and
    the object's shadow [[aux]] capability slot while cooperating with the
    garbage collector. The effect list [store_effects] records the five
    steps that a heap pointer store declares for that protocol. *)
Definition store_effects : list effect :=
  [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite].
(** Stack-allocated local objects already have shadow [[aux]] space
    reserved in the stack frame and do not need heap allocation or
    write-barrier steps. The effect list [local_store_effects] therefore
    records only writing the capability [[lower]] and the pointer
    address. *)
Definition local_store_effects : list effect := [LowerWrite; AddressWrite].
(** An atomic pointer load delegates its memory protocol to the Fil-C
    runtime helper and declares the single effect [atomic_load_effects]. *)
Definition atomic_load_effects : list effect := [AtomicRead].
(** An atomic pointer store delegates its memory protocol to the Fil-C
    runtime helper and declares the single effect
    [atomic_store_effects]. *)
Definition atomic_store_effects : list effect := [AtomicWrite].

(** Given a comparison condition c and an operand [[class]] k,
    [comparison] tests whether c can compare values of class k. Signed and
    unsigned ordering conditions apply to integers, ordered and unordered
    floating-point conditions apply to floats, and equality and inequality
    apply to both. *)
Definition comparison (c : cond) (k : class) : bool :=
  match c with
  | Eq | Ne => int_class k || float_class k
  | Sle | Slt | Sge | Sgt | Ule | Ult | Uge | Ugt => int_class k
  | Le | Lt | Ge | Gt | Ord | Unord => float_class k
  end.

(** Given an operation o from the [[core-subset|core subset]], [valid_op]
    checks that the immediate parameters carried by o are well formed.
    Capability [[check]] and [[reuse]] operations must satisfy [check_ok],
    [[check_ahead]] must also place its early bound strictly inside its
    full span, [[span_test]] and [[limit]] must carry in-range bounds, and
    raw pointer loads must declare heap, local, or atomic memory
    effects. *)
Definition valid_op (o : op) : bool :=
  match o with
  | Cmp c k => comparison c k
  | Alloc al => alloc_align al
  | Check lo hi _ al | Renew lo hi _ al | RenewHull lo hi _ al | RenewIf lo hi _ al
  | CheckLimit lo hi _ al | HalfCheck _ lo hi _ al => check_ok lo hi al
  | CheckAhead lo hi _ al ahi => check_ok lo hi al && (lo <? ahi) && (ahi <? hi)
  | SpanTest lo hi => (lo <? hi) && (- 2 ^ 63 <=? lo) && (hi <=? 2 ^ 63 - 1)
  | Limit size => (0 <? size) && (size <=? 2 ^ 31 - 1)
  | CheckLocal _ off bytes _ al =>
      local_offset off && (0 <? bytes) && (bytes <=? 2 ^ 31 - 1) && check_align al
  | RawLoadPointer _ es =>
      effects_eqb es load_effects || effects_eqb es local_load_effects
      || effects_eqb es atomic_load_effects
  | _ => true
  end.

(** Given a register [[class]] k, [any_class] returns `true` when k is an
    ordinary value class rather than one of the capability [[proof]]
    classes in [proof_class]. *)
Definition any_class (k : class) : bool := negb (proof_class k).

(** Given an operation o and a destination [[class]] k, [op_result_ok]
    tests whether a `let` instruction running o in Fil-C [[mode]] may
    define a temporary of class k. Arithmetic, conversion, and raw-load
    operations must produce a matching integer, floating-point, or pointer
    class, capability [[check]] and [[reuse]] forms must produce a
    memory-access [[proof]], and `check_function` must produce a
    function-call proof. *)
Definition op_result_ok (o : op) (k : class) : bool :=
  match o with
  | Add | Sub | Copy => any_class k
  | Mul | Div => int_class k || float_class k
  | Udiv | Rem | Urem | And | Or | Xor | Sar | Shr | Shl => int_class k
  | Neg => int_class k || float_class k
  | Select => int_class k
  | Ptoi => class_eqb k L
  | Itop => class_eqb k P
  | Cmp _ ck => if float_class ck then class_eqb k W else int_class k
  | Ext t => match t with Sw | Uw => class_eqb k L | _ => int_class k end
  | ExtF Single => class_eqb k Double || class_eqb k Extended
  | ExtF Double => class_eqb k Extended
  | ExtF _ => false
  | Truncd => class_eqb k Single
  | Truncx => class_eqb k Single || class_eqb k Double
  | FloatToInt _ _ => int_class k
  | IntToFloat _ _ => float_class k
  | Cast => int_class k || float_class k
  | Sqrt => float_class k
  | Alloc _ => class_eqb k P
  | Check _ _ _ _ | CheckAhead _ _ _ _ _ | Renew _ _ _ _ | RenewHull _ _ _ _
  | HalfCheck _ _ _ _ _ | RenewIf _ _ _ _ | CheckLimit _ _ _ _ | CheckLocal _ _ _ _ _ =>
      class_eqb k A
  | SpanTest _ _ => class_eqb k W
  | Limit _ => class_eqb k L
  | CheckFunction => class_eqb k F
  | RawLoad LdL _ => class_eqb k L
  | RawLoad LdS _ => class_eqb k Single
  | RawLoad LdD _ => class_eqb k Double
  | RawLoad LdX _ => class_eqb k Extended
  | RawLoad (LdNarrow _) _ => int_class k
  | RawLoadPointer _ _ => class_eqb k P
  | RawCas CasL _ => class_eqb k L
  | RawCas CasP _ => class_eqb k P
  | RawCas (CasNarrow _) _ => int_class k
  | VaArgs => class_eqb k P
  | VaArg => any_class k
  | Setjmp _ => class_eqb k W
  end.

(** ## Signatures

    When a function calls another function defined in the same module, the
    call site must pass arguments and bind return values that match the
    callee's parameter and return types, even when the callee uses features
    outside the [[core-subset|core subset]]. This section extracts a
    uniform [sig] record from both core-subset functions and raw Prolog
    function terms so that [valid_inst] can type-check direct calls. *)

(** Given a register [[class]] k, [eclass] returns the Prolog atom that
    represents k in raw IR terms, allowing [func_sig] to compare core
    classes with functions outside the [[core-subset|core subset]]. *)
Definition eclass (k : class) : term :=
  TAtom (match k with
         | W => "w" | L => "l" | P => "p" | A => "a" | F => "f"
         | Single => "s" | Double => "d" | Extended => "x"
         end).

(** Given a function return type r, [eret] converts r into the Prolog term
    representation used in raw function signatures. *)
Definition eret (r : ret_type) : term :=
  match r with
  | RClass k => eclass k
  | RVoid => TAtom "void"
  | RTuple ks => TApp "tuple" [TList (map eclass ks)]
  end.

(** A [sig] record summarizes the signature information that a direct call
    checks against its callee: the callee's linkage term, its parameter
    class terms, its return-type term, and whether it accepts variadic
    arguments. *)
Record sig : Type := mkSig {
  sig_linkage : term;
  sig_params : list term;
  sig_ret : term;
  sig_variadic : bool
}.

(** Given a raw instruction term t, [is_va_args] returns `true` when t is a
    `va_args` instruction, which marks the enclosing function as variadic. *)
Definition is_va_args (t : term) : bool :=
  match t with
  | TApp "let" [_; TAtom "p"; TAtom "va_args"; _] => true
  | _ => false
  end.

(** Given the raw Prolog term t of a function outside the
    [[core-subset|core subset]], [term_sig] extracts its [sig] record. A
    function with a `data` return type returns through `zreturn` and is
    always treated as variadic. *)
Definition term_sig (t : term) : option sig :=
  match t with
  | TApp "func" [_; lk; r; TList ps; TList bs] =>
      Some (mkSig lk (map (fun p => match p with TApp "param" [k; _] => k | _ => p end) ps) r
                  (term_eqb r (TAtom "data") || existsb (fun b => match b with
                                     | TApp "block" [_; _; TList is; _] => existsb is_va_args is
                                     | _ => false
                                     end) bs))
  | _ => None
  end.

(** Given a function name n and a module md, [func_sig] returns the [sig]
    of the first function named n in md, whether that function belongs to
    the [[core-subset|core subset]] or sits outside it. *)
Fixpoint func_sig (n : name) (md : module) : option sig :=
  match md with
  | [] => None
  | IFunc f :: rest =>
      if name_eqb (fn_name f) n
      then Some (mkSig (fn_linkage f) (map (fun p => eclass (fst p)) (fn_params f))
                       (eret (fn_ret f)) (variadic_func f))
      else func_sig n rest
  | IOutside f t :: rest => if name_eqb f n then term_sig t else func_sig n rest
  | _ :: rest => func_sig n rest
  end.

(** Given a raw term t, [float_atom] returns `true` when t is the atom of
    a single, double, or extended floating-point [[class]]. *)
Definition float_atom (t : term) : bool :=
  match t with TAtom ("s" | "d" | "x") => true | _ => false end.

(** Given a raw term t, [class_atom] returns `true` when t is the atom of
    an integer, pointer, or floating-point value [[class]]. *)
Definition class_atom (t : term) : bool :=
  match t with TAtom ("w" | "l" | "p" | "s" | "d" | "x") => true | _ => false end.

(** Given a call's result binding r and a callee's return-type term ret,
    [call_result_ok] tests whether r is compatible with ret. A tuple
    result must match the callee's tuple classes exactly, a single
    floating-point or pointer result must match the exact return class,
    and a 64-bit long result may not be read from a 32-bit word return,
    whereas a `data` callee accepts any result binding. *)
Definition call_result_ok (r : call_result) (ret : term) : bool :=
  (* call_result_ok(_, _, _, data): a `zreturn` callee's words are read
     as through the generic entry, with their size checked at run time. *)
  term_eqb ret (TAtom "data") ||
  match r with
  | CVoid => true
  | CTuple rs => term_eqb ret (TApp "tuple" [TList (map (fun x => eclass (snd x)) rs)])
  | CResult _ k =>
      (* to_result_ok/4 and class_result_ok/4 *)
      class_atom ret &&
      if float_atom ret || float_class k then term_eqb ret (eclass k)
      else negb (class_eqb k L && term_eqb ret (TAtom "w"))
           && Bool.eqb (class_eqb k P) (term_eqb ret (TAtom "p"))
  end.

(** Given two term lists ps and xs, [prefix_eqb] tests whether ps is a
    prefix of xs, which [valid_inst] uses to match the fixed parameters of
    a variadic callee against the leading arguments of a call. *)
Fixpoint prefix_eqb (ps xs : list term) : bool :=
  match ps, xs with
  | [], _ => true
  | p :: ps', x :: xs' => term_eqb p x && prefix_eqb ps' xs'
  | _, _ => false
  end.

(** ## Instructions, jumps and phis

    With operand classes, operation parameters, and function signatures in
    place, the validator can check individual instructions, jumps, [[phi]]
    nodes, and stack-local declarations. This section defines those
    block-level well-formedness checks and verifies that capability
    [[proof]] temporaries are created only by check instructions. *)

(** Given a function f, [labels] returns the list of [[block]] labels in
    f. *)
Definition labels (f : func) : list name := map b_label (fn_blocks f).

(** Given a memory store width w, [width_value_ok] returns the operand
    [[class]] that a scalar `raw_store` of width w must read, or `None` for
    the pointer width [Wp], which must use `raw_store_pointer` instead. *)
Definition width_value_ok (w : width) : option class :=
  match w with
  | Wb | Wh | Ww => Some W | Wl => Some L
  | Ws => Some Single | Wd => Some Double | Wx => Some Extended
  | Wp => None
  end.

(** Given a module md and a symbol name s, [init_entry_named] returns
    `true` when s names a constructor or destructor table entry in md,
    which instructions may neither copy nor call. *)
Definition init_entry_named (md : module) (s : name) : bool :=
  existsb (fun it => match it with IData n (LInit _ _) _ _ => name_eqb n s | _ => false end) md.

(** Given a module, a temporary-class table, and an instruction,
    [valid_inst] checks that the instruction is well formed and reads
    every operand at an allowed [[class]] via [valid_use]. It verifies
    operation parameters and result classes with [valid_op] and
    [op_result_ok], checks memory store effects, and matches direct calls
    against [func_sig]. *)
Definition valid_inst (md : module) (classes : list (name * class)) (i : inst) : bool :=
  let use := valid_use classes in
  match i with
  | Loc file _ => match file with TAtom _ => true | _ => false end
  | Touch q => use A (Tmp q)
  | LocalAlloc _ size => (0 <=? size) && (size <=? 2 ^ 31 - 1)
  | Flight _ o args lw =>
      match o, args with
      | Copy, [_] | Add, [_; _] | Sub, [_; _] => true
      | _, _ => false
      end
      && forallb (fun a => match a with FAddress p => use P p | FValue v => use L v end) args
      && match lw with LowerNone => true | LowerOf p => use P p end
  | Let _ P Copy [Global g] => negb (init_entry_named md g)
  | Let _ k o args =>
      valid_op o && op_result_ok o k &&
      (* `va_args needs a non-negative constant` *)
      match o, args with
      | VaArgs, [Const off] => 0 <=? off
      | VaArgs, _ => false
      (* `setjmp and _setjmp need a zero SaveMask` *)
      | Setjmp SjSig, _ => true
      | Setjmp _, [_; Const Z0] => true
      | Setjmp _, _ => false
      | _, _ => true
      end &&
      match op_arg_classes o k with
      | Some cs => (length cs =? length args)%nat
                   && forallb (fun ca => use (fst ca) (snd ca)) (combine cs args)
      | None => false
      end
  | RawStore w _ v a =>
      match width_value_ok w with Some k => use k v && use A a | None => false end
  | RawStorePointer _ v a es =>
      (effects_eqb es store_effects || effects_eqb es local_store_effects
       || effects_eqb es atomic_store_effects) && use P v && use A a
  | Call r (Global c) args =>
      negb (init_entry_named md c) &&
      match func_sig c md with
      | Some s =>
          let acs := map (fun a => eclass (arg_class a)) args in
          ((((length acs =? length (sig_params s))%nat
             && forallb (fun p => term_eqb (fst p) (snd p)) (combine acs (sig_params s)))
            || (sig_variadic s && prefix_eqb (sig_params s) acs))
           && call_result_ok r (sig_ret s))
      | None => true
      end
      && forallb (fun a => use (arg_class a) (arg_value a)) args
  | Call _ (Tmp n) args => use P (Tmp n) && forallb (fun a => use (arg_class a) (arg_value a)) args
  | Call _ _ _ => false
  | RawCall _ callee args => use F callee && forallb (fun a => use (arg_class a) (arg_value a)) args
  end.

(** Given a function f, a temporary-class table classes, and a jump j,
    [valid_jump] checks that all target labels belong to f, that a
    conditional branch reads its condition as a 32-bit word, and that a
    return instruction matches the return type of f. *)
Definition valid_jump (f : func) (classes : list (name * class)) (j : jump) : bool :=
  let exists_ t := mem (edge_label t) (labels f) in
  match j with
  | JGoto t => exists_ t
  | JBranch v t1 t2 => valid_use classes W v && exists_ t1 && exists_ t2
  | JRet v => match fn_ret f with RClass k => valid_use classes k v | _ => false end
  | JRets vs =>
      match fn_ret f with
      | RTuple ks => (length ks =? length vs)%nat
                     && forallb (fun kv => valid_use classes (fst kv) (snd kv)) (combine ks vs)
      | _ => false
      end
  | JRetVoid => match fn_ret f with RVoid => true | _ => false end
  | JUnreachable => true
  end.

(** Given a temporary-class table classes, a block's predecessor list
    preds, and a [[phi]] node ph, [valid_phi] checks that the incoming
    labels of ph match preds as a set and that every incoming value is read
    at the class of ph. *)
Definition valid_phi (classes : list (name * class)) (preds : list name) (ph : phi) : bool :=
  match ph with
  | Phi _ k pairs =>
      sets_eqb (map fst pairs) preds && forallb (fun pv => valid_use classes k (snd pv)) pairs
  end.

(** Given a module md, a function f, a temporary-class table classes, and a
    [[block]] b, [valid_block] checks all [[phi]] nodes, instructions, and
    the terminating jump of b, and ensures that any block with phi nodes
    has at least one predecessor. *)
Definition valid_block (md : module) (f : func) (classes : list (name * class)) (b : block)
  : bool :=
  let preds := preds_of (fn_blocks f) (b_label b) in
  forallb (valid_phi classes preds) (b_phis b)
  && forallb (valid_inst md classes) (b_insts b)
  && valid_jump f classes (b_jump b)
  && (match b_phis b, preds with _ :: _, [] => false | _, _ => true end).

(** Given a function f, [proof_class_defs] verifies that capability
    [[proof]] temporaries are defined only by `let` check instructions, and
    never appear as function parameters, [[phi]] results, call arguments,
    or call results. *)
Definition proof_class_defs (f : func) : bool :=
  forallb (fun p => negb (proof_class (fst p))) (fn_params f) &&
  forallb (fun b =>
             forallb (fun ph => match ph with Phi _ k _ => negb (proof_class k) end) (b_phis b)
             && forallb (fun i =>
                           match i with
                           | Call r _ args | RawCall r _ args =>
                               forallb (fun dk => negb (proof_class (snd dk))) (inst_temp_defs i)
                               && forallb (fun a => negb (proof_class (arg_class a))) args
                           | _ => true
                           end) (b_insts b))
          (fn_blocks f).

(** Given a list of names ns, [no_dups] returns `true` when no name appears
    more than once in ns. *)
Fixpoint no_dups (ns : list name) : bool :=
  match ns with [] => true | n :: rest => negb (mem n rest) && no_dups rest end.

(** Given a function f, [valid_locals] checks that every named stack-local
    object in f has a distinct name, is disallowed if f calls `setjmp`, and
    is allocated once by a `local_alloc` in the entry block before any
    `check_local` of that object runs. *)
Definition valid_locals (f : func) : bool :=
  let objs := local_objects f in
  no_dups (map fst objs) &&
  match objs with [] => true | _ :: _ => negb (setjmp_func f) end &&
  match fn_blocks f with
  | [] => false
  | entry :: _ =>
      let declared := fst (fold_left (fun (acc : list (name * Z) * Z) (i : inst) =>
                                        let (ds, j) := acc in
                                        match i with
                                        | LocalAlloc x _ => (ds ++ [(x, j)], j + 1)
                                        | _ => (ds, j + 1)
                                        end) (b_insts entry) ([], 0)) in
      (length declared =? length objs)%nat &&
      forallb (fun b =>
                 fst (fold_left (fun (acc : bool * Z) (i : inst) =>
                                   let (ok, j) := acc in
                                   (ok && match i with
                                          | Let _ _ (CheckLocal x _ _ _ _) _ =>
                                              match lookup x declared with
                                              | Some at_ => negb (name_eqb (b_label b) (b_label entry))
                                                            || (at_ <? j)
                                              | None => false
                                              end
                                          | _ => true
                                          end, j + 1)) (b_insts b) (true, 0)))
              (fn_blocks f)
  end.

(** ## Evidence

    When a capability [[check]] succeeds, it establishes a
    [[live-fact|live fact]] stating that a pointer's [[capability]] covers
    a byte span with given [[rights]] and alignment. Subsequent scalar
    accesses can reuse that proof only while no instruction has freed the
    object or redefined the proof or pointer temporary. This section
    defines the [fact] record and the transfer functions that update or
    intersect live facts across instructions and control-flow joins. *)

(** When a capability check succeeds at run time, it proves that a pointer
    can safely read or write a specific byte range of an object. A [fact]
    record captures that proven capability guarantee—the proof name, the
    pointer operand, the lower and upper byte offsets, the access
    [[rights]], and the alignment—for later instructions to reuse. *)
Record fact : Type := mkFact {
  f_q : name; f_p : value; f_lo : Z; f_hi : Z; f_r : rights; f_al : Z
}.

(** Given two live facts a and b, [fact_eqb] tests whether all six fields
    of a and b are equal. *)
Definition fact_eqb (a b : fact) : bool :=
  name_eqb (f_q a) (f_q b) && value_eqb (f_p a) (f_p b) && Z.eqb (f_lo a) (f_lo b)
  && Z.eqb (f_hi a) (f_hi b) && rights_eqb (f_r a) (f_r b) && Z.eqb (f_al a) (f_al b).

(** Once an instruction overwrites a temporary with a new value, any
    capability guarantee that referred to the old value of that temporary
    no longer holds. Given a redefined temporary name d and a list of
    facts fs, [kill] removes every fact that names d as its proof or
    pointer. *)
Definition kill (d : name) (fs : list fact) : list fact :=
  filter (fun f => negb (name_eqb (f_q f) d || value_eqb (f_p f) (Tmp d))) fs.

(** Given an instruction i and the current [[live-fact|live facts]] fs,
    [evidence_after] computes the facts that survive i. Any instruction
    that is not [evidence_preserving] clears all live facts because it may
    free memory, whereas an evidence-preserving instruction kills only the
    facts that mention the temporary it defines. *)
Definition evidence_after (i : inst) (fs : list fact) : list fact :=
  if evidence_preserving i
  then match inst_def_first i with Some d => kill d fs | None => fs end
  else [].

(** Given a proof name q and a list of live facts fs, [fact_of] returns
    the most recently added [[live-fact|live fact]] for q, or `None` if q
    has no live fact in fs. *)
Fixpoint fact_of (q : name) (fs : list fact) : option fact :=
  match fs with [] => None | f :: rest => if name_eqb (f_q f) q then Some f else fact_of q rest end.

(** Given the live-fact lists arriving along all incoming edges of a block,
    [evidence_meet] intersects them so that the block assumes only the
    [[evidence]] that holds on every incoming edge, returning the empty
    list when the block has no incoming edges. *)
Definition evidence_meet (sets : list (list fact)) : list fact :=
  match sets with
  | [] => []
  | s :: ss => filter (fun f => forallb (fun s' => existsb (fact_eqb f) s') ss) s
  end.

(** ## Accesses

    In checked IR, every raw load, store, or compare-and-swap instruction
    names the access [[proof]] temporary that authorizes it. To verify
    that the proof covers the instruction, the validator inspects the byte
    offset, transfer size, required alignment, required [[rights]], and
    memory effects of the instruction. This section extracts those
    properties from each [[raw-access|raw access]] and defines when a proof
    covers an immediate or reusing access. *)

(** An [access_type] classifies what a [[raw-access|raw access]] reads or
    writes: a scalar load [XLoad] of type t, a scalar store [XWidth] of
    width w, a pointer load or store [XPtr], or an atomic [[cas]] [XCas]
    of type t. *)
Inductive access_type : Type :=
  XLoad (t : load_type) | XWidth (w : width) | XPtr | XCas (t : cas_type).

(** Given an instruction i, [raw_access] recognizes whether i is a
    [[raw-access|raw access]] and returns the access [[proof]] name q, the
    [access_type], the byte offset from the proven pointer, and the
    required [[rights]]. Loads require [Read] rights, while stores and
    atomic [[cas]] instructions require [Write] rights. *)
Definition raw_access (i : inst) : option (name * access_type * Z * rights) :=
  match i with
  | Let _ _ (RawLoad t off) [Tmp q] => Some (q, XLoad t, off, Read)
  | RawStore w off _ (Tmp q) => Some (q, XWidth w, off, Write)
  | Let _ _ (RawLoadPointer off _) [Tmp q] => Some (q, XPtr, off, Read)
  | RawStorePointer off _ (Tmp q) _ => Some (q, XPtr, off, Write)
  | Let _ _ (RawCas t off) (Tmp q :: _) => Some (q, XCas t, off, Write)
  | _ => None
  end.

(** Given an [access_type] x, [access_size_align] returns the byte count
    that x transfers and the address alignment that x requires: 8-byte
    alignment for pointers and 80-bit extended floats, natural width
    alignment for an atomic [[cas]], and 1-byte alignment for all other
    scalar accesses. *)
Definition access_size_align (x : access_type) : Z * Z :=
  match x with
  | XLoad (LdL | LdD) => (8, 1)
  | XLoad LdS => (4, 1)
  | XLoad LdX => (10, 8)
  | XLoad (LdNarrow t) => (fst (narrow_type t), 1)
  | XWidth Wp | XPtr => (8, 8)
  | XWidth Wx => (10, 8)
  | XWidth w => (width_bytes w, 1)
  | XCas t => (cas_bytes t, cas_bytes t)
  end.

(** Given the capability [[rights]] `have` proved by a check and the rights
    `need` required by an access, [rights_allow] returns `true` when `have`
    is at least as strong as `need`, so [Write] rights permit both reads
    and writes. *)
Definition rights_allow (have need : rights) : bool :=
  match have, need with Write, _ => true | Read, Read => true | Read, Write => false end.

(** Given an instruction and the parameters of an access [[proof]],
    [covered_access] tests whether the instruction is a
    [[raw-access|raw access]] authorized by that proof. It checks that the
    accessed bytes fall within the proven span, that the address meets the
    required alignment, and that [rights_allow] permits the operation. *)
Definition covered_access (i : inst) (q : name) (lo hi : Z) (r : rights) (al : Z) : bool :=
  match raw_access i with
  | Some (q', x, off, need) =>
      let (size, aa) := access_size_align x in
      name_eqb q' q && (lo <=? off) && (off + size <=? hi)
      && (al mod aa =? 0) && ((off - lo) mod aa =? 0) && rights_allow r need
  | None => false
  end.

(** A [storage] tag distinguishes whether a [[raw-access|raw access]]
    targets the general [Heap'] or a proven stack-allocated [Local']
    object. *)
Inductive storage : Type := Heap' | Local'.

(** Given a raw access instruction i and a target [storage] kind s,
    [storage_effects] checks that i declares the memory effects required
    for s. Scalar loads and stores need no effect list, pointer accesses
    must declare heap, local, or atomic effects matching s, and atomic
    [[cas]] instructions may target only the heap. *)
Definition storage_effects (i : inst) (s : storage) : bool :=
  match i, s with
  | Let _ _ (RawLoad _ _) _, _ | RawStore _ _ _ _, _ => true
  | Let _ P (RawLoadPointer _ es) _, Heap' =>
      effects_eqb es load_effects || effects_eqb es atomic_load_effects
  | Let _ P (RawLoadPointer _ es) _, Local' => effects_eqb es local_load_effects
  | RawStorePointer _ _ _ es, Heap' =>
      effects_eqb es store_effects || effects_eqb es atomic_store_effects
  | RawStorePointer _ _ _ es, Local' => effects_eqb es local_store_effects
  | Let _ _ (RawCas _ _) _, Heap' => true
  | _, _ => false
  end.

(** Every heap capability [[check]] or [[reuse]] instruction must be used
    immediately by the next instruction in the block. The function
    [proof_use] verifies that the following instruction either consumes
    the proof with a [[touch]] or performs a heap [[raw-access|raw access]]
    covered by [covered_access]. *)
Definition proof_use (i : inst) (q : name) (lo hi : Z) (r : rights) (al : Z) : bool :=
  match i with
  | Touch q' => name_eqb q' q
  | _ => covered_access i q lo hi r al && storage_effects i Heap'
  end.

(** Given a raw access instruction i of type x, [reusing_access] tests
    whether i may reuse an existing [[live-fact|live fact]] instead of
    following its own check immediately. Scalar accesses and non-atomic
    heap pointer loads may reuse live evidence, whereas pointer stores and
    atomic [[cas]] instructions must always follow their own check. *)
Definition reusing_access (i : inst) (x : access_type) : bool :=
  match x with
  | XPtr => match i with
            | Let _ P (RawLoadPointer _ es) _ => effects_eqb es load_effects
            | _ => false
            end
  | XCas _ => false
  | _ => true
  end.

(** ## Single definitions, chains and intervals

    The capability [[reuse]] forms allow a pointer access to rely on an
    earlier check, span guard, or object limit when the validator can bound
    the byte distance between the two pointers. Because a [[temporary]]
    defined only once in a function holds the same value at every point it
    dominates, this section restricts its analysis to
    [[single-definition|single definitions]], computes
    [[offset-interval|offset intervals]] for integer expressions, and walks
    [[guard-chain|guard chains]] of pointer [[flight|flights]] to verify
    each reuse condition. *)

(** A [def] records what defines a [[temporary]] in the single-definition
    table: a function parameter [DParam], a [[phi]] node [DPhi], or an
    instruction [DInst]. *)
Inductive def : Type := DParam | DPhi (ph : phi) | DInst (i : inst).

(** Given a function f, [all_defs] collects every temporary definition in
    f paired with its defining parameter, [[phi]] node, or instruction. *)
Definition all_defs (f : func) : list (name * def) :=
  map (fun p => (snd p, DParam)) (fn_params f) ++
  flat_map (fun b => map (fun ph => match ph with Phi d _ _ => (d, DPhi ph) end) (b_phis b)
                     ++ flat_map (fun i => map (fun dk => (fst dk, DInst i)) (inst_temp_defs i))
                                 (b_insts b)) (fn_blocks f).

(** Given a function f, [single_definitions] returns all temporaries in f
    that have a [[single-definition|single definition]], paired with what
    defines them. Because a single definition that dominates a program
    point still holds the value it computed there, the [[reuse]] rules
    inspect only temporaries in this list. *)
Definition single_definitions (f : func) : list (name * def) :=
  let ds := all_defs f in
  filter (fun d => (length (filter (fun d' => name_eqb (fst d) (fst d')) ds) =? 1)%nat) ds.

(** Given a single-definition table once and a temporary name n, [once_has]
    returns `true` when n has a single definition in once. *)
Definition once_has (once : list (name * def)) (n : name) : bool :=
  match lookup n once with Some _ => true | None => false end.

(** Given an integer offset k, [near_offset] tests whether k lies between
    `-2^62` and `2^62`. Because pointer arithmetic on a
    [[guard-chain|guard chain]] wraps modulo `2^64`, the reuse rules
    require [[near-offset|near offsets]] so that modular differences match
    true mathematical distances. *)
Definition near_offset (k : Z) : bool := (- 2 ^ 62 <=? k) && (k <=? 2 ^ 62).

(** Given an integer [[class]] k and a raw constant c, [signed_value]
    interprets c as a two's-complement signed integer of class k's bit
    width. *)
Definition signed_value (k : class) (c : Z) : option Z :=
  let* bits := class_bits k in
  let u := c mod 2 ^ bits in
  Some (if 2 ^ (bits - 1) <=? u then u - 2 ^ bits else u).

(** Given a narrow integer type t, [narrow_range] returns the inclusive
    value range produced by extending a signed or unsigned byte or 16-bit
    halfword, or `None` for wider types. *)
Definition narrow_range (t : narrow) : option (Z * Z) :=
  match t with
  | Ub => Some (0, 255) | Uh => Some (0, 65535)
  | Sb => Some (-128, 127) | Sh => Some (-32768, 32767)
  | _ => None
  end.

(** Given an integer [[class]] k and bounds lo and hi, [interval_fits]
    checks whether the [[offset-interval|offset interval]] from lo to hi is
    valid for class k. A 32-bit word interval must fit within the signed
    32-bit range so that word arithmetic never wraps, whereas a 64-bit long
    interval may span any bounds because it tracks values modulo `2^64`. *)
Definition interval_fits (k : class) (lo hi : Z) : bool :=
  match k with
  | W => (- 2 ^ 31 <=? lo) && (hi <=? 2 ^ 31 - 1)
  | L => true
  | _ => false
  end.

(** The association list [memo] caches the results of [oi], mapping each
    queried pair of temporary name and [[class]] to its computed
    [[offset-interval|offset interval]] or `None`. *)
Definition memo := list ((name * class) * option (Z * Z)).

(** Given a temporary name n, a [[class]] k, and a memo table m,
    [memo_lookup] returns the cached interval result for n at class k when
    present. *)
Fixpoint memo_lookup (n : name) (k : class) (m : memo) : option (option (Z * Z)) :=
  match m with
  | [] => None
  | (nk, r) :: rest =>
      if name_eqb (fst nk) n && class_eqb (snd nk) k then Some r else memo_lookup n k rest
  end.

(** Given an operand value v, [is_const] returns `true` when v is an
    integer constant. *)
Definition is_const (v : value) : bool := match v with Const _ => true | _ => false end.

(** Given a recursive operand walker rec, an operation o with arguments
    args, a result [[class]] k, and a memo table m, [op_interval] computes
    an [[offset-interval|offset interval]] for the result of o. Each branch
    commits in the same order as the Prolog cuts in `ir.pl`, so bitwise
    `and` checks its right operand as a constant mask before its left
    operand, and a failed sign extension does not fall through. *)
Definition op_interval (rec : value -> class -> memo -> option (Z * Z) * memo)
    (o : op) (args : list value) (k : class) (m : memo) : option (Z * Z) * memo :=
  match o, args with
  | Ext t, _ =>
      match narrow_range t with
      | Some r => (Some r, m)
      | None =>
          match t, args with
          | Sw, [a] => rec a W m
          | Uw, [a] =>
              match rec a W m with
              | (Some (lo, hi), m1) => if 0 <=? lo then (Some (lo, hi), m1) else (None, m1)
              | r => r
              end
          | _, _ => (None, m)
          end
      end
  | RawLoad (LdNarrow t) _, _ => (narrow_range t, m)
  | Copy, [a] => rec a k m
  | And, _ =>
      let mask c := match signed_value k c with
                    | Some v => if 0 <=? v then Some (0, v) else None
                    | None => None
                    end in
      match args with
      | [_; Const c] =>
          match mask c with
          | Some r => (Some r, m)
          | None => match args with [Const c'; _] => (mask c', m) | _ => (None, m) end
          end
      | [Const c; _] => (mask c, m)
      | _ => (None, m)
      end
  | Urem, [_; Const c] =>
      match class_bits k with
      | Some bits =>
          let u := c mod 2 ^ bits in
          ((if (0 <? u) && (u <=? 2 ^ (bits - 1)) then Some (0, u - 1) else None), m)
      | None => (None, m)
      end
  | Shl, [a; Const s] =>
      match class_bits k with
      | Some bits =>
          if (0 <=? s) && (s <? bits) then
            match rec a k m with
            | (Some (lo, hi), m1) => (Some (lo * 2 ^ s, hi * 2 ^ s), m1)
            | r => r
            end
          else (None, m)
      | None => (None, m)
      end
  | Mul, _ =>
      let scaled a c :=
        match signed_value k c with
        | Some v =>
            match rec a k m with
            | (Some (lo, hi), m1) =>
                (Some (if 0 <=? v then (lo * v, hi * v) else (hi * v, lo * v)), m1)
            | r => r
            end
        | None => (None, m)
        end in
      match args with
      | [a; Const c] => if is_const a then
                          match args with [Const c'; a'] =>
                            if is_const a' then (None, m) else scaled a' c'
                          | _ => (None, m) end
                        else scaled a c
      | [Const c; a] => if is_const a then (None, m) else scaled a c
      | _ => (None, m)
      end
  | Add, [a; b] =>
      match rec a k m with
      | (Some (lo1, hi1), m1) =>
          match rec b k m1 with
          | (Some (lo2, hi2), m2) => (Some (lo1 + lo2, hi1 + hi2), m2)
          | r => r
          end
      | r => r
      end
  | Sub, [a; Const c] =>
      match signed_value k c with
      | Some v =>
          match rec a k m with
          | (Some (lo, hi), m1) => (Some (lo - v, hi - v), m1)
          | r => r
          end
      | None => (None, m)
      end
  | _, _ => (None, m)
  end.

(** Given the single-definition table once, a recursion budget fuel, an
    operand v of [[class]] k, a recursion depth, and a memo table m, [oi]
    walks single definitions up to depth 32 to bound every runtime value
    of v within an [[offset-interval|offset interval]]. It threads the memo
    table in the exact order of `ir.pl`: a successful walk preserves all
    memo entries added by its subtrees, whereas a failed walk discards
    subtree entries and records `None` for the queried temporary. *)
Fixpoint oi (once : list (name * def)) (fuel : nat) (v : value) (k : class) (depth : Z)
    (m : memo) : option (Z * Z) * memo :=
  match v with
  | Const c => (match signed_value k c with Some x => Some (x, x) | None => None end, m)
  | Global _ => (None, m)
  | Tmp n =>
      match memo_lookup n k m with
      | Some r => (r, m)
      | None =>
          let '(r, m') :=
            match fuel with
            | O => (None, m)
            | S f =>
                if depth <? 32 then
                  match lookup n once with
                  | Some (DInst (Let n' k' o args)) =>
                      if name_eqb n' n && class_eqb k' k then
                        match op_interval (fun v k m => oi once f v k (depth + 1) m) o args k m with
                        | (Some (lo, hi), m1) =>
                            if interval_fits k lo hi then (Some (lo, hi), m1) else (None, m)
                        | (None, _) => (None, m)
                        end
                      else (None, m)
                  | _ => (None, m)
                  end
                else (None, m)
            end in
          (r, ((n, k), r) :: m')
      end
  end.

(** Given a single-definition table once, an operand value v, and an
    integer [[class]] k, [offset_interval] runs [oi] from depth 0 with an
    empty memo table and returns the derived
    [[offset-interval|offset interval]] for v, if any. *)
Definition offset_interval (once : list (name * def)) (v : value) (k : class) : option (Z * Z) :=
  fst (oi once 33 v k 0 []).

(** Given a pointer [[flight]] operation o, its argument list args, and a
    base pointer b, [flight_term] extracts the offset operand and sign (1
    for `add` or `copy`, -1 for `sub`) when the flight displaces b. *)
Definition flight_term (o : op) (args : list flight_arg) (b : value) : option (value * Z) :=
  match o, args with
  | Add, [FAddress b0; FValue ov] => if value_eqb b0 b then Some (ov, 1) else None
  | Sub, [FAddress b0; FValue ov] => if value_eqb b0 b then Some (ov, -1) else None
  | Copy, [FAddress b0] => if value_eqb b0 b then Some (Const 0, 1) else None
  | _, _ => None
  end.

(** Given a single-definition table once, a step budget fuel, a pointer p,
    and an accumulated offset interval from lo to hi, [guard_chain_go]
    walks backward through single-definition pointer [[flight|flights]] and
    records each base pointer along with its offset interval. *)
Fixpoint guard_chain_go (once : list (name * def)) (fuel : nat) (p : value) (lo hi : Z)
  : list (value * (Z * Z)) :=
  (p, (lo, hi)) ::
  match fuel, p with
  | S f, Tmp x =>
      match lookup x once with
      | Some (DInst (Flight _ o args (LowerOf b))) =>
          match flight_term o args b with
          | Some (ov, sign) =>
              match offset_interval once ov L with
              | Some (olo, ohi) =>
                  if sign =? 1 then guard_chain_go once f b (lo + olo) (hi + ohi)
                  else guard_chain_go once f b (lo - ohi) (hi - olo)
              | None => []
              end
          | None => []
          end
      | _ => []
      end
  | _, _ => []
  end.

(** Given a single-definition table once and a pointer operand p,
    [guard_chain] computes the [[guard-chain|guard chain]] of p up to 64
    steps deep. The chain starts with p at offset 0 and lists each base
    pointer b from which p inherits its [[capability]] through
    single-definition `add`, `sub`, and `copy` [[flight|flights]], paired
    with the interval of p's byte offset from b. *)
Definition guard_chain (once : list (name * def)) (p : value) : list (value * (Z * Z)) :=
  guard_chain_go once 64 p 0 0.

(** Given a single-definition table once and a guard-chain entry e,
    [exact_base] checks whether e names a single-definition temporary at a
    single known byte offset, returning that [[exact-base|exact base]] name
    and offset when lower and upper bounds coincide. *)
Definition exact_base (once : list (name * def)) (e : value * (Z * Z)) : option (name * Z) :=
  match e with
  | (Tmp n, (k, k')) => if (k =? k') && once_has once n then Some (n, k) else None
  | _ => None
  end.

(** Given a partial function f and a list xs, [first_some] returns the
    first `Some` result produced by applying f to elements of xs in order. *)
Fixpoint first_some {X Y : Type} (f : X -> option Y) (xs : list X) : option Y :=
  match xs with [] => None | x :: rest => match f x with Some y => Some y | None => first_some f rest end end.

(** Given a single-definition table once and two pointers p and p1,
    [pointer_distance] computes the constant byte [[pointer-distance|distance]]
    from p1 to p modulo `2^64` when both pointers reach a common
    [[exact-base|exact base]] on their [[guard-chain|guard chains]]. Matching
    the cut in `ir.pl`, it selects the first exact base on p's chain that
    also appears with an exact offset on p1's chain. *)
Definition pointer_distance (once : list (name * def)) (p p1 : value) : option Z :=
  let c1 := guard_chain once p1 in
  first_some (fun e =>
                match exact_base once e with
                | Some (n, k) =>
                    first_some (fun e1 => match e1 with
                                          | (Tmp n1, (k1, k1')) =>
                                              if name_eqb n1 n && (k1 =? k1') then Some (k - k1) else None
                                          | _ => None
                                          end) c1
                | None => None
                end) (guard_chain once p).

(** Given a bound direction bd, a new access span from lo to hi, a modular
    pointer distance d0, and a previously checked span from lo1 to hi1,
    [half_known] tests whether a [[half_check]] may check only bound bd.
    When both displaced endpoints are [[near-offset|near offsets]] and the
    new span is at most `2^62` bytes wide, an [Upper] check already knows
    the lower bound if `d + lo` sits at or above `lo1`, and a [Lower]
    check already knows the upper bound if `d + hi` sits at or below
    `hi1`. *)
Definition half_known (bd : bound) (lo hi d0 lo1 hi1 : Z) : bool :=
  let d := ((d0 + 2 ^ 63) mod 2 ^ 64) - 2 ^ 63 in
  let e := d + lo - lo1 in
  let f := d + hi - hi1 in
  near_offset e && near_offset f && (hi - lo <=? 2 ^ 62) &&
  match bd with Upper => 0 <=? e | Lower => f <=? 0 end.

(** Later [[reuse]] instructions can derive a new access proof from an
    earlier check when both the earlier proof and its pointer are defined
    only once in the function. Given an instruction, [renew_source]
    returns that [[renew-source|renew source]]—its proof name, pointer
    name, byte bounds, and alignment—whenever the instruction is a
    qualifying check. *)
Definition renew_source (once : list (name * def)) (i : inst) : option (name * (name * Z * Z * Z)) :=
  match i with
  | Let q1 A o args =>
      let src := match o, args with
                 | Check lo hi _ al, [Tmp p] | CheckAhead lo hi _ al _, [Tmp p]
                 | RenewIf lo hi _ al, [Tmp p; _] | CheckLimit lo hi _ al, [Tmp p; _]
                 | HalfCheck _ lo hi _ al, [_; Tmp p] => Some (p, lo, hi, al)
                 | _, _ => None
                 end in
      match src with
      | Some (p, lo, hi, al) =>
          if once_has once q1 && once_has once p then Some (q1, (p, lo, hi, al)) else None
      | None => None
      end
  | _ => None
  end.

(** Given the table of [[renew-source|renew sources]] srcs, the
    single-definition table once, a target pointer p with span lo to hi and
    alignment al, and two source proofs ql and qh, [hull_renewable] checks
    whether a [[renew_hull]] instruction is valid. The target span must sit
    between the lower bound of ql and the upper bound of qh at
    [[pointer-distance|pointer distances]] between 0 and `2^62`, have
    width at most `2^62`, and inherit its alignment from at least one of
    the two sources. *)
Definition hull_renewable (srcs : list (name * (name * Z * Z * Z))) (once : list (name * def))
    (p : value) (lo hi al : Z) (ql qh : value) : bool :=
  match ql, qh with
  | Tmp nl, Tmp nh =>
      match lookup nl srcs, lookup nh srcs with
      | Some (pl, lol, _, all), Some (ph, loh, hih, alh) =>
          match pointer_distance once p (Tmp pl), pointer_distance once p (Tmp ph) with
          | Some dl, Some dh =>
              let e := lo + dl - lol in
              let f := hih - hi - dh in
              (0 <=? e) && (e <=? 2 ^ 62) && (0 <=? f) && (f <=? 2 ^ 62) && (hi - lo <=? 2 ^ 62)
              && (((all mod al =? 0) && (e mod al =? 0))
                  || ((alh mod al =? 0) && ((lo + dh - loh) mod al =? 0)))
          | _, _ => false
          end
      | _, _ => false
      end
  | _, _ => false
  end.

(** Given a single-definition table once, a pointer p, a guard operand g,
    and byte bounds lo and hi, [guard_covers] checks the side condition of
    a [[renew_if]] instruction. The operand g must be a single-definition
    [[span_test]] on a single-definition base pointer n0 from p's
    [[guard-chain|guard chain]], and the tested span must cover lo through
    hi across the entire offset interval between n0 and p. *)
Definition guard_covers (once : list (name * def)) (p g : value) (lo hi : Z) : bool :=
  match g with
  | Tmp gn =>
      match lookup gn once with
      | Some (DInst (Let gn' W (SpanTest glo ghi) [Tmp n0])) =>
          name_eqb gn' gn && once_has once n0 &&
          match first_some (fun e => if value_eqb (fst e) (Tmp n0) then Some (snd e) else None)
                           (guard_chain once p) with
          | Some (olo, ohi) => (glo <=? olo + lo) && (ohi + hi <=? ghi)
          | None => false
          end
      | _ => false
      end
  | _ => false
  end.

(** Given a single-definition table once, a step budget fuel, a pointer p,
    and a base pointer b, [lower_chain] tests whether p inherits the
    capability [[lower]] of b through a [[lower-chain|lower chain]] of
    single-definition [[flight]] instructions, regardless of how those
    flights displace the address. *)
Fixpoint lower_chain (once : list (name * def)) (fuel : nat) (p b : value) : bool :=
  value_eqb p b ||
  match fuel, p with
  | S f, Tmp x =>
      match lookup x once with
      | Some (DInst (Flight _ _ _ (LowerOf d))) => lower_chain once f d b
      | _ => false
      end
  | _, _ => false
  end.

(** Given a single-definition table once, a pointer p, a limit operand u,
    and bounds lo and hi, [limit_covers] checks the side condition of a
    `check_limit` instruction. The operand u must be a single-definition
    [[limit]] of `size` bytes on a single-definition pointer n0 linked to p
    by [lower_chain], and the checked span from lo to hi must run from 0
    to `size`. *)
Definition limit_covers (once : list (name * def)) (p u : value) (lo hi : Z) : bool :=
  match u with
  | Tmp un =>
      match lookup un once with
      | Some (DInst (Let un' L (Limit size) [Tmp n0])) =>
          name_eqb un' un && (lo =? 0) && (hi =? size) && once_has once n0
          && lower_chain once 64 p (Tmp n0)
      | _ => false
      end
  | _ => false
  end.

(** Given a raw access instruction i through proof q of pointer p, the
    proven offset lo and alignment al of q, the current [[live-fact|live facts]]
    live, and the single-definition table once, [hull_covered] tests
    whether i is covered by the convex hull of live facts on p's object. At
    least one live fact at a [[near-offset|near]] [[pointer-distance]] from
    p must start at or before the access, another must end at or after it,
    alignment must follow from lo and al, and a write access requires at
    least one live fact with [Write] [[rights]]. *)
Definition hull_covered (i : inst) (q : name) (p : value) (lo al : Z) (live : list fact)
    (once : list (name * def)) : bool :=
  match raw_access i with
  | Some (q', x, off, need) =>
      let (size, aa) := access_size_align x in
      let end_ := off + size in
      let spans := flat_map (fun f =>
                               match pointer_distance once (f_p f) p with
                               | Some d =>
                                   let l1 := f_lo f + d in
                                   let h1 := f_hi f + d in
                                   if near_offset d && near_offset l1 && near_offset h1
                                   then [(l1, h1, f_r f)] else []
                               | None => []
                               end) live in
      name_eqb q' q && (al mod aa =? 0) && ((off - lo) mod aa =? 0)
      && near_offset off && near_offset end_
      && existsb (fun s => let '(l1, _, _) := s in l1 <=? off) spans
      && existsb (fun s => let '(_, h1, _) := s in end_ <=? h1) spans
      && match need with
         | Read => true
         | Write => existsb (fun s => let '(_, _, r) := s in rights_eqb r Write) spans
         end
  | None => false
  end.

(** ## Scheduled checks

    A [[check_ahead|scheduled check]] tests a wider byte span than its
    immediate access uses so that subsequent accesses along the path can
    reuse the resulting proof without checking bounds again. To prevent a
    scheduled check from trapping on bytes that the original program would
    never have touched, this section runs a backward dataflow pass that
    computes each base pointer's [[need]]—the upper byte offset that later
    instructions are guaranteed to access on every path—and accepts a
    [[check_ahead]] only when its full span is needed. *)

(** The association list [facts] represents the backward [[need]] state at
    a program point, mapping each [[exact-base|exact base]] temporary to
    the highest byte offset that subsequent instructions are certain to
    access. *)
Definition facts := list (name * Z).

(** Given a base temporary name n and a need map fs, [del] removes any
    recorded [[need]] for n from fs. *)
Definition del (n : name) (fs : facts) : facts := filter (fun f => negb (name_eqb (fst f) n)) fs.

(** Given the need maps fss arriving from the outgoing edges of a block,
    [ahead_meet] keeps only the base temporaries present in every map paired
    with the minimum of their guaranteed [[need]] offsets, or returns the
    empty list when the block has no outgoing edges. *)
Definition ahead_meet (fss : list facts) : facts :=
  match fss with
  | [] => []
  | f :: rest =>
      flat_map (fun bh =>
                  match fold_left (fun acc f' => let* h := acc in
                                                 let* h1 := lookup (fst bh) f' in
                                                 Some (Z.min h h1)) rest (Some (snd bh)) with
                  | Some h => [(fst bh, h)]
                  | None => []
                  end) f
  end.

(** When a raw memory access touches bytes at a known offset from a base
    pointer, every execution path reaching that access must have at least
    those bytes in bounds. Given a guard-chain entry, [raise_need] checks
    whether the entry is an [[exact-base|exact base]] at a
    [[near-offset|near offset]] and raises that base pointer's recorded
    [[need]] to cover the accessed byte range. *)
Definition raise_need (once : list (name * def)) (off size : Z) (fs : facts)
    (e : value * (Z * Z)) : facts :=
  match exact_base once e with
  | Some (n, k) =>
      let h := k + off + size in
      if near_offset k && near_offset h then
        match lookup n fs with
        | Some h0 => if h <=? h0 then fs else put n h fs
        | None => put n h fs
        end
      else fs
  | None => fs
  end.

(** Given a single-definition table once, a proof-to-pointer map ptrs, an
    instruction i, and the need map fs after i, [ahead_step] computes the
    [[need]] map before i. Any instruction that is not
    [[ahead-transparent]] clears all needs because it may exit or trap
    before later accesses run, while an ahead-transparent instruction
    clears the need of any base temporary it defines and raises the needs
    of all bases on the [[guard-chain|guard chain]] of a raw access via
    [raise_need]. *)
Definition ahead_step (once : list (name * def)) (ptrs : list (name * value)) (i : inst)
    (fs : facts) : facts :=
  if ahead_transparent i then
    let fs1 := match first_some (fun dk => match lookup (fst dk) fs with
                                           | Some _ => Some (fst dk)
                                           | None => None
                                           end)
                                (inst_temp_defs i) with
               | Some d => del d fs
               | None => fs
               end in
    match raw_access i with
    | Some (q, x, off, _) =>
        match lookup q ptrs with
        | Some p => fold_left (raise_need once off (fst (access_size_align x))) (guard_chain once p) fs1
        | None => fs1
        end
    | None => fs1
    end
  else [].

(** Given a capability [[check]] or [[reuse]] operation o and its argument
    list args, [proof_pointer] extracts the pointer operand whose
    capability o checks. *)
Definition proof_pointer (o : op) (args : list value) : option value :=
  match o, args with
  | Check _ _ _ _, [p] | CheckAhead _ _ _ _ _, [p] => Some p
  | Renew _ _ _ _, [_; p] | HalfCheck _ _ _ _ _, [_; p] => Some p
  | RenewHull _ _ _ _, [_; _; p] => Some p
  | RenewIf _ _ _ _, [p; _] | CheckLimit _ _ _ _, [p; _] => Some p
  | _, _ => None
  end.

(** To know which pointer a raw memory access uses, the backward pass maps
    each access proof back to the pointer operand of its check. Given a
    function and its single-definition table, [proof_pointers] builds that
    lookup list for all single-definition access proofs. *)
Definition proof_pointers (f : func) (once : list (name * def)) : list (name * value) :=
  flat_map (fun b => flat_map (fun i =>
                                 match i with
                                 | Let q A o args =>
                                     match proof_pointer o args with
                                     | Some p => if once_has once q then [(q, p)] else []
                                     | None => []
                                     end
                                 | _ => []
                                 end) (b_insts b)) (fn_blocks f).

(** A [[check_ahead|scheduled check]] tests a wider byte span than its
    immediate access uses, which is safe only when later instructions on
    every path are guaranteed to access the rest of that span. Given an
    instruction and the [[need]] map after its immediate access,
    [ahead_accepts] tests whether the instruction is a justified scheduled
    check. It returns the proof name when some [[exact-base|exact base]]
    of the pointer needs at least the check's upper bound. *)
Definition ahead_accepts (once : list (name * def)) (next : facts) (i : inst) : option name :=
  match i with
  | Let q A (CheckAhead lo hi _ _ _) [p] =>
      if once_has once q &&
         existsb (fun e => match exact_base once e with
                           | Some (n, k) =>
                               near_offset k && near_offset (k + lo) &&
                               match lookup n next with Some h => k + hi <=? h | None => false end
                           | None => false
                           end) (guard_chain once p)
      then Some q else None
  | _ => None
  end.

(** To find which byte offsets a basic block is guaranteed to access from
    its entry onward, [ahead_insts] walks the block's instructions in
    reverse order from exit to entry. At each instruction, it updates the
    guaranteed access offsets with [ahead_step] and collects any scheduled
    check accepted by [ahead_accepts]. *)
Fixpoint ahead_insts (once : list (name * def)) (ptrs : list (name * value)) (ris : list inst)
    (after next : facts) (js : list name) : facts * list name :=
  match ris with
  | [] => (after, js)
  | i :: rest =>
      let js1 := match ahead_accepts once next i with Some q => q :: js | None => js end in
      ahead_insts once ptrs rest (ahead_step once ptrs i after) after js1
  end.

(** Given a block label l, a label list ls, and a starting index n,
    [index_of] returns the position of l in ls counting from n, or `None`
    if l is absent. *)
Fixpoint index_of (l : name) (ls : list name) (n : nat) : option nat :=
  match ls with [] => None | l' :: rest => if name_eqb l l' then Some n else index_of l rest (S n) end.

(** Given the block-order list order, the current block's position pos, the
    table ins of block entry needs, and a jump target edge t, [ahead_edge]
    returns the [[need]] map carried backward across t. Plain forward edges
    to later blocks propagate the target block's entry needs, whereas
    [[poll]] edges and back-edges carry no needs. *)
Definition ahead_edge (order : list name) (pos : option nat) (ins : list (name * facts)) (t : target)
  : facts :=
  match t with
  | Poll _ => []
  | To l =>
      match index_of l order 0, pos, lookup l ins with
      | Some tp, Some p, Some fs => if (p <? tp)%nat then fs else []
      | _, _, _ => []
      end
  end.

(** Given a block's [[phi]] nodes phs and the need map fs at the top of its
    instructions, [phis_end_needs] deletes the [[need]] of every base
    temporary redefined by a phi node at block entry. *)
Definition phis_end_needs (phs : list phi) (fs : facts) : facts :=
  fold_left (fun (fs : facts) (ph : phi) => match ph with Phi d _ _ => del d fs end) phs fs.

(** A basic [[block]] can guarantee a future access offset at its exit
    only when every outgoing path from the block guarantees that offset.
    The function [ahead_block] intersects the outgoing edge guarantees
    with [ahead_meet], walks the block's instructions in reverse with
    [ahead_insts], and clears any base temporaries redefined by [[phi]]
    nodes at block entry. *)
Definition ahead_block (order : list name) (once : list (name * def)) (ptrs : list (name * value))
    (st : list (name * facts) * list name) (b : block) : list (name * facts) * list name :=
  let (ins, js) := st in
  let out := ahead_meet (map (ahead_edge order (index_of (b_label b) order 0) ins) (jump_targets (b_jump b))) in
  let '(entry0, js') := ahead_insts once ptrs (rev (b_insts b)) out [] js in
  (put (b_label b) (phis_end_needs (b_phis b) entry0) ins, js').

(** To propagate guaranteed byte accesses backward across the control-flow
    graph, [ahead_fold] runs [ahead_block] over all blocks of a function in
    reverse order. It returns the table of block entry [[need|needs]]
    together with the list of justified [[check_ahead]] proofs. *)
Definition ahead_fold (f : func) (once : list (name * def)) : list (name * facts) * list name :=
  fold_left (ahead_block (map b_label (fn_blocks f)) once (proof_pointers f once)) (rev (fn_blocks f)) ([], []).

(** A [[check_ahead|scheduled check]] may check bytes beyond its immediate
    access only when subsequent instructions on every path are certain to
    access those bytes before exiting or polling. Given a function and its
    single-definition table, [ahead_justified] runs the backward pass in
    [ahead_fold] and returns the names of all justified scheduled checks. *)
Definition ahead_justified (f : func) (once : list (name * def)) : list name :=
  snd (ahead_fold f once).

(** ## Getters

    In Fil-C, reading a global symbol runs a [[getter]] helper that returns
    the symbol's pointer capability. An arbitrary getter call could invoke
    lazy initialization and invalidate live capability evidence, but a
    getter for a module-local function or data object that has already been
    evaluated on every dominating path simply returns the same pointer
    without side effects. This section identifies those
    [[repeated-getter|repeated getters]] so the evidence pass can preserve
    live facts across them. *)

(** Given a symbol name g and a module md, [first_func_linkage] returns the
    linkage term of the first function named g in md, whether inside or
    outside the [[core-subset|core subset]]. *)
Fixpoint first_func_linkage (g : name) (md : module) : option term :=
  match md with
  | [] => None
  | IFunc f :: rest => if name_eqb (fn_name f) g then Some (fn_linkage f) else first_func_linkage g rest
  | IOutside n t :: rest =>
      if name_eqb n g then match t with TApp "func" [_; lk; _; _; _] => Some lk | _ => None end
      else first_func_linkage g rest
  | _ :: rest => first_func_linkage g rest
  end.

(** Given a symbol name g and a module md, [first_data_linkage] returns the
    linkage of the first global data definition named g in md, skipping
    `extern(weak)` declarations because they do not define an object. *)
Fixpoint first_data_linkage (g : name) (md : module) : option linkage :=
  match md with
  | [] => None
  | IData n lk _ _ :: rest =>
      match lk with
      | LExternWeak => first_data_linkage g rest
      | _ => if name_eqb n g then Some lk else first_data_linkage g rest
      end
  | _ :: rest => first_data_linkage g rest
  end.

(** Given a module md and a symbol name g, [local_global] returns `true`
    when the first function or data item defining g in md has `local`
    linkage, meaning that g belongs to this module and cannot be interposed
    externally. *)
Definition local_global (md : module) (g : name) : bool :=
  match first_func_linkage g md with
  | Some lk => term_eqb lk (TAtom "local")
  | None =>
      match first_data_linkage g md with
      | Some LLocal => true
      | Some (LRo l) | Some (LTls l) => term_eqb l (TAtom "local")
      | _ => false
      end
  end.

(** Given a module md, a function f, its dominator intervals doms, and its
    single-definition table once, [repeated_getters] finds every
    single-definition [[getter]] instruction in a reachable block that
    copies a [local_global] symbol g and is [[dominance|dominated]] by an
    earlier copy of g. Because the earlier getter has already initialized
    and resolved g, the [[evidence-pass|evidence pass]] preserves existing
    [[live-fact|live facts]] across these [[repeated-getter|repeated getters]]. *)
Definition repeated_getters (md : module) (f : func) (doms : nmap (Z * Z))
    (once : list (name * def)) : list (name * name) :=
  let sites := flat_map (fun b =>
                           snd (fold_left (fun (acc : Z * list (name * Z * name * name)) (i : inst) =>
                                             let (j, ss) := acc in
                                             (j + 1, match i with
                                                     | Let d P Copy [Global g] =>
                                                         if local_global md g then ss ++ [(b_label b, j, d, g)] else ss
                                                     | _ => ss
                                                     end)) (b_insts b) (0, [])))
                        (fn_blocks f) in
  flat_map (fun s =>
              let '(l, i, d, g) := s in
              if once_has once d && is_reachable doms l &&
                 existsb (fun s1 => let '(l1, i1, _, g1) := s1 in
                                    name_eqb g1 g &&
                                    (if name_eqb l1 l then i1 <? i
                                     else dominates doms l1 l)) sites
              then [(d, g)] else []) sites.

(** ## The evidence pass

    In a checked-IR function, the [[evidence-pass|evidence pass]] walks
    each block's instructions in order, verifying that every capability
    check is consumed immediately by a covered access and that every other
    raw access is covered by a [[live-fact|live fact]] that still holds.
    Alongside the evidence walk, this section checks that [[limit]] values
    are read only by `check_limit` and that every cycle in the control-flow
    graph traverses at least one [[poll]] safepoint. *)

(** The [src] record packages the four precomputed tables that
    [stage_sources] gathers for a function: its
    [[renew-source|renew sources]], its [[single-definition|single definitions]],
    its justified [[check_ahead|scheduled checks]], and its
    [[repeated-getter|repeated getters]]. *)
Record src : Type := mkSrc {
  s_renews : list (name * (name * Z * Z * Z));
  s_once : list (name * def);
  s_ahead : list name;
  s_getters : list (name * name)
}.

(** Given a module md, a function f, and its dominator intervals doms,
    [stage_sources] computes the [src] tables for f. When f calls `setjmp`,
    all four tables are left empty because a second return from `setjmp`
    can re-enter the function on paths not shown by the control-flow graph,
    disallowing all [[reuse]] forms. *)
Definition stage_sources (md : module) (f : func) (doms : nmap (Z * Z)) : src :=
  if setjmp_func f then mkSrc [] [] [] [] else
  let once := single_definitions f in
  mkSrc (flat_map (fun b => flat_map (fun i => match renew_source once i with
                                               | Some r => [r]
                                               | None => []
                                               end) (b_insts b)) (fn_blocks f))
        once (ahead_justified f once) (repeated_getters md f doms once).

(** When a capability [[check]] or [[reuse]] instruction is immediately
    followed by the memory access it authorizes, both instructions affect
    the set of [[live-fact|live facts]]. The helper [after_check] updates
    the live facts across the check, adds the new [fact] established by
    the check, and then updates the resulting facts across the access. *)
Definition after_check (i access : inst) (q : name) (p : value) (lo hi : Z) (r : rights)
    (al : Z) (live : list fact) : list fact :=
  evidence_after access (mkFact q p lo hi r al :: evidence_after i live).

(** Every raw memory access in a checked function must be authorized
    either by an immediately preceding capability check or by an earlier
    check whose capability guarantee still holds. Given the current
    instruction and the remaining instructions in a block,
    [checked_inst_rest] verifies that a check is immediately consumed by a
    covered access or that a standalone access is covered by a live
    [fact]. *)
Definition checked_inst_rest (s : src) (i : inst) (rest : list inst) (live : list fact)
  : option (list inst * list fact) :=
  let once := s_once s in
  let with_access q p lo hi r al (ok : bool) :=
    if negb ok then None else
    match rest with
    | access :: rest' =>
        if proof_use access q lo hi r al
        then Some (rest', after_check i access q p lo hi r al live)
        else None
    | [] => None
    end in
  match i with
  | Let q A (Check lo hi r al) [p] => with_access q p lo hi r al true
  | Let q A (CheckAhead lo hi r al ahi) [p] =>
      if negb (mem q (s_ahead s)) then None else
      match rest with
      | access :: rest' =>
          if proof_use access q lo ahi r al && ahead_transparent access
          then Some (rest', after_check i access q p lo hi r al live)
          else None
      | [] => None
      end
  | Let q A (CheckLocal _ _ bytes r al) [] =>
      match rest with
      | access :: rest' =>
          match raw_access access with
          | Some (q', _, 0, _) =>
              if name_eqb q' q && covered_access access q 0 bytes r al && storage_effects access Local'
              then Some (rest', evidence_after access (kill q live))
              else None
          | _ => None
          end
      | [] => None
      end
  | Let q F CheckFunction _ =>
      match rest with
      | RawCall _ (Tmp q') _ :: rest' => if name_eqb q' q then Some (rest', []) else None
      | _ => None
      end
  | Let q A (Renew lo hi r al) [q1; p] =>
      match q1 with
      | Tmp n1 =>
          match lookup n1 (s_renews s) with
          | Some (p1, lo1, hi1, al1) =>
              match pointer_distance once p (Tmp p1) with
              | Some d =>
                  with_access q p lo hi r al
                    ((lo1 <=? lo + d) && (hi + d <=? hi1) && (al1 mod al =? 0)
                     && ((lo + d - lo1) mod al =? 0))
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | Let q A (RenewHull lo hi r al) [ql; qh; p] =>
      with_access q p lo hi r al (hull_renewable (s_renews s) once p lo hi al ql qh)
  | Let q A (HalfCheck bd lo hi r al) [q1; p] =>
      with_access q p lo hi r al
        (match q1 with
         | Tmp n1 =>
             match lookup n1 (s_renews s) with
             | Some (p1, lo1, hi1, _) =>
                 match pointer_distance once p (Tmp p1) with
                 | Some d0 => half_known bd lo hi d0 lo1 hi1
                 | None => false
                 end
             | None => false
             end
         | _ => false
         end)
  | Let q A (RenewIf lo hi r al) [p; g] => with_access q p lo hi r al (guard_covers once p g lo hi)
  | Let q A (CheckLimit lo hi r al) [p; u] => with_access q p lo hi r al (limit_covers once p u lo hi)
  | _ =>
      let live' := match i with
                   | Let d P Copy [Global g] =>
                       match lookup d (s_getters s) with
                       | Some g1 => if name_eqb g1 g then kill d live else evidence_after i live
                       | None => evidence_after i live
                       end
                   | _ => evidence_after i live
                   end in
      let ok :=
        match raw_access i with
        | Some (q, x, _, _) =>
            reusing_access i x &&
            match fact_of q live with
            | Some fa =>
                covered_access i q (f_lo fa) (f_hi fa) (f_r fa) (f_al fa)
                || hull_covered i q (f_p fa) (f_lo fa) (f_al fa) live once
            | None => false
            end
        | None =>
            match i with
            | RawCall _ _ _ => false
            | Touch _ => false                                  (* not right after its check *)
            | Call _ (Tmp _) _ => false                         (* unchecked_access *)
            | Let _ P (Add | Sub | Itop) _ => false              (* implicit_flight *)
            | Let _ P Copy [Tmp _] | Let _ P Copy [Const _] => false
            | _ => true
            end
        end in
      if ok then Some (rest, live') else None
  end.

(** Given a basic block's instruction list and the [[live-fact|live facts]]
    that hold at block entry, [checked_insts] applies [checked_inst_rest]
    to each instruction in turn. It returns the live facts that still hold
    at the end of the block, or `None` if any instruction in the block is
    rejected. *)
Fixpoint checked_insts (s : src) (fuel : nat) (is : list inst) (live : list fact)
  : option (list fact) :=
  match is with
  | [] => Some live
  | i :: rest =>
      match fuel with
      | O => None
      | S f =>
          let* rl := checked_inst_rest s i rest live in
          checked_insts s f (fst rl) (snd rl)
      end
  end.

(** Given a list of blocks bs and a target label l, [incoming] returns all
    incoming control-flow edges to l paired with a boolean flag indicating
    whether the edge is a [[poll]] edge, ordered with the last edge first
    to match `ir.pl`. *)
Definition incoming (bs : list block) (l : name) : list (name * bool) :=
  rev (flat_map (fun b => flat_map (fun t => if name_eqb (edge_label t) l
                                             then [(b_label b, is_poll t)] else [])
                                   (jump_targets (b_jump b))) bs).

(** Given a function and its precomputed reuse tables, [evidence_pass]
    walks the function's blocks in order to verify that every memory access
    is authorized by capability [[evidence]]. At the start of each block,
    it intersects the exit facts of already-visited predecessor blocks
    across non-[[poll]] edges, removes facts for temporaries redefined by
    [[phi]] nodes, and checks the block's instructions with
    [checked_insts]. *)
Definition evidence_pass (s : src) (f : func) : bool :=
  match fold_left
          (fun (acc : option (list (name * list fact))) (b : block) =>
             let* exits := acc in
             let sets := map (fun (e : name * bool) => if snd e then []
                                       else match lookup (fst e) exits with
                                            | Some fs => fs
                                            | None => []
                                            end) (incoming (fn_blocks f) (b_label b)) in
             let live0 := evidence_meet sets in
             let live1 := fold_left (fun (fs : list fact) (ph : phi) => match ph with Phi d _ _ =>
                                       filter (fun fa => negb (name_eqb (f_q fa) d
                                                               || value_eqb (f_p fa) (Tmp d))) fs end)
                                    (b_phis b) live0 in
             let* out := checked_insts s (S (length (b_insts b))) (b_insts b) live1 in
             Some (put (b_label b) out exits))
          (fn_blocks f) (Some []) with
  | Some _ => true
  | None => false
  end.

(** Given a function f, [limit_reads] checks that every temporary defined
    by a [[limit]] instruction in f is read only as the second operand of a
    `check_limit` instruction, and never by another instruction, [[phi]]
    node, or jump. *)
Definition limit_reads (f : func) : bool :=
  let limits := flat_map (fun b => flat_map (fun i => match i with
                                                      | Let n _ (Limit _) _ => [n]
                                                      | _ => []
                                                      end) (b_insts b)) (fn_blocks f) in
  let none_read (us : list name) := negb (existsb (fun u => mem u limits) us) in
  match limits with
  | [] => true
  | _ =>
      forallb (fun b =>
                 forallb (fun i =>
                            match i with
                            | Let _ _ (CheckLimit _ _ _ _) [p; u] =>
                                none_read (value_temps [p]) &&
                                match u with Tmp n => mem n limits | _ => false end
                            | _ => none_read (inst_uses i)
                            end) (b_insts b)
                 && none_read (jump_uses (b_jump b))
                 && forallb (fun ph => match ph with
                                       | Phi _ _ pairs => none_read (value_temps (map snd pairs))
                                       end) (b_phis b))
              (fn_blocks f)
  end.

(** Given a step budget fuel and a directed graph g of unpolled block
    edges, [peel] repeatedly removes sink blocks that have no outgoing
    edges into the remaining graph, returning `true` when the entire graph
    reduces to empty and `false` if an unpolled cycle remains. *)
Fixpoint peel (fuel : nat) (g : list (name * list name)) : bool :=
  match g with
  | [] => true
  | _ =>
      match fuel with
      | O => false
      | S f =>
          let left := map fst g in
          let sinks := filter (fun nl => negb (existsb (fun s => mem s left) (snd nl))) g in
          match sinks with
          | [] => false
          | _ => peel f (filter (fun nl => negb (mem (fst nl) (map fst sinks))) g)
          end
      end
  end.

(** Given a function f, [polls_every_cycle] builds the subgraph of
    non-[[poll]] control-flow edges in f and runs [peel] to verify that
    every cycle in f, including unreachable cycles, passes through at least
    one [[poll]] safepoint. *)
Definition polls_every_cycle (f : func) : bool :=
  let g := map (fun b => (b_label b, map edge_label (filter (fun t => negb (is_poll t))
                                                            (jump_targets (b_jump b)))))
               (fn_blocks f) in
  forallb (fun nl => forallb (fun s => mem s (map fst g)) (snd nl)) g
  && peel (S (length g)) g.

(** Given a module md, a function f, and its dominator intervals doms,
    [stage_func] checks all checked-[[stage]] requirements for f:
    [evidence_pass], [limit_reads], and [polls_every_cycle]. *)
Definition stage_func (md : module) (f : func) (doms : nmap (Z * Z)) : bool :=
  evidence_pass (stage_sources md f doms) f && limit_reads f && polls_every_cycle f.

(** ## The stage

    Whether a module is in the unchecked or checked [[stage]] is determined
    by its instruction vocabulary rather than a header flag: if any
    function in the module uses a check, reuse form, raw access, pointer
    [[flight]], or [[poll]] edge, the entire module is judged as checked
    IR. This section tests both core-subset and raw-term functions for
    checked-stage constructs so [valid_func] knows when to run
    [stage_func]. *)

(** Given an operation o, [checked_op] returns `true` when o belongs to the
    checked [[stage]], including capability [[check]] and [[reuse]] forms,
    [[span_test]], [[limit]], raw loads, and raw [[cas]] operations. *)
Definition checked_op (o : op) : bool :=
  match o with
  | Check _ _ _ _ | CheckAhead _ _ _ _ _ | Renew _ _ _ _ | RenewHull _ _ _ _
  | HalfCheck _ _ _ _ _ | SpanTest _ _ | RenewIf _ _ _ _ | Limit _ | CheckLimit _ _ _ _
  | CheckLocal _ _ _ _ _ | CheckFunction | RawLoad _ _ | RawLoadPointer _ _
  | RawCas _ _ => true
  | _ => false
  end.

(** Given an instruction i, [checked_inst] returns `true` when i uses a
    checked-[[stage]] construct: a `let` of a [checked_op], a raw store, a
    `raw_call`, a pointer [[flight]], or a [[touch]]. *)
Definition checked_inst (i : inst) : bool :=
  match i with
  | Let _ _ o _ => checked_op o
  | RawStore _ _ _ _ | RawStorePointer _ _ _ _ | RawCall _ _ _ | Flight _ _ _ _ | Touch _ => true
  | _ => false
  end.

(** Given a block-ending jump j, [checked_jump] returns `true` when j
    traverses a [[poll]] edge. *)
Definition checked_jump (j : jump) : bool := existsb is_poll (jump_targets j).

(** Given a raw operation term t from a function outside the
    [[core-subset|core subset]], [checked_op_term] tests whether t names a
    checked-[[stage]] operation. *)
Definition checked_op_term (t : term) : bool :=
  match t with
  | TAtom "check_function" => true
  | TApp ("check" | "check_ahead" | "renew" | "renew_hull" | "half_check" | "span_test"
          | "renew_if" | "limit" | "check_limit" | "check_local" | "raw_load"
          | "raw_load_pointer" | "raw_cas") _ => true
  | _ => false
  end.

(** Given a raw instruction term t from a function outside the
    [[core-subset|core subset]], [checked_inst_term] tests whether t uses a
    checked-[[stage]] instruction or operation. *)
Definition checked_inst_term (t : term) : bool :=
  match t with
  | TApp "let" [_; _; o; _] => checked_op_term o
  | TApp ("raw_store" | "raw_store_pointer" | "raw_call" | "flight" | "touch") _ => true
  | _ => false
  end.

(** Given a raw jump term t from a function outside the
    [[core-subset|core subset]], [checked_jump_term] tests whether t takes
    a [[poll]] edge. *)
Definition checked_jump_term (t : term) : bool :=
  match t with
  | TApp "goto" [TApp "poll" [_]] => true
  | TApp "branch" [_; a; b] =>
      match a with TApp "poll" [_] => true | _ =>
        match b with TApp "poll" [_] => true | _ => false end end
  | _ => false
  end.

(** Given a module md, [module_checked] returns `true` when any function in
    md—whether inside or outside the [[core-subset|core subset]]—contains a
    checked instruction or a [[poll]] edge, placing the whole module in the
    checked [[stage]]. *)
Definition module_checked (md : module) : bool :=
  existsb (fun it =>
             match it with
             | IFunc f => existsb (fun b => existsb checked_inst (b_insts b)
                                            || checked_jump (b_jump b)) (fn_blocks f)
             | IOutside _ (TApp "func" [_; _; _; _; TList bs]) =>
                 existsb (fun b => match b with
                                   | TApp "block" [_; _; TList is; j] =>
                                       existsb checked_inst_term is || checked_jump_term j
                                   | _ => false
                                   end) bs
             | _ => false
             end) md.

(** ## Functions and modules

    A function in the [[core-subset|core subset]] is valid when its control
    flow, linkage, return type, temporary classes, SSA dominance, local
    allocations, and blocks are all well formed, and when it also passes
    [stage_func] if the module is in the checked [[stage]]. This section
    combines those function-level checks into [valid_func]. *)

(** Given a function f, [extended_crosses] returns `true` when an 80-bit
    extended floating-point value of [[class]] [Extended] appears where the
    ABI and calling convention forbid it: as a function parameter or return
    value, as a call argument or result, or in a [[phi]] node. *)
Definition extended_crosses (f : func) : bool :=
  let ext k := class_eqb k Extended in
  match fn_ret f with RClass k => ext k | _ => false end
  || existsb (fun p => ext (fst p)) (fn_params f)
  || existsb (fun b =>
                existsb (fun ph => match ph with Phi _ k _ => ext k end) (b_phis b)
                || existsb (fun i => match i with
                                     | Call r _ args =>
                                         match r with CResult _ k => ext k | _ => false end
                                         || existsb (fun a => ext (arg_class a)) args
                                     | _ => false
                                     end) (b_insts b)) (fn_blocks f).

(** Given a module and a function from the [[core-subset|core subset]],
    [valid_func] checks that the function satisfies all structural, typing,
    and safety rules of Fil-C [[mode]]. It verifies that the function has
    valid linkage, return types, block labels, temporary classes,
    [[ssa|strict SSA]] dominance, and stack-local declarations, and when
    the module is in the checked [[stage]] it also runs [stage_func]. *)
Definition valid_func (md : module) (f : func) : bool :=
  let bs := fn_blocks f in
  let defs := temp_defs f in
  match bs, block_intervals bs with
  | [], _ | _, None => false
  | entry :: _, Some doms =>
      match fn_linkage f with TAtom ("export" | "local" | "weak") => true | _ => false end
      && match fn_ret f with
         | RTuple ks =>
             (length ks =? 2)%nat
             && forallb (fun k => existsb (class_eqb k) [L; P; Single; Double]) ks
         | RClass k => any_class k
         | RVoid => true
         end
      && negb (extended_crosses f)
      && no_dups (map b_label bs)
      && temp_classes_ok defs
      && negb (existsb (fun b => mem (b_label entry) (succ_labels (b_jump b))) bs)
      && proof_class_defs f
      && definitions_dominate f doms
      && valid_locals f
      && forallb (valid_block md f defs) bs
      && (negb (module_checked md) || stage_func md f doms)
  end.

(** ## Data

    Besides functions, a module can define global data objects with static
    initializers, weak external declarations, and constructor or destructor
    table entries. In Fil-C, every pointer initializer in a data object
    must start at an 8-byte-aligned offset so its capability fits in a
    shadow [[aux]] slot. This section checks data alignments, linkages,
    initializer items, and cross-module symbol references. *)

(** Given an alignment a in bytes, [data_align] tests whether a is a power
    of two between 1 and 4096. *)
Definition data_align (a : Z) : bool :=
  (1 <=? a) && (a <=? 4096) && (Z.land a (a - 1) =? 0).

(** Given a global data linkage lk and a list of initializer items its,
    [data_linkage_ok] checks that lk is a valid Fil-C data linkage and
    that its initializer list matches the linkage kind. Weak external
    declarations must have an empty item list, while constructor and
    destructor table entries must carry a valid priority and a single
    symbol pointer at offset 0. *)
Definition data_linkage_ok (lk : linkage) (its : list data_item) : bool :=
  match lk with
  | LExport | LLocal | LWeak => true
  | LRo (TAtom ("export" | "local" | "weak")) => true
  | LTls (TAtom ("export" | "local")) => true
  | LExternWeak => match its with [] => true | _ => false end
  | LInit k prio =>
      match k with TAtom ("ctor" | "dtor") => true | _ => false end
      && match prio with
         | TAtom "none" => true
         | TInt n => (0 <=? n) && (n <=? 65535)
         | _ => false
         end
      && match its with [Sym _ off] => off =? 0 | _ => false end
  | _ => false
  end.

(** Given a data initializer item it, [data_item_ok] checks that floating-point
    bit patterns fit their width modulus, string literals contain only byte
    values, symbol pointer items name their target with an atom, zero runs
    have non-negative length, and unrecognized item forms [ItemOther] are
    rejected. *)
Definition data_item_ok (it : data_item) : bool :=
  match it with
  | Item Ws n => (0 <=? n) && (n <? 2 ^ 32)
  | Item Wd n => (0 <=? n) && (n <? 2 ^ 64)
  | Item Wx n => (0 <=? n) && (n <? 2 ^ 80)
  | Item _ _ => true
  | Str cs => forallb (fun c => c <=? 255) cs
  | Sym (TAtom _) _ => true
  | Sym _ _ => false
  | Zero n => 0 <=? n
  | ItemOther _ => false
  end.

(** Given a running byte offset off into a data object and a list of data
    items its, [pointer_items_aligned] verifies that every symbol-pointer
    item in its starts at a multiple of 8 bytes. *)
Fixpoint pointer_items_aligned (off : Z) (its : list data_item) : bool :=
  match its with
  | [] => true
  | it :: rest =>
      match it with Sym _ _ => off mod 8 =? 0 | _ => true end
      && pointer_items_aligned (off + item_size it) rest
  end.

(** Given a module md and a symbol name n, [func_named] returns `true` when
    md defines a function named n, whether inside or outside the
    [[core-subset|core subset]]. *)
Definition func_named (md : module) (n : name) : bool :=
  match first_func_linkage n md with Some _ => true | None => false end.

(** Given a module md and a symbol name n, [data_named] returns `true` when
    md defines a non-`extern(weak)` data object named n. *)
Definition data_named (md : module) (n : name) : bool :=
  match first_data_linkage n md with Some _ => true | None => false end.

(** Given a module md, a data object name n, its linkage lk, and its items
    its, [data_names_ok] checks the symbol references of the data object.
    A constructor or destructor entry must name a function defined in md,
    an `extern(weak)` declaration may not shadow a [local_global] symbol of
    md, and no pointer item may refer to a constructor or destructor table
    entry. *)
Definition data_names_ok (md : module) (n : name) (lk : linkage) (its : list data_item) : bool :=
  match lk, its with
  | LInit _ _, [Sym f _] => func_named md f
  | LExternWeak, _ => negb (local_global md n)
  | _, _ => true
  end
  && forallb (fun it => match it with Sym s _ => negb (init_entry_named md s) | _ => true end) its.

(** Given a module md and the name n, linkage lk, byte alignment align, and
    initializer list its of a global data object, [valid_data] checks
    [data_align], [data_linkage_ok], [data_item_ok],
    [pointer_items_aligned], and [data_names_ok]. *)
Definition valid_data (md : module) (n : name) (lk : linkage) (align : Z) (its : list data_item)
  : bool :=
  data_align align && data_linkage_ok lk its && forallb data_item_ok its
  && pointer_items_aligned 0 its && data_names_ok md n lk its.

(** ## Aliases

    A symbol alias gives an additional exported or weak name to a function
    or data object defined in the same module. To prevent a direct call
    from jumping to a data object through an alias, the validator checks
    that any alias targeting data is never called directly by another
    function in the module. This section defines those alias checks. *)

(** Given a list of already-seen names seen and a module md, [first_funcs]
    returns the first function item of each function name in md, matching
    the symbol index built by `ir.pl`. *)
Fixpoint first_funcs (seen : list name) (md : module) : list item :=
  match md with
  | [] => []
  | IFunc f :: rest =>
      if mem (fn_name f) seen then first_funcs seen rest
      else IFunc f :: first_funcs (fn_name f :: seen) rest
  | IOutside n t :: rest =>
      if mem n seen then first_funcs seen rest
      else IOutside n t :: first_funcs (n :: seen) rest
  | _ :: rest => first_funcs seen rest
  end.

(** Given a function item it and a global symbol name n, [calls_global]
    returns `true` when any instruction in it makes a direct call to n,
    whether it is a [[core-subset|core subset]] function or a raw term. *)
Definition calls_global (it : item) (n : name) : bool :=
  match it with
  | IFunc f =>
      existsb (fun b => existsb (fun i => match i with
                                          | Call _ (Global g) _ => name_eqb g n
                                          | _ => false
                                          end) (b_insts b)) (fn_blocks f)
  | IOutside _ (TApp "func" [_; _; _; _; TList bs]) =>
      existsb (fun b => match b with
                        | TApp "block" [_; _; TList is; _] =>
                            existsb (fun i => match i with
                                              | TApp "call" [_; TApp "global" [g]; _] => term_eqb g n
                                              | _ => false
                                              end) is
                        | _ => false
                        end) bs
  | _ => false
  end.

(** Given a module item it, [item_name] returns its function name when it
    is a core-subset or raw-term function, and `None` otherwise. *)
Definition item_name (it : item) : option name :=
  match it with IFunc f => Some (fn_name f) | IOutside n _ => Some n | _ => None end.

(** Given a module md, an alias name n, a linkage term lk, and a target
    symbol name target, [valid_alias] checks that the alias has `export` or
    `weak` linkage, does not collide with any function or data name, and
    targets either a defined function or an allowed data object that no
    other function in md calls through n. *)
Definition valid_alias (md : module) (n : name) (lk : term) (target : name) : bool :=
  match lk with TAtom ("export" | "weak") => true | _ => false end
  && negb (func_named md n || data_named md n)
  && (func_named md target
      || match first_data_linkage target md with
         | Some (LExport | LLocal | LWeak | LRo _ | LTls _) =>
             negb (existsb (fun it => match item_name it with
                                      | Some g => negb (name_eqb g n) && calls_global it n
                                      | None => false
                                      end) (first_funcs [] md))
         | _ => false
         end).

(** ## Modules

    At the top level, a module is a list of functions, data objects, and
    aliases that share a single global symbol namespace. This final section
    checks that no two definitions in the module share a name and combines
    all item checks into the top-level [valid] judgment. *)

(** Given a module item it, [defined_name] returns the global symbol name
    that it defines, or `None` for an `extern(weak)` declaration, which
    declares a symbol without defining it. *)
Definition defined_name (it : item) : option name :=
  match it with
  | IFunc f => Some (fn_name f)
  | IOutside n _ => Some n
  | IData _ LExternWeak _ _ => None
  | IData n _ _ _ => Some n
  | IAlias n _ _ => Some n
  end.

(** Given a module md, [unique_names] checks that no two items in md define
    the same global symbol name across functions, data objects, and
    aliases. *)
Definition unique_names (md : module) : bool :=
  match fold_left (fun acc it =>
                     let* seen := acc in
                     match defined_name it with
                     | Some n => if nm_mem n seen then None else Some (nm_add n tt seen)
                     | None => Some seen
                     end) md (Some nm_empty) with
  | Some _ => true
  | None => false
  end.

(** Given a module md, [valid_items] checks that all defined symbol names
     satisfy [unique_names] and that every function, data object, and alias
    in the [[core-subset|core subset]] passes its validator check. *)
Definition valid_items (md : module) : bool :=
  unique_names md &&
  forallb (fun it => match it with
                     | IFunc f => valid_func md f
                     | IData n lk al its => valid_data md n lk al its
                     | IAlias n lk t => valid_alias md n lk t
                     | IOutside _ _ => true
                     end) md.

(** Given a module md, [valid] returns `None` if any function in md uses
    constructs outside the [[core-subset|core subset]], and otherwise
    returns `Some` with the boolean verdict of [valid_items]. Provenance
    [[context]] records from `ir.pl` are omitted here because the runtime
    semantics never reads them. *)
Definition valid (md : module) : option bool :=
  if existsb (fun it => match it with IOutside _ _ => true | _ => false end) md then None
  else Some (valid_items md).
