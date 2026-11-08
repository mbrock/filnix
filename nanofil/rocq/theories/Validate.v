(** The validator of checked IR, transcribed from ir.pl's
    `valid_module/1` for the core subset: `valid_func md f` is true
    exactly when ir.pl accepts the function f of the module md, checked
    stage, filc mode; `valid_data` and `valid_alias` do the same for
    the module's data objects and aliases.

    ir.pl's validator throws `nanofil_error(Message)` at the first
    problem and fails on a few terms outside the grammar; both are
    `false` here. The order of the tests therefore does not matter, and
    the definitions below follow ir.pl's clause groups, not its order of
    evaluation.

    ## Parts

    | Gallina | ir.pl | Checks |
    |---|---|---|
    | `valid_use` | `valid_use/3` | an operand read at a class its definition allows |
    | `valid_op`, `op_result_ok` | `valid_op/1`, `op_result_ok/3` | an op's parameters and its result class |
    | `valid_inst`, `valid_jump`, `valid_phi` | the same | each instruction, jump and phi |
    | `definitions_dominate` | the same | strict SSA: every use has a dominating definition |
    | `valid_locals` | the same | named locals declared once, in the entry block, before use |
    | `stage_func` | the same | every access covered by evidence that still holds; a poll on every cycle |
    | `valid_data` | `valid_item/4` for data | alignment, linkage, item shapes; a table entry names a function, a weak declaration no local definition, no pointer a table entry |
    | `valid_alias` | `valid_item/4` for aliases | linkage, a name of its own, a target the module defines |

    `stage_func` is the part Campaign 3 is about. A block's entry
    evidence is the meet over its incoming edges of what each carries
    (none over a poll edge or from a block later in block order); a
    check must be followed at
    once by an access it covers; a later scalar access may read a proof
    whose fact is still live; and each reuse form (`renew`,
    `renew_hull`, `half_check`, `renew_if`, `check_limit`,
    `check_ahead`) has its own side conditions, stated over the
    single-definition names of the function (`Once`), the chains of
    flights from a pointer to its bases (`guard_chain`) and the
    intervals of offsets (`offset_interval`).

    ## Where Prolog's evaluation shows through

    The transcription keeps three places where ir.pl's result depends on
    how Prolog evaluates, not only on what the clauses say:

    - `offset_interval/8` memoises each name's interval under a depth
      limit of 32. A failure is never kept (the memo is discarded on
      backtracking), but a success is, so a name met again deeper than
      the limit allows still has its interval. `oi` threads the same
      memo in the same order.
    - `pointer_distance/4` commits to the first base of P's chain that
      P1's chain shares (a cut). `pointer_distance` takes the same
      first one.
    - `op_interval/9`'s clauses commit by cuts after their heads, so an
      `and` with a constant tries its left operand before its right one,
      and a failed `ext(sw)` does not fall through to a later clause. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Syntax Values Memory Ops Semantics Cfg.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Names, uses and definitions *)

Definition mem (n : name) (ns : list name) : bool := existsb (name_eqb n) ns.

Definition value_eqb (v w : value) : bool :=
  match v, w with
  | Tmp a, Tmp b | Global a, Global b => name_eqb a b
  | Const a, Const b => Z.eqb a b
  | _, _ => false
  end.

Definition value_temps (vs : list value) : list name :=
  flat_map (fun v => match v with Tmp n => [n] | _ => [] end) vs.

(** `inst_temp_def(Inst, N, K)`: the temporaries an instruction defines,
    with their classes. *)
Definition inst_temp_defs (i : inst) : list (name * class) :=
  match i with
  | Let d k _ _ => [(d, k)]
  | Flight d _ _ _ => [(d, P)]
  | Call r _ _ | RawCall r _ _ =>
      match r with CVoid => [] | CResult d k => [(d, k)] | CTuple rs => rs end
  | _ => []
  end.

(** cfg.pl's `inst_def(Inst, D)`, its first solution. *)
Definition inst_def_first (i : inst) : option name :=
  match inst_temp_defs i with (d, _) :: _ => Some d | [] => None end.

Definition arg_value (a : arg) : value := match a with Arg _ v => v end.
Definition arg_class (a : arg) : class := match a with Arg k _ => k end.

Definition flight_arg_value (a : flight_arg) : value :=
  match a with FValue v => v | FAddress p => p end.

(** cfg.pl's `inst_uses(Inst, Uses)`. *)
Definition inst_uses (i : inst) : list name :=
  match i with
  | Let _ _ _ args => value_temps args
  | Flight _ _ args lw =>
      value_temps (map flight_arg_value args
                   ++ match lw with LowerOf p => [p] | LowerNone => [] end)
  | RawStore _ _ v a | RawStorePointer _ v a _ => value_temps [v; a]
  | Call _ f args | RawCall _ f args => value_temps (f :: map arg_value args)
  | LocalAlloc _ _ | Loc _ _ => []
  end.

(** cfg.pl's `jump_uses(Jump, Uses)`. *)
Definition jump_uses (j : jump) : list name :=
  match j with
  | JBranch v _ _ | JRet v => value_temps [v]
  | JRets vs => value_temps vs
  | _ => []
  end.

(** `jump_edge(Jump, T)`: the jump's targets, both arms of a branch. *)
Definition jump_targets (j : jump) : list target :=
  match j with JGoto t => [t] | JBranch _ t1 t2 => [t1; t2] | _ => [] end.

Definition succ_labels (j : jump) : list name := map edge_label (jump_targets j).

Definition is_poll (t : target) : bool := match t with Poll _ => true | To _ => false end.

(** ## Dominance *)

(** The labels of the blocks that jump to l, unreachable ones included. *)
Definition preds_of (bs : list block) (l : name) : list name :=
  map b_label (filter (fun b => mem l (succ_labels (b_jump b))) bs).

(** The same labels, in any order and number. *)
Definition sets_eqb (a b : list name) : bool :=
  forallb (fun x => mem x b) a && forallb (fun x => mem x a) b.

(** `dominates_by_interval(Intervals, A, B)` over the intervals of
    Cfg.v's `block_intervals`. *)
Definition dominates (doms : nmap (Z * Z)) (a b : name) : bool := dominates_by_interval doms a b.

(** A label is reachable when it has an interval. *)
Definition is_reachable (doms : nmap (Z * Z)) (l : name) : bool := nm_mem l doms.

(** A definition site of a temporary: `param`, or `at(L, I)`, index I of
    block L, a phi's at -1. *)
Inductive site : Type := SParam | SAt (l : name) (i : Z).

(** `block_sites(Blocks)` with the parameters' sites: each temporary
    with its definition sites. *)
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

(** `site_dominates(Def, L, I, Intervals)`: the definition comes before
    position I of block L on every path from the entry. *)
Definition site_dominates (doms : nmap (Z * Z)) (l : name) (i : Z) (s : site) : bool :=
  match s with
  | SParam => true
  | SAt d j => if name_eqb d l then j <? i else dominates doms d l
  end.

(** `dominated_use(D, L, I, N)`: some definition of N dominates
    position I of block L. *)
Definition dominated_use (sites : nmap (list site)) (doms : nmap (Z * Z)) (l : name) (i : Z)
    (n : name) : bool :=
  match nm_find n sites with
  | Some defs => existsb (site_dominates doms l i) defs
  | None => false
  end.

(** `definitions_dominate(Fn, Params, Blocks)`: in every reachable
    block, each use is dominated by a definition; a phi's operand is
    used at the end of its predecessor, if that is reachable. *)
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

(** ## Classes of temporaries *)

(** `temp_defs(Params, Blocks, Defs)`. *)
Definition temp_defs (f : func) : list (name * class) :=
  map (fun p => (snd p, fst p)) (fn_params f) ++
  flat_map (fun b => map (fun ph => match ph with Phi d k _ => (d, k) end) (b_phis b)
                     ++ flat_map inst_temp_defs (b_insts b)) (fn_blocks f).

(** `check_temp_classes(Fn, Defs)`: one class per temporary, that is,
    every definition has the class of the temporary's first one. *)
Definition temp_classes_ok (defs : list (name * class)) : bool :=
  let first := fold_left (fun m d => if nm_mem (fst d) m then m else nm_add (fst d) (snd d) m)
                         defs nm_empty in
  forallb (fun d => match nm_find (fst d) first with
                    | Some k => class_eqb k (snd d)
                    | None => false
                    end) defs.

Definition proof_class (k : class) : bool := match k with A | F => true | _ => false end.

(** `valid_use(Ctx, K, V)`: V may be read at class K. A proof or float
    temporary is read only at its own class, and the reverse; a `p`
    temporary only at `p`, and the reverse; a long may be read as a
    word; a float constant is a bit pattern of its class; only a check
    makes a proof; in filc mode only `copy` reads a symbol. *)
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

(** ## Ops *)

Definition check_align (al : Z) : bool :=
  existsb (Z.eqb al) [1; 2; 4; 8; 16].

(** `alloc_align(Align)`: a power of two from 4 to 4096. *)
Definition alloc_align (al : Z) : bool :=
  (4 <=? al) && (al <=? 4096) && (Z.land al (al - 1) =? 0).

Definition check_ok (lo hi al : Z) : bool := (lo <? hi) && check_align al.

Definition local_offset (off : Z) : bool := (- 2 ^ 63 <=? off) && (off <? 2 ^ 63).

Definition store_effects : list effect :=
  [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite].
Definition local_store_effects : list effect := [LowerWrite; AddressWrite].
Definition atomic_load_effects : list effect := [AtomicRead].
Definition atomic_store_effects : list effect := [AtomicWrite].

(** `comparison(Cond, K)`: the signed and unsigned orders at an
    integer class, the float conditions at a float class, `eq` and `ne`
    at both. *)
Definition comparison (c : cond) (k : class) : bool :=
  match c with
  | Eq | Ne => int_class k || float_class k
  | Sle | Slt | Sge | Sgt | Ule | Ult | Uge | Ugt => int_class k
  | Le | Lt | Ge | Gt | Ord | Unord => float_class k
  end.

(** `valid_op(Op)` for the core subset's ops. *)
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

(** `any_class(K)`: a class a value may have, every class but the
    proofs'. *)
Definition any_class (k : class) : bool := negb (proof_class k).

(** `op_result_ok(filc, Op, K)`. *)
Definition op_result_ok (o : op) (k : class) : bool :=
  match o with
  | Add | Sub | Copy => any_class k
  | Mul | Div => int_class k || float_class k
  | Udiv | Rem | Urem | And | Or | Xor | Sar | Shr | Shl => int_class k
  | Neg => int_class k || float_class k
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
  | VaArgs => class_eqb k P
  | VaArg => any_class k
  end.

(** ## Signatures *)

Definition eclass (k : class) : term :=
  TAtom (match k with
         | W => "w" | L => "l" | P => "p" | A => "a" | F => "f"
         | Single => "s" | Double => "d" | Extended => "x"
         end).

Definition eret (r : ret_type) : term :=
  match r with
  | RClass k => eclass k
  | RVoid => TAtom "void"
  | RTuple ks => TApp "tuple" [TList (map eclass ks)]
  end.

(** What a call site needs of its callee (`func_named/3`'s func): its
    linkage, parameter classes, return and whether it is variadic. *)
Record sig : Type := mkSig {
  sig_linkage : term;
  sig_params : list term;
  sig_ret : term;
  sig_variadic : bool
}.

Definition is_va_args (t : term) : bool :=
  match t with
  | TApp "let" [_; TAtom "p"; TAtom "va_args"; _] => true
  | _ => false
  end.

(** The signature of a function outside the subset, read off its term. *)
Definition term_sig (t : term) : option sig :=
  match t with
  | TApp "func" [_; lk; r; TList ps; TList bs] =>
      Some (mkSig lk (map (fun p => match p with TApp "param" [k; _] => k | _ => p end) ps) r
                  (existsb (fun b => match b with
                                     | TApp "block" [_; _; TList is; _] => existsb is_va_args is
                                     | _ => false
                                     end) bs))
  | _ => None
  end.

(** `func_named(M, Name, Func)`: the first function of that name. *)
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

Definition float_atom (t : term) : bool :=
  match t with TAtom ("s" | "d" | "x") => true | _ => false end.

Definition class_atom (t : term) : bool :=
  match t with TAtom ("w" | "l" | "p" | "s" | "d" | "x") => true | _ => false end.

(** `call_result_ok(Fn, Callee, Res, CalleeRet)`. *)
Definition call_result_ok (r : call_result) (ret : term) : bool :=
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

Fixpoint prefix_eqb (ps xs : list term) : bool :=
  match ps, xs with
  | [], _ => true
  | p :: ps', x :: xs' => term_eqb p x && prefix_eqb ps' xs'
  | _, _ => false
  end.

(** ## Instructions, jumps and phis *)

Definition labels (f : func) : list name := map b_label (fn_blocks f).

(** `store_value_class(Width, K)` for a raw store, which is never of a
    pointer. *)
Definition width_value_ok (w : width) : option class :=
  match w with
  | Wb | Wh | Ww => Some W | Wl => Some L
  | Ws => Some Single | Wd => Some Double | Wx => Some Extended
  | Wp => None
  end.

(** `not_init_entry(M, Fn, S)`, negated: S names a constructor or
    destructor table entry, which nothing may copy or call. *)
Definition init_entry_named (md : module) (s : name) : bool :=
  existsb (fun it => match it with IData n (LInit _ _) _ _ => name_eqb n s | _ => false end) md.

(** `valid_inst(Ctx, Inst)`. *)
Definition valid_inst (md : module) (classes : list (name * class)) (i : inst) : bool :=
  let use := valid_use classes in
  match i with
  | Loc file _ => match file with TAtom _ => true | _ => false end
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

(** `valid_jump(Ctx, Jump)`. *)
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

(** `valid_phi(Ctx, Label, Preds, Phi)`: a phi's predecessors are the
    block's, as sets, and its values are read at its class. *)
Definition valid_phi (classes : list (name * class)) (preds : list name) (ph : phi) : bool :=
  match ph with
  | Phi _ k pairs =>
      sets_eqb (map fst pairs) preds && forallb (fun pv => valid_use classes k (snd pv)) pairs
  end.

(** `valid_block(Ctx, Block)`. *)
Definition valid_block (md : module) (f : func) (classes : list (name * class)) (b : block)
  : bool :=
  let preds := preds_of (fn_blocks f) (b_label b) in
  forallb (valid_phi classes preds) (b_phis b)
  && forallb (valid_inst md classes) (b_insts b)
  && valid_jump f classes (b_jump b)
  && (match b_phis b, preds with _ :: _, [] => false | _, _ => true end).

(** `proof_class_defs(Fn, Params, Blocks)`: only a check defines a
    proof; no parameter, phi, call result or argument is one. *)
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

Fixpoint no_dups (ns : list name) : bool :=
  match ns with [] => true | n :: rest => negb (mem n rest) && no_dups rest end.

(** `valid_locals(Fn, Params, Blocks)`: each local is declared once, in
    the entry block, before each check_local of it there; in another
    block a reference needs only the declaration. *)
Definition valid_locals (f : func) : bool :=
  let objs := local_objects f in
  no_dups (map fst objs) &&
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

(** ## Evidence *)

(** `live(Q, P, Lo, Hi, Rights, Align)`: Q proves Rights over
    [P+Lo, P+Hi) at Align, and its evidence still holds. *)
Record fact : Type := mkFact {
  f_q : name; f_p : value; f_lo : Z; f_hi : Z; f_r : rights; f_al : Z
}.

Definition fact_eqb (a b : fact) : bool :=
  name_eqb (f_q a) (f_q b) && value_eqb (f_p a) (f_p b) && Z.eqb (f_lo a) (f_lo b)
  && Z.eqb (f_hi a) (f_hi b) && rights_eqb (f_r a) (f_r b) && Z.eqb (f_al a) (f_al b).

(** `evidence_names(D, Fact)` and `evidence_kill/3`. *)
Definition kill (d : name) (fs : list fact) : list fact :=
  filter (fun f => negb (name_eqb (f_q f) d || value_eqb (f_p f) (Tmp d))) fs.

(** `evidence_after(Inst, Live0, Live)`. *)
Definition evidence_after (i : inst) (fs : list fact) : list fact :=
  if evidence_preserving i
  then match inst_def_first i with Some d => kill d fs | None => fs end
  else [].

(** The live fact of Q, the newest (`get_assoc(Q, ByQ, _)`). *)
Fixpoint fact_of (q : name) (fs : list fact) : option fact :=
  match fs with [] => None | f :: rest => if name_eqb (f_q f) q then Some f else fact_of q rest end.

(** `evidence_meet(Sets, Live)`. *)
Definition evidence_meet (sets : list (list fact)) : list fact :=
  match sets with
  | [] => []
  | s :: ss => filter (fun f => forallb (fun s' => existsb (fact_eqb f) s') ss) s
  end.

(** ## Accesses *)

(** What a raw access reads or writes: a load type, a store width, or a
    pointer (raw_access/5's X). *)
Inductive access_type : Type := XLoad (t : load_type) | XWidth (w : width) | XPtr.

(** `raw_access(Inst, Q, X, Off, Rights)`. *)
Definition raw_access (i : inst) : option (name * access_type * Z * rights) :=
  match i with
  | Let _ _ (RawLoad t off) [Tmp q] => Some (q, XLoad t, off, Read)
  | RawStore w off _ (Tmp q) => Some (q, XWidth w, off, Write)
  | Let _ _ (RawLoadPointer off _) [Tmp q] => Some (q, XPtr, off, Read)
  | RawStorePointer off _ (Tmp q) _ => Some (q, XPtr, off, Write)
  | _ => None
  end.

(** `access_size_align(X, Size, Align)`, its first solution. *)
Definition access_size_align (x : access_type) : Z * Z :=
  match x with
  | XLoad (LdL | LdD) => (8, 1)
  | XLoad LdS => (4, 1)
  | XLoad LdX => (10, 8)
  | XLoad (LdNarrow t) => (fst (narrow_type t), 1)
  | XWidth Wp | XPtr => (8, 8)
  | XWidth Wx => (10, 8)
  | XWidth w => (width_bytes w, 1)
  end.

Definition rights_allow (have need : rights) : bool :=
  match have, need with Write, _ => true | Read, Read => true | Read, Write => false end.

(** `covered_access(Access, Q, Lo, Hi, Rights, Align)`. *)
Definition covered_access (i : inst) (q : name) (lo hi : Z) (r : rights) (al : Z) : bool :=
  match raw_access i with
  | Some (q', x, off, need) =>
      let (size, aa) := access_size_align x in
      name_eqb q' q && (lo <=? off) && (off + size <=? hi)
      && (al mod aa =? 0) && ((off - lo) mod aa =? 0) && rights_allow r need
  | None => false
  end.

Inductive storage : Type := Heap' | Local'.

(** `access_storage_effects(Access, Storage)`. *)
Definition storage_effects (i : inst) (s : storage) : bool :=
  match i, s with
  | Let _ _ (RawLoad _ _) _, _ | RawStore _ _ _ _, _ => true
  | Let _ P (RawLoadPointer _ es) _, Heap' =>
      effects_eqb es load_effects || effects_eqb es atomic_load_effects
  | Let _ P (RawLoadPointer _ es) _, Local' => effects_eqb es local_load_effects
  | RawStorePointer _ _ _ es, Heap' =>
      effects_eqb es store_effects || effects_eqb es atomic_store_effects
  | RawStorePointer _ _ _ es, Local' => effects_eqb es local_store_effects
  | _, _ => false
  end.

(** `proof_use(Access, Q, Lo, Hi, Rights, Align)`: a heap raw access the
    proof Q covers. *)
Definition proof_use (i : inst) (q : name) (lo hi : Z) (r : rights) (al : Z) : bool :=
  covered_access i q lo hi r al && storage_effects i Heap'.

(** `reusing_access(Inst, X)`: a scalar access, or a heap pointer load,
    may read a proof that is not its own check's. *)
Definition reusing_access (i : inst) (x : access_type) : bool :=
  match x with
  | XPtr => match i with
            | Let _ P (RawLoadPointer _ es) _ => effects_eqb es load_effects
            | _ => false
            end
  | _ => true
  end.

(** ## Single definitions, chains and intervals *)

(** A name's one definition (single_definitions/3's Once). *)
Inductive def : Type := DParam | DPhi (ph : phi) | DInst (i : inst).

Definition all_defs (f : func) : list (name * def) :=
  map (fun p => (snd p, DParam)) (fn_params f) ++
  flat_map (fun b => map (fun ph => match ph with Phi d _ _ => (d, DPhi ph) end) (b_phis b)
                     ++ flat_map (fun i => map (fun dk => (fst dk, DInst i)) (inst_temp_defs i))
                                 (b_insts b)) (fn_blocks f).

(** `single_definitions(Params, Blocks, Once)`. *)
Definition single_definitions (f : func) : list (name * def) :=
  let ds := all_defs f in
  filter (fun d => (length (filter (fun d' => name_eqb (fst d) (fst d')) ds) =? 1)%nat) ds.

Definition once_has (once : list (name * def)) (n : name) : bool :=
  match lookup n once with Some _ => true | None => false end.

(** `near_offset(K)`. *)
Definition near_offset (k : Z) : bool := (- 2 ^ 62 <=? k) && (k <=? 2 ^ 62).

(** `signed_value(K, C, V)` for the integer classes. *)
Definition signed_value (k : class) (c : Z) : option Z :=
  let* bits := class_bits k in
  let u := c mod 2 ^ bits in
  Some (if 2 ^ (bits - 1) <=? u then u - 2 ^ bits else u).

(** `narrow_range(T, Lo, Hi)`. *)
Definition narrow_range (t : narrow) : option (Z * Z) :=
  match t with
  | Ub => Some (0, 255) | Uh => Some (0, 65535)
  | Sb => Some (-128, 127) | Sh => Some (-32768, 32767)
  | _ => None
  end.

(** `interval_fits(K, Lo, Hi)`: a `w` result must not wrap. *)
Definition interval_fits (k : class) (lo hi : Z) : bool :=
  match k with
  | W => (- 2 ^ 31 <=? lo) && (hi <=? 2 ^ 31 - 1)
  | L => true
  | _ => false
  end.

Definition memo := list ((name * class) * option (Z * Z)).

Fixpoint memo_lookup (n : name) (k : class) (m : memo) : option (option (Z * Z)) :=
  match m with
  | [] => None
  | (nk, r) :: rest =>
      if name_eqb (fst nk) n && class_eqb (snd nk) k then Some r else memo_lookup n k rest
  end.

Definition is_const (v : value) : bool := match v with Const _ => true | _ => false end.

(** `op_interval(Op, Args, K, Once, Depth, Lo, Hi, Memo0, Memo)`, with
    rec the walk of an operand one level deeper. Each clause commits
    once its head matches, as ir.pl's cuts do. *)
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

(** `offset_interval(Once, V, K, Depth, Lo, Hi, Memo0, Memo)`: every
    value V of class K can hold lies in [Lo, Hi] (for `l`, modulo
    2^64). A failed walk leaves the memo as it was, then records the
    name as having none. *)
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

Definition offset_interval (once : list (name * def)) (v : value) (k : class) : option (Z * Z) :=
  fst (oi once 33 v k 0 []).

(** `flight_term(Op, Args, B, O, Sign)`. *)
Definition flight_term (o : op) (args : list flight_arg) (b : value) : option (value * Z) :=
  match o, args with
  | Add, [FAddress b0; FValue ov] => if value_eqb b0 b then Some (ov, 1) else None
  | Sub, [FAddress b0; FValue ov] => if value_eqb b0 b then Some (ov, -1) else None
  | Copy, [FAddress b0] => if value_eqb b0 b then Some (Const 0, 1) else None
  | _, _ => None
  end.

(** `guard_chain(Once, P, Chain)`: P at offset [0, 0] of itself, then
    each base B whose capability P has, through single-definition add,
    sub and copy flights whose lower donor is their address operand, at
    the interval of P's offset from B. *)
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

Definition guard_chain (once : list (name * def)) (p : value) : list (value * (Z * Z)) :=
  guard_chain_go once 64 p 0 0.

(** A chain element that is an exact single-definition base. *)
Definition exact_base (once : list (name * def)) (e : value * (Z * Z)) : option (name * Z) :=
  match e with
  | (Tmp n, (k, k')) => if (k =? k') && once_has once n then Some (n, k) else None
  | _ => None
  end.

Fixpoint first_some {X Y : Type} (f : X -> option Y) (xs : list X) : option Y :=
  match xs with [] => None | x :: rest => match f x with Some y => Some y | None => first_some f rest end end.

(** `pointer_distance(Once, P, P1, D)`: the first exact base of P's
    chain that P1's chain has exactly too, D its offset difference. *)
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

(** `half_known(Bound, Lo, Hi, D0, Lo1, Hi1)`. *)
Definition half_known (bd : bound) (lo hi d0 lo1 hi1 : Z) : bool :=
  let d := ((d0 + 2 ^ 63) mod 2 ^ 64) - 2 ^ 63 in
  let e := d + lo - lo1 in
  let f := d + hi - hi1 in
  near_offset e && near_offset f && (hi - lo <=? 2 ^ 62) &&
  match bd with Upper => 0 <=? e | Lower => f <=? 0 end.

(** A renew source: the checked pointer, bounds and alignment of a
    single-definition proof (`renew_source_op/6`). *)
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

(** `hull_renewable(Sources, Once, P, Lo, Hi, Align, QL, QH)`. *)
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

(** `guard_covers(Once, P, G, Lo, Hi)`. *)
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

(** `lower_chain(Once, P, B)`: P has B's lower. *)
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

(** `limit_covers(Once, P, U, Lo, Hi)`. *)
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

(** `hull_covered(Access, Q, P, Lo, Align, Live, Once)`: the access lies
    within the hull of the live facts of P's object. *)
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

(** ## Scheduled checks *)

Definition facts := list (name * Z).

Definition del (n : name) (fs : facts) : facts := filter (fun f => negb (name_eqb (fst f) n)) fs.

(** `ahead_meet(Facts, Meet)`: the bases in every one of Facts, each
    with its least need. *)
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

(** `raise_need(Once, Off, Size, B-i(K, K1), F0, F)`. *)
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

(** `ahead_step(I, Once, Ptrs, F0, F)`. *)
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

(** `proof_pointers(Blocks, Once, Ptrs)`: each single-definition heap
    proof with the pointer it proves (`proof_pointer/3`). *)
Definition proof_pointer (o : op) (args : list value) : option value :=
  match o, args with
  | Check _ _ _ _, [p] | CheckAhead _ _ _ _ _, [p] => Some p
  | Renew _ _ _ _, [_; p] | HalfCheck _ _ _ _ _, [_; p] => Some p
  | RenewHull _ _ _ _, [_; _; p] => Some p
  | RenewIf _ _ _ _, [p; _] | CheckLimit _ _ _ _, [p; _] => Some p
  | _, _ => None
  end.

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

(** The check_ahead proofs `ahead_insts/8` accepts in one block, walking
    its instructions from the last: `next` are the facts after the
    instruction that follows the current one, its access. *)
Fixpoint ahead_insts (once : list (name * def)) (ptrs : list (name * value)) (ris : list inst)
    (after next : facts) (js : list name) : facts * list name :=
  match ris with
  | [] => (after, js)
  | i :: rest =>
      let js1 :=
        match i with
        | Let q A (CheckAhead lo hi _ _ _) [p] =>
            if once_has once q &&
               existsb (fun e => match exact_base once e with
                                 | Some (n, k) =>
                                     near_offset k && near_offset (k + lo) &&
                                     match lookup n next with Some h => k + hi <=? h | None => false end
                                 | None => false
                                 end) (guard_chain once p)
            then q :: js else js
        | _ => js
        end in
      ahead_insts once ptrs rest (ahead_step once ptrs i after) after js1
  end.

Fixpoint index_of (l : name) (ls : list name) (n : nat) : option nat :=
  match ls with [] => None | l' :: rest => if name_eqb l l' then Some n else index_of l rest (S n) end.

(** `ahead_justified(Blocks, Once, Ahead)`: the needs computed backward
    in one pass over the blocks in reverse order. An edge carries its
    target's entry facts only if it is plain and goes to a later block. *)
Definition ahead_justified (f : func) (once : list (name * def)) : list name :=
  let bs := fn_blocks f in
  let order := map b_label bs in
  let ptrs := proof_pointers f once in
  snd (fold_left
         (fun (st : list (name * facts) * list name) (b : block) =>
            let (ins, js) := st in
            let pos := index_of (b_label b) order 0 in
            let edge (t : target) : facts :=
              match t with
              | Poll _ => []
              | To l =>
                  match index_of l order 0, pos, lookup l ins with
                  | Some tp, Some p, Some fs => if (p <? tp)%nat then fs else []
                  | _, _, _ => []
                  end
              end in
            let out := ahead_meet (map edge (jump_targets (b_jump b))) in
            let '(entry0, js') := ahead_insts once ptrs (rev (b_insts b)) out [] js in
            let entry := fold_left (fun (fs : facts) (ph : phi) => match ph with Phi d _ _ => del d fs end)
                                   (b_phis b) entry0 in
            (put (b_label b) entry ins, js'))
         (rev bs) ([], [])).

(** ## Getters *)

(** `local_global(Symbols, G)`: G is a function or data object this
    module defines with local linkage, the first item of its name. *)
Fixpoint first_func_linkage (g : name) (md : module) : option term :=
  match md with
  | [] => None
  | IFunc f :: rest => if name_eqb (fn_name f) g then Some (fn_linkage f) else first_func_linkage g rest
  | IOutside n t :: rest =>
      if name_eqb n g then match t with TApp "func" [_; lk; _; _; _] => Some lk | _ => None end
      else first_func_linkage g rest
  | _ :: rest => first_func_linkage g rest
  end.

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

(** `repeated_getters(Symbols, Blocks, Once, Getters)`: each
    single-definition getter copy of a local symbol that another copy of
    the same symbol dominates (earlier in its block, or in a block that
    strictly dominates it). *)
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

(** ## The evidence pass *)

(** `stage_sources/4`'s src: the renew sources, the single definitions,
    the justified check_aheads and the repeated getters. *)
Record src : Type := mkSrc {
  s_renews : list (name * (name * Z * Z * Z));
  s_once : list (name * def);
  s_ahead : list name;
  s_getters : list (name * name)
}.

Definition stage_sources (md : module) (f : func) (doms : nmap (Z * Z)) : src :=
  let once := single_definitions f in
  mkSrc (flat_map (fun b => flat_map (fun i => match renew_source once i with
                                               | Some r => [r]
                                               | None => []
                                               end) (b_insts b)) (fn_blocks f))
        once (ahead_justified f once) (repeated_getters md f doms once).

(** The evidence after a check-like instruction i of proof q over
    [lo, hi) and its access (`evidence_after`, `evidence_add`,
    `evidence_after`). *)
Definition after_check (i access : inst) (q : name) (p : value) (lo hi : Z) (r : rights)
    (al : Z) (live : list fact) : list fact :=
  evidence_after access (mkFact q p lo hi r al :: evidence_after i live).

(** `checked_inst_rest(Inst, Insts, Fn-Sources, Mode, Live0, Rest, Live)`:
    None when ir.pl throws; otherwise the instructions left and the
    evidence after. A check-like instruction consumes its access. *)
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
            | Call _ (Tmp _) _ => false                         (* unchecked_access *)
            | Let _ P (Add | Sub | Itop) _ => false              (* implicit_flight *)
            | Let _ P Copy [Tmp _] | Let _ P Copy [Const _] => false
            | _ => true
            end
        end in
      if ok then Some (rest, live') else None
  end.

(** `checked_insts(Insts, Fn, Mode, Live, LiveOut)`. *)
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

(** `incoming_edges(Blocks, Incoming)` for one label: its incoming
    edges, one per jump target, the last first (add_edge prepends). *)
Definition incoming (bs : list block) (l : name) : list (name * bool) :=
  rev (flat_map (fun b => flat_map (fun t => if name_eqb (edge_label t) l
                                             then [(b_label b, is_poll t)] else [])
                                   (jump_targets (b_jump b))) bs).

(** `checked_block`, folded over the blocks in order (stage_func/6). *)
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

(** `limit_reads(Fn, Blocks)`: a limit is read only as a check_limit's
    second argument. *)
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

(** `polls_every_cycle(Blocks)`: without its poll edges the graph is
    acyclic. Blocks with no unpolled edge into what is left are removed
    until none are left, or none can be. *)
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

Definition polls_every_cycle (f : func) : bool :=
  let g := map (fun b => (b_label b, map edge_label (filter (fun t => negb (is_poll t))
                                                            (jump_targets (b_jump b)))))
               (fn_blocks f) in
  forallb (fun nl => forallb (fun s => mem s (map fst g)) (snd nl)) g
  && peel (S (length g)) g.

(** `stage_func(checked, ...)`. *)
Definition stage_func (md : module) (f : func) (doms : nmap (Z * Z)) : bool :=
  evidence_pass (stage_sources md f doms) f && limit_reads f && polls_every_cycle f.

(** ## Functions and modules *)

(** ## The stage *)

Definition checked_op (o : op) : bool :=
  match o with
  | Check _ _ _ _ | CheckAhead _ _ _ _ _ | Renew _ _ _ _ | RenewHull _ _ _ _
  | HalfCheck _ _ _ _ _ | SpanTest _ _ | RenewIf _ _ _ _ | Limit _ | CheckLimit _ _ _ _
  | CheckLocal _ _ _ _ _ | CheckFunction | RawLoad _ _ | RawLoadPointer _ _ => true
  | _ => false
  end.

(** `checked_inst(Inst)` and `checked_jump(Jump)`. *)
Definition checked_inst (i : inst) : bool :=
  match i with
  | Let _ _ o _ => checked_op o
  | RawStore _ _ _ _ | RawStorePointer _ _ _ _ | RawCall _ _ _ | Flight _ _ _ _ => true
  | _ => false
  end.

Definition checked_jump (j : jump) : bool := existsb is_poll (jump_targets j).

(** The same, read off the term of a function outside the subset. *)
Definition checked_op_term (t : term) : bool :=
  match t with
  | TAtom "check_function" => true
  | TApp ("check" | "check_ahead" | "renew" | "renew_hull" | "half_check" | "span_test"
          | "renew_if" | "limit" | "check_limit" | "check_local" | "raw_load"
          | "raw_load_pointer" | "raw_cas") _ => true
  | _ => false
  end.

Definition checked_inst_term (t : term) : bool :=
  match t with
  | TApp "let" [_; _; o; _] => checked_op_term o
  | TApp ("raw_store" | "raw_store_pointer" | "raw_call" | "flight" | "touch") _ => true
  | _ => false
  end.

Definition checked_jump_term (t : term) : bool :=
  match t with
  | TApp "goto" [TApp "poll" [_]] => true
  | TApp "branch" [_; a; b] =>
      match a with TApp "poll" [_] => true | _ =>
        match b with TApp "poll" [_] => true | _ => false end end
  | _ => false
  end.

(** `module_stage(M, Stage)`: checked when any function uses a word of
    the checked stage, a check, raw access, flight or poll edge. The
    stage is read off the vocabulary of the whole module, never stated:
    a module whose only checked word is one poll edge is unchecked
    without it, and then needs no poll on its cycles. *)
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

(** ## Functions and modules *)

(** The `x` rule of `valid_item(_, _, _, func(...))`: an `x` value is
    never a parameter, a result, a call's argument or result, or a phi. *)
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

(** `valid_item(Symbols, filc, Stage, func(...))` for a function of
    the core subset. In the unchecked stage there is no evidence to
    check; the core subset then has no memory access at all. *)
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

(** ## Data *)

(** `data_align(Align)`: a power of two from 1 to 4096. *)
Definition data_align (a : Z) : bool :=
  (1 <=? a) && (a <=? 4096) && (Z.land a (a - 1) =? 0).

(** The linkage clauses of `valid_item(_, filc, _, data(...))`: the
    linkages data of a Fil-C module may have, and what `extern(weak)`
    and `init(Kind, Prio)` ask of the items. *)
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

(** What `valid_item` asks of each item: it has one of the header's
    shapes (`data_item_shape/1`), a float item's constant is below the
    class's modulus, a string holds bytes, and a pointer names its
    symbol by an atom. In a Fil-C module `item(l, sym(_, _))`, like any
    other term, decodes to `ItemOther` and is refused. *)
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

(** `pointer_items_aligned(Name, Items, Off)`: each pointer item, from
    off bytes into the object, starts at a multiple of 8. *)
Fixpoint pointer_items_aligned (off : Z) (its : list data_item) : bool :=
  match its with
  | [] => true
  | it :: rest =>
      match it with Sym _ _ => off mod 8 =? 0 | _ => true end
      && pointer_items_aligned (off + item_size it) rest
  end.

(** `func_named(Symbols, Name, _)`: the module defines a function Name,
    in the subset or not. *)
Definition func_named (md : module) (n : name) : bool :=
  match first_func_linkage n md with Some _ => true | None => false end.

(** `data_named(Symbols, Name)`: the module defines data Name, that is
    data of that name not declared `extern(weak)`. *)
Definition data_named (md : module) (n : name) : bool :=
  match first_data_linkage n md with Some _ => true | None => false end.

(** What data asks of the rest of the module: a constructor or
    destructor table entry names a function the module defines; a weak
    declaration is of no name the module defines with local linkage
    (`local_global(Symbols, Name)`), whose symbols it would make weak and
    global; and no pointer item names a table entry, which has no
    address. *)
Definition data_names_ok (md : module) (n : name) (lk : linkage) (its : list data_item) : bool :=
  match lk, its with
  | LInit _ _, [Sym f _] => func_named md f
  | LExternWeak, _ => negb (local_global md n)
  | _, _ => true
  end
  && forallb (fun it => match it with Sym s _ => negb (init_entry_named md s) | _ => true end) its.

(** `valid_item(Symbols, filc, Stage, data(Name, Linkage, Align, Items))`. *)
Definition valid_data (md : module) (n : name) (lk : linkage) (align : Z) (its : list data_item)
  : bool :=
  data_align align && data_linkage_ok lk its && forallb data_item_ok its
  && pointer_items_aligned 0 its && data_names_ok md n lk its.

(** ## Aliases *)

(** The first function of each name, as `module_symbols/2` indexes
    them. *)
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

(** `memberchk(call(_, global(Name), _), Is)` for some block of F: read
    off its blocks in the subset, off its term outside it. *)
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

Definition item_name (it : item) : option name :=
  match it with IFunc f => Some (fn_name f) | IOutside n _ => Some n | _ => None end.

(** `valid_item(Symbols, filc, Stage, alias(Name, Linkage, Target))`:
    the linkage is `export` or `weak`, no function or data shares the
    alias's name, and the target is a function the module defines, or
    data of a linkage an alias may name (`export`, `local`, `weak` or
    `ro(_)`) that no other function calls through the alias. *)
Definition valid_alias (md : module) (n : name) (lk : term) (target : name) : bool :=
  match lk with TAtom ("export" | "weak") => true | _ => false end
  && negb (func_named md n || data_named md n)
  && (func_named md target
      || match first_data_linkage target md with
         | Some (LExport | LLocal | LWeak | LRo _) =>
             negb (existsb (fun it => match item_name it with
                                      | Some g => negb (name_eqb g n) && calls_global it n
                                      | None => false
                                      end) (first_funcs [] md))
         | _ => false
         end).

(** ## Modules *)

(** `defined_name(Item, Name)`: the name an item defines; a weak
    declaration defines none. *)
Definition defined_name (it : item) : option name :=
  match it with
  | IFunc f => Some (fn_name f)
  | IOutside n _ => Some n
  | IData _ LExternWeak _ _ => None
  | IData n _ _ _ => Some n
  | IAlias n _ _ => Some n
  end.

(** `unique_names(Items)`: no two items define the same name. *)
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

(** No two items share a name, and the items of the module that the
    model can judge are valid. *)
Definition valid_items (md : module) : bool :=
  unique_names md &&
  forallb (fun it => match it with
                     | IFunc f => valid_func md f
                     | IData n lk al its => valid_data md n lk al its
                     | IAlias n lk t => valid_alias md n lk t
                     | IOutside _ _ => true
                     end) md.

(** `valid md`, ir:valid_module/1 for a Fil-C module without its
    contexts: None when a function is outside the core subset, which the
    model cannot judge. The `context/2` items are provenance's records,
    which `valid_contexts/1` checks and run/5 never reads; the model
    has none (docs/rocq.md). *)
Definition valid (md : module) : option bool :=
  if existsb (fun it => match it with IOutside _ _ => true | _ => false end) md then None
  else Some (valid_items md).
