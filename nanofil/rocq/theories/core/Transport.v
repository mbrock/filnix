(** When Nanofil compiles a C program or generates a [[mutant]] test
    case, it prints the resulting [[stage|checked]]
    intermediate-representation module and its expected run outcomes
    as ground Prolog terms. To run the formal model or the translation
    [[validator]] on those printed terms, we must convert between
    untyped ground [term] trees and the typed syntax and run-time
    values of the formal semantics.

    This module defines that [[transport]] layer in three parts. The
    decoder [decode_module] parses a Prolog module term into a typed
    [module], the encoder [eoutcome] formats a run [outcome] back as a
    Prolog term, and the test harnesses [judge] and [judge_valid]
    compare the extracted model against the Prolog [[interpreter]] and
    validator.

    Decoding is partial in one deliberate way: when a function uses an
    instruction or type outside the [[core-subset|core subset]], such
    as vector arithmetic, an unchecked [[cas]], or [[asm_fixed]],
    [ditem] wraps the function in [IOutside] instead of rejecting the
    module. The function keeps its symbol address and its raw term so
    that pointers to it and validator signature checks behave just as
    they do in the Prolog compiler, while any attempt to step into its
    body halts as outside the core subset. *)

From Stdlib Require Import String ZArith List Bool Ascii.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Runtime Run Validate ValidFast.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** The local notation `a == b` abbreviates boolean string equality
    `String.eqb a b`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Decoding

    The functions in this section parse ground Prolog [term] trees
    into the inductive syntax of the formal model, returning `None`
    whenever a term does not belong to the [[core-subset|core subset]].
    Smaller decoders extract integers, atoms, lists, classes, and
    operands before [dop], [dinst], [dblock], and [decode_module]
    assemble full instructions, basic blocks, functions, and top-level
    modules. *)

(** Given a ground [term], [dz] extracts its integer value when the
    term is a [TInt] literal and returns `None` otherwise. *)
Definition dz (t : term) : option Z := match t with TInt n => Some n | _ => None end.

(** Given a ground [term], [datom] extracts its string name when the
    term is a [TAtom] and returns `None` otherwise. *)
Definition datom (t : term) : option string := match t with TAtom a => Some a | _ => None end.

(** Given a ground [term], [dlist] extracts its element list when the
    term is a proper list [TList] and returns `None` otherwise. *)
Definition dlist (t : term) : option (list term) := match t with TList ts => Some ts | _ => None end.

(** Given a functor name, an expected arity, and a ground [term],
    [dapp] returns the argument list when the term is a compound
    [TApp] with that functor and argument count, and returns `None`
    otherwise. *)
Definition dapp (f : string) (n : nat) (t : term) : option (list term) :=
  match t with
  | TApp g xs => if (g == f) && (length xs =? n)%nat then Some xs else None
  | _ => None
  end.

(** Given a ground [term], [dclass] decodes one of the eight IR
    register [[class]] atoms into the corresponding [class]
    constructor, or returns `None` for any other term. *)
Definition dclass (t : term) : option class :=
  let* a := datom t in
  if a == "w" then Some W else if a == "l" then Some L else if a == "p" then Some P
  else if a == "a" then Some A else if a == "f" then Some F
  else if a == "s" then Some Single else if a == "d" then Some Double
  else if a == "x" then Some Extended else None.

(** Given a ground [term], [dtmp] extracts the identifier [name] from
    a compound [[temporary]] term, or returns `None` if the term has
    any other shape. *)
Definition dtmp (t : term) : option name :=
  let* xs := dapp "tmp" 1 t in match xs with [n] => Some n | _ => None end.

(** Given a ground [term], [dvalue] decodes an IR operand into a [Tmp]
    temporary, a [Const] integer literal, or a [Global] symbol
    reference. *)
Definition dvalue (t : term) : option value :=
  match t with
  | TApp "tmp" [n] => Some (Tmp n)
  | TApp "const" [TInt n] => Some (Const n)
  | TApp "global" [s] => Some (Global s)
  | _ => None
  end.

(** Given a ground [term], [drights] decodes the atom `read` or
    `write` into the access [[rights]] value [Read] or [Write]. *)
Definition drights (t : term) : option rights :=
  let* a := datom t in
  if a == "read" then Some Read else if a == "write" then Some Write else None.

(** Given a ground [term], [dbound] decodes the atom `upper` or
    `lower` into the [bound] tested by a [[half_check|half check]]. *)
Definition dbound (t : term) : option bound :=
  let* a := datom t in
  if a == "upper" then Some Upper else if a == "lower" then Some Lower else None.

(** Given a ground [term], [dnarrow] decodes a narrow integer width
    atom for a signed or unsigned word, halfword, or byte into its
    [narrow] constructor. *)
Definition dnarrow (t : term) : option narrow :=
  let* a := datom t in
  if a == "sw" then Some Sw else if a == "uw" then Some Uw
  else if a == "sh" then Some Sh else if a == "uh" then Some Uh
  else if a == "sb" then Some Sb else if a == "ub" then Some Ub else None.

(** Given a ground [term], [dload_type] decodes the type tag of a
    [[raw-access|raw load]] into a 64-bit integer, floating-point, or
    narrow integer [load_type]. *)
Definition dload_type (t : term) : option load_type :=
  let* a := datom t in
  if a == "l" then Some LdL else if a == "s" then Some LdS
  else if a == "d" then Some LdD else if a == "x" then Some LdX
  else let* n := dnarrow t in Some (LdNarrow n).

(** Given a ground [term], [dcas_type] decodes the operand type of a
    raw [[cas|compare-and-exchange]] into a 64-bit integer, pointer,
    or narrow integer [cas_type]. *)
Definition dcas_type (t : term) : option cas_type :=
  let* a := datom t in
  if a == "l" then Some CasL else if a == "p" then Some CasP
  else let* n := dnarrow t in Some (CasNarrow n).

(** Given a ground [term], [dcond] decodes a relational comparison
    atom into its integer or floating-point [cond] constructor. *)
Definition dcond (t : term) : option cond :=
  let* a := datom t in
  if a == "eq" then Some Eq else if a == "ne" then Some Ne
  else if a == "sle" then Some Sle else if a == "slt" then Some Slt
  else if a == "sge" then Some Sge else if a == "sgt" then Some Sgt
  else if a == "ule" then Some Ule else if a == "ult" then Some Ult
  else if a == "uge" then Some Uge else if a == "ugt" then Some Ugt
  else if a == "le" then Some Le else if a == "lt" then Some Lt
  else if a == "ge" then Some Ge else if a == "gt" then Some Gt
  else if a == "o" then Some Ord else if a == "uo" then Some Unord else None.

(** Given a ground [term], [deffect] decodes a single memory-effect
    atom of a raw pointer load or store, such as reading the shadow
    [[aux]] slot or resolving the [[lower]] capability, into an
    [effect]. *)
Definition deffect (t : term) : option effect :=
  let* a := datom t in
  if a == "aux_read" then Some AuxRead else if a == "lower_resolve" then Some LowerResolve
  else if a == "address_read" then Some AddressRead else if a == "atomic_read" then Some AtomicRead
  else if a == "aux_ensure" then Some AuxEnsure else if a == "lower_barrier" then Some LowerBarrier
  else if a == "rooted_reload" then Some RootedReload else if a == "lower_write" then Some LowerWrite
  else if a == "address_write" then Some AddressWrite else if a == "atomic_write" then Some AtomicWrite
  else None.

(** Given a ground [term], [deffects] decodes a Prolog list of
    memory-effect atoms into a list of [effect] values. *)
Definition deffects (t : term) : option (list effect) :=
  let* ts := dlist t in map_option deffect ts.

(** Given a ground [term], [dwidth] decodes a storage-width atom for
    an integer, pointer, or floating-point width into a [width]
    constructor. *)
Definition dwidth (t : term) : option width :=
  let* a := datom t in
  if a == "b" then Some Wb else if a == "h" then Some Wh else if a == "w" then Some Ww
  else if a == "l" then Some Wl else if a == "p" then Some Wp else if a == "s" then Some Ws
  else if a == "d" then Some Wd else if a == "x" then Some Wx else None.

(** Given a list of four Prolog argument terms and an operation
    constructor, [dcheck4] decodes the lower offset, upper offset,
    access [[rights]], and alignment of a capability [[check]] and
    applies the constructor to them. *)
Definition dcheck4 (xs : list term) (k : Z -> Z -> rights -> Z -> op) : option op :=
  match xs with
  | [lo; hi; r; al] =>
      let* lo' := dz lo in let* hi' := dz hi in let* r' := drights r in
      let* al' := dz al in Some (k lo' hi' r' al')
  | _ => None
  end.

(** Given a ground [term], [dop] decodes an IR operation of the
    [[core-subset|core subset]] into an [op] value, covering
    arithmetic, conversions, comparisons, allocations, capability
    [[check|checks]] and their [[reuse]] forms, and raw loads, or
    returns `None` for operations outside the subset. *)
Definition dop (t : term) : option op :=
  match t with
  | TAtom a =>
      if a == "add" then Some Add else if a == "sub" then Some Sub
      else if a == "mul" then Some Mul else if a == "div" then Some Div
      else if a == "udiv" then Some Udiv else if a == "rem" then Some Rem
      else if a == "urem" then Some Urem else if a == "and" then Some And
      else if a == "or" then Some Or else if a == "xor" then Some Xor
      else if a == "sar" then Some Sar else if a == "shr" then Some Shr
      else if a == "shl" then Some Shl else if a == "neg" then Some Neg
      else if a == "copy" then Some Copy else if a == "select" then Some Select
      else if a == "ptoi" then Some Ptoi
      else if a == "itop" then Some Itop
      else if a == "truncd" then Some Truncd else if a == "truncx" then Some Truncx
      else if a == "stosi" then Some (FloatToInt Single Signed)
      else if a == "stoui" then Some (FloatToInt Single Unsigned)
      else if a == "dtosi" then Some (FloatToInt Double Signed)
      else if a == "dtoui" then Some (FloatToInt Double Unsigned)
      else if a == "xtosi" then Some (FloatToInt Extended Signed)
      else if a == "xtoui" then Some (FloatToInt Extended Unsigned)
      else if a == "swtof" then Some (IntToFloat W Signed)
      else if a == "uwtof" then Some (IntToFloat W Unsigned)
      else if a == "sltof" then Some (IntToFloat L Signed)
      else if a == "ultof" then Some (IntToFloat L Unsigned)
      else if a == "cast" then Some Cast else if a == "sqrt" then Some Sqrt
      else if a == "va_args" then Some VaArgs else if a == "va_arg" then Some VaArg
      else if a == "check_function" then Some CheckFunction else None
  | TApp f xs =>
      if f == "cmp" then
        match xs with [c; k] => let* c' := dcond c in let* k' := dclass k in Some (Cmp c' k')
                    | _ => None end
      else if f == "ext" then
        match xs with
        | [TAtom "s"] => Some (ExtF Single)
        | [TAtom "d"] => Some (ExtF Double)
        | [n] => let* n' := dnarrow n in Some (Ext n')
        | _ => None
        end
      else if f == "alloc" then
        match xs with [al] => let* al' := dz al in Some (Alloc al') | _ => None end
      else if f == "check" then dcheck4 xs Check
      else if f == "renew" then dcheck4 xs Renew
      else if f == "renew_hull" then dcheck4 xs RenewHull
      else if f == "renew_if" then dcheck4 xs RenewIf
      else if f == "check_limit" then dcheck4 xs CheckLimit
      else if f == "check_ahead" then
        match xs with
        | [lo; hi; r; al; ahi] =>
            let* ahi' := dz ahi in
            dcheck4 [lo; hi; r; al] (fun lo hi r al => CheckAhead lo hi r al ahi')
        | _ => None
        end
      else if f == "half_check" then
        match xs with
        | b :: rest => let* b' := dbound b in dcheck4 rest (HalfCheck b')
        | _ => None
        end
      else if f == "span_test" then
        match xs with [lo; hi] => let* lo' := dz lo in let* hi' := dz hi in
                                  Some (SpanTest lo' hi') | _ => None end
      else if f == "setjmp" then
        match xs with
        | [TAtom "setjmp"] => Some (Setjmp SjSetjmp)
        | [TAtom "_setjmp"] => Some (Setjmp SjUnderscore)
        | [TAtom "sigsetjmp"] => Some (Setjmp SjSig)
        | _ => None
        end
      else if f == "limit" then
        match xs with [n] => let* n' := dz n in Some (Limit n') | _ => None end
      else if f == "check_local" then
        match xs with
        | [x; off; bytes; r; al] =>
            let* off' := dz off in let* bytes' := dz bytes in let* r' := drights r in
            let* al' := dz al in Some (CheckLocal x off' bytes' r' al')
        | _ => None
        end
      else if f == "raw_load" then
        match xs with [ty; off] => let* ty' := dload_type ty in let* off' := dz off in
                                   Some (RawLoad ty' off') | _ => None end
      else if f == "raw_cas" then
        match xs with [ty; off] => let* ty' := dcas_type ty in let* off' := dz off in
                                   Some (RawCas ty' off') | _ => None end
      else if f == "raw_load_pointer" then
        match xs with [off; es] => let* off' := dz off in let* es' := deffects es in
                                   Some (RawLoadPointer off' es') | _ => None end
      else None
  | _ => None
  end.

(** Given a ground [term], [dflight_arg] decodes a [[flight]] operand
    into either a pointer address projection [FAddress] or a plain
    value [FValue]. *)
Definition dflight_arg (t : term) : option flight_arg :=
  match t with
  | TApp "address" [v] => let* v' := dvalue v in Some (FAddress v')
  | _ => let* v := dvalue t in Some (FValue v)
  end.

(** Given a ground [term], [dflight_lower] decodes the capability
    source of a [[flight]] instruction into [LowerNone] when no
    capability is attached or [LowerOf] when copied from a pointer's
    [[lower]]. *)
Definition dflight_lower (t : term) : option flight_lower :=
  match t with
  | TAtom "none" => Some LowerNone
  | TApp "lower" [v] => let* v' := dvalue v in Some (LowerOf v')
  | _ => None
  end.

(** Given a ground [term], [dresult] decodes a single call-result
    compound into the destination [[temporary]] name and its register
    [class]. *)
Definition dresult (t : term) : option (name * class) :=
  let* xs := dapp "result" 2 t in
  match xs with [d; k] => let* d' := dtmp d in let* k' := dclass k in Some (d', k') | _ => None end.

(** Given a ground [term], [dcall_result] decodes a call's return
    binding into [CVoid] for a void call, [CTuple] for a multi-word
    return, or [CResult] for a single returned temporary. *)
Definition dcall_result (t : term) : option call_result :=
  match t with
  | TAtom "void" => Some CVoid
  | TApp "tuple" [TList rs] => let* rs' := map_option dresult rs in Some (CTuple rs')
  | _ => let* r := dresult t in Some (CResult (fst r) (snd r))
  end.

(** Given a ground [term], [darg] decodes a call-argument compound
    into an [Arg] pairing its register [class] and operand [value]. *)
Definition darg (t : term) : option arg :=
  let* xs := dapp "arg" 2 t in
  match xs with [k; v] => let* k' := dclass k in let* v' := dvalue v in Some (Arg k' v') | _ => None end.

(** Given a ground [term], [dargs] decodes a Prolog list of call
    arguments into a list of [arg] values. *)
Definition dargs (t : term) : option (list arg) := let* ts := dlist t in map_option darg ts.

(** Given a ground [term], [dinst] decodes a single IR instruction in
    the [[core-subset|core subset]] into an [inst], or returns `None`
    when the instruction uses an operation or form outside the subset. *)
Definition dinst (t : term) : option inst :=
  match t with
  | TApp "let" [d; k; o; TList args] =>
      let* d' := dtmp d in let* k' := dclass k in let* o' := dop o in
      let* args' := map_option dvalue args in Some (Let d' k' o' args')
  | TApp "flight" [d; o; TList args; lw] =>
      let* d' := dtmp d in let* o' := dop o in
      let* args' := map_option dflight_arg args in let* lw' := dflight_lower lw in
      Some (Flight d' o' args' lw')
  | TApp "raw_store" [w; off; v; a] =>
      let* w' := dwidth w in
      match w' with
      | Wb | Wh | Ww | Wl | Ws | Wd | Wx =>
          let* off' := dz off in let* v' := dvalue v in let* a' := dvalue a in
          Some (RawStore w' off' v' a')
      | _ => None
      end
  | TApp "raw_store_pointer" [off; v; a; es] =>
      let* off' := dz off in let* v' := dvalue v in let* a' := dvalue a in
      let* es' := deffects es in Some (RawStorePointer off' v' a' es')
  | TApp "call" [r; callee; args] =>
      let* r' := dcall_result r in let* c := dvalue callee in let* args' := dargs args in
      Some (Call r' c args')
  | TApp "raw_call" [r; callee; args] =>
      let* r' := dcall_result r in let* c := dvalue callee in let* args' := dargs args in
      Some (RawCall r' c args')
  | TApp "local_alloc" [x; TInt size] => Some (LocalAlloc x size)
  | TApp "loc" [file; TInt line] => Some (Loc file line)
  | TApp "touch" [TApp "tmp" [q]] => Some (Touch q)
  | _ => None
  end.

(** Given a ground [term], [dtarget] decodes a jump target into a
    [[poll|poll edge]] [Poll] when wrapped in a poll compound and a
    plain block label [To] otherwise. *)
Definition dtarget (t : term) : option target :=
  match t with
  | TApp "poll" [l] => Some (Poll l)
  | _ => Some (To t)
  end.

(** Given a ground [term], [djump] decodes the control-flow jump at
    the end of a basic [[block]] into an unconditional [JGoto], a
    conditional [JBranch], a return [JRet], [JRets], or [JRetVoid], or
    [JUnreachable]. *)
Definition djump (t : term) : option jump :=
  match t with
  | TApp "goto" [l] => let* l' := dtarget l in Some (JGoto l')
  | TApp "branch" [v; l1; l2] =>
      let* v' := dvalue v in let* l1' := dtarget l1 in let* l2' := dtarget l2 in
      Some (JBranch v' l1' l2')
  | TApp "ret" [v] => let* v' := dvalue v in Some (JRet v')
  | TApp "rets" [TList vs] => let* vs' := map_option dvalue vs in Some (JRets vs')
  | TAtom "ret" => Some JRetVoid
  | TAtom "unreachable" => Some JUnreachable
  | _ => None
  end.

(** Given a ground [term], [dpair] decodes a predecessor-value pair of
    a [[phi]] node into the predecessor block label and the incoming
    [value] for that edge. *)
Definition dpair (t : term) : option (name * value) :=
  let* xs := dapp "-" 2 t in
  match xs with [l; v] => let* v' := dvalue v in Some (l, v') | _ => None end.

(** Given a ground [term], [dphi] decodes a phi compound term into a
    [Phi] node with its destination temporary, register [class], and
    incoming edge pairs. *)
Definition dphi (t : term) : option phi :=
  match t with
  | TApp "phi" [d; k; TList pairs] =>
      let* d' := dtmp d in let* k' := dclass k in let* ps := map_option dpair pairs in
      Some (Phi d' k' ps)
  | _ => None
  end.

(** Given a ground [term], [dblock] decodes a basic-block compound
    into a [block] record when all of its phi nodes, instructions, and
    terminating jump belong to the core subset. *)
Definition dblock (t : term) : option block :=
  match t with
  | TApp "block" [l; TList phis; TList insts; j] =>
      let* phis' := map_option dphi phis in let* insts' := map_option dinst insts in
      let* j' := djump j in Some (mkBlock l phis' insts' j')
  | _ => None
  end.

(** Given a ground [term], [dret] decodes a function's return-type
    specification into [RVoid], a multi-word [RTuple], or a single
    return class [RClass]. *)
Definition dret (t : term) : option ret_type :=
  match t with
  | TAtom "void" => Some RVoid
  | TApp "tuple" [TList ks] =>
      let* ks' := map_option dclass ks in
      if forallb (fun k => match k with L | P | Single | Double => true | _ => false end) ks'
      then Some (RTuple ks') else None
  | _ => let* k := dclass t in
         match k with W | L | P | Single | Double => Some (RClass k) | _ => None end
  end.

(** Given a ground [term], [dparam] decodes a parameter declaration
    compound into the parameter's register [class] and temporary
    [name]. *)
Definition dparam (t : term) : option (class * name) :=
  let* xs := dapp "param" 2 t in
  match xs with [k; d] => let* k' := dclass k in let* d' := dtmp d in Some (k', d') | _ => None end.

(** Given the five subterms of a function declaration compound,
    [dfunc] decodes the return type, parameter list, and basic blocks
    into a [func] record, or returns `None` if any part lies outside
    the [[core-subset|core subset]]. *)
Definition dfunc (n lk r ps bs : term) : option func :=
  let* r' := dret r in
  let* ps' := let* ts := dlist ps in map_option dparam ts in
  let* bs' := let* ts := dlist bs in map_option dblock ts in
  Some (mkFunc n lk r' ps' bs').

(** Given a ground [term], [dlinkage] decodes a top-level item's
    linkage specification into a [linkage] value, wrapping any linkage
    form the model does not distinguish in [LOther]. *)
Definition dlinkage (t : term) : option linkage :=
  match t with
  | TAtom "export" => Some LExport
  | TAtom "local" => Some LLocal
  | TAtom "weak" => Some LWeak
  | TApp "ro" [l] => Some (LRo l)
  | TApp "tls" [l] => Some (LTls l)
  | TApp "init" [w; p] => Some (LInit w p)
  | TApp "extern" [TAtom "weak"] => Some LExternWeak
  | _ => Some (LOther t)
  end.

(** Given a ground [term], [ddata_item] decodes a static initializer
    entry of a global data definition into a byte string [Str], a
    symbol-plus-offset pointer [Sym], a fixed-width integer [Item], a
    zero run [Zero], or an uninterpreted [ItemOther]. *)
Definition ddata_item (t : term) : option data_item :=
  match t with
  | TApp "item" [TAtom "b"; TApp "str" [TList cs]] =>
      Some (match map_option char_code cs with Some codes => Str codes | None => ItemOther t end)
  | TApp "item" [TAtom "p"; TApp "sym" [s; TInt off]] => Some (Sym s off)
  | TApp "item" [w; TApp "const" [TInt n]] =>
      Some (match dwidth w with Some w' => Item w' n | None => ItemOther t end)
  | TApp "zero" [TInt n] => Some (Zero n)
  | _ => Some (ItemOther t)
  end.

(** Given a ground [term], [ditem] decodes a top-level module entry
    into a function, a global data definition [IData], or a symbol
    alias [IAlias]. Functions that fail [dfunc] are preserved as
    [IOutside] so they still receive an address and signature, while
    explanatory [[context]] entries return `Some None` so
    [decode_module] drops them. *)
Definition ditem (t : term) : option (option item) :=
  match t with
  | TApp "func" [n; lk; r; ps; bs] =>
      Some (Some (match dfunc n lk r ps bs with
                  | Some f => IFunc f
                  | None => IOutside n t
                  end))
  | TApp "data" [n; lk; TInt al; TList its] =>
      let* lk' := dlinkage lk in let* its' := map_option ddata_item its in
      Some (Some (IData n lk' al its'))
  | TApp "alias" [n; lk; tg] => Some (Some (IAlias n lk tg))
  | TApp "context" [_; _] => Some None
  | _ => None
  end.

(** Given a ground [term] representing a top-level module compound,
    [decode_module] decodes every item with [ditem] and drops any
    [[context]] annotations to produce a [module]. *)
Definition decode_module (t : term) : option module :=
  match t with
  | TApp "module" [TList items] =>
      let* its := map_option ditem items in
      Some (flat_map (fun o => match o with Some i => [i] | None => [] end) its)
  | _ => None
  end.

(** ## Encoding

    After the model steps a function to completion, we format its
    final [outcome] back into the exact Prolog term representation
    that the reference [[interpreter]] prints. This section defines
    the term encoders for capabilities, run-time words, trap reasons,
    and outcomes. *)

(** Given a pointer [[capability]] [cap], [ecap] encodes it as the
    Prolog atom or compound term written by the reference interpreter,
    tagging object bases, read-only bases, functions, and external
    symbols with their respective functors. *)
Definition ecap (c : cap) : term :=
  match c with
  | CNone => TAtom "none"
  | Obj b => TApp "obj" [TInt b]
  | Ro b => TApp "ro" [TInt b]
  | Fn f => TApp "fn" [f]
  | External n => TApp "ext" [n]
  end.

(** Given a run-time [word], [eword] encodes an integer as a [TInt], a
    pointer as a `ptr` compound of its address and encoded capability,
    and a limit snapshot as a `limit` compound of its capability and
    size. *)
Definition eword (x : word) : term :=
  match x with
  | WInt n => TInt n
  | WPtr p => TApp "ptr" [TInt (ptr_addr p); ecap (ptr_cap p)]
  | WLimit c size => TApp "limit" [ecap c; TInt size]
  end.

(** Given a failure [reason], [ereason] encodes it as the lowercase
    Prolog atom or nested `early` or `ahead` compound term reported by
    the reference interpreter. *)
Fixpoint ereason (r : reason) : term :=
  match r with
  | NullCapability => TAtom "null_capability"
  | OutOfBounds => TAtom "out_of_bounds"
  | Misaligned => TAtom "misaligned"
  | Readonly => TAtom "readonly"
  | NotAFunction => TAtom "not_a_function"
  | ArgumentSize => TAtom "argument_size"
  | ReturnSize => TAtom "return_size"
  | InvalidFree => TAtom "invalid_free"
  | DoubleFree => TAtom "double_free"
  | TooBig => TAtom "too_big"
  | OutOfMemory => TAtom "out_of_memory"
  | Alias => TAtom "alias"
  | Span => TAtom "span"
  | Half => TAtom "half"
  | WhyLimit => TAtom "limit"
  | Early r' => TApp "early" [ereason r']
  | Ahead r' => TApp "ahead" [ereason r']
  end.

(** Given a run [outcome], [eoutcome] encodes it as the Prolog term
    produced by the reference interpreter so that [judge] can compare
    the two outcomes with [term_eqb]. *)
Definition eoutcome (o : outcome) : term :=
  match o with
  | Ret x => TApp "ret" [eword x]
  | Rets xs => TApp "rets" [TList (map eword xs)]
  | RetVoid => TAtom "ret"
  | Unreachable => TAtom "unreachable"
  | UB why => TApp "ub" [why]
  | Trap r => TApp "trap" [ereason r]
  | Unchecked r => TApp "unchecked" [ereason r]
  | OutOfFuel => TAtom "out_of_fuel"
  end.

(** ## Judging a line

    The differential testing harnesses compare the extracted Rocq
    model against the Prolog [[interpreter]] and [[validator]] line by
    line. This section instantiates the reference runner [Model] and
    defines [judge] for execution outcome lines and [judge_valid] for
    [[mutant]] validation verdicts. *)

(** Given a halt label string, [is_outside] returns `true` when the
    runner halted because execution reached a function or instruction
    outside the [[core-subset|core subset]]. *)
Definition is_outside (why : string) : bool := why == "outside the core subset".

(** The module [Model] instantiates the execution functor [Driver]
    with [InterpRuntime] to form the executable reference runner that
    [judge] calls on each test case. *)
Module Model := Driver InterpRuntime.

(** Given a decoded [module] and an outcome or error line printed by
    the compiler's outcome runner, [judge] executes the entry function
    in [Model.run] and compares the encoded result with the
    interpreter's expected term. It returns `agree` when both produce
    the same outcome, `outside` when the run halts on a feature
    outside the [[core-subset|core subset]], `stuck_both` when both
    the interpreter and the model halt with an error, and `disagree`
    whenever their results differ. *)
Definition judge (md : module) (line : term) : term :=
  match line with
  | TApp "outcome" [fn; TList args; TInt fuel; expected] =>
      match map_option dz args with
      | None => TApp "bad_line" [line]
      | Some ns =>
          match Model.run md fn (map WInt ns) fuel with
          | Finished o =>
              let got := eoutcome o in
              if term_eqb got expected then TApp "agree" [fn; TList args; got]
              else TApp "disagree" [fn; TList args; got; expected]
          | Halted why =>
              if is_outside why then TApp "outside" [fn; TList args; TAtom why]
              else TApp "disagree" [fn; TList args; TApp "stuck" [TAtom why]; expected]
          end
      end
  | TApp "error" [fn; TList args; TInt fuel; e] =>
      match map_option dz args with
      | None => TApp "bad_line" [line]
      | Some ns =>
          match Model.run md fn (map WInt ns) fuel with
          | Halted why => TApp "stuck_both" [fn; TList args; TAtom why]
          | Finished o => TApp "disagree" [fn; TList args; eoutcome o; TApp "error" [e]]
          end
      end
  | _ => TApp "bad_line" [line]
  end.

(** Given a zero-based item index, a replacement list of items, and a
    [module], [splice_at] replaces the item at that index with the
    replacement list, which deletes the item when the list is empty,
    replaces it when the list has one element, and inserts before it
    when the old item follows the new one. *)
Fixpoint splice_at (i : nat) (xs : list item) (md : module) : module :=
  match i, md with
  | O, _ :: rest => app xs rest
  | O, [] => xs
  | S i', it :: rest => it :: splice_at i' xs rest
  | S _, [] => []
  end.

(** Given a boolean validity result, [everdict] encodes `true` as the
    atom `valid` and `false` as the atom `invalid` to match the output
    of `mutants.pl`. *)
Definition everdict (b : bool) : term := TAtom (if b then "valid" else "invalid").

(** Given a symbol [name] and a ground [term], [mentions] returns
    `true` when the term contains a `global` compound referring to
    that symbol. *)
Fixpoint mentions (n : name) (t : term) : bool :=
  match t with
  | TApp "global" [m] => term_eqb m n
  | TApp _ ts | TList ts => existsb (mentions n) ts
  | _ => false
  end.

(** Given two function signatures, [sig_eqb] returns `true` when they
    have the exact same parameter classes, return type, and
    variadicity flag. *)
Definition sig_eqb (a b : sig) : bool :=
  ((length (sig_params a) =? length (sig_params b))%nat
   && forallb (fun p => term_eqb (fst p) (snd p)) (combine (sig_params a) (sig_params b)))
  && term_eqb (sig_ret a) (sig_ret b) && Bool.eqb (sig_variadic a) (sig_variadic b).

(** Given a [module], a function name, and a mutated [func],
    [unjudged_callers] returns `true` when the mutation changes the
    function's signature and some [IOutside] function in the module
    references that function name, since the model cannot check
    whether the outside caller still matches the new signature. *)
Definition unjudged_callers (md : module) (fn : name) (f : func) : bool :=
  match func_sig fn md, func_sig fn [IFunc f] with
  | Some old, Some new =>
      negb (sig_eqb old new) &&
      existsb (fun it => match it with IOutside _ t => mentions fn t | _ => false end) md
  | _, _ => false
  end.

(** Given a top-level module [item], [defined_name] returns the symbol
    [name] that the item defines. *)
Definition defined_name (it : item) : name :=
  match it with
  | IFunc f => fn_name f
  | IOutside n _ | IData n _ _ _ | IAlias n _ _ => n
  end.

(** Given a [module] and the lists of removed and added items in a
    mutation, [unjudged_users] returns `true` when an [IOutside]
    function in the module references any of the affected item names,
    since the model cannot check whether that outside function remains
    valid after the change. *)
Definition unjudged_users (md : module) (olds news : list item) : bool :=
  let names := map defined_name (app olds news) in
  existsb (fun it => match it with
                     | IOutside _ t => existsb (fun n => mentions n t) names
                     | _ => false
                     end) md.

(** Given a decoded [module] and a mutant verdict line from the
    mutation generator, [judge_valid] applies the item change at the
    specified index with [splice_at] and runs the fast translation
    [[validator]] [valid_items_fast] on the mutated module. If the
    mutation introduces or affects an [IOutside] function in a way the
    model cannot check, [judge_valid] returns `outside`; otherwise it
    compares [everdict] against the Prolog validator's verdict and
    returns `agree` or `disagree`. *)
Definition judge_valid (md : module) (line : term) : term :=
  match line with
  | TApp "verdict" [nm; TInt at_; id; change; expected] =>
      let i := Z.to_nat at_ in
      let old := firstn 1 (skipn i md) in
      (* Decode the mutation into the replacement splice list, the removed items, and the added items. *)
      let new :=
        match change with
        | TApp "replace" [t] => let* it := ditem t in let* it := it in Some ([it], old, [it])
        | TAtom "delete" => Some ([], old, [])
        | TApp "insert" [t] => let* it := ditem t in let* it := it in Some (it :: old, [], [it])
        | _ => None
        end in
      match new with
      | None => TApp "bad_line" [line]
      | Some (xs, removed, added) =>
          let outside :=
            existsb (fun it => match it with IOutside _ _ => true | _ => false end) added
            || match removed, added with
               | [IFunc _], [IFunc f] => unjudged_callers md (fn_name f) f
               | [IFunc _], _ | _, [IFunc _] => true
               | _, _ => unjudged_users md removed added
               end in
          if outside then TApp "outside" [nm; id] else
          let got := everdict (valid_items_fast (splice_at i xs md)) in
          if term_eqb got expected then TApp "agree" [nm; id; got]
          else TApp "disagree" [nm; id; got; expected]
      end
  | _ => TApp "bad_line" [line]
  end.
