(** [[transport|Transport]] between Prolog terms and the model:
    decoding a [[stage|checked]] module that nanofil printed
    (`nanofil outcomes FILE`, main.pl's `outcomes/3`) into the syntax
    of Syntax.v, and encoding the model's [[outcome]] as the term
    `interp:run/5` would give, so the two can be compared with `==`.

    Decoding is partial in one deliberate way: a function that uses
    anything outside the [[core subset]] (a vector class, `store`,
    [[cas]], `setjmp`, [[asm_fixed]] ...) decodes to
    [IOutside Name Term]. It keeps its address and its term (the
    [[validator]] reads its signature), so calls to it and pointers to
    it behave as the interpreter's do, but running it is stuck. *)

From Stdlib Require Import String ZArith List Bool Ascii.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Runtime Run Validate ValidFast.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** String equality, written as Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Decoding *)

(** The integer the term t is. *)
Definition dz (t : term) : option Z := match t with TInt n => Some n | _ => None end.

(** The name of the atom t. *)
Definition datom (t : term) : option string := match t with TAtom a => Some a | _ => None end.

(** The elements of the list t. *)
Definition dlist (t : term) : option (list term) := match t with TList ts => Some ts | _ => None end.

(** The arguments of t when it is the compound f/n. *)
Definition dapp (f : string) (n : nat) (t : term) : option (list term) :=
  match t with
  | TApp g xs => if (g == f) && (length xs =? n)%nat then Some xs else None
  | _ => None
  end.

(** The [[class]] an atom names: `w`, `l`, `p`, `a`, `f`, `s`, `d` or
    `x`. *)
Definition dclass (t : term) : option class :=
  let* a := datom t in
  if a == "w" then Some W else if a == "l" then Some L else if a == "p" then Some P
  else if a == "a" then Some A else if a == "f" then Some F
  else if a == "s" then Some Single else if a == "d" then Some Double
  else if a == "x" then Some Extended else None.

(** The name of the [[temporary]] `tmp(N)`. *)
Definition dtmp (t : term) : option name :=
  let* xs := dapp "tmp" 1 t in match xs with [n] => Some n | _ => None end.

(** An IR value: a temporary, an integer constant, or a global symbol. *)
Definition dvalue (t : term) : option value :=
  match t with
  | TApp "tmp" [n] => Some (Tmp n)
  | TApp "const" [TInt n] => Some (Const n)
  | TApp "global" [s] => Some (Global s)
  | _ => None
  end.

(** The access [[rights]] `read` or `write`. *)
Definition drights (t : term) : option rights :=
  let* a := datom t in
  if a == "read" then Some Read else if a == "write" then Some Write else None.

(** The bound a [[half check]] tests: `upper` or `lower`. *)
Definition dbound (t : term) : option bound :=
  let* a := datom t in
  if a == "upper" then Some Upper else if a == "lower" then Some Lower else None.

(** A narrow integer width with its signedness: `sw`, `uw`, `sh`, `uh`,
    `sb` or `ub` (signed or unsigned word, half or byte). *)
Definition dnarrow (t : term) : option narrow :=
  let* a := datom t in
  if a == "sw" then Some Sw else if a == "uw" then Some Uw
  else if a == "sh" then Some Sh else if a == "uh" then Some Uh
  else if a == "sb" then Some Sb else if a == "ub" then Some Ub else None.

(** The type a raw load reads: `l`, `s`, `d`, `x`, or a narrow width. *)
Definition dload_type (t : term) : option load_type :=
  let* a := datom t in
  if a == "l" then Some LdL else if a == "s" then Some LdS
  else if a == "d" then Some LdD else if a == "x" then Some LdX
  else let* n := dnarrow t in Some (LdNarrow n).

(** A comparison's condition: equality, signed and unsigned integer
    order, float order, and whether two floats are ordered or not. *)
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

(** One memory effect of a raw pointer load or store, such as reading
    the [[aux]] or resolving the [[lower]]. *)
Definition deffect (t : term) : option effect :=
  let* a := datom t in
  if a == "aux_read" then Some AuxRead else if a == "lower_resolve" then Some LowerResolve
  else if a == "address_read" then Some AddressRead else if a == "atomic_read" then Some AtomicRead
  else if a == "aux_ensure" then Some AuxEnsure else if a == "lower_barrier" then Some LowerBarrier
  else if a == "rooted_reload" then Some RootedReload else if a == "lower_write" then Some LowerWrite
  else if a == "address_write" then Some AddressWrite else if a == "atomic_write" then Some AtomicWrite
  else None.

(** A list of memory effects. *)
Definition deffects (t : term) : option (list effect) :=
  let* ts := dlist t in map_option deffect ts.

(** The width of a store or a data item: `b`, `h`, `w`, `l`, `p`, `s`,
    `d` or `x`. *)
Definition dwidth (t : term) : option width :=
  let* a := datom t in
  if a == "b" then Some Wb else if a == "h" then Some Wh else if a == "w" then Some Ww
  else if a == "l" then Some Wl else if a == "p" then Some Wp else if a == "s" then Some Ws
  else if a == "d" then Some Wd else if a == "x" then Some Wx else None.

(** The four bounds arguments `(Lo, Hi, Rights, Align)` of a
    [[check]], given to k to make the op. *)
Definition dcheck4 (xs : list term) (k : Z -> Z -> rights -> Z -> op) : option op :=
  match xs with
  | [lo; hi; r; al] =>
      let* lo' := dz lo in let* hi' := dz hi in let* r' := drights r in
      let* al' := dz al in Some (k lo' hi' r' al')
  | _ => None
  end.

(** An Op of ir.pl's table, in the [[core subset]]: arithmetic,
    conversions, comparisons, checks, raw loads and the rest. *)
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
      else if a == "copy" then Some Copy else if a == "ptoi" then Some Ptoi
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
      else if f == "raw_load_pointer" then
        match xs with [off; es] => let* off' := dz off in let* es' := deffects es in
                                   Some (RawLoadPointer off' es') | _ => None end
      else None
  | _ => None
  end.

(** An argument of a [[flight]]: `address(V)`, a pointer's address, or
    a plain value. *)
Definition dflight_arg (t : term) : option flight_arg :=
  match t with
  | TApp "address" [v] => let* v' := dvalue v in Some (FAddress v')
  | _ => let* v := dvalue t in Some (FValue v)
  end.

(** A flight's capability source: `none`, or `lower(V)`, the [[lower]]
    of the pointer V. *)
Definition dflight_lower (t : term) : option flight_lower :=
  match t with
  | TAtom "none" => Some LowerNone
  | TApp "lower" [v] => let* v' := dvalue v in Some (LowerOf v')
  | _ => None
  end.

(** One result `result(tmp(D), K)` of a call: the temporary it binds
    and its class. *)
Definition dresult (t : term) : option (name * class) :=
  let* xs := dapp "result" 2 t in
  match xs with [d; k] => let* d' := dtmp d in let* k' := dclass k in Some (d', k') | _ => None end.

(** How a call reads its result: `void`, a `tuple` of results, or one
    result. *)
Definition dcall_result (t : term) : option call_result :=
  match t with
  | TAtom "void" => Some CVoid
  | TApp "tuple" [TList rs] => let* rs' := map_option dresult rs in Some (CTuple rs')
  | _ => let* r := dresult t in Some (CResult (fst r) (snd r))
  end.

(** A call argument `arg(K, V)`: a value and its class. *)
Definition darg (t : term) : option arg :=
  let* xs := dapp "arg" 2 t in
  match xs with [k; v] => let* k' := dclass k in let* v' := dvalue v in Some (Arg k' v') | _ => None end.

(** A list of call arguments. *)
Definition dargs (t : term) : option (list arg) := let* ts := dlist t in map_option darg ts.

(** An instruction of the [[core subset]]; None for any other. *)
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

(** A jump target: `poll(L)`, a [[poll|poll edge]] to L, or a plain
    label. *)
Definition dtarget (t : term) : option target :=
  match t with
  | TApp "poll" [l] => Some (Poll l)
  | _ => Some (To t)
  end.

(** The jump that ends a block: goto, branch, return of one or several
    values or of none, or unreachable. *)
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

(** One `L-V` pair of a phi: a predecessor's label and the value for
    the edge from it. *)
Definition dpair (t : term) : option (name * value) :=
  let* xs := dapp "-" 2 t in
  match xs with [l; v] => let* v' := dvalue v in Some (l, v') | _ => None end.

(** A [[phi]] `phi(tmp(D), K, Pairs)`. *)
Definition dphi (t : term) : option phi :=
  match t with
  | TApp "phi" [d; k; TList pairs] =>
      let* d' := dtmp d in let* k' := dclass k in let* ps := map_option dpair pairs in
      Some (Phi d' k' ps)
  | _ => None
  end.

(** A [[block]] `block(L, Phis, Insts, Jump)`, every part decoded. *)
Definition dblock (t : term) : option block :=
  match t with
  | TApp "block" [l; TList phis; TList insts; j] =>
      let* phis' := map_option dphi phis in let* insts' := map_option dinst insts in
      let* j' := djump j in Some (mkBlock l phis' insts' j')
  | _ => None
  end.

(** A function's return type: `void`, a `tuple` of classes `l`, `p`,
    `s` or `d`, or one class `w`, `l`, `p`, `s` or `d`. *)
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

(** A parameter `param(K, tmp(D))`: its class and temporary. *)
Definition dparam (t : term) : option (class * name) :=
  let* xs := dapp "param" 2 t in
  match xs with [k; d] => let* k' := dclass k in let* d' := dtmp d in Some (k', d') | _ => None end.

(** A function from the arguments of its `func(N, Lk, R, Ps, Bs)` term;
    None if any part is outside the [[core subset]]. *)
Definition dfunc (n lk r ps bs : term) : option func :=
  let* r' := dret r in
  let* ps' := let* ts := dlist ps in map_option dparam ts in
  let* bs' := let* ts := dlist bs in map_option dblock ts in
  Some (mkFunc n lk r' ps' bs').

(** An item's linkage; one the model does not know is kept as its
    term. *)
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

(** One item of a data object: a string of bytes, a pointer to a
    symbol plus an offset, a constant of a width, or zero bytes; any
    other is kept as its term. *)
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

(** An item of the module: a function, outside the [[core subset]] if
    [dfunc] fails, data or an alias; Some None for an explanatory
    `context(_, _)` item ([[context]]). *)
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

(** The module `module(Items)`, its context items dropped. *)
Definition decode_module (t : term) : option module :=
  match t with
  | TApp "module" [TList items] =>
      let* its := map_option ditem items in
      Some (flat_map (fun o => match o with Some i => [i] | None => [] end) its)
  | _ => None
  end.

(** ## Encoding *)

(** A [[capability]] as the interpreter writes it: `none`, `obj(B)`,
    `ro(B)`, `fn(F)` or `ext(N)`. *)
Definition ecap (c : cap) : term :=
  match c with
  | CNone => TAtom "none"
  | Obj b => TApp "obj" [TInt b]
  | Ro b => TApp "ro" [TInt b]
  | Fn f => TApp "fn" [f]
  | External n => TApp "ext" [n]
  end.

(** A [[word]] as the interpreter writes it: an integer,
    `ptr(Addr, Cap)` or `limit(Cap, Size)`. *)
Definition eword (x : word) : term :=
  match x with
  | WInt n => TInt n
  | WPtr p => TApp "ptr" [TInt (ptr_addr p); ecap (ptr_cap p)]
  | WLimit c size => TApp "limit" [ecap c; TInt size]
  end.

(** A [[trap|trap reason]] as the interpreter writes it, an atom, or
    `early(R)` and `ahead(R)` around another. *)
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

(** The [[outcome]] as `interp:run/5` writes it. *)
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

(** ## Judging a line *)

(** The run halted because it left the [[core subset]]. *)
Definition is_outside (why : string) : bool := why == "outside the core subset".

(** The model the gates run: the driver with the interpreter's runtime
    ([Driver InterpRuntime]). *)
Module Model := Driver InterpRuntime.

(** The model's run of the module md on one `outcome(Fn, Args, Fuel,
    Outcome)` or `error(Fn, Args, Fuel, E)` line that `outcomes/3`
    printed, compared with the interpreter's:

    | Judgment | Means |
    |---|---|
    | `agree(Outcome)` | the model and the interpreter have the same outcome |
    | `disagree(Model, Prolog)` | they differ: a finding, presumed the model's fault |
    | `outside(Fn, Why)` | the run leaves the core subset, so it is not compared |
    | `stuck_both(Fn, Why)` | the interpreter threw or failed, and the model is stuck too | *)
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

(** The module with its item at index i (0-based, without contexts)
    replaced by the items xs: none deletes it, one replaces it, the
    new item and then the old one insert before it. *)
Fixpoint splice_at (i : nat) (xs : list item) (md : module) : module :=
  match i, md with
  | O, _ :: rest => app xs rest
  | O, [] => xs
  | S i', it :: rest => it :: splice_at i' xs rest
  | S _, [] => []
  end.

(** A validity verdict as rocq/scripts/mutants.pl writes it: `valid` or
    `invalid`. *)
Definition everdict (b : bool) : term := TAtom (if b then "valid" else "invalid").

(** The term t mentions `global(N)`, for the name n. *)
Fixpoint mentions (n : name) (t : term) : bool :=
  match t with
  | TApp "global" [m] => term_eqb m n
  | TApp _ ts | TList ts => existsb (mentions n) ts
  | _ => false
  end.

(** Whether two function signatures are the same: parameters, return
    and variadicity. *)
Definition sig_eqb (a b : sig) : bool :=
  ((length (sig_params a) =? length (sig_params b))%nat
   && forallb (fun p => term_eqb (fst p) (snd p)) (combine (sig_params a) (sig_params b)))
  && term_eqb (sig_ret a) (sig_ret b) && Bool.eqb (sig_variadic a) (sig_variadic b).

(** A [[mutant]] f of the function fn that changes its signature, in a
    module md where a function outside the [[core subset]] refers to
    it: what that function may now pass or read cannot be judged by
    the model. *)
Definition unjudged_callers (md : module) (fn : name) (f : func) : bool :=
  match func_sig fn md, func_sig fn [IFunc f] with
  | Some old, Some new =>
      negb (sig_eqb old new) &&
      existsb (fun it => match it with IOutside _ t => mentions fn t | _ => false end) md
  | _, _ => false
  end.

(** The name an item defines. *)
Definition defined_name (it : item) : name :=
  match it with
  | IFunc f => fn_name f
  | IOutside n _ | IData n _ _ _ | IAlias n _ _ => n
  end.

(** A change, removing the items olds and adding news, to a data object
    or an alias that a function outside the core subset refers to by
    the old or the new name: whether that function is still valid
    cannot be judged by the model. *)
Definition unjudged_users (md : module) (olds news : list item) : bool :=
  let names := map defined_name (app olds news) in
  existsb (fun it => match it with
                     | IOutside _ t => existsb (fun n => mentions n t) names
                     | _ => false
                     end) md.

(** The model's [[validator]] on one `verdict(Name, At, Id, Change, V)`
    line that rocq/scripts/mutants.pl printed, compared with
    `ir:valid_module/1`'s verdict V. It makes the Change, `replace(Item)`,
    `delete` or `insert(Item)` before it, to the module's item at index
    At, and judges [valid_items] of the whole module (a [[mutant]] can
    change what its callers may pass it): `agree(Name, Id, V)`,
    `disagree(Name, Id, Model, Prolog)` or `outside(Name, Id)`. A
    mutant is outside when it is outside the core subset, when it
    changes a function's signature and a function outside the subset
    refers to it, or when it changes data or an alias that a function
    outside the subset refers to by name. It runs [valid_items_fast],
    which is [valid_items] by [valid_items_fast_eq]. *)
Definition judge_valid (md : module) (line : term) : term :=
  match line with
  | TApp "verdict" [nm; TInt at_; id; change; expected] =>
      let i := Z.to_nat at_ in
      let old := firstn 1 (skipn i md) in
      (* What replaces the item, what is removed and what is added. *)
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
