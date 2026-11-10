(** The [[stage|checked]] IR back as Prolog terms: the encoders of the
    syntax of Syntax.v, the inverse of Transport.v's decoders, so that
    the backend can print an instruction as the very term the Prolog
    compiler printed it as (`nanofil abi-terms FILE`).

    Each encoder writes the one term its decoder reads its value from:
    when the decoder reads a term t as x, the encoder writes x as t,
    and the decoder reads that as x again. No decoder reads one value
    from two terms, so there is no spelling to choose.

    The encoders are total, but not every value of the syntax has a
    term. What is written for a value that no term decodes to:

    - [To] of a label that is itself `poll(L)` is written `poll(L)`,
      which reads back as [Poll] of L ([enc_target]);
    - a [RawStore] of width `p` is written `raw_store(p, ...)`, which
      the decoder refuses: a pointer store is `raw_store_pointer`
      ([enc_inst]);
    - [ExtF], [FloatToInt] and [IntToFloat] at a class ir.pl has no
      such op for are written as terms that are not ops, which the
      decoder refuses ([enc_op]).

    The examples at the end check both directions, by computation, on
    terms the Prolog compiler printed for nanofil/tests/filc. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Validate Transport.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Values and the small tables *)

(** As ir.pl writes the [[temporary]] named d: `tmp(D)`. *)
Definition enc_tmp (d : name) : term := TApp "tmp" [d].

(** As ir.pl writes a value: `tmp(N)`, `const(N)` or `global(S)`. *)
Definition enc_value (v : value) : term :=
  match v with
  | Tmp n => enc_tmp n
  | Const n => TApp "const" [TInt n]
  | Global s => TApp "global" [s]
  end.

(** As ir.pl writes the [[rights]] of an access: `read` or `write`. *)
Definition enc_rights (r : rights) : term :=
  TAtom (match r with Read => "read" | Write => "write" end).

(** As ir.pl writes the bound a [[half check]] tests: `upper` or
    `lower`. *)
Definition enc_bound (b : bound) : term :=
  TAtom (match b with Upper => "upper" | Lower => "lower" end).

(** As ir.pl writes a narrow integer type: `sw`, `uw`, `sh`, `uh`, `sb`
    or `ub`. *)
Definition enc_narrow (t : narrow) : term :=
  TAtom (match t with
         | Sw => "sw" | Uw => "uw" | Sh => "sh" | Uh => "uh" | Sb => "sb" | Ub => "ub"
         end).

(** As ir.pl writes the type of a raw load: `l`, `s`, `d`, `x`, or a
    narrow type. *)
Definition enc_load_type (t : load_type) : term :=
  match t with
  | LdL => TAtom "l"
  | LdS => TAtom "s"
  | LdD => TAtom "d"
  | LdX => TAtom "x"
  | LdNarrow n => enc_narrow n
  end.

(** As ir.pl writes a comparison's Cond: `eq`, `ne`, the signed and
    unsigned integer orders `sle` to `ugt`, the float orders `le` `lt`
    `ge` `gt`, `o` (ordered) or `uo` (unordered). *)
Definition enc_cond (c : cond) : term :=
  TAtom (match c with
         | Eq => "eq" | Ne => "ne"
         | Sle => "sle" | Slt => "slt" | Sge => "sge" | Sgt => "sgt"
         | Ule => "ule" | Ult => "ult" | Uge => "uge" | Ugt => "ugt"
         | Le => "le" | Lt => "lt" | Ge => "ge" | Gt => "gt"
         | Ord => "o" | Unord => "uo"
         end).

(** As ir.pl writes one memory effect of a raw pointer load or store:
    `aux_read`, `lower_resolve`, `address_read`, `atomic_read`,
    `aux_ensure`, `lower_barrier`, `rooted_reload`, `lower_write`,
    `address_write` or `atomic_write`. *)
Definition enc_effect (e : effect) : term :=
  TAtom (match e with
         | AuxRead => "aux_read" | LowerResolve => "lower_resolve"
         | AddressRead => "address_read" | AtomicRead => "atomic_read"
         | AuxEnsure => "aux_ensure" | LowerBarrier => "lower_barrier"
         | RootedReload => "rooted_reload" | LowerWrite => "lower_write"
         | AddressWrite => "address_write" | AtomicWrite => "atomic_write"
         end).

(** As ir.pl writes the Effects of a raw pointer load or store: the
    list of its effects, in order. *)
Definition enc_effects (es : list effect) : term := TList (map enc_effect es).

(** As ir.pl writes the width of a store: `b`, `h`, `w`, `l`, `p`, `s`,
    `d` or `x`. *)
Definition enc_width (w : width) : term :=
  TAtom (match w with
         | Wb => "b" | Wh => "h" | Ww => "w" | Wl => "l"
         | Wp => "p" | Ws => "s" | Wd => "d" | Wx => "x"
         end).

(** The atom `signed` or `unsigned`. No term of the IR holds it: it is
    written only in the terms of [enc_op] that are not ops. *)
Definition enc_signedness (sg : signedness) : term :=
  TAtom (match sg with Signed => "signed" | Unsigned => "unsigned" end).

(** ## Ops *)

(** As ir.pl writes a [[check]] or one of its [[reuse]] forms of the
    name f: `f(Lo, Hi, Rights, Align)`. *)
Definition enc_check4 (f : string) (lo hi : Z) (r : rights) (al : Z) : term :=
  TApp f [TInt lo; TInt hi; enc_rights r; TInt al].

(** As ir.pl writes an Op: an atom such as `add` or `ptoi`, or a
    compound such as `cmp(Cond, K)`, `ext(T)`, `alloc(Align)`,
    `check(Lo, Hi, Rights, Align)`,
    `check_ahead(Lo, Hi, Rights, Align, AHi)`,
    `half_check(Bound, Lo, Hi, Rights, Align)`, `span_test(Lo, Hi)`,
    `limit(Size)`, `check_local(Name, Off, Bytes, Rights, Align)`,
    `raw_load(T, Off)` or `raw_load_pointer(Off, Effects)`.

    A float widening is `ext(s)` or `ext(d)`, naming its source class;
    a float to an integer is `stosi`, `stoui`, `dtosi`, `dtoui`,
    `xtosi` or `xtoui`, and an integer to a float `swtof`, `uwtof`,
    `sltof` or `ultof`. Those are all the conversions ir.pl has. At any
    other class [ExtF] k is written `ext(K)`, and [FloatToInt] k sg and
    [IntToFloat] k sg are written `float_to_int(K, Sg)` and
    `int_to_float(K, Sg)`, Sg being `signed` or `unsigned`: none of
    them is an op, and the decoder refuses each. *)
Definition enc_op (o : op) : term :=
  match o with
  | Add => TAtom "add" | Sub => TAtom "sub" | Mul => TAtom "mul"
  | Div => TAtom "div" | Udiv => TAtom "udiv"
  | Rem => TAtom "rem" | Urem => TAtom "urem"
  | And => TAtom "and" | Or => TAtom "or" | Xor => TAtom "xor"
  | Sar => TAtom "sar" | Shr => TAtom "shr" | Shl => TAtom "shl"
  | Neg => TAtom "neg" | Copy => TAtom "copy"
  | Ptoi => TAtom "ptoi" | Itop => TAtom "itop"
  | Cmp c k => TApp "cmp" [enc_cond c; eclass k]
  | Ext t => TApp "ext" [enc_narrow t]
  | ExtF k => TApp "ext" [eclass k]
  | Truncd => TAtom "truncd" | Truncx => TAtom "truncx"
  | FloatToInt k sg =>
      match k, sg with
      | Single, Signed => TAtom "stosi" | Single, Unsigned => TAtom "stoui"
      | Double, Signed => TAtom "dtosi" | Double, Unsigned => TAtom "dtoui"
      | Extended, Signed => TAtom "xtosi" | Extended, Unsigned => TAtom "xtoui"
      | _, _ => TApp "float_to_int" [eclass k; enc_signedness sg]
      end
  | IntToFloat k sg =>
      match k, sg with
      | W, Signed => TAtom "swtof" | W, Unsigned => TAtom "uwtof"
      | L, Signed => TAtom "sltof" | L, Unsigned => TAtom "ultof"
      | _, _ => TApp "int_to_float" [eclass k; enc_signedness sg]
      end
  | Cast => TAtom "cast"
  | Sqrt => TAtom "sqrt"
  | Alloc al => TApp "alloc" [TInt al]
  | Check lo hi r al => enc_check4 "check" lo hi r al
  | CheckAhead lo hi r al ahi =>
      TApp "check_ahead" [TInt lo; TInt hi; enc_rights r; TInt al; TInt ahi]
  | Renew lo hi r al => enc_check4 "renew" lo hi r al
  | RenewHull lo hi r al => enc_check4 "renew_hull" lo hi r al
  | HalfCheck b lo hi r al =>
      TApp "half_check" [enc_bound b; TInt lo; TInt hi; enc_rights r; TInt al]
  | SpanTest lo hi => TApp "span_test" [TInt lo; TInt hi]
  | RenewIf lo hi r al => enc_check4 "renew_if" lo hi r al
  | Limit size => TApp "limit" [TInt size]
  | CheckLimit lo hi r al => enc_check4 "check_limit" lo hi r al
  | CheckLocal x off bytes r al =>
      TApp "check_local" [x; TInt off; TInt bytes; enc_rights r; TInt al]
  | CheckFunction => TAtom "check_function"
  | RawLoad t off => TApp "raw_load" [enc_load_type t; TInt off]
  | RawLoadPointer off es => TApp "raw_load_pointer" [TInt off; enc_effects es]
  | VaArgs => TAtom "va_args"
  | VaArg => TAtom "va_arg"
  | Setjmp kind =>
      TApp "setjmp" [TAtom match kind with
                           | SjSetjmp => "setjmp"
                           | SjUnderscore => "_setjmp"
                           | SjSig => "sigsetjmp"
                           end]
  end.

(** ## Instructions *)

(** As ir.pl writes an argument of a [[flight]]: `address(V)`, or the
    value itself. *)
Definition enc_flight_arg (a : flight_arg) : term :=
  match a with
  | FValue v => enc_value v
  | FAddress p => TApp "address" [enc_value p]
  end.

(** As ir.pl writes a flight's Lower: `none` or `lower(V)`. *)
Definition enc_flight_lower (lw : flight_lower) : term :=
  match lw with
  | LowerNone => TAtom "none"
  | LowerOf p => TApp "lower" [enc_value p]
  end.

(** As ir.pl writes one result of a call, the temporary d of class k:
    `result(tmp(D), K)`. *)
Definition enc_result (r : name * class) : term :=
  TApp "result" [enc_tmp (fst r); eclass (snd r)].

(** As ir.pl writes a call's Res: `void`, `result(tmp(D), K)`, or
    `tuple([result(tmp(D1), K1), result(tmp(D2), K2)])`. *)
Definition enc_call_result (r : call_result) : term :=
  match r with
  | CVoid => TAtom "void"
  | CResult d k => enc_result (d, k)
  | CTuple rs => TApp "tuple" [TList (map enc_result rs)]
  end.

(** As ir.pl writes a call's argument, the class first: `arg(K, V)`. *)
Definition enc_arg (a : arg) : term :=
  match a with Arg k v => TApp "arg" [eclass k; enc_value v] end.

(** As ir.pl writes a call's arguments: the list of them. *)
Definition enc_args (args : list arg) : term := TList (map enc_arg args).

(** As ir.pl writes an instruction: `let(tmp(D), K, Op, Args)`,
    `flight(tmp(D), Op, Args, Lower)`,
    `raw_store(Width, Off, Value, Addr)`,
    `raw_store_pointer(Off, Value, Addr, Effects)`,
    `call(Res, Callee, Args)`, `raw_call(Res, Callee, Args)`,
    `local_alloc(Name, Size)`, `loc(File, Line)` or `touch(tmp(Q))`.

    A [RawStore] of the width [Wp] is written `raw_store(p, ...)`,
    which is not an instruction of the IR (a pointer store is
    `raw_store_pointer`) and which the decoder refuses. *)
Definition enc_inst (i : inst) : term :=
  match i with
  | Let d k o args => TApp "let" [enc_tmp d; eclass k; enc_op o; TList (map enc_value args)]
  | Flight d o args lw =>
      TApp "flight" [enc_tmp d; enc_op o; TList (map enc_flight_arg args); enc_flight_lower lw]
  | RawStore w off v a => TApp "raw_store" [enc_width w; TInt off; enc_value v; enc_value a]
  | RawStorePointer off v a es =>
      TApp "raw_store_pointer" [TInt off; enc_value v; enc_value a; enc_effects es]
  | Call r callee args => TApp "call" [enc_call_result r; enc_value callee; enc_args args]
  | RawCall r callee args =>
      TApp "raw_call" [enc_call_result r; enc_value callee; enc_args args]
  | LocalAlloc x size => TApp "local_alloc" [x; TInt size]
  | Loc file line => TApp "loc" [file; TInt line]
  | Touch q => TApp "touch" [enc_tmp q]
  end.

(** ## Jumps and phis *)

(** As ir.pl writes a jump's target: the label `L`, or `poll(L)` for a
    [[poll|poll edge]]. A label is any ground term, and one that is
    itself `poll(L)` cannot be told from a poll edge to L: [To] of it
    is written `poll(L)`, which the decoder reads as [Poll] of L. The
    decoder never gives such a [To]. *)
Definition enc_target (t : target) : term :=
  match t with
  | To l => l
  | Poll l => TApp "poll" [l]
  end.

(** As ir.pl writes the jump that ends a block: `goto(L)`,
    `branch(V, L1, L2)`, `ret(V)`, `rets([V1, V2])`, `ret` or
    `unreachable`. *)
Definition enc_jump (j : jump) : term :=
  match j with
  | JGoto t => TApp "goto" [enc_target t]
  | JBranch v t1 t2 => TApp "branch" [enc_value v; enc_target t1; enc_target t2]
  | JRet v => TApp "ret" [enc_value v]
  | JRets vs => TApp "rets" [TList (map enc_value vs)]
  | JRetVoid => TAtom "ret"
  | JUnreachable => TAtom "unreachable"
  end.

(** As ir.pl writes one pair of a [[phi]], a predecessor's label and the
    value for the edge from it: `Pred-Value`. *)
Definition enc_pair (p : name * value) : term := TApp "-" [fst p; enc_value (snd p)].

(** As ir.pl writes a [[phi]]: `phi(tmp(D), K, [Pred-Value])`. *)
Definition enc_phi (p : phi) : term :=
  match p with
  | Phi d k pairs => TApp "phi" [enc_tmp d; eclass k; TList (map enc_pair pairs)]
  end.

(** ## Examples *)

(** The decoder dec reads the term t, and the encoder enc writes what
    it read as t again. Then dec also reads what enc wrote as the same
    value, since that is t: one statement checks both directions. *)
Definition writes_back {X : Type} (dec : term -> option X) (enc : X -> term) (t : term) : Prop :=
  option_map enc (dec t) = Some t.

(** The decoder dec reads back each value of xs from the term the
    encoder enc writes for it. *)
Definition reads_back {X : Type} (dec : term -> option X) (enc : X -> term) (xs : list X) : Prop :=
  map (fun x => dec (enc x)) xs = map Some xs.

(** Every class is read back from [eclass]'s atom for it. *)
Example class_reads_back : forall k, dclass (eclass k) = Some k.
Proof. intros k. destruct k; reflexivity. Qed.

(** Both rights are read back. *)
Example rights_reads_back : forall r, drights (enc_rights r) = Some r.
Proof. intros r. destruct r; reflexivity. Qed.

(** Both bounds are read back. *)
Example bound_reads_back : forall b, dbound (enc_bound b) = Some b.
Proof. intros b. destruct b; reflexivity. Qed.

(** Every narrow type is read back. *)
Example narrow_reads_back : forall t, dnarrow (enc_narrow t) = Some t.
Proof. intros t. destruct t; reflexivity. Qed.

(** Every load type is read back. *)
Example load_type_reads_back : forall t, dload_type (enc_load_type t) = Some t.
Proof. intros t. destruct t as [| | | | n]; try reflexivity. destruct n; reflexivity. Qed.

(** Every condition is read back. *)
Example cond_reads_back : forall c, dcond (enc_cond c) = Some c.
Proof. intros c. destruct c; reflexivity. Qed.

(** Every effect is read back. *)
Example effect_reads_back : forall e, deffect (enc_effect e) = Some e.
Proof. intros e. destruct e; reflexivity. Qed.

(** Every width is read back. *)
Example width_reads_back : forall w, dwidth (enc_width w) = Some w.
Proof. intros w. destruct w; reflexivity. Qed.

(** Every value is read back. *)
Example value_reads_back : forall v, dvalue (enc_value v) = Some v.
Proof. intros v. destruct v; reflexivity. Qed.

(** The two effect lists of a pointer load, and the empty one. *)
Example effects_read_back :
  reads_back deffects enc_effects [load_effects; local_load_effects; []].
Proof. reflexivity. Qed.

(** Every op that is an atom, the float conversions among them. *)
Example atom_ops_read_back :
  reads_back dop enc_op
    [Add; Sub; Mul; Div; Udiv; Rem; Urem; And; Or; Xor; Sar; Shr; Shl; Neg; Copy; Ptoi; Itop;
     Truncd; Truncx; Cast; Sqrt; CheckFunction; VaArgs; VaArg;
     FloatToInt Single Signed; FloatToInt Single Unsigned;
     FloatToInt Double Signed; FloatToInt Double Unsigned;
     FloatToInt Extended Signed; FloatToInt Extended Unsigned;
     IntToFloat W Signed; IntToFloat W Unsigned; IntToFloat L Signed; IntToFloat L Unsigned].
Proof. reflexivity. Qed.

(** Every op that is a compound, one or two of each. *)
Example compound_ops_read_back :
  reads_back dop enc_op
    [Cmp Eq W; Cmp Ult L; Cmp Unord Double; Ext Sw; Ext Ub; ExtF Single; ExtF Double;
     Alloc 8; Check 0 8 Write 1; CheckAhead 0 16 Read 8 8; Renew 0 8 Write 1;
     RenewHull 4 12 Read 4; HalfCheck Upper 0 8 Read 1; HalfCheck Lower (-8) 0 Write 8;
     SpanTest 0 9; RenewIf 0 9 Read 1; Limit 16; CheckLimit 0 4 Read 1;
     CheckLocal (TAtom "x") 0 1 Read 1; RawLoad LdL 0; RawLoad LdX 16;
     RawLoad (LdNarrow Sb) (-1); RawLoadPointer 8 load_effects].
Proof. reflexivity. Qed.

(** The conversions ir.pl does not have are refused, each one. *)
Example no_such_conversion :
  map (fun o => dop (enc_op o))
    [ExtF W; ExtF L; ExtF P; ExtF A; ExtF F; ExtF Extended;
     FloatToInt W Signed; FloatToInt L Unsigned; FloatToInt P Signed;
     FloatToInt A Signed; FloatToInt F Unsigned;
     IntToFloat P Signed; IntToFloat A Unsigned; IntToFloat F Signed;
     IntToFloat Single Signed; IntToFloat Double Unsigned; IntToFloat Extended Signed]
  = repeat None 17.
Proof. reflexivity. Qed.

(** A raw store of a pointer is refused, and a label `poll(l)` reads
    back as a poll edge. *)
Example no_such_term :
  dinst (enc_inst (RawStore Wp 0 (Const 0) (Tmp (TAtom "q")))) = None /\
  dtarget (enc_target (To (TApp "poll" [TAtom "l"]))) = Some (Poll (TAtom "l")).
Proof. split; reflexivity. Qed.

(** `let(tmp(chk0), a, check(0, 8, write, 1), [tmp(p)])`: a check. *)
Example term_let_check :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a";
                 TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 1];
                 TList [TApp "tmp" [TAtom "p"]]]).
Proof. reflexivity. Qed.

(** `let(tmp(chk0), a, check_local(x, 0, 1, read, 1), [])`: a check of
    a named local, which reads no argument. *)
Example term_let_check_local :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "chk0"]; TAtom "a";
                 TApp "check_local" [TAtom "x"; TInt 0; TInt 1; TAtom "read"; TInt 1];
                 TList []]).
Proof. reflexivity. Qed.

(** `let(tmp(a), l, raw_load(sb, 0), [tmp(chk3)])`: a raw load. *)
Example term_let_raw_load :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "a"]; TAtom "l"; TApp "raw_load" [TAtom "sb"; TInt 0];
                 TList [TApp "tmp" [TAtom "chk3"]]]).
Proof. reflexivity. Qed.

(** `let(tmp(back), p, raw_load_pointer(0, [aux_read, lower_resolve,
    address_read]), [tmp(chk2)])`: a raw pointer load. *)
Example term_let_raw_load_pointer :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "back"]; TAtom "p";
                 TApp "raw_load_pointer"
                   [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]];
                 TList [TApp "tmp" [TAtom "chk2"]]]).
Proof. reflexivity. Qed.

(** `let(tmp(c), w, cmp(eq, w), [tmp(k), const(1)])`: a comparison. *)
Example term_let_cmp :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "c"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"];
                 TList [TApp "tmp" [TAtom "k"]; TApp "const" [TInt 1]]]).
Proof. reflexivity. Qed.

(** `let(tmp(b), d, ext(s), [tmp(a)])`: a float widening. *)
Example term_let_ext_float :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "b"]; TAtom "d"; TApp "ext" [TAtom "s"];
                 TList [TApp "tmp" [TAtom "a"]]]).
Proof. reflexivity. Qed.

(** `let(tmp(kl), l, ext(sw), [tmp(k)])`: an integer extension. *)
Example term_let_ext_narrow :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "kl"]; TAtom "l"; TApp "ext" [TAtom "sw"];
                 TList [TApp "tmp" [TAtom "k"]]]).
Proof. reflexivity. Qed.

(** `let(tmp(r), w, dtosi, [tmp(b)])`: a float to an integer. *)
Example term_let_float_to_int :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "r"]; TAtom "w"; TAtom "dtosi";
                 TList [TApp "tmp" [TAtom "b"]]]).
Proof. reflexivity. Qed.

(** `let(tmp(base), p, copy, [global(g)])`: a symbol's address. *)
Example term_let_copy_global :
  writes_back dinst enc_inst
    (TApp "let" [TApp "tmp" [TAtom "base"]; TAtom "p"; TAtom "copy";
                 TList [TApp "global" [TAtom "g"]]]).
Proof. reflexivity. Qed.

(** `raw_store(l, 0, const(-2), tmp(chk0))`: a raw store. *)
Example term_raw_store :
  writes_back dinst enc_inst
    (TApp "raw_store" [TAtom "l"; TInt 0; TApp "const" [TInt (-2)]; TApp "tmp" [TAtom "chk0"]]).
Proof. reflexivity. Qed.

(** `raw_store_pointer(0, tmp(obj), tmp(chk1), [aux_ensure,
    lower_barrier, rooted_reload, lower_write, address_write])`: a raw
    pointer store. *)
Example term_raw_store_pointer :
  writes_back dinst enc_inst
    (TApp "raw_store_pointer"
       [TInt 0; TApp "tmp" [TAtom "obj"]; TApp "tmp" [TAtom "chk1"];
        TList [TAtom "aux_ensure"; TAtom "lower_barrier"; TAtom "rooted_reload";
               TAtom "lower_write"; TAtom "address_write"]]).
Proof. reflexivity. Qed.

(** `flight(tmp(q), add, [address(tmp(p)), const(8)], lower(tmp(p)))`:
    a flight with a lower. *)
Example term_flight_lower :
  writes_back dinst enc_inst
    (TApp "flight" [TApp "tmp" [TAtom "q"]; TAtom "add";
                    TList [TApp "address" [TApp "tmp" [TAtom "p"]]; TApp "const" [TInt 8]];
                    TApp "lower" [TApp "tmp" [TAtom "p"]]]).
Proof. reflexivity. Qed.

(** `flight(tmp(f), copy, [tmp(i)], none)`: a flight without one. *)
Example term_flight_none :
  writes_back dinst enc_inst
    (TApp "flight" [TApp "tmp" [TAtom "f"]; TAtom "copy"; TList [TApp "tmp" [TAtom "i"]];
                    TAtom "none"]).
Proof. reflexivity. Qed.

(** `call(void, global(churn), [])`: a call with no result. *)
Example term_call_void :
  writes_back dinst enc_inst
    (TApp "call" [TAtom "void"; TApp "global" [TAtom "churn"]; TList []]).
Proof. reflexivity. Qed.

(** `call(result(tmp(p), p), global(make), [arg(l, tmp(v))])`: a call
    with one result. *)
Example term_call_result :
  writes_back dinst enc_inst
    (TApp "call" [TApp "result" [TApp "tmp" [TAtom "p"]; TAtom "p"];
                  TApp "global" [TAtom "make"];
                  TList [TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v"]]]]).
Proof. reflexivity. Qed.

(** `call(tuple([result(tmp(c), l), result(tmp(d), l)]), global(two),
    [arg(l, tmp(a))])`: a call with a tuple of results. *)
Example term_call_tuple :
  writes_back dinst enc_inst
    (TApp "call" [TApp "tuple" [TList [TApp "result" [TApp "tmp" [TAtom "c"]; TAtom "l"];
                                       TApp "result" [TApp "tmp" [TAtom "d"]; TAtom "l"]]];
                  TApp "global" [TAtom "two"];
                  TList [TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "a"]]]]).
Proof. reflexivity. Qed.

(** `raw_call(result(tmp(a), s), tmp(chk0), [arg(s, const(1069547520))])`:
    a call of a proven function. *)
Example term_raw_call_result :
  writes_back dinst enc_inst
    (TApp "raw_call" [TApp "result" [TApp "tmp" [TAtom "a"]; TAtom "s"];
                      TApp "tmp" [TAtom "chk0"];
                      TList [TApp "arg" [TAtom "s"; TApp "const" [TInt 1069547520]]]]).
Proof. reflexivity. Qed.

(** `raw_call(tuple([result(tmp(g), l), result(tmp(h), l)]), tmp(chk2),
    [arg(l, tmp(x))])`: one with a tuple of results. *)
Example term_raw_call_tuple :
  writes_back dinst enc_inst
    (TApp "raw_call" [TApp "tuple" [TList [TApp "result" [TApp "tmp" [TAtom "g"]; TAtom "l"];
                                           TApp "result" [TApp "tmp" [TAtom "h"]; TAtom "l"]]];
                      TApp "tmp" [TAtom "chk2"];
                      TList [TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "x"]]]]).
Proof. reflexivity. Qed.

(** `local_alloc(x, 13)`: a named local. *)
Example term_local_alloc :
  writes_back dinst enc_inst (TApp "local_alloc" [TAtom "x"; TInt 13]).
Proof. reflexivity. Qed.

(** `loc('basic.c', 12)`: a source position. *)
Example term_loc :
  writes_back dinst enc_inst (TApp "loc" [TAtom "basic.c"; TInt 12]).
Proof. reflexivity. Qed.

(** `branch(tmp(c), poll(fill), sum)`: a branch, one edge polling. *)
Example term_branch_poll :
  writes_back djump enc_jump
    (TApp "branch" [TApp "tmp" [TAtom "c"]; TApp "poll" [TAtom "fill"]; TAtom "sum"]).
Proof. reflexivity. Qed.

(** `goto(poll(loop))`: a goto that polls. *)
Example term_goto_poll :
  writes_back djump enc_jump (TApp "goto" [TApp "poll" [TAtom "loop"]]).
Proof. reflexivity. Qed.

(** `goto(end)`: a plain goto. *)
Example term_goto_plain : writes_back djump enc_jump (TApp "goto" [TAtom "end"]).
Proof. reflexivity. Qed.

(** `ret(const(1))`: a return of one value. *)
Example term_ret_value : writes_back djump enc_jump (TApp "ret" [TApp "const" [TInt 1]]).
Proof. reflexivity. Qed.

(** `rets([tmp(n), tmp(m)])`: a return of a tuple. *)
Example term_rets_tuple :
  writes_back djump enc_jump
    (TApp "rets" [TList [TApp "tmp" [TAtom "n"]; TApp "tmp" [TAtom "m"]]]).
Proof. reflexivity. Qed.

(** `ret`: a return from a `void` function. *)
Example term_ret_void : writes_back djump enc_jump (TAtom "ret").
Proof. reflexivity. Qed.

(** `unreachable`. *)
Example term_unreachable : writes_back djump enc_jump (TAtom "unreachable").
Proof. reflexivity. Qed.

(** `phi(tmp(i), w, [start-const(0), fill-tmp(i1)])`: a phi of two
    edges. *)
Example term_phi_pairs :
  writes_back dphi enc_phi
    (TApp "phi" [TApp "tmp" [TAtom "i"]; TAtom "w";
                 TList [TApp "-" [TAtom "start"; TApp "const" [TInt 0]];
                        TApp "-" [TAtom "fill"; TApp "tmp" [TAtom "i1"]]]]).
Proof. reflexivity. Qed.
