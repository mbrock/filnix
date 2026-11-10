(** The [[step|small-step]] semantics of the [[core subset]] of the
    [[stage|checked IR]], transcribed from the [[interpreter]]'s `run/5`
    (interp.pl).

    The interpreter is a big-step relation over [[block|blocks]]:
    `block_outcome/7` runs a block and everything after it, and a call
    runs its callee to an [[outcome]] inside the instruction. The model
    takes the same steps one at a time over an explicit
    [[configuration]] (formal.md's decision: small-step, not interaction
    trees), so that Campaign 3's invariants can be stated between any
    two steps.

    ## The configuration

    | Part | Is | interp.pl |
    |---|---|---|
    | [c_frame] | the running invocation | the `ctx(...)` term, Env and the block being run |
    | [c_callers] | the suspended callers, each with how it reads the result | Prolog's own stack |
    | [c_mem] | memory | `s(Mem, Fuel)`'s Mem, less Next |
    | [c_fuel] | blocks left to run | `s(Mem, Fuel)`'s Fuel |

    ## Outcomes

    | Gallina | interp.pl |
    |---|---|
    | [Ret x] | `ret(V)` |
    | [Rets xs] | `rets([X1, X2])` |
    | [RetVoid] | `ret` |
    | [Unreachable] | `unreachable` |
    | [UB why] | `ub(Reason)`: here only `float_conversion`, an invalid float-to-integer conversion |
    | [Trap why] | `trap(Reason)` |
    | [Unchecked why] | `unchecked(Reason)` |
    | [OutOfFuel] | `out_of_fuel` | *)

From Stdlib Require Import String ZArith List Bool Relations.
From Nanofil Require Import Term Syntax Values Memory Ops.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** How a run ends (the table above): a return of one [[word]], of
    several, or of none; an `unreachable` jump reached; undefined
    behaviour; a [[trap]] with its reason; an [[unchecked]] access,
    which only a broken pass produces; or no [[fuel]] left. *)
Inductive outcome : Type :=
| Ret (x : word)
| Rets (xs : list word)
| RetVoid
| Unreachable
| UB (why : term)
| Trap (why : reason)
| Unchecked (why : reason)
| OutOfFuel.

(** ## The prepared module *)

(** A function the module names: one with a body in the [[core subset]],
    or one outside it, kept only by its name n. *)
Inductive fn_def : Type := Defined (f : func) | Outside (n : name).

(** The global environment: the module ready to run
    (`module_prepared/2`'s Fns and Globals, each global's name with its
    pointer), and the [[runtime]]'s free that a call of libc's `free`
    runs: Memory.v's [free_res] in the interpreter, [R.free] of a
    [Runtime] R (Run.v's [Driver], Machine.v). *)
Record genv : Type := mkGenv {
  ge_module : module;
  ge_globals : list (name * ptr);
  ge_free : word -> mem -> option (res unit * mem)
}.

(** The function or outside function of the module items named n,
    not looking through aliases. *)
Fixpoint find_direct (n : name) (items : module) : option fn_def :=
  match items with
  | [] => None
  | IFunc f :: rest => if name_eqb (fn_name f) n then Some (Defined f) else find_direct n rest
  | IOutside f _ :: rest => if name_eqb f n then Some (Outside f) else find_direct n rest
  | _ :: rest => find_direct n rest
  end.

(** The target of the alias named n among the module items, if there
    is one. *)
Fixpoint find_alias (n : name) (items : module) : option name :=
  match items with
  | [] => None
  | IAlias a _ t :: rest => if name_eqb a n then Some t else find_alias n rest
  | _ :: rest => find_alias n rest
  end.

(** The function a call of the name n runs, as `get_assoc(F, Fns, Fn)`
    finds it in the prepared module's Fns: a function by its own name,
    or an alias of one by the alias's name. *)
Definition find_fn (ge : genv) (n : name) : option fn_def :=
  match find_direct n (ge_module ge) with
  | Some d => Some d
  | None => let* t := find_alias n (ge_module ge) in find_direct t (ge_module ge)
  end.

(** ## Values *)

(** An environment: each [[temporary]] assigned so far, with its
    [[word]]. *)
Definition env := list (name * word).

(** As `value_x/5`: the IR value v read at [[class]] k in the
    environment e. A constant at `p` is a pointer with no
    [[capability]]; a symbol the module does not define is
    `ptr(0, ext(Name))`, a pointer with an external capability. *)
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

(** f applied to every element of xs, or None if it fails on any. *)
Fixpoint map_option {X Y : Type} (f : X -> option Y) (xs : list X) : option (list Y) :=
  match xs with
  | [] => Some []
  | x :: xs' => let* y := f x in let* ys := map_option f xs' in Some (y :: ys)
  end.

(** f applied to the elements of xs and ys pairwise, or None if it
    fails on any pair or the lists differ in length. *)
Fixpoint map2_option {X Y Z : Type} (f : X -> Y -> option Z) (xs : list X) (ys : list Y)
  : option (list Z) :=
  match xs, ys with
  | [], [] => Some []
  | x :: xs', y :: ys' => let* z := f x y in let* zs := map2_option f xs' ys' in Some (z :: zs)
  | _, _ => None
  end.

(** As `arg_x/4`: a call argument's value read at its own [[class]]. *)
Definition arg_x (ge : genv) (e : env) (a : arg) : option word :=
  match a with Arg k v => value_x ge e k v end.

(** As `flight_arg_x/4`: an argument of a [[flight]]'s address
    computation. An address projection takes the low 64 bits of a
    pointer's address; any other argument is read at class `l`. *)
Definition flight_arg_x (ge : genv) (e : env) (a : flight_arg) : option word :=
  match a with
  | FAddress v =>
      let* x := value_x ge e P v in
      match x with WPtr p => Some (WInt (ptr_addr p mod 2 ^ 64)) | _ => None end
  | FValue v => value_x ge e L v
  end.

(** As `flight_cap/4`: the [[capability]] a [[flight]] gives its
    pointer. A [[lower]] source copies its pointer's capability, and so
    the object's [[identity]]; none gives no capability. *)
Definition flight_cap (ge : genv) (e : env) (lw : flight_lower) : option cap :=
  match lw with
  | LowerNone => Some CNone
  | LowerOf v =>
      let* x := value_x ge e P v in
      match x with WPtr p => Some (ptr_cap p) | _ => None end
  end.

(** ## Frames and configurations *)

(** Where a [[frame]] is in its function:
    - [Snapshot xs l]: a variadic callee about to take the snapshot of
      its arguments xs, an allocation, before entering its entry block l;
    - [Enter l from]: about to run [[block]] l, entered from the block
      from (None for the entry); entering costs one unit of [[fuel]],
      and with none left the run is [OutOfFuel], as `block_outcome/7` says;
    - [Exec l insts j]: inside block l, with the instructions insts and
      then the jump j left to run. *)
Inductive point : Type :=
| Snapshot (xs : list word) (l : name)
| Enter (l : name) (from : option name)
| Exec (l : name) (insts : list inst) (j : jump).

(** One invocation of a function: the function, its environment of
    [[temporary|temporaries]], each named local with its object's base
    once allocated, the reason it is [[doomed]] if an early
    [[check_ahead]] failed, and where it is. *)
Record frame : Type := mkFrame {
  fr_fn : func;
  fr_env : env;
  fr_locals : list (name * option Z);
  fr_doomed : option reason;
  fr_at : point
}.

(** How a suspended caller reads its callee's [[outcome]]: the call's
    Res, the temporaries it binds, and for a call through the
    [[fast-generic-convention|generic entry]] the caller's and callee's
    word [[class|classes]] (`indirect_call_conv/7`'s
    `conv(CallerWords, CalleeWords)`). *)
Record pending : Type := mkPending {
  pd_res : call_result;
  pd_conv : option (list class * list class)
}.

(** A [[configuration]]: the running [[frame]], the suspended callers
    innermost first, each with how it reads the result, the memory, and
    the [[fuel]] left (the table above). *)
Record config : Type := mkConfig {
  c_frame : frame;
  c_callers : list (frame * pending);
  c_mem : mem;
  c_fuel : Z
}.

(** The frame fr moved to the point pt, all else kept. *)
Definition with_point (fr : frame) (pt : point) : frame :=
  mkFrame (fr_fn fr) (fr_env fr) (fr_locals fr) (fr_doomed fr) pt.

(** The new frame of a function f called with the words xs, as
    `call_outcome/8` starts it: parameters bound to the first arguments
    as they are, each local declared and not yet allocated, at the
    entry block; a variadic callee first takes the snapshot of all its
    arguments (`entry_snapshot/6`). None if there are fewer arguments
    than parameters or f has no blocks. *)
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

(** ## The entry argument snapshot *)

(** The name of the environment's hidden entry that holds the pointer
    to a variadic callee's argument snapshot, which `va_args` reads. *)
Definition va_snapshot : name := TApp "hidden" [TAtom "va_snapshot"].

(** As `snapshot_values/5`: the memory m with the argument words xs
    stored from address a on, 8 bytes apart, each as `p` if it is a
    pointer (its address in the bytes, its [[capability]] in the
    [[aux]]), else as `l`. The stores are into a [[fresh]] object of 8
    bytes per argument, so their checks pass. *)
Fixpoint snapshot_values (xs : list word) (a : Z) (m : mem) : mem :=
  match xs with
  | [] => m
  | WPtr p :: rest =>
      snapshot_values rest (a + 8) (store_aux (store_bytes m a 8 (ptr_addr p)) a (ptr_cap p))
  | WInt n :: rest => snapshot_values rest (a + 8) (store_bytes m a 8 n)
  | _ :: rest => snapshot_values rest (a + 8) m
  end.

(** The words `snapshot_values/5` can store: integers and pointers. *)
Definition snapshot_word (x : word) : bool :=
  match x with WInt _ | WPtr _ => true | _ => false end.

(** The [[block]] labelled l among bs. *)
Fixpoint find_block (l : name) (bs : list block) : option block :=
  match bs with
  | [] => None
  | b :: bs' => if name_eqb (b_label b) l then Some b else find_block l bs'
  end.

(** As `phis_env/6`: the environment after a block's [[phi|phis]],
    entered from the block from. Each phi reads its value for the edge
    from that predecessor in the environment e0 as it was on entry, so
    they all bind at once. An entry block (from None) has no phis. *)
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

(** As `invalidate_locals/3`: an invocation's named locals end with it.
    Their [[identity|identities]], bytes and [[aux]] stay; their bounds
    become empty, so any later access through them traps. *)
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

(** ## Calls *)

(** As `function_check_res/3`: the pointer p designates a function
    only with that function's [[capability]] at its exact callable
    address; otherwise the check traps. A pointer with an external
    capability has no answer here. *)
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

(** As `result_words/2`: the [[class|classes]] of the words a call site
    reads. *)
Definition result_words (r : call_result) : list class :=
  match r with
  | CVoid => []
  | CResult _ k => [k]
  | CTuple rs => map snd rs
  end.

(** As `return_words(Ret, Ks)` in interp.pl: the [[class|classes]] of
    the words a function returns. *)
Definition return_words (t : ret_type) : list class :=
  match t with
  | RVoid => []
  | RTuple ks => ks
  | RClass k => [k]
  end.

(** The kinds of word a call passes or returns: integer, pointer,
    single float and double float. *)
Inductive word_kind : Type := IntWord | PtrWord | SingleWord | DoubleWord.

(** As `word_class/2`: the kind of word a [[class]] k is. Classes w
    and l are the same word; p, s and d are each their own. *)
Definition word_class (k : class) : option word_kind :=
  match k with
  | W | L => Some IntWord
  | P => Some PtrWord
  | Single => Some SingleWord
  | Double => Some DoubleWord
  | _ => None
  end.

(** Whether two word kinds are the same. *)
Definition word_kind_eqb (a b : word_kind) : bool :=
  match a, b with
  | IntWord, IntWord | PtrWord, PtrWord | SingleWord, SingleWord | DoubleWord, DoubleWord => true
  | _, _ => false
  end.

(** The `->` condition of `indirect_call_conv/7`: both lists of words
    have word classes, and the same ones. *)
Definition same_words (ks ks' : list class) : bool :=
  match map_option word_class ks, map_option word_class ks' with
  | Some cs, Some cs' =>
      (length cs =? length cs')%nat && forallb (fun p => word_kind_eqb (fst p) (snd p)) (combine cs cs')
  | _, _ => false
  end.

(** As `generic_word/4`: the word x written at [[class]] from and read
    at class to through the [[fast-generic-convention|generic entry]].
    An integer read as a pointer has no [[capability]]; a pointer read
    as an integer or a float is its address. *)
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

(** What converting a call through a function pointer gives: a
    [[trap]], or the converted arguments ys and, if the result words
    need converting too, the caller's and callee's word classes. *)
Inductive conv : Type :=
| ConvTrap (why : reason)
| Converted (ys : list word) (words : option (list class * list class)).

(** As `indirect_call_conv/7`: a call through a pointer to f, reading
    its result as r, with arguments args whose values are xs. It traps
    if the caller passes fewer arguments than f has parameters or reads
    more result words than f returns; otherwise each argument is read
    as f's parameter through the
    [[fast-generic-convention|generic entry]] ([generic_word]). *)
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

(** As `outcome_words/2`: the words a returning [[outcome]] returns;
    None for one that does not return. *)
Definition outcome_words (o : outcome) : option (list word) :=
  match o with
  | RetVoid => Some []
  | Ret x => Some [x]
  | Rets xs => match xs with _ :: _ :: _ => Some xs | _ => None end
  | _ => None
  end.

(** The returning outcome that returns the words ys. *)
Definition words_outcome (ys : list word) : outcome :=
  match ys with
  | [] => RetVoid
  | [y] => Ret y
  | _ => Rets ys
  end.

(** As `converted_outcome/4`: the callee's outcome o as a call site
    that reads the word classes caller reads it, each word converted
    from the callee's class by [generic_word]. An outcome that does not
    return passes unchanged. *)
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

(** As `call_outcome_result/5` for a returning outcome o: the caller's
    environment e with the returned words bound as its Res r reads them. *)
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

(** ## Instructions *)

(** What one instruction does: continue with an environment, locals
    and memory; stop with an [[outcome]]; call a function with the
    words xs, the caller to read the result as pd says; allocate for
    the request q, going on as k says of the new base; or call a
    function outside the [[core subset]]. *)
Inductive inst_out : Type :=
| IContinue (e : env) (locals : list (name * option Z)) (m : mem)
| IStop (o : outcome)
| ICall (f : func) (xs : list word) (pd : pending)
| IFresh (q : alloc_req) (k : Z -> env * list (name * option Z) * mem)
| ICallOutside (f : name).

(** As `res_result/5`: an operation's result r bound to the temporary
    d, or its [[trap]] or [[unchecked]] reason as the outcome. *)
Definition bind_res (d : name) (r : res word) (e : env) locals (m : mem) : inst_out :=
  match r with
  | RVal x => IContinue (put d x e) locals m
  | RTrap why => IStop (Trap why)
  | RUnchecked why => IStop (Unchecked why)
  end.

(** As `store_res_result/4`: a store's result r, going on with nothing
    bound, or its trap or unchecked reason as the outcome. *)
Definition store_out (r : res unit) (e : env) locals (m : mem) : inst_out :=
  match r with
  | RVal _ => IContinue e locals m
  | RTrap why => IStop (Trap why)
  | RUnchecked why => IStop (Unchecked why)
  end.

(** As `width_value_class/2` (filc_amd64.pl): the [[class]] at which a
    raw store of width w reads the value it stores. *)
Definition width_value_class (w : width) : option class :=
  match w with
  | Wb | Wh | Ww => Some W
  | Wl => Some L
  | Wp => Some P
  | Ws => Some Single
  | Wd => Some Double
  | Wx => Some Extended
  end.

(** The name of libc's `free`, the one [[external call]] the model
    runs. *)
Definition free_name : name := TAtom "free".

(** A call of a name f the module does not define as a function:
    `inst_result/5`'s call of `global(F)`. Data the module defines is
    not a function, and the call traps, as native code's function check
    does. Otherwise it is `external_call_outcome/9`: only libc's
    `void free(p)` is modeled, through the [[runtime]]'s free, the
    genv's [ge_free]; any other external call is stuck until
    Campaign 4 gives it a [[external-call|contract]]. *)
Definition external_call (ge : genv) (f : name) (r : call_result) (args : list arg)
    (xs : list word) (e : env) locals (m : mem) : option inst_out :=
  match lookup f (ge_globals ge) with
  | Some _ => Some (IStop (Trap NotAFunction))
  | None =>
      if negb (name_eqb f free_name) then None
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

(** As `inst_result/5` for the [[core subset]]: what the instruction i
    does in the frame fr with memory m. None where the interpreter
    throws or fails, such as a [[temporary]] read before it is
    assigned or an access through an external capability. *)
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
                          (* a variadic callee gets the extra arguments
                             unconverted after its parameters *)
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

(** As `doomed_result/5`: an instruction's result out, adjusted for
    [[doomed|doom]], with the frame's doom after it. A [[check_ahead]]
    whose early bytes fail yields its pointer and dooms the run
    (docs/schedule.md). From then on it must reach, through
    [[ahead-transparent]] instructions only, an access whose reference
    check fails: an [[unchecked]] [[raw access]] there is the program's
    [[trap]], made early. A [[renew]] of another object (alias) or a
    wrong [[limit]] stays a broken pass. *)
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

(** ## Steps *)

(** What one [[step]] gives:
    - [Next c], the next [[configuration]];
    - [Done o], the run's [[outcome]];
    - [Fresh q k], an allocation of the request q, whose next
      configuration is [k base] for any base [fresh] in the memory
      ([step_rel] makes that choice nondeterministic);
    - [Stuck why], where the interpreter throws or fails (a call to an
      external symbol, an access through an external capability, a
      temporary read before it is assigned, an ill-classed word); the
      step relation has no step there. *)
Inductive step_result : Type :=
| Next (c : config)
| Done (o : outcome)
| Fresh (q : alloc_req) (k : Z -> config)
| Stuck (why : string).

(** The step result r, or stuck with the label why where there is
    none. *)
Definition or_stuck (why : string) (r : option step_result) : step_result :=
  match r with Some s => s | None => Stuck why end.

(** The configuration after the frame fr, in memory m, moved on. *)
Definition continue_at (c : config) (fr : frame) (m : mem) (fuel : Z) : config :=
  mkConfig fr (c_callers c) m fuel.

(** The end of the running invocation of the configuration c with the
    returning outcome o (`call_outcome/8` after `block_outcome/7`, then
    the caller's `call_outcome_result/5`): its locals end, and the
    caller, if any, reads the result and goes on; with no caller, o is
    the run's outcome. *)
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

(** As `edge_outcome/7`: taking the edge from the block from to the
    target t. A [[poll|poll edge]] reached while [[doomed]] means the
    early check was not anticipated, an [[unchecked]] outcome. *)
Definition edge_step (c : config) (from : name) (t : target) : step_result :=
  let fr := c_frame c in
  match t, fr_doomed fr with
  | Poll _, Some why => Done (Unchecked (Ahead why))
  | _, _ => Next (continue_at c (with_point fr (Enter (edge_label t) (Some from)))
                              (c_mem c) (c_fuel c))
  end.

(** As `result_outcome/6` and `jump_outcome/7`: the step of the jump j
    that ends block l, a goto, a branch on a word, or a return. A
    doomed frame may not return: its early check was not anticipated. *)
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

(** The step after an instruction's result out in block l, with the
    instructions rest and the jump j left and the doom doomed after it:
    on in the block, the outcome, into a callee (the caller suspended
    on top of c's callers), or an allocation. *)
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

(** One [[step]] of the configuration c in the global environment ge:
    take the argument snapshot, enter a block (spending [[fuel]] and
    binding its phis), run one instruction, or take the block's jump. *)
Definition step (ge : genv) (c : config) : step_result :=
  let fr := c_frame c in
  let m := c_mem c in
  match fr_at fr with
  | Snapshot xs l =>
      (* entry_snapshot/6 and args_snapshot/4: no arguments is a null
         pointer; otherwise a fresh 16-aligned object holds them, and
         its pointer is read-only. *)
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
      (* block_outcome/7: fuel first, then the block's phis. *)
      if c_fuel c =? 0 then Done OutOfFuel else
      or_stuck "block" (
        let* b := find_block l (fn_blocks (fr_fn fr)) in
        let* e := phis_env ge (b_phis b) from (fr_env fr) in
        Some (Next (mkConfig (mkFrame (fr_fn fr) e (fr_locals fr) (fr_doomed fr)
                                      (Exec l (b_insts b) (b_jump b)))
                             (c_callers c) m (c_fuel c - 1))))
  | Exec l [] j => jump_step ge c l j
  | Exec l (i :: rest) j =>
      (* insts_result/5: a doomed run stops at the first instruction
         that is not ahead_transparent. *)
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

(** ## The step relation *)

(** The configuration c' may follow c. An allocation's base is any
    that is [fresh] in c's memory; the interpreter's choice is one. *)
Inductive step_rel (ge : genv) : config -> config -> Prop :=
| step_next : forall c c', step ge c = Next c' -> step_rel ge c c'
| step_fresh : forall c q k base,
    step ge c = Fresh q k -> fresh (c_mem c) q base -> step_rel ge c (k base).

(** The run in the configuration c ends now with the outcome o. *)
Definition final (ge : genv) (c : config) (o : outcome) : Prop := step ge c = Done o.

(** The configuration c' follows c after any number of steps of
    [step_rel]. *)
Definition reachable (ge : genv) : config -> config -> Prop :=
  clos_refl_trans config (step_rel ge).
