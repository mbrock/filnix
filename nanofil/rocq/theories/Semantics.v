(** The small-step semantics of the checked IR's core subset,
    transcribed from interp.pl's `run/5`.

    The interpreter is a big-step relation over blocks: `block_outcome`
    runs a block and everything after it, and a call runs its callee to
    an outcome inside the instruction. The model takes the same steps
    one at a time over an explicit configuration (formal.md's decision:
    small-step, not interaction trees), so that Campaign 3's invariants
    can be stated between any two steps.

    ## The configuration

    | Part | Is | interp.pl |
    |---|---|---|
    | `c_frame` | the running invocation | the `ctx(...)` term, Env and the block being run |
    | `c_callers` | the suspended callers, each with how it reads the result | Prolog's own stack |
    | `c_mem` | memory | `s(Mem, Fuel)`'s Mem, less Next |
    | `c_fuel` | blocks left to run | `s(Mem, Fuel)`'s Fuel |

    A frame is at `Enter l from`, about to run block l entered from
    `from` (None for the entry), or at `Exec l insts jump`, inside block
    l with insts left to run. A variadic callee starts at `Snapshot xs
    l`, where it takes the snapshot of its arguments xs, an allocation,
    before entering its entry block l. Entering a block costs one unit of fuel;
    with none left the run is `OutOfFuel`, as `block_outcome/7` says.

    ## Steps

    `step` gives the next configuration, the outcome, or `Fresh q k`:
    an allocation of q, whose next configuration is `k base` for any
    base `fresh` in the memory. The step relation `step_rel` makes that
    choice nondeterministic. `Stuck` is where the interpreter throws or
    fails (a call to an external symbol, an access through an external
    capability, a temporary read before it is assigned, an ill-classed
    word); the relation has no step there. Externals stay stuck until
    Campaign 4 gives them contracts; only `free` is modeled, as the
    genv's `ge_free`, the runtime's.

    ## Outcomes

    | Gallina | interp.pl |
    |---|---|
    | `Ret x` | `ret(V)` |
    | `Rets xs` | `rets([X1, X2])` |
    | `RetVoid` | `ret` |
    | `Unreachable` | `unreachable` |
    | `UB why` | `ub(Reason)`: here only `float_conversion`, an invalid float-to-integer conversion |
    | `Trap why` | `trap(Reason)` |
    | `Unchecked why` | `unchecked(Reason)` |
    | `OutOfFuel` | `out_of_fuel` | *)

From Stdlib Require Import String ZArith List Bool Relations.
From Nanofil Require Import Term Syntax Values Memory Ops.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

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

(** A function the module names: one with a body in the subset, or
    one outside it. *)
Inductive fn_def : Type := Defined (f : func) | Outside (n : name).

(** The module ready to run (`module_prepared/2`'s Fns and Globals),
    and the runtime's free that a call of libc's `free` runs: Memory.v's
    `free_res` in the interpreter, `R.free` of a `Runtime` R (Run.v's
    `Driver`, Machine.v). *)
Record genv : Type := mkGenv {
  ge_module : module;
  ge_globals : list (name * ptr);
  ge_free : word -> mem -> option (res unit * mem)
}.

Fixpoint find_direct (n : name) (items : module) : option fn_def :=
  match items with
  | [] => None
  | IFunc f :: rest => if name_eqb (fn_name f) n then Some (Defined f) else find_direct n rest
  | IOutside f _ :: rest => if name_eqb f n then Some (Outside f) else find_direct n rest
  | _ :: rest => find_direct n rest
  end.

Fixpoint find_alias (n : name) (items : module) : option name :=
  match items with
  | [] => None
  | IAlias a _ t :: rest => if name_eqb a n then Some t else find_alias n rest
  | _ :: rest => find_alias n rest
  end.

(** `get_assoc(F, Fns, Fn)`: Fns has the module's functions, and each
    alias of a function, called as its target. *)
Definition find_fn (ge : genv) (n : name) : option fn_def :=
  match find_direct n (ge_module ge) with
  | Some d => Some d
  | None => let* t := find_alias n (ge_module ge) in find_direct t (ge_module ge)
  end.

(** ## Values *)

Definition env := list (name * word).

(** `value_x(K, V, Ctx, Env, X)`: the IR value V read at class K. A
    constant at `p` has no capability; a symbol the module does not
    define is `ptr(0, ext(Name))`. *)
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

Fixpoint map_option {X Y : Type} (f : X -> option Y) (xs : list X) : option (list Y) :=
  match xs with
  | [] => Some []
  | x :: xs' => let* y := f x in let* ys := map_option f xs' in Some (y :: ys)
  end.

Fixpoint map2_option {X Y Z : Type} (f : X -> Y -> option Z) (xs : list X) (ys : list Y)
  : option (list Z) :=
  match xs, ys with
  | [], [] => Some []
  | x :: xs', y :: ys' => let* z := f x y in let* zs := map2_option f xs' ys' in Some (z :: zs)
  | _, _ => None
  end.

(** `arg_x(Ctx, Env, arg(K, V), X)`. *)
Definition arg_x (ge : genv) (e : env) (a : arg) : option word :=
  match a with Arg k v => value_x ge e k v end.

(** `flight_arg_x/4`: an address projection takes the low 64 bits of a
    pointer's address; any other argument is read at `l`. *)
Definition flight_arg_x (ge : genv) (e : env) (a : flight_arg) : option word :=
  match a with
  | FAddress v =>
      let* x := value_x ge e P v in
      match x with WPtr p => Some (WInt (ptr_addr p mod 2 ^ 64)) | _ => None end
  | FValue v => value_x ge e L v
  end.

(** `flight_cap/4`: a lower copies a capability's identity. *)
Definition flight_cap (ge : genv) (e : env) (lw : flight_lower) : option cap :=
  match lw with
  | LowerNone => Some CNone
  | LowerOf v =>
      let* x := value_x ge e P v in
      match x with WPtr p => Some (ptr_cap p) | _ => None end
  end.

(** ## Frames and configurations *)

Inductive point : Type :=
| Snapshot (xs : list word) (l : name)
| Enter (l : name) (from : option name)
| Exec (l : name) (insts : list inst) (j : jump).

Record frame : Type := mkFrame {
  fr_fn : func;
  fr_env : env;
  fr_locals : list (name * option Z);
  fr_doomed : option reason;
  fr_at : point
}.

(** How a suspended caller reads its callee's outcome: the call's Res,
    and for a call through the generic entry the caller's and callee's
    word classes (`indirect_call_conv/7`'s `conv(CallerWords,
    CalleeWords)`). *)
Record pending : Type := mkPending {
  pd_res : call_result;
  pd_conv : option (list class * list class)
}.

Record config : Type := mkConfig {
  c_frame : frame;
  c_callers : list (frame * pending);
  c_mem : mem;
  c_fuel : Z
}.

Definition with_point (fr : frame) (pt : point) : frame :=
  mkFrame (fr_fn fr) (fr_env fr) (fr_locals fr) (fr_doomed fr) pt.

(** `call_outcome/8`'s callee invocation: parameters bound to the first
    arguments as they are, each local declared and not yet allocated,
    at the entry block; a variadic callee first takes the snapshot of
    all its arguments (`entry_snapshot/6`). *)
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

(** The environment's hidden `va_snapshot` entry: the snapshot's
    pointer, for `va_args`. *)
Definition va_snapshot : name := TApp "hidden" [TAtom "va_snapshot"].

(** `snapshot_values(Xs, A, Base, Mem0, Mem)`: each argument stored as
    `p` if it is a pointer, else as `l`, 8 bytes apart. The stores are
    into a fresh object of 8 bytes per argument, so their checks
    pass. *)
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

Fixpoint find_block (l : name) (bs : list block) : option block :=
  match bs with
  | [] => None
  | b :: bs' => if name_eqb (b_label b) l then Some b else find_block l bs'
  end.

(** `phis_env(Phis, Ctx, Pred, EntryEnv, Env0, Env)`: each phi reads its
    value for the edge from Pred in the environment as it was on entry,
    so they all bind at once. An entry block has no phis. *)
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

(** `invalidate_locals/3`: an invocation's named locals end with it.
    Their identities, bytes and aux stay; their bounds become empty. *)
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

(** `function_check_res(P, Ctx, Res)`: P designates a function only
    with that function's capability at its exact callable address. *)
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

(** `result_words(Res, Ks)`: the classes of the words a call site reads. *)
Definition result_words (r : call_result) : list class :=
  match r with
  | CVoid => []
  | CResult _ k => [k]
  | CTuple rs => map snd rs
  end.

(** `return_words(Ret, Ks)`: the classes of the words a function returns. *)
Definition return_words (t : ret_type) : list class :=
  match t with
  | RVoid => []
  | RTuple ks => ks
  | RClass k => [k]
  end.

(** `word_class(K, Class)`: w and l are the same word; p, s and d are
    each their own. *)
Inductive word_kind : Type := IntWord | PtrWord | SingleWord | DoubleWord.

Definition word_class (k : class) : option word_kind :=
  match k with
  | W | L => Some IntWord
  | P => Some PtrWord
  | Single => Some SingleWord
  | Double => Some DoubleWord
  | _ => None
  end.

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

(** `generic_word(From, To, X, Y)`: Y is the word X written at class
    From and read at class To through the generic entry. *)
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

(** The conversion of a call through a function pointer
    (`indirect_call_conv/7`): a trap, or the converted arguments and
    whether the result words need converting too. *)
Inductive conv : Type :=
| ConvTrap (why : reason)
| Converted (ys : list word) (words : option (list class * list class)).

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

(** `outcome_words(Out, Xs)`: the words a returning outcome returns. *)
Definition outcome_words (o : outcome) : option (list word) :=
  match o with
  | RetVoid => Some []
  | Ret x => Some [x]
  | Rets xs => match xs with _ :: _ :: _ => Some xs | _ => None end
  | _ => None
  end.

Definition words_outcome (ys : list word) : outcome :=
  match ys with
  | [] => RetVoid
  | [y] => Ret y
  | _ => Rets ys
  end.

(** `converted_outcome(CallerWords, CalleeWords, Out0, Out)`: the
    callee's outcome as a call site that reads CallerWords reads it. *)
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

(** `call_outcome_result/5` for a returning outcome: the caller's
    environment with the returned words bound as its Res reads them. *)
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
    and memory; stop with an outcome; call a function; or allocate. *)
Inductive inst_out : Type :=
| IContinue (e : env) (locals : list (name * option Z)) (m : mem)
| IStop (o : outcome)
| ICall (f : func) (xs : list word) (pd : pending)
| IFresh (q : alloc_req) (k : Z -> env * list (name * option Z) * mem)
| ICallOutside (f : name).

(** `res_result/5` and `store_res_result/4`. *)
Definition bind_res (d : name) (r : res word) (e : env) locals (m : mem) : inst_out :=
  match r with
  | RVal x => IContinue (put d x e) locals m
  | RTrap why => IStop (Trap why)
  | RUnchecked why => IStop (Unchecked why)
  end.

Definition store_out (r : res unit) (e : env) locals (m : mem) : inst_out :=
  match r with
  | RVal _ => IContinue e locals m
  | RTrap why => IStop (Trap why)
  | RUnchecked why => IStop (Unchecked why)
  end.

(** `width_value_class(Width, K)`. *)
Definition width_value_class (w : width) : option class :=
  match w with
  | Wb | Wh | Ww => Some W
  | Wl => Some L
  | Wp => Some P
  | Ws => Some Single
  | Wd => Some Double
  | Wx => Some Extended
  end.

(** A call of a name the module does not define as a function:
    `inst_result/5`'s call of `global(F)`. Data the module defines is
    not a function, and the call traps, as native code's function check
    does. Otherwise it is `external_call_outcome/9`: only libc's
    `void free(p)` is modeled, through the runtime's free. *)
Definition free_name : name := TAtom "free".

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

(** `inst_result(Inst, Ctx, Env0, S0, Result)` for the core subset. *)
Definition inst_step (ge : genv) (fr : frame) (m : mem) (i : inst) : option inst_out :=
  let e := fr_env fr in
  let locals := fr_locals fr in
  match i with
  | Loc _ _ => Some (IContinue e locals m)
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

(** `doomed_result/5`: a check_ahead whose early bytes fail yields its
    pointer and dooms the run (docs/schedule.md). From then on it must
    reach, through ahead_transparent instructions only, an access whose
    reference check fails: an unchecked raw access there is the
    program's trap, made early. A renew of another object or a wrong
    limit stays a broken pass. *)
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

Inductive step_result : Type :=
| Next (c : config)
| Done (o : outcome)
| Fresh (q : alloc_req) (k : Z -> config)
| Stuck (why : string).

Definition or_stuck (why : string) (r : option step_result) : step_result :=
  match r with Some s => s | None => Stuck why end.

(** The configuration after the frame fr, in memory m, moved on. *)
Definition continue_at (c : config) (fr : frame) (m : mem) (fuel : Z) : config :=
  mkConfig fr (c_callers c) m fuel.

(** The end of the running invocation with the returning outcome o
    (`call_outcome/8` after `block_outcome/7`, then the caller's
    `call_outcome_result/5`): its locals end, and the caller, if any,
    reads the result and goes on. *)
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

(** `edge_outcome/7`: a poll edge reached while doomed means the early
    check was not anticipated. *)
Definition edge_step (c : config) (from : name) (t : target) : step_result :=
  let fr := c_frame c in
  match t, fr_doomed fr with
  | Poll _, Some why => Done (Unchecked (Ahead why))
  | _, _ => Next (continue_at c (with_point fr (Enter (edge_label t) (Some from)))
                              (c_mem c) (c_fuel c))
  end.

(** `result_outcome/6` and `jump_outcome/7`. *)
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

(** The step after an instruction's result: on in the block, the
    outcome, into a callee, or an allocation. *)
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

(** One step of the configuration c. *)
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

(** `step_rel ge c c'`: c' may follow c. An allocation's base is any
    that is fresh in c's memory; the interpreter's choice is one. *)
Inductive step_rel (ge : genv) : config -> config -> Prop :=
| step_next : forall c c', step ge c = Next c' -> step_rel ge c c'
| step_fresh : forall c q k base,
    step ge c = Fresh q k -> fresh (c_mem c) q base -> step_rel ge c (k base).

(** `final ge c o`: the run in c ends now with the outcome o. *)
Definition final (ge : genv) (c : config) (o : outcome) : Prop := step ge c = Done o.

(** `reachable ge c c'`: c' follows c after any number of steps. *)
Definition reachable (ge : genv) : config -> config -> Prop :=
  clos_refl_trans config (step_rel ge).
