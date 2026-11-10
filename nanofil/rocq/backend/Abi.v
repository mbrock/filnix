(** Fil-C ABI lowering (filc_abi.pl's `lower_function/4` and
    `lower_thunks/2`): the [plan] of a checked function, before any
    register or frame offset is chosen. Its frame names payload
    slots, ordered roots and aliases; a call, a getter or a return
    becomes a list of ABI actions in the place of the instruction it
    lowers; and the function's public object says how a generic
    caller reaches it.

    Fast words split a pointer into its address and its lower;
    generic cells are one eightbyte a value. `registers` or
    `buffer(N)` is the return protocol. Nothing here knows a native
    location.

    The first version shares the frame's pools and gives every
    temporary and phi a slot of its own kind, as the Prolog compiler
    does without `-O`; it has no setjmp sites. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Validate Maps Cfg Transport.
From Backend Require Import Order Plan Fuse Liveness FrameSlots.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Signatures *)

(** As `class_digit/2`: the digit of a word of the class k in a
    signature: 0 for an integer, 7 for a pointer, 1 and 2 for the
    floats. Other classes have none. *)
Definition class_digit (k : class) : option Z :=
  match k with
  | W | L => Some 0
  | P => Some 7
  | Single => Some 1
  | Double => Some 2
  | _ => None
  end.

(** As `bijective_value/2`: the digits ds, the first the least, as a
    number in bijective base 11. *)
Fixpoint bijective_value (ds : list Z) : Z :=
  match ds with
  | [] => 0
  | d :: ds' => d + 1 + 11 * bijective_value ds'
  end.

(** As `never_signature/1`: the signature no function object has,
    for more than 16 argument words. A call with it always goes
    generic. *)
Definition never_signature : Z := 18446744073709551615.

(** As `ret_kinds/2`: the classes a function of the return type r
    returns. *)
Definition ret_kinds (r : ret_type) : option (list class) :=
  match r with
  | RVoid => Some []
  | RTuple ks => Some ks
  | RClass k => match k with
                | W | L | P | Single | Double => Some [k]
                | _ => None
                end
  end.

(** As `word_codes/3`: the bijective values of the return digits and
    of the argument digits of a function returning r on parameters of
    the classes ks. *)
Definition word_codes (r : ret_type) (ks : list class) : option (Z * Z) :=
  let* rks := ret_kinds r in
  let* rds := all_some class_digit rks in
  let* ads := all_some class_digit ks in
  Some (bijective_value rds, bijective_value ads).

(** As `signature/3`: Fil-C's fast-call signature number, 1 + R +
    133 * A, or the [never_signature] for more than 16 arguments. It
    names private bodies. *)
Definition signature (r : ret_type) (ks : list class) : option Z :=
  let* c := word_codes r ks in
  Some (if Zlength ks <=? 16 then 1 + fst c + 133 * snd c else never_signature).

(** As `return_protocol/2`: how a function of the return type r
    returns: through a buffer if more than two integer words come
    back, a pointer being two. Float words return in registers of
    their own. *)
Definition return_protocol (r : ret_type) : option protocol :=
  let* ks := ret_kinds r in
  let* ns := all_some (fun k => match k with
                                | P => Some 2
                                | W | L => Some 1
                                | Single | Double => Some 0
                                | _ => None
                                end) ks in
  let n := fold_left Z.add ns 0 in
  Some (if n >? 2 then Buffer n else Registers).

(** As `result_ret/2`: the return type a call reading the result r
    expects. *)
Definition result_ret (r : call_result) : ret_type :=
  match r with
  | CVoid => RVoid
  | CResult _ k => RClass k
  | CTuple rs => RTuple (map snd rs)
  end.

(** ## Symbols *)

(** What a call needs of a function the module defines: its
    linkage, its own signature if it has one, and whether it is
    variadic. *)
Record fentry : Type := mkFentry {
  fe_linkage : term;
  fe_sig : option Z;
  fe_variadic : bool
}.

(** As `module_symbols/2`: a module's functions and data by name,
    the first of a name, and the names it declares weak. *)
Record symbols : Type := mkSymbols {
  sy_funcs : nmap fentry;
  sy_data : nmap linkage;
  sy_weak : nmap unit
}.

(** The [fentry] of a function outside the core subset, read off its
    term t. *)
Definition outside_entry (t : term) : option fentry :=
  let* sg := term_sig t in
  Some (mkFentry (sig_linkage sg)
                 (let* ks := all_some dclass (sig_params sg) in
                  let* r := dret (sig_ret sg) in
                  signature r ks)
                 (sig_variadic sg)).

(** As `module_symbols/2`. *)
Definition module_symbols (md : module) : symbols :=
  fold_left
    (fun sy it =>
       let func := fun n fe => if nm_mem n (sy_funcs sy) then sy
                               else mkSymbols (nm_add n fe (sy_funcs sy)) (sy_data sy) (sy_weak sy) in
       match it with
       | IFunc f =>
           func (fn_name f) (mkFentry (fn_linkage f) (signature (fn_ret f) (map fst (fn_params f)))
                                      (variadic_func f))
       | IOutside n t =>
           match outside_entry t with Some fe => func n fe | None => sy end
       | IData n LExternWeak _ [] =>
           mkSymbols (sy_funcs sy) (sy_data sy) (nm_add n tt (sy_weak sy))
       | IData _ LExternWeak _ _ => sy
       | IData n lk _ _ =>
           if nm_mem n (sy_data sy) then sy
           else mkSymbols (sy_funcs sy) (nm_add n lk (sy_data sy)) (sy_weak sy)
       | IAlias _ _ _ => sy
       end)
    md (mkSymbols nm_empty nm_empty nm_empty).

(** Whether the term t is the atom a. *)
Definition is_atom (a : string) (t : term) : bool :=
  match t with TAtom b => String.eqb a b | _ => false end.

(** As `weak_defined/2`: the module defines the name n with linkage
    `weak` or `ro(weak)`, so another object's definition may replace
    it. *)
Definition weak_defined (sy : symbols) (n : name) : bool :=
  match nm_find n (sy_funcs sy) with
  | Some fe => is_atom "weak" (fe_linkage fe)
  | None => false
  end
  || match nm_find n (sy_data sy) with
     | Some LWeak => true
     | Some (LRo l) => is_atom "weak" l
     | _ => false
     end.

(** As `direct_target/4`: what a direct call of f at the call-site
    signature sig invokes: the private body, under the callee's own
    signature, if the module defines f, not variadic and not weak;
    else the weak thunk of f and sig. *)
Definition direct_target (sy : symbols) (f : name) (sig : sigref) : option call_target :=
  match nm_find f (sy_funcs sy) with
  | Some fe =>
      if negb (fe_variadic fe) && negb (weak_defined sy f)
      then let* s := fe_sig fe in Some (TImplementation f s)
      else Some (TEntry f sig)
  | None => Some (TEntry f sig)
  end.

(** As `getter_target/3`: the getter of the symbol s: this module's
    if it defines s and not weakly, a weak one, which may give null,
    if it declares s weak, else an external one. *)
Definition getter_target (sy : symbols) (s : name) : getter :=
  if (nm_mem s (sy_funcs sy) || nm_mem s (sy_data sy)) && negb (weak_defined sy s)
  then GetLocal s
  else if nm_mem s (sy_weak sy) then GetWeak s
  else GetExternal s.

(** ## Frames *)

(** The standard order of two `N-K` pairs, a temporary and its
    class. *)
Definition temp_compare (a b : name * class) : Datatypes.comparison :=
  match term_compare (fst a) (fst b) with
  | Datatypes.Eq => term_compare (eclass (snd a)) (eclass (snd b))
  | c => c
  end.

(** The destination of a phi and its class. *)
Definition phi_dest (p : phi) : name * class := match p with Phi d k _ => (d, k) end.

(** As `storage_keys/3`: `storage(Pool, I)` for i from 0 up to n. *)
Definition storage_keys (p : pool) (n : Z) : list key :=
  map (fun i => KStorage p (Z.of_nat i)) (seq 0 (Z.to_nat n)).

(** As `body_params/3`: the parameters of the private body of f: a
    variadic function's has the hidden pointer to the promoted
    packet last. *)
Definition body_params (f : func) : list (class * name) :=
  if variadic_func f then fn_params f ++ [(P, va_snapshot)] else fn_params f.

(** As `frame/6`: the frame of a body with the parameters ps and the
    fused blocks bs, returning by ret; with it, the payload keys a
    setjmp would snapshot and the number of named locals.

    The plain keys are the slots of the pools, a shadow for each phi,
    `thread`, `aux`, the return buffer if there is one, and the named
    locals. The roots are the lowers of the pointer slots and of the
    pointer phis' shadows, then the stack auxes of the locals, the
    last root group, as the collector's origin says. *)
Definition frame_of (ps : list (class * name)) (bs : list fblock) (ret : protocol)
  : option (frame * list key * Z) :=
  let phis := flat_map (fun b => map phi_dest (fb_phis b)) bs in
  let temps := sort temp_compare
                    (map (fun p => (snd p, fst p)) ps
                     ++ flat_map (fun b => map phi_dest (fb_phis b)
                                           ++ flat_map finst_defs (fb_insts b)) bs) in
  let shadows := sort temp_compare phis in
  let* sl := temp_slots ps bs temps in
  let pointers := storage_keys PoolPointer (sl_pointers sl) in
  let aliases :=
    flat_map (fun a =>
                match snd a with
                | (PoolPointer, i) =>
                    [(KTmp (fst a), KStorage PoolPointer i);
                     (KLower (KTmp (fst a)), KLower (KStorage PoolPointer i))]
                | (pool, i) => [(KTmp (fst a), KStorage pool i)]
                end) (sl_aliases sl) in
  let locals := flat_map (fun b => flat_map (fun i => match i with
                                                      | FPlain (LocalAlloc x size) => [(x, size)]
                                                      | _ => []
                                                      end) (fb_insts b)) bs in
  let plain := storage_keys PoolScalar (sl_scalars sl) ++ pointers
               ++ storage_keys PoolWide (sl_wides sl)
               ++ map (fun s => KShadow (fst s)) shadows
               ++ [KThread; KAux]
               ++ match ret with Buffer _ => [KRetbuf] | Registers => [] end
               ++ map (fun l => KLocal (fst l) (snd l)) locals in
  let roots := map KLower pointers
               ++ flat_map (fun s => match snd s with
                                     | P => [KLower (KShadow (fst s))]
                                     | _ => []
                                     end) shadows
               ++ map (fun l => KStackAux (fst l)) locals in
  let payload := map KShadow (nsort (map fst shadows)) ++ map KTmp (nsort (map fst temps)) in
  Some (mkFrame plain roots aliases, payload, Zlength locals).

(** ## Words and cells *)

(** As `fast_params/2`: the words a body receives for the parameters
    ps: a pointer is its address and its lower, both at `l`. *)
Definition fast_params (ps : list (class * name)) : list word :=
  flat_map (fun p => match fst p with
                     | P => [Wf L (SrcSlot (KTmp (snd p))); Wf L (SrcSlot (KLower (KTmp (snd p))))]
                     | k => [Wf k (SrcSlot (KTmp (snd p)))]
                     end) ps.

(** As `fast_args/2`: the words of a fast call's arguments. *)
Definition fast_args (args : list arg) : list word :=
  flat_map (fun a => match a with
                     | Arg P v => [Wf L (SrcAddr v); Wf L (SrcLower v)]
                     | Arg k v => [Wf k (SrcVal k v)]
                     end) args.

(** As `payload_class/2`: the class of a value's data word in a
    generic packet. *)
Definition payload_class (k : class) : class := match k with P => L | _ => k end.

(** The elements of xs, each with its index from i. *)
Fixpoint indexed {X : Type} (i : Z) (xs : list X) : list (Z * X) :=
  match xs with
  | [] => []
  | x :: xs' => (i, x) :: indexed (i + 1) xs'
  end.

(** As `generic_args/2`: the cells of a generic call's arguments,
    one a value, a pointer's with its lower. *)
Definition generic_args (args : list arg) : list cell :=
  map (fun ia => match snd ia with
                 | Arg k v => Cell (fst ia) (payload_class k) (CellValue v)
                                   (match k with P => Some (CellValue v) | _ => None end)
                 end) (indexed 0 args).

(** As `generic_params/2`: the words a generic packet holds for
    parameters of the classes ks: a pointer's data and aux, another
    value's data. *)
Definition generic_params (ks : list class) : list word :=
  flat_map (fun ik => match snd ik with
                      | P => [Wf L (SrcData (fst ik)); Wf L (SrcAux (fst ik))]
                      | k => [Wf k (SrcData (fst ik))]
                      end) (indexed 0 ks).

(** As `result_tos/2`: the results a call reads. *)
Definition result_tos (r : call_result) : list (name * class) :=
  match r with
  | CVoid => []
  | CResult d k => [(d, k)]
  | CTuple rs => rs
  end.

(** Whether k is a float class a register returns: `s` or `d`. *)
Definition returned_float (k : class) : bool :=
  match k with Single | Double => true | _ => false end.

(** As `fast_result/2`: the return protocol and the channels of a
    fast call's result r. One float has a channel of its own; a
    tuple with a float names each slot's class; anything else is
    integer words, a pointer two. *)
Definition fast_result (r : call_result) : option (protocol * channels) :=
  let* ret := return_protocol (result_ret r) in
  let split := fun (d : name * class) => match snd d with
                                         | P => [KTmp (fst d); KLower (KTmp (fst d))]
                                         | _ => [KTmp (fst d)]
                                         end in
  Some (ret,
        match r with
        | CResult d k =>
            if returned_float k then ChFloat k d else ChSlots (split (d, k))
        | CTuple rs =>
            if existsb (fun d => returned_float (snd d)) rs
            then ChTyped (flat_map (fun d => match snd d with
                                             | P => [(L, KTmp (fst d)); (L, KLower (KTmp (fst d)))]
                                             | k => [(k, KTmp (fst d))]
                                             end) rs)
            else ChSlots (flat_map split rs)
        | CVoid => ChSlots []
        end).

(** As `generic_result/2`: the bytes a generic call's result r needs
    and the cells it comes back in. *)
Definition generic_result (r : call_result) : Z * list cell :=
  let tos := result_tos r in
  (8 * Zlength tos,
   map (fun id => match snd id with
                  | (d, k) => Cell (fst id) k (CellValue (Tmp d))
                                   (match k with P => Some (CellValue (Tmp d)) | _ => None end)
                  end) (indexed 0 tos)).

(** ## Instructions *)

(** As `call_signature/3`: the signature of a call reading r on the
    arguments args. *)
Definition call_signature (r : call_result) (args : list arg) : option Z :=
  signature (result_ret r) (map arg_class args).

(** As `call_symbol_signature/4`: the signature in the name of the
    weak thunk a direct call goes through. Every call of more than 16
    words has the never signature, so its thunk is named by the whole
    word list. *)
Definition call_symbol_signature (r : call_result) (args : list arg) : option sigref :=
  let* s := call_signature r args in
  if s =? never_signature
  then let* c := word_codes (result_ret r) (map arg_class args) in Some (SigNever (fst c) (snd c))
  else Some (SigNumber s).

(** As `small_copy/5`: the inline filter of a call of f that is a
    memcpy or memmove of a constant 1 to 16 bytes, if the module
    defines neither: the emitter may test for the common case in
    front of the unchanged call. *)
Definition small_copy (sy : symbols) (f : name) (r : call_result) (args : list arg)
  : option action :=
  match args with
  | [Arg P d; Arg P s; Arg L (Const n)] =>
      if (is_atom "memcpy" f || is_atom "memmove" f)
         && (1 <=? n) && (n <=? 16)
         && match r with CVoid | CResult _ P => true | _ => false end
         && negb (nm_mem f (sy_funcs sy)) && negb (nm_mem f (sy_data sy))
      then Some (ACopyFilter d s n r)
      else None
  | _ => None
  end.

(** As `lower_inst/4`: the fused instruction i lowered. A direct
    call invokes its target's fast entry; a call of a checked
    function pointer dispatches on the signature, fast or generic; a
    symbol's address comes from its getter; `va_args` and `va_arg`
    read the promoted packet; a local's declaration initializes it.
    Every other instruction passes through. *)
Definition lower_inst (sy : symbols) (i : finst) : option pinst :=
  match i with
  | FPlain (Call r (Global f) args) =>
      let* sig := call_symbol_signature r args in
      let* target := direct_target sy f sig in
      let* res := fast_result r in
      let call := [AOrigin; AReserveResult (fst res); AInvoke target (fst res) (fast_args args);
                   AResult (fst res) (snd res); AReleaseResult (fst res)] in
      Some (PAbi (match small_copy sy f r args with
                  | Some filter => filter :: call ++ [ACopyJoin]
                  | None => call
                  end))
  | FCall r p args =>
      let* sig := call_signature r args in
      let* res := fast_result r in
      let g := generic_result r in
      Some (PAbi [AOrigin; AReserveResult (fst res);
                  ADispatch p sig (fst res) (fast_args args) (snd res) (8 * Zlength args)
                            (generic_args args) (fst g) (snd g);
                  AReleaseResult (fst res)])
  | FPlain (Let d P Copy [Global s]) => Some (PAbi [AOrigin; AGetter (getter_target sy s) d])
  | FPlain (Let d P VaArgs [Const off]) => Some (PAbi [ASnapshotCursor off d])
  | FPlain (Let d k VaArg [p]) =>
      let* size := match k with
                   | Extended => Some 16
                   | W | Single => Some 4
                   | L | P | Double => Some 8
                   | _ => None
                   end in
      Some (PAbi [AOrigin; AConsumeVa k p size d])
  | FPlain (LocalAlloc x _) => Some (PAbi [AInitializeLocal x])
  | _ => Some (PInst i)
  end.

(** As `lower_jump/4`: the jump j of a function returning r by the
    protocol ret. A return's values are in place before the roots
    are popped, and no safepoint comes between. *)
Definition lower_jump (r : ret_type) (ret : protocol) (j : jump) : pjump :=
  match j with
  | JRet v => PReturnValue r v ret
  | JRets vs =>
      match r, ret with
      | RTuple ks, Buffer n =>
          let ws := fast_args (map (fun kv => Arg (fst kv) (snd kv)) (combine ks vs)) in
          if (Zlength ks =? Zlength vs) && (Zlength ws =? n) then PReturnBuffer ws else PJump j
      | RTuple ks, Registers =>
          if existsb returned_float ks then PReturnTyped ks vs else PReturnRegisters vs
      | _, Registers => PReturnRegisters vs
      | _, _ => PJump j
      end
  | JRetVoid => PReturnVoid ret
  | _ => PJump j
  end.

(** As `lower_block/6`. *)
Definition lower_block (sy : symbols) (r : ret_type) (ret : protocol) (b : fblock)
  : option pblock :=
  let* is := all_some (lower_inst sy) (fb_insts b) in
  Some (mkPBlock (fb_label b) (fb_phis b) is (lower_jump r ret (fb_jump b))).

(** ## Public objects *)

(** As `adapter_return/2`: how an adapter turns the fast result of a
    function returning r into a generic packet. The void result is
    one zero word.

    The words zeroed are the aux of each cell that holds no pointer,
    whatever else comes back: `tuple([l, s])` zeroes `aux(0)` and
    `aux(1)`, so no stale aux word of the caller's reaches a result
    read as a pointer. *)
Definition adapter_return (r : ret_type) : option adapter_result :=
  let* ret := return_protocol r in
  let* ks := ret_kinds r in
  let channel := match ks with
                 | [] => AdVoid
                 | [k] => if returned_float k then AdFloat k else AdWords
                 | _ => if existsb returned_float ks then AdTyped ks else AdWords
                 end in
  let copies := map (fun w => match w with Wf _ s => s end) (generic_params ks) in
  let zeros := match ks with
               | [] => [SrcData 0; SrcAux 0]
               | _ =>
                   flat_map (fun ik => if class_eqb (snd ik) P then [] else [SrcAux (fst ik)])
                            (indexed 0 ks)
               end in
  Some (mkAdapterResult ret channel (8 * Z.max 1 (Zlength ks)) copies zeros).

(** As `public_object/3`: the public object of the function f: a
    fast entry under its signature and a generic adapter, or, for a
    variadic function, a generic entry that promotes the incoming
    packet. *)
Definition public_object (f : func) : option object :=
  let ks := map fst (fn_params f) in
  let need := 8 * Zlength ks in
  let* res := adapter_return (fn_ret f) in
  if variadic_func f
  then Some (GenericOnly need (generic_params ks ++ [Wf L SrcSnapshot; Wf L SrcSnapshot]) res)
  else let* sig := signature (fn_ret f) ks in
       Some (FastAndGeneric sig need (generic_params ks) res).

(** ## The plan of a function *)

(** As `lower_function/4` of the function f after `fused_blocks/5`:
    its plan, with sy the symbols of its module. Nothing if the
    function is outside what the first version lowers. *)
Definition lower_function (sy : symbols) (f : func) : option plan :=
  let* bs := fused_blocks (fn_params f) (fn_blocks f) in
  let* sig := signature (fn_ret f) (map fst (fn_params f)) in
  let* ret := return_protocol (fn_ret f) in
  let body := body_params f in
  let* fr := frame_of body bs ret in
  let* blocks := all_some (lower_block sy (fn_ret f) ret) bs in
  let* obj := public_object f in
  Some (mkPlan (fn_name f) (fn_linkage f) (fn_ret f) sig (fst (fst fr)) ret (fast_params body)
               (snd (fst fr)) blocks obj (snd fr)).

(** ## Thunks *)

(** A direct call that goes through a weak thunk: the callee, the
    signature in the thunk's name, and the call's return type and
    argument classes. *)
Record thunk_call : Type := mkThunkCall {
  tc_name : name;
  tc_sig : sigref;
  tc_ret : ret_type;
  tc_classes : list class
}.

(** A signature in a symbol as its term: the number, or
    `never(R-A)`. *)
Definition sigref_term (s : sigref) : term :=
  match s with
  | SigNumber n => TInt n
  | SigNever r a => TApp "never" [TApp "-" [TInt r; TInt a]]
  end.

(** As `t(F, Sig, Ret, Ks)`, the term `lower_thunks/2` sorts thunk
    calls by. *)
Definition thunk_call_term (c : thunk_call) : term :=
  TApp "t" [tc_name c; sigref_term (tc_sig c); eret (tc_ret c); TList (map eclass (tc_classes c))].

(** The thunk call of a direct call of f returning r on arguments of
    the classes ks, if its target is a thunk and it has a signature. *)
Definition thunk_call_of (sy : symbols) (f : name) (r : ret_type) (ks : list class)
  : list thunk_call :=
  let implemented := match nm_find f (sy_funcs sy) with
                     | Some fe => negb (fe_variadic fe) && negb (weak_defined sy f)
                     | None => false
                     end in
  if implemented then [] else
  match signature r ks with
  | Some s =>
      if s =? never_signature
      then match word_codes r ks with
           | Some c => [mkThunkCall f (SigNever (fst c) (snd c)) r ks]
           | None => []
           end
      else [mkThunkCall f (SigNumber s) r ks]
  | None => []
  end.

(** The return type the term t of a call's result expects: `void`,
    `result(_, K)` or `tuple([result(_, K), ...])`. *)
Definition term_result_ret (t : term) : option ret_type :=
  let class_of := fun r => match r with TApp "result" [_; k] => dclass k | _ => None end in
  match t with
  | TAtom "void" => Some RVoid
  | TApp "tuple" [TList rs] => let* ks := all_some class_of rs in Some (RTuple ks)
  | _ => let* k := class_of t in Some (RClass k)
  end.

(** The thunk calls among the instruction terms of a function
    outside the core subset, whose term is t: its direct calls,
    `call(Res, global(F), Args)`, as `lower_thunks/2` reads them. *)
Definition outside_thunk_calls (sy : symbols) (t : term) : list thunk_call :=
  match t with
  | TApp "func" [_; _; _; _; TList bs] =>
      flat_map
        (fun b =>
           match b with
           | TApp "block" [_; _; TList is; _] =>
               flat_map
                 (fun i =>
                    match i with
                    | TApp "call" [res; TApp "global" [f]; TList args] =>
                        match term_result_ret res,
                              all_some (fun a => match a with
                                                 | TApp "arg" [k; _] => dclass k
                                                 | _ => None
                                                 end) args with
                        | Some r, Some ks => thunk_call_of sy f r ks
                        | _, _ => []
                        end
                    | _ => []
                    end) is
           | _ => []
           end) bs
  | _ => []
  end.

(** The thunk calls of a module: those of every direct call in it. *)
Definition module_thunk_calls (sy : symbols) (md : module) : list thunk_call :=
  flat_map
    (fun it =>
       match it with
       | IFunc f =>
           flat_map (fun b =>
                       flat_map (fun i => match i with
                                          | Call r (Global g) args =>
                                              thunk_call_of sy g (result_ret r) (map arg_class args)
                                          | _ => []
                                          end) (b_insts b)) (fn_blocks f)
       | IOutside _ t => outside_thunk_calls sy t
       | _ => []
       end) md.

(** As `one_per_symbol/2`: of the sorted calls cs, the first of each
    symbol and signature. *)
Fixpoint one_per_symbol (cs : list (term * thunk_call)) : list thunk_call :=
  match cs with
  | [] => []
  | (_, c) :: cs' =>
      c :: match cs' with
           | (_, c') :: _ =>
               if name_eqb (tc_name c) (tc_name c')
                  && term_eqb (sigref_term (tc_sig c)) (sigref_term (tc_sig c'))
               then tl (one_per_symbol cs')
               else one_per_symbol cs'
           | [] => []
           end
  end.

(** As `thunk_cells/4`: the generic cells of a thunk for parameters
    of the classes ks, the value i from the fast word w the thunk
    saved; a pointer takes two words. *)
Fixpoint thunk_cells (ks : list class) (i w : Z) : list cell :=
  match ks with
  | [] => []
  | P :: ks' => Cell i L (CellSaved w) (Some (CellSaved (w + 1))) :: thunk_cells ks' (i + 1) (w + 2)
  | k :: ks' => Cell i k (CellSaved w) None :: thunk_cells ks' (i + 1) (w + 1)
  end.

(** As `lower_thunk/3`: the plan of the weak thunk for the call c.
    It is `weak` if the callee is declared weak, since its getter may
    be null; `local` if this module defines the callee with local
    linkage, so that the thunk never merges with another object's;
    else `strong`. *)
Definition lower_thunk (sy : symbols) (c : thunk_call) : option thunk :=
  let f := tc_name c in
  let local_data := match nm_find f (sy_data sy) with
                    | Some LLocal => true
                    | Some (LRo l) | Some (LTls l) => is_atom "local" l
                    | _ => false
                    end in
  let ref := if nm_mem f (sy_weak sy) then RefWeak
             else if match nm_find f (sy_funcs sy) with
                     | Some fe => is_atom "local" (fe_linkage fe)
                     | None => false
                     end then RefLocal
             else if local_data then RefLocal
             else RefStrong in
  let ks := tc_classes c in
  let* res := adapter_return (tc_ret c) in
  let* rks := ret_kinds (tc_ret c) in
  Some (mkThunk f ref (tc_sig c)
                (fast_params (map (fun ik => (snd ik, TInt (fst ik))) (indexed 0 ks)))
                (thunk_cells ks 0 0) (8 * Zlength ks) res (8 * Zlength rks)).

(** As `lower_thunks/2`: the plans of the weak thunks the module md
    needs, one for each symbol and signature of a direct call to a
    function it does not implement, in the standard order of
    `t(F, Sig, Ret, Ks)`. *)
Definition lower_thunks (sy : symbols) (md : module) : option (list thunk) :=
  let calls := map (fun c => (thunk_call_term c, c)) (module_thunk_calls sy md) in
  all_some (lower_thunk sy)
           (one_per_symbol (sort (fun a b => term_compare (fst a) (fst b)) calls)).
