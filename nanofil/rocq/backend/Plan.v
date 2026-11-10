(** The ABI plan of a function, as filc_abi.pl's `abi_function/10`
    states it before any register or frame offset is chosen: a frame
    of named slots, entry actions, blocks whose calls, getters and
    returns are lists of ABI actions, and the function's public
    object. It is what Fuse.v and Abi.v build and what instruction
    selection reads.

    The instructions inside it are Syntax.v's, the model's own: the
    plan adds only the forms the checked IR has no term for, which
    are a check fused with its access, a reused proof, and
    `abi(Actions)`. PlanTerm.v writes a plan as the term the Prolog
    compiler prints for it. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Validate.
Import ListNotations.
Local Open Scope Z_scope.

(** [f] of every element of xs, or nothing if any has none. *)
Fixpoint all_some {X Y : Type} (f : X -> option Y) (xs : list X) : option (list Y) :=
  match xs with
  | [] => Some []
  | x :: xs' =>
      match f x with
      | Some y => match all_some f xs' with Some ys => Some (y :: ys) | None => None end
      | None => None
      end
  end.

(** ## Fused instructions *)

(** Where a fused access is: at the pointer `P` its check proved, or
    at `local(X, Off)`, the named local x plus off, which
    `check_local` proves. *)
Inductive place : Type :=
| AtValue (p : value)
| AtLocal (x : name) (off : Z).

(** A raw access with its proof replaced by the [place] proven: the
    raw loads and stores of Syntax.v's [inst], which read a proof
    temporary there. *)
Inductive access : Type :=
| ALoad (d : name) (k : class) (t : load_type) (off : Z) (p : place) (* `let(tmp(D), K, raw_load(T, Off), [P])` *)
| AStore (w : width) (off : Z) (v : value) (p : place) (* `raw_store(W, Off, V, P)` *)
| ALoadPointer (d : name) (off : Z) (es : list effect) (p : place) (* `let(tmp(D), p, raw_load_pointer(Off, Es), [P])` *)
| AStorePointer (off : Z) (v : value) (p : place) (es : list effect) (* `raw_store_pointer(Off, V, P, Es)` *)
| ATouch (p : place). (* `touch(P)`: the check alone, with no access after it *)

(** An instruction after fusion (filc_amd64.pl's `fused_blocks/5`). *)
Inductive finst : Type :=
| FPlain (i : inst) (* an instruction of the checked IR, unchanged *)
| FFused (c : op) (a : access) (* `fused(Check, Access)`: a check and the access it proves, at one index *)
| FReused (a : access) (* `reused(Access)`: an access under an earlier check's proof, with no check *)
| FCall (r : call_result) (p : value) (args : list arg). (* `fused(check_function, call(Res, P, Args))` *)

(** The temporaries a place reads: its pointer, if a temporary. *)
Definition place_uses (p : place) : list name :=
  match p with
  | AtValue v => value_temps [v]
  | AtLocal _ _ => []
  end.

(** The temporaries an access reads. *)
Definition access_uses (a : access) : list name :=
  match a with
  | ALoad _ _ _ _ p | ALoadPointer _ _ _ p | ATouch p => place_uses p
  | AStore _ _ v p | AStorePointer _ v p _ => value_temps [v] ++ place_uses p
  end.

(** The temporary an access defines, with its class. *)
Definition access_defs (a : access) : list (name * class) :=
  match a with
  | ALoad d k _ _ _ => [(d, k)]
  | ALoadPointer d _ _ _ => [(d, P)]
  | AStore _ _ _ _ | AStorePointer _ _ _ _ | ATouch _ => []
  end.

(** As `cfg:inst_uses/2` of `live_inst/2`: the temporaries a fused
    instruction reads, as liveness and the frame layout see it: the
    bare access at its checked pointer, or the call of the checked
    pointer. The proof is not among them: it is a register value and
    has no slot. *)
Definition finst_uses (i : finst) : list name :=
  match i with
  | FPlain i' => inst_uses i'
  | FFused _ a | FReused a => access_uses a
  | FCall _ p args => value_temps (p :: map arg_value args)
  end.

(** As `cfg:inst_def/2` of `live_inst/2`: the temporaries a fused
    instruction defines, each with its class. *)
Definition finst_defs (i : finst) : list (name * class) :=
  match i with
  | FPlain i' => inst_temp_defs i'
  | FFused _ a | FReused a => access_defs a
  | FCall r _ _ => match r with CVoid => [] | CResult d k => [(d, k)] | CTuple rs => rs end
  end.

(** ## Frames *)

(** A pool of the frame's slots (frame_slots.pl): [PoolScalar] holds
    the `w`, `l`, `s` and `d` temporaries, [PoolPointer] the `p`
    ones, each slot an address and its lower, and [PoolWide] the `x`
    ones. *)
Inductive pool : Type := PoolScalar | PoolPointer | PoolWide.

(** The name of something a frame holds. *)
Inductive key : Type :=
| KTmp (n : name) (* `tmp(N)`: the payload of the temporary n *)
| KShadow (n : name) (* `shadow(N)`: the copy of the phi n that an edge's parallel moves read *)
| KStorage (p : pool) (i : Z) (* `storage(Pool, I)`: the slot i of a pool *)
| KThread (* `thread`: the saved thread pointer *)
| KAux (* `aux`: a scratch word *)
| KRetbuf (* `retbuf`: the caller's return buffer *)
| KLocal (x : name) (size : Z) (* `local(X, Size)`: the bytes of a named local *)
| KLower (k : key) (* `lower(K)`: the capability beside the address K, a root *)
| KStackAux (x : name). (* `stack_aux(X)`: the aux of a named local, a root *)

(** As `frame(Plain, Roots, Aliases)`: the payload slots, the roots
    the collector scans, in order, and the slot each temporary's
    payload or lower is kept in. *)
Record frame : Type := mkFrame {
  fr_plain : list key;
  fr_roots : list key;
  fr_aliases : list (key * key)
}.

(** ## Words, cells and results *)

(** How a function returns: `registers`, or `buffer(N)`, through a
    buffer of n words when more than two integer words come back. *)
Inductive protocol : Type := Registers | Buffer (n : Z).

(** Where a fast word comes from or goes. *)
Inductive source : Type :=
| SrcSlot (k : key) (* a parameter's slot, `tmp(N)` or `lower(tmp(N))` *)
| SrcAddr (v : value) (* `addr(V)`: the address of the pointer v *)
| SrcLower (v : value) (* `lower(V)`: its capability *)
| SrcVal (k : class) (v : value) (* `val(K, V)`: the value v at class k *)
| SrcData (i : Z) (* `data(I)`: the data word of the generic cell i *)
| SrcAux (i : Z) (* `aux(I)`: its aux word *)
| SrcSnapshot. (* `snapshot`: a variadic entry's promoted argument packet *)

(** As `wf(K, Source)`: one word of a fast call, at the class k (`l`
    for both words of a pointer). *)
Inductive word : Type := Wf (k : class) (s : source).

(** What a generic cell holds: a value, or `saved(W)`, the fast word
    w a thunk saved. *)
Inductive cell_source : Type := CellValue (v : value) | CellSaved (w : Z).

(** As `cell(I, K, Source, Lower)`: the eightbyte i of a generic
    packet, with the capability beside it if it is a pointer. *)
Inductive cell : Type :=
  Cell (i : Z) (k : class) (s : cell_source) (lower : option cell_source).

(** The channels a fast call's results come back in. *)
Inductive channels : Type :=
| ChSlots (ks : list key) (* `slots([...])`: integer words, to these slots *)
| ChFloat (k : class) (d : name) (* `float(K, tmp(D))`: one float *)
| ChTyped (ks : list (class * key)). (* `typed([K-Slot, ...])`: a tuple with a float in it *)

(** A direct call's signature in its symbol: its number, or
    `never(R-A)` for a call of more than 16 words, which has no fast
    signature. *)
Inductive sigref : Type := SigNumber (n : Z) | SigNever (r a : Z).

(** What a direct call invokes. *)
Inductive call_target : Type :=
| TImplementation (f : name) (sig : Z) (* `implementation(F, Sig)`: the private body of a function of this module *)
| TEntry (f : name) (sig : sigref). (* `entry(F, Sig)`: the weak thunk of this symbol and signature *)

(** The getter that gives a symbol's address. *)
Inductive getter : Type :=
| GetLocal (s : name) (* `local_getter(S)`: this module defines s *)
| GetWeak (s : name) (* `weak_getter(S)`: declared weak; may be null *)
| GetExternal (s : name). (* `external_getter(S)` *)

(** ## Actions *)

(** One step of an `abi(Actions)` instruction. Each list of them
    occupies the one index of the instruction it lowers. *)
Inductive action : Type :=
| AOrigin (* `origin(c)`: record the catching origin before a safepoint *)
| AReserveResult (r : protocol) (* `reserve_result(R)` *)
| AInvoke (t : call_target) (r : protocol) (ws : list word) (* `invoke(Target, R, Words)` *)
| AResult (r : protocol) (c : channels) (* `result(R, Channels)` *)
| AReleaseResult (r : protocol) (* `release_result(R)` *)
| ACopyFilter (d s : value) (n : Z) (res : call_result) (* `copy_filter(D, S, N, Res)`: a small memcpy's inline filter *)
| ACopyJoin (* `copy_join` *)
| ADispatch (p : value) (sig : Z) (r : protocol) (ws : list word) (c : channels)
            (size : Z) (cells : list cell) (need : Z) (results : list cell)
    (* `dispatch(P, Sig, R, Words, result(R, C), Size, Cells, receive_generic(Need, Results))`: an indirect call, fast if the callee has this signature, else generic *)
| AGetter (g : getter) (d : name) (* `getter(G, c, D)` *)
| ASnapshotCursor (off : Z) (d : name) (* `snapshot_cursor(tmp(hidden(va_snapshot)), Off, D)` *)
| AConsumeVa (k : class) (p : value) (size : Z) (d : name) (* `consume_va(K, P, Size, D)` *)
| AInitializeLocal (x : name). (* `initialize_local(X)` *)

(** An instruction of a plan: a fused instruction passed through, or
    `abi(Actions)`. *)
Inductive pinst : Type :=
| PInst (i : finst)
| PAbi (acts : list action).

(** The jump that ends a plan's block: a jump of the IR, or
    `abi_return(Actions)`, the actions of a return. *)
Inductive pjump : Type :=
| PJump (j : jump) (* `goto`, `branch` or `unreachable`, unchanged *)
| PReturnValue (r : ret_type) (v : value) (p : protocol) (* `[return_value(Ret, V), pop_frame, success(P)]` *)
| PReturnBuffer (ws : list word) (* `[return_buffer(Words), success_buffer, pop_frame, native_return]` *)
| PReturnTyped (ks : list class) (vs : list value) (* `[return_typed(Ks, Vs), pop_frame, success(registers)]` *)
| PReturnRegisters (vs : list value) (* `[return_registers(Vs), pop_frame, success(registers)]` *)
| PReturnVoid (p : protocol). (* `[pop_frame, success(P)]` *)

(** A block of a plan. *)
Record pblock : Type := mkPBlock {
  pb_label : name;
  pb_phis : list phi;
  pb_insts : list pinst;
  pb_jump : pjump
}.

(** ## Public objects and thunks *)

(** The channel a generic adapter takes the fast result from. *)
Inductive adapter_channel : Type :=
| AdVoid | AdFloat (k : class) | AdTyped (ks : list class) | AdWords.

(** As `adapter_result(R, Channel, Size, packet(Copies, Zeros))`: how
    an adapter turns a fast result into a generic packet of size
    bytes: the words it copies and those it zeroes. *)
Record adapter_result : Type := mkAdapterResult {
  ar_return : protocol;
  ar_channel : adapter_channel;
  ar_size : Z;
  ar_copies : list source;
  ar_zeros : list source
}.

(** A function's public object. *)
Inductive object : Type :=
| FastAndGeneric (sig need : Z) (ws : list word) (r : adapter_result)
    (* `fast_and_generic(Sig, adapt(Need, Words, Result))` *)
| GenericOnly (need : Z) (ws : list word) (r : adapter_result).
    (* `generic_only(promote_incoming(Need, Words, Result))`: a variadic function *)

(** How a thunk refers to its callee. *)
Inductive thunk_ref : Type := RefWeak | RefLocal | RefStrong.

(** As `thunk(F, Ref, Sig, Words, Cells, ArgsSize, Result, Need)`:
    the weak thunk of a symbol and signature that the module calls
    directly and does not define. *)
Record thunk : Type := mkThunk {
  th_name : name;
  th_ref : thunk_ref;
  th_sig : sigref;
  th_words : list word;
  th_cells : list cell;
  th_args_size : Z;
  th_result : adapter_result;
  th_need : Z
}.

(** ## The plan *)

(** As `abi_function(Name, Linkage, Ret, Sig, Frame, Entry, Blocks,
    Exit, Object, Origins)`. The entry actions, the exception exit
    and the origins have one shape each, so the plan keeps what they
    vary in: the return protocol, the words received, the payload
    slots a setjmp would snapshot, and the numbers of roots and
    named locals. *)
Record plan : Type := mkPlan {
  pl_name : name;
  pl_linkage : term;
  pl_ret : ret_type;
  pl_sig : Z;
  pl_frame : frame;
  pl_return : protocol;
  pl_incoming : list word;
  pl_payload : list key;
  pl_blocks : list pblock;
  pl_object : object;
  pl_nlocals : Z
}.
