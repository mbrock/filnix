(** A [plan] as the term the Prolog compiler writes for it
    (filc_abi.pl's `abi_function/10`), and a module's thunks as its
    `thunks(List)`. `nanofil abi-terms` prints both, so the plans
    Abi.v builds are compared with the Prolog compiler's as terms,
    on every function of the corpus. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Validate.
From Backend Require Import IrTerm Plan FrameSlots Abi.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Keys, words and cells *)

(** The atom of a term with no arguments. *)
Definition atom (a : string) : term := TAtom a.

(** As `A-B`, a pair. *)
Definition pair_term (a b : term) : term := TApp "-" [a; b].

(** The name of a pool: `scalar`, `pointer` or `wide`. *)
Definition pool_term (p : pool) : term :=
  atom (match p with PoolScalar => "scalar" | PoolPointer => "pointer" | PoolWide => "wide" end).

(** A key of a frame. *)
Fixpoint key_term (k : key) : term :=
  match k with
  | KTmp n => TApp "tmp" [n]
  | KShadow n => TApp "shadow" [n]
  | KStorage p i => TApp "storage" [pool_term p; TInt i]
  | KThread => atom "thread"
  | KAux => atom "aux"
  | KRetbuf => atom "retbuf"
  | KLocal x size => TApp "local" [x; TInt size]
  | KLower k' => TApp "lower" [key_term k']
  | KStackAux x => TApp "stack_aux" [x]
  end.

(** A return protocol: `registers` or `buffer(N)`. *)
Definition protocol_term (p : protocol) : term :=
  match p with
  | Registers => atom "registers"
  | Buffer n => TApp "buffer" [TInt n]
  end.

(** The source of a fast word. *)
Definition source_term (s : source) : term :=
  match s with
  | SrcSlot k => key_term k
  | SrcAddr v => TApp "addr" [enc_value v]
  | SrcLower v => TApp "lower" [enc_value v]
  | SrcVal k v => TApp "val" [eclass k; enc_value v]
  | SrcData i => TApp "data" [TInt i]
  | SrcAux i => TApp "aux" [TInt i]
  | SrcSnapshot => atom "snapshot"
  end.

(** As `wf(K, Source)`. *)
Definition word_term (w : word) : term :=
  match w with Wf k s => TApp "wf" [eclass k; source_term s] end.

(** As `cell(I, K, Source, Lower)`: the lower of a value is
    `lower(V)`, that of a saved word the `saved(W)` beside it, and
    `none` if the cell holds no pointer. *)
Definition cell_term (c : cell) : term :=
  match c with
  | Cell i k s lower =>
      TApp "cell" [TInt i; eclass k;
                   match s with
                   | CellValue v => enc_value v
                   | CellSaved w => TApp "saved" [TInt w]
                   end;
                   match lower with
                   | None => atom "none"
                   | Some (CellValue v) => TApp "lower" [enc_value v]
                   | Some (CellSaved w) => TApp "saved" [TInt w]
                   end]
  end.

(** The channels of a fast result. *)
Definition channels_term (c : channels) : term :=
  match c with
  | ChSlots ks => TApp "slots" [TList (map key_term ks)]
  | ChFloat k d => TApp "float" [eclass k; TApp "tmp" [d]]
  | ChTyped ks => TApp "typed" [TList (map (fun s => pair_term (eclass (fst s)) (key_term (snd s))) ks)]
  end.

(** As `result(R, Channels)`. *)
Definition result_term (r : protocol) (c : channels) : term :=
  TApp "result" [protocol_term r; channels_term c].

(** What a direct call invokes. *)
Definition target_term (t : call_target) : term :=
  match t with
  | TImplementation f sig => TApp "implementation" [f; TInt sig]
  | TEntry f sig => TApp "entry" [f; sigref_term sig]
  end.

(** A getter. *)
Definition getter_term (g : getter) : term :=
  match g with
  | GetLocal s => TApp "local_getter" [s]
  | GetWeak s => TApp "weak_getter" [s]
  | GetExternal s => TApp "external_getter" [s]
  end.

(** ## Actions and instructions *)

(** An ABI action. *)
Definition action_term (a : action) : term :=
  match a with
  | AOrigin => TApp "origin" [atom "c"]
  | AReserveResult r => TApp "reserve_result" [protocol_term r]
  | AInvoke t r ws => TApp "invoke" [target_term t; protocol_term r; TList (map word_term ws)]
  | AResult r c => result_term r c
  | AReleaseResult r => TApp "release_result" [protocol_term r]
  | ACopyFilter d s n res =>
      TApp "copy_filter" [enc_value d; enc_value s; TInt n; enc_call_result res]
  | ACopyJoin => atom "copy_join"
  | ADispatch p sig r ws c size cells need results =>
      TApp "dispatch" [enc_value p; TInt sig; protocol_term r; TList (map word_term ws);
                       result_term r c; TInt size; TList (map cell_term cells);
                       TApp "receive_generic" [TInt need; TList (map cell_term results)]]
  | AGetter g d => TApp "getter" [getter_term g; atom "c"; d]
  | ASnapshotCursor off d =>
      TApp "snapshot_cursor" [TApp "tmp" [va_snapshot]; TInt off; d]
  | AConsumeVa k p size d => TApp "consume_va" [eclass k; enc_value p; TInt size; d]
  | AInitializeLocal x => TApp "initialize_local" [x]
  end.

(** The place of a fused access: the checked pointer, or
    `local(X, Off)`. *)
Definition place_term (p : place) : term :=
  match p with
  | AtValue v => enc_value v
  | AtLocal x off => TApp "local" [x; TInt off]
  end.

(** A fused access: the raw load or store, its proof replaced by
    its place. *)
Definition access_term (a : access) : term :=
  match a with
  | ALoad d k t off p =>
      TApp "let" [TApp "tmp" [d]; eclass k; enc_op (RawLoad t off); TList [place_term p]]
  | AStore w off v p => TApp "raw_store" [enc_width w; TInt off; enc_value v; place_term p]
  | ALoadPointer d off es p =>
      TApp "let" [TApp "tmp" [d]; eclass P; enc_op (RawLoadPointer off es); TList [place_term p]]
  | AStorePointer off v p es =>
      TApp "raw_store_pointer" [TInt off; enc_value v; place_term p; enc_effects es]
  end.

(** An instruction after fusion. *)
Definition finst_term (i : finst) : term :=
  match i with
  | FPlain i' => enc_inst i'
  | FFused c a => TApp "fused" [enc_op c; access_term a]
  | FReused a => TApp "reused" [access_term a]
  | FCall r p args =>
      TApp "fused" [atom "check_function";
                    TApp "call" [enc_call_result r; enc_value p; TList (map enc_arg args)]]
  end.

(** An instruction of a plan. *)
Definition pinst_term (i : pinst) : term :=
  match i with
  | PInst i' => finst_term i'
  | PAbi acts => TApp "abi" [TList (map action_term acts)]
  end.

(** The jump of a plan's block: a jump of the IR, or
    `abi_return(Actions)`. *)
Definition pjump_term (j : pjump) : term :=
  let returns := fun acts => TApp "abi_return" [TList acts] in
  let success := fun p => TApp "success" [protocol_term p] in
  match j with
  | PJump j' => enc_jump j'
  | PReturnValue r v p =>
      returns [TApp "return_value" [eret r; enc_value v]; atom "pop_frame"; success p]
  | PReturnBuffer ws =>
      returns [TApp "return_buffer" [TList (map word_term ws)]; atom "success_buffer";
               atom "pop_frame"; atom "native_return"]
  | PReturnTyped ks vs =>
      returns [TApp "return_typed" [TList (map eclass ks); TList (map enc_value vs)];
               atom "pop_frame"; success Registers]
  | PReturnRegisters vs =>
      returns [TApp "return_registers" [TList (map enc_value vs)]; atom "pop_frame";
               success Registers]
  | PReturnVoid p => returns [atom "pop_frame"; success p]
  end.

(** As `block(L, Phis, Insts, Jump)`. *)
Definition pblock_term (b : pblock) : term :=
  TApp "block" [pb_label b; TList (map enc_phi (pb_phis b)); TList (map pinst_term (pb_insts b));
                pjump_term (pb_jump b)].

(** ## Public objects and thunks *)

(** As `adapter_result(R, Channel, Size, packet(Copies, Zeros))`. *)
Definition adapter_result_term (r : adapter_result) : term :=
  TApp "adapter_result"
       [protocol_term (ar_return r);
        match ar_channel r with
        | AdVoid => atom "void"
        | AdFloat k => TApp "float" [eclass k]
        | AdTyped ks => TApp "typed" [TList (map eclass ks)]
        | AdWords => atom "words"
        end;
        TInt (ar_size r);
        TApp "packet" [TList (map source_term (ar_copies r)); TList (map source_term (ar_zeros r))]].

(** A public object. *)
Definition object_term (o : object) : term :=
  match o with
  | FastAndGeneric sig need ws r =>
      TApp "fast_and_generic"
           [TInt sig; TApp "adapt" [TInt need; TList (map word_term ws); adapter_result_term r]]
  | GenericOnly need ws r =>
      TApp "generic_only"
           [TApp "promote_incoming" [TInt need; TList (map word_term ws); adapter_result_term r]]
  end.

(** As `thunk(F, Ref, Sig, Words, Cells, ArgsSize, Result, Need)`. *)
Definition thunk_term (t : thunk) : term :=
  TApp "thunk" [th_name t;
                atom (match th_ref t with
                      | RefWeak => "weak" | RefLocal => "local" | RefStrong => "strong"
                      end);
                sigref_term (th_sig t); TList (map word_term (th_words t));
                TList (map cell_term (th_cells t)); TInt (th_args_size t);
                adapter_result_term (th_result t); TInt (th_need t)].

(** As `thunks(List)`, what `nanofil abi-terms` prints last. *)
Definition thunks_term (ts : list thunk) : term := TApp "thunks" [TList (map thunk_term ts)].

(** ## The plan *)

(** As `abi_function(Name, Linkage, Ret, Sig, Frame, Entry, Blocks,
    Exit, Object, Origins)`. The entry receives the fast words and
    has no setjmp sites to snapshot; the exit is the exception's; the
    two origins, catching and not, count the roots and the named
    locals. *)
Definition plan_term (p : plan) : term :=
  let ret := protocol_term (pl_return p) in
  let fr := pl_frame p in
  let nroots := TInt (Zlength (fr_roots fr)) in
  let origin := fun which catch =>
                  TApp "origin" [atom which; atom catch; nroots; TInt 0; TInt (pl_nlocals p)] in
  TApp "abi_function"
       [pl_name p; pl_linkage p; eret (pl_ret p); TInt (pl_sig p);
        TApp "frame" [TList (map key_term (fr_plain fr)); TList (map key_term (fr_roots fr));
                      TList (map (fun a => pair_term (key_term (fst a)) (key_term (snd a)))
                                 (fr_aliases fr))];
        TList [TApp "native_frame" [ret]; atom "stack_check"; atom "save_thread";
               TApp "save_return" [ret]; TApp "zero_roots" [nroots];
               TApp "push_frame" [atom "c"];
               TApp "receive" [ret; TList (map word_term (pl_incoming p))];
               TApp "snapshots" [TList []; TList (map key_term (pl_payload p))]];
        TList (map pblock_term (pl_blocks p));
        TList [atom "pop_frame"; TApp "exception" [ret]];
        object_term (pl_object p);
        TList [origin "c" "catches"; origin "n" "no_catch"]].
