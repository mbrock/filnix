(** # Function objects

    Every function has a getter, a generic entry and a function
    object, so that its address can be taken; an exported one also
    has the public alias of its implementation and a global getter.
    As filc_amd64.pl's `function_object//5` and `variadic_object//4`.
    The generic entry adapts a packet of cells in the thread to the
    fast convention and the fast result back to a packet. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Text Asm Plan PlanTerm Layout.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Adapter operands *)

(** Where an adapter reads a word of the fast call from: memory, a
    register, or the aux word at an offset of a promoted packet,
    which has no aux if `%r13` is null. *)
Inductive adapter_operand : Type :=
| AoMem (off : Z) (base : string)
| AoReg (r : string)
| AoSnapshotLower (off : Z).

(** As `channel_offset/2`: the thread offset of a generic cell's
    data or aux word. *)
Definition channel_offset (s : source) : option Z :=
  match s with
  | SrcData i => Some (thread_cc_inline_buffer + eight * i)
  | SrcAux i => Some (thread_cc_inline_aux_buffer + eight * i)
  | _ => None
  end.

(** As `adapter_operand/3`: for the area `thread` the cells are in
    the thread at `%rbx`; for `snapshot` they are in the promoted
    packet at `%r12`. *)
Definition adapter_operand_of (snapshot : bool) (s : source) : option adapter_operand :=
  if snapshot
  then match s with
       | SrcData i => Some (AoMem (eight * i) "r12")
       | SrcAux i => Some (AoSnapshotLower (eight * i))
       | SrcSnapshot => Some (AoReg "r12")
       | _ => None
       end
  else option_map (fun off => AoMem off "rbx") (channel_offset s).

(** As `snapshot_load//2`: the operand into `%rax`. *)
Definition snapshot_load (o : adapter_operand) (g : string) : list line :=
  match o with
  | AoReg r => [ins "mov" "q" [reg r; reg "rax"]]
  | AoMem off b => [ins "mov" "q" [mem off b; reg "rax"]]
  | AoSnapshotLower off =>
      let noaux := (g ++ ".lower." ++ decimal off)%string in
      [ins "xor" "l" [reg "eax"; reg "eax"];
       ins "test" "q" [reg "r13"; reg "r13"];
       ins0 "jz" [sym noaux];
       ins "mov" "q" [mem off "r13"; reg "rax"];
       label noaux]
  end.

Definition is_single (k : class) : bool := match k with Single => true | _ => false end.

(** As `adapter_load//3`: a single is the low half of its word. *)
Definition adapter_load (k : class) (o : adapter_operand) (g : string) : list line :=
  snapshot_load o g ++ (if is_single k then [ins "mov" "l" [reg "eax"; reg "eax"]] else []).

(** A word of the adapter's fast call and its operand. *)
Definition adapter_word (snapshot : bool) (w : word) : class * option adapter_operand :=
  match w with Wf k s => (k, adapter_operand_of snapshot s) end.

(** As `adapter_stack//3`: the words that travel on the stack,
    through `%rax`, which is the only scratch register. *)
Fixpoint adapter_stack (ts : list (class * option adapter_operand)) (ls : list location)
                       (g : string) : list line :=
  match ts, ls with
  | (k, o) :: ts', l :: ls' =>
      match l, o with
      | LocStack i, Some o' =>
          adapter_load k o' g ++ [ins "mov" "q" [reg "rax"; mem (eight * i) "rsp"]]
      | LocStack _, None => todo "adapter source"
      | _, _ => []
      end
      ++ adapter_stack ts' ls' g
  | _, _ => []
  end.

(** As `adapter_registers//3`: an integer register takes a word in
    memory directly. *)
Fixpoint adapter_registers (ts : list (class * option adapter_operand)) (ls : list location)
                           (g : string) : list line :=
  match ts, ls with
  | (k, o) :: ts', l :: ls' =>
      match l, o with
      | LocStack _, _ => []
      | _, None => todo "adapter source"
      | LocReg r, Some (AoMem off b) =>
          if is_single k
          then adapter_load k (AoMem off b) g ++ [ins "mov" "q" [reg "rax"; reg (reg64 r)]]
          else [ins "mov" "q" [mem off b; reg (reg64 r)]]
      | LocReg r, Some o' => adapter_load k o' g ++ [ins "mov" "q" [reg "rax"; reg (reg64 r)]]
      | LocXmm x, Some o' => adapter_load k o' g ++ to_xmm k "a" x
      end
      ++ adapter_registers ts' ls' g
  | _, _ => []
  end.

(** ## The generic result *)

(** As `generic_zeroings//1`. *)
Definition generic_zeroings (offs : list Z) : list line :=
  map (fun off => ins "mov" "q" [imm 0; mem off "rbx"]) offs.

(** As `generic_reg_stores//2`: each result register at its thread
    offset. *)
Fixpoint generic_reg_stores (offs : list Z) (rs : list string) : list line :=
  match offs, rs with
  | [], _ => []
  | off :: offs', r :: rs' =>
      ins "mov" "q" [reg r; mem off "rbx"] :: generic_reg_stores offs' rs'
  | _ :: _, [] => todo "result registers"
  end.

(** As `generic_buffer_copies//2`: each word of the return buffer,
    from `off(%rsp)` on, to its thread offset. *)
Fixpoint generic_buffer_copies (dests : list Z) (off : Z) : list line :=
  match dests with
  | [] => []
  | d :: dests' =>
      [ins "mov" "q" [mem off "rsp"; reg "rax"]; ins "mov" "q" [reg "rax"; mem d "rbx"]]
      ++ generic_buffer_copies dests' (off + eight)
  end.

(** As `typed_ret_kind/3`: a pointer of a returned tuple is two
    integer words. *)
Definition typed_ret_kinds (ks : list class) : list class :=
  flat_map (fun k => match k with P => [L; L] | _ => [k] end) ks.

(** As `generic_typed_gprs//2` and `generic_typed_xmms//2`, over the
    registers `result_registers/2` gives the words: integer words in
    `%rdx` then `%rcx`, float words in `%xmm0` then `%xmm1`. *)
Fixpoint generic_typed_gprs (ks : list class) (gs : list string) (offs : list Z)
  : list line :=
  match ks, offs with
  | k :: ks', off :: offs' =>
      if float_class k then generic_typed_gprs ks' gs offs'
      else match gs with
           | g :: gs' => ins "mov" "q" [reg g; mem off "rbx"] :: generic_typed_gprs ks' gs' offs'
           | [] => todo "result registers"
           end
  | _, _ => []
  end.

Fixpoint generic_typed_xmms (ks : list class) (xs : list string) (offs : list Z)
  : list line :=
  match ks, offs with
  | k :: ks', off :: offs' =>
      if float_class k
      then match xs with
           | x :: xs' =>
               from_xmm k x "a" ++ [ins "mov" "q" [reg "rax"; mem off "rbx"]]
               ++ generic_typed_xmms ks' xs' offs'
           | [] => todo "result registers"
           end
      else generic_typed_xmms ks' xs offs'
  | _, _ => []
  end.

(** As `generic_reg_results//2`: the result words from their
    registers to their thread offsets; a void result is one zero
    word. *)
Definition generic_reg_results (c : adapter_channel) (dests zeros : list Z) : list line :=
  match c with
  | AdVoid => match dests with [] => generic_zeroings zeros | _ => todo "void result" end
  | AdFloat k =>
      match dests, zeros with
      | [off], [lower] =>
          from_xmm k "xmm0" "d"
          ++ [ins "mov" "q" [reg "rdx"; mem off "rbx"]; ins "mov" "q" [imm 0; mem lower "rbx"]]
      | _, _ => todo "float result"
      end
  | AdTyped ks =>
      let kts := typed_ret_kinds ks in
      generic_typed_gprs kts ["rdx"; "rcx"] dests
      ++ generic_typed_xmms kts ["xmm0"; "xmm1"] dests
      ++ [ins "xor" "l" [reg "eax"; reg "eax"]]
      ++ generic_zeroings zeros
  | AdWords => generic_reg_stores dests ["rdx"; "rcx"] ++ generic_zeroings zeros
  end.

Definition stack_release (bytes : Z) : list line :=
  if bytes >? 0 then [ins "add" "q" [imm bytes; reg "rsp"]] else [].
Definition reserve_stack (bytes : Z) : list line :=
  if bytes >? 0 then [ins "sub" "q" [imm bytes; reg "rsp"]] else [].
Definition ret_buffer_reservation (r : protocol) : list line :=
  match r with
  | Registers => []
  | Buffer n => [ins "sub" "q" [imm (buffer_bytes n); reg "rsp"]]
  end.
Definition ret_buffer_release (r : protocol) : list line :=
  match r with
  | Registers => []
  | Buffer n => [ins "add" "q" [imm (buffer_bytes n); reg "rsp"]]
  end.

(** The thread offsets of sources; `None` if one is not a cell. *)
Fixpoint channel_offsets (ss : list source) : option (list Z) :=
  match ss with
  | [] => Some []
  | s :: ss' =>
      match channel_offset s, channel_offsets ss' with
      | Some o, Some os => Some (o :: os)
      | _, _ => None
      end
  end.

(** As `generic_entry_call//6`: the call of the fast entry of the
    function object in `%rsi`, then the result into the packet and
    its size in `%edx`. An exception skips the result. *)
Definition generic_entry_call (res : adapter_result) (pop : Z) (done : string) : list line :=
  match channel_offsets (ar_copies res), channel_offsets (ar_zeros res) with
  | Some dests, Some zeros =>
      match ar_return res with
      | Registers =>
          [ins "call" "q" [ind (mem function_object_fast_entry "rsi")]]
          ++ stack_release pop
          ++ [ins "test" "b" [imm 1; reg "al"]; ins0 "jnz" [sym done]]
          ++ generic_reg_results (ar_channel res) dests zeros
          ++ [ins "mov" "l" [imm (ar_size res); reg "edx"]; label done]
      | Buffer n =>
          [ins "mov" "q" [reg "rsi"; reg "rdx"];
           ins "mov" "q" [reg "rbx"; reg "rsi"];
           ins "lea" "q" [mem pop "rsp"; reg "rdi"];
           ins "call" "q" [ind (mem function_object_fast_entry "rdx")]]
          ++ stack_release pop
          ++ [ins "mov" "b" [mem 0 "rsp"; reg "al"];
              ins "test" "b" [reg "al"; reg "al"];
              ins0 "jnz" [sym done]]
          ++ generic_buffer_copies dests eight
          ++ generic_zeroings zeros
          ++ [ins "mov" "l" [imm (ar_size res); reg "edx"];
              ins "xor" "l" [reg "eax"; reg "eax"];
              label done]
          ++ ret_buffer_release (Buffer n)
      end
  | _, _ => todo "adapter packet"
  end.

(** The failure of an entry given fewer than need bytes of
    arguments. *)
Definition short_args (short : string) (need : Z) : list line :=
  [label short;
   ins "mov" "q" [reg "rdx"; reg "rdi"];
   ins "mov" "l" [imm need; reg "esi"];
   ins "xor" "l" [reg "edx"; reg "edx"];
   ins0 "call" [plt "filc_cc_args_check_failure"];
   ins0 "ud2" []].

(** As `generic_entry//2`: `{i1, i64 ret_size} (thread, callee_lower,
    args_size)`. *)
Definition generic_entry (generic : string) (need : Z) (ws : list word)
                         (res : adapter_result) : list line :=
  let ts := map (adapter_word false) ws in
  let '(ls, ns, _) := typed_locations ws (ar_return res) in
  let pop := stack_bytes ns in
  [Dir (DSection SText); label generic;
   ins "push" "q" [reg "rbx"];
   ins "cmp" "q" [imm need; reg "rdx"];
   ins0 "jb" [sym (generic ++ ".short")];
   ins "mov" "q" [reg "rdi"; reg "rbx"]]
  ++ ret_buffer_reservation (ar_return res)
  ++ reserve_stack pop
  ++ adapter_stack ts ls generic
  ++ adapter_registers ts ls generic
  ++ generic_entry_call res pop (generic ++ ".done")
  ++ [ins "pop" "q" [reg "rbx"]; ins0 "ret" []]
  ++ short_args (generic ++ ".short") need.

(** As `variadic_adapter//3`: the generic entry of a variadic
    function, which promotes its packet to the heap and passes the
    snapshot to the private fast body, whose object is body. The
    promotion is the only exiting call before the body roots the
    snapshot. *)
Definition variadic_adapter (generic body : string) (need : Z) (ws : list word)
                            (res : adapter_result) : list line :=
  let ts := map (adapter_word true) ws in
  let '(ls, ns, _) := typed_locations ws (ar_return res) in
  let pop := stack_bytes ns in
  let aux := (generic ++ ".aux")%string in
  [Dir (DSection SText); Dir (DType (LSym generic) (LSym "function")); label generic;
   ins "push" "q" [reg "rbx"]; ins "push" "q" [reg "r12"]; ins "push" "q" [reg "r13"];
   ins "cmp" "q" [imm need; reg "rdx"];
   ins0 "jb" [sym (generic ++ ".short")];
   ins "mov" "q" [reg "rdi"; reg "rbx"];
   ins "mov" "q" [reg "rdx"; reg "rsi"];
   ins0 "call" [plt "filc_promote_args_to_heap"];
   ins "mov" "q" [reg "rax"; reg "r12"];
   ins "xor" "l" [reg "r13d"; reg "r13d"];
   ins "test" "q" [reg "rdx"; reg "rdx"];
   ins0 "jz" [sym aux];
   ins "mov" "q" [mem (-8) "rdx"; reg "r13"];
   ins "movabs" "q" [imm 281474976710655; reg "rax"];
   ins "and" "q" [reg "rax"; reg "r13"];
   label aux]
  ++ ret_buffer_reservation (ar_return res)
  ++ reserve_stack pop
  ++ adapter_stack ts ls generic
  ++ adapter_registers ts ls generic
  ++ [ins "mov" "q" [reg "rbx"; reg "rdi"]; ins "lea" "q" [rip body; reg "rsi"]]
  ++ generic_entry_call res pop (generic ++ ".done")
  ++ [ins "pop" "q" [reg "r13"]; ins "pop" "q" [reg "r12"]; ins "pop" "q" [reg "rbx"];
      ins0 "ret" []]
  ++ short_args (generic ++ ".short") need.

(** ## The object *)

(** `S+16`, the address of the payload of the object s. *)
Definition payload_of (s : string) : expr := EAdd (ELit (LSym s)) (ELit (LInt sixteen)).

(** As `aux_bits/2` of `[global, readonly, function]`. *)
Definition function_object_flags : Z := 36873221949095936.

(** As `object_getter//2`: the getter of the function object fo
    gives its flight pointer, whose lower is its address, in
    `%rax` and `%rdx`. *)
Definition object_getter (getter fo : string) : list line :=
  [Dir (DType (LSym getter) (LSym "function")); label getter;
   ins "lea" "q" [ORip (payload_of fo); reg "rax"];
   ins "mov" "q" [reg "rax"; reg "rdx"];
   ins0 "ret" []].

(** As `function_object_data//4`: the object with its entries (a
    symbol, or 0 for none) and its signature. Its header has upper =
    lower, so it cannot be read or written, and an aux word that
    points at itself. *)
Definition function_object_data (fo : string) (fast : option string) (generic : string)
                                (sig : Z) : list line :=
  [Dir (DType (LSym fo) (LSym "object")); label fo;
   Dir (DQuad (payload_of fo));
   Dir (DQuad (EAdd (payload_of fo) (ELit (LInt function_object_flags))));
   match fast with Some f => quad_sym f | None => quad_int 0 end;
   quad_sym generic;
   quad_int sig;
   Dir (DSizeOf (LSym fo) (LInt 40))].

(** A function's linkage. *)
Inductive linkage : Type := LkExport | LkLocal | LkWeak | LkOther.

Definition linkage_of (t : term) : linkage :=
  match t with
  | TAtom a =>
      if String.eqb a "export" then LkExport
      else if String.eqb a "local" then LkLocal
      else if String.eqb a "weak" then LkWeak
      else LkOther
  | _ => LkOther
  end.

(** As `linkage_alias//4`: an exported function has the public
    alias fi of its implementation and a global getter; a weak one
    has a weak getter and no alias, since callers elsewhere go
    through their thunks to whichever definition the linker keeps. *)
Definition linkage_alias (l : linkage) (fi impl getter : string) : list line :=
  match l with
  | LkExport =>
      [Dir (DGlobl (LSym fi)); Dir (DType (LSym fi) (LSym "function"));
       Dir (DSet (LSym fi) (ELit (LSym impl))); Dir (DGlobl (LSym getter))]
  | LkLocal => []
  | LkWeak => [Dir (DWeak (LSym getter))]
  | LkOther => todo "linkage"
  end.

Definition p2align4 : line := Dir (DP2align (LInt 4)).

(** As `function_object//5`. The object of a function that is not
    local names its fast entry by a local alias, since a global
    implementation symbol is preemptible and the dynamic linker
    would bind the word to the first definition of the name. *)
Definition function_object (name : string) (l : linkage) (sig need : Z) (ws : list word)
                           (res : adapter_result) (impl : string) : list line :=
  let fi := entry_symbol (SigNumber sig) name in
  let fo := function_object_symbol name in
  let getter := getter_symbol name in
  let generic := (".L" ++ name ++ "..generic")%string in
  let local := (".L" ++ impl ++ ".local")%string in
  linkage_alias l fi impl getter
  ++ object_getter getter fo
  ++ generic_entry generic need ws res
  ++ match l with
     | LkLocal => []
     | _ => [Dir (DType (LSym local) (LSym "function")); Dir (DSet (LSym local) (ELit (LSym impl)))]
     end
  ++ [Dir (DSection SDataRelRo); p2align4]
  ++ function_object_data fo (Some match l with LkLocal => impl | _ => local end) generic sig.

(** As `variadic_object//4`: a variadic function has a generic
    entry only, which is public, and a private fast body. *)
Definition variadic_object (name : string) (l : linkage) (need : Z) (ws : list word)
                           (res : adapter_result) (impl : string) : list line :=
  let fo := function_object_symbol name in
  let getter := getter_symbol name in
  let generic := impl_symbol 0 name in
  let fi := entry_symbol (SigNumber 0) name in
  let body := (generic ++ ".body")%string in
  linkage_alias l fi generic getter
  ++ object_getter getter fo
  ++ variadic_adapter generic body need ws res
  ++ [Dir (DSection SDataRelRo); p2align4; label body; quad_sym impl]
  ++ function_object_data fo None generic 0.

(** As `body_function_object//4`. *)
Definition function_object_lines (cx : ctx) (p : plan) (impl : string) : list line :=
  let l := linkage_of (pl_linkage p) in
  match pl_object p with
  | FastAndGeneric sig need ws res => function_object (cx_name cx) l sig need ws res impl
  | GenericOnly need ws res => variadic_object (cx_name cx) l need ws res impl
  end.
