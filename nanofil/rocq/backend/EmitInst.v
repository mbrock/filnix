(** # Instructions

    The code of one instruction of a plan, as filc_amd64.pl's
    `inst//4` and `abi_action//4` give it in the reference emission:
    every temporary in its stack slot, the split bounds check, no
    inline copies. A form that is not ported yet is a `todo` line
    ([Layout]). *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Text Asm Plan Fuse PlanTerm FrameSlots Layout EmitOps.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Heap checks *)

Definition rights_write (r : rights) : bool := match r with Write => true | Read => false end.

(** As `aux_pointer_mask/1`: the low 48 bits of an aux word are the
    aux pointer; the high 16 are the object's flags. *)
Definition aux_pointer_mask : Z := 281474976710655.
(** As `aux_bits/2` of `special_type` and of `function`. *)
Definition special_type_mask : Z := 540431955284459520.
Definition function_bits : Z := 36028797018963968.

(** As `write_check//2`: a write needs an object that is neither
    read-only nor free. *)
Definition write_check (write : bool) (fail : string) : list line :=
  if write then [ins "test" "b" [imm 6; mem (-2) "rcx"]; ins0 "jnz" [sym fail]] else [].

(** As `align_check//2`. *)
Definition align_check (align : Z) (fail : string) : list line :=
  if align =? 1 then []
  else if (align =? 2) || (align =? 4) || (align =? 8)
  then [ins "test" "b" [imm (align - 1); reg "al"]; ins0 "jnz" [sym fail]]
  else todo "alignment".

(** As `access_check//2` with the split bounds: with the pointer in
    `%rax` and its lower in `%rcx`, a jump to the kind's failure
    block unless the lower is not null, lower <= pointer and
    pointer + size <= upper, and the flags and alignment permit. *)
Definition access_check (cx : ctx) (k : check_kind) : list line :=
  let fail := check_fail_label cx k in
  [ins "test" "q" [reg "rcx"; reg "rcx"]; ins0 "jz" [sym fail];
   ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "jb" [sym fail];
   ins "mov" "q" [mem (-16) "rcx"; reg "rdx"];
   ins "sub" "q" [imm (ck_size k); reg "rdx"]; ins0 "jb" [sym fail];
   ins "cmp" "q" [reg "rdx"; reg "rax"]; ins0 "ja" [sym fail]]
  ++ write_check (ck_write k) fail
  ++ align_check (ck_align k) fail.

(** ## Raw accesses

    After its check, an access has its address in `%rax` and the
    lower of the pointer in `%rcx`. *)

(** As `raw_load//6`: a scalar load of the type t at the class k into
    the temporary d. *)
Definition raw_load (cx : ctx) (t : load_type) (k : class) (d : name) : list line :=
  match t with
  | LdX => ins "fld" "t" [mem 0 "rax"] :: x87_pop cx d
  | _ => load_insn t k ++ slot_store cx "rax" (KTmp d)
  end.

(** As `width_value_class/2`: the class a store of the width w reads
    its value at. *)
Definition width_value_class (w : width) : option class :=
  match w with
  | Wb | Wh | Ww => Some W
  | Wl => Some L
  | Ws => Some Single
  | Wd => Some Double
  | Wp | Wx => None
  end.

(** As `raw_store//6`. *)
Definition raw_store (cx : ctx) (w : width) (v : value) : list line :=
  match w with
  | Wx => x87_push cx v ++ [ins "fstp" "t" [mem 0 "rax"]]
  | _ =>
      match width_value_class w with
      | Some k => load cx v k "d" ++ store_insn w "d"
      | None => todo "store width"
      end
  end.

(** As `aux_of_lower//0`: the aux pointer of the object at the lower
    in `%rcx` into `%rdx`, setting ZF if it has none. *)
Definition aux_of_lower : list line :=
  [ins "mov" "q" [mem (-8) "rcx"; reg "rdx"];
   ins "movabs" "q" [imm aux_pointer_mask; reg "rsi"];
   ins "and" "q" [reg "rsi"; reg "rdx"]].

(** As `pointer_load_effect//4`: one step of a pointer load's
    protocol, at the instruction index of the block b. *)
Definition pointer_load_effect (cx : ctx) (b : name) (index : string) (e : effect)
  : list line :=
  let nolower := local_label cx b index "nolower" in
  let have := local_label cx b index "have" in
  match e with
  | AuxRead =>
      aux_of_lower
      ++ [ins0 "jz" [sym nolower];
          ins "mov" "q" [reg "rax"; reg "rsi"];
          ins "sub" "q" [reg "rcx"; reg "rsi"];
          ins "mov" "q" [mem_index 0 "rdx" "rsi"; reg "rsi"]]
  | LowerResolve =>
      [ins "test" "b" [imm 1; reg "sil"];
       ins0 "jz" [sym have];
       ins "and" "q" [imm (-2); reg "rsi"];
       ins "mov" "q" [mem 8 "rsi"; reg "rsi"];
       ins0 "jmp" [sym have];
       label nolower;
       ins "xor" "l" [reg "esi"; reg "esi"];
       label have]
  | AtomicRead =>
      [ins "mov" "q" [reg "rax"; reg "rdi"]; ins "mov" "q" [reg "rcx"; reg "rsi"]]
      ++ origin_store cx "c"
      ++ [ins0 "call" [plt "filc_load_ptr_atomic_with_manual_tracking_outline"];
          ins "mov" "q" [reg "rdx"; reg "rcx"]]
  | AddressRead =>
      [ins "mov" "q" [mem 0 "rax"; reg "rax"]; ins "mov" "q" [reg "rsi"; reg "rcx"]]
  | _ => todo "pointer load effect"
  end.

(** As `pointer_store_effect//6`: one step of the protocol of a
    store of the pointer v at the pointer a. Ensuring the aux may
    exit, so `rooted_reload` reads both again from their roots
    before the lower and then the address are written. *)
Definition pointer_store_effect (cx : ctx) (b : name) (index : string) (v a : value)
                                (e : effect) : list line :=
  match e with
  | AuxEnsure =>
      let haveaux := local_label cx b index "haveaux" in
      aux_of_lower
      ++ [ins0 "jnz" [sym haveaux]]
      ++ slot_load cx KThread "rdi"
      ++ [ins "lea" "q" [mem (-16) "rcx"; reg "rsi"];
          ins0 "call" [plt "filc_object_ensure_aux_ptr_outline"];
          ins "mov" "q" [reg "rax"; reg "rdx"];
          label haveaux]
      ++ slot_store cx "rdx" KAux
  | LowerBarrier =>
      let nobarrier := local_label cx b index "nobarrier" in
      lower_load cx v "rsi"
      ++ [ins "test" "q" [reg "rsi"; reg "rsi"];
          ins0 "jz" [sym nobarrier];
          ins "mov" "q" [gotpcrel "filc_current_marking_state"; reg "rax"];
          ins "cmp" "l" [imm 0; mem 0 "rax"];
          ins0 "je" [sym nobarrier]]
      ++ slot_load cx KThread "rdi"
      ++ [ins0 "call" [plt "filc_store_barrier_for_lower_slow"]; label nobarrier]
  | RootedReload =>
      flight_load cx a
      ++ slot_load cx KAux "rdx"
      ++ [ins "mov" "q" [reg "rax"; reg "r8"]; ins "sub" "q" [reg "rcx"; reg "r8"]]
      ++ lower_load cx v "rsi"
      ++ load cx v L "r9"
  | AtomicWrite =>
      [ins "mov" "q" [reg "rax"; reg "rsi"]; ins "mov" "q" [reg "rcx"; reg "rdx"]]
      ++ origin_store cx "c"
      ++ slot_load cx KThread "rdi"
      ++ load cx v L "c"
      ++ lower_load cx v "r8"
      ++ [ins0 "call" [plt "filc_store_ptr_atomic_outline"]]
  | LowerWrite => [ins "mov" "q" [reg "rsi"; mem_index 0 "rdx" "r8"]]
  | AddressWrite => [ins "mov" "q" [reg "r9"; mem 0 "rax"]]
  | _ => todo "pointer store effect"
  end.

(** As `raw_access//4`: the access a at a heap pointer. *)
Definition raw_access (cx : ctx) (b : name) (index : string) (a : access) : list line :=
  match a with
  | ALoad d k t _ _ => raw_load cx t k d
  | AStore w _ v _ => raw_store cx w v
  | ALoadPointer d _ es _ =>
      flat_map (pointer_load_effect cx b index) es ++ flight_store cx d
  | AStorePointer _ v (AtValue p) es => flat_map (pointer_store_effect cx b index v p) es
  | AStorePointer _ _ (AtLocal _ _) _ => todo "pointer store at a local"
  | ATouch _ => []
  end.

(** ## Named locals *)

(** As `local_address//5`: the address of the access's aux word into
    `%rdx` and of its payload into `%rax`. The check has passed, so
    an offset in range and aligned is a constant displacement. *)
Definition local_address (off limit mask a p : Z) : list line :=
  if (0 <=? off) && (off <=? limit) && (Z.land off mask =? 0)
  then [ins "lea" "q" [mem (a + off) "rbp"; reg "rdx"];
        ins "lea" "q" [mem (p + off) "rbp"; reg "rax"]]
  else [ins "lea" "q" [mem_index a "rbp" "rax"; reg "rdx"];
        ins "lea" "q" [mem_index p "rbp" "rax"; reg "rax"]].

(** As `local_check//6`: the exact bounds of the named local x,
    with no heap lower. The offset and the size are the stack
    reporter's arguments; the address is formed only after the
    check. *)
Definition local_check (cx : ctx) (b : name) (index : string) (x : name) (off : Z)
                       (k : check_kind) : list line :=
  match nm_find x (cx_locals cx) with
  | None => todo "no local"
  | Some s =>
      let mask := ck_align k - 1 in
      let limit := ls_size s - ck_size k in
      let fail := local_label cx b index "localfail" in
      let good := local_label cx b index "localok" in
      load cx (Const off) L "a"
      ++ load cx (Const (ls_size s)) L "c"
      ++ load cx (Const limit) L "d"
      ++ [ins "test" "q" [reg "rdx"; reg "rdx"]; ins0 "js" [sym fail];
          ins "cmp" "q" [reg "rdx"; reg "rax"]; ins0 "ja" [sym fail];
          ins "test" "q" [imm mask; reg "rax"]; ins0 "jnz" [sym fail];
          ins0 "jmp" [sym good];
          label fail;
          ins "mov" "q" [reg "rax"; reg "rdi"];
          ins "mov" "q" [reg "rcx"; reg "rsi"];
          ins "lea" "q" [rip (check_origin_label (cx_name cx) k); reg "rdx"];
          ins0 "call" [plt "filc_optimized_stack_access_check_fail"];
          ins0 "ud2" [];
          label good]
      ++ local_address off limit mask (eight - ls_aux s) (- ls_payload s)
  end.

(** As `local_raw_access//4`: the access a at a named local, with
    the payload address in `%rax` and the aux word's in `%rdx`. Only
    what a pointer load reads or a pointer store writes has a heap
    lower. *)
Definition local_raw_access (cx : ctx) (b : name) (index : string) (a : access)
  : list line :=
  match a with
  | ALoadPointer d _ es _ =>
      flat_map (fun e => match e with
                         | AuxRead => [ins "mov" "q" [mem 0 "rdx"; reg "rcx"]]
                         | AddressRead => [ins "mov" "q" [mem 0 "rax"; reg "rax"]]
                         | _ => todo "local load effect"
                         end) es
      ++ flight_store cx d
  | AStorePointer _ v _ es =>
      flat_map (fun e => match e with
                         | LowerWrite =>
                             lower_load cx v "rcx" ++ [ins "mov" "q" [reg "rcx"; mem 0 "rdx"]]
                         | AddressWrite =>
                             load cx v L "si" ++ [ins "mov" "q" [reg "rsi"; mem 0 "rax"]]
                         | _ => todo "local store effect"
                         end) es
  | _ => raw_access cx b index a
  end.

(** ## Values *)

(** As `integer_inst//5`: the op's value in `%rax`, then into the
    temporary d. *)
Definition integer_inst (cx : ctx) (o : op) (k : class) (args : list value) (d : name)
  : list line :=
  compute_op cx o k args ++ slot_store cx "rax" (KTmp d).

Definition int32_min : Z := -2147483648.
Definition int32_max : Z := 2147483647.

(** As `span_end//2`: the pointer in `%rax` plus off, modulo 2^64,
    into the register r. *)
Definition span_end (off : Z) (r : string) : list line :=
  if (int32_min <=? off) && (off <=? int32_max)
  then [ins "lea" "q" [mem off "rax"; reg r]]
  else [ins "movabs" "q" [imm (off mod two64); reg "rsi"];
        ins "lea" "q" [mem_index 0 "rax" "rsi"; reg r]].

(** As the `span_test` clause of `kind_inst//8`: 1 when the lower
    of p is not null and lower <= p + lo < p + hi <= upper,
    unsigned; else 0. It reads only what a full check reads and
    never traps. *)
Definition span_test_lines (cx : ctx) (b : name) (index : string) (lo hi : Z) (p : value)
                           (d : name) : list line :=
  let zero := local_label cx b index "span0" in
  let done := local_label cx b index "span1" in
  flight_load cx p
  ++ [ins "test" "q" [reg "rcx"; reg "rcx"]; ins0 "jz" [sym zero]]
  ++ span_end lo "rdx"
  ++ [ins "cmp" "q" [reg "rcx"; reg "rdx"]; ins0 "jb" [sym zero]]
  ++ span_end hi "rax"
  ++ [ins "cmp" "q" [reg "rdx"; reg "rax"]; ins0 "jbe" [sym zero];
      ins "cmp" "q" [mem (-16) "rcx"; reg "rax"]; ins0 "ja" [sym zero];
      ins "mov" "l" [imm 1; reg "eax"];
      ins0 "jmp" [sym done];
      label zero;
      ins "xor" "l" [reg "eax"; reg "eax"];
      label done]
  ++ slot_store cx "rax" (KTmp d).

(** As `kind_inst//8`: the temporary d, of class k, is o of args,
    at the instruction index of the block b. *)
Definition let_lines (cx : ctx) (b : name) (index : string) (d : name) (k : class) (o : op)
                     (args : list value) : list line :=
  if x87_op o k then x87_inst cx o k args d
  else
    match o with
    | Add | Sub | Copy =>
        match k with
        | W | L | Single | Double => integer_inst cx o k args d
        | _ => todo "class"
        end
    | Mul | Div | Udiv | Rem | Urem | And | Or | Xor | Sar | Shr | Shl | Neg | Select
    | Cmp _ _ | Ext _ | ExtF _ | Truncd | Truncx | FloatToInt _ _ | IntToFloat _ _ | Cast =>
        integer_inst cx o k args d
    | Ptoi =>
        match k, args with
        | L, [p] => load cx p L "a" ++ slot_store cx "rax" (KTmp d)
        | _, _ => todo "ptoi"
        end
    | Alloc align =>
        match k, args with
        | P, [n] =>
            load cx n L "si"
            ++ slot_load cx KThread "rdi"
            ++ (if align >=? sixteen
                then [ins "mov" "l" [imm align; reg "edx"];
                      ins0 "call" [plt "filc_allocate_with_alignment"]]
                else [ins0 "call" [plt "filc_allocate"]])
            ++ [ins "lea" "q" [mem sixteen "rax"; reg "rax"];
                ins "mov" "q" [reg "rax"; reg "rcx"]]
            ++ flight_store cx d
        | _, _ => todo "alloc"
        end
    | SpanTest lo hi =>
        match k, args with
        | W, [p] => span_test_lines cx b index lo hi p d
        | _, _ => todo "span_test"
        end
    | _ => todo "let"
    end.

(** As `flight_address_load//3`: an address operand of a flight
    into the short register r. *)
Definition flight_address_load (cx : ctx) (a : flight_arg) (r : string) : list line :=
  match a with
  | FAddress p => load cx p L r
  | FValue v => load cx v L r
  end.

(** As `shared_lower/3`: the flight d's lower is the root of its
    donor, which already holds it. *)
Definition shared_lower (cx : ctx) (lower : flight_lower) (d : name) : bool :=
  match lower with
  | LowerOf (Tmp p) =>
      negb (name_eqb p d)
      && match slot cx (KLower (KTmp p)), slot cx (KLower (KTmp d)) with
         | Some o1, Some o2 => o1 =? o2
         | _, _ => false
         end
  | _ => false
  end.

(** As the `flight` clause of `inst//4`: every input is read before
    the destination is written. The second address goes by `%rdx`;
    `%rcx` holds the lower. *)
Definition flight_lines (cx : ctx) (d : name) (o : op) (args : list flight_arg)
                        (lower : flight_lower) : list line :=
  match args with
  | [] => todo "flight arguments"
  | a :: rest =>
      let calc :=
        match o, rest with
        | Copy, [] => []
        | Add, [x] => flight_address_load cx x "d" ++ [ins "add" "q" [reg "rdx"; reg "rax"]]
        | Sub, [x] => flight_address_load cx x "d" ++ [ins "sub" "q" [reg "rdx"; reg "rax"]]
        | _, _ => todo "flight"
        end in
      if shared_lower cx lower d
      then flight_address_load cx a "a" ++ calc ++ slot_store cx "rax" (KTmp d)
      else flight_address_load cx a "a"
           ++ match lower with
              | LowerOf p => lower_load cx p "rcx"
              | LowerNone => [ins "xor" "l" [reg "ecx"; reg "ecx"]]
              end
           ++ calc ++ flight_store cx d
  end.

(** ## Calls *)

(** As `word_reg_load//4`: a word of a call into the short register
    r. *)
Definition word_reg_load (cx : ctx) (s : source) (r : string) : list line :=
  match s with
  | SrcAddr v => load cx v L r
  | SrcVal k v => load cx v k r
  | SrcLower v => lower_load cx v (reg64 r)
  | _ => todo "call word"
  end.

(** As `typed_stack_args//4`: the words that travel on the stack,
    through `%rax`. *)
Fixpoint typed_stack_args (cx : ctx) (ws : list word) (ls : list location) : list line :=
  match ws, ls with
  | Wf _ s :: ws', l :: ls' =>
      match l with
      | LocStack i => word_reg_load cx s "a" ++ [ins "mov" "q" [reg "rax"; mem (eight * i) "rsp"]]
      | _ => []
      end
      ++ typed_stack_args cx ws' ls'
  | _, _ => []
  end.

(** As `typed_register_args//4`. *)
Fixpoint typed_register_args (cx : ctx) (ws : list word) (ls : list location) : list line :=
  match ws, ls with
  | Wf k s :: ws', l :: ls' =>
      match l with
      | LocStack _ => []
      | LocReg r => word_reg_load cx s r
      | LocXmm x => word_reg_load cx s "a" ++ to_xmm k "a" x
      end
      ++ typed_register_args cx ws' ls'
  | _, _ => []
  end.

(** As `entry_call//4`: the entry registers and the call of a fast
    entry: of the operand callee, or without one of the function
    object whose lower is in the aux slot. A buffered return's buffer
    sits above the pop bytes of stack words. *)
Definition entry_call (cx : ctx) (r : protocol) (callee : option operand) (pop : Z)
  : list line :=
  match r, callee with
  | Registers, Some target =>
      slot_load cx KThread "rdi"
      ++ [ins "xor" "l" [reg "esi"; reg "esi"]; ins0 "call" [target]]
  | Registers, None =>
      slot_load cx KThread "rdi" ++ slot_load cx KAux "rsi"
      ++ [ins "call" "q" [ind (mem function_object_fast_entry "rsi")]]
  | Buffer _, Some target =>
      slot_load cx KThread "rsi"
      ++ [ins "lea" "q" [mem pop "rsp"; reg "rdi"];
          ins "xor" "l" [reg "edx"; reg "edx"];
          ins0 "call" [target]]
  | Buffer _, None =>
      slot_load cx KThread "rsi" ++ slot_load cx KAux "rdx"
      ++ [ins "lea" "q" [mem pop "rsp"; reg "rdi"];
          ins "call" "q" [ind (mem function_object_fast_entry "rdx")]]
  end.

(** As `fast_call//4`: the arguments, the entry registers and the
    call, in the fast convention. *)
Definition fast_call (cx : ctx) (r : protocol) (ws : list word) (callee : option operand)
  : list line :=
  let '(ls, ns, _) := typed_locations ws r in
  let pop := stack_bytes ns in
  (if pop >? 0 then [ins "sub" "q" [imm pop; reg "rsp"]] else [])
  ++ typed_stack_args cx ws ls
  ++ typed_register_args cx ws ls
  ++ entry_call cx r callee pop
  ++ (if pop >? 0 then [ins "add" "q" [imm pop; reg "rsp"]] else []).

(** As `reg_slot_stores//3`. *)
Fixpoint reg_slot_stores (cx : ctx) (ks : list key) (rs : list string) : list line :=
  match ks, rs with
  | [], _ => []
  | k :: ks', r :: rs' => slot_store cx r k ++ reg_slot_stores cx ks' rs'
  | _ :: _, [] => todo "result registers"
  end.

(** As `buffer_slot_copies//3`: each word of a returned buffer into
    its slot. *)
Fixpoint buffer_slot_copies (cx : ctx) (ks : list key) (off : Z) : list line :=
  match ks with
  | [] => []
  | k :: ks' =>
      ins "mov" "q" [mem off "rsp"; reg "rax"] :: slot_store cx "rax" k
      ++ buffer_slot_copies cx ks' (off + eight)
  end.

(** As `typed_result_gprs//3` and `typed_result_xmms//3`, over the
    registers `result_registers/2` gives a returned tuple's words.
    The integer registers are stored first, since a float goes to
    its slot through `%rax`. *)
Fixpoint typed_result_gprs (cx : ctx) (ts : list key) (rs : list result_reg) : list line :=
  match ts, rs with
  | [], [] => []
  | t :: ts', r :: rs' =>
      match r with RrGpr g => slot_store cx g t | RrXmm _ _ => [] end
      ++ typed_result_gprs cx ts' rs'
  | _, _ => todo "result registers"
  end.

Fixpoint typed_result_xmms (cx : ctx) (ts : list key) (rs : list result_reg) : list line :=
  match ts, rs with
  | [], [] => []
  | t :: ts', r :: rs' =>
      match r with
      | RrXmm k x => from_xmm k x "a" ++ slot_store cx "rax" t
      | RrGpr _ => []
      end
      ++ typed_result_xmms cx ts' rs'
  | _, _ => todo "result registers"
  end.

(** As `typed_result_stores//3`, with `result_registers/2`. *)
Definition typed_result_stores (cx : ctx) (ks : list (class * key)) : list line :=
  match result_registers (map fst ks) ["rdx"; "rcx"] ["xmm0"; "xmm1"] with
  | Some rs => typed_result_gprs cx (map snd ks) rs ++ typed_result_xmms cx (map snd ks) rs
  | None => todo "result registers"
  end.

(** As `fast_result//3`: the exception flag, then the results from
    their registers or the buffer into their slots. *)
Definition fast_result (cx : ctx) (r : protocol) (c : channels) : list line :=
  let exc := special_label cx "exc" in
  let flag := [ins "test" "b" [imm 1; reg "al"]; ins0 "jnz" [sym exc]] in
  match r, c with
  | Registers, ChFloat k d => flag ++ from_xmm k "xmm0" "a" ++ slot_store cx "rax" (KTmp d)
  | Registers, ChTyped ks =>
      flag ++ typed_result_stores cx ks
  | Registers, ChSlots ks => flag ++ reg_slot_stores cx ks ["rdx"; "rcx"]
  | Buffer _, ChSlots ks =>
      [ins "cmp" "b" [imm 0; mem 0 "rsp"]; ins0 "jne" [sym exc]]
      ++ buffer_slot_copies cx ks eight
  | Buffer _, _ => todo "buffered result"
  end.

(** As `function_check//1`: with a pointer in `%rax` and `%rcx`, a
    jump to fail unless it is the address of a function object. *)
Definition function_check (fail : string) : list line :=
  [ins "test" "q" [reg "rcx"; reg "rcx"];
   ins0 "jz" [sym fail];
   ins "mov" "q" [mem (-8) "rcx"; reg "rdx"];
   ins "movabs" "q" [imm special_type_mask; reg "rsi"];
   ins "and" "q" [reg "rdx"; reg "rsi"];
   ins "movabs" "q" [imm function_bits; reg "rdi"];
   ins "cmp" "q" [reg "rdi"; reg "rsi"];
   ins0 "jne" [sym fail];
   ins "movabs" "q" [imm aux_pointer_mask; reg "rsi"];
   ins "and" "q" [reg "rsi"; reg "rdx"];
   ins "cmp" "q" [reg "rdx"; reg "rax"];
   ins0 "jne" [sym fail]].

(** The generic packet: 32 cells are inline in the thread. *)
Definition inline_cells : Z := 32.
Definition inline_bytes : Z := 256.

(** As `cell_stores//2`: the argument cell i from `%rax` and its
    lower from `%rcx`, with the thread in the register t: in the
    inline buffers, or past them in the outline ones, by `%rsi`. *)
Definition cell_stores (i : Z) (t : string) : list line :=
  if i <? inline_cells
  then [ins "mov" "q" [reg "rax"; mem (thread_cc_inline_buffer + eight * i) t];
        ins "mov" "q" [reg "rcx"; mem (thread_cc_inline_aux_buffer + eight * i) t]]
  else let off := eight * (i - inline_cells) in
       [ins "mov" "q" [mem thread_cc_outline_buffer t; reg "rsi"];
        ins "mov" "q" [reg "rax"; mem off "rsi"];
        ins "mov" "q" [mem thread_cc_outline_aux_buffer t; reg "rsi"];
        ins "mov" "q" [reg "rcx"; mem off "rsi"]].

(** As `generic_call_args//3`: each argument into the thread's
    generic argument area. *)
Definition generic_call_arg (cx : ctx) (c : cell) : list line :=
  match c with
  | Cell i k (CellValue v) lower =>
      load cx v k "a"
      ++ match lower with
         | Some (CellValue p) => lower_load cx p "rcx"
         | Some (CellSaved _) => todo "saved lower"
         | None => [ins "xor" "l" [reg "ecx"; reg "ecx"]]
         end
      ++ slot_load cx KThread "rdx"
      ++ cell_stores i "rdx"
  | Cell _ _ (CellSaved _) _ => todo "saved cell"
  end.

(** As `outline_ensure//3`: a packet of more than the inline bytes
    needs the thread's outline buffers to hold the rest, before any
    cell is set. *)
Definition outline_ensure (cx : ctx) (size : Z) (ok : string) : list line :=
  if size >? inline_bytes
  then slot_load cx KThread "rdi"
       ++ [ins "cmp" "q" [imm (size - inline_bytes); mem thread_cc_outline_size "rdi"];
           ins0 "jae" [sym ok];
           ins "mov" "q" [imm (size - inline_bytes); reg "rsi"];
           ins0 "call" [plt "filc_thread_ensure_cc_outline_buffer_slow"];
           label ok]
  else [].

(** As `generic_slot_copies//2`: a generic return's words, from the
    thread at `%rsi`, into their slots. *)
Definition generic_slot_copy (cx : ctx) (c : cell) : list line :=
  match c with
  | Cell i _ (CellValue (Tmp d)) lower =>
      ins "mov" "q" [mem (thread_cc_inline_buffer + eight * i) "rsi"; reg "rax"]
      :: slot_store cx "rax" (KTmp d)
      ++ match lower with
         | Some (CellValue (Tmp l)) =>
             ins "mov" "q" [mem (thread_cc_inline_aux_buffer + eight * i) "rsi"; reg "rax"]
             :: slot_store cx "rax" (KLower (KTmp l))
         | Some _ => todo "result lower"
         | None => []
         end
  | _ => todo "result cell"
  end.

(** As `generic_results//3`, with `rets_check//2`: the check that
    the generic return's size in `%rdx` is at least need, then the
    result cells. *)
Definition generic_results (cx : ctx) (need : Z) (results : list cell) (retok : string)
  : list line :=
  match results with
  | [] => if need =? 0 then [] else todo "generic results"
  | _ =>
      slot_load cx KThread "rsi"
      ++ [ins "cmp" "q" [imm need; reg "rdx"];
          ins0 "jae" [sym retok];
          ins "mov" "q" [reg "rdx"; reg "rdi"];
          ins "mov" "l" [imm need; reg "esi"];
          ins "xor" "l" [reg "edx"; reg "edx"];
          ins0 "call" [plt "filc_cc_rets_check_failure"];
          ins0 "ud2" [];
          label retok]
      ++ flat_map (generic_slot_copy cx) results
  end.

(** As `indirect_call//10`: a call through a checked function, whose
    lower is in the aux slot and in `%rcx`: the fast entry if its
    signature is the call site's, else the generic entry, with each
    argument a cell of the thread's packet. *)
Definition indirect_call (cx : ctx) (b : name) (index : string) (sig : Z) (r : protocol)
                         (ws : list word) (c : channels) (size : Z) (cells : list cell)
                         (need : Z) (results : list cell) : list line :=
  let exc := special_label cx "exc" in
  let generic := local_label cx b index "generic" in
  let done := local_label cx b index "done" in
  [ins "movabs" "q" [imm sig; reg "rsi"];
   ins "cmp" "q" [reg "rsi"; mem function_object_signature "rcx"];
   ins0 "jne" [sym generic]]
  ++ fast_call cx r ws None
  ++ fast_result cx r c
  ++ [ins0 "jmp" [sym done]; label generic]
  ++ outline_ensure cx size (local_label cx b index "outline")
  ++ flat_map (generic_call_arg cx) cells
  ++ slot_load cx KThread "rdi"
  ++ slot_load cx KAux "rsi"
  ++ [ins "mov" "l" [imm size; reg "edx"];
      ins "call" "q" [ind (mem function_object_generic_entry "rsi")];
      ins "test" "b" [imm 1; reg "al"];
      ins0 "jnz" [sym exc]]
  ++ generic_results cx need results (local_label cx b index "retok")
  ++ [label done].

(** ## Actions *)

(** As `target_operand/2`. *)
Definition target_operand (t : call_target) : operand :=
  match t with
  | TImplementation f sig => sym (impl_symbol sig (name_text f))
  | TEntry f sig => sym (entry_symbol sig (name_text f))
  end.

(** As the plain `getter` clause of `abi_action//4`: the call of a
    symbol's getter, which gives its address in `%rax` and `%rdx`. *)
Definition getter_call (cx : ctx) (target : operand) (d : name) : list line :=
  slot_load cx KThread "rdi"
  ++ [ins "lea" "q" [rip (origin_label (cx_name cx) "c"); reg "rsi"];
      ins0 "call" [target];
      ins "mov" "q" [reg "rdx"; reg "rcx"]]
  ++ flight_store cx d.

(** As `va_arg_load//5`: the helper has left the address of the
    argument's payload in `%rax` and of its aux word in `%rdx`;
    both are read with no safepoint between. *)
Definition va_arg_load (cx : ctx) (b : name) (index : string) (k : class) (d : name)
  : list line :=
  match k with
  | W | Single => ins "mov" "l" [mem 0 "rax"; reg "eax"] :: slot_store cx "rax" (KTmp d)
  | L | Double => ins "mov" "q" [mem 0 "rax"; reg "rax"] :: slot_store cx "rax" (KTmp d)
  | Extended => ins "fld" "t" [mem 0 "rax"] :: x87_pop cx d
  | P =>
      let none := local_label cx b index "va_none" in
      let have := local_label cx b index "va_have" in
      [ins "xor" "l" [reg "ecx"; reg "ecx"];
       ins "test" "q" [reg "rdx"; reg "rdx"];
       ins0 "jz" [sym none];
       ins "mov" "q" [mem 0 "rdx"; reg "rcx"];
       ins "test" "b" [imm 1; reg "cl"];
       ins0 "jz" [sym have];
       ins "and" "q" [imm (-2); reg "rcx"];
       ins "mov" "q" [mem 8 "rcx"; reg "rcx"];
       label have; label none;
       ins "mov" "q" [mem 0 "rax"; reg "rax"]]
      ++ flight_store cx d
  | _ => todo "va_arg class"
  end.

(** As `zero_words//2`: n zero words from `off(%rbp)` up. *)
Fixpoint zero_words (fuel : nat) (off : Z) : list line :=
  match fuel with
  | O => []
  | S fuel' => ins "mov" "q" [imm 0; mem off "rbp"] :: zero_words fuel' (off + eight)
  end.

(** As `abi_action//4`, for the actions of an instruction. The
    reference emission copies nothing inline, so a copy's filter and
    join are empty. *)
Definition action_lines (cx : ctx) (b : name) (index : string) (a : action) : list line :=
  match a with
  | AOrigin => origin_store cx "c"
  | AReserveResult (Buffer n) => [ins "sub" "q" [imm (buffer_bytes n); reg "rsp"]]
  | AReleaseResult (Buffer n) => [ins "add" "q" [imm (buffer_bytes n); reg "rsp"]]
  | AReserveResult Registers | AReleaseResult Registers => []
  | AInvoke t r ws => fast_call cx r ws (Some (target_operand t))
  | AResult r c => fast_result cx r c
  | ACopyFilter _ _ _ _ | ACopyJoin => []
  | ADispatch p sig r ws c size cells need results =>
      flight_load cx p
      ++ function_check (special_label cx "notfn")
      ++ slot_store cx "rcx" KAux
      ++ indirect_call cx b index sig r ws c size cells need results
  | AGetter (GetLocal s) d => getter_call cx (sym (getter_symbol (name_text s))) d
  | AGetter (GetExternal s) d => getter_call cx (plt (getter_symbol (name_text s))) d
  | AGetter (GetWeak s) d =>
      let getter := getter_symbol (name_text s) in
      let null := local_label cx b index "weak_null" in
      let done := local_label cx b index "weak_done" in
      [ins "cmp" "q" [imm 0; gotpcrel getter]; ins0 "je" [sym null]]
      ++ getter_call cx (plt getter) d
      ++ [ins0 "jmp" [sym done]; label null;
          ins "xor" "l" [reg "eax"; reg "eax"]; ins "xor" "l" [reg "ecx"; reg "ecx"]]
      ++ flight_store cx d
      ++ [label done]
  | ASnapshotCursor off d =>
      flight_load cx (Tmp va_snapshot)
      ++ load cx (Const off) L "d"
      ++ [ins "add" "q" [reg "rdx"; reg "rax"]]
      ++ flight_store cx d
  | AConsumeVa k p size d =>
      flight_load cx p
      ++ [ins "mov" "q" [reg "rax"; reg "rdi"];
          ins "mov" "q" [reg "rcx"; reg "rsi"];
          ins "mov" "l" [imm size; reg "edx"];
          ins "mov" "l" [imm size; reg "ecx"];
          ins0 "call" [plt "filc_get_next_ptr_bytes_for_va_arg"]]
      ++ va_arg_load cx b index k d
  | AInitializeLocal x =>
      match nm_find x (cx_locals cx) with
      | None => todo "no local"
      | Some s =>
          let words := ls_padded s / eight in
          zero_words (Z.to_nat words) (- ls_payload s)
          ++ zero_words (Z.to_nat words) (eight - ls_aux s)
          ++ [ins "mov" "q" [imm words; mem (- ls_aux s) "rbp"];
              ins "lea" "q" [mem (- ls_aux s) "rbp"; reg "rax"]]
          ++ slot_store cx "rax" (KStackAux x)
      end
  end.

(** ## Instructions *)

(** The pointer an access is at. *)
Definition access_place (a : access) : place :=
  match a with
  | ALoad _ _ _ _ p | AStore _ _ _ p | ALoadPointer _ _ _ p | AStorePointer _ _ p _
  | ATouch p => p
  end.

(** As `inst//4`: the code of the instruction at index i of the
    block b. *)
Definition inst_lines (cx : ctx) (b : name) (i : Z) (pi : pinst) : list line :=
  let index := decimal i in
  match pi with
  | PAbi acts => flat_map (action_lines cx b index) acts
  | PInst (FPlain (Let d k o args)) => let_lines cx b index d k o args
  | PInst (FPlain (Flight d o args lower)) => flight_lines cx d o args lower
  | PInst (FPlain _) => todo "plain instruction"
  | PInst (FFused (Check _ size r align) a) =>
      match access_place a with
      | AtValue p =>
          flight_load cx p
          ++ access_check cx (mkKind size (rights_write r) align)
          ++ raw_access cx b index a
      | AtLocal _ _ => todo "heap check at a local"
      end
  | PInst (FFused (CheckLocal x off size r align) a) =>
      local_check cx b index x off (mkKind size (rights_write r) align)
      ++ local_raw_access cx b index a
  | PInst (FFused _ _) => todo "fused check"
  | PInst (FReused a) =>
      match access_place a with
      | AtValue p =>
          let off := access_offset a in
          match a with
          | ALoadPointer _ _ _ _ => flight_load cx p
          | _ => load cx p L "a"
          end
          ++ (if off =? 0 then [] else [ins "add" "q" [imm off; reg "rax"]])
          ++ raw_access cx b index a
      | AtLocal _ _ => todo "reused access at a local"
      end
  | PInst (FCall _ _ _) => todo "call that is not lowered"
  end.
