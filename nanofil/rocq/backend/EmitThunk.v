(** # Weak thunks

    The lines of a weak thunk from its plan (Plan.v's [thunk]), as
    filc_amd64.pl's `thunk//1` gives them. The thunk resolves its
    symbol through the getter and calls the fast entry when the
    callee's signature is the call's, else it transports its words as
    generic cells and the generic result back.

    Every incoming word is saved below `%rbp` before the getter can
    clobber it: word i at `-32-8i(%rbp)`. `%rbx` holds the thread,
    `%r12` the return buffer of a buffered return, and `-24(%rbp)`
    the callee's function object.

    Where the Prolog compiler has no clause for a form, the lines
    hold a [todo] (Layout.v) in that place. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Text Asm Plan PlanTerm Layout EmitObject Emit EmitInst.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## The words a thunk saves *)

(** As `never_signature/1`: the signature no function object has,
    which a call of more than 16 words is compared with, so that it
    always goes generic. *)
Definition thunk_never_signature : Z := 18446744073709551615.

(** The offsets, below `%rbp`, of the first saved word and of the
    callee's function object. *)
Definition saved_base : Z := -32.
Definition saved_object : Z := -24.

(** As `saved_operand/2`: the fast word `saved(I)` is at
    `-32-8I(%rbp)`. A cell of a thunk holds nothing else. *)
Definition saved_operand (s : cell_source) : option adapter_operand :=
  match s with
  | CellSaved i => Some (AoMem (saved_base - eight * i) "rbp")
  | CellValue _ => None
  end.

(** As `saved_words/3`: each word's class and where it is saved, the
    first at the index i. *)
Fixpoint saved_words (ws : list word) (i : Z) : list (class * option adapter_operand) :=
  match ws with
  | [] => []
  | Wf k _ :: ws' => (k, Some (AoMem (saved_base - eight * i) "rbp")) :: saved_words ws' (i + 1)
  end.

(** As `mixed_thunk_thread//1`: the thread into `%rbx`. A buffered
    return has its buffer in `%rdi`, kept in `%r12`, and the thread
    in `%rsi`, which the getter takes in `%rdi`. *)
Definition mixed_thunk_thread (r : protocol) : list line :=
  match r with
  | Registers => [ins "mov" "q" [reg "rdi"; reg "rbx"]]
  | Buffer _ =>
      [ins "mov" "q" [reg "rdi"; reg "r12"];
       ins "mov" "q" [reg "rsi"; reg "rbx"];
       ins "mov" "q" [reg "rsi"; reg "rdi"]]
  end.

(** As `incoming_bits//2`: the word at a location of the fast
    convention into `%rax`; a stack word is at `16+8I(%rbp)`. *)
Definition incoming_bits (l : location) (k : class) : list line :=
  match l with
  | LocReg r => [ins "mov" "q" [reg (reg64 r); reg "rax"]]
  | LocXmm x => from_xmm k x "a"
  | LocStack i =>
      match class_half k with
      | Some half =>
          [ins "mov" (class_suffix half) [mem (sixteen + eight * i) "rbp"; reg (reg_name "a" half)]]
      | None => todo "incoming class"
      end
  end.

(** As `save_mixed_words//3`: each incoming word to where it is
    saved. An integer stack word is copied whole, as a register one
    is: `w` and `l` share a signature digit, so a thunk emitted for a
    32-bit call also serves another object's 64-bit calls. *)
Fixpoint save_mixed_words (ws : list word) (ls : list location)
                          (ss : list (class * option adapter_operand)) : list line :=
  match ws, ls, ss with
  | [], [], [] => []
  | Wf k0 _ :: ws', l :: ls', (_, s) :: ss' =>
      incoming_bits l (match k0 with W => L | _ => k0 end)
      ++ match s with
         | Some (AoMem off b) => [ins "mov" "q" [reg "rax"; mem off b]]
         | _ => todo "saved word"
         end
      ++ save_mixed_words ws' ls' ss'
  | _, _, _ => todo "thunk words"
  end.

(** ## The callee *)

(** The getter's call, as `thunk_getter(strong, Getter, G)`: the
    callee's function object in `%rax` and `%rcx`. *)
Definition thunk_getter_call (getter : string) : list line :=
  [ins "xor" "l" [reg "esi"; reg "esi"];
   ins0 "call" [plt getter];
   ins "mov" "q" [reg "rdx"; reg "rcx"]].

(** As `thunk_getter//3`. The getter of a weak declaration may be
    null, and then so is the object: the function check fails, as
    clang's thunk does. *)
Definition thunk_getter (ref : thunk_ref) (getter g : string) : list line :=
  match ref with
  | RefLocal | RefStrong => thunk_getter_call getter
  | RefWeak =>
      let null := (g ++ ".null")%string in
      let got := (g ++ ".got")%string in
      [ins "cmp" "q" [imm 0; gotpcrel getter]; ins0 "je" [sym null]]
      ++ thunk_getter_call getter
      ++ [ins0 "jmp" [sym got]; label null;
          ins "xor" "l" [reg "eax"; reg "eax"];
          ins "xor" "l" [reg "ecx"; reg "ecx"];
          label got]
  end.

(** As `mixed_thunk_call//1`: the call of the fast entry of the
    object at `-24(%rbp)`, with the thread, and before it the buffer
    of a buffered return. *)
Definition mixed_thunk_call (r : protocol) : list line :=
  match r with
  | Registers =>
      [ins "mov" "q" [reg "rbx"; reg "rdi"];
       ins "mov" "q" [mem saved_object "rbp"; reg "rsi"];
       ins "call" "q" [ind (mem function_object_fast_entry "rsi")]]
  | Buffer _ =>
      [ins "mov" "q" [reg "r12"; reg "rdi"];
       ins "mov" "q" [reg "rbx"; reg "rsi"];
       ins "mov" "q" [mem saved_object "rbp"; reg "rdx"];
       ins "call" "q" [ind (mem function_object_fast_entry "rdx")]]
  end.

(** ## The generic call *)

(** As `outline_ensure_rdi//2`: with the thread in `%rdi`, a packet
    of more than the inline bytes needs the thread's outline buffers
    to hold the rest. *)
Definition outline_ensure_rdi (size : Z) (ok : string) : list line :=
  if size >? inline_bytes
  then [ins "cmp" "q" [imm (size - inline_bytes); mem thread_cc_outline_size "rdi"];
        ins0 "jae" [sym ok];
        ins "mov" "q" [imm (size - inline_bytes); reg "rsi"];
        ins0 "call" [plt "filc_thread_ensure_cc_outline_buffer_slow"];
        label ok]
  else [].

(** As `thunk_outline_ensure//2`. *)
Definition thunk_outline_ensure (size : Z) (g : string) : list line :=
  if size >? inline_bytes
  then ins "mov" "q" [reg "rbx"; reg "rdi"]
       :: outline_ensure_rdi size (g ++ ".outline")%string
  else [].

(** As `operand_thread_store//2`: the operand into the thread at an
    offset, through `%rax` if it is in memory. *)
Definition operand_thread_store (o : adapter_operand) (off : Z) : list line :=
  match o with
  | AoReg r => [ins "mov" "q" [reg r; mem off "rbx"]]
  | AoMem d b => [ins "mov" "q" [mem d b; reg "rax"]; ins "mov" "q" [reg "rax"; mem off "rbx"]]
  | AoSnapshotLower _ => todo "thread store"
  end.

(** One cell of `saved_generic//1`: an inline cell goes straight to
    the thread at `%rbx`, a later one through `cell_stores//2` into
    the outline buffers. A cell with no lower gets a zero one. *)
Definition saved_generic_cell (c : cell) : list line :=
  match c with
  | Cell i k data lower =>
      let ao := thread_cc_inline_buffer + eight * i in
      let lo := thread_cc_inline_aux_buffer + eight * i in
      match saved_operand data, lower with
      | None, _ => todo "thunk cell"
      | Some a, Some l =>
          match saved_operand l with
          | None => todo "thunk cell lower"
          | Some lw =>
              if i <? inline_cells
              then operand_thread_store a ao ++ operand_thread_store lw lo
              else match a, lw with
                   | AoMem ad ab, AoMem ld lb =>
                       [ins "mov" "q" [mem ad ab; reg "rax"];
                        ins "mov" "q" [mem ld lb; reg "rcx"];
                        ins "mov" "q" [reg "rbx"; reg "rdx"]]
                       ++ cell_stores i "rdx"
                   | _, _ => todo "thunk cell"
                   end
          end
      | Some w, None =>
          if i <? inline_cells
          then adapter_load k w "unused"
               ++ [ins "mov" "q" [reg "rax"; mem ao "rbx"]; ins "mov" "q" [imm 0; mem lo "rbx"]]
          else adapter_load k w "unused"
               ++ [ins "xor" "l" [reg "ecx"; reg "ecx"]; ins "mov" "q" [reg "rbx"; reg "rdx"]]
               ++ cell_stores i "rdx"
      end
  end.

(** As `saved_generic//1`: the saved words into the cells of the
    generic packet. *)
Definition saved_generic (cells : list cell) : list line :=
  flat_map saved_generic_cell cells.

(** ## The generic return *)

(** As `rets_check//2`: the check that the generic return's size in
    `%rdx` is at least need, with a call of
    `filc_cc_rets_check_failure` if it is not. *)
Definition rets_check (need : Z) (retok : string) : list line :=
  [ins "cmp" "q" [imm need; reg "rdx"];
   ins0 "jae" [sym retok];
   ins "mov" "q" [reg "rdx"; reg "rdi"];
   ins "mov" "l" [imm need; reg "esi"];
   ins "xor" "l" [reg "edx"; reg "edx"];
   ins0 "call" [plt "filc_cc_rets_check_failure"];
   ins0 "ud2" [];
   label retok].

(** As `thunk_typed_loads//2`: each word of a returned tuple from its
    thread offset into its register, a float through `%rax`. *)
Fixpoint thunk_typed_loads (rs : list result_reg) (offs : list Z) : list line :=
  match rs, offs with
  | [], [] => []
  | RrGpr g :: rs', off :: offs' =>
      ins "mov" "q" [mem off "rbx"; reg g] :: thunk_typed_loads rs' offs'
  | RrXmm k x :: rs', off :: offs' =>
      ins "mov" "q" [mem off "rbx"; reg "rax"] :: to_xmm k "a" x ++ thunk_typed_loads rs' offs'
  | _, _ => todo "typed result words"
  end.

(** As `thunk_reg_loads//2`: each generic return word, at its thread
    offset, into its register. *)
Fixpoint thunk_reg_loads (offs : list Z) (rs : list string) : list line :=
  match offs, rs with
  | [], _ => []
  | off :: offs', r :: rs' => ins "mov" "q" [mem off "rbx"; reg r] :: thunk_reg_loads offs' rs'
  | _ :: _, [] => todo "result registers"
  end.

(** As `thunk_generic_reg_words//4`: the result words, if the channel
    has any, in `%rdx` and `%rcx`, or `%xmm0` and `%xmm1`. *)
Definition thunk_generic_reg_words (c : adapter_channel) (need : Z) (srcs : list Z)
                                   (retok : string) : list line :=
  match c with
  | AdVoid => []
  | AdFloat k =>
      match srcs, class_half k with
      | [off], Some half =>
          rets_check need retok
          ++ [ins "mov" (class_suffix half) [mem off "rbx"; reg (reg_name "d" half)]]
          ++ to_xmm k "d" "xmm0"
      | _, _ => todo "float result"
      end
  | AdTyped ks =>
      match result_registers (typed_ret_kinds ks) ["rdx"; "rcx"] ["xmm0"; "xmm1"] with
      | Some rs => rets_check need retok ++ thunk_typed_loads rs srcs
      | None => todo "result registers"
      end
  | AdWords => rets_check need retok ++ thunk_reg_loads srcs ["rdx"; "rcx"]
  end.

(** As `thunk_buffer_copies//2`: each generic return word, at its
    thread offset, into the return buffer at `off(%r12)`. *)
Fixpoint thunk_buffer_copies (srcs : list Z) (off : Z) : list line :=
  match srcs with
  | [] => []
  | src :: srcs' =>
      [ins "mov" "q" [mem src "rbx"; reg "rax"]; ins "mov" "q" [reg "rax"; mem off "r12"]]
      ++ thunk_buffer_copies srcs' (off + eight)
  end.

(** As `thunk_generic_return//7`: after the generic entry's call and
    the test of its exception flag, the return of its result words,
    at the thread offsets srcs, then a jump to out. A buffered
    return's flag is the buffer's first byte. *)
Definition thunk_generic_return (r : protocol) (c : adapter_channel) (need : Z)
                                (srcs : list Z) (out retok exc : string) : list line :=
  match r with
  | Registers =>
      [ins0 "jnz" [sym out]]
      ++ thunk_generic_reg_words c need srcs retok
      ++ [ins "xor" "l" [reg "eax"; reg "eax"]; ins0 "jmp" [sym out]]
  | Buffer _ =>
      [ins0 "jnz" [sym exc]]
      ++ rets_check need retok
      ++ thunk_buffer_copies srcs eight
      ++ [ins "mov" "b" [imm 0; mem 0 "r12"];
          ins "mov" "q" [reg "r12"; reg "rax"];
          ins0 "jmp" [sym out];
          label exc;
          ins "mov" "b" [imm 1; mem 0 "r12"];
          ins "mov" "q" [reg "r12"; reg "rax"];
          ins0 "jmp" [sym out]]
  end.

(** ## The thunk *)

(** The value a thunk compares the callee's signature with. *)
Definition thunk_signature (s : sigref) : Z :=
  match s with
  | SigNumber n => n
  | SigNever _ _ => thunk_never_signature
  end.

(** As `thunk//1`. *)
Definition thunk_lines (t : thunk) : list line :=
  let f := name_text (th_name t) in
  let fi := entry_symbol (th_sig t) f in
  let getter := getter_symbol f in
  let g := (".L" ++ fi)%string in
  let generic := (g ++ ".generic")%string in
  let out := (g ++ ".out")%string in
  let fail := (g ++ ".fail")%string in
  let retok := (g ++ ".retok")%string in
  let exc := (g ++ ".exc")%string in
  let res := th_result t in
  let form := ar_return res in
  let ws := th_words t in
  let '(ls, ns, _) := typed_locations ws form in
  let pop := stack_bytes ns in
  let saved := saved_words ws 0 in
  let alloc := round16 (eight + eight * Zlength ws) in
  match channel_offsets (ar_copies res), channel_offsets (ar_zeros res) with
  | Some srcs, Some _ =>
      [Dir (DSection SText); p2align4]
      ++ match th_ref t with
         | RefLocal => []
         | _ => [Dir (DHidden (LSym fi)); Dir (DWeak (LSym fi))]
         end
      ++ [Dir (DType (LSym fi) (LSym "function")); label fi;
          ins "push" "q" [reg "rbp"];
          ins "mov" "q" [reg "rsp"; reg "rbp"];
          ins "push" "q" [reg "rbx"];
          ins "push" "q" [reg "r12"];
          ins "sub" "q" [imm alloc; reg "rsp"]]
      ++ mixed_thunk_thread form
      ++ save_mixed_words ws ls saved
      ++ thunk_getter (th_ref t) getter g
      ++ function_check fail
      ++ [ins "mov" "q" [reg "rcx"; mem saved_object "rbp"];
          ins "movabs" "q" [imm (thunk_signature (th_sig t)); reg "rsi"];
          ins "cmp" "q" [reg "rsi"; mem function_object_signature "rcx"];
          ins0 "jne" [sym generic]]
      ++ reserve_stack pop
      ++ adapter_stack saved ls g
      ++ adapter_registers saved ls g
      ++ mixed_thunk_call form
      ++ [ins0 "jmp" [sym out]; label generic]
      ++ thunk_outline_ensure (th_args_size t) g
      ++ saved_generic (th_cells t)
      ++ [ins "mov" "q" [reg "rbx"; reg "rdi"];
          ins "mov" "q" [mem saved_object "rbp"; reg "rsi"];
          ins "mov" "l" [imm (th_args_size t); reg "edx"];
          ins "call" "q" [ind (mem function_object_generic_entry "rsi")];
          ins "test" "b" [imm 1; reg "al"]]
      ++ thunk_generic_return form (ar_channel res) (th_need t) srcs out retok exc
      ++ [label fail;
          ins "mov" "q" [reg "rax"; reg "rdi"];
          ins "mov" "q" [reg "rcx"; reg "rsi"];
          ins0 "call" [plt "filc_check_function_call_fail"];
          ins0 "ud2" [];
          label out;
          ins "lea" "q" [mem (-16) "rbp"; reg "rsp"];
          ins "pop" "q" [reg "r12"];
          ins "pop" "q" [reg "rbx"];
          ins "pop" "q" [reg "rbp"];
          ins0 "ret" [];
          Dir (DSize (LSym fi))]
  | _, _ => todo "thunk packet"
  end.

(** The third word is saved at `-48(%rbp)`. *)
Example saved_words_third :
  saved_operand (CellSaved 2) = Some (AoMem (-48) "rbp").
Proof. reflexivity. Qed.
