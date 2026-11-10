(** The code of a function from its plan: filc_amd64.pl's
    `function//2` with every temporary in its stack slot, which is
    what `--registers=stack` selects there. The lines are the Prolog
    compiler's, one for one, which the backend's gate checks on the
    corpus (emit.sh).

    What is not ported yet is a [todo] line (Layout.v). *)
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Text Asm Plan PlanTerm Layout EmitOps EmitInst EmitObject.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## The frame's entry and exit *)

(** As `entry_regs_shift//1`: a buffered return's entry has the
    buffer in `%rdi` and the thread in `%rsi`. *)
Definition entry_regs_shift (r : protocol) : list line :=
  match r with
  | Registers => []
  | Buffer _ => [ins "mov" "q" [reg "rdi"; reg "rax"]; ins "mov" "q" [reg "rsi"; reg "rdi"]]
  end.

(** As `lowers_zeroing//2`: zero `lowers[0..n)`, so that the
    collector sees no stale lower. *)
Fixpoint lower_entry_stores (fuel : nat) (i base : Z) : list line :=
  match fuel with
  | O => []
  | S fuel' =>
      ins "mov" "q" [reg "rax"; mem (sixteen + eight * i - base) "rbp"]
      :: lower_entry_stores fuel' (i + 1) base
  end.
Definition lowers_zeroing (n base : Z) : list line :=
  if n >? 0
  then ins "xor" "l" [reg "eax"; reg "eax"] :: lower_entry_stores (Z.to_nat n) 0 base
  else [].

(** As `incoming_word//4`: a word of the fast convention from its
    location into its slot; an integer register goes straight there,
    the rest through `%rax`. *)
Definition incoming_word (cx : ctx) (l : location) (w : word) : list line :=
  match w with
  | Wf k (SrcSlot t) =>
      match l with
      | LocReg r => slot_store cx (reg64 r) t
      | LocXmm x => from_xmm k x "a" ++ slot_store cx "rax" t
      | LocStack i =>
          match class_half k with
          | Some half =>
              ins "mov" (class_suffix half) [mem (sixteen + eight * i) "rbp"; reg (reg_name "a" half)]
              :: slot_store cx "rax" t
          | None => todo "incoming class"
          end
      end
  | _ => todo "incoming source"
  end.

Fixpoint typed_incoming (cx : ctx) (ws : list word) (ls : list location) : list line :=
  match ws, ls with
  | w :: ws', l :: ls' => incoming_word cx l w ++ typed_incoming cx ws' ls'
  | _, _ => []
  end.

(** The entry of a function: `native_frame`, `stack_check`,
    `save_thread`, `save_return`, `zero_roots`, `push_frame(c)` and
    `receive`. There are no setjmp sites to snapshot. *)
Definition entry_lines (cx : ctx) (p : plan) : list line :=
  let ret := pl_return p in
  let base := cx_base cx in
  [ins "push" "q" [reg "rbp"];
   ins "mov" "q" [reg "rsp"; reg "rbp"];
   ins "sub" "q" [imm (cx_size cx); reg "rsp"]]
  ++ entry_regs_shift ret
  ++ [ins "cmp" "q" [reg "rsp"; mem thread_stack_limit "rdi"];
      ins0 "jae" [plt "filc_stack_overflow_failure"]]
  ++ slot_store cx "rdi" KThread
  ++ match ret with Registers => [] | Buffer _ => slot_store cx "rax" KRetbuf end
  ++ lowers_zeroing (Zlength (fr_roots (pl_frame p))) base
  ++ [ins "mov" "q" [mem thread_top_frame "rdi"; reg "rax"];
      ins "mov" "q" [reg "rax"; mem (- base) "rbp"]]
  ++ origin_store cx "c"
  ++ [ins "lea" "q" [mem (- base) "rbp"; reg "rax"];
      ins "mov" "q" [reg "rax"; mem thread_top_frame "rdi"]]
  ++ (let '(ls, _, _) := typed_locations (pl_incoming p) ret in
      typed_incoming cx (pl_incoming p) ls).

(** As `frame_pop//1`: the thread's top frame back to this frame's
    parent. *)
Definition frame_pop (cx : ctx) : list line :=
  slot_load cx KThread "rsi"
  ++ [ins "mov" "q" [mem (- cx_base cx) "rbp"; reg "rdi"];
      ins "mov" "q" [reg "rdi"; mem thread_top_frame "rsi"]].

Definition leave_ret : list line := [ins0 "leave" []; ins0 "ret" []].

(** The exception exit: `pop_frame`, then `exception(Return)`, which
    sets has_exception in `%al` or in the return buffer. *)
Definition exit_lines (cx : ctx) (ret : protocol) : list line :=
  frame_pop cx
  ++ match ret with
     | Registers => [ins "mov" "b" [imm 1; reg "al"]]
     | Buffer _ => slot_load cx KRetbuf "rax" ++ [ins "mov" "b" [imm 1; mem 0 "rax"]]
     end
  ++ leave_ret.

(** ## Edges *)

(** As `pollcheck//3`: call the runtime if the thread's state asks. *)
Definition pollcheck (cx : ctx) (block : name) (tag : string) : list line :=
  let no_poll := local_label cx block tag "poll" in
  slot_load cx KThread "rdi"
  ++ [ins "test" "b" [imm 14; mem thread_state "rdi"];
      ins0 "jz" [sym no_poll];
      ins "lea" "q" [rip (origin_label (cx_name cx) "n"); reg "rsi"];
      ins0 "call" [plt "filc_pollcheck_slow"];
      label no_poll].

Fixpoint pair_value (from : name) (pairs : list (name * value)) : option value :=
  match pairs with
  | [] => None
  | (l, v) :: pairs' => if term_eqb l from then Some v else pair_value from pairs'
  end.

(** As `phi_read//5`: the value a phi takes from the block from, into
    the phi's shadow slots. *)
Definition phi_read (cx : ctx) (from : name) (ph : phi) : list line :=
  match ph with
  | Phi d k pairs =>
      match pair_value from pairs with
      | None => todo "phi without a value for the edge"
      | Some v =>
          match k with
          | P =>
              load cx v L "a" ++ slot_store cx "rax" (KShadow d)
              ++ lower_load cx v "rax" ++ slot_store cx "rax" (KLower (KShadow d))
          | W | L | Single | Double => load cx v k "a" ++ slot_store cx "rax" (KShadow d)
          | _ => todo "phi class"
          end
      end
  end.

(** As `phi_writes//2`: each phi's shadow into the phi. *)
Definition phi_write (cx : ctx) (ph : phi) : list line :=
  match ph with
  | Phi d k _ =>
      slot_load cx (KShadow d) "rax" ++ slot_store cx "rax" (KTmp d)
      ++ match k with
         | P => slot_load cx (KLower (KShadow d)) "rax" ++ slot_store cx "rax" (KLower (KTmp d))
         | _ => []
         end
  end.

(** As `edge_moves//4`: the parallel copy of the target's phis, then
    the pollcheck if the target asks for one. *)
Definition edge_moves (cx : ctx) (from : name) (t : target) (tag : string) : list line :=
  let phis := match nm_find (edge_label t) (cx_phis cx) with Some phis => phis | None => [] end in
  flat_map (phi_read cx from) phis
  ++ flat_map (phi_write cx) phis
  ++ match t with Poll _ => pollcheck cx from tag | To _ => [] end.

(** As `edge//4`: the moves of the edge, then the jump. *)
Definition edge (cx : ctx) (from : name) (t : target) (tag : string) : list line :=
  edge_moves cx from t tag ++ [ins0 "jmp" [sym (block_label cx (edge_label t))]].

(** ## Returns *)

(** As `success(registers)`: has_exception = 0 in `%al`. *)
Definition success (r : protocol) : list line :=
  match r with
  | Registers => ins "xor" "l" [reg "eax"; reg "eax"] :: leave_ret
  | Buffer _ => todo "success of a buffered return"
  end.

(** As `ret_value//3`: the returned value in `%rdx`, with its lower
    in `%rcx` for a pointer; a float in `%xmm0`. *)
Definition ret_value (cx : ctx) (r : ret_type) (v : value) : list line :=
  match r with
  | RClass P => load cx v L "d" ++ lower_load cx v "rcx"
  | RClass W => load cx v W "d"
  | RClass L => load cx v L "d"
  | RClass Single => load cx v Single "a" ++ to_xmm Single "a" "xmm0"
  | RClass Double => load cx v Double "a" ++ to_xmm Double "a" "xmm0"
  | _ => todo "return class"
  end.

(** A word of a returned tuple. *)
Inductive ret_word : Type :=
| RwVal (k : class) (v : value)
| RwAddr (v : value)
| RwLower (v : value).

(** As `typed_return_word/4`: a pointer is its address and its
    lower. *)
Fixpoint typed_return_words (ks : list class) (vs : list value) : list ret_word :=
  match ks, vs with
  | k :: ks', v :: vs' =>
      match k with
      | P => RwAddr v :: RwLower v :: typed_return_words ks' vs'
      | _ => RwVal k v :: typed_return_words ks' vs'
      end
  | _, _ => []
  end.

(** The class of a word of a returned tuple. *)
Definition ret_word_class (w : ret_word) : class :=
  match w with RwVal k _ => k | RwAddr _ | RwLower _ => L end.

(** As `typed_return_loads//4` and `typed_return_load//5`: each word
    into the register `result_registers/2` gives it, here by its
    short name. *)
Fixpoint typed_return_loads (cx : ctx) (ws : list ret_word) (rs : list result_reg) : list line :=
  match ws, rs with
  | [], [] => []
  | w :: ws', r :: rs' =>
      match w, r with
      | RwVal k v, RrXmm _ x => load cx v k "a" ++ to_xmm k "a" x
      | RwVal k v, RrGpr g => load cx v k g
      | RwAddr v, RrGpr g => load cx v L g
      | RwLower v, RrGpr g => lower_load cx v (reg64 g)
      | _, _ => todo "typed return word"
      end
      ++ typed_return_loads cx ws' rs'
  | _, _ => todo "typed return words"
  end.

(** As `buffer_words//3`: the words of a buffered return into the
    buffer at `%rax`, each a full eightbyte. *)
Fixpoint buffer_words (cx : ctx) (ws : list word) (off : Z) : list line :=
  match ws with
  | [] => []
  | Wf _ s :: ws' =>
      match s with
      | SrcLower v => lower_load cx v "rcx" ++ [ins "mov" "q" [reg "rcx"; mem off "rax"]]
      | SrcAddr v | SrcVal _ v => load cx v L "d" ++ [ins "mov" "q" [reg "rdx"; mem off "rax"]]
      | _ => todo "buffer word"
      end
      ++ buffer_words cx ws' (off + eight)
  end.

(** ## Jumps *)

(** As `jump//3`: the code that ends the block from. *)
Definition jump_lines (cx : ctx) (from : name) (j : pjump) : list line :=
  match j with
  | PJump (JGoto t) => edge cx from t "j"
  | PJump (JBranch v t f) =>
      let false_label := local_label cx from "jnz" "false" in
      load cx v W "a"
      ++ [ins "test" "l" [reg "eax"; reg "eax"]; ins0 "jz" [sym false_label]]
      ++ edge cx from t "t"
      ++ [label false_label]
      ++ edge cx from f "f"
  | PJump JUnreachable => [ins0 "jmp" [sym (special_label cx "unreachable")]]
  | PJump _ => todo "a return that is not lowered"
  | PReturnValue r v p => ret_value cx r v ++ frame_pop cx ++ success p
  | PReturnBuffer ws =>
      slot_load cx KRetbuf "rax" ++ buffer_words cx ws eight
      ++ [ins "mov" "b" [imm 0; mem 0 "rax"]]
      ++ frame_pop cx ++ leave_ret
  | PReturnTyped ks vs =>
      let ws := typed_return_words ks vs in
      match result_registers (map ret_word_class ws) ["d"; "c"] ["xmm0"; "xmm1"] with
      | Some rs => typed_return_loads cx ws rs
      | None => todo "result registers"
      end
      ++ frame_pop cx ++ success Registers
  | PReturnRegisters [v1; v2] =>
      load cx v1 L "d" ++ load cx v2 L "c" ++ frame_pop cx ++ success Registers
  | PReturnRegisters _ => todo "return_registers"
  | PReturnVoid p => frame_pop cx ++ success p
  end.

(** ## Blocks *)

Fixpoint insts_lines (cx : ctx) (b : name) (i : Z) (is : list pinst) : list line :=
  match is with
  | [] => []
  | pi :: is' => inst_lines cx b i pi ++ insts_lines cx b (i + 1) is'
  end.

(** As `block_code//3`: a block's label, instructions and jump. *)
Definition block_lines (cx : ctx) (b : pblock) : list line :=
  label (block_label cx (pb_label b))
  :: insts_lines cx (pb_label b) 0 (pb_insts b)
  ++ jump_lines cx (pb_label b) (pb_jump b).

(** ## Branch selection

    As the branch selection of filc_amd64.pl (docs/perf.md). A block
    whose last instruction is an integer comparison that only the
    block's branch reads branches on the comparison's flags. A
    branch whose edge has no phi copy and no poll jumps straight to
    its block. An edge to the next block falls through. *)

(** One more occurrence of the temporary n. *)
Definition count_temp (n : name) (m : nmap Z) : nmap Z :=
  nm_add n (match nm_find n m with Some c => c + 1 | None => 1 end) m.

(** As `temp_names//1`: each occurrence of `tmp(N)` in the term t
    counted into m. The name N is not searched. *)
Fixpoint count_temps (t : term) (m : nmap Z) : nmap Z :=
  let fix count_list (ts : list term) (m : nmap Z) : nmap Z :=
    match ts with
    | [] => m
    | t :: ts' => count_list ts' (count_temps t m)
    end in
  match t with
  | TApp f args =>
      match args with
      | [n] => if String.eqb f "tmp" then count_temp n m else count_temps n m
      | _ => count_list args m
      end
  | TList ts => count_list ts m
  | TInt _ | TAtom _ => m
  end.

(** As `branch_selection/3`: how many times each temporary occurs in
    the blocks of the plan, its definition included. *)
Definition temp_uses (bs : list pblock) : nmap Z :=
  fold_left (fun m b => count_temps (pblock_term b) m) bs nm_empty.

(** As `negated/2`, on the comparison. *)
Definition negated (c : cond) : cond :=
  match c with
  | Eq => Ne | Ne => Eq
  | Slt => Sge | Sge => Slt
  | Sle => Sgt | Sgt => Sle
  | Ult => Uge | Uge => Ult
  | Ule => Ugt | Ugt => Ule
  | Le | Lt | Ge | Gt | Ord | Unord => c
  end.

(** The jump to the label l when the flags hold the comparison c. *)
Definition jump_if (c : cond) (l : string) : list line :=
  match cond_code c with
  | Some cc => [ins0 ("j" ++ cc) [sym l]]
  | None => todo "branch condition"
  end.

Definition two31 : Z := 2147483648.

(** As `integer_immediate/3`: the signed 32-bit immediate that
    stands for the constant n: always at a word, and at a long only
    when sign extension gives n back. *)
Definition integer_immediate (half : bool) (n : Z) : option Z :=
  if half then Some ((n + two31) mod two32 - two31)
  else
    let u := n mod two64 in
    let v := if u >=? two63 then u - two64 else u in
    if (- two31 <=? v) && (v <=? two31 - 1) then Some v else None.

(** As `plain_edge/2`: an edge to a block without phis, and without
    a poll. *)
Definition plain_edge (cx : ctx) (t : target) : bool :=
  match t with
  | Poll _ => false
  | To l => match nm_find l (cx_phis cx) with Some [] => true | _ => false end
  end.

(** Whether the edge goes to the next block. *)
Definition to_next (t : target) (next : option name) : bool :=
  match next with
  | Some l => name_eqb (edge_label t) l
  | None => false
  end.

(** As `selected_edge//5`: the edge without its jump when it goes to
    the next block. *)
Definition selected_edge (cx : ctx) (from : name) (t : target) (tag : string)
    (next : option name) : list line :=
  if to_next t next then edge_moves cx from t tag else edge cx from t tag.

(** As `selected_branch//6`: the flags hold c exactly when the
    branch goes to t. *)
Definition selected_branch (cx : ctx) (c : cond) (t f : target) (from : name)
    (next : option name) : list line :=
  let to_false := jump_if (negated c) (block_label cx (edge_label f)) in
  if to_next t next && plain_edge cx t && plain_edge cx f then to_false
  else if plain_edge cx t then
    jump_if c (block_label cx (edge_label t)) ++ selected_edge cx from f "f" next
  else if plain_edge cx f then
    to_false ++ selected_edge cx from t "t" next
  else
    let false_label := local_label cx from "jnz" "false" in
    jump_if (negated c) false_label
    ++ edge cx from t "t"
    ++ [label false_label]
    ++ selected_edge cx from f "f" next.

(** As the `compare` clause of `selected_jump//4`: x and y compared
    at the class k, y as an immediate when it is a constant that
    fits one. *)
Definition compare_flags (cx : ctx) (k : class) (x y : value) : list line :=
  match k with
  | W | L =>
      let half := match k with W => true | _ => false end in
      let a := reg (reg_name "a" half) in
      load cx x k "a"
      ++ match match y with Const n => integer_immediate half n | _ => None end with
         | Some v => [ins "cmp" (class_suffix half) [imm v; a]]
         | None =>
             load cx y k "c" ++ [ins "cmp" (class_suffix half) [reg (reg_name "c" half); a]]
         end
  | _ => todo "compare class"
  end.

(** The instructions before the last, and the last. *)
Fixpoint split_last {A : Type} (xs : list A) : option (list A * A) :=
  match xs with
  | [] => None
  | x :: xs' =>
      match split_last xs' with
      | None => Some ([], x)
      | Some (init, last) => Some (x :: init, last)
      end
  end.

(** As `compare_branch/5`: the instructions before a last integer
    comparison that only the block's branch reads, with the
    comparison and the two targets. *)
Definition compare_branch (uses : nmap Z) (b : pblock)
  : option (list pinst * cond * class * value * value * target * target) :=
  match pb_jump b with
  | PJump (JBranch (Tmp d) t f) =>
      match split_last (pb_insts b) with
      | Some (init, PInst (FPlain (Let d' W (Cmp c k) [x; y]))) =>
          if name_eqb d d'
             && match k with W | L => true | _ => false end
             && match nm_find d uses with Some n => n =? 2 | None => false end
          then Some (init, c, k, x, y, t, f)
          else None
      | _ => None
      end
  | _ => None
  end.

(** As `block_code//3` with selected branches: next is the label of
    the block after b. *)
Definition selected_block (cx : ctx) (uses : nmap Z) (next : option name) (b : pblock)
  : list line :=
  let from := pb_label b in
  label (block_label cx from)
  :: match compare_branch uses b with
     | Some (init, c, k, x, y, t, f) =>
         insts_lines cx from 0 init
         ++ compare_flags cx k x y
         ++ selected_branch cx c t f from next
     | None =>
         insts_lines cx from 0 (pb_insts b)
         ++ match pb_jump b with
            | PJump (JBranch v t f) =>
                load cx v W "a"
                ++ [ins "test" "l" [reg "eax"; reg "eax"]]
                ++ selected_branch cx Ne t f from next
            | PJump (JGoto t) => selected_edge cx from t "j" next
            | j => jump_lines cx from j
            end
     end.

Fixpoint selected_blocks (cx : ctx) (uses : nmap Z) (bs : list pblock) : list line :=
  match bs with
  | [] => []
  | b :: bs' =>
      selected_block cx uses (match bs' with b' :: _ => Some (pb_label b') | [] => None end) b
      ++ selected_blocks cx uses bs'
  end.

(** The code of the blocks: with selected branches, or as the
    reference, which stores a comparison's boolean, tests it and
    jumps on both arms. *)
Definition blocks_lines (selected : bool) (cx : ctx) (bs : list pblock) : list line :=
  if selected then selected_blocks cx (temp_uses bs) bs else flat_map (block_lines cx) bs.

(** ## The shared failure blocks *)

Definition kind_leb (a b : check_kind) : bool :=
  if ck_size a <? ck_size b then true
  else if ck_size b <? ck_size a then false
  else if Bool.eqb (ck_write a) (ck_write b)
       then ck_align a <=? ck_align b
       else negb (ck_write a).
Definition kind_eqb (a b : check_kind) : bool :=
  (ck_size a =? ck_size b) && Bool.eqb (ck_write a) (ck_write b) && (ck_align a =? ck_align b).

(** k into the sorted ks, once, as `sort/2` orders `k(Size, Write,
    Align)`. *)
Fixpoint kind_insert (k : check_kind) (ks : list check_kind) : list check_kind :=
  match ks with
  | [] => [k]
  | k' :: ks' =>
      if kind_eqb k k' then ks
      else if kind_leb k k' then k :: ks
      else k' :: kind_insert k ks'
  end.

(** As `inst_check_kind/2`: the kind of check an instruction's access
    needs, if it has one. *)
Definition inst_check_kind (pi : pinst) : option check_kind :=
  match pi with
  | PInst (FFused (Check _ size r align) _) => Some (mkKind size (rights_write r) align)
  | PInst (FFused (CheckLocal _ _ size r align) _) => Some (mkKind size (rights_write r) align)
  | _ => None
  end.

(** As `access_check_kinds/2`: the distinct kinds of a function, in
    order. *)
Definition access_check_kinds (bs : list pblock) : list check_kind :=
  fold_left (fun ks b =>
               fold_left (fun ks pi => match inst_check_kind pi with
                                       | Some k => kind_insert k ks
                                       | None => ks
                                       end)
                         (pb_insts b) ks)
            bs [].

(** As `check_fail_blocks//2`: a failure block for each kind, which
    calls the runtime's reporter. *)
Definition check_fail_block (cx : ctx) (k : check_kind) : list line :=
  [label (check_fail_label cx k);
   ins "mov" "q" [reg "rax"; reg "rdi"];
   ins "mov" "q" [reg "rcx"; reg "rsi"];
   ins "lea" "q" [rip (check_origin_label (cx_name cx) k); reg "rdx"];
   ins0 "call" [plt "filc_optimized_access_check_fail"];
   ins0 "ud2" []].

Definition has_dispatch (bs : list pblock) : bool :=
  existsb (fun b => existsb (fun pi => match pi with
                                       | PAbi acts =>
                                           existsb (fun a => match a with
                                                             | ADispatch _ _ _ _ _ _ _ _ _ => true
                                                             | _ => false
                                                             end) acts
                                       | _ => false
                                       end) (pb_insts b)) bs.

Definition has_unreachable (bs : list pblock) : bool :=
  existsb (fun b => match pb_jump b with PJump JUnreachable => true | _ => false end) bs.

(** As `not_function_block//2`: where a call through a pointer that
    is not a function's goes. *)
Definition not_function_block (cx : ctx) (bs : list pblock) : list line :=
  if has_dispatch bs
  then [label (special_label cx "notfn");
        ins "mov" "q" [reg "rax"; reg "rdi"];
        ins "mov" "q" [reg "rcx"; reg "rsi"];
        ins0 "call" [plt "filc_check_function_call_fail"];
        ins0 "ud2" []]
  else [].

Definition unreachable_message_label (name : string) : string :=
  ".L" ++ name ++ "..unreachable_msg".

(** As `unreachable_block//2`: `filc_error(Message, Origin)`, as
    clang's code panics at a reached unreachable. *)
Definition unreachable_block (cx : ctx) (bs : list pblock) : list line :=
  if has_unreachable bs
  then [label (special_label cx "unreachable");
        ins "lea" "q" [rip (unreachable_message_label (cx_name cx)); reg "rdi"];
        ins "lea" "q" [rip (origin_label (cx_name cx) "n"); reg "rsi"];
        ins0 "call" [plt "filc_error"];
        ins0 "ud2" []]
  else [].

Definition unreachable_message (cx : ctx) (bs : list pblock) : list line :=
  if has_unreachable bs
  then [Dir (DSection SRodata); label (unreachable_message_label (cx_name cx));
        Dir (DAsciz (LSym "llvm unreachable instruction"))]
  else [].

(** ## Origins *)

Definition long (n : Z) : line := Dir (DLong (LInt n)).
Definition zero (n : Z) : line := Dir (DZero (LInt n)).
Definition p2align (n : Z) : line := Dir (DP2align (LInt n)).

(** As `function_origin//7`: a function origin and the origin that
    points at it. *)
Definition function_origin (name name_label which : string) (nlowers can_catch nlocals : Z)
  : list line :=
  let forigin := (".L" ++ name ++ "..forigin_" ++ which)%string in
  [label forigin;
   quad_sym name_label; quad_int 0;
   long nlowers; zero 4;
   quad_int 0;
   Dir (DByte (LInt 0) [LInt can_catch]); zero 2;
   long 0; long nlocals; zero 4;
   label (origin_label name which);
   quad_sym forigin; long 0; long 0].

(** As `check_origins//2`: an origin for each kind of check. *)
Definition check_origin (name : string) (k : check_kind) : list line :=
  let origin := origin_label name "n" in
  [p2align 4; label (check_origin_label name k);
   long (ck_size k);
   Dir (DByte (LInt (ck_align k)) [LInt 0; LInt (if ck_write k then 1 else 0)]); zero 1;
   quad_sym origin; quad_sym origin; quad_int 0].

(** As `origins//3`: the name's text, the catching and the plain
    function origin, and the check origins. *)
Definition origins (cx : ctx) (p : plan) (kinds : list check_kind) : list line :=
  let name := cx_name cx in
  let name_label := (".L" ++ name ++ "..name")%string in
  let nroots := Zlength (fr_roots (pl_frame p)) in
  [Dir (DSection SRodata); label name_label; Dir (DAsciz (LSym name));
   Dir (DSection SDataRelRo); p2align 4]
  ++ function_origin name name_label "c" nroots 1 (pl_nlocals p)
  ++ function_origin name name_label "n" nroots 0 (pl_nlocals p)
  ++ flat_map (check_origin name) kinds.

(** ## The function *)

(** As `linkage_globl//2`. *)
Definition linkage_globl (linkage : term) (s : string) : list line :=
  match linkage with
  | TAtom a =>
      if String.eqb a "export" then [Dir (DGlobl (LSym s))]
      else if String.eqb a "weak" then [Dir (DWeak (LSym s))]
      else []
  | _ => []
  end.

(** As `function//2`: the implementation (the entry, the blocks, the
    shared exception exit and the failure blocks), then the function
    object and the origins. *)
Definition function_code (selected : bool) (p : plan) : list line :=
  let cx := plan_ctx p in
  let impl := impl_symbol (pl_sig p) (cx_name cx) in
  let bs := pl_blocks p in
  let kinds := access_check_kinds bs in
  [Dir (DSection SText); p2align 4]
  ++ linkage_globl (pl_linkage p) impl
  ++ [Dir (DType (LSym impl) (LSym "function")); label impl]
  ++ entry_lines cx p
  ++ blocks_lines selected cx bs
  ++ [label (special_label cx "exc")]
  ++ exit_lines cx (pl_return p)
  ++ flat_map (check_fail_block cx) kinds
  ++ not_function_block cx bs
  ++ unreachable_block cx bs
  ++ [Dir (DSize (LSym impl))]
  ++ function_object_lines cx p impl
  ++ origins cx p kinds
  ++ unreachable_message cx bs.

(** The reference: no branch is selected. *)
Definition function_lines : plan -> list line := function_code false.
