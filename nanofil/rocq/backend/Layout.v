(** Where a function's plan lives below `%rbp`, and the names its code
    uses: filc_amd64.pl's `layout/4`, its function context, its
    labels and `abi_symbol/3`, with the short ways to write a line
    that the emission (Emit.v and the files it calls) is built from.

    Emission is total: where the Prolog compiler would fail or reach
    a form this port does not have yet, the code holds a [todo] line,
    which is not an instruction. The driver emits no function that
    has one. *)
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Text Asm Plan PlanTerm.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Lines *)

Definition ins (op suffix : string) (os : list operand) : line := Ins op (Some suffix) os.
Definition ins0 (op : string) (os : list operand) : line := Ins op None os.
Definition reg (r : string) : operand := OReg r.
Definition imm (n : Z) : operand := OImm (ELit (LInt n)).
Definition mem (d : Z) (b : string) : operand := OMem (LInt d) b.
Definition rip (s : string) : operand := ORip (ELit (LSym s)).
Definition sym (s : string) : operand := OSym (ELit (LSym s)).
Definition plt (s : string) : operand := OPlt (LSym s).
Definition gotpcrel (s : string) : operand := OGotpcrel (LSym s).
Definition label (s : string) : line := Label (LSym s).
Definition quad_sym (s : string) : line := Dir (DQuad (ELit (LSym s))).
Definition quad_int (n : Z) : line := Dir (DQuad (ELit (LInt n))).

(** The mnemonic of a [todo] line. *)
Definition todo_op : string := "todo".

(** A place in the code for what, which this port does not emit: a
    form not ported yet, or one the Prolog compiler has no code for
    (a slot the frame lacks, a class an operation does not take). *)
Definition todo (what : string) : list line := [ins0 todo_op [sym what]].

(** Whether a line is a [todo]. *)
Definition is_todo (l : line) : bool :=
  match l with
  | Ins op None _ => String.eqb op todo_op
  | _ => false
  end.

(** The first thing lines leave undone, if any. *)
Fixpoint first_todo (ls : list line) : option string :=
  match ls with
  | [] => None
  | l :: ls' =>
      if is_todo l
      then match l with
           | Ins _ _ [OSym (ELit (LSym what))] => Some what
           | _ => Some ""
           end
      else first_todo ls'
  end.

(** ## Names *)

(** The text of a name as `format`'s `~w` writes it: an atom or an
    integer as it is, anything else in canonical form. *)
Fixpoint name_text (t : term) : string :=
  match t with
  | TAtom a => a
  | TInt n => decimal n
  | TApp f args => f ++ "(" ++ String.concat "," (map name_text args) ++ ")"
  | TList xs => "[" ++ String.concat "," (map name_text xs) ++ "]"
  end.

(** As `abi_symbol/3`: the names under which code finds a function f
    or a global: its implementation for the signature sig and the
    public alias of it, its getter, its function object, its data
    object and aux array. *)
Definition impl_symbol (sig : Z) (f : string) : string :=
  "pizlonatedFIP" ++ decimal sig ++ "_" ++ f.
Definition entry_symbol (sig : sigref) (f : string) : string :=
  match sig with
  | SigNumber n => "pizlonatedFI" ++ decimal n ++ "_" ++ f
  | SigNever r a => "pizlonatedFIN" ++ decimal r ++ "_" ++ decimal a ++ "_" ++ f
  end.
Definition getter_symbol (f : string) : string := "pizlonated_" ++ f.
Definition function_object_symbol (f : string) : string := "pizlonatedFO_" ++ f.
Definition data_object_symbol (f : string) : string := "pizlonatedDO_" ++ f.
Definition data_aux_symbol (f : string) : string := "pizlonatedDA_" ++ f.

(** As `struct_field/3`: the offsets of the thread's fields and of a
    function object's. *)
Definition thread_stack_limit : Z := 0.
Definition thread_state : Z := 8.
Definition thread_top_frame : Z := 16.
Definition thread_cc_inline_buffer : Z := 128.
Definition thread_cc_inline_aux_buffer : Z := 384.
Definition thread_cc_outline_buffer : Z := 640.
Definition thread_cc_outline_aux_buffer : Z := 648.
Definition thread_cc_outline_size : Z := 656.
Definition function_object_fast_entry : Z := 0.
Definition function_object_generic_entry : Z := 8.
Definition function_object_signature : Z := 16.

(** ## The frame *)

(** n rounded up to a multiple of 16. *)
Definition sixteen : Z := 16.
Definition fifteen : Z := 15.
Definition eight : Z := 8.
Definition round16 (n : Z) : Z := (n + fifteen) / sixteen * sixteen.

(** Where a named local is: its payload at `-payload(%rbp)`, 16
    aligned, and its aux, a count and then a lower for each word, at
    `-aux(%rbp)`. *)
Record local_slot : Type := mkLocalSlot {
  ls_payload : Z;
  ls_aux : Z;
  ls_size : Z;
  ls_padded : Z
}.

(** As `ctx(f(Name, Ret, Slots, Blocks), Size, FrameBase, Labels, _)`:
    what the code of a function reads of it. A slot's number n means
    `-n(%rbp)`. The frame record the collector walks is at
    `-base(%rbp)`: its parent, its origin, then `lowers[]`. *)
Record ctx : Type := mkCtx {
  cx_name : string; (* the function's name, the stem of its labels *)
  cx_slots : nmap Z; (* each key's slot, by [key_term] *)
  cx_locals : nmap local_slot; (* each named local, by its name *)
  cx_size : Z; (* the bytes `sub`tracted from `%rsp` *)
  cx_base : Z;
  cx_phis : nmap (list phi) (* each block's phis, by its label *)
}.

(** As `plain_slot/3`: place one payload key after off bytes. *)
Definition plain_slot (st : nmap Z * nmap local_slot * Z) (k : key)
  : nmap Z * nmap local_slot * Z :=
  let '(slots, locals, off) := st in
  match k with
  | KLocal x size =>
      let padded := round16 size in
      let payload := round16 (off + padded) in
      let aux := payload + padded + eight in
      (slots, nm_add x (mkLocalSlot payload aux size padded) locals, aux)
  | KStorage PoolWide _ => (nm_add (key_term k) (off + sixteen) slots, locals, off + sixteen)
  | _ => (nm_add (key_term k) (off + eight) slots, locals, off + eight)
  end.

(** As `lower_slot/4`: the root k is `lowers[i]`. *)
Definition lower_slot (base : Z) (st : nmap Z * Z) (k : key) : nmap Z * Z :=
  let '(slots, i) := st in
  (nm_add (key_term k) (base - sixteen - eight * i) slots, i + 1).

(** As `layout/4` and `function_ctx/8`: the context of a plan. An
    alias whose key has no slot gets none. *)
Definition plan_ctx (p : plan) : ctx :=
  let fr := pl_frame p in
  let '(slots1, locals, plain_bytes) :=
    fold_left plain_slot (fr_plain fr) (nm_empty, nm_empty, 0) in
  let base := plain_bytes + sixteen + eight * Zlength (fr_roots fr) in
  let '(slots2, _) := fold_left (lower_slot base) (fr_roots fr) (slots1, 0) in
  let slots :=
    fold_left (fun m a => match nm_find (key_term (snd a)) slots2 with
                          | Some off => nm_add (key_term (fst a)) off m
                          | None => m
                          end)
              (fr_aliases fr) slots2 in
  mkCtx (name_text (pl_name p)) slots locals (round16 base) base
        (nm_of_list (map (fun b => (pb_label b, pb_phis b)) (pl_blocks p))).

(** As `ctx_slot/3`. *)
Definition slot (cx : ctx) (k : key) : option Z := nm_find (key_term k) (cx_slots cx).

(** The lines f gives for k's slot. *)
Definition with_slot (cx : ctx) (k : key) (f : Z -> list line) : list line :=
  match slot cx k with
  | Some off => f off
  | None => todo "no slot"
  end.

(** As `reg_slot_store//3`: the store of the register r into k's
    slot. *)
Definition slot_store (cx : ctx) (r : string) (k : key) : list line :=
  with_slot cx k (fun off => [ins "mov" "q" [reg r; mem (- off) "rbp"]]).

(** As `slot_reg_load//3`: the load of k's slot into the register
    r. *)
Definition slot_load (cx : ctx) (k : key) (r : string) : list line :=
  with_slot cx k (fun off => [ins "mov" "q" [mem (- off) "rbp"; reg r]]).

(** ## Labels *)

(** As `special_label/3`: a label shared by the whole function. *)
Definition special_label (cx : ctx) (tag : string) : string :=
  ".L" ++ cx_name cx ++ ".." ++ tag.

(** As `block_label/3`. *)
Definition block_label (cx : ctx) (l : name) : string :=
  ".L" ++ cx_name cx ++ "." ++ name_text l.

(** As `local_label/5`: a label inside the code of the instruction
    index of a block, or of its jump. *)
Definition local_label (cx : ctx) (block : name) (index tag : string) : string :=
  ".L" ++ cx_name cx ++ "." ++ name_text block ++ ".." ++ index ++ "." ++ tag.

(** As `origin_label/3`: the frame's origin, which is `c` at calls
    and `n` at pollchecks and checks. *)
Definition origin_label (name which : string) : string :=
  ".L" ++ name ++ "..origin_" ++ which.

(** ## Registers and values *)

(** As `reg_name/3`: the name of the short register r at a class, as
    integers have it; a float's bits travel in the same registers. *)
Definition reg64 (r : string) : string :=
  if String.eqb r "a" then "rax" else if String.eqb r "c" then "rcx"
  else if String.eqb r "d" then "rdx" else if String.eqb r "si" then "rsi"
  else if String.eqb r "di" then "rdi" else r.
Definition reg32 (r : string) : string :=
  if String.eqb r "a" then "eax" else if String.eqb r "c" then "ecx"
  else if String.eqb r "d" then "edx" else if String.eqb r "si" then "esi"
  else if String.eqb r "di" then "edi" else r ++ "d".

(** Whether a class is 32 bits wide in a register, or 64; nothing for
    the classes with no register form. *)
Definition class_half (k : class) : option bool :=
  match k with
  | W | Single => Some true
  | L | Double => Some false
  | _ => None
  end.

Definition reg_name (r : string) (half : bool) : string := if half then reg32 r else reg64 r.

(** As `att_suffix/2` at a class. *)
Definition class_suffix (half : bool) : string := if half then "l" else "q".

Definition two32 : Z := 4294967296.
Definition two63 : Z := 9223372036854775808.
Definition two64 : Z := 18446744073709551616.

(** As amd64.pl's `load//4`: the code that puts the value v, read at
    the class k, in the short register r. A global's address is the
    same at every class. *)
Definition load (cx : ctx) (v : value) (k : class) (r : string) : list line :=
  match v, class_half k with
  | Global g, _ => [ins "lea" "q" [rip (name_text g); reg (reg64 r)]]
  | _, None => todo "load class"
  | Tmp n, Some half =>
      with_slot cx (KTmp n)
        (fun off => [ins "mov" (class_suffix half) [mem (- off) "rbp"; reg (reg_name r half)]])
  | Const n, Some half =>
      if half then [ins "mov" "l" [imm (n mod two32); reg (reg32 r)]]
      else let u := n mod two64 in
           [ins "movabs" "q" [imm (if u >=? two63 then u - two64 else u); reg (reg64 r)]]
  end.

(** As `lower_reg_load//3`: the lower of a `p` value into the
    register r: its root's, or 0 for a constant. *)
Definition lower_load (cx : ctx) (v : value) (r : string) : list line :=
  match v with
  | Tmp n => slot_load cx (KLower (KTmp n)) r
  | Const _ => [ins "mov" "q" [imm 0; reg r]]
  | Global _ => todo "lower of a global"
  end.

(** As `flight_load//2`: a `p` value's address into `%rax` and its
    lower into `%rcx`. *)
Definition flight_load (cx : ctx) (v : value) : list line :=
  load cx v L "a" ++ lower_load cx v "rcx".

(** As `flight_store//2`: the pointer in `%rax` and `%rcx` into the
    temporary d and its root. *)
Definition flight_store (cx : ctx) (d : name) : list line :=
  slot_store cx "rax" (KTmp d) ++ slot_store cx "rcx" (KLower (KTmp d)).

(** As `origin_store//2`: the store of the `c` or `n` origin into
    the frame record. *)
Definition origin_store (cx : ctx) (which : string) : list line :=
  [ins "lea" "q" [rip (origin_label (cx_name cx) which); reg "rax"];
   ins "mov" "q" [reg "rax"; mem (eight - cx_base cx) "rbp"]].

(** As `to_xmm//3` and `from_xmm//3`: a float's bits between the
    short register r and an xmm register. *)
Definition xmm_move (k : class) : string := match k with Single => "movd" | _ => "movq" end.
Definition to_xmm (k : class) (r x : string) : list line :=
  [ins0 (xmm_move k) [reg (reg_name r (match k with Single => true | _ => false end)); reg x]].
Definition from_xmm (k : class) (x r : string) : list line :=
  [ins0 (xmm_move k) [reg x; reg (reg_name r (match k with Single => true | _ => false end))]].

(** As `target_form/2`: the bytes of stack a buffered return of n
    words takes around a call. *)
Definition buffer_bytes (n : Z) : Z := round16 (eight + eight * n).

(** ## More operands *)

(** `D(%B,%I)`. *)
Definition mem_index (d : Z) (b i : string) : operand := OMemIndex (LInt d) b i.

(** `S+N(%rip)`. *)
Definition rip_plus (s : string) (n : Z) : operand :=
  ORip (EAdd (ELit (LSym s)) (ELit (LInt n))).

(** `*O`, the target of an indirect call. *)
Definition ind (o : operand) : operand := OInd o.

(** ## The fast convention *)

(** As `form_short_regs/2`: the integer registers that carry a call's
    words, by the return's protocol. A buffered return's buffer takes
    `%rdx`'s place. *)
Definition form_short_regs (r : protocol) : list string :=
  match r with
  | Registers => ["d"; "c"; "r8"; "r9"]
  | Buffer _ => ["c"; "r8"; "r9"]
  end.

(** Where a word of a call travels. *)
Inductive location : Type :=
| LocReg (r : string) (* the short register r *)
| LocXmm (x : string) (* an xmm register *)
| LocStack (i : Z). (* the stack word i, at `8i(%rsp)` at the call *)

(** As amd64.pl's `float_class/1`. *)
Definition float_class (k : class) : bool :=
  match k with Single | Double => true | _ => false end.

Definition xmm_reg (i : Z) : string := "xmm" ++ decimal i.

(** The register of a word of a returned tuple: `gpr(G)` or
    `xmm(K, X)`. *)
Inductive result_reg : Type :=
| RrGpr (g : string)
| RrXmm (k : class) (x : string).

(** As `result_registers/4`: integer words in the registers gs in
    order, float words in xs. A float word with no xmm register left
    takes an integer one, as the second clause gives it; nothing if
    the integer ones run out. *)
Fixpoint result_registers (ks : list class) (gs xs : list string) : option (list result_reg) :=
  match ks with
  | [] => Some []
  | k :: ks' =>
      match (if float_class k then xs else []) with
      | x :: xs' => option_map (cons (RrXmm k x)) (result_registers ks' gs xs')
      | [] =>
          match gs with
          | g :: gs' => option_map (cons (RrGpr g)) (result_registers ks' gs' xs)
          | [] => None
          end
      end
  end.

(** A tuple's third float word has no xmm register and takes an
    integer one. *)
Example result_registers_floats :
  result_registers [Double; L; Double; Double] ["rdx"; "rcx"] ["xmm0"; "xmm1"]
  = Some [RrXmm Double "xmm0"; RrGpr "rdx"; RrXmm Double "xmm1"; RrGpr "rcx"].
Proof. reflexivity. Qed.

(** As `bank_locations/7`: each class's location, then the count of
    stack words and of xmm registers. *)
Fixpoint bank_locations (ks : list class) (rs : list string) (x s : Z)
  : list location * Z * Z :=
  match ks with
  | [] => ([], s, x)
  | k :: ks' =>
      if float_class k
      then if x <? eight
           then let '(ls, ns, nx) := bank_locations ks' rs (x + 1) s in
                (LocXmm (xmm_reg x) :: ls, ns, nx)
           else let '(ls, ns, nx) := bank_locations ks' rs x (s + 1) in
                (LocStack s :: ls, ns, nx)
      else match rs with
           | r :: rs' =>
               let '(ls, ns, nx) := bank_locations ks' rs' x s in (LocReg r :: ls, ns, nx)
           | [] =>
               let '(ls, ns, nx) := bank_locations ks' [] x (s + 1) in (LocStack s :: ls, ns, nx)
           end
  end.

Definition word_class (w : word) : class := match w with Wf k _ => k end.

(** As `typed_locations/5`. *)
Definition typed_locations (ws : list word) (r : protocol) : list location * Z * Z :=
  bank_locations (map word_class ws) (form_short_regs r) 0 0.

(** As `stack_bytes/2`: n stack words keep `%rsp` 16 aligned. *)
Definition stack_bytes (n : Z) : Z := (n + 1) / 2 * sixteen.

(** ## Check kinds *)

(** As `k(Size, Write, Align)`: what an access check tests, which
    names its failure block and its origin. *)
Record check_kind : Type := mkKind { ck_size : Z; ck_write : bool; ck_align : Z }.

Definition kind_text (k : check_kind) : string :=
  decimal (ck_size k) ++ "." ++ (if ck_write k then "1" else "0") ++ "." ++ decimal (ck_align k).

(** As `check_fail_label/3` and `check_origin_label/3`. *)
Definition check_fail_label (cx : ctx) (k : check_kind) : string :=
  ".L" ++ cx_name cx ++ "..fail." ++ kind_text k.
Definition check_origin_label (name : string) (k : check_kind) : string :=
  ".L" ++ name ++ "..chk." ++ kind_text k.
