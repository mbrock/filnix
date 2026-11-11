(** # Escape classification of allocs

    As escape.pl, on terms: which temporaries of a function hold the
    address of an alloc at a known offset ([address_temps]), and, for
    each alloc, whether its address is only used for loads and stores
    at such offsets ([alloc_classes]). Promote.v turns the slots of
    such an alloc into temporaries.

    The analysis rests on one fact: a local alloc can only be reached
    through its own address, so no other pointer or integer can name
    it. Offsets are exact integers.

    escape.pl also says why an alloc escapes; no pass reads that, so
    it is left out. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality, written as Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Widths *)

(** As ir.pl's `width_bytes(W, Bytes)`: the bytes of the width w. *)
Definition width_bytes (w : term) : option Z :=
  match w with
  | TAtom a =>
      if a == "b" then Some 1
      else if a == "h" then Some 2
      else if (a == "w") || (a == "s") then Some 4
      else if (a == "l") || (a == "p") || (a == "d") then Some 8
      else if a == "x" then Some 10
      else None
  | _ => None
  end.

(** As `slot_load_width(T, W)`: the width a load of the type t
    reads. None for a type whose load is no slot access, as `x`. *)
Definition slot_load_width (t : term) : option term :=
  match t with
  | TAtom a =>
      if (a == "l") || (a == "p") || (a == "s") || (a == "d") then Some t
      else if (a == "sw") || (a == "uw") then Some (TAtom "w")
      else if (a == "sh") || (a == "uh") then Some (TAtom "h")
      else if (a == "sb") || (a == "ub") then Some (TAtom "b")
      else None
  | _ => None
  end.

(** ## Instructions *)

(** The destination, class, op and arguments when the term i is
    `let(D, K, Op, Args)`. *)
Definition let_parts (i : term) : option (term * term * term * list term) :=
  match i with
  | TApp f [d; k; o; TList args] => if f == "let" then Some (d, k, o, args) else None
  | _ => None
  end.

(** Whether the op o is an `alloc(Align)`. *)
Definition is_alloc (o : term) : bool :=
  match o with TApp g [_] => g == "alloc" | _ => false end.

(** The integer n when the value v is `const(N)`. *)
Definition const_int (v : term) : option Z :=
  match v with
  | TApp f [TInt n] => if f == "const" then Some n else None
  | _ => None
  end.

(** As `offset_of(Inst, X, N)`: the instruction i gives its
    destination the value of the temporary x plus the constant n. *)
Definition offset_of (i : term) : option (term * Z) :=
  match let_parts i with
  | Some (_, _, TAtom o, args) =>
      match args with
      | [a; b] =>
          if o == "add" then
            match tmp_name a, const_int b, const_int a, tmp_name b with
            | [x], Some n, _, _ => Some (x, n)
            | _, _, Some n, [x] => Some (x, n)
            | _, _, _, _ => None
            end
          else if o == "sub" then
            match tmp_name a, const_int b with
            | [x], Some n => Some (x, - n)
            | _, _ => None
            end
          else None
      | [a] =>
          if o == "copy" then match tmp_name a with [x] => Some (x, 0) | _ => None end
          else None
      | _ => None
      end
  | _ => None
  end.

(** ## Address temporaries *)

(** For each temporary that holds an address of an alloc: the alloc's
    temporary, the root, and the offset from it. *)
Definition addresses : Type := nmap (term * Z).

(** The root and the offset when the value v is an address
    temporary. *)
Definition address_of (addrs : addresses) (v : term) : list (term * Z) :=
  flat_map (fun x => match nm_find x addrs with Some r => [r] | None => [] end) (tmp_name v).

(** The edges from the temporary x: the position, the destination
    and the constant of each instruction that adds a constant to x. *)
Definition edges_at (m : nmap (list (Z * term * Z))) (x : term) : list (Z * term * Z) :=
  match nm_find x m with Some es => es | None => [] end.

(** Of the pairs ps, sorted by key, the first with each key. *)
Fixpoint first_of_key {A : Type} (ps : list (term * A)) : list (term * A) :=
  match ps with
  | [] => []
  | p :: ps' =>
      match first_of_key ps' with
      | [] => [p]
      | q :: rest => if term_eqb (fst p) (fst q) then p :: rest else p :: q :: rest
      end
  end.

(** As `layers_addrs/4`: the addresses addrs and those derived from
    the temporaries of layer, layer by layer. A temporary that two
    instructions of a layer define takes the first one's source.
    Every layer but the last adds a temporary that an instruction
    defines, so a fuel of their number, and one, is enough. *)
Fixpoint layers_addrs (fuel : nat) (by_source : nmap (list (Z * term * Z)))
    (layer : list (term * (term * Z))) (addrs : addresses) : addresses :=
  match fuel, layer with
  | O, _ => addrs
  | _, [] => addrs
  | S fuel', _ =>
      let found :=
        flat_map (fun e =>
                    flat_map (fun edge =>
                                let d := snd (fst edge) in
                                if nm_mem d addrs then []
                                else [(fst (fst edge),
                                       (d, (fst (snd e), snd (snd e) + snd edge)))])
                             (edges_at by_source (fst e))) layer in
      let ordered := map snd (msort (fun a b => Z.compare (fst a) (fst b)) found) in
      let new := first_of_key (msort (fun a b => term_compare (fst a) (fst b)) ordered) in
      layers_addrs fuel' by_source new
                   (fold_left (fun m p => nm_add (fst p) (snd p) m) new addrs)
  end.

(** As `address_temps(F, Addrs)`: the address temporaries of the
    blocks bs. The temporary of each alloc is its own root, at offset
    0; a temporary defined as an address plus or minus a constant, or
    as its copy, is an address too. None when two allocs define one
    temporary, where `list_to_assoc/2` throws. *)
Definition address_temps (bs : list tblock) : option addresses :=
  let insts := flat_map tb_insts bs in
  let allocs :=
    flat_map (fun i => match let_parts i with
                       | Some (d, _, o, _) => if is_alloc o then tmp_name d else []
                       | None => []
                       end) insts in
  let* addrs0 :=
    fold_left (fun acc a =>
                 let* m := acc in
                 if nm_mem a m then None else Some (nm_add a (a, 0) m))
              allocs (Some nm_empty) in
  let by_source :=
    fold_left (fun m pi =>
                 match let_parts (snd pi), offset_of (snd pi) with
                 | Some (d, _, _, _), Some (x, n) =>
                     match tmp_name d with
                     | [d] => nm_add x ((fst pi, d, n) :: edges_at m x) m
                     | _ => m
                     end
                 | _, _ => m
                 end)
              (rev' (numbered 0 insts)) nm_empty in
  Some (layers_addrs (S (length insts)) by_source
                     (map (fun a => (a, (a, 0))) (nsort allocs)) addrs0).

(** ## Classes *)

(** An access `acc(Off, W)`: the bytes of the width w at the offset
    off of an alloc. *)
Definition acc : Type := (Z * term)%type.

(** The standard order of two accesses, as terms `acc(Off, W)`. *)
Definition acc_compare (a b : acc) : comparison :=
  thenc (Z.compare (fst a) (fst b)) (term_compare (snd a) (snd b)).

(** Whether a and b are the same access. *)
Definition acc_eqb (a b : acc) : bool :=
  (fst a =? fst b) && term_eqb (snd a) (snd b).

(** The accesses the map m has for the alloc a, none if it has no
    entry. *)
Definition accs_at (m : nmap (list acc)) (a : term) : list acc :=
  match nm_find a m with Some xs => xs | None => [] end.

(** What an instruction does to an alloc, the root: an access, or,
    with None, a use that lets its address escape. *)
Definition event : Type := (term * option acc)%type.

(** An escape for each address among the values vs. *)
Definition escapes_of (addrs : addresses) (vs : list term) : list event :=
  map (fun r => (fst r, None)) (flat_map (address_of addrs) vs).

(** Whether the op o is of a kind whose address arguments escape
    (`kind_event/4`): the arithmetic, a copy, the conversions between
    pointers and integers, `va_args` and `va_arg`, setjmp, a
    comparison, the extension of a narrow integer and an alloc. *)
Definition escaping_op (o : term) : bool :=
  match o with
  | TAtom a =>
      existsb (String.eqb a)
              ["add"; "sub"; "mul"; "div"; "udiv"; "rem"; "urem"; "and"; "or"; "xor";
               "sar"; "shr"; "shl"; "neg"; "select"; "copy"; "ptoi"; "itop"; "va_args"; "va_arg"]
  | TApp g [x] =>
      if g == "setjmp" then is_atom "setjmp" x || is_atom "_setjmp" x || is_atom "sigsetjmp" x
      else if g == "ext" then
        match x with
        | TAtom a => match narrow_bytes a with Some _ => true | None => false end
        | _ => false
        end
      else g == "alloc"
  | TApp g [_; _] => g == "cmp"
  | _ => false
  end.

(** As `inst_event(Inst, Addrs, Event)`: the events of the
    instruction i.

    - A load from an address is an access of the type's width, or an
      escape for a type with none.
    - A store to an address is an access; a store of an address lets
      it escape.
    - An address that an atomic access, a compare-and-swap, an
      `access`, an `asm_fixed` or a call reads escapes.
    - So does an address argument of an op of [escaping_op], but in
      an instruction that derives an address from an address
      ([offset_of]).
    - A `va_arg` of an address is, besides, an access of a pointer. *)
Definition inst_events (addrs : addresses) (i : term) : list event :=
  match i with
  | TApp f xs =>
      if f == "let" then
        match xs with
        | [_; _; o; TList args] =>
            let by_kind :=
              if escaping_op o
                 && negb (match offset_of i with
                          | Some (y, _) => nm_mem y addrs
                          | None => false
                          end)
              then escapes_of addrs args else [] in
            match o with
            | TApp g [t] =>
                if g == "load" then
                  match args with
                  | [a] => map (fun r => (fst r, option_map (fun w => (snd r, w))
                                                            (slot_load_width t)))
                               (address_of addrs a)
                  | _ => []
                  end
                else if g == "atomic_load" then
                  match args with [a] => escapes_of addrs [a] | _ => [] end
                else if g == "cas" then escapes_of addrs args
                else by_kind
            | TAtom a =>
                match args with
                | [x] =>
                    if a == "va_arg"
                    then by_kind ++ map (fun r => (fst r, Some (snd r, TAtom "p")))
                                        (address_of addrs x)
                    else by_kind
                | _ => by_kind
                end
            | _ => by_kind
            end
        | _ => []
        end
      else if f == "store" then
        match xs with
        | [w; v; a] =>
            escapes_of addrs [v]
            ++ map (fun r => (fst r, Some (snd r, w))) (address_of addrs a)
        | _ => []
        end
      else if f == "atomic_store" then
        match xs with [_; v; a] => escapes_of addrs [v; a] | _ => [] end
      else if f == "access" then
        match xs with [_; a; _; _] => escapes_of addrs [a] | _ => [] end
      else if f == "asm_fixed" then
        match xs with
        | [_; TList ins; _] => escapes_of addrs (flat_map pair_value ins)
        | _ => []
        end
      else if f == "call" then
        match xs with
        | [_; g; TList args] => escapes_of addrs (g :: flat_map arg_value args)
        | _ => []
        end
      else []
  | _ => []
  end.

(** As `jump_value(Jump, V)`: the values the jump j reads. *)
Definition jump_values (j : term) : list term :=
  match j with
  | TApp f [v; _; _] => if f == "branch" then [v] else []
  | TApp f [v] => if f == "ret" then [v] else if f == "rets" then listed v else []
  | _ => []
  end.

(** Every definition of a temporary in a function: by a param, a
    phi, a `let`, a call or an `asm_fixed`. A temporary defined twice
    is there twice. *)
Definition all_defs (params : list term) (bs : list tblock) : list term :=
  flat_map param_def params
  ++ flat_map (fun b => flat_map phi_def (tb_phis b) ++ flat_map counted_defs (tb_insts b)) bs.

(** As `alloc_classes(F, Addrs, DefCounts, Classes)`: for each
    `let(tmp(A), _, alloc(_), [Size])` of the blocks bs, in their
    order, the temporary a, the size and the class: None when the
    address escapes, or else the ordset of the alloc's accesses,
    `local(Size, Accs)`. Besides the instructions' events, an address
    escapes as a phi argument, as a jump's value, and when its
    temporary has two definitions. *)
Definition alloc_classes (addrs : addresses) (counts : nmap nat) (params : list term)
    (bs : list tblock) : list (term * term * option (list acc)) :=
  let insts := flat_map tb_insts bs in
  let twice d := match nm_find d counts with Some n => Nat.ltb 1 n | None => false end in
  let events :=
    flat_map (inst_events addrs) insts
    ++ flat_map (fun b =>
                   flat_map (fun p => match p with
                                      | TApp f [_; _; TList args] =>
                                          if f == "phi"
                                          then escapes_of addrs (flat_map pair_value args)
                                          else []
                                      | _ => []
                                      end) (tb_phis b)) bs
    ++ flat_map (fun b => escapes_of addrs (jump_values (tb_jump b))) bs
    ++ escapes_of addrs (map tmp (filter twice (all_defs params bs))) in
  let escaped :=
    fold_left (fun m e => match snd e with
                          | None => nm_add (fst e) tt m
                          | Some _ => m
                          end) events nm_empty in
  let accessed :=
    fold_left (fun m e => match snd e with
                          | Some a => nm_add (fst e) (a :: accs_at m (fst e)) m
                          | None => m
                          end) events nm_empty in
  flat_map (fun i => match let_parts i with
                     | Some (d, _, o, [size]) =>
                         if is_alloc o then
                           map (fun a => (a, size,
                                          if nm_mem a escaped then None
                                          else Some (sort acc_compare (accs_at accessed a))))
                               (tmp_name d)
                         else []
                     | _ => []
                     end) insts.
