(** # Pizlonation

    As pizlonate.pl's `pizlonate_module/2`: from the unchecked IR to
    the [[stage|checked]] IR, the form the backend compiles. Each
    access at a `p` address becomes a [[check]], whose class `a`
    result is the proven address, and the raw access that reads it;
    each pure pointer operation becomes a [[flight]]; and every edge
    to a block at or before its source in block order becomes a
    [[poll|poll edge]]. The table at the head of pizlonate.pl gives
    each row.

    The pass is on terms, as the Prolog one is, and for the same
    reason: it rewrites a handful of instruction forms and leaves
    every other term as it is, whatever it is. So a function with an
    instruction the model has no constructor for is pizlonated like
    any other, and Transport.v's `decode_module` then keeps it as its
    checked term ([IOutside]), the very term Prolog gives. The
    unchecked stage needs no inductive of its own.

    What pizlonate.pl does besides is left out, because the module
    the backend compiles has no context items:

    - the records of where each check and poll came from
      (`checked_origins/4`, `remap_sites/3`);
    - the origins that `legacy_context/2` makes of `loc(File, Line)`
      markers. The markers themselves are dropped here, as there.

    [pizlonate_module] gives None where `pizlonate_module/2` fails
    or throws: an item, block or jump of no known shape, a jump to a
    label no block has, or two blocks of one function with one
    label. The gate (tests/pizlonate.sh) holds the result to the
    term `nanofil pizlonate-terms` prints. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Validate.
From Backend Require Import Text.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** String equality, written as Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Small terms *)

(** Whether the term t is the atom a. *)
Definition is_atom (a : string) (t : term) : bool :=
  match t with TAtom b => a == b | _ => false end.

(** Whether the list xs has n terms: the arity of a compound. *)
Definition arity (n : nat) (xs : list term) : bool := Nat.eqb (length xs) n.

(** The [[temporary]] named q, as ir.pl writes it: `tmp(Q)`. *)
Definition tmp (q : term) : term := TApp "tmp" [q].

(** The name d when the term t is `tmp(D)`. *)
Definition tmp_name (t : term) : list term :=
  match t with TApp f [d] => if f == "tmp" then [d] else [] | _ => [] end.

(** ## The size and alignment of an access *)

(** As `narrow_type/3`: the bytes of the narrow integer type a. *)
Definition narrow_bytes (a : string) : option Z :=
  if (a == "sw") || (a == "uw") then Some 4
  else if (a == "sh") || (a == "uh") then Some 2
  else if (a == "sb") || (a == "ub") then Some 1
  else None.

(** As `cas_type/1` and `cas_bytes/2`: the bytes a [[cas]] of type t
    compares and swaps. *)
Definition cas_bytes (t : term) : option Z :=
  match t with
  | TAtom a => if (a == "l") || (a == "p") then Some 8 else narrow_bytes a
  | _ => None
  end.

(** As the first answer of `access_size_align/3`: a load of type x or
    a store of width x accesses so many bytes at an address that must
    be so aligned: 8 for a pointer, whose capability is in the
    [[aux]] word of its 8-byte slot, the width for a [[cas]], else
    1. No x has two answers. *)
Definition size_align (x : term) : option (Z * Z) :=
  match x with
  | TAtom a =>
      if a == "p" then Some (8, 8)
      else if a == "x" then Some (10, 8)
      else if a == "b" then Some (1, 1)
      else if a == "h" then Some (2, 1)
      else if (a == "w") || (a == "s") then Some (4, 1)
      else if (a == "l") || (a == "d") then Some (8, 1)
      else option_map (fun n => (n, 1)) (narrow_bytes a)
  | TApp f [t] => if f == "cas" then option_map (fun n => (n, n)) (cas_bytes t) else None
  | _ => None
  end.

(** ## An access and its check *)

(** A list of memory effects, as `pointer_memory_effects/2` writes
    it. *)
Definition effects (es : list string) : term := TList (map TAtom es).

(** `pointer_memory_effects(load, Es)`. *)
Definition load_effects : term := effects ["aux_read"; "lower_resolve"; "address_read"].

(** `pointer_memory_effects(store, Es)`. *)
Definition store_effects : term :=
  effects ["aux_ensure"; "lower_barrier"; "rooted_reload"; "lower_write"; "address_write"].

(** `pointer_memory_effects(local_load, Es)`. *)
Definition local_load_effects : term := effects ["aux_read"; "address_read"].

(** `pointer_memory_effects(local_store, Es)`. *)
Definition local_store_effects : term := effects ["lower_write"; "address_write"].

(** `let(tmp(Q), a, check(0, Size, Rights, Align), [A])`: the
    [[check]] of an access of size bytes at the address a, whose
    proof is q. *)
Definition check_inst (q size rights align a : term) : term :=
  TApp "let" [tmp q; TAtom "a"; TApp "check" [TInt 0; size; rights; align]; TList [a]].

(** [check_inst] for a size and alignment that [size_align] gave. *)
Definition check_sized (q : term) (size : Z) (rights : string) (align : Z) (a : term) : term :=
  check_inst q (TInt size) (TAtom rights) (TInt align) a.

(** `let(tmp(Q), a, check_local(X, Off, Size, Rights, Align), [])`:
    the check of an access to the local x at the offset off. *)
Definition check_local_inst (q x off : term) (size : Z) (rights : string) (align : Z) : term :=
  TApp "let" [tmp q; TAtom "a";
              TApp "check_local" [x; off; TInt size; TAtom rights; TInt align]; TList []].

(** `let(D, p, raw_load_pointer(0, Es), [tmp(Q)])`. *)
Definition raw_load_pointer (d q es : term) : term :=
  TApp "let" [d; TAtom "p"; TApp "raw_load_pointer" [TInt 0; es]; TList [tmp q]].

(** `raw_store_pointer(0, V, tmp(Q), Es)`. *)
Definition raw_store_pointer (v q es : term) : term :=
  TApp "raw_store_pointer" [TInt 0; v; tmp q; es].

(** `let(D, K, raw_load(T, 0), [tmp(Q)])`. *)
Definition raw_load (d k t q : term) : term :=
  TApp "let" [d; k; TApp "raw_load" [t; TInt 0]; TList [tmp q]].

(** `raw_store(W, 0, V, tmp(Q))`. *)
Definition raw_store (w v q : term) : term := TApp "raw_store" [w; TInt 0; v; tmp q].

(** As `checked_access/4`, a clause for each row of pizlonate.pl's
    table: when the instruction i is an access, its check, defining
    `tmp(Q)`, and its raw access, for the fresh name q it is given.
    None for an instruction that is not an access. *)
Definition checked_access (i : term) : option (term -> list term) :=
  match i with
  | TApp f xs =>
      if f == "let" then
        match xs with
        | [d; k; TApp o [t]; TList args] =>
            let pointer := is_atom "p" k && is_atom "p" t in
            if o == "load" then
              match args with
              | [a] =>
                  if pointer
                  then Some (fun q => [check_sized q 8 "read" 8 a;
                                       raw_load_pointer d q load_effects])
                  else match size_align t with
                       | Some (size, align) =>
                           Some (fun q => [check_sized q size "read" align a; raw_load d k t q])
                       | None => None
                       end
              | _ => None
              end
            else if o == "atomic_load" then
              match args with
              | [a] =>
                  if pointer
                  then Some (fun q => [check_sized q 8 "read" 8 a;
                                       raw_load_pointer d q (effects ["atomic_read"])])
                  else None
              | _ => None
              end
            else if o == "cas" then
              match args with
              | [e; n; a] =>
                  match cas_bytes t with
                  | Some size =>
                      Some (fun q => [check_sized q size "write" size a;
                                      TApp "let" [d; k; TApp "raw_cas" [t; TInt 0];
                                                  TList [tmp q; e; n]]])
                  | None => None
                  end
              | _ => None
              end
            else None
        | _ => None
        end
      else if f == "store" then
        match xs with
        | [w; v; a] =>
            if is_atom "p" w
            then Some (fun q => [check_sized q 8 "write" 8 a; raw_store_pointer v q store_effects])
            else match size_align w with
                 | Some (size, align) =>
                     Some (fun q => [check_sized q size "write" align a; raw_store w v q])
                 | None => None
                 end
        | _ => None
        end
      else if f == "atomic_store" then
        match xs with
        | [w; v; a] =>
            if is_atom "p" w
            then Some (fun q => [check_sized q 8 "write" 8 a;
                                 raw_store_pointer v q (effects ["atomic_write"])])
            else None
        | _ => None
        end
      else if f == "access" then
        match xs with
        | [k; a; size; align] => Some (fun q => [check_inst q size k align a; TApp "touch" [tmp q]])
        | _ => None
        end
      else if f == "call" then
        match xs with
        | [res; TApp g [p]; args] =>
            if g == "tmp"
            then Some (fun q => [TApp "let" [tmp q; TAtom "f"; TAtom "check_function";
                                             TList [tmp p]];
                                 TApp "raw_call" [res; tmp q; args]])
            else None
        | _ => None
        end
      else if f == "local_load" then
        match xs with
        | [d; k; t; x; off] =>
            match size_align t with
            | Some (size, align) =>
                Some (fun q => [check_local_inst q x off size "read" align;
                                if is_atom "p" t then raw_load_pointer d q local_load_effects
                                else raw_load d k t q])
            | None => None
            end
        | _ => None
        end
      else if f == "local_store" then
        match xs with
        | [w; v; x; off] =>
            match size_align w with
            | Some (size, align) =>
                Some (fun q => [check_local_inst q x off size "write" align;
                                if is_atom "p" w then raw_store_pointer v q local_store_effects
                                else raw_store w v q])
            | None => None
            end
        | _ => None
        end
      else None
  | _ => None
  end.

(** ## Flights *)

(** As `flight_inst/2`: the [[flight]] of the pure pointer operation
    i, which is `add` or `sub` of an offset, a copy of a temporary or
    a constant, or `itop`, which has no [[lower]]. A copy of a symbol
    calls its getter and stays as it is. *)
Definition flight_inst (i : term) : option term :=
  match i with
  | TApp f [d; k; TAtom o; TList args] =>
      if (f == "let") && is_atom "p" k then
        let flight o args lower := TApp "flight" [d; TAtom o; TList args; lower] in
        let of_pointer o p rest :=
          flight o (TApp "address" [p] :: rest) (TApp "lower" [p]) in
        if (o == "add") || (o == "sub") then
          match args with [p; x] => Some (of_pointer o p [x]) | _ => None end
        else if o == "copy" then
          match args with
          | [TApp g [_] as v] =>
              if (g == "tmp") || (g == "const") then Some (of_pointer o v []) else None
          | _ => None
          end
        else if o == "itop" then
          match args with [x] => Some (flight "copy" [x] (TAtom "none")) | _ => None end
        else None
      else None
  | _ => None
  end.

(** ## Fresh names *)

(** The name d when the term r is `result(tmp(D), K)`. *)
Definition result_def (r : term) : list term :=
  match r with TApp f [t; _] => if f == "result" then tmp_name t else [] | _ => [] end.

(** As cfg.pl's `inst_def/2`: the names of the temporaries the
    instruction i defines; a call can define several. *)
Fixpoint inst_defs (i : term) : list term :=
  match i with
  | TApp f xs =>
      if (f == "let") || (f == "flight") then
        match xs with [d; _; _; _] => tmp_name d | _ => [] end
      else if f == "local_load" then
        match xs with [d; _; _; _; _] => tmp_name d | _ => [] end
      else if (f == "call") || (f == "raw_call") then
        match xs with
        | [r; _; _] =>
            match r with
            | TApp g [TList rs] => if g == "tuple" then flat_map result_def rs else []
            | _ => result_def r
            end
        | _ => []
        end
      else if f == "uses" then
        match xs with [j; _] => inst_defs j | _ => [] end
      else if f == "asm_fixed" then
        match xs with
        | [_; _; TList outs] =>
            flat_map (fun o => match o with
                               | TApp m [_; t] => if m == "-" then tmp_name t else []
                               | _ => []
                               end) outs
        | _ => []
        end
      else []
  | _ => []
  end.

(** The text of the name n when it could be a proof's name: an atom
    that begins `chk`. *)
Definition chk_name (n : term) : list string :=
  match n with TAtom a => if prefix "chk" a then [a] else [] | _ => [] end.

(** As `func_temp_names/3`, kept to the names a fresh one could be:
    of the temporaries that the function with the parameters params
    and the blocks defines, as a parameter, a [[phi]] or an
    instruction's result, those whose name begins `chk`. *)
Definition defined_chks (params : term) (blocks : list term) : list string :=
  let chks ns := flat_map chk_name ns in
  let param p := match p with TApp g [_; t] => if g == "param" then chks (tmp_name t) else []
                         | _ => [] end in
  let phi p := match p with TApp g [d; _; _] => if g == "phi" then chks (tmp_name d) else []
                       | _ => [] end in
  let listed (g : term -> list string) (t : term) :=
    match t with TList ts => flat_map g ts | _ => [] end in
  app (listed param params)
      (flat_map (fun b => match b with
                          | TApp g [_; phis; insts; _] =>
                              if g == "block"
                              then app (listed phi phis)
                                       (listed (fun i => chks (inst_defs i)) insts)
                              else []
                          | _ => []
                          end) blocks).

(** As `fresh_name/4`: the name `chkI` for the least I from n on that
    is not among names, and I + 1. Each name passed over is another
    of names, so a fuel of their number is enough: when it is spent,
    every one of them has been passed over. *)
Fixpoint fresh (fuel : nat) (names : list string) (n : Z) : string * Z :=
  let q := String.append "chk" (decimal n) in
  match fuel with
  | O => (q, n + 1)
  | S fuel' => if existsb (String.eqb q) names then fresh fuel' names (n + 1) else (q, n + 1)
  end.

(** ## Instructions *)

(** Whether the instruction i is a `loc(File, Line)` marker. *)
Definition is_loc (i : term) : bool :=
  match i with TApp f [_; _] => f == "loc" | _ => false end.

(** A step of `checked_insts/11`, in filc [[mode]]: the count of
    fresh names and the instructions so far, last first, with the
    instruction i after them: an access as its check and raw access
    ([checked_access]), a pure pointer operation as its flight
    ([flight_inst]), and any other as it is. *)
Definition inst_step (names : list string) (fuel : nat) (st : Z * list term) (i : term)
  : Z * list term :=
  let '(n, out) := st in
  match checked_access i with
  | Some access =>
      let '(q, n') := fresh fuel names n in
      (n', rev_append (access (TAtom q)) out)
  | None => (n, match flight_inst i with Some j => j | None => i end :: out)
  end.

(** ## Jumps *)

(** As `polled_target/4`: the target l of a jump from the block at
    the index from: `poll(L)` when the block l is at or before it in
    block order (index), and l as it is when it is later, or is a
    poll edge already. None for a label no block has. *)
Definition polled_target (index : nmap Z) (from : Z) (l : term) : option term :=
  let plain :=
    match nm_find l index with
    | Some to => Some (if to <=? from then TApp "poll" [l] else l)
    | None => None
    end in
  match l with
  | TApp f [_] => if f == "poll" then Some l else plain
  | _ => plain
  end.

(** As `polled_jump/4`: the jump j that ends the block at the index
    from, with a poll edge for each target at or before it, so that
    every cycle of the function polls. *)
Definition polled_jump (index : nmap Z) (from : Z) (j : term) : option term :=
  match j with
  | TApp f xs =>
      if f == "goto" then
        match xs with
        | [l] => option_map (fun t => TApp "goto" [t]) (polled_target index from l)
        | _ => None
        end
      else if f == "branch" then
        match xs with
        | [v; l1; l2] =>
            match polled_target index from l1, polled_target index from l2 with
            | Some t1, Some t2 => Some (TApp "branch" [v; t1; t2])
            | _, _ => None
            end
        | _ => None
        end
      else if (f == "ret") || (f == "rets") then
        match xs with [_] => Some j | _ => None end
      else None
  | TAtom a => if (a == "ret") || (a == "unreachable") then Some j else None
  | _ => None
  end.

(** ## Functions *)

(** Each block's label with its place in block order, from i on,
    added to m. None when a term is not a block or two blocks have
    one label, where `list_to_assoc/2` throws. *)
Fixpoint label_index (i : Z) (bs : list term) (m : nmap Z) : option (nmap Z) :=
  match bs with
  | [] => Some m
  | TApp f [l; _; _; _] :: rest =>
      if (f == "block") && negb (nm_mem l m) then label_index (i + 1) rest (nm_add l i m)
      else None
  | _ :: _ => None
  end.

(** As `pizlonated_blocks/7`: the blocks bs, the first at the index i
    in block order, their `loc` markers dropped when drop is set,
    their instructions by [inst_step] in filc [[mode]] and their
    jumps by [polled_jump]. n counts the fresh names, across the
    blocks. *)
Fixpoint pizlonated_blocks (filc drop : bool) (names : list string) (fuel : nat)
    (index : nmap Z) (i n : Z) (bs : list term) : option (list term) :=
  match bs with
  | [] => Some []
  | TApp f [l; phis; TList insts; j] :: rest =>
      if f == "block" then
        let insts := if drop then filter (fun x => negb (is_loc x)) insts else insts in
        let '(n', insts') :=
          if filc then
            let '(n', out) := fold_left (inst_step names fuel) insts (n, []) in (n', rev' out)
          else (n, insts) in
        match polled_jump index i j with
        | Some j' =>
            match pizlonated_blocks filc drop names fuel index (i + 1) n' rest with
            | Some rest' => Some (TApp "block" [l; phis; TList insts'; j'] :: rest')
            | None => None
            end
        | None => None
        end
      else None
  | _ :: _ => None
  end.

(** As `pizlonated_item/4` for the function
    `func(Name, Linkage, Ret, Params, Blocks)`. *)
Definition pizlonated_func (filc drop : bool) (name lk ret params blocks : term) : option term :=
  match blocks with
  | TList bs =>
      let names := defined_chks params bs in
      match label_index 0 bs nm_empty with
      | Some index =>
          option_map (fun bs' => TApp "func" [name; lk; ret; params; TList bs'])
                     (pizlonated_blocks filc drop names (length names) index 0 0 bs)
      | None => None
      end
  | _ => None
  end.

(** ## The mode and the stage of a module *)

(** As ir.pl's `pointer_inst/1`: the instruction i makes, stores,
    passes or calls through a `p` value, or converts one. *)
Definition pointer_inst (i : term) : bool :=
  match i with
  | TApp f xs =>
      if f == "let" then
        match xs with
        | [_; k; o; _] =>
            is_atom "p" k || is_atom "x" k || is_atom "a" k || is_atom "f" k
            || match o with
               | TAtom a => a == "ptoi"
               | TApp g ys => ((g == "setjmp") && arity 1 ys)
                              || ((g == "raw_load_pointer") && arity 2 ys)
               | _ => false
               end
        | _ => false
        end
      else if f == "store" then
        match xs with [w; _; _] => is_atom "x" w || is_atom "p" w | _ => false end
      else if f == "call" then
        match xs with
        | [r; callee; args] =>
            match r with
            | TApp g [_; k] => (g == "result") && is_atom "p" k
            | TApp g [_] => g == "tuple"
            | _ => false
            end
            || match args with
               | TList ts => existsb (fun a => match a with
                                               | TApp g [k; _] => (g == "arg") && is_atom "p" k
                                               | _ => false
                                               end) ts
               | _ => false
               end
            || match callee with TApp g [_] => g == "tmp" | _ => false end
        | _ => false
        end
      else if (f == "atomic_store") || (f == "raw_call") then arity 3 xs
      else if (f == "raw_store") || (f == "raw_store_pointer") || (f == "flight")
              || (f == "local_store") then arity 4 xs
      else if f == "local_alloc" then arity 2 xs
      else if f == "local_load" then arity 5 xs
      else false
  | _ => false
  end.

(** The blocks of the item it when it is a function. *)
Definition func_blocks (it : term) : list term :=
  match it with
  | TApp f [_; _; _; _; TList bs] => if f == "func" then bs else []
  | _ => []
  end.

(** The instructions and the jump of the term b when it is a
    block. *)
Definition block_parts (b : term) : option (term * list term * term) :=
  match b with
  | TApp f [_; phis; TList insts; j] => if f == "block" then Some (phis, insts, j) else None
  | _ => None
  end.

(** As ir.pl's `pointer_item/1`: the item it has class `p`
    somewhere, or is an alias, a weak function, or read-only, weak,
    external or thread-local data, which only filc [[mode]]
    models. *)
Definition pointer_item (it : term) : bool :=
  match it with
  | TApp f xs =>
      if f == "func" then
        match xs with
        | [_; lk; r; ps; _] =>
            is_atom "weak" lk || is_atom "p" r
            || match r with TApp g [_] => g == "tuple" | _ => false end
            || match ps with
               | TList ps => existsb (fun p => match p with
                                               | TApp g [k; _] => (g == "param") && is_atom "p" k
                                               | _ => false
                                               end) ps
               | _ => false
               end
            || existsb (fun b =>
                          match block_parts b with
                          | Some (phis, insts, _) =>
                              match phis with
                              | TList phis =>
                                  existsb (fun p => match p with
                                                    | TApp g [_; k; _] =>
                                                        (g == "phi") && is_atom "p" k
                                                    | _ => false
                                                    end) phis
                              | _ => false
                              end
                              || existsb pointer_inst insts
                          | None => false
                          end) (func_blocks it)
        | _ => false
        end
      else if f == "alias" then arity 3 xs
      else if f == "data" then
        match xs with
        | [_; lk; _; items] =>
            match lk with
            | TApp g [_] => (g == "ro") || (g == "tls") || (g == "extern")
            | TAtom a => a == "weak"
            | _ => false
            end
            || match items with
               | TList ts => existsb (fun i => match i with
                                               | TApp g [k; _] => (g == "item") && is_atom "p" k
                                               | _ => false
                                               end) ts
               | _ => false
               end
        | _ => false
        end
      else false
  | _ => false
  end.

(** As ir.pl's `module_mode/2`: the module of the items is in filc
    [[mode]] when an item is a [pointer_item], or a function calls a
    symbol that no function of the module defines. A plain module's
    addresses are not Fil-C pointers. *)
Definition module_filc (items : list term) : bool :=
  existsb pointer_item items
  || (let funcs := fold_left (fun m it => match it with
                                          | TApp f [n; _; _; _; _] =>
                                              if f == "func" then nm_add n tt m else m
                                          | _ => m
                                          end) items nm_empty in
      existsb (fun it =>
                 existsb (fun b =>
                            match block_parts b with
                            | Some (_, insts, _) =>
                                existsb (fun i => match i with
                                                  | TApp h [_; TApp g [callee]; _] =>
                                                      (h == "call") && (g == "global")
                                                      && negb (nm_mem callee funcs)
                                                  | _ => false
                                                  end) insts
                            | None => false
                            end) (func_blocks it)) items).

(** As ir.pl's `module_stage/2`, on terms: the module of the items is
    in the checked [[stage]] when a function uses a word of it. *)
Definition module_checked (items : list term) : bool :=
  existsb (fun it =>
             existsb (fun b => match block_parts b with
                               | Some (_, insts, j) =>
                                   existsb checked_inst_term insts || checked_jump_term j
                               | None => false
                               end) (func_blocks it)) items.

(** ## Modules *)

(** Whether the item it is a `context(Name, Records)`. *)
Definition is_context (it : term) : bool :=
  match it with TApp f [_; _] => f == "context" | _ => false end.

(** As `pizlonated_item/4`: a function by [pizlonated_func], data
    and an alias as they are. *)
Definition pizlonated_item (filc drop : bool) (it : term) : option term :=
  match it with
  | TApp f xs =>
      if f == "func" then
        match xs with
        | [name; lk; ret; params; blocks] => pizlonated_func filc drop name lk ret params blocks
        | _ => None
        end
      else if f == "data" then if arity 4 xs then Some it else None
      else if f == "alias" then if arity 3 xs then Some it else None
      else None
  | _ => None
  end.

(** As `pizlonate_module/2`, without the context items: the module m
    with every check explicit and a poll on every edge to a block at
    or before its source. In a plain module only the polls are
    added. The `loc` markers of an unchecked module are dropped, as
    `legacy_context/2` drops them; a checked module keeps its
    own. *)
Definition pizlonate_module (m : term) : option term :=
  match m with
  | TApp f [TList items] =>
      if f == "module" then
        let filc := module_filc items in
        let drop := negb (module_checked items) in
        option_map (fun its => TApp "module" [TList its])
                   (map_option (pizlonated_item filc drop)
                               (filter (fun it => negb (is_context it)) items))
      else None
  | _ => None
  end.

(** ## Examples *)

(** A load: a read check of the type's size, then the raw load of the
    proven address. *)
Example load_word :
  option_map (fun k => k (TAtom "chk0"))
    (checked_access (TApp "let" [tmp (TAtom "d"); TAtom "w"; TApp "load" [TAtom "sw"];
                                 TList [tmp (TAtom "p")]]))
  = Some [check_sized (TAtom "chk0") 4 "read" 1 (tmp (TAtom "p"));
          TApp "let" [tmp (TAtom "d"); TAtom "w"; TApp "raw_load" [TAtom "sw"; TInt 0];
                      TList [tmp (TAtom "chk0")]]].
Proof. reflexivity. Qed.

(** A pointer store: a write check of 8 bytes at an 8-aligned
    address, then the raw store with the store's effects. *)
Example store_pointer :
  option_map (fun k => k (TAtom "chk0"))
    (checked_access (TApp "store" [TAtom "p"; tmp (TAtom "v"); tmp (TAtom "a")]))
  = Some [check_sized (TAtom "chk0") 8 "write" 8 (tmp (TAtom "a"));
          TApp "raw_store_pointer" [TInt 0; tmp (TAtom "v"); tmp (TAtom "chk0"); store_effects]].
Proof. reflexivity. Qed.

(** A pointer's offset is a flight of its address and its lower. *)
Example add_flight :
  flight_inst (TApp "let" [tmp (TAtom "q"); TAtom "p"; TAtom "add";
                           TList [tmp (TAtom "p"); TApp "const" [TInt 8]]])
  = Some (TApp "flight" [tmp (TAtom "q"); TAtom "add";
                         TList [TApp "address" [tmp (TAtom "p")]; TApp "const" [TInt 8]];
                         TApp "lower" [tmp (TAtom "p")]]).
Proof. reflexivity. Qed.

(** A fresh name passes over the names the function defines. *)
Example fresh_passes_over : fresh 2 ["chk1"; "chk0"] 0 = ("chk2", 3).
Proof. reflexivity. Qed.

(** A loop: the back edge polls, the forward edge does not, and the
    load in a module with a pointer gets its check. *)
Example loop_module :
  pizlonate_module
    (TApp "module" [TList [TApp "func" [TAtom "f"; TAtom "export"; TAtom "w";
       TList [TApp "param" [TAtom "p"; tmp (TAtom "a")]];
       TList [TApp "block" [TAtom "top"; TList [];
                            TList [TApp "let" [tmp (TAtom "x"); TAtom "w";
                                               TApp "load" [TAtom "w"]; TList [tmp (TAtom "a")]]];
                            TApp "branch" [tmp (TAtom "x"); TAtom "top"; TAtom "out"]];
              TApp "block" [TAtom "out"; TList []; TList []; TApp "ret" [tmp (TAtom "x")]]]]]])
  = Some (TApp "module" [TList [TApp "func" [TAtom "f"; TAtom "export"; TAtom "w";
       TList [TApp "param" [TAtom "p"; tmp (TAtom "a")]];
       TList [TApp "block" [TAtom "top"; TList [];
                            TList [check_sized (TAtom "chk0") 4 "read" 1 (tmp (TAtom "a"));
                                   TApp "let" [tmp (TAtom "x"); TAtom "w";
                                               TApp "raw_load" [TAtom "w"; TInt 0];
                                               TList [tmp (TAtom "chk0")]]];
                            TApp "branch" [tmp (TAtom "x"); TApp "poll" [TAtom "top"];
                                           TAtom "out"]];
              TApp "block" [TAtom "out"; TList []; TList []; TApp "ret" [tmp (TAtom "x")]]]]]]).
Proof. reflexivity. Qed.
