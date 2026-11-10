(** # Promotion of memory slots to temporaries

    As promote.pl's `promote_module/2`, on terms. A slot is one
    offset and width, `acc(Off, W)`, of an alloc whose address does
    not escape (Escape.v). An alloc is promoted, all its slots at
    once, when its size is a constant, its slots lie inside it and do
    not overlap, and its float slots are stored before they are read.
    Each load of a slot then becomes a copy or an extension of the
    slot's value, each store goes, and phis named `pr.N` join the
    values where paths meet (pruned SSA, Cytron et al.).

    An `l` access that another access overlaps is first split into
    two `w` accesses, when the alloc then promotes.

    A function that is not in strict SSA form, or that calls setjmp,
    is left as it is. What promote.pl does besides is left out, as in
    Copy.v: the context records and their sites. [promote_module]
    gives None where `promote_module/2` fails or throws. The gate
    (tests/promote.sh) holds the result to the term
    `nanofil promote-terms` prints. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg Escape.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality, written as Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Terms *)

(** The instruction `let(D, K, Op, Args)`. *)
Definition let_term (d k o : term) (args : list term) : term :=
  TApp "let" [d; k; o; TList args].

(** The instruction `store(W, V, A)`. *)
Definition store_term (w v a : term) : term := TApp "store" [w; v; a].

(** The value `const(N)`. *)
Definition const_term (n : Z) : term := TApp "const" [TInt n].

(** The width, value and address when the term i is
    `store(W, V, A)`. *)
Definition store_parts (i : term) : option (term * term * term) :=
  match i with
  | TApp f [w; v; a] => if f == "store" then Some (w, v, a) else None
  | _ => None
  end.

(** The destination, class, type and address name when the term i
    is `let(D, K, load(T), [tmp(X)])`. *)
Definition load_parts (i : term) : option (term * term * term * term) :=
  match let_parts i with
  | Some (d, k, TApp g [t], [a]) =>
      if g == "load" then
        match tmp_name a with [x] => Some (d, k, t, x) | _ => None end
      else None
  | _ => None
  end.

(** Whether x is in the ordset xs. *)
Definition nmem (x : name) (xs : names) : bool := ord_mem term_compare x xs.

(** A slot of an alloc as a name, the term `A-Off`. *)
Definition slot_var (a : term) (off : Z) : term := TApp "-" [a; TInt off].

(** ## Which allocs *)

(** As `stored_accs(F, Addrs, Stored)`: for each alloc, the accesses
    of the stores to its addresses. *)
Definition stored_accs (addrs : addresses) (bs : list tblock) : nmap (list acc) :=
  fold_left (fun m i =>
               match store_parts i with
               | Some (w, _, a) =>
                   fold_left (fun m r => nm_add (fst r) ((snd r, w) :: accs_at m (fst r)) m)
                             (address_of addrs a) m
               | None => m
               end)
            (flat_map tb_insts bs) nm_empty.

(** As `acc_inside(Acc, Outer)`: the bytes of the access a are bytes
    of the access outer. *)
Definition acc_inside (a outer : acc) : bool :=
  match width_bytes (snd a), width_bytes (snd outer) with
  | Some b, Some sb => (fst outer <=? fst a) && (fst a + b <=? fst outer + sb)
  | _, _ => false
  end.

(** As `punned_slots(Accs, Stored, Slots)`: the slots of an alloc
    with the accesses accs, those that are inside no other. Each
    access inside another must be a punned read: of width `b` or `h`,
    never stored, and the first slot it is inside of width `h` or
    `w`. None when one is not. *)
Definition punned_slots (accs stored : list acc) : option (list acc) :=
  let inner a := existsb (fun o => negb (acc_eqb o a) && acc_inside a o) accs in
  let parts := partition inner accs in
  let slots := snd parts in
  let punned a :=
    (is_atom "b" (snd a) || is_atom "h" (snd a))
    && negb (existsb (acc_eqb a) stored)
    && match find (acc_inside a) slots with
       | Some s => is_atom "h" (snd s) || is_atom "w" (snd s)
       | None => false
       end in
  if forallb punned (fst parts) then Some slots else None.

(** As `slots_disjoint/1`: each of the slots, sorted, ends before the
    next begins. *)
Fixpoint slots_disjoint (slots : list acc) : bool :=
  match slots with
  | a :: (b :: _) as rest =>
      match width_bytes (snd a) with
      | Some n => (fst a + n <=? fst b) && slots_disjoint rest
      | None => false
      end
  | _ => true
  end.

(** As `slots_ok(Mode, Size, Slots)`: an alloc of size bytes can go
    for its slots. In filc [[mode]] its size is one an alloc cannot
    trap on, at most 2^48 - 1. Each slot lies inside the alloc, a
    `p` slot is 8-aligned in filc mode, so no access could trap, and
    the slots do not overlap. No slot has the width `x`. *)
Definition slots_ok (filc : bool) (size : Z) (slots : list acc) : bool :=
  (negb filc || ((0 <=? size) && (size <=? 281474976710655)))
  && forallb (fun a =>
                match width_bytes (snd a) with
                | Some n =>
                    (0 <=? fst a) && (fst a + n <=? size)
                    && (if is_atom "p" (snd a) then negb filc || (fst a mod 8 =? 0)
                        else negb (is_atom "x" (snd a)))
                | None => false
                end) slots
  && slots_disjoint slots.

(** A promoted alloc: its temporary and its slots. *)
Definition root : Type := (term * list acc)%type.

(** Whether w is a float width, `s` or `d`. *)
Definition float_width (w : term) : bool := is_atom "s" w || is_atom "d" w.

(** As `stored_transfer(Addrs, A-Os, I, S0, S)`: the offsets among
    os of the alloc a that are stored after the instruction i, given
    those stored before, s. The alloc itself stores none. *)
Definition stored_transfer (addrs : addresses) (a : term) (os : names) (i : term)
    (s : names) : names :=
  match let_parts i with
  | Some (d, _, o, _) => if is_alloc o && existsb (term_eqb a) (tmp_name d) then [] else s
  | None =>
      match store_parts i with
      | Some (_, _, x) =>
          match address_of addrs x with
          | [(r, off)] =>
              if term_eqb r a && nmem (TInt off) os then nunion s [TInt off] else s
          | _ => s
          end
      | None => s
      end
  end.

(** As `float_slots_stored(Cfg, ByLabel, Addrs, A-Slots)`: every load
    of a float slot of the alloc a comes after a store to it, on
    every path from the alloc. The stored offsets at each block's end
    are the greatest solution of a forward analysis over the
    reachable blocks: a block starts with what all its predecessors
    with a set so far end with, the entry with nothing. *)
Definition float_slots_stored (g : cfg) (by_label : nmap tblock) (addrs : addresses)
    (r : root) : bool :=
  let a := fst r in
  let os := nsort (flat_map (fun s => if float_width (snd s) then [TInt (fst s)] else [])
                            (snd r)) in
  match os with
  | [] => true
  | _ =>
      let insts l := match nm_find l by_label with Some b => tb_insts b | None => [] end in
      let block_in (out : nmap names) (l : name) : names :=
        if name_eqb l (cfg_entry g) then [] else
        match flat_map (fun p => match nm_find p out with Some s => [s] | None => [] end)
                       (match nm_find l (cfg_preds g) with Some ps => ps | None => [] end) with
        | s0 :: rest => fold_left (ord_intersection term_compare) rest s0
        | [] => []
        end in
      let step (out : nmap names) : nmap names * bool :=
        fold_left (fun st l =>
                     let new := fold_left (fun s i => stored_transfer addrs a os i s)
                                          (insts l) (block_in (fst st) l) in
                     match nm_find l (fst st) with
                     | Some old =>
                         if names_eqb old new then st else (nm_add l new (fst st), true)
                     | None => (nm_add l new (fst st), true)
                     end)
                  (cfg_rpo g) (out, false) in
      let res := live_rounds 40 step nm_empty in
      negb (snd res)
      && forallb (fun l =>
                    snd (fold_left
                           (fun st i =>
                              let ok :=
                                match load_parts i with
                                | Some (_, _, _, x) =>
                                    match nm_find x addrs with
                                    | Some (rt, off) =>
                                        if term_eqb rt a && nmem (TInt off) os
                                        then nmem (TInt off) (fst st) else true
                                    | None => true
                                    end
                                | None => true
                                end in
                              (stored_transfer addrs a os i (fst st), snd st && ok))
                           (insts l) (block_in (fst res) l, true)))
                 (cfg_rpo g)
  end.

(** What `promotable/4` finds of a function: the allocs to promote,
    with the classes, address temporaries and definition counts they
    come from. *)
Record analysis : Type := mkAnalysis {
  an_roots : list root; (* the allocs to promote *)
  an_classes : list (term * term * option (list acc)); (* each alloc's size and class *)
  an_addrs : addresses; (* the address temporaries *)
  an_counts : nmap nat (* how often each temporary is defined *)
}.

(** As `promotable(Mode, F, Roots, An)`, for a function with an
    alloc that does not call setjmp: the allocs of constant size
    whose slots are fit ([punned_slots], [slots_ok]) and whose float
    slots are stored before they are read. *)
Definition promotable (filc : bool) (params : list term) (bs : list tblock)
  : option analysis :=
  let* addrs := address_temps bs in
  let counts := def_counts params bs in
  let classes := alloc_classes addrs counts params bs in
  let stored := stored_accs addrs bs in
  let roots0 :=
    flat_map (fun c =>
                match c with
                | (a, size, Some accs) =>
                    match const_int size, punned_slots accs (accs_at stored a) with
                    | Some n, Some slots => if slots_ok filc n slots then [(a, slots)] else []
                    | _, _ => []
                    end
                | _ => []
                end) classes in
  let* roots :=
    if existsb (fun r => existsb (fun s => float_width (snd s)) (snd r)) roots0 then
      let* g := term_cfg bs in
      let by_label := nm_of_list (map (fun b => (tb_label b, b)) bs) in
      Some (filter (float_slots_stored g by_label addrs) roots0)
    else Some roots0 in
  Some (mkAnalysis roots classes addrs counts).

(** ## Splitting words *)

(** As `split_offsets(Accs, Offs)`: the ordset of the offsets of the
    `l` accesses among accs that another access overlaps. *)
Definition split_offsets (accs : list acc) : list Z :=
  let overlap (a b : acc) :=
    match width_bytes (snd a), width_bytes (snd b) with
    | Some n1, Some n2 => (fst a <? fst b + n2) && (fst b <? fst a + n1)
    | _, _ => false
    end in
  sort Z.compare
       (flat_map (fun x =>
                    if is_atom "l" (snd x)
                       && existsb (fun o => negb (acc_eqb o x) && overlap x o) accs
                    then [fst x] else []) accs).

(** As `split_accs(Offs, Accs0, Accs)`: the accesses accs with each
    `l` access at an offset of offs as its two words. *)
Definition split_accs (offs : list Z) (accs : list acc) : list acc :=
  sort acc_compare
       (flat_map (fun x =>
                    if is_atom "l" (snd x) && existsb (Z.eqb (fst x)) offs
                    then [(fst x, TAtom "w"); (fst x + 4, TAtom "w")] else [x]) accs).

(** As `split_roots(Mode, F, Roots, Classes, Addrs, Splits)`: the
    allocs to split, each with the offsets of the `l` accesses to
    split. They are the allocs of constant size with an `l` access
    that are no roots but would have fit slots once split. An alloc
    with a store of an `l` that is neither a temporary nor a constant
    is not split. *)
Definition split_roots (filc : bool) (bs : list tblock) (an : analysis)
  : list (term * list Z) :=
  let addrs := an_addrs an in
  let cands :=
    flat_map (fun c =>
                match c with
                | (a, size, Some accs) =>
                    match const_int size with
                    | Some n =>
                        if negb (existsb (fun r => term_eqb (fst r) a) (an_roots an))
                           && existsb (fun x => is_atom "l" (snd x)) accs
                        then [(a, n, accs)] else []
                    | None => []
                    end
                | _ => []
                end) (an_classes an) in
  match cands with
  | [] => []
  | _ =>
      let stored := stored_accs addrs bs in
      let bad :=
        flat_map (fun i =>
                    match store_parts i with
                    | Some (w, v, a) =>
                        let simple := match v with
                                      | TApp f [_] => (f == "tmp") || (f == "const")
                                      | _ => false
                                      end in
                        if is_atom "l" w && negb simple
                        then map fst (address_of addrs a) else []
                    | None => []
                    end) (flat_map tb_insts bs) in
      flat_map (fun c =>
                  let '(a, size, accs) := c in
                  if existsb (term_eqb a) bad then [] else
                  match split_offsets accs with
                  | [] => []
                  | offs =>
                      match punned_slots (split_accs offs accs)
                                         (split_accs offs (accs_at stored a)) with
                      | Some slots => if slots_ok filc size slots then [(a, offs)] else []
                      | None => []
                      end
                  end) cands
  end.

(** As `fresh_temps/4` for one name: the name `sw.I` for the least I
    from n on that counts has no definition of, and I + 1. Each name
    passed over is another key of counts, so a fuel of their number
    is enough. *)
Fixpoint fresh_split (fuel : nat) (counts : nmap nat) (n : Z) : term * Z :=
  let q := TAtom (String.append "sw." (decimal n)) in
  match fuel with
  | O => (q, n + 1)
  | S fuel' => if nm_mem q counts then fresh_split fuel' counts (n + 1) else (q, n + 1)
  end.

(** As `split_inst/5`: the instruction i, with a store or a load of
    an `l` at a split address as two of a `w`, the low word at the
    address and the high word 4 bytes on; n counts the fresh names.
    The address 4 bytes on has the class k, `p` in filc [[mode]] and
    else `l`. *)
Definition split_inst (splits : list (term * list Z)) (addrs : addresses) (counts : nmap nat)
    (fuel : nat) (k : term) (i : term) (n : Z) : list term * Z :=
  let split_address (a : term) : bool :=
    match address_of addrs a with
    | [(r, o)] =>
        match find (fun s => term_eqb (fst s) r) splits with
        | Some s => existsb (Z.eqb o) (snd s)
        | None => false
        end
    | _ => false
    end in
  let l := TAtom "l" in
  let w := TAtom "w" in
  match store_parts i with
  | Some (sw, v, a) =>
      if is_atom "l" sw && split_address a then
        let h := fresh_split fuel counts n in
        let x4 := fresh_split fuel counts (snd h) in
        ([let_term (tmp (fst h)) l (TAtom "shr") [v; const_term 32];
          store_term w v a;
          let_term (tmp (fst x4)) k (TAtom "add") [a; const_term 4];
          store_term w (tmp (fst h)) (tmp (fst x4))], snd x4)
      else ([i], n)
  | None =>
      match load_parts i with
      | Some (d, kl, t, x) =>
          if is_atom "l" kl && is_atom "l" t && split_address (tmp x) then
            let lo := fresh_split fuel counts n in
            let x4 := fresh_split fuel counts (snd lo) in
            let hi := fresh_split fuel counts (snd x4) in
            let hs := fresh_split fuel counts (snd hi) in
            let load_uw := TApp "load" [TAtom "uw"] in
            ([let_term (tmp (fst lo)) l load_uw [tmp x];
              let_term (tmp (fst x4)) k (TAtom "add") [tmp x; const_term 4];
              let_term (tmp (fst hi)) l load_uw [tmp (fst x4)];
              let_term (tmp (fst hs)) l (TAtom "shl") [tmp (fst hi); const_term 32];
              let_term d l (TAtom "or") [tmp (fst hs); tmp (fst lo)]], snd hs)
          else ([i], n)
      | None => ([i], n)
      end
  end.

(** As `split_words/8`: the blocks bs with the `l` accesses of
    splits as words, and whether any was split. *)
Definition split_words (filc : bool) (splits : list (term * list Z)) (addrs : addresses)
    (counts : nmap nat) (fuel : nat) (bs : list tblock) : list tblock * bool :=
  let k := TAtom (if filc then "p" else "l") in
  let r :=
    fold_left (fun st b =>
                 let r := fold_left (fun s i =>
                                       let o := split_inst splits addrs counts fuel k i (snd s) in
                                       (rev_append (fst o) (fst s), snd o))
                                    (tb_insts b) ([], snd st) in
                 (mkTBlock (tb_label b) (tb_phis b) (rev' (fst r)) (tb_jump b) :: fst st,
                  snd r))
              bs ([], 0) in
  (rev' (fst r), negb (snd r =? 0)).

(** ## The rewrite *)

(** As the `AddrShifts` of `promote_roots/11`: the slot an address
    at the offset off of the alloc a names, and the byte of the slot
    it starts at. That is the first of slots with the byte at off,
    or a slot at off itself. *)
Definition address_slot (a : term) (off : Z) (slots : list acc) : term * Z :=
  match find (fun s => match width_bytes (snd s) with
                       | Some n => (fst s <=? off) && (off <? fst s + n)
                       | None => false
                       end) slots with
  | Some s => (slot_var a (fst s), off - fst s)
  | None => (slot_var a off, 0)
  end.

(** The slots the instruction i sets: those of a root it allocates,
    or the one it stores to. *)
Definition inst_sets (slot_of : nmap (term * Z)) (alloc_vars : nmap (list term)) (i : term)
  : list term :=
  match let_parts i with
  | Some (d, _, o, _) =>
      if is_alloc o then
        flat_map (fun a => match nm_find a alloc_vars with Some vs => vs | None => [] end)
                 (tmp_name d)
      else []
  | None =>
      match store_parts i with
      | Some (_, _, a) =>
          flat_map (fun x => match nm_find x slot_of with Some s => [fst s] | None => [] end)
                   (tmp_name a)
      | None => []
      end
  end.

(** As `slot_gen_kill/4`: the slots the instructions read before
    they set them, and those they set. *)
Definition slot_gen_kill (slot_of : nmap (term * Z)) (alloc_vars : nmap (list term))
    (insts : list term) : names * names :=
  fold_left (fun gk i =>
               match load_parts i with
               | Some (_, _, _, x) =>
                   match nm_find x slot_of with
                   | Some (v, _) => if nmem v (snd gk) then gk else (nunion (fst gk) [v], snd gk)
                   | None => gk
                   end
               | None => (fst gk, nunion (snd gk) (nsort (inst_sets slot_of alloc_vars i)))
               end)
            insts ([], []).

(** As `iterated_frontier/6`: the labels where the slot var needs a
    phi, an ordset: those of the dominance frontiers of the labels of
    work, and of the labels so found, where var is live. Each turn
    takes a label off work, and a label is put on it once, so a fuel
    of the labels of work and of the graph is enough. *)
Fixpoint iterated_frontier (fuel : nat) (df live_in : nmap names) (var : term)
    (work : list name) (placed : names) : option names :=
  match work with
  | [] => Some placed
  | l :: ls =>
      match fuel with
      | O => None
      | S fuel' =>
          let* frontier := nm_find l df in
          let st :=
            fold_left (fun st y =>
                         if negb (nmem y (fst st)) && nmem var (names_at live_in y)
                         then (nunion (fst st) [y], y :: snd st) else st)
                      frontier (placed, ls) in
          iterated_frontier fuel' df live_in var (snd st) (fst st)
      end
  end.

(** As `unused_temp/4`: the name `pr.I` for the least I above n that
    counts has no definition of, and I. *)
Fixpoint fresh_phi (fuel : nat) (counts : nmap nat) (n : Z) : term * Z :=
  let q := TAtom (String.append "pr." (decimal (n + 1))) in
  match fuel with
  | O => (q, n + 1)
  | S fuel' => if nm_mem q counts then fresh_phi fuel' counts (n + 1) else (q, n + 1)
  end.

(** As `load_op(T, K, Op)`: the op that makes of a slot's value what
    a load of the type t gives at the class k. *)
Definition load_op (t k : term) : option term :=
  match t with
  | TAtom a =>
      if (a == "l") || (a == "p") || (a == "s") || (a == "d") then Some (TAtom "copy")
      else if (a == "sw") || (a == "uw") then
        if is_atom "w" k then Some (TAtom "copy")
        else if is_atom "l" k then Some (TApp "ext" [t])
        else None
      else if (a == "sh") || (a == "uh") || (a == "sb") || (a == "ub")
      then Some (TApp "ext" [t])
      else None
  | _ => None
  end.

(** As `slot_class(Width, K)`: the class of the phi of a slot of the
    width w. *)
Definition slot_class (w : term) : option term :=
  match w with
  | TAtom a =>
      if (a == "l") || (a == "p") || (a == "s") || (a == "d") then Some w
      else if (a == "w") || (a == "h") || (a == "b") then Some (TAtom "w")
      else None
  | _ => None
  end.

(** As `inst_renamed/4`: what the instruction i becomes, and the
    slots' values after it, given those before, cur.

    - The alloc of a root goes; its slots are 0.
    - An instruction that defines an address of a root goes.
    - A load of a slot is the [load_op] on the slot's value, or, for
      a punned read at a byte past the slot's first, on the value
      shifted right by 8 bits a byte, in the temporary `pun.D`.
    - A store to a slot goes; the slot has its value.

    None where promote.pl fails: for a slot with no value, a load
    with no op, or a punned read into something that is no named
    temporary. *)
Definition inst_renamed (slot_of : nmap (term * Z)) (alloc_vars : nmap (list term))
    (cur : nmap term) (i : term) : option (nmap term * list term) :=
  let keep := Some (cur, [i]) in
  match let_parts i with
  | Some (d, k, o, _) =>
      let avs := if is_alloc o then
                   match tmp_name d with [a] => nm_find a alloc_vars | _ => None end
                 else None in
      match avs with
      | Some vs => Some (fold_left (fun c v => nm_add v (const_term 0) c) vs cur, [])
      | None =>
          if existsb (fun x => nm_mem x slot_of) (tmp_name d) then Some (cur, []) else
          match load_parts i with
          | Some (_, _, t, x) =>
              match nm_find x slot_of with
              | Some (var, shift) =>
                  let* v := nm_find var cur in
                  let* op := load_op t k in
                  if shift =? 0 then Some (cur, [let_term d k op [v]]) else
                  let* p := match tmp_name d with
                            | [TAtom n] => Some (TAtom (String.append "pun." n))
                            | [TInt n] => Some (TAtom (String.append "pun." (decimal n)))
                            | _ => None
                            end in
                  Some (cur, [let_term (tmp p) (TAtom "w") (TAtom "shr")
                                       [v; const_term (8 * shift)];
                              let_term d k op [tmp p]])
              | None => keep
              end
          | None => keep
          end
      end
  | None =>
      match store_parts i with
      | Some (_, v, a) =>
          match tmp_name a with
          | [x] =>
              match nm_find x slot_of with
              | Some (var, _) => Some (nm_add var v cur, [])
              | None => keep
              end
          | _ => keep
          end
      | None => keep
      end
  end.

(** A renamed block, with the phi arguments it gives its successors:
    under each `Succ-Slot`, the term `Pred-Value`. *)
Definition renamed : Type := (tblock * list (term * term))%type.

(** The slots with a phi at the label l, each with the phi's
    temporary. *)
Definition phis_at (phi_at : nmap (list (term * term))) (l : name) : list (term * term) :=
  match nm_find l phi_at with Some vts => vts | None => [] end.

(** As `block_renamed/5`: the block at the label l renamed from the
    slots' values cur at its start, and their values at its end. Its
    slot phis' temporaries are its slots' first values. *)
Definition block_renamed (slot_of : nmap (term * Z)) (alloc_vars : nmap (list term))
    (phi_at : nmap (list (term * term))) (by_label : nmap tblock)
    (succs : nmap (list name)) (l : name) (cur : nmap term)
  : option (nmap term * renamed) :=
  let* b := nm_find l by_label in
  let cur1 := fold_left (fun c vt => nm_add (fst vt) (tmp (snd vt)) c) (phis_at phi_at l) cur in
  let* r := fold_left (fun acc i =>
                         let* st := acc in
                         let* o := inst_renamed slot_of alloc_vars (fst st) i in
                         Some (fst o, rev_append (snd o) (snd st)))
                      (tb_insts b) (Some (cur1, [])) in
  let* ss := nm_find l succs in
  let args :=
    flat_map (fun s =>
                flat_map (fun vt =>
                            match nm_find (fst vt) (fst r) with
                            | Some v => [(TApp "-" [s; fst vt], TApp "-" [l; v])]
                            | None => []
                            end) (phis_at phi_at s)) ss in
  Some (fst r, (mkTBlock l (tb_phis b) (rev' (snd r)) (tb_jump b), args)).

(** As `subtree_renamed//3`: the blocks of the dominator tree at the
    label l renamed, each from the values at its parent's end, put
    before those of done. The tree is no deeper than the graph has
    labels, the fuel. *)
Fixpoint subtree_renamed (fuel : nat)
    (block : name -> nmap term -> option (nmap term * renamed))
    (kids : nmap (list name)) (l : name) (cur : nmap term) (done : list renamed)
  : option (list renamed) :=
  match fuel with
  | O => None
  | S fuel' =>
      let* r := block l cur in
      let* ks := nm_find l kids in
      fold_left (fun acc k =>
                   let* d := acc in subtree_renamed fuel' block kids k (fst r) d)
                ks (Some (snd r :: done))
  end.

(** As `promote_roots/11`: the blocks bs with the slots of roots as
    temporaries. The graph g, with the immediate dominators idom, is
    that of bs, which are in strict SSA form; addrs and counts are
    their address temporaries and definition counts, and fuel is at
    least the number of defined temporaries.

    A slot's phis are on the iterated dominance frontier of the entry
    and the reachable blocks that set the slot, where the slot is
    live. The blocks are renamed down the dominator tree from the
    entry, where every slot is 0, and each unreachable block from
    all 0. *)
Definition promote_roots (roots : list root) (addrs : addresses) (counts : nmap nat)
    (fuel : nat) (bs : list tblock) (g : cfg) (idom : nmap name) : option (list tblock) :=
  let roots_map := nm_of_list roots in
  let slot_of : nmap (term * Z) :=
    nm_of_list
      (flat_map (fun i =>
                   match let_parts i with
                   | Some (d, _, _, _) =>
                       flat_map (fun x =>
                                   match nm_find x addrs with
                                   | Some (a, off) =>
                                       match nm_find a roots_map with
                                       | Some slots => [(x, address_slot a off slots)]
                                       | None => []
                                       end
                                   | None => []
                                   end) (tmp_name d)
                   | None => []
                   end) (flat_map tb_insts bs)) in
  let root_vars (r : root) := map (fun s => slot_var (fst r) (fst s)) (snd r) in
  let widths :=
    nm_of_list (flat_map (fun r => map (fun s => (slot_var (fst r) (fst s), snd s)) (snd r))
                         roots) in
  let vars := flat_map root_vars roots in
  let alloc_vars := nm_of_list (map (fun r => (fst r, root_vars r)) roots) in
  let gk := nm_of_list (map (fun b => (tb_label b, slot_gen_kill slot_of alloc_vars (tb_insts b)))
                            bs) in
  let reach := reached g in
  let order := rev' (cfg_rpo g)
               ++ filter (fun l => negb (nm_mem l reach)) (map tb_label bs) in
  let live := live_rounds 40 (live_round order (cfg_succs g) gk nm_empty) nm_empty in
  if snd live then None else
  let live_in := fst live in
  let* df := cfg_frontiers g idom in
  let stores : nmap names :=
    fold_left (fun m b =>
                 if nm_mem (tb_label b) df then
                   fold_left (fun m v => nm_add v (tb_label b :: names_at m v) m)
                             (nsort (flat_map (inst_sets slot_of alloc_vars) (tb_insts b))) m
                 else m)
              bs nm_empty in
  let labels := length (cfg_rpo g) in
  let* phi_labels :=
    map_option (fun v =>
                  let work := nsort (cfg_entry g :: names_at stores v) in
                  option_map (fun ls => (v, ls))
                             (iterated_frontier (S (length work + labels)) df live_in v work []))
               vars in
  let phi_at : nmap (list (term * term)) :=
    fst (fold_left (fun st lv =>
                      let t := fresh_phi fuel counts (snd st) in
                      (nm_add (fst lv) ((snd lv, fst t) :: phis_at (fst st) (fst lv)) (fst st),
                       snd t))
                   (flat_map (fun p => map (fun l => (l, fst p)) (snd p)) phi_labels)
                   (nm_empty, 0)) in
  let zero := fold_left (fun c v => nm_add v (const_term 0) c) vars nm_empty in
  let by_label := nm_of_list (map (fun b => (tb_label b, b)) bs) in
  let* kids := dom_children g idom in
  let block := block_renamed slot_of alloc_vars phi_at by_label (cfg_succs g) in
  let* reached_blocks := subtree_renamed (S labels) block kids (cfg_entry g) zero [] in
  let* all :=
    fold_left (fun acc b =>
                 let* done := acc in
                 if nm_mem (tb_label b) reach then Some done else
                 let* r := block (tb_label b) zero in
                 Some (snd r :: done))
              bs (Some reached_blocks) in
  let new_blocks := nm_of_list (map (fun r => (tb_label (fst r), fst r)) all) in
  let args_at : nmap (list term) :=
    fold_left (fun m r =>
                 fold_left (fun m a => nm_add (fst a) (snd a :: names_at m (fst a)) m) (snd r) m)
              all nm_empty in
  map_option
    (fun b =>
       let l := tb_label b in
       let* nb := nm_find l new_blocks in
       let slot_phis :=
         flat_map (fun vt =>
                     match nm_find (fst vt) widths with
                     | Some w =>
                         match slot_class w, nm_find (TApp "-" [l; fst vt]) args_at with
                         | Some k, Some args =>
                             [TApp "phi" [tmp (snd vt); k; TList (nsort args)]]
                         | _, _ => []
                         end
                     | None => []
                     end) (phis_at phi_at l) in
       Some (mkTBlock l (tb_phis nb ++ slot_phis) (tb_insts nb) (tb_jump nb)))
    bs.

(** ## Functions and modules *)

(** As `promote_context/5`, without the records: the blocks bs of a
    function with the given params, in filc [[mode]] or not, its
    promotable allocs gone. The words of the allocs of
    [split_roots] are split first, if the function is in strict SSA
    form and every such alloc then promotes. *)
Definition promote_blocks (filc : bool) (params : list term) (bs : list tblock)
  : option (list tblock) :=
  if calls_setjmp bs then Some bs else
  if negb (existsb (fun i => match let_parts i with
                             | Some (_, _, o, _) => is_alloc o
                             | None => false
                             end) (flat_map tb_insts bs)) then Some bs else
  let names := S (length (all_defs params bs)) in
  let strict (an : analysis) (bs : list tblock) : option (cfg * nmap name) :=
    match term_cfg bs with
    | Some g =>
        match cfg_idoms g with
        | Some idom =>
            if strict_ssa (an_counts an) params bs g idom then Some (g, idom) else None
        | None => None
        end
    | None => None
    end in
  let* an0 := promotable filc params bs in
  let* split :=
    match split_roots filc bs an0 with
    | [] => Some None
    | splits =>
        match strict an0 bs with
        | Some _ =>
            let r := split_words filc splits (an_addrs an0) (an_counts an0) names bs in
            let* an1 := promotable filc params (fst r) in
            if snd r && forallb (fun s => existsb (fun r => term_eqb (fst r) (fst s))
                                                  (an_roots an1)) splits
            then Some (Some (fst r, an1)) else Some None
        | None => Some None
        end
    end in
  let bs0 := match split with Some s => fst s | None => bs end in
  let an := match split with Some s => snd s | None => an0 end in
  match an_roots an with
  | [] => Some bs0
  | roots =>
      match strict an bs0 with
      | Some (g, idom) =>
          promote_roots roots (an_addrs an) (an_counts an)
                        (S (length (all_defs params bs0))) bs0 g idom
      | None => Some bs0
      end
  end.

(** As `promote_module/2`, without the context items. *)
Definition promote_module (m : term) : option term := pass_module promote_blocks m.
