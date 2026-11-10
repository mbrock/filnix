(** # The control-flow graph of an unchecked function

    The middle end's passes (promote.pl, copy.pl) run before
    pizlonation, on the unchecked IR, which the model has no
    inductive for. So they are on terms, as Pizlonate.v is, and this
    file gives them what cfg.pl, escape.pl and promote.pl give the
    Prolog ones:

    - a function's blocks taken apart ([tblock]);
    - its graph ([term_cfg]), with the successors of a branch sorted
      as `jump_succs/2` sorts them. Cfg.v's graph keeps a jump's own
      order, which the validator does not depend on; these passes do,
      through the reverse postorder. The dominators and their
      intervals are Cfg.v's, which only read the graph;
    - the dominance frontiers ([cfg_frontiers]);
    - what an instruction and a jump read ([inst_uses], [jump_uses]);
    - how often each temporary is defined ([def_counts]);
    - whether the function is in strict SSA form ([strict_ssa]). *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality, written as Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Blocks *)

(** A block `block(Label, Phis, Insts, Jump)` taken apart. *)
Record tblock : Type := mkTBlock {
  tb_label : term; (* its label *)
  tb_phis : list term; (* its phis, `phi(tmp(D), K, Args)` *)
  tb_insts : list term; (* its instructions *)
  tb_jump : term (* its jump *)
}.

(** The block the term b is, if it is one. *)
Definition term_block (b : term) : option tblock :=
  match b with
  | TApp f [l; TList phis; TList insts; j] =>
      if f == "block" then Some (mkTBlock l phis insts j) else None
  | _ => None
  end.

(** The term of the block b. *)
Definition block_term (b : tblock) : term :=
  TApp "block" [tb_label b; TList (tb_phis b); TList (tb_insts b); tb_jump b].

(** The name d when the term p is `phi(tmp(D), K, Args)`. *)
Definition phi_def (p : term) : list term :=
  match p with TApp f [d; _; _] => if f == "phi" then tmp_name d else [] | _ => [] end.

(** The name d when the term p is `param(K, tmp(D))`. *)
Definition param_def (p : term) : list term :=
  match p with TApp f [_; d] => if f == "param" then tmp_name d else [] | _ => [] end.

(** The terms of a list term, none for any other term. *)
Definition listed (t : term) : list term :=
  match t with TList ts => ts | _ => [] end.

(** The pair when the term t is `A-B`. *)
Definition pair_parts (t : term) : option (term * term) :=
  match t with TApp f [a; b] => if f == "-" then Some (a, b) else None | _ => None end.

(** ## The graph *)

(** As `edge_label/2`: the label a jump's target t names, which is
    the label itself or `poll(L)`. *)
Definition target_label (t : term) : term :=
  match t with TApp f [l] => if f == "poll" then l else t | _ => t end.

(** As `jump_succs(Jump, Succs)`: the ordset of the labels the jump
    j can go to. None for a term that is no jump. *)
Definition jump_labels (j : term) : option names :=
  match j with
  | TApp f xs =>
      if f == "goto" then
        match xs with [t] => Some [target_label t] | _ => None end
      else if f == "branch" then
        match xs with
        | [_; t1; t2] => Some (nsort [target_label t1; target_label t2])
        | _ => None
        end
      else if (f == "ret") || (f == "rets") then
        if arity 1 xs then Some [] else None
      else None
  | TAtom a => if (a == "ret") || (a == "unreachable") then Some [] else None
  | _ => None
  end.

(** As `func_cfg(Blocks, Cfg)`: the graph of the blocks bs, whose
    entry is the first. Each block's predecessors are in the order of
    their labels, unreachable ones included. None when a jump is of
    no known shape or goes to a label that is no block's. *)
Definition term_cfg (bs : list tblock) : option cfg :=
  match bs with
  | [] => None
  | entry :: _ =>
      let* pairs := map_option (fun b => option_map (fun ss => (tb_label b, ss))
                                                   (jump_labels (tb_jump b))) bs in
      let succs := nm_of_list pairs in
      let edges := flat_map (fun p => map (fun s => (s, fst p)) (snd p)) pairs in
      if negb (forallb (fun e => nm_mem (fst e) succs) edges) then None else
      let by_pred := msort (fun a b => term_compare (snd a) (snd b)) edges in
      let preds :=
        fold_left (fun m e => nm_add (fst e) (snd e :: match nm_find (fst e) m with
                                                        | Some ps => ps
                                                        | None => []
                                                        end) m)
                  (rev' by_pred) (nm_of_list (map (fun b => (tb_label b, [])) bs)) in
      let* r := reverse_postorder (S (S (length edges))) [tb_label entry] succs nm_empty [] in
      Some (mkCfg (tb_label entry) (snd r) succs preds)
  end.

(** The labels of the graph g that the entry reaches, as a set. *)
Definition reached (g : cfg) : nmap unit :=
  nm_of_list (map (fun l => (l, tt)) (cfg_rpo g)).

(** ## Dominance frontiers *)

(** As `runner_frontiers/6`: the map df with the label b in the
    frontier of every label on the path of immediate dominators from
    runner up to, and not including, stop. The path has at most as
    many labels as the graph, the fuel. *)
Fixpoint runner_frontiers (fuel : nat) (idom : nmap name) (stop b runner : name)
    (df : nmap (list name)) : option (nmap (list name)) :=
  match fuel with
  | O => None
  | S fuel' =>
      if name_eqb runner stop then Some df else
      let* xs := nm_find runner df in
      let* up := nm_find runner idom in
      runner_frontiers fuel' idom stop b up (nm_add runner (b :: xs) df)
  end.

(** As `cfg_frontiers(Cfg, Idom, DF)`: the dominance frontier of
    every reachable label, an ordset. A label with two or more
    reachable predecessors is in the frontier of each label on the
    path from each of them up to its own immediate dominator (Cooper,
    Harvey and Kennedy). *)
Definition cfg_frontiers (g : cfg) (idom : nmap name) : option (nmap names) :=
  let fuel := S (length (cfg_rpo g)) in
  let* df :=
    fold_left
      (fun acc b =>
         let* df := acc in
         let* ps0 := nm_find b (cfg_preds g) in
         match filter (fun p => nm_mem p df) ps0, nm_find b idom with
         | (_ :: _ :: _) as ps, Some stop =>
             fold_left (fun acc r => let* d := acc in runner_frontiers fuel idom stop b r d)
                       ps (Some df)
         | _, _ => Some df
         end)
      (cfg_rpo g) (Some (nm_of_list (map (fun l => (l, [])) (cfg_rpo g)))) in
  Some (nm_of_list (map (fun l => (l, nsort (names_at df l))) (cfg_rpo g))).

(** ## Uses *)

(** As `temps(Values, Names)`: the ordset of the names of the
    temporaries among the values vs. *)
Definition temps (vs : list term) : names := nsort (flat_map tmp_name vs).

(** The value when the term a is `arg(K, V)`. *)
Definition arg_value (a : term) : list term :=
  match a with TApp f [_; v] => if f == "arg" then [v] else [] | _ => [] end.

(** The value when the term p is `Reg-V`, an input of an
    `asm_fixed`. *)
Definition pair_value (p : term) : list term :=
  match pair_parts p with Some (_, v) => [v] | None => [] end.

(** As `inst_uses(Inst, Uses)`: the ordset of the temporaries the
    instruction i reads. None for a term cfg.pl has no clause for;
    the backend's own `uses(I, Extra)` is left out, since no
    unchecked function has it. *)
Definition inst_uses (i : term) : option names :=
  match i with
  | TAtom a => if a == "fence" then Some [] else None
  | TApp f xs =>
      if f == "let" then
        match xs with [_; _; _; TList args] => Some (temps args) | _ => None end
      else if f == "flight" then
        match xs with
        | [_; _; TList args; lw] =>
            let vs := flat_map (fun a => match a with
                                         | TApp g [p] =>
                                             if g == "address" then [p]
                                             else if (g == "tmp") || (g == "const") then [a]
                                             else []
                                         | _ => []
                                         end) args in
            Some (temps (match lw with
                         | TApp g [p] => if g == "lower" then p :: vs else vs
                         | _ => vs
                         end))
        | _ => None
        end
      else if (f == "store") || (f == "atomic_store") then
        match xs with [_; v; a] => Some (temps [v; a]) | _ => None end
      else if f == "access" then
        match xs with [_; a; _; _] => Some (temps [a]) | _ => None end
      else if f == "touch" then
        match xs with [q] => Some (temps [q]) | _ => None end
      else if f == "asm_fixed" then
        match xs with
        | [_; TList ins; _] => Some (temps (flat_map pair_value ins))
        | _ => None
        end
      else if f == "raw_store" then
        match xs with [_; _; v; a] => Some (temps [v; a]) | _ => None end
      else if f == "raw_store_pointer" then
        match xs with [_; v; a; _] => Some (temps [v; a]) | _ => None end
      else if (f == "call") || (f == "raw_call") then
        match xs with
        | [_; g; TList args] => Some (temps (g :: flat_map arg_value args))
        | _ => None
        end
      else if (f == "loc") || (f == "local_alloc") then
        if arity 2 xs then Some [] else None
      else if f == "local_load" then
        if arity 5 xs then Some [] else None
      else if f == "local_store" then
        match xs with [_; v; _; _] => Some (temps [v]) | _ => None end
      else None
  | _ => None
  end.

(** As `jump_uses(Jump, Uses)`: the ordset of the temporaries the
    jump j reads. *)
Definition jump_uses (j : term) : option names :=
  match j with
  | TAtom a => if (a == "ret") || (a == "unreachable") then Some [] else None
  | TApp f xs =>
      if f == "goto" then if arity 1 xs then Some [] else None
      else if f == "branch" then
        match xs with [v; _; _] => Some (temps [v]) | _ => None end
      else if f == "ret" then
        match xs with [v] => Some (temps [v]) | _ => None end
      else if f == "rets" then
        match xs with [TList vs] => Some (temps vs) | _ => None end
      else None
  | _ => None
  end.

(** ## Definitions *)

(** The names that the instruction i defines for escape.pl's
    `def_counts/2` and copy.pl's `temp_classes/3`: a `let`'s, a
    call's results and the outputs of an `asm_fixed`. *)
Definition counted_defs (i : term) : list term :=
  match i with
  | TApp f _ =>
      if (f == "let") || (f == "call") || (f == "asm_fixed") then inst_defs i else []
  | _ => []
  end.

(** As `def_counts(Func, Counts)`: how many definitions each
    temporary has, among the params, the phis and the instructions
    of the blocks bs. *)
Definition def_counts (params : list term) (bs : list tblock) : nmap nat :=
  let count m d := nm_add d (S (match nm_find d m with Some n => n | None => O end)) m in
  fold_left (fun m b =>
               fold_left (fun m i => fold_left count (counted_defs i) m) (tb_insts b)
                         (fold_left count (flat_map phi_def (tb_phis b)) m))
            bs (fold_left count (flat_map param_def params) nm_empty).

(** Whether some temporary of the function has two definitions. *)
Definition defined_twice (counts : nmap nat) (params : list term) (bs : list tblock) : bool :=
  let twice d := match nm_find d counts with Some n => Nat.ltb 1 n | None => false end in
  existsb twice (flat_map param_def params)
  || existsb (fun b => existsb twice (flat_map phi_def (tb_phis b))
                       || existsb (fun i => existsb twice (counted_defs i)) (tb_insts b)) bs.

(** ## Strict SSA *)

(** The terms of xs, each with its position from n. *)
Fixpoint numbered {A : Type} (n : Z) (xs : list A) : list (Z * A) :=
  match xs with
  | [] => []
  | x :: xs' => (n, x) :: numbered (n + 1) xs'
  end.

(** As `strict_ssa(F, Counts, Cfg, Idom)`: every temporary has one
    definition, and in the blocks the entry reaches each definition
    dominates each use. Params and phis are defined at position 0 of
    their block, the instructions from 1, and the jump reads after
    them; a phi argument is read at the end of its predecessor, and
    counts only if that is reachable. A use is defined when its
    definition is earlier in the same block, or in a block that
    dominates it. *)
Definition strict_ssa (counts : nmap nat) (params : list term) (bs : list tblock)
    (g : cfg) (idom : nmap name) : bool :=
  if defined_twice counts params bs then false else
  match dom_intervals g idom with
  | None => false
  | Some ivs =>
      let defs :=
        nm_of_list
          (map (fun d => (d, (cfg_entry g, 0))) (flat_map param_def params)
           ++ flat_map (fun b =>
                          map (fun d => (d, (tb_label b, 0))) (flat_map phi_def (tb_phis b))
                          ++ flat_map (fun pi => map (fun d => (d, (tb_label b, fst pi)))
                                                     (inst_defs (snd pi)))
                                      (numbered 1 (tb_insts b))) bs) in
      let reach := reached g in
      (* Whether t, read in the block l at the position n or at its
         end, is defined before. *)
      let defined (l : name) (n : option Z) (t : name) : bool :=
        match nm_find t defs with
        | Some (dl, dpos) =>
            if name_eqb dl l then match n with Some n => dpos <? n | None => true end
            else dominates_by_interval ivs dl l
        | None => false
        end in
      forallb
        (fun b =>
           let l := tb_label b in
           negb (nm_mem l reach)
           || (forallb (fun p => match p with
                                 | TApp f [_; _; TList args] =>
                                     negb (f == "phi")
                                     || forallb (fun a => match pair_parts a with
                                                          | Some (pred, v) =>
                                                              negb (nm_mem pred reach)
                                                              || forallb (defined pred None)
                                                                         (tmp_name v)
                                                          | None => true
                                                          end) args
                                 | _ => true
                                 end) (tb_phis b)
               && forallb (fun pi => match inst_uses (snd pi) with
                                     | Some us => forallb (defined l (Some (fst pi))) us
                                     | None => true
                                     end) (numbered 1 (tb_insts b))
               && match jump_uses (tb_jump b) with
                  | Some us => forallb (defined l (Some (Z.of_nat (length (tb_insts b)) + 1))) us
                  | None => true
                  end))
        bs
  end.

(** ## Functions *)

(** As ir.pl's `setjmp_func/1`: some block of bs calls setjmp. *)
Definition calls_setjmp (bs : list tblock) : bool :=
  existsb (fun b => existsb (fun i => match i with
                                      | TApp f [_; _; TApp g [_]; _] =>
                                          (f == "let") && (g == "setjmp")
                                      | _ => false
                                      end) (tb_insts b)) bs.

(** Whether the instruction i is a `local_alloc(Name, Size)`. *)
Definition is_local_alloc (i : term) : bool :=
  match i with TApp f [_; _] => f == "local_alloc" | _ => false end.

(** As opt.pl's `optimize_pass/3` with the pass `pass`, which makes
    of a function's name, linkage, result, params and blocks its new
    blocks, in filc [[mode]] or not. A checked module and one with a
    local object are left as they are; else the context items go, as
    `code_items/2` drops them, and the `loc` markers, as
    `legacy_context/2` drops them. None where the Prolog pass fails
    or throws. *)
Definition pass_module (pass : bool -> list term -> list tblock -> option (list tblock))
    (m : term) : option term :=
  match m with
  | TApp f [TList items] =>
      if negb (f == "module") then None
      else if module_checked items
              || existsb (fun it => existsb (fun b => match block_parts b with
                                                      | Some (_, insts, _) =>
                                                          existsb is_local_alloc insts
                                                      | None => false
                                                      end) (func_blocks it)) items
      then Some m
      else
        let filc := module_filc items in
        option_map (fun its => TApp "module" [TList its])
          (map_option
             (fun it =>
                match it with
                | TApp h xs =>
                    if h == "func" then
                      match xs with
                      | [name; lk; ret; TList params; TList blocks] =>
                          let* bs := map_option term_block blocks in
                          let bs := map (fun b => mkTBlock (tb_label b) (tb_phis b)
                                                    (filter (fun i => negb (is_loc i)) (tb_insts b))
                                                    (tb_jump b)) bs in
                          let* bs' := pass filc params bs in
                          Some (TApp "func" [name; lk; ret; TList params;
                                             TList (map block_term bs')])
                      | _ => None
                      end
                    else if h == "data" then if arity 4 xs then Some it else None
                    else if h == "alias" then if arity 3 xs then Some it else None
                    else None
                | _ => None
                end)
             (filter (fun it => negb (is_context it)) items))
  | _ => None
  end.
