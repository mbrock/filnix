(** This module implements static function inlining on unchecked IR before
    promotion, matching `inline.pl`. Small mode runs two rounds of leaf
    inlining with optional callee preparation (promotion, copy propagation,
    and simplification); wide mode walks the call graph callees first, admits
    `always_inline`, single-site, and bounded plain callees, and drops
    unreferenced local functions afterward.

    Every inlined call splits its calling block around renamed parameter copies
    and the callee's alpha-renamed body, joins returns through a fresh join
    block and phis, updates successor phi predecessor labels, and transports
    both caller and callee provenance contexts. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg Escape Promote.
From Opt Require Import Provenance OptPromote OptCopy Simplify.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Budgets and data types

    The five size caps mirror `callee_limit/1`, `caller_limit/1`,
    `single_limit/1`, `always_limit/1`, and `grown_limit/1` in `inline.pl`. *)

(** Maximum instruction-plus-jump count of a plain inlined callee. *)
Definition callee_limit : Z := 120.

(** Maximum original size of a plain or single-site caller. *)
Definition caller_limit : Z := 2000.

(** Maximum size of a single-call-site callee under wide inlining. *)
Definition single_limit : Z := 500.

(** Maximum size of an `always_inline` callee under wide inlining. *)
Definition always_limit : Z := 4000.

(** Maximum grown caller size when admitting a single-site callee. *)
Definition grown_limit : Z := 2000.

(** Callee admission classes under wide inlining distinguish `always_inline`,
    single-site, and ordinary bounded callees. *)
Inductive callee_class : Type :=
| CcAlwaysInline
| CcSingle
| CcPlain.

(** An inlining policy distinguishes small mode from wide mode parameterized by
    the caller's original size. *)
Inductive inline_policy : Type :=
| PolSmall
| PolWide (orig : Z).

(** A prepared callee entry packages its function term, context records, size,
    and admission class. *)
Record callee_info : Type := mkCalleeInfo {
  ci_func : term;
  ci_records : list term;
  ci_size : Z;
  ci_class : callee_class
}.

(** A caller's remaining inlining budget pairs the plain budget with the
    caller's current size for wide single-site caps. *)
Record budget_state : Type := mkBudgetState {
  bg_budget : Z;
  bg_size : Z
}.

(** ## Sizing, call graphs, cycles, and references

    Both inlining modes compute block sizes, detect direct-call cycles through
    sink and source peeling, and in wide mode walk functions in post-order and
    garbage-collect unreferenced local functions. *)

(** Counting instructions plus one jump per block computes `func_size/2`. *)
Definition func_size (bs : list tblock) : Z :=
  fold_left (fun s b => s + Z.of_nat (length (tb_insts b)) + 1) bs 0.

(** Counting instructions and jumps directly from a `func/5` term returns zero
    for malformed inputs. *)
Definition func_term_size (fn : term) : option Z :=
  match fn with
  | TApp f [_; _; _; _; TList bs_terms] =>
      if f == "func" then
        let* bs := map_option term_block bs_terms in
        Some (func_size bs)
      else None
  | _ => None
  end.

(** Building a membership map from a list of names matches `name_set/2`. *)
Definition name_set (xs : list term) : nmap unit :=
  fold_left (fun m x => nm_add x tt m) xs nm_empty.

(** Listing direct calls to defined module functions preserves multiplicity,
    matching `direct_calls/3`. *)
Definition direct_calls (defined : nmap unit) (bs : list tblock) : list term :=
  flat_map
    (fun b =>
       flat_map
         (fun i =>
            match i with
            | TApp f [_; TApp g [callee]; _] =>
                if (f == "call") && (g == "global") && nm_mem callee defined
                then [callee] else []
            | _ => []
            end)
         (tb_insts b))
    bs.

(** Counting direct call sites per callee across [calls] matches
    `call_sites/2`. *)
Definition call_sites (calls : list (term * list term)) : nmap Z :=
  fold_left
    (fun m g =>
       let n := match nm_find g m with Some c => c | None => 0 end in
       nm_add g (n + 1) m)
    (flat_map snd calls) nm_empty.

(** Collecting every atom [s] occurring inside `global(S)` anywhere in [t]
    matches `term_global/2`. *)
Fixpoint term_globals (t : term) : list term :=
  match t with
  | TApp f [TAtom s] => if f == "global" then [TAtom s] else []
  | TApp _ args => flat_map term_globals args
  | TList xs => flat_map term_globals xs
  | _ => []
  end.

(** Collecting symbol references from one module item optionally skips the
    callee slot of direct calls, matching `item_reference/3`. *)
Definition item_references (include_direct_callee : bool) (it : term) : list term :=
  match it with
  | TApp f xs =>
      if f == "func" then
        match xs with
        | [_; _; _; _; TList bs_terms] =>
            flat_map
              (fun bt =>
                 match term_block bt with
                 | Some b =>
                     flat_map
                       (fun i =>
                          match i with
                          | TApp cf [_; callee; args] =>
                              if cf == "call" then
                                (if include_direct_callee then
                                   match callee with
                                   | TApp gf [TAtom s] => if gf == "global" then [TAtom s] else []
                                   | _ => []
                                   end
                                 else [])
                                ++ term_globals args
                              else term_globals i
                          | _ => term_globals i
                          end)
                       (tb_insts b)
                     ++ flat_map term_globals (tb_phis b)
                     ++ term_globals (tb_jump b)
                 | None => []
                 end)
              bs_terms
        | _ => []
        end
      else if f == "data" then
        match xs with
        | [_; _; _; TList ds] =>
            flat_map
              (fun d =>
                 match d with
                 | TApp df [_; TApp sf [s; _]] =>
                     if (df == "item") && (sf == "sym") then [s] else []
                 | _ => []
                 end)
              ds
        | _ => []
        end
      else if f == "alias" then
        match xs with [_; _; s] => [s] | _ => [] end
      else []
  | _ => []
  end.

(** Collecting all non-direct-call symbol references across [items] builds the
    exclusion set for single-site callees, matching `other_references/2`. *)
Definition other_references (items : list term) : nmap unit :=
  name_set (flat_map (item_references false) items).

(** Traversing reachable local functions from external roots marks every live
    symbol, matching `reach/4`. *)
Fixpoint reach_locals (fuel : nat) (work : list term) (locals : nmap term)
    (seen : nmap unit) : nmap unit :=
  match fuel, work with
  | O, _ => seen
  | _, [] => seen
  | S fuel', s :: ss =>
      if nm_mem s seen then reach_locals fuel' ss locals seen
      else
        let seen1 := nm_add s tt seen in
        let work1 :=
          match nm_find s locals with
          | Some fn => item_references true fn ++ ss
          | None => ss
          end in
        reach_locals fuel' work1 locals seen1
  end.

(** Dropping local functions and contexts unreachable from exported, weak,
    data, or alias items matches `referenced_items/2`. *)
Definition referenced_items (items0 : list term) : list term :=
  let local_pairs :=
    flat_map
      (fun it =>
         match it with
         | TApp f [n; lk; _; _; _] =>
             if (f == "func") && is_atom "local" lk then [(n, it)] else []
         | _ => []
         end)
      items0 in
  let locals := nm_of_list local_pairs in
  let is_local_func (it : term) : bool :=
    match it with
    | TApp f [_; lk; _; _; _] => (f == "func") && is_atom "local" lk
    | _ => false
    end in
  let roots :=
    flat_map
      (fun it =>
         if negb (is_local_func it) && negb (is_context it)
         then item_references true it
         else [])
      items0 in
  let edge_sum :=
    fold_left (fun acc p => Nat.add acc (length (item_references true (snd p)))) local_pairs O in
  let seen := reach_locals (S (Nat.add (length roots) edge_sum)) roots locals nm_empty in
  filter
    (fun it =>
       match it with
       | TApp f [n; lk; _; _; _] =>
           if (f == "func") && is_atom "local" lk then
             negb (nm_mem n locals && negb (nm_mem n seen))
           else true
       | TApp f [n; _] =>
           if f == "context" then
             negb (nm_mem n locals && negb (nm_mem n seen))
           else true
       | _ => true
       end)
    items0.

(** Peeling nodes with no outgoing edges repeatedly reduces a call graph to its
    potential-cycle core, matching `peel/2`. *)
Fixpoint peel_graph (fuel : nat) (graph : list (term * names)) : list (term * names) :=
  match fuel with
  | O => graph
  | S fuel' =>
      let sinks :=
        nsort (flat_map (fun p => match snd p with [] => [fst p] | _ => [] end) graph) in
      match sinks with
      | [] => graph
      | _ =>
          let graph1 :=
            flat_map
              (fun p =>
                 if ord_mem term_compare (fst p) sinks then []
                 else [(fst p, ord_subtract term_compare (snd p) sinks)])
              graph in
          peel_graph fuel' graph1
      end
  end.

(** Testing whether [target] is reachable from [work] in [graph] checks
    self-reachability for cycle membership, matching `reaches/4`. *)
Fixpoint graph_reaches (fuel : nat) (graph : nmap names) (work : list term)
    (target : term) (seen : nmap unit) : bool :=
  match fuel, work with
  | O, _ => false
  | _, [] => false
  | S fuel', c :: cs =>
      if term_eqb c target then true
      else if nm_mem c seen then graph_reaches fuel' graph cs target seen
      else
        let seen1 := nm_add c tt seen in
        let next := match nm_find c graph with Some ns => ns | None => [] end in
        graph_reaches fuel' graph (next ++ cs) target seen1
  end.

(** Finding the ordset of functions lying on a direct-call cycle peels sinks,
    peels sources on the reversed graph, and tests self-reachability on the
    core, matching `cyclic_functions/3`. *)
Definition cyclic_functions (code : list term) (defined : nmap unit) : names :=
  let pairs :=
    flat_map
      (fun it =>
         match it with
         | TApp f [n; _; _; _; TList bs_terms] =>
             if f == "func" then
               match map_option term_block bs_terms with
               | Some bs => [(n, nsort (direct_calls defined bs))]
               | None => []
               end
             else []
         | _ => []
         end)
      code in
  let core0 := peel_graph (S (length pairs)) pairs in
  let rev_edges :=
    flat_map (fun p => map (fun c => (c, fst p)) (snd p)) core0 in
  let rev_map := nm_of_list (group_pairs_by_key rev_edges) in
  let rev_graph :=
    map (fun p =>
           let ps := match nm_find (fst p) rev_map with Some xs => nsort xs | None => [] end in
           (fst p, ps))
        core0 in
  let core_r := peel_graph (S (length rev_graph)) rev_graph in
  let keep := nsort (map fst core_r) in
  let core :=
    flat_map
      (fun p =>
         if ord_mem term_compare (fst p) keep
         then [(fst p, ord_intersection term_compare (snd p) keep)]
         else [])
      core0 in
  let gmap := nm_of_list core in
  let edge_sum := fold_left (fun acc p => Nat.add acc (length (snd p))) core O in
  let fuel := S (Nat.add (length keep) edge_sum) in
  filter
    (fun n =>
       match nm_find n gmap with
       | Some cs => graph_reaches fuel gmap cs n nm_empty
       | None => false
       end)
    keep.

(** Visiting nodes depth-first in [graph] appends each node after all its
    callees in exact post-order, matching `post_order/3`. *)
Fixpoint visit_post (fuel : nat) (graph : nmap names) (nodes : list term)
    (seen : nmap unit) (order_rev : list term) : nmap unit * list term :=
  match fuel, nodes with
  | O, _ => (seen, order_rev)
  | _, [] => (seen, order_rev)
  | S fuel', n :: rest =>
      if nm_mem n seen then visit_post fuel' graph rest seen order_rev
      else
        let seen1 := nm_add n tt seen in
        let cs := match nm_find n graph with Some xs => xs | None => [] end in
        let '(seen2, order_rev1) := visit_post fuel' graph cs seen1 order_rev in
        visit_post fuel' graph rest seen2 (n :: order_rev1)
  end.

(** Ordering [names] callees first computes the post-order of [graph], matching
    `post_order/3`. *)
Definition post_order (ns : list term) (graph : nmap names) : list term :=
  let edge_sum :=
    fold_left (fun acc p => Nat.add acc (length (snd p))) (nm_elements graph) O in
  let '(_, order_rev) := visit_post (S (Nat.add (length ns) edge_sum)) graph ns nm_empty [] in
  rev' order_rev.

(** ## Eligibility and callee preparation

    Eligibility checks linkage, return shape, absence of `setjmp` and
    `va_args`, allocation promotability or escape rules, and strict SSA. *)

(** Testing whether a block terminator is a return instruction matches
    `returns/1`. *)
Definition is_return_jump (j : term) : bool :=
  match j with
  | TAtom a => a == "ret"
  | TApp f [_] => (f == "ret") || (f == "rets")
  | _ => false
  end.

(** Testing whether an instruction disqualifies a callee from inlining rejects
    `va_args` and non-constant or oversized allocations, matching
    `excluded_inst/2`. *)
Definition excluded_inst (max_alloc : option Z) (i : term) : bool :=
  match let_parts i with
  | Some (_, k, op, args) =>
      if is_atom "va_args" op then true
      else if is_atom "p" k && is_alloc op then
        match args with
        | [v] =>
            match const_int v with
            | Some n =>
                match max_alloc with
                | None => false
                | Some lim => negb (n <=? lim)
                end
            | None => true
            end
        | _ => false
        end
      else false
  | None => false
  end.

(** Testing whether a callee's allocations satisfy mode-specific rules requires
    every non-escaping allocation to promote in Fil-C mode and every allocation
    to promote in plain mode, matching `allocs_ok/2`. *)
Definition allocs_ok (filc : bool) (params : list term) (bs : list tblock) : bool :=
  let has_alloc :=
    existsb (fun i => match let_parts i with Some (_, _, o, _) => is_alloc o | None => false end)
            (flat_map tb_insts bs) in
  if negb has_alloc then true
  else
    match promotable filc params bs with
    | None => false
    | Some an =>
        let is_root (a : term) : bool := existsb (fun r => term_eqb (fst r) a) (an_roots an) in
        if filc then
          forallb
            (fun c =>
               match c with
               | (a, _, Some _) => is_root a
               | _ => true
               end)
            (an_classes an)
        else
          forallb
            (fun i =>
               match let_parts i with
               | Some (d, k, o, _) =>
                   if is_atom "p" k && is_alloc o then
                     match tmp_name d with [a] => is_root a | _ => true end
                   else true
               | None => true
               end)
            (flat_map tb_insts bs)
    end.

(** Checking whether [fn] is structurally inlinable under [max_alloc] matches
    `inlinable/3`. *)
Definition is_inlinable (filc : bool) (max_alloc : option Z) (fn : term) : bool :=
  match fn with
  | TApp f [_; lk; _; TList params; TList bs_terms] =>
      if negb ((f == "func") && is_atom "local" lk) then false else
      match map_option term_block bs_terms with
      | None => false
      | Some bs =>
          negb (calls_setjmp bs)
          && existsb (fun b => is_return_jump (tb_jump b)) bs
          && negb (existsb (excluded_inst max_alloc) (flat_map tb_insts bs))
          && allocs_ok filc params bs
          && match strict_ssa_cfg (def_counts params bs) params bs with
             | Some _ => true
             | None => false
             end
      end
  | _ => false
  end.

(** Checking small-mode callee eligibility excludes tuple and data returns,
    functions exceeding [callee_limit], and non-leaf functions, matching
    `eligible_callee/3`. *)
Definition eligible_callee (filc : bool) (defined : nmap unit) (fn : term) : bool :=
  match fn with
  | TApp f [_; _; ret; _; TList bs_terms] =>
      if negb (f == "func") then false else
      let ret_ok :=
        negb (is_atom "data" ret)
        && match ret with TApp g [_] => negb (g == "tuple") | _ => true end in
      if negb ret_ok then false else
      match map_option term_block bs_terms with
      | None => false
      | Some bs =>
          (func_size bs <=? callee_limit)
          && match direct_calls defined bs with [] => true | _ => false end
          && is_inlinable filc (Some 256) fn
      end
  | _ => false
  end.

(** Checking small-mode caller eligibility excludes `setjmp` functions, cyclic
    functions, and functions above [caller_limit], matching
    `eligible_caller/3`. *)
Definition eligible_caller (cyclic : nmap unit) (orig : Z) (fn : term) : bool :=
  match fn with
  | TApp f [name; _; _; _; TList bs_terms] =>
      if negb (f == "func") then false else
      match map_option term_block bs_terms with
      | None => false
      | Some bs =>
          negb (calls_setjmp bs) && negb (nm_mem name cyclic) && (orig <=? caller_limit)
      end
  | _ => false
  end.

(** Preparing one callee function runs promotion, copy propagation, and
    simplification when `prep_simplified` is true, matching
    `prepared_func/6`. *)
Definition prepared_func (prep_simplified filc : bool) (fn : term) (rs0 : list term)
  : option (term * list term) :=
  if negb prep_simplified then Some (fn, rs0) else
  let* opt_pair_1 := promote_context filc fn rs0 in let '(f1, rs1) := opt_pair_1 in
  let* opt_pair_2 := copy_context f1 rs1 in let '(f2, rs2) := opt_pair_2 in
  simplify_context filc f2 rs2.

(** ## Alpha renaming, block splitting, and provenance transport

    Inlining a callee prefixes every callee temporary and label with `iR_N.`
    chosen to avoid collisions with the caller, converts returns into jumps to
    a fresh join block, and records split sites and `inl(R, N, Id)` callee
    provenance records. *)

(** Prefixing an atom or integer term with string [p] matches `atom_concat/3`. *)
Definition prefix_name (p : string) (x : term) : term :=
  match x with
  | TAtom s => TAtom (String.append p s)
  | TInt z => TAtom (String.append p (decimal z))
  | _ => x
  end.

(** Collecting every parameter, block label, phi, and instruction definition
    name in a function matches `used_names/2`. *)
Definition used_names (fn : term) : names :=
  match fn with
  | TApp f [_; _; _; TList params; TList bs_terms] =>
      if f == "func" then
        match map_option term_block bs_terms with
        | Some bs =>
            nsort
              (flat_map param_def params
               ++ map tb_label bs
               ++ flat_map (fun b => flat_map phi_def (tb_phis b)) bs
               ++ flat_map inst_defs (flat_map tb_insts bs))
        | None => []
        end
      else []
  | _ => []
  end.

(** Choosing a fresh join label `P ++ Base` appends underscores until neither
    `Base` is in [callee_names] nor `P ++ Base` is in [used], matching
    `join_label/5`. *)
Fixpoint join_label (fuel : nat) (p : string) (callee_names : names)
    (used : nmap unit) (base : string) : term :=
  let j0 := TAtom (String.append p base) in
  match fuel with
  | O => j0
  | S fuel' =>
      if negb (ord_mem term_compare (TAtom base) callee_names) && negb (nm_mem j0 used)
      then j0
      else join_label fuel' p callee_names used (String.append base "_")
  end.

(** Choosing the first prefix `iR_N.` from [n0] whose renamed callee names do
    not collide with [used] returns `(N, P, Join)`, matching `fresh_prefix/7`. *)
Fixpoint fresh_prefix (fuel : nat) (round_str : string) (n0 : Z)
    (callee_names : names) (used : nmap unit) : Z * string * term :=
  let p0 := String.append "i" (String.append round_str (String.append "_" (String.append (decimal n0) "."))) in
  match fuel with
  | O => (n0, p0, join_label (S (Nat.add (length callee_names) 64%nat)) p0 callee_names used "join")
  | S fuel' =>
      if negb (existsb (fun x => nm_mem (prefix_name p0 x) used) callee_names)
      then (n0, p0, join_label (S (Nat.add (length callee_names) (length (nm_elements used)))) p0 callee_names used "join")
      else fresh_prefix fuel' round_str (n0 + 1) callee_names used
  end.

(** Renaming every `tmp(X)` anywhere inside term [t] matches
    `renamed_temps/3`. *)
Fixpoint rename_temps (p : string) (t : term) : term :=
  match t with
  | TApp f [x] =>
      if f == "tmp" then TApp "tmp" [prefix_name p x]
      else TApp f [rename_temps p x]
  | TApp f args => TApp f (map (rename_temps p) args)
  | TList xs => TList (map (rename_temps p) xs)
  | _ => t
  end.

(** Renaming a jump target prefixes the underlying label inside `poll/1` or a
    plain label, matching `renamed_target/3`. *)
Definition rename_target (p : string) (tgt : term) : term :=
  match tgt with
  | TApp f [l] => if f == "poll" then TApp "poll" [prefix_name p l] else prefix_name p tgt
  | _ => prefix_name p tgt
  end.

(** Renaming a non-return jump prefixes its labels and operand temporaries,
    matching `renamed_jump/3`. *)
Definition rename_jump (p : string) (j : term) : term :=
  match j with
  | TApp f [t] => if f == "goto" then TApp "goto" [rename_target p t] else rename_temps p j
  | TApp f [v; a; b] =>
      if f == "branch" then
        TApp "branch" [rename_temps p v; rename_target p a; rename_target p b]
      else rename_temps p j
  | _ => rename_temps p j
  end.

(** Renaming a callee block prefixes its label, phis, instructions, and jumps
    while converting returns into `goto(Join)` and collecting join arguments,
    matching `renamed_block/5`. *)
Definition rename_block (p : string) (join_lbl : term) (b : tblock)
  : tblock * list (term * option (list term)) :=
  let l1 := prefix_name p (tb_label b) in
  let phis1 :=
    map (fun ph =>
           match ph with
           | TApp f [d; k; TList ins] =>
               if f == "phi" then
                 let ins1 :=
                   map (fun a =>
                          match pair_parts a with
                          | Some (pl, v) => TApp "-" [prefix_name p pl; rename_temps p v]
                          | None => a
                          end) ins in
                 TApp f [rename_temps p d; k; TList ins1]
               else ph
           | _ => ph
           end)
        (tb_phis b) in
  let is1 := map (rename_temps p) (tb_insts b) in
  match tb_jump b with
  | TApp f [v] =>
      if f == "ret" then
        (mkTBlock l1 phis1 is1 (TApp "goto" [join_lbl]), [(l1, Some [rename_temps p v])])
      else if f == "rets" then
        let vs1 := map (rename_temps p) (listed v) in
        (mkTBlock l1 phis1 is1 (TApp "goto" [join_lbl]), [(l1, Some vs1)])
      else (mkTBlock l1 phis1 is1 (rename_jump p (tb_jump b)), [])
  | TAtom a =>
      if a == "ret" then
        (mkTBlock l1 phis1 is1 (TApp "goto" [join_lbl]), [(l1, None)])
      else (mkTBlock l1 phis1 is1 (rename_jump p (tb_jump b)), [])
  | j0 => (mkTBlock l1 phis1 is1 (rename_jump p j0), [])
  end.

(** Renaming an entire callee returns its renamed blocks, renamed parameters,
    and return edges for the join block, matching `renamed_callee/6`. *)
Definition rename_callee (p : string) (join_lbl : term) (callee : term)
  : option (list tblock * list term * list (term * option (list term))) :=
  match callee with
  | TApp f [_; _; _; TList ps0; TList bs_terms] =>
      if negb (f == "func") then None else
      let* bs0 := map_option term_block bs_terms in
      let ps :=
        map (fun pr =>
               match pr with
               | TApp pf [k; TApp tf [x]] =>
                   if (pf == "param") && (tf == "tmp")
                   then TApp "param" [k; TApp "tmp" [prefix_name p x]]
                   else pr
               | _ => pr
               end)
            ps0 in
      let pairs := map (rename_block p join_lbl) bs0 in
      Some (map fst pairs, ps, concat (map snd pairs))
  | _ => None
  end.

(** Building parameter copies from renamed callee parameters and call arguments
    matches `param_copy/3`. *)
Fixpoint make_param_copies (ps args : list term) : option (list term) :=
  match ps, args with
  | [], [] => Some []
  | TApp pf [k; d] :: ps', TApp af [_; v] :: args' =>
      if (pf == "param") && (af == "arg") then
        let* rest := make_param_copies ps' args' in
        Some (let_term d k (TAtom "copy") [v] :: rest)
      else None
  | _, _ => None
  end.

(** Selecting the [i]-th element of a list (0-based) retrieves one component of
    a tuple return. *)
Fixpoint nth_opt {A : Type} (i : nat) (xs : list A) : option A :=
  match i, xs with
  | _, [] => None
  | O, x :: _ => Some x
  | S i', _ :: rest => nth_opt i' rest
  end.

(** Constructing join-block phis for void, single-value, or tuple call results
    matches `join_phis/3`. *)
Definition join_phis (res : term) (rets : list (term * option (list term))) : list term :=
  match res with
  | TAtom a => if a == "void" then [] else []
  | TApp f [d; k] =>
      if f == "result" then
        let pairs :=
          flat_map
            (fun r =>
               match snd r with
               | Some [v] => [TApp "-" [fst r; v]]
               | _ => []
               end)
            rets in
        [TApp "phi" [d; k; TList pairs]]
      else []
  | TApp f [TList rs] =>
      if f == "tuple" then
        let fix build (i : nat) (xs : list term) :=
          match xs with
          | [] => []
          | TApp rf [d; k] :: rest =>
              if rf == "result" then
                let ins :=
                  flat_map
                    (fun r =>
                       match snd r with
                       | Some vs =>
                           match nth_opt i vs with
                           | Some v => [TApp "-" [fst r; v]]
                           | None => []
                           end
                       | None => []
                       end)
                    rets in
                TApp "phi" [d; k; TList ins] :: build (S i) rest
              else build (S i) rest
          | _ :: rest => build (S i) rest
          end in
        build O rs
      else []
  | _ => []
  end.

(** Testing whether a callee of class [cls] and size [cs] is admitted under
    [policy] and [bg] returns the updated budget, matching `admitted/5`. *)
Definition admit_callee (policy : inline_policy) (cls : callee_class) (cs : Z)
    (bg : budget_state) : option budget_state :=
  match policy with
  | PolSmall =>
      if cs <=? bg_budget bg then Some (mkBudgetState (bg_budget bg - cs) (bg_size bg))
      else None
  | PolWide orig =>
      match cls with
      | CcAlwaysInline =>
          if cs <=? always_limit then Some (mkBudgetState (bg_budget bg) (bg_size bg + cs))
          else None
      | CcSingle =>
          let s := bg_size bg + cs in
          if (orig <=? caller_limit) && (cs <=? single_limit) && (s <=? grown_limit)
          then Some (mkBudgetState (bg_budget bg) s)
          else None
      | CcPlain =>
          if (orig <=? caller_limit) && (cs <=? callee_limit) && (cs <=? bg_budget bg)
          then Some (mkBudgetState (bg_budget bg - cs) (bg_size bg + cs))
          else None
      end
  end.

(** Renaming a callee's provenance records wraps origin and binding identities
    as `inl(Round, N, Id)` and prefixes temporaries and labels with [p],
    matching `callee_context/3`. *)
Definition rename_callee_context (round_t : term) (n : Z) (p : string) (crs : list term)
  : list term :=
  let wid (id : term) : term := TApp "inl" [round_t; TInt n; id] in
  let wtmp (t : term) : term := prefix_name p t in
  let whint (h : term) : term :=
    match h with
    | TApp f [b; role] => if f == "named" then TApp "named" [wid b; role] else h
    | _ => h
    end in
  let wval (v : term) : term :=
    match v with
    | TApp f [x] =>
        if f == "tmp" then TApp "tmp" [wtmp x]
        else if f == "historical" then TApp "historical" [wid x]
        else v
    | _ => v
    end in
  let wsite (s : term) : term :=
    match s with
    | TApp f [l; i] => if f == "inst" then TApp "inst" [wtmp l; i] else s
    | TApp f [x] =>
        if f == "phi" then TApp "phi" [wtmp x]
        else if f == "jump" then TApp "jump" [wtmp x]
        else s
    | _ => s
    end in
  map
    (fun r =>
       match r with
       | TApp f xs =>
           if f == "binding" then
             match xs with [b; nm; ty; loc] => TApp f [wid b; nm; ty; loc] | _ => r end
           else if f == "origin" then
             match xs with
             | [id; loc; d; TList ps] => TApp f [wid id; loc; d; TList (map wid ps)]
             | _ => r
             end
           else if f == "value" then
             match xs with
             | [t; h; TList os] => TApp f [wtmp t; whint h; TList (map wid os)]
             | _ => r
             end
           else if f == "alias" then
             match xs with
             | [t; v; h; TList os] => TApp f [wtmp t; wval v; whint h; TList (map wid os)]
             | _ => r
             end
           else if f == "history" then
             match xs with
             | [id; t; h; TList os; rep] =>
                 let rep' :=
                   match rep with
                   | TApp rf [v] => if rf == "replaced" then TApp "replaced" [wval v] else rep
                   | _ => rep
                   end in
                 TApp f [wid id; wtmp t; whint h; TList (map wid os); rep']
             | _ => r
             end
           else if f == "site" then
             match xs with
             | [s; TList os] => TApp f [wsite s; TList (map wid os)]
             | _ => r
             end
           else r
       | _ => r
       end)
    crs.

(** Metadata recorded for each block split around an inlined call. *)
Record split_info : Type := mkSplitInfo {
  sp_npre : Z;
  sp_ncopies : Z;
  sp_join : term
}.

(** State threaded while inlining calls across a caller's blocks. *)
Record inline_state : Type := mkInlineState {
  is_round_term : term;
  is_round_str : string;
  is_next : Z;
  is_budget : budget_state;
  is_splits : list (term * split_info);
  is_ctxs : list (list term)
}.

(** Finding the first admitted direct call in [insts] splits the list into
    instructions before the call, the call details and callee, the updated
    budget, and the remaining instructions. *)
Fixpoint find_admitted_call (policy : inline_policy) (callees : nmap callee_info)
    (bg : budget_state) (insts : list term) (pre_rev : list term)
  : option (list term * term * list term * callee_info * budget_state * list term) :=
  match insts with
  | [] => None
  | i :: rest =>
      let hit :=
        match i with
        | TApp f [res; TApp g [sym]; TList args] =>
            if (f == "call") && (g == "global") then
              let* ci := nm_find sym callees in
              let* bg' := admit_callee policy (ci_class ci) (ci_size ci) bg in
              Some (rev' pre_rev, res, args, ci, bg', rest)
            else None
        | _ => None
        end in
      match hit with
      | Some found => Some found
      | None => find_admitted_call policy callees bg rest (i :: pre_rev)
      end
  end.

(** Inlining every admitted call inside one block recursively splits the block
    at each admitted call and returns the emitted blocks, final piece label,
    and updated state, matching `block_inlined/7`. *)
Fixpoint block_inlined (fuel : nat) (policy : inline_policy) (callees : nmap callee_info)
    (used : nmap unit) (used_count : nat) (b : tblock) (st : inline_state)
  : option (list tblock * term * inline_state) :=
  let lbl := tb_label b in
  match fuel with
  | O => Some ([b], lbl, st)
  | S fuel' =>
      match find_admitted_call policy callees (is_budget st) (tb_insts b) [] with
      | None => Some ([b], lbl, st)
      | Some (pre, res, args, ci, bg', post) =>
          let cnames := used_names (ci_func ci) in
          let '(n, p, join_lbl) :=
            fresh_prefix (S used_count) (is_round_str st) (is_next st) cnames used in
          let* opt_pair_3 := rename_callee p join_lbl (ci_func ci) in let '(cbs, cps, rets) := opt_pair_3 in
          match cbs with
          | [] => None
          | entry_cb :: _ =>
              let* copies := make_param_copies cps args in
              let pre_is := pre ++ copies in
              let jphis := join_phis res rets in
              let npre := Z.of_nat (length pre) in
              let nc := Z.of_nat (length copies) in
              let ctx_rs := rename_callee_context (is_round_term st) n p (ci_records ci) in
              let st1 :=
                mkInlineState (is_round_term st) (is_round_str st) (n + 1) bg'
                  ((lbl, mkSplitInfo npre nc join_lbl) :: is_splits st)
                  (ctx_rs :: is_ctxs st) in
              let* opt_pair_4 :=
                block_inlined fuel' policy callees used used_count
                  (mkTBlock join_lbl jphis post (tb_jump b)) st1 in let '(join_out, last_lbl, st2) := opt_pair_4 in
              Some ((mkTBlock lbl (tb_phis b) pre_is (TApp "goto" [tb_label entry_cb]) :: cbs)
                    ++ join_out,
                    last_lbl, st2)
          end
      end
  end.

(** Rewriting phi predecessor labels after block splitting moves each split
    block label to its final piece label, matching `moved_phis/3`. *)
Definition move_block_phis (moves : nmap term) (b : tblock) : tblock :=
  let phis :=
    map (fun ph =>
           match ph with
           | TApp f [d; k; TList ins] =>
               if f == "phi" then
                 let ins' :=
                   map (fun a =>
                          match pair_parts a with
                          | Some (from, v) =>
                              let to := match nm_find from moves with Some t => t | None => from end in
                              TApp "-" [to; v]
                          | None => a
                          end) ins in
                 TApp f [d; k; TList ins']
               else ph
           | _ => ph
           end)
        (tb_phis b) in
  mkTBlock (tb_label b) phis (tb_insts b) (tb_jump b).

(** Generating [nc] copies of origin list [os] at indices `npre..npre+nc-1`
    matches `copy_sites/5`. *)
Fixpoint copy_sites (k : nat) (lbl : term) (idx : Z) (os : term) : list term :=
  match k with
  | O => []
  | S k' => TApp "site" [TApp "inst" [lbl; TInt idx]; os] :: copy_sites k' lbl (idx + 1) os
  end.

(** Remapping one caller context record through all block splits and moves
    matches `split_record//3`. *)
Fixpoint split_record (fuel : nat) (splits : nmap split_info) (moves : nmap term)
    (r : term) : list term :=
  match fuel with
  | O => [r]
  | S fuel' =>
      match r with
      | TApp f [TApp g [l; TInt i]; os] =>
          if (f == "site") && (g == "inst") then
            match nm_find l splits with
            | Some sp =>
                if i <? sp_npre sp then [r]
                else if i =? sp_npre sp then
                  copy_sites (Z.to_nat (sp_ncopies sp)) l (sp_npre sp) os
                else
                  split_record fuel' splits moves
                    (TApp "site" [TApp "inst" [sp_join sp; TInt (i - sp_npre sp - 1)]; os])
            | None => [r]
            end
          else [r]
      | TApp f [TApp g [l]; os] =>
          if (f == "site") && (g == "jump") then
            match nm_find l moves with
            | Some t => [TApp "site" [TApp "jump" [t]; os]]
            | None => [r]
            end
          else [r]
      | _ => [r]
      end
  end.

(** Inlining admitted calls into one caller function updates both its blocks
    and its provenance records, matching `inline_func/8`. *)
Definition inline_func (round_t : term) (round_str : string) (policy : inline_policy)
    (orig : Z) (callees : nmap callee_info) (fn : term) (rs0 : list term)
  : option (term * list term) :=
  match fn with
  | TApp f [name; lk; ret; TList params; TList bs_terms] =>
      if negb (f == "func") then None else
      let* bs0 := map_option term_block bs_terms in
      let has_hit :=
        existsb
          (fun i =>
             match i with
             | TApp cf [_; TApp gf [g]; _] =>
                 (cf == "call") && (gf == "global") && nm_mem g callees
             | _ => false
             end)
          (flat_map tb_insts bs0) in
      if negb has_hit then Some (fn, rs0) else
      let used_list := used_names fn in
      let used := name_set used_list in
      let used_count := length used_list in
      let s0 := func_size bs0 in
      let half_orig := Z.div orig 2 in
      let budget0 := Z.max half_orig callee_limit - (s0 - orig) in
      let bg0 := mkBudgetState budget0 s0 in
      let init_st := mkInlineState round_t round_str 1 bg0 [] [] in
      let* opt_pair_5 :=
        fold_left
          (fun acc b =>
             let* opt_pair_19 := acc in let '(bs_r, mv_r, st) := opt_pair_19 in
             let lbl := tb_label b in
             let* opt_pair_20 :=
               block_inlined (S (length (tb_insts b))) policy callees used used_count b st in let '(out_bs, last_lbl, st1) := opt_pair_20 in
             let mv_r1 := if term_eqb last_lbl lbl then mv_r else (lbl, last_lbl) :: mv_r in
             Some (rev_append out_bs bs_r, mv_r1, st1))
          bs0 (Some ([], [], init_st)) in let '(bs_rev, moves_rev, st_end) := opt_pair_5 in
      let bs1 := rev' bs_rev in
      let move_index := nm_of_list (rev' moves_rev) in
      let bs := map (move_block_phis move_index) bs1 in
      let split_index := nm_of_list (is_splits st_end) in
      let ctx_rs := concat (rev' (is_ctxs st_end)) in
      let fuel := S (length (is_splits st_end)) in
      let caller_rs := flat_map (split_record fuel split_index move_index) rs0 in
      Some (TApp "func" [name; lk; ret; TList params; TList (map block_term bs)],
            caller_rs ++ ctx_rs)
  | _ => None
  end.

(** ## Small-mode and wide-mode drivers

    Small mode runs two leaf rounds with optional callee preparation between
    them. Wide mode traverses functions in call-graph post-order, prepares
    eligible callees, and prunes unreferenced local functions. *)

(** Preparing local leaf callees between small-mode rounds matches
    `prepared/3`. *)
Definition prepare_small_module (prep_simplified : bool) (m0 : term) : option term :=
  if negb prep_simplified then Some m0 else
  match m0 with
  | TApp f [TList items0] =>
      if negb (f == "module") then None else
      let filc := module_filc items0 in
      let code := code_items items0 in
      let contexts := context_index items0 in
      let defined :=
        name_set (flat_map (fun it => match it with TApp h [n; _; _; _; _] => if h == "func" then [n] else [] | _ => [] end) code) in
      let* groups :=
        map_option
          (fun it =>
             match it with
             | TApp h [name; lk; _; _; TList bs_terms] =>
                 if h == "func" then
                   let rs0 := context_records contexts name in
                   if is_atom "local" lk then
                     let* bs := map_option term_block bs_terms in
                     if (func_size bs <=? 4 * callee_limit)
                        && match direct_calls defined bs with [] => true | _ => false end
                     then
                       let* opt_pair_6 := prepared_func true filc it rs0 in let '(fn', rs') := opt_pair_6 in
                       Some (with_context fn' rs')
                     else Some (with_context it rs0)
                   else Some (with_context it rs0)
                 else Some [it]
             | _ => Some [it]
             end)
          code in
      Some (TApp "module" [TList (concat groups)])
  | _ => None
  end.

(** Running one small-mode inlining round matches `inline_round/4`. *)
Definition inline_round (round_n : Z) (sizes : nmap Z) (m0 : term) : option term :=
  match m0 with
  | TApp f [TList items0] =>
      if negb (f == "module") then None else
      let filc := module_filc items0 in
      let code := code_items items0 in
      let contexts := context_index items0 in
      let defined :=
        name_set (flat_map (fun it => match it with TApp h [n; _; _; _; _] => if h == "func" then [n] else [] | _ => [] end) code) in
      let* callee_pairs :=
        map_option
          (fun fn =>
             match fn with
             | TApp _ [n; _; _; _; _] =>
                 let* sz := func_term_size fn in
                 Some (n, mkCalleeInfo fn (context_records contexts n) sz CcPlain)
             | _ => None
             end)
          (filter (eligible_callee filc defined) code) in
      let callees := nm_of_list callee_pairs in
      let cyclic := name_set (cyclic_functions code defined) in
      let rstr := decimal round_n in
      let* groups :=
        map_option
          (fun it =>
             match it with
             | TApp h [name; _; _; _; _] =>
                 if h == "func" then
                   let rs0 := context_records contexts name in
                   let* orig := nm_find name sizes in
                   let* opt_pair_7 :=
                     if eligible_caller cyclic orig it
                     then inline_func (TInt round_n) rstr PolSmall orig callees it rs0
                     else Some (it, rs0) in let '(fn', rs') := opt_pair_7 in
                   Some (with_context fn' rs')
                 else Some [it]
             | _ => Some [it]
             end)
          code in
      Some (TApp "module" [TList (concat groups)])
  | _ => None
  end.

(** Running two small-mode inlining rounds matches `inline_module/2,3` for
    `plain` and `simplified`. *)
Definition inline_module_small (prep_simplified : bool) (m0 : term) : option term :=
  let* m1 := legacy_context m0 in
  match m1 with
  | TApp f [TList items1] =>
      if negb (f == "module") then None else
      let* size_pairs :=
        map_option
          (fun it =>
             match it with
             | TApp h [n; _; _; _; _] =>
                 if h == "func" then
                   let* sz := func_term_size it in
                   Some [(n, sz)]
                 else Some []
             | _ => Some []
             end)
          items1 in
      let sizes := nm_of_list (concat size_pairs) in
      let* m2 := inline_round 1 sizes m1 in
      let* m3 := prepare_small_module prep_simplified m2 in
      inline_round 2 sizes m3
  | _ => None
  end.

(** Classifying a wide-mode callee from its attribute map, call-site count, and
    non-call references matches `callee_class/5`. *)
Definition classify_wide_callee (name : term) (attrs : nmap string) (nsites : Z)
    (others : nmap unit) : option callee_class :=
  match nm_find name attrs with
  | Some a => if a == "always_inline" then Some CcAlwaysInline else None
  | None =>
      if (nsites =? 1) && negb (nm_mem name others) then Some CcSingle
      else Some CcPlain
  end.

(** Testing the pre-preparation size cap of a wide-mode callee class matches
    `prepare_limit/2`. *)
Definition prepare_limit_ok (cls : callee_class) (sz : Z) : bool :=
  match cls with
  | CcAlwaysInline => true
  | CcSingle => sz <=? 4 * single_limit
  | CcPlain => sz <=? 4 * callee_limit
  end.

(** Running wide-mode bottom-up inlining with attributes and dead local
    function cleanup matches `wide_module/4`. *)
Definition inline_module_wide (prep_simplified : bool) (attrs_list : list (string * string))
    (m0 : term) : option term :=
  let* m1 := legacy_context m0 in
  match m1 with
  | TApp f [TList items1] =>
      if negb (f == "module") then None else
      let filc := module_filc items1 in
      let code := code_items items1 in
      let contexts := context_index items1 in
      let ns :=
        flat_map
          (fun it => match it with TApp h [n; _; _; _; _] => if h == "func" then [n] else [] | _ => [] end)
          code in
      let defined := name_set ns in
      let cyclic := name_set (cyclic_functions code defined) in
      let attrs :=
        nm_of_list
          (map (fun p => (TAtom (fst p), snd p))
               (msort (fun a b => atom_compare (fst a) (fst b)) attrs_list)) in
      let funcs :=
        nm_of_list
          (flat_map
             (fun it => match it with TApp h [n; _; _; _; _] => if h == "func" then [(n, it)] else [] | _ => [] end)
             code) in
      let* calls :=
        map_option
          (fun it =>
             match it with
             | TApp h [n; _; _; _; TList bs_terms] =>
                 if h == "func" then
                   let* bs := map_option term_block bs_terms in
                   Some [(n, direct_calls defined bs)]
                 else Some []
             | _ => Some []
             end)
          code in
      let calls_flat := concat calls in
      let sites := call_sites calls_flat in
      let others := other_references items1 in
      let graph := nm_of_list (map (fun p => (fst p, nsort (snd p))) calls_flat) in
      let order := post_order ns graph in
      let* opt_pair_8 :=
        fold_left
          (fun acc name =>
             let* opt_pair_21 := acc in let '(callees0, out0) := opt_pair_21 in
             let* fn0 := nm_find name funcs in
             let rs0 := context_records contexts name in
             match fn0 with
             | TApp _ [_; lk; _; _; TList bs0_terms] =>
                 let* bs0 := map_option term_block bs0_terms in
                 let orig := func_size bs0 in
                 let* opt_pair_22 :=
                   if negb (calls_setjmp bs0) && negb (nm_mem name cyclic)
                   then inline_func (TAtom "w") "w" (PolWide orig) orig callees0 fn0 rs0
                   else Some (fn0, rs0) in let '(fn1, rs1) := opt_pair_22 in
                 let can_prepare :=
                   if is_atom "local" lk && negb (nm_mem name cyclic) then
                     let* nsites := nm_find name sites in
                     let* cls := classify_wide_callee name attrs nsites others in
                     let* s1 := func_term_size fn1 in
                     if prepare_limit_ok cls s1 then Some cls else None
                   else None in
                 let* opt_pair_23 :=
                   match can_prepare with
                   | Some cls =>
                       let* opt_pair_29 := prepared_func prep_simplified filc fn1 rs1 in let '(fn2, rs2) := opt_pair_29 in
                       if is_inlinable filc None fn2 then
                         let* cs := func_term_size fn2 in
                         Some (fn2, rs2, nm_add name (mkCalleeInfo fn2 rs2 cs cls) callees0)
                       else Some (fn2, rs2, callees0)
                   | None => Some (fn1, rs1, callees0)
                   end in let '(fn_out, rs_out, callees1) := opt_pair_23 in
                 Some (callees1, nm_add name (fn_out, rs_out) out0)
             | _ => None
             end)
          order (Some (nm_empty, nm_empty)) in let '(_, out_map) := opt_pair_8 in
      let* groups :=
        map_option
          (fun it =>
             match it with
             | TApp h [name; _; _; _; _] =>
                 if h == "func" then
                   let* opt_pair_9 := nm_find name out_map in let '(fn_out, rs_out) := opt_pair_9 in
                   Some (with_context fn_out rs_out)
                 else Some [it]
             | _ => Some [it]
             end)
          code in
      let items2 := concat groups in
      let items3 := referenced_items items2 in
      let items := if Bool.eqb (module_filc items3) filc then items3 else items2 in
      Some (TApp "module" [TList items])
  | _ => None
  end.
