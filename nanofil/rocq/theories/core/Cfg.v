(** A compiler must ensure that every path to a temporary's use passes
    through a suitable definition before the value is read.
    This module builds each function's control-flow graph and computes
    its [[dominance|dominators]], following the algorithms in cfg.pl.
    The [[validator]] uses this information to check the placement of
    [[temporary]] definitions and the proof instructions that justify later memory accesses.

    The graph records [[block]] successors and predecessors, and a
    depth-first traversal orders the reachable blocks for computing immediate dominators.
    The algorithm follows Cooper, Harvey and Kennedy's "A Simple, Fast
    Dominance Algorithm", repeatedly refining each block's nearest dominating ancestor.
    Numbering the resulting tree lets the validator answer each later
    dominance question by comparing a block number with one ancestor's interval.

    The Prolog implementation sorts graph neighbors, while this model
    preserves each jump's order, so their traversal numbers can differ.
    The immediate dominators are unique, however, and both numberings
    describe the same dominance relationship used by the validator.
    Recursive walks carry explicit [[fuel]] bounds and return no answer
    if exhausted; the bounds below reflect the graph or tree being traversed. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
Import ListNotations.
Local Open Scope Z_scope.

(** A failed intermediate computation stops the remaining computation,
    while a successful one binds its result through the following option notation. *)
Notation "'let*' x ':=' e 'in' b" :=
  (match e with Some x => b | None => None end)
  (at level 200, x name, e at level 100, b at level 200).

(** ## The graph

    A function's jumps determine which blocks can follow each block
    and which blocks are reachable from its entry.
    The graph keeps unreachable predecessors too, because later phi
    checks must account for every incoming edge, not just the executable ones. *)

(** A jump's possible destination labels come from [jump_succs], which
    preserves their written order and includes destinations reached through [[poll|poll edges]]. *)
Definition jump_succs (j : jump) : list name :=
  match j with
  | JGoto t => [edge_label t]
  | JBranch _ t1 t2 => [edge_label t1; edge_label t2]
  | _ => []
  end.

(** A function's control-flow graph uses [cfg] to record its entry,
    reachable traversal order, successor map, and predecessor map over block labels. *)
Record cfg : Type := mkCfg {
  cfg_entry : name; (* This label identifies the function's entry block. *)
  cfg_rpo : list name; (* These reachable labels appear in reverse postorder. *)
  cfg_succs : nmap (list name); (* This map records each block's successor labels. *)
  cfg_preds : nmap (list name) (* This map includes unreachable predecessors as well as reachable ones. *)
}.

(** Visiting successors before finishing their parent gives a postorder,
    which [reverse_postorder] reverses by prepending each finished label to the result.
    Already visited labels are skipped, and each recursive descent
    consumes an entry or successor-list element before the final empty-list call.
    The caller therefore supplies two more fuel units than the number
    of graph edges, covering the entry and final empty-list cases. *)
Fixpoint reverse_postorder (fuel : nat) (ns : list name) (succs : nmap (list name))
    (seen : nmap unit) (post : list name) : option (nmap unit * list name) :=
  match fuel with
  | O => None
  | S fuel' =>
      match ns with
      | [] => Some (seen, post)
      | l :: ls =>
          if nm_mem l seen then reverse_postorder fuel' ls succs seen post
          else
            let* ss := nm_find l succs in
            let* r := reverse_postorder fuel' ss succs (nm_add l tt seen) post in
            let (seen2, post1) := r in
            reverse_postorder fuel' ls succs seen2 (l :: post1)
      end
  end.

(** The first block supplies the entry for [func_cfg], which builds
    successor and predecessor maps before ordering the reachable labels.
    An empty function or a jump to a missing label produces no graph;
    otherwise, predecessor lists retain incoming edges from unreachable blocks too. *)
Definition func_cfg (bs : list block) : option cfg :=
  match bs with
  | [] => None
  | entry :: _ =>
      let succs := nm_of_list (map (fun b => (b_label b, jump_succs (b_jump b))) bs) in
      let edges := flat_map (fun b => map (fun s => (s, b_label b)) (jump_succs (b_jump b))) bs in
      if negb (forallb (fun e => nm_mem (fst e) succs) edges) then None else
      let preds := fold_left (fun m e =>
                                let ps := match nm_find (fst e) m with Some ps => ps | None => [] end in
                                nm_add (fst e) (snd e :: ps) m)
                             edges (nm_of_list (map (fun b => (b_label b, [])) bs)) in
      let* r := reverse_postorder (S (S (length edges))) [b_label entry] succs nm_empty [] in
      Some (mkCfg (b_label entry) (snd r) succs preds)
  end.

(** ## Immediate dominators

    A block dominates another block when every entry path to the
    latter passes through the former, including the block itself.
    The immediate dominator is the nearest distinct such ancestor;
    repeated graph sweeps compute these ancestors using the traversal order. *)

(** Comparing traversal positions requires [labels_numbered], which
    maps each label to its zero-based position in the supplied label list. *)
Definition labels_numbered (ls : list name) : nmap Z :=
  snd (fold_left (fun acc l => (fst acc + 1, nm_add l (fst acc) (snd acc))) ls (0, nm_empty)).

(** Two ancestor chains meet at their nearest common dominator when
    [common_dominator] repeatedly moves the later traversal position toward its parent.
    Each move reduces one position in reverse postorder, so twice the
    number of labels bounds the walk before the chains meet. *)
Fixpoint common_dominator (fuel : nat) (num : nmap Z) (idom : nmap name) (a b : name)
  : option name :=
  match fuel with
  | O => None
  | S fuel' =>
      if name_eqb a b then Some a else
      let* na := nm_find a num in
      let* nb := nm_find b num in
      if nb <? na then let* a1 := nm_find a idom in common_dominator fuel' num idom a1 b
      else let* b1 := nm_find b idom in common_dominator fuel' num idom a b1
  end.

(** One sweep updates a block's parent through [label_idoms], combining
    predecessors whose dominators have already been recorded in the current map.
    Their nearest common dominator becomes the new parent, and a flag
    records whether this update changed the map. *)
Definition label_idoms (preds : nmap (list name)) (num : nmap Z) (fuel : nat)
    (st : option (nmap name * bool)) (b : name) : option (nmap name * bool) :=
  let* st' := st in
  let (idom, changed) := st' in
  let* ps := nm_find b preds in
  match filter (fun p => nm_mem p idom) ps with
  | [] => None
  | first :: others =>
      let* nw := fold_left (fun acc p => let* c := acc in common_dominator fuel num idom p c)
                           others (Some first) in
      match nm_find b idom with
      | Some old => if name_eqb old nw then Some (idom, changed) else Some (nm_add b nw idom, true)
      | None => Some (nm_add b nw idom, true)
      end
  end.

(** Repeated sweeps refine parent choices until an entire sweep leaves
    them unchanged, which [idom_fixpoint] detects through the accumulated change flag.
    The computation returns no answer if its sweep budget expires;
    each sweep also receives a separate bound for walking ancestor chains. *)
Fixpoint idom_fixpoint (fuel : nat) (ls : list name) (preds : nmap (list name)) (num : nmap Z)
    (cfuel : nat) (idom : nmap name) : option (nmap name) :=
  match fuel with
  | O => None
  | S fuel' =>
      let* r := fold_left (label_idoms preds num cfuel) ls (Some (idom, false)) in
      let (idom1, changed) := r in
      if changed then idom_fixpoint fuel' ls preds num cfuel idom1 else Some idom1
  end.

(** Every path to a reachable block passes through its nearest
    dominating ancestor, which [cfg_idoms] computes for each block except the entry.
    The entry temporarily serves as its own parent during computation,
    but the returned map omits that artificial entry. *)
Definition cfg_idoms (g : cfg) : option (nmap name) :=
  match cfg_rpo g with
  | [] => None
  | _ :: rest =>
      let n := length (cfg_rpo g) in
      let num := labels_numbered (cfg_rpo g) in
      let* idom := idom_fixpoint (S (S n)) rest (cfg_preds g) num (S (2 * n))
                                 (nm_add (cfg_entry g) (cfg_entry g) nm_empty) in
      (* The entry serves as its own parent only during the sweeps. *)
      Some (nm_remove (cfg_entry g) idom)
  end.

(** ## The dominator tree's intervals

    A preorder walk visits each ancestor before all of its descendants,
    giving every subtree a consecutive range of block numbers.
    The validator can then test dominance by asking whether one block's
    number lies inside the other block's subtree interval. *)

(** Walking the dominator tree needs child lists, which [dom_children]
    builds by grouping reachable labels beneath their recorded immediate dominators.
    The function processes labels in reverse traversal order and prepends
    each child, leaving siblings ordered by the original reverse postorder. *)
Definition dom_children (g : cfg) (idom : nmap name) : option (nmap (list name)) :=
  fold_left (fun acc l =>
               let* kids := acc in
               match nm_find l idom with
               | Some parent =>
                   let* cs := nm_find parent kids in Some (nm_add parent (l :: cs) kids)
               | None => Some kids
               end)
            (rev (cfg_rpo g)) (Some (nm_of_list (map (fun l => (l, [])) (cfg_rpo g)))).

(** A preorder traversal assigns each label its own number and the
    last number reached below it, as [subtree_intervals] records in the interval map.
    The traversal returns the next unused number and consumes fuel by
    tree depth, which cannot exceed the number of labels. *)
Fixpoint subtree_intervals (fuel : nat) (kids : nmap (list name)) (l : name) (n0 : Z)
    (ivs : nmap (Z * Z)) : option (Z * nmap (Z * Z)) :=
  match fuel with
  | O => None
  | S fuel' =>
      let* ks := nm_find l kids in
      let* r := fold_left (fun acc k => let* a := acc in
                                        subtree_intervals fuel' kids k (fst a) (snd a))
                          ks (Some (n0 + 1, ivs)) in
      let (n, ivs1) := r in
      Some (n, nm_add l (n0, n - 1) ivs1)
  end.

(** Building child lists and numbering from the entry gives each
    reachable label its complete subtree interval through [dom_intervals]. *)
Definition dom_intervals (g : cfg) (idom : nmap name) : option (nmap (Z * Z)) :=
  let* kids := dom_children g idom in
  let* r := subtree_intervals (S (length (cfg_rpo g))) kids (cfg_entry g) 0 nm_empty in
  Some (snd r).

(** A reachable block dominates another when the latter's preorder
    number lies inside its subtree interval, including the ancestor's own number.
    The function [dominates_by_interval] performs this comparison and
    returns false if either label has no recorded interval. *)
Definition dominates_by_interval (ivs : nmap (Z * Z)) (a b : name) : bool :=
  match nm_find a ivs, nm_find b ivs with
  | Some (pa, la), Some (pb, _) => (pa <=? pb) && (pb <=? la)
  | _, _ => false
  end.

(** A validator obtains all block dominance intervals through
    [block_intervals], which builds the graph, computes immediate dominators, and numbers the resulting tree. *)
Definition block_intervals (bs : list block) : option (nmap (Z * Z)) :=
  let* g := func_cfg bs in
  let* idom := cfg_idoms g in
  dom_intervals g idom.
