(** The control-flow graph (CFG) of a function and its
    [[dominance|dominators]], transcribed from cfg.pl: `func_cfg/2`,
    `cfg_idoms/2` (Cooper, Harvey and Kennedy, "A Simple, Fast
    Dominance Algorithm"), `dom_children/3`, `dom_intervals/3` and
    `dominates_by_interval/3`. The [[validator]] asks "does A dominate
    B?" for every use of every [[temporary]], and the dominator tree's
    preorder intervals answer it in constant time, as they do for
    ir.pl.

    ## Parts

    | Gallina | cfg.pl |
    |---|---|
    | `jump_succs` | `jump_succs/2` |
    | `cfg`, `func_cfg` | `func_cfg/2`, `reverse_postorder/6` |
    | `cfg_idoms` | `cfg_idoms/2`, `label_idoms/5`, `common_dominator/5` |
    | `dom_children`, `dom_intervals` | the same, `subtree_intervals/6` |
    | `dominates_by_interval` | the same |

    ## Orders

    cfg.pl keeps a block's successors and predecessors as ordsets,
    sorted in the standard order of terms. The model keeps a jump's
    own order and does not sort. That changes the reverse postorder,
    the order of the sweeps and the preorder numbers, but not the
    immediate dominators, which are unique, nor the relation
    `dominates_by_interval` states, which is all ir.pl reads from
    them.

    ## Fuel

    The Prolog recursions end because each visits a block at most once
    or walks up a finite tree; the Gallina ones carry [[fuel]] that bounds
    the same walk, and give no answer if it runs out, which a correct
    bound never lets happen. The bounds are noted at each. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
Import ListNotations.
Local Open Scope Z_scope.

(** Option binding: `let* x := e in b` is b with x the value of e, or
    none if e has none. *)
Notation "'let*' x ':=' e 'in' b" :=
  (match e with Some x => b | None => None end)
  (at level 200, x name, e at level 100, b at level 200).

(** ## The graph *)

(** As `jump_succs(Jump, Succs)`: the labels the jump j can go to, in
    its own order, a [[poll|poll edge]]'s included. *)
Definition jump_succs (j : jump) : list name :=
  match j with
  | JGoto t => [edge_label t]
  | JBranch _ t1 t2 => [edge_label t1; edge_label t2]
  | _ => []
  end.

(** As `cfg(Entry, Rpo, Succs, Preds)`: a function's control-flow
    graph, over its [[block]] labels. *)
Record cfg : Type := mkCfg {
  cfg_entry : name; (* the entry block's label *)
  cfg_rpo : list name; (* the labels reachable from the entry, in reverse postorder *)
  cfg_succs : nmap (list name); (* each block's successors *)
  cfg_preds : nmap (list name) (* each block's predecessors, unreachable ones included *)
}.

(** As `reverse_postorder(Ns, Succs, Seen0, Seen, Post0, Post)`: depth
    first from each of Ns in turn, a label's successors before the
    labels after it; Post has the reverse postorder in front of Post0.
    Along any chain of nested calls, each call but the last takes one
    element of some list the walk has met (the entry or a block's
    successors), and the last is on an empty list, so the fuel is two
    more than the number of edges. *)
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

(** As `func_cfg(Blocks, Cfg)`: the graph of the blocks bs, whose entry
    is the first block; each block's predecessors include unreachable
    ones. No graph when an edge targets a label that is no block's,
    where `label_preds/3` fails. *)
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

(** ## Immediate dominators *)

(** As `labels_numbered(Labels, 0, Pairs)`: each label of ls with its
    position in the list, from 0. *)
Definition labels_numbered (ls : list name) : nmap Z :=
  snd (fold_left (fun acc l => (fst acc + 1, nm_add l (fst acc) (snd acc))) ls (0, nm_empty)).

(** As `common_dominator(Num, Idom, A, B, Common)`: the nearest common
    dominator of the labels a and b in the tree of immediate
    dominators idom found so far, num being reverse postorder numbers.
    Walk up from the later of a and b until they meet. Each step moves
    one of them to its immediate dominator (idom), earlier in reverse
    postorder, so twice the number of labels is enough fuel. *)
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

(** As `label_idoms(Preds, Num, B, Idom0-Changed0, Idom-Changed)`: one
    step of a sweep, at the label b. Its immediate dominator becomes
    the [common_dominator] of its predecessors that have one so far,
    and the flag records whether it changed. *)
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

(** As `idom_fixpoint(Labels, Preds, Num, Idom0, Idom)`: sweeps of
    [label_idoms] over the labels ls in reverse postorder until one
    changes nothing. A sweep changes an idom only
    to a label earlier in reverse postorder, and the sweeps settle
    within the graph's loop nesting depth plus two (Cooper, Harvey and
    Kennedy), so one more sweep than labels is enough fuel. *)
Fixpoint idom_fixpoint (fuel : nat) (ls : list name) (preds : nmap (list name)) (num : nmap Z)
    (cfuel : nat) (idom : nmap name) : option (nmap name) :=
  match fuel with
  | O => None
  | S fuel' =>
      let* r := fold_left (label_idoms preds num cfuel) ls (Some (idom, false)) in
      let (idom1, changed) := r in
      if changed then idom_fixpoint fuel' ls preds num cfuel idom1 else Some idom1
  end.

(** As `cfg_idoms(Cfg, Idom)`: each reachable label of the graph g but
    the entry, with its immediate dominator, the nearest block every
    path from the entry to it passes through. *)
Definition cfg_idoms (g : cfg) : option (nmap name) :=
  match cfg_rpo g with
  | [] => None
  | _ :: rest =>
      let n := length (cfg_rpo g) in
      let num := labels_numbered (cfg_rpo g) in
      let* idom := idom_fixpoint (S (S n)) rest (cfg_preds g) num (S (2 * n))
                                 (nm_add (cfg_entry g) (cfg_entry g) nm_empty) in
      (* del_assoc(Entry, ...): the entry is its own idom only during the
         sweeps. *)
      Some (nm_remove (cfg_entry g) idom)
  end.

(** ## The dominator tree's intervals *)

(** As `dom_children(Cfg, Idom, Kids)`: each reachable label's children
    in the [[dominance|dominator tree]], the labels it is the immediate
    dominator of, in reverse postorder. *)
Definition dom_children (g : cfg) (idom : nmap name) : option (nmap (list name)) :=
  fold_left (fun acc l =>
               let* kids := acc in
               match nm_find l idom with
               | Some parent =>
                   let* cs := nm_find parent kids in Some (nm_add parent (l :: cs) kids)
               | None => Some kids
               end)
            (rev (cfg_rpo g)) (Some (nm_of_list (map (fun l => (l, [])) (cfg_rpo g)))).

(** As `subtree_intervals(L, Kids, N0, N, Intervals0, Intervals)`:
    number the subtree at the label l in preorder from n0, giving each
    label its number and the last number of its subtree, and return the
    next free number. The tree's depth is at most the number of
    labels, the fuel. *)
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

(** As `dom_intervals(Cfg, Idom, Intervals)`: each reachable label's
    preorder number in the dominator tree and the last one of its
    subtree, its dominator interval. *)
Definition dom_intervals (g : cfg) (idom : nmap name) : option (nmap (Z * Z)) :=
  let* kids := dom_children g idom in
  let* r := subtree_intervals (S (length (cfg_rpo g))) kids (cfg_entry g) 0 nm_empty in
  Some (snd r).

(** As `dominates_by_interval(Intervals, A, B)`: the label a
    [[dominance|dominates]] b, both reachable: every path from the
    entry to b passes through a, which holds when b's preorder number
    lies in a's interval. A label dominates itself. *)
Definition dominates_by_interval (ivs : nmap (Z * Z)) (a b : name) : bool :=
  match nm_find a ivs, nm_find b ivs with
  | Some (pa, la), Some (pb, _) => (pa <=? pb) && (pb <=? la)
  | _, _ => false
  end.

(** The dominator intervals of a function's blocks bs: [func_cfg],
    [cfg_idoms] and [dom_intervals] in turn, as `definitions_dominate/3`
    and `stage_sources/4` compute them. *)
Definition block_intervals (bs : list block) : option (nmap (Z * Z)) :=
  let* g := func_cfg bs in
  let* idom := cfg_idoms g in
  dom_intervals g idom.
