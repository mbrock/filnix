(** Liveness of temporaries over fused blocks (cfg.pl's
    `temp_liveness/3`): the temporaries live on entry to and on exit
    from each block, reachable or not, the least solution of

    - LiveOut(B) = the union over successors S of LiveIn(S) and the
      temporaries the phis of S read on the edge from B;
    - LiveIn(B) = Gen(B) ∪ (LiveOut(B) − Kill(B)).

    The frame layout (FrameSlots.v) reads it. The sets are ordsets
    of names in the standard order, as the Prolog compiler's are. A
    least solution is the same in whatever order the blocks are
    visited, so this visits them in rounds where cfg.pl keeps a
    worklist. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Validate Maps Cfg.
From Backend Require Import Order Plan Fuse.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Sets of names *)

(** An ordset of names: sorted in the standard order, each once. *)
Notation names := (list name) (only parsing).

(** As `sort/2` on names: the ordset of the names ns. *)
Definition nsort (ns : list name) : names := sort term_compare ns.

(** As `ord_union/3` on names. *)
Definition nunion (xs ys : names) : names := ord_union term_compare xs ys.

(** As `ord_subtract/3` on names. *)
Definition nsubtract (xs ys : names) : names := ord_subtract term_compare xs ys.

(** The ordset the map m has for the label l, empty if it has none. *)
Definition names_at (m : nmap names) (l : name) : names :=
  match nm_find l m with Some ns => ns | None => [] end.

(** ## Gen and Kill *)

(** A block's events so far: the names defined, the names read
    before any definition, and the names defined, in reverse order
    of event. *)
Record events : Type := mkEvents {
  ev_defined : nmap unit;
  ev_gen : list name;
  ev_kill : list name
}.

(** The events ev and then a use of n: n is read first if nothing
    defined it before. *)
Definition use_event (ev : events) (n : name) : events :=
  if nm_mem n (ev_defined ev) then ev
  else mkEvents (ev_defined ev) (n :: ev_gen ev) (ev_kill ev).

(** The events ev and then a definition of n. *)
Definition def_event (ev : events) (n : name) : events :=
  mkEvents (nm_add n tt (ev_defined ev)) (ev_gen ev) (n :: ev_kill ev).

(** As `block_gen_kill/3`: Gen, the temporaries the block b reads
    before it writes them, and Kill, those it writes. Its events are
    the phi definitions, then each instruction's uses before its
    definitions, then the jump's uses. *)
Definition block_gen_kill (b : fblock) : names * names :=
  let ev0 := fold_left (fun ev p => match p with Phi d _ _ => def_event ev d end)
                       (fb_phis b) (mkEvents nm_empty [] []) in
  let ev1 := fold_left (fun ev i =>
                          fold_left (fun ev d => def_event ev (fst d)) (finst_defs i)
                                    (fold_left use_event (finst_uses i) ev))
                       (fb_insts b) ev0 in
  let ev2 := fold_left use_event (jump_uses (fb_jump b)) ev1 in
  (nsort (ev_gen ev2), nsort (ev_kill ev2)).

(** ## Edge uses *)

(** As `phi_edge_uses/2`, for one block: each predecessor p of the
    block mapped to the ordset of the temporaries its phis read on
    the edge from p. *)
Definition block_edge_uses (b : fblock) : nmap names :=
  let pairs := flat_map (fun p => match p with
                                  | Phi _ _ args =>
                                      flat_map (fun a => match snd a with
                                                         | Tmp t => [(fst a, t)]
                                                         | _ => []
                                                         end) args
                                  end) (fb_phis b) in
  let by_pred := fold_left (fun m e => nm_add (fst e) (snd e :: names_at m (fst e)) m)
                           pairs nm_empty in
  fold_left (fun m p => nm_add p (nsort (names_at by_pred p)) m)
            (nsort (map fst pairs)) nm_empty.

(** As `phi_edge_uses/2`: each block's label mapped to its
    [block_edge_uses], for the blocks with phis. *)
Definition phi_edge_uses (bs : list fblock) : nmap (nmap names) :=
  fold_left (fun m b => match fb_phis b with
                        | [] => m
                        | _ => nm_add (fb_label b) (block_edge_uses b) m
                        end) bs nm_empty.

(** ## The fixpoint *)

(** As `live_out/5`: the live-out set of the block l, whose
    successors are ss, given the live-in sets. *)
Definition live_out (eu : nmap (nmap names)) (live_in : nmap names) (l : name)
                    (ss : list name) : names :=
  fold_left (fun out s =>
               let out1 := nunion out (names_at live_in s) in
               match nm_find s eu with
               | Some m => nunion out1 (names_at m l)
               | None => out1
               end) ss [].

(** One round: each block of order in turn takes the live-in set its
    equation gives from the sets so far. The result has the new sets
    and whether any grew. *)
Definition live_round (order : list name) (succs : nmap (list name))
                      (gk : nmap (names * names)) (eu : nmap (nmap names))
                      (live_in : nmap names) : nmap names * bool :=
  fold_left
    (fun st l =>
       let m := fst st in
       let out := live_out eu m l (match nm_find l succs with Some ss => ss | None => [] end) in
       match nm_find l gk with
       | Some (gen, kill) =>
           let new := nunion gen (nsubtract out kill) in
           if names_eqb (names_at m l) new then st else (nm_add l new m, true)
       | None => st
       end)
    order (live_in, false).

(** Up to 2^k rounds of step from m, stopping at the first that
    changes nothing; the flag says whether the last round run still
    changed something. The sets only grow, and there are finitely
    many names and blocks, so enough rounds reach the least solution. *)
Fixpoint live_rounds (k : nat) (step : nmap names -> nmap names * bool) (m : nmap names)
  : nmap names * bool :=
  match k with
  | O => step m
  | S k' =>
      let r := live_rounds k' step m in
      if snd r then live_rounds k' step (fst r) else r
  end.

(** As `temp_liveness/3`: the live-in and the live-out set of every
    block of bs, by label. The blocks are visited in postorder, a
    block after its successors where there is no cycle, then the
    unreachable ones; 2^40 rounds are more than any function needs. *)
Definition temp_liveness (bs : list fblock) : option (nmap names * nmap names) :=
  let* g := func_cfg (map (fun b => mkBlock (fb_label b) [] [] (fb_jump b)) bs) in
  let reached := nm_of_list (map (fun l => (l, tt)) (cfg_rpo g)) in
  let order := rev' (cfg_rpo g)
               ++ filter (fun l => negb (nm_mem l reached)) (map fb_label bs) in
  let gk := nm_of_list (map (fun b => (fb_label b, block_gen_kill b)) bs) in
  let eu := phi_edge_uses bs in
  let r := live_rounds 40 (live_round order (cfg_succs g) gk eu) nm_empty in
  if snd r then None else
  let live_in := fst r in
  let live_outs :=
    nm_of_list (map (fun b => (fb_label b,
                               live_out eu live_in (fb_label b)
                                        (match nm_find (fb_label b) (cfg_succs g) with
                                         | Some ss => ss
                                         | None => []
                                         end))) bs) in
  Some (live_in, live_outs).
