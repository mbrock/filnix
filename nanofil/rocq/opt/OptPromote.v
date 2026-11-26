(** This module implements scalar promotion with full source context transport,
    matching `promote.pl`. It reuses the escape classification, slot selection,
    word splitting, and instruction renaming rules from [Backend.Promote] while
    tracking old-to-new instruction site maps and synthesizing `origin/4`,
    `value/3`, and `site/2` records for promoted slot phis.

    Functions that call `setjmp`, lack allocations, or fail strict SSA remain
    unchanged together with their context records. Word splitting stays only
    when every split allocation subsequently promotes, preserving exact memory
    access counts on allocations that remain in memory. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg Escape Promote.
From Opt Require Import Provenance.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Word splitting with site remapping

    Splitting an overlapped 64-bit access replaces one instruction with four or
    five instructions. Recording each emitted instruction's source site keeps
    the function's context synchronized before promotion runs. *)

(** Rewriting the instructions of one block with [split_inst] collects both the
    emitted instructions and the old-to-new site pairs for [remap_sites]. *)
Fixpoint split_insts_ctx (splits : list (term * list Z)) (addrs : addresses)
    (counts : nmap nat) (fuel : nat) (k lbl : term) (old_idx new_idx : Z)
    (insts : list term) (n : Z) (out_rev : list term) (map_rev : list (term * term))
  : list term * list (term * term) * Z :=
  match insts with
  | [] => (rev' out_rev, rev' map_rev, n)
  | i :: rest =>
      let '(emitted, n1) := split_inst splits addrs counts fuel k i n in
      let '(map_rev1, next_idx) := emission_sites_rev lbl old_idx new_idx emitted map_rev in
      split_insts_ctx splits addrs counts fuel k lbl (old_idx + 1) next_idx
        rest n1 (rev_append emitted out_rev) map_rev1
  end.

(** Splitting overlapped `l` accesses across every block rewrites the block
    list, reports whether any split occurred, and remaps the function's context
    records, matching `split_words/8`. *)
Definition split_words_ctx (filc : bool) (splits : list (term * list Z))
    (addrs : addresses) (counts : nmap nat) (fuel : nat)
    (bs : list tblock) (rs0 : list term)
  : list tblock * list term * bool :=
  let k := TAtom (if filc then "p" else "l") in
  let '(bs_rev, maps_rev, n_end) :=
    fold_left
      (fun st b =>
         let '(bs_r, ms_r, n) := st in
         let '(is', smap, n1) :=
           split_insts_ctx splits addrs counts fuel k (tb_label b) 0 0 (tb_insts b) n [] [] in
         (mkTBlock (tb_label b) (tb_phis b) is' (tb_jump b) :: bs_r,
          smap :: ms_r, n1))
      bs ([], [], 0) in
  let smap := concat (rev' maps_rev) in
  (rev' bs_rev, remap_sites rs0 smap, negb (n_end =? 0)).

(** ## Promoting roots with site and provenance tracking

    Renaming instructions down the dominator tree and across unreachable blocks
    in the exact traversal order of `promote_roots/11` yields both the new
    instruction lists and the site map required to update provenance records. *)

(** One renamed block carries its new block term, successor phi arguments, and
    instruction site map. *)
Definition renamed_ctx : Type := (tblock * list (term * term) * list (term * term))%type.

(** Renaming the instructions of a single block threads slot values while
    building the block's old-to-new site map. *)
Fixpoint insts_renamed_ctx (slot_of : nmap (term * Z)) (alloc_vars : nmap (list term))
    (lbl : term) (old_idx new_idx : Z) (cur : nmap term) (insts : list term)
    (out_rev : list term) (map_rev : list (term * term))
  : option (nmap term * list term * list (term * term)) :=
  match insts with
  | [] => Some (cur, rev' out_rev, rev' map_rev)
  | i :: rest =>
      let* opt_pair_1 := inst_renamed slot_of alloc_vars cur i in let '(cur1, emitted) := opt_pair_1 in
      let '(map_rev1, next_idx) := emission_sites_rev lbl old_idx new_idx emitted map_rev in
      insts_renamed_ctx slot_of alloc_vars lbl (old_idx + 1) next_idx
        cur1 rest (rev_append emitted out_rev) map_rev1
  end.

(** Renaming block [l] from incoming slot values [cur] returns the exit slot
    values together with the renamed block, successor phi arguments, and site
    map, matching `block_renamed/5`. *)
Definition block_renamed_ctx (slot_of : nmap (term * Z)) (alloc_vars : nmap (list term))
    (phi_at : nmap (list (term * term))) (by_label : nmap tblock)
    (succs : nmap (list name)) (l : name) (cur : nmap term)
  : option (nmap term * renamed_ctx) :=
  let* b := nm_find l by_label in
  let cur1 := fold_left (fun c vt => nm_add (fst vt) (tmp (snd vt)) c) (phis_at phi_at l) cur in
  let* opt_pair_2 :=
    insts_renamed_ctx slot_of alloc_vars l 0 0 cur1 (tb_insts b) [] [] in let '(cur2, insts, smap) := opt_pair_2 in
  let* ss := nm_find l succs in
  let args :=
    flat_map
      (fun s =>
         flat_map
           (fun vt =>
              match nm_find (fst vt) cur2 with
              | Some v => [(TApp "-" [s; fst vt], TApp "-" [l; v])]
              | None => []
              end)
           (phis_at phi_at s))
      ss in
  Some (cur2, (mkTBlock l (tb_phis b) insts (tb_jump b), args, smap)).

(** Walking the dominator tree in preorder collects renamed blocks in reverse
    so reversing the final list yields exact `subtree_renamed//3` order. *)
Fixpoint subtree_renamed_ctx (fuel : nat)
    (block : name -> nmap term -> option (nmap term * renamed_ctx))
    (kids : nmap (list name)) (l : name) (cur : nmap term) (done_rev : list renamed_ctx)
  : option (list renamed_ctx) :=
  match fuel with
  | O => None
  | S fuel' =>
      let* opt_pair_3 := block l cur in let '(cur1, r) := opt_pair_3 in
      let* ks := nm_find l kids in
      fold_left
        (fun acc k =>
           let* d := acc in subtree_renamed_ctx fuel' block kids k cur1 d)
        ks (Some (r :: done_rev))
  end.

(** Promoting [roots] produces the rewritten blocks, the full instruction site
    map, the unreversed list of placed phis, the address-to-slot map, and the
    slot-to-width map, matching `promote_roots/11`. *)
Definition promote_roots_ctx (roots : list root) (addrs : addresses) (counts : nmap nat)
    (fuel : nat) (bs : list tblock) (g : cfg) (idom : nmap name)
  : option (list tblock * list (term * term) * list (term * (term * term)) *
            nmap term * nmap term) :=
  let roots_map := nm_of_list roots in
  let slot_of : nmap (term * Z) :=
    nm_of_list
      (flat_map
         (fun i =>
            match let_parts i with
            | Some (d, _, _, _) =>
                flat_map
                  (fun x =>
                     match nm_find x addrs with
                     | Some (a, off) =>
                         match nm_find a roots_map with
                         | Some slots => [(x, address_slot a off slots)]
                         | None => []
                         end
                     | None => []
                     end)
                  (tmp_name d)
            | None => []
            end)
         (flat_map tb_insts bs)) in
  let addr_slot : nmap term :=
    nm_of_list (map (fun p => (fst p, fst (snd p))) (nm_elements slot_of)) in
  let root_vars (r : root) := map (fun s => slot_var (fst r) (fst s)) (snd r) in
  let widths :=
    nm_of_list
      (flat_map (fun r => map (fun s => (slot_var (fst r) (fst s), snd s)) (snd r)) roots) in
  let vars := flat_map root_vars roots in
  let alloc_vars := nm_of_list (map (fun r => (fst r, root_vars r)) roots) in
  let gk :=
    nm_of_list (map (fun b => (tb_label b, slot_gen_kill slot_of alloc_vars (tb_insts b))) bs) in
  let reach := reached g in
  let order :=
    rev' (cfg_rpo g) ++ filter (fun l => negb (nm_mem l reach)) (map tb_label bs) in
  let live := live_rounds 40 (live_round order (cfg_succs g) gk nm_empty) nm_empty in
  if snd live then None else
  let live_in := fst live in
  let* df := cfg_frontiers g idom in
  let stores : nmap names :=
    fold_left
      (fun m b =>
         if nm_mem (tb_label b) df then
           fold_left (fun m v => nm_add v (tb_label b :: names_at m v) m)
                     (nsort (flat_map (inst_sets slot_of alloc_vars) (tb_insts b))) m
         else m)
      bs nm_empty in
  let labels := length (cfg_rpo g) in
  let* phi_labels :=
    map_option
      (fun v =>
         let work := nsort (cfg_entry g :: names_at stores v) in
         option_map (fun ls => (v, ls))
                    (iterated_frontier (S (length work + labels)) df live_in v work []))
      vars in
  let '(placed_rev, phi_at, _) :=
    fold_left
      (fun st lv =>
         let '(pl_r, pa, n) := st in
         let '(t, n1) := fresh_phi fuel counts n in
         ((fst lv, (snd lv, t)) :: pl_r,
          nm_add (fst lv) ((snd lv, t) :: phis_at pa (fst lv)) pa,
          n1))
      (flat_map (fun p => map (fun l => (l, fst p)) (snd p)) phi_labels)
      ([], nm_empty, 0) in
  let placed0 := rev' placed_rev in
  let zero := fold_left (fun c v => nm_add v (const_term 0) c) vars nm_empty in
  let by_label := nm_of_list (map (fun b => (tb_label b, b)) bs) in
  let* kids := dom_children g idom in
  let block := block_renamed_ctx slot_of alloc_vars phi_at by_label (cfg_succs g) in
  let* reached_rev := subtree_renamed_ctx (S labels) block kids (cfg_entry g) zero [] in
  let* all_rev :=
    fold_left
      (fun acc b =>
         let* done := acc in
         if nm_mem (tb_label b) reach then Some done else
         let* opt_pair_4 := block (tb_label b) zero in let '(_, r) := opt_pair_4 in
         Some (r :: done))
      bs (Some reached_rev) in
  let all := rev' all_rev in
  let new_blocks := nm_of_list (map (fun r => (tb_label (fst (fst r)), fst (fst r))) all) in
  let args_at : nmap (list term) :=
    fold_left
      (fun m r =>
         fold_left (fun m a => nm_add (fst a) (snd a :: names_at m (fst a)) m) (snd (fst r)) m)
      all nm_empty in
  let smap := concat (map snd all) in
  let* out_bs :=
    map_option
      (fun b =>
         let l := tb_label b in
         let* nb := nm_find l new_blocks in
         let slot_phis :=
           flat_map
             (fun vt =>
                match nm_find (fst vt) widths with
                | Some w =>
                    match slot_class w, nm_find (TApp "-" [l; fst vt]) args_at with
                    | Some k, Some args =>
                        [TApp "phi" [tmp (snd vt); k; TList (nsort args)]]
                    | _, _ => []
                    end
                | None => []
                end)
             (phis_at phi_at l) in
         Some (mkTBlock l (tb_phis nb ++ slot_phis) (tb_insts nb) (tb_jump nb)))
      bs in
  Some (out_bs, smap, placed0, addr_slot, widths).

(** ## Provenance records for promoted slots

    Each promoted slot receives an `initial_zero` origin and a `slot_stores`
    summary origin combining every store site to that slot. Each placed phi
    receives a generated origin citing that summary and inherits its
    declaration's name hint when the slot covers a scalar whole object at
    offset zero. *)

(** Checking whether C type [ty] matches whole-object scalar slot width [w]
    strips outer `qualified/2` wrappers before checking scalar and pointer
    types, matching `type_slot/2`. *)
Fixpoint type_slot (ty w : term) : bool :=
  match ty with
  | TApp f [_; inner] =>
      if f == "qualified" then type_slot inner w else false
  | TApp f [_] => (f == "ptr") && is_atom "p" w
  | TAtom a =>
      if (a == "char") || (a == "schar") || (a == "uchar") || (a == "bool")
      then is_atom "b" w
      else if (a == "short") || (a == "ushort") then is_atom "h" w
      else if (a == "int") || (a == "uint") then is_atom "w" w
      else if (a == "long") || (a == "ulong") || (a == "llong") || (a == "ullong")
      then is_atom "l" w
      else false
  | _ => false
  end.

(** Creating shared summary origins for every promoted slot builds both the
    slot-to-summary map and the new `origin/4` records, matching
    `slot_records/7`. *)
Fixpoint slot_records (slots : list term) (values stores : nmap (list term))
    (ids : origin_set)
  : origin_set * list (term * term) * list term :=
  match slots with
  | [] => (ids, [], [])
  | slot :: rest =>
      match slot with
      | TApp _ [a; off] =>
          let alloc_os := match nm_find a values with Some os => os | None => [] end in
          let parents := match nm_find slot stores with Some ps => ps | None => [] end in
          let '(ids1, init_id) := fresh_origin_add (TApp "initial" [a; off]) ids in
          let '(ids2, sum_id) := fresh_origin_add (TApp "stores" [a; off]) ids1 in
          let '(ids3, pairs, rs) := slot_records rest values stores ids2 in
          (ids3, (slot, sum_id) :: pairs,
           TApp "origin" [init_id; TAtom "none";
                          TApp "generated" [TAtom "promote"; TAtom "initial_zero"];
                          TList alloc_os]
           :: TApp "origin" [sum_id; TAtom "none";
                             TApp "generated" [TAtom "promote"; TApp "slot_stores" [a; off]];
                             TList (init_id :: parents)]
           :: rs)
      | _ => slot_records rest values stores ids
      end
  end.

(** Creating provenance records for each placed phi emits its generated origin,
    its `value/3` record with optional scalar binding hint, and its `site/2`
    record, matching `phi_records/7`. *)
Fixpoint phi_records (placed : list (term * (term * term)))
    (bindings widths summaries : nmap term) (ids : origin_set)
  : origin_set * list term :=
  match placed with
  | [] => (ids, [])
  | (_, (slot, t)) :: rest =>
      match slot, nm_find slot widths, nm_find slot summaries with
      | TApp _ [a; off], Some width, Some summary =>
          let hint :=
            match off, nm_find a bindings with
            | TInt z, Some ty =>
                if (z =? 0) && type_slot ty width
                then TApp "named" [a; TAtom "value"]
                else TAtom "none"
            | _, _ => TAtom "none"
            end in
          let '(ids1, id) := fresh_origin_add (TApp "promote" [t]) ids in
          let '(ids2, rs) := phi_records rest bindings widths summaries ids1 in
          (ids2,
           TApp "origin" [id; TAtom "none";
                          TApp "generated" [TAtom "promote"; TApp "slot" [a; off; width]];
                          TList [summary]]
           :: TApp "value" [t; hint; TList [id]]
           :: TApp "site" [TApp "phi" [t]; TList [id]]
           :: rs)
      | _, _, _ => phi_records rest bindings widths summaries ids
      end
  end.

(** Collecting every store's origin list per promoted slot builds the conservative
    contributor table used in `promoted_context/7`. *)
Definition collect_slot_stores (bs : list tblock) (addrs : nmap term)
    (sites : nmap (list term)) : nmap (list term) :=
  let pairs :=
    flat_map
      (fun b =>
         let l := tb_label b in
         flat_map
           (fun pi =>
              match store_parts (snd pi) with
              | Some (_, _, addr) =>
                  match tmp_name addr with
                  | [x] =>
                      match nm_find x addrs with
                      | Some slot =>
                          [(slot, site_origins sites (TApp "inst" [l; TInt (fst pi)]))]
                      | None => []
                      end
                  | _ => []
                  end
              | None => []
              end)
           (numbered 0 (tb_insts b)))
      bs in
  nm_of_list
    (map (fun g => (fst g, nsort (concat (snd g)))) (group_pairs_by_key pairs)).

(** Updating the function's context after promoting slots retires any reused
    phi temporary spellings and appends slot summary origins and phi records,
    matching `promoted_context/7`. *)
Definition promoted_context (before rs1 : list term) (bs0 : list tblock)
    (placed : list (term * (term * term))) (addrs widths : nmap term)
  : list term :=
  match before with
  | [] => rs1
  | _ =>
      let sites := site_index before in
      let ids0 := origin_ids before in
      let temps := map (fun p => snd (snd p)) placed in
      let '(ids1, kept) := retire_values rs1 temps ids0 in
      let values :=
        fold_left
          (fun m r =>
             match r with
             | TApp f [a; _; TList os] => if f == "value" then nm_add a os m else m
             | _ => m
             end)
          before nm_empty in
      let bindings :=
        fold_left
          (fun m r =>
             match r with
             | TApp f [a; _; ty; _] => if f == "binding" then nm_add a ty m else m
             | _ => m
             end)
          before nm_empty in
      let stores := collect_slot_stores bs0 addrs sites in
      let slots := nsort (map (fun p => fst (snd p)) placed) in
      let '(ids2, sum_pairs, summaries) := slot_records slots values stores ids1 in
      let summary_ids := nm_of_list sum_pairs in
      let '(_, phis) := phi_records placed bindings widths summary_ids ids2 in
      kept ++ summaries ++ phis
  end.

(** ## Function and module entry points

    The entry points mirror `promote_context/5`, `promote_func/3`, and
    `promote_module/2`, preserving full provenance records on every rewritten
    function. *)

(** Checking whether [bs] is in strict SSA form builds its CFG and immediate
    dominators and verifies dominance with [TermCfg.strict_ssa]. *)
Definition strict_ssa_cfg (counts : nmap nat) (params : list term) (bs : list tblock)
  : option (cfg * nmap name) :=
  match term_cfg bs with
  | Some g =>
      match cfg_idoms g with
      | Some idom =>
          if strict_ssa counts params bs g idom then Some (g, idom) else None
      | None => None
      end
  | None => None
  end.

(** Promoting the slots of one function together with its context records
    matches `promote_context/5`. *)
Definition promote_context (filc : bool) (fn : term) (rs00 : list term)
  : option (term * list term) :=
  match fn with
  | TApp f [name; lk; ret; TList params; TList bs_terms] =>
      if negb (f == "func") then None else
      let* bs00 := map_option term_block bs_terms in
      if calls_setjmp bs00 then Some (fn, rs00) else
      if negb (existsb (fun i => match let_parts i with
                                 | Some (_, _, o, _) => is_alloc o
                                 | None => false
                                 end) (flat_map tb_insts bs00))
      then Some (fn, rs00) else
      let* an0 := promotable filc params bs00 in
      let names0 := S (length (all_defs params bs00)) in
      let* split :=
        match split_roots filc bs00 an0 with
        | [] => Some None
        | splits =>
            match strict_ssa_cfg (an_counts an0) params bs00 with
            | Some _ =>
                let '(bs01, rs01, changed) :=
                  split_words_ctx filc splits (an_addrs an0) (an_counts an0) names0 bs00 rs00 in
                let* an1 := promotable filc params bs01 in
                if changed
                   && forallb (fun s => existsb (fun r => term_eqb (fst r) (fst s))
                                                (an_roots an1)) splits
                then Some (Some (bs01, rs01, an1))
                else Some None
            | None => Some None
            end
        end in
      let '(bs0, rs0, an) :=
        match split with
        | Some triple => triple
        | None => (bs00, rs00, an0)
        end in
      match an_roots an with
      | [] => Some (TApp "func" [name; lk; ret; TList params; TList (map block_term bs0)], rs0)
      | roots =>
          match strict_ssa_cfg (an_counts an) params bs0 with
          | Some (g, idom) =>
              let* opt_pair_5 :=
                promote_roots_ctx roots (an_addrs an) (an_counts an)
                  (S (length (all_defs params bs0))) bs0 g idom in let '(bs, smap, placed, addrs, widths) := opt_pair_5 in
              let rs1 := remap_sites rs0 smap in
              let rs := promoted_context rs0 rs1 bs0 placed addrs widths in
              Some (TApp "func" [name; lk; ret; TList params; TList (map block_term bs)], rs)
          | None =>
              Some (TApp "func" [name; lk; ret; TList params; TList (map block_term bs0)], rs0)
          end
      end
  | _ => None
  end.

(** Promoting every function of an unchecked module while transporting all
    context items matches `promote_module/2`. *)
Definition promote_module (m0 : term) : option term :=
  let* m1 := legacy_context m0 in
  match m1 with
  | TApp f [TList items0] =>
      if negb (f == "module") then None else
      let filc := module_filc items0 in
      let code := code_items items0 in
      let contexts := context_index items0 in
      let* groups :=
        map_option
          (fun it =>
             match it with
             | TApp h xs =>
                 if h == "func" then
                   match xs with
                   | [name; _; _; _; _] =>
                       let rs0 := context_records contexts name in
                       let* opt_pair_6 := promote_context filc it rs0 in let '(fn', rs') := opt_pair_6 in
                       Some (with_context fn' rs')
                   | _ => None
                   end
                 else if h == "data" then if arity 4 xs then Some [it] else None
                 else if h == "alias" then if arity 3 xs then Some [it] else None
                 else None
             | _ => None
             end)
          code in
      Some (TApp "module" [TList (concat groups)])
  | _ => None
  end.
