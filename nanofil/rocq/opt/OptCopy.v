(** This module implements copy and trivial-phi propagation with full source
    context transport, matching `copy.pl`. It reuses the class table, copy
    chain resolution, substitution rules, and trivial-phi worklist from
    [Backend.Copy] while tracking instruction site maps and appending `alias/4`
    records for eliminated values.

    Removed copies and trivial phis retain their original `value/3` definitions
    as history while recording their surviving replacement in `alias/4`.
    Functions outside strict SSA or calling `setjmp` remain unchanged along
    with their context records. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg Copy.
From Opt Require Import Provenance.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Block substitution with site mapping

    Applying a temporary replacement map removes copied definitions and trivial
    phis while reindexing every kept instruction so [remap_sites] moves
    instruction sites accurately. *)

(** Rewriting the instructions of one block drops replaced copies and collects
    both the surviving instructions and their site map. *)
Fixpoint insts_reps_map (reps : nmap term) (lbl : term) (old_idx new_idx : Z)
    (insts : list term) (out_rev : list term) (map_rev : list (term * term))
  : option (list term * list (term * term)) :=
  match insts with
  | [] => Some (rev' out_rev, rev' map_rev)
  | i0 :: rest =>
      if replaced reps i0 then
        insts_reps_map reps lbl (old_idx + 1) new_idx rest out_rev map_rev
      else
        let* i := inst_reps reps i0 in
        let '(map_rev1, next_idx) := emission_sites_rev lbl old_idx new_idx [i] map_rev in
        insts_reps_map reps lbl (old_idx + 1) next_idx rest (i :: out_rev) map_rev1
  end.

(** Rewriting one block removes replaced phis and copies, substitutes every use,
    and returns the block's old-to-new instruction site map, matching
    `reps_block/4`. *)
Definition reps_block_map (reps : nmap term) (b : tblock)
  : option (tblock * list (term * term)) :=
  let* phis :=
    map_option
      (fun p =>
         match p with
         | TApp f [d; k; TList args] =>
             if f == "phi" then
               let* args' :=
                 map_option
                   (fun a =>
                      let* lv := pair_parts a in
                      let* v' := value_reps reps (snd lv) in
                      Some (TApp "-" [fst lv; v']))
                   args in
               Some (TApp f [d; k; TList args'])
             else None
         | _ => None
         end)
      (filter (fun p => negb (replaced reps p)) (tb_phis b)) in
  let* opt_pair_1 := insts_reps_map reps (tb_label b) 0 0 (tb_insts b) [] [] in let '(insts, smap) := opt_pair_1 in
  let* j := jump_reps reps (tb_jump b) in
  Some (mkTBlock (tb_label b) phis insts j, smap).

(** Rewriting every block of a function returns the updated block list and the
    concatenated instruction site map. *)
Definition reps_blocks_map (reps : nmap term) (bs : list tblock)
  : option (list tblock * list (term * term)) :=
  let* pairs := map_option (reps_block_map reps) bs in
  Some (map fst pairs, concat (map snd pairs)).

(** ## Context transport for substituted values

    Substituting a map of replaced temporaries moves instruction sites, drops
    sites of eliminated phis, updates target values inside existing `alias/4`
    records, and records a new `alias/4` entry for every eliminated `value/3`. *)

(** Testing whether [r] is a phi site for a temporary eliminated by [reps]
    matches `removed_phi_site/2`. *)
Definition removed_phi_site (reps : nmap term) (r : term) : bool :=
  match r with
  | TApp f [TApp g [t]; _] => (f == "site") && (g == "phi") && nm_mem t reps
  | _ => false
  end.

(** Substituting the replacement value inside an existing `alias/4` record
    leaves `historical/1` references untouched, matching `alias_reps/3`. *)
Definition alias_reps (reps : nmap term) (r : term) : term :=
  match r with
  | TApp f [t; v0; h; os] =>
      if f == "alias" then
        match v0 with
        | TApp g [_] =>
            if g == "historical" then r
            else
              match value_reps reps v0 with
              | Some v => TApp "alias" [t; v; h; os]
              | None => r
              end
        | _ =>
            match value_reps reps v0 with
            | Some v => TApp "alias" [t; v; h; os]
            | None => r
            end
        end
      else r
  | _ => r
  end.

(** Updating provenance records after substituting [reps] with site map [smap]
    matches `copied_records/4`. *)
Definition copied_records (reps : nmap term) (smap : list (term * term)) (rs0 : list term)
  : list term :=
  let rs1 := remap_sites rs0 smap in
  let rs2 := filter (fun r => negb (removed_phi_site reps r)) rs1 in
  let rs3 := map (alias_reps reps) rs2 in
  let aliases :=
    flat_map
      (fun r =>
         match r with
         | TApp f [t; hint; os] =>
             if f == "value" then
               match nm_find t reps with
               | Some v => [TApp "alias" [t; v; hint; os]]
               | None => []
               end
             else []
         | _ => []
         end)
      rs0 in
  rs3 ++ aliases.

(** ## Trivial phis and module entry points

    Eliminating trivial phis reuses [Copy.phi_worklist] and [Copy.chain_reps],
    returning the replacement map and site map so context records update in
    tandem. *)

(** Simplifying trivial phis across reachable blocks returns the rewritten
    blocks, the resolved replacement map, and the instruction site map,
    matching `trivial_phis/6`. *)
Definition trivial_phis_ctx (classes : nmap term) (reach : nmap unit) (bs : list tblock)
  : option (list tblock * nmap term * list (term * term)) :=
  let pairs :=
    flat_map
      (fun b =>
         if nm_mem (tb_label b) reach then
           flat_map
             (fun p =>
                match p with
                | TApp f [d; k; TList args] =>
                    if f == "phi" then
                      match tmp_name d,
                            map_option
                              (fun a =>
                                 let* lv := pair_parts a in
                                 copy_value classes k (snd lv))
                              args with
                      | [d'], Some vs => [(d', vs)]
                      | _, _ => []
                      end
                    else []
                | _ => []
                end)
             (tb_phis b)
         else [])
      bs in
  let edges :=
    sort (fun a b => thenc (term_compare (fst a) (fst b)) (term_compare (snd a) (snd b)))
         (flat_map (fun p => map (fun s => (s, fst p)) (flat_map tmp_name (snd p))) pairs) in
  let users :=
    fold_left (fun m e => nm_add (fst e) (snd e :: names_at m (fst e)) m) (rev' edges) nm_empty in
  let n := length pairs in
  let* found :=
    phi_worklist (S (n + n * n)) (nsort (map fst pairs)) (nm_of_list pairs) users [] in
  let* reps := chain_reps (msort (fun a b => term_compare (fst a) (fst b)) found) in
  let* opt_pair_2 := reps_blocks_map reps bs in let '(bs', smap) := opt_pair_2 in
  Some (bs', reps, smap).

(** Propagating copies and trivial phis in one function together with its
    context records matches `copy_context/4`. *)
Definition copy_context (fn : term) (rs0 : list term) : option (term * list term) :=
  match fn with
  | TApp f [name; lk; ret; TList params; TList bs_terms] =>
      if negb (f == "func") then None else
      let* bs0 := map_option term_block bs_terms in
      if calls_setjmp bs0 then Some (fn, rs0) else
      let* g := term_cfg bs0 in
      let* idom := cfg_idoms g in
      if negb (strict_ssa (def_counts params bs0) params bs0 g idom)
      then Some (fn, rs0) else
      let classes := temp_classes params bs0 in
      let reach := reached g in
      let copies :=
        flat_map
          (fun b =>
             if nm_mem (tb_label b) reach then
               flat_map
                 (fun i =>
                    match i with
                    | TApp h [d; k; o; TList [src]] =>
                        if (h == "let") && is_atom "copy" o then
                          match tmp_name d, copy_value classes k src with
                          | [d'], Some v => [(d', v)]
                          | _, _ => []
                          end
                        else []
                    | _ => []
                    end)
                 (tb_insts b)
             else [])
          bs0 in
      let* reps := chain_reps copies in
      let* opt_pair_3 := reps_blocks_map reps bs0 in let '(copied, smap1) := opt_pair_3 in
      let rs1 := copied_records reps smap1 rs0 in
      let* opt_pair_4 := trivial_phis_ctx classes reach copied in let '(bs, phi_reps, smap2) := opt_pair_4 in
      let rs := copied_records phi_reps smap2 rs1 in
      Some (TApp "func" [name; lk; ret; TList params; TList (map block_term bs)], rs)
  | _ => None
  end.

(** Propagating copies and trivial phis across every function in a module while
    preserving context items matches `copy_module/2`. *)
Definition copy_module (m0 : term) : option term :=
  let* m1 := legacy_context m0 in
  match m1 with
  | TApp f [TList items0] =>
      if negb (f == "module") then None else
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
                       let* opt_pair_5 := copy_context it rs0 in let '(fn', rs') := opt_pair_5 in
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
