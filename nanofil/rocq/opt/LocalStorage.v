(** This module implements local-storage selection for non-escaping entry
    allocations that survive scalar promotion, matching `local_storage.pl`.
    Eligible allocations in unchecked Fil-C functions become named
    `local_alloc/2` objects whose fixed-offset loads and stores become
    `local_load/5` and `local_store/4` instructions.

    Selection requires strict SSA, no `setjmp` call, a constant entry-block
    allocation of alignment at most sixteen, all accesses strictly inside the
    declared size with supported integer or pointer load types, and a total
    per-function payload and auxiliary budget of 4096 bytes. Plain-mode and
    checked modules remain unchanged. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate TermCfg Escape.
From Opt Require Import Provenance OptIr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Selection and budget

    Candidate objects are collected in allocation order and admitted greedily
    while their rounded payload, auxiliary storage, header, root, and alignment
    slack fit within the remaining budget. *)

(** Testing whether an access lies completely inside an object of [size] bytes
    matches `access_inside/2`. *)
Definition access_inside (size : Z) (a : acc) : bool :=
  match width_bytes (snd a) with
  | Some bytes => (0 <=? fst a) && (fst a + bytes <=? size)
  | None => false
  end.

(** Greedily admitting candidate local objects up to [budget] bytes reserves
    rounded payload and auxiliary space plus 32 bytes of overhead per object,
    matching `within_budget/3`. *)
Fixpoint within_budget (cands : list (term * Z)) (budget : Z) : list (term * Z) :=
  match cands with
  | [] => []
  | (a, size) :: rest =>
      let cost := 2 * (Z.div (size + 15) 16 * 16) + 32 in
      if cost <=? budget then (a, size) :: within_budget rest (budget - cost)
      else within_budget rest budget
  end.

(** Finding an entry-block `let(tmp(A), p, alloc(Align), [const(Size)])` with
    alignment at most sixteen confirms that allocation [a] qualifies for a
    16-aligned local object. *)
Definition entry_local_alloc_ok (entry : list term) (a : term) (size : Z) : bool :=
  existsb
    (fun i =>
       match let_parts i with
       | Some (d, k, TApp g [TInt align], [sz]) =>
           (g == "alloc") && is_atom "p" k && (align <=? 16)
           && match tmp_name d, const_int sz with
              | [a'], Some s => term_eqb a' a && (s =? size)
              | _, _ => false
              end
       | _ => false
       end)
    entry.

(** Selecting eligible local objects for function blocks [bs] excludes objects
    with unsupported float loads and enforces exact bounds and the 4096-byte
    budget, matching `local_objects/4`. *)
Definition select_local_objects (params : list term) (bs : list tblock)
    (addrs : addresses) (counts : nmap nat) : list (term * Z) :=
  match bs with
  | [] => []
  | entry_b :: _ =>
      let entry := tb_insts entry_b in
      let classes := alloc_classes addrs counts params bs in
      let unsupported :=
        fold_left
          (fun m i =>
             match let_parts i with
             | Some (_, _, TApp g [t], [addr]) =>
                 if g == "load" then
                   match load_width t with
                   | Some _ => m
                   | None =>
                       fold_left (fun m' r => nm_add (fst r) tt m') (address_of addrs addr) m
                   end
                 else m
             | _ => m
             end)
          (flat_map tb_insts bs) nm_empty in
      let cands :=
        flat_map
          (fun c =>
             match c with
             | (a, sz_term, Some accesses) =>
                 match const_int sz_term with
                 | Some size =>
                     if (0 <=? size) && negb (nm_mem a unsupported)
                        && entry_local_alloc_ok entry a size
                        && forallb (access_inside size) accesses
                     then [(a, size)]
                     else []
                 | None => []
                 end
             | _ => []
             end)
          classes in
      within_budget cands 4096
  end.

(** ## Rewriting instructions and contexts

    Each selected allocation becomes `local_alloc(A, Size)`, each load or store
    through its address chain becomes `local_load/5` or `local_store/4`, and
    intermediate address calculations for selected objects disappear. *)

(** Rewriting a load or store targeting a selected local object returns its
    local instruction, matching `local_access/4`. *)
Definition local_access (objects : nmap Z) (addrs : addresses) (i : term) : option term :=
  match let_parts i with
  | Some (d, k, TApp g [t], [p]) =>
      if g == "load" then
        match address_of addrs p with
        | [(a, off)] =>
            if nm_mem a objects then Some (TApp "local_load" [d; k; t; a; TInt off])
            else None
        | _ => None
        end
      else None
  | None =>
      match i with
      | TApp f [w; v; p] =>
          if f == "store" then
            match address_of addrs p with
            | [(a, off)] =>
                if nm_mem a objects then Some (TApp "local_store" [w; v; a; TInt off])
                else None
            | _ => None
            end
          else None
      | _ => None
      end
  | _ => None
  end.

(** Rewriting the instructions of one block emits local allocations and
    accesses while collecting the old-to-new site map, matching
    `local_insts/8`. *)
Fixpoint local_insts_ctx (objects : nmap Z) (addrs : addresses) (lbl : term)
    (old_idx new_idx : Z) (insts : list term) (out_rev : list term)
    (map_rev : list (term * term))
  : list term * list (term * term) :=
  match insts with
  | [] => (rev' out_rev, rev' map_rev)
  | i0 :: rest =>
      let emitted :=
        let is_sel_alloc :=
          match let_parts i0 with
          | Some (d, k, o, [sz]) =>
              if is_atom "p" k && is_alloc o then
                match tmp_name d, const_int sz with
                | [a], Some size =>
                    match nm_find a objects with
                    | Some sz' => if sz' =? size then Some (TApp "local_alloc" [a; TInt size]) else None
                    | None => None
                    end
                | _, _ => None
                end
              else None
          | _ => None
          end in
        match is_sel_alloc with
        | Some i => [i]
        | None =>
            match local_access objects addrs i0 with
            | Some i => [i]
            | None =>
                let drop_addr :=
                  match let_parts i0 with
                  | Some (d, k, _, _) =>
                      is_atom "p" k
                      && match tmp_name d with
                         | [x] =>
                             match nm_find x addrs with
                             | Some (a, _) => nm_mem a objects
                             | None => false
                             end
                         | _ => false
                         end
                  | None => false
                  end in
                if drop_addr then [] else [i0]
            end
        end in
      let '(map_rev1, next_idx) := emission_sites_rev lbl old_idx new_idx emitted map_rev in
      local_insts_ctx objects addrs lbl (old_idx + 1) next_idx
        rest (rev_append emitted out_rev) map_rev1
  end.

(** Checking whether the entry block contains any constant-size pointer
    allocation skips CFG construction on functions that cannot qualify. *)
Definition entry_has_const_alloc (bs : list tblock) : bool :=
  match bs with
  | entry :: _ =>
      existsb
        (fun i =>
           match let_parts i with
           | Some (_, k, o, [sz]) =>
               is_atom "p" k && is_alloc o
               && match const_int sz with Some _ => true | None => false end
           | _ => false
           end)
        (tb_insts entry)
  | [] => false
  end.

(** Lowering eligible allocations in one Fil-C function together with its
    context records matches `local_context/4`. *)
Definition local_context (fn : term) (rs0 : list term) : option (term * list term) :=
  match fn with
  | TApp f [name; lk; ret; TList params; TList bs_terms] =>
      if negb (f == "func") then None else
      let* bs0 := map_option term_block bs_terms in
      if calls_setjmp bs0 || func_has_local_objects bs0 || negb (entry_has_const_alloc bs0)
      then Some (fn, rs0) else
      let* g := term_cfg bs0 in
      let* idom := cfg_idoms g in
      let counts := def_counts params bs0 in
      if negb (strict_ssa counts params bs0 g idom) then Some (fn, rs0) else
      let* addrs := address_temps bs0 in
      let objects_list := select_local_objects params bs0 addrs counts in
      match objects_list with
      | [] => Some (fn, rs0)
      | _ =>
          let objects := nm_of_list objects_list in
          let pairs :=
            map (fun b =>
                   let '(is', smap) :=
                     local_insts_ctx objects addrs (tb_label b) 0 0 (tb_insts b) [] [] in
                   (mkTBlock (tb_label b) (tb_phis b) is' (tb_jump b), smap))
                bs0 in
          let bs := map fst pairs in
          let smap := concat (map snd pairs) in
          let rs := remap_sites rs0 smap in
          Some (TApp "func" [name; lk; ret; TList params; TList (map block_term bs)], rs)
      end
  | _ => None
  end.

(** Applying local-storage selection across an unchecked Fil-C module matches
    `local_storage_module/2`, leaving plain-mode and checked modules intact. *)
Definition local_storage_module (m0 : term) : option term :=
  match m0 with
  | TApp f [TList items_in] =>
      if negb (f == "module") then None else
      if negb (module_filc items_in) || module_checked items_in then Some m0 else
      let* m1 := legacy_context m0 in
      match m1 with
      | TApp _ [TList items0] =>
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
                           let* opt_pair_1 := local_context it rs0 in let '(fn', rs') := opt_pair_1 in
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
      end
  | _ => None
  end.
