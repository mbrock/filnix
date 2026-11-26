(** Pointer-as-integer laundering for unchecked Fil-C IR modules.

    This module ports nanofil/src/launder.pl to pure Gallina over the shared
    [term] representation of [Term.v]. When an integer computed from a single
    pointer capability is converted back to a pointer by `itop`, laundering
    recovers that capability and adjusts its address by the computed offset.
    The abstract interpretation runs on the SSA form produced by
    [Backend.Promote.promote_blocks], and the rewrite inserts shadow pointer
    allocs, shadow stores, shadow loads, capability phis, and offset
    computations while remapping provenance instruction sites. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg Escape Promote.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality, matching Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Abstract values and instruction classifiers

    Each `w` or `l` integer temporary carries an abstract capability source:
    [AvBot] for no capability source, [AvDef] for a single pointer source, or
    [AvTop] for conflicting sources. These helpers classify integer classes,
    value-merging operations, and memory writes in the same way as launder.pl. *)

Inductive launder_av : Type :=
| AvBot
| AvDef (id : term)
| AvTop.

Definition av_eqb (a b : launder_av) : bool :=
  match a with
  | AvBot => match b with AvBot => true | _ => false end
  | AvTop => match b with AvTop => true | _ => false end
  | AvDef x => match b with AvDef y => term_eqb x y | _ => false end
  end.

Definition av_merge (a b : launder_av) : launder_av :=
  match a with
  | AvBot => b
  | AvTop => AvTop
  | AvDef x =>
      match b with
      | AvBot => AvDef x
      | AvDef y => if term_eqb x y then AvDef x else AvTop
      | AvTop => AvTop
      end
  end.

Definition int_class (k : term) : bool :=
  is_atom "w" k || is_atom "l" k.

Definition merge_op (op : term) : bool :=
  match op with
  | TAtom a =>
      (a == "add") || (a == "sub") || (a == "mul") || (a == "div")
      || (a == "udiv") || (a == "rem") || (a == "urem") || (a == "and")
      || (a == "or") || (a == "xor") || (a == "sar") || (a == "shr")
      || (a == "shl") || (a == "neg") || (a == "copy") || (a == "cast")
  | TApp f [_] => f == "ext"
  | _ => false
  end.

Definition pure_value_op (k op : term) : bool :=
  if is_atom "p" k then
    is_atom "add" op || is_atom "sub" op
  else
    int_class k && merge_op op && negb (is_atom "copy" op).

Definition writes_memory (op : term) : bool :=
  match op with
  | TAtom a => a == "va_arg"
  | TApp f [_] => negb ((f == "load") || (f == "ext") || (f == "alloc"))
  | TApp f [_; _] => negb (f == "cmp")
  | _ => true
  end.

Definition inst_def_name (i : term) : option term :=
  match i with
  | TApp f (d :: _) =>
      if (f == "phi") || (f == "let") then
        match tmp_name d with
        | [t] => Some t
        | _ => None
        end
      else None
  | _ => None
  end.

(** ## Copy resolution, block value numbering, and fixpoint equations

    Value numbering inside each promoted block merges repeated pure pointer
    or integer expressions and repeated pointer loads with no intervening
    memory write. The fixpoint then solves the laundering equations over the
    promoted SSA function. *)

Fixpoint resolve_root (fuel : nat) (copies : nmap term) (v : term) : term :=
  match fuel with
  | O => v
  | S fuel' =>
      match tmp_name v with
      | [t] =>
          match nm_find t copies with
          | Some v' => resolve_root fuel' copies v'
          | None => v
          end
      | _ => v
      end
  end.

Fixpoint constant_base (fuel rfuel : nat) (copies : nmap term) (p : term) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match p with
      | TApp f [_] =>
          if f == "const" then true
          else if f == "tmp" then
            match tmp_name p with
            | [t] =>
                match nm_find (TApp "base" [t]) copies with
                | Some b => constant_base fuel' rfuel copies (resolve_root rfuel copies b)
                | None => false
                end
            | _ => false
            end
          else false
      | _ => false
      end
  end.

Definition block_loads (rfuel : nat) (copies0 : nmap term) (b : tblock) : nmap term :=
  fst (fold_left
         (fun st i =>
            let '(cs0, seen0) := st in
            match let_parts i with
            | Some (d, k, op, args) =>
                match tmp_name d with
                | [t] =>
                    if is_atom "p" k &&
                       match op, args with
                       | TApp lf [lt], [a] => (lf == "load") && is_atom "p" lt
                       | _, _ => false
                       end then
                      match args with
                      | [a] =>
                          let r := resolve_root rfuel cs0 a in
                          match nm_find r seen0 with
                          | Some t0 => (nm_add t (tmp t0) cs0, seen0)
                          | None => (cs0, nm_add r t seen0)
                          end
                      | _ => (cs0, seen0)
                      end
                    else if pure_value_op k op then
                      let rs := map (resolve_root rfuel cs0) args in
                      let key := TApp "op" [k; op; TList rs] in
                      let '(cs1, seen1) :=
                        match nm_find key seen0 with
                        | Some t0 => (nm_add t (tmp t0) cs0, seen0)
                        | None => (cs0, nm_add key t seen0)
                        end in
                      let cs2 :=
                        if is_atom "p" k then
                          match args with
                          | b0 :: _ => nm_add (TApp "base" [t]) b0 cs1
                          | [] => cs1
                          end
                        else cs1 in
                      (cs2, seen1)
                    else if negb (writes_memory op) then (cs0, seen0)
                    else (cs0, nm_empty)
                | _ =>
                    if negb (writes_memory op) then (cs0, seen0) else (cs0, nm_empty)
                end
            | None => (cs0, nm_empty)
            end)
         (tb_insts b) (copies0, nm_empty)).

Inductive launder_eq_rule : Type :=
| EqPtoi (id : term)
| EqMerge (args : list term)
| EqPhi (vs : list term).

Definition inst_equation (rfuel : nat) (copies : nmap term) (i : term)
  : option (term * launder_eq_rule) :=
  match i with
  | TApp f [d; k; op; TList args] =>
      if f == "let" then
        match tmp_name d with
        | [t] =>
            if is_atom "l" k && is_atom "ptoi" op then
              match args with
              | [p] =>
                  let id := resolve_root rfuel copies p in
                  if constant_base rfuel rfuel copies id then Some (t, EqMerge [])
                  else Some (t, EqPtoi id)
              | _ => Some (t, EqMerge [])
              end
            else if int_class k && merge_op op then
              Some (t, EqMerge args)
            else None
        | _ => None
        end
      else None
  | TApp f [d; k; TList ins] =>
      if f == "phi" then
        if int_class k then
          match tmp_name d with
          | [t] =>
              let vs := flat_map (fun e => match pair_parts e with
                                           | Some (_, v) => [v]
                                           | None => []
                                           end) ins in
              Some (t, EqPhi vs)
          | _ => None
          end
        else None
      else None
  | _ => None
  end.

Definition value_state (rfuel : nat) (copies : nmap term) (states : nmap launder_av)
  (v : term) : launder_av :=
  match tmp_name (resolve_root rfuel copies v) with
  | [t] => match nm_find t states with Some av => av | None => AvBot end
  | _ => AvBot
  end.

Definition rule_value (rfuel : nat) (copies : nmap term) (states : nmap launder_av)
  (d : term) (rule : launder_eq_rule) : launder_av :=
  match rule with
  | EqPtoi id => AvDef id
  | EqMerge args =>
      fold_left (fun acc v => av_merge acc (value_state rfuel copies states v)) args AvBot
  | EqPhi vs =>
      if existsb (fun v => negb (av_eqb (value_state rfuel copies states v) AvBot)) vs then
        AvDef (TApp "phi" [d])
      else AvBot
  end.

Fixpoint solve_fixpoint (fuel rfuel : nat) (eqs : list (term * launder_eq_rule))
  (copies : nmap term) (s0 : nmap launder_av) : nmap launder_av :=
  match fuel with
  | O => s0
  | S fuel' =>
      let '(s1, changed) :=
        fold_left
          (fun st eq =>
             let '(cur, ch) := st in
             let '(d, rule) := eq in
             let nw := rule_value rfuel copies cur d rule in
             let old := match nm_find d cur with Some av => av | None => AvBot end in
             if av_eqb nw old then (cur, ch)
             else if av_eqb nw AvBot then (cur, ch)
             else (nm_add d nw cur, true))
          eqs (s0, false) in
      if changed then solve_fixpoint fuel' rfuel eqs copies s1 else s1
  end.

(** ## Function analysis and shadow slot selection

    The analysis identifies volatile local allocations from context records,
    runs value numbering and the abstract fixpoint over the promoted blocks,
    and assigns fresh `ld.N` shadow allocation names to tracked non-pointer
    promotable slots that receive a non-bottom integer value. *)

Record launder_an : Type := mkLaunderAn {
  la_rfuel : nat;
  la_copies : nmap term;
  la_states : nmap launder_av;
  la_defs : nmap term;
  la_addrs : addresses;
  la_shadows : nmap term;
  la_alloc_shadows : nmap (list term);
}.

Definition volatile_allocs (rs : list term) : names :=
  let vol_bs : nmap unit :=
    fold_left
      (fun m r =>
         match r with
         | TApp f [b; _; TApp qf [TList qs; _]; _] =>
             if (f == "binding") && (qf == "qualified")
                && existsb (is_atom "volatile") qs then
               nm_add b tt m
             else m
         | _ => m
         end)
      rs nm_empty in
  let as_list :=
    flat_map
      (fun r =>
         match r with
         | TApp f [a; TApp nf [b; kind]; _] =>
             if (f == "value") && (nf == "named") && is_atom "address" kind
                && nm_mem b vol_bs then
               [a]
             else []
         | _ => []
         end)
      rs in
  nsort as_list.

Definition used_name_set (params : list term) (bs : list tblock) : nmap unit :=
  let pnames := flat_map param_def params in
  let bnames :=
    flat_map (fun b =>
                flat_map (fun i => match inst_def_name i with Some t => [t] | None => [] end)
                         (tb_phis b ++ tb_insts b)) bs in
  nm_of_list (map (fun t => (t, tt)) (pnames ++ bnames)).

Fixpoint fresh_prefixed (fuel : nat) (prefix : string) (used : nmap unit) (n0 : Z)
  : term * Z :=
  let n1 := n0 + 1 in
  let cand := TAtom (prefix ++ "." ++ decimal n1) in
  match fuel with
  | O => (cand, n1)
  | S fuel' =>
      if nm_mem cand used then fresh_prefixed fuel' prefix used n1
      else (cand, n1)
  end.

Definition has_alloc_inst (bs : list tblock) : bool :=
  existsb (fun i => match let_parts i with
                    | Some (_, _, o, _) => is_alloc o
                    | None => false
                    end) (flat_map tb_insts bs).

Definition run_analysis (params : list term) (bs0 bsP : list tblock) (rs : list term)
  : launder_an :=
  let '(roots0, addrs) :=
    if calls_setjmp bs0 || negb (has_alloc_inst bs0) then ([], nm_empty)
    else
      match promotable true params bs0 with
      | Some an => (an_roots an, an_addrs an)
      | None => ([], nm_empty)
      end in
  let vol := volatile_allocs rs in
  let roots := filter (fun r => negb (nmem (fst r) vol)) roots0 in
  let root_map : nmap (list acc) := nm_of_list roots in
  let vol_loads : nmap unit :=
    fold_left
      (fun m i =>
         match load_parts i with
         | Some (d, _, _, x) =>
             match nm_find x addrs, tmp_name d with
             | Some (a, _), [t] => if nmem a vol then nm_add t tt m else m
             | _, _ => m
             end
         | None => m
         end)
      (flat_map tb_insts bs0) nm_empty in
  let copies0 : nmap term :=
    fold_left
      (fun m i =>
         match let_parts i with
         | Some (d, _, op, [v]) =>
             if is_atom "copy" op then
               match tmp_name d with
               | [t] => if nm_mem t vol_loads then m else nm_add t v m
               | _ => m
               end
             else m
         | _ => m
         end)
      (flat_map tb_insts bsP) nm_empty in
  let total_p :=
    fold_left (fun acc b => (acc + length (tb_phis b) + length (tb_insts b))%nat) bsP 0%nat in
  let rfuel := S (total_p + 16)%nat in
  let copies := fold_left (block_loads rfuel) bsP copies0 in
  let eqs :=
    flat_map (fun b =>
                flat_map (fun i =>
                            match inst_equation rfuel copies i with
                            | Some (d, rule) =>
                                if nm_mem d vol_loads then [] else [(d, rule)]
                            | None => []
                            end) (tb_phis b ++ tb_insts b)) bsP in
  let states := solve_fixpoint (S (2 * length eqs + 4))%nat rfuel eqs copies nm_empty in
  let defs : nmap term :=
    fold_left
      (fun m b =>
         fold_left
           (fun m1 i =>
              match inst_def_name i with
              | Some t => nm_add t i m1
              | None => m1
              end)
           (tb_phis b ++ tb_insts b) m)
      bs0 nm_empty in
  let tracked_raw :=
    flat_map
      (fun i =>
         match store_parts i with
         | Some (w, v, x_term) =>
             if is_atom "p" w then []
             else
               match tmp_name x_term with
               | [x] =>
                   match nm_find x addrs with
                   | Some (a, off) =>
                       match nm_find a root_map with
                       | Some slots =>
                           if existsb (acc_eqb (off, w)) slots &&
                              negb (av_eqb (value_state rfuel copies states v) AvBot) then
                             [slot_var a off]
                           else []
                       | None => []
                       end
                   | None => []
                   end
               | _ => []
               end
         | None => []
         end)
      (flat_map tb_insts bs0) in
  let tracked := nsort tracked_raw in
  let used := used_name_set params bs0 in
  let ufuel := S (length params +
                  fold_left (fun acc b => (acc + length (tb_phis b) + length (tb_insts b))%nat)
                            bs0 0%nat + 8)%nat in
  let '(shadow_pairs_rev, _) :=
    fold_left
      (fun st slot =>
         let '(ps, n0) := st in
         let '(sh, n1) := fresh_prefixed ufuel "ld" used n0 in
         ((slot, sh) :: ps, n1))
      tracked ([], 0) in
  let shadow_pairs := rev shadow_pairs_rev in
  let shadows := nm_of_list shadow_pairs in
  let alloc_shadows :=
    fold_left
      (fun m p =>
         let '(slot, sh) := p in
         match pair_parts slot with
         | Some (a, _) =>
             let cur := match nm_find a m with Some xs => xs | None => [] end in
             nm_add a (sh :: cur) m
         | None => m
         end)
      shadow_pairs_rev nm_empty in
  mkLaunderAn rfuel copies states defs addrs shadows alloc_shadows.

Definition an_state (an : launder_an) (v : term) : launder_av :=
  value_state (la_rfuel an) (la_copies an) (la_states an) v.

Definition tracked_shadow (an : launder_an) (x : term) : option term :=
  match nm_find x (la_addrs an) with
  | Some (a, off) => nm_find (slot_var a off) (la_shadows an)
  | None => None
  end.

(** ## Capability demand discovery

    Starting from each `itop` of a single-capability integer and each store to
    a tracked slot, demand traversal allocates fresh `lc.N` temporaries for
    required shadow loads, capability phis, and offset arithmetic. *)

Record demand_st : Type := mkDemandSt {
  ds_n : Z;
  ds_ufuel : nat;
  ds_used : nmap unit;
  ds_reals : nmap term;
  ds_loads : nmap term;
  ds_phis : nmap (term * list term);
  ds_itops : nmap (term * term);
}.

Definition ds_fresh (st : demand_st) : term * demand_st :=
  let '(t, n1) := fresh_prefixed (ds_ufuel st) "lc" (ds_used st) (ds_n st) in
  (t, mkDemandSt n1 (ds_ufuel st) (ds_used st)
                 (ds_reals st) (ds_loads st) (ds_phis st) (ds_itops st)).

Definition ds_put_real (t r : term) (st : demand_st) : demand_st :=
  mkDemandSt (ds_n st) (ds_ufuel st) (ds_used st)
             (nm_add t r (ds_reals st)) (ds_loads st) (ds_phis st) (ds_itops st).

Definition ds_put_load (t c : term) (st : demand_st) : demand_st :=
  mkDemandSt (ds_n st) (ds_ufuel st) (ds_used st)
             (ds_reals st) (nm_add t c (ds_loads st)) (ds_phis st) (ds_itops st).

Definition ds_put_phi (t c : term) (ins : list term) (st : demand_st) : demand_st :=
  mkDemandSt (ds_n st) (ds_ufuel st) (ds_used st)
             (ds_reals st) (ds_loads st) (nm_add t (c, ins) (ds_phis st)) (ds_itops st).

Definition ds_put_itop (d i1 i2 : term) (st : demand_st) : demand_st :=
  mkDemandSt (ds_n st) (ds_ufuel st) (ds_used st)
             (ds_reals st) (ds_loads st) (ds_phis st) (nm_add d (i1, i2) (ds_itops st)).

Fixpoint resolve_real (fuel : nat) (an : launder_an) (v : term) (st : demand_st)
  : term * demand_st :=
  match fuel with
  | O => (const_term 0, st)
  | S fuel' =>
      match tmp_name v with
      | [t] =>
          match nm_find t (ds_reals st) with
          | Some r => (r, st)
          | None =>
              match nm_find t (la_defs an) with
              | None => (const_term 0, st)
              | Some inst =>
                  match inst with
                  | TApp f [_; k; op; TList args] =>
                      if f == "let" then
                        if is_atom "l" k && is_atom "ptoi" op then
                          match args with
                          | [p] => (p, ds_put_real t p st)
                          | _ => (const_term 0, ds_put_real t (const_term 0) st)
                          end
                        else if is_atom "copy" op then
                          match args with
                          | [a] =>
                              let '(r, st1) := resolve_real fuel' an a st in
                              (r, ds_put_real t r st1)
                          | _ => (const_term 0, ds_put_real t (const_term 0) st)
                          end
                        else
                          match op, args with
                          | TApp lf [_], [x_term] =>
                              if lf == "load" then
                                match tmp_name x_term with
                                | [x] =>
                                    match tracked_shadow an x with
                                    | Some _ =>
                                        let '(c, st1) := ds_fresh st in
                                        let r := tmp c in
                                        (r, ds_put_real t r (ds_put_load t c st1))
                                    | None => (const_term 0, ds_put_real t (const_term 0) st)
                                    end
                                | _ => (const_term 0, ds_put_real t (const_term 0) st)
                                end
                              else
                                match an_state an (tmp t) with
                                | AvDef id =>
                                    match find (fun a =>
                                                  match an_state an a with
                                                  | AvDef id1 => term_eqb id1 id
                                                  | _ => false
                                                  end) args with
                                    | Some a =>
                                        let '(r, st1) := resolve_real fuel' an a st in
                                        (r, ds_put_real t r st1)
                                    | None => (const_term 0, ds_put_real t (const_term 0) st)
                                    end
                                | _ => (const_term 0, ds_put_real t (const_term 0) st)
                                end
                          | _, _ =>
                              match an_state an (tmp t) with
                              | AvDef id =>
                                  match find (fun a =>
                                                match an_state an a with
                                                | AvDef id1 => term_eqb id1 id
                                                | _ => false
                                                end) args with
                                  | Some a =>
                                      let '(r, st1) := resolve_real fuel' an a st in
                                      (r, ds_put_real t r st1)
                                  | None => (const_term 0, ds_put_real t (const_term 0) st)
                                  end
                              | _ => (const_term 0, ds_put_real t (const_term 0) st)
                              end
                          end
                      else (const_term 0, st)
                  | TApp f [_; _; TList ins] =>
                      if f == "phi" then
                        let '(c, st1) := ds_fresh st in
                        let st2 := ds_put_real t (tmp c) st1 in
                        let '(cap_ins_rev, st3) :=
                          fold_left
                            (fun acc e =>
                               let '(xs, cur) := acc in
                               match pair_parts e with
                               | Some (pred_l, val) =>
                                   let '(r, cur1) :=
                                     match an_state an val with
                                     | AvDef _ => resolve_real fuel' an val cur
                                     | _ => (const_term 0, cur)
                                     end in
                                   (TApp "-" [pred_l; r] :: xs, cur1)
                               | None => (xs, cur)
                               end)
                            ins ([], st2) in
                        (tmp c, ds_put_phi t c (rev cap_ins_rev) st3)
                      else (const_term 0, st)
                  | _ => (const_term 0, st)
                  end
              end
          end
      | _ => (const_term 0, st)
      end
  end.

Definition run_demands (params : list term) (bs0 : list tblock) (an : launder_an) : demand_st :=
  let used := used_name_set params bs0 in
  let total :=
    (length params +
     fold_left (fun acc b => (acc + length (tb_phis b) + length (tb_insts b))%nat) bs0 0%nat)%nat in
  let ufuel := S (total + 8)%nat in
  let dfuel := S (2 * total + 16)%nat in
  let st0 := mkDemandSt 0 ufuel used nm_empty nm_empty nm_empty nm_empty in
  fold_left
    (fun st i =>
       match let_parts i with
       | Some (d, k, op, [x]) =>
           if is_atom "p" k && is_atom "itop" op then
             match tmp_name d, an_state an x with
             | [dt], AvDef _ =>
                 let '(r, st1) := resolve_real dfuel an x st in
                 match const_int r with
                 | Some _ => st1
                 | None =>
                     let '(i1, st2) := ds_fresh st1 in
                     let '(i2, st3) := ds_fresh st2 in
                     ds_put_itop dt i1 i2 st3
                 end
             | _, _ => st
             end
           else st
       | _ =>
           match store_parts i with
           | Some (w, v, x_term) =>
               if is_atom "p" w then st
               else
                 match tmp_name x_term with
                 | [x] =>
                     match tracked_shadow an x, an_state an v with
                     | Some _, AvDef _ => snd (resolve_real dfuel an v st)
                     | _, _ => st
                     end
                 | _ => st
                 end
           | None => st
           end
       end)
    (flat_map tb_insts bs0) st0.

(** ## IR rewrite and provenance site remapping

    Each demanded `itop` expands into `ptoi`, `sub`, and pointer `add`, tracked
    allocations gain 8-byte pointer shadow allocations, stores and loads to
    tracked slots mirror capabilities in their shadows, and context instruction
    sites move to match the emitted instructions. *)

Definition rewrite_inst (an : launder_an) (st : demand_st) (i : term) : list term :=
  match let_parts i with
  | Some (d, k, op, args) =>
      if is_atom "p" k && is_atom "itop" op then
        match tmp_name d, args with
        | [dt], [x] =>
            match nm_find dt (ds_itops st) with
            | Some (i1, i2) =>
                let c :=
                  match tmp_name x with
                  | [tx] => match nm_find tx (ds_reals st) with
                            | Some r => r
                            | None => const_term 0
                            end
                  | _ => const_term 0
                  end in
                [ let_term (tmp i1) (TAtom "l") (TAtom "ptoi") [c];
                  let_term (tmp i2) (TAtom "l") (TAtom "sub") [x; tmp i1];
                  let_term (tmp dt) (TAtom "p") (TAtom "add") [c; tmp i2] ]
            | None => [i]
            end
        | _, _ => [i]
        end
      else if is_atom "p" k && is_alloc op then
        match tmp_name d with
        | [a] =>
            match nm_find a (la_alloc_shadows an) with
            | Some shs =>
                match shs with
                | [] => [i]
                | _ =>
                    i :: map (fun sh =>
                                let_term (tmp sh) (TAtom "p") (TApp "alloc" [TInt 8]) [const_term 8])
                             shs
                end
            | None => [i]
            end
        | _ => [i]
        end
      else
        match load_parts i with
        | Some (ld, _, _, x) =>
            match tmp_name ld with
            | [t] =>
                match nm_find t (ds_loads st), tracked_shadow an x with
                | Some c, Some sh =>
                    [i; let_term (tmp c) (TAtom "p") (TApp "load" [TAtom "p"]) [tmp sh]]
                | _, _ => [i]
                end
            | _ => [i]
            end
        | None => [i]
        end
  | None =>
      match store_parts i with
      | Some (w, v, x_term) =>
          if is_atom "p" w then [i]
          else
            match tmp_name x_term with
            | [x] =>
                match tracked_shadow an x with
                | Some sh =>
                    let cap :=
                      match an_state an v, tmp_name v with
                      | AvDef _, [t] =>
                          match nm_find t (ds_reals st) with
                          | Some c => c
                          | None => const_term 0
                          end
                      | _, _ => const_term 0
                      end in
                    [i; store_term (TAtom "p") cap (tmp sh)]
                | None => [i]
                end
            | _ => [i]
            end
      | None => [i]
      end
  end.

Fixpoint emission_sites_rev (lbl : term) (old_idx new_idx : Z) (emitted : list term)
  (acc : list (term * term)) : list (term * term) * Z :=
  match emitted with
  | [] => (acc, new_idx)
  | _ :: rest =>
      emission_sites_rev lbl old_idx (new_idx + 1) rest
        ((TApp "inst" [lbl; TInt old_idx], TApp "inst" [lbl; TInt new_idx]) :: acc)
  end.

Definition rewrite_block (an : launder_an) (st : demand_st) (b : tblock)
  : tblock * list (term * term) :=
  let new_phis :=
    flat_map
      (fun p =>
         match phi_def p with
         | [t] =>
             match nm_find t (ds_phis st) with
             | Some (c, cap_ins) => [TApp "phi" [tmp c; TAtom "p"; TList cap_ins]]
             | None => []
             end
         | _ => []
         end)
      (tb_phis b) in
  let '(insts_rev, map_rev, _, _) :=
    fold_left
      (fun acc i0 =>
         let '(is_acc, m_acc, old_i, new_i) := acc in
         let out := rewrite_inst an st i0 in
         let '(m_acc1, next_i) := emission_sites_rev (tb_label b) old_i new_i out m_acc in
         (rev_append out is_acc, m_acc1, old_i + 1, next_i))
      (tb_insts b) ([], [], 0, 0) in
  (mkTBlock (tb_label b) (tb_phis b ++ new_phis) (rev insts_rev) (tb_jump b), rev map_rev).

Definition is_instruction_site (r : term) : bool :=
  match r with
  | TApp f [TApp sf [_; _]; _] => (f == "site") && (sf == "inst")
  | _ => false
  end.

Definition remap_sites (rs0 : list term) (site_map : list (term * term)) : list term :=
  let sites : nmap term :=
    fold_left
      (fun m r =>
         match r with
         | TApp f [s; os] => if f == "site" then nm_add s os m else m
         | _ => m
         end)
      rs0 nm_empty in
  let kept := filter (fun r => negb (is_instruction_site r)) rs0 in
  let new_sites :=
    flat_map
      (fun p =>
         let '(old_s, new_s) := p in
         match nm_find old_s sites with
         | Some os => [TApp "site" [new_s; os]]
         | None => []
         end)
      site_map in
  kept ++ new_sites.

(** ## Function and module entry points

    Functions without `itop` instructions or outside strict SSA form pass
    through unchanged. Every other function is analyzed via promotion and
    rewritten together with its accompanying `context/2` provenance item. *)

Definition has_itop (bs : list tblock) : bool :=
  existsb
    (fun i =>
       match let_parts i with
       | Some (_, k, op, _) => is_atom "p" k && is_atom "itop" op
       | None => false
       end)
    (flat_map tb_insts bs).

Definition launder_func (f0 : term) (rs0 : list term) : term * list term :=
  match f0 with
  | TApp f [name; linkage; ret; TList params; TList blocks0_t] =>
      if f == "func" then
        match map_option term_block blocks0_t with
        | Some bs0 =>
            if has_itop bs0 then
              match term_cfg bs0 with
              | Some g =>
                  match cfg_idoms g with
                  | Some idom =>
                      if strict_ssa (def_counts params bs0) params bs0 g idom then
                        let bsP :=
                          match promote_blocks true params bs0 with
                          | Some bs => bs
                          | None => bs0
                          end in
                        let an := run_analysis params bs0 bsP rs0 in
                        let st := run_demands params bs0 an in
                        let '(bs1_rev, map_parts_rev) :=
                          fold_left
                            (fun acc b =>
                               let '(bs_acc, m_acc) := acc in
                               let '(b1, m1) := rewrite_block an st b in
                               (b1 :: bs_acc, rev_append m1 m_acc))
                            bs0 ([], []) in
                        let f1 :=
                          TApp "func" [name; linkage; ret; TList params;
                                       TList (map block_term (rev bs1_rev))] in
                        (f1, remap_sites rs0 (rev map_parts_rev))
                      else (f0, rs0)
                  | None => (f0, rs0)
                  end
              | None => (f0, rs0)
              end
            else (f0, rs0)
        | None => (f0, rs0)
        end
      else (f0, rs0)
  | _ => (f0, rs0)
  end.

Definition list_term_eqb (xs ys : list term) : bool :=
  term_eqb (TList xs) (TList ys).

Definition launder_module (items0 : list term) : list term :=
  let contexts0 : nmap (list term) :=
    fold_left
      (fun m item =>
         match item with
         | TApp f [name; TList rs] =>
             if f == "context" then
               if nm_mem name m then m else nm_add name rs m
             else m
         | _ => m
         end)
      items0 nm_empty in
  let '(items1_rev, contexts) :=
    fold_left
      (fun acc item =>
         let '(is_acc, cs) := acc in
         match item with
         | TApp f [name; _; _; _; _] =>
             if f == "func" then
               let rs0 := match nm_find name cs with Some rs => rs | None => [] end in
               let '(f1, rs1) := launder_func item rs0 in
               let cs1 := if list_term_eqb rs0 rs1 then cs else nm_add name rs1 cs in
               (f1 :: is_acc, cs1)
             else (item :: is_acc, cs)
         | _ => (item :: is_acc, cs)
         end)
      items0 ([], contexts0) in
  map
    (fun item =>
       match item with
       | TApp f [name; _] =>
           if f == "context" then
             match nm_find name contexts with
             | Some rs => TApp "context" [name; TList rs]
             | None => item
             end
           else item
       | _ => item
       end)
    (rev items1_rev).
