(** # Copy propagation

    As copy.pl's `copy_module/2`, on terms: in each function in
    strict SSA form, a copy `let(tmp(D), K, copy, [Src])` of a value
    of the same class goes, and every use of D reads what Src stands
    for; then each phi whose arguments, apart from itself, are one
    value goes the same way, which can make another phi trivial. A
    function that is not in strict SSA form, or that calls setjmp, is
    left as it is.

    What copy.pl does besides is left out, as in Pizlonate.v: the
    context records and their sites. [copy_module] gives None where
    `copy_module/2` fails or throws: an item, an instruction, a
    value or a jump of no known shape, or a jump to a label no block
    has. The gate (tests/promote.sh) holds the result to the term
    `nanofil promote-terms` prints. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality, written as Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Classes *)

(** The temporaries the instruction i defines, each with the class
    of its definition; an output of an `asm_fixed` is a `w`. *)
Definition inst_classes (i : term) : list (term * term) :=
  let result r := match r with
                  | TApp f [t; k] =>
                      if f == "result" then map (fun d => (d, k)) (tmp_name t) else []
                  | _ => []
                  end in
  match i with
  | TApp f xs =>
      if f == "let" then
        match xs with [d; k; _; _] => map (fun d => (d, k)) (tmp_name d) | _ => [] end
      else if f == "call" then
        match xs with
        | [r; _; _] =>
            match r with
            | TApp g [TList rs] => if g == "tuple" then flat_map result rs else []
            | _ => result r
            end
        | _ => []
        end
      else if f == "asm_fixed" then map (fun d => (d, TAtom "w")) (inst_defs i)
      else []
  | _ => []
  end.

(** As `temp_classes(Params, Blocks, Classes)`: the class of each
    temporary's definition. *)
Definition temp_classes (params : list term) (bs : list tblock) : nmap term :=
  nm_of_list
    (flat_map (fun p => match p with
                        | TApp f [k; t] =>
                            if f == "param" then map (fun d => (d, k)) (tmp_name t) else []
                        | _ => []
                        end) params
     ++ flat_map (fun b =>
                    flat_map (fun p => match p with
                                       | TApp f [d; k; _] =>
                                           if f == "phi" then map (fun d => (d, k)) (tmp_name d)
                                           else []
                                       | _ => []
                                       end) (tb_phis b)
                    ++ flat_map inst_classes (tb_insts b)) bs).

(** As `copy_value(Src, K, Classes, V)`: what a copy at the class k
    of the value src can be replaced by: a temporary of that class,
    or a constant at `w` or `l`, reduced to the class's width. *)
Definition copy_value (classes : nmap term) (k src : term) : option term :=
  match src with
  | TApp f [x] =>
      if f == "tmp" then
        match nm_find x classes with
        | Some k' => if term_eqb k' k then Some src else None
        | None => None
        end
      else if f == "const" then
        match x with
        | TInt n =>
            if is_atom "w" k then Some (TApp "const" [TInt (n mod 2 ^ 32)])
            else if is_atom "l" k then Some (TApp "const" [TInt (n mod 2 ^ 64)])
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

(** ## Chains *)

(** As `copy_chain/6`: following the copies, and the values already
    in reps, from the value v ends at a value that is not copied; the
    path has the temporaries on the way that reps lacks. A chain has
    at most as many links as there are copies, the fuel. *)
Fixpoint copy_chain (fuel : nat) (copies reps : nmap term) (v : term) (path : list term)
  : option (list term * term) :=
  match fuel with
  | O => None
  | S fuel' =>
      match tmp_name v with
      | [t] =>
          match nm_find t reps with
          | Some v' => Some (path, v')
          | None =>
              match nm_find t copies with
              | Some src => copy_chain fuel' copies reps src (t :: path)
              | None => Some (path, v)
              end
          end
      | _ => Some (path, v)
      end
  end.

(** As `foldl(copy_reps(Copies), Pairs, Empty, Reps)`: the value
    that replaces each temporary of pairs, the end of its chain. *)
Definition chain_reps (pairs : list (term * term)) : option (nmap term) :=
  let copies := nm_of_list pairs in
  let fuel := S (S (length pairs)) in
  fold_left (fun acc p =>
               let* reps := acc in
               let* r := copy_chain fuel copies reps (tmp (fst p)) [] in
               Some (fold_left (fun m t => nm_add t (snd r) m) (fst r) reps))
            pairs (Some nm_empty).

(** ## Substitution *)

(** As `value_reps(V0, Reps, V)`: what replaces the value v, or v
    itself. *)
Definition value_reps (reps : nmap term) (v : term) : option term :=
  match v with
  | TApp f [x] =>
      if f == "tmp" then Some (match nm_find x reps with Some v' => v' | None => v end)
      else if (f == "const") || (f == "global") then Some v
      else None
  | _ => None
  end.

(** As `inst_reps(Inst0, Reps, Inst)`. *)
Definition inst_reps (reps : nmap term) (i : term) : option term :=
  match i with
  | TAtom a => if a == "fence" then Some i else None
  | TApp f xs =>
      if f == "loc" then if arity 2 xs then Some i else None
      else if f == "let" then
        match xs with
        | [d; k; o; TList vs] =>
            let* vs' := map_option (value_reps reps) vs in
            Some (TApp f [d; k; o; TList vs'])
        | _ => None
        end
      else if (f == "store") || (f == "atomic_store") then
        match xs with
        | [w; v; a] =>
            let* v' := value_reps reps v in
            let* a' := value_reps reps a in
            Some (TApp f [w; v'; a'])
        | _ => None
        end
      else if f == "access" then
        match xs with
        | [k; a; s; al] => let* a' := value_reps reps a in Some (TApp f [k; a'; s; al])
        | _ => None
        end
      else if f == "asm_fixed" then
        match xs with
        | [m; TList ins; outs] =>
            let* ins' := map_option (fun p => let* rv := pair_parts p in
                                              let* v' := value_reps reps (snd rv) in
                                              Some (TApp "-" [fst rv; v'])) ins in
            Some (TApp f [m; TList ins'; outs])
        | _ => None
        end
      else if f == "call" then
        match xs with
        | [r; g; TList args] =>
            let* g' := value_reps reps g in
            let* args' := map_option (fun a => match a with
                                               | TApp h [k; v] =>
                                                   if h == "arg" then
                                                     let* v' := value_reps reps v in
                                                     Some (TApp h [k; v'])
                                                   else None
                                               | _ => None
                                               end) args in
            Some (TApp f [r; g'; TList args'])
        | _ => None
        end
      else None
  | _ => None
  end.

(** As `jump_reps(Jump0, Reps, Jump)`. *)
Definition jump_reps (reps : nmap term) (j : term) : option term :=
  match j with
  | TAtom a => if (a == "ret") || (a == "unreachable") then Some j else None
  | TApp f xs =>
      if f == "goto" then if arity 1 xs then Some j else None
      else if f == "branch" then
        match xs with
        | [v; t; e] => let* v' := value_reps reps v in Some (TApp f [v'; t; e])
        | _ => None
        end
      else if f == "ret" then
        match xs with
        | [v] => let* v' := value_reps reps v in Some (TApp f [v'])
        | _ => None
        end
      else if f == "rets" then
        match xs with
        | [TList vs] => let* vs' := map_option (value_reps reps) vs in Some (TApp f [TList vs'])
        | _ => None
        end
      else None
  | _ => None
  end.

(** Whether the term t defines, as a phi or as a copy, a temporary
    that reps replaces. *)
Definition replaced (reps : nmap term) (t : term) : bool :=
  match t with
  | TApp f [d; _; x] =>
      (f == "phi") && existsb (fun d => nm_mem d reps) (tmp_name d)
  | TApp f [d; _; o; _] =>
      (f == "let") && is_atom "copy" o && existsb (fun d => nm_mem d reps) (tmp_name d)
  | _ => false
  end.

(** As `reps_block(Reps, Block0, Block, _)`: the block b without the
    phis and the copies whose temporary reps replaces, and with every
    use of such a temporary replaced by its value. *)
Definition reps_block (reps : nmap term) (b : tblock) : option tblock :=
  let* phis :=
    map_option (fun p => match p with
                         | TApp f [d; k; TList args] =>
                             if f == "phi" then
                               let* args' := map_option (fun a => let* lv := pair_parts a in
                                                                  let* v' := value_reps reps (snd lv) in
                                                                  Some (TApp "-" [fst lv; v'])) args in
                               Some (TApp f [d; k; TList args'])
                             else None
                         | _ => None
                         end)
               (filter (fun p => negb (replaced reps p)) (tb_phis b)) in
  let* insts := map_option (inst_reps reps)
                           (filter (fun i => negb (replaced reps i)) (tb_insts b)) in
  let* j := jump_reps reps (tb_jump b) in
  Some (mkTBlock (tb_label b) phis insts j).

(** ## Trivial phis *)

(** As `phi_worklist_reps/5`: the value of each trivial phi, found
    by a worklist over the phi temporaries pending, an ordset. phis
    has the operand values of each phi not yet simplified, and users
    the ordset of the phis that read each temporary. A phi is trivial
    when its operands other than itself are one value; the phis that
    read it then read that value, and are looked at again. The result
    is in the order the phis were simplified, the last first; the
    caller puts it in the order of the temporaries, an assoc's. Each
    step takes a temporary off pending or simplifies a phi, and only
    simplifying adds any, at most all the phis: the fuel. *)
Fixpoint phi_worklist (fuel : nat) (pending : names) (phis : nmap (list term))
    (users : nmap names) (found : list (term * term)) : option (list (term * term)) :=
  match fuel with
  | O => None
  | S fuel' =>
      match pending with
      | [] => Some found
      | d :: pending0 =>
          let self := tmp d in
          match option_map (fun vs => sort term_compare
                                           (filter (fun v => negb (term_eqb v self)) vs))
                           (nm_find d phis) with
          | Some [v] =>
              let phis1 := nm_remove d phis in
              let live := filter (fun u => nm_mem u phis1) (names_at users d) in
              let phis2 :=
                fold_left (fun m u =>
                             match nm_find u m with
                             | Some vs => nm_add u (map (fun v0 => if term_eqb v0 self then v
                                                                   else v0) vs) m
                             | None => m
                             end) live phis1 in
              let users' := match tmp_name v with
                            | [s] => if nm_mem s phis2
                                     then nm_add s (nunion (names_at users s) live) users
                                     else users
                            | _ => users
                            end in
              phi_worklist fuel' (nunion pending0 live) phis2 users' ((d, v) :: found)
          | _ => phi_worklist fuel' pending0 phis users found
          end
      end
  end.

(** As `trivial_phis/6`: the blocks bs without their trivial phis.
    Only a phi of a reachable block whose every argument a copy could
    stand for ([copy_value]) is looked at. *)
Definition trivial_phis (classes : nmap term) (reach : nmap unit) (bs : list tblock)
  : option (list tblock) :=
  let pairs :=
    flat_map (fun b =>
                if nm_mem (tb_label b) reach then
                  flat_map (fun p => match p with
                                     | TApp f [d; k; TList args] =>
                                         if f == "phi" then
                                           match tmp_name d,
                                                 map_option (fun a => let* lv := pair_parts a in
                                                                      copy_value classes k (snd lv))
                                                            args with
                                           | [d], Some vs => [(d, vs)]
                                           | _, _ => []
                                           end
                                         else []
                                     | _ => []
                                     end) (tb_phis b)
                else []) bs in
  let edges :=
    sort (fun a b => thenc (term_compare (fst a) (fst b)) (term_compare (snd a) (snd b)))
         (flat_map (fun p => map (fun s => (s, fst p)) (flat_map tmp_name (snd p))) pairs) in
  let users := fold_left (fun m e => nm_add (fst e) (snd e :: names_at m (fst e)) m)
                         (rev' edges) nm_empty in
  let n := length pairs in
  let* found := phi_worklist (S (n + n * n)) (nsort (map fst pairs)) (nm_of_list pairs)
                             users [] in
  let* reps := chain_reps (msort (fun a b => term_compare (fst a) (fst b)) found) in
  map_option (reps_block reps) bs.

(** ## Functions and modules *)

(** As `copy_context/4`, without the records: the blocks bs of a
    function with the given params, its copies and trivial phis
    gone. *)
Definition copy_blocks (filc : bool) (params : list term) (bs : list tblock)
  : option (list tblock) :=
  if calls_setjmp bs then Some bs else
  let* g := term_cfg bs in
  let* idom := cfg_idoms g in
  if negb (strict_ssa (def_counts params bs) params bs g idom) then Some bs else
  let classes := temp_classes params bs in
  let reach := reached g in
  let copies :=
    flat_map (fun b =>
                if nm_mem (tb_label b) reach then
                  flat_map (fun i => match i with
                                     | TApp f [d; k; o; TList [src]] =>
                                         if (f == "let") && is_atom "copy" o then
                                           match tmp_name d, copy_value classes k src with
                                           | [d], Some v => [(d, v)]
                                           | _, _ => []
                                           end
                                         else []
                                     | _ => []
                                     end) (tb_insts b)
                else []) bs in
  let* reps := chain_reps copies in
  let* copied := map_option (reps_block reps) bs in
  trivial_phis classes reach copied.

(** As `copy_module/2`, without the context items. *)
Definition copy_module (m : term) : option term := pass_module copy_blocks m.

(** A copy goes, and its use reads the source. *)
Example copy_goes :
  copy_module
    (TApp "module" [TList [TApp "func" [TAtom "f"; TAtom "export"; TAtom "w";
       TList [TApp "param" [TAtom "w"; tmp (TAtom "a")]];
       TList [TApp "block" [TAtom "top"; TList [];
                            TList [TApp "let" [tmp (TAtom "x"); TAtom "w"; TAtom "copy";
                                               TList [tmp (TAtom "a")]]];
                            TApp "ret" [tmp (TAtom "x")]]]]]])
  = Some (TApp "module" [TList [TApp "func" [TAtom "f"; TAtom "export"; TAtom "w";
       TList [TApp "param" [TAtom "w"; tmp (TAtom "a")]];
       TList [TApp "block" [TAtom "top"; TList []; TList [];
                            TApp "ret" [tmp (TAtom "a")]]]]]]).
Proof. reflexivity. Qed.
