(** This module implements base-plus-constant-offset address analysis for
    strict SSA functions, matching `alias.pl`. Each `l` or `p` temporary that
    derives from a base through same-class copies and constant additions or
    subtractions receives an `addr(Class, Base, Offset)` fact with a signed
    64-bit offset modulo two to the sixty-fourth power.

    Different bases may still alias at runtime because parameters, symbols, and
    opaque values need not designate distinct objects. Functions outside strict
    SSA yield an empty fact table, and unreachable cycles with no base have no
    fact. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Order Pizlonate TermCfg Escape.
From Opt Require Import Provenance OptIr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Address definitions and bases

    Every `l` or `p` parameter, phi, instruction, or call result in a function
    enters the definition table as a parameter, a `let` instruction, or an
    opaque value. *)

(** Testing whether [k] is an address class recognizes `l` and `p`. *)
Definition is_address_class (k : term) : bool :=
  is_atom "l" k || is_atom "p" k.

(** The origin of an address-class temporary separates parameters, `let`
    definitions, and opaque values such as phis or call results. *)
Inductive addr_source : Type :=
| SrcParam
| SrcOpaque
| SrcLet (op : term) (args : list term).

(** Collecting every address-class definition in [params] and [bs] matches
    `address_def/4`. *)
Definition address_defs (params : list term) (bs : list tblock)
  : list (term * (term * addr_source)) :=
  let param_defs :=
    flat_map
      (fun p =>
         match p with
         | TApp f [k; t] =>
             if (f == "param") && is_address_class k then
               map (fun d => (d, (k, SrcParam))) (tmp_name t)
             else []
         | _ => []
         end)
      params in
  let result_defs r :=
    match r with
    | TApp f [t; k] =>
        if (f == "result") && is_address_class k then
          map (fun d => (d, (k, SrcOpaque))) (tmp_name t)
        else []
    | _ => []
    end in
  let block_defs :=
    flat_map
      (fun b =>
         flat_map
           (fun p =>
              match p with
              | TApp f [d; k; _] =>
                  if (f == "phi") && is_address_class k then
                    map (fun t => (t, (k, SrcOpaque))) (tmp_name d)
                  else []
              | _ => []
              end)
           (tb_phis b)
         ++ flat_map
              (fun i =>
                 match i with
                 | TApp f xs =>
                     if f == "let" then
                       match xs with
                       | [d; k; op; TList args] =>
                           if is_address_class k then
                             map (fun t => (t, (k, SrcLet op args))) (tmp_name d)
                           else []
                       | _ => []
                       end
                     else if f == "call" then
                       match xs with
                       | [r; _; _] =>
                           match r with
                           | TApp g [TList rs] =>
                               if g == "tuple" then flat_map result_defs rs else []
                           | _ => result_defs r
                           end
                       | _ => []
                       end
                     else []
                 | _ => []
                 end)
              (tb_insts b))
      bs in
  param_defs ++ block_defs.

(** Checking whether [src] at class [k] derives from a same-class temporary [s]
    plus constant [delta] matches `address_offset/5`. *)
Definition address_offset (src : addr_source) (k : term)
    (by_temp : nmap (term * addr_source)) : option (term * Z) :=
  let same_class (s : term) (req : term) : bool :=
    match nm_find s by_temp with
    | Some (k', _) => term_eqb k' req
    | None => false
    end in
  match src with
  | SrcLet op args =>
      match op with
      | TAtom a =>
          if a == "copy" then
            match args with
            | [v] =>
                match tmp_name v with
                | [s] => if same_class s k then Some (s, 0) else None
                | _ => None
                end
            | _ => None
            end
          else if a == "add" then
            match args with
            | [a1; a2] =>
                match tmp_name a1, const_int a2 with
                | [s], Some n => if same_class s k then Some (s, n) else None
                | _, _ =>
                    if is_atom "l" k then
                      match const_int a1, tmp_name a2 with
                      | Some n, [s] => if same_class s (TAtom "l") then Some (s, n) else None
                      | _, _ => None
                      end
                    else None
                end
            | _ => None
            end
          else if a == "sub" then
            match args with
            | [a1; a2] =>
                match tmp_name a1, const_int a2 with
                | [s], Some n => if same_class s k then Some (s, - n) else None
                | _, _ => None
                end
            | _ => None
            end
          else None
      | _ => None
      end
  | _ => None
  end.

(** Determining whether definition [d] starts a fresh address base returns its
    base term (`param`, `alloc`, `symbol`, or `value`) and returns [None] when
    [d] instead offsets another address, matching `address_base/5`. *)
Definition address_base (src : addr_source) (d k : term)
    (by_temp : nmap (term * addr_source)) : option term :=
  match src with
  | SrcParam => Some (TApp "param" [d])
  | SrcOpaque => Some (TApp "value" [d])
  | SrcLet op args =>
      let* kind := op_kind op in
      match kind with
      | OkAdditive =>
          match address_offset src k by_temp with
          | Some _ => None
          | None => Some (TApp "value" [d])
          end
      | OkAlu | OkShift | OkNeg | OkSelect | OkPtoi | OkItop | OkVaArgs
      | OkVaArg | OkCmp | OkExt | OkLoad | OkAtomicLoad | OkCas =>
          Some (TApp "value" [d])
      | OkAlloc => Some (TApp "alloc" [d])
      | OkCopy =>
          match args with
          | [TApp g [sym]] =>
              if g == "global" then Some (TApp "symbol" [sym])
              else if g == "tmp" then
                match address_offset src k by_temp with
                | Some _ => None
                | None => Some (TApp "value" [d])
                end
              else if g == "const" then Some (TApp "value" [d])
              else None
          | _ => None
          end
      | _ => None
      end
  end.

(** ## Fact propagation

    Each derived temporary has at most one source edge, so walking outward from
    base seeds assigns every reachable derived temporary its wrapped signed
    64-bit offset without revisiting any node. *)

(** Wrapping [off + delta] into the signed 64-bit range matches
    `addr_edge_state/4`. *)
Definition wrap_signed64 (off delta : Z) : Z :=
  let u := (off + delta) mod 18446744073709551616 in
  if 9223372036854775808 <=? u then u - 18446744073709551616 else u.

(** Propagating address facts along offset edges stops once the worklist
    empties or fuel runs out, matching `pending_facts/4`. *)
Fixpoint pending_facts (fuel : nat) (pending : list (term * term))
    (users : nmap (list (term * Z))) (facts : nmap term) : nmap term :=
  match fuel, pending with
  | O, _ => facts
  | _, [] => facts
  | S fuel', (s, addr) :: rest =>
      let edges := match nm_find s users with Some es => es | None => [] end in
      let '(facts1, pending1) :=
        match addr with
        | TApp _ [k; base; TInt off] =>
            fold_left
              (fun st edge =>
                 let '(fs, pend) := st in
                 let '(d, delta) := edge in
                 let next_addr := TApp "addr" [k; base; TInt (wrap_signed64 off delta)] in
                 (nm_add d next_addr fs, (d, next_addr) :: pend))
              edges (facts, rest)
        | _ => (facts, rest)
        end in
      pending_facts fuel' pending1 users facts1
  end.

(** Computing the address facts of function [fn] returns the map from temporary
    names to `addr(Class, Base, Offset)` terms for strict SSA functions and an
    empty map otherwise, matching `alias_facts/2`. *)
Definition alias_facts (fn : term) : option (nmap term) :=
  match fn with
  | TApp f [_; _; _; TList params; TList bs_terms] =>
      if negb (f == "func") then None else
      let* bs := map_option term_block bs_terms in
      let* g := term_cfg bs in
      let* idom := cfg_idoms g in
      if negb (strict_ssa (def_counts params bs) params bs g idom)
      then Some nm_empty else
      let defs := address_defs params bs in
      let by_temp := nm_of_list defs in
      let seeds :=
        flat_map
          (fun p =>
             let '(d, (k, src)) := p in
             match address_base src d k by_temp with
             | Some base => [(d, TApp "addr" [k; base; TInt 0])]
             | None => []
             end)
          defs in
      let initial := nm_of_list seeds in
      let edges0 :=
        flat_map
          (fun p =>
             let '(d, (k, src)) := p in
             match address_offset src k by_temp with
             | Some (s, delta) => [(s, (d, delta))]
             | None => []
             end)
          defs in
      let users := nm_of_list (group_pairs_by_key edges0) in
      Some (pending_facts (S (length defs)) seeds users initial)
  | _ => None
  end.
