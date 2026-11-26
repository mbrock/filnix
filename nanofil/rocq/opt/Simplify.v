(** This module implements the cheap middle-end simplifier over unchecked strict
    SSA IR, matching `simplify.pl`. It folds constant integer operations through
    total ALU semantics, simplifies algebraic identities and boolean
    comparisons, cancels additive and equality terms, numbers pure values down
    the dominator tree, rebases neighbouring element addresses within a block,
    folds constant branches, prunes unreachable blocks, eliminates dead pure
    definitions, and merges straight-line and empty pass-through blocks.

    Every rewrite preserves side-effecting instructions, memory accesses, calls,
    allocations, and traps in their exact order. Source context records follow
    every transformation through site remapping, dropped sites, and `alias/4`
    history records. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg Escape Promote Copy.
From Opt Require Import Provenance OptIr OptCopy.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Small helpers and algebraic tables

    The helpers below test integer constants, classify pure and foldable
    operations, mirror and negate integer comparison conditions, and track
    narrow integer subranges. *)

(** Testing whether [n] is zero modulo the width of class [k] matches
    `zero/2`. *)
Definition is_zero_mod (k : term) (n : Z) : bool :=
  match class_modulus k with
  | Some m => (n mod m) =? 0
  | None => false
  end.

(** Testing whether [n] is one modulo the width of class [k] matches `one/2`. *)
Definition is_one_mod (k : term) (n : Z) : bool :=
  match class_modulus k with
  | Some m => (n mod m) =? 1
  | None => false
  end.

(** Testing whether [v] is a `const(N)` term with an integer argument matches
    `is_const/1`. *)
Definition is_const_term (v : term) : bool :=
  match const_int v with Some _ => true | None => false end.

(** Computing the modulus for additive cancellation treats class `p` as 64-bit
    class `l`, matching `arith_modulus/2`. *)
Definition arith_modulus (k : term) : option Z :=
  if is_atom "p" k then Some 18446744073709551616 else class_modulus k.

(** Testing whether [op] is foldable on constant integer operands matches
    `foldable/1`. *)
Definition foldable_op (op : term) : bool :=
  match op_kind op with
  | Some OkAdditive | Some OkAlu | Some OkShift | Some OkNeg
  | Some OkSelect | Some OkCopy | Some OkExt => true
  | Some OkCmp =>
      match op with
      | TApp _ [_; ck] => is_int_class ck
      | _ => false
      end
  | _ => false
  end.

(** Testing whether [op] is a commutative integer binary operation matches
    `commutative/1`. *)
Definition commutative_op (op : term) : bool :=
  match op with
  | TAtom a =>
      (a == "add") || (a == "mul") || (a == "and") || (a == "or") || (a == "xor")
  | _ => false
  end.

(** Testing whether [op] is pure and safe to delete or share matches
    `pure_op/2`. *)
Definition pure_op (op : term) : bool :=
  match op_kind op with
  | Some OkAdditive | Some OkShift | Some OkNeg | Some OkSelect | Some OkCopy
  | Some OkPtoi | Some OkItop | Some OkCmp | Some OkExt | Some OkFloatConvert
  | Some OkIntToFloat | Some OkFloatToInt | Some OkCast => true
  | _ =>
      match op with
      | TAtom a => (a == "mul") || (a == "and") || (a == "or") || (a == "xor")
      | _ => false
      end
  end.

(** Testing whether an instruction defines a temporary by a removable pure
    operation excludes `copy` of a global symbol, matching `removable/1`. *)
Definition removable_inst (i : term) : bool :=
  match let_parts i with
  | Some (d, _, op, args) =>
      match tmp_name d with
      | [_] =>
          pure_op op
          && negb (is_atom "copy" op
                   && match args with
                      | [TApp g [_]] => g == "global"
                      | _ => false
                      end)
      | _ => false
      end
  | None => false
  end.

(** Mirroring an integer comparison condition swaps its operands, matching
    `mirrored/2`. *)
Definition mirrored_cond (c : term) : option term :=
  match c with
  | TAtom a =>
      if (a == "eq") || (a == "ne") then Some c
      else if a == "slt" then Some (TAtom "sgt")
      else if a == "sgt" then Some (TAtom "slt")
      else if a == "sle" then Some (TAtom "sge")
      else if a == "sge" then Some (TAtom "sle")
      else if a == "ult" then Some (TAtom "ugt")
      else if a == "ugt" then Some (TAtom "ult")
      else if a == "ule" then Some (TAtom "uge")
      else if a == "uge" then Some (TAtom "ule")
      else None
  | _ => None
  end.

(** Negating an integer comparison condition yields its logical complement,
    matching `negated/2`. *)
Definition negated_cond (c : term) : option term :=
  match c with
  | TAtom a =>
      if a == "eq" then Some (TAtom "ne")
      else if a == "ne" then Some (TAtom "eq")
      else if a == "slt" then Some (TAtom "sge")
      else if a == "sge" then Some (TAtom "slt")
      else if a == "sle" then Some (TAtom "sgt")
      else if a == "sgt" then Some (TAtom "sle")
      else if a == "ult" then Some (TAtom "uge")
      else if a == "uge" then Some (TAtom "ult")
      else if a == "ule" then Some (TAtom "ugt")
      else if a == "ugt" then Some (TAtom "ule")
      else None
  | _ => None
  end.

(** Testing whether every value of narrow type [t1] fits in narrow type [t2]
    matches `fits/2`. *)
Definition narrow_fits (t1 t2 : term) : bool :=
  match t1, t2 with
  | TAtom a, TAtom b =>
      if a == "ub" then
        (b == "ub") || (b == "uh") || (b == "uw") || (b == "sh") || (b == "sw")
      else if a == "uh" then (b == "uh") || (b == "uw") || (b == "sw")
      else if a == "sb" then (b == "sb") || (b == "sh") || (b == "sw")
      else if a == "sh" then (b == "sh") || (b == "sw")
      else if a == "uw" then b == "uw"
      else if a == "sw" then b == "sw"
      else false
  | _, _ => false
  end.

(** Returning the signed range of narrow type [t] matches `narrow_range/3`. *)
Definition narrow_range (t : term) : option (Z * Z) :=
  match t with
  | TAtom a =>
      if a == "ub" then Some (0, 255)
      else if a == "uh" then Some (0, 65535)
      else if a == "sb" then Some (-128, 127)
      else if a == "sh" then Some (-32768, 32767)
      else None
  | _ => None
  end.

(** Computing the base-two logarithm of a positive power of two counts right
    shifts until reaching one, bounded by [fuel]. *)
Fixpoint log2_steps (fuel : nat) (v s : Z) : Z :=
  if v <=? 1 then s
  else
    match fuel with
    | O => s
    | S fuel' => log2_steps fuel' (Z.shiftr v 1) (s + 1)
    end.

(** Testing whether [n] reduced modulo class [k] is a power of two returns its
    exponent, matching `power_of_two/3`. *)
Definition power_of_two (k : term) (n : Z) : option Z :=
  let* m := class_modulus k in
  let v := n mod m in
  if (0 <? v) && (Z.land v (v - 1) =? 0) then Some (log2_steps 64 v 0)
  else None.

(** Reducing constant operands according to their expected classes zips [ks]
    with [args] for constant evaluation. *)
Fixpoint arg_numbers (ks : list term) (args : list term) : option (list Z) :=
  match ks, args with
  | [], [] => Some []
  | k :: ks', a :: args' =>
      let* n := const_int a in
      let* m := class_modulus k in
      let* rest := arg_numbers ks' args' in
      Some ((n mod m) :: rest)
  | _, _ => None
  end.

(** ## Simplification state and single-instruction rules

    Walking the dominator tree threads replacement maps, boolean equivalences,
    definition facts, rewritten blocks, and branch-folding status while passing
    available value-numbering and rebasing tables strictly downward. *)

(** A primary definition fact records an integer comparison, a boolean
    negation, or a narrow integer load or extension. *)
Inductive main_def : Type :=
| DefCmp (cond ck a b : term)
| DefNot (b : term)
| DefNarrow (ty : term).

(** The collected definition facts separate primary facts, additive forms,
    64-bit linear offset forms, 32-bit signed ranges, and 32-bit additive
    sums. *)
Record simp_defs : Type := mkSimpDefs {
  sd_main : nmap main_def;
  sd_arith : nmap (term * term * term * term);
  sd_lin : nmap (term * Z);
  sd_range : nmap (Z * Z);
  sd_wsum : nmap (term * Z)
}.

(** An empty definition fact table initializes all five maps to empty. *)
Definition empty_defs : simp_defs :=
  mkSimpDefs nm_empty nm_empty nm_empty nm_empty nm_empty.

(** Available pure expressions and per-block rebased address anchors are passed
    down the dominator tree without escaping to siblings. *)
Record simp_avail : Type := mkSimpAvail {
  sa_num : nmap term;
  sa_based : nmap (term * Z)
}.

(** An empty availability table initializes both maps to empty. *)
Definition empty_avail : simp_avail := mkSimpAvail nm_empty nm_empty.

(** The threaded state of the dominator walk holds replacements, boolean
    equivalences, definition facts, rewritten blocks, and branch-fold status. *)
Record walk_state : Type := mkWalkState {
  ws_reps : nmap term;
  ws_bools : nmap (list (term * term));
  ws_defs : simp_defs;
  ws_out : nmap tblock;
  ws_folded : bool
}.

(** The result of simplifying one operation is either a direct value or an
    equivalent operation term. *)
Inductive simp_res : Type :=
| SimpVal (v : term)
| SimpOp (op : term) (args : list term).

(** The result of value numbering and address rebasing either reuses an
    existing temporary or keeps an operation. *)
Inductive rebase_res : Type :=
| FoundSame (e : term)
| FoundOp (op : term) (args : list term).

(** Substituting one value through [reps] replaces a mapped temporary and
    leaves every other value unchanged, matching `subst/3`. *)
Definition subst_val (reps : nmap term) (v : term) : term :=
  match tmp_name v with
  | [t] => match nm_find t reps with Some v' => v' | None => v end
  | _ => v
  end.

(** Validating whether [v] can replace uses of a temporary of class [k] accepts
    a same-class temporary or a reduced `w`/`l` constant, matching
    `replacement/4`. *)
Definition replacement_val (classes : nmap term) (k v : term) : option term :=
  match v with
  | TApp f [x] =>
      if f == "tmp" then
        match nm_find x classes with
        | Some k' => if term_eqb k' k then Some v else None
        | None => None
        end
      else if f == "const" then
        match x with
        | TInt n =>
            if is_int_class k then
              let* m := class_modulus k in Some (TApp "const" [TInt (n mod m)])
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

(** Testing whether [v] is known to hold zero or one checks integer literals
    zero and one and entries in [bools], matching `boolean/3`. *)
Definition is_boolean (bools : nmap (list (term * term))) (v : term) : bool :=
  match const_int v with
  | Some n => (n =? 0) || (n =? 1)
  | None =>
      match tmp_name v with
      | [t] => nm_mem t bools
      | _ => false
      end
  end.

(** Finding the first temporary in [eqs] whose actual definition class equals
    [k] matches `same_class/4`. *)
Fixpoint same_class_temp (classes : nmap term) (k : term) (eqs : list (term * term))
  : option term :=
  match eqs with
  | [] => None
  | (_, e) :: rest =>
      match nm_find e classes with
      | Some k' => if term_eqb k' k then Some e else same_class_temp classes k rest
      | None => same_class_temp classes k rest
      end
  end.

(** Testing algebraic identities for an integer operation at class [k] applies
    the identity rules in the exact clause order of `identity/7`. *)
Definition apply_identity (op k : term) (args : list term)
    (bools : nmap (list (term * term))) : option simp_res :=
  match op, args with
  | TAtom a, [x; y] =>
      match const_int y with
      | Some n =>
          if ((a == "add") || (a == "sub") || (a == "or") || (a == "xor"))
             && is_zero_mod k n
          then Some (SimpVal x)
          else if ((a == "shl") || (a == "shr") || (a == "sar"))
                  && match class_bits k with Some bits => (n mod bits) =? 0 | None => false end
          then Some (SimpVal x)
          else if ((a == "mul") || (a == "udiv") || (a == "div")) && is_one_mod k n
          then Some (SimpVal x)
          else if (a == "and")
                  && match class_modulus k with Some m => (n mod m) =? (m - 1) | None => false end
          then Some (SimpVal x)
          else if (a == "and") && (n =? 1) && is_boolean bools x
          then Some (SimpVal x)
          else if ((a == "mul") || (a == "and")) && is_zero_mod k n
          then Some (SimpVal (TApp "const" [TInt 0]))
          else if a == "mul" then
            match power_of_two k n with
            | Some s => if 0 <? s then Some (SimpOp (TAtom "shl") [x; TApp "const" [TInt s]]) else None
            | None => None
            end
          else if a == "udiv" then
            match power_of_two k n with
            | Some s => if 0 <? s then Some (SimpOp (TAtom "shr") [x; TApp "const" [TInt s]]) else None
            | None => None
            end
          else if a == "urem" then
            match power_of_two k n with
            | Some s =>
                if 0 <? s then
                  Some (SimpOp (TAtom "and") [x; TApp "const" [TInt (Z.shiftl 1 s - 1)]])
                else None
            | None => None
            end
          else None
      | None =>
          match tmp_name x, tmp_name y with
          | [tx], [ty] =>
              if term_eqb tx ty then
                if (a == "sub") || (a == "xor") then Some (SimpVal (TApp "const" [TInt 0]))
                else if (a == "and") || (a == "or") then Some (SimpVal x)
                else None
              else None
          | _, _ => None
          end
      end
  | _, _ => None
  end.

(** Cancelling two nested additive expressions preserves the left base pointer
    capability at class `p`, matching `cancel_pair/9`. *)
Definition cancel_pair (k aop a1 a2 op bop b1 b2 : term) : option simp_res :=
  let intk := is_int_class k in
  if is_atom "add" aop then
    if is_atom "add" op && is_atom "sub" bop then
      if term_eqb a2 b2 then Some (SimpOp (TAtom "add") [a1; b1])
      else if intk && term_eqb a1 b2 then Some (SimpOp (TAtom "add") [a2; b1])
      else None
    else if is_atom "sub" op && is_atom "add" bop then
      if term_eqb a2 b1 then Some (SimpOp (TAtom "sub") [a1; b2])
      else if term_eqb a2 b2 then Some (SimpOp (TAtom "sub") [a1; b1])
      else if intk && term_eqb a1 b1 then Some (SimpOp (TAtom "sub") [a2; b2])
      else if intk && term_eqb a1 b2 then Some (SimpOp (TAtom "sub") [a2; b1])
      else None
    else if is_atom "sub" op && is_atom "sub" bop then
      if term_eqb a2 b1 then Some (SimpOp (TAtom "add") [a1; b2])
      else if intk && term_eqb a1 b1 then Some (SimpOp (TAtom "add") [a2; b2])
      else None
    else None
  else if is_atom "sub" aop then
    if is_atom "add" op && is_atom "add" bop then
      if term_eqb a2 b1 then Some (SimpOp (TAtom "add") [a1; b2])
      else if term_eqb a2 b2 then Some (SimpOp (TAtom "add") [a1; b1])
      else None
    else if is_atom "add" op && is_atom "sub" bop then
      if term_eqb a2 b1 then Some (SimpOp (TAtom "sub") [a1; b2])
      else None
    else if is_atom "sub" op && is_atom "sub" bop then
      if term_eqb a2 b2 then Some (SimpOp (TAtom "sub") [a1; b1])
      else None
    else None
  else None.

(** Cancelling an outer addition or subtraction against a left-hand additive
    definition matches `cancel_left/8`. *)
Definition cancel_left (k aop a1 a2 op b : term) (defs : simp_defs) : option simp_res :=
  if is_atom "add" aop && is_atom "sub" op && term_eqb a2 b then Some (SimpVal a1)
  else if is_atom "add" aop && is_atom "sub" op && is_int_class k && term_eqb a1 b then Some (SimpVal a2)
  else if is_atom "sub" aop && is_atom "add" op && term_eqb a2 b then Some (SimpVal a1)
  else
    match const_int a2, const_int b with
    | Some c1, Some c2 =>
        let* m := arith_modulus k in
        let half := Z.shiftr m 1 in
        let s1 := if is_atom "add" aop then c1 else - c1 in
        let s2 := if is_atom "add" op then c2 else - c2 in
        let d := (s1 + s2) mod m in
        if d =? 0 then Some (SimpVal a1)
        else if d <? half then Some (SimpOp (TAtom "add") [a1; TApp "const" [TInt d]])
        else Some (SimpOp (TAtom "sub") [a1; TApp "const" [TInt (m - d)]])
    | _, _ =>
        match tmp_name b with
        | [bt] =>
            let bk := if is_atom "p" k then TAtom "l" else k in
            match nm_find bt (sd_arith defs) with
            | Some (bk', bop, b1, b2) =>
                if term_eqb bk' bk then cancel_pair k aop a1 a2 op bop b1 b2 else None
            | None => None
            end
        | _ => None
        end
    end.

(** Cancelling an integer operation against a right-hand additive definition
    matches `cancel_right/6`. *)
Definition cancel_right (op a bop b1 b2 : term) : option simp_res :=
  if is_atom "add" op && is_atom "sub" bop && term_eqb a b2 then Some (SimpVal b1)
  else if is_atom "sub" op && is_atom "sub" bop && term_eqb a b1 then Some (SimpVal b2)
  else if is_atom "sub" op && is_atom "add" bop && term_eqb a b1 then Some (SimpOp (TAtom "neg") [b2])
  else if is_atom "sub" op && is_atom "add" bop && term_eqb a b2 then Some (SimpOp (TAtom "neg") [b1])
  else None.

(** Applying additive cancellation checks left-hand cancellation first and
    falls back to right-hand cancellation for integer classes, matching
    `cancel_arith/5`. *)
Definition cancel_arith (k op : term) (args : list term) (defs : simp_defs) : option simp_res :=
  if negb (is_atom "p" k || is_int_class k) then None
  else if negb (is_atom "add" op || is_atom "sub" op) then None
  else
    match args with
    | [a; b] =>
        let try_left :=
          match tmp_name a with
          | [at_] =>
              match nm_find at_ (sd_arith defs) with
              | Some (ak, aop, a1, a2) =>
                  if term_eqb ak k then cancel_left k aop a1 a2 op b defs else None
              | None => None
              end
          | _ => None
          end in
        match try_left with
        | Some r => Some r
        | None =>
            if is_int_class k then
              match tmp_name b with
              | [bt] =>
                  match nm_find bt (sd_arith defs) with
                  | Some (bk, bop, b1, b2) =>
                      if term_eqb bk k then cancel_right op a bop b1 b2 else None
                  | None => None
                  end
              | _ => None
              end
            else None
        end
    | _ => None
    end.

(** Simplifying an integer comparison of identical operands, unsigned zero
    bounds, or a boolean against zero or one matches `boolean_cmp/8`. *)
Definition boolean_cmp (c ck k : term) (args : list term) (classes : nmap term)
    (bools : nmap (list (term * term))) (defs : simp_defs) : option simp_res :=
  match args with
  | [x; y] =>
      match tmp_name x, tmp_name y with
      | [tx], [ty] =>
          if term_eqb tx ty then
            let v :=
              if is_atom "eq" c || is_atom "ule" c || is_atom "uge" c
                 || is_atom "sle" c || is_atom "sge" c
              then 1 else 0 in
            Some (SimpVal (TApp "const" [TInt v]))
          else None
      | _, _ =>
          match const_int y with
          | Some n =>
              if is_atom "ult" c && is_zero_mod ck n then Some (SimpVal (TApp "const" [TInt 0]))
              else if is_atom "uge" c && is_zero_mod ck n then Some (SimpVal (TApp "const" [TInt 1]))
              else
                match tmp_name x with
                | [b] =>
                    match nm_find b bools with
                    | Some eqs =>
                        let truth :=
                          if (is_atom "ne" c && is_zero_mod ck n)
                             || (is_atom "eq" c && is_one_mod ck n)
                          then Some true
                          else if (is_atom "eq" c && is_zero_mod ck n)
                                  || (is_atom "ne" c && is_one_mod ck n)
                          then Some false
                          else None in
                        match truth with
                        | Some true =>
                            let* e := same_class_temp classes k ((k, b) :: eqs) in
                            Some (SimpVal (tmp e))
                        | Some false =>
                            let fix find_cmp (ps : list (term * term)) :=
                              match ps with
                              | [] => None
                              | (_, e) :: rest =>
                                  match nm_find e (sd_main defs) with
                                  | Some (DefCmp c0 ck0 a0 b0) =>
                                      let* c1 := negated_cond c0 in
                                      Some (SimpOp (TApp "cmp" [c1; ck0]) [a0; b0])
                                  | _ => find_cmp rest
                                  end
                              end in
                            find_cmp ((k, b) :: eqs)
                        | None => None
                        end
                    | None => None
                    end
                | _ => None
                end
          | None => None
          end
      end
  | _ => None
  end.

(** Cancelling common additive terms across `eq` or `ne` integer comparisons
    matches `cancel_cmp/5`. *)
Definition cancel_cmp (c ck : term) (args : list term) (defs : simp_defs) : option (list term) :=
  if negb (is_atom "eq" c || is_atom "ne" c) then None else
  match args with
  | [a; b] =>
      match tmp_name a, tmp_name b with
      | [at_], [bt] =>
          match nm_find at_ (sd_arith defs), nm_find bt (sd_arith defs) with
          | Some (ak, aop, a1, a2), Some (bk, bop, b1, b2) =>
              if term_eqb ak ck && term_eqb bk ck && term_eqb aop bop then
                if is_atom "sub" aop && term_eqb a2 b2 then Some [a1; b1]
                else if is_atom "add" aop then
                  if term_eqb a2 b2 then Some [a1; b1]
                  else if term_eqb a1 b1 then Some [a2; b2]
                  else if term_eqb a1 b2 then Some [a2; b1]
                  else if term_eqb a2 b1 then Some [a1; b2]
                  else None
                else None
              else None
          | _, _ => None
          end
      | _, _ => None
      end
  | _ => None
  end.

(** Simplifying one operation applies constant folding, commutativity,
    identities, cancellation, boolean comparisons, and redundant extension
    elimination in the exact order of `simplified/7`. *)
Fixpoint simplified (fuel : nat) (k op : term) (args : list term)
    (classes : nmap term) (filc : bool)
    (bools : nmap (list (term * term))) (defs : simp_defs) : simp_res :=
  let fallback (_ : unit) := SimpOp op args in
  match fuel with
  | O => fallback tt
  | S fuel' =>
      if is_atom "copy" op then
        match args with
        | [TApp g [_]] => if g == "global" then SimpOp op args else SimpVal (TApp g (match args with [TApp _ xs] => xs | _ => [] end))
        | [v] => SimpVal v
        | _ => fallback tt
        end
      else if is_atom "p" k && (is_atom "add" op || is_atom "sub" op)
              && match args with
                 | [_; y] => match const_int y with Some n => is_zero_mod (TAtom "l") n | None => false end
                 | _ => false
                 end
      then
        match args with [x; _] => SimpVal x | _ => fallback tt end
      else
        let folded :=
          if is_int_class k && foldable_op op && forallb is_const_term args then
            let* arg_ks := op_arg_classes op k filc in
            let* xs := arg_numbers arg_ks args in
            let* v := eval_alu op k xs in
            Some (SimpVal (TApp "const" [TInt v]))
          else None in
        match folded with
        | Some r => r
        | None =>
            let comm :=
              if is_int_class k && commutative_op op then
                match args with
                | [x; y] =>
                    if is_const_term x && negb (is_const_term y)
                    then Some (simplified fuel' k op [y; x] classes filc bools defs)
                    else None
                | _ => None
                end
              else None in
            match comm with
            | Some r => r
            | None =>
                let mirror :=
                  match op, args with
                  | TApp f [c; ck], [x; y] =>
                      if (f == "cmp") && is_int_class ck && is_const_term x && negb (is_const_term y) then
                        let* c1 := mirrored_cond c in
                        Some (simplified fuel' k (TApp "cmp" [c1; ck]) [y; x] classes filc bools defs)
                      else None
                  | _, _ => None
                  end in
                match mirror with
                | Some r => r
                | None =>
                    let id_res := if is_int_class k then apply_identity op k args bools else None in
                    match id_res with
                    | Some r => r
                    | None =>
                        match cancel_arith k op args defs with
                        | Some (SimpOp op1 args1) =>
                            simplified fuel' k op1 args1 classes filc bools defs
                        | Some r => r
                        | None =>
                            let cmp_res :=
                              match op with
                              | TApp f [c; ck] =>
                                  if (f == "cmp") && is_int_class ck then
                                    match boolean_cmp c ck k args classes bools defs with
                                    | Some r => Some r
                                    | None =>
                                        match cancel_cmp c ck args defs with
                                        | Some args1 =>
                                            Some (simplified fuel' k op args1 classes filc bools defs)
                                        | None => None
                                        end
                                    end
                                  else None
                              | _ => None
                              end in
                            match cmp_res with
                            | Some r => r
                            | None =>
                                match op, args with
                                | TApp f [t], [v] =>
                                    if f == "ext" then
                                      match tmp_name v with
                                      | [b] =>
                                          let bool_ext :=
                                            let* eqs := nm_find b bools in
                                            let* e := same_class_temp classes k eqs in
                                            Some (SimpVal (tmp e)) in
                                          match bool_ext with
                                          | Some r => r
                                          | None =>
                                              match nm_find b (sd_main defs), nm_find b classes with
                                              | Some (DefNarrow t0), Some kb =>
                                                  if narrow_fits t0 t && term_eqb kb k
                                                  then SimpVal v
                                                  else fallback tt
                                              | _, _ => fallback tt
                                              end
                                          end
                                      | _ => fallback tt
                                      end
                                    else fallback tt
                                | _, _ => fallback tt
                                end
                            end
                        end
                    end
                end
            end
        end
  end.

(** ## Value numbering, address rebasing, and fact recording

    Pure operations are keyed in the dominator-scoped availability map, while
    pointer additions of class-`l` linear forms rebase onto earlier elements in
    the same block to expose shared capability flights. *)

(** Constructing the value-numbering key of a pure operation sorts commutative
    integer operands and scopes pointer-plus-constant keys to their block,
    matching `numbered/5`. *)
Definition numbered_key (k op : term) (args : list term) (lbl : term) : option term :=
  if pure_op op && negb (is_atom "copy" op) then
    let key0 := if commutative_op op && is_int_class k then msort term_compare args else args in
    let key :=
      if is_atom "p" k && existsb is_const_term args
      then TApp "-" [TList key0; lbl]
      else TList key0 in
    Some (TApp "-" [TApp "-" [k; op]; key])
  else None.

(** Inserting one expression into [avail] binds its [numbered_key] to [d],
    matching `numbered_avail/6`. *)
Definition numbered_avail (k lbl d op : term) (args : list term) (avail : simp_avail)
  : simp_avail :=
  match numbered_key k op args lbl with
  | Some key => mkSimpAvail (nm_add key d (sa_num avail)) (sa_based avail)
  | None => avail
  end.

(** Retrieving the 64-bit linear form `Key + C` of class-`l` temporary [t]
    defaults to `v(T) + 0`, matching `lin/4`. *)
Definition lin_of (defs : simp_defs) (t : term) : term * Z :=
  match nm_find t (sd_lin defs) with
  | Some p => p
  | None => (TApp "v" [t], 0)
  end.

(** Retrieving the signed 32-bit range of class-`w` temporary [y] checks
    explicit range facts first and narrow load/extension facts second,
    matching `range/4`. *)
Definition range_of (defs : simp_defs) (y : term) : option (Z * Z) :=
  match nm_find y (sd_range defs) with
  | Some r => Some r
  | None =>
      match nm_find y (sd_main defs) with
      | Some (DefNarrow t) => narrow_range t
      | _ => None
      end
  end.

(** Computing the 64-bit linear form of a class-`l` operation tracks constant
    offsets, shifts, multiplications, and range-checked `w`-to-`l` extensions,
    matching `lin_op/5`. *)
Definition lin_op (op : term) (args : list term) (defs : simp_defs) : option (term * Z) :=
  match op, args with
  | TAtom a, [va; vn] =>
      match tmp_name va, const_int vn with
      | [ta], Some n =>
          let '(key0, c0) := lin_of defs ta in
          if a == "add" then Some (key0, (c0 + n) mod 18446744073709551616)
          else if a == "sub" then Some (key0, (c0 - n) mod 18446744073709551616)
          else if a == "shl" then
            let s := n mod 64 in
            if 0 <? s then
              Some (TApp "shl" [key0; TInt s], (Z.shiftl c0 s) mod 18446744073709551616)
            else None
          else if a == "mul" then
            let m := n mod 18446744073709551616 in
            Some (TApp "mul" [key0; TInt m], (c0 * m) mod 18446744073709551616)
          else None
      | _, _ => None
      end
  | TApp f [t], [vb] =>
      if f == "ext" then
        match tmp_name vb with
        | [b] =>
            if is_atom "uw" t then
              match nm_find b (sd_wsum defs) with
              | Some (y, c) =>
                  match range_of defs y with
                  | Some (lo, hi) =>
                      if (0 <=? lo) && (hi + c <=? 4294967295)
                      then Some (TApp "ext" [TAtom "uw"; y], c)
                      else Some (TApp "ext" [TAtom "uw"; b], 0)
                  | None => Some (TApp "ext" [TAtom "uw"; b], 0)
                  end
              | None => Some (TApp "ext" [TAtom "uw"; b], 0)
              end
            else if is_atom "sw" t then
              match nm_find b (sd_wsum defs) with
              | Some (y, c0) =>
                  match range_of defs y with
                  | Some (lo, hi) =>
                      let s := if 2147483648 <=? c0 then c0 - 4294967296 else c0 in
                      if (-2147483648 <=? lo + s) && (hi + s <=? 2147483647)
                      then Some (TApp "ext" [TAtom "sw"; y], s mod 18446744073709551616)
                      else Some (TApp "ext" [TAtom "sw"; b], 0)
                  | None => Some (TApp "ext" [TAtom "sw"; b], 0)
                  end
              | None => Some (TApp "ext" [TAtom "sw"; b], 0)
              end
            else None
        | _ => None
        end
      else None
  | _, _ => None
  end.

(** Recognizing a pointer-plus-linear-offset addition computes its per-block
    rebasing key `based(L, P, Key)` and offset `C`, matching `based/7`. *)
Definition based_addr (k op : term) (args : list term) (lbl : term)
    (classes : nmap term) (defs : simp_defs) : option (term * Z) :=
  if is_atom "p" k && is_atom "add" op then
    match args with
    | [vp; vt] =>
        match tmp_name vp, tmp_name vt with
        | [p], [t] =>
            match nm_find t classes with
            | Some kt =>
                if is_atom "l" kt then
                  let '(key, c) := lin_of defs t in
                  Some (TApp "based" [lbl; p; key], c)
                else None
            | None => None
            end
        | _, _ => None
        end
    | _ => None
    end
  else None.

(** Consulting the value-numbering and rebasing tables either reuses an earlier
    temporary, rebases onto an earlier address in the same block, or keeps the
    operation, matching `rebased_op/7`. *)
Definition rebased_op (k op0 : term) (args0 : list term) (lbl : term)
    (base : option (term * Z)) (avail : simp_avail) : rebase_res :=
  let num_hit :=
    let* key := numbered_key k op0 args0 lbl in
    nm_find key (sa_num avail) in
  match num_hit with
  | Some e => FoundSame e
  | None =>
      match base with
      | Some (bk, c) =>
          match nm_find bk (sa_based avail) with
          | Some (b, c0) =>
              let dist := (c - c0) mod 18446744073709551616 in
              if dist =? 0 then FoundSame b
              else
                let '(op, args) :=
                  if dist <? 9223372036854775808 then
                    (TAtom "add", [tmp b; TApp "const" [TInt dist]])
                  else
                    (TAtom "sub", [tmp b; TApp "const" [TInt (18446744073709551616 - dist)]]) in
                let rebased_hit :=
                  let* key := numbered_key k op args lbl in
                  nm_find key (sa_num avail) in
                match rebased_hit with
                | Some e => FoundSame e
                | None => FoundOp op args
                end
          | None => FoundOp op0 args0
          end
      | None => FoundOp op0 args0
      end
  end.

(** Recording the first address of a linear family within a block leaves any
    existing anchor intact, matching `based_avail/4`. *)
Definition based_avail (base : option (term * Z)) (d : term) (avail : simp_avail)
  : simp_avail :=
  match base with
  | Some (bk, c) =>
      if nm_mem bk (sa_based avail) then avail
      else mkSimpAvail (sa_num avail) (nm_add bk (d, c) (sa_based avail))
  | None => avail
  end.

(** Detecting whether a kept operation produces a boolean zero-or-one value
    returns any existing equal boolean temporaries, matching `bool_result/5`. *)
Definition bool_result (op : term) (args : list term)
    (bools : nmap (list (term * term))) : option (list (term * term)) :=
  match op with
  | TApp f [_; _] => if f == "cmp" then Some [] else None
  | TApp f [_] =>
      if f == "ext" then
        match args with
        | [v] => match tmp_name v with [b] => nm_find b bools | _ => None end
        | _ => None
        end
      else None
  | TAtom a =>
      if (a == "and")
         && match args with [_; y] => match const_int y with Some n => n =? 1 | None => false end | _ => false end
      then Some []
      else if (a == "and") || (a == "or") || (a == "xor") then
        match args with
        | [x; y] => if is_boolean bools x && is_boolean bools y then Some [] else None
        | _ => None
        end
      else None
  | _ => None
  end.

(** Recording linear offset, range, and 32-bit sum facts for a kept definition
    matches `offset_facts/6`. *)
Definition offset_facts (d k op : term) (args : list term) (defs : simp_defs) : simp_defs :=
  if is_atom "l" k then
    match lin_op op args defs with
    | Some p =>
        mkSimpDefs (sd_main defs) (sd_arith defs) (nm_add d p (sd_lin defs))
                   (sd_range defs) (sd_wsum defs)
    | None => defs
    end
  else if is_atom "w" k then
    match op, args with
    | TAtom a, [va; vn] =>
        match const_int vn with
        | Some n =>
            if a == "shr" then
              let s := n mod 32 in
              if 0 <? s then
                let hi := Z.shiftl 1 (32 - s) - 1 in
                mkSimpDefs (sd_main defs) (sd_arith defs) (sd_lin defs)
                           (nm_add d (0, hi) (sd_range defs)) (sd_wsum defs)
              else defs
            else if a == "and" then
              let m := n mod 4294967296 in
              if m <? 2147483648 then
                mkSimpDefs (sd_main defs) (sd_arith defs) (sd_lin defs)
                           (nm_add d (0, m) (sd_range defs)) (sd_wsum defs)
              else defs
            else if a == "add" then
              match tmp_name va with
              | [y] =>
                  mkSimpDefs (sd_main defs) (sd_arith defs) (sd_lin defs)
                             (sd_range defs) (nm_add d (y, n mod 4294967296) (sd_wsum defs))
              | _ => defs
              end
            else if a == "sub" then
              match tmp_name va with
              | [y] =>
                  mkSimpDefs (sd_main defs) (sd_arith defs) (sd_lin defs)
                             (sd_range defs) (nm_add d (y, (- n) mod 4294967296) (sd_wsum defs))
              | _ => defs
              end
            else defs
        | None => defs
        end
    | _, _ => defs
    end
  else defs.

(** Recording all facts learned from kept definition `D = Op(Args)` updates the
    boolean table and definition maps, matching `facts/8`. *)
Definition record_facts (d k op : term) (args : list term)
    (bools0 : nmap (list (term * term))) (defs0 : simp_defs)
  : nmap (list (term * term)) * simp_defs :=
  let bools :=
    match bool_result op args bools0 with
    | Some eqs => nm_add d ((k, d) :: eqs) bools0
    | None => bools0
    end in
  let main1 :=
    match op with
    | TApp f [c; ck] =>
        if (f == "cmp") && is_int_class ck then
          match args with
          | [a; b] =>
              let is_not :=
                if is_atom "eq" c then
                  match tmp_name a, const_int b with
                  | [tb], Some z =>
                      if is_zero_mod ck z && nm_mem tb bools0 then Some tb else None
                  | _, _ => None
                  end
                else None in
              match is_not with
              | Some tb => nm_add d (DefNot tb) (sd_main defs0)
              | None => nm_add d (DefCmp c ck a b) (sd_main defs0)
              end
          | _ => sd_main defs0
          end
        else sd_main defs0
    | TApp f [t] =>
        if ((f == "load") || (f == "ext")) && narrow_fits t t
        then nm_add d (DefNarrow t) (sd_main defs0)
        else sd_main defs0
    | _ => sd_main defs0
    end in
  let arith1 :=
    if (is_atom "p" k || is_int_class k) && (is_atom "add" op || is_atom "sub" op) then
      match args with
      | [a1; a2] => nm_add d (k, op, a1, a2) (sd_arith defs0)
      | _ => sd_arith defs0
      end
    else sd_arith defs0 in
  let defs2 := mkSimpDefs main1 arith1 (sd_lin defs0) (sd_range defs0) (sd_wsum defs0) in
  (bools, offset_facts d k op args defs2).

(** ## Dominator-tree folding walk

    Walking the dominator tree in preorder simplifies each block's phis,
    instructions, and terminator while accumulating replacements and branch
    folds. *)

(** Substituting operands of a non-`let` instruction through [reps] matches
    `inst_subst/3`. *)
Definition inst_subst (reps : nmap term) (i : term) : term :=
  match i with
  | TApp f xs =>
      if (f == "store") || (f == "atomic_store") then
        match xs with
        | [w; v; a] => TApp f [w; subst_val reps v; subst_val reps a]
        | _ => i
        end
      else if f == "access" then
        match xs with
        | [k; a; s; al] => TApp f [k; subst_val reps a; s; al]
        | _ => i
        end
      else if f == "asm_fixed" then
        match xs with
        | [m; TList ins; outs] =>
            let ins' :=
              map (fun p =>
                     match pair_parts p with
                     | Some (r, v) => TApp "-" [r; subst_val reps v]
                     | None => p
                     end) ins in
            TApp f [m; TList ins'; outs]
        | _ => i
        end
      else if f == "call" then
        match xs with
        | [r; g; TList args] =>
            let args' :=
              map (fun a =>
                     match a with
                     | TApp h [k; v] => if h == "arg" then TApp h [k; subst_val reps v] else a
                     | _ => a
                     end) args in
            TApp f [r; subst_val reps g; TList args']
        | _ => i
        end
      else i
  | _ => i
  end.

(** Folding one phi substitutes known replacements into its arguments, records
    a replacement when all non-self operands match one value, and marks boolean
    phis, matching `fold_phi/5`. *)
Definition fold_phi (classes : nmap term)
    (st : nmap term * nmap (list (term * term))) (p : term)
  : term * (nmap term * nmap (list (term * term))) :=
  let '(reps0, bools0) := st in
  match p with
  | TApp f [d_term; k; TList pairs0] =>
      if f == "phi" then
        match tmp_name d_term with
        | [d] =>
            let pairs :=
              map (fun a =>
                     match pair_parts a with
                     | Some (pred, v) => TApp "-" [pred; subst_val reps0 v]
                     | None => a
                     end) pairs0 in
            let vs := flat_map (fun a => match pair_parts a with Some (_, v) => [v] | None => [] end) pairs in
            let others := filter (fun v => negb (term_eqb v d_term)) vs in
            let distinct := sort term_compare others in
            let reps :=
              match distinct with
              | [v] =>
                  match replacement_val classes k v with
                  | Some r => nm_add d r reps0
                  | None => reps0
                  end
              | _ => reps0
              end in
            let bools :=
              match others with
              | [] => bools0
              | _ =>
                  if forallb (is_boolean bools0) others then nm_add d [(k, d)] bools0
                  else bools0
              end in
            (TApp f [d_term; k; TList pairs], (reps, bools))
        | _ => (p, st)
        end
      else (p, st)
  | _ => (p, st)
  end.

(** Folding one instruction simplifies `let` bindings through [simplified] and
    [rebased_op] and substitutes operands in all other instructions, matching
    `fold_inst/8`. *)
Definition fold_inst (lbl : term) (classes : nmap term) (filc : bool)
    (avail0 : simp_avail) (st0 : walk_state) (i0 : term)
  : term * simp_avail * walk_state :=
  match let_parts i0 with
  | Some (d_term, k, op0, args0) =>
      match tmp_name d_term with
      | [d] =>
          let reps0 := ws_reps st0 in
          let bools0 := ws_bools st0 in
          let defs0 := ws_defs st0 in
          let args1 := map (subst_val reps0) args0 in
          match simplified 16 k op0 args1 classes filc bools0 defs0 with
          | SimpVal v =>
              let i := let_term d_term k (TAtom "copy") [v] in
              let reps :=
                match replacement_val classes k v with
                | Some rep => nm_add d rep reps0
                | None => reps0
                end in
              let bools :=
                if is_boolean bools0 v then nm_add d [(k, d)] bools0 else bools0 in
              (i, avail0, mkWalkState reps bools defs0 (ws_out st0) (ws_folded st0))
          | SimpOp op1 args2 =>
              let base := based_addr k op1 args2 lbl classes defs0 in
              match rebased_op k op1 args2 lbl base avail0 with
              | FoundSame e =>
                  let i := let_term d_term k (TAtom "copy") [tmp e] in
                  let reps := nm_add d (tmp e) reps0 in
                  let bools :=
                    match nm_find e bools0 with
                    | Some eqs => nm_add d ((k, d) :: eqs) bools0
                    | None => bools0
                    end in
                  let avail := based_avail base e avail0 in
                  (i, avail, mkWalkState reps bools defs0 (ws_out st0) (ws_folded st0))
              | FoundOp op args =>
                  let i := let_term d_term k op args in
                  let avail1 :=
                    numbered_avail k lbl d op args
                      (numbered_avail k lbl d op1 args2 avail0) in
                  let avail := based_avail base d avail1 in
                  let '(bools, defs) := record_facts d k op args bools0 defs0 in
                  (i, avail, mkWalkState reps0 bools defs (ws_out st0) (ws_folded st0))
              end
          end
      | _ => (inst_subst (ws_reps st0) i0, avail0, st0)
      end
  | None => (inst_subst (ws_reps st0) i0, avail0, st0)
  end.

(** Folding a block's instructions processes each instruction in order and
    returns the rewritten instruction list, updated availability, and state. *)
Fixpoint fold_insts (lbl : term) (classes : nmap term) (filc : bool)
    (avail : simp_avail) (st : walk_state) (insts : list term) (out_rev : list term)
  : list term * simp_avail * walk_state :=
  match insts with
  | [] => (rev' out_rev, avail, st)
  | i0 :: rest =>
      let '(i, avail1, st1) := fold_inst lbl classes filc avail st i0 in
      fold_insts lbl classes filc avail1 st1 rest (i :: out_rev)
  end.

(** Folding a block terminator substitutes known values, collapses constant or
    same-target branches into `goto`, and flips negated boolean branches,
    matching `fold_jump/7`. *)
Definition fold_jump (reps : nmap term) (bools : nmap (list (term * term)))
    (defs : simp_defs) (f0 : bool) (j0 : term) : term * bool :=
  match j0 with
  | TApp f xs =>
      if f == "branch" then
        match xs with
        | [v0; t1; t2] =>
            let v := subst_val reps v0 in
            match const_int v with
            | Some n =>
                let tgt := if negb ((n mod 4294967296) =? 0) then t1 else t2 in
                (TApp "goto" [tgt], true)
            | None =>
                if term_eqb t1 t2 then (TApp "goto" [t1], true)
                else
                  match tmp_name v with
                  | [x] =>
                      match nm_find x (sd_main defs) with
                      | Some (DefNot b) =>
                          if nm_mem b bools then (TApp "branch" [tmp b; t2; t1], f0)
                          else (TApp "branch" [v; t1; t2], f0)
                      | _ => (TApp "branch" [v; t1; t2], f0)
                      end
                  | _ => (TApp "branch" [v; t1; t2], f0)
                  end
            end
        | _ => (j0, f0)
        end
      else if f == "ret" then
        match xs with [v0] => (TApp "ret" [subst_val reps v0], f0) | _ => (j0, f0) end
      else if f == "rets" then
        match xs with
        | [TList vs0] => (TApp "rets" [TList (map (subst_val reps) vs0)], f0)
        | _ => (j0, f0)
        end
      else (j0, f0)
  | _ => (j0, f0)
  end.

(** Walking the dominator tree folds each reachable block and recurses on its
    dominator children with the block's updated availability map, matching
    `walk/7`. *)
Fixpoint walk_dom (fuel : nat) (kids : nmap (list name)) (by_label : nmap tblock)
    (classes : nmap term) (filc : bool) (lbl : name) (avail0 : simp_avail)
    (st0 : walk_state) : option walk_state :=
  match fuel with
  | O => None
  | S fuel' =>
      let* b := nm_find lbl by_label in
      let '(phis_rev, (reps1, bools1)) :=
        fold_left
          (fun acc p =>
             let '(ps, rb) := acc in
             let '(p', rb') := fold_phi classes rb p in
             (p' :: ps, rb'))
          (tb_phis b) ([], (ws_reps st0, ws_bools st0)) in
      let st_mid := mkWalkState reps1 bools1 (ws_defs st0) (ws_out st0) (ws_folded st0) in
      let '(insts, avail1, st1) :=
        fold_insts lbl classes filc avail0 st_mid (tb_insts b) [] in
      let '(j, f2) := fold_jump (ws_reps st1) (ws_bools st1) (ws_defs st1) (ws_folded st1) (tb_jump b) in
      let out2 := nm_add lbl (mkTBlock lbl (rev' phis_rev) insts j) (ws_out st1) in
      let st2 := mkWalkState (ws_reps st1) (ws_bools st1) (ws_defs st1) out2 f2 in
      let* cs := nm_find lbl kids in
      fold_left
        (fun acc c =>
           let* s := acc in walk_dom fuel' kids by_label classes filc c avail1 s)
        cs (Some st2)
  end.

(** Running one dominator-tree fold over [bs] returns the rewritten blocks,
    accumulated replacement map, and whether any branch folded, matching
    `fold_func/7`. *)
Definition fold_func (classes : nmap term) (filc : bool) (bs0 : list tblock)
    (g : cfg) (idom : nmap name)
  : option (list tblock * nmap term * bool) :=
  let* kids := dom_children g idom in
  let by_label := nm_of_list (map (fun b => (tb_label b, b)) bs0) in
  let init := mkWalkState nm_empty nm_empty empty_defs nm_empty false in
  let* st := walk_dom (S (length (cfg_rpo g))) kids by_label classes filc (cfg_entry g) empty_avail init in
  let bs :=
    map (fun b => match nm_find (tb_label b) (ws_out st) with Some b' => b' | None => b end) bs0 in
  Some (bs, ws_reps st, ws_folded st).

(** ## Pruning unreachable blocks and single-pass trivial phis

    After a branch folds to `goto`, unreachable blocks and dead incoming phi
    edges disappear and newly trivial phis collapse in one substitution pass. *)

(** Dropping site records for removed blocks and removed phis matches
    `drop_sites/4`. *)
Definition drop_sites (labels phis rs0 : list term) : list term :=
  let la := fold_left (fun m l => nm_add l tt m) labels nm_empty in
  let ta := fold_left (fun m t => nm_add t tt m) phis nm_empty in
  filter
    (fun r =>
       match r with
       | TApp f [s; _] =>
           if f == "site" then
             match s with
             | TApp g [l; _] => if g == "inst" then negb (nm_mem l la) else true
             | TApp g [x] =>
                 if g == "jump" then negb (nm_mem x la)
                 else if g == "phi" then negb (nm_mem x ta)
                 else true
             | _ => true
             end
           else true
       | _ => true
       end)
    rs0.

(** Pruning unreachable blocks removes every block outside `cfg_rpo` and strips
    dead incoming phi edges, dropping removed block and phi sites from [rs0],
    matching `prune/4`. *)
Definition prune_blocks (bs0 : list tblock) (rs0 : list term)
  : option (list tblock * list term) :=
  let* g := term_cfg bs0 in
  let reach := reached g in
  let succs := cfg_succs g in
  let is_live_edge (lbl pred : term) : bool :=
    nm_mem pred reach
    && match nm_find pred succs with
       | Some ss => existsb (term_eqb lbl) ss
       | None => false
       end in
  let live_phi (lbl : term) (p : term) : term :=
    match p with
    | TApp f [d; k; TList pairs0] =>
        if f == "phi" then
          let pairs :=
            filter
              (fun a =>
                 match pair_parts a with
                 | Some (pred, _) => is_live_edge lbl pred
                 | None => false
                 end)
              pairs0 in
          TApp f [d; k; TList pairs]
        else p
    | _ => p
    end in
  let '(kept, gone) := partition (fun b => nm_mem (tb_label b) reach) bs0 in
  let bs :=
    map (fun b => mkTBlock (tb_label b) (map (live_phi (tb_label b)) (tb_phis b))
                           (tb_insts b) (tb_jump b)) kept in
  let unchanged :=
    match gone with
    | [] =>
        forallb (fun p => term_eqb (block_term (fst p)) (block_term (snd p))) (combine bs0 bs)
    | _ => false
    end in
  if unchanged then Some (bs, rs0)
  else
    let gone_labels := map tb_label gone in
    let gone_phis := flat_map (fun b => flat_map phi_def (tb_phis b)) gone in
    Some (bs, drop_sites gone_labels gone_phis rs0).

(** Eliminating phis whose non-self operands are one replaceable value matches
    `simplify:trivial_phis/5`. *)
Definition trivial_phis_simp (classes : nmap term) (bs0 : list tblock) (rs0 : list term)
  : option (list tblock * list term) :=
  let pairs0 :=
    flat_map
      (fun b =>
         flat_map
           (fun p =>
              match p with
              | TApp f [d_term; k; TList args] =>
                  if f == "phi" then
                    match tmp_name d_term with
                    | [d] =>
                        let vs :=
                          flat_map (fun a => match pair_parts a with Some (_, v) => [v] | None => [] end) args in
                        let others := filter (fun v => negb (term_eqb v d_term)) vs in
                        match sort term_compare others with
                        | [v0] =>
                            match replacement_val classes k v0 with
                            | Some v => [(d, v)]
                            | None => []
                            end
                        | _ => []
                        end
                    | _ => []
                    end
                  else []
              | _ => []
              end)
           (tb_phis b))
      bs0 in
  match pairs0 with
  | [] => Some (bs0, rs0)
  | _ =>
      let* reps := chain_reps pairs0 in
      let* opt_pair_1 := reps_blocks_map reps bs0 in let '(bs, smap) := opt_pair_1 in
      Some (bs, copied_records reps smap rs0)
  end.

(** Running up to [rounds] folding rounds repeats folding, substitution,
    pruning, and trivial-phi removal while a branch folds, matching
    `fold_rounds/8`. *)
Fixpoint fold_rounds (rounds : nat) (classes : nmap term) (filc : bool)
    (bs0 : list tblock) (g : cfg) (idom : nmap name) (rs0 : list term)
  : option (list tblock * list term) :=
  let* opt_pair_2 := fold_func classes filc bs0 g idom in let '(bs1, reps, folded) := opt_pair_2 in
  let* opt_pair_3 :=
    if nm_is_empty reps then Some (bs1, rs0)
    else
      let* opt_pair_21 := reps_blocks_map reps bs1 in let '(bs', smap) := opt_pair_21 in
      Some (bs', copied_records reps smap rs0) in let '(bs2, rs2) := opt_pair_3 in
  let* opt_pair_4 :=
    if negb folded && Nat.eqb (length (cfg_rpo g)) (length bs0) then Some (bs2, rs2)
    else
      let* opt_pair_22 := prune_blocks bs2 rs2 in let '(bs_p, rs_p) := opt_pair_22 in
      trivial_phis_simp classes bs_p rs_p in let '(bs3, rs3) := opt_pair_4 in
  match rounds with
  | O | S O => Some (bs3, rs3)
  | S rounds' =>
      if folded then
        let* g3 := term_cfg bs3 in
        let* idom3 := cfg_idoms g3 in
        fold_rounds rounds' classes filc bs3 g3 idom3 rs3
      else Some (bs3, rs3)
  end.

(** ## Dead pure code elimination

    A backwards reachability mark from all non-removable instructions and block
    terminators identifies every live pure definition and phi, dropping all
    unused pure definitions and updating context sites. *)

(** Marking live temporaries starting from [work] explores pure-definition
    dependencies up to [fuel] steps, matching `mark/4`. *)
Fixpoint mark_live (fuel : nat) (work : list term) (pure : nmap (list term))
    (live : nmap unit) : nmap unit :=
  match fuel, work with
  | O, _ => live
  | _, [] => live
  | S fuel', t :: ts =>
      if nm_mem t live then mark_live fuel' ts pure live
      else
        let live1 := nm_add t tt live in
        let ts1 :=
          match nm_find t pure with
          | Some us => us ++ ts
          | None => ts
          end in
        mark_live fuel' ts1 pure live1
  end.

(** Removing dead pure instructions from one block builds the kept instruction
    list and old-to-new site map, matching `live_insts/8`. *)
Fixpoint live_insts_ctx (pure : nmap (list term)) (live : nmap unit) (lbl : term)
    (old_idx new_idx : Z) (insts : list term) (out_rev : list term)
    (map_rev : list (term * term))
  : list term * list (term * term) :=
  match insts with
  | [] => (rev' out_rev, rev' map_rev)
  | i :: rest =>
      let dead :=
        match let_parts i with
        | Some (d, _, _, _) =>
            match tmp_name d with
            | [t] => nm_mem t pure && negb (nm_mem t live)
            | _ => false
            end
        | None => false
        end in
      let emitted := if dead then [] else [i] in
      let '(map_rev1, next_idx) := emission_sites_rev lbl old_idx new_idx emitted map_rev in
      live_insts_ctx pure live lbl (old_idx + 1) next_idx
        rest (rev_append emitted out_rev) map_rev1
  end.

(** Eliminating unused pure definitions and phis across [bs0] matches
    `dead_code/4`. *)
Definition dead_code (bs0 : list tblock) (rs0 : list term)
  : option (list tblock * list term) :=
  let pure_uses :=
    flat_map
      (fun b =>
         flat_map
           (fun p =>
              match p with
              | TApp f [d_term; _; TList pairs] =>
                  if f == "phi" then
                    match tmp_name d_term with
                    | [d] =>
                        let vs :=
                          flat_map (fun a => match pair_parts a with Some (_, v) => [v] | None => [] end) pairs in
                        [(d, temps vs)]
                    | _ => []
                    end
                  else []
              | _ => []
              end)
           (tb_phis b)
         ++ flat_map
              (fun i =>
                 if removable_inst i then
                   match let_parts i, inst_uses i with
                   | Some (d_term, _, _, _), Some us =>
                       match tmp_name d_term with [d] => [(d, us)] | _ => [] end
                   | _, _ => []
                   end
                 else [])
              (tb_insts b))
      bs0 in
  let pure := nm_of_list pure_uses in
  let is_pure_def (i : term) : bool :=
    match let_parts i with
    | Some (d_term, _, _, _) =>
        match tmp_name d_term with [d] => nm_mem d pure | _ => false end
    | None => false
    end in
  let* roots_lists :=
    map_option
      (fun b =>
         let* ius :=
           map_option
             (fun i =>
                if is_pure_def i then Some [] else inst_uses i)
             (tb_insts b) in
         let* jus := jump_uses (tb_jump b) in
         Some (concat ius ++ jus))
      bs0 in
  let roots := concat roots_lists in
  let edge_sum := fold_left (fun acc p => Nat.add acc (length (snd p))) pure_uses O in
  let live := mark_live (S (Nat.add (length roots) edge_sum)) roots pure nm_empty in
  if forallb (fun p => nm_mem (fst p) live) pure_uses then Some (bs0, rs0)
  else
    let pairs :=
      map (fun b =>
             let phis :=
               filter (fun p => match phi_def p with [d] => nm_mem d live | _ => true end)
                      (tb_phis b) in
             let '(insts, smap) :=
               live_insts_ctx pure live (tb_label b) 0 0 (tb_insts b) [] [] in
             (mkTBlock (tb_label b) phis insts (tb_jump b), smap))
          bs0 in
    let bs := map fst pairs in
    let smap := concat (map snd pairs) in
    let rs1 := remap_sites rs0 smap in
    let dead_phis :=
      flat_map
        (fun b =>
           filter (fun d => negb (nm_mem d live))
                  (flat_map phi_def (tb_phis b)))
        bs0 in
    Some (bs, drop_sites [] dead_phis rs1).

(** ## Block bypassing and absorption

    Empty non-entry pass-through blocks whose predecessors do not already jump
    to their target are bypassed, and single-predecessor `goto` targets without
    phis are absorbed into their predecessor while remapping instruction and
    jump sites. *)

(** Listing every jump target of [j], preserving duplicates for a branch with
    equal arms, matches `jump_targets/2`. *)
Definition jump_targets (j : term) : list term :=
  match j with
  | TApp f [t] => if f == "goto" then [t] else []
  | TApp f [_; t1; t2] => if f == "branch" then [t1; t2] else []
  | _ => []
  end.

(** Testing whether target [t] is a plain label rather than `poll(L)` matches
    `atom_label/1`. *)
Definition is_plain_target (t : term) : bool :=
  match t with TApp f [_] => negb (f == "poll") | _ => true end.

(** Computing the incoming-edge predecessor list of each block preserves edge
    multiplicity, matching `edge_preds/2`. *)
Definition edge_preds (bs : list tblock) : nmap (list term) :=
  let pairs :=
    flat_map
      (fun b =>
         map (fun t0 => (target_label t0, tb_label b)) (jump_targets (tb_jump b)))
      bs in
  nm_of_list (group_pairs_by_key pairs).

(** Reading the predecessor list of [lbl] defaults to empty. *)
Definition preds_of (preds : nmap (list term)) (lbl : term) : list term :=
  match nm_find lbl preds with Some ps => ps | None => [] end.

(** Extracting every operand temporary occurrence in instruction [i] preserves
    multiplicity for use counting, matching `operand_temp/2`. *)
Definition inst_operand_temps (i : term) : list term :=
  match i with
  | TApp f xs =>
      if f == "let" then
        match xs with [_; _; _; TList args] => flat_map tmp_name args | _ => [] end
      else if (f == "store") || (f == "atomic_store") then
        match xs with [_; v; a] => tmp_name v ++ tmp_name a | _ => [] end
      else if f == "asm_fixed" then
        match xs with [_; TList ins; _] => flat_map tmp_name (flat_map pair_value ins) | _ => [] end
      else if f == "access" then
        match xs with [_; a; _; _] => tmp_name a | _ => [] end
      else if f == "call" then
        match xs with [_; g; TList args] => tmp_name g ++ flat_map tmp_name (flat_map arg_value args) | _ => [] end
      else []
  | _ => []
  end.

(** Extracting operand temporary occurrences in terminator [j] matches
    `jump_operand/2`. *)
Definition jump_operand_temps (j : term) : list term :=
  match j with
  | TApp f [v; _; _] => if f == "branch" then tmp_name v else []
  | TApp f [v] =>
      if f == "ret" then tmp_name v
      else if f == "rets" then flat_map tmp_name (listed v)
      else []
  | _ => []
  end.

(** Counting operand uses of every temporary across [bs] matches
    `use_counts/2`. *)
Definition use_counts (bs : list tblock) : nmap Z :=
  let add1 (m : nmap Z) (t : term) : nmap Z :=
    let cur := match nm_find t m with Some n => n | None => 0 end in
    nm_add t (cur + 1) m in
  fold_left
    (fun m b =>
       let m1 :=
         fold_left
           (fun m' p =>
              match p with
              | TApp f [_; _; TList pairs] =>
                  if f == "phi" then
                    fold_left add1 (flat_map tmp_name (flat_map pair_value pairs)) m'
                  else m'
              | _ => m'
              end)
           (tb_phis b) m in
       let m2 :=
         fold_left (fun m' i => fold_left add1 (inst_operand_temps i) m') (tb_insts b) m1 in
       fold_left add1 (jump_operand_temps (tb_jump b)) m2)
    bs nm_empty.

(** Adjusting the use count of value [v] by [delta] matches `add_use/4`. *)
Definition add_use (delta : Z) (v : term) (uses : nmap Z) : nmap Z :=
  match tmp_name v with
  | [t] =>
      let cur := match nm_find t uses with Some n => n | None => 0 end in
      nm_add t (cur + delta) uses
  | _ => uses
  end.

(** Testing whether join block [s] has either no phis or at most 64 incoming
    edges avoids quadratic rewriting on huge dispatch headers, matching
    `small_join/3`. *)
Definition small_join (idx : nmap tblock) (preds : nmap (list term)) (s : term) : bool :=
  match nm_find s idx with
  | Some b =>
      match tb_phis b with
      | [] => true
      | _ => Nat.leb (length (preds_of preds s)) 64
      end
  | None => false
  end.

(** Testing whether block [p] jumps to [e] only by plain edges matches
    `plain_edge/3`. *)
Definition plain_edge (idx : nmap tblock) (p e : term) : bool :=
  match nm_find p idx with
  | Some b =>
      let ts := jump_targets (tb_jump b) in
      existsb (term_eqb e) ts && negb (existsb (term_eqb (TApp "poll" [e])) ts)
  | None => false
  end.

(** Removing the first phi edge matching predecessor [e] returns its value and
    the remaining edges, matching `select(E-V, Pairs0, Rest)`. *)
Fixpoint select_phi_edge (e : term) (pairs : list term) : option (term * list term) :=
  match pairs with
  | [] => None
  | a :: rest =>
      match pair_parts a with
      | Some (p, v) =>
          if term_eqb p e then Some (v, rest)
          else
            let* opt_pair_5 := select_phi_edge e rest in let '(v', rest') := opt_pair_5 in
            Some (v', a :: rest')
      | None =>
          let* opt_pair_6 := select_phi_edge e rest in let '(v', rest') := opt_pair_6 in
          Some (v', a :: rest')
      end
  end.

(** Forwarding value [v] through bypassed block [e]'s phis for predecessor [p]
    matches `forwarded/4`. *)
Definition forwarded_val (ephis : nmap (list term)) (p v : term) : term :=
  match tmp_name v with
  | [x] =>
      match nm_find x ephis with
      | Some pairs =>
          match find (fun a => match pair_parts a with Some (p', _) => term_eqb p' p | None => false end) pairs with
          | Some a => match pair_parts a with Some (_, vp) => vp | None => v end
          | None => v
          end
      | None => v
      end
  | _ => v
  end.

(** Retargeting plain jumps from [e] to [t] in block [p] matches
    `retarget/5`. *)
Definition retarget_block (e t p : term) (idx : nmap tblock) : nmap tblock :=
  match nm_find p idx with
  | Some b =>
      let j :=
        match tb_jump b with
        | TApp f [x] =>
            if (f == "goto") && term_eqb x e then TApp "goto" [t] else tb_jump b
        | TApp f [v; t1; t2] =>
            if f == "branch" then
              let u1 := if term_eqb t1 e then t else t1 in
              let u2 := if term_eqb t2 e then t else t2 in
              TApp "branch" [v; u1; u2]
            else tb_jump b
        | j0 => j0
        end in
      nm_add p (mkTBlock (tb_label b) (tb_phis b) (tb_insts b) j) idx
  | None => idx
  end.

(** The state threaded through the empty-block bypass sweep. *)
Record bypass_state : Type := mkBypassState {
  bs_index : nmap tblock;
  bs_preds : nmap (list term);
  bs_uses : nmap Z;
  bs_gone : list term;
  bs_dead_phis : list term
}.

(** Attempting to bypass empty pass-through block [e] updates successor phis,
    predecessor jumps, use counts, and removed-site lists, matching
    `bypass/4`. *)
Definition bypass_one (entry e : term) (st : bypass_state) : bypass_state :=
  let idx0 := bs_index st in
  let preds0 := bs_preds st in
  let uses0 := bs_uses st in
  match nm_find e idx0 with
  | Some eb =>
      match tb_insts eb, tb_jump eb with
      | [], TApp jf [t] =>
          if negb ((jf == "goto") && negb (term_eqb e entry)
                   && is_plain_target t && negb (term_eqb t e))
          then st else
          let epreds := preds_of preds0 e in
          match epreds with
          | [] => st
          | _ =>
              if negb (Nat.eqb (length epreds) (length (nsort epreds)))
                 || existsb (term_eqb e) epreds
              then st else
              let tpreds := preds_of preds0 t in
              if existsb (fun p => existsb (term_eqb p) tpreds) epreds
                 || negb (forallb (fun p => plain_edge idx0 p e) epreds)
                 || negb (small_join idx0 preds0 t)
              then st else
              match nm_find t idx0 with
              | None => st
              | Some tb =>
                  let ephis := tb_phis eb in
                  let tphis0 := tb_phis tb in
                  let count_fwd (d : term) : Z :=
                    fold_left
                      (fun acc p =>
                         match p with
                         | TApp pf [_; _; TList pairs] =>
                             if pf == "phi" then
                               acc + Z.of_nat (length (filter (fun a =>
                                 match pair_parts a with
                                 | Some (pr, v) => term_eqb pr e && term_eqb v (tmp d)
                                 | None => false
                                 end) pairs))
                             else acc
                         | _ => acc
                         end)
                      tphis0 0 in
                  let phis_ok :=
                    forallb
                      (fun p =>
                         match phi_def p with
                         | [d] =>
                             let nd := match nm_find d uses0 with Some n => n | None => 0 end in
                             count_fwd d =? nd
                         | _ => false
                         end)
                      ephis in
                  if negb phis_ok then st else
                  let ephi_map :=
                    nm_of_list
                      (flat_map
                         (fun p =>
                            match p with
                            | TApp pf [d_term; _; TList pairs] =>
                                if pf == "phi" then
                                  match tmp_name d_term with [d] => [(d, pairs)] | _ => [] end
                                else []
                            | _ => []
                            end)
                         ephis) in
                  let '(tphis_rev, uses1) :=
                    fold_left
                      (fun acc tp =>
                         let '(acc_ps, us) := acc in
                         match tp with
                         | TApp pf [d; k; TList pairs0] =>
                             if pf == "phi" then
                               match select_phi_edge e pairs0 with
                               | Some (v, rest) =>
                                   let new_edges :=
                                     map (fun p =>
                                            let vp := forwarded_val ephi_map p v in
                                            (TApp "-" [p; vp], vp))
                                         epreds in
                                   let pairs := rest ++ map fst new_edges in
                                   let us1 := add_use (-1) v us in
                                   let us2 := fold_left (fun u x => add_use 1 (snd x) u) new_edges us1 in
                                   (TApp pf [d; k; TList pairs] :: acc_ps, us2)
                               | None => (tp :: acc_ps, us)
                               end
                             else (tp :: acc_ps, us)
                         | _ => (tp :: acc_ps, us)
                         end)
                      tphis0 ([], uses0) in
                  let uses2 :=
                    fold_left
                      (fun us ep =>
                         match ep with
                         | TApp pf [_; _; TList pairs] =>
                             if pf == "phi" then
                               fold_left (fun u v => add_use (-1) v u) (flat_map pair_value pairs) us
                             else us
                         | _ => us
                         end)
                      ephis uses1 in
                  let idx1 := nm_add t (mkTBlock t (rev' tphis_rev) (tb_insts tb) (tb_jump tb)) idx0 in
                  let idx2 := fold_left (fun ix p => retarget_block e t p ix) epreds idx1 in
                  let idx3 := nm_remove e idx2 in
                  let tpreds2 := filter (fun p => negb (term_eqb p e)) tpreds ++ epreds in
                  let preds1 := nm_remove e (nm_add t tpreds2 preds0) in
                  let ds := flat_map phi_def ephis in
                  mkBypassState idx3 preds1 uses2 (e :: bs_gone st) (ds ++ bs_dead_phis st)
              end
          end
      | _, _ => st
      end
  | None => st
  end.

(** Renaming incoming phi edges and predecessor records from [t] to [b] on
    successor [s] matches `renamed_pred/5`. *)
Definition rename_pred (t b s : term) (st : nmap tblock * nmap (list term))
  : nmap tblock * nmap (list term) :=
  let '(idx0, preds0) := st in
  let rlbl (l : term) : term := if term_eqb l t then b else l in
  let idx1 :=
    match nm_find s idx0 with
    | Some sb =>
        let phis :=
          map (fun p =>
                 match p with
                 | TApp pf [d; k; TList pairs0] =>
                     if pf == "phi" then
                       let pairs :=
                         map (fun a =>
                                match pair_parts a with
                                | Some (p0, v) => TApp "-" [rlbl p0; v]
                                | None => a
                                end) pairs0 in
                       TApp pf [d; k; TList pairs]
                     else p
                 | _ => p
                 end)
              (tb_phis sb) in
        nm_add s (mkTBlock s phis (tb_insts sb) (tb_jump sb)) idx0
    | None => idx0
    end in
  let preds1 := nm_add s (map rlbl (preds_of preds0 s)) preds0 in
  (idx1, preds1).

(** The state threaded through straight-line block absorption. *)
Record absorb_state : Type := mkAbsorbState {
  as_index : nmap tblock;
  as_preds : nmap (list term);
  as_moves : nmap (term * Z);
  as_jump_of : nmap term
}.

(** Repeatedly absorbing single-predecessor `goto` successors into block [b]
    records instruction moves and terminator ownership, matching `absorb/4`. *)
Fixpoint absorb_one (fuel : nat) (entry b : term) (st : absorb_state) : absorb_state :=
  match fuel with
  | O => st
  | S fuel' =>
      let idx0 := as_index st in
      let preds0 := as_preds st in
      match nm_find b idx0 with
      | Some bb =>
          match tb_jump bb with
          | TApp jf [t] =>
              if negb ((jf == "goto") && is_plain_target t
                       && negb (term_eqb t b) && negb (term_eqb t entry))
              then st else
              match preds_of preds0 t with
              | [p0] =>
                  if negb (term_eqb p0 b) then st else
                  match nm_find t idx0 with
                  | Some tb =>
                      match tb_phis tb with
                      | [] =>
                          let ss := nsort (map target_label (jump_targets (tb_jump tb))) in
                          if negb (forallb (small_join idx0 preds0) ss) then st else
                          let off := Z.of_nat (length (tb_insts bb)) in
                          let insts1 := tb_insts bb ++ tb_insts tb in
                          let idx1 := nm_remove t idx0 in
                          let idx2 := nm_add b (mkTBlock b (tb_phis bb) insts1 (tb_jump tb)) idx1 in
                          let '(idx3, preds1) := fold_left (fun acc s => rename_pred t b s acc) ss (idx2, preds0) in
                          let preds2 := nm_remove t preds1 in
                          let moves1 := nm_add t (b, off) (as_moves st) in
                          let '(j, jump_of1) :=
                            match nm_find t (as_jump_of st) with
                            | Some j0 => (j0, nm_remove t (as_jump_of st))
                            | None => (t, as_jump_of st)
                            end in
                          let jump_of2 := nm_add b j jump_of1 in
                          absorb_one fuel' entry b (mkAbsorbState idx3 preds2 moves1 jump_of2)
                      | _ => st
                      end
                  | None => st
                  end
              | _ => st
              end
          | _ => st
          end
      | None => st
      end
  end.

(** Following chained block absorptions resolves block [l] to its final holding
    block and cumulative instruction offset, matching `holder/4`. *)
Fixpoint resolve_holder (fuel : nat) (moves : nmap (term * Z)) (l : term) : term * Z :=
  match fuel with
  | O => (l, 0)
  | S fuel' =>
      match nm_find l moves with
      | Some (b, off0) =>
          let '(h, off1) := resolve_holder fuel' moves b in
          (h, off0 + off1)
      | None => (l, 0)
      end
  end.

(** Updating context records after bypassing and absorbing blocks shifts moved
    instruction sites, transfers jump sites to absorbing holders, and drops
    sites of bypassed blocks and phis, matching `merged_records/6`. *)
Definition merged_records (fuel : nat) (moves : nmap (term * Z)) (jump_of : nmap term)
    (bypassed dead_phis rs0 : list term) : list term :=
  let jump_sites :=
    nm_of_list
      (sort (fun a b => term_compare (fst a) (fst b))
            (flat_map
               (fun r =>
                  match r with
                  | TApp f [TApp g [s]; os] =>
                      if (f == "site") && (g == "jump") then [(s, os)] else []
                  | _ => []
                  end)
               rs0)) in
  let new_jumps :=
    flat_map
      (fun p =>
         match nm_find (snd p) jump_sites with
         | Some os => [TApp "site" [TApp "jump" [fst p]; os]]
         | None => []
         end)
      (nm_to_sorted_list jump_of) in
  let ba := fold_left (fun m l => nm_add l tt m) bypassed nm_empty in
  let da := fold_left (fun m t => nm_add t tt m) dead_phis nm_empty in
  let kept :=
    flat_map
      (fun r =>
         match r with
         | TApp f [s; os] =>
             if f == "site" then
               match s with
               | TApp g [l; TInt i] =>
                   if g == "inst" then
                     let '(h, off) := resolve_holder fuel moves l in
                     [TApp "site" [TApp "inst" [h; TInt (i + off)]; os]]
                   else [r]
               | TApp g [l] =>
                   if g == "jump" then
                     if negb (nm_mem l moves) && negb (nm_mem l jump_of) && negb (nm_mem l ba)
                     then [r] else []
                   else if g == "phi" then
                     if negb (nm_mem l da) then [r] else []
                   else [r]
               | _ => [r]
               end
             else [r]
         | _ => [r]
         end)
      rs0 in
  kept ++ new_jumps.

(** Running the empty-block bypass sweep followed by straight-line block
    absorption updates both blocks and provenance records, matching
    `merge_blocks/5`. *)
Definition merge_blocks (bs0 : list tblock) (rs0 : list term)
  : list tblock * list term * bool :=
  match bs0 with
  | [] => (bs0, rs0, false)
  | entry_b :: _ =>
      let entry := tb_label entry_b in
      let order := map tb_label bs0 in
      let idx0 := nm_of_list (map (fun b => (tb_label b, b)) bs0) in
      let preds0 := edge_preds bs0 in
      let uses0 := use_counts bs0 in
      let bst :=
        fold_left (fun st e => bypass_one entry e st)
                  order (mkBypassState idx0 preds0 uses0 [] []) in
      let fuel := S (length order) in
      let ast :=
        fold_left (fun st b => absorb_one fuel entry b st)
                  order (mkAbsorbState (bs_index bst) (bs_preds bst) nm_empty nm_empty) in
      if match bs_gone bst with [] => true | _ => false end && nm_is_empty (as_moves ast)
      then (bs0, rs0, false)
      else
        let bs :=
          flat_map (fun l => match nm_find l (as_index ast) with Some b => [b] | None => [] end)
                   order in
        let rs := merged_records fuel (as_moves ast) (as_jump_of ast) (bs_gone bst) (bs_dead_phis bst) rs0 in
        (bs, rs, true)
  end.

(** ## Function and module entry points

    The entry points mirror `simplify_context/5` and `simplify_module/2`,
    leaving non-SSA and `setjmp` functions unchanged. *)

(** Simplifying one function together with its context records matches
    `simplify_context/5`. *)
Definition simplify_context (filc : bool) (fn : term) (rs0 : list term)
  : option (term * list term) :=
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
      let* opt_pair_7 := fold_rounds 3 classes filc bs0 g idom rs0 in let '(bs1, rs1) := opt_pair_7 in
      let* opt_pair_8 := dead_code bs1 rs1 in let '(bs2, rs2) := opt_pair_8 in
      let '(bs3, rs3, merged) := merge_blocks bs2 rs2 in
      let* opt_pair_9 :=
        if merged then trivial_phis_simp classes bs3 rs3 else Some (bs3, rs3) in let '(bs, rs) := opt_pair_9 in
      Some (TApp "func" [name; lk; ret; TList params; TList (map block_term bs)], rs)
  | _ => None
  end.

(** Simplifying every strict SSA function in an unchecked module while
    transporting source contexts matches `simplify_module/2`. *)
Definition simplify_module (m0 : term) : option term :=
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
                       let* opt_pair_10 := simplify_context filc it rs0 in let '(fn', rs') := opt_pair_10 in
                       Some (with_context fn' rs')
                   | _ => None
                   end
                 else Some [it]
             | _ => Some [it]
             end)
          code in
      Some (TApp "module" [TList (concat groups)])
  | _ => None
  end.
