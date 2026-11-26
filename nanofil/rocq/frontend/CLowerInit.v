(** This module lowers aggregate and static C initializers, evaluates address
    constants, and emits global data items for the Gallina C frontend.

    It ports the initializer leaf walker, brace-elision rules, designated and
    range initializers, static byte-chunk table, address constant evaluator,
    and global declaration emitter from nanofil/src/c_lower.pl. Every
    definition is pure and zero-axiom so both OCaml extraction and CertiRocq
    λANF compile it directly. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Nanofil Require Import Term Maps.
From Backend Require Import Text Order Pizlonate.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp
  CTypeAst CTypeTables CTypes CLowerState.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** String equality, matching Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Ordered integer map for static initializer chunks

    Static initializers can override earlier offsets via designators. A simple
    AVL tree keyed by byte offset provides logarithmic lookup, insertion, and
    deletion together with linear in-order traversal for gap filling. *)

Inductive zmap (A : Type) : Type :=
| ZMLeaf
| ZMNode (h : Z) (l : zmap A) (k : Z) (v : A) (r : zmap A).

Arguments ZMLeaf {A}.
Arguments ZMNode {A} h l k v r.

Definition zm_height {A : Type} (t : zmap A) : Z :=
  match t with ZMLeaf => 0 | ZMNode h _ _ _ _ => h end.

Definition zm_make {A : Type} (l : zmap A) (k : Z) (v : A) (r : zmap A) : zmap A :=
  ZMNode (1 + Z.max (zm_height l) (zm_height r)) l k v r.

Definition zm_balance {A : Type} (l : zmap A) (k : Z) (v : A) (r : zmap A) : zmap A :=
  let hl := zm_height l in
  let hr := zm_height r in
  if hr + 2 <=? hl then
    match l with
    | ZMNode _ ll lk lv lr =>
        if zm_height lr <=? zm_height ll then zm_make ll lk lv (zm_make lr k v r)
        else
          match lr with
          | ZMNode _ lrl lrk lrv lrr =>
              zm_make (zm_make ll lk lv lrl) lrk lrv (zm_make lrr k v r)
          | ZMLeaf => zm_make l k v r
          end
    | ZMLeaf => zm_make l k v r
    end
  else if hl + 2 <=? hr then
    match r with
    | ZMNode _ rl rk rv rr =>
        if zm_height rl <=? zm_height rr then zm_make (zm_make l k v rl) rk rv rr
        else
          match rl with
          | ZMNode _ rll rlk rlv rlr =>
              zm_make (zm_make l k v rll) rlk rlv (zm_make rlr rk rv rr)
          | ZMLeaf => zm_make l k v r
          end
    | ZMLeaf => zm_make l k v r
    end
  else zm_make l k v r.

Fixpoint zm_find {A : Type} (x : Z) (t : zmap A) : option A :=
  match t with
  | ZMLeaf => None
  | ZMNode _ l k v r =>
      match Z.compare x k with
      | Eq => Some v
      | Lt => zm_find x l
      | Gt => zm_find x r
      end
  end.

Fixpoint zm_add {A : Type} (x : Z) (val : A) (t : zmap A) : zmap A :=
  match t with
  | ZMLeaf => ZMNode 1 ZMLeaf x val ZMLeaf
  | ZMNode _ l k v r =>
      match Z.compare x k with
      | Eq => zm_make l k val r
      | Lt => zm_balance (zm_add x val l) k v r
      | Gt => zm_balance l k v (zm_add x val r)
      end
  end.

Fixpoint zm_remove_min {A : Type} (t : zmap A) : option (Z * A * zmap A) :=
  match t with
  | ZMLeaf => None
  | ZMNode _ ZMLeaf k v r => Some (k, v, r)
  | ZMNode _ l k v r =>
      match zm_remove_min l with
      | Some (mk, mv, l') => Some (mk, mv, zm_balance l' k v r)
      | None => Some (k, v, r)
      end
  end.

Fixpoint zm_del {A : Type} (x : Z) (t : zmap A) : zmap A :=
  match t with
  | ZMLeaf => ZMLeaf
  | ZMNode _ l k v r =>
      match Z.compare x k with
      | Lt => zm_balance (zm_del x l) k v r
      | Gt => zm_balance l k v (zm_del x r)
      | Eq =>
          match r with
          | ZMLeaf => l
          | _ =>
              match zm_remove_min r with
              | Some (rk, rv, r') => zm_balance l rk rv r'
              | None => l
              end
          end
      end
  end.

Fixpoint zm_values_acc {A : Type} (t : zmap A) (acc : list A) : list A :=
  match t with
  | ZMLeaf => acc
  | ZMNode _ l _ v r => zm_values_acc l (v :: zm_values_acc r acc)
  end.

Fixpoint zm_keys_acc {A : Type} (t : zmap A) (acc : list Z) : list Z :=
  match t with
  | ZMLeaf => acc
  | ZMNode _ l k _ r => zm_keys_acc l (k :: zm_keys_acc r acc)
  end.

(** ## Initializer leaf extraction and array completion

    Every initializer lowers to an ordered list of [init_leaf] assignments.
    Walking the initializer entries also determines the completed length of an
    array of unknown size, handling brace elision, nested designators,
    anonymous struct or union members, and GNU range designators. *)

Inductive init_leaf : Type :=
| ILZero (off : Z) (ty : c_type)
| ILVal (off : Z) (ty : c_type) (n : Z)
| ILVals (off : Z) (ty : c_type) (ns : list Z)
| ILExpr (off : Z) (ty : c_type) (e : c_expr)
| ILBits (off : Z) (ty : c_type) (pos w : Z) (e : c_expr).

Inductive slot_type : Type :=
| STType (ty : c_type)
| STBits (ty : c_type) (pos w : Z).

Inductive init_desig : Type :=
| IDField (name : string)
| IDIndex (e : c_expr)
| IDRange (lo hi : c_expr)
| IDAnon (idx : Z).

Definition of_c_desig (d : c_designator) : init_desig :=
  match d with
  | DField n => IDField n
  | DIndex e => IDIndex e
  | DRange lo hi => IDRange lo hi
  end.

Definition init_entry_i : Type := (list init_desig * c_init)%type.

Definition of_c_entry (e : c_init_entry) : init_entry_i :=
  match e with
  | InitEntry ds ini => (map of_c_desig ds, ini)
  end.

Definition wide_type_to_c_type (wt : wide_type) : c_type :=
  match wt with
  | WInt => TInt
  | WUShort => TUShort
  | WUInt => TUInt
  end.

Fixpoint str_elems_aux (fuel : nat) (ini : c_init) (elem : c_type) : option (list Z) :=
  match fuel with
  | O => None
  | S f =>
      match ini with
      | InitExpr (EStr bs) => if is_char_type elem then Some bs else None
      | InitExpr (EWStr wt vs) =>
          if int_type elem then
            match int_info elem, int_info (wide_type_to_c_type wt) with
            | Some (sz1, _), Some (sz2, _) => if Z.eqb sz1 sz2 then Some vs else None
            | _, _ => None
            end
          else None
      | InitList [InitEntry [] inner] =>
          match inner with
          | InitList _ => None
          | _ => str_elems_aux f inner elem
          end
      | _ => None
      end
  end.

Definition str_elems (ini : c_init) (elem : c_type) : option (list Z) :=
  str_elems_aux 4 ini elem.

Definition table_type (ty : c_type) : bool :=
  negb (c_type_eqb ty TBool) && match int_info ty with Some _ => true | None => false end.

Fixpoint int_entries (es : list init_entry_i) (ty : c_type) (acc : list Z)
  : option (list Z) :=
  match es with
  | [] => Some (rev acc)
  | ([], InitExpr (ENum v0 _ _)) :: rest | ([], InitExpr (EChr v0)) :: rest =>
      match convert_int v0 ty with
      | Some v => int_entries rest ty (v :: acc)
      | None => None
      end
  | _ => None
  end.

Fixpoint elem_leaves_acc (vs : list Z) (ty : c_type) (off sz : Z)
  (acc : list init_leaf) : list init_leaf :=
  match vs with
  | [] => acc
  | v :: rest => elem_leaves_acc rest ty (off + sz) sz (ILVal off ty v :: acc)
  end.

Fixpoint effectful_expr (fuel : nat) (e : c_expr) : bool :=
  match fuel with
  | O => true
  | S f =>
      match e with
      | EAssign _ _ _ | ECall _ _ | EStmtExpr _ => true
      | EUn UPreInc _ | EUn UPreDec _ | EUn UPostInc _ | EUn UPostDec _ => true
      | EUn _ a => effectful_expr f a
      | EBin _ a b | EComma a b | EIndex a b | EGCond a b =>
          effectful_expr f a || effectful_expr f b
      | ECond a b c =>
          effectful_expr f a || effectful_expr f b || effectful_expr f c
      | ECast _ a | EConvertVector a _ | EMember a _ | EArrow a _
      | ESizeofExpr a | EAlignofExpr a | ERealPart a | EImagPart a
      | EVaArg a _ | EBitCast _ a =>
          effectful_expr f a
      | EComplit _ es => existsb (effectful_entry f) es
      | EGeneric a gs =>
          effectful_expr f a ||
          existsb (fun g => match g with GAssocType _ x | GAssocDefault x => effectful_expr f x end) gs
      | _ => false
      end
  end
with effectful_init (fuel : nat) (ini : c_init) : bool :=
  match fuel with
  | O => true
  | S f =>
      match ini with
      | InitExpr e => effectful_expr f e
      | InitList es => existsb (effectful_entry f) es
      end
  end
with effectful_entry (fuel : nat) (en : c_init_entry) : bool :=
  match fuel with
  | O => true
  | S f =>
      match en with
      | InitEntry _ ini => effectful_init f ini
      end
  end.

Definition is_static_complit (ini : c_init) (ty : c_type) (env : c_type_env)
  (whole : bool) : option (list c_init_entry) :=
  if whole || negb (is_aggregate ty) then None
  else
    match ini with
    | InitExpr (EComplit tn es) =>
        match type_name_type tn env with
        | TOk (t, _) => if c_type_eqb t ty then Some es else None
        | TErr _ => None
        end
    | _ => None
    end.

Definition is_single_value (st : slot_type) (ini : c_init) (env : c_type_env)
  (whole : bool) : bool :=
  match ini with
  | InitList _ => true
  | _ =>
      match st with
      | STBits _ _ _ => true
      | STType ty =>
          match is_static_complit ini ty env whole with
          | Some _ => true
          | None =>
              if negb (is_aggregate ty) then true
              else
                match ty with
                | TArray elem _ =>
                    match str_elems ini elem with Some _ => true | None => false end
                | TStruct _ | TUnion _ =>
                    if whole then
                      match ini with
                      | InitExpr e =>
                          match expression_type e env with
                          | Some t0 => c_type_eqb (unqualified (value_type t0)) ty
                          | None => false
                          end
                      | InitList _ => true
                      end
                    else false
                | _ => false
                end
          end
      end
  end.

Definition member_slot (m : c_member_layout) : option string * Z * slot_type :=
  match ml_bits m with
  | MBNone => (ml_name m, ml_off m, STType (ml_type m))
  | MBBits pos w => (ml_name m, ml_off m, STBits (ml_type m) pos w)
  end.

Definition aggregate_slot (ty : c_type) (env : c_type_env) (i : Z)
  : option (Z * slot_type) :=
  match ty with
  | TArray elem len =>
      let in_bounds :=
        match len with
        | ALNone => true
        | ALConst n => i <? n
        | _ => false
        end in
      if in_bounds then
        match type_size_align elem env with
        | TOk (sz, _) => Some (i * sz, STType elem)
        | TErr _ => None
        end
      else None
  | TStruct _ =>
      match su_members_of ty env with
      | Some ms =>
          match nth_error ms (Z.to_nat i) with
          | Some m => let '(_, off, st) := member_slot m in Some (off, st)
          | None => None
          end
      | None => None
      end
  | TUnion _ =>
      if Z.eqb i 0 then
        match su_members_of ty env with
        | Some (m :: _) => let '(_, off, st) := member_slot m in Some (off, st)
        | _ => None
        end
      else None
  | _ => None
  end.

Definition anonymous_member (ty : c_type) (fld : string) (env : c_type_env) : option Z :=
  match su_members_of ty env with
  | None => None
  | Some ms =>
      let has_direct :=
        existsb (fun m => match ml_name m with Some n => n == fld | None => false end) ms in
      if has_direct then None
      else
        let fix go (idx : Z) (l : list c_member_layout) : option Z :=
          match l with
          | [] => None
          | m :: rest =>
              match ml_name m, ml_bits m with
              | None, MBNone =>
                  match member_layout (ml_type m) fld env with
                  | Some _ => Some idx
                  | None => go (idx + 1) rest
                  end
              | _, _ => go (idx + 1) rest
              end
          end in
        go 0 ms
  end.

Definition designated_slot (d : init_desig) (ty : c_type) (env : c_type_env)
  (loc : c_loc) : c_tr (Z * Z * slot_type) :=
  match d, ty with
  | IDIndex e, TArray elem len =>
      match const_value e env with
      | TOk (idx, _) =>
          if 0 <=? idx then
            match aggregate_slot (TArray elem len) env idx with
            | Some (off, st) => TOk (idx, off, st)
            | None => sema_err loc "bad array designator"
            end
          else sema_err loc "bad array designator"
      | TErr _ => sema_err loc "bad array designator"
      end
  | IDField fld, TStruct _ | IDField fld, TUnion _ =>
      match su_members_of ty env with
      | Some ms =>
          let fix go (idx : Z) (l : list c_member_layout) : option (Z * Z * slot_type) :=
            match l with
            | [] => None
            | m :: rest =>
                match ml_name m with
                | Some n =>
                    if n == fld then
                      let '(_, off, st) := member_slot m in Some (idx, off, st)
                    else go (idx + 1) rest
                | None => go (idx + 1) rest
                end
            end in
          match go 0 ms with
          | Some r => TOk r
          | None => sema_err loc ("no member " ++ fld)
          end
      | None => sema_err loc ("no member " ++ fld)
      end
  | IDAnon idx, TStruct _ | IDAnon idx, TUnion _ =>
      match su_members_of ty env with
      | Some ms =>
          match nth_error ms (Z.to_nat idx) with
          | Some m => let '(_, off, st) := member_slot m in TOk (idx, off, st)
          | None => sema_err loc ("bad designator for a " ++ c_type_diag_str ty)
          end
      | None => sema_err loc ("bad designator for a " ++ c_type_diag_str ty)
      end
  | _, _ => sema_err loc ("bad designator for a " ++ c_type_diag_str ty)
  end.

Fixpoint split_undesignated (es : list init_entry_i) (pre : list init_entry_i)
  : list init_entry_i * list init_entry_i :=
  match es with
  | [] => (rev pre, [])
  | ((_ :: _, _) :: _) as post => (rev pre, post)
  | e :: rest => split_undesignated rest (e :: pre)
  end.

Fixpoint object_init_f (fuel : nat) (st : slot_type) (off : Z) (ini : c_init)
  (env : c_type_env) (whole : bool) (loc : c_loc) (acc : list init_leaf)
  : c_tr (list init_leaf) :=
  match fuel with
  | O => sema_err loc "initializer recursion limit"
  | S f =>
      match st with
      | STBits t pos w =>
          match ini with
          | InitList [InitEntry _ v] => object_init_f f (STBits t pos w) off v env whole loc acc
          | InitList (_ :: _ :: _) => sema_err loc "excess initializers"
          | InitList [] => sema_err loc "empty bit-field initializer"
          | InitExpr e => TOk (ILBits off t pos w e :: acc)
          end
      | STType ty =>
          match is_static_complit ini ty env whole with
          | Some es => object_init_f f (STType ty) off (InitList es) env whole loc acc
          | None =>
              match ty with
              | TAtomic s p =>
                  match ini with
                  | InitList _ =>
                      sema_err loc "an _Atomic struct or union cannot be initialized by a braced list"
                  | _ => object_init_f f (STType s) off ini env whole loc (ILZero off (TAtomic s p) :: acc)
                  end
              | TVec elem n _ =>
                  match ini with
                  | InitList _ =>
                      object_init_f f (STType (TArray elem (ALConst n))) off ini env whole loc acc
                  | InitExpr e => TOk (ILExpr off ty e :: acc)
                  end
              | TArray elem len =>
                  match ini with
                  | InitList es0 =>
                      let single_str :=
                        match es0 with
                        | [InitEntry [] inner] =>
                            match str_elems inner elem with
                            | Some _ => Some inner
                            | None => None
                            end
                        | _ => None
                        end in
                      match single_str with
                      | Some inner => object_init_f f (STType ty) off inner env whole loc acc
                      | None =>
                          let es := map of_c_entry es0 in
                          match len with
                          | ALConst n =>
                              if table_type elem then
                                match int_entries es elem [] with
                                | Some vs =>
                                    if Z.of_nat (length vs) <=? n then
                                      TOk (ILVals off elem vs :: ILZero off ty :: acc)
                                    else object_init_list_f f ty off es env whole loc acc
                                | None => object_init_list_f f ty off es env whole loc acc
                                end
                              else object_init_list_f f ty off es env whole loc acc
                          | _ => object_init_list_f f ty off es env whole loc acc
                          end
                      end
                  | _ =>
                      match str_elems ini elem with
                      | Some vs =>
                          let too_long :=
                            match len with
                            | ALConst n => n <? Z.of_nat (length vs)
                            | _ => false
                            end in
                          if too_long then sema_err loc "string initializer is too long"
                          else
                            match type_size_align elem env with
                            | TErr err => TErr err
                            | TOk (sz, _) =>
                                let acc1 := ILZero off ty :: acc in
                                if table_type elem then TOk (ILVals off elem vs :: acc1)
                                else TOk (elem_leaves_acc vs elem off sz acc1)
                            end
                      | None => sema_err loc "array initializer must be a list"
                      end
                  end
              | _ =>
                  match ini with
                  | InitList es0 =>
                      let es := map of_c_entry es0 in
                      object_init_list_f f ty off es env whole loc acc
                  | InitExpr e => TOk (ILExpr off ty e :: acc)
                  end
              end
          end
      end
  end

with object_init_list_f (fuel : nat) (ty : c_type) (off : Z) (es : list init_entry_i)
  (env : c_type_env) (whole : bool) (loc : c_loc) (acc : list init_leaf)
  : c_tr (list init_leaf) :=
  match fuel with
  | O => sema_err loc "initializer list recursion limit"
  | S f =>
      let acc0 := ILZero off ty :: acc in
      if is_aggregate ty then
        match slots_f f ty 0 off es 0 env whole loc acc0 with
        | TErr err => TErr err
        | TOk (rest, _, acc1) =>
            match rest with
            | [] => TOk acc1
            | _ => sema_err loc "excess initializers"
            end
        end
      else
        match es with
        | [] => TOk acc0
        | [(_, v)] => object_init_f f (STType ty) off v env whole loc acc0
        | _ => sema_err loc "excess initializers"
        end
  end

with slots_f (fuel : nat) (ty : c_type) (i off : Z) (es0 : list init_entry_i) (max0 : Z)
  (env : c_type_env) (whole : bool) (loc : c_loc) (acc : list init_leaf)
  : c_tr (list init_entry_i * Z * list init_leaf) :=
  match fuel with
  | O => sema_err loc "slots recursion limit"
  | S f =>
      match es0 with
      | [] => TOk ([], max0, acc)
      | (IDRange e1 e2 :: ds, v) :: rest =>
          match const_value e1 env, const_value e2 env with
          | TOk (lo, _), TOk (hi, _) =>
              if (0 <=? lo) && (lo <=? hi) then
                if (lo <? hi) && effectful_init 128 v then
                  sema_err loc "a range designator's initializer has side effects"
                else
                  let expanded :=
                    map (fun k => (IDIndex (ENum k SufNone RadDec) :: ds, v)) (numlist_Z lo hi) in
                  slots_f f ty 0 off (app expanded rest) max0 env whole loc acc
              else sema_err loc "bad range designator"
          | _, _ => sema_err loc "bad range designator"
          end
      | (IDField fld :: ds, v) :: rest =>
          match anonymous_member ty fld env with
          | Some k =>
              slots_f f ty i off ((IDAnon k :: IDField fld :: ds, v) :: rest) max0 env whole loc acc
          | None =>
              match designated_slot (IDField fld) ty env loc with
              | TErr err => TErr err
              | TOk (idx, soff, st) =>
                  let off1 := off + soff in
                  let step :=
                    match ds with
                    | [] => slot_init_f f st off1 v rest env whole loc acc
                    | _ =>
                        match st with
                        | STType sub_ty =>
                            match slots_f f sub_ty 0 off1 [(ds, v)] 0 env whole loc acc with
                            | TErr err => TErr err
                            | TOk (_, _, acc1) => TOk (rest, acc1)
                            end
                        | STBits _ _ _ => sema_err loc "designator into bit-field"
                        end
                    end in
                  match step with
                  | TErr err => TErr err
                  | TOk (es1, acc1) =>
                      let i1 := idx + 1 in
                      slots_f f ty i1 off es1 (Z.max max0 i1) env whole loc acc1
                  end
              end
          end
      | (d :: ds, v) :: rest =>
          match designated_slot d ty env loc with
          | TErr err => TErr err
          | TOk (idx, soff, st) =>
              let off1 := off + soff in
              let step :=
                match ds with
                | [] => slot_init_f f st off1 v rest env whole loc acc
                | _ =>
                    match st with
                    | STType sub_ty =>
                        match slots_f f sub_ty 0 off1 [(ds, v)] 0 env whole loc acc with
                        | TErr err => TErr err
                        | TOk (_, _, acc1) => TOk (rest, acc1)
                        end
                    | STBits _ _ _ => sema_err loc "designator into bit-field"
                    end
                end in
              match step with
              | TErr err => TErr err
              | TOk (es1, acc1) =>
                  let i1 := idx + 1 in
                  slots_f f ty i1 off es1 (Z.max max0 i1) env whole loc acc1
              end
          end
      | ([], v) :: rest =>
          match aggregate_slot ty env i with
          | None => TOk (es0, max0, acc)
          | Some (soff, st) =>
              match slot_init_f f st (off + soff) v rest env whole loc acc with
              | TErr err => TErr err
              | TOk (es1, acc1) =>
                  let i1 := i + 1 in
                  slots_f f ty i1 off es1 (Z.max max0 i1) env whole loc acc1
              end
          end
      end
  end

with slot_init_f (fuel : nat) (st : slot_type) (off : Z) (v : c_init)
  (es0 : list init_entry_i) (env : c_type_env) (whole : bool) (loc : c_loc)
  (acc : list init_leaf) : c_tr (list init_entry_i * list init_leaf) :=
  match fuel with
  | O => sema_err loc "slot_init recursion limit"
  | S f =>
      if is_single_value st v env whole then
        match object_init_f f st off v env whole loc acc with
        | TErr err => TErr err
        | TOk acc1 => TOk (es0, acc1)
        end
      else
        match st with
        | STType sub_ty =>
            let '(pre, post) := split_undesignated es0 [] in
            match slots_f f sub_ty 0 off (([], v) :: pre) 0 env whole loc acc with
            | TErr err => TErr err
            | TOk (rest, _, acc1) => TOk (app rest post, acc1)
            end
        | STBits _ _ _ => sema_err loc "invalid bit-field initializer"
        end
  end.

Fixpoint init_entry_fuel (e : c_init_entry) : nat :=
  match e with InitEntry ds i => (length ds + init_fuel_aux i + 4)%nat end
with init_fuel_aux (i : c_init) : nat :=
  match i with
  | InitExpr _ => 8%nat
  | InitList es => fold_left (fun a e => (a + init_entry_fuel e)%nat) es 16%nat
  end.

Definition init_fuel (ini : c_init) : nat :=
  (2 * init_fuel_aux ini + 256)%nat.

Definition init_leaves (ty : c_type) (ini : c_init) (env : c_type_env)
  (whole : bool) (loc : c_loc) : c_tr (list init_leaf) :=
  match object_init_f (init_fuel ini) (STType ty) 0 ini env whole loc [] with
  | TErr err => TErr err
  | TOk rev_lvs => TOk (rev rev_lvs)
  end.

Definition complete_array (ty0 : c_type) (oini : option c_init) (loc : c_loc)
  (env : c_type_env) (whole : bool) : c_tr c_type :=
  match ty0, oini with
  | TArray elem ALNone, None => TOk (TArray elem ALNone)
  | TArray elem ALNone, Some ini =>
      match str_elems ini elem with
      | Some vs => TOk (TArray elem (ALConst (Z.of_nat (length vs) + 1)))
      | None =>
          match ini with
          | InitList es0 =>
              let es := map of_c_entry es0 in
              match slots_f (init_fuel ini) (TArray elem ALNone) 0 0 es 0 env whole loc [] with
              | TErr err => TErr err
              | TOk (_, max_n, _) => TOk (TArray elem (ALConst max_n))
              end
          | InitExpr _ => sema_err loc "array of unknown size"
          end
      end
  | _, _ => TOk ty0
  end.

(** ## Static initializers, address constants, and global declarations

    Static initializers turn initializer leaves into non-overlapping IR data
    chunks (`item/2` and `zero/1`), merging bit-fields byte by byte and
    evaluating C11 address constants with string and compound literal creation. *)

Inductive addr_const : Type :=
| ACSym (sym : string) (off : Z)
| ACInt (addr : Z)
| ACNull.

Definition g_link_term (l : g_linkage) (ro : bool) : term :=
  match l with
  | GLTls s => TApp "tls" [TAtom s]
  | GLNormal s => if ro then TApp "ro" [TAtom s] else TAtom s
  end.

Definition define_global_g (sym : string) (ty : c_type) (lnk : g_linkage)
  (oini : option c_init) (loc : c_loc) (lg0 : c_lower_globals)
  : c_tr c_lower_globals :=
  match smap_find sym (lg_gdefs lg0) with
  | Some gd =>
      match gd_init gd with
      | Some _ =>
          match oini with
          | None => TOk lg0
          | Some _ => sema_err loc (sym ++ " is initialized twice")
          end
      | None =>
          TOk (mkCLowerGlobals
                 (smap_add sym (mkGDef ty lnk oini loc) (lg_gdefs lg0))
                 (lg_gdef_syms lg0) (lg_lits lg0) (lg_lit_syms lg0)
                 (lg_lit_of lg0) (lg_func_names lg0) (lg_deferred lg0)
                 (lg_inline_copy lg0) (lg_inline_copy_of lg0)
                 (lg_inline_attr lg0) (lg_readonly lg0) (lg_galign lg0)
                 (lg_qsym lg0) (lg_initialized lg0) (lg_inits lg0))
      end
  | None =>
      TOk (mkCLowerGlobals
             (smap_add sym (mkGDef ty lnk oini loc) (lg_gdefs lg0))
             (sym :: lg_gdef_syms lg0) (lg_lits lg0) (lg_lit_syms lg0)
             (lg_lit_of lg0) (lg_func_names lg0) (lg_deferred lg0)
             (lg_inline_copy lg0) (lg_inline_copy_of lg0)
             (lg_inline_attr lg0) (lg_readonly lg0) (lg_galign lg0)
             (lg_qsym lg0) (lg_initialized lg0) (lg_inits lg0))
  end.

Definition mark_readonly_g (sym : string) (lg0 : c_lower_globals) : c_lower_globals :=
  mkCLowerGlobals (lg_gdefs lg0) (lg_gdef_syms lg0) (lg_lits lg0) (lg_lit_syms lg0)
                  (lg_lit_of lg0) (lg_func_names lg0) (lg_deferred lg0)
                  (lg_inline_copy lg0) (lg_inline_copy_of lg0)
                  (lg_inline_attr lg0) (smap_add sym true (lg_readonly lg0))
                  (lg_galign lg0) (lg_qsym lg0) (lg_initialized lg0) (lg_inits lg0).

Definition new_complit_g (tn : c_type_name) (ty0 : c_type) (ini : c_init)
  (loc : c_loc) (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (string * c_type_env * c_lower_globals) :=
  let '(n, env1) := next_env_id env0 in
  let sym := "complit." ++ decimal n in
  match complete_array ty0 (Some ini) loc env0 false with
  | TErr err => TErr err
  | TOk ty =>
      match define_global_g sym ty (GLNormal "local") (Some ini) loc lg0 with
      | TErr err => TErr err
      | TOk lg1 =>
          let rt := reflect_type tn ty0 env0 in
          let lg2 := if readonly_object_type rt then mark_readonly_g sym lg1 else lg1 in
          TOk (sym, env1, lg2)
      end
  end.

Definition offset_const (op : c_binop) (r0 : addr_const) (elem : c_type) (k : Z)
  (env : c_type_env) (loc : c_loc) : c_tr addr_const :=
  match r0 with
  | ACSym sym off0 =>
      match arith_size elem env with
      | TErr (TEBad why) =>
          sema_err loc ("pointer arithmetic on " ++ c_type_diag_str elem ++ " (" ++ why ++ ")")
      | TErr err => TErr err
      | TOk sz =>
          let off := match op with BAdd => off0 + k * sz | _ => off0 - k * sz end in
          TOk (ACSym sym off)
      end
  | _ => sema_err loc "initializer is not an address constant"
  end.

Fixpoint address_constant_f (fuel : nat) (xv : c_typed_node) (loc : c_loc)
  (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (addr_const * c_type_env * c_lower_globals) :=
  match fuel with
  | O => sema_err loc "address_constant recursion limit"
  | S f =>
      match constant_address xv env0 with
      | Some a =>
          let u := z_mod_pow2 a 64 in
          TOk (if Z.eqb u 0 then ACNull else ACInt u, env0, lg0)
      | None =>
          match xv with
          | TNode CatVal _ (TFDecay x) | TNode CatVal _ (TFAddr x) =>
              place_constant_f f x loc env0 lg0
          | TNode CatVal _ (TFCast tn inner) =>
              match type_name_type tn env0 with
              | TErr err => TErr err
              | TOk (ty, _) =>
                  match check_supported ty loc with
                  | Some msg => TErr (TESema msg)
                  | None =>
                      if vm_type ty then
                        sema_err loc "a variably modified type in a constant initializer"
                      else
                        match ty with
                        | TPtr _ =>
                            if int_type (lowered_node_type inner) then
                              match folded inner env0 with
                              | TOk (Some (CVInt n)) =>
                                  let u := z_mod_pow2 n 64 in
                                  TOk (if Z.eqb u 0 then ACNull else ACInt u, env0, lg0)
                              | _ => address_constant_f f inner loc env0 lg0
                              end
                            else address_constant_f f inner loc env0 lg0
                        | _ =>
                            if int_type ty && is_ptr_type (lowered_node_type inner) then
                              match type_size_align ty env0 with
                              | TOk (8, _) => address_constant_f f inner loc env0 lg0
                              | _ => sema_err loc "initializer is not a constant"
                              end
                            else sema_err loc "initializer is not a constant"
                        end
                  end
              end
          | TNode CatVal (TPtr _) (TFCond xc xa xb) =>
              if int_type (lowered_node_type xc) then
                match folded xc env0 with
                | TOk (Some (CVInt c)) =>
                    if negb (Z.eqb c 0) then address_constant_f f xa loc env0 lg0
                    else address_constant_f f xb loc env0 lg0
                | _ => sema_err loc "initializer is not an address constant"
                end
              else sema_err loc "initializer is not an address constant"
          | TNode CatVal (TPtr _) (TFBin op xa xb) =>
              let is_add_sub := match op with BAdd | BSub => true | _ => false end in
              if is_add_sub then
                let ta := lowered_node_type xa in
                let tb := lowered_node_type xb in
                let pair_opt :=
                  match ta with
                  | TPtr elem => Some (elem, xa, xb)
                  | _ =>
                      match tb with
                      | TPtr elem => Some (elem, xb, xa)
                      | _ => None
                      end
                  end in
                match pair_opt with
                | Some (elem, xp, xk) =>
                    match folded xk env0 with
                    | TOk (Some (CVInt k)) =>
                        match address_constant_f f xp loc env0 lg0 with
                        | TErr err => TErr err
                        | TOk (r0, env1, lg1) =>
                            match offset_const op r0 elem k env1 loc with
                            | TErr err => TErr err
                            | TOk r => TOk (r, env1, lg1)
                            end
                        end
                    | _ => sema_err loc "initializer is not an address constant"
                    end
                | None => sema_err loc "initializer is not an address constant"
                end
              else sema_err loc "initializer is not an address constant"
          | _ =>
              if int_type (lowered_node_type xv) then
                match folded xv env0 with
                | TOk (Some (CVInt 0)) => TOk (ACNull, env0, lg0)
                | _ => sema_err loc "initializer is not an address constant"
                end
              else sema_err loc "initializer is not an address constant"
          end
      end
  end

with place_constant_f (fuel : nat) (x : c_typed_node) (loc : c_loc)
  (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (addr_const * c_type_env * c_lower_globals) :=
  match fuel with
  | O => sema_err loc "place_constant recursion limit"
  | S f =>
      match x with
      | TNode CatObj _ (TFId name) =>
          match lookup_ordinary env0 name with
          | Some (BGVar _ sym _ tls) =>
              if tls then
                sema_err loc ("the address of thread-local " ++ name ++ " is not a constant")
              else TOk (ACSym sym 0, env0, lg0)
          | _ => sema_err loc (name ++ " is not a global")
          end
      | TNode CatFun _ (TFId name) =>
          match lookup_ordinary env0 name with
          | Some (BFn _ sym _) => TOk (ACSym sym 0, env0, lg0)
          | _ => sema_err loc "initializer is not an address constant"
          end
      | TNode CatObj _ (TFStr bs) =>
          let '(sym, env1, lg1) := new_literal_g (LitBytes bs) env0 lg0 in
          TOk (ACSym sym 0, env1, lg1)
      | TNode CatObj _ (TFPredefined name) =>
          match sc_enclosing_fn (te_scope env0) with
          | Some fn =>
              let '(sym, env1, lg1) := func_literal_g fn env0 lg0 in
              TOk (ACSym sym 0, env1, lg1)
          | None => sema_err loc (name ++ " outside a function")
          end
      | TNode CatObj _ (TFWStr wt vs) =>
          let '(sym, env1, lg1) := new_literal_g (LitWide (wide_type_to_c_type wt) vs) env0 lg0 in
          TOk (ACSym sym 0, env1, lg1)
      | TNode CatObj _ (TFComplit tn es) =>
          match type_name_type tn env0 with
          | TErr err => TErr err
          | TOk (ty0, _) =>
              match check_supported ty0 loc with
              | Some msg => TErr (TESema msg)
              | None =>
                  if vm_type ty0 then
                    sema_err loc "a variably modified type in a constant initializer"
                  else
                    match new_complit_g tn ty0 (InitList es) loc env0 lg0 with
                    | TErr err => TErr err
                    | TOk (sym, env1, lg1) => TOk (ACSym sym 0, env1, lg1)
                    end
              end
          end
      | TNode CatObj _ (TFDeref xv) =>
          match address_constant_f f xv loc env0 lg0 with
          | TErr err => TErr err
          | TOk (ACSym sym off, env1, lg1) => TOk (ACSym sym off, env1, lg1)
          | TOk _ => sema_err loc "initializer is not an address constant"
          end
      | TNode CatObj _ (TFMember (TNode CatObj t_sub f_sub) fld) =>
          match place_constant_f f (TNode CatObj t_sub f_sub) loc env0 lg0 with
          | TErr err => TErr err
          | TOk (ACSym sym off0, env1, lg1) =>
              let su_t := unqualified t_sub in
              if is_su su_t then
                match member_type_offset su_t fld env1 with
                | Some (_, moff) => TOk (ACSym sym (off0 + moff), env1, lg1)
                | None => sema_err loc ("no member named " ++ fld)
                end
              else sema_err loc ("no member named " ++ fld)
          | TOk _ => sema_err loc "initializer is not an address constant"
          end
      | _ => sema_err loc "initializer is not an address constant"
      end
  end.

Record data_chunk : Type := mkDataChunk {
  dc_off : Z;
  dc_bytes : Z;
  dc_item : term;
  dc_str_bytes : option (list Z);
}.

Definition int_chunk (off : Z) (ty : c_type) (v : Z) : option data_chunk :=
  match int_info ty, convert_int v ty with
  | Some (n, _), Some u =>
      let w :=
        if Z.eqb n 1 then "b"
        else if Z.eqb n 2 then "h"
        else if Z.eqb n 4 then "w"
        else "l" in
      Some (mkDataChunk off n (ir_item w (ir_const u)) None)
  | _, _ => None
  end.

Fixpoint le_bytes_acc (k : nat) (u : Z) (acc : list Z) : list Z :=
  match k with
  | O => acc
  | S k' => le_bytes_acc k' (Z.shiftr u 8) (Z.land u 255 :: acc)
  end.

Definition vals_bytes (vs : list Z) (ty : c_type) (sz : Z) : list Z :=
  let k := Z.to_nat sz in
  rev (fold_left
         (fun acc v =>
            let u := match convert_int v ty with Some x => x | None => 0 end in
            le_bytes_acc k u acc)
         vs []).

Definition split_strs_zm (cm0 : zmap data_chunk) : zmap data_chunk :=
  fold_left
    (fun cm ch =>
       match dc_str_bytes ch with
       | Some bs =>
           snd (fold_left
                  (fun st b =>
                     let '(o, m) := st in
                     (o + 1, zm_add o (mkDataChunk o 1 (ir_item "b" (ir_const b)) None) m))
                  bs (dc_off ch, cm))
       | None => cm
       end)
    (zm_values_acc cm0 []) cm0.

Definition drop_chunks_zm (lo hi : Z) (cm0 : zmap data_chunk) : zmap data_chunk :=
  let offs :=
    if hi - lo <=? 64 then numlist_Z lo (hi - 1)
    else filter (fun o => (lo <=? o) && (o <? hi)) (zm_keys_acc cm0 []) in
  fold_left (fun cm o => zm_del o cm) offs cm0.

Definition bitfield_byte_zm (start w v : Z) (cm0 : zmap data_chunk) (byte_off : Z)
  : zmap data_chunk :=
  let old :=
    match zm_find byte_off cm0 with
    | Some ch =>
        if Z.eqb (dc_bytes ch) 1 then
          match dc_item ch with
          | TApp f [TAtom w_s; TApp cf [Term.TInt n]] =>
              if (f == "item") && (w_s == "b") && (cf == "const") then n else 0
          | _ => 0
          end
        else 0
    | None => 0
    end in
  let sh := start - 8 * byte_off in
  let mask := Z.land (Z.shiftr (Z.shiftl (Z.shiftl 1 w - 1) (sh + 64)) 64) 255 in
  let bits := Z.land (Z.shiftr (Z.shiftl (Z.land v (Z.shiftl 1 w - 1)) (sh + 64)) 64) 255 in
  let nw := Z.lor (Z.land old (z_not_mask mask 8)) bits in
  zm_add byte_off (mkDataChunk byte_off 1 (ir_item "b" (ir_const nw)) None) cm0.

Definition expr_chunk (ty : c_type) (off : Z) (e : c_expr) (loc : c_loc)
  (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (data_chunk * c_type_env * c_lower_globals) :=
  if arithmetic_type ty then
    match constant_value e env0 with
    | TOk (v0, from_t) =>
        match const_convert (CVInt v0) from_t ty with
        | Some (CVInt v) =>
            if float_type ty then
              match type_class ty with
              | Some k =>
                  TOk (mkDataChunk off (ir_width_bytes k) (ir_item k (ir_const v)) None, env0, lg0)
              | None => sema_err loc "initializer is not a constant"
              end
            else
              match int_chunk off ty v with
              | Some ch => TOk (ch, env0, lg0)
              | None => sema_err loc "initializer is not a constant"
              end
        | _ => sema_err loc "initializer is not a constant"
        end
    | TErr _ => sema_err loc "initializer is not a constant"
    end
  else
    match ty with
    | TPtr _ =>
        match elaborate_loc e env0 loc with
        | TErr err => TErr err
        | TOk None => sema_err loc "initializer is not a constant"
        | TOk (Some x) =>
            match address_constant_f 128 (value_node x) loc env0 lg0 with
            | TErr err => TErr err
            | TOk (r, env1, lg1) =>
                let misaligned := negb (Z.eqb (Z.modulo off 8) 0) in
                let bad_ptr :=
                  misaligned &&
                  match r with
                  | ACSym _ _ => true
                  | ACInt n0 => negb (Z.eqb n0 0)
                  | ACNull => false
                  end in
                if bad_ptr then
                  sema_err loc "Fil-C cannot initialize this object: a pointer in its initializer is not word-aligned"
                else
                  let ch :=
                    match r with
                    | ACSym sym soff => mkDataChunk off 8 (ir_item "p" (ir_sym sym soff)) None
                    | ACInt n => mkDataChunk off 8 (ir_item "l" (ir_const n)) None
                    | ACNull => mkDataChunk off 8 (ir_item "l" (ir_const 0)) None
                    end in
                  TOk (ch, env1, lg1)
            end
        end
    | _ => sema_err loc ("cannot statically initialize a " ++ c_type_diag_str ty)
    end.

Definition leaf_off (lf : init_leaf) : Z :=
  match lf with
  | ILZero o _ | ILVal o _ _ | ILVals o _ _ | ILExpr o _ _ | ILBits o _ _ _ _ => o
  end.

Definition static_leaf_step (loc : c_loc)
  (st : c_type_env * c_lower_globals * zmap data_chunk * Z * bool)
  (lf : init_leaf)
  : c_tr (c_type_env * c_lower_globals * zmap data_chunk * Z * bool) :=
  let '(env0, lg0, cm0, end0, str0) := st in
  let off := leaf_off lf in
  let '(cm1, str1) :=
    if str0 && (off <? end0) then (split_strs_zm cm0, false) else (cm0, str0) in
  let res :=
    match lf with
    | ILZero o ty =>
        if end0 <=? o then TOk (env0, lg0, cm1, end0)
        else
          match type_size_align ty env0 with
          | TErr err => TErr err
          | TOk (sz, _) => TOk (env0, lg0, drop_chunks_zm o (o + sz) cm1, end0)
          end
    | ILVals _ _ [] => TOk (env0, lg0, cm1, end0)
    | ILVals o ty vs =>
        match int_info ty with
        | Some (sz, _) =>
            let bs := vals_bytes vs ty sz in
            let n := Z.of_nat (length bs) in
            let ch := mkDataChunk o n (ir_item "b" (ir_str bs)) (Some bs) in
            TOk (env0, lg0, zm_add o ch cm1, Z.max end0 (o + n))
        | None => sema_err loc "invalid vals leaf"
        end
    | ILVal o ty v =>
        match int_chunk o ty v with
        | Some ch => TOk (env0, lg0, zm_add o ch cm1, Z.max end0 (o + dc_bytes ch))
        | None => sema_err loc "invalid val leaf"
        end
    | ILExpr o ty e =>
        match expr_chunk ty o e loc env0 lg0 with
        | TErr err => TErr err
        | TOk (ch, env1, lg1) =>
            TOk (env1, lg1, zm_add o ch cm1, Z.max end0 (o + dc_bytes ch))
        end
    | ILBits o ty pos w e =>
        match constant_value e env0 with
        | TOk (v0, from_t) =>
            match const_convert (CVInt v0) from_t ty with
            | Some (CVInt v) =>
                let start := 8 * o + pos in
                let first := Z.div start 8 in
                let last := Z.div (start + w - 1) 8 in
                let cm2 := fold_left (bitfield_byte_zm start w v) (numlist_Z first last) cm1 in
                TOk (env0, lg0, cm2, Z.max end0 (last + 1))
            | _ => sema_err loc "initializer is not a constant"
            end
        | TErr _ => sema_err loc "initializer is not a constant"
        end
    end in
  match res with
  | TErr err => TErr err
  | TOk (env1, lg1, cm2, end1) =>
      let is_val_or_expr := match lf with ILVal _ _ _ | ILExpr _ _ _ => true | _ => false end in
      let cm3 :=
        if (off <? end0) && is_val_or_expr then
          match zm_find off cm2 with
          | Some ch =>
              if 1 <? dc_bytes ch then drop_chunks_zm (off + 1) (off + dc_bytes ch) cm2
              else cm2
          | None => cm2
          end
        else cm2 in
      let str2 := match lf with ILVals _ _ _ => true | _ => str1 end in
      TOk (env1, lg1, cm3, end1, str2)
  end.

Fixpoint fill_items_aux (chs : list data_chunk) (pos sz : Z) (loc : c_loc)
  (acc : list term) : c_tr (list term) :=
  match chs with
  | [] =>
      let acc1 := if pos <? sz then ir_zero (sz - pos) :: acc else acc in
      TOk (rev acc1)
  | ch :: rest =>
      let o := dc_off ch in
      if o <? pos then sema_err loc "overlapping initializers"
      else
        let acc1 := if pos <? o then ir_zero (o - pos) :: acc else acc in
        fill_items_aux rest (o + dc_bytes ch) sz loc (dc_item ch :: acc1)
  end.

Definition static_items (ty : c_type) (oini : option c_init) (loc : c_loc)
  (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (list term * c_type_env * c_lower_globals) :=
  match type_size_align ty env0 with
  | TErr err => TErr err
  | TOk (sz, _) =>
      let lvs_res :=
        match oini with
        | None => TOk []
        | Some ini => init_leaves ty ini env0 false loc
        end in
      match lvs_res with
      | TErr err => TErr err
      | TOk lvs =>
          let fix go (xs : list init_leaf)
            (st : c_type_env * c_lower_globals * zmap data_chunk * Z * bool) :=
            match xs with
            | [] => TOk st
            | lf :: rest =>
                match static_leaf_step loc st lf with
                | TErr err => TErr err
                | TOk st1 => go rest st1
                end
            end in
          match go lvs (env0, lg0, ZMLeaf, 0, false) with
          | TErr err => TErr err
          | TOk (env1, lg1, cm, _, _) =>
              match fill_items_aux (zm_values_acc cm []) 0 sz loc [] with
              | TErr err => TErr err
              | TOk items => TOk (items, env1, lg1)
              end
          end
      end
  end.

(** ## Global declarations and module-level data emission

    Global declarations resolve asm labels, check redeclaration compatibility,
    record alignments and constness, and collect global data, merged string
    literals, and constructor/destructor entries in Prolog's canonical order. *)

Definition declared_symbol (name : string) (oasm : option string) (env : c_type_env)
  : string :=
  match oasm with
  | Some sym => sym
  | None =>
      if (name == "zmemmove_union") || (name == "zmemmove_builtin")
         || (name == "zmemmove_builtin_volatile") then "zmemmove"
      else
        match lookup_ordinary env name with
        | Some (BFn _ sym _) => sym
        | Some (BGVar _ sym lnk _) => if lnk == "static" then name else sym
        | _ => name
        end
  end.

Definition prior_storage (name : string) (stg0 : c_storage) (env : c_type_env) : c_storage :=
  match stg0 with
  | StStatic => StStatic
  | _ =>
      match lookup_ordinary env name with
      | Some (BFn _ _ lnk) => if lnk == "local" then StStatic else stg0
      | _ => stg0
      end
  end.

Definition qsym_key (name sym : string) : string :=
  name ++ string_of_rev [byte 0] ++ sym.

Definition same_enum_redeclared (name sym : string) (env : c_type_env)
  (lg : c_lower_globals) : bool :=
  match lookup_qtype env name, smap_find (qsym_key name sym) (lg_qsym lg) with
  | Some qt, Some pqt =>
      match composite_type pqt qt (Some env) with Some _ => true | None => false end
  | _, _ => false
  end.

Definition redeclared (loc : c_loc) (name sym : string) (ty0 : c_type)
  (env : c_type_env) (lg : c_lower_globals) : c_tr c_type :=
  let prev_opt :=
    match lookup_ordinary env name with
    | Some (BFn pt ps _) => if ps == sym then Some pt else None
    | Some (BGVar pt ps _ _) => if ps == sym then Some pt else None
    | _ => None
    end in
  match prev_opt with
  | None => TOk ty0
  | Some pt =>
      let k0 := is_func_type pt in
      let k1 := is_func_type ty0 in
      if negb (Bool.eqb k0 k1) then
        sema_err loc ("redefinition of '" ++ name ++ "' as different kind of symbol")
      else
        match composite_type pt ty0 (Some env) with
        | Some comp => TOk comp
        | None =>
            if same_enum_redeclared name sym env lg then TOk ty0
            else if k1 then sema_err loc ("conflicting types for '" ++ name ++ "'")
            else sema_err loc ("redeclaration of '" ++ name ++ "' with a different type")
        end
  end.

Definition qualified_redeclared (loc : c_loc) (name sym : string) (ty : c_type)
  (env : c_type_env) (lg0 : c_lower_globals) : c_tr c_lower_globals :=
  match lookup_qtype env name with
  | None => TOk lg0
  | Some qt =>
      let key := qsym_key name sym in
      let c_res :=
        match smap_find key (lg_qsym lg0) with
        | Some pqt =>
            match composite_type pqt qt (Some env) with
            | Some c => TOk c
            | None =>
                if is_func_type ty then sema_err loc ("conflicting types for '" ++ name ++ "'")
                else sema_err loc ("redeclaration of '" ++ name ++ "' with a different type")
            end
        | None => TOk qt
        end in
      match c_res with
      | TErr err => TErr err
      | TOk c =>
          TOk (mkCLowerGlobals (lg_gdefs lg0) (lg_gdef_syms lg0) (lg_lits lg0) (lg_lit_syms lg0)
                 (lg_lit_of lg0) (lg_func_names lg0) (lg_deferred lg0)
                 (lg_inline_copy lg0) (lg_inline_copy_of lg0) (lg_inline_attr lg0)
                 (lg_readonly lg0) (lg_galign lg0) (smap_add key c (lg_qsym lg0))
                 (lg_initialized lg0) (lg_inits lg0))
      end
  end.

Definition storage_link_str (s : c_storage) : string :=
  match s with
  | StStatic => "static"
  | StExtern => "extern"
  | _ => "none"
  end.

Definition readonly_global_g (tls : bool) (name sym : string) (env : c_type_env)
  (lg0 : c_lower_globals) : c_lower_globals :=
  if tls then lg0
  else
    match lookup_qtype env name with
    | Some rt => if readonly_object_type rt then mark_readonly_g sym lg0 else lg0
    | None => lg0
    end.

Definition data_alignment_g (name sym : string) (env : c_type_env)
  (lg0 : c_lower_globals) : c_lower_globals :=
  match lookup_qalign env name with
  | Some (Some a) =>
      let a1 := match smap_find sym (lg_galign lg0) with Some a0 => Z.max a a0 | None => a end in
      mkCLowerGlobals (lg_gdefs lg0) (lg_gdef_syms lg0) (lg_lits lg0) (lg_lit_syms lg0)
                      (lg_lit_of lg0) (lg_func_names lg0) (lg_deferred lg0)
                      (lg_inline_copy lg0) (lg_inline_copy_of lg0) (lg_inline_attr lg0)
                      (lg_readonly lg0) (smap_add sym a1 (lg_galign lg0)) (lg_qsym lg0)
                      (lg_initialized lg0) (lg_inits lg0)
  | _ => lg0
  end.

Definition global_decl_g (loc : c_loc) (d : c_decl) (env0 : c_type_env)
  (lg0 : c_lower_globals) : c_tr (c_type_env * c_lower_globals) :=
  let name := cd_name d in
  let ty1 := cd_type d in
  let stg0 := cd_storage d in
  let oasm := cd_asm d in
  let oini := cd_init d in
  let sym := declared_symbol name oasm env0 in
  match redeclared loc name sym ty1 env0 lg0 with
  | TErr err => TErr err
  | TOk ty0 =>
      match qualified_redeclared loc name sym ty0 env0 lg0 with
      | TErr err => TErr err
      | TOk lg1 =>
          let '(stg, tls) :=
            match stg0 with
            | StThreadLocal inner => (inner, true)
            | _ => (stg0, false)
            end in
          match ty0 with
          | TFunc _ _ _ =>
              if tls then sema_err loc ("function " ++ name ++ " cannot be _Thread_local")
              else
                let stg1 := prior_storage name stg env0 in
                let lnk := match stg1 with StStatic => "local" | _ => "export" end in
                match oini with
                | Some _ => sema_err loc ("function " ++ name ++ " has an initializer")
                | None => TOk (bind_ordinary name (BFn ty0 sym lnk) env0, lg1)
                end
          | _ =>
              match check_supported ty0 loc with
              | Some msg => TErr (TESema msg)
              | None =>
                  if vm_type ty0 then
                    sema_err loc (name ++ " has a variably modified type at file scope or with linkage")
                  else
                    match complete_array ty0 oini loc env0 false with
                    | TErr err => TErr err
                    | TOk ty =>
                        let env1 :=
                          bind_ordinary name (BGVar ty sym (storage_link_str stg) tls) env0 in
                        match stg, oini with
                        | StExtern, None => TOk (env1, lg1)
                        | _, _ =>
                            let lnk0 := match stg with StStatic => "local" | _ => "export" end in
                            let lnk := if tls then GLTls lnk0 else GLNormal lnk0 in
                            match define_global_g sym ty lnk oini loc lg1 with
                            | TErr err => TErr err
                            | TOk lg2 =>
                                let lg3 := readonly_global_g tls name sym env1 lg2 in
                                let lg4 := data_alignment_g name sym env1 lg3 in
                                TOk (env1, lg4)
                            end
                        end
                    end
              end
          end
      end
  end.

Definition sort_strings_unique (xs : list string) : list string :=
  let sorted := msort atom_compare xs in
  let fix dedup (l : list string) : list string :=
    match l with
    | [] => []
    | x :: rest =>
        match rest with
        | [] => [x]
        | y :: _ => if x == y then dedup rest else x :: dedup rest
        end
    end in
  dedup sorted.

Definition global_item_g (opts : c_lower_opts) (sym : string) (gd : gdef_entry)
  (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (term * c_type_env * c_lower_globals) :=
  let lnk0 :=
    match gd_linkage gd, gd_init gd with
    | GLNormal s, None =>
        if (s == "export") && lo_common opts then GLNormal "weak" else GLNormal s
    | l, _ => l
    end in
  let ro :=
    match smap_find sym (lg_readonly lg0), lnk0 with
    | Some true, GLNormal s => (s == "export") || (s == "local") || (s == "weak")
    | _, _ => false
    end in
  let lnk_t := g_link_term lnk0 ro in
  match type_size_align (gd_type gd) env0 with
  | TErr (TEBad why) =>
      sema_err (gd_loc gd) (sym ++ " has an unsupported type (" ++ why ++ ")")
  | TErr err => TErr err
  | TOk (_, al0) =>
      let req := match smap_find sym (lg_galign lg0) with Some a => a | None => 1 end in
      let al := Z.max al0 req in
      match smap_find sym (lg_initialized lg0) with
      | Some items => TOk (ir_data sym lnk_t al items, env0, lg0)
      | None =>
          match static_items (gd_type gd) (gd_init gd) (gd_loc gd) env0 lg0 with
          | TErr err => TErr err
          | TOk (items, env1, lg1) => TOk (ir_data sym lnk_t al items, env1, lg1)
          end
      end
  end.

Fixpoint global_items_loop (fuel : nat) (opts : c_lower_opts) (done : smap bool)
  (env0 : c_type_env) (lg0 : c_lower_globals) (acc : list term)
  : c_tr (list term * c_type_env * c_lower_globals) :=
  match fuel with
  | O => TOk (rev acc, env0, lg0)
  | S f =>
      let syms :=
        filter (fun s => match smap_find s done with Some true => false | _ => true end)
               (sort_strings_unique (lg_gdef_syms lg0)) in
      match syms with
      | [] => TOk (rev acc, env0, lg0)
      | _ =>
          let fix emit_batch (ss : list string) (e : c_type_env) (g : c_lower_globals)
            (a : list term) :=
            match ss with
            | [] => TOk (a, e, g)
            | s :: rest =>
                match smap_find s (lg_gdefs g) with
                | None => emit_batch rest e g a
                | Some gd =>
                    match global_item_g opts s gd e g with
                    | TErr err => TErr err
                    | TOk (ditem, e1, g1) => emit_batch rest e1 g1 (ditem :: a)
                    end
                end
            end in
          match emit_batch syms env0 lg0 acc with
          | TErr err => TErr err
          | TOk (acc1, env1, lg1) =>
              let done1 := fold_left (fun m s => smap_add s true m) syms done in
              global_items_loop f opts done1 env1 lg1 acc1
          end
      end
  end.

Definition literal_data_item (sym : string) (lit : lit_entry) : term :=
  let '(al, w, vs0) :=
    match lit with
    | LitBytes bs => (1, "b", bs)
    | LitWide wt vs =>
        match int_info wt with
        | Some (2, _) => (2, "h", vs)
        | Some (4, _) => (4, "w", vs)
        | _ => (4, "w", vs)
        end
    end in
  let items := map (fun v => ir_item w (ir_const v)) (app vs0 [0]) in
  ir_data sym (TApp "ro" [TAtom "local"]) al items.

Definition global_data_g (opts : c_lower_opts) (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (list term * c_type_env * c_lower_globals) :=
  match global_items_loop 64 opts smap_empty env0 lg0 [] with
  | TErr err => TErr err
  | TOk (gdata, env1, lg1) =>
      let lit_syms := sort_strings_unique (lg_lit_syms lg1) in
      let ldata :=
        flat_map (fun s => match smap_find s (lg_lits lg1) with
                           | Some lit => [literal_data_item s lit]
                           | None => []
                           end) lit_syms in
      let sorted_inits :=
        msort (fun a b => Z.compare (ie_order a) (ie_order b)) (lg_inits lg1) in
      let idata :=
        map (fun ie =>
               let nm := "__nanofil_" ++ ie_kind ie ++ "_" ++ ie_sym ie in
               let pr := match ie_prio ie with Some p => Term.TInt p | None => TAtom "none" end in
               ir_data nm (TApp "init" [TAtom (ie_kind ie); pr]) 8
                       [ir_item "p" (ir_sym (ie_sym ie) 0)])
            sorted_inits in
      TOk (app gdata (app ldata idata), env1, lg1)
  end.
