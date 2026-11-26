(** This module lowers a parsed C translation unit into unchecked Nanofil IR
    and source provenance records in pure Gallina.

    It ports the statement, expression, function, and translation-unit lowering
    of nanofil/src/c_lower.pl, connecting [CTypes], [CLowerState],
    [CLowerInit], [CLowerAsm], [CLowerBuiltins], and [CLaunder] into one pure,
    zero-axiom compiler pass [c_module_opts]. The pass produces ground IR
    clauses and [context/2] provenance records while returning the completed
    type environment for [CLayouts]. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Nanofil Require Import Term Maps.
From Backend Require Import Text Order.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp
  CTypeAst CTypeTables CTypes CLaunder CLowerState CLowerInit CLowerAsm CLowerBuiltins.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Notation "a == b" := (String.eqb a b) (at level 70, no associativity).

(** ## Attribute inspection helpers

    GNU attributes on declarations and function definitions govern linkage,
    weak aliases, weakrefs, constructors/destructors, inline rules, cleanup
    handlers, and Clang overloadable wrappers. *)

Definition attr_entries_of (ts : list attr_tok) : list (string * list attr_tok) :=
  flat_map
    (fun t =>
       match t with
       | AGroup inner =>
           flat_map
             (fun item =>
                match item with
                | ATok (TId w) :: rest => [(w, rest)]
                | ATok (TKw w) :: rest => [(w, rest)]
                | _ => []
                end)
             (attribute_items inner)
       | ATok _ => []
       end)
    ts.

Definition spec_attr_entries (specs : list c_spec) : list (string * list attr_tok) :=
  flat_map (fun sp => match sp with SpAttr ts => attr_entries_of ts | _ => [] end) specs.

Definition has_attr_word (ws : list string) (specs : list c_spec) : bool :=
  existsb (fun p => str_mem (fst p) ws) (spec_attr_entries specs).

Definition weak_attr (specs : list c_spec) : bool :=
  has_attr_word ["weak"; "__weak__"] specs.

Definition common_attr (specs : list c_spec) : bool :=
  has_attr_word ["common"; "__common__"] specs.

Definition always_inline_attr (specs : list c_spec) : bool :=
  has_attr_word ["always_inline"; "__always_inline__"] specs.

Definition noinline_attr (specs : list c_spec) : bool :=
  has_attr_word ["noinline"; "__noinline__"] specs.

Definition overloadable_attr (specs : list c_spec) : bool :=
  has_attr_word ["overloadable"; "__overloadable__"] specs.

Definition gnu_inline_rule (opts : c_lower_opts) (specs : list c_spec) : bool :=
  lo_gnu89 opts || has_attr_word ["gnu_inline"; "__gnu_inline__"] specs.

Definition alias_attr_spec (sp : c_spec) : bool :=
  match sp with
  | SpAttr ts => existsb (fun p => (fst p == "alias") || (fst p == "__alias__")) (attr_entries_of ts)
  | _ => false
  end.

Definition alias_target (specs : list c_spec) : option string :=
  let fix go (es : list (string * list attr_tok)) : option string :=
    match es with
    | [] => None
    | (w, rest) :: tl =>
        if (w == "alias") || (w == "__alias__") then
          match rest with
          | AGroup [ATok (TStr bs)] :: _ => Some (bytes_to_string bs)
          | _ => go tl
          end
        else go tl
    end in
  go (spec_attr_entries specs).

Definition weakref_target (specs : list c_spec) : option string :=
  let fix go (es : list (string * list attr_tok)) : option string :=
    match es with
    | [] => None
    | (w, rest) :: tl =>
        if (w == "weakref") || (w == "__weakref__") then
          match rest with
          | AGroup [ATok (TStr bs)] :: _ => Some (bytes_to_string bs)
          | _ => alias_target specs
          end
        else go tl
    end in
  go (spec_attr_entries specs).

Definition weakref_spec (sp : c_spec) : bool :=
  match sp with
  | SpStorage s => s == "static"
  | SpAttr ts =>
      existsb (fun p => str_mem (fst p) ["weakref"; "__weakref__"; "alias"; "__alias__"])
              (attr_entries_of ts)
  | _ => false
  end.

Definition cleanup_attr (specs : list c_spec) : c_tr (option string) :=
  let fix go (es : list (string * list attr_tok)) : c_tr (option string) :=
    match es with
    | [] => TOk None
    | (w, rest) :: tl =>
        if (w == "cleanup") || (w == "__cleanup__") then
          match rest with
          | AGroup [ATok (TId fn)] :: _ => TOk (Some fn)
          | AGroup _ :: _ => TErr (TESema "the cleanup attribute takes one function name")
          | _ => go tl
          end
        else go tl
    end in
  go (spec_attr_entries specs).

Definition init_attrs (specs : list c_spec) : list (string * option (option Z)) :=
  flat_map
    (fun p =>
       let '(w, rest) := p in
       let okind :=
         if (w == "constructor") || (w == "__constructor__") then Some "ctor"
         else if (w == "destructor") || (w == "__destructor__") then Some "dtor"
         else None in
       match okind with
       | None => []
       | Some k =>
           match rest with
           | AGroup arg :: _ =>
               match arg with
               | [ATok (CAst.TInt pr _ _)] =>
                   if (0 <=? pr) && (pr <=? 65535) then [(k, Some (Some pr))]
                   else [(k, None)]
               | _ => [(k, None)]
               end
           | _ => [(k, Some None)]
           end
       end)
    (spec_attr_entries specs).

Definition has_storage_spec (s : string) (specs : list c_spec) : bool :=
  existsb (fun sp => match sp with SpStorage x => x == s | _ => false end) specs.

Definition has_fspec (f : string) (specs : list c_spec) : bool :=
  existsb (fun sp => match sp with SpFspec x => x == f | _ => false end) specs.

Definition extern_specs (specs0 : list c_spec) : list c_spec :=
  if has_storage_spec "extern" specs0 || has_storage_spec "static" specs0 then specs0
  else SpStorage "extern" :: specs0.

(** ## Syntax walks over function bodies

    Before lowering a function body, three structural walks check label
    redefinitions and jumps into statement expressions, collect address-taken
    GNU labels ([&&L]), and detect identifiers such as [zreturn] or self-calls
    inside GNU extern inline bodies. *)

Inductive jump_event : Type :=
| JELabel (name : string) (regs : list (list Z)) (loc : c_loc)
| JEJump (name : string) (regs : list (list Z)) (loc : c_loc).

Fixpoint list_Z_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: ra, y :: rb => Z.eqb x y && list_Z_eqb ra rb
  | _, _ => false
  end.

Fixpoint regs_eqb (a b : list (list Z)) : bool :=
  match a, b with
  | [], [] => true
  | x :: ra, y :: rb => list_Z_eqb x y && regs_eqb ra rb
  | _, _ => false
  end.

Fixpoint regs_suffix (sub whole : list (list Z)) : bool :=
  if regs_eqb sub whole then true
  else
    match whole with
    | [] => false
    | _ :: rest => regs_suffix sub rest
    end.

Definition walk_fuel : nat := Z.to_nat 2048.

Fixpoint jr_stmt_f (fuel : nat) (s : c_stmt) (path : list Z) (regs sw : list (list Z))
  (acc : list jump_event) {struct fuel} : c_tr (list jump_event) :=
  match fuel with
  | O => TOk acc
  | S f =>
      match s with
      | Stmt loc body =>
          let fix go_idx {A : Type} (fn : A -> list Z -> list jump_event -> c_tr (list jump_event))
            (xs : list A) (i : Z) (a : list jump_event) : c_tr (list jump_event) :=
            match xs with
            | [] => TOk a
            | x :: rest =>
                match fn x (i :: path) a with
                | TErr err => TErr err
                | TOk a1 => go_idx fn rest (i + 1) a1
                end
            end in
          match body with
          | SBlock items =>
              go_idx (fun it p a =>
                        match it with
                        | BIStmt st => jr_stmt_f f st p regs sw a
                        | BIDecl d => jr_item_f f d p regs sw a
                        end) items 0 acc
          | SExpr e => jr_expr_f f e (0 :: path) regs sw loc acc
          | SNull | SBreak | SContinue | SUnsupportedAsm _ => TOk acc
          | SIf c t oe =>
              match jr_expr_f f c (0 :: path) regs sw loc acc with
              | TErr err => TErr err
              | TOk a1 =>
                  match jr_stmt_f f t (1 :: path) regs sw a1 with
                  | TErr err => TErr err
                  | TOk a2 =>
                      match oe with
                      | Some e => jr_stmt_f f e (2 :: path) regs sw a2
                      | None => TOk a2
                      end
                  end
              end
          | SWhile c b | SDo b c =>
              match jr_expr_f f c (0 :: path) regs sw loc acc with
              | TErr err => TErr err
              | TOk a1 => jr_stmt_f f b (1 :: path) regs sw a1
              end
          | SFor ini oc os b =>
              let a0 :=
                match ini with
                | FINone => TOk acc
                | FIExpr e => jr_expr_f f e (0 :: path) regs sw loc acc
                | FIDecl it => jr_item_f f it (0 :: path) regs sw acc
                end in
              match a0 with
              | TErr err => TErr err
              | TOk a1 =>
                  let a2 :=
                    match oc with
                    | Some c => jr_expr_f f c (1 :: path) regs sw loc a1
                    | None => TOk a1
                    end in
                  match a2 with
                  | TErr err => TErr err
                  | TOk a3 =>
                      let a4 :=
                        match os with
                        | Some stp => jr_expr_f f stp (2 :: path) regs sw loc a3
                        | None => TOk a3
                        end in
                      match a4 with
                      | TErr err => TErr err
                      | TOk a5 => jr_stmt_f f b (3 :: path) regs sw a5
                      end
                  end
              end
          | SSwitch e b =>
              match jr_expr_f f e (0 :: path) regs sw loc acc with
              | TErr err => TErr err
              | TOk a1 => jr_stmt_f f b (1 :: path) regs regs a1
              end
          | SCase e b =>
              if regs_eqb regs sw then
                match jr_expr_f f e (0 :: path) regs sw loc acc with
                | TErr err => TErr err
                | TOk a1 => jr_stmt_f f b (1 :: path) regs sw a1
                end
              else sema_err loc "switch dispatch into a statement expression is not allowed"
          | SCaseRange lo hi b =>
              if regs_eqb regs sw then
                match jr_expr_f f lo (0 :: path) regs sw loc acc with
                | TErr err => TErr err
                | TOk a1 =>
                    match jr_expr_f f hi (1 :: path) regs sw loc a1 with
                    | TErr err => TErr err
                    | TOk a2 => jr_stmt_f f b (2 :: path) regs sw a2
                    end
                end
              else sema_err loc "switch dispatch into a statement expression is not allowed"
          | SDefault b =>
              if regs_eqb regs sw then jr_stmt_f f b (0 :: path) regs sw acc
              else sema_err loc "switch dispatch into a statement expression is not allowed"
          | SReturn oe =>
              match oe with
              | Some e => jr_expr_f f e (0 :: path) regs sw loc acc
              | None => TOk acc
              end
          | SGoto name => TOk (JEJump name regs loc :: acc)
          | SComputedGoto e => jr_expr_f f e (0 :: path) regs sw loc acc
          | SLabel name b =>
              jr_stmt_f f b (0 :: path) regs sw (JELabel name regs loc :: acc)
          | SAsmEmpty outs ins _ _ | SAsm _ outs ins _ _ =>
              match go_idx (fun op p a => match op with AsmOp _ e => jr_expr_f f e p regs sw loc a end) outs 0 acc with
              | TErr err => TErr err
              | TOk a1 => go_idx (fun op p a => match op with AsmOp _ e => jr_expr_f f e p regs sw loc a end) ins 0 a1
              end
          end
      end
  end

with jr_item_f (fuel : nat) (it : c_item) (path : list Z) (regs sw : list (list Z))
  (acc : list jump_event) {struct fuel} : c_tr (list jump_event) :=
  match fuel with
  | O => TOk acc
  | S f =>
      match it with
      | IDecl loc _ inits =>
          let fix go (xs : list c_init_decl) (i : Z) (a : list jump_event) :=
            match xs with
            | [] => TOk a
            | InitDecl _ (Some ini) :: rest =>
                match jr_init_f f ini (i :: path) regs sw loc a with
                | TErr err => TErr err
                | TOk a1 => go rest (i + 1) a1
                end
            | _ :: rest => go rest (i + 1) a
            end in
          go inits 0 acc
      | IStaticAssert loc c _ => jr_expr_f f c (0 :: path) regs sw loc acc
      | _ => TOk acc
      end
  end

with jr_init_f (fuel : nat) (ini : c_init) (path : list Z) (regs sw : list (list Z))
  (loc : c_loc) (acc : list jump_event) {struct fuel} : c_tr (list jump_event) :=
  match fuel with
  | O => TOk acc
  | S f =>
      match ini with
      | InitExpr e => jr_expr_f f e (0 :: path) regs sw loc acc
      | InitList es =>
          let fix go (xs : list c_init_entry) (i : Z) (a : list jump_event) :=
            match xs with
            | [] => TOk a
            | InitEntry _ sub :: rest =>
                match jr_init_f f sub (i :: path) regs sw loc a with
                | TErr err => TErr err
                | TOk a1 => go rest (i + 1) a1
                end
            end in
          go es 0 acc
      end
  end

with jr_expr_f (fuel : nat) (e : c_expr) (path : list Z) (regs sw : list (list Z))
  (loc : c_loc) (acc : list jump_event) {struct fuel} : c_tr (list jump_event) :=
  match fuel with
  | O => TOk acc
  | S f =>
      match e with
      | EStmtExpr blk => jr_stmt_f f blk (0 :: path) (path :: regs) sw acc
      | EBin _ a b | EAssign _ a b | EGCond a b | EComma a b | EIndex a b =>
          match jr_expr_f f a (0 :: path) regs sw loc acc with
          | TErr err => TErr err
          | TOk a1 => jr_expr_f f b (1 :: path) regs sw loc a1
          end
      | ECond c a b =>
          match jr_expr_f f c (0 :: path) regs sw loc acc with
          | TErr err => TErr err
          | TOk a1 =>
              match jr_expr_f f a (1 :: path) regs sw loc a1 with
              | TErr err => TErr err
              | TOk a2 => jr_expr_f f b (2 :: path) regs sw loc a2
              end
          end
      | EUn _ x | EMember x _ | EArrow x _ | ECast _ x | ESizeofExpr x
      | EAlignofExpr x | ERealPart x | EImagPart x | EConvertVector x _
      | EVaArg x _ | EBitCast _ x =>
          jr_expr_f f x (0 :: path) regs sw loc acc
      | ECall fn args =>
          match jr_expr_f f fn (0 :: path) regs sw loc acc with
          | TErr err => TErr err
          | TOk a1 =>
              let fix go (xs : list c_expr) (i : Z) (a : list jump_event) :=
                match xs with
                | [] => TOk a
                | ex :: rest =>
                    match jr_expr_f f ex (i :: path) regs sw loc a with
                    | TErr err => TErr err
                    | TOk a2 => go rest (i + 1) a2
                    end
                end in
              go args 1 a1
          end
      | EComplit _ es => jr_init_f f (InitList es) path regs sw loc acc
      | EGeneric ctrl gs =>
          match jr_expr_f f ctrl (0 :: path) regs sw loc acc with
          | TErr err => TErr err
          | TOk a1 =>
              let fix go (xs : list c_generic_assoc) (i : Z) (a : list jump_event) :=
                match xs with
                | [] => TOk a
                | GAssocType _ ex :: rest | GAssocDefault ex :: rest =>
                    match jr_expr_f f ex (i :: path) regs sw loc a with
                    | TErr err => TErr err
                    | TOk a2 => go rest (i + 1) a2
                    end
                end in
              go gs 1 a1
          end
      | _ => TOk acc
      end
  end.

Definition statement_expression_jumps (body : c_stmt) (loc : c_loc) : c_tr unit :=
  match jr_stmt_f walk_fuel body [] [] [] [] with
  | TErr err => TErr err
  | TOk rev_ev =>
      let evs := rev rev_ev in
      let defs :=
        flat_map (fun ev => match ev with JELabel n r l => [(n, r, l)] | _ => [] end) evs in
      let fix check_dups (xs : list (string * list (list Z) * c_loc)) (seen : list string) : c_tr unit :=
        match xs with
        | [] => TOk tt
        | (n, _, l) :: rest =>
            if str_mem n seen then sema_err l ("redefinition of label " ++ n)
            else check_dups rest (n :: seen)
        end in
      match check_dups defs [] with
      | TErr err => TErr err
      | TOk _ =>
          let fix check_jumps (xs : list jump_event) : c_tr unit :=
            match xs with
            | [] => TOk tt
            | JEJump n from l :: rest =>
                let bad :=
                  existsb (fun d =>
                             let '(dn, to, _) := d in
                             (dn == n) && negb (regs_suffix to from)) defs in
                if bad then sema_err l "goto into a statement expression is not allowed"
                else check_jumps rest
            | JELabel _ _ _ :: rest => check_jumps rest
            end in
          check_jumps evs
      end
  end.

(** Collect address-taken labels and identifier references in source order. *)

Fixpoint la_stmt_f (fuel : nat) (s : c_stmt) (acc : list string) {struct fuel} : list string :=
  match fuel with
  | O => acc
  | S f =>
      match s with
      | Stmt _ b =>
          match b with
          | SBlock items =>
              fold_left (fun a it =>
                           match it with
                           | BIStmt st => la_stmt_f f st a
                           | BIDecl d => la_item_f f d a
                           end) items acc
          | SExpr e | SComputedGoto e => la_expr_f f e acc
          | SIf c t oe =>
              let a1 := la_stmt_f f t (la_expr_f f c acc) in
              match oe with Some e => la_stmt_f f e a1 | None => a1 end
          | SWhile c body => la_stmt_f f body (la_expr_f f c acc)
          | SDo body c => la_expr_f f c (la_stmt_f f body acc)
          | SFor ini oc os body =>
              let a1 :=
                match ini with
                | FINone => acc
                | FIExpr e => la_expr_f f e acc
                | FIDecl it => la_item_f f it acc
                end in
              let a2 := match oc with Some c => la_expr_f f c a1 | None => a1 end in
              let a3 := match os with Some st => la_expr_f f st a2 | None => a2 end in
              la_stmt_f f body a3
          | SSwitch e body | SCase e body => la_stmt_f f body (la_expr_f f e acc)
          | SCaseRange lo hi body => la_stmt_f f body (la_expr_f f hi (la_expr_f f lo acc))
          | SDefault body | SLabel _ body => la_stmt_f f body acc
          | SReturn (Some e) => la_expr_f f e acc
          | SAsmEmpty outs ins _ _ | SAsm _ outs ins _ _ =>
              let a1 := fold_left (fun a op => match op with AsmOp _ e => la_expr_f f e a end) outs acc in
              fold_left (fun a op => match op with AsmOp _ e => la_expr_f f e a end) ins a1
          | _ => acc
          end
      end
  end
with la_item_f (fuel : nat) (it : c_item) (acc : list string) {struct fuel} : list string :=
  match fuel with
  | O => acc
  | S f =>
      match it with
      | IDecl _ _ inits =>
          fold_left (fun a d => match d with InitDecl _ (Some ini) => la_init_f f ini a | _ => a end) inits acc
      | IStaticAssert _ c _ => la_expr_f f c acc
      | _ => acc
      end
  end
with la_init_f (fuel : nat) (ini : c_init) (acc : list string) {struct fuel} : list string :=
  match fuel with
  | O => acc
  | S f =>
      match ini with
      | InitExpr e => la_expr_f f e acc
      | InitList es =>
          fold_left (fun a en => match en with InitEntry _ i => la_init_f f i a end) es acc
      end
  end
with la_expr_f (fuel : nat) (e : c_expr) (acc : list string) {struct fuel} : list string :=
  match fuel with
  | O => acc
  | S f =>
      match e with
      | ELabelAddr nm => nm :: acc
      | EStmtExpr blk => la_stmt_f f blk acc
      | EBin _ a b | EAssign _ a b | EGCond a b | EComma a b | EIndex a b =>
          la_expr_f f b (la_expr_f f a acc)
      | ECond c a b => la_expr_f f b (la_expr_f f a (la_expr_f f c acc))
      | EUn _ x | EMember x _ | EArrow x _ | ECast _ x | ESizeofExpr x
      | EAlignofExpr x | ERealPart x | EImagPart x | EConvertVector x _
      | EVaArg x _ | EBitCast _ x => la_expr_f f x acc
      | ECall fn args => fold_left (fun a x => la_expr_f f x a) args (la_expr_f f fn acc)
      | EComplit _ es =>
          fold_left (fun a en => match en with InitEntry _ i => la_init_f f i a end) es acc
      | EGeneric ctrl gs =>
          fold_left (fun a g => match g with GAssocType _ x | GAssocDefault x => la_expr_f f x a end)
                    gs (la_expr_f f ctrl acc)
      | _ => acc
      end
  end.

Definition first_uses_str (xs : list string) : list string :=
  let fix go (l : list string) (seen : list string) (acc : list string) :=
    match l with
    | [] => rev acc
    | x :: rest =>
        if str_mem x seen then go rest seen acc
        else go rest (x :: seen) (x :: acc)
    end in
  go xs [] [].

Definition label_values (body : c_stmt) (env0 : c_type_env) : c_type_env * list string :=
  let names := first_uses_str (rev (la_stmt_f walk_fuel body [])) in
  let fix bind_all (ns : list string) (n : Z) (e : c_type_env) :=
    match ns with
    | [] => e
    | nm :: rest => bind_all rest (n + 1) (bind_label_addr nm n e)
    end in
  (bind_all names 1 env0, names).

Fixpoint id_stmt_f (fuel : nat) (p : string -> bool) (s : c_stmt) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S f =>
      match s with
      | Stmt _ b =>
          match b with
          | SBlock items =>
              existsb (fun it =>
                         match it with
                         | BIStmt st => id_stmt_f f p st
                         | BIDecl d => id_item_f f p d
                         end) items
          | SExpr e | SComputedGoto e => id_expr_f f p e
          | SIf c t oe =>
              id_expr_f f p c || id_stmt_f f p t
              || match oe with Some e => id_stmt_f f p e | None => false end
          | SWhile c body | SDo body c => id_expr_f f p c || id_stmt_f f p body
          | SFor ini oc os body =>
              (match ini with FINone => false | FIExpr e => id_expr_f f p e | FIDecl d => id_item_f f p d end)
              || (match oc with Some c => id_expr_f f p c | None => false end)
              || (match os with Some st => id_expr_f f p st | None => false end)
              || id_stmt_f f p body
          | SSwitch e body | SCase e body => id_expr_f f p e || id_stmt_f f p body
          | SCaseRange lo hi body => id_expr_f f p lo || id_expr_f f p hi || id_stmt_f f p body
          | SDefault body | SLabel _ body => id_stmt_f f p body
          | SReturn (Some e) => id_expr_f f p e
          | SAsmEmpty outs ins _ _ | SAsm _ outs ins _ _ =>
              existsb (fun op => match op with AsmOp _ e => id_expr_f f p e end) outs
              || existsb (fun op => match op with AsmOp _ e => id_expr_f f p e end) ins
          | _ => false
          end
      end
  end
with id_item_f (fuel : nat) (p : string -> bool) (it : c_item) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S f =>
      match it with
      | IDecl _ _ inits =>
          existsb (fun d => match d with InitDecl _ (Some ini) => id_init_f f p ini | _ => false end) inits
      | IStaticAssert _ c _ => id_expr_f f p c
      | _ => false
      end
  end
with id_init_f (fuel : nat) (p : string -> bool) (ini : c_init) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S f =>
      match ini with
      | InitExpr e => id_expr_f f p e
      | InitList es => existsb (fun en => match en with InitEntry _ i => id_init_f f p i end) es
      end
  end
with id_expr_f (fuel : nat) (p : string -> bool) (e : c_expr) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S f =>
      match e with
      | EId x => p x
      | EStmtExpr blk => id_stmt_f f p blk
      | EBin _ a b | EAssign _ a b | EGCond a b | EComma a b | EIndex a b =>
          id_expr_f f p a || id_expr_f f p b
      | ECond c a b => id_expr_f f p c || id_expr_f f p a || id_expr_f f p b
      | EUn _ x | EMember x _ | EArrow x _ | ECast _ x | ESizeofExpr x
      | EAlignofExpr x | ERealPart x | EImagPart x | EConvertVector x _
      | EVaArg x _ | EBitCast _ x => id_expr_f f p x
      | ECall fn args => id_expr_f f p fn || existsb (id_expr_f f p) args
      | EComplit _ es => existsb (fun en => match en with InitEntry _ i => id_init_f f p i end) es
      | EGeneric ctrl gs =>
          id_expr_f f p ctrl
          || existsb (fun g => match g with GAssocType _ x | GAssocDefault x => id_expr_f f p x end) gs
      | _ => false
      end
  end.

Definition id_stmt (p : string -> bool) (s : c_stmt) : bool :=
  id_stmt_f walk_fuel p s.

Definition names_symbol (x sym : string) (env : c_type_env) : bool :=
  match lookup_ordinary env x with
  | Some (BFn _ s _) => s == sym
  | _ =>
      match strip_prefix "__builtin_" x with
      | Some b =>
          if b == sym then true
          else match lookup_ordinary env b with Some (BFn _ s _) => s == sym | _ => false end
      | None => false
      end
  end.

Definition zreturn_body (body : c_stmt) (env : c_type_env) : bool :=
  match lookup_ordinary env "zreturn" with
  | Some (BFn _ s _) => (s == "zreturn") && id_stmt (fun x => x == "zreturn") body
  | _ => false
  end.

(** ## ABI checks, variably modified scopes, cleanups, and switch dispatch *)

Fixpoint holds_vec_f (fuel : nat) (ty : c_type) (env : c_type_env) : option string :=
  match fuel with
  | O => None
  | S f =>
      match ty with
      | TVec _ _ _ => Some "a vector"
      | TAtomic _ _ => Some "an _Atomic struct or union"
      | TArray t _ => holds_vec_f f t env
      | TStruct id | TUnion id =>
          match smap_find (su_id_key id) (df_su (te_defs env)) with
          | Some (SUDef _ members _ _) =>
              let fix go (ms : list c_member_layout) : option string :=
                match ms with
                | [] => None
                | m :: rest =>
                    match holds_vec_f f (ml_type m) env with
                    | Some k => Some k
                    | None => go rest
                    end
                end in
              go members
          | _ => None
          end
      | _ => None
      end
  end.

Definition holds_vec (ty : c_type) (env : c_type_env) : option string :=
  holds_vec_f 64 ty env.

Definition vector_abi (ft : c_type) (env : c_type_env) (loc : c_loc) : c_tr unit :=
  match ft with
  | TFunc ret ops _ =>
      let found :=
        match holds_vec ret env with
        | Some k => Some k
        | None =>
            match ops with
            | Some ps =>
                let fix go (l : list c_type) :=
                  match l with
                  | [] => None
                  | p :: rest => match holds_vec p env with Some k => Some k | None => go rest end
                  end in
                go ps
            | None => None
            end
        end in
      match found with
      | Some k =>
          sema_err loc ("a function with external linkage or called through a pointer cannot take or return " ++ k)
      | None => TOk tt
      end
  | _ => TOk tt
  end.

Definition ret_class_of (loc : c_loc) (ret_t : c_type) (env : c_type_env) : c_tr term :=
  match ret_t with
  | TVoid => TOk (TAtom "void")
  | TFloatK FLDouble => TOk (TApp "tuple" [TList [TAtom "l"; TAtom "l"]])
  | _ =>
      match complex_type ret_t with
      | Some (TFloatK FLDouble) =>
          sema_err loc "returning _Complex long double is not supported yet"
      | _ =>
          match type_class ret_t with
          | Some k => TOk (TAtom k)
          | None =>
              if is_memtype ret_t then
                match ret_shape ret_t env loc with
                | TErr err => TErr err
                | TOk (RetWords [eb]) => TOk (TAtom (eb_class eb))
                | TOk (RetWords [eb1; eb2]) =>
                    TOk (TApp "tuple" [TList [TAtom (eb_class eb1); TAtom (eb_class eb2)]])
                | TOk _ => TOk (TAtom "void")
                end
              else sema_err loc ("returning " ++ c_type_diag_str ret_t ++ " is not supported yet")
          end
      end
  end.

Definition static_assert_check (loc : c_loc) (e : c_expr) (env : c_type_env) : c_tr unit :=
  match const_value e env with
  | TErr _ => sema_err loc "static assertion is not a constant"
  | TOk (v, _) =>
      if Z.eqb v 0 then sema_err loc "static assertion failed" else TOk tt
  end.

Definition stmt_body_kind (b : c_stmt_body) : string :=
  match b with
  | SBlock _ => "block"
  | SExpr _ => "expr"
  | SNull => "null"
  | SIf _ _ _ => "if"
  | SWhile _ _ => "while"
  | SDo _ _ => "do"
  | SFor _ _ _ _ => "for"
  | SSwitch _ _ => "switch"
  | SCase _ _ | SCaseRange _ _ _ => "case"
  | SDefault _ => "default"
  | SBreak => "break"
  | SContinue => "continue"
  | SReturn _ => "return"
  | SGoto _ => "goto"
  | SComputedGoto _ => "computed_goto"
  | SLabel _ _ => "label"
  | SAsmEmpty _ _ _ _ => "asm_empty"
  | SAsm _ _ _ _ _ => "asm"
  | SUnsupportedAsm _ => "unsupported_asm"
  end.

Definition vm_typed (t l : c_type) : c_type :=
  if vm_type t then l else unqualified t.

Definition vm_scope_enter (ty : c_type) (st : c_func_st) : c_func_st :=
  if vm_type ty then
    let '(k, env1) := next_env_id (fs_env st) in
    let ls := fs_lscope st in
    let ls1 :=
      mkCLowerScope (VMSNormal k :: ls_vm_scopes ls) (ls_vm_switch ls)
                    (ls_cleanup_at ls) (ls_labels_taken ls) (ls_va_args ls) (ls_sret ls) in
    set_fs_lscope ls1 (set_fs_env env1 st)
  else st.

Definition vm_label_mark (name : string) (st : c_func_st) : c_func_st :=
  let scopes := ls_vm_scopes (fs_lscope st) in
  mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) (fs_cur st) (fs_insts st)
            (fs_blocks st) (fs_n st) (fs_labels st)
            (smap_add name scopes (fs_vm_labels st))
            (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
            (fs_computed_goto st) (fs_cases st) (fs_build st) (fs_opts st).

Definition vm_goto_mark (name : string) (loc : c_loc) (st : c_func_st) : c_func_st :=
  let scopes := ls_vm_scopes (fs_lscope st) in
  mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) (fs_cur st) (fs_insts st)
            (fs_blocks st) (fs_n st) (fs_labels st) (fs_vm_labels st)
            ((name, scopes, loc) :: fs_vm_gotos st)
            (fs_cleanups st) (fs_cleanup_gotos st)
            (fs_computed_goto st) (fs_cases st) (fs_build st) (fs_opts st).

Fixpoint vm_scopes_eqb (a b : list vm_scope_id) : bool :=
  match a, b with
  | [], [] => true
  | x :: ra, y :: rb => vm_scope_id_eqb x y && vm_scopes_eqb ra rb
  | _, _ => false
  end.

Fixpoint vm_scopes_suffix (sub whole : list vm_scope_id) : bool :=
  if vm_scopes_eqb sub whole then true
  else match whole with [] => false | _ :: rest => vm_scopes_suffix sub rest end.

Definition entered_cleanup (to_s from_s : list vm_scope_id) : bool :=
  existsb (fun s =>
             match s with
             | VMSCleanup k =>
                 negb (existsb (vm_scope_id_eqb (VMSCleanup k)) from_s)
             | VMSNormal _ => false
             end) to_s.

Definition vm_jumps_check (st : c_func_st) : l_res unit :=
  let fix go (gs : list (string * list vm_scope_id * c_loc)) : l_res unit :=
    match gs with
    | [] => LOk tt st
    | (name, from_s, loc) :: rest =>
        match smap_find name (fs_vm_labels st) with
        | Some to_s =>
            if negb (vm_scopes_suffix to_s from_s) then
              if entered_cleanup to_s from_s then
                l_err loc "cannot jump from this goto statement to its label: it bypasses the initialization of a variable with __attribute__((cleanup))" st
              else
                l_err loc "goto into the scope of a variably modified identifier" st
            else go rest
        | None => go rest
        end
    end in
  go (fs_vm_gotos st).

Definition vm_case_check (ctx : c_lower_ctx) (st : c_func_st) : l_res unit :=
  let ls := fs_lscope st in
  let sc := ls_vm_scopes ls in
  let out := ls_vm_switch ls in
  if vm_scopes_eqb sc out then LOk tt st
  else if entered_cleanup sc out then
    l_err (ctx_loc ctx) "cannot jump from switch statement to this case label: it bypasses the initialization of a variable with __attribute__((cleanup))" st
  else
    l_err (ctx_loc ctx) "switch jumps into the scope of a variably modified identifier" st.

Definition cleanup_keys_of (scopes : list vm_scope_id) : list Z :=
  flat_map (fun s => match s with VMSCleanup k => [k] | VMSNormal _ => [] end) scopes.

Definition cleanup_keys_st (st : c_func_st) : list Z :=
  cleanup_keys_of (ls_vm_scopes (fs_lscope st)).

Fixpoint list_Z_strip_suffix (outer full : list Z) : option (list Z) :=
  if list_Z_eqb outer full then Some []
  else
    match full with
    | [] => None
    | x :: rest =>
        match list_Z_strip_suffix outer rest with
        | Some pre => Some (x :: pre)
        | None => None
        end
    end.

Definition leaving_cleanups (outer : list Z) (st : c_func_st) : l_res (list Z) :=
  let ks0 := cleanup_keys_st st in
  match list_Z_strip_suffix outer ks0 with
  | Some ks => LOk ks st
  | None => LErr "cleanup scopes are not properly nested"
  end.

Definition cleanup_targets_set (lbls : list string) (st : c_func_st) : c_func_st :=
  let ks := cleanup_keys_st st in
  let ls := fs_lscope st in
  let m1 := fold_left (fun m l => smap_add l ks m) lbls (ls_cleanup_at ls) in
  set_fs_lscope
    (mkCLowerScope (ls_vm_scopes ls) (ls_vm_switch ls) m1
                   (ls_labels_taken ls) (ls_va_args ls) (ls_sret ls)) st.

Definition is_automatic_decl (d : c_decl) : bool :=
  match cd_type d with
  | TFunc _ _ _ => false
  | _ =>
      match cd_storage d with
      | StStatic | StExtern | StThreadLocal _ => false
      | _ => true
      end
  end.

Definition cleanup_parameter_check (loc : c_loc) (fn : string) (fnb varb : ord_binding)
  (env : c_type_env) : c_tr unit :=
  match fnb with
  | BFn (TFunc _ ops _) _ _ =>
      match varb with
      | BVar _ vt0 =>
          let vt := unqualified vt0 in
          match ops with
          | Some [pt] =>
              match unqualified pt with
              | TPtr q0 =>
                  let q := unqualified q0 in
                  if c_type_eqb q TVoid || compatible_type q vt (Some env) then TOk tt
                  else sema_err loc ("'cleanup' function " ++ fn ++ " parameter has type " ++
                                     c_type_diag_str pt ++ " which is incompatible with type " ++
                                     c_type_diag_str (TPtr vt0))
              | _ =>
                  sema_err loc ("'cleanup' function " ++ fn ++ " parameter has type " ++
                                c_type_diag_str pt ++ " which is incompatible with type " ++
                                c_type_diag_str (TPtr vt0))
              end
          | _ => sema_err loc ("'cleanup' function " ++ fn ++ " must take 1 parameter")
          end
      | _ => sema_err loc "a cleanup attribute on this variable is not supported"
      end
  | _ => sema_err loc ("'cleanup' argument " ++ fn ++ " is not a function")
  end.

Definition cleanup_var_register (loc : c_loc) (name fn : string) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res unit :=
  let env0 := fs_env st0 in
  match lookup_ordinary env0 name with
  | None => l_err loc "unknown cleanup variable" st0
  | Some varb =>
      match lookup_ordinary env0 fn with
      | Some (BFn _ _ _ as fnb) =>
          match cleanup_parameter_check loc fn fnb varb env0 with
          | TErr err => LErr (l_tr_msg loc err)
          | TOk _ =>
              let '(k, env1) := next_env_id env0 in
              let vn := "cleanup." ++ decimal k ++ ".var" in
              let fnm := "cleanup." ++ decimal k ++ ".fn" in
              let binds := [(vn, varb); (fnm, fnb)] in
              let env2 := bind_ordinary fnm fnb (bind_ordinary vn varb env1) in
              match elaborate_loc (ECall (EId fnm) [EUn UAddr (EId vn)]) env2 loc with
              | TErr err => LErr (l_tr_msg loc err)
              | TOk None => l_err loc "cannot elaborate cleanup call" st0
              | TOk (Some x) =>
                  let xv := value_node x in
                  let ls := fs_lscope st0 in
                  let ls1 :=
                    mkCLowerScope (VMSCleanup k :: ls_vm_scopes ls) (ls_vm_switch ls)
                                  (ls_cleanup_at ls) (ls_labels_taken ls) (ls_va_args ls) (ls_sret ls) in
                  let info := mkCleanupInfo xv binds (ctx_at ctx loc) in
                  let st1 :=
                    mkCFuncSt env2 ls1 (fs_globals st0) (fs_cur st0) (fs_insts st0)
                              (fs_blocks st0) (fs_n st0) (fs_labels st0) (fs_vm_labels st0)
                              (fs_vm_gotos st0)
                              (smap_add (decimal k) info (fs_cleanups st0))
                              (fs_cleanup_gotos st0) (fs_computed_goto st0) (fs_cases st0)
                              (fs_build st0) (fs_opts st0) in
                  LOk tt st1
              end
          end
      | _ => l_err loc ("'cleanup' argument " ++ fn ++ " is not a function") st0
      end
  end.

Definition returned_cleanup_var (expr : c_expr) (ret_t : c_type) (ks : list Z)
  (loc : c_loc) (st : c_func_st) : l_res unit :=
  match ks, expr with
  | _ :: _, EId name =>
      if is_aggregate (unqualified ret_t) then
        match lookup_ordinary (fs_env st) name with
        | Some (BVar (VSNamed b) _) =>
            let hit :=
              existsb (fun k =>
                         match smap_find (decimal k) (fs_cleanups st) with
                         | Some ci =>
                             match ci_binds ci with
                             | (_, BVar (VSNamed b2) _) :: _ => b == b2
                             | _ => false
                             end
                         | None => false
                         end) ks in
            if hit then l_err loc ("returning the aggregate cleanup variable " ++ name ++ " is not supported") st
            else LOk tt st
        | _ => LOk tt st
        end
      else LOk tt st
  | _, _ => LOk tt st
  end.

(** Switch case validation and binary-search dispatch. *)

Inductive dispatch_target : Type :=
| DTLbl (lbl : string)
| DTRange (hi : Z) (lbl : string).

Definition sort_Z_pairs {A : Type} (xs : list (Z * A)) : list (Z * A) :=
  let fix ins (p : Z * A) (l : list (Z * A)) : list (Z * A) :=
    match l with
    | [] => [p]
    | q :: rest =>
        match Z.compare (fst p) (fst q) with
        | Gt => q :: ins p rest
        | _ => p :: l
        end
    end in
  fold_left (fun acc p => ins p acc) xs [].

Definition distinct_cases (cs : list switch_case) (ty : c_type) (loc : c_loc) : c_tr unit :=
  let fix check_ranges (l : list switch_case) : c_tr unit :=
    match l with
    | [] => TOk tt
    | SCRange lo hi _ :: rest =>
        match convert_int lo ty, convert_int hi ty with
        | Some lo', Some hi' =>
            if Z.eqb lo lo' && Z.eqb hi hi' then check_ranges rest
            else sema_err loc ("case range " ++ decimal lo ++ " ... " ++ decimal hi ++ " does not fit the switch's type")
        | _, _ => sema_err loc ("case range " ++ decimal lo ++ " ... " ++ decimal hi ++ " does not fit the switch's type")
        end
    | _ :: rest => check_ranges rest
    end in
  match check_ranges cs with
  | TErr err => TErr err
  | TOk _ =>
      let ivs :=
        flat_map (fun c =>
                    match c with
                    | SCCase v _ =>
                        match convert_int v ty with Some w => [(w, w)] | None => [] end
                    | SCRange lo hi _ => [(lo, hi)]
                    | SCDefault _ => []
                    end) cs in
      let sorted := sort_Z_pairs ivs in
      let fix check_overlap (l : list (Z * Z)) : c_tr unit :=
        match l with
        | (_, h0) :: rest =>
            match rest with
            | (l1, _) :: _ =>
                if l1 <=? h0 then sema_err loc ("duplicate case value " ++ decimal l1)
                else check_overlap rest
            | [] => TOk tt
            end
        | [] => TOk tt
        end in
      check_overlap sorted
  end.

Fixpoint dispatch_cases (ps : list (Z * dispatch_target)) (val : term)
  (cls ldef : string) (st0 : c_func_st) : c_func_st :=
  match ps with
  | [] => l_term (ir_goto ldef) st0
  | (lo, DTRange hi lbl) :: rest =>
      let span := hi - lo in
      let '(d, st1) := l_let cls (TAtom "sub") [val; ir_const lo] st0 in
      let '(tst, st2) := l_let "w" (TApp "cmp" [TAtom "ule"; TAtom cls]) [d; ir_const span] st1 in
      let '(nxt, st3) := l_label st2 in
      let st4 := l_term (ir_branch tst lbl nxt) st3 in
      let st5 := l_start nxt st4 in
      dispatch_cases rest val cls ldef st5
  | (w, DTLbl lbl) :: rest =>
      let '(tst, st1) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom cls]) [val; ir_const w] st0 in
      let '(nxt, st2) := l_label st1 in
      let st3 := l_term (ir_branch tst lbl nxt) st2 in
      let st4 := l_start nxt st3 in
      dispatch_cases rest val cls ldef st4
  end.

Fixpoint dispatch_search_f (fuel : nat) (ps : list (Z * dispatch_target))
  (val : term) (sg : c_sign) (cls ldef : string) (st0 : c_func_st) : c_func_st :=
  match fuel with
  | O => dispatch_cases ps val cls ldef st0
  | S f =>
      let n := length ps in
      if (4 <? n)%nat then
        let half := Nat.div n 2 in
        let '(lower, upper) := list_split_at half ps in
        let pivot := match upper with (p, _) :: _ => p | [] => 0 end in
        let less := match sg with CSigned => "slt" | CUnsigned => "ult" end in
        let '(tst, st1) := l_let "w" (TApp "cmp" [TAtom less; TAtom cls]) [val; ir_const pivot] st0 in
        let '(llow, st2) := l_label st1 in
        let '(lup, st3) := l_label st2 in
        let st4 := l_term (ir_branch tst llow lup) st3 in
        let st5 := l_start llow st4 in
        let st6 := dispatch_search_f f lower val sg cls ldef st5 in
        let st7 := l_start lup st6 in
        dispatch_search_f f upper val sg cls ldef st7
      else dispatch_cases ps val cls ldef st0
  end.

Definition dispatch_switch (cs : list switch_case) (val : term) (ty : c_type)
  (lend : string) (st0 : c_func_st) : c_func_st :=
  match cs with
  | [] => l_term (ir_goto lend) st0
  | _ =>
      let single_ps :=
        flat_map (fun c =>
                    match c with
                    | SCCase v lbl =>
                        match convert_int v ty with Some w => [(w, DTLbl lbl)] | None => [] end
                    | _ => []
                    end) cs in
      let range_ps :=
        flat_map (fun c =>
                    match c with
                    | SCRange lo hi lbl =>
                        match convert_int lo ty, convert_int hi ty with
                        | Some wl, Some wh => [(wl, DTRange wh lbl)]
                        | _, _ => []
                        end
                    | _ => []
                    end) cs in
      let ps0 := app single_ps range_ps in
      let ldef :=
        match find (fun c => match c with SCDefault _ => true | _ => false end) cs with
        | Some (SCDefault l) => l
        | _ => lend
        end in
      let cls := match type_class ty with Some k => k | None => "w" end in
      if (length ps0 <=? 4)%nat then dispatch_cases ps0 val cls ldef st0
      else
        let sg := match int_info ty with Some (_, s) => s | None => CSigned end in
        dispatch_search_f 64%nat (sort_Z_pairs ps0) val sg cls ldef st0
  end.

Definition computed_dispatch (st0 : c_func_st) : c_func_st :=
  match fs_computed_goto st0 with
  | None => st0
  | Some (ldisp, slot, _) =>
      let st1 := l_start ldisp st0 in
      let '(x, st2) := l_let "l" (TApp "load" [TAtom "l"]) [slot] st1 in
      let names := ls_labels_taken (fs_lscope st2) in
      let fix make_cases (ns : list string) (n : Z) (st : c_func_st) :=
        match ns with
        | [] => ([], st)
        | nm :: rest =>
            let '(lbl, s1) := l_goto_label nm st in
            let '(cs, s2) := make_cases rest (n + 1) s1 in
            (SCCase n lbl :: cs, s2)
        end in
      let '(cs, st3) := make_cases names 1 st2 in
      let '(ltrap, st4) := l_label st3 in
      let st5 := dispatch_switch cs x TULong ltrap st4 in
      let st6 := l_start ltrap st5 in
      l_term ir_unreachable st6
  end.

(** ## Small expression and call helpers *)

Definition compound_assign_op (op : string) : option c_binop :=
  if op == "+=" then Some BAdd
  else if op == "-=" then Some BSub
  else if op == "*=" then Some BMul
  else if op == "/=" then Some BDiv
  else if op == "%=" then Some BMod
  else if op == "&=" then Some BAnd
  else if op == "|=" then Some BOr
  else if op == "^=" then Some BXor
  else if op == "<<=" then Some BShl
  else if op == ">>=" then Some BShr
  else None.

Definition binding_obj (b : ord_binding) (st : c_func_st) : option (c_place * c_func_st) :=
  match b with
  | BVar (VSNamed t) ty => Some (PLv (ir_tmp t) ty, st)
  | BFn ty sym _ => Some (PFn (ir_global sym) ty, st)
  | BGVar ty sym _ _ =>
      let '(addr, st1) := l_let "p" (TAtom "copy") [ir_global sym] st in
      Some (PLv addr ty, st1)
  | _ => None
  end.

Definition callee_temp (v : term) (st : c_func_st) : term * c_func_st :=
  match v with
  | TApp f [_] => if f == "tmp" then (v, st) else l_let "p" (TAtom "copy") [v] st
  | _ => l_let "p" (TAtom "copy") [v] st
  end.

Definition member_lv (addr : term) (su : c_type) (fld : string) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (term * c_type) :=
  let env := fs_env st0 in
  let loc := ctx_loc ctx in
  match su with
  | TStruct id | TUnion id =>
      match member_type_offset su fld env with
      | Some (ty, off) =>
          let '(p, st1) := l_offset addr off st0 in
          LOk (p, ty) st1
      | None =>
          match smap_find (su_id_key id) (df_su (te_defs env)) with
          | Some (SUBad why) | Some (SUPartial why _) =>
              l_err loc ("member " ++ fld ++ " of a type nanofil does not support (" ++ why ++ ")") st0
          | _ => l_err loc ("no member named " ++ fld) st0
          end
      end
  | _ => l_err loc ("no member named " ++ fld) st0
  end.

Definition decayed_place (p : c_place) (t : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res c_val :=
  match p with
  | PLv addr _ => LOk (CVal addr (unqualified t)) st0
  | PFn (TApp f [TAtom sym]) ft =>
      if f == "global" then
        if is_setjmp_sym sym then
          l_err (ctx_loc ctx) "setjmp requires a direct call, not a function pointer" st0
        else
          let '(addr, st1) := l_let "p" (TAtom "copy") [ir_global sym] st0 in
          LOk (CVal addr (TPtr ft)) st1
      else LOk (CVal (TApp f [TAtom sym]) (TPtr ft)) st0
  | PFn callee ft => LOk (CVal callee (TPtr ft)) st0
  | PBits _ _ _ _ => l_err (ctx_loc ctx) "cannot take address of bit-field" st0
  end.

Definition id_place (name : string) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_place :=
  match lookup_ordinary (fs_env st0) name with
  | None => l_err (ctx_loc ctx) ("undeclared identifier " ++ name) st0
  | Some b =>
      match binding_obj b st0 with
      | None => l_err (ctx_loc ctx) ("identifier " ++ name ++ " is not an object or function") st0
      | Some (p, st1) =>
          match b, p with
          | BGVar _ sym _ _, PLv (TApp f [TAtom t]) _ =>
              if f == "tmp" then
                let st2 := l_binding_context name b st1 in
                let st3 := l_record (TApp "hint" [TAtom t; TApp "named" [ir_global sym; TAtom "address"]]) st2 in
                LOk p st3
              else LOk p st1
          | _, _ => LOk p st1
          end
      end
  end.

Definition setjmp_args_of (kind : string) (args : list term) : option (list term) :=
  if kind == "sigsetjmp" then
    match args with
    | [TApp f1 [TAtom k1; buf]; TApp f2 [TAtom k2; msk]] =>
        if (f1 == "arg") && (k1 == "p") && (f2 == "arg") && (k2 == "w") then Some [buf; msk] else None
    | _ => None
    end
  else if (kind == "setjmp") || (kind == "_setjmp") then
    match args with
    | [TApp f1 [TAtom k1; buf]] =>
        if (f1 == "arg") && (k1 == "p") then Some [buf; ir_const 0] else None
    | _ => None
    end
  else None.

Definition struct_call (ret_t : c_type) (callee : term) (args : list term)
  (loc : c_loc) (st0 : c_func_st) : l_res c_val :=
  match ret_shape ret_t (fs_env st0) loc with
  | TErr err => LErr (l_tr_msg loc err)
  | TOk shape =>
      match l_local_slot ret_t st0 with
      | LErr msg => LErr msg
      | LOk tmp st1 =>
          match shape with
          | RetSret =>
              let st2 := l_emit (ir_call (TAtom "void") callee (ir_arg "p" tmp :: args)) st1 in
              LOk (CVal tmp ret_t) st2
          | RetWords [eb] =>
              let '(d, st2) := l_fresh st1 in
              let st3 := l_emit (ir_call (ir_result d (eb_class eb)) callee args) st2 in
              LOk (CVal tmp ret_t) (store_words [eb] [d] tmp st3)
          | RetWords [eb1; eb2] =>
              let '(d1, st2) := l_fresh st1 in
              let '(d2, st3) := l_fresh st2 in
              let res := ir_tuple [ir_result d1 (eb_class eb1); ir_result d2 (eb_class eb2)] in
              let st4 := l_emit (ir_call res callee args) st3 in
              LOk (CVal tmp ret_t) (store_words [eb1; eb2] [d1; d2] tmp st4)
          | RetWords _ => LOk (CVal tmp ret_t) st1
          end
      end
  end.

Definition call_result (callee : term) (ret_t : c_type) (ir_args : list term)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  let loc := ctx_loc ctx in
  let is_sj :=
    match callee with
    | TApp f [TAtom sym] => if (f == "global") && is_setjmp_sym sym then Some sym else None
    | _ => None
    end in
  match is_sj with
  | Some kind =>
      if c_type_eqb ret_t TInt then
        match setjmp_args_of kind ir_args with
        | Some ops =>
            let '(v, st1) := l_let "w" (TApp "setjmp" [TAtom kind]) ops st0 in
            LOk (CVal v TInt) st1
        | None => l_err loc ("invalid " ++ kind ++ " signature") st0
        end
      else l_err loc ("invalid " ++ kind ++ " signature") st0
  | None =>
      match complex_type ret_t with
      | Some (TFloatK FLDouble) =>
          l_err loc "calls returning _Complex long double are not supported yet" st0
      | _ =>
          if is_memtype ret_t then struct_call ret_t callee ir_args loc st0
          else if c_type_eqb ret_t TLDouble then
            match struct_call ret_t callee ir_args loc st0 with
            | LErr msg => LErr msg
            | LOk (CVal tmp _) st1 =>
                let '(v, st2) := l_let "x" (TApp "load" [TAtom "x"]) [tmp] st1 in
                LOk (CVal v ret_t) st2
            end
          else if c_type_eqb ret_t TVoid then
            LOk (CVal (ir_const 0) TVoid) (l_emit (ir_call (TAtom "void") callee ir_args) st0)
          else
            match type_class ret_t with
            | Some cls =>
                let '(d, st1) := l_fresh st0 in
                let st2 := l_emit (ir_call (ir_result d cls) callee ir_args) st1 in
                let '(v, st3) := normalize_call_result ret_t d st2 in
                LOk (CVal v ret_t) st3
            | None => l_err loc ("calls returning " ++ c_type_diag_str ret_t ++ " are not supported yet") st0
            end
      end
  end.

Definition return_struct (ret_t : c_type) (addr : term) (loc : c_loc)
  (st0 : c_func_st) : l_res unit :=
  match ret_shape ret_t (fs_env st0) loc with
  | TErr err => LErr (l_tr_msg loc err)
  | TOk RetSret =>
      match ls_sret (fs_lscope st0) with
      | Some p =>
          match copy_object ret_t addr p st0 with
          | LErr msg => LErr msg
          | LOk _ st1 => LOk tt (l_term ir_ret_void st1)
          end
      | None => l_err loc "missing sret parameter" st0
      end
  | TOk (RetWords ebs) =>
      let '(ws, st1) := load_words ebs addr st0 in
      match ws with
      | [w] => LOk tt (l_term (ir_ret w) st1)
      | _ => LOk tt (l_term (ir_rets ws) st1)
      end
  end.

Definition zero_ret (ret_t : c_type) (st0 : c_func_st) : l_res unit :=
  if c_type_eqb ret_t TVoid then LOk tt (l_term ir_ret_void st0)
  else if c_type_eqb ret_t TLDouble then
    LOk tt (l_term (ir_rets [ir_const 0; ir_const 0]) st0)
  else if is_memtype ret_t then
    match ret_shape ret_t (fs_env st0) unknown_loc with
    | TOk (RetWords [_; _]) => LOk tt (l_term (ir_rets [ir_const 0; ir_const 0]) st0)
    | TOk (RetWords _) => LOk tt (l_term (ir_ret (ir_const 0)) st0)
    | TOk RetSret => LOk tt (l_term ir_ret_void st0)
    | TErr err => LErr (l_tr_msg unknown_loc err)
    end
  else LOk tt (l_term (ir_ret (ir_const 0)) st0).

Definition fall_off (ret_t : c_type) (st0 : c_func_st) : l_res unit :=
  match fs_cur st0 with
  | None => LOk tt st0
  | Some _ => zero_ret ret_t st0
  end.

Fixpoint va_words (ebs : list abi_eb) (p : term) (st0 : c_func_st)
  : list term * c_func_st :=
  match ebs with
  | [] => ([], st0)
  | eb :: rest =>
      let '(w, st1) := l_let (eb_class eb) (TAtom "va_arg") [p] st0 in
      let '(ws, st2) := va_words rest p st1 in
      (w :: ws, st2)
  end.

Fixpoint element_type (ty : c_type) : c_type :=
  match ty with
  | TArray t _ => element_type t
  | _ => ty
  end.

Definition check_local_type (ty : c_type) (env : c_type_env) (loc : c_loc)
  (name : string) : option string :=
  match check_supported ty loc with
  | Some msg => Some msg
  | None =>
      let elem := if vla_type ty then element_type ty else ty in
      match type_size_align elem env with
      | TErr (TEBad why) => Some (sema_msg loc (name ++ " has a type nanofil does not support (" ++ why ++ ")"))
      | _ => None
      end
  end.

Definition vla_slot (ty : c_type) (min_al : Z) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res term :=
  match extent ty ctx st0 with
  | LErr msg => LErr msg
  | LOk sz st1 =>
      let elem := element_type ty in
      match type_size_align elem (fs_env st1) with
      | TErr (TEBad why) => LErr why
      | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
      | TOk (_, al0) =>
          let al := Z.max 4 (Z.max min_al al0) in
          let '(addr, st2) := l_let "p" (TApp "alloc" [Term.TInt al]) [sz] st1 in
          LOk addr st2
      end
  end.

Definition type_size_const (tn : c_type_name) (env0 : c_type_env) (loc : c_loc) : c_tr Z :=
  match type_name_type tn env0 with
  | TErr err => TErr err
  | TOk (ty, env1) =>
      match check_supported ty loc with
      | Some msg => TErr (TESema msg)
      | None =>
          match sizeof_size ty env1 with
          | TOk sz => TOk sz
          | TErr (TEBad why) => sema_err loc ("sizeof: " ++ why)
          | TErr err => TErr err
          end
      end
  end.

(** ## Fuel-bounded mutual lowering of expressions, places, statements, and initializers

    List traversals ([items], [local_decls], [store_leaves], [call_args],
    [run_cleanups]) iterate structurally on their lists without consuming
    recursion fuel so functions with thousands of statements or giant
    initializers only consume fuel proportional to AST nesting depth. *)

Fixpoint lower_f (fuel : nat) (x : c_typed_node) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res c_val :=
  match fuel with
  | O => l_err (ctx_loc ctx) "lowering recursion limit" st0
  | S f =>
      let '(saved, st1) := l_typed_origin x ctx st0 in
      match lower_node_f f x ctx st1 with
      | LErr msg => LErr msg
      | LOk r st2 =>
          let st3 := l_result_name x r st2 in
          LOk r (l_restore_origin saved st3)
      end
  end

with lower_node_f (fuel : nat) (x : c_typed_node) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res c_val :=
  match fuel with
  | O => l_err (ctx_loc ctx) "lowering recursion limit" st0
  | S f =>
      let loc := ctx_loc ctx in
      let eval_rval (e : c_expr) (c : c_lower_ctx) (s : c_func_st) : l_res c_val :=
        match elaborate e (fs_env s) with
        | TErr err => LErr (l_tr_msg (ctx_loc c) err)
        | TOk (Some n) => lower_f f (value_node n) c s
        | TOk None => l_err (ctx_loc c) "cannot type expression" s
        end in
      let eval_judged_rval (e : c_expr) (c : c_lower_ctx) (s : c_func_st) : l_res c_val :=
        let s1 := set_fs_env (expression_tags e (fs_env s)) s in
        match elaborate_loc e (fs_env s1) (ctx_loc c) with
        | TErr err => LErr (l_tr_msg (ctx_loc c) err)
        | TOk (Some n) => lower_f f (value_node n) c s1
        | TOk None => l_err (ctx_loc c) "cannot type expression" s1
        end in
      let eval_type (tn : c_type_name) (c : c_lower_ctx) (s : c_func_st) : l_res c_type :=
        match type_name_type tn (fs_env s) with
        | TErr err => LErr (l_tr_msg (ctx_loc c) err)
        | TOk (t0, _) =>
            match check_supported t0 (ctx_loc c) with
            | Some msg => LErr msg
            | None => realized_f f t0 c s
            end
        end in
      let '(TNode _ t0_node form) := x in
      match form with
      | TFInt v => LOk (CVal (ir_const v) (unqualified t0_node)) st0
      | TFFloat cs =>
          match float_literal cs with
          | Some (v, ty) => LOk (CVal (ir_const v) ty) st0
          | None => l_err loc ("invalid floating constant " ++ cs) st0
          end
      | TFImag xf =>
          let t := t0_node in
          match lower_node_f f xf ctx st0 with
          | LErr msg => LErr msg
          | LOk v st1 => cx_made t (CVal (ir_const 0) TInt) v st1
          end
      | TFLoad x0 =>
          let t := t0_node in
          match place_f f x0 ctx st0 with
          | LErr msg => LErr msg
          | LOk p st1 =>
              let u := unqualified t in
              let tx := tree_type x0 in
              match p with
              | PLv addr (TPtr _) =>
                  if atomic_or_volatile tx then
                    let '(d, st2) := l_let "p" (TApp "atomic_load" [TAtom "p"]) [addr] st1 in
                    LOk (CVal d u) st2
                  else place_loaded p u ctx st1
              | PLv addr (TAtomic s sz) => atomic_su_loaded s sz addr ctx st1
              | _ => place_loaded p u ctx st1
              end
          end
      | TFDecay x0 =>
          let t0 := t0_node in
          match place_f f x0 ctx st0 with
          | LErr msg => LErr msg
          | LOk p st1 =>
              let pt := match p with PLv _ (TArray e _) => TPtr e | _ => t0 end in
              decayed_place p (vm_typed t0 pt) ctx st1
          end
      | TFAddr x0 =>
          let t0 := t0_node in
          match place_f f x0 ctx st0 with
          | LErr msg => LErr msg
          | LOk p st1 =>
              let pt := match p with PLv _ pt0 => TPtr pt0 | _ => t0 end in
              decayed_place p (vm_typed t0 pt) ctx st1
          end
      | TFMember xs fld =>
          match lower_f f xs ctx st0 with
          | LErr msg => LErr msg
          | LOk (CVal addr su) st1 =>
              match member_lv addr su fld ctx st1 with
              | LErr msg => LErr msg
              | LOk (p, ty) st2 =>
                  match ty with
                  | TArray e _ => LOk (CVal p (TPtr e)) st2
                  | _ => loaded_val ty p ctx st2
                  end
              end
          end
      | TFVLane xv xi =>
          let t := t0_node in
          match lower_f f xv ctx st0 with
          | LErr msg => LErr msg
          | LOk (CVal addr _) st1 =>
              let u := unqualified t in
              match lower_f f xi ctx st1 with
              | LErr msg => LErr msg
              | LOk vi st2 =>
                  match ptr_offset BAdd (CVal addr (TPtr u)) u vi convert_val ctx st2 with
                  | LErr msg => LErr msg
                  | LOk (CVal p _) st3 => loaded_val u p ctx st3
                  end
              end
          end
      | TFComma xa xb =>
          match lower_f f xa ctx st0 with
          | LErr msg => LErr msg
          | LOk _ st1 => lower_f f xb ctx st1
          end
      | TFUn op xv =>
          match lower_f f xv ctx st0 with
          | LErr msg => LErr msg
          | LOk v st1 => unary_op op v ctx st1
          end
      | TFBin op xa xb =>
          match op with
          | BLand | BLor =>
              match lower_f f xa ctx st0 with
              | LErr msg => LErr msg
              | LOk va st1 =>
                  match truth_val va ctx st1 with
                  | LErr msg => LErr msg
                  | LOk wa st2 =>
                      let '(la, st3) := l_here st2 in
                      let '(lright, st4) := l_label st3 in
                      let '(ljoin, st5) := l_label st4 in
                      let '(jmp, short_v) :=
                        match op with
                        | BLand => (ir_branch wa lright ljoin, 0)
                        | _ => (ir_branch wa ljoin lright, 1)
                        end in
                      let st6 := l_term jmp st5 in
                      let st7 := l_start lright st6 in
                      match lower_f f xb ctx st7 with
                      | LErr msg => LErr msg
                      | LOk vb st8 =>
                          match truth_val vb ctx st8 with
                          | LErr msg => LErr msg
                          | LOk wb st9 =>
                              let '(nb, st10) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom "w"]) [wb; ir_const 0] st9 in
                              let '(lb, st11) := l_here st10 in
                              let st12 := l_term (ir_goto ljoin) st11 in
                              let '(v, st13) := l_fresh st12 in
                              let phi_t := ir_phi v "w" [ir_edge (TAtom la) (ir_const short_v); ir_edge (TAtom lb) nb] in
                              LOk (CVal v TInt) (l_start_phi ljoin [phi_t] st13)
                          end
                      end
                  end
              end
          | _ =>
              match lower_f f xa ctx st0 with
              | LErr msg => LErr msg
              | LOk va st1 =>
                  match lower_f f xb ctx st1 with
                  | LErr msg => LErr msg
                  | LOk vb st2 => binary_op op va vb ctx st2
                  end
              end
          end
      | TFCond xc xa xb =>
          let t := t0_node in
          let u := unqualified t in
          let '(la, st1) := l_label st0 in
          let '(lb, st2) := l_label st1 in
          let '(ljoin, st3) := l_label st2 in
          match lower_f f xc ctx st3 with
          | LErr msg => LErr msg
          | LOk vc st4 =>
              match truth_val vc ctx st4 with
              | LErr msg => LErr msg
              | LOk w st5 =>
                  let st6 := l_term (ir_branch w la lb) st5 in
                  let st7 := l_start la st6 in
                  match lower_f f xa ctx st7 with
                  | LErr msg => LErr msg
                  | LOk va st8 =>
                      match converted_val va u st8 with
                      | LErr msg => LErr msg
                      | LOk (CVal va0 _) st9 =>
                          match arm_value u va0 st9 with
                          | LErr msg => LErr msg
                          | LOk va1 st10 =>
                              let '(la1, st11) := l_here st10 in
                              let st12 := l_term (ir_goto ljoin) st11 in
                              let st13 := l_start lb st12 in
                              match lower_f f xb ctx st13 with
                              | LErr msg => LErr msg
                              | LOk vb st14 =>
                                  match converted_val vb u st14 with
                                  | LErr msg => LErr msg
                                  | LOk (CVal vb0 _) st15 =>
                                      match arm_value u vb0 st15 with
                                      | LErr msg => LErr msg
                                      | LOk vb1 st16 =>
                                          let '(lb1, st17) := l_here st16 in
                                          let st18 := l_term (ir_goto ljoin) st17 in
                                          join_arms u ljoin la1 va1 lb1 vb1 st18
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      | TFGCond xc xb =>
          let t := t0_node in
          let u := unqualified t in
          match lower_f f xc ctx st0 with
          | LErr msg => LErr msg
          | LOk vc st1 =>
              match truth_val vc ctx st1 with
              | LErr msg => LErr msg
              | LOk w st2 =>
                  let '(la, st3) := l_label st2 in
                  let '(lb, st4) := l_label st3 in
                  let '(ljoin, st5) := l_label st4 in
                  let st6 := l_term (ir_branch w la lb) st5 in
                  let st7 := l_start la st6 in
                  match converted_val vc u st7 with
                  | LErr msg => LErr msg
                  | LOk (CVal va0 _) st8 =>
                      match arm_value u va0 st8 with
                      | LErr msg => LErr msg
                      | LOk va1 st9 =>
                          let '(la1, st10) := l_here st9 in
                          let st11 := l_term (ir_goto ljoin) st10 in
                          let st12 := l_start lb st11 in
                          match lower_f f xb ctx st12 with
                          | LErr msg => LErr msg
                          | LOk vb st13 =>
                              match converted_val vb u st13 with
                              | LErr msg => LErr msg
                              | LOk (CVal vb0 _) st14 =>
                                  match arm_value u vb0 st14 with
                                  | LErr msg => LErr msg
                                  | LOk vb1 st15 =>
                                      let '(lb1, st16) := l_here st15 in
                                      let st17 := l_term (ir_goto ljoin) st16 in
                                      join_arms u ljoin la1 va1 lb1 vb1 st17
                                  end
                              end
                          end
                      end
                  end
              end
          end
      | TFAssign op xl xb =>
          let tx := tree_type xl in
          let is_vol_ptr :=
            (op == "=") && negb (atomic_qualified tx) && qualified_with tx QVolatile
            && match unqualified tx with TPtr _ => true | _ => false end in
          if is_vol_ptr then
            match place_f f xl ctx st0 with
            | LErr msg => LErr msg
            | LOk (PLv addr u) st1 =>
                match lower_f f xb ctx st1 with
                | LErr msg => LErr msg
                | LOk v0 st2 =>
                    match converted_val v0 u st2 with
                    | LErr msg => LErr msg
                    | LOk (CVal v _ as r) st3 =>
                        match atomic_stored u v addr 5 st3 with
                        | LErr msg => LErr msg
                        | LOk _ st4 => LOk r st4
                        end
                    end
                end
            | LOk _ st1 => l_err loc "invalid volatile pointer lvalue" st1
            end
          else if atomic_qualified tx then
            if op == "=" then
              match place_f f xl ctx st0 with
              | LErr msg => LErr msg
              | LOk (PLv addr u) st1 =>
                  match lower_f f xb ctx st1 with
                  | LErr msg => LErr msg
                  | LOk v0 st2 =>
                      match u with
                      | TAtomic s sz =>
                          match converted_val v0 s st2 with
                          | LErr msg => LErr msg
                          | LOk r st3 =>
                              match atomic_su_word s sz r ctx st3 with
                              | LErr msg => LErr msg
                              | LOk w st4 =>
                                  match atomic_word sz with
                                  | None => l_err loc "unsupported atomic struct size" st4
                                  | Some wt =>
                                      match atomic_stored wt w addr 5 st4 with
                                      | LErr msg => LErr msg
                                      | LOk _ st5 => LOk r st5
                                      end
                                  end
                              end
                          end
                      | _ =>
                          match converted_val v0 u st2 with
                          | LErr msg => LErr msg
                          | LOk (CVal v _ as r) st3 =>
                              match atomic_stored u v addr 5 st3 with
                              | LErr msg => LErr msg
                              | LOk _ st4 => LOk r st4
                              end
                          end
                      end
                  end
              | LOk _ st1 => l_err loc "invalid atomic lvalue" st1
              end
            else
              match rmw_aligned xl ctx st0 with
              | LErr msg => LErr msg
              | LOk _ st1 =>
                  match place_f f xl ctx st1 with
                  | LErr msg => LErr msg
                  | LOk (PLv addr u0) st2 =>
                      match lower_f f xb ctx st2 with
                      | LErr msg => LErr msg
                      | LOk vb st3 =>
                          let u := unqualified u0 in
                          let rop :=
                            if op == "+=" then "add"
                            else if op == "-=" then "sub"
                            else if op == "*=" then "mul"
                            else if op == "/=" then "div"
                            else if op == "%=" then "mod"
                            else if op == "&=" then "and"
                            else if op == "|=" then "or"
                            else if op == "^=" then "xor"
                            else if op == "<<=" then "shl"
                            else "shr" in
                          match rmw u addr rop vb ctx st3 with
                          | LErr msg => LErr msg
                          | LOk (_, r) st4 => LOk r st4
                          end
                      end
                  | LOk _ st2 => l_err loc "invalid atomic lvalue" st2
                  end
              end
          else
            match place_f f xl ctx st0 with
            | LErr msg => LErr msg
            | LOk p st1 =>
                let v_res :=
                  if op == "=" then lower_f f xb ctx st1
                  else
                    match compound_assign_op op with
                    | None => l_err loc ("unsupported compound assignment " ++ op) st1
                    | Some bop =>
                        match place_read p ctx st1 with
                        | LErr msg => LErr msg
                        | LOk cur st2 =>
                            match lower_f f xb ctx st2 with
                            | LErr msg => LErr msg
                            | LOk vb st3 => binary_op bop cur vb ctx st3
                            end
                        end
                    end in
                match v_res with
                | LErr msg => LErr msg
                | LOk v0 st2 => place_write p v0 ctx st2
                end
            end
      | TFIncDec op xl =>
          let tx := tree_type xl in
          let is_inc := match op with UPreInc | UPostInc => true | _ => false end in
          let is_pre := match op with UPreInc | UPreDec => true | _ => false end in
          if atomic_qualified tx then
            match rmw_aligned xl ctx st0 with
            | LErr msg => LErr msg
            | LOk _ st1 =>
                match place_f f xl ctx st1 with
                | LErr msg => LErr msg
                | LOk (PLv addr u0) st2 =>
                    let u := unqualified u0 in
                    let rop := if is_inc then "add" else "sub" in
                    match rmw u addr rop (CVal (ir_const 1) TInt) ctx st2 with
                    | LErr msg => LErr msg
                    | LOk (old_v, new_v) st3 => LOk (if is_pre then new_v else old_v) st3
                    end
                | LOk _ st2 => l_err loc "invalid atomic lvalue" st2
                end
            end
          else
            match place_f f xl ctx st0 with
            | LErr msg => LErr msg
            | LOk p st1 =>
                match place_read p ctx st1 with
                | LErr msg => LErr msg
                | LOk cur st2 =>
                    let bop := if is_inc then BAdd else BSub in
                    match binary_op bop cur (CVal (ir_const 1) TInt) ctx st2 with
                    | LErr msg => LErr msg
                    | LOk v0 st3 =>
                        match place_write p v0 ctx st3 with
                        | LErr msg => LErr msg
                        | LOk new_v st4 => LOk (if is_pre then new_v else cur) st4
                        end
                    end
                end
            end
      | TFCall xf xargs =>
          let t := t0_node in
          let special :=
            let decayed_fn_id :=
              match xf with
              | TNode CatVal _ (TFDecay inner) =>
                  match inner with
                  | TNode CatFun _ (TFId name) => Some name
                  | _ => None
                  end
              | _ => None
              end in
            match decayed_fn_id with
            | Some name =>
                if str_mem name ["_mm_pause"; "_mm_sfence"; "_mm_lfence"; "_mm_mfence";
                                 "_mm_clflush"; "_mm_getcsr"; "_mm_setcsr"] then
                  match lookup_ordinary (fs_env st0) name with
                  | Some (BFn _ _ lnk) =>
                      if lnk == "export" then
                        if ((name == "_mm_pause") || (name == "_mm_sfence")) && match xargs with [] => true | _ => false end then
                          let m := if name == "_mm_pause" then "pause" else "sfence" in
                          Some (LOk (CVal (ir_const 0) TVoid) (l_emit (ir_asm_fixed m [] []) st0))
                        else if ((name == "_mm_lfence") || (name == "_mm_mfence")) && match xargs with [] => true | _ => false end then
                          let m := if name == "_mm_lfence" then "lfence" else "mfence" in
                          Some (LOk (CVal (ir_const 0) TVoid)
                                    (safety_error ("Unhandled intrinsic:   call void @llvm.x86.sse2." ++ m ++ "()") st0))
                        else Some (l_err loc (name ++ " is not supported") st0)
                      else None
                  | _ => None
                  end
                else if (name == "zargs") && match xargs with [] => true | _ => false end then
                  match lookup_ordinary (fs_env st0) "zargs" with
                  | Some (BFn _ sym _) =>
                      if sym == "zargs" then
                        let '(v, st1) := l_let "p" (TAtom "va_args") [ir_const 0] st0 in
                        Some (LOk (CVal v t) st1)
                      else None
                  | _ => None
                  end
                else if (name == "zreturn") then
                  match xargs with
                  | [x1] =>
                      match lookup_ordinary (fs_env st0) "zreturn" with
                      | Some (BFn _ sym _) =>
                          if sym == "zreturn" then
                            Some (
                              match lower_f f x1 ctx st0 with
                              | LErr msg => LErr msg
                              | LOk v0 st1 =>
                                  match convert_val v0 (TPtr TVoid) st1 with
                                  | LErr msg => LErr msg
                                  | LOk (CVal v _) st2 => LOk (CVal (ir_const 0) TVoid) (l_term (ir_ret v) st2)
                                  end
                              end)
                          else None
                      | _ => None
                      end
                  | _ => None
                  end
                else if (name == "zgc_alloc") && c_type_eqb t (TPtr TVoid) then
                  match xargs with
                  | [sz_x] =>
                      match lookup_ordinary (fs_env st0) "zgc_alloc" with
                      | Some (BFn _ sym _) =>
                          if sym == "zgc_alloc" then
                            Some (
                              match lower_f f sz_x ctx st0 with
                              | LErr msg => LErr msg
                              | LOk v0 st1 =>
                                  match converted_val v0 TULong st1 with
                                  | LErr msg => LErr msg
                                  | LOk (CVal n _) st2 =>
                                      let '(addr, st3) := l_let "p" (TApp "alloc" [Term.TInt 16]) [n] st2 in
                                      LOk (CVal addr (TPtr TVoid)) st3
                                  end
                              end)
                          else None
                      | _ => None
                      end
                  | _ => None
                  end
                else None
            | None => None
            end in
          match special with
          | Some res => res
          | None =>
              let decayed_fn :=
                match xf with
                | TNode CatVal _ (TFDecay inner) =>
                    match inner with
                    | TNode CatFun _ _ => Some inner
                    | _ => None
                    end
                | _ => None
                end in
              let callee_res :=
                match decayed_fn with
                | Some fn_n =>
                    match place_f f fn_n ctx st0 with
                    | LErr msg => LErr msg
                    | LOk (PFn cal0 ft) st1 =>
                        let lnk :=
                          match fn_n with
                          | TNode CatFun _ (TFId nm) =>
                              match lookup_ordinary (fs_env st1) nm with
                              | Some (BFn _ _ l) => l
                              | _ => "export"
                              end
                          | _ => "export"
                          end in
                        let abi_ok :=
                          if lnk == "local" then TOk tt
                          else vector_abi ft (fs_env st1) loc in
                        match abi_ok with
                        | TErr err => LErr (l_tr_msg loc err)
                        | TOk _ =>
                            let cal :=
                              match cal0 with
                              | TApp gf [TAtom sym] =>
                                  if gf == "global" then
                                    match smap_find sym (lg_inline_copy (fs_globals st1)) with
                                    | Some local_s => ir_global local_s
                                    | None => cal0
                                    end
                                  else cal0
                              | _ => cal0
                              end in
                            LOk (cal, ft) st1
                        end
                    | LOk _ st1 => l_err loc "invalid function designator" st1
                    end
                | _ =>
                    match lower_f f xf ctx st0 with
                    | LErr msg => LErr msg
                    | LOk (CVal v (TPtr ft)) st1 =>
                        match vector_abi ft (fs_env st1) loc with
                        | TErr err => LErr (l_tr_msg loc err)
                        | TOk _ =>
                            let '(cal, st2) := callee_temp v st1 in
                            LOk (cal, ft) st2
                        end
                    | LOk _ st1 => l_err loc "called object is not a function pointer" st1
                    end
                end in
              match callee_res with
              | LErr msg => LErr msg
              | LOk (cal0, TFunc ret_t ops _) st1 =>
                  let '(ptys, cal) :=
                    match ops with
                    | None =>
                        let c1 :=
                          match cal0 with
                          | TApp gf [TAtom s] =>
                              if (gf == "global") && negb (is_setjmp_sym s) then ir_unproto s else cal0
                          | _ => cal0
                          end in
                        ([], c1)
                    | Some ps => (ps, cal0)
                    end in
                  match call_args_f f xargs ptys ctx st1 with
                  | LErr msg => LErr msg
                  | LOk ir_args0 st2 =>
                      let nsret :=
                        if is_memtype ret_t then
                          match ret_shape ret_t (fs_env st2) unknown_loc with
                          | TOk RetSret => 1
                          | _ => 0
                          end
                        else 0 in
                      let ir_args := pad_args_aux ir_args0 nsret [] in
                      call_result cal ret_t ir_args ctx st2
                  end
              | LOk _ st1 => l_err loc "callee is not a function" st1
              end
          end
      | TFBuiltin name args =>
          lower_builtin (mkBuiltinEvalCb eval_rval) name args ctx st0
      | TFConvertVector arg tn =>
          generic_vector_convert (mkBuiltinEvalCb eval_rval) arg tn ctx st0
      | TFBitCast xa =>
          let t := t0_node in
          match lower_f f xa ctx st0 with
          | LErr msg => LErr msg
          | LOk (CVal v a) st1 =>
              match l_local_slot t st1 with
              | LErr msg => LErr msg
              | LOk tmp st2 =>
                  match store_typed a v tmp st2 with
                  | LErr msg => LErr msg
                  | LOk _ st3 => loaded_val t tmp ctx st3
                  end
              end
          end
      | TFCast tn xv =>
          match eval_type tn ctx st0 with
          | LErr msg => LErr msg
          | LOk ty st1 =>
              match lower_f f xv ctx st1 with
              | LErr msg => LErr msg
              | LOk v0 st2 => converted_val v0 ty st2
              end
          end
      | TFVaArg tn xa =>
          match eval_type tn ctx st0 with
          | LErr msg => LErr msg
          | LOk ty st1 =>
              if is_su ty then
                let env := fs_env st1 in
                match eightbytes ty env loc with
                | TErr err => LErr (l_tr_msg loc err)
                | TOk ebs0 =>
                    let lvs := type_leaves ty env in
                    match va_cells ebs0 lvs ty loc with
                    | TErr err => LErr (l_tr_msg loc err)
                    | TOk ebs =>
                        match lower_f f xa ctx st1 with
                        | LErr msg => LErr msg
                        | LOk (CVal p _) st2 =>
                            let '(ws, st3) := va_words ebs p st2 in
                            match l_local_slot ty st3 with
                            | LErr msg => LErr msg
                            | LOk tmp st4 => LOk (CVal tmp ty) (store_words ebs ws tmp st4)
                            end
                        end
                    end
                end
              else
                let ok_va :=
                  match ty with
                  | TIntK IInt | TIntK IUInt | TIntK ILong | TIntK IULong
                  | TIntK ILLong | TIntK IULLong | TFloatK FDouble
                  | TFloatK FLDouble | TPtr _ => true
                  | _ => false
                  end in
                match type_class ty with
                | Some k =>
                    if ok_va then
                      match lower_f f xa ctx st1 with
                      | LErr msg => LErr msg
                      | LOk (CVal p _) st2 =>
                          let '(v, st3) := l_let k (TAtom "va_arg") [p] st2 in
                          LOk (CVal v ty) st3
                      end
                    else l_err loc ("unsupported va_arg type " ++ c_type_diag_str ty) st1
                | None => l_err loc ("unsupported va_arg type " ++ c_type_diag_str ty) st1
                end
          end
      | TFSizeofType tn =>
          match type_name_type tn (fs_env st0) with
          | TErr err => LErr (l_tr_msg loc err)
          | TOk (t0, _) =>
              if vla_type t0 then
                match eval_type tn ctx st0 with
                | LErr msg => LErr msg
                | LOk ty st1 =>
                    match extent ty ctx st1 with
                    | LErr msg => LErr msg
                    | LOk sz st2 => LOk (CVal sz TULong) st2
                    end
                end
              else
                match type_size_const tn (fs_env st0) loc with
                | TErr err => LErr (l_tr_msg loc err)
                | TOk sz0 => LOk (CVal (ir_const sz0) TULong) st0
                end
          end
      | TFSizeofExpr x0 =>
          let uncomp_cl :=
            match x0 with
            | TNode CatObj (TArray _ ALNone) (TFComplit tn es) => Some (tn, es)
            | _ => None
            end in
          match uncomp_cl with
          | Some (tn, es) =>
              match type_name_type tn (fs_env st0) with
              | TErr err => LErr (l_tr_msg loc err)
              | TOk (t0, env1) =>
                  match complete_array t0 (Some (InitList es)) loc env1 true with
                  | TErr err => LErr (l_tr_msg loc err)
                  | TOk ty =>
                      match type_size_align ty env1 with
                      | TErr err => LErr (l_tr_msg loc err)
                      | TOk (sz, _) => LOk (CVal (ir_const sz) TULong) st0
                      end
                  end
              end
          | None =>
              let tx := tree_type x0 in
              if vla_type tx then
                match place_f f x0 ctx st0 with
                | LErr msg => LErr msg
                | LOk (PLv _ ty) st1 =>
                    match extent ty ctx st1 with
                    | LErr msg => LErr msg
                    | LOk sz st2 => LOk (CVal sz TULong) st2
                    end
                | LOk _ st1 => l_err loc "sizeof of non-object VLA" st1
                end
              else
                match sizeof_size tx (fs_env st0) with
                | TOk sz0 => LOk (CVal (ir_const sz0) TULong) st0
                | TErr (TEBad why) => l_err loc ("sizeof: " ++ why) st0
                | TErr err => LErr (l_tr_msg loc err)
                end
          end
      | TFAlignofType (TypeName sps syn as tn) =>
          let env0 := fs_env st0 in
          match type_name_type tn env0 with
          | TErr err => LErr (l_tr_msg loc err)
          | TOk (t0, env1) =>
              match check_supported t0 loc with
              | Some msg => LErr msg
              | None =>
                  let ty := element_type t0 in
                  match type_size_align ty env1 with
                  | TErr (TEBad why) => l_err loc ("alignof: " ++ why) st0
                  | TErr err => LErr (l_tr_msg loc err)
                  | TOk (_, al0) =>
                      let al :=
                        match inherited_alignment sps syn env0 with
                        | Some a => a
                        | None => al0
                        end in
                      LOk (CVal (ir_const al) TULong) st0
                  end
              end
          end
      | TFAlignofExpr x0 =>
          match expr_alignment x0 (fs_env st0) with
          | TOk a => LOk (CVal (ir_const a) TULong) st0
          | TErr (TEBad why) => l_err loc ("alignof: " ++ why) st0
          | TErr err => LErr (l_tr_msg loc err)
          end
      | TFOffsetof tn path =>
          let env0 := fs_env st0 in
          match const_value (EOffsetof tn path) env0 with
          | TOk (v0, _) => LOk (CVal (ir_const v0) TULong) st0
          | TErr _ =>
              match type_name_type tn env0 with
              | TErr err => LErr (l_tr_msg loc err)
              | TOk (t, env1) =>
                  let has_idx := existsb (fun d => match d with DIndex _ => true | _ => false end) path in
                  if has_idx then
                    let fix rt_off (ps : list c_designator) (ty : c_type) (v0 : term) (s : c_func_st) : l_res term :=
                      match ps with
                      | [] => LOk v0 s
                      | DField fld :: rest =>
                          match member_type_offset ty fld env1 with
                          | None => l_err loc "bad offsetof" s
                          | Some (ft, moff) =>
                              let '(v1, s1) := l_let "l" (TAtom "add") [v0; ir_const moff] s in
                              rt_off rest ft v1 s1
                          end
                      | DIndex idx_e :: rest =>
                          match ty with
                          | TArray et _ =>
                              match type_size_align et env1 with
                              | TOk (sz, _) =>
                                  match eval_rval idx_e ctx s with
                                  | LErr msg => LErr msg
                                  | LOk xv s1 =>
                                      match assign_convert idx_e xv TLong loc s1 with
                                      | LErr msg => LErr msg
                                      | LOk (CVal iv _) s2 =>
                                          let '(d, s3) := l_let "l" (TAtom "mul") [iv; ir_const sz] s2 in
                                          let '(v1, s4) := l_let "l" (TAtom "add") [v0; d] s3 in
                                          rt_off rest et v1 s4
                                      end
                                  end
                              | TErr _ => l_err loc "bad offsetof" s
                              end
                          | _ => l_err loc "bad offsetof" s
                          end
                      | DRange _ _ :: _ => l_err loc "bad offsetof" s
                      end in
                    match rt_off path t (ir_const 0) st0 with
                    | LErr msg => LErr msg
                    | LOk v st1 => LOk (CVal v TULong) st1
                    end
                  else l_err loc "bad offsetof" st0
              end
          end
      | TFStmtExpr stmt_s =>
          match stmt_s with
          | Stmt _ (SBlock items) =>
          let saved_env := te_scope (fs_env st0) in
          let saved_ls := fs_lscope st0 in
          let outer := cleanup_keys_st st0 in
          let fix se_last_stmt (k : nat) (st : c_stmt) (c : c_lower_ctx) (s : c_func_st) : l_res c_val :=
            match k with
            | O => l_err loc "statement expression label limit" s
            | S k' =>
                match st with
                | Stmt sloc (SExpr e) => eval_judged_rval e (ctx_at c sloc) s
                | Stmt _ (SLabel nm body) =>
                    let s1 := vm_label_mark nm s in
                    let '(lbl, s2) := l_goto_label nm s1 in
                    match label_cleanups_f f nm lbl s2 with
                    | LErr msg => LErr msg
                    | LOk _ s3 => se_last_stmt k' body c (l_start lbl s3)
                    end
                | _ =>
                    match stmt_f f st c s with
                    | LErr msg => LErr msg
                    | LOk _ s1 => LOk (CVal (ir_const 0) TVoid) s1
                    end
                end
            end in
          let se_last (it : c_block_item) (c : c_lower_ctx) (s : c_func_st) : l_res c_val :=
            match it with
            | BIStmt st => se_last_stmt 256%nat st c s
            | _ =>
                match item_f f it c s with
                | LErr msg => LErr msg
                | LOk _ s1 => LOk (CVal (ir_const 0) TVoid) s1
                end
            end in
          let fix se_items (xs : list c_block_item) (s : c_func_st) : l_res c_val :=
            match xs with
            | [] => LOk (CVal (ir_const 0) TVoid) s
            | [last_it] => se_last last_it ctx s
            | it :: rest =>
                match item_f f it ctx s with
                | LErr msg => LErr msg
                | LOk _ s1 => se_items rest s1
                end
            end in
          match se_items items st0 with
          | LErr msg => LErr msg
          | LOk r0 st1 =>
              match leaving_cleanups outer st1 with
              | LErr msg => LErr msg
              | LOk ks st2 =>
                  let r_res :=
                    match ks, r0 with
                    | _ :: _, CVal a ty =>
                        if is_memtype ty then
                          match l_local_slot ty st2 with
                          | LErr msg => LErr msg
                          | LOk a1 st3 =>
                              match copy_object ty a a1 st3 with
                              | LErr msg => LErr msg
                              | LOk _ st4 => LOk (CVal a1 ty) st4
                              end
                          end
                        else LOk r0 st2
                    | _, _ => LOk r0 st2
                    end in
                  match r_res with
                  | LErr msg => LErr msg
                  | LOk r st3 =>
                      match run_cleanups_f f ks st3 with
                      | LErr msg => LErr msg
                      | LOk _ st4 =>
                          let env_rest := with_scope (fs_env st4) saved_env in
                          LOk r (set_fs_lscope saved_ls (set_fs_env env_rest st4))
                      end
                  end
              end
          end
          | _ => l_err loc "unsupported expression node" st0
          end
      | _ => l_err loc "unsupported expression node" st0
      end
  end

with place_f (fuel : nat) (x : c_typed_node) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res c_place :=
  match fuel with
  | O => l_err (ctx_loc ctx) "lowering recursion limit" st0
  | S f =>
      let '(saved, st1) := l_typed_origin x ctx st0 in
      match place_node_f f x ctx st1 with
      | LErr msg => LErr msg
      | LOk p st2 => LOk p (l_restore_origin saved st2)
      end
  end

with place_node_f (fuel : nat) (x : c_typed_node) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res c_place :=
  match fuel with
  | O => l_err (ctx_loc ctx) "lowering recursion limit" st0
  | S f =>
      let loc := ctx_loc ctx in
      let '(TNode cat t form) := x in
      match form with
      | TFId name =>
          match cat with
          | CatObj => id_place name ctx st0
          | CatFun =>
              match lookup_ordinary (fs_env st0) name with
              | Some b =>
                  match binding_obj b st0 with
                  | Some (p, st1) => LOk p st1
                  | None => l_err loc ("invalid function " ++ name) st0
                  end
              | None => l_err loc ("undeclared function " ++ name) st0
              end
          | CatVal => l_err loc "expression is not a modifiable lvalue" st0
          end
      | TFPredefined _ =>
          match cat with
          | CatObj =>
              let fn := ctx_func ctx in
              let n := Z.of_nat (String.length fn) + 1 in
              let '(sym, st1) := l_func_literal fn st0 in
              let '(addr, st2) := l_let "p" (TAtom "copy") [ir_global sym] st1 in
              LOk (PLv addr (TArray TChar (ALConst n))) st2
          | _ => l_err loc "expression is not a modifiable lvalue" st0
          end
      | TFStr bs =>
          match cat with
          | CatObj =>
              let '(sym, st1) := l_new_literal (LitBytes bs) st0 in
              let n := Z.of_nat (length bs) + 1 in
              let '(addr, st2) := l_let "p" (TAtom "copy") [ir_global sym] st1 in
              LOk (PLv addr (TArray TChar (ALConst n))) st2
          | _ => l_err loc "expression is not a modifiable lvalue" st0
          end
      | TFWStr wt vs =>
          match cat with
          | CatObj =>
              let elem := match wt with WInt => TInt | WUShort => TUShort | WUInt => TUInt end in
              let '(sym, st1) := l_new_literal (LitWide elem vs) st0 in
              let n := Z.of_nat (length vs) + 1 in
              let '(addr, st2) := l_let "p" (TAtom "copy") [ir_global sym] st1 in
              LOk (PLv addr (TArray elem (ALConst n))) st2
          | _ => l_err loc "expression is not a modifiable lvalue" st0
          end
      | TFComplit tn es =>
          match cat with
          | CatObj =>
              match type_name_type tn (fs_env st0) with
              | TErr err => LErr (l_tr_msg loc err)
              | TOk (t00, _) =>
                  if vla_type t00 then
                    l_err loc "a compound literal cannot have a variable length array type" st0
                  else
                    match check_supported t00 loc with
                    | Some msg => LErr msg
                    | None =>
                        match realized_f f t00 ctx st0 with
                        | LErr msg => LErr msg
                        | LOk t0 st1 =>
                            let ini := InitList es in
                            match complete_array t0 (Some ini) loc (fs_env st1) true with
                            | TErr err => LErr (l_tr_msg loc err)
                            | TOk ty =>
                                match check_local_type ty (fs_env st1) loc "compound literal" with
                                | Some msg => LErr msg
                                | None =>
                                    match l_local_slot ty st1 with
                                    | LErr msg => LErr msg
                                    | LOk addr st2 =>
                                        match init_f f addr ty ini ctx st2 with
                                        | LErr msg => LErr msg
                                        | LOk _ st3 => LOk (PLv addr ty) st3
                                        end
                                    end
                                end
                            end
                        end
                    end
              end
          | _ => l_err loc "expression is not a modifiable lvalue" st0
          end
      | TFDeref xv =>
          match cat with
          | CatObj =>
              match lower_f f xv ctx st0 with
              | LErr msg => LErr msg
              | LOk (CVal v pt) st1 =>
                  let l := match pt with TPtr inner => inner | _ => t end in
                  LOk (PLv v (vm_typed t l)) st1
              end
          | CatFun =>
              match lower_f f xv ctx st0 with
              | LErr msg => LErr msg
              | LOk (CVal v _) st1 =>
                  let '(cal, st2) := callee_temp v st1 in
                  LOk (PFn cal (unqualified t)) st2
              end
          | CatVal => l_err loc "expression is not a modifiable lvalue" st0
          end
      | TFMember xs fld =>
          match cat with
          | CatObj =>
              match place_f f xs ctx st0 with
              | LErr msg => LErr msg
              | LOk (PLv addr su) st1 =>
                  match member_lv addr su fld ctx st1 with
                  | LErr msg => LErr msg
                  | LOk (p, _) st2 =>
                      let u0 := unqualified t in
                      let u :=
                        match u0 with
                        | TVec e n a0 =>
                            match member_alignment_node (TNode CatObj t (TFMember xs fld)) (fs_env st2) with
                            | Some a1 => TVec e n (Z.min a0 a1)
                            | None => u0
                            end
                        | _ => u0
                        end in
                      LOk (PLv p u) st2
                  end
              | LOk _ st1 => l_err loc "member base is not an lvalue" st1
              end
          | _ => l_err loc "expression is not a modifiable lvalue" st0
          end
      | TFVLane xs xi =>
          match cat with
          | CatObj =>
              match place_f f xs ctx st0 with
              | LErr msg => LErr msg
              | LOk (PLv addr _) st1 =>
                  let u := unqualified t in
                  match lower_f f xi ctx st1 with
                  | LErr msg => LErr msg
                  | LOk vi st2 =>
                      match ptr_offset BAdd (CVal addr (TPtr u)) u vi convert_val ctx st2 with
                      | LErr msg => LErr msg
                      | LOk (CVal p _) st3 => LOk (PLv p u) st3
                      end
                  end
              | LOk _ st1 => l_err loc "vector lane base is not an lvalue" st1
              end
          | _ => l_err loc "expression is not a modifiable lvalue" st0
          end
      | TFBitfield xs fld w =>
          match cat with
          | CatObj =>
              match place_f f xs ctx st0 with
              | LErr msg => LErr msg
              | LOk (PLv addr su) st1 =>
                  match member_layout su fld (fs_env st1) with
                  | Some (bt, off, MBBits pos _) =>
                      let '(p, st2) := l_offset addr off st1 in
                      LOk (PBits p bt pos w) st2
                  | _ => l_err loc ("no bit-field named " ++ fld) st1
                  end
              | LOk _ st1 => l_err loc "bit-field base is not an lvalue" st1
              end
          | _ => l_err loc "expression is not a modifiable lvalue" st0
          end
      | _ => l_err loc "expression is not a modifiable lvalue" st0
      end
  end

with stmt_f (fuel : nat) (s : c_stmt) (ctx0 : c_lower_ctx) (st0 : c_func_st)
  : l_res unit :=
  match fuel with
  | O => l_err (ctx_loc ctx0) "lowering recursion limit" st0
  | S f =>
      match s with
      | Stmt loc body =>
          let ctx := ctx_at ctx0 loc in
          let '(saved, st1) :=
            l_enter_origin loc (TApp "statement" [TAtom (stmt_body_kind body)]) st0 in
          match stmt_body_f f body ctx st1 with
          | LErr msg => LErr msg
          | LOk _ st2 => LOk tt (l_restore_origin saved st2)
          end
      end
  end

with stmt_body_f (fuel : nat) (body : c_stmt_body) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res unit :=
  match fuel with
  | O => l_err (ctx_loc ctx) "lowering recursion limit" st0
  | S f =>
      let loc := ctx_loc ctx in
      let eval_rval (e : c_expr) (c : c_lower_ctx) (s : c_func_st) : l_res c_val :=
        match elaborate e (fs_env s) with
        | TErr err => LErr (l_tr_msg (ctx_loc c) err)
        | TOk (Some n) => lower_f f (value_node n) c s
        | TOk None => l_err (ctx_loc c) "cannot type expression" s
        end in
      let eval_judged (e : c_expr) (c : c_lower_ctx) (s : c_func_st) : l_res unit :=
        let s1 := set_fs_env (expression_tags e (fs_env s)) s in
        match elaborate_loc e (fs_env s1) (ctx_loc c) with
        | TErr err => LErr (l_tr_msg (ctx_loc c) err)
        | TOk _ => LOk tt s1
        end in
      let eval_judged_rval (e : c_expr) (c : c_lower_ctx) (s : c_func_st) : l_res c_val :=
        let s1 := set_fs_env (expression_tags e (fs_env s)) s in
        match elaborate_loc e (fs_env s1) (ctx_loc c) with
        | TErr err => LErr (l_tr_msg (ctx_loc c) err)
        | TOk (Some n) => lower_f f (value_node n) c s1
        | TOk None => l_err (ctx_loc c) "cannot type expression" s1
        end in
      let cond_jump (e : c_expr) (c : c_lower_ctx) (lt lf : string) (s : c_func_st) : l_res unit :=
        match eval_rval e c s with
        | LErr msg => LErr msg
        | LOk v s1 =>
            match truth_val v c s1 with
            | LErr msg => LErr msg
            | LOk tst s2 => LOk tt (l_term (ir_branch tst lt lf) s2)
            end
        end in
      let loop_located (c : c_lower_ctx) (s : c_func_st) : c_func_st :=
        snd (l_enter_origin (ctx_loc c) (TApp "statement" [TAtom "loop"]) s) in
      let asm_cb := mkAsmEvalCb eval_judged_rval (place_f f) in
      match body with
      | SBlock items =>
          let saved_env := te_scope (fs_env st0) in
          let saved_ls := fs_lscope st0 in
          let outer := cleanup_keys_st st0 in
          let fix go (xs : list c_block_item) (s : c_func_st) : l_res unit :=
            match xs with
            | [] => LOk tt s
            | it :: rest =>
                match item_f f it ctx s with
                | LErr msg => LErr msg
                | LOk _ s1 => go rest s1
                end
            end in
          match go items st0 with
          | LErr msg => LErr msg
          | LOk _ st1 =>
              match leaving_cleanups outer st1 with
              | LErr msg => LErr msg
              | LOk ks st2 =>
                  match run_cleanups_f f ks st2 with
                  | LErr msg => LErr msg
                  | LOk _ st3 =>
                      let env_rest := with_scope (fs_env st3) saved_env in
                      LOk tt (set_fs_lscope saved_ls (set_fs_env env_rest st3))
                  end
              end
          end
      | SNull => LOk tt st0
      | SAsmEmpty outs ins clobs is_goto =>
          asm_empty_lowered asm_cb outs ins clobs is_goto ctx st0
      | SAsm tpl outs ins clobs is_goto =>
          asm_stmt_lowered asm_cb tpl outs ins clobs is_goto ctx st0
      | SUnsupportedAsm (AUMemory tpl) =>
          let msg := "cannot handle inline asm (inline assembly with pointer argument is not supported): " ++ bytes_to_string tpl in
          LOk tt (safety_error msg st0)
      | SUnsupportedAsm AUOther =>
          l_err loc "inline asm is not supported, except the empty barrier asm volatile("""" ::: ""memory"")" st0
      | SExpr e =>
          match eval_judged_rval e ctx st0 with
          | LErr msg => LErr msg
          | LOk _ st1 => LOk tt st1
          end
      | SIf cond thn oels =>
          match eval_judged cond ctx st0 with
          | LErr msg => LErr msg
          | LOk _ st1 =>
              let '(lthn, st2) := l_label st1 in
              let '(lels, st3) := l_label st2 in
              let '(ljoin, st4) := l_label st3 in
              match cond_jump cond ctx lthn lels st4 with
              | LErr msg => LErr msg
              | LOk _ st5 =>
                  let st6 := l_start lthn st5 in
                  match stmt_f f thn ctx st6 with
                  | LErr msg => LErr msg
                  | LOk _ st7 =>
                      let st8 := l_term (ir_goto ljoin) st7 in
                      let st9 := l_start lels st8 in
                      let els_res :=
                        match oels with
                        | None => LOk tt st9
                        | Some es => stmt_f f es ctx st9
                        end in
                      match els_res with
                      | LErr msg => LErr msg
                      | LOk _ st10 => LOk tt (l_start ljoin st10)
                      end
                  end
              end
          end
      | SWhile cond b =>
          let '(lcond, st1) := l_label st0 in
          let '(lbody, st2) := l_label st1 in
          let '(lend, st3) := l_label st2 in
          let st4 := cleanup_targets_set [lend; lcond] st3 in
          let st5 := loop_located ctx (l_start lcond st4) in
          match eval_judged cond ctx st5 with
          | LErr msg => LErr msg
          | LOk _ st6 =>
              match cond_jump cond ctx lbody lend st6 with
              | LErr msg => LErr msg
              | LOk _ st7 =>
                  let st8 := l_start lbody st7 in
                  match stmt_f f b (loop_ctx ctx lend lcond) st8 with
                  | LErr msg => LErr msg
                  | LOk _ st9 =>
                      let st10 := l_term (ir_goto lcond) st9 in
                      LOk tt (l_start lend st10)
                  end
              end
          end
      | SDo b cond =>
          let '(lbody, st1) := l_label st0 in
          let '(lcond, st2) := l_label st1 in
          let '(lend, st3) := l_label st2 in
          let st4 := cleanup_targets_set [lend; lcond] st3 in
          let st5 := l_start lbody st4 in
          match stmt_f f b (loop_ctx ctx lend lcond) st5 with
          | LErr msg => LErr msg
          | LOk _ st6 =>
              let st7 := loop_located ctx (l_start lcond st6) in
              match eval_judged cond ctx st7 with
              | LErr msg => LErr msg
              | LOk _ st8 =>
                  match cond_jump cond ctx lbody lend st8 with
                  | LErr msg => LErr msg
                  | LOk _ st9 => LOk tt (l_start lend st9)
                  end
              end
          end
      | SFor ini ocond ostep b =>
          let saved_env := te_scope (fs_env st0) in
          let saved_ls := fs_lscope st0 in
          let outer := cleanup_keys_st st0 in
          let ini_res :=
            match ini with
            | FINone => LOk tt st0
            | FIExpr e =>
                match eval_judged_rval e ctx st0 with
                | LErr msg => LErr msg
                | LOk _ s1 => LOk tt s1
                end
            | FIDecl d => item_f f (BIDecl d) ctx st0
            end in
          match ini_res with
          | LErr msg => LErr msg
          | LOk _ st1 =>
              let '(lcond, st2) := l_label st1 in
              let '(lbody, st3) := l_label st2 in
              let '(lstep, st4) := l_label st3 in
              let '(lend, st5) := l_label st4 in
              let st6 := cleanup_targets_set [lend; lstep] st5 in
              let st7 := loop_located ctx (l_start lcond st6) in
              let cond_res :=
                match ocond with
                | None => LOk tt (l_term (ir_goto lbody) st7)
                | Some ce =>
                    match eval_judged ce ctx st7 with
                    | LErr msg => LErr msg
                    | LOk _ s1 => cond_jump ce ctx lbody lend s1
                    end
                end in
              match cond_res with
              | LErr msg => LErr msg
              | LOk _ st8 =>
                  let st9 := l_start lbody st8 in
                  match stmt_f f b (loop_ctx ctx lend lstep) st9 with
                  | LErr msg => LErr msg
                  | LOk _ st10 =>
                      let st11 := loop_located ctx (l_start lstep st10) in
                      let step_res :=
                        match ostep with
                        | None => LOk tt st11
                        | Some se =>
                            match eval_judged_rval se ctx st11 with
                            | LErr msg => LErr msg
                            | LOk _ s1 => LOk tt s1
                            end
                        end in
                      match step_res with
                      | LErr msg => LErr msg
                      | LOk _ st12 =>
                          let st13 := l_term (ir_goto lcond) st12 in
                          let st14 := l_start lend st13 in
                          match leaving_cleanups outer st14 with
                          | LErr msg => LErr msg
                          | LOk ks st15 =>
                              match run_cleanups_f f ks st15 with
                              | LErr msg => LErr msg
                              | LOk _ st16 =>
                                  let env_rest := with_scope (fs_env st16) saved_env in
                                  LOk tt (set_fs_lscope saved_ls (set_fs_env env_rest st16))
                              end
                          end
                      end
                  end
              end
          end
      | SSwitch expr b =>
          match eval_judged_rval expr ctx st0 with
          | LErr msg => LErr msg
          | LOk (CVal _ ty0 as val0) st1 =>
              if int_type ty0 then
                let ty := integer_promotion ty0 in
                match convert_val val0 ty st1 with
                | LErr msg => LErr msg
                | LOk (CVal val _) st2 =>
                    let '(ldisp, st3) := l_label st2 in
                    let '(lend, st4) := l_label st3 in
                    let st5 := cleanup_targets_set [lend] st4 in
                    let st6 := l_term (ir_goto ldisp) st5 in
                    let outer_cases := fs_cases st6 in
                    let ls := fs_lscope st6 in
                    let outer_sw := ls_vm_switch ls in
                    let ls1 :=
                      mkCLowerScope (ls_vm_scopes ls) (ls_vm_scopes ls)
                                    (ls_cleanup_at ls) (ls_labels_taken ls)
                                    (ls_va_args ls) (ls_sret ls) in
                    let st7 := set_fs_lscope ls1 (set_fs_cases [] st6) in
                    match stmt_f f b (switch_ctx ctx lend) st7 with
                    | LErr msg => LErr msg
                    | LOk _ st8 =>
                        let ls2 := fs_lscope st8 in
                        let ls3 :=
                          mkCLowerScope (ls_vm_scopes ls2) outer_sw
                                        (ls_cleanup_at ls2) (ls_labels_taken ls2)
                                        (ls_va_args ls2) (ls_sret ls2) in
                        let st9 := l_term (ir_goto lend) (set_fs_lscope ls3 st8) in
                        let cs := rev (fs_cases st9) in
                        let st10 := set_fs_cases outer_cases st9 in
                        match distinct_cases cs ty loc with
                        | TErr err => LErr (l_tr_msg loc err)
                        | TOk _ =>
                            let st11 := l_start ldisp st10 in
                            let st12 := dispatch_switch cs val ty lend st11 in
                            LOk tt (l_start lend st12)
                        end
                    end
                end
              else l_err loc "switch on a non-integer" st1
          end
      | SCase expr b =>
          match const_value expr (fs_env st0) with
          | TErr _ => l_err loc "case label is not a constant" st0
          | TOk (v, _) =>
              match vm_case_check ctx st0 with
              | LErr msg => LErr msg
              | LOk _ st1 =>
                  let '(lbl, st2) := l_label st1 in
                  let st3 := l_start lbl st2 in
                  let st4 := set_fs_cases (SCCase v lbl :: fs_cases st3) st3 in
                  stmt_f f b ctx st4
              end
          end
      | SCaseRange lo_e hi_e b =>
          match const_value lo_e (fs_env st0), const_value hi_e (fs_env st0) with
          | TOk (l, _), TOk (h, _) =>
              match vm_case_check ctx st0 with
              | LErr msg => LErr msg
              | LOk _ st1 =>
                  let '(lbl, st2) := l_label st1 in
                  let st3 := l_start lbl st2 in
                  let new_cs :=
                    if 4096 <=? h - l then [SCRange l h lbl]
                    else if h <? l then []
                    else rev (map (fun v => SCCase v lbl) (numlist_Z l h)) in
                  let st4 := set_fs_cases (app new_cs (fs_cases st3)) st3 in
                  stmt_f f b ctx st4
              end
          | _, _ => l_err loc "case label is not a constant" st0
          end
      | SDefault b =>
          match vm_case_check ctx st0 with
          | LErr msg => LErr msg
          | LOk _ st1 =>
              let '(lbl, st2) := l_label st1 in
              let st3 := l_start lbl st2 in
              let st4 := set_fs_cases (SCDefault lbl :: fs_cases st3) st3 in
              stmt_f f b ctx st4
          end
      | SBreak =>
          match ctx_break ctx with
          | None => l_err loc "break outside a loop or switch" st0
          | Some lbl =>
              let outer := match smap_find lbl (ls_cleanup_at (fs_lscope st0)) with Some ks => ks | None => [] end in
              match leaving_cleanups outer st0 with
              | LErr msg => LErr msg
              | LOk ks st1 =>
                  match run_cleanups_f f ks st1 with
                  | LErr msg => LErr msg
                  | LOk _ st2 => LOk tt (l_term (ir_goto lbl) st2)
                  end
              end
          end
      | SContinue =>
          match ctx_cont ctx with
          | None => l_err loc "continue outside a loop" st0
          | Some lbl =>
              let outer := match smap_find lbl (ls_cleanup_at (fs_lscope st0)) with Some ks => ks | None => [] end in
              match leaving_cleanups outer st0 with
              | LErr msg => LErr msg
              | LOk ks st1 =>
                  match run_cleanups_f f ks st1 with
                  | LErr msg => LErr msg
                  | LOk _ st2 => LOk tt (l_term (ir_goto lbl) st2)
                  end
              end
          end
      | SReturn None =>
          let ks := cleanup_keys_st st0 in
          match run_cleanups_f f ks st0 with
          | LErr msg => LErr msg
          | LOk _ st1 => zero_ret (ctx_ret ctx) st1
          end
      | SReturn (Some expr) =>
          let ret_t := ctx_ret ctx in
          match eval_judged_rval expr ctx st0 with
          | LErr msg => LErr msg
          | LOk val0 st1 =>
              let ks := cleanup_keys_st st1 in
              match returned_cleanup_var expr ret_t ks loc st1 with
              | LErr msg => LErr msg
              | LOk _ st2 =>
                  if c_type_eqb ret_t TVoid then
                    match run_cleanups_f f ks st2 with
                    | LErr msg => LErr msg
                    | LOk _ st3 => LOk tt (l_term ir_ret_void st3)
                    end
                  else if is_abi_memory ret_t then
                    match assign_convert expr val0 ret_t loc st2 with
                    | LErr msg => LErr msg
                    | LOk (CVal v _) st3 =>
                        match abi_source ret_t v st3 with
                        | LErr msg => LErr msg
                        | LOk addr0 st4 =>
                            let rc_res :=
                              match cleanup_keys_st st4 with
                              | [] => LOk addr0 st4
                              | rks =>
                                  match l_local_slot ret_t st4 with
                                  | LErr msg => LErr msg
                                  | LOk addr st5 =>
                                      match copy_object ret_t addr0 addr st5 with
                                      | LErr msg => LErr msg
                                      | LOk _ st6 =>
                                          match run_cleanups_f f rks st6 with
                                          | LErr msg => LErr msg
                                          | LOk _ st7 => LOk addr st7
                                          end
                                      end
                                  end
                              end in
                            match rc_res with
                            | LErr msg => LErr msg
                            | LOk addr st5 => return_struct ret_t addr loc st5
                            end
                        end
                    end
                  else
                    match assign_convert expr val0 ret_t loc st2 with
                    | LErr msg => LErr msg
                    | LOk (CVal v _) st3 =>
                        match run_cleanups_f f ks st3 with
                        | LErr msg => LErr msg
                        | LOk _ st4 => LOk tt (l_term (ir_ret v) st4)
                        end
                    end
              end
          end
      | SGoto name =>
          let st1 := vm_goto_mark name loc st0 in
          let '(lbl, st2) := l_goto_label name st1 in
          let from_ks := cleanup_keys_st st2 in
          match from_ks with
          | [] => LOk tt (l_term (ir_goto lbl) st2)
          | _ =>
              match smap_find name (fs_vm_labels st2) with
              | Some to_scopes =>
                  let to_ks := cleanup_keys_of to_scopes in
                  match leaving_cleanups to_ks st2 with
                  | LErr msg => LErr msg
                  | LOk ks st3 =>
                      match run_cleanups_f f ks st3 with
                      | LErr msg => LErr msg
                      | LOk _ st4 => LOk tt (l_term (ir_goto lbl) st4)
                      end
                  end
              | None =>
                  let '(tgt, st3) := l_label st2 in
                  let prev := match smap_find name (fs_cleanup_gotos st3) with Some ps => ps | None => [] end in
                  let st4 :=
                    mkCFuncSt (fs_env st3) (fs_lscope st3) (fs_globals st3) (fs_cur st3) (fs_insts st3)
                              (fs_blocks st3) (fs_n st3) (fs_labels st3) (fs_vm_labels st3)
                              (fs_vm_gotos st3) (fs_cleanups st3)
                              (smap_add name ((tgt, from_ks) :: prev) (fs_cleanup_gotos st3))
                              (fs_computed_goto st3) (fs_cases st3) (fs_build st3) (fs_opts st3) in
                  LOk tt (l_term (ir_goto tgt) st4)
              end
          end
      | SComputedGoto e =>
          match eval_rval e ctx st0 with
          | LErr msg => LErr msg
          | LOk (CVal _ (TPtr _) as v0) st1 =>
              match convert_val v0 TULong st1 with
              | LErr msg => LErr msg
              | LOk (CVal x _) st2 =>
                  match cleanup_keys_st st2 with
                  | _ :: _ =>
                      l_err loc "goto * in the scope of a variable with a cleanup attribute is not supported" st2
                  | [] =>
                      let tgts := ls_labels_taken (fs_lscope st2) in
                      let st3 := fold_left (fun s nm => vm_goto_mark nm loc s) tgts st2 in
                      let disp_res :=
                        match fs_computed_goto st3 with
                        | Some (ldisp, slot, _) => LOk (ldisp, slot) st3
                        | None =>
                            let '(ldisp, st4) := l_label st3 in
                            match l_local_slot TULong st4 with
                            | LErr msg => LErr msg
                            | LOk slot st5 =>
                                let st6 :=
                                  mkCFuncSt (fs_env st5) (fs_lscope st5) (fs_globals st5)
                                            (fs_cur st5) (fs_insts st5) (fs_blocks st5)
                                            (fs_n st5) (fs_labels st5) (fs_vm_labels st5)
                                            (fs_vm_gotos st5) (fs_cleanups st5)
                                            (fs_cleanup_gotos st5) (Some (ldisp, slot, loc))
                                            (fs_cases st5) (fs_build st5) (fs_opts st5) in
                                LOk (ldisp, slot) st6
                            end
                        end in
                      match disp_res with
                      | LErr msg => LErr msg
                      | LOk (ldisp, slot) st4 =>
                          match store_typed TULong x slot st4 with
                          | LErr msg => LErr msg
                          | LOk _ st5 => LOk tt (l_term (ir_goto ldisp) st5)
                          end
                      end
                  end
              end
          | LOk _ st1 => l_err loc "goto * of a non-pointer" st1
          end
      | SLabel name b =>
          let st1 := vm_label_mark name st0 in
          let '(lbl, st2) := l_goto_label name st1 in
          match label_cleanups_f f name lbl st2 with
          | LErr msg => LErr msg
          | LOk _ st3 => stmt_f f b ctx (l_start lbl st3)
          end
      end
  end

with item_f (fuel : nat) (it : c_block_item) (ctx0 : c_lower_ctx) (st0 : c_func_st)
  : l_res unit :=
  match fuel with
  | O => l_err (ctx_loc ctx0) "lowering recursion limit" st0
  | S f =>
      match it with
      | BIStmt s => stmt_f f s ctx0 st0
      | BIDecl (IStaticAssert loc e _) =>
          match static_assert_check loc e (fs_env st0) with
          | TErr err => LErr (l_tr_msg loc err)
          | TOk _ => LOk tt st0
          end
      | BIDecl (IDecl loc specs inits) =>
          match decl_types specs inits (fs_env st0) with
          | TErr TENotConstant => l_err loc "array size is not a constant" st0
          | TErr err => LErr (l_tr_msg loc err)
          | TOk (decls, env1) =>
              let st1 := set_fs_env env1 st0 in
              let ctx := ctx_at ctx0 loc in
              let '(saved, st2) := l_enter_origin loc (TApp "statement" [TAtom "decl"]) st1 in
              let is_td := has_storage_spec "typedef" specs in
              let vm_td_res :=
                if is_td then
                  let fix go_td (xs : list c_init_decl) (s : c_func_st) : l_res unit :=
                    match xs with
                    | [] => LOk tt s
                    | InitDecl (Dcl (Some nm) _ _) _ :: rest =>
                        match lookup_ordinary (fs_env s) nm with
                        | Some (BTypedef t0) =>
                            if vm_type t0 then
                              match realized_f f t0 ctx s with
                              | LErr msg => LErr msg
                              | LOk ty s1 =>
                                  let s2 := set_fs_env (bind_ordinary nm (BTypedef ty) (fs_env s1)) s1 in
                                  go_td rest (vm_scope_enter ty s2)
                              end
                            else go_td rest s
                        | _ => go_td rest s
                        end
                    | _ :: rest => go_td rest s
                    end in
                  go_td inits st2
                else LOk tt st2 in
              match vm_td_res with
              | LErr msg => LErr msg
              | LOk _ st3 =>
                  let lower_one_local (d : c_decl) (s : c_func_st) : l_res unit :=
                    let nm := cd_name d in
                    let ty0 := cd_type d in
                    let stg0 := cd_storage d in
                    let oini := cd_init d in
                    let '(stg, tls) :=
                      match stg0 with
                      | StThreadLocal inner => (inner, true)
                      | _ => (stg0, false)
                      end in
                    let is_fn_or_ext :=
                      match ty0, stg with
                      | TFunc _ _ _, _ | _, StExtern => true
                      | _, _ => false
                      end in
                    if is_fn_or_ext then
                      match global_decl_g loc d (fs_env s) (fs_globals s) with
                      | TErr err => LErr (l_tr_msg loc err)
                      | TOk (env2, lg2) => LOk tt (set_fs_globals lg2 (set_fs_env env2 s))
                      end
                    else if tls && match stg with StStatic => false | _ => true end then
                      l_err loc ("_Thread_local " ++ nm ++ " at block scope must also be static or extern") s
                    else if match stg with StStatic => true | _ => false end then
                      match check_supported ty0 loc with
                      | Some msg => LErr msg
                      | None =>
                          if vla_type ty0 then
                            l_err loc (nm ++ " is a variable length array with static storage") s
                          else
                            match realized_f f ty0 ctx s with
                            | LErr msg => LErr msg
                            | LOk ty1 s1 =>
                                let '(k, env_k) := next_env_id (fs_env s1) in
                                let sym := ctx_func ctx ++ "." ++ nm ++ "." ++ decimal k in
                                match complete_array ty1 oini loc (fs_env s1) false with
                                | TErr err => LErr (l_tr_msg loc err)
                                | TOk ty =>
                                    let env2 := bind_ordinary nm (BGVar ty sym "static" tls) env_k in
                                    let lnk := if tls then GLTls "local" else GLNormal "local" in
                                    match define_global_g sym ty lnk oini loc (fs_globals s1) with
                                    | TErr err => LErr (l_tr_msg loc err)
                                    | TOk lg2b =>
                                        let lg2a := readonly_global_g tls nm sym env2 lg2b in
                                        let lg3 := data_alignment_g nm sym env2 lg2a in
                                        match static_items ty oini loc env2 lg3 with
                                        | TErr err => LErr (l_tr_msg loc err)
                                        | TOk (items, env4, lg4) =>
                                            let lg5 :=
                                              mkCLowerGlobals (lg_gdefs lg4) (lg_gdef_syms lg4)
                                                (lg_lits lg4) (lg_lit_syms lg4) (lg_lit_of lg4)
                                                (lg_func_names lg4) (lg_deferred lg4)
                                                (lg_inline_copy lg4) (lg_inline_copy_of lg4)
                                                (lg_inline_attr lg4) (lg_readonly lg4) (lg_galign lg4)
                                                (lg_qsym lg4)
                                                (smap_add sym items (lg_initialized lg4))
                                                (lg_inits lg4) in
                                            LOk tt (vm_scope_enter ty (set_fs_globals lg5 (set_fs_env env4 s1)))
                                        end
                                    end
                                end
                            end
                      end
                    else
                      match realized_f f ty0 ctx s with
                      | LErr msg => LErr msg
                      | LOk ty1 s1 =>
                          match complete_array ty1 oini loc (fs_env s1) true with
                          | TErr err => LErr (l_tr_msg loc err)
                          | TOk ty =>
                              match check_local_type ty (fs_env s1) loc nm with
                              | Some msg => LErr msg
                              | None =>
                                  let a :=
                                    match lookup_qalign (fs_env s1) nm with
                                    | Some (Some av) => av
                                    | _ => 1
                                    end in
                                  let slot_res :=
                                    if vla_type ty then
                                      match oini with
                                      | None => vla_slot ty a ctx s1
                                      | Some _ => l_err loc "a variable length array cannot be initialized" s1
                                      end
                                    else l_local_slot_min ty a s1 in
                                  match slot_res with
                                  | LErr msg => LErr msg
                                  | LOk addr s2 =>
                                      let bname := match addr with TApp _ [TAtom b] => b | _ => "" end in
                                      let s3 := l_bind_ord nm (BVar (VSNamed bname) ty) s2 in
                                      let s4 := vm_scope_enter ty s3 in
                                      match oini with
                                      | None => LOk tt s4
                                      | Some ini => init_f f addr ty ini ctx s4
                                      end
                                  end
                              end
                          end
                      end in
                  let cleanup_res :=
                    if is_td then TOk None else cleanup_attr specs in
                  match cleanup_res with
                  | TErr err => LErr (l_tr_msg loc err)
                  | TOk ocfn =>
                      let fix go_ds (ds : list c_decl) (s : c_func_st) : l_res unit :=
                        match ds with
                        | [] => LOk tt s
                        | d :: rest =>
                            match lower_one_local d s with
                            | LErr msg => LErr msg
                            | LOk _ s1 =>
                                match ocfn with
                                | Some fn =>
                                    if is_automatic_decl d then
                                      match cleanup_var_register loc (cd_name d) fn ctx s1 with
                                      | LErr msg => LErr msg
                                      | LOk _ s2 => go_ds rest s2
                                      end
                                    else go_ds rest s1
                                | None => go_ds rest s1
                                end
                            end
                        end in
                      match go_ds decls st3 with
                      | LErr msg => LErr msg
                      | LOk _ st4 => LOk tt (l_restore_origin saved st4)
                      end
                  end
              end
          end
      | BIDecl _ => LOk tt st0
      end
  end

with realized_f (fuel : nat) (ty0 : c_type) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res c_type :=
  match fuel with
  | O => l_err (ctx_loc ctx) "realized recursion limit" st0
  | S f =>
      if negb (vm_type ty0) then LOk ty0 st0
      else
        match ty0 with
        | TPtr inner =>
            match realized_f f inner ctx st0 with
            | LErr msg => LErr msg
            | LOk t st1 => LOk (TPtr t) st1
            end
        | TArray _ ALVlaStar =>
            l_err (ctx_loc ctx) "[*] is allowed only in a function prototype" st0
        | TArray inner (ALVlaExpr e) =>
            let s1 := set_fs_env (expression_tags e (fs_env st0)) st0 in
            match elaborate_loc e (fs_env s1) (ctx_loc ctx) with
            | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
            | TOk None => l_err (ctx_loc ctx) "cannot type array size" s1
            | TOk (Some n) =>
                match lower_f f (value_node n) ctx s1 with
                | LErr msg => LErr msg
                | LOk (CVal _ lt as v0) st1 =>
                    if int_type lt then
                      match convert_val v0 TLong st1 with
                      | LErr msg => LErr msg
                      | LOk (CVal v _) st2 =>
                          match realized_f f inner ctx st2 with
                          | LErr msg => LErr msg
                          | LOk t st3 => LOk (TArray t (ALDyn (term_to_dyn_str v))) st3
                          end
                      end
                    else l_err (ctx_loc ctx) "array size is not an integer" st1
                end
            end
        | TArray inner len =>
            match realized_f f inner ctx st0 with
            | LErr msg => LErr msg
            | LOk t st1 => LOk (TArray t len) st1
            end
        | TFunc r0 ps v =>
            match realized_f f r0 ctx st0 with
            | LErr msg => LErr msg
            | LOk r st1 => LOk (TFunc r ps v) st1
            end
        | _ => LOk ty0 st0
        end
  end

with init_f (fuel : nat) (addr : term) (ty : c_type) (ini : c_init)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res unit :=
  match fuel with
  | O => l_err (ctx_loc ctx) "initializer recursion limit" st0
  | S f =>
      let loc := ctx_loc ctx in
      match init_leaves ty ini (fs_env st0) true loc with
      | TErr err => LErr (l_tr_msg loc err)
      | TOk lvs =>
          let store_one (lv : init_leaf) (s : c_func_st) : l_res unit :=
            match lv with
            | ILZero off zty =>
                let '(p, s1) := l_offset addr off s in
                zero_object p zty s1
            | ILVal off vty n =>
                let '(p, s1) := l_offset addr off s in
                match store_width vty with
                | Some w => LOk tt (l_emit (ir_store w (ir_const n) p) s1)
                | None => l_err loc "invalid scalar store in initializer" s1
                end
            | ILVals off vty ns =>
                match int_info vty, store_width vty with
                | Some (esz, _), Some w =>
                    let fix go_vals (xs : list Z) (cur_off : Z) (st : c_func_st) : l_res unit :=
                      match xs with
                      | [] => LOk tt st
                      | n :: rest =>
                          let '(p, st1) := l_offset addr cur_off st in
                          go_vals rest (cur_off + esz) (l_emit (ir_store w (ir_const n) p) st1)
                      end in
                    go_vals ns off s
                | _, _ => l_err loc "invalid array store in initializer" s
                end
            | ILExpr off ety expr =>
                let '(p, s1) := l_offset addr off s in
                let s2 := set_fs_env (expression_tags expr (fs_env s1)) s1 in
                match elaborate_loc expr (fs_env s2) loc with
                | TErr err => LErr (l_tr_msg loc err)
                | TOk None => l_err loc "cannot type initializer expression" s2
                | TOk (Some n) =>
                    match lower_f f (value_node n) ctx s2 with
                    | LErr msg => LErr msg
                    | LOk v0 s3 =>
                        match assign_convert expr v0 ety loc s3 with
                        | LErr msg => LErr msg
                        | LOk (CVal v _) s4 =>
                            let is_unaligned_null_ptr :=
                              term_eqb v (ir_const 0)
                              && negb (Z.eqb (Z.modulo off 8) 0)
                              && match unqualified ety with TPtr _ => true | _ => false end in
                            if is_unaligned_null_ptr then
                              LOk tt (l_emit (ir_store "l" (ir_const 0) p) s4)
                            else store_typed ety v p s4
                        end
                    end
                end
            | ILBits off bty pos w expr =>
                let '(p, s1) := l_offset addr off s in
                let s2 := set_fs_env (expression_tags expr (fs_env s1)) s1 in
                match elaborate_loc expr (fs_env s2) loc with
                | TErr err => LErr (l_tr_msg loc err)
                | TOk None => l_err loc "cannot type bit-field initializer" s2
                | TOk (Some n) =>
                    match lower_f f (value_node n) ctx s2 with
                    | LErr msg => LErr msg
                    | LOk v0 s3 =>
                        match assign_convert expr v0 bty loc s3 with
                        | LErr msg => LErr msg
                        | LOk v s4 =>
                            match place_write (PBits p bty pos w) v ctx s4 with
                            | LErr msg => LErr msg
                            | LOk _ s5 => LOk tt s5
                            end
                        end
                    end
                end
            end in
          let fix go_lvs (xs : list init_leaf) (s : c_func_st) : l_res unit :=
            match xs with
            | [] => LOk tt s
            | lv :: rest =>
                match store_one lv s with
                | LErr msg => LErr msg
                | LOk _ s1 => go_lvs rest s1
                end
            end in
          go_lvs lvs st0
      end
  end

with call_args_f (fuel : nat) (xargs : list c_typed_node) (ptys : list c_type)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list pad_item) :=
  match fuel with
  | O => l_err (ctx_loc ctx) "call_args recursion limit" st0
  | S f =>
      let loc := ctx_loc ctx in
      let fix go (xs : list c_typed_node) (ps : list c_type) (s : c_func_st) : l_res (list pad_item) :=
        match xs with
        | [] => LOk [] s
        | xa :: rx =>
            match ps with
            | TAtomic s0 p0 :: _ =>
                l_err loc ("parameter of type " ++ c_type_diag_str (TAtomic s0 p0) ++ " is not supported yet") s
            | pty :: rp =>
                if is_abi_memory pty then
                  match lower_f f xa ctx s with
                  | LErr msg => LErr msg
                  | LOk v0 s1 =>
                      let v_res :=
                        match transparent_argument pty xa (fs_env s1) with
                        | Some mem_t =>
                            match l_local_slot pty s1 with
                            | LErr msg => LErr msg
                            | LOk v s2 =>
                                match converted_val v0 mem_t s2 with
                                | LErr msg => LErr msg
                                | LOk (CVal mv _) s3 =>
                                    match store_typed mem_t mv v s3 with
                                    | LErr msg => LErr msg
                                    | LOk _ s4 => LOk v s4
                                    end
                                end
                            end
                        | None =>
                            match converted_val v0 pty s1 with
                            | LErr msg => LErr msg
                            | LOk (CVal v _) s2 => LOk v s2
                            end
                        end in
                      match v_res with
                      | LErr msg => LErr msg
                      | LOk v s2 =>
                          match abi_source pty v s2 with
                          | LErr msg => LErr msg
                          | LOk src s3 =>
                              match arg_words pty (fs_env s3) loc with
                              | TErr err => LErr (l_tr_msg loc err)
                              | TOk ebs =>
                                  let '(ws, s4) := load_words ebs src s3 in
                                  let args00 :=
                                    map (fun p => ir_arg (eb_class (fst p)) (snd p)) (combine ebs ws) in
                                  let args0 := pad16_mark pty (fs_env s4) args00 in
                                  match go rx rp s4 with
                                  | LErr msg => LErr msg
                                  | LOk args1 s5 => LOk (app args0 args1) s5
                                  end
                              end
                          end
                      end
                  end
                else
                  match lower_f f xa ctx s with
                  | LErr msg => LErr msg
                  | LOk v0 s1 =>
                      match converted_val v0 pty s1 with
                      | LErr msg => LErr msg
                      | LOk (CVal v ty) s2 =>
                          match type_class ty with
                          | None => l_err loc ("unsupported argument type " ++ c_type_diag_str ty) s2
                          | Some cls =>
                              match go rx rp s2 with
                              | LErr msg => LErr msg
                              | LOk args1 s3 => LOk (PITerm (ir_arg cls v) :: args1) s3
                              end
                          end
                      end
                  end
            | [] =>
                match lower_f f xa ctx s with
                | LErr msg => LErr msg
                | LOk (CVal v0 ty0 as val0) s1 =>
                    if is_abi_memory ty0 then
                      match abi_source ty0 v0 s1 with
                      | LErr msg => LErr msg
                      | LOk src s2 =>
                          match holds_vec ty0 (fs_env s2) with
                          | Some k =>
                              l_err loc ("passing " ++ k ++ " to a variadic or unprototyped function is not supported") s2
                          | None =>
                              match variadic_words ty0 (fs_env s2) loc with
                              | TErr err => LErr (l_tr_msg loc err)
                              | TOk ebs =>
                                  let '(ws, s3) := load_words ebs src s2 in
                                  let args00 :=
                                    map (fun p => ir_arg (eb_class (fst p)) (snd p)) (combine ebs ws) in
                                  let args0 := pad16_mark ty0 (fs_env s3) args00 in
                                  match go rx [] s3 with
                                  | LErr msg => LErr msg
                                  | LOk args1 s4 => LOk (app args0 args1) s4
                                  end
                              end
                          end
                      end
                    else
                      let arg_res :=
                        if arithmetic_type ty0 then
                          let ty := default_promotion ty0 in
                          match convert_val val0 ty s1 with
                          | LErr msg => LErr msg
                          | LOk (CVal v _) s2 => LOk (v, ty) s2
                          end
                        else
                          match ty0 with
                          | TPtr _ => LOk (v0, ty0) s1
                          | _ => l_err loc ("passing " ++ c_type_diag_str ty0 ++ " to a variadic or unprototyped function is not supported") s1
                          end in
                      match arg_res with
                      | LErr msg => LErr msg
                      | LOk (v, ty) s2 =>
                          match type_class ty with
                          | None => l_err loc ("unsupported argument type " ++ c_type_diag_str ty) s2
                          | Some cls =>
                              match go rx [] s2 with
                              | LErr msg => LErr msg
                              | LOk args1 s3 => LOk (PITerm (ir_arg cls v) :: args1) s3
                              end
                          end
                      end
                end
            end
        end in
      go xargs ptys st0
  end

with run_cleanups_f (fuel : nat) (ks : list Z) (st0 : c_func_st) : l_res unit :=
  match fuel with
  | O => LErr "cleanup recursion limit"
  | S f =>
      match fs_cur st0 with
      | None => LOk tt st0
      | Some _ =>
          let fix go (xs : list Z) (s : c_func_st) : l_res unit :=
            match xs with
            | [] => LOk tt s
            | k :: rest =>
                match fs_cur s with
                | None => LOk tt s
                | Some _ =>
                    match smap_find (decimal k) (fs_cleanups s) with
                    | None => go rest s
                    | Some ci =>
                        let env1 :=
                          fold_left (fun e p => bind_ordinary (fst p) (snd p) e) (ci_binds ci) (fs_env s) in
                        let s1 := set_fs_env env1 s in
                        match lower_f f (ci_node ci) (ci_ctx ci) s1 with
                        | LErr msg => LErr msg
                        | LOk _ s2 => go rest s2
                        end
                    end
                end
            end in
          go ks st0
      end
  end

with label_cleanups_f (fuel : nat) (name lbl : string) (st0 : c_func_st) : l_res unit :=
  match fuel with
  | O => LErr "label_cleanups recursion limit"
  | S f =>
      match smap_find name (fs_cleanup_gotos st0) with
      | None => LOk tt st0
      | Some ps =>
          let st1 := l_term (ir_goto lbl) st0 in
          let to_ks := cleanup_keys_st st1 in
          let fix go (xs : list (string * list Z)) (s : c_func_st) : l_res unit :=
            match xs with
            | [] => LOk tt s
            | (t, from_ks) :: rest =>
                let s1 := l_start t s in
                let ks := match list_Z_strip_suffix to_ks from_ks with Some k => k | None => [] end in
                match run_cleanups_f f ks s1 with
                | LErr msg => LErr msg
                | LOk _ s2 => go rest (l_term (ir_goto lbl) s2)
                end
            end in
          go ps st1
      end
  end.

Definition lower_fuel : nat := Z.to_nat 4096.

(** ## Function lowering and provenance context assembly *)

Definition param_names_of (dcl : c_dcl_type) : list (option string) :=
  match dcl with
  | DTFunc _ (PParams ps _) => map (fun p => match p with Param _ (Dcl nm _ _) => nm end) ps
  | _ => []
  end.

Definition param_mins_of (dcl : c_dcl_type) (env : c_type_env) : list Z :=
  match dcl with
  | DTFunc _ (PParams ps _) =>
      map (fun p =>
             match p with
             | Param specs (Dcl _ DTBase _) =>
                 match inherited_alignment specs DTBase env with
                 | Some m => m
                 | None => 1
                 end
             | _ => 1
             end) ps
  | _ => []
  end.

Definition sret_param (ret_t : c_type) (st0 : c_func_st) : list term * c_func_st :=
  if is_memtype ret_t then
    match ret_shape ret_t (fs_env st0) unknown_loc with
    | TOk RetSret =>
        let '(p, st1) := l_fresh st0 in
        let ls := fs_lscope st1 in
        let ls1 :=
          mkCLowerScope (ls_vm_scopes ls) (ls_vm_switch ls) (ls_cleanup_at ls)
                        (ls_labels_taken ls) (ls_va_args ls) (Some p) in
        ([ir_param "p" p], set_fs_lscope ls1 st1)
    | _ => ([], st0)
    end
  else ([], st0).

Fixpoint fresh_params (ebs : list abi_eb) (st0 : c_func_st)
  : list term * list term * c_func_st :=
  match ebs with
  | [] => ([], [], st0)
  | eb :: rest =>
      let '(p, st1) := l_fresh st0 in
      let '(ps, vs, st2) := fresh_params rest st1 in
      (ir_param (eb_class eb) p :: ps, p :: vs, st2)
  end.

Fixpoint lower_params (names : list (option string)) (mins : list Z)
  (tys : list c_type) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list pad_item) :=
  match names, mins, tys with
  | [], _, [] => LOk [] st0
  | onm :: rns, mn :: rms, ty :: rts =>
      let loc := ctx_loc ctx in
      if is_abi_memory ty then
        match arg_words ty (fs_env st0) loc with
        | TErr err => LErr (l_tr_msg loc err)
        | TOk ebs =>
            let '(ps0, vs, st1) := fresh_params ebs st0 in
            let store_res :=
              match onm with
              | None => LOk tt st1
              | Some nm =>
                  match l_local_slot_min ty mn st1 with
                  | LErr msg => LErr msg
                  | LOk addr st2 =>
                      let bname := match addr with TApp _ [TAtom b] => b | _ => "" end in
                      let st3 := l_bind_ord nm (BVar (VSNamed bname) ty) st2 in
                      let st4 := l_name_values vs addr "piece" st3 in
                      LOk tt (store_words ebs vs addr st4)
                  end
              end in
            match store_res with
            | LErr msg => LErr msg
            | LOk _ st2 =>
                match lower_params rns rms rts ctx st2 with
                | LErr msg => LErr msg
                | LOk ps1 st3 =>
                    let ps2 := pad16_mark ty (fs_env st3) ps0 in
                    LOk (app ps2 ps1) st3
                end
            end
        end
      else
        match check_supported ty loc with
        | Some msg => LErr msg
        | None =>
            match type_class ty with
            | None => l_err loc ("parameter of type " ++ c_type_diag_str ty ++ " is not supported yet") st0
            | Some cls =>
                let '(p, st1) := l_fresh st0 in
                let store_res :=
                  match onm with
                  | None => LOk tt st1
                  | Some nm =>
                      match l_local_slot_min ty mn st1 with
                      | LErr msg => LErr msg
                      | LOk addr st2 =>
                          let bname := match addr with TApp _ [TAtom b] => b | _ => "" end in
                          let st3 := l_bind_ord nm (BVar (VSNamed bname) ty) st2 in
                          let st4 := l_name_value p addr "value" st3 in
                          store_typed ty p addr st4
                      end
                  end in
                match store_res with
                | LErr msg => LErr msg
                | LOk _ st2 =>
                    match lower_params rns rms rts ctx st2 with
                    | LErr msg => LErr msg
                    | LOk ps1 st3 => LOk (PITerm (ir_param cls p) :: ps1) st3
                    end
                end
            end
        end
  | _, _, _ => LOk [] st0
  end.

Definition variadic_entry (variadic : bool) (ret_t : c_type) (ptys : list c_type)
  (sret ps0 : list term) (st0 : c_func_st) : c_func_st :=
  let nw := Z.of_nat (length (app sret ps0)) in
  let off := 8 * nw in
  if variadic then
    let ls := fs_lscope st0 in
    let ls1 :=
      mkCLowerScope (ls_vm_scopes ls) (ls_vm_switch ls) (ls_cleanup_at ls)
                    (ls_labels_taken ls) (Some (ir_tmp "va_args")) (ls_sret ls) in
    let st1 := set_fs_lscope ls1 st0 in
    l_emit (ir_let (ir_tmp "va_args") "p" (TAtom "va_args") [ir_const off]) st1
  else
    let env := fs_env st0 in
    let need_va :=
      existsb (fun ty => is_abi_memory ty && generic_only_type ty env) ptys
      || (is_memtype ret_t && float_pair_type ret_t env)
      || x87_type ret_t env
      || (16 <? nw) in
    if need_va then
      l_emit (ir_let (ir_tmp "va_args") "p" (TAtom "va_args") [ir_const off]) st0
    else st0.

Fixpoint vm_params_lower (names : list (option string)) (tys : list c_type)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res unit :=
  match names, tys with
  | onm :: rns, ty0 :: rts =>
      match onm with
      | Some nm =>
          if vm_type ty0 then
            match lookup_ordinary (fs_env st0) nm with
            | Some (BVar slot _) =>
                match realized_f lower_fuel ty0 ctx st0 with
                | LErr msg => LErr msg
                | LOk ty st1 =>
                    let st2 := set_fs_env (bind_ordinary nm (BVar slot ty) (fs_env st1)) st1 in
                    vm_params_lower rns rts ctx st2
                end
            | _ => vm_params_lower rns rts ctx st0
            end
          else vm_params_lower rns rts ctx st0
      | None => vm_params_lower rns rts ctx st0
      end
  | _, _ => LOk tt st0
  end.

Definition inst_defs_of (inst : term) : list string :=
  match inst with
  | TApp f [TApp tf [TAtom t]; _; _; _] =>
      if ((f == "let") || (f == "flight")) && (tf == "tmp") then [t] else []
  | TApp f [TApp tf [TAtom t]; _; _] =>
      if (f == "local_load") && (tf == "tmp") then [t] else []
  | TApp f [TApp rf [TApp tf [TAtom t]; _]; _; _] =>
      if ((f == "call") || (f == "raw_call")) && (rf == "result") && (tf == "tmp") then [t] else []
  | TApp f [TApp tup [TList rs]; _; _] =>
      if (f == "call") && (tup == "tuple") then
        flat_map (fun r =>
                    match r with
                    | TApp rf [TApp tf [TAtom t]; _] =>
                        if (rf == "result") && (tf == "tmp") then [t] else []
                    | _ => []
                    end) rs
      else []
  | TApp f [TApp tf [TAtom t]; _] =>
      if (f == "uses") && (tf == "tmp") then [t] else []
  | TApp f [_; _; TList outs] =>
      if f == "asm_fixed" then
        flat_map (fun o =>
                    match o with
                    | TApp ef [_; TApp tf [TAtom t]] =>
                        if (ef == "-") && (tf == "tmp") then [t] else []
                    | _ => []
                    end) outs
      else []
  | _ => []
  end.

Definition is_hint_term (r : term) : bool :=
  match r with TApp f [_; _] => f == "hint" | _ => false end.

Definition data_return_block (blk : closed_block) : closed_block :=
  let '(lbl, phis, insts, (os, jmp)) := blk in
  if term_eqb jmp ir_ret_void then (lbl, phis, insts, (os, ir_ret (ir_const 0)))
  else blk.

Definition lower_function (opts : c_lower_opts) (loc : c_loc) (name : string)
  (ty : c_type) (dcl : c_dcl_type) (body : c_stmt)
  (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (list term * c_type_env * c_lower_globals) :=
  match ty with
  | TFunc ret_t ops variadic =>
      let bad_ret :=
        match holds_vec ret_t env0 with
        | Some k => if k == "a vector" then None else Some k
        | None => None
        end in
      match bad_ret with
      | Some k => sema_err loc ("a function returning " ++ k ++ ", or an aggregate holding one, is not supported")
      | None =>
          match lookup_ordinary env0 name with
          | Some (BFn _ sym lnk) =>
              let ptys := match ops with Some ps => ps | None => [] end in
              let ret_cls_res :=
                if zreturn_body body env0 then
                  if c_type_eqb ret_t TVoid then TOk (TAtom "data")
                  else sema_err loc "zreturn in a function that does not return void is not supported"
                else ret_class_of loc ret_t env0 in
              match ret_cls_res with
              | TErr err => TErr err
              | TOk ret_cls =>
                  let pnames := param_names_of dcl in
                  let pmins := param_mins_of dcl env0 in
                  match statement_expression_jumps body loc with
                  | TErr err => TErr err
                  | TOk _ =>
                      let sc0 := te_scope env0 in
                      let func_env :=
                        with_scope env0
                          (mkCScope (sc_ords sc0) (sc_qtypes sc0) (sc_qalign sc0) (sc_talign sc0)
                                    (sc_cval sc0) (sc_labels sc0) (sc_tags sc0)
                                    (sc_member_base sc0) (Some name)) in
                      let param_env0 := reflect_params dcl ptys func_env in
                      let '(param_env, taken) := label_values body param_env0 in
                      let ctx := mkCLowerCtx name ret_t None None loc in
                      let src_loc := source_location_term loc in
                      let orig0 := TApp "origin" [Term.TInt 0; src_loc; TApp "statement" [TAtom "function"]; TList []] in
                      let bld0 := mkCBuildSt [] [0] 1 [orig0] nm_empty nm_empty src_loc in
                      let ls0 := mkCLowerScope [] [] smap_empty taken None None in
                      let st0 :=
                        mkCFuncSt param_env ls0 lg0 (Some ("start", [])) [] [] 0
                                  smap_empty smap_empty [] smap_empty smap_empty None [] bld0 opts in
                      let '(sret_ps, st1) := sret_param ret_t st0 in
                      match lower_params pnames pmins ptys ctx st1 with
                      | LErr msg => TErr (TESema msg)
                      | LOk ps00 st2 =>
                          let nsret := Z.of_nat (length sret_ps) in
                          let '(ps0, st3) := pad_params_aux ps00 nsret [] st2 in
                          let st4 := variadic_entry variadic ret_t ptys sret_ps ps0 st3 in
                          match vm_params_lower pnames ptys ctx st4 with
                          | LErr msg => TErr (TESema msg)
                          | LOk _ st5 =>
                              match stmt_f lower_fuel body ctx st5 with
                              | LErr msg => TErr (TESema msg)
                              | LOk _ st6 =>
                                  match fall_off ret_t st6 with
                                  | LErr msg => TErr (TESema msg)
                                  | LOk _ st7 =>
                                      let st8 := computed_dispatch st7 in
                                      match vm_jumps_check st8 with
                                      | LErr msg => TErr (TESema msg)
                                      | LOk _ st9 =>
                                          let params := app sret_ps ps0 in
                                          let env_end := with_scope (fs_env st9) sc0 in
                                          let lg_end := fs_globals st9 in
                                          let rev_blks :=
                                            if term_eqb ret_cls (TAtom "data") then
                                              map data_return_block (fs_blocks st9)
                                            else fs_blocks st9 in
                                          let blks0 := rev rev_blks in
                                          let allocs := rev (bs_rev_allocs (fs_build st9)) in
                                          let blks_with_allocs :=
                                            match blks0 with
                                            | (l0, ph0, is0, j0) :: rest =>
                                                (l0, ph0, app allocs is0, j0) :: rest
                                            | [] => []
                                            end in
                                          let hints := bs_hints (fs_build st9) in
                                          let hint_of (t : string) : term :=
                                            match nm_find (TAtom t) hints with
                                            | Some h => h
                                            | None => TAtom "none"
                                            end in
                                          let os_list (os : list Z) : term := TList (map Term.TInt os) in
                                          let param_vals :=
                                            flat_map (fun p =>
                                                        match p with
                                                        | TApp pf [_; TApp tf [TAtom t]] =>
                                                            if (pf == "param") && (tf == "tmp") then
                                                              [TApp "value" [TAtom t; hint_of t; os_list [0]]]
                                                            else []
                                                        | _ => []
                                                        end) params in
                                          let fix proc_blocks (bs : list closed_block)
                                            (ir_acc : list term) (val_acc : list term) (site_acc : list term)
                                            : list term * list term * list term :=
                                            match bs with
                                            | [] => (rev ir_acc, rev val_acc, rev site_acc)
                                            | (lbl, phis, insts, (jos, jmp)) :: rest =>
                                                let ir_phis := map snd phis in
                                                let ir_insts := map snd insts in
                                                let blk_t := ir_block lbl ir_phis ir_insts jmp in
                                                let '(p_vals, p_sites) :=
                                                  fold_left
                                                    (fun acc p =>
                                                       let '(va, sa) := acc in
                                                       let '(os, pt) := p in
                                                       match pt with
                                                       | TApp pf [TApp tf [TAtom t]; _; _] =>
                                                           if (pf == "phi") && (tf == "tmp") then
                                                             let s_t := TApp "site" [TApp "phi" [TAtom t]; os_list os] in
                                                             let v_t := TApp "value" [TAtom t; hint_of t; os_list os] in
                                                             (v_t :: va, s_t :: sa)
                                                           else (va, sa)
                                                       | _ => (va, sa)
                                                       end) phis (val_acc, site_acc) in
                                                let '(_, i_vals, i_sites) :=
                                                  fold_left
                                                    (fun acc p =>
                                                       let '(idx, va, sa) := acc in
                                                       let '(os, ins) := p in
                                                       let s_t := TApp "site" [TApp "inst" [TAtom lbl; Term.TInt idx]; os_list os] in
                                                       let va1 :=
                                                         fold_left (fun v_a t =>
                                                                      TApp "value" [TAtom t; hint_of t; os_list os] :: v_a)
                                                                   (inst_defs_of ins) va in
                                                       (idx + 1, va1, s_t :: sa))
                                                    insts (0, p_vals, p_sites) in
                                                let j_site := TApp "site" [TApp "jump" [TAtom lbl]; os_list jos] in
                                                proc_blocks rest (blk_t :: ir_acc) i_vals (j_site :: i_sites)
                                            end in
                                          let '(ir_blks, blk_vals, sites) := proc_blocks blks_with_allocs [] [] [] in
                                          let raw_recs := rev (bs_rev_records (fs_build st9)) in
                                          let origins := filter (fun r => negb (is_hint_term r)) raw_recs in
                                          let records := app origins (app (app param_vals blk_vals) sites) in
                                          let fn_t := ir_func sym lnk ret_cls params ir_blks in
                                          let ctx_t := ir_context sym records in
                                          TOk ([fn_t; ctx_t], env_end, lg_end)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          | _ => sema_err loc ("undeclared function " ++ name)
          end
      end
  | _ => sema_err loc (name ++ " is not a function")
  end.

(** ## Top-level declarations, weak symbols, aliases, and deferred inlines *)

Definition alias_kind_of (ty : c_type) : string :=
  match ty with TFunc _ _ _ => "func" | _ => "data" end.

Definition make_pending_alias (name lnk target kind : string) (loc : c_loc) : term :=
  TApp "alias4" [TAtom name; TAtom lnk; TAtom target; TAtom kind; TAtom (loc_to_string loc)].

Definition weakref_item (all : list c_item) (it : c_item) : c_tr c_item :=
  match it with
  | IDecl loc specs0 [InitDecl (Dcl (Some n) syn None) None] =>
      match weakref_target specs0 with
      | Some t =>
          if has_storage_spec "static" specs0 then
            let specs1 := filter (fun sp => negb (weakref_spec sp)) specs0 in
            let decl_t :=
              existsb (fun x =>
                         match x with
                         | IDecl _ _ is_ =>
                             existsb (fun d => match d with InitDecl (Dcl (Some nm) _ _) _ => nm == t | _ => false end) is_
                         | IFundef _ _ (Dcl (Some nm) _ _) _ => nm == t
                         | _ => false
                         end) all in
            let weak_sp :=
              if decl_t then [] else [SpAttr [AGroup [ATok (TId "weak")]]] in
            let specs := app (SpStorage "extern" :: weak_sp) specs1 in
            TOk (IDecl loc specs [InitDecl (Dcl (Some n) syn (Some t)) None])
          else sema_err loc ("weakref declaration of " ++ n ++ " must have internal linkage")
      | None => TOk it
      end
  | _ => TOk it
  end.

Record pending_weak_alias : Type := mkPendingWeakAlias {
  pwa_loc : c_loc;
  pwa_specs : list c_spec;
  pwa_inits : list c_init_decl;
  pwa_target : string;
}.

Definition weak_aliases (all : list c_item) : c_tr (list c_item * list pending_weak_alias) :=
  let fix go (xs : list c_item) (iacc : list c_item) (aacc : list pending_weak_alias) :=
    match xs with
    | [] => TOk (rev iacc, rev aacc)
    | IDecl loc specs inits :: rest =>
        if weak_attr specs then
          match alias_target specs with
          | Some tgt =>
              let specs0 := filter (fun sp => negb (alias_attr_spec sp)) specs in
              let specs1 := extern_specs specs0 in
              go rest (IDecl loc specs1 inits :: iacc)
                      (mkPendingWeakAlias loc specs1 inits tgt :: aacc)
          | None => go rest (IDecl loc specs inits :: iacc) aacc
          end
        else go rest (IDecl loc specs inits :: iacc) aacc
    | IPragmaWeak loc name (Some tgt) :: rest =>
        let found :=
          find (fun x =>
                  match x with
                  | IDecl _ _ [InitDecl (Dcl (Some nm) _ _) None] => nm == name
                  | _ => false
                  end) all in
        match found with
        | Some (IDecl _ specs0 inits) =>
            let specs1 := filter (fun sp => negb (alias_attr_spec sp)) specs0 in
            let specs := extern_specs specs1 in
            go rest iacc (mkPendingWeakAlias loc specs inits tgt :: aacc)
        | _ => sema_err loc ("#pragma weak " ++ name ++ " = " ++ tgt ++ " needs a declaration of " ++ name)
        end
    | it :: rest => go rest (it :: iacc) aacc
    end in
  go all [] [].

Definition weak_alias_item (a : pending_weak_alias) (env0 : c_type_env)
  : c_tr (term * c_type_env) :=
  match pwa_inits a with
  | [InitDecl (Dcl (Some name) _ None) None] =>
      match decl_types (pwa_specs a) (pwa_inits a) env0 with
      | TErr err => TErr err
      | TOk ([d], env1) =>
          TOk (make_pending_alias name "weak" (pwa_target a) (alias_kind_of (cd_type d)) (pwa_loc a), env1)
      | TOk _ => sema_err (pwa_loc a) "alias is supported only for one declarator"
      end
  | _ => sema_err (pwa_loc a) "alias is supported only for one declarator"
  end.

Definition external_inline_names (items : list c_item) : list string :=
  flat_map
    (fun it =>
       match it with
       | IDecl _ specs inits =>
           if negb (has_storage_spec "typedef" specs)
              && (has_storage_spec "extern" specs || negb (has_fspec "inline" specs)) then
             flat_map (fun d => match d with InitDecl (Dcl (Some nm) _ _) _ => [nm] | _ => [] end) inits
           else []
       | IFundef _ specs (Dcl (Some nm) _ _) _ =>
           if negb (has_storage_spec "typedef" specs)
              && (has_storage_spec "extern" specs || negb (has_fspec "inline" specs)) then [nm]
           else []
       | _ => []
       end)
    items.

Definition add_inline_attr_g (sym : string) (lg : c_lower_globals) : c_lower_globals :=
  mkCLowerGlobals (lg_gdefs lg) (lg_gdef_syms lg) (lg_lits lg) (lg_lit_syms lg)
                  (lg_lit_of lg) (lg_func_names lg) (lg_deferred lg)
                  (lg_inline_copy lg) (lg_inline_copy_of lg)
                  (if str_mem sym (lg_inline_attr lg) then lg_inline_attr lg else sym :: lg_inline_attr lg)
                  (lg_readonly lg) (lg_galign lg) (lg_qsym lg) (lg_initialized lg) (lg_inits lg).

Definition put_deferred_g (sym : string) (df : deferred_fn) (lg : c_lower_globals) : c_lower_globals :=
  mkCLowerGlobals (lg_gdefs lg) (lg_gdef_syms lg) (lg_lits lg) (lg_lit_syms lg)
                  (lg_lit_of lg) (lg_func_names lg)
                  (smap_add sym df (lg_deferred lg))
                  (lg_inline_copy lg) (lg_inline_copy_of lg) (lg_inline_attr lg)
                  (lg_readonly lg) (lg_galign lg) (lg_qsym lg) (lg_initialized lg) (lg_inits lg).

Definition local_inline_copy_g (kind : string) (loc : c_loc) (name : string)
  (ty : c_type) (dcl : c_dcl_type) (body : c_stmt) (env : c_type_env)
  (lg0 : c_lower_globals) : c_lower_globals :=
  match lookup_ordinary env name with
  | Some (BFn _ sym _) =>
      let local_s := sym ++ "." ++ kind in
      let df := mkDeferredFn loc name ty dcl body (te_scope env) in
      let lg1 :=
        mkCLowerGlobals (lg_gdefs lg0) (lg_gdef_syms lg0) (lg_lits lg0) (lg_lit_syms lg0)
                        (lg_lit_of lg0) (lg_func_names lg0)
                        (smap_add local_s df (lg_deferred lg0))
                        (smap_add sym local_s (lg_inline_copy lg0))
                        (smap_add local_s sym (lg_inline_copy_of lg0))
                        (lg_inline_attr lg0) (lg_readonly lg0) (lg_galign lg0)
                        (lg_qsym lg0) (lg_initialized lg0) (lg_inits lg0) in
      if kind == "always_inline" then add_inline_attr_g local_s lg1 else lg1
  | _ => lg0
  end.

Definition init_decl_g (loc : c_loc) (specs : list c_spec) (d : c_decl)
  (env0 : c_type_env) (lg0 : c_lower_globals) : c_tr (c_type_env * c_lower_globals) :=
  match cd_type d with
  | TFunc _ _ _ =>
      let ia := init_attrs specs in
      match ia with
      | [] => TOk (env0, lg0)
      | _ =>
          match lookup_ordinary env0 (cd_name d) with
          | Some (BFn _ sym _) =>
              let fix go (xs : list (string * option (option Z))) (e : c_type_env) (lg : c_lower_globals) :=
                match xs with
                | [] => TOk (e, lg)
                | (kind, None) :: _ =>
                    sema_err loc ("the " ++ kind ++ " priority of " ++ sym ++ " is not an integer from 0 to 65535")
                | (kind, Some oprio) :: rest =>
                    let '(n, e1) := next_env_id e in
                    let inits1 :=
                      mkInitEntry n kind sym oprio
                      :: filter (fun ie => negb ((ie_kind ie == kind) && (ie_sym ie == sym))) (lg_inits lg) in
                    let lg1 :=
                      mkCLowerGlobals (lg_gdefs lg) (lg_gdef_syms lg) (lg_lits lg) (lg_lit_syms lg)
                                      (lg_lit_of lg) (lg_func_names lg) (lg_deferred lg)
                                      (lg_inline_copy lg) (lg_inline_copy_of lg) (lg_inline_attr lg)
                                      (lg_readonly lg) (lg_galign lg) (lg_qsym lg) (lg_initialized lg)
                                      inits1 in
                    go rest e1 lg1
                end in
              go ia env0 lg0
          | _ => TOk (env0, lg0)
          end
      end
  | _ => TOk (env0, lg0)
  end.

Definition is_overload_skip (specs : list c_spec) (dcl : c_dcl) (env : c_type_env) : bool :=
  if overloadable_attr specs then
    match dcl with
    | Dcl (Some name) _ _ =>
        match lookup_ordinary env name with
        | Some (BFn vis _ _) =>
            match decl_types specs [InitDecl dcl None] env with
            | TOk ([d], _) => negb (compatible_type vis (cd_type d) (Some env))
            | _ => false
            end
        | _ => false
        end
    | _ => false
    end
  else false.

Definition overload_wrapper_info (specs : list c_spec) (dcl : c_dcl) (env : c_type_env)
  : option (string * c_type) :=
  if overloadable_attr specs then
    match dcl with
    | Dcl (Some name) _ _ =>
        match lookup_ordinary env name with
        | Some (BFn vis sym lnk) =>
            if negb (lnk == "local") then
              match decl_types specs [InitDecl dcl None] env with
              | TOk ([d], _) =>
                  match cd_storage d with
                  | StStatic =>
                      if compatible_type vis (cd_type d) (Some env) then Some (sym, cd_type d) else None
                  | _ => None
                  end
              | _ => None
              end
            else None
        | _ => None
        end
    | _ => None
    end
  else None.

Definition alias_decl_g (loc : c_loc) (specs : list c_spec) (inits : list c_init_decl)
  (target : string) (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (list term * c_type_env * c_lower_globals) :=
  match inits with
  | [InitDecl (Dcl (Some name) dcl_ty None) None] =>
      let specs1 := extern_specs specs in
      match decl_types specs1 [InitDecl (Dcl (Some name) dcl_ty (Some target)) None] env0 with
      | TErr err => TErr err
      | TOk ([d], env1) =>
          match global_decl_g loc d env1 lg0 with
          | TErr err => TErr err
          | TOk (env2, lg2) =>
              let items :=
                match cd_storage d with
                | StStatic => []
                | _ => [make_pending_alias name "export" target (alias_kind_of (cd_type d)) loc]
                end in
              TOk (items, env2, lg2)
          end
      | TOk _ => sema_err loc "alias is supported only for one declarator"
      end
  | _ => sema_err loc "alias is supported only for one declarator"
  end.

Fixpoint top_item_f (fuel : nat) (opts : c_lower_opts) (ext_names : list string)
  (it : c_item) (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (list term * c_type_env * c_lower_globals) :=
  match fuel with
  | O => TErr (TESema "top_item recursion limit")
  | S f =>
      match it with
      | IPragmaWeak _ _ _ | IToplevelAsm _ _ => TOk ([], env0, lg0)
      | IStaticAssert loc e _ =>
          match static_assert_check loc e env0 with
          | TErr err => TErr err
          | TOk _ => TOk ([], env0, lg0)
          end
      | IDecl _ specs [InitDecl dcl None] =>
          if is_overload_skip specs dcl env0 then TOk ([], env0, lg0)
          else
            match it with
            | IDecl loc sps inits =>
                match alias_target sps with
                | Some tgt => alias_decl_g loc sps inits tgt env0 lg0
                | None =>
                    match decl_types sps inits env0 with
                    | TErr TENotConstant => sema_err loc "array size is not a constant"
                    | TErr err => TErr err
                    | TOk (decls, env1) =>
                        let fix go_gd (ds : list c_decl) (e : c_type_env) (lg : c_lower_globals) :=
                          match ds with
                          | [] => TOk (e, lg)
                          | d :: rest =>
                              match global_decl_g loc d e lg with
                              | TErr err => TErr err
                              | TOk (e1, lg1) => go_gd rest e1 lg1
                              end
                          end in
                        match go_gd decls env1 lg0 with
                        | TErr err => TErr err
                        | TOk (env2, lg2) =>
                            let fix go_id (ds : list c_decl) (e : c_type_env) (lg : c_lower_globals) :=
                              match ds with
                              | [] => TOk (e, lg)
                              | d :: rest =>
                                  match init_decl_g loc sps d e lg with
                                  | TErr err => TErr err
                                  | TOk (e1, lg1) => go_id rest e1 lg1
                                  end
                              end in
                            match go_id decls env2 lg2 with
                            | TErr err => TErr err
                            | TOk (env3, lg3) => TOk ([], env3, lg3)
                            end
                        end
                    end
                end
            | _ => TOk ([], env0, lg0)
            end
      | IDecl loc specs inits =>
          match alias_target specs with
          | Some tgt => alias_decl_g loc specs inits tgt env0 lg0
          | None =>
              match decl_types specs inits env0 with
              | TErr TENotConstant => sema_err loc "array size is not a constant"
              | TErr err => TErr err
              | TOk (decls, env1) =>
                  let fix go_gd (ds : list c_decl) (e : c_type_env) (lg : c_lower_globals) :=
                    match ds with
                    | [] => TOk (e, lg)
                    | d :: rest =>
                        match global_decl_g loc d e lg with
                        | TErr err => TErr err
                        | TOk (e1, lg1) => go_gd rest e1 lg1
                        end
                    end in
                  match go_gd decls env1 lg0 with
                  | TErr err => TErr err
                  | TOk (env2, lg2) =>
                      let fix go_id (ds : list c_decl) (e : c_type_env) (lg : c_lower_globals) :=
                        match ds with
                        | [] => TOk (e, lg)
                        | d :: rest =>
                            match init_decl_g loc specs d e lg with
                            | TErr err => TErr err
                            | TOk (e1, lg1) => go_id rest e1 lg1
                            end
                        end in
                      match go_id decls env2 lg2 with
                      | TErr err => TErr err
                      | TOk (env3, lg3) => TOk ([], env3, lg3)
                      end
                  end
              end
          end
      | IFundef loc specs (Dcl (Some name) (DTFunc ret_dcl (PKnrDef knr_ns knr_ds)) oasm)
                (Stmt bloc (SBlock bitems)) =>
          let prototyped :=
            match lookup_ordinary env0 name with
            | Some (BFn (TFunc _ (Some _) _) _ _) => true
            | _ => false
            end in
          match knr_definition loc knr_ns knr_ds prototyped env0 with
          | TErr err => TErr err
          | TOk (params, locals) =>
              let bitems1 := app (map BIDecl locals) bitems in
              let rewritten :=
                IFundef loc specs (Dcl (Some name) (DTFunc ret_dcl params) oasm)
                        (Stmt bloc (SBlock bitems1)) in
              match top_item_f f opts ext_names rewritten env0 lg0 with
              | TErr err => TErr err
              | TOk (funcs, env1, lg1) =>
                  if negb prototyped then
                    match lookup_ordinary env1 name with
                    | Some (BFn (TFunc fret _ false) sym lnk) =>
                        let env2 := bind_ordinary name (BFn (TFunc fret None false) sym lnk) env1 in
                        let env3 :=
                          match lookup_qtype env2 name with
                          | Some (TFunc qret _ false) => bind_qtype name (TFunc qret None false) env2
                          | _ => env2
                          end in
                        TOk (funcs, env3, lg1)
                    | _ => TOk (funcs, env1, lg1)
                    end
                  else TOk (funcs, env1, lg1)
              end
          end
      | IFundef loc specs dcl body =>
          if is_overload_skip specs dcl env0 then TOk ([], env0, lg0)
          else
            match overload_wrapper_info specs dcl env0 with
            | Some (sym, ty) =>
                match dcl with
                | Dcl (Some name) dcl_ty _ =>
                    let local_s := sym ++ ".overload" in
                    let df := mkDeferredFn loc name ty dcl_ty body (te_scope env0) in
                    let lg1 :=
                      mkCLowerGlobals (lg_gdefs lg0) (lg_gdef_syms lg0) (lg_lits lg0) (lg_lit_syms lg0)
                                      (lg_lit_of lg0) (lg_func_names lg0)
                                      (smap_add local_s df (lg_deferred lg0))
                                      (smap_add sym local_s (lg_inline_copy lg0))
                                      (smap_add local_s sym (lg_inline_copy_of lg0))
                                      (lg_inline_attr lg0) (lg_readonly lg0) (lg_galign lg0)
                                      (lg_qsym lg0) (lg_initialized lg0) (lg_inits lg0) in
                    TOk ([], env0, lg1)
                | _ => TOk ([], env0, lg0)
                end
            | None =>
                match dcl with
                | Dcl (Some name) dcl_ty oasm =>
                    match decl_types specs [InitDecl dcl None] env0 with
                    | TErr err => TErr err
                    | TOk ([d0], env1) =>
                        let ty := cd_type d0 in
                        let stg := prior_storage name (cd_storage d0) env1 in
                        let d1 := mkCDecl name ty stg oasm None in
                        match global_decl_g loc d1 env1 lg0 with
                        | TErr err => TErr err
                        | TOk (env1a, lg1a) =>
                            match init_decl_g loc specs d1 env1a lg1a with
                            | TErr err => TErr err
                            | TOk (env1b, lg1b) =>
                                let def_sym :=
                                  match lookup_ordinary env1b name with
                                  | Some (BFn _ s _) => s
                                  | _ => name
                                  end in
                                let lg2 :=
                                  if always_inline_attr specs then add_inline_attr_g def_sym lg1b
                                  else lg1b in
                                let is_static := match stg with StStatic => true | _ => false end in
                                let is_extern := match stg with StExtern => true | _ => false end in
                                let ext_inline_body :=
                                  if gnu_inline_rule opts specs then negb is_extern
                                  else str_mem name ext_names in
                                if has_fspec "inline" specs && (is_static || negb ext_inline_body) then
                                  if is_static then
                                    let df := mkDeferredFn loc name ty dcl_ty body (te_scope env1b) in
                                    TOk ([], env1b, put_deferred_g def_sym df lg2)
                                  else if always_inline_attr specs && negb (gnu_inline_rule opts specs) then
                                    TOk ([], env1b, local_inline_copy_g "always_inline" loc name ty dcl_ty body env1b lg2)
                                  else if gnu_inline_rule opts specs
                                          && negb (id_stmt (fun x => names_symbol x def_sym env1b) body) then
                                    TOk ([], env1b, local_inline_copy_g "gnu_inline" loc name ty dcl_ty body env1b lg2)
                                  else TOk ([], env1b, lg2)
                                else if is_static then
                                  match lower_function opts loc name ty dcl_ty body env1b lg2 with
                                  | TOk (funcs, env3, lg3) => TOk (funcs, env3, lg3)
                                  | TErr _ =>
                                      let df := mkDeferredFn loc name ty dcl_ty body (te_scope env1b) in
                                      TOk ([], env1b, put_deferred_g def_sym df lg2)
                                  end
                                else
                                  match vector_abi ty env1b loc with
                                  | TErr err => TErr err
                                  | TOk _ => lower_function opts loc name ty dcl_ty body env1b lg2
                                  end
                            end
                        end
                    | TOk _ => sema_err loc "invalid function definition"
                    end
                | _ => sema_err loc "unnamed function definition"
                end
            end
      end
  end.

(** ## Used deferred inlines, weak linkage, unprototyped calls, and alias chains *)

Definition item_refs_acc (it : term) (acc : list string) : list string :=
  match it with
  | TApp f args =>
      if f == "func" then
        match args with
        | [_; _; _; _; TList blks] =>
            fold_left
              (fun a1 blk =>
                 match blk with
                 | TApp bf [_; _; TList insts; _] =>
                     if bf == "block" then
                       fold_left
                         (fun a2 ins =>
                            match ins with
                            | TApp inf iargs =>
                                if inf == "let" then
                                  match iargs with
                                  | [_; _; _; TList args0] =>
                                      fold_left (fun a3 ag =>
                                                   match ag with
                                                   | TApp gf [TAtom s] => if gf == "global" then s :: a3 else a3
                                                   | _ => a3
                                                   end) args0 a2
                                  | _ => a2
                                  end
                                else if inf == "call" then
                                  match iargs with
                                  | [_; TApp cf [TAtom s]; _] =>
                                      if (cf == "global") || (cf == "unproto") then s :: a2 else a2
                                  | _ => a2
                                  end
                                else a2
                            | _ => a2
                            end) insts a1
                     else a1
                 | _ => a1
                 end) blks acc
        | _ => acc
        end
      else if f == "data" then
        match args with
        | [_; _; _; TList ditems] =>
            fold_left
              (fun a1 di =>
                 match di with
                 | TApp itf [TAtom pt; TApp sf [TAtom s; _]] =>
                     if (itf == "item") && (pt == "p") && (sf == "sym") then s :: a1 else a1
                 | _ => a1
                 end) ditems acc
        | _ => acc
        end
      else if f == "alias4" then
        match args with [_; _; TAtom s; _; _] => s :: acc | _ => acc end
      else if f == "alias" then
        match args with [_; _; TAtom s] => s :: acc | _ => acc end
      else acc
  | _ => acc
  end.

Definition items_refs_sorted (items : list term) : list string :=
  let raw := fold_left (fun a it => item_refs_acc it a) items [] in
  let fix ins (x : string) (xs : list string) :=
    match xs with
    | [] => [x]
    | y :: rest =>
        match Order.atom_compare x y with
        | Eq => xs
        | Lt => x :: xs
        | Gt => y :: ins x rest
        end
    end in
  fold_left (fun a s => ins s a) raw [].

Definition func_symbols_of (items : list term) : list string :=
  flat_map (fun it =>
              match it with
              | TApp f [TAtom s; _; _; _; _] => if f == "func" then [s] else []
              | _ => []
              end) items.

Definition lower_deferred_sym (opts : c_lower_opts) (sym : string)
  (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (list term * c_type_env * c_lower_globals) :=
  match smap_find sym (lg_deferred lg0) with
  | None => TOk ([], env0, lg0)
  | Some df =>
      let env1a := with_scope env0 (df_scope df) in
      let env1 :=
        match smap_find sym (lg_inline_copy_of lg0) with
        | Some _ => bind_ordinary (df_name df) (BFn (df_type df) sym "local") env1a
        | None => env1a
        end in
      match lower_function opts (df_loc df) (df_name df) (df_type df) (df_dcl df) (df_body df) env1 lg0 with
      | TErr err => TErr err
      | TOk (func_items, env2, lg2) =>
          TOk (func_items, with_scope env2 (te_scope env0), lg2)
      end
  end.

Fixpoint used_inlines_f (fuel : nat) (opts : c_lower_opts) (scan : list term)
  (defined : list string) (env0 : c_type_env) (lg0 : c_lower_globals)
  : c_tr (list term * c_type_env * c_lower_globals) :=
  match fuel with
  | O => TOk ([], env0, lg0)
  | S f =>
      match global_data_g opts env0 lg0 with
      | TErr err => TErr err
      | TOk (data, _, _) =>
          let refs := items_refs_sorted (app scan data) in
          let syms :=
            filter (fun s =>
                      negb (str_mem s defined)
                      && match smap_find s (lg_deferred lg0) with Some _ => true | None => false end)
                   refs in
          match syms with
          | [] => TOk ([], env0, lg0)
          | _ =>
              let fix lower_all (xs : list string) (e : c_type_env) (lg : c_lower_globals)
                (acc : list term) :=
                match xs with
                | [] => TOk (acc, e, lg)
                | s :: rest =>
                    match lower_deferred_sym opts s e lg with
                    | TErr err => TErr err
                    | TOk (fi, e1, lg1) => lower_all rest e1 lg1 (app acc fi)
                    end
                end in
              match lower_all syms env0 lg0 [] with
              | TErr err => TErr err
              | TOk (new0, env1, lg1) =>
                  let defined1 := app (func_symbols_of new0) defined in
                  match used_inlines_f f opts new0 defined1 env1 lg1 with
                  | TErr err => TErr err
                  | TOk (new1, env2, lg2) => TOk (app new0 new1, env2, lg2)
                  end
              end
          end
      end
  end.

Definition with_used_inlines (opts : c_lower_opts) (funcs0 : list term)
  (env0 : c_type_env) (lg0 : c_lower_globals) : c_tr (list term * c_type_env * c_lower_globals) :=
  let defined := func_symbols_of funcs0 in
  match used_inlines_f (Z.to_nat 1024) opts funcs0 defined env0 lg0 with
  | TErr err => TErr err
  | TOk (new_fs, env1, lg1) =>
      match global_data_g opts env1 lg1 with
      | TErr err => TErr err
      | TOk (data0, env2, lg2) =>
          let funcs := app funcs0 new_fs in
          let def_syms := func_symbols_of funcs in
          let data :=
            filter (fun d =>
                      match d with
                      | TApp f [_; TApp inf [_; _]; _; TList [TApp itf [TAtom pt; TApp sf [TAtom sym; _]]]] =>
                          if (f == "data") && (inf == "init") && (itf == "item") && (pt == "p") && (sf == "sym") then
                            str_mem sym def_syms
                          else true
                      | _ => true
                      end) data0 in
          TOk (app funcs data, env2, lg2)
      end
  end.

Definition weak_symbols (items : list c_item) (env : c_type_env) : c_tr (list string) :=
  let weak_lns :=
    flat_map (fun it =>
                match it with
                | IPragmaWeak loc nm _ => [(loc, nm)]
                | IDecl loc specs inits =>
                    if weak_attr specs then
                      flat_map (fun d => match d with InitDecl (Dcl (Some nm) _ _) _ => [(loc, nm)] | _ => [] end) inits
                    else []
                | IFundef loc specs (Dcl (Some nm) _ _) _ =>
                    if weak_attr specs then [(loc, nm)] else []
                | _ => []
                end) items in
  let numbered :=
    let fix go (i : Z) (xs : list c_item) :=
      match xs with [] => [] | x :: r => (i, x) :: go (i + 1) r end in
    go 1 items in
  let common_lns :=
    flat_map (fun p =>
                let '(i, it) := p in
                match it with
                | IDecl loc specs inits =>
                    if common_attr specs then
                      flat_map (fun d =>
                                  match d with
                                  | InitDecl (Dcl (Some nm) _ _) None =>
                                      let bad :=
                                        existsb (fun x =>
                                                   match x with
                                                   | IDecl _ s is_ =>
                                                       existsb (fun dd =>
                                                                  match dd with
                                                                  | InitDecl (Dcl (Some nm2) _ _) v =>
                                                                      (nm2 == nm)
                                                                      && (match v with Some _ => true | None => false end
                                                                          || has_storage_spec "static" s
                                                                          || has_storage_spec "thread_local" s
                                                                          || has_storage_spec "typedef" s)
                                                                  | _ => false
                                                                  end) is_
                                                   | _ => false
                                                   end) items in
                                      let has_tent :=
                                        existsb (fun q =>
                                                   let '(j, y) := q in
                                                   (i <=? j) &&
                                                   match y with
                                                   | IDecl _ s is_ =>
                                                       negb (has_storage_spec "extern" s)
                                                       && existsb (fun dd =>
                                                                     match dd with
                                                                     | InitDecl (Dcl (Some nm2) _ _) None => nm2 == nm
                                                                     | _ => false
                                                                     end) is_
                                                   | _ => false
                                                   end) numbered in
                                      let is_gvar :=
                                        match lookup_ordinary env nm with
                                        | Some (BGVar _ _ _ _) => true
                                        | _ => false
                                        end in
                                      if negb bad && has_tent && is_gvar then [(loc, nm)] else []
                                  | _ => []
                                  end) inits
                    else []
                | _ => []
                end) numbered in
  let fix resolve (xs : list (c_loc * string)) (acc : list string) : c_tr (list string) :=
    match xs with
    | [] =>
        let fix ins (x : string) (l : list string) :=
          match l with
          | [] => [x]
          | y :: r =>
              match Order.atom_compare x y with
              | Eq => l
              | Lt => x :: l
              | Gt => y :: ins x r
              end
          end in
        TOk (fold_left (fun a s => ins s a) acc [])
    | (loc, nm) :: rest =>
        match lookup_ordinary env nm with
        | Some (BFn _ sym lnk) =>
            if lnk == "local" then sema_err loc ("weak declaration of " ++ nm ++ " must have external linkage")
            else resolve rest (sym :: acc)
        | Some (BGVar _ sym lnk tls) =>
            if tls then sema_err loc ("weak thread-local variable " ++ nm ++ " is not supported")
            else if lnk == "static" then sema_err loc ("weak declaration of " ++ nm ++ " must have external linkage")
            else resolve rest (sym :: acc)
        | _ => resolve rest acc
        end
    end in
  resolve (app weak_lns common_lns) [].

Definition weak_item_rewrite (weak : list string) (it : term) : term :=
  match it with
  | TApp f [TAtom s; TAtom lnk; a; b; c] =>
      if ((f == "func") || (f == "alias4")) && (lnk == "export") && str_mem s weak then
        TApp f [TAtom s; TAtom "weak"; a; b; c]
      else it
  | TApp f [TAtom s; TAtom lnk; a; is0] =>
      if (f == "data") && (lnk == "export") && str_mem s weak then TApp f [TAtom s; TAtom "weak"; a; is0] else it
  | TApp f [TAtom s; TApp rof [TAtom lnk]; a; is0] =>
      if (f == "data") && (rof == "ro") && (lnk == "export") && str_mem s weak then
        TApp f [TAtom s; TApp "ro" [TAtom "weak"]; a; is0]
      else it
  | _ => it
  end.

Definition weak_linkage (weak : list string) (items0 : list term) : list term :=
  match weak with
  | [] => items0
  | _ =>
      let items1 := map (weak_item_rewrite weak) items0 in
      let defined :=
        flat_map (fun it =>
                    match it with
                    | TApp f (TAtom s :: _) =>
                        if (f == "func") || (f == "data") || (f == "alias4") || (f == "alias") then [s] else []
                    | _ => []
                    end) items0 in
      let refs := items_refs_sorted items0 in
      let decls :=
        flat_map (fun sym =>
                    if negb (str_mem sym defined) && str_mem sym refs then
                      [ir_data sym (TApp "extern" [TAtom "weak"]) 1 []]
                    else []) weak in
      app items1 decls
  end.

Definition is_variadic_func_term (f_t : term) : bool :=
  match f_t with
  | TApp fn [_; _; _; _; TList blks] =>
      (fn == "func") &&
      existsb (fun blk =>
                 match blk with
                 | TApp bf [_; _; TList insts; _] =>
                     (bf == "block") &&
                     existsb (fun ins =>
                                match ins with
                                | TApp inf [_; _; TAtom "va_args"; _] => inf == "let"
                                | _ => false
                                end) insts
                 | _ => false
                 end) blks
  | _ => false
  end.

Fixpoint str_list_prefix (pre whole : list string) : bool :=
  match pre, whole with
  | [], _ => true
  | x :: rp, y :: rw => (x == y) && str_list_prefix rp rw
  | _, [] => false
  end.

Fixpoint str_list_eqb (a b : list string) : bool :=
  match a, b with
  | [], [] => true
  | x :: ra, y :: rb => (x == y) && str_list_eqb ra rb
  | _, _ => false
  end.

Definition unprototyped_calls (items0 : list term) : list term :=
  let defs : smap (list string * bool) :=
    fold_left (fun m it =>
                 match it with
                 | TApp f [TAtom s; _; _; TList ps; _] =>
                     if f == "func" then
                       let ks :=
                         flat_map (fun p =>
                                     match p with
                                     | TApp pf [TAtom k; _] => if pf == "param" then [k] else []
                                     | _ => []
                                     end) ps in
                       smap_add s (ks, is_variadic_func_term it) m
                     else m
                 | _ => m
                 end) items0 smap_empty in
  let rewrite_item (it : term) : term :=
    match it with
    | TApp f [s; l; r; ps; TList blks] =>
        if f == "func" then
          let fix go_blks (bs : list term) (n : Z) (acc : list term) :=
            match bs with
            | [] => rev acc
            | TApp bf [bl; phis; TList insts; jmp] :: rest =>
                if bf == "block" then
                  let fix go_is (xs : list term) (k : Z) (ia : list term) :=
                    match xs with
                    | [] => (rev ia, k)
                    | TApp cf [res; TApp uf [TAtom sym]; TList args] :: ri =>
                        if (cf == "call") && (uf == "unproto") then
                          match smap_find sym defs with
                          | Some (ks, is_v) =>
                              let ks1 :=
                                flat_map (fun ag =>
                                            match ag with
                                            | TApp af [TAtom ak; _] => if af == "arg" then [ak] else []
                                            | _ => []
                                            end) args in
                              if negb (str_list_eqb ks1 ks) && negb (is_v && str_list_prefix ks ks1) then
                                let t := ir_tmp ("unproto" ++ decimal k) in
                                let i1 := ir_let t "p" (TAtom "copy") [ir_global sym] in
                                let i2 := ir_call res t args in
                                go_is ri (k + 1) (i2 :: i1 :: ia)
                              else go_is ri k (ir_call res (ir_global sym) args :: ia)
                          | None => go_is ri k (ir_call res (ir_global sym) args :: ia)
                          end
                        else go_is ri k (TApp cf [res; TApp uf [TAtom sym]; TList args] :: ia)
                    | ins :: ri => go_is ri k (ins :: ia)
                    end in
                  let '(insts1, n1) := go_is insts n [] in
                  go_blks rest n1 (TApp bf [bl; phis; TList insts1; jmp] :: acc)
                else go_blks rest n (TApp bf [bl; phis; TList insts; jmp] :: acc)
            | b :: rest => go_blks rest n (b :: acc)
            end in
          TApp f [s; l; r; ps; TList (go_blks blks 0 [])]
        else it
    | _ => it
    end in
  map rewrite_item items0.

Definition alias_kinds (items0 : list term) : c_tr (list term) :=
  let fix chain_end (fuel : nat) (loc_s : string) (seen : list string) (t0 : string) : c_tr string :=
    match fuel with
    | O => TErr (TESema (loc_s ++ ": alias " ++ t0 ++ " is part of a cycle of aliases"))
    | S f =>
        match find (fun it =>
                      match it with
                      | TApp af [TAtom nm; _; _; _; _] => (af == "alias4") && (nm == t0)
                      | _ => false
                      end) items0 with
        | Some (TApp _ [_; _; TAtom t1; _; _]) =>
            if str_mem t0 seen then TErr (TESema (loc_s ++ ": alias " ++ t0 ++ " is part of a cycle of aliases"))
            else chain_end f loc_s (t0 :: seen) t1
        | _ => TOk t0
        end
    end in
  let fix go (xs : list term) (acc : list term) : c_tr (list term) :=
    match xs with
    | [] => TOk (rev acc)
    | TApp af [TAtom nm; TAtom lnk; TAtom tgt0; TAtom kind; TAtom loc_s] :: rest =>
        if af == "alias4" then
          match chain_end 256%nat loc_s [nm] tgt0 with
          | TErr err => TErr err
          | TOk tgt =>
              let ofound :=
                if existsb (fun it =>
                              match it with
                              | TApp ff [TAtom s; _; _; _; _] => (ff == "func") && (s == tgt)
                              | _ => false
                              end) items0 then Some "func"
                else if existsb (fun it =>
                                   match it with
                                   | TApp df [TAtom s; l; _; _] =>
                                       (df == "data") && (s == tgt)
                                       && negb (term_eqb l (TApp "extern" [TAtom "weak"]))
                                   | _ => false
                                   end) items0 then Some "data"
                else None in
              match ofound with
              | None => TErr (TESema (loc_s ++ ": alias " ++ nm ++ " must point to a defined variable or function, not " ++ tgt))
              | Some found =>
                  if found == kind then go rest (ir_alias nm lnk tgt :: acc)
                  else TErr (TESema (loc_s ++ ": alias " ++ nm ++ " of a " ++ kind ++ " names the " ++ found ++ " " ++ tgt))
              end
          end
        else go rest (TApp af [TAtom nm; TAtom lnk; TAtom tgt0; TAtom kind; TAtom loc_s] :: acc)
    | it :: rest => go rest (it :: acc)
    end in
  go items0 [].

(** ## Top-level entry point [c_module_opts]

    Matches [c_lower:c_module/4] step for step: prepends [builtin_declarations],
    lowers weakrefs, weak aliases, top-level items, deferred static/GNU/always
    inlines, weak linkage, unprototyped calls, alias chains, `.filc_*` module
    asm symbol directives, and [CLaunder.launder_module]. *)

Record c_module_res : Type := mkCModuleRes {
  cm_items : list term;
  cm_attrs : list (string * string);
  cm_env : c_type_env;
}.

Definition c_module_opts (opts : c_lower_opts) (items00 : list c_item) : c_tr c_module_res :=
  let env0 := empty_type_env_opts (lower_type_opts opts) in
  let items_b := app builtin_declarations items00 in
  let fix map_wr (xs : list c_item) (acc : list c_item) :=
    match xs with
    | [] => TOk (rev acc)
    | x :: rest =>
        match weakref_item items_b x with
        | TErr err => TErr err
        | TOk y => map_wr rest (y :: acc)
        end
    end in
  match map_wr items_b [] with
  | TErr err => TErr err
  | TOk items0 =>
      match weak_aliases items0 with
      | TErr err => TErr err
      | TOk (items, aliases) =>
          let ext_names := external_inline_names items in
          let fix go_top (xs : list c_item) (e : c_type_env) (lg : c_lower_globals) (acc : list term) :=
            match xs with
            | [] => TOk (acc, e, lg)
            | it :: rest =>
                match top_item_f 16%nat opts ext_names it e lg with
                | TErr err => TErr err
                | TOk (fs, e1, lg1) => go_top rest e1 lg1 (app acc fs)
                end
            end in
          match go_top items env0 empty_lower_globals [] with
          | TErr err => TErr err
          | TOk (funcs0a, env1, lg1) =>
              let fix go_wa (xs : list pending_weak_alias) (e : c_type_env) (acc : list term) :=
                match xs with
                | [] => TOk (rev acc, e)
                | a :: rest =>
                    match weak_alias_item a e with
                    | TErr err => TErr err
                    | TOk (it, e1) => go_wa rest e1 (it :: acc)
                    end
                end in
              match go_wa aliases env1 [] with
              | TErr err => TErr err
              | TOk (alias_items, env2) =>
                  let funcs0 := app funcs0a alias_items in
                  match with_used_inlines opts funcs0 env2 lg1 with
                  | TErr err => TErr err
                  | TOk (funcs1, _env3, lg3) =>
                      match weak_symbols items0 env2 with
                      | TErr err => TErr err
                      | TOk weak =>
                          let funcs2 := weak_linkage weak funcs1 in
                          let funcs3 := unprototyped_calls funcs2 in
                          match alias_kinds funcs3 with
                          | TErr err => TErr err
                          | TOk funcs4 =>
                              match filc_directives items00 with
                              | TErr err => TErr err
                              | TOk dirs =>
                                  match module_asm_symbols dirs funcs4 with
                                  | TErr err => TErr err
                                  | TOk (funcs5, fin) =>
                                      let funcs := launder_module funcs5 in
                                      let def_funcs := func_symbols_of funcs in
                                      let always :=
                                        flat_map (fun s0 =>
                                                    let s := final_symbol fin (TAtom s0) in
                                                    if str_mem s def_funcs then [(s, "always_inline")] else [])
                                                 (rev (lg_inline_attr lg1)) in
                                      let noinl_names :=
                                        flat_map (fun it =>
                                                    match it with
                                                    | IDecl _ specs inits =>
                                                        if noinline_attr specs then
                                                          flat_map (fun d => match d with InitDecl (Dcl (Some nm) _ _) _ => [nm] | _ => [] end) inits
                                                        else []
                                                    | IFundef _ specs (Dcl (Some nm) _ _) _ =>
                                                        if noinline_attr specs then [nm] else []
                                                    | _ => []
                                                    end) items0 in
                                      let never_syms :=
                                        let raw :=
                                          flat_map (fun nm =>
                                                      match lookup_ordinary env2 nm with
                                                      | Some (BFn _ s0 _) =>
                                                          let s := final_symbol fin (TAtom s0) in
                                                          if str_mem s def_funcs then [s] else []
                                                      | _ => []
                                                      end) noinl_names in
                                        let fix ins (x : string) (l : list string) :=
                                          match l with
                                          | [] => [x]
                                          | y :: r =>
                                              match Order.atom_compare x y with
                                              | Eq => l
                                              | Lt => x :: l
                                              | Gt => y :: ins x r
                                              end
                                          end in
                                        fold_left (fun a s => ins s a) raw [] in
                                      let never := map (fun s => (s, "noinline")) never_syms in
                                      TOk (mkCModuleRes funcs (app never always) env2)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end
  end.

Definition c_module (items00 : list c_item) : c_tr c_module_res :=
  c_module_opts default_lower_opts items00.
