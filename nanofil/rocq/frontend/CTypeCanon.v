(** Canonical SWI-Prolog term printers and translation-unit semantic dumper for
    the Gallina C type checker.

    This module serializes types, declarations, struct and union layouts, typed
    expression trees, and constant values in the exact canonical term format
    used by nanofil/src/c_types.pl, and walks parsed translation units so
    differential tests can compare Gallina against SWI-Prolog byte for byte. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp CTypeAst CTypeTables CTypes.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Semantic type and layout printers

    Each printer appends string fragments to a reversed [list string]
    accumulator, matching CCanon.v and SWI-Prolog's `write_canonical`. *)

Definition emit_su_id (id : su_id) (acc : list string) : list string :=
  match id with
  | SUInt n => emit_z n acc
  | SUBuiltin s => emit_atom s acc
  end.

Definition emit_enum_key (k : enum_key_t) (acc : list string) : list string :=
  match k with
  | EKTag s => emit_atom s acc
  | EKAnon s => emit ")" (emit_atom s (emit "anon(" acc))
  end.

Definition emit_c_qual (q : c_qual) (acc : list string) : list string :=
  match q with
  | QAtomic => emit "atomic" acc
  | QConst => emit "const" acc
  | QRestrict => emit "restrict" acc
  | QVolatile => emit "volatile" acc
  | QEnum k => emit ")" (emit_enum_key k (emit "enum(" acc))
  end.

Definition emit_arr_len (len : c_arr_len) (acc : list string) : list string :=
  match len with
  | ALNone => emit "none" acc
  | ALConst n => emit_z n acc
  | ALVlaStar => emit "vla(star)" acc
  | ALVlaExpr e => emit ")" (emit_expr e (emit "vla(" acc))
  | ALDyn v => emit "))" (emit_atom v (emit "dyn(tmp(" acc))
  end.

Fixpoint emit_c_type (t : c_type) (acc : list string) : list string :=
  let fix emit_tlist (xs : list c_type) (first : bool) (a : list string) : list string :=
    match xs with
    | [] => emit "]" a
    | x :: rest =>
        let a1 := if first then a else emit "," a in
        emit_tlist rest false (emit_c_type x a1)
    end in
  match t with
  | TVoid => emit "void" acc
  | TIntK k => emit (c_int_kind_name k) acc
  | TFloatK k => emit (c_float_kind_name k) acc
  | TPtr inner => emit ")" (emit_c_type inner (emit "ptr(" acc))
  | TArray elem len =>
      emit ")" (emit_arr_len len (emit "," (emit_c_type elem (emit "array(" acc))))
  | TFunc ret ps variadic =>
      let a1 := emit "," (emit_c_type ret (emit "func(" acc)) in
      let a2 :=
        match ps with
        | None => emit "unspecified" a1
        | Some xs => emit_tlist xs true (emit "[" a1)
        end in
      let vstr := if variadic then ",variadic)" else ",fixed)" in
      emit vstr a2
  | TStruct id => emit ")" (emit_su_id id (emit "struct(" acc))
  | TUnion id => emit ")" (emit_su_id id (emit "union(" acc))
  | TAtomic s p => emit ")" (emit_z p (emit "," (emit_c_type s (emit "atomic(" acc))))
  | TVec el n a =>
      emit ")" (emit_z a (emit "," (emit_z n (emit "," (emit_c_type el (emit "vec(" acc))))))
  | TQual qs inner =>
      emit ")" (emit_c_type inner (emit "," (emit_list emit_c_qual qs (emit "qualified(" acc))))
  | TBad why => emit ")" (emit_atom why (emit "bad(" acc))
  end.

Fixpoint emit_c_storage (s : c_storage) (acc : list string) : list string :=
  match s with
  | StNone => emit "none" acc
  | StTypedef => emit "typedef" acc
  | StStatic => emit "static" acc
  | StExtern => emit "extern" acc
  | StAuto => emit "auto" acc
  | StRegister => emit "register" acc
  | StThreadLocal inner => emit ")" (emit_c_storage inner (emit "thread_local(" acc))
  end.

Definition emit_member_layout (m : c_member_layout) (acc : list string) : list string :=
  let a1 := emit_opt_some emit_atom (ml_name m) (emit "m(" acc) in
  let a2 := emit_z (ml_off m) (emit "," (emit_c_type (ml_type m) (emit "," a1))) in
  match ml_bits m with
  | MBNone => emit ")" a2
  | MBBits pos w => emit "))" (emit_z w (emit "," (emit_z pos (emit ",bits(" a2))))
  end.

Definition emit_su_def (d : su_def) (acc : list string) : list string :=
  match d with
  | SUIncomplete tag =>
      emit ")" (emit_opt_some emit_atom tag (emit "incomplete(" acc))
  | SUDef kind ms sz al =>
      let kstr := match kind with KStruct => "struct" | KUnion => "union" end in
      emit ")" (emit_z al (emit "," (emit_z sz (emit ","
        (emit_list emit_member_layout ms (emit "," (emit kstr (emit "def(" acc))))))))
  | SUPartial why ms =>
      emit ")" (emit_list emit_member_layout ms (emit "," (emit_atom why (emit "partial(" acc))))
  | SUBad why =>
      emit ")" (emit_atom why (emit "bad(" acc))
  end.

Definition emit_const_val (v : c_const_val) (acc : list string) : list string :=
  match v with
  | CVInt n => emit_z n acc
  | CVUb => emit "ub" acc
  end.

Fixpoint emit_typed_node (n : c_typed_node) (acc : list string) : list string :=
  let fix emit_nodes (xs : list c_typed_node) (first : bool) (a : list string) : list string :=
    match xs with
    | [] => emit "]" a
    | x :: rest =>
        let a1 := if first then a else emit "," a in
        emit_nodes rest false (emit_typed_node x a1)
    end in
  match n with
  | TNode cat ty form =>
      let head :=
        match cat with
        | CatObj => "obj("
        | CatFun => "fun("
        | CatVal => "val("
        end in
      let a1 := emit "," (emit_c_type ty (emit head acc)) in
      let a2 :=
        match form with
        | TFId nm => emit ")" (emit_atom nm (emit "id(" a1))
        | TFPredefined nm => emit ")" (emit_atom nm (emit "predefined(" a1))
        | TFInt v => emit ")" (emit_z v (emit "int(" a1))
        | TFFloat s => emit ")" (emit_chars_atom_list s (emit "float(" a1))
        | TFImag x => emit ")" (emit_typed_node x (emit "imag(" a1))
        | TFStr bs => emit ")" (emit_list emit_z bs (emit "str(" a1))
        | TFWStr wt cs =>
            emit ")" (emit_list emit_z cs (emit "," (emit (wt_name wt) (emit "wstr(" a1))))
        | TFLoad x => emit ")" (emit_typed_node x (emit "load(" a1))
        | TFDecay x => emit ")" (emit_typed_node x (emit "decay(" a1))
        | TFAddr x => emit ")" (emit_typed_node x (emit "addr(" a1))
        | TFDeref x => emit ")" (emit_typed_node x (emit "deref(" a1))
        | TFCast tn x =>
            emit ")" (emit_typed_node x (emit "," (emit_type_name tn (emit "cast(" a1))))
        | TFComplit tn entries =>
            emit "))" (emit_list emit_init_entry entries
              (emit ",list(" (emit_type_name tn (emit "complit(" a1))))
        | TFIncDec op x =>
            emit ")" (emit_typed_node x (emit "," (emit (unop_name op) (emit "incdec(" a1))))
        | TFUn op x =>
            emit ")" (emit_typed_node x (emit "," (emit (unop_name op) (emit "un(" a1))))
        | TFBin op a b =>
            emit ")" (emit_typed_node b (emit "," (emit_typed_node a
              (emit "," (emit (binop_name op) (emit "bin(" a1))))))
        | TFCond c a b =>
            emit ")" (emit_typed_node b (emit "," (emit_typed_node a
              (emit "," (emit_typed_node c (emit "cond(" a1))))))
        | TFGCond c b =>
            emit ")" (emit_typed_node b (emit "," (emit_typed_node c (emit "gcond(" a1))))
        | TFAssign op a b =>
            emit ")" (emit_typed_node b (emit "," (emit_typed_node a
              (emit "," (emit_atom op (emit "assign(" a1))))))
        | TFComma a b =>
            emit ")" (emit_typed_node b (emit "," (emit_typed_node a (emit "comma(" a1))))
        | TFMember x f =>
            emit ")" (emit_atom f (emit "," (emit_typed_node x (emit "member(" a1))))
        | TFBitfield x f w =>
            emit ")" (emit_z w (emit ")," (emit_atom f (emit "," (emit_typed_node x (emit "bitfield(member(" a1))))))
        | TFVLane v i =>
            emit ")" (emit_typed_node i (emit "," (emit_typed_node v (emit "vlane(" a1))))
        | TFCall f args =>
            emit ")" (emit_nodes args true (emit ",[" (emit_typed_node f (emit "call(" a1))))
        | TFBuiltin nm args =>
            emit ")" (emit_list emit_expr args (emit "," (emit_atom nm (emit "builtin(" a1))))
        | TFConvertVector a tn =>
            emit "])" (emit_type_name tn (emit "," (emit_expr a
              (emit "builtin('__builtin_convertvector',[" a1))))
        | TFSizeofExpr x => emit ")" (emit_typed_node x (emit "sizeof(" a1))
        | TFSizeofType tn => emit ")" (emit_type_name tn (emit "sizeof(" a1))
        | TFAlignofType tn => emit ")" (emit_type_name tn (emit "alignof(" a1))
        | TFAlignofExpr x => emit ")" (emit_typed_node x (emit "alignof_expr(" a1))
        | TFOffsetof tn path =>
            emit ")" (emit_list emit_desig path (emit "," (emit_type_name tn (emit "offsetof(" a1))))
        | TFVaArg tn x =>
            emit ")" (emit_typed_node x (emit "," (emit_type_name tn (emit "va_arg(" a1))))
        | TFBitCast x => emit ")" (emit_typed_node x (emit "bit_cast(" a1))
        | TFStmtExpr body => emit ")" (emit_stmt body (emit "stmtexpr(" a1))
        end in
      emit ")" a2
  end.

Definition emit_type_err (e : c_type_err) (acc : list string) : list string :=
  match e with
  | TENotConstant => emit "not_constant" acc
  | TEBad why => emit ")" (emit_atom why (emit "bad(" acc))
  | TESema msg => emit ")" (emit_atom msg (emit "sema(" acc))
  end.

Definition emit_to_string (acc : list string) : string :=
  String.concat "" (rev_append acc []).

(** ## Translation-unit semantic dumper

    Walks a parsed translation unit identically to a companion SWI-Prolog
    harness over c_types.pl, emitting every top-level and local declaration,
    every elaborated expression and folded constant value, and every laid-out
    struct or union definition. *)

Definition bind_top_decl (d : c_decl) (env : c_type_env) : c_type_env :=
  match cd_storage d with
  | StTypedef => env
  | _ =>
      let nm := cd_name d in
      let ty := cd_type d in
      match ty with
      | TFunc _ _ _ => bind_ordinary nm (BFn ty nm "external") env
      | _ => bind_ordinary nm (BGVar ty nm "external" false) env
      end
  end.

Definition bind_local_decl (d : c_decl) (env : c_type_env) : c_type_env :=
  match cd_storage d with
  | StTypedef => env
  | _ =>
      let nm := cd_name d in
      let ty := cd_type d in
      match ty with
      | TFunc _ _ _ => bind_ordinary nm (BFn ty nm "external") env
      | _ => bind_ordinary nm (BVar VSNone ty) env
      end
  end.

Definition load_builtin_item (env : c_type_env) (it : c_item) : c_type_env :=
  match it with
  | IDecl _ specs inits =>
      match decl_types specs inits env with
      | TOk (ds, env1) => fold_left (fun e d => bind_top_decl d e) ds env1
      | TErr _ => env
      end
  | _ => env
  end.

Definition check_expr_record (e : c_expr) (env0 : c_type_env)
  : string * c_type_env :=
  let env := expression_tags e env0 in
  let line :=
    match elaborate e env with
    | TErr err => emit_to_string (emit ")" (emit_type_err err (emit "expr_err(" [])))
    | TOk (Some x) =>
        let xv := value_node x in
        match folded xv env with
        | TErr err => emit_to_string (emit ")" (emit_type_err err (emit "expr_err(" [])))
        | TOk ocv =>
            let a1 := emit "," (emit_typed_node x (emit "expr(" [])) in
            let a2 :=
              match ocv with
              | Some cv => emit ")" (emit_const_val cv (emit "some(" a1))
              | None => emit "none" a1
              end in
            emit_to_string (emit ")" a2)
        end
    | TOk None =>
        match fault e env with
        | Some msg => emit_to_string (emit ")" (emit_atom msg (emit "expr_fault(" [])))
        | None => "expr_none"
        end
    end in
  (line, env).

Fixpoint check_init_records (fuel : nat) (ini : c_init) (env : c_type_env) (acc : list string)
  : list string * c_type_env :=
  match fuel with
  | O => (acc, env)
  | S f =>
      match ini with
      | InitExpr e =>
          let '(line, env1) := check_expr_record e env in
          (line :: acc, env1)
      | InitList entries =>
          let fix go (xs : list c_init_entry) (e : c_type_env) (a : list string) :=
            match xs with
            | [] => (a, e)
            | InitEntry _ i1 :: rest =>
                let '(a1, e1) := check_init_records f i1 e a in
                go rest e1 a1
            end in
          go entries env acc
      end
  end.

Fixpoint collect_stmt_labels (fuel : nat) (s : c_stmt) (acc : list string) : list string :=
  match fuel with
  | O => acc
  | S f =>
      match s with
      | Stmt _ (SLabel nm body) => collect_stmt_labels f body (nm :: acc)
      | Stmt _ (SBlock items) =>
          let fix go_is (xs : list c_block_item) (a : list string) :=
            match xs with
            | [] => a
            | BIStmt s1 :: rest => go_is rest (collect_stmt_labels f s1 a)
            | BIDecl _ :: rest => go_is rest a
            end in
          go_is items acc
      | Stmt _ (SIf _ t oe) =>
          let a1 := collect_stmt_labels f t acc in
          match oe with Some e1 => collect_stmt_labels f e1 a1 | None => a1 end
      | Stmt _ (SWhile _ b) | Stmt _ (SDo b _) | Stmt _ (SSwitch _ b)
      | Stmt _ (SCase _ b) | Stmt _ (SCaseRange _ _ b) | Stmt _ (SDefault b) =>
          collect_stmt_labels f b acc
      | Stmt _ (SFor _ _ _ b) => collect_stmt_labels f b acc
      | _ => acc
      end
  end.

Definition bind_func_labels (body : c_stmt) (env0 : c_type_env) : c_type_env :=
  let lbls := rev_append (collect_stmt_labels (Z.to_nat 1024) body []) [] in
  let fix go (xs : list string) (i : Z) (e : c_type_env) :=
    match xs with
    | [] => e
    | nm :: rest =>
        match lookup_label_addr e nm with
        | Some _ => go rest i e
        | None => go rest (i + 1) (bind_label_addr nm i e)
        end
    end in
  go lbls 1 env0.

Fixpoint check_stmt_records (fuel : nat) (s : c_stmt) (env : c_type_env) (acc : list string)
  : list string * c_type_env :=
  match fuel with
  | O => (acc, env)
  | S f =>
      let check_e (e : c_expr) (env0 : c_type_env) (a0 : list string) :=
        let '(line, env1) := check_expr_record e env0 in
        (line :: a0, env1) in
      let check_oe (oe : option c_expr) (env0 : c_type_env) (a0 : list string) :=
        match oe with Some e => check_e e env0 a0 | None => (a0, env0) end in
      let check_local_decl (specs : list c_spec) (inits : list c_init_decl)
        (env0 : c_type_env) (a0 : list string) :=
        match decl_types specs inits env0 with
        | TErr err =>
            (emit_to_string (emit ")" (emit_type_err err (emit "decl_err(" []))) :: a0, env0)
        | TOk (ds, env1) =>
            let fix go_ds (xs : list c_decl) (e : c_type_env) (a : list string) :=
              match xs with
              | [] => (a, e)
              | d :: rest =>
                  let line := emit_to_string
                    (emit ")" (emit_c_storage (cd_storage d)
                      (emit "," (emit_c_type (cd_type d)
                        (emit "," (emit_atom (cd_name d) (emit "local_decl(" []))))))) in
                  let e1 := bind_local_decl d e in
                  let '(a1, e2) :=
                    match cd_init d with
                    | Some ini => check_init_records f ini e1 (line :: a)
                    | None => (line :: a, e1)
                    end in
                  go_ds rest e2 a1
              end in
            go_ds ds env1 a0
        end in
      match s with
      | Stmt _ SNull | Stmt _ SBreak | Stmt _ SContinue | Stmt _ (SGoto _)
      | Stmt _ (SAsmEmpty _ _ _ _) | Stmt _ (SAsm _ _ _ _ _) | Stmt _ (SUnsupportedAsm _) => (acc, env)
      | Stmt _ (SExpr e) | Stmt _ (SComputedGoto e) => check_e e env acc
      | Stmt _ (SReturn oe) => check_oe oe env acc
      | Stmt _ (SIf c t oe) =>
          let '(a1, e1) := check_e c env acc in
          let '(a2, e2) := check_stmt_records f t e1 a1 in
          match oe with
          | Some els => check_stmt_records f els e2 a2
          | None => (a2, e2)
          end
      | Stmt _ (SWhile c b) =>
          let '(a1, e1) := check_e c env acc in
          check_stmt_records f b e1 a1
      | Stmt _ (SDo b c) =>
          let '(a1, e1) := check_stmt_records f b env acc in
          check_e c e1 a1
      | Stmt _ (SFor fi fc fs b) =>
          let saved := te_scope env in
          let '(a1, e1) :=
            match fi with
            | FINone => (acc, env)
            | FIExpr e => check_e e env acc
            | FIDecl (IDecl _ specs inits) => check_local_decl specs inits env acc
            | FIDecl _ => (acc, env)
            end in
          let '(a2, e2) := check_oe fc e1 a1 in
          let '(a3, e3) := check_oe fs e2 a2 in
          let '(a4, e4) := check_stmt_records f b e3 a3 in
          (a4, with_scope e4 saved)
      | Stmt _ (SSwitch c b) =>
          let '(a1, e1) := check_e c env acc in
          check_stmt_records f b e1 a1
      | Stmt _ (SCase e b) =>
          let '(a1, e1) := check_e e env acc in
          check_stmt_records f b e1 a1
      | Stmt _ (SCaseRange lo hi b) =>
          let '(a1, e1) := check_e lo env acc in
          let '(a2, e2) := check_e hi e1 a1 in
          check_stmt_records f b e2 a2
      | Stmt _ (SDefault b) | Stmt _ (SLabel _ b) =>
          check_stmt_records f b env acc
      | Stmt _ (SBlock items) =>
          let saved := te_scope env in
          let fix go_bs (xs : list c_block_item) (e : c_type_env) (a : list string) :=
            match xs with
            | [] => (a, with_scope e saved)
            | BIStmt s1 :: rest =>
                let '(a1, e1) := check_stmt_records f s1 e a in
                go_bs rest e1 a1
            | BIDecl (IDecl _ dsp dinits) :: rest =>
                let '(a1, e1) := check_local_decl dsp dinits e a in
                go_bs rest e1 a1
            | BIDecl (IStaticAssert _ se _) :: rest =>
                let '(a1, e1) := check_e se e a in
                go_bs rest e1 a1
            | BIDecl _ :: rest => go_bs rest e a
            end in
          go_bs items env acc
      end
  end.

Definition bind_param_list (syn : c_dcl_type) (pts : list c_type) (env0 : c_type_env)
  : c_type_env :=
  match syn with
  | DTFunc _ (PParams ps _) =>
      let fix go (a : list c_param) (b : list c_type) (e : c_type_env) :=
        match a, b with
        | Param _ (Dcl (Some nm) _ _) :: ra, pt :: rb =>
            go ra rb (bind_ordinary nm (BVar VSNone pt) e)
        | _ :: ra, _ :: rb => go ra rb e
        | _, _ => e
        end in
      go ps pts env0
  | _ => env0
  end.

Definition check_tu_items (items : list c_item) (opts : c_type_opts) : list string :=
  let env0 := fold_left load_builtin_item builtin_declarations (empty_type_env_opts opts) in
  let fix go (xs : list c_item) (env : c_type_env) (acc : list string)
    : list string * c_type_env :=
    match xs with
    | [] => (acc, env)
    | IDecl _ specs inits :: rest =>
        match decl_types specs inits env with
        | TErr err =>
            let line := emit_to_string (emit ")" (emit_type_err err (emit "decl_err(" []))) in
            go rest env (line :: acc)
        | TOk (ds, env1) =>
            let fix go_ds (ys : list c_decl) (e : c_type_env) (a : list string) :=
              match ys with
              | [] => (a, e)
              | d :: drest =>
                  let line := emit_to_string
                    (emit ")" (emit_c_storage (cd_storage d)
                      (emit "," (emit_c_type (cd_type d)
                        (emit "," (emit_atom (cd_name d) (emit "top_decl(" []))))))) in
                  let e1 := bind_top_decl d e in
                  let '(a1, e2) :=
                    match cd_init d with
                    | Some ini => check_init_records (Z.to_nat 1024) ini e1 (line :: a)
                    | None => (line :: a, e1)
                    end in
                  go_ds drest e2 a1
              end in
            let '(acc1, env2) := go_ds ds env1 acc in
            go rest env2 acc1
        end
    | IFundef loc specs (Dcl (Some nm) syn0 _) body :: rest =>
        let prototyped :=
          match lookup_ordinary env nm with
          | Some (BFn (TFunc _ (Some _) _) _ _) => true
          | _ => false
          end in
        let res_syn : c_tr (c_dcl_type * list c_item) :=
          match syn0 with
          | DTFunc inner (PKnrDef knr_ns knr_ds) =>
              match knr_definition loc knr_ns knr_ds prototyped env with
              | TErr err => TErr err
              | TOk (ps1, locs1) => TOk (DTFunc inner ps1, locs1)
              end
          | _ => TOk (syn0, [])
          end in
        match res_syn with
        | TErr err =>
            let line := emit_to_string (emit ")" (emit_type_err err (emit "func_err(" []))) in
            go rest env (line :: acc)
        | TOk (syn, knr_locs) =>
            match specs_type specs env with
            | TErr err =>
                let line := emit_to_string (emit ")" (emit_type_err err (emit "func_err(" []))) in
                go rest env (line :: acc)
            | TOk (base, env1) =>
                match apply_declarator syn base env1 with
                | TErr err =>
                    let line := emit_to_string (emit ")" (emit_type_err err (emit "func_err(" []))) in
                    go rest env1 (line :: acc)
                | TOk (fn_ty, env2) =>
                    let refl := reflect_type (TypeName specs syn) fn_ty env2 in
                    let line := emit_to_string
                      (emit ")" (emit_c_type refl
                        (emit "," (emit_c_type fn_ty
                          (emit "," (emit_atom nm (emit "top_func(" []))))))) in
                    let env3 := bind_qtype nm refl (bind_ordinary nm (BFn fn_ty nm "external") env2) in
                    let outer_sc := te_scope env3 in
                    let env4 := set_enclosing_fn (Some nm) env3 in
                    let env5 :=
                      match fn_ty with
                      | TFunc _ (Some pts) _ =>
                          reflect_params syn pts (bind_param_list syn pts env4)
                      | _ => env4
                      end in
                    let env6 := bind_func_labels body env5 in
                    let body_full :=
                      match knr_locs with
                      | [] => body
                      | _ =>
                          let kl := map BIDecl knr_locs in
                          match body with
                          | Stmt l (SBlock bs) => Stmt l (SBlock (kl ++ bs))
                          | _ => Stmt loc (SBlock (kl ++ [BIStmt body]))
                          end
                      end in
                    let '(acc1, env7) :=
                      check_stmt_records (Z.to_nat 2048) body_full env6 (line :: acc) in
                    go rest (with_scope env7 outer_sc) acc1
                end
            end
        end
    | IStaticAssert _ expr _ :: rest =>
        let '(line, env1) := check_expr_record expr env in
        go rest env1 (line :: acc)
    | _ :: rest => go rest env acc
    end in
  let '(rev_lines, env_final) := go items env0 [] in
  let next_n := Z.to_nat (df_next (te_defs env_final)) in
  let fix emit_sus (k : nat) (i : Z) (a : list string) : list string :=
    match k with
    | O => a
    | S k' =>
        let a1 :=
          match lookup_su_def env_final (SUInt i) with
          | Some d =>
              emit_to_string (emit ")" (emit_su_def d (emit "," (emit_z i (emit "su_def(" []))))) :: a
          | None => a
          end in
        emit_sus k' (i + 1) a1
    end in
  let rev_all := emit_sus next_n 0 rev_lines in
  rev_append rev_all [].
