(** This module lowers C builtins, atomic read-modify-write operations,
    floating-point classification helpers, and SSE or AVX2 vector intrinsics
    into Nanofil IR.

    It ports the builtin and vector intrinsic lowering rules of
    nanofil/src/c_lower.pl in pure, zero-axiom Gallina. Parameterizing the
    pass by a small expression-evaluation callback [builtin_eval_cb] lets this
    file compile ahead of [CLower.v] while exposing atomic and safety-trap
    helpers that statement and expression lowering also call. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Nanofil Require Import Term.
From Backend Require Import Text Order.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp
  CTypeAst CTypeTables CTypes CLowerState CLowerAsm.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Notation "a == b" := (String.eqb a b) (at level 70, no associativity).

(** ## Evaluation callback and shared atomic helpers

    Expression lowering in [CLower.v] passes [rval] through [builtin_eval_cb].
    The atomic helpers ([rmw], [cas_once], [atomic_stored], [atomic_su_loaded],
    [atomic_su_word], [rmw_aligned], and [safety_error]) need no expression
    recursion and are shared directly with [CLower.v]. *)

Record builtin_eval_cb : Type := mkBuiltinEvalCb {
  be_rval : c_expr -> c_lower_ctx -> c_func_st -> l_res c_val;
}.

Definition safety_error (msg : string) (st0 : c_func_st) : c_func_st :=
  let '(sym, st1) := l_new_literal (LitBytes (string_to_bytes msg)) st0 in
  let '(addr, st2) := l_let "p" (TAtom "copy") [ir_global sym] st1 in
  l_emit (ir_call (TAtom "void") (ir_global "zsafety_error") [ir_arg "p" addr]) st2.

Definition atomic_word (p : Z) : option c_type :=
  if Z.eqb p 1 then Some TUChar
  else if Z.eqb p 2 then Some TUShort
  else if Z.eqb p 4 then Some TUInt
  else if Z.eqb p 8 then Some TULong
  else None.

Definition atomic_stored (t : c_type) (x addr : term) (order : Z)
  (st0 : c_func_st) : l_res unit :=
  match t with
  | TPtr _ => LOk tt (l_emit (ir_atomic_store "p" x addr) st0)
  | _ =>
      match store_typed t x addr st0 with
      | LErr msg => LErr msg
      | LOk _ st1 =>
          if Z.eqb order 5 then LOk tt (l_emit ir_fence st1)
          else LOk tt st1
      end
  end.

Definition atomic_su_loaded (s : c_type) (p : Z) (addr : term)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  match atomic_word p with
  | None => l_err (ctx_loc ctx) "unsupported atomic struct size" st0
  | Some wt =>
      match l_local_slot (TAtomic s p) st0 with
      | LErr msg => LErr msg
      | LOk slot st1 =>
          match load_typed wt addr ctx st1 with
          | LErr msg => LErr msg
          | LOk x st2 =>
              match store_typed wt x slot st2 with
              | LErr msg => LErr msg
              | LOk _ st3 => LOk (CVal slot s) st3
              end
          end
      end
  end.

Definition atomic_su_word (s : c_type) (p : Z) (v : c_val)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res term :=
  let '(CVal src _) := v in
  match atomic_word p with
  | None => l_err (ctx_loc ctx) "unsupported atomic struct size" st0
  | Some wt =>
      match l_local_slot (TAtomic s p) st0 with
      | LErr msg => LErr msg
      | LOk slot st1 =>
          match store_typed wt (ir_const 0) slot st1 with
          | LErr msg => LErr msg
          | LOk _ st2 =>
              match copy_object s src slot st2 with
              | LErr msg => LErr msg
              | LOk _ st3 => load_typed wt slot ctx st3
              end
          end
      end
  end.

Fixpoint underaligned_member_b (x : c_typed_node) (env : c_type_env) (w : Z) : option string :=
  match x with
  | TNode CatObj _ (TFMember xs fld) =>
      let su := unqualified (tree_type xs) in
      let bad_align :=
        match type_size_align su env with
        | TOk (_, al) => al <? w
        | TErr _ => false
        end in
      if bad_align then Some fld
      else
        let bad_off :=
          match member_layout su fld env with
          | Some (_, moff, _) => negb (Z.eqb (Z.modulo moff w) 0)
          | None => false
          end in
        if bad_off then Some fld
        else underaligned_member_b xs env w
  | _ => None
  end.

Definition rmw_aligned (x : c_typed_node) (ctx : c_lower_ctx) (st : c_func_st) : l_res unit :=
  let env := fs_env st in
  let t := unqualified (tree_type x) in
  match type_size_align t env with
  | TOk (w, _) =>
      match underaligned_member_b x env w with
      | Some name =>
          l_err (ctx_loc ctx)
            ("an atomic read-modify-write of " ++ name ++
             ", a member of a packed struct or union, may be misaligned; clang calls libatomic for it, which nanofil does not have")
            st
      | None => LOk tt st
      end
  | TErr _ => LOk tt st
  end.

Definition rmw_arg_aligned (p : c_expr) (ctx : c_lower_ctx) (st : c_func_st) : l_res unit :=
  match elaborate p (fs_env st) with
  | TOk (Some (TNode CatVal _ (TFAddr x))) => rmw_aligned x ctx st
  | _ => LOk tt st
  end.

Definition cas_repr (u : c_type) : option (string * string * option string) :=
  match u with
  | TFloatK FFloat => Some ("uw", "w", Some "s")
  | TFloatK FDouble => Some ("l", "l", Some "d")
  | _ =>
      match load_op u with
      | Some (k, t) => Some (t, k, None)
      | None => None
      end
  end.

Definition cas_equal (k : string) (a b : term) (st0 : c_func_st) : term * c_func_st :=
  if k == "p" then
    let '(ia, st1) := l_let "l" (TAtom "ptoi") [a] st0 in
    let '(ib, st2) := l_let "l" (TAtom "ptoi") [b] st1 in
    l_let "w" (TApp "cmp" [TAtom "eq"; TAtom "l"]) [ia; ib] st2
  else
    l_let "w" (TApp "cmp" [TAtom "eq"; TAtom k]) [a; b] st0.

Definition to_bits_v (bits : option string) (v : term) (st : c_func_st) : term * c_func_st :=
  match bits with
  | None => (v, st)
  | Some b =>
      if b == "s" then l_let "w" (TAtom "cast") [v] st
      else l_let "l" (TAtom "cast") [v] st
  end.

Definition from_bits_v (bits : option string) (b : term) (st : c_func_st) : term * c_func_st :=
  match bits with
  | None => (b, st)
  | Some s => l_let s (TAtom "cast") [b] st
  end.

Definition cas_once (t : c_type) (addr e n : term) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (term * term) :=
  match cas_repr t with
  | None => l_err (ctx_loc ctx) ("unsupported atomic type " ++ c_type_diag_str t) st0
  | Some (ct, k, bits) =>
      let '(eb, st1) := to_bits_v bits e st0 in
      let '(nb, st2) := to_bits_v bits n st1 in
      let '(gb, st3) := l_let k (TApp "cas" [TAtom ct]) [eb; nb; addr] st2 in
      let '(eqv, st4) := cas_equal k gb eb st3 in
      let '(got, st5) := from_bits_v bits gb st4 in
      LOk (got, eqv) st5
  end.

Definition rmw_binop_of (op : string) : option c_binop :=
  if op == "add" then Some BAdd
  else if op == "sub" then Some BSub
  else if op == "mul" then Some BMul
  else if op == "div" then Some BDiv
  else if op == "mod" then Some BMod
  else if op == "and" then Some BAnd
  else if op == "or" then Some BOr
  else if op == "xor" then Some BXor
  else if op == "shl" then Some BShl
  else if op == "shr" then Some BShr
  else None.

Definition rmw_new (op : string) (old_v v : c_val) (u : c_type)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  if op == "xchg" then convert_val v u st0
  else if op == "nand" then
    match binary_op BAnd old_v v ctx st0 with
    | LErr msg => LErr msg
    | LOk a st1 =>
        match unary_op UBnot a ctx st1 with
        | LErr msg => LErr msg
        | LOk b st2 => convert_val b u st2
        end
    end
  else if (op == "max") || (op == "min") then
    let cmp := if op == "max" then BGt else BLt in
    match binary_op cmp old_v v ctx st0 with
    | LErr msg => LErr msg
    | LOk c st1 =>
        match convert_val c u st1 with
        | LErr msg => LErr msg
        | LOk c1 st2 =>
            match unary_op UNeg c1 ctx st2 with
            | LErr msg => LErr msg
            | LOk m st3 =>
                match convert_val m u st3 with
                | LErr msg => LErr msg
                | LOk m1 st4 =>
                    match binary_op BAnd old_v m1 ctx st4 with
                    | LErr msg => LErr msg
                    | LOk a st5 =>
                        match unary_op UBnot m1 ctx st5 with
                        | LErr msg => LErr msg
                        | LOk nm st6 =>
                            match binary_op BAnd v nm ctx st6 with
                            | LErr msg => LErr msg
                            | LOk b st7 =>
                                match binary_op BOr a b ctx st7 with
                                | LErr msg => LErr msg
                                | LOk o st8 => convert_val o u st8
                                end
                            end
                        end
                    end
                end
            end
        end
    end
  else
    match rmw_binop_of op with
    | Some bop =>
        match binary_op bop old_v v ctx st0 with
        | LErr msg => LErr msg
        | LOk b st1 => convert_val b u st1
        end
    | None => l_err (ctx_loc ctx) ("unsupported atomic op " ++ op) st0
    end.

(** Replace placeholder edge label in a phi inside [fs_blocks] or [fs_cur].
    Prolog unifies the backedge label [LB] after starting block [LL] because
    [rmw_new] can emit multiple blocks or leave [LB] equal to [LL]. We use a
    sentinel label `"__rmw_backedge__"` and patch it once [LB] is known. *)

Definition replace_phi_label_term (old_l new_l : string) (t : term) : term :=
  match t with
  | TApp f [d; k; TList edges] =>
      if f == "phi" then
        let edges1 :=
          map (fun e =>
                 match e with
                 | TApp ef [TAtom l; v] =>
                     if (ef == "-") && (l == old_l) then ir_edge (TAtom new_l) v else e
                 | _ => e
                 end) edges in
        TApp f [d; k; TList edges1]
      else t
  | _ => t
  end.

Definition patch_rmw_phi (ll old_l new_l : string) (got_v : term) (st : c_func_st) : c_func_st :=
  let patch_phi (p : list Z * term) : list Z * term :=
    let '(os, t) := p in
    match t with
    | TApp f [d; k; TList edges] =>
        if f == "phi" then
          let edges1 :=
            map (fun e =>
                   match e with
                   | TApp ef [TAtom l; _] =>
                       if (ef == "-") && (l == old_l) then ir_edge (TAtom new_l) got_v else e
                   | _ => e
                   end) edges in
          (os, TApp f [d; k; TList edges1])
        else (os, t)
    | _ => (os, t)
    end in
  let cur1 :=
    match fs_cur st with
    | Some (lbl, phis) =>
        if lbl == ll then Some (lbl, map patch_phi phis) else Some (lbl, phis)
    | None => None
    end in
  let blks1 :=
    map (fun blk =>
           let '(lbl, phis, insts, jmp) := blk in
           if lbl == ll then (lbl, map patch_phi phis, insts, jmp) else blk)
        (fs_blocks st) in
  mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) cur1 (fs_insts st)
            blks1 (fs_n st) (fs_labels st) (fs_vm_labels st) (fs_vm_gotos st)
            (fs_cleanups st) (fs_cleanup_gotos st) (fs_computed_goto st)
            (fs_cases st) (fs_build st) (fs_opts st).

Definition rmw (u : c_type) (addr : term) (op : string) (v : c_val)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (c_val * c_val) :=
  match cas_repr u, type_class u with
  | Some (t, k, bits), Some ku =>
      let '(old0, st1) :=
        if t == "p" then l_let "p" (TApp "atomic_load" [TAtom "p"]) [addr] st0
        else
          let '(b0, s1) := l_let k (TApp "load" [TAtom t]) [addr] st0 in
          from_bits_v bits b0 s1 in
      let '(le, st2) := l_here st1 in
      let '(ll, st3) := l_label st2 in
      let '(ld, st4) := l_label st3 in
      let '(old_t, st5) := l_fresh st4 in
      let st6 := l_term (ir_goto ll) st5 in
      let sentinel := "__rmw_backedge__" in
      let phi_t :=
        ir_phi old_t ku [ir_edge (TAtom le) old0; ir_edge (TAtom sentinel) (ir_const 0)] in
      let st7 := l_start_phi ll [phi_t] st6 in
      match rmw_new op (CVal old_t u) v u ctx st7 with
      | LErr msg => LErr msg
      | LOk (CVal new_t _) st8 =>
          let '(ob, st9) := to_bits_v bits old_t st8 in
          let '(nb, st10) := to_bits_v bits new_t st9 in
          let '(gb, st11) := l_let k (TApp "cas" [TAtom t]) [ob; nb; addr] st10 in
          let '(eqv, st12) := cas_equal k gb ob st11 in
          let '(got, st13) := from_bits_v bits gb st12 in
          let '(lb, st14) := l_here st13 in
          let st15 := patch_rmw_phi ll sentinel lb got st14 in
          let st16 := l_term (ir_branch eqv ld ll) st15 in
          let st17 := l_start ld st16 in
          LOk (CVal old_t u, CVal new_t u) st17
      end
  | _, _ => l_err (ctx_loc ctx) ("unsupported atomic type " ++ c_type_diag_str u) st0
  end.

Definition atomic_rmw_value (family op which : string) (t : c_type) (addr : term)
  (v_expr : c_expr) (v0 : c_val) (loc : c_loc) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res c_val :=
  let to_t :=
    match t with
    | TPtr _ => if op == "xchg" then t else TLong
    | _ => t
    end in
  match assign_convert v_expr v0 to_t loc st0 with
  | LErr msg => LErr msg
  | LOk v1 st1 =>
      match rmw t addr op v1 ctx st1 with
      | LErr msg => LErr msg
      | LOk (old_v, new_v) st2 =>
          let r0 := if which == "old" then old_v else new_v in
          match t, r0 with
          | TPtr _, CVal a _ =>
              if (family == "c11") && negb (op == "xchg") then
                let '(i, st3) := l_let "l" (TAtom "ptoi") [a] st2 in
                let '(d, st4) := l_let "p" (TAtom "add") [ir_const 0; i] st3 in
                LOk (CVal d t) st4
              else LOk r0 st2
          | _, _ => LOk r0 st2
          end
      end
  end.

(** ## Compile-time constant predicates and classification helpers

    Port of [builtin_constant_p/3], [object_size/4], floating-point sign and
    bit classification helpers, and x87 80-bit long double decomposition. *)

Fixpoint literal_length_b (e : c_expr) : option Z :=
  match e with
  | ECast _ inner => literal_length_b inner
  | EStr bs => Some (Z.of_nat (length bs))
  | EWStr _ cs => Some (Z.of_nat (length cs))
  | _ => None
  end.

Fixpoint constant_pointer_b (e : c_expr) (env : c_type_env) : bool :=
  match e with
  | ECast _ inner =>
      if constant_pointer_b inner env then true
      else match const_value inner env with TOk _ => true | TErr _ => false end
  | _ => match literal_length_b e with Some _ => true | None => false end
  end.

Definition builtin_constant_p_b (e : c_expr) (env : c_type_env) : Z :=
  match constant_value e env with
  | TOk _ => 1
  | TErr _ =>
      if constant_pointer_b e env then 1
      else
        let check_idx (s idx : c_expr) : bool :=
          match literal_length_b s, const_value idx env with
          | Some n, TOk (k, _) => (0 <=? k) && (k <=? n)
          | _, _ => false
          end in
        match e with
        | EUn UDeref s => if check_idx s (ENum 0 SufNone RadDec) then 1 else 0
        | EIndex s idx => if check_idx s idx then 1 else 0
        | _ => 0
        end
  end.

Definition object_size_b (name : string) (args : list c_expr) (env : c_type_env) : option Z :=
  if (name == "__builtin_object_size") || (name == "__builtin_dynamic_object_size") then
    match args with
    | [_; ty_e] =>
        match const_value ty_e env with
        | TOk (k, _) =>
            if Z.eqb k 0 || Z.eqb k 1 then Some 18446744073709551615
            else if Z.eqb k 2 || Z.eqb k 3 then Some 0
            else None
        | TErr _ => None
        end
    | _ => None
    end
  else None.

Definition sign_bits_info (t : c_type) : option (string * string * Z * Z) :=
  match t with
  | TFloatK FFloat => Some ("s", "w", 2147483648, 2147483647)
  | TFloatK FDouble => Some ("d", "l", 9223372036854775808, 9223372036854775807)
  | _ => None
  end.

Definition trunc_format_info (t : c_type)
  : option (string * string * string * string * Z) :=
  match t with
  | TFloatK FFloat => Some ("s", "w", "stosi", "swtof", 1258291200)
  | TFloatK FDouble => Some ("d", "l", "dtosi", "sltof", 4841369599423283200)
  | _ => None
  end.

Fixpoint sign_bits_of (xs : list term) (k : string) (st0 : c_func_st)
  : list term * c_func_st :=
  match xs with
  | [] => ([], st0)
  | x :: rest =>
      let '(b, st1) := l_let k (TAtom "cast") [x] st0 in
      let '(bs, st2) := sign_bits_of rest k st1 in
      (b :: bs, st2)
  end.

Fixpoint sign_tops (xs : list term) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res (list (term * term) * list term) :=
  match xs with
  | [] => LOk ([], []) st0
  | x :: rest =>
      match l_local_slot TLDouble st0 with
      | LErr msg => LErr msg
      | LOk slot st1 =>
          match store_typed TLDouble x slot st1 with
          | LErr msg => LErr msg
          | LOk _ st2 =>
              let '(top, st3) := l_let "p" (TAtom "add") [slot; ir_const 8] st2 in
              match load_typed TUShort top ctx st3 with
              | LErr msg => LErr msg
              | LOk e st4 =>
                  match sign_tops rest ctx st4 with
                  | LErr msg => LErr msg
                  | LOk (sts, es) st5 => LOk ((slot, top) :: sts, e :: es) st5
                  end
              end
          end
      end
  end.

Definition sign_result (t : c_type) (op : string) (xs : list term)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res term :=
  match sign_bits_info t with
  | Some (f, k, sign, mask) =>
      let '(bs, st1) := sign_bits_of xs k st0 in
      let '(b1, st2) :=
        if op == "abs" then
          match bs with
          | [b] => l_let k (TAtom "and") [b; ir_const mask] st1
          | _ => (ir_const 0, st1)
          end
        else
          match bs with
          | [bx; by_] =>
              let '(mx, s1) := l_let k (TAtom "and") [bx; ir_const mask] st1 in
              let '(sy, s2) := l_let k (TAtom "and") [by_; ir_const sign] s1 in
              l_let k (TAtom "or") [mx; sy] s2
          | _ => (ir_const 0, st1)
          end in
      let '(r, st3) := l_let f (TAtom "cast") [b1] st2 in
      LOk r st3
  | None =>
      match sign_tops xs ctx st0 with
      | LErr msg => LErr msg
      | LOk (sts, es) st1 =>
          match sts, es with
          | (slot, top) :: _, e :: erest =>
              let '(e1, st2) :=
                if op == "abs" then l_let "w" (TAtom "and") [e; ir_const 32767] st1
                else
                  match erest with
                  | [ey] =>
                      let '(mx, s1) := l_let "w" (TAtom "and") [e; ir_const 32767] st1 in
                      let '(sy, s2) := l_let "w" (TAtom "and") [ey; ir_const 32768] s1 in
                      l_let "w" (TAtom "or") [mx; sy] s2
                  | _ => (e, st1)
                  end in
              match store_typed TUShort e1 top st2 with
              | LErr msg => LErr msg
              | LOk _ st3 => load_typed TLDouble slot ctx st3
              end
          | _, _ => l_err (ctx_loc ctx) "wrong sign_result arguments" st1
          end
      end
  end.

Fixpoint sign_args (cb : builtin_eval_cb) (args : list c_expr) (t : c_type)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list term) :=
  match args with
  | [] => LOk [] st0
  | a :: rest =>
      match be_rval cb a ctx st0 with
      | LErr msg => LErr msg
      | LOk v0 st1 =>
          match assign_convert a v0 t (ctx_loc ctx) st1 with
          | LErr msg => LErr msg
          | LOk (CVal x _) st2 =>
              match sign_args cb rest t ctx st2 with
              | LErr msg => LErr msg
              | LOk xs st3 => LOk (x :: xs) st3
              end
          end
      end
  end.

Record ld_class_flags : Type := mkLdClassFlags {
  ld_nan : term;
  ld_inf : term;
  ld_normal : term;
  ld_sub : term;
  ld_zero : term;
  ld_isnormal : term;
  ld_neg : term;
}.

Definition ld_classes (x : term) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res ld_class_flags :=
  match l_local_slot TLDouble st0 with
  | LErr msg => LErr msg
  | LOk slot st1 =>
      match store_typed TLDouble x slot st1 with
      | LErr msg => LErr msg
      | LOk _ st2 =>
          match load_typed TULong slot ctx st2 with
          | LErr msg => LErr msg
          | LOk s st3 =>
              let '(top, st4) := l_let "p" (TAtom "add") [slot; ir_const 8] st3 in
              match load_typed TUShort top ctx st4 with
              | LErr msg => LErr msg
              | LOk se st5 =>
                  let '(neg, st6) := l_let "w" (TAtom "shr") [se; ir_const 15] st5 in
                  let '(e, st7) := l_let "w" (TAtom "and") [se; ir_const 32767] st6 in
                  let '(ez, st8) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom "w"]) [e; ir_const 0] st7 in
                  let '(enz, st9) := l_let "w" (TAtom "xor") [ez; ir_const 1] st8 in
                  let '(emax, st10) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom "w"]) [e; ir_const 32767] st9 in
                  let '(enmax, st11) := l_let "w" (TAtom "xor") [emax; ir_const 1] st10 in
                  let '(i, st12) := l_let "w" (TApp "cmp" [TAtom "slt"; TAtom "l"]) [s; ir_const 0] st11 in
                  let '(noi, st13) := l_let "w" (TAtom "xor") [i; ir_const 1] st12 in
                  let '(sz, st14) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom "l"]) [s; ir_const 0] st13 in
                  let '(f, st15) := l_let "l" (TAtom "shl") [s; ir_const 1] st14 in
                  let '(fnz, st16) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom "l"]) [f; ir_const 0] st15 in
                  let '(bad, st17) := l_let "w" (TAtom "and") [enz; noi] st16 in
                  let '(hinan, st18) := l_let "w" (TAtom "and") [emax; fnz] st17 in
                  let '(nan, st19) := l_let "w" (TAtom "or") [bad; hinan] st18 in
                  let '(ei, st20) := l_let "w" (TAtom "and") [emax; i] st19 in
                  let '(fz, st21) := l_let "w" (TAtom "xor") [fnz; ir_const 1] st20 in
                  let '(inf, st22) := l_let "w" (TAtom "and") [ei; fz] st21 in
                  let '(zero, st23) := l_let "w" (TAtom "and") [ez; sz] st22 in
                  let '(snz, st24) := l_let "w" (TAtom "xor") [sz; ir_const 1] st23 in
                  let '(eznoi, st25) := l_let "w" (TAtom "and") [ez; noi] st24 in
                  let '(sub, st26) := l_let "w" (TAtom "and") [eznoi; snz] st25 in
                  let '(c1, st27) := l_let "w" (TAtom "add") [nan; inf] st26 in
                  let '(c2, st28) := l_let "w" (TAtom "add") [c1; zero] st27 in
                  let '(c3, st29) := l_let "w" (TAtom "add") [c2; sub] st28 in
                  let '(normal, st30) := l_let "w" (TAtom "xor") [c3; ir_const 1] st29 in
                  let '(mid, st31) := l_let "w" (TAtom "and") [enz; enmax] st30 in
                  let '(isnormal, st32) := l_let "w" (TAtom "and") [mid; i] st31 in
                  LOk (mkLdClassFlags nan inf normal sub zero isnormal neg) st32
              end
          end
      end
  end.

Definition ld_classified (name : string) (c : ld_class_flags) (st0 : c_func_st)
  : term * c_func_st :=
  if name == "__builtin_isinf" then (ld_inf c, st0)
  else if name == "__builtin_isinf_sign" then
    let '(t, st1) := l_let "w" (TAtom "and") [ld_inf c; ld_neg c] st0 in
    let '(t2, st2) := l_let "w" (TAtom "add") [t; t] st1 in
    l_let "w" (TAtom "sub") [ld_inf c; t2] st2
  else if name == "__builtin_isfinite" then
    let '(t, st1) := l_let "w" (TAtom "or") [ld_nan c; ld_inf c] st0 in
    l_let "w" (TAtom "xor") [t; ir_const 1] st1
  else (ld_isnormal c, st0).

Definition normal_flag (k : string) (abs_v : term) (inf_n min_n : Z) (st0 : c_func_st)
  : term * c_func_st :=
  let '(d, st1) := l_let k (TAtom "sub") [abs_v; ir_const min_n] st0 in
  let r := inf_n - min_n in
  l_let "w" (TApp "cmp" [TAtom "ult"; TAtom k]) [d; ir_const r] st1.

Definition classified_f (name k : string) (bits abs_v : term) (inf_n min_n : Z)
  (st0 : c_func_st) : term * c_func_st :=
  if name == "__builtin_isinf_sign" then
    let '(isinf, st1) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom k]) [abs_v; ir_const inf_n] st0 in
    let '(neg, st2) := l_let "w" (TApp "cmp" [TAtom "slt"; TAtom k]) [bits; ir_const 0] st1 in
    let '(t, st3) := l_let "w" (TAtom "and") [isinf; neg] st2 in
    let '(t2, st4) := l_let "w" (TAtom "add") [t; t] st3 in
    l_let "w" (TAtom "sub") [isinf; t2] st4
  else if name == "__builtin_isinf" then
    l_let "w" (TApp "cmp" [TAtom "eq"; TAtom k]) [abs_v; ir_const inf_n] st0
  else if name == "__builtin_isfinite" then
    l_let "w" (TApp "cmp" [TAtom "ult"; TAtom k]) [abs_v; ir_const inf_n] st0
  else if name == "__builtin_isnormal" then
    normal_flag k abs_v inf_n min_n st0
  else
    l_let "w" (TApp "cmp" [TAtom "slt"; TAtom k]) [bits; ir_const 0] st0.

Fixpoint class_sum (cb : builtin_eval_cb) (fs : list (term * c_expr))
  (ctx : c_lower_ctx) (acc : term) (st0 : c_func_st) : l_res term :=
  match fs with
  | [] => LOk acc st0
  | (flag, e) :: rest =>
      match be_rval cb e ctx st0 with
      | LErr msg => LErr msg
      | LOk v0 st1 =>
          match assign_convert e v0 TInt (ctx_loc ctx) st1 with
          | LErr msg => LErr msg
          | LOk (CVal x _) st2 =>
              let '(t, st3) := l_let "w" (TAtom "mul") [flag; x] st2 in
              let '(acc1, st4) := l_let "w" (TAtom "add") [acc; t] st3 in
              class_sum cb rest ctx acc1 st4
          end
      end
  end.

Definition float_bits_of_val (a : c_expr) (v0 : c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (string * term * term * Z * Z) :=
  match v0 with
  | CVal x (TFloatK FFloat) =>
      let '(bits, st1) := l_let "w" (TAtom "cast") [x] st0 in
      let '(abs_v, st2) := l_let "w" (TAtom "and") [bits; ir_const 2147483647] st1 in
      LOk ("w", bits, abs_v, 2139095040, 8388608) st2
  | _ =>
      match assign_convert a v0 TDouble (ctx_loc ctx) st0 with
      | LErr msg => LErr msg
      | LOk (CVal x _) st1 =>
          let '(bits, st2) := l_let "l" (TAtom "cast") [x] st1 in
          let '(abs_v, st3) := l_let "l" (TAtom "and") [bits; ir_const 9223372036854775807] st2 in
          LOk ("l", bits, abs_v, 9218868437227405312, 4503599627370496) st3
      end
  end.

(** ## Bit counting, byte swap, and 128-bit checked overflow arithmetic *)

Definition popcount64 (x : term) (st0 : c_func_st) : term * c_func_st :=
  let '(a1, st1) := l_let "l" (TAtom "shr") [x; ir_const 1] st0 in
  let '(a2, st2) := l_let "l" (TAtom "and") [a1; ir_const 6148914691236517205] st1 in
  let '(b, st3) := l_let "l" (TAtom "sub") [x; a2] st2 in
  let '(c1, st4) := l_let "l" (TAtom "and") [b; ir_const 3689348814741910323] st3 in
  let '(c2, st5) := l_let "l" (TAtom "shr") [b; ir_const 2] st4 in
  let '(c3, st6) := l_let "l" (TAtom "and") [c2; ir_const 3689348814741910323] st5 in
  let '(c, st7) := l_let "l" (TAtom "add") [c1; c3] st6 in
  let '(d1, st8) := l_let "l" (TAtom "shr") [c; ir_const 4] st7 in
  let '(d2, st9) := l_let "l" (TAtom "add") [c; d1] st8 in
  let '(d, st10) := l_let "l" (TAtom "and") [d2; ir_const 1085102592571150095] st9 in
  let '(e, st11) := l_let "l" (TAtom "mul") [d; ir_const 72340172838076673] st10 in
  l_let "l" (TAtom "shr") [e; ir_const 56] st11.

Fixpoint smear_bits (shs : list Z) (x : term) (st0 : c_func_st) : term * c_func_st :=
  match shs with
  | [] => (x, st0)
  | sh :: rest =>
      let '(t, st1) := l_let "l" (TAtom "shr") [x; ir_const sh] st0 in
      let '(x1, st2) := l_let "l" (TAtom "or") [x; t] st1 in
      smear_bits rest x1 st2
  end.

Definition bit_count (op : string) (bits : Z) (x0 : term) (st0 : c_func_st)
  : term * c_func_st :=
  if op == "popcount" then popcount64 x0 st0
  else if op == "ctz" then
    let '(x, st1) :=
      if bits <? 64 then l_let "l" (TAtom "or") [x0; ir_const (Z.shiftl 1 bits)] st0
      else (x0, st0) in
    let '(m, st2) := l_let "l" (TAtom "neg") [x] st1 in
    let '(low, st3) := l_let "l" (TAtom "and") [x; m] st2 in
    let '(below, st4) := l_let "l" (TAtom "sub") [low; ir_const 1] st3 in
    popcount64 below st4
  else if op == "ffs" then
    let '(m, st1) := l_let "l" (TAtom "neg") [x0] st0 in
    let '(low, st2) := l_let "l" (TAtom "and") [x0; m] st1 in
    let '(low2, st3) := l_let "l" (TAtom "add") [low; low] st2 in
    let '(upto, st4) := l_let "l" (TAtom "sub") [low2; ir_const 1] st3 in
    let '(p, st5) := popcount64 upto st4 in
    let '(any_, st6) := l_let "l" (TAtom "or") [x0; m] st5 in
    let '(nz, st7) := l_let "l" (TAtom "shr") [any_; ir_const 63] st6 in
    l_let "l" (TAtom "mul") [p; nz] st7
  else
    let '(s, st1) := smear_bits [1; 2; 4; 8; 16; 32] x0 st0 in
    let '(p, st2) := popcount64 s st1 in
    let '(negn, st3) := l_let "l" (TAtom "sub") [p; ir_const bits] st2 in
    l_let "l" (TAtom "neg") [negn] st3.

Fixpoint swapped_bytes (is_ : list Z) (x : term) (last : Z) (y0 : option term)
  (st0 : c_func_st) : term * c_func_st :=
  match is_ with
  | [] => (match y0 with Some y => y | None => ir_const 0 end, st0)
  | i :: rest =>
      let from_s := 8 * i in
      let to_s := 8 * (last - i) in
      let '(b0, st1) := l_let "l" (TAtom "shr") [x; ir_const from_s] st0 in
      let '(b, st2) := l_let "l" (TAtom "and") [b0; ir_const 255] st1 in
      let '(moved, st3) := l_let "l" (TAtom "shl") [b; ir_const to_s] st2 in
      let '(y1, st4) :=
        match y0 with
        | None => (moved, st3)
        | Some prev => l_let "l" (TAtom "or") [prev; moved] st3
        end in
      swapped_bytes rest x last (Some y1) st4
  end.

Definition overflow_operand (fixed : option c_type) (v : c_val) (st : c_func_st)
  : l_res c_val :=
  match fixed with
  | None => LOk v st
  | Some ty => convert_val v ty st
  end.

Definition overflow_widen (v : c_val) (st0 : c_func_st) : (term * term) * c_func_st :=
  let '(CVal x ty) := v in
  match int_info ty with
  | Some (sz, sg) =>
      let '(low, st1) :=
        if sz <? 8 then
          let ext := match sg with CSigned => "sw" | CUnsigned => "uw" end in
          l_let "l" (TApp "ext" [TAtom ext]) [x] st0
        else (x, st0) in
      match sg with
      | CSigned =>
          let '(hi, st2) := l_let "l" (TAtom "sar") [low; ir_const 63] st1 in
          ((low, hi), st2)
      | CUnsigned => ((low, ir_const 0), st1)
      end
  | None => ((x, ir_const 0), st0)
  end.

Definition overflow_exact (op : string) (x xh y yh : term) (st0 : c_func_st)
  : (term * term) * c_func_st :=
  if op == "add" then
    let '(low, st1) := l_let "l" (TAtom "add") [x; y] st0 in
    let '(carry, st2) := l_let "w" (TApp "cmp" [TAtom "ult"; TAtom "l"]) [low; x] st1 in
    let '(c, st3) := l_let "l" (TApp "ext" [TAtom "uw"]) [carry] st2 in
    let '(h, st4) := l_let "l" (TAtom "add") [xh; yh] st3 in
    let '(hi, st5) := l_let "l" (TAtom "add") [h; c] st4 in
    ((low, hi), st5)
  else if op == "sub" then
    let '(low, st1) := l_let "l" (TAtom "sub") [x; y] st0 in
    let '(borrow, st2) := l_let "w" (TApp "cmp" [TAtom "ult"; TAtom "l"]) [x; y] st1 in
    let '(c, st3) := l_let "l" (TApp "ext" [TAtom "uw"]) [borrow] st2 in
    let '(h, st4) := l_let "l" (TAtom "sub") [xh; yh] st3 in
    let '(hi, st5) := l_let "l" (TAtom "sub") [h; c] st4 in
    ((low, hi), st5)
  else
    let m32 := 4294967295 in
    let '(low, st1) := l_let "l" (TAtom "mul") [x; y] st0 in
    let '(xl, st2) := l_let "l" (TAtom "and") [x; ir_const m32] st1 in
    let '(xu, st3) := l_let "l" (TAtom "shr") [x; ir_const 32] st2 in
    let '(yl, st4) := l_let "l" (TAtom "and") [y; ir_const m32] st3 in
    let '(yu, st5) := l_let "l" (TAtom "shr") [y; ir_const 32] st4 in
    let '(ll, st6) := l_let "l" (TAtom "mul") [xl; yl] st5 in
    let '(ul, st7) := l_let "l" (TAtom "mul") [xu; yl] st6 in
    let '(lu, st8) := l_let "l" (TAtom "mul") [xl; yu] st7 in
    let '(uu, st9) := l_let "l" (TAtom "mul") [xu; yu] st8 in
    let '(llh, st10) := l_let "l" (TAtom "shr") [ll; ir_const 32] st9 in
    let '(ull, st11) := l_let "l" (TAtom "and") [ul; ir_const m32] st10 in
    let '(lul, st12) := l_let "l" (TAtom "and") [lu; ir_const m32] st11 in
    let '(mid0, st13) := l_let "l" (TAtom "add") [llh; ull] st12 in
    let '(mid, st14) := l_let "l" (TAtom "add") [mid0; lul] st13 in
    let '(carry, st15) := l_let "l" (TAtom "shr") [mid; ir_const 32] st14 in
    let '(ulh, st16) := l_let "l" (TAtom "shr") [ul; ir_const 32] st15 in
    let '(luh, st17) := l_let "l" (TAtom "shr") [lu; ir_const 32] st16 in
    let '(h0, st18) := l_let "l" (TAtom "add") [uu; ulh] st17 in
    let '(h1, st19) := l_let "l" (TAtom "add") [h0; luh] st18 in
    let '(h2, st20) := l_let "l" (TAtom "add") [h1; carry] st19 in
    let '(cx, st21) := l_let "l" (TAtom "and") [xh; y] st20 in
    let '(cy, st22) := l_let "l" (TAtom "and") [yh; x] st21 in
    let '(h3, st23) := l_let "l" (TAtom "sub") [h2; cx] st22 in
    let '(hi, st24) := l_let "l" (TAtom "sub") [h3; cy] st23 in
    ((low, hi), st24).

Definition checked_arithmetic (cb : builtin_eval_cb) (args : list c_expr)
  (op : string) (fixed : option c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res c_val :=
  let loc := ctx_loc ctx in
  match args with
  | [a; b; p] =>
      match be_rval cb a ctx st0 with
      | LErr msg => LErr msg
      | LOk va0 st1 =>
          match be_rval cb b ctx st1 with
          | LErr msg => LErr msg
          | LOk vb0 st2 =>
              match be_rval cb p ctx st2 with
              | LErr msg => LErr msg
              | LOk vp st3 =>
                  let '(CVal _ ta) := va0 in
                  let '(CVal _ tb) := vb0 in
                  match vp with
                  | CVal addr (TPtr ty) =>
                      let fixed_ok :=
                        match fixed with
                        | None => true
                        | Some ft => c_type_eqb ft ty
                        end in
                      if int_type ta && int_type tb && int_type ty && negb (c_type_eqb ty TBool) && fixed_ok then
                        match overflow_operand fixed va0 st3 with
                        | LErr msg => LErr msg
                        | LOk va st4 =>
                            match overflow_operand fixed vb0 st4 with
                            | LErr msg => LErr msg
                            | LOk vb st5 =>
                                let '((x, xh), st6) := overflow_widen va st5 in
                                let '((y, yh), st7) := overflow_widen vb st6 in
                                let '((low, hi), st8) := overflow_exact op x xh y yh st7 in
                                match convert_val (CVal low TULong) ty st8 with
                                | LErr msg => LErr msg
                                | LOk (CVal stored _) st9 =>
                                    match store_typed ty stored addr st9 with
                                    | LErr msg => LErr msg
                                    | LOk _ st10 =>
                                        let '((back, backh), st11) := overflow_widen (CVal stored ty) st10 in
                                        let '(bad_lo, st12) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom "l"]) [low; back] st11 in
                                        let '(bad_hi, st13) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom "l"]) [hi; backh] st12 in
                                        let '(flag, st14) := l_let "w" (TAtom "or") [bad_lo; bad_hi] st13 in
                                        LOk (CVal flag TBool) st14
                                    end
                                end
                            end
                        end
                      else l_err loc "invalid checked arithmetic operand types" st3
                  | _ => l_err loc "invalid checked arithmetic operand types" st3
                  end
              end
          end
      end
  | _ => l_err loc "checked arithmetic requires three arguments" st0
  end.

Definition cpu_word (sym : string) (off : Z) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res term :=
  let '(g, st1) := l_let "p" (TAtom "copy") [ir_global sym] st0 in
  let '(a, st2) := l_offset g off st1 in
  load_typed TUInt a ctx st2.

(** ## SSE, SSE4.2, AVX2, FMA, and generic vector intrinsic lowering

    All GNU vector builtins execute element by element over stack-allocated
    vector copies using C scalar arithmetic and branch-free selection [isel]. *)

Definition vk (n : Z) : c_val := CVal (ir_const n) TInt.

Definition isel (c a b : c_val) (t : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res c_val :=
  match convert_val a t st0 with
  | LErr msg => LErr msg
  | LOk a1 st1 =>
      match convert_val b t st1 with
      | LErr msg => LErr msg
      | LOk b1 st2 =>
          match binary_op BSub (vk 0) c ctx st2 with
          | LErr msg => LErr msg
          | LOk m0 st3 =>
              match convert_val m0 t st3 with
              | LErr msg => LErr msg
              | LOk m st4 =>
                  match binary_op BXor a1 b1 ctx st4 with
                  | LErr msg => LErr msg
                  | LOk d st5 =>
                      match binary_op BAnd d m ctx st5 with
                      | LErr msg => LErr msg
                      | LOk d1 st6 =>
                          match binary_op BXor b1 d1 ctx st6 with
                          | LErr msg => LErr msg
                          | LOk r0 st7 => convert_val r0 t st7
                          end
                      end
                  end
              end
          end
      end
  end.

Definition clamped_v (x : c_val) (lo hi : Z) (t : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res c_val :=
  let vlo := vk lo in
  let vhi := vk hi in
  match binary_op BLt x vlo ctx st0 with
  | LErr msg => LErr msg
  | LOk clo st1 =>
      match isel clo vlo x TLong ctx st1 with
      | LErr msg => LErr msg
      | LOk x1 st2 =>
          match binary_op BGt x1 vhi ctx st2 with
          | LErr msg => LErr msg
          | LOk chi st3 =>
              match isel chi vhi x1 TLong ctx st3 with
              | LErr msg => LErr msg
              | LOk x2 st4 => convert_val x2 t st4
              end
          end
      end
  end.

Definition v_lanes (v : c_val) (vt : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  let '(CVal addr _) := v in
  match vt with
  | TVec e _ _ =>
      match lanes_loaded vt addr ctx st0 with
      | LErr msg => LErr msg
      | LOk xs st1 => LOk (map (fun x => CVal x e) xs) st1
      end
  | _ => l_err (ctx_loc ctx) "not a vector type" st0
  end.

Fixpoint lane_converted (ls : list c_val) (e : c_type) (st0 : c_func_st)
  : l_res (list term) :=
  match ls with
  | [] => LOk [] st0
  | l :: rest =>
      match convert_val l e st0 with
      | LErr msg => LErr msg
      | LOk (CVal x _) st1 =>
          match lane_converted rest e st1 with
          | LErr msg => LErr msg
          | LOk xs st2 => LOk (x :: xs) st2
          end
      end
  end.

Definition v_made (vt : c_type) (ls : list c_val) (st0 : c_func_st) : l_res c_val :=
  match vt with
  | TVec e n _ =>
      if Z.eqb (Z.of_nat (length ls)) n then
        match lane_converted ls e st0 with
        | LErr msg => LErr msg
        | LOk xs st1 =>
            match l_local_slot vt st1 with
            | LErr msg => LErr msg
            | LOk addr st2 =>
                match lanes_stored vt addr 0 xs st2 with
                | LErr msg => LErr msg
                | LOk _ st3 => LOk (CVal addr vt) st3
                end
            end
        end
      else LErr "vector arity"
  | _ => LErr "vector arity"
  end.

Definition v_imm (a : c_expr) (ctx : c_lower_ctx) (st : c_func_st) : l_res Z :=
  match const_value a (fs_env st) with
  | TOk (i, _) => LOk i st
  | TErr _ => l_err (ctx_loc ctx) "this vector builtin needs a constant operand" st
  end.

Definition nth_cval (idx : Z) (xs : list c_val) : c_val :=
  nth (Z.to_nat idx) xs (vk 0).

Definition unsigned_type_v (e : c_type) : option c_type :=
  match int_info e with
  | Some (1, _) => Some TUChar
  | Some (2, _) => Some TUShort
  | Some (4, _) => Some TUInt
  | Some (8, _) => Some TULLong
  | _ => None
  end.

Definition v16qu : c_type := TVec TUChar 16 16.
Definition v8hu : c_type := TVec TUShort 8 16.
Definition v4su : c_type := TVec TUInt 4 16.
Definition v2du : c_type := TVec TULLong 2 16.
Definition v16qi : c_type := TVec TChar 16 16.
Definition v8hi : c_type := TVec TShort 8 16.
Definition v4si : c_type := TVec TInt 4 16.
Definition v2di : c_type := TVec TLLong 2 16.

Fixpoint clmul_bits_f (fuel : nat) (i : Z) (a b : c_val) (ctx : c_lower_ctx)
  (lo0 hi0 : c_val) (st0 : c_func_st) : l_res (c_val * c_val) :=
  match fuel with
  | O => LOk (lo0, hi0) st0
  | S f =>
      if Z.eqb i 64 then LOk (lo0, hi0) st0
      else
        match binary_op BShr b (vk i) ctx st0 with
        | LErr msg => LErr msg
        | LOk b1 st1 =>
            match binary_op BAnd b1 (CVal (ir_const 1) TULLong) ctx st1 with
            | LErr msg => LErr msg
            | LOk bit st2 =>
                match binary_op BSub (CVal (ir_const 0) TULLong) bit ctx st2 with
                | LErr msg => LErr msg
                | LOk m st3 =>
                    match binary_op BShl a (vk i) ctx st3 with
                    | LErr msg => LErr msg
                    | LOk al st4 =>
                        match binary_op BAnd al m ctx st4 with
                        | LErr msg => LErr msg
                        | LOk tl st5 =>
                            match binary_op BXor lo0 tl ctx st5 with
                            | LErr msg => LErr msg
                            | LOk lo1 st6 =>
                                if Z.eqb i 0 then
                                  clmul_bits_f f (i + 1) a b ctx lo1 hi0 st6
                                else
                                  match binary_op BShr a (vk (64 - i)) ctx st6 with
                                  | LErr msg => LErr msg
                                  | LOk ah st7 =>
                                      match binary_op BAnd ah m ctx st7 with
                                      | LErr msg => LErr msg
                                      | LOk th st8 =>
                                          match binary_op BXor hi0 th ctx st8 with
                                          | LErr msg => LErr msg
                                          | LOk hi1 st9 =>
                                              clmul_bits_f f (i + 1) a b ctx lo1 hi1 st9
                                          end
                                      end
                                  end
                            end
                        end
                    end
                end
            end
        end
  end.

Definition pcmpstr_info (name : string) : option (string * string) :=
  let check_len (len : string) : option (string * string) :=
    match strip_prefix ("pcmp" ++ len ++ "str") name with
    | None => None
    | Some rest =>
        if rest == "m128" then Some (len, "m")
        else if rest == "i128" then Some (len, "i")
        else if rest == "ia128" then Some (len, "ia")
        else if rest == "ic128" then Some (len, "ic")
        else if rest == "io128" then Some (len, "io")
        else if rest == "is128" then Some (len, "is")
        else if rest == "iz128" then Some (len, "iz")
        else None
    end in
  match check_len "i" with
  | Some r => Some r
  | None => check_len "e"
  end.

Definition pcmp_format (i : Z) : c_type :=
  let f := Z.land i 3 in
  if Z.eqb f 0 then TVec TUChar 16 16
  else if Z.eqb f 1 then TVec TUShort 8 16
  else if Z.eqb f 2 then TVec TSChar 16 16
  else TVec TShort 8 16.

Fixpoint pcmp_nonzero (ls : list c_val) (p : c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match ls with
  | [] => LOk [] st0
  | l :: rest =>
      match binary_op BNe l (vk 0) ctx st0 with
      | LErr msg => LErr msg
      | LOk nz st1 =>
          match binary_op BAnd p nz ctx st1 with
          | LErr msg => LErr msg
          | LOk v st2 =>
              match pcmp_nonzero rest v ctx st2 with
              | LErr msg => LErr msg
              | LOk vs st3 => LOk (v :: vs) st3
              end
          end
      end
  end.

Fixpoint pcmp_below (js : list Z) (a : c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match js with
  | [] => LOk [] st0
  | j :: rest =>
      match binary_op BLt (CVal (ir_const j) TLong) a ctx st0 with
      | LErr msg => LErr msg
      | LOk v st1 =>
          match pcmp_below rest a ctx st1 with
          | LErr msg => LErr msg
          | LOk vs st2 => LOk (v :: vs) st2
          end
      end
  end.

Definition pcmp_valid (len : string) (ls : list c_val) (lv : option c_val)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  if len == "i" then pcmp_nonzero ls (vk 1) ctx st0
  else
    match lv with
    | None => LOk [] st0
    | Some lv0 =>
        match convert_val lv0 TLong st0 with
        | LErr msg => LErr msg
        | LOk l st1 =>
            match binary_op BLt l (CVal (ir_const 0) TLong) ctx st1 with
            | LErr msg => LErr msg
            | LOk neg st2 =>
                match binary_op BSub (CVal (ir_const 0) TLong) l ctx st2 with
                | LErr msg => LErr msg
                | LOk negl st3 =>
                    match isel neg negl l TLong ctx st3 with
                    | LErr msg => LErr msg
                    | LOk abs_v st4 =>
                        let js := numlist_Z 0 (Z.of_nat (length ls) - 1) in
                        pcmp_below js abs_v ctx st4
                    end
                end
            end
        end
    end.

Fixpoint pcmp_masked (xs vs : list c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match xs, vs with
  | x :: rx, v :: rv =>
      match isel v x (vk 65536) TInt ctx st0 with
      | LErr msg => LErr msg
      | LOk y st1 =>
          match pcmp_masked rx rv ctx st1 with
          | LErr msg => LErr msg
          | LOk ys st2 => LOk (y :: ys) st2
          end
      end
  | _, _ => LOk [] st0
  end.

Fixpoint pcmp_masked_ranges (xs vs : list c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match xs, vs with
  | lo :: hi :: rx, vlo :: vhi :: rv =>
      match binary_op BAnd vlo vhi ctx st0 with
      | LErr msg => LErr msg
      | LOk v st1 =>
          match isel v lo (vk 65536) TInt ctx st1 with
          | LErr msg => LErr msg
          | LOk lo1 st2 =>
              match convert_val hi TInt st2 with
              | LErr msg => LErr msg
              | LOk hi1 st3 =>
                  match pcmp_masked_ranges rx rv ctx st3 with
                  | LErr msg => LErr msg
                  | LOk ys st4 => LOk (lo1 :: hi1 :: ys) st4
                  end
              end
          end
      end
  | _, _ => LOk [] st0
  end.

Fixpoint pcmp_nots (vs : list c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match vs with
  | [] => LOk [] st0
  | v :: rest =>
      match binary_op BXor v (vk 1) ctx st0 with
      | LErr msg => LErr msg
      | LOk n st1 =>
          match pcmp_nots rest ctx st1 with
          | LErr msg => LErr msg
          | LOk ns st2 => LOk (n :: ns) st2
          end
      end
  end.

Fixpoint pcmp_any (as_ : list c_val) (b : c_val) (ctx : c_lower_ctx)
  (acc : c_val) (st0 : c_func_st) : l_res c_val :=
  match as_ with
  | [] => LOk acc st0
  | a :: rest =>
      match binary_op BEq a b ctx st0 with
      | LErr msg => LErr msg
      | LOk e st1 =>
          match binary_op BOr acc e ctx st1 with
          | LErr msg => LErr msg
          | LOk acc1 st2 => pcmp_any rest b ctx acc1 st2
          end
      end
  end.

Fixpoint pcmp_ranges (as_ : list c_val) (b : c_val) (ctx : c_lower_ctx)
  (acc : c_val) (st0 : c_func_st) : l_res c_val :=
  match as_ with
  | lo :: hi :: rest =>
      match binary_op BLe lo b ctx st0 with
      | LErr msg => LErr msg
      | LOk c1 st1 =>
          match binary_op BLe b hi ctx st1 with
          | LErr msg => LErr msg
          | LOk c2 st2 =>
              match binary_op BAnd c1 c2 ctx st2 with
              | LErr msg => LErr msg
              | LOk c st3 =>
                  match binary_op BOr acc c ctx st3 with
                  | LErr msg => LErr msg
                  | LOk acc1 st4 => pcmp_ranges rest b ctx acc1 st4
                  end
              end
          end
      end
  | _ => LOk acc st0
  end.

Fixpoint pcmp_ordered (ks : list Z) (j : Z) (as_ bs nas : list c_val)
  (ctx : c_lower_ctx) (acc : c_val) (st0 : c_func_st) : l_res c_val :=
  match ks with
  | [] => LOk acc st0
  | k :: rest =>
      let a := nth_cval k as_ in
      let na := nth_cval k nas in
      let b := nth_cval (j + k) bs in
      match binary_op BEq a b ctx st0 with
      | LErr msg => LErr msg
      | LOk e st1 =>
          match binary_op BOr na e ctx st1 with
          | LErr msg => LErr msg
          | LOk t st2 =>
              match binary_op BAnd acc t ctx st2 with
              | LErr msg => LErr msg
              | LOk acc1 st3 => pcmp_ordered rest j as_ bs nas ctx acc1 st3
              end
          end
      end
  end.

Definition pcmp_bit (agg j : Z) (as_ bs vas vbs : list c_val)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  if Z.eqb agg 0 then
    let b := nth_cval j bs in
    let vb := nth_cval j vbs in
    match pcmp_any as_ b ctx (vk 0) st0 with
    | LErr msg => LErr msg
    | LOk any_ st1 => binary_op BAnd any_ vb ctx st1
    end
  else if Z.eqb agg 1 then
    let b := nth_cval j bs in
    let vb := nth_cval j vbs in
    match pcmp_ranges as_ b ctx (vk 0) st0 with
    | LErr msg => LErr msg
    | LOk any_ st1 => binary_op BAnd any_ vb ctx st1
    end
  else if Z.eqb agg 2 then
    let a := nth_cval j as_ in
    let b := nth_cval j bs in
    let va := nth_cval j vas in
    let vb := nth_cval j vbs in
    match binary_op BEq a b ctx st0 with
    | LErr msg => LErr msg
    | LOk e st1 =>
        match binary_op BAnd va vb ctx st1 with
        | LErr msg => LErr msg
        | LOk both st2 =>
            match binary_op BAnd both e ctx st2 with
            | LErr msg => LErr msg
            | LOk t st3 =>
                match binary_op BOr va vb ctx st3 with
                | LErr msg => LErr msg
                | LOk either st4 =>
                    match binary_op BXor either (vk 1) ctx st4 with
                    | LErr msg => LErr msg
                    | LOk neither st5 => binary_op BOr t neither ctx st5
                    end
                end
            end
        end
    end
  else
    let n := Z.of_nat (length as_) in
    let ks := numlist_Z 0 (n - 1 - j) in
    pcmp_ordered ks j as_ bs vas ctx (vk 1) st0.

Fixpoint pcmp_bits (js : list Z) (agg : Z) (as_ bs vas vbs : list c_val)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  match js with
  | [] => LOk [] st0
  | j :: rest =>
      match pcmp_bit agg j as_ bs vas vbs ctx st0 with
      | LErr msg => LErr msg
      | LOk r st1 =>
          match pcmp_bits rest agg as_ bs vas vbs ctx st1 with
          | LErr msg => LErr msg
          | LOk rs st2 => LOk (r :: rs) st2
          end
      end
  end.

Definition pcmp_aggregated (agg : Z) (as0 bs0 vas vbs : list c_val)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  let js := numlist_Z 0 (Z.of_nat (length bs0) - 1) in
  if Z.eqb agg 0 then
    match pcmp_masked as0 vas ctx st0 with
    | LErr msg => LErr msg
    | LOk as_ st1 => pcmp_bits js 0 as_ bs0 vas vbs ctx st1
    end
  else if Z.eqb agg 1 then
    match pcmp_masked_ranges as0 vas ctx st0 with
    | LErr msg => LErr msg
    | LOk as_ st1 => pcmp_bits js 1 as_ bs0 vas vbs ctx st1
    end
  else if Z.eqb agg 3 then
    match pcmp_masked bs0 vbs ctx st0 with
    | LErr msg => LErr msg
    | LOk bs st1 =>
        match pcmp_nots vas ctx st1 with
        | LErr msg => LErr msg
        | LOk nas st2 => pcmp_bits js 3 as0 bs nas vbs ctx st2
        end
    end
  else pcmp_bits js agg as0 bs0 vas vbs ctx st0.

Fixpoint pcmp_xors (rs : list c_val) (oms : option (list c_val))
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  match rs with
  | [] => LOk [] st0
  | r :: rest =>
      let '(m, oms1) :=
        match oms with
        | None => (vk 1, None)
        | Some (m0 :: ms1) => (m0, Some ms1)
        | Some [] => (vk 1, Some [])
        end in
      match binary_op BXor r m ctx st0 with
      | LErr msg => LErr msg
      | LOk x st1 =>
          match pcmp_xors rest oms1 ctx st1 with
          | LErr msg => LErr msg
          | LOk xs st2 => LOk (x :: xs) st2
          end
      end
  end.

Definition pcmp_polarity (pol : Z) (r1 vbs : list c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  if Z.eqb (Z.land pol 1) 0 then LOk r1 st0
  else if Z.eqb pol 1 then pcmp_xors r1 None ctx st0
  else pcmp_xors r1 (Some vbs) ctx st0.

Fixpoint pcmp_mask (bs : list c_val) (js : list Z) (ctx : c_lower_ctx)
  (m0 : c_val) (st0 : c_func_st) : l_res c_val :=
  match bs, js with
  | b :: rb, j :: rj =>
      match binary_op BShl b (vk j) ctx st0 with
      | LErr msg => LErr msg
      | LOk s st1 =>
          match binary_op BOr m0 s ctx st1 with
          | LErr msg => LErr msg
          | LOk m1 st2 => pcmp_mask rb rj ctx m1 st2
          end
      end
  | _, _ => LOk m0 st0
  end.

Fixpoint pcmp_units (bs : list c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match bs with
  | [] => LOk [] st0
  | b :: rest =>
      match binary_op BSub (vk 0) b ctx st0 with
      | LErr msg => LErr msg
      | LOk u st1 =>
          match pcmp_units rest ctx st1 with
          | LErr msg => LErr msg
          | LOk us st2 => LOk (u :: us) st2
          end
      end
  end.

Fixpoint pcmp_or_acc (bs : list c_val) (ctx : c_lower_ctx) (r0 : c_val)
  (st0 : c_func_st) : l_res c_val :=
  match bs with
  | [] => LOk r0 st0
  | b :: rest =>
      match binary_op BOr r0 b ctx st0 with
      | LErr msg => LErr msg
      | LOk r1 st1 => pcmp_or_acc rest ctx r1 st1
      end
  end.

Definition pcmp_or (bs : list c_val) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  match bs with
  | [] => LOk (vk 0) st0
  | b :: rest => pcmp_or_acc rest ctx b st0
  end.

Definition pcmp_result (out_k : string) (msb : Z) (vt : c_type) (n : Z)
  (r2 : list c_val) (js : list Z) (r20 van vbn : c_val) (ret : c_type)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  if out_k == "i" then
    if Z.eqb msb 0 then
      match pcmp_mask r2 js ctx (vk 0) st0 with
      | LErr msg => LErr msg
      | LOk m0 st1 =>
          let stop := Z.shiftl 1 n in
          match binary_op BOr m0 (vk stop) ctx st1 with
          | LErr msg => LErr msg
          | LOk m1 st2 =>
              match convert_val m1 TULLong st2 with
              | LErr msg => LErr msg
              | LOk (CVal x _) st3 =>
                  let '(c, st4) := bit_count "ctz" 32 x st3 in
                  let '(i, st5) := l_let "w" (TAtom "copy") [c] st4 in
                  LOk (CVal i TInt) st5
              end
          end
      end
    else
      match pcmp_mask r2 js ctx (vk 0) st0 with
      | LErr msg => LErr msg
      | LOk m st1 =>
          match convert_val m TULLong st1 with
          | LErr msg => LErr msg
          | LOk (CVal x _) st2 =>
              let '(s, st3) := smear_bits [1; 2; 4; 8; 16] x st2 in
              let '(p, st4) := popcount64 s st3 in
              let '(hi, st5) := l_let "l" (TAtom "sub") [p; ir_const 1] st4 in
              let '(hiw, st6) := l_let "w" (TAtom "copy") [hi] st5 in
              match binary_op BEq m (vk 0) ctx st6 with
              | LErr msg => LErr msg
              | LOk none_ st7 => isel none_ (vk n) (CVal hiw TInt) TInt ctx st7
              end
          end
      end
  else if out_k == "m" then
    if Z.eqb msb 0 then
      match pcmp_mask r2 js ctx (vk 0) st0 with
      | LErr msg => LErr msg
      | LOk m st1 =>
          let z := vk 0 in
          match v_made (TVec TUShort 8 16) [m; z; z; z; z; z; z; z] st1 with
          | LErr msg => LErr msg
          | LOk (CVal addr _) st2 => LOk (CVal addr ret) st2
          end
      end
    else
      match pcmp_units r2 ctx st0 with
      | LErr msg => LErr msg
      | LOk us st1 =>
          match v_made vt us st1 with
          | LErr msg => LErr msg
          | LOk (CVal addr _) st2 => LOk (CVal addr ret) st2
          end
      end
  else if out_k == "ic" then pcmp_or r2 ctx st0
  else if out_k == "ia" then
    match pcmp_or r2 ctx st0 with
    | LErr msg => LErr msg
    | LOk c st1 =>
        match binary_op BXor c (vk 1) ctx st1 with
        | LErr msg => LErr msg
        | LOk nc st2 => binary_op BAnd nc vbn ctx st2
        end
    end
  else if out_k == "io" then LOk r20 st0
  else if out_k == "is" then binary_op BXor van (vk 1) ctx st0
  else binary_op BXor vbn (vk 1) ctx st0.

Fixpoint addsub_lanes (as_ bs : list c_val) (j : Z) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match as_, bs with
  | a :: ra, b :: rb =>
      let op := if Z.eqb (Z.land j 1) 0 then BSub else BAdd in
      match binary_op op a b ctx st0 with
      | LErr msg => LErr msg
      | LOk o st1 =>
          match addsub_lanes ra rb (j + 1) ctx st1 with
          | LErr msg => LErr msg
          | LOk os st2 => LOk (o :: os) st2
          end
      end
  | _, _ => LOk [] st0
  end.

Fixpoint fma_lanes (as_ bs cs : list c_val) (sub_even : bool) (j : Z)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  match as_, bs, cs with
  | CVal x e :: ra, CVal y _ :: rb, c0 :: rc =>
      let c_res :=
        if sub_even && Z.eqb (Z.land j 1) 0 then unary_op UNeg c0 ctx st0
        else LOk c0 st0 in
      match c_res with
      | LErr msg => LErr msg
      | LOk (CVal z _) st1 =>
          let '(k, f) :=
            match e with
            | TFloatK FFloat => ("s", "fmaf")
            | _ => ("d", "fma")
            end in
          let '(d, st2) := l_fresh st1 in
          let st3 :=
            l_emit (ir_call (ir_result d k) (ir_global f)
                      [ir_arg k x; ir_arg k y; ir_arg k z]) st2 in
          match fma_lanes ra rb rc sub_even (j + 1) ctx st3 with
          | LErr msg => LErr msg
          | LOk os st4 => LOk (CVal d e :: os) st4
          end
      end
  | _, _, _ => LOk [] st0
  end.

Definition half_type (vt : c_type) : c_type :=
  match vt with
  | TVec e n _ => TVec e (Z.div n 2) 16
  | _ => vt
  end.

Fixpoint v_halves (vs : list c_val) (off : Z) (st0 : c_func_st)
  : list c_val * c_func_st :=
  match vs with
  | [] => ([], st0)
  | v :: rest =>
      let '(h, st1) :=
        match v with
        | CVal a (TVec _ _ _ as vt) =>
            match type_size_align vt (fs_env st0) with
            | TOk (32, _) =>
                let ht := half_type vt in
                let '(b, s1) := l_offset a off st0 in
                (CVal b ht, s1)
            | _ => (v, st0)
            end
        | _ => (v, st0)
        end in
      let '(hs, st2) := v_halves rest off st1 in
      (h :: hs, st2)
  end.

Definition perm2_half (j i : Z) (va vb c : term) (st0 : c_func_st) : l_res unit :=
  let s := Z.land (Z.shiftr i (4 * j)) 15 in
  let off := 16 * j in
  let ht := TVec TULLong 2 16 in
  let '(d, st1) := l_offset c off st0 in
  if negb (Z.eqb (Z.land s 8) 0) then
    lanes_stored ht d 0 [ir_const 0; ir_const 0] st1
  else
    let src0 := if Z.eqb (Z.land s 2) 0 then va else vb in
    let soff := 16 * Z.land s 1 in
    let '(src, st2) := l_offset src0 soff st1 in
    copy_object ht src d st2.

Fixpoint v_permuted (is_ : list c_val) (va : term) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match is_ with
  | [] => LOk [] st0
  | i :: rest =>
      match binary_op BAnd i (vk 7) ctx st0 with
      | LErr msg => LErr msg
      | LOk j st1 =>
          match binary_op BShl j (vk 2) ctx st1 with
          | LErr msg => LErr msg
          | LOk off0 st2 =>
              match convert_val off0 TLong st2 with
              | LErr msg => LErr msg
              | LOk (CVal off _) st3 =>
                  let '(p, st4) := l_let "p" (TAtom "add") [va; off] st3 in
                  match load_typed TUInt p ctx st4 with
                  | LErr msg => LErr msg
                  | LOk x st5 =>
                      match v_permuted rest va ctx st5 with
                      | LErr msg => LErr msg
                      | LOk ls st6 => LOk (CVal x TUInt :: ls) st6
                      end
                  end
              end
          end
      end
  end.

Fixpoint v_sign_bits (ls : list c_val) (i bit : Z) (ctx : c_lower_ctx)
  (m0 : c_val) (st0 : c_func_st) : l_res c_val :=
  match ls with
  | [] => LOk m0 st0
  | l :: rest =>
      match binary_op BShr l (vk bit) ctx st0 with
      | LErr msg => LErr msg
      | LOk b0 st1 =>
          match convert_val b0 TInt st1 with
          | LErr msg => LErr msg
          | LOk b st2 =>
              match binary_op BShl b (vk i) ctx st2 with
              | LErr msg => LErr msg
              | LOk b1 st3 =>
                  match binary_op BOr m0 b1 ctx st3 with
                  | LErr msg => LErr msg
                  | LOk m1 st4 => v_sign_bits rest (i + 1) bit ctx m1 st4
                  end
              end
          end
      end
  end.

Definition shift_builtin_info (name : string) : option (string * string) :=
  if (name == "psllwi128") || (name == "pslldi128") || (name == "psllqi128") then Some ("shl", "imm")
  else if (name == "psllw128") || (name == "pslld128") || (name == "psllq128") then Some ("shl", "vector")
  else if (name == "psrlwi128") || (name == "psrldi128") || (name == "psrlqi128") then Some ("shr", "imm")
  else if (name == "psrlw128") || (name == "psrld128") || (name == "psrlq128") then Some ("shr", "vector")
  else if (name == "psrawi128") || (name == "psradi128") then Some ("sar", "imm")
  else if (name == "psraw128") || (name == "psrad128") then Some ("sar", "vector")
  else None.

Fixpoint shift_each (ls : list c_val) (kind : string) (s in_range : c_val)
  (ue : c_type) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  match ls with
  | [] => LOk [] st0
  | l :: rest =>
      let o_res :=
        if kind == "sar" then binary_op BShr l s ctx st0
        else
          let op := if kind == "shl" then BShl else BShr in
          match binary_op op l s ctx st0 with
          | LErr msg => LErr msg
          | LOk o0 st1 =>
              match convert_val o0 ue st1 with
              | LErr msg => LErr msg
              | LOk o1 st2 => isel in_range o1 (vk 0) ue ctx st2
              end
          end in
      match o_res with
      | LErr msg => LErr msg
      | LOk o st1 =>
          match shift_each rest kind s in_range ue ctx st1 with
          | LErr msg => LErr msg
          | LOk os st2 => LOk (o :: os) st2
          end
      end
  end.

Definition shifted_lanes (kind : string) (v c : c_val) (ret : c_type)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  match ret with
  | TVec e n al =>
      match int_info e, unsigned_type_v e with
      | Some (bytes, _), Some ue =>
          let bits := 8 * bytes in
          let max_s := bits - 1 in
          let lt := if kind == "sar" then TVec e n al else TVec ue n al in
          match convert_val c TULLong st0 with
          | LErr msg => LErr msg
          | LOk cu st1 =>
              match binary_op BLt cu (vk bits) ctx st1 with
              | LErr msg => LErr msg
              | LOk in_range st2 =>
                  let s_res :=
                    if kind == "sar" then isel in_range cu (vk max_s) TInt ctx st2
                    else
                      match binary_op BAnd cu (vk max_s) ctx st2 with
                      | LErr msg => LErr msg
                      | LOk s0 st3 => convert_val s0 TInt st3
                      end in
                  match s_res with
                  | LErr msg => LErr msg
                  | LOk s st3 =>
                      match v_lanes v lt ctx st3 with
                      | LErr msg => LErr msg
                      | LOk ls st4 =>
                          match shift_each ls kind s in_range ue ctx st4 with
                          | LErr msg => LErr msg
                          | LOk out st5 => v_made ret out st5
                          end
                      end
                  end
              end
          end
      | _, _ => l_err (ctx_loc ctx) "unsupported vector shift element type" st0
      end
  | _ => l_err (ctx_loc ctx) "not a vector type" st0
  end.

Fixpoint clamp_all (ls : list c_val) (lo hi : Z) (t : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match ls with
  | [] => LOk [] st0
  | l :: rest =>
      match convert_val l TLong st0 with
      | LErr msg => LErr msg
      | LOk l1 st1 =>
          match clamped_v l1 lo hi t ctx st1 with
          | LErr msg => LErr msg
          | LOk o st2 =>
              match clamp_all rest lo hi t ctx st2 with
              | LErr msg => LErr msg
              | LOk os st3 => LOk (o :: os) st3
              end
          end
      end
  end.

Definition shuffled_idx (name : string) (i j : Z) : Z :=
  if name == "pshufd" then Z.land (Z.shiftr i (2 * j)) 3
  else if name == "pshuflw" then
    if j <? 4 then Z.land (Z.shiftr i (2 * j)) 3 else j
  else
    if 4 <=? j then 4 + Z.land (Z.shiftr i (2 * (j - 4))) 3 else j.

Fixpoint v_blendv (as_ bs ms : list c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match as_, bs, ms with
  | a :: ra, b :: rb, (CVal _ t as m) :: rm =>
      match binary_op BLt m (vk 0) ctx st0 with
      | LErr msg => LErr msg
      | LOk c st1 =>
          match isel c b a t ctx st1 with
          | LErr msg => LErr msg
          | LOk o st2 =>
              match v_blendv ra rb rm ctx st2 with
              | LErr msg => LErr msg
              | LOk os st3 => LOk (o :: os) st3
              end
          end
      end
  | _, _, _ => LOk [] st0
  end.

Fixpoint pair_products (as_ bs : list c_val) (t : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match as_, bs with
  | a0 :: a1 :: ra, b0 :: b1 :: rb =>
      match convert_val a0 TInt st0 with
      | LErr msg => LErr msg
      | LOk x0 st1 =>
          match convert_val a1 TInt st1 with
          | LErr msg => LErr msg
          | LOk x1 st2 =>
              match convert_val b0 TInt st2 with
              | LErr msg => LErr msg
              | LOk y0 st3 =>
                  match convert_val b1 TInt st3 with
                  | LErr msg => LErr msg
                  | LOk y1 st4 =>
                      match binary_op BMul x0 y0 ctx st4 with
                      | LErr msg => LErr msg
                      | LOk p0 st5 =>
                          match binary_op BMul x1 y1 ctx st5 with
                          | LErr msg => LErr msg
                          | LOk p1 st6 =>
                              match convert_val p0 t st6 with
                              | LErr msg => LErr msg
                              | LOk q0 st7 =>
                                  match convert_val p1 t st7 with
                                  | LErr msg => LErr msg
                                  | LOk q1 st8 =>
                                      match binary_op BAdd q0 q1 ctx st8 with
                                      | LErr msg => LErr msg
                                      | LOk s st9 =>
                                          match pair_products ra rb t ctx st9 with
                                          | LErr msg => LErr msg
                                          | LOk ss st10 => LOk (s :: ss) st10
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end
  | _, _ => LOk [] st0
  end.

Fixpoint abs_diff_sum (as_ bs : list c_val) (ctx : c_lower_ctx) (s0 : c_val)
  (st0 : c_func_st) : l_res c_val :=
  match as_, bs with
  | a :: ra, b :: rb =>
      match binary_op BSub a b ctx st0 with
      | LErr msg => LErr msg
      | LOk d st1 =>
          match binary_op BLt d (vk 0) ctx st1 with
          | LErr msg => LErr msg
          | LOk neg st2 =>
              match binary_op BSub (vk 0) d ctx st2 with
              | LErr msg => LErr msg
              | LOk nd st3 =>
                  match isel neg nd d TInt ctx st3 with
                  | LErr msg => LErr msg
                  | LOk ad st4 =>
                      match binary_op BAdd s0 ad ctx st4 with
                      | LErr msg => LErr msg
                      | LOk s1 st5 => abs_diff_sum ra rb ctx s1 st5
                      end
                  end
              end
          end
      end
  | _, _ => LOk s0 st0
  end.

Fixpoint v_mulhi (as_ bs : list c_val) (shift : Z) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match as_, bs with
  | a :: ra, b :: rb =>
      match binary_op BMul a b ctx st0 with
      | LErr msg => LErr msg
      | LOk p st1 =>
          match binary_op BShr p (vk shift) ctx st1 with
          | LErr msg => LErr msg
          | LOk o st2 =>
              match v_mulhi ra rb shift ctx st2 with
              | LErr msg => LErr msg
              | LOk os st3 => LOk (o :: os) st3
              end
          end
      end
  | _, _ => LOk [] st0
  end.

Fixpoint v_horizontal (ls : list c_val) (op : c_binop) (sat : bool)
  (e : c_type) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  match ls with
  | a :: b :: rest =>
      match binary_op op a b ctx st0 with
      | LErr msg => LErr msg
      | LOk o0 st1 =>
          let o_res :=
            if sat then
              match convert_val o0 TLong st1 with
              | LErr msg => LErr msg
              | LOk o1 st2 => clamped_v o1 (-32768) 32767 e ctx st2
              end
            else LOk o0 st1 in
          match o_res with
          | LErr msg => LErr msg
          | LOk o st2 =>
              match v_horizontal rest op sat e ctx st2 with
              | LErr msg => LErr msg
              | LOk os st3 => LOk (o :: os) st3
              end
          end
      end
  | _ => LOk [] st0
  end.

Fixpoint v_averaged (as_ bs : list c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match as_, bs with
  | a :: ra, b :: rb =>
      match binary_op BAdd a b ctx st0 with
      | LErr msg => LErr msg
      | LOk s st1 =>
          match binary_op BAdd s (vk 1) ctx st1 with
          | LErr msg => LErr msg
          | LOk s1 st2 =>
              match binary_op BShr s1 (vk 1) ctx st2 with
              | LErr msg => LErr msg
              | LOk o st3 =>
                  match v_averaged ra rb ctx st3 with
                  | LErr msg => LErr msg
                  | LOk os st4 => LOk (o :: os) st4
                  end
              end
          end
      end
  | _, _ => LOk [] st0
  end.

Fixpoint signed_lanes (as_ bs : list c_val) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match as_, bs with
  | (CVal _ t as a) :: ra, b :: rb =>
      let z := vk 0 in
      match binary_op BLt b z ctx st0 with
      | LErr msg => LErr msg
      | LOk neg st1 =>
          match binary_op BEq b z ctx st1 with
          | LErr msg => LErr msg
          | LOk isz st2 =>
              match binary_op BSub z a ctx st2 with
              | LErr msg => LErr msg
              | LOk na st3 =>
                  match isel neg na a t ctx st3 with
                  | LErr msg => LErr msg
                  | LOk o1 st4 =>
                      match isel isz z o1 t ctx st4 with
                      | LErr msg => LErr msg
                      | LOk o st5 =>
                          match signed_lanes ra rb ctx st5 with
                          | LErr msg => LErr msg
                          | LOk os st6 => LOk (o :: os) st6
                          end
                      end
                  end
              end
          end
      end
  | _, _ => LOk [] st0
  end.

Fixpoint shuffled_bytes (is_ : list c_val) (addr : term) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list c_val) :=
  match is_ with
  | [] => LOk [] st0
  | i :: rest =>
      match binary_op BAnd i (vk 15) ctx st0 with
      | LErr msg => LErr msg
      | LOk j st1 =>
          match convert_val j TLong st1 with
          | LErr msg => LErr msg
          | LOk (CVal jl _) st2 =>
              let '(p, st3) := l_let "p" (TAtom "add") [addr; jl] st2 in
              match load_typed TUChar p ctx st3 with
              | LErr msg => LErr msg
              | LOk x st4 =>
                  match binary_op BAnd i (vk 128) ctx st4 with
                  | LErr msg => LErr msg
                  | LOk top st5 =>
                      match binary_op BNe top (vk 0) ctx st5 with
                      | LErr msg => LErr msg
                      | LOk zero st6 =>
                          match isel zero (vk 0) (CVal x TUChar) TUChar ctx st6 with
                          | LErr msg => LErr msg
                          | LOk o st7 =>
                              match shuffled_bytes rest addr ctx st7 with
                              | LErr msg => LErr msg
                              | LOk os st8 => LOk (o :: os) st8
                              end
                          end
                      end
                  end
              end
          end
      end
  end.

Fixpoint tested_or (as_ bs : list c_val) (is_z : bool) (ctx : c_lower_ctx)
  (or0 : c_val) (st0 : c_func_st) : l_res c_val :=
  match as_, bs with
  | a :: ra, b :: rb =>
      let a1_res := if is_z then LOk a st0 else unary_op UBnot a ctx st0 in
      match a1_res with
      | LErr msg => LErr msg
      | LOk a1 st1 =>
          match binary_op BAnd a1 b ctx st1 with
          | LErr msg => LErr msg
          | LOk x st2 =>
              match binary_op BOr or0 x ctx st2 with
              | LErr msg => LErr msg
              | LOk or1 st3 => tested_or ra rb is_z ctx or1 st3
              end
          end
      end
  | _, _ => LOk or0 st0
  end.

Definition v_tested (as_ bs : list c_val) (is_z : bool) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res c_val :=
  match tested_or as_ bs is_z ctx (CVal (ir_const 0) TULLong) st0 with
  | LErr msg => LErr msg
  | LOk or_v st1 => binary_op BEq or_v (vk 0) ctx st1
  end.

Definition bits_of_v (v : c_val) (from_t to_t : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res c_val :=
  let '(CVal x _) := v in
  match l_local_slot from_t st0 with
  | LErr msg => LErr msg
  | LOk tmp st1 =>
      match store_typed from_t x tmp st1 with
      | LErr msg => LErr msg
      | LOk _ st2 => loaded_val to_t tmp ctx st2
      end
  end.

Definition rounded_even (x : c_val) (f : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res c_val :=
  let '(it, sign, magic, abs_m) :=
    match f with
    | TFloatK FFloat => (TUInt, 2147483648, 1258291200, 2147483647)
    | _ => (TULLong, 9223372036854775808, 4841369599423283200, 9223372036854775807)
    end in
  match bits_of_v x f it ctx st0 with
  | LErr msg => LErr msg
  | LOk xb st1 =>
      match binary_op BAnd xb (CVal (ir_const sign) it) ctx st1 with
      | LErr msg => LErr msg
      | LOk s st2 =>
          match binary_op BOr s (CVal (ir_const magic) it) ctx st2 with
          | LErr msg => LErr msg
          | LOk mb st3 =>
              match bits_of_v mb it f ctx st3 with
              | LErr msg => LErr msg
              | LOk m st4 =>
                  match binary_op BAdd x m ctx st4 with
                  | LErr msg => LErr msg
                  | LOk x1 st5 =>
                      match convert_val x1 f st5 with
                      | LErr msg => LErr msg
                      | LOk x2 st6 =>
                          match binary_op BSub x2 m ctx st6 with
                          | LErr msg => LErr msg
                          | LOk x3 st7 =>
                              match convert_val x3 f st7 with
                              | LErr msg => LErr msg
                              | LOk x4 st8 =>
                                  match bits_of_v x4 f it ctx st8 with
                                  | LErr msg => LErr msg
                                  | LOk rb st9 =>
                                      match binary_op BAnd xb (CVal (ir_const abs_m) it) ctx st9 with
                                      | LErr msg => LErr msg
                                      | LOk ab st10 =>
                                          match binary_op BGe ab (CVal (ir_const magic) it) ctx st10 with
                                          | LErr msg => LErr msg
                                          | LOk big st11 =>
                                              match isel big xb rb it ctx st11 with
                                              | LErr msg => LErr msg
                                              | LOk yb st12 => bits_of_v yb it f ctx st12
                                              end
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end
  end.

Fixpoint list_set_nth {A : Type} (idx : nat) (x : A) (xs : list A) : list A :=
  match idx, xs with
  | O, _ :: rest => x :: rest
  | S k, y :: rest => y :: list_set_nth k x rest
  | _, [] => []
  end.

Fixpoint vector_op_f (fuel : nat) (name : string) (args : list c_expr)
  (vs : list c_val) (ret : c_type) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res c_val :=
  match fuel with
  | O => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
  | S f =>
      match lane_builtin name with
      | Some name128 =>
          let reth := half_type ret in
          let '(vs0, st1) := v_halves vs 0 st0 in
          let '(vs1, st2) := v_halves vs 16 st1 in
          match vector_op_f f name128 args vs0 reth ctx st2 with
          | LErr msg => LErr msg
          | LOk (CVal a0 _) st3 =>
              match vector_op_f f name128 args vs1 reth ctx st3 with
              | LErr msg => LErr msg
              | LOk (CVal a1 _) st4 =>
                  match l_local_slot ret st4 with
                  | LErr msg => LErr msg
                  | LOk c st5 =>
                      match copy_object reth a0 c st5 with
                      | LErr msg => LErr msg
                      | LOk _ st6 =>
                          let '(c1, st7) := l_offset c 16 st6 in
                          match copy_object reth a1 c1 st7 with
                          | LErr msg => LErr msg
                          | LOk _ st8 => LOk (CVal c ret) st8
                          end
                      end
                  end
              end
          end
      | None =>
          if str_mem name ["extract128i256"; "vextractf128_si256"; "vextractf128_ps256"; "vextractf128_pd256"] then
            match args, vs with
            | [_; a], [CVal w _; _] =>
                match v_imm a ctx st0 with
                | LErr msg => LErr msg
                | LOk i st1 =>
                    let off := 16 * Z.land i 1 in
                    let '(h, st2) := l_offset w off st1 in
                    LOk (CVal h ret) st2
                end
            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if str_mem name ["insert128i256"; "vinsertf128_si256"; "vinsertf128_ps256"; "vinsertf128_pd256"] then
            match args, vs with
            | [_; _; a], [CVal w _; CVal h ht; _] =>
                match v_imm a ctx st0 with
                | LErr msg => LErr msg
                | LOk i st1 =>
                    let off := 16 * Z.land i 1 in
                    match l_local_slot ret st1 with
                    | LErr msg => LErr msg
                    | LOk c st2 =>
                        match copy_object ret w c st2 with
                        | LErr msg => LErr msg
                        | LOk _ st3 =>
                            let '(d, st4) := l_offset c off st3 in
                            match copy_object ht h d st4 with
                            | LErr msg => LErr msg
                            | LOk _ st5 => LOk (CVal c ret) st5
                            end
                        end
                    end
                end
            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if str_mem name ["permti256"; "vperm2f128_si256"; "vperm2f128_ps256"; "vperm2f128_pd256"] then
            match args, vs with
            | [_; _; a], [CVal va _; CVal vb _; _] =>
                match v_imm a ctx st0 with
                | LErr msg => LErr msg
                | LOk i st1 =>
                    match l_local_slot ret st1 with
                    | LErr msg => LErr msg
                    | LOk c st2 =>
                        match perm2_half 0 i va vb c st2 with
                        | LErr msg => LErr msg
                        | LOk _ st3 =>
                            match perm2_half 1 i va vb c st3 with
                            | LErr msg => LErr msg
                            | LOk _ st4 => LOk (CVal c ret) st4
                            end
                        end
                    end
                end
            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if (name == "permvarsi256") || (name == "permvarsf256") then
            match vs with
            | [CVal va _; vb] =>
                let q := TVec TUInt 8 32 in
                match v_lanes vb q ctx st0 with
                | LErr msg => LErr msg
                | LOk is_ st1 =>
                    match v_permuted is_ va ctx st1 with
                    | LErr msg => LErr msg
                    | LOk out st2 =>
                        match v_made q out st2 with
                        | LErr msg => LErr msg
                        | LOk (CVal addr _) st3 => LOk (CVal addr ret) st3
                        end
                    end
                end
            | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if str_mem name ["vec_ext_v32qi"; "vec_ext_v16hi"; "vec_ext_v8si"; "vec_ext_v4di"] then
            match args, vs with
            | [_; a], [(CVal _ (TVec _ n _ as vt) as v); _] =>
                match v_imm a ctx st0 with
                | LErr msg => LErr msg
                | LOk i st1 =>
                    let j := Z.modulo i n in
                    match v_lanes v vt ctx st1 with
                    | LErr msg => LErr msg
                    | LOk ls st2 =>
                        let '(CVal x _) := nth_cval j ls in
                        LOk (CVal x ret) st2
                    end
                end
            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if (name == "vzeroupper") || (name == "vzeroall") then
            LOk (CVal (ir_const 0) TVoid)
                (safety_error ("Unhandled intrinsic:   call void @llvm.x86.avx." ++ name ++ "()") st0)
          else if (name == "addsubps") || (name == "addsubpd") then
            match vs with
            | [va; vb] =>
                match v_lanes va ret ctx st0 with
                | LErr msg => LErr msg
                | LOk la st1 =>
                    match v_lanes vb ret ctx st1 with
                    | LErr msg => LErr msg
                    | LOk lb st2 =>
                        match addsub_lanes la lb 0 ctx st2 with
                        | LErr msg => LErr msg
                        | LOk out st3 => v_made ret out st3
                        end
                    end
                end
            | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if str_mem name ["vfmaddps"; "vfmaddpd"; "vfmaddsubps"; "vfmaddsubpd"] then
            let sub_even := (name == "vfmaddsubps") || (name == "vfmaddsubpd") in
            match vs with
            | [va; vb; vc] =>
                match v_lanes va ret ctx st0 with
                | LErr msg => LErr msg
                | LOk la st1 =>
                    match v_lanes vb ret ctx st1 with
                    | LErr msg => LErr msg
                    | LOk lb st2 =>
                        match v_lanes vc ret ctx st2 with
                        | LErr msg => LErr msg
                        | LOk lc st3 =>
                            match fma_lanes la lb lc sub_even 0 ctx st3 with
                            | LErr msg => LErr msg
                            | LOk out st4 => v_made ret out st4
                            end
                        end
                    end
                end
            | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if name == "vpermilps" then
            match args, vs with
            | [_; a], [v; _] =>
                match v_imm a ctx st0 with
                | LErr msg => LErr msg
                | LOk i st1 =>
                    let q := TVec TUInt 4 16 in
                    match v_lanes v q ctx st1 with
                    | LErr msg => LErr msg
                    | LOk ls st2 =>
                        let out :=
                          map (fun j => nth_cval (Z.land (Z.shiftr i (2 * j)) 3) ls) [0; 1; 2; 3] in
                        match v_made q out st2 with
                        | LErr msg => LErr msg
                        | LOk (CVal addr _) st3 => LOk (CVal addr ret) st3
                        end
                    end
                end
            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if (name == "vpermilpd") || (name == "vpermilpd256") then
            match args, vs, ret with
            | [_; a], [v; _], TVec _ n al =>
                match v_imm a ctx st0 with
                | LErr msg => LErr msg
                | LOk i st1 =>
                    let q := TVec TULLong n al in
                    match v_lanes v q ctx st1 with
                    | LErr msg => LErr msg
                    | LOk ls st2 =>
                        let out :=
                          map (fun j =>
                                 let s := Z.land j (-2) + Z.land (Z.shiftr i j) 1 in
                                 nth_cval s ls) (numlist_Z 0 (n - 1)) in
                        match v_made q out st2 with
                        | LErr msg => LErr msg
                        | LOk (CVal addr _) st3 => LOk (CVal addr ret) st3
                        end
                    end
                end
            | _, _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if name == "shufpd256" then
            match args, vs with
            | [_; _; c], [va; vb; _] =>
                match v_imm c ctx st0 with
                | LErr msg => LErr msg
                | LOk i st1 =>
                    let q := TVec TULLong 4 32 in
                    match v_lanes va q ctx st1 with
                    | LErr msg => LErr msg
                    | LOk la st2 =>
                        match v_lanes vb q ctx st2 with
                        | LErr msg => LErr msg
                        | LOk lb st3 =>
                            let out :=
                              map (fun j =>
                                     let s := Z.land j (-2) + Z.land (Z.shiftr i j) 1 in
                                     if Z.eqb (Z.land j 1) 0 then nth_cval s la else nth_cval s lb)
                                  [0; 1; 2; 3] in
                            match v_made q out st3 with
                            | LErr msg => LErr msg
                            | LOk (CVal addr _) st4 => LOk (CVal addr ret) st4
                            end
                        end
                    end
                end
            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else if name == "lddqu" then
            match vs with
            | [CVal p _] =>
                match l_local_slot ret st0 with
                | LErr msg => LErr msg
                | LOk copy st1 =>
                    match vector_access "read" (TVec TChar 16 1) p st1 with
                    | LErr msg => LErr msg
                    | LOk _ st2 =>
                        match copy_object ret p copy st2 with
                        | LErr msg => LErr msg
                        | LOk _ st3 => LOk (CVal copy ret) st3
                        end
                    end
                end
            | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
            end
          else
            let movmsk :=
              if name == "pmovmskb128" then Some (TVec TUChar 16 16, 7)
              else if name == "movmskps" then Some (TVec TUInt 4 16, 31)
              else if name == "movmskpd" then Some (TVec TULLong 2 16, 63)
              else if name == "pmovmskb256" then Some (TVec TUChar 32 32, 7)
              else if name == "movmskps256" then Some (TVec TUInt 8 32, 31)
              else if name == "movmskpd256" then Some (TVec TULLong 4 32, 63)
              else None in
            match movmsk with
            | Some (vt, bit) =>
                match vs with
                | [v] =>
                    match v_lanes v vt ctx st0 with
                    | LErr msg => LErr msg
                    | LOk ls st1 =>
                        match v_sign_bits ls 0 bit ctx (vk 0) st1 with
                        | LErr msg => LErr msg
                        | LOk (CVal m _) st2 => LOk (CVal m TInt) st2
                        end
                    end
                | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                end
            | None =>
                match shift_builtin_info name with
                | Some (kind, cnt) =>
                    match vs with
                    | [v; c] =>
                        if cnt == "imm" then shifted_lanes kind v c ret ctx st0
                        else
                          match v_lanes c v2du ctx st0 with
                          | LErr msg => LErr msg
                          | LOk (c0 :: _) st1 => shifted_lanes kind v c0 ret ctx st1
                          | LOk [] st1 => l_err (ctx_loc ctx) "empty shift count vector" st1
                          end
                    | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                    end
                | None =>
                    if (name == "pslldqi128_byteshift") || (name == "psrldqi128_byteshift") then
                      let is_left := name == "pslldqi128_byteshift" in
                      match args, vs with
                      | [_; a], [v; _] =>
                          match v_imm a ctx st0 with
                          | LErr msg => LErr msg
                          | LOk i0 st1 =>
                              let i := Z.land i0 255 in
                              match v_lanes v v16qu ctx st1 with
                              | LErr msg => LErr msg
                              | LOk ls st2 =>
                                  let out :=
                                    map (fun j =>
                                           let s := if is_left then j - i else j + i in
                                           if (0 <=? s) && (s <? 16) then nth_cval s ls else vk 0)
                                        (numlist_Z 0 15) in
                                  match v_made v16qu out st2 with
                                  | LErr msg => LErr msg
                                  | LOk (CVal addr _) st3 => LOk (CVal addr ret) st3
                                  end
                              end
                          end
                      | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                      end
                    else
                      let pack :=
                        if name == "packsswb128" then Some (-128, 127)
                        else if name == "packuswb128" then Some (0, 255)
                        else if name == "packssdw128" then Some (-32768, 32767)
                        else if name == "packusdw128" then Some (0, 65535)
                        else None in
                      match pack with
                      | Some (lo, hi) =>
                          match vs, ret with
                          | [(CVal _ in_t as a); b], TVec re _ _ =>
                              match v_lanes a in_t ctx st0 with
                              | LErr msg => LErr msg
                              | LOk la st1 =>
                                  match v_lanes b in_t ctx st1 with
                                  | LErr msg => LErr msg
                                  | LOk lb st2 =>
                                      match clamp_all (app la lb) lo hi re ctx st2 with
                                      | LErr msg => LErr msg
                                      | LOk out st3 => v_made ret out st3
                                      end
                                  end
                              end
                          | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                          end
                      | None =>
                          if (name == "pshufd") || (name == "pshuflw") || (name == "pshufhw") then
                            match args, vs with
                            | [_; a], [v; _] =>
                                match v_imm a ctx st0 with
                                | LErr msg => LErr msg
                                | LOk i st1 =>
                                    match v_lanes v ret ctx st1 with
                                    | LErr msg => LErr msg
                                    | LOk ls st2 =>
                                        let out :=
                                          map (fun j => nth_cval (shuffled_idx name i j) ls)
                                              (numlist_Z 0 (Z.of_nat (length ls) - 1)) in
                                        v_made ret out st2
                                    end
                                end
                            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                            end
                          else if name == "palignr128" then
                            match args, vs with
                            | [_; _; a], [va; vb; _] =>
                                match v_imm a ctx st0 with
                                | LErr msg => LErr msg
                                | LOk i0 st1 =>
                                    let i := Z.land i0 255 in
                                    match v_lanes vb v16qu ctx st1 with
                                    | LErr msg => LErr msg
                                    | LOk lb st2 =>
                                        match v_lanes va v16qu ctx st2 with
                                        | LErr msg => LErr msg
                                        | LOk la st3 =>
                                            let t := app lb la in
                                            let out :=
                                              map (fun j =>
                                                     let s := j + i in
                                                     if s <? 32 then nth_cval s t else vk 0)
                                                  (numlist_Z 0 15) in
                                            match v_made v16qu out st3 with
                                            | LErr msg => LErr msg
                                            | LOk (CVal addr _) st4 => LOk (CVal addr ret) st4
                                            end
                                        end
                                    end
                                end
                            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                            end
                          else if name == "pblendvb128" then
                            match vs with
                            | [va; vb; vm] =>
                                match v_lanes va ret ctx st0 with
                                | LErr msg => LErr msg
                                | LOk la st1 =>
                                    match v_lanes vb ret ctx st1 with
                                    | LErr msg => LErr msg
                                    | LOk lb st2 =>
                                        match v_lanes vm ret ctx st2 with
                                        | LErr msg => LErr msg
                                        | LOk lm st3 =>
                                            match v_blendv la lb lm ctx st3 with
                                            | LErr msg => LErr msg
                                            | LOk out st4 => v_made ret out st4
                                            end
                                        end
                                    end
                                end
                            | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                            end
                          else if name == "pblendw128" then
                            match args, vs with
                            | [_; _; a], [va; vb; _] =>
                                match v_imm a ctx st0 with
                                | LErr msg => LErr msg
                                | LOk i st1 =>
                                    match v_lanes va ret ctx st1 with
                                    | LErr msg => LErr msg
                                    | LOk la st2 =>
                                        match v_lanes vb ret ctx st2 with
                                        | LErr msg => LErr msg
                                        | LOk lb st3 =>
                                            let out :=
                                              map (fun j =>
                                                     if Z.eqb (Z.land (Z.shiftr i j) 1) 1 then nth_cval j lb
                                                     else nth_cval j la)
                                                  (numlist_Z 0 (Z.of_nat (length la) - 1)) in
                                            v_made ret out st3
                                        end
                                    end
                                end
                            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                            end
                          else if (name == "pmuludq128") || (name == "pmuldq128") then
                            let '(in_t, wide_t) :=
                              if name == "pmuludq128" then (TVec TUInt 4 16, TULLong)
                              else (TVec TInt 4 16, TLLong) in
                            match vs with
                            | [va; vb] =>
                                match v_lanes va in_t ctx st0 with
                                | LErr msg => LErr msg
                                | LOk [a0; _; a2; _] st1 =>
                                    match v_lanes vb in_t ctx st1 with
                                    | LErr msg => LErr msg
                                    | LOk [b0; _; b2; _] st2 =>
                                        match convert_val a0 wide_t st2 with
                                        | LErr msg => LErr msg
                                        | LOk x0 st3 =>
                                            match convert_val a2 wide_t st3 with
                                            | LErr msg => LErr msg
                                            | LOk x2 st4 =>
                                                match binary_op BMul x0 b0 ctx st4 with
                                                | LErr msg => LErr msg
                                                | LOk p0 st5 =>
                                                    match binary_op BMul x2 b2 ctx st5 with
                                                    | LErr msg => LErr msg
                                                    | LOk p2 st6 => v_made ret [p0; p2] st6
                                                    end
                                                end
                                            end
                                        end
                                    | LOk _ st2 => l_err (ctx_loc ctx) "unexpected lane count" st2
                                    end
                                | LOk _ st1 => l_err (ctx_loc ctx) "unexpected lane count" st1
                                end
                            | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                            end
                          else if name == "pclmulqdq128" then
                            match args, vs with
                            | [_; _; c], [va; vb; _] =>
                                match v_imm c ctx st0 with
                                | LErr msg => LErr msg
                                | LOk i st1 =>
                                    let sa := Z.land i 1 in
                                    let sb := Z.land (Z.shiftr i 4) 1 in
                                    match v_lanes va v2du ctx st1 with
                                    | LErr msg => LErr msg
                                    | LOk la st2 =>
                                        match v_lanes vb v2du ctx st2 with
                                        | LErr msg => LErr msg
                                        | LOk lb st3 =>
                                            let a := nth_cval sa la in
                                            let b := nth_cval sb lb in
                                            let z := CVal (ir_const 0) TULLong in
                                            match clmul_bits_f 65%nat 0 a b ctx z z st3 with
                                            | LErr msg => LErr msg
                                            | LOk (lo, hi) st4 => v_made ret [lo; hi] st4
                                            end
                                        end
                                    end
                                end
                            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                            end
                          else if (name == "shufpd") || (name == "shufps") then
                            let '(q, n, bits) :=
                              if name == "shufpd" then (TVec TULLong 2 16, 2, 1)
                              else (TVec TUInt 4 16, 4, 2) in
                            match args, vs with
                            | [_; _; c], [va; vb; _] =>
                                match v_imm c ctx st0 with
                                | LErr msg => LErr msg
                                | LOk i st1 =>
                                    match v_lanes va q ctx st1 with
                                    | LErr msg => LErr msg
                                    | LOk la st2 =>
                                        match v_lanes vb q ctx st2 with
                                        | LErr msg => LErr msg
                                        | LOk lb st3 =>
                                            let half := Z.div n 2 in
                                            let mask := Z.shiftl 1 bits - 1 in
                                            let out :=
                                              map (fun j =>
                                                     let s := Z.land (Z.shiftr i (bits * j)) mask in
                                                     if j <? half then nth_cval s la else nth_cval s lb)
                                                  (numlist_Z 0 (n - 1)) in
                                            match v_made q out st3 with
                                            | LErr msg => LErr msg
                                            | LOk (CVal addr _) st4 => LOk (CVal addr ret) st4
                                            end
                                        end
                                    end
                                end
                            | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                            end
                          else
                            match pcmpstr_info name with
                            | Some (len, out_k) =>
                                match list_last args with
                                | None => l_err (ctx_loc ctx) "missing pcmpstr immediate" st0
                                | Some ia =>
                                    match v_imm ia ctx st0 with
                                    | LErr msg => LErr msg
                                    | LOk i st1 =>
                                        let vt := pcmp_format i in
                                        let n := match vt with TVec _ nv _ => nv | _ => 16 end in
                                        let unpacked :=
                                          if len == "e" then
                                            match vs with
                                            | [va; la_v; vb; lb_v; _] => Some (va, Some la_v, vb, Some lb_v)
                                            | _ => None
                                            end
                                          else
                                            match vs with
                                            | [va; vb; _] => Some (va, None, vb, None)
                                            | _ => None
                                            end in
                                        match unpacked with
                                        | None => l_err (ctx_loc ctx) "wrong pcmpstr arguments" st1
                                        | Some (va, ola, vb, olb) =>
                                            match v_lanes va vt ctx st1 with
                                            | LErr msg => LErr msg
                                            | LOk la st2 =>
                                                match v_lanes vb vt ctx st2 with
                                                | LErr msg => LErr msg
                                                | LOk lb st3 =>
                                                    match pcmp_valid len la ola ctx st3 with
                                                    | LErr msg => LErr msg
                                                    | LOk va_s st4 =>
                                                        match pcmp_valid len lb olb ctx st4 with
                                                        | LErr msg => LErr msg
                                                        | LOk vb_s st5 =>
                                                            let agg := Z.land (Z.shiftr i 2) 3 in
                                                            let pol := Z.land (Z.shiftr i 4) 3 in
                                                            let msb := Z.land (Z.shiftr i 6) 1 in
                                                            let r2_res :=
                                                              if (out_k == "is") || (out_k == "iz") then LOk [vk 0] st5
                                                              else
                                                                match pcmp_aggregated agg la lb va_s vb_s ctx st5 with
                                                                | LErr msg => LErr msg
                                                                | LOk r1 st6 => pcmp_polarity pol r1 vb_s ctx st6
                                                                end in
                                                            match r2_res with
                                                            | LErr msg => LErr msg
                                                            | LOk r2 st6 =>
                                                                let van := match list_last va_s with Some x => x | None => vk 0 end in
                                                                let vbn := match list_last vb_s with Some x => x | None => vk 0 end in
                                                                let r20 := match r2 with x :: _ => x | [] => vk 0 end in
                                                                let js := numlist_Z 0 (Z.of_nat (length r2) - 1) in
                                                                pcmp_result out_k msb vt n r2 js r20 van vbn ret ctx st6
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end
                            | None =>
                                if name == "pmaddwd128" then
                                  match vs with
                                  | [va; vb] =>
                                      match v_lanes va v8hi ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk la st1 =>
                                          match v_lanes vb v8hi ctx st1 with
                                          | LErr msg => LErr msg
                                          | LOk lb st2 =>
                                              match pair_products la lb TUInt ctx st2 with
                                              | LErr msg => LErr msg
                                              | LOk out st3 => v_made ret out st3
                                              end
                                          end
                                      end
                                  | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                  end
                                else if name == "pmaddubsw128" then
                                  match vs with
                                  | [va; vb] =>
                                      match v_lanes va v16qu ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk la st1 =>
                                          match v_lanes vb v16qi ctx st1 with
                                          | LErr msg => LErr msg
                                          | LOk lb st2 =>
                                              match pair_products la lb TInt ctx st2 with
                                              | LErr msg => LErr msg
                                              | LOk sums st3 =>
                                                  match clamp_all sums (-32768) 32767 TShort ctx st3 with
                                                  | LErr msg => LErr msg
                                                  | LOk out st4 => v_made ret out st4
                                                  end
                                              end
                                          end
                                      end
                                  | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                  end
                                else if name == "psadbw128" then
                                  match vs with
                                  | [va; vb] =>
                                      match v_lanes va v16qu ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk la st1 =>
                                          match v_lanes vb v16qu ctx st1 with
                                          | LErr msg => LErr msg
                                          | LOk lb st2 =>
                                              let '(la1, la2) := list_split_at 8%nat la in
                                              let '(lb1, lb2) := list_split_at 8%nat lb in
                                              match abs_diff_sum la1 lb1 ctx (vk 0) st2 with
                                              | LErr msg => LErr msg
                                              | LOk s1 st3 =>
                                                  match abs_diff_sum la2 lb2 ctx (vk 0) st3 with
                                                  | LErr msg => LErr msg
                                                  | LOk s2 st4 => v_made ret [s1; s2] st4
                                                  end
                                              end
                                          end
                                      end
                                  | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                  end
                                else if (name == "pmulhuw128") || (name == "pmulhw128") then
                                  let in_t := if name == "pmulhuw128" then TVec TUShort 8 16 else TVec TShort 8 16 in
                                  match vs with
                                  | [va; vb] =>
                                      match v_lanes va in_t ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk la st1 =>
                                          match v_lanes vb in_t ctx st1 with
                                          | LErr msg => LErr msg
                                          | LOk lb st2 =>
                                              match v_mulhi la lb 16 ctx st2 with
                                              | LErr msg => LErr msg
                                              | LOk out st3 => v_made ret out st3
                                              end
                                          end
                                      end
                                  | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                  end
                                else if (name == "pavgb128") || (name == "pavgw128") then
                                  let in_t := if name == "pavgb128" then TVec TUChar 16 16 else TVec TUShort 8 16 in
                                  match vs with
                                  | [va; vb] =>
                                      match v_lanes va in_t ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk la st1 =>
                                          match v_lanes vb in_t ctx st1 with
                                          | LErr msg => LErr msg
                                          | LOk lb st2 =>
                                              match v_averaged la lb ctx st2 with
                                              | LErr msg => LErr msg
                                              | LOk out st3 => v_made ret out st3
                                              end
                                          end
                                      end
                                  | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                  end
                                else if (name == "psignb128") || (name == "psignw128") || (name == "psignd128") then
                                  match vs with
                                  | [va; vb] =>
                                      match v_lanes va ret ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk la st1 =>
                                          match v_lanes vb ret ctx st1 with
                                          | LErr msg => LErr msg
                                          | LOk lb st2 =>
                                              match signed_lanes la lb ctx st2 with
                                              | LErr msg => LErr msg
                                              | LOk out st3 => v_made ret out st3
                                              end
                                          end
                                      end
                                  | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                  end
                                else
                                  let horiz :=
                                    if (name == "phaddw128") || (name == "phaddd128") then Some (BAdd, false)
                                    else if (name == "phsubw128") || (name == "phsubd128") then Some (BSub, false)
                                    else if name == "phaddsw128" then Some (BAdd, true)
                                    else if name == "phsubsw128" then Some (BSub, true)
                                    else None in
                                  match horiz with
                                  | Some (op, sat) =>
                                      match vs, ret with
                                      | [va; vb], TVec e _ _ =>
                                          match v_lanes va ret ctx st0 with
                                          | LErr msg => LErr msg
                                          | LOk la st1 =>
                                              match v_lanes vb ret ctx st1 with
                                              | LErr msg => LErr msg
                                              | LOk lb st2 =>
                                                  match v_horizontal (app la lb) op sat e ctx st2 with
                                                  | LErr msg => LErr msg
                                                  | LOk out st3 => v_made ret out st3
                                                  end
                                              end
                                          end
                                      | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                      end
                                  | None =>
                                      if name == "pshufb128" then
                                        match vs with
                                        | [CVal aaddr _; vb] =>
                                            match v_lanes vb v16qu ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk lb st1 =>
                                                match shuffled_bytes lb aaddr ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk out st2 =>
                                                    match v_made v16qu out st2 with
                                                    | LErr msg => LErr msg
                                                    | LOk (CVal addr _) st3 => LOk (CVal addr ret) st3
                                                    end
                                                end
                                            end
                                        | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                        end
                                      else if (name == "ptestz128") || (name == "ptestc128") || (name == "ptestnzc128") then
                                        match vs with
                                        | [va; vb] =>
                                            match v_lanes va v2du ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk la st1 =>
                                                match v_lanes vb v2du ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk lb st2 =>
                                                    match v_tested la lb true ctx st2 with
                                                    | LErr msg => LErr msg
                                                    | LOk z st3 =>
                                                        match v_tested la lb false ctx st3 with
                                                        | LErr msg => LErr msg
                                                        | LOk c st4 =>
                                                            if name == "ptestz128" then
                                                              let '(CVal t _) := z in LOk (CVal t TInt) st4
                                                            else if name == "ptestc128" then
                                                              let '(CVal t _) := c in LOk (CVal t TInt) st4
                                                            else
                                                              match binary_op BEq z (vk 0) ctx st4 with
                                                              | LErr msg => LErr msg
                                                              | LOk nz st5 =>
                                                                  match binary_op BEq c (vk 0) ctx st5 with
                                                                  | LErr msg => LErr msg
                                                                  | LOk nc st6 =>
                                                                      match binary_op BAnd nz nc ctx st6 with
                                                                      | LErr msg => LErr msg
                                                                      | LOk (CVal t _) st7 => LOk (CVal t TInt) st7
                                                                      end
                                                                  end
                                                              end
                                                        end
                                                    end
                                                end
                                            end
                                        | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                        end
                                      else if str_starts_with "vec_ext_" name then
                                        match args, vs with
                                        | [_; a], [(CVal _ (TVec _ n _ as vt) as v); _] =>
                                            match v_imm a ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk i0 st1 =>
                                                let i := Z.modulo i0 n in
                                                match v_lanes v vt ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk ls st2 => convert_val (nth_cval i ls) ret st2
                                                end
                                            end
                                        | _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                        end
                                      else if str_starts_with "vec_set_" name then
                                        match args, vs, ret with
                                        | [_; _; a], [v; x; _], TVec _ n _ =>
                                            match v_imm a ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk i0 st1 =>
                                                let i := Z.modulo i0 n in
                                                match v_lanes v ret ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk ls st2 =>
                                                    let out := list_set_nth (Z.to_nat i) x ls in
                                                    v_made ret out st2
                                                end
                                            end
                                        | _, _, _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                        end
                                      else if name == "undef128" then
                                        match ret with
                                        | TVec _ n _ => v_made ret (z_repeat n (vk 0)) st0
                                        | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                        end
                                      else if str_mem name ["cvtss2si"; "cvtss2si64"; "cvtsd2si"; "cvtsd2si64"] then
                                        let flt :=
                                          if (name == "cvtss2si") || (name == "cvtss2si64") then TFloat else TDouble in
                                        match vs with
                                        | [(CVal _ vt as v)] =>
                                            match v_lanes v vt ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk (x :: _) st1 =>
                                                match rounded_even x flt ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk y st2 => convert_val y ret st2
                                                end
                                            | LOk [] st1 => l_err (ctx_loc ctx) "empty vector" st1
                                            end
                                        | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                        end
                                      else if name == "cvtpd2ps" then
                                        match vs with
                                        | [(CVal _ vt as v)] =>
                                            match v_lanes v vt ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk [a; b] st1 =>
                                                match convert_val a TFloat st1 with
                                                | LErr msg => LErr msg
                                                | LOk fa st2 =>
                                                    match convert_val b TFloat st2 with
                                                    | LErr msg => LErr msg
                                                    | LOk fb st3 => v_made ret [fa; fb; vk 0; vk 0] st3
                                                    end
                                                end
                                            | LOk _ st1 => l_err (ctx_loc ctx) "unexpected lane count" st1
                                            end
                                        | _ => l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                        end
                                      else l_err (ctx_loc ctx) ("__builtin_ia32_" ++ name ++ " is not supported") st0
                                  end
                            end
                      end
                end
            end
      end
  end.

Fixpoint vector_args (cb : builtin_eval_cb) (args : list c_expr) (ps : list c_type)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  match args, ps with
  | [], [] => LOk [] st0
  | a :: ra, p :: rp =>
      match be_rval cb a ctx st0 with
      | LErr msg => LErr msg
      | LOk v0 st1 =>
          match assign_convert a v0 p (ctx_loc ctx) st1 with
          | LErr msg => LErr msg
          | LOk v st2 =>
              match vector_args cb ra rp ctx st2 with
              | LErr msg => LErr msg
              | LOk vs st3 => LOk (v :: vs) st3
              end
          end
      end
  | _, _ => l_err (ctx_loc ctx) "vector argument arity mismatch" st0
  end.

Definition operand_type_b (e : c_expr) (env : c_type_env) : option c_type :=
  match elaborate e env with
  | TOk (Some x) => Some (unqualified (tree_type (value_node x)))
  | _ => None
  end.

Definition vector_builtin_type_b (name : string) (args : list c_expr)
  (env : c_type_env) : option c_type :=
  if name == "__builtin_shufflevector" then
    match args with
    | a :: b :: is_ =>
        match operand_type_b a env, operand_type_b b env with
        | Some (TVec e1 n1 _), Some (TVec e2 n2 _) =>
            if c_type_eqb e1 e2 && Z.eqb n1 n2 then
              match type_size_align e1 env with
              | TOk (es, _) =>
                  let k := Z.of_nat (length is_) in
                  Some (TVec e1 k (es * k))
              | TErr _ => None
              end
            else None
        | _, _ => None
        end
    | _ => None
    end
  else
    match args with
    | a :: bs =>
        match operand_type_b a env with
        | Some (TVec e n _ as t) =>
            let ok :=
              forallb (fun b =>
                         match operand_type_b b env with
                         | Some (TVec e2 n2 _) => c_type_eqb e e2 && Z.eqb n n2
                         | _ => false
                         end) bs in
            if ok then Some t else None
        | _ => None
        end
    | [] => None
    end.

Fixpoint shuffle_picks (is_ : list c_expr) (ls : list c_val) (nl : Z)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  match is_ with
  | [] => LOk [] st0
  | i :: rest =>
      match v_imm i ctx st0 with
      | LErr msg => LErr msg
      | LOk k st1 =>
          let pick_res :=
            if Z.eqb k (-1) then LOk (vk 0) st1
            else if (0 <=? k) && (k <? nl) then LOk (nth_cval k ls) st1
            else l_err (ctx_loc ctx) ("shuffle index " ++ decimal k ++ " out of range") st1 in
          match pick_res with
          | LErr msg => LErr msg
          | LOk l st2 =>
              match shuffle_picks rest ls nl ctx st2 with
              | LErr msg => LErr msg
              | LOk out st3 => LOk (l :: out) st3
              end
          end
      end
  end.

Fixpoint elementwise_args (cb : builtin_eval_cb) (args : list c_expr) (t : c_type)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res (list c_val) :=
  match args with
  | [] => LOk [] st0
  | a :: rest =>
      match be_rval cb a ctx st0 with
      | LErr msg => LErr msg
      | LOk v0 st1 =>
          match convert_val v0 t st1 with
          | LErr msg => LErr msg
          | LOk v st2 =>
              match elementwise_args cb rest t ctx st2 with
              | LErr msg => LErr msg
              | LOk vs st3 => LOk (v :: vs) st3
              end
          end
      end
  end.

Fixpoint lanes_of_list (vs : list c_val) (t : c_type) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res (list (list c_val)) :=
  match vs with
  | [] => LOk [] st0
  | v :: rest =>
      match v_lanes v t ctx st0 with
      | LErr msg => LErr msg
      | LOk ls st1 =>
          match lanes_of_list rest t ctx st1 with
          | LErr msg => LErr msg
          | LOk lss st2 => LOk (ls :: lss) st2
          end
      end
  end.

Fixpoint pairs_rows (as_ bs : list c_val) : list (list c_val) :=
  match as_, bs with
  | a :: ra, b :: rb => [a; b] :: pairs_rows ra rb
  | _, _ => []
  end.

Definition transpose_lanes (lss : list (list c_val)) : list (list c_val) :=
  match lss with
  | [ls] => map (fun l => [l]) ls
  | [as_; bs] => pairs_rows as_ bs
  | _ => []
  end.

Definition elementwise_one (op : string) (row : list c_val) (e : c_type)
  (sg : c_sign) (bytes : Z) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  if op == "abs" then
    match row with
    | [a] =>
        let z := vk 0 in
        match binary_op BLt a z ctx st0 with
        | LErr msg => LErr msg
        | LOk neg st1 =>
            match binary_op BSub z a ctx st1 with
            | LErr msg => LErr msg
            | LOk na st2 => isel neg na a e ctx st2
            end
        end
    | _ => l_err (ctx_loc ctx) "wrong elementwise arity" st0
    end
  else if (op == "min") || (op == "max") then
    let cmp := if op == "min" then BLt else BGt in
    match row with
    | [a; b] =>
        match binary_op cmp a b ctx st0 with
        | LErr msg => LErr msg
        | LOk c st1 => isel c a b e ctx st1
        end
    | _ => l_err (ctx_loc ctx) "wrong elementwise arity" st0
    end
  else
    let bop := if op == "add_sat" then BAdd else BSub in
    let bits := 8 * bytes in
    let '(lo, hi) :=
      match sg with
      | CSigned => (-(Z.shiftl 1 (bits - 1)), Z.shiftl 1 (bits - 1) - 1)
      | CUnsigned => (0, Z.shiftl 1 bits - 1)
      end in
    match row with
    | [a; b] =>
        match convert_val a TInt st0 with
        | LErr msg => LErr msg
        | LOk a1 st1 =>
            match convert_val b TInt st1 with
            | LErr msg => LErr msg
            | LOk b1 st2 =>
                match binary_op bop a1 b1 ctx st2 with
                | LErr msg => LErr msg
                | LOk s st3 =>
                    match convert_val s TLong st3 with
                    | LErr msg => LErr msg
                    | LOk s1 st4 => clamped_v s1 lo hi e ctx st4
                    end
                end
            end
        end
    | _ => l_err (ctx_loc ctx) "wrong elementwise arity" st0
    end.

Fixpoint elementwise_rows (rows : list (list c_val)) (op : string) (e : c_type)
  (sg : c_sign) (bytes : Z) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res (list c_val) :=
  match rows with
  | [] => LOk [] st0
  | row :: rest =>
      match elementwise_one op row e sg bytes ctx st0 with
      | LErr msg => LErr msg
      | LOk o st1 =>
          match elementwise_rows rest op e sg bytes ctx st1 with
          | LErr msg => LErr msg
          | LOk os st2 => LOk (o :: os) st2
          end
      end
  end.

Definition generic_vector_convert (cb : builtin_eval_cb) (a : c_expr)
  (tn : c_type_name) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  match type_name_type tn (fs_env st0) with
  | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
  | TOk (t0, _) =>
      let t := unqualified t0 in
      match be_rval cb a ctx st0 with
      | LErr msg => LErr msg
      | LOk (CVal _ vt as va) st1 =>
          match v_lanes va vt ctx st1 with
          | LErr msg => LErr msg
          | LOk ls st2 => v_made t ls st2
          end
      end
  end.

Definition generic_vector_op (cb : builtin_eval_cb) (name : string)
  (args : list c_expr) (t : c_type) (ctx : c_lower_ctx) (st0 : c_func_st)
  : l_res c_val :=
  if name == "__builtin_nondeterministic_value" then
    match t with
    | TVec _ n _ => v_made t (z_repeat n (vk 0)) st0
    | _ => l_err (ctx_loc ctx) ("wrong arguments to " ++ name) st0
    end
  else if name == "__builtin_shufflevector" then
    match args with
    | a :: b :: is_ =>
        match be_rval cb a ctx st0 with
        | LErr msg => LErr msg
        | LOk (CVal _ vt as va) st1 =>
            match be_rval cb b ctx st1 with
            | LErr msg => LErr msg
            | LOk vb st2 =>
                match v_lanes va vt ctx st2 with
                | LErr msg => LErr msg
                | LOk la st3 =>
                    match v_lanes vb vt ctx st3 with
                    | LErr msg => LErr msg
                    | LOk lb st4 =>
                        let ls := app la lb in
                        let nl := Z.of_nat (length ls) in
                        match shuffle_picks is_ ls nl ctx st4 with
                        | LErr msg => LErr msg
                        | LOk out st5 => v_made t out st5
                        end
                    end
                end
            end
        end
    | _ => l_err (ctx_loc ctx) ("wrong arguments to " ++ name) st0
    end
  else
    match strip_prefix "__builtin_elementwise_" name, t with
    | Some op, TVec e _ _ =>
        match elementwise_args cb args t ctx st0 with
        | LErr msg => LErr msg
        | LOk vs st1 =>
            match int_info e with
            | Some (bytes, sg) =>
                let sat_ok :=
                  if (op == "add_sat") || (op == "sub_sat") then bytes <=? 2 else true in
                if sat_ok then
                  match lanes_of_list vs t ctx st1 with
                  | LErr msg => LErr msg
                  | LOk lss st2 =>
                      let rows := transpose_lanes lss in
                      match elementwise_rows rows op e sg bytes ctx st2 with
                      | LErr msg => LErr msg
                      | LOk out st3 => v_made t out st3
                      end
                  end
                else l_err (ctx_loc ctx) (name ++ " of a vector of " ++ c_type_diag_str e ++ " is not supported") st1
            | None => l_err (ctx_loc ctx) (name ++ " of a vector of " ++ c_type_diag_str e ++ " is not supported") st1
            end
        end
    | _, _ => l_err (ctx_loc ctx) ("wrong arguments to " ++ name) st0
    end.

(** ## Top-level builtin dispatch

    [lower_builtin] matches every builtin clause of [c_lower:builtin//4] in the
    exact precedence order of the Prolog compiler. *)

Fixpoint rvals_discarded (cb : builtin_eval_cb) (args : list c_expr)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res unit :=
  match args with
  | [] => LOk tt st0
  | a :: rest =>
      match be_rval cb a ctx st0 with
      | LErr msg => LErr msg
      | LOk _ st1 => rvals_discarded cb rest ctx st1
      end
  end.

Definition lower_signbit (cb : builtin_eval_cb) (name : string) (a : c_expr)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  let loc := ctx_loc ctx in
  match be_rval cb a ctx st0 with
  | LErr msg => LErr msg
  | LOk v0 st1 =>
      let is_ld :=
        (name == "__builtin_signbitl") ||
        match v0 with CVal _ (TFloatK FLDouble) => true | _ => false end in
      if is_ld then
        match assign_convert a v0 TLDouble loc st1 with
        | LErr msg => LErr msg
        | LOk (CVal x _) st2 =>
            match l_local_slot TLDouble st2 with
            | LErr msg => LErr msg
            | LOk slot st3 =>
                match store_typed TLDouble x slot st3 with
                | LErr msg => LErr msg
                | LOk _ st4 =>
                    let '(top, st5) := l_let "p" (TAtom "add") [slot; ir_const 8] st4 in
                    match load_typed TUShort top ctx st5 with
                    | LErr msg => LErr msg
                    | LOk exp st6 =>
                        let '(n, st7) := l_let "w" (TAtom "shr") [exp; ir_const 15] st6 in
                        LOk (CVal n TInt) st7
                    end
                end
            end
        end
      else
        match float_bits_of_val a v0 ctx st1 with
        | LErr msg => LErr msg
        | LOk (k, bits, abs_v, inf_n, min_n) st2 =>
            let '(n, st3) := classified_f "__builtin_signbit" k bits abs_v inf_n min_n st2 in
            LOk (CVal n TInt) st3
        end
  end.

Definition lower_builtin (cb : builtin_eval_cb) (name : string)
  (args : list c_expr) (ctx : c_lower_ctx) (st0 : c_func_st) : l_res c_val :=
  let loc := ctx_loc ctx in
  if name == "__builtin_va_start" then
    match args with
    | [a; _] =>
        match ls_va_args (fs_lscope st0) with
        | None => l_err loc "va_start outside a variadic function" st0
        | Some cursor =>
            match be_rval cb a ctx st0 with
            | LErr msg => LErr msg
            | LOk (CVal p _) st1 =>
                LOk (CVal (ir_const 0) TVoid) (l_emit (ir_store "p" cursor p) st1)
            end
        end
    | _ => l_err loc ("wrong arguments to " ++ name) st0
    end
  else if name == "__builtin_va_copy" then
    match args with
    | [a; b] =>
        match be_rval cb a ctx st0 with
        | LErr msg => LErr msg
        | LOk (CVal p _) st1 =>
            match be_rval cb b ctx st1 with
            | LErr msg => LErr msg
            | LOk (CVal q _) st2 =>
                let '(v, st3) := l_let "p" (TApp "load" [TAtom "p"]) [q] st2 in
                LOk (CVal (ir_const 0) TVoid) (l_emit (ir_store "p" v p) st3)
            end
        end
    | _ => l_err loc ("wrong arguments to " ++ name) st0
    end
  else if name == "__builtin_va_end" then
    match args with
    | [a] =>
        match be_rval cb a ctx st0 with
        | LErr msg => LErr msg
        | LOk _ st1 => LOk (CVal (ir_const 0) TVoid) st1
        end
    | _ => l_err loc ("wrong arguments to " ++ name) st0
    end
  else
    let try_float_b :=
      match args with
      | [] => float_builtin name
      | _ => None
      end in
    match try_float_b with
    | Some (ty, v) => LOk (CVal (ir_const v) ty) st0
    | None =>
        if name == "__builtin_constant_p" then
          match args with
          | [e] => LOk (CVal (ir_const (builtin_constant_p_b e (fs_env st0))) TInt) st0
          | _ => l_err loc ("wrong arguments to " ++ name) st0
          end
        else
          match object_size_b name args (fs_env st0) with
          | Some v => LOk (CVal (ir_const v) TULong) st0
          | None =>
              if (name == "__builtin_unreachable") || (name == "__builtin_trap") then
                match args with
                | [] => LOk (CVal (ir_const 0) TVoid) (l_term ir_unreachable st0)
                | _ => l_err loc ("wrong arguments to " ++ name) st0
                end
              else if name == "__builtin_frame_address" then
                match args with
                | [a] =>
                    match const_value a (fs_env st0) with
                    | TErr _ => l_err loc "__builtin_frame_address needs a constant level" st0
                    | TOk (lvl, _) =>
                        if Z.eqb lvl 0 then
                          l_err loc "__builtin_frame_address(0) is not supported: nanofil cannot express the frame address" st0
                        else
                          let st1 := safety_error "cannot use __builtin_frame_address with nonzero argument." st0 in
                          convert_val (CVal (ir_const 0) TInt) (TPtr TVoid) st1
                    end
                | _ => l_err loc ("wrong arguments to " ++ name) st0
                end
              else if name == "__builtin_alloca" then
                match args with
                | [sz] =>
                    match be_rval cb sz ctx st0 with
                    | LErr msg => LErr msg
                    | LOk v0 st1 =>
                        match assign_convert sz v0 TULong loc st1 with
                        | LErr msg => LErr msg
                        | LOk (CVal n _) st2 =>
                            let '(addr, st3) := l_let "p" (TApp "alloc" [Term.TInt 16]) [n] st2 in
                            LOk (CVal addr (TPtr TVoid)) st3
                        end
                    end
                | _ => l_err loc ("wrong arguments to " ++ name) st0
                end
              else
                match sign_builtin name with
                | Some (op, t) =>
                    let expected := if op == "abs" then 1%nat else 2%nat in
                    if Nat.eqb (length args) expected then
                      match sign_args cb args t ctx st0 with
                      | LErr msg => LErr msg
                      | LOk xs st1 =>
                          match sign_result t op xs ctx st1 with
                          | LErr msg => LErr msg
                          | LOk r st2 => LOk (CVal r t) st2
                          end
                      end
                    else l_err loc ("wrong number of arguments to " ++ name) st0
                | None =>
                    match root_builtin name with
                    | Some (f, t) =>
                        match args with
                        | [a] =>
                            match be_rval cb a ctx st0 with
                            | LErr msg => LErr msg
                            | LOk v0 st1 =>
                                match assign_convert a v0 t loc st1 with
                                | LErr msg => LErr msg
                                | LOk (CVal x _) st2 =>
                                    match type_class t with
                                    | None => l_err loc "unsupported sqrt type" st2
                                    | Some k =>
                                        if negb (lo_math_errno (fs_opts st2)) then
                                          let '(d, st3) := l_let k (TAtom "sqrt") [x] st2 in
                                          LOk (CVal d t) st3
                                        else if c_type_eqb t TLDouble then
                                          l_err loc (name ++ " under -fmath-errno is not supported") st2
                                        else
                                          let '(d, st3) := l_fresh st2 in
                                          let st4 := l_emit (ir_call (ir_result d k) (ir_global f) [ir_arg k x]) st3 in
                                          LOk (CVal d t) st4
                                    end
                                end
                            end
                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                        end
                    | None =>
                        match trunc_builtin name with
                        | Some t =>
                            match args with
                            | [a] =>
                                match be_rval cb a ctx st0 with
                                | LErr msg => LErr msg
                                | LOk v0 st1 =>
                                    match assign_convert a v0 t loc st1 with
                                    | LErr msg => LErr msg
                                    | LOk (CVal x _) st2 =>
                                        match trunc_format_info t with
                                        | None => l_err loc "unsupported trunc type" st2
                                        | Some (k, ik, to_int, from_int, big) =>
                                            match sign_result t "abs" [x] ctx st2 with
                                            | LErr msg => LErr msg
                                            | LOk ax st3 =>
                                                let '(small, st4) := l_let "w" (TApp "cmp" [TAtom "lt"; TAtom k]) [ax; ir_const big] st3 in
                                                let '(la, st5) := l_label st4 in
                                                let '(lb, st6) := l_label st5 in
                                                let '(ljoin, st7) := l_label st6 in
                                                let st8 := l_term (ir_branch small la lb) st7 in
                                                let st9 := l_start la st8 in
                                                let '(i, st10) := l_let ik (TAtom to_int) [x] st9 in
                                                let '(f0, st11) := l_let k (TAtom from_int) [i] st10 in
                                                match sign_result t "copysign" [f0; x] ctx st11 with
                                                | LErr msg => LErr msg
                                                | LOk ra st12 =>
                                                    let '(la1, st13) := l_here st12 in
                                                    let st14 := l_term (ir_goto ljoin) st13 in
                                                    let st15 := l_start lb st14 in
                                                    let '(rb, st16) := l_let k (TAtom "add") [x; ir_const 0] st15 in
                                                    let '(lb1, st17) := l_here st16 in
                                                    let st18 := l_term (ir_goto ljoin) st17 in
                                                    join_arms t ljoin la1 ra lb1 rb st18
                                                end
                                            end
                                        end
                                    end
                                end
                            | _ => l_err loc ("wrong arguments to " ++ name) st0
                            end
                        | None =>
                            match libm_builtin name with
                            | Some f =>
                                match args with
                                | [a] =>
                                    match be_rval cb a ctx st0 with
                                    | LErr msg => LErr msg
                                    | LOk v0 st1 =>
                                        match assign_convert a v0 TDouble loc st1 with
                                        | LErr msg => LErr msg
                                        | LOk (CVal x _) st2 =>
                                            let '(d, st3) := l_fresh st2 in
                                            let st4 := l_emit (ir_call (ir_result d "d") (ir_global f) [ir_arg "d" x]) st3 in
                                            LOk (CVal d TDouble) st4
                                        end
                                    end
                                | _ => l_err loc ("wrong arguments to " ++ name) st0
                                end
                            | None =>
                                if name == "__builtin_isnan" then
                                  match args with
                                  | [a] =>
                                      match be_rval cb a ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk v0 st1 =>
                                          match v0 with
                                          | CVal x (TFloatK FFloat) =>
                                              let '(n, st2) := l_let "w" (TApp "cmp" [TAtom "uo"; TAtom "s"]) [x; x] st1 in
                                              LOk (CVal n TInt) st2
                                          | _ =>
                                              match assign_convert a v0 TDouble loc st1 with
                                              | LErr msg => LErr msg
                                              | LOk (CVal x _) st2 =>
                                                  let '(n, st3) := l_let "w" (TApp "cmp" [TAtom "uo"; TAtom "d"]) [x; x] st2 in
                                                  LOk (CVal n TInt) st3
                                              end
                                          end
                                      end
                                  | _ => l_err loc ("wrong arguments to " ++ name) st0
                                  end
                                else if name == "__builtin_fpclassify" then
                                  match args with
                                  | [nan_e; inf_e; norm_e; sub_e; zero_e; a] =>
                                      match be_rval cb a ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk v0 st1 =>
                                          match v0 with
                                          | CVal x (TFloatK FLDouble) =>
                                              match ld_classes x ctx st1 with
                                              | LErr msg => LErr msg
                                              | LOk c st2 =>
                                                  match class_sum cb
                                                          [(ld_nan c, nan_e); (ld_inf c, inf_e);
                                                           (ld_normal c, norm_e); (ld_sub c, sub_e);
                                                           (ld_zero c, zero_e)]
                                                          ctx (ir_const 0) st2 with
                                                  | LErr msg => LErr msg
                                                  | LOk n st3 => LOk (CVal n TInt) st3
                                                  end
                                              end
                                          | _ =>
                                              match float_bits_of_val a v0 ctx st1 with
                                              | LErr msg => LErr msg
                                              | LOk (k, _, abs_v, inf_n, min_n) st2 =>
                                                  let '(isnan, st3) := l_let "w" (TApp "cmp" [TAtom "ugt"; TAtom k]) [abs_v; ir_const inf_n] st2 in
                                                  let '(isinf, st4) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom k]) [abs_v; ir_const inf_n] st3 in
                                                  let '(isnorm, st5) := normal_flag k abs_v inf_n min_n st4 in
                                                  let '(iszero, st6) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom k]) [abs_v; ir_const 0] st5 in
                                                  let '(small, st7) := l_let "w" (TApp "cmp" [TAtom "ult"; TAtom k]) [abs_v; ir_const min_n] st6 in
                                                  let '(issub, st8) := l_let "w" (TAtom "sub") [small; iszero] st7 in
                                                  match class_sum cb
                                                          [(isnan, nan_e); (isinf, inf_e);
                                                           (isnorm, norm_e); (issub, sub_e);
                                                           (iszero, zero_e)]
                                                          ctx (ir_const 0) st8 with
                                                  | LErr msg => LErr msg
                                                  | LOk n st9 => LOk (CVal n TInt) st9
                                                  end
                                              end
                                          end
                                      end
                                  | _ => l_err loc ("wrong arguments to " ++ name) st0
                                  end
                                else if name == "__builtin_signbitf" then
                                  match args with
                                  | [a] =>
                                      lower_signbit cb "__builtin_signbit"
                                        (ECast (TypeName [SpTspec "float"] DTBase) a) ctx st0
                                  | _ => l_err loc ("wrong arguments to " ++ name) st0
                                  end
                                else if (name == "__builtin_signbit") || (name == "__builtin_signbitl") then
                                  match args with
                                  | [a] => lower_signbit cb name a ctx st0
                                  | _ => l_err loc ("wrong arguments to " ++ name) st0
                                  end
                                else if classify_builtin name then
                                  match args with
                                  | [a] =>
                                      match be_rval cb a ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk v0 st1 =>
                                          match v0 with
                                          | CVal x (TFloatK FLDouble) =>
                                              match ld_classes x ctx st1 with
                                              | LErr msg => LErr msg
                                              | LOk c st2 =>
                                                  let '(n, st3) := ld_classified name c st2 in
                                                  LOk (CVal n TInt) st3
                                              end
                                          | _ =>
                                              match float_bits_of_val a v0 ctx st1 with
                                              | LErr msg => LErr msg
                                              | LOk (k, bits, abs_v, inf_n, min_n) st2 =>
                                                  let '(n, st3) := classified_f name k bits abs_v inf_n min_n st2 in
                                                  LOk (CVal n TInt) st3
                                              end
                                          end
                                      end
                                  | _ => l_err loc ("wrong arguments to " ++ name) st0
                                  end
                                else if name == "__builtin_flt_rounds" then
                                  match args with
                                  | [] =>
                                      let '(r, st1) := l_fresh st0 in
                                      let st2 := l_emit (ir_call (ir_result r "w") (ir_global "fegetround") []) st1 in
                                      let '(s, st3) := l_let "w" (TAtom "shr") [r; ir_const 9] st2 in
                                      let '(m, st4) := l_let "w" (TAtom "shr") [ir_const 45; s] st3 in
                                      let '(n, st5) := l_let "w" (TAtom "and") [m; ir_const 3] st4 in
                                      LOk (CVal n TInt) st5
                                  | _ => l_err loc ("wrong arguments to " ++ name) st0
                                  end
                                else if (name == "__atomic_load_n") || (name == "__c11_atomic_load") then
                                  match args with
                                  | [p; _] =>
                                      match be_rval cb p ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk (CVal addr (TPtr t0)) st1 =>
                                          let t := unqualified t0 in
                                          let '(d, st2) := l_let "p" (TApp "atomic_load" [TAtom "p"]) [addr] st1 in
                                          LOk (CVal d t) st2
                                      | LOk _ st1 => l_err loc ("wrong arguments to " ++ name) st1
                                      end
                                  | _ => l_err loc ("wrong arguments to " ++ name) st0
                                  end
                                else if (name == "__atomic_store_n") || (name == "__c11_atomic_store") || (name == "__c11_atomic_init") then
                                  let ok_args :=
                                    match name == "__c11_atomic_init", args with
                                    | true, [p; v] => Some (p, v, None)
                                    | false, [p; v; oe] => Some (p, v, Some oe)
                                    | _, _ => None
                                    end in
                                  match ok_args with
                                  | None => l_err loc ("wrong arguments to " ++ name) st0
                                  | Some (p, v, ooe) =>
                                      match be_rval cb p ctx st0 with
                                      | LErr msg => LErr msg
                                      | LOk (CVal addr (TPtr t0)) st1 =>
                                          match be_rval cb v ctx st1 with
                                          | LErr msg => LErr msg
                                          | LOk v0 st2 =>
                                              let t := unqualified t0 in
                                              match assign_convert v v0 t loc st2 with
                                              | LErr msg => LErr msg
                                              | LOk (CVal x _) st3 =>
                                                  match ooe with
                                                  | Some oe =>
                                                      match const_value oe (fs_env st3) with
                                                      | TOk (ord, _) =>
                                                          match atomic_stored t x addr ord st3 with
                                                          | LErr msg => LErr msg
                                                          | LOk _ st4 => LOk (CVal (ir_const 0) TVoid) st4
                                                          end
                                                      | TErr err => LErr (l_tr_msg loc err)
                                                      end
                                                  | None =>
                                                      match store_typed t x addr st3 with
                                                      | LErr msg => LErr msg
                                                      | LOk _ st4 => LOk (CVal (ir_const 0) TVoid) st4
                                                      end
                                                  end
                                              end
                                          end
                                      | LOk _ st1 => l_err loc ("wrong arguments to " ++ name) st1
                                      end
                                  end
                                else if fence_builtin name then
                                  match args with
                                  | [oe] =>
                                      let is_thread :=
                                        (name == "__c11_atomic_thread_fence") || (name == "__atomic_thread_fence") in
                                      let st1 :=
                                        match const_value oe (fs_env st0) with
                                        | TOk (5, _) => if is_thread then l_emit ir_fence st0 else st0
                                        | _ => st0
                                        end in
                                      LOk (CVal (ir_const 0) TVoid) st1
                                  | _ => l_err loc ("wrong arguments to " ++ name) st0
                                  end
                                else
                                  match rmw_builtin name with
                                  | Some (family, op, which) =>
                                      match args with
                                      | p :: v :: _ =>
                                          match rmw_arg_aligned p ctx st0 with
                                          | LErr msg => LErr msg
                                          | LOk _ st1 =>
                                              match be_rval cb p ctx st1 with
                                              | LErr msg => LErr msg
                                              | LOk (CVal addr (TPtr t0)) st2 =>
                                                  match be_rval cb v ctx st2 with
                                                  | LErr msg => LErr msg
                                                  | LOk v0 st3 =>
                                                      let t := unqualified t0 in
                                                      match t with
                                                      | TAtomic s sz =>
                                                          match assign_convert v v0 s loc st3 with
                                                          | LErr msg => LErr msg
                                                          | LOk v1 st4 =>
                                                              match atomic_su_word s sz v1 ctx st4 with
                                                              | LErr msg => LErr msg
                                                              | LOk w st5 =>
                                                                  match atomic_word sz with
                                                                  | None => l_err loc "unsupported atomic struct size" st5
                                                                  | Some wt =>
                                                                      match rmw wt addr "xchg" (CVal w wt) ctx st5 with
                                                                      | LErr msg => LErr msg
                                                                      | LOk (CVal old_w _, _) st6 =>
                                                                          match l_local_slot t st6 with
                                                                          | LErr msg => LErr msg
                                                                          | LOk slot st7 =>
                                                                              match store_typed wt old_w slot st7 with
                                                                              | LErr msg => LErr msg
                                                                              | LOk _ st8 => LOk (CVal slot s) st8
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      | _ => atomic_rmw_value family op which t addr v v0 loc ctx st3
                                                      end
                                                  end
                                              | LOk _ st2 => l_err loc ("wrong arguments to " ++ name) st2
                                              end
                                          end
                                      | _ => l_err loc ("wrong arguments to " ++ name) st0
                                      end
                                  | None =>
                                      if (name == "__c11_atomic_compare_exchange_strong")
                                         || (name == "__c11_atomic_compare_exchange_weak")
                                         || (name == "__atomic_compare_exchange_n") then
                                        match args with
                                        | p :: e :: d :: _ =>
                                            match rmw_arg_aligned p ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk _ st1 =>
                                                match be_rval cb p ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk (CVal addr (TPtr t0)) st2 =>
                                                    match be_rval cb e ctx st2 with
                                                    | LErr msg => LErr msg
                                                    | LOk (CVal eaddr _) st3 =>
                                                        match be_rval cb d ctx st3 with
                                                        | LErr msg => LErr msg
                                                        | LOk d0 st4 =>
                                                            let t := unqualified t0 in
                                                            let prep :=
                                                              match t with
                                                              | TAtomic s sz =>
                                                                  match assign_convert d d0 s loc st4 with
                                                                  | LErr msg => LErr msg
                                                                  | LOk d1 st5 =>
                                                                      match atomic_word sz with
                                                                      | None => l_err loc "unsupported atomic struct size" st5
                                                                      | Some wt =>
                                                                          match atomic_su_word s sz (CVal eaddr s) ctx st5 with
                                                                          | LErr msg => LErr msg
                                                                          | LOk expected st6 =>
                                                                              match atomic_su_word s sz d1 ctx st6 with
                                                                              | LErr msg => LErr msg
                                                                              | LOk new_w st7 =>
                                                                                  match l_local_slot t st7 with
                                                                                  | LErr msg => LErr msg
                                                                                  | LOk slot st8 => LOk (wt, expected, new_w, Some (s, slot)) st8
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              | _ =>
                                                                  match assign_convert d d0 t loc st4 with
                                                                  | LErr msg => LErr msg
                                                                  | LOk (CVal new_w _) st5 =>
                                                                      match load_typed t eaddr ctx st5 with
                                                                      | LErr msg => LErr msg
                                                                      | LOk expected st6 => LOk (t, expected, new_w, None) st6
                                                                      end
                                                                  end
                                                              end in
                                                            match prep with
                                                            | LErr msg => LErr msg
                                                            | LOk (wt, expected, new_w, oslot) st5 =>
                                                                match cas_once wt addr expected new_w ctx st5 with
                                                                | LErr msg => LErr msg
                                                                | LOk (got, eqv) st6 =>
                                                                    let '(lf, st7) := l_label st6 in
                                                                    let '(lj, st8) := l_label st7 in
                                                                    let st9 := l_term (ir_branch eqv lj lf) st8 in
                                                                    let st10 := l_start lf st9 in
                                                                    let fail_store :=
                                                                      match oslot with
                                                                      | Some (s, slot) =>
                                                                          match store_typed wt got slot st10 with
                                                                          | LErr msg => LErr msg
                                                                          | LOk _ st11 => copy_object s slot eaddr st11
                                                                          end
                                                                      | None => store_typed t got eaddr st10
                                                                      end in
                                                                    match fail_store with
                                                                    | LErr msg => LErr msg
                                                                    | LOk _ st11 =>
                                                                        let st12 := l_term (ir_goto lj) st11 in
                                                                        let st13 := l_start lj st12 in
                                                                        LOk (CVal eqv TBool) st13
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                | LOk _ st2 => l_err loc ("wrong arguments to " ++ name) st2
                                                end
                                            end
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if (name == "__sync_val_compare_and_swap")
                                              || (name == "__sync_bool_compare_and_swap") then
                                        let is_val := name == "__sync_val_compare_and_swap" in
                                        match args with
                                        | p :: o :: n :: _ =>
                                            match rmw_arg_aligned p ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk _ st1 =>
                                                match be_rval cb p ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk (CVal addr (TPtr t0)) st2 =>
                                                    match be_rval cb o ctx st2 with
                                                    | LErr msg => LErr msg
                                                    | LOk o0 st3 =>
                                                        match be_rval cb n ctx st3 with
                                                        | LErr msg => LErr msg
                                                        | LOk n0 st4 =>
                                                            let t := unqualified t0 in
                                                            match assign_convert o o0 t loc st4 with
                                                            | LErr msg => LErr msg
                                                            | LOk (CVal expected _) st5 =>
                                                                match assign_convert n n0 t loc st5 with
                                                                | LErr msg => LErr msg
                                                                | LOk (CVal new_w _) st6 =>
                                                                    match cas_once t addr expected new_w ctx st6 with
                                                                    | LErr msg => LErr msg
                                                                    | LOk (got, eqv) st7 =>
                                                                        if is_val then LOk (CVal got t) st7
                                                                        else LOk (CVal eqv TBool) st7
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                | LOk _ st2 => l_err loc ("wrong arguments to " ++ name) st2
                                                end
                                            end
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if name == "__sync_lock_release" then
                                        match args with
                                        | p :: _ =>
                                            match be_rval cb p ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk (CVal addr (TPtr t0)) st1 =>
                                                let t := unqualified t0 in
                                                match atomic_stored t (ir_const 0) addr 3 st1 with
                                                | LErr msg => LErr msg
                                                | LOk _ st2 => LOk (CVal (ir_const 0) TVoid) st2
                                                end
                                            | LOk _ st1 => l_err loc ("wrong arguments to " ++ name) st1
                                            end
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if name == "__sync_synchronize" then
                                        match args with
                                        | [] => LOk (CVal (ir_const 0) TVoid) (l_emit ir_fence st0)
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if name == "__atomic_test_and_set" then
                                        match args with
                                        | [p; _] =>
                                            match be_rval cb p ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk (CVal addr _) st1 =>
                                                match rmw TUChar addr "xchg" (CVal (ir_const 1) TUChar) ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk (CVal old_v _, _) st2 =>
                                                    let '(set_v, st3) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom "w"]) [old_v; ir_const 0] st2 in
                                                    LOk (CVal set_v TBool) st3
                                                end
                                            end
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if name == "__atomic_clear" then
                                        match args with
                                        | [p; oe] =>
                                            match be_rval cb p ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk (CVal addr _) st1 =>
                                                match const_value oe (fs_env st1) with
                                                | TErr err => LErr (l_tr_msg loc err)
                                                | TOk (ord, _) =>
                                                    match atomic_stored TUChar (ir_const 0) addr ord st1 with
                                                    | LErr msg => LErr msg
                                                    | LOk _ st2 => LOk (CVal (ir_const 0) TVoid) st2
                                                    end
                                                end
                                            end
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if name == "zhas_union" then
                                        match args with
                                        | [p] =>
                                            match be_rval cb p ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk _ st1 => LOk (CVal (ir_const 0) TVoid) st1
                                            end
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if name == "__builtin_assume_aligned" then
                                        match args with
                                        | p :: rest =>
                                            match be_rval cb p ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk vp st1 =>
                                                match rvals_discarded cb rest ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk _ st2 => assign_convert p vp (TPtr TVoid) loc st2
                                                end
                                            end
                                        | [] => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if name == "__builtin_cpu_init" then
                                        match args with
                                        | [] =>
                                            let '(t, st1) := l_fresh st0 in
                                            let st2 := l_emit (ir_call (ir_result t "w") (ir_global "__cpu_indicator_init") []) st1 in
                                            LOk (CVal (ir_const 0) TVoid) st2
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else if (name == "__builtin_cpu_supports") || (name == "__builtin_cpu_is") then
                                        match args with
                                        | [EStr bs] =>
                                            let f := bytes_to_string bs in
                                            if name == "__builtin_cpu_supports" then
                                              match cpu_feature f with
                                              | Some (sym, off, mask) =>
                                                  match cpu_word sym off ctx st0 with
                                                  | LErr msg => LErr msg
                                                  | LOk w st1 =>
                                                      let '(m, st2) := l_let "w" (TAtom "and") [w; ir_const mask] st1 in
                                                      let '(n, st3) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom "w"]) [m; ir_const mask] st2 in
                                                      LOk (CVal n TInt) st3
                                                  end
                                              | None => LOk (CVal (ir_const 0) TInt) st0
                                              end
                                            else
                                              match cpu_model_value f with
                                              | Some (off, v) =>
                                                  match cpu_word "__cpu_model" off ctx st0 with
                                                  | LErr msg => LErr msg
                                                  | LOk w st1 =>
                                                      let '(n, st2) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom "w"]) [w; ir_const v] st1 in
                                                      LOk (CVal n TInt) st2
                                                  end
                                              | None => l_err loc ("invalid cpu name " ++ f ++ " for __builtin_cpu_is") st0
                                              end
                                        | _ => l_err loc (name ++ " needs a string literal") st0
                                        end
                                      else if name == "__builtin_expect" then
                                        match args with
                                        | [a; b] =>
                                            match be_rval cb a ctx st0 with
                                            | LErr msg => LErr msg
                                            | LOk va st1 =>
                                                match be_rval cb b ctx st1 with
                                                | LErr msg => LErr msg
                                                | LOk _ st2 => assign_convert a va TLong loc st2
                                                end
                                            end
                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                        end
                                      else
                                        match overflow_builtin name with
                                        | Some (op, fixed) => checked_arithmetic cb args op fixed ctx st0
                                        | None =>
                                            if name == "__builtin_ia32_rdtsc" then
                                              match args with
                                              | [] =>
                                                  let '(ta, st1) := l_fresh st0 in
                                                  let '(td, st2) := l_fresh st1 in
                                                  let outs := [ir_edge (TAtom "a") ta; ir_edge (TAtom "d") td] in
                                                  let st3 := l_emit (ir_asm_fixed "rdtsc" [] outs) st2 in
                                                  match convert_val (CVal ta TUInt) TULLong st3 with
                                                  | LErr msg => LErr msg
                                                  | LOk lo st4 =>
                                                      match convert_val (CVal td TUInt) TULLong st4 with
                                                      | LErr msg => LErr msg
                                                      | LOk hi0 st5 =>
                                                          match binary_op BShl hi0 (vk 32) ctx st5 with
                                                          | LErr msg => LErr msg
                                                          | LOk hi st6 => binary_op BOr hi lo ctx st6
                                                          end
                                                      end
                                                  end
                                              | _ => l_err loc ("wrong arguments to " ++ name) st0
                                              end
                                            else
                                              match vector_builtin name with
                                              | Some (ps, ret) =>
                                                  if Nat.eqb (length args) (length ps) then
                                                    match strip_prefix "__builtin_ia32_" name with
                                                    | Some short =>
                                                        match vector_args cb args ps ctx st0 with
                                                        | LErr msg => LErr msg
                                                        | LOk vs st1 => vector_op_f 4%nat short args vs ret ctx st1
                                                        end
                                                    | None => l_err loc ("wrong arguments to " ++ name) st0
                                                    end
                                                  else l_err loc ("wrong arguments to " ++ name) st0
                                              | None =>
                                                  if generic_vector_builtin name then
                                                    match vector_builtin_type_b name args (fs_env st0) with
                                                    | Some t => generic_vector_op cb name args t ctx st0
                                                    | None => l_err loc ("wrong arguments to " ++ name) st0
                                                    end
                                                  else
                                                    match bit_builtin name with
                                                    | Some (op, ty) =>
                                                        match args with
                                                        | [a] =>
                                                            match be_rval cb a ctx st0 with
                                                            | LErr msg => LErr msg
                                                            | LOk v0 st1 =>
                                                                match assign_convert a v0 ty loc st1 with
                                                                | LErr msg => LErr msg
                                                                | LOk v1 st2 =>
                                                                    match convert_val v1 TULong st2 with
                                                                    | LErr msg => LErr msg
                                                                    | LOk (CVal x _) st3 =>
                                                                        let bits := match int_info ty with Some (b, _) => 8 * b | None => 32 end in
                                                                        let '(n, st4) := bit_count op bits x st3 in
                                                                        convert_val (CVal n TLong) TInt st4
                                                                    end
                                                                end
                                                            end
                                                        | _ => l_err loc ("wrong arguments to " ++ name) st0
                                                        end
                                                    | None =>
                                                        if str_starts_with "__builtin_bswap" name then
                                                          match builtin_type name, args with
                                                          | Some ty, [a] =>
                                                              match be_rval cb a ctx st0 with
                                                              | LErr msg => LErr msg
                                                              | LOk v0 st1 =>
                                                                  match assign_convert a v0 ty loc st1 with
                                                                  | LErr msg => LErr msg
                                                                  | LOk v1 st2 =>
                                                                      match convert_val v1 TULong st2 with
                                                                      | LErr msg => LErr msg
                                                                      | LOk (CVal x _) st3 =>
                                                                          let bytes := match int_info ty with Some (b, _) => b | None => 4 end in
                                                                          let last := bytes - 1 in
                                                                          let is_ := 0 :: numlist_Z 1 last in
                                                                          let '(y, st4) := swapped_bytes is_ x last None st3 in
                                                                          convert_val (CVal y TULong) ty st4
                                                                      end
                                                                  end
                                                              end
                                                          | _, _ => l_err loc ("wrong arguments to " ++ name) st0
                                                          end
                                                        else
                                                          match rotate_builtin name with
                                                          | Some (dir, ty) =>
                                                              match args with
                                                              | [a; b] =>
                                                                  match be_rval cb a ctx st0 with
                                                                  | LErr msg => LErr msg
                                                                  | LOk va0 st1 =>
                                                                      match be_rval cb b ctx st1 with
                                                                      | LErr msg => LErr msg
                                                                      | LOk vb0 st2 =>
                                                                          let bytes := match int_info ty with Some (bs, _) => bs | None => 4 end in
                                                                          let mask := 8 * bytes - 1 in
                                                                          match assign_convert a va0 ty loc st2 with
                                                                          | LErr msg => LErr msg
                                                                          | LOk va st3 =>
                                                                              match assign_convert b vb0 ty loc st3 with
                                                                              | LErr msg => LErr msg
                                                                              | LOk vb st4 =>
                                                                                  match convert_val va TULong st4 with
                                                                                  | LErr msg => LErr msg
                                                                                  | LOk (CVal x _) st5 =>
                                                                                      match convert_val vb TULong st5 with
                                                                                      | LErr msg => LErr msg
                                                                                      | LOk (CVal n _) st6 =>
                                                                                          let '(s, st7) := l_let "l" (TAtom "and") [n; ir_const mask] st6 in
                                                                                          let '(m, st8) := l_let "l" (TAtom "neg") [n] st7 in
                                                                                          let '(t, st9) := l_let "l" (TAtom "and") [m; ir_const mask] st8 in
                                                                                          let '(first_op, second_op) :=
                                                                                            if dir == "left" then ("shl", "shr") else ("shr", "shl") in
                                                                                          let '(y1, st10) := l_let "l" (TAtom first_op) [x; s] st9 in
                                                                                          let '(y2, st11) := l_let "l" (TAtom second_op) [x; t] st10 in
                                                                                          let '(y, st12) := l_let "l" (TAtom "or") [y1; y2] st11 in
                                                                                          convert_val (CVal y TULong) ty st12
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              | _ => l_err loc ("wrong arguments to " ++ name) st0
                                                              end
                                                          | None => l_err loc ("wrong arguments to " ++ name) st0
                                                          end
                                                    end
                                              end
                                        end
                                  end
                            end
                        end
                    end
                end
          end
    end.
