(** The C parser turns a token stream from CLex into a C syntax tree,
    tracking only the active typedef names in scope so declarations and
    expressions can be disambiguated. This module is a pure Gallina
    translation of nanofil/src/c_parse.pl.

    Mutually recursive grammar rules share a single [nat] fuel counter that
    extracts to an unboxed machine integer under both OCaml extraction and
    the λANF runtime. Soft backtracking uses [PFail], while hard syntax
    errors propagate directly through [PError]. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith OrderedTypeEx FMapAVL.
From Frontend Require Import CAst CAttrs CLex.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Typedef environment

    Typedef names live in a hash-bucketed integer AVL tree so lookup,
    insertion, and shadowing stay logarithmic even on headers with thousands
    of typedefs. *)

Module ZMap := FMapAVL.Make Z_as_OT.

Definition env_hash_bound : Z := 1048576.

Fixpoint env_string_hash (s : string) (h : Z) : Z :=
  match s with
  | EmptyString => h
  | String c s' =>
      env_string_hash s' ((h * 31 + Z.of_nat (CLex.code c)) mod env_hash_bound)
  end.

Definition c_env : Type := ZMap.t (list string).

Definition env_empty : c_env := ZMap.empty _.

Definition env_mem (name : string) (e : c_env) : bool :=
  match ZMap.find (env_string_hash name 0) e with
  | Some bucket => existsb (String.eqb name) bucket
  | None => false
  end.

Definition env_add (name : string) (e : c_env) : c_env :=
  let k := env_string_hash name 0 in
  let bucket := match ZMap.find k e with Some b => b | None => [] end in
  if existsb (String.eqb name) bucket then e
  else ZMap.add k (name :: bucket) e.

Definition env_remove (name : string) (e : c_env) : c_env :=
  let k := env_string_hash name 0 in
  match ZMap.find k e with
  | None => e
  | Some bucket =>
      let bucket' := filter (fun s => negb (String.eqb name s)) bucket in
      match bucket' with
      | [] => ZMap.remove k e
      | _ => ZMap.add k bucket' e
      end
  end.

Definition env_add_many (names : list string) (e : c_env) : c_env :=
  fold_left (fun acc n => env_add n acc) names e.

Definition env_remove_many (names : list string) (e : c_env) : c_env :=
  fold_left (fun acc n => env_remove n acc) names e.

Definition initial_env : c_env :=
  env_add "__builtin_va_list"
    (env_add "__int128_t"
      (env_add "__uint128_t" env_empty)).

(** ## Parser results and token primitives

    Every nonterminal returns [POk v rest] on success, [PFail] when an
    optional alternative does not match, or [PError msg] for a fatal syntax
    error that must not be swallowed by backtracking. *)

Inductive pres (A : Type) : Type :=
| POk (v : A) (rest : list token)
| PFail
| PError (msg : string).

Arguments POk {A} v rest.
Arguments PFail {A}.
Arguments PError {A} msg.

Definition p_bind {A B : Type} (r : pres A) (k : A -> list token -> pres B) : pres B :=
  match r with
  | POk v rest => k v rest
  | PFail => PFail
  | PError m => PError m
  end.

Definition p_or {A : Type} (r1 : pres A) (r2 : unit -> pres A) : pres A :=
  match r1 with
  | POk v rest => POk v rest
  | PError m => PError m
  | PFail => r2 tt
  end.

Definition peek_loc (ts : list token) : c_loc :=
  match ts with
  | mkTok _ l :: _ => l
  | [] => LocEof
  end.

Definition token_preview (k : tok_kind) : string :=
  match k with
  | TPunct p => p
  | TKw w => w
  | TId n => n
  | TInt _ _ _ => "int"
  | TFloat _ => "float"
  | TImag _ => "imag"
  | TChr _ => "chr"
  | TStr _ => "str"
  | TWStr _ _ => "wstr"
  | TPragmaWeak n _ => n
  | TPragmaPack _ => "pragma_pack"
  end.

Definition parse_err_msg (msg : string) (ts : list token) : string :=
  match ts with
  | mkTok k l :: _ =>
      loc_to_string l ++ ": " ++ msg ++ ", at " ++ token_preview k
  | [] =>
      "end of input: " ++ msg
  end.

Definition parse_err {A : Type} (msg : string) (ts : list token) : pres A :=
  PError (parse_err_msg msg ts).

Definition expect_punct (p : string) (ts : list token) : pres unit :=
  match ts with
  | mkTok (TPunct q) _ :: rest =>
      if String.eqb p q then POk tt rest
      else parse_err ("expected " ++ p) ts
  | _ => parse_err ("expected " ++ p) ts
  end.

Definition match_punct_tok (p : string) (ts : list token) : option (list token) :=
  match ts with
  | mkTok (TPunct q) _ :: rest => if String.eqb p q then Some rest else None
  | _ => None
  end.

Definition match_kw_tok (w : string) (ts : list token) : option (list token) :=
  match ts with
  | mkTok (TKw k) _ :: rest => if String.eqb w k then Some rest else None
  | _ => None
  end.

Definition is_punct_head (p : string) (ts : list token) : bool :=
  match ts with
  | mkTok (TPunct q) _ :: _ => String.eqb p q
  | _ => false
  end.

(** ## Specifier, operator, and declarator helpers *)

Definition is_storage_kw (s : string) : bool :=
  str_in s [ "typedef"; "extern"; "static"; "auto"; "register"; "thread_local" ].

Definition is_tspec_kw (s : string) : bool :=
  str_in s [ "void"; "char"; "short"; "int"; "long"; "float"; "double";
             "signed"; "unsigned"; "bool"; "complex"; "int128"; "float16"; "bf16" ].

Definition is_qual_kw (s : string) : bool :=
  str_in s [ "const"; "volatile"; "restrict"; "atomic" ].

Definition is_fspec_kw (s : string) : bool :=
  str_in s [ "inline"; "noreturn" ].

Definition spec_sets_type (sp : c_spec) : bool :=
  match sp with
  | SpTspec _ | SpSu _ _ _ _ | SpEnum _ _ | SpTypeofType _ | SpTypeofExpr _
  | SpAutoType | SpAtomic _ | SpTname _ => true
  | _ => false
  end.

Definition type_start_token (k : tok_kind) (env : c_env) : bool :=
  match k with
  | TKw w =>
      is_tspec_kw w || is_qual_kw w ||
      str_in w [ "struct"; "union"; "enum"; "typeof"; "attribute";
                 "alignas"; "extension" ]
  | TId n => env_mem n env
  | _ => false
  end.

Fixpoint starts_type (env : c_env) (ts : list token) : bool :=
  match ts with
  | mkTok (TKw w) _ :: rest =>
      if String.eqb w "extension" then starts_type env rest
      else type_start_token (TKw w) env
  | mkTok k _ :: _ => type_start_token k env
  | [] => false
  end.

Definition is_label_start (ts : list token) : bool :=
  match ts with
  | mkTok (TId _) _ :: mkTok (TPunct p) _ :: _ => String.eqb p ":"
  | _ => false
  end.

Definition is_assign_op (p : string) : bool :=
  str_in p [ "="; "*="; "/="; "%="; "+="; "-="; "<<="; ">>="; "&="; "^="; "|=" ].

Definition binop_at_level (level : nat) (p : string) : option c_binop :=
  match level with
  | 1%nat => if String.eqb p "||" then Some BLor else None
  | 2%nat => if String.eqb p "&&" then Some BLand else None
  | 3%nat => if String.eqb p "|" then Some BOr else None
  | 4%nat => if String.eqb p "^" then Some BXor else None
  | 5%nat => if String.eqb p "&" then Some BAnd else None
  | 6%nat =>
      if String.eqb p "==" then Some BEq
      else if String.eqb p "!=" then Some BNe
      else None
  | 7%nat =>
      if String.eqb p "<" then Some BLt
      else if String.eqb p ">" then Some BGt
      else if String.eqb p "<=" then Some BLe
      else if String.eqb p ">=" then Some BGe
      else None
  | 8%nat =>
      if String.eqb p "<<" then Some BShl
      else if String.eqb p ">>" then Some BShr
      else None
  | 9%nat =>
      if String.eqb p "+" then Some BAdd
      else if String.eqb p "-" then Some BSub
      else None
  | 10%nat =>
      if String.eqb p "*" then Some BMul
      else if String.eqb p "/" then Some BDiv
      else if String.eqb p "%" then Some BMod
      else None
  | _ => None
  end.

Definition lookup_unop (p : string) : option c_unop :=
  if String.eqb p "&" then Some UAddr
  else if String.eqb p "*" then Some UDeref
  else if String.eqb p "+" then Some UPlus
  else if String.eqb p "-" then Some UNeg
  else if String.eqb p "~" then Some UBnot
  else if String.eqb p "!" then Some UNot
  else None.

(** Replace the single [DTBase] hole at the bottom of a declarator type spine
    with [mid], matching the logic-variable composition in c_parse.pl. *)
Fixpoint subst_dcl_base (outer mid : c_dcl_type) : c_dcl_type :=
  match outer with
  | DTBase => mid
  | DTPtr inner qs => DTPtr (subst_dcl_base inner mid) qs
  | DTArray inner sz => DTArray (subst_dcl_base inner mid) sz
  | DTFunc inner ps => DTFunc (subst_dcl_base inner mid) ps
  end.

Definition string_of_bytes (bs : list Z) : string :=
  CLex.string_of_rev (rev_append (map (fun z => CLex.byte (Z.to_nat z)) bs) []).

Definition is_blank_asm (bs : list Z) : bool :=
  forallb (fun b => Z.eqb b 32 || Z.eqb b 9 || Z.eqb b 10 || Z.eqb b 13) bs.

(** Classify an unsupported inline assembly token list as [AUMemory] if an
    operand constraint contains `'m'`, otherwise [AUOther]. *)
Definition classify_asm_kind (ts : list attr_tok) : c_asm_unsupported :=
  let fix take_strs (xs : list attr_tok) (acc : list Z) : list Z * list attr_tok :=
    match xs with
    | ATok (TStr bs) :: rest => take_strs rest (rev_append bs acc)
    | _ => (rev_append acc [], xs)
    end in
  let fix has_mem (xs : list attr_tok) : bool :=
    match xs with
    | ATok (TStr c) :: AGroup _ :: rest =>
        if existsb (Z.eqb 109) c then true else has_mem rest
    | _ :: rest => has_mem rest
    | [] => false
    end in
  let '(tpl, rest) := take_strs ts [] in
  if has_mem rest then AUMemory tpl else AUOther.

(** ## Balanced attribute token parsing

    GNU attributes and C23 `[[...]]` attribute specifiers parse before full
    expressions and therefore need no mutual recursion with expressions. *)

Fixpoint parse_balanced (fuel : nat) (ts : list token) (acc : list attr_tok)
  : pres (list attr_tok) :=
  match fuel with
  | O => parse_err "attribute fuel exhausted" ts
  | S f =>
      match ts with
      | mkTok (TPunct p) _ :: rest =>
          if String.eqb p ")" then POk (rev_append acc []) rest
          else if String.eqb p "(" then
            p_bind (parse_balanced f rest []) (fun inner rest1 =>
              parse_balanced f rest1 (AGroup inner :: acc))
          else parse_balanced f rest (ATok (TPunct p) :: acc)
      | mkTok k _ :: rest =>
          parse_balanced f rest (ATok k :: acc)
      | [] => parse_err "unbalanced parentheses" ts
      end
  end.

Definition parse_gnu_attr (fuel : nat) (ts : list token) : pres (list attr_tok) :=
  match ts with
  | mkTok (TKw w) loc :: rest =>
      if String.eqb w "attribute" then
        p_bind (expect_punct "(" rest) (fun _ rest1 =>
          p_bind (parse_balanced fuel rest1 []) (fun a0 rest2 =>
            match check_known_attributes a0 loc with
            | COk tt => POk a0 rest2
            | CErr m => PError m
            end))
      else PFail
  | mkTok (TId n) _ :: rest =>
      if String.eqb n "__declspec" then
        p_bind (expect_punct "(" rest) (fun _ rest1 =>
          p_bind (parse_balanced fuel rest1 []) (fun a0 rest2 =>
            match declspec_attr a0 with
            | Some a => POk a rest2
            | None => parse_err "this __declspec is not supported" rest2
            end))
      else PFail
  | _ => PFail
  end.

Definition attr_delim_close (p : string) : option string :=
  if String.eqb p "(" then Some ")"
  else if String.eqb p "[" then Some "]"
  else if String.eqb p "{" then Some "}"
  else None.

Fixpoint skip_attr_arg (fuel : nat) (close : string) (ts : list token) : pres unit :=
  match fuel with
  | O => parse_err "unbalanced attribute argument" ts
  | S f =>
      match ts with
      | mkTok (TPunct p) _ :: rest =>
          if String.eqb p close then POk tt rest
          else
            match attr_delim_close p with
            | Some end_p =>
                p_bind (skip_attr_arg f end_p rest) (fun _ rest1 =>
                  skip_attr_arg f close rest1)
            | None =>
                if String.eqb p ")" || String.eqb p "]" || String.eqb p "}" then
                  parse_err "unbalanced attribute argument" ts
                else skip_attr_arg f close rest
            end
      | _ :: rest => skip_attr_arg f close rest
      | [] => parse_err "unbalanced attribute argument" ts
      end
  end.

Definition read_attr_word (ts : list token) : option (string * list token) :=
  match ts with
  | mkTok (TId w) _ :: rest | mkTok (TKw w) _ :: rest => Some (w, rest)
  | _ => None
  end.

Fixpoint parse_c23_entries (fuel : nat) (ts : list token) : pres unit :=
  match fuel with
  | O => parse_err "attribute fuel exhausted" ts
  | S f =>
      let loc := peek_loc ts in
      let step :=
        match read_attr_word ts with
        | Some (w1, rest1) =>
            match match_punct_tok ":" rest1 with
            | Some rest2 =>
                p_bind (expect_punct ":" rest2) (fun _ rest3 =>
                  match read_attr_word rest3 with
                  | Some (w2, rest4) =>
                      if (String.eqb w1 "gnu" || String.eqb w1 "__gnu__") &&
                         (String.eqb w2 "packed" || String.eqb w2 "__packed__" ||
                          String.eqb w2 "aligned" || String.eqb w2 "__aligned__")
                      then parse_err "alignment attributes are not supported" rest4
                      else
                        let after_arg :=
                          match match_punct_tok "(" rest4 with
                          | Some r => skip_attr_arg f ")" r
                          | None => POk tt rest4
                          end in
                        p_bind after_arg (fun _ rest5 =>
                          match check_c23_known (Some w1) w2 loc with
                          | COk tt => POk tt rest5
                          | CErr m => PError m
                          end)
                  | None => parse_err "expected attribute name" rest3
                  end)
            | None =>
                let after_arg :=
                  match match_punct_tok "(" rest1 with
                  | Some r => skip_attr_arg f ")" r
                  | None => POk tt rest1
                  end in
                p_bind after_arg (fun _ rest2 =>
                  match check_c23_known None w1 loc with
                  | COk tt => POk tt rest2
                  | CErr m => PError m
                  end)
            end
        | None => POk tt ts
        end in
      p_bind step (fun _ rest =>
        match match_punct_tok "," rest with
        | Some rest' => parse_c23_entries f rest'
        | None => POk tt rest
        end)
  end.

Definition parse_c23_attr (fuel : nat) (ts : list token) : pres unit :=
  match ts with
  | mkTok (TPunct p1) _ :: mkTok (TPunct p2) _ :: rest =>
      if String.eqb p1 "[" && String.eqb p2 "[" then
        p_bind (parse_c23_entries fuel rest) (fun _ rest1 =>
          p_bind (expect_punct "]" rest1) (fun _ rest2 =>
            expect_punct "]" rest2))
      else PFail
  | _ => PFail
  end.

Fixpoint skip_discarded_attrs (fuel : nat) (ts : list token) : pres unit :=
  match fuel with
  | O => POk tt ts
  | S f =>
      let loc := peek_loc ts in
      match parse_gnu_attr f ts with
      | POk a rest =>
          match check_hint_attributes a loc with
          | COk tt => skip_discarded_attrs f rest
          | CErr m => PError m
          end
      | PError m => PError m
      | PFail =>
          match parse_c23_attr f ts with
          | POk _ rest => skip_discarded_attrs f rest
          | PError m => PError m
          | PFail => POk tt ts
          end
      end
  end.

Fixpoint skip_leading_attrs (fuel : nat) (ts : list token) : list token :=
  match fuel with
  | O => ts
  | S f =>
      match parse_gnu_attr f ts with
      | POk _ rest => skip_leading_attrs f rest
      | _ =>
          match parse_c23_attr f ts with
          | POk _ rest => skip_leading_attrs f rest
          | _ => ts
          end
      end
  end.

Fixpoint parse_attr_list (fuel : nat) (ts : list token) (acc : list (list attr_tok))
  : pres (list (list attr_tok)) :=
  match fuel with
  | O => POk (rev_append acc []) ts
  | S f =>
      match parse_gnu_attr f ts with
      | POk a rest => parse_attr_list f rest (a :: acc)
      | PError m => PError m
      | PFail =>
          match ts with
          | mkTok (TPunct p1) _ :: mkTok (TPunct p2) _ :: rest0 =>
              if String.eqb p1 "[" && String.eqb p2 "[" then
                let try_gnu_packed :=
                  match read_attr_word rest0 with
                  | Some (pfx, mkTok (TPunct c1) _ :: mkTok (TPunct c2) _ :: rest1) =>
                      if (String.eqb pfx "gnu" || String.eqb pfx "__gnu__") &&
                         String.eqb c1 ":" && String.eqb c2 ":" then
                        match read_attr_word rest1 with
                        | Some (nm, mkTok (TPunct b1) _ :: mkTok (TPunct b2) _ :: rest2) =>
                            if (String.eqb nm "packed" || String.eqb nm "__packed__") &&
                               String.eqb b1 "]" && String.eqb b2 "]" then
                              Some rest2
                            else None
                        | _ => None
                        end
                      else None
                  | _ => None
                  end in
                match try_gnu_packed with
                | Some rest2 =>
                    parse_attr_list f rest2
                      ([AGroup [ATok (TId "packed")]] :: acc)
                | None =>
                    match parse_c23_attr f ts with
                    | POk _ rest => parse_attr_list f rest acc
                    | PError m => PError m
                    | PFail => POk (rev_append acc []) ts
                    end
                end
              else POk (rev_append acc []) ts
          | _ => POk (rev_append acc []) ts
          end
      end
  end.

Fixpoint parse_enum_attrs (fuel : nat) (packed : bool) (ts : list token)
  : pres bool :=
  match fuel with
  | O => POk packed ts
  | S f =>
      let loc := peek_loc ts in
      match parse_gnu_attr f ts with
      | POk a rest =>
          let '(a1, p1) :=
            match select_packed a with
            | Some r => (r, true)
            | None => (a, packed)
            end in
          match check_hint_attributes a1 loc with
          | COk tt => parse_enum_attrs f p1 rest
          | CErr m => PError m
          end
      | PError m => PError m
      | PFail =>
          match parse_c23_attr f ts with
          | POk _ rest => parse_enum_attrs f packed rest
          | PError m => PError m
          | PFail => POk packed ts
          end
      end
  end.

Fixpoint parse_string_bytes_acc (ts : list token) (acc : list Z)
  : option (list Z * list token) :=
  match ts with
  | mkTok (TStr bs) _ :: rest =>
      parse_string_bytes_acc rest (rev_append bs acc)
  | _ => Some (rev_append acc [], ts)
  end.

Definition parse_string_bytes (ts : list token) : pres (list Z) :=
  match ts with
  | mkTok (TStr bs) _ :: rest =>
      match parse_string_bytes_acc rest (rev_append bs []) with
      | Some (all, rem) => POk all rem
      | None => PFail
      end
  | _ => PFail
  end.

Definition parse_gnu_suffix (fuel : nat) (ts : list token)
  : pres (option string * list c_spec) :=
  p_bind (parse_attr_list fuel ts []) (fun a0 rest1 =>
    let asm_step :=
      match match_kw_tok "asm" rest1 with
      | Some r1 =>
          p_bind (expect_punct "(" r1) (fun _ r2 =>
            p_bind (parse_string_bytes r2) (fun bs r3 =>
              p_bind (expect_punct ")" r3) (fun _ r4 =>
                POk (Some (string_of_bytes bs)) r4)))
      | None => POk None rest1
      end in
    p_bind asm_step (fun asm_sym rest2 =>
      p_bind (parse_attr_list fuel rest2 []) (fun a1 rest3 =>
        POk (asm_sym, map SpAttr (app a0 a1)) rest3))).

Definition starts_decl (fuel : nat) (env : c_env) (ts : list token) : bool :=
  let rest := skip_leading_attrs fuel ts in
  if is_label_start rest then false
  else if starts_type env rest then true
  else
    match rest with
    | mkTok (TKw w) _ :: _ =>
        is_storage_kw w || is_fspec_kw w || String.eqb w "auto_type"
    | _ => false
    end.

Definition is_extension_decl (fuel : nat) (env : c_env) (ts : list token) : bool :=
  match ts with
  | mkTok (TKw w) _ :: rest =>
      if String.eqb w "extension" then
        match rest with
        | mkTok (TKw w2) _ :: _ =>
            if String.eqb w2 "static_assert" || String.eqb w2 "extension" then true
            else starts_decl fuel env rest
        | _ => starts_decl fuel env rest
        end
      else false
  | _ => false
  end.

(** ## Declaration-level helpers: `__auto_type`, typedef scopes, and `__label__` *)

Fixpoint remove_auto_type (specs : list c_spec) : option (list c_spec) :=
  match specs with
  | [] => None
  | SpAutoType :: rest => Some rest
  | sp :: rest =>
      match remove_auto_type rest with
      | Some r => Some (sp :: r)
      | None => None
      end
  end.

Definition apply_auto_type (specs0 : list c_spec) (inits : list c_init_decl)
  (loc : c_loc) : c_result (list c_spec) :=
  match remove_auto_type specs0 with
  | None => COk specs0
  | Some rest =>
      match inits with
      | [InitDecl _ (Some (InitExpr e))] =>
          COk (SpTypeofExpr (EComma (ENum 0 SufNone RadDec) e) :: rest)
      | _ =>
          CErr (loc_to_string loc ++
                ": __auto_type needs one declarator with an expression initializer")
      end
  end.

Definition has_typedef_storage (specs : list c_spec) : bool :=
  existsb (fun sp => match sp with SpStorage s => String.eqb s "typedef" | _ => false end) specs.

Definition init_decl_names (inits : list c_init_decl) : list string :=
  flat_map
    (fun idcl =>
       match idcl with
       | InitDecl (Dcl (Some n) _ _) _ => [n]
       | _ => []
       end)
    inits.

Definition update_decl_env (specs : list c_spec) (inits : list c_init_decl)
  (env : c_env) : c_env :=
  let ns := init_decl_names inits in
  if has_typedef_storage specs then env_add_many ns env
  else env_remove_many ns env.

Definition update_params_env (ps : c_params) (env : c_env) : c_env :=
  match ps with
  | PParams params _ =>
      let ns :=
        flat_map
          (fun p =>
             match p with
             | Param _ (Dcl (Some n) _ _) => [n]
             | _ => []
             end)
          params in
      env_remove_many ns env
  | _ => env
  end.

Definition check_one_decl_attrs (attrs : list c_spec) (loc : c_loc) : c_result unit :=
  match first_honored_attr attrs with
  | Some w =>
      CErr (loc_to_string loc ++ ": attribute " ++ w ++
            " on one of several declarators is not supported")
  | None => COk tt
  end.

(** Rename GNU `__label__` declarations throughout a block's syntax tree. *)
Definition rename_label (lmap : list (string * string)) (l : string) : string :=
  let fix go (xs : list (string * string)) : string :=
    match xs with
    | [] => l
    | (a, b) :: rest => if String.eqb a l then b else go rest
    end in
  go lmap.

Section LocalRename.
  Variable lmap : list (string * string).

  Fixpoint rename_item (it : c_item) : c_item :=
    match it with
    | IDecl loc sps inits =>
        IDecl loc (map rename_spec sps) (map rename_init_decl inits)
    | IFundef loc sps dcl body =>
        IFundef loc (map rename_spec sps) (rename_dcl dcl) (rename_stmt body)
    | IStaticAssert loc c msg => IStaticAssert loc (rename_expr c) msg
    | IPragmaWeak _ _ _ | IToplevelAsm _ _ => it
    end
  with rename_init_decl (idcl : c_init_decl) : c_init_decl :=
    match idcl with
    | InitDecl dcl oinit =>
        InitDecl (rename_dcl dcl) (option_map rename_init oinit)
    end
  with rename_dcl (dcl : c_dcl) : c_dcl :=
    match dcl with
    | Dcl nm ty asym => Dcl nm (rename_dcl_type ty) asym
    end
  with rename_dcl_type (ty : c_dcl_type) : c_dcl_type :=
    match ty with
    | DTBase => DTBase
    | DTPtr inner qs => DTPtr (rename_dcl_type inner) qs
    | DTArray inner sz => DTArray (rename_dcl_type inner) (rename_array_size sz)
    | DTFunc inner ps => DTFunc (rename_dcl_type inner) (rename_params ps)
    end
  with rename_array_size (sz : c_array_size) : c_array_size :=
    match sz with
    | ASNone => ASNone
    | ASStar => ASStar
    | ASExpr e => ASExpr (rename_expr e)
    end
  with rename_params (ps : c_params) : c_params :=
    match ps with
    | PUnspecified => PUnspecified
    | PParams xs v => PParams (map rename_param xs) v
    | PKnr ns => PKnr ns
    | PKnrDef ns ds => PKnrDef ns (map rename_item ds)
    end
  with rename_param (p : c_param) : c_param :=
    match p with
    | Param sps dcl => Param (map rename_spec sps) (rename_dcl dcl)
    end
  with rename_type_name (tn : c_type_name) : c_type_name :=
    match tn with
    | TypeName sps ty => TypeName (map rename_spec sps) (rename_dcl_type ty)
    end
  with rename_spec (sp : c_spec) : c_spec :=
    match sp with
    | SpSu k tg oms ats => SpSu k tg (option_map (map rename_member) oms) ats
    | SpEnum tg es => SpEnum tg (rename_enumerators es)
    | SpAlignasType tn => SpAlignasType (rename_type_name tn)
    | SpAlignasExpr e => SpAlignasExpr (rename_expr e)
    | SpTypeofType tn => SpTypeofType (rename_type_name tn)
    | SpTypeofExpr e => SpTypeofExpr (rename_expr e)
    | SpAtomic tn => SpAtomic (rename_type_name tn)
    | _ => sp
    end
  with rename_member (m : c_member) : c_member :=
    match m with
    | MField sps dcl ow =>
        MField (map rename_spec sps) (rename_dcl dcl) (option_map rename_expr ow)
    | MStaticAssert loc c msg => MStaticAssert loc (rename_expr c) msg
    end
  with rename_enumerators (es : c_enumerators) : c_enumerators :=
    match es with
    | EnumNone => EnumNone
    | EnumList xs => EnumList (map rename_enumerator xs)
    | EnumPacked xs => EnumPacked (map rename_enumerator xs)
    end
  with rename_enumerator (e : c_enumerator) : c_enumerator :=
    match e with
    | Enumerator nm ov => Enumerator nm (option_map rename_expr ov)
    end
  with rename_init (ini : c_init) : c_init :=
    match ini with
    | InitExpr e => InitExpr (rename_expr e)
    | InitList es => InitList (map rename_init_entry es)
    end
  with rename_init_entry (en : c_init_entry) : c_init_entry :=
    match en with
    | InitEntry ds ini => InitEntry (map rename_designator ds) (rename_init ini)
    end
  with rename_designator (d : c_designator) : c_designator :=
    match d with
    | DField f => DField f
    | DIndex e => DIndex (rename_expr e)
    | DRange lo hi => DRange (rename_expr lo) (rename_expr hi)
    end
  with rename_stmt (st : c_stmt) : c_stmt :=
    match st with
    | Stmt loc body => Stmt loc (rename_stmt_body body)
    end
  with rename_block_item (bi : c_block_item) : c_block_item :=
    match bi with
    | BIDecl it => BIDecl (rename_item it)
    | BIStmt st => BIStmt (rename_stmt st)
    end
  with rename_for_init (fi : c_for_init) : c_for_init :=
    match fi with
    | FINone => FINone
    | FIExpr e => FIExpr (rename_expr e)
    | FIDecl it => FIDecl (rename_item it)
    end
  with rename_asm_op (ao : c_asm_op) : c_asm_op :=
    match ao with
    | AsmOp c e => AsmOp c (rename_expr e)
    end
  with rename_stmt_body (sb : c_stmt_body) : c_stmt_body :=
    match sb with
    | SBlock bis => SBlock (map rename_block_item bis)
    | SExpr e => SExpr (rename_expr e)
    | SNull => SNull
    | SIf c t oe => SIf (rename_expr c) (rename_stmt t) (option_map rename_stmt oe)
    | SWhile c b => SWhile (rename_expr c) (rename_stmt b)
    | SDo b c => SDo (rename_stmt b) (rename_expr c)
    | SFor fi oc os b =>
        SFor (rename_for_init fi) (option_map rename_expr oc)
             (option_map rename_expr os) (rename_stmt b)
    | SSwitch c b => SSwitch (rename_expr c) (rename_stmt b)
    | SCase v b => SCase (rename_expr v) (rename_stmt b)
    | SCaseRange lo hi b => SCaseRange (rename_expr lo) (rename_expr hi) (rename_stmt b)
    | SDefault b => SDefault (rename_stmt b)
    | SBreak => SBreak
    | SContinue => SContinue
    | SReturn oe => SReturn (option_map rename_expr oe)
    | SGoto l => SGoto (rename_label lmap l)
    | SComputedGoto e => SComputedGoto (rename_expr e)
    | SLabel l b => SLabel (rename_label lmap l) (rename_stmt b)
    | SAsmEmpty outs ins clobs g =>
        SAsmEmpty (map rename_asm_op outs) (map rename_asm_op ins)
          (map (fun c => match c with
                         | ACName s => ACName s
                         | ACLabels ls => ACLabels (map (rename_label lmap) ls)
                         end) clobs) g
    | SAsm tpl outs ins clobs g =>
        SAsm tpl (map rename_asm_op outs) (map rename_asm_op ins)
          (map (fun c => match c with
                         | ACName s => ACName s
                         | ACLabels ls => ACLabels (map (rename_label lmap) ls)
                         end) clobs) g
    | SUnsupportedAsm k => SUnsupportedAsm k
    end
  with rename_generic_assoc (ga : c_generic_assoc) : c_generic_assoc :=
    match ga with
    | GAssocType tn e => GAssocType (rename_type_name tn) (rename_expr e)
    | GAssocDefault e => GAssocDefault (rename_expr e)
    end
  with rename_expr (e : c_expr) : c_expr :=
    match e with
    | EId _ | ENum _ _ _ | EChr _ | EFloat _ | EImag _ | EStr _ | EWStr _ _ => e
    | EBin op a b => EBin op (rename_expr a) (rename_expr b)
    | EAssign op a b => EAssign op (rename_expr a) (rename_expr b)
    | EUn op a => EUn op (rename_expr a)
    | ECond c a b => ECond (rename_expr c) (rename_expr a) (rename_expr b)
    | EGCond c b => EGCond (rename_expr c) (rename_expr b)
    | EComma a b => EComma (rename_expr a) (rename_expr b)
    | ECall fn args => ECall (rename_expr fn) (map rename_expr args)
    | EConvertVector a tn => EConvertVector (rename_expr a) (rename_type_name tn)
    | EIndex a i => EIndex (rename_expr a) (rename_expr i)
    | EMember a f => EMember (rename_expr a) f
    | EArrow a f => EArrow (rename_expr a) f
    | ECast tn a => ECast (rename_type_name tn) (rename_expr a)
    | ESizeofType tn => ESizeofType (rename_type_name tn)
    | ESizeofExpr a => ESizeofExpr (rename_expr a)
    | EAlignofType tn => EAlignofType (rename_type_name tn)
    | EAlignofExpr a => EAlignofExpr (rename_expr a)
    | ERealPart a => ERealPart (rename_expr a)
    | EImagPart a => EImagPart (rename_expr a)
    | EComplit tn es => EComplit (rename_type_name tn) (map rename_init_entry es)
    | EOffsetof tn ds => EOffsetof (rename_type_name tn) (map rename_designator ds)
    | EVaArg a tn => EVaArg (rename_expr a) (rename_type_name tn)
    | EBitCast tn a => EBitCast (rename_type_name tn) (rename_expr a)
    | ETypesCompatible a b => ETypesCompatible (rename_type_name a) (rename_type_name b)
    | EStmtExpr b => EStmtExpr (rename_stmt b)
    | ELabelAddr l => ELabelAddr (rename_label lmap l)
    | EGeneric c assocs => EGeneric (rename_expr c) (map rename_generic_assoc assocs)
    end.
End LocalRename.

(** Concatenate adjacent narrow or wide string literals. *)
Inductive str_part : Type :=
| SPNarrow (bs : list Z)
| SPWide (wt : wide_type) (vs : list Z).

Definition wide_type_eqb (a b : wide_type) : bool :=
  match a, b with
  | WInt, WInt | WUShort, WUShort | WUInt, WUInt => true
  | _, _ => false
  end.

Fixpoint collect_str_parts (ts : list token) (acc : list str_part)
  : list str_part * list token :=
  match ts with
  | mkTok (TStr bs) _ :: rest => collect_str_parts rest (SPNarrow bs :: acc)
  | mkTok (TWStr wt vs) _ :: rest => collect_str_parts rest (SPWide wt vs :: acc)
  | _ => (rev_append acc [], ts)
  end.

Definition combine_str_parts (parts : list str_part) : c_result c_expr :=
  let fix check_wt (ps : list str_part) (cur : option wide_type)
    : c_result (option wide_type) :=
    match ps with
    | [] => COk cur
    | SPNarrow _ :: rest => check_wt rest cur
    | SPWide wt _ :: rest =>
        match cur with
        | None => check_wt rest (Some wt)
        | Some wt0 =>
            if wide_type_eqb wt0 wt then check_wt rest cur
            else CErr "concatenating string literals of different wide types"
        end
    end in
  let all :=
    flat_map (fun p => match p with SPNarrow bs => bs | SPWide _ vs => vs end) parts in
  match check_wt parts None with
  | CErr m => CErr m
  | COk None => COk (EStr all)
  | COk (Some wt) => COk (EWStr wt all)
  end.

(** Read `__label__ a, b;` declarations at the head of a block. *)
Fixpoint parse_label_names (fuel : nat) (ts : list token) (acc : list string)
  : pres (list string) :=
  match fuel with
  | O => parse_err "expected a label name after __label__" ts
  | S f =>
      match ts with
      | mkTok (TId l) _ :: rest =>
          match match_punct_tok "," rest with
          | Some rest' => parse_label_names f rest' (l :: acc)
          | None => POk (rev_append (l :: acc) []) rest
          end
      | _ => parse_err "expected a label name after __label__" ts
      end
  end.

Fixpoint parse_local_labels (fuel : nat) (ts : list token)
  (acc : list (string * string)) : pres (list (string * string)) :=
  match fuel with
  | O => POk (rev_append acc []) ts
  | S f =>
      match ts with
      | mkTok (TId n) _ :: rest =>
          if String.eqb n "__label__" then
            let k := Z.of_nat (List.length rest) in
            let suf := ".." ++ z_to_string k in
            p_bind (parse_label_names f rest []) (fun names rest1 =>
              p_bind (expect_punct ";" rest1) (fun _ rest2 =>
                let pairs := map (fun nm => (nm, nm ++ suf)) names in
                parse_local_labels f rest2 (rev_append pairs acc)))
          else POk (rev_append acc []) ts
      | _ => POk (rev_append acc []) ts
      end
  end.

(** Read pointer qualifiers, optionally sliding symbol declaration attributes
    onto the enclosing declaration. *)
Fixpoint parse_qualifiers (fuel : nat) (slid : option (list c_spec))
  (ts : list token) (qacc : list string)
  : pres (list string * option (list c_spec)) :=
  match fuel with
  | O => POk (rev_append qacc [], slid) ts
  | S f =>
      match ts with
      | mkTok (TKw q) _ :: rest =>
          if is_qual_kw q then parse_qualifiers f slid rest (q :: qacc)
          else
            let loc := peek_loc ts in
            match parse_gnu_attr f ts with
            | POk a rest1 =>
                match slid with
                | Some s0 =>
                    if all_honored_are_decl a then
                      parse_qualifiers f (Some (app s0 [SpAttr a])) rest1 qacc
                    else
                      match check_hint_attributes a loc with
                      | COk tt => parse_qualifiers f slid rest1 qacc
                      | CErr m => PError m
                      end
                | None =>
                    match check_hint_attributes a loc with
                    | COk tt => parse_qualifiers f None rest1 qacc
                    | CErr m => PError m
                    end
                end
            | PError m => PError m
            | PFail => POk (rev_append qacc [], slid) ts
            end
      | mkTok (TId n) _ :: rest =>
          if is_nullability n then parse_qualifiers f slid rest qacc
          else
            let loc := peek_loc ts in
            match parse_gnu_attr f ts with
            | POk a rest1 =>
                match slid with
                | Some s0 =>
                    if all_honored_are_decl a then
                      parse_qualifiers f (Some (app s0 [SpAttr a])) rest1 qacc
                    else
                      match check_hint_attributes a loc with
                      | COk tt => parse_qualifiers f slid rest1 qacc
                      | CErr m => PError m
                      end
                | None =>
                    match check_hint_attributes a loc with
                    | COk tt => parse_qualifiers f None rest1 qacc
                    | CErr m => PError m
                    end
                end
            | PError m => PError m
            | PFail => POk (rev_append qacc [], slid) ts
            end
      | _ =>
          match parse_c23_attr f ts with
          | POk _ rest1 => parse_qualifiers f slid rest1 qacc
          | PError m => PError m
          | PFail => POk (rev_append qacc [], slid) ts
          end
      end
  end.

Fixpoint parse_asm_qualifiers (ts : list token) (is_goto : bool)
  : bool * list token :=
  match ts with
  | mkTok (TKw w) _ :: rest =>
      if String.eqb w "volatile" || String.eqb w "inline" then
        parse_asm_qualifiers rest is_goto
      else if String.eqb w "goto" then
        parse_asm_qualifiers rest true
      else (is_goto, ts)
  | _ => (is_goto, ts)
  end.

Fixpoint parse_asm_clobbers (fuel : nat) (ts : list token)
  (acc : list c_asm_clobber) : list c_asm_clobber * list token :=
  match fuel with
  | O => (rev_append acc [], ts)
  | S f =>
      match parse_string_bytes ts with
      | POk bs rest =>
          let c := ACName (string_of_bytes bs) in
          match match_punct_tok "," rest with
          | Some rest' => parse_asm_clobbers f rest' (c :: acc)
          | None => (rev_append (c :: acc) [], rest)
          end
      | _ => (rev_append acc [], ts)
      end
  end.

Fixpoint parse_asm_labels (fuel : nat) (ts : list token) (acc : list string)
  : list string * list token :=
  match fuel with
  | O => (rev_append acc [], ts)
  | S f =>
      match ts with
      | mkTok (TId l) _ :: rest =>
          match match_punct_tok "," rest with
          | Some rest' => parse_asm_labels f rest' (l :: acc)
          | None => (rev_append (l :: acc) [], rest)
          end
      | _ => (rev_append acc [], ts)
      end
  end.


(** ## Modular grammar over open recursion

    Factoring the grammar into small, independent definitions inside a section
    parameterized by the seven cycle-breaking nonterminals keeps every local
    definition fast to check. A single seven-way fixpoint at the bottom ties
    the recursive knot with explicit [{struct fuel}] annotations. *)

Section Grammar.
  Variable p_decl_specs : c_env -> list token -> pres (list c_spec).
  Variable p_type_name : c_env -> list token -> pres c_type_name.
  Variable p_expr : c_env -> list token -> pres c_expr.
  Variable p_assignment : c_env -> list token -> pres c_expr.
  Variable p_conditional : c_env -> list token -> pres c_expr.
  Variable p_block : c_env -> list token -> pres c_stmt.
  Variable p_stmt : c_env -> list token -> pres c_stmt.

  Fixpoint parse_knr_names_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list string) {struct fuel} : pres (list string) :=
    match fuel with
    | O => PFail
    | S f =>
        if starts_type env ts then PFail
        else
          match ts with
          | mkTok (TId n) _ :: rest =>
              match match_punct_tok "," rest with
              | Some r1 => parse_knr_names_g f env r1 (n :: acc)
              | None => POk (rev_append (n :: acc) []) rest
              end
          | _ => PFail
          end
    end.

  Fixpoint parse_designators_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_designator) {struct fuel} : pres (list c_designator) :=
    match fuel with
    | O => POk (rev_append acc []) ts
    | S f =>
        match ts with
        | mkTok (TPunct p) _ :: rest =>
            if String.eqb p "." then
              match rest with
              | mkTok (TId nm) _ :: rest2 =>
                  parse_designators_g f env rest2 (DField nm :: acc)
              | _ => POk (rev_append acc []) ts
              end
            else if String.eqb p "[" then
              p_bind (p_conditional env rest) (fun e r1 =>
                match match_punct_tok "..." r1 with
                | Some r2 =>
                    p_bind (p_conditional env r2) (fun hi r3 =>
                      p_bind (expect_punct "]" r3) (fun _ r4 =>
                        parse_designators_g f env r4 (DRange e hi :: acc)))
                | None =>
                    p_bind (expect_punct "]" r1) (fun _ r2 =>
                      parse_designators_g f env r2 (DIndex e :: acc))
                end)
            else POk (rev_append acc []) ts
        | _ => POk (rev_append acc []) ts
        end
    end.

  Fixpoint parse_offsetof_path_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_designator) {struct fuel} : pres (list c_designator) :=
    match fuel with
    | O => POk (rev_append acc []) ts
    | S f =>
        match ts with
        | mkTok (TPunct p) _ :: r1 =>
            if String.eqb p "." then
              match r1 with
              | mkTok (TId fld) _ :: r2 =>
                  parse_offsetof_path_g f env r2 (DField fld :: acc)
              | _ => parse_err "expected a member name" r1
              end
            else if String.eqb p "[" then
              p_bind (p_expr env r1) (fun idx r2 =>
                p_bind (expect_punct "]" r2) (fun _ r3 =>
                  parse_offsetof_path_g f env r3 (DIndex idx :: acc)))
            else POk (rev_append acc []) ts
        | _ => POk (rev_append acc []) ts
        end
    end.

  Fixpoint parse_args_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_expr) {struct fuel} : pres (list c_expr) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match match_punct_tok ")" ts with
        | Some r1 => POk (rev_append acc []) r1
        | None =>
            p_bind (p_assignment env ts) (fun a r1 =>
              match match_punct_tok "," r1 with
              | Some r2 => parse_args_g f env r2 (a :: acc)
              | None =>
                  p_bind (expect_punct ")" r1) (fun _ r2 =>
                    POk (rev_append (a :: acc) []) r2)
              end)
        end
    end.

  Fixpoint parse_postfix_g (fuel : nat) (env : c_env) (a : c_expr)
    (ts : list token) {struct fuel} : pres c_expr :=
    match fuel with
    | O => POk a ts
    | S f =>
        match ts with
        | mkTok (TPunct p) _ :: r1 =>
            if String.eqb p "[" then
              p_bind (p_expr env r1) (fun idx r2 =>
                p_bind (expect_punct "]" r2) (fun _ r3 =>
                  parse_postfix_g f env (EIndex a idx) r3))
            else if String.eqb p "(" then
              p_bind (parse_args_g f env r1 []) (fun args r2 =>
                parse_postfix_g f env (ECall a args) r2)
            else if String.eqb p "." then
              match r1 with
              | mkTok (TId fld) _ :: r2 => parse_postfix_g f env (EMember a fld) r2
              | _ => parse_err "expected a member name" r1
              end
            else if String.eqb p "->" then
              match r1 with
              | mkTok (TId fld) _ :: r2 => parse_postfix_g f env (EArrow a fld) r2
              | _ => parse_err "expected a member name" r1
              end
            else if String.eqb p "++" then
              parse_postfix_g f env (EUn UPostInc a) r1
            else if String.eqb p "--" then
              parse_postfix_g f env (EUn UPostDec a) r1
            else POk a ts
        | _ => POk a ts
        end
    end.

  Fixpoint parse_generic_assocs_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_generic_assoc) {struct fuel} : pres (list c_generic_assoc) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let one :=
          match match_kw_tok "default" ts with
          | Some r1 =>
              p_bind (expect_punct ":" r1) (fun _ r2 =>
                p_bind (p_assignment env r2) (fun e r3 =>
                  POk (GAssocDefault e) r3))
          | None =>
              p_bind (p_type_name env ts) (fun tn r1 =>
                p_bind (expect_punct ":" r1) (fun _ r2 =>
                  p_bind (p_assignment env r2) (fun e r3 =>
                    POk (GAssocType tn e) r3)))
          end in
        p_bind one (fun ga r1 =>
          match match_punct_tok "," r1 with
          | Some r2 => parse_generic_assocs_g f env r2 (ga :: acc)
          | None => POk (rev_append (ga :: acc) []) r1
          end)
    end.

  Definition parse_primary_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_expr :=
    match ts with
    | mkTok (TId n) _ :: r1 =>
        if String.eqb n "__builtin_offsetof" then
          p_bind (expect_punct "(" r1) (fun _ r2 =>
            p_bind (p_type_name env r2) (fun tn r3 =>
              p_bind (expect_punct "," r3) (fun _ r4 =>
                match r4 with
                | mkTok (TId fld) _ :: r5 =>
                    p_bind (parse_offsetof_path_g fuel env r5 []) (fun steps r6 =>
                      p_bind (expect_punct ")" r6) (fun _ r7 =>
                        POk (EOffsetof tn (DField fld :: steps)) r7))
                | _ => parse_err "expected a member name" r4
                end)))
        else if String.eqb n "__builtin_va_arg" then
          p_bind (expect_punct "(" r1) (fun _ r2 =>
            p_bind (p_assignment env r2) (fun a r3 =>
              p_bind (expect_punct "," r3) (fun _ r4 =>
                p_bind (p_type_name env r4) (fun tn r5 =>
                  p_bind (expect_punct ")" r5) (fun _ r6 =>
                    POk (EVaArg a tn) r6)))))
        else if String.eqb n "__builtin_bit_cast" then
          p_bind (expect_punct "(" r1) (fun _ r2 =>
            p_bind (p_type_name env r2) (fun tn r3 =>
              p_bind (expect_punct "," r3) (fun _ r4 =>
                p_bind (p_assignment env r4) (fun e r5 =>
                  p_bind (expect_punct ")" r5) (fun _ r6 =>
                    POk (EBitCast tn e) r6)))))
        else if String.eqb n "__builtin_convertvector" then
          p_bind (expect_punct "(" r1) (fun _ r2 =>
            p_bind (p_assignment env r2) (fun a r3 =>
              p_bind (expect_punct "," r3) (fun _ r4 =>
                p_bind (p_type_name env r4) (fun tn r5 =>
                  p_bind (expect_punct ")" r5) (fun _ r6 =>
                    POk (EConvertVector a tn) r6)))))
        else if String.eqb n "__builtin_types_compatible_p" then
          p_bind (expect_punct "(" r1) (fun _ r2 =>
            p_bind (p_type_name env r2) (fun a r3 =>
              p_bind (expect_punct "," r3) (fun _ r4 =>
                p_bind (p_type_name env r4) (fun b r5 =>
                  p_bind (expect_punct ")" r5) (fun _ r6 =>
                    POk (ETypesCompatible a b) r6)))))
        else POk (EId n) r1
    | mkTok (TKw w) _ :: r1 =>
        if String.eqb w "true" then
          POk (ECast (TypeName [SpTspec "bool"] DTBase) (ENum 1 SufNone RadDec)) r1
        else if String.eqb w "false" then
          POk (ECast (TypeName [SpTspec "bool"] DTBase) (ENum 0 SufNone RadDec)) r1
        else if String.eqb w "nullptr" then
          POk (ECast (TypeName [SpTspec "void"] (DTPtr DTBase []))
                     (ENum 0 SufNone RadDec)) r1
        else if String.eqb w "generic" then
          p_bind (expect_punct "(" r1) (fun _ r2 =>
            p_bind (p_assignment env r2) (fun ctrl r3 =>
              p_bind (expect_punct "," r3) (fun _ r4 =>
                p_bind (parse_generic_assocs_g fuel env r4 []) (fun assocs r5 =>
                  p_bind (expect_punct ")" r5) (fun _ r6 =>
                    POk (EGeneric ctrl assocs) r6)))))
        else parse_err "expected an expression" ts
    | mkTok (TInt v suf rad) _ :: r1 => POk (ENum v suf rad) r1
    | mkTok (TFloat cs) _ :: r1 => POk (EFloat cs) r1
    | mkTok (TImag cs) _ :: r1 => POk (EImag cs) r1
    | mkTok (TChr v) _ :: r1 => POk (EChr v) r1
    | mkTok (TStr _) _ :: _ | mkTok (TWStr _ _) _ :: _ =>
        let '(parts, r1) := collect_str_parts ts [] in
        match combine_str_parts parts with
        | COk e => POk e r1
        | CErr m => PError m
        end
    | mkTok (TPunct p) _ :: r1 =>
        if String.eqb p "(" then
          if is_punct_head "{" r1 then
            p_bind (p_block env r1) (fun blk r2 =>
              p_bind (expect_punct ")" r2) (fun _ r3 =>
                POk (EStmtExpr blk) r3))
          else
            p_bind (p_expr env r1) (fun e r2 =>
              p_bind (expect_punct ")" r2) (fun _ r3 => POk e r3))
        else parse_err "expected an expression" ts
    | _ => parse_err "expected an expression" ts
    end.

  Fixpoint parse_initializer_g (fuel : nat) (env : c_env) (ts : list token)
    {struct fuel} : pres c_init :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match match_punct_tok "{" ts with
        | Some r1 =>
            p_bind (parse_init_entries_g f env r1 []) (fun es r2 =>
              POk (InitList es) r2)
        | None =>
            p_bind (p_assignment env ts) (fun e r1 => POk (InitExpr e) r1)
        end
    end

  with parse_init_entries_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_init_entry) {struct fuel} : pres (list c_init_entry) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match match_punct_tok "}" ts with
        | Some r1 => POk (rev_append acc []) r1
        | None =>
            let parse_std_desigs (_ : unit) :=
              p_bind (parse_designators_g f env ts []) (fun ds r1 =>
                match ds with
                | [] => POk [] ts
                | _ => p_bind (expect_punct "=" r1) (fun _ r2 => POk ds r2)
                end) in
            let desig_step :=
              match ts with
              | mkTok (TId fld) _ :: mkTok (TPunct p) _ :: r1 =>
                  if String.eqb p ":" then POk [DField fld] r1
                  else parse_std_desigs tt
              | _ => parse_std_desigs tt
              end in
            p_bind desig_step (fun ds r1 =>
              p_bind (parse_initializer_g f env r1) (fun ini r2 =>
                let en := InitEntry ds ini in
                match match_punct_tok "," r2 with
                | Some r3 => parse_init_entries_g f env r3 (en :: acc)
                | None =>
                    p_bind (expect_punct "}" r2) (fun _ r3 =>
                      POk (rev_append (en :: acc) []) r3)
                end))
        end
    end.

  Fixpoint parse_cast_g (fuel : nat) (env : c_env) (ts : list token)
    {struct fuel} : pres c_expr :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match match_punct_tok "(" ts with
        | Some r1 =>
            if starts_type env r1 then
              p_bind (p_type_name env r1) (fun tn r2 =>
                p_bind (expect_punct ")" r2) (fun _ r3 =>
                  match match_punct_tok "{" r3 with
                  | Some r4 =>
                      p_bind (parse_init_entries_g f env r4 []) (fun es r5 =>
                        parse_postfix_g f env (EComplit tn es) r5)
                  | None =>
                      p_bind (parse_cast_g f env r3) (fun e0 r4 =>
                        POk (ECast tn e0) r4)
                  end))
            else parse_unary_g f env ts
        | None => parse_unary_g f env ts
        end
    end

  with parse_unary_g (fuel : nat) (env : c_env) (ts : list token)
    {struct fuel} : pres c_expr :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let fallback (_ : unit) :=
          p_bind (parse_primary_g f env ts) (fun p0 r1 =>
            parse_postfix_g f env p0 r1) in
        match ts with
        | mkTok (TPunct p) _ :: r1 =>
            if String.eqb p "++" then
              p_bind (parse_unary_g f env r1) (fun e r2 => POk (EUn UPreInc e) r2)
            else if String.eqb p "--" then
              p_bind (parse_unary_g f env r1) (fun e r2 => POk (EUn UPreDec e) r2)
            else if String.eqb p "&&" then
              match r1 with
              | mkTok (TId l) _ :: r2 => POk (ELabelAddr l) r2
              | _ => parse_err "expected a label after &&" r1
              end
            else
              match lookup_unop p with
              | Some op =>
                  p_bind (parse_cast_g f env r1) (fun e r2 => POk (EUn op e) r2)
              | None => fallback tt
              end
        | mkTok (TKw w) _ :: r1 =>
            if String.eqb w "sizeof" then
              match match_punct_tok "(" r1 with
              | Some r2 =>
                  if starts_type env r2 then
                    p_bind (p_type_name env r2) (fun tn r3 =>
                      p_bind (expect_punct ")" r3) (fun _ r4 =>
                        match match_punct_tok "{" r4 with
                        | Some r5 =>
                            p_bind (parse_init_entries_g f env r5 []) (fun es r6 =>
                              p_bind (parse_postfix_g f env (EComplit tn es) r6) (fun e0 r7 =>
                                POk (ESizeofExpr e0) r7))
                        | None => POk (ESizeofType tn) r4
                        end))
                  else
                    p_bind (parse_unary_g f env r1) (fun e0 r2 => POk (ESizeofExpr e0) r2)
              | None =>
                  p_bind (parse_unary_g f env r1) (fun e0 r2 => POk (ESizeofExpr e0) r2)
              end
            else if String.eqb w "real" then
              p_bind (parse_cast_g f env r1) (fun e r2 => POk (ERealPart e) r2)
            else if String.eqb w "imag" then
              p_bind (parse_cast_g f env r1) (fun e r2 => POk (EImagPart e) r2)
            else if String.eqb w "alignof" then
              match match_punct_tok "(" r1 with
              | Some r2 =>
                  if starts_type env r2 then
                    p_bind (p_type_name env r2) (fun tn r3 =>
                      p_bind (expect_punct ")" r3) (fun _ r4 =>
                        POk (EAlignofType tn) r4))
                  else
                    p_bind (parse_unary_g f env r1) (fun e0 r2 => POk (EAlignofExpr e0) r2)
              | None =>
                  p_bind (parse_unary_g f env r1) (fun e0 r2 => POk (EAlignofExpr e0) r2)
              end
            else if String.eqb w "extension" then parse_cast_g f env r1
            else fallback tt
        | _ => fallback tt
        end
    end.

  Fixpoint parse_bin_rest_g (fuel : nat) (level : nat)
    (sub : list token -> pres c_expr) (lhs : c_expr) (ts : list token)
    {struct fuel} : pres c_expr :=
    match fuel with
    | O => POk lhs ts
    | S f =>
        match ts with
        | mkTok (TPunct p) _ :: r1 =>
            match binop_at_level level p with
            | Some op =>
                p_bind (sub r1) (fun rhs r2 =>
                  parse_bin_rest_g f level sub (EBin op lhs rhs) r2)
            | None => POk lhs ts
            end
        | _ => POk lhs ts
        end
    end.

  Fixpoint parse_binary_levels_g (rem : nat) (fuel : nat) (env : c_env)
    (ts : list token) {struct rem} : pres c_expr :=
    match rem with
    | O => parse_cast_g fuel env ts
    | S rem' =>
        let level := (11 - rem)%nat in
        let sub := parse_binary_levels_g rem' fuel env in
        p_bind (sub ts) (fun lhs r1 =>
          parse_bin_rest_g fuel level sub lhs r1)
    end.

  Definition parse_conditional_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_expr :=
    p_bind (parse_binary_levels_g 10%nat fuel env ts) (fun c r1 =>
      match match_punct_tok "?" r1 with
      | None => POk c r1
      | Some r2 =>
          match match_punct_tok ":" r2 with
          | Some r3 =>
              p_bind (p_conditional env r3) (fun b r4 => POk (EGCond c b) r4)
          | None =>
              p_bind (p_expr env r2) (fun a r3 =>
                p_bind (expect_punct ":" r3) (fun _ r4 =>
                  p_bind (p_conditional env r4) (fun b r5 =>
                    POk (ECond c a b) r5)))
          end
      end).

  Definition parse_assignment_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_expr :=
    p_bind (parse_conditional_g fuel env ts) (fun lhs r1 =>
      match r1 with
      | mkTok (TPunct op) _ :: r2 =>
          if is_assign_op op then
            p_bind (p_assignment env r2) (fun rhs r3 => POk (EAssign op lhs rhs) r3)
          else POk lhs r1
      | _ => POk lhs r1
      end).

  Definition parse_expr_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_expr :=
    p_bind (parse_assignment_g fuel env ts) (fun e0 r1 =>
      match match_punct_tok "," r1 with
      | Some r2 =>
          p_bind (p_expr env r2) (fun e1 r3 => POk (EComma e0 e1) r3)
      | None => POk e0 r1
      end).

  Fixpoint parse_array_size_g (fuel : nat) (env : c_env) (ts : list token)
    {struct fuel} : pres c_array_size :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let as_expr (_ : unit) :=
          p_bind (p_assignment env ts) (fun e r => POk (ASExpr e) r) in
        match ts with
        | mkTok (TPunct p) _ :: r1 =>
            if String.eqb p "]" then POk ASNone ts
            else if String.eqb p "*" then
              match r1 with
              | mkTok (TPunct p2) _ :: rest =>
                  if String.eqb p2 "]" then
                    POk ASStar (mkTok (TPunct "]") (peek_loc ts) :: rest)
                  else as_expr tt
              | _ => as_expr tt
              end
            else as_expr tt
        | mkTok (TKw q) _ :: rest =>
            if String.eqb q "static" || String.eqb q "const" ||
               String.eqb q "volatile" || String.eqb q "restrict"
            then parse_array_size_g f env rest
            else as_expr tt
        | _ => as_expr tt
        end
    end.

  Fixpoint parse_declarator_g (fuel : nat) (env : c_env) (base : c_dcl_type)
    (slid0 : option (list c_spec)) (ts : list token) {struct fuel}
    : pres (string * c_dcl_type * option (list c_spec)) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match match_punct_tok "*" ts with
        | Some r1 =>
            p_bind (parse_qualifiers f slid0 r1 []) (fun '(qs, slid1) r2 =>
              parse_declarator_g f env (DTPtr base qs) slid1 r2)
        | None =>
            p_bind (skip_discarded_attrs f ts) (fun _ r1 =>
              match match_punct_tok "*" r1 with
              | Some r2 =>
                  p_bind (parse_qualifiers f slid0 r2 []) (fun '(qs, slid1) r3 =>
                    parse_declarator_g f env (DTPtr base qs) slid1 r3)
              | None =>
                  match r1 with
                  | mkTok (TId nm) _ :: rest =>
                      p_bind (parse_suffixes_g f env base rest) (fun ty r2 =>
                        POk (nm, ty, slid0) r2)
                  | mkTok (TPunct p) _ :: rest =>
                      if String.eqb p "(" then
                        p_bind (parse_declarator_g f env DTBase slid0 rest)
                          (fun '(nm, inner_ty, slid1) r2 =>
                             p_bind (expect_punct ")" r2) (fun _ r3 =>
                               p_bind (parse_suffixes_g f env base r3) (fun mid r4 =>
                                 POk (nm, subst_dcl_base inner_ty mid, slid1) r4)))
                      else PFail
                  | _ => PFail
                  end
              end)
        end
    end

  with parse_abstract_declarator_g (fuel : nat) (env : c_env)
    (base : c_dcl_type) (ts : list token) {struct fuel} : pres c_dcl_type :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match match_punct_tok "*" ts with
        | Some r1 =>
            p_bind (parse_qualifiers f None r1 []) (fun '(qs, _) r2 =>
              parse_abstract_declarator_g f env (DTPtr base qs) r2)
        | None =>
            match match_punct_tok "(" ts with
            | Some r1 =>
                let try_nested :=
                  p_bind (skip_discarded_attrs f r1) (fun _ r2 =>
                    if is_punct_head "*" r2 || is_punct_head "[" r2 then
                      p_bind (parse_abstract_declarator_g f env DTBase r2) (fun inner_ty r3 =>
                        p_bind (expect_punct ")" r3) (fun _ r4 =>
                          p_bind (parse_suffixes_g f env base r4) (fun mid r5 =>
                            POk (subst_dcl_base inner_ty mid) r5)))
                    else PFail) in
                p_or try_nested (fun _ => parse_suffixes_g f env base ts)
            | None => parse_suffixes_g f env base ts
            end
        end
    end

  with parse_suffixes_g (fuel : nat) (env : c_env) (base : c_dcl_type)
    (ts : list token) {struct fuel} : pres c_dcl_type :=
    match fuel with
    | O => POk base ts
    | S f =>
        match parse_c23_attr f ts with
        | POk _ r1 => parse_suffixes_g f env base r1
        | PError m => PError m
        | PFail =>
            match match_punct_tok "[" ts with
            | Some r1 =>
                p_bind (parse_array_size_g f env r1) (fun sz r2 =>
                  p_bind (expect_punct "]" r2) (fun _ r3 =>
                    p_bind (parse_suffixes_g f env base r3) (fun ty1 r4 =>
                      POk (DTArray ty1 sz) r4)))
            | None =>
                match match_punct_tok "(" ts with
                | Some r1 =>
                    p_bind (parse_params_g f env r1) (fun ps r2 =>
                      p_bind (parse_suffixes_g f env base r2) (fun ty1 r3 =>
                        POk (DTFunc ty1 ps) r3))
                | None => POk base ts
                end
            end
        end
    end

  with parse_params_g (fuel : nat) (env : c_env) (ts : list token)
    {struct fuel} : pres c_params :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let parse_nonempty (_ : unit) :=
          let try_knr :=
            p_bind (parse_knr_names_g f env ts []) (fun ns r1 =>
              match match_punct_tok ")" r1 with
              | Some r2 => POk (PKnr ns) r2
              | None => PFail
              end) in
          p_or try_knr (fun _ =>
            p_bind (parse_param_list_g f env ts []) (fun '(ps, var) r1 =>
              p_bind (expect_punct ")" r1) (fun _ r2 =>
                POk (PParams ps var) r2))) in
        match ts with
        | mkTok (TPunct p) _ :: rest =>
            if String.eqb p ")" then POk PUnspecified rest
            else parse_nonempty tt
        | mkTok (TKw w) _ :: mkTok (TPunct p) _ :: rest =>
            if String.eqb w "void" && String.eqb p ")" then
              POk (PParams [] false) rest
            else parse_nonempty tt
        | _ => parse_nonempty tt
        end
    end

  with parse_param_list_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_param) {struct fuel} : pres (list c_param * bool) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match match_punct_tok "..." ts with
        | Some r1 => POk (rev_append acc [], true) r1
        | None =>
            match p_decl_specs env ts with
            | POk sps r1 =>
                let dcl_step :=
                  p_or
                    (p_bind (parse_declarator_g f env DTBase None r1) (fun '(nm, ty, _) r2 =>
                       POk (Dcl (Some nm) ty None) r2))
                    (fun _ =>
                       p_bind (parse_abstract_declarator_g f env DTBase r1) (fun ty r2 =>
                         POk (Dcl None ty None) r2)) in
                p_bind dcl_step (fun dcl r2 =>
                  p_bind (skip_discarded_attrs f r2) (fun _ r3 =>
                    let p := Param sps dcl in
                    match match_punct_tok "," r3 with
                    | Some r4 => parse_param_list_g f env r4 (p :: acc)
                    | None => POk (rev_append (p :: acc) [], false) r3
                    end))
            | PError m => PError m
            | PFail =>
                match ts with
                | mkTok (TId _) _ :: _ =>
                    parse_err "K&R-style parameter lists are not supported" ts
                | _ => parse_err "expected a parameter declaration" ts
                end
            end
        end
    end.

  Definition parse_full_declarator_g (fuel : nat) (env : c_env)
    (slid0 : option (list c_spec)) (ts : list token)
    : pres (c_dcl * list c_spec) :=
    p_bind (parse_attr_list fuel ts []) (fun pre0 r1 =>
      p_bind (parse_declarator_g fuel env DTBase slid0 r1) (fun '(nm, ty, slid1) r2 =>
        p_bind (parse_gnu_suffix fuel r2) (fun '(asym, ats1) r3 =>
          let pre := map SpAttr pre0 in
          let s_ats := match slid1 with Some xs => xs | None => [] end in
          POk (Dcl (Some nm) ty asym, app pre (app s_ats ats1)) r3))).

  Fixpoint parse_init_declarators_g (fuel : nat) (env : c_env) (dcl : c_dcl)
    (ats0 : list c_spec) (ts : list token) (acc : list c_init_decl)
    {struct fuel} : pres (list c_init_decl * list c_spec) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let init_step :=
          match match_punct_tok "=" ts with
          | Some r1 =>
              p_bind (parse_initializer_g f env r1) (fun ini r2 => POk (Some ini) r2)
          | None => POk None ts
          end in
        p_bind init_step (fun oini r1 =>
          let loc := peek_loc r1 in
          let acc1 := InitDecl dcl oini :: acc in
          match match_punct_tok "," r1 with
          | Some r2 =>
              p_bind (parse_full_declarator_g f env (Some []) r2) (fun '(dcl1, ats1) r3 =>
                let ats2 := app ats0 ats1 in
                match check_one_decl_attrs ats2 loc with
                | COk tt => parse_init_declarators_g f env dcl1 ats2 r3 acc1
                | CErr m => PError m
                end)
          | None => POk (rev_append acc1 [], ats0) r1
          end)
    end.

  Fixpoint parse_field_decls_g (fuel : nat) (env : c_env) (sps mark : list c_spec)
    (ts : list token) (acc : list c_member) {struct fuel}
    : pres (list c_member) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let one :=
          match match_punct_tok ":" ts with
          | Some r1 =>
              p_bind (p_conditional env r1) (fun w r2 =>
                POk (Dcl None DTBase None, [], Some w) r2)
          | None =>
              p_bind (parse_full_declarator_g f env None ts) (fun '(dcl, ats) r1 =>
                match match_punct_tok ":" r1 with
                | Some r2 =>
                    p_bind (p_conditional env r2) (fun w r3 =>
                      POk (dcl, ats, Some w) r3)
                | None => POk (dcl, ats, None) r1
                end)
          end in
        p_bind one (fun '(dcl, ats, ow) r1 =>
          p_bind (parse_attr_list f r1 []) (fun ats1 r2 =>
            let fsps := app mark (app sps (app ats (map SpAttr ats1))) in
            let fld := MField fsps dcl ow in
            match match_punct_tok "," r2 with
            | Some r3 => parse_field_decls_g f env sps [SpSharedBase] r3 (fld :: acc)
            | None => POk (rev_append (fld :: acc) []) r2
            end))
    end.

  Fixpoint parse_members_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_member) {struct fuel} : pres (list c_member) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let parse_member_decl (_ : unit) :=
          match p_decl_specs env ts with
          | POk sps r1 =>
              match match_punct_tok ";" r1 with
              | Some r2 =>
                  parse_members_g f env r2 (MField sps (Dcl None DTBase None) None :: acc)
              | None =>
                  p_bind (parse_field_decls_g f env sps [] r1 []) (fun fs r2 =>
                    p_bind (expect_punct ";" r2) (fun _ r3 =>
                      parse_members_g f env r3 (rev_append fs acc)))
              end
          | PError m => PError m
          | PFail => parse_err "expected a member declaration" ts
          end in
        match ts with
        | mkTok (TPunct p) _ :: rest =>
            if String.eqb p "}" then POk (rev_append acc []) rest
            else if String.eqb p ";" then parse_members_g f env rest acc
            else parse_member_decl tt
        | mkTok (TKw w) loc :: rest =>
            if String.eqb w "static_assert" then
              p_bind (expect_punct "(" rest) (fun _ r1 =>
                p_bind (p_conditional env r1) (fun e r2 =>
                  let msg_step :=
                    match match_punct_tok "," r2 with
                    | Some r3 => parse_string_bytes r3
                    | None => POk [] r2
                    end in
                  p_bind msg_step (fun msg r3 =>
                    p_bind (expect_punct ")" r3) (fun _ r4 =>
                      p_bind (expect_punct ";" r4) (fun _ r5 =>
                        parse_members_g f env r5 (MStaticAssert loc e msg :: acc))))))
            else parse_member_decl tt
        | _ => parse_member_decl tt
        end
    end.

  Fixpoint parse_enumerators_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_enumerator) {struct fuel} : pres (list c_enumerator) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match ts with
        | mkTok (TPunct p) _ :: rest =>
            if String.eqb p "}" then POk (rev_append acc []) rest
            else parse_err "expected an enumerator" ts
        | mkTok (TId nm) _ :: rest =>
            p_bind (skip_discarded_attrs f rest) (fun _ r1 =>
              let val_step :=
                match match_punct_tok "=" r1 with
                | Some r2 =>
                    p_bind (p_conditional env r2) (fun v r3 => POk (Some v) r3)
                | None => POk None r1
                end in
              p_bind val_step (fun ov r2 =>
                let en := Enumerator nm ov in
                match match_punct_tok "," r2 with
                | Some r3 => parse_enumerators_g f env r3 (en :: acc)
                | None =>
                    p_bind (expect_punct "}" r2) (fun _ r3 =>
                      POk (rev_append (en :: acc) []) r3)
                end))
        | _ => parse_err "expected an enumerator" ts
        end
    end.

  Definition parse_struct_spec_g (fuel : nat) (env : c_env) (kind : su_kind)
    (ts : list token) : pres c_spec :=
    p_bind (parse_attr_list fuel ts []) (fun a0 r1 =>
      let '(tag, r2) :=
        match r1 with
        | mkTok (TId t) _ :: r' => (Some t, r')
        | _ => (None, r1)
        end in
      match match_punct_tok "{" r2 with
      | Some r3 =>
          p_bind (parse_members_g fuel env r3 []) (fun ms r4 =>
            p_bind (parse_attr_list fuel r4 []) (fun a1 r5 =>
              POk (SpSu kind tag (Some ms) (app a0 a1)) r5))
      | None =>
          match tag with
          | Some _ => POk (SpSu kind tag None a0) r2
          | None => PFail
          end
      end).

  Definition parse_enum_spec_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_spec :=
    p_bind (parse_enum_attrs fuel false ts) (fun p0 r1 =>
      let '(tag, r2) :=
        match r1 with
        | mkTok (TId t) _ :: r' => (Some t, r')
        | _ => (None, r1)
        end in
      match match_punct_tok "{" r2 with
      | Some r3 =>
          p_bind (parse_enumerators_g fuel env r3 []) (fun es r4 =>
            p_bind (parse_enum_attrs fuel p0 r4) (fun p1 r5 =>
              POk (SpEnum tag (if p1 then EnumPacked es else EnumList es)) r5))
      | None =>
          match tag with
          | Some _ =>
              p_bind (skip_discarded_attrs fuel r2) (fun _ r3 =>
                POk (SpEnum tag EnumNone) r3)
          | None => PFail
          end
      end).

  Definition parse_specifier_g (fuel : nat) (env : c_env) (type_seen : bool)
    (ts : list token) : pres c_spec :=
    match ts with
    | mkTok (TKw w) _ :: rest =>
        if is_storage_kw w then POk (SpStorage w) rest
        else if is_tspec_kw w then POk (SpTspec w) rest
        else if String.eqb w "atomic" then
          match match_punct_tok "(" rest with
          | Some r1 =>
              p_bind (p_type_name env r1) (fun tn r2 =>
                p_bind (expect_punct ")" r2) (fun _ r3 => POk (SpAtomic tn) r3))
          | None => POk (SpQual "atomic") rest
          end
        else if is_qual_kw w then POk (SpQual w) rest
        else if is_fspec_kw w then POk (SpFspec w) rest
        else if String.eqb w "attribute" then
          p_bind (parse_gnu_attr fuel ts) (fun a r => POk (SpAttr a) r)
        else if String.eqb w "extension" then POk (SpAttrTag "extension") rest
        else if String.eqb w "alignas" then
          p_bind (expect_punct "(" rest) (fun _ r1 =>
            let body :=
              p_or
                (p_bind (p_type_name env r1) (fun tn r2 => POk (SpAlignasType tn) r2))
                (fun _ =>
                   p_bind (p_conditional env r1) (fun e r2 => POk (SpAlignasExpr e) r2)) in
            p_bind body (fun sp r2 =>
              p_bind (expect_punct ")" r2) (fun _ r3 => POk sp r3)))
        else if String.eqb w "struct" then parse_struct_spec_g fuel env KStruct rest
        else if String.eqb w "union" then parse_struct_spec_g fuel env KUnion rest
        else if String.eqb w "enum" then parse_enum_spec_g fuel env rest
        else if String.eqb w "auto_type" then POk SpAutoType rest
        else if String.eqb w "typeof" then
          p_bind (expect_punct "(" rest) (fun _ r1 =>
            let body :=
              if starts_type env r1 then
                p_or
                  (p_bind (p_type_name env r1) (fun tn r2 => POk (SpTypeofType tn) r2))
                  (fun _ =>
                     p_bind (p_expr env r1) (fun e r2 => POk (SpTypeofExpr e) r2))
              else
                p_bind (p_expr env r1) (fun e r2 => POk (SpTypeofExpr e) r2) in
            p_bind body (fun sp r2 =>
              p_bind (expect_punct ")" r2) (fun _ r3 => POk sp r3)))
        else PFail
    | mkTok (TId n) _ :: rest =>
        if String.eqb n "__declspec" then
          p_bind (parse_gnu_attr fuel ts) (fun a r => POk (SpAttr a) r)
        else if is_nullability n then POk (SpAttrTag "nullability") rest
        else if negb type_seen && env_mem n env then POk (SpTname n) rest
        else PFail
    | mkTok (TPunct p1) _ :: mkTok (TPunct p2) _ :: _ =>
        if String.eqb p1 "[" && String.eqb p2 "[" then
          p_bind (parse_c23_attr fuel ts) (fun _ r => POk (SpAttrTag "c23") r)
        else PFail
    | _ => PFail
    end.

  Fixpoint parse_specifiers_g (fuel : nat) (env : c_env) (type_seen : bool)
    (ts : list token) (acc : list c_spec) {struct fuel} : pres (list c_spec) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match parse_specifier_g f env type_seen ts with
        | POk sp rest =>
            let ts1 := type_seen || spec_sets_type sp in
            parse_specifiers_g f env ts1 rest (sp :: acc)
        | PError m => PError m
        | PFail => POk (rev_append acc []) ts
        end
    end.

  Definition parse_decl_specs_g (fuel : nat) (env : c_env) (ts : list token)
    : pres (list c_spec) :=
    p_bind (parse_specifiers_g fuel env false ts []) (fun sps rest =>
      match sps with
      | [] => PFail
      | _ => POk sps rest
      end).

  Definition parse_type_name_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_type_name :=
    p_bind (parse_decl_specs_g fuel env ts) (fun sps r1 =>
      p_bind (parse_abstract_declarator_g fuel env DTBase r1) (fun ty r2 =>
        POk (TypeName sps ty) r2)).

  Definition parse_static_assert_rest_g (env : c_env) (loc : c_loc)
    (ts : list token) : pres c_item :=
    p_bind (expect_punct "(" ts) (fun _ r1 =>
      p_bind (p_conditional env r1) (fun e r2 =>
        let msg_step :=
          match match_punct_tok "," r2 with
          | Some r3 => parse_string_bytes r3
          | None => POk [] r2
          end in
        p_bind msg_step (fun msg r3 =>
          p_bind (expect_punct ")" r3) (fun _ r4 =>
            p_bind (expect_punct ";" r4) (fun _ r5 =>
              POk (IStaticAssert loc e msg) r5))))).

  Definition parse_local_decl_g (fuel : nat) (env : c_env) (ts : list token)
    : pres (c_item * c_env) :=
    let loc := peek_loc ts in
    p_bind (p_decl_specs env ts) (fun sps r1 =>
      let body :=
        match match_punct_tok ";" r1 with
        | Some r2 => POk ([], []) r2
        | None =>
            p_bind (parse_full_declarator_g fuel env (Some []) r1) (fun '(dcl, ats0) r2 =>
              p_bind (parse_init_declarators_g fuel env dcl ats0 r2 []) (fun '(inits, ats) r3 =>
                p_bind (expect_punct ";" r3) (fun _ r4 => POk (inits, ats) r4)))
        end in
      p_bind body (fun '(inits, ats) r2 =>
        match apply_auto_type sps inits loc with
        | CErr m => PError m
        | COk sps_a =>
            let env1 := update_decl_env sps_a inits env in
            POk (IDecl loc (app sps_a ats) inits, env1) r2
        end)).

  Definition parse_opt_expr_g (env : c_env) (ts : list token)
    : pres (option c_expr) :=
    if is_punct_head ";" ts || is_punct_head ")" ts then POk None ts
    else p_bind (p_expr env ts) (fun e r => POk (Some e) r).

  Fixpoint parse_asm_ops_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_asm_op) {struct fuel} : pres (list c_asm_op) :=
    match fuel with
    | O => POk (rev_append acc []) ts
    | S f =>
        let after_name :=
          match match_punct_tok "[" ts with
          | Some (mkTok (TId _) _ :: r1) =>
              match expect_punct "]" r1 with
              | POk _ r2 => Some r2
              | _ => None
              end
          | Some _ => None
          | None => Some ts
          end in
        match after_name with
        | None => POk (rev_append acc []) ts
        | Some r1 =>
            match parse_string_bytes r1 with
            | POk bs r2 =>
                p_bind (expect_punct "(" r2) (fun _ r3 =>
                  p_bind (p_expr env r3) (fun e r4 =>
                    p_bind (expect_punct ")" r4) (fun _ r5 =>
                      let op := AsmOp (string_of_bytes bs) e in
                      match match_punct_tok "," r5 with
                      | Some r6 =>
                          p_bind (parse_asm_ops_g f env r6 []) (fun more r7 =>
                            match more with
                            | [] => PFail
                            | _ => POk (rev_append (op :: acc) more) r7
                            end)
                      | None => POk (rev_append (op :: acc) []) r5
                      end)))
            | _ => POk (rev_append acc []) ts
            end
        end
    end.

  Definition parse_asm_sections_g (fuel : nat) (env : c_env) (ts : list token)
    : pres (list c_asm_op * list c_asm_op * list c_asm_clobber) :=
    match match_punct_tok ":" ts with
    | None => POk ([], [], []) ts
    | Some r1 =>
        p_bind (parse_asm_ops_g fuel env r1 []) (fun outs r2 =>
          match match_punct_tok ":" r2 with
          | None => POk (outs, [], []) r2
          | Some r3 =>
              p_bind (parse_asm_ops_g fuel env r3 []) (fun ins r4 =>
                match match_punct_tok ":" r4 with
                | None => POk (outs, ins, []) r4
                | Some r5 =>
                    let '(cs, r6) := parse_asm_clobbers fuel r5 [] in
                    match match_punct_tok ":" r6 with
                    | None => POk (outs, ins, cs) r6
                    | Some r7 =>
                        let '(ls, r8) := parse_asm_labels fuel r7 [] in
                        POk (outs, ins, app cs [ACLabels ls]) r8
                    end
                end)
          end)
    end.

  Definition parse_stmt_body_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_stmt_body :=
    let expr_stmt (_ : unit) :=
      p_bind (p_expr env ts) (fun e r1 =>
        p_bind (expect_punct ";" r1) (fun _ r2 => POk (SExpr e) r2)) in
    match ts with
    | mkTok (TPunct p) _ :: rest =>
        if String.eqb p "{" then
          p_bind (p_block env ts) (fun st r =>
            match st with Stmt _ sb => POk sb r end)
        else if String.eqb p ";" then POk SNull rest
        else expr_stmt tt
    | mkTok (TKw w) _ :: rest =>
        if String.eqb w "if" then
          p_bind (expect_punct "(" rest) (fun _ r1 =>
            p_bind (p_expr env r1) (fun c r2 =>
              p_bind (expect_punct ")" r2) (fun _ r3 =>
                p_bind (p_stmt env r3) (fun thn r4 =>
                  match match_kw_tok "else" r4 with
                  | Some r5 =>
                      p_bind (p_stmt env r5) (fun els r6 =>
                        POk (SIf c thn (Some els)) r6)
                  | None => POk (SIf c thn None) r4
                  end))))
        else if String.eqb w "while" then
          p_bind (expect_punct "(" rest) (fun _ r1 =>
            p_bind (p_expr env r1) (fun c r2 =>
              p_bind (expect_punct ")" r2) (fun _ r3 =>
                p_bind (p_stmt env r3) (fun body r4 =>
                  POk (SWhile c body) r4))))
        else if String.eqb w "do" then
          p_bind (p_stmt env rest) (fun body r1 =>
            match match_kw_tok "while" r1 with
            | None => parse_err "expected while" r1
            | Some r2 =>
                p_bind (expect_punct "(" r2) (fun _ r3 =>
                  p_bind (p_expr env r3) (fun c r4 =>
                    p_bind (expect_punct ")" r4) (fun _ r5 =>
                      p_bind (expect_punct ";" r5) (fun _ r6 =>
                        POk (SDo body c) r6))))
            end)
        else if String.eqb w "for" then
          p_bind (expect_punct "(" rest) (fun _ r1 =>
            let init_step :=
              if starts_decl fuel env r1 then
                p_bind (parse_local_decl_g fuel env r1) (fun '(it, env1) r2 =>
                  POk (FIDecl it, env1) r2)
              else
                p_bind (parse_opt_expr_g env r1) (fun oe r2 =>
                  p_bind (expect_punct ";" r2) (fun _ r3 =>
                    let fi := match oe with None => FINone | Some e => FIExpr e end in
                    POk (fi, env) r3)) in
            p_bind init_step (fun '(fi, env1) r2 =>
              p_bind (parse_opt_expr_g env1 r2) (fun oc r3 =>
                p_bind (expect_punct ";" r3) (fun _ r4 =>
                  p_bind (parse_opt_expr_g env1 r4) (fun ostep r5 =>
                    p_bind (expect_punct ")" r5) (fun _ r6 =>
                      p_bind (p_stmt env1 r6) (fun body r7 =>
                        POk (SFor fi oc ostep body) r7)))))))
        else if String.eqb w "switch" then
          p_bind (expect_punct "(" rest) (fun _ r1 =>
            p_bind (p_expr env r1) (fun c r2 =>
              p_bind (expect_punct ")" r2) (fun _ r3 =>
                p_bind (p_stmt env r3) (fun body r4 =>
                  POk (SSwitch c body) r4))))
        else if String.eqb w "case" then
          p_bind (p_conditional env rest) (fun e0 r1 =>
            match match_punct_tok "..." r1 with
            | Some r2 =>
                p_bind (p_conditional env r2) (fun hi r3 =>
                  p_bind (expect_punct ":" r3) (fun _ r4 =>
                    p_bind (p_stmt env r4) (fun body r5 =>
                      POk (SCaseRange e0 hi body) r5)))
            | None =>
                p_bind (expect_punct ":" r1) (fun _ r2 =>
                  p_bind (p_stmt env r2) (fun body r3 =>
                    POk (SCase e0 body) r3))
            end)
        else if String.eqb w "default" then
          p_bind (expect_punct ":" rest) (fun _ r1 =>
            p_bind (p_stmt env r1) (fun body r2 => POk (SDefault body) r2))
        else if String.eqb w "break" then
          p_bind (expect_punct ";" rest) (fun _ r1 => POk SBreak r1)
        else if String.eqb w "continue" then
          p_bind (expect_punct ";" rest) (fun _ r1 => POk SContinue r1)
        else if String.eqb w "return" then
          p_bind (parse_opt_expr_g env rest) (fun oe r1 =>
            p_bind (expect_punct ";" r1) (fun _ r2 => POk (SReturn oe) r2))
        else if String.eqb w "goto" then
          let tgt :=
            match rest with
            | mkTok (TId l) _ :: r1 => POk (SGoto l) r1
            | mkTok (TPunct p) _ :: r1 =>
                if String.eqb p "*" then
                  p_bind (p_expr env r1) (fun e r2 => POk (SComputedGoto e) r2)
                else parse_err "expected a label after goto" rest
            | _ => parse_err "expected a label after goto" rest
            end in
          p_bind tgt (fun sb r1 =>
            p_bind (expect_punct ";" r1) (fun _ r2 => POk sb r2))
        else if String.eqb w "asm" then
          let '(is_goto, r1) := parse_asm_qualifiers rest false in
          match match_punct_tok "(" r1 with
          | None => parse_err "expected asm operands in parentheses" r1
          | Some r2 =>
              let try_structured :=
                p_bind (parse_string_bytes r2) (fun tpl r3 =>
                  p_bind (parse_asm_sections_g fuel env r3) (fun '(outs, ins, clobs) r4 =>
                    match match_punct_tok ")" r4 with
                    | Some r5 =>
                        if is_blank_asm tpl then
                          POk (SAsmEmpty outs ins clobs is_goto) r5
                        else
                          POk (SAsm tpl outs ins clobs is_goto) r5
                    | None => PFail
                    end)) in
              let body :=
                match try_structured with
                | POk sb r5 => POk sb r5
                | _ =>
                    p_bind (parse_balanced fuel r2 []) (fun toks r5 =>
                      POk (SUnsupportedAsm (classify_asm_kind toks)) r5)
                end in
              p_bind body (fun sb r5 =>
                p_bind (expect_punct ";" r5) (fun _ r6 => POk sb r6))
          end
        else expr_stmt tt
    | mkTok (TId lbl) _ :: mkTok (TPunct p) _ :: rest =>
        if String.eqb p ":" then
          p_bind (skip_discarded_attrs fuel rest) (fun _ r1 =>
            p_bind (p_stmt env r1) (fun body r2 => POk (SLabel lbl body) r2))
        else expr_stmt tt
    | _ => expr_stmt tt
    end.

  Definition parse_stmt_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_stmt :=
    let loc := peek_loc ts in
    p_bind (skip_discarded_attrs fuel ts) (fun _ r1 =>
      match parse_stmt_body_g fuel env r1 with
      | POk sb r2 => POk (Stmt loc sb) r2
      | PError m => PError m
      | PFail => parse_err "expected a statement" r1
      end).

  Fixpoint parse_block_item_g (fuel : nat) (env : c_env) (ts : list token)
    {struct fuel} : pres (c_block_item * c_env) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let loc := peek_loc ts in
        match match_kw_tok "static_assert" ts with
        | Some r1 =>
            p_bind (parse_static_assert_rest_g env loc r1) (fun it r2 =>
              POk (BIDecl it, env) r2)
        | None =>
            if is_extension_decl f env ts then
              match ts with
              | _ :: r1 => parse_block_item_g f env r1
              | [] => PFail
              end
            else if starts_decl f env ts then
              p_bind (parse_local_decl_g f env ts) (fun '(it, env1) r1 =>
                POk (BIDecl it, env1) r1)
            else
              p_bind (p_stmt env ts) (fun st r1 => POk (BIStmt st, env) r1)
        end
    end.

  Fixpoint parse_block_items_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_block_item) {struct fuel} : pres (list c_block_item) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        match match_punct_tok "}" ts with
        | Some r1 => POk (rev_append acc []) r1
        | None =>
            p_bind (parse_block_item_g f env ts) (fun '(bi, env1) r1 =>
              parse_block_items_g f env1 r1 (bi :: acc))
        end
    end.

  Definition parse_block_g (fuel : nat) (env : c_env) (ts : list token)
    : pres c_stmt :=
    let loc := peek_loc ts in
    match match_punct_tok "{" ts with
    | None => PFail
    | Some r1 =>
        p_bind (parse_local_labels fuel r1 []) (fun lmap r2 =>
          p_bind (parse_block_items_g fuel env r2 []) (fun bis r3 =>
            let bis' :=
              match lmap with
              | [] => bis
              | _ => map (rename_block_item lmap) bis
              end in
            POk (Stmt loc (SBlock bis')) r3))
    end.

  Fixpoint parse_knr_decls_g (fuel : nat) (env : c_env) (ts : list token)
    (acc : list c_item) {struct fuel} : pres (list c_item) :=
    match fuel with
    | O => POk (rev_append acc []) ts
    | S f =>
        let loc := peek_loc ts in
        match p_decl_specs env ts with
        | POk sps r1 =>
            p_bind (parse_full_declarator_g f env (Some []) r1) (fun '(dcl, ats0) r2 =>
              p_bind (parse_init_declarators_g f env dcl ats0 r2 []) (fun '(inits, ats) r3 =>
                p_bind (expect_punct ";" r3) (fun _ r4 =>
                  parse_knr_decls_g f env r4 (IDecl loc (app sps ats) inits :: acc))))
        | PError m => PError m
        | PFail => POk (rev_append acc []) ts
        end
    end.

  Fixpoint parse_external_decl_g (fuel : nat) (env : c_env) (ts : list token)
    {struct fuel} : pres (option c_item * c_env) :=
    match fuel with
    | O => parse_err "parser fuel exhausted" ts
    | S f =>
        let parse_decl_or_fun (_ : unit) :=
          let loc := peek_loc ts in
          p_bind (p_decl_specs env ts) (fun sps r1 =>
            match match_punct_tok ";" r1 with
            | Some r2 => POk (Some (IDecl loc sps []), env) r2
            | None =>
                p_bind (parse_full_declarator_g f env (Some []) r1) (fun '(dcl, ats0) r2 =>
                  let try_ansi_fundef :=
                    match dcl with
                    | Dcl (Some nm) (DTFunc _ ps) _ =>
                        match ps with
                        | PKnr _ | PKnrDef _ _ => PFail
                        | _ =>
                            if is_punct_head "{" r2 then
                              let env1 := env_remove nm env in
                              let body_env := update_params_env ps env1 in
                              p_bind (p_block body_env r2) (fun body r3 =>
                                POk (Some (IFundef loc (app sps ats0) dcl body), env1) r3)
                            else PFail
                        end
                    | _ => PFail
                    end in
                  p_or try_ansi_fundef (fun _ =>
                    let try_knr_fundef :=
                      match dcl with
                      | Dcl (Some nm) (DTFunc ret (PKnr names)) asym =>
                          p_bind (parse_knr_decls_g f env r2 []) (fun decls r3 =>
                            if is_punct_head "{" r3 then
                              let env1 := env_remove_many (nm :: names) env in
                              let dcl1 := Dcl (Some nm) (DTFunc ret (PKnrDef names decls)) asym in
                              p_bind (p_block env1 r3) (fun body r4 =>
                                POk (Some (IFundef loc (app sps ats0) dcl1 body), env1) r4)
                            else PFail)
                      | _ => PFail
                      end in
                    p_or try_knr_fundef (fun _ =>
                      p_bind (parse_init_declarators_g f env dcl ats0 r2 []) (fun '(inits, ats) r3 =>
                        p_bind (expect_punct ";" r3) (fun _ r4 =>
                          match apply_auto_type sps inits loc with
                          | CErr m => PError m
                          | COk sps_a =>
                              let env1 := update_decl_env sps_a inits env in
                              POk (Some (IDecl loc (app sps_a ats) inits), env1) r4
                          end)))))
            end) in
        match ts with
        | mkTok (TPunct p) _ :: rest =>
            if String.eqb p ";" then POk (None, env) rest
            else parse_decl_or_fun tt
        | mkTok (TKw w) loc :: rest =>
            if String.eqb w "extension" then parse_external_decl_g f env rest
            else if String.eqb w "static_assert" then
              p_bind (parse_static_assert_rest_g env loc rest) (fun it r1 =>
                POk (Some it, env) r1)
            else if String.eqb w "asm" then
              let asm_tpl :=
                match match_punct_tok "(" rest with
                | Some r1 =>
                    p_bind (parse_string_bytes r1) (fun tpl r2 =>
                      match match_punct_tok ")" r2 with
                      | Some r3 => POk tpl r3
                      | None => PFail
                      end)
                | None => PFail
                end in
              match asm_tpl with
              | POk tpl r1 =>
                  p_bind (expect_punct ";" r1) (fun _ r2 =>
                    POk (Some (IToplevelAsm loc tpl), env) r2)
              | _ =>
                  parse_err "expected a string in parentheses after top-level asm" rest
              end
            else parse_decl_or_fun tt
        | mkTok (TPragmaWeak nm tgt) loc :: rest =>
            POk (Some (IPragmaWeak loc nm tgt), env) rest
        | _ => parse_decl_or_fun tt
        end
    end.
End Grammar.

(** ## Guarded recursive knot and entry points

    Each of the seven mutually recursive entry points decrements [fuel] once
    and passes its guarded continuations to the modular step functions above. *)

Fixpoint k_decl_specs (fuel : nat) (env : c_env) (ts : list token) {struct fuel}
  : pres (list c_spec) :=
  match fuel with
  | O => parse_err "parser fuel exhausted" ts
  | S f =>
      parse_decl_specs_g (k_decl_specs f) (k_type_name f) (k_expr f)
        (k_assignment f) (k_conditional f) f env ts
  end

with k_type_name (fuel : nat) (env : c_env) (ts : list token) {struct fuel}
  : pres c_type_name :=
  match fuel with
  | O => parse_err "parser fuel exhausted" ts
  | S f =>
      parse_type_name_g (k_decl_specs f) (k_type_name f) (k_expr f)
        (k_assignment f) (k_conditional f) f env ts
  end

with k_expr (fuel : nat) (env : c_env) (ts : list token) {struct fuel}
  : pres c_expr :=
  match fuel with
  | O => parse_err "parser fuel exhausted" ts
  | S f =>
      parse_expr_g (k_type_name f) (k_expr f) (k_assignment f)
        (k_conditional f) (k_block f) f env ts
  end

with k_assignment (fuel : nat) (env : c_env) (ts : list token) {struct fuel}
  : pres c_expr :=
  match fuel with
  | O => parse_err "parser fuel exhausted" ts
  | S f =>
      parse_assignment_g (k_type_name f) (k_expr f) (k_assignment f)
        (k_conditional f) (k_block f) f env ts
  end

with k_conditional (fuel : nat) (env : c_env) (ts : list token) {struct fuel}
  : pres c_expr :=
  match fuel with
  | O => parse_err "parser fuel exhausted" ts
  | S f =>
      parse_conditional_g (k_type_name f) (k_expr f) (k_assignment f)
        (k_conditional f) (k_block f) f env ts
  end

with k_block (fuel : nat) (env : c_env) (ts : list token) {struct fuel}
  : pres c_stmt :=
  match fuel with
  | O => parse_err "parser fuel exhausted" ts
  | S f =>
      parse_block_g (k_decl_specs f) (k_assignment f) (k_conditional f)
        (k_stmt f) f env ts
  end

with k_stmt (fuel : nat) (env : c_env) (ts : list token) {struct fuel}
  : pres c_stmt :=
  match fuel with
  | O => parse_err "parser fuel exhausted" ts
  | S f =>
      parse_stmt_g (k_decl_specs f) (k_expr f) (k_assignment f)
        (k_conditional f) (k_block f) (k_stmt f) f env ts
  end.

Definition run_external_decl (fuel : nat) (env : c_env) (ts : list token)
  : pres (option c_item * c_env) :=
  parse_external_decl_g (k_decl_specs fuel) (k_assignment fuel)
    (k_conditional fuel) (k_block fuel) fuel env ts.

Fixpoint parse_unit_loop (fuel decl_fuel : nat) (env : c_env)
  (ts : list token) (acc : list c_item) {struct fuel} : c_result (list c_item) :=
  match fuel with
  | O => CErr "unit fuel exhausted"
  | S f =>
      match ts with
      | [] => COk (rev_append acc [])
      | _ =>
          match run_external_decl decl_fuel env ts with
          | POk (None, env1) rest => parse_unit_loop f decl_fuel env1 rest acc
          | POk (Some it, env1) rest => parse_unit_loop f decl_fuel env1 rest (it :: acc)
          | PError m => CErr m
          | PFail => CErr (parse_err_msg "expected a declaration" ts)
          end
      end
  end.

(** Parse a C translation unit from tokens into its list of items. *)
Definition c_parse (ts : list token) : c_result (list c_item) :=
  let n := List.length ts in
  let unit_fuel := S (n + 4) in
  let decl_fuel := S (8 * n + Z.to_nat 256) in
  parse_unit_loop unit_fuel decl_fuel initial_env ts [].

(** Parse a standalone constant expression (as in `#if` or attribute arguments)
    with the given list of names treated as typedefs. *)
Definition c_constant_expression (ts : list token) (typedefs : list string)
  : c_result c_expr :=
  let env := env_add_many typedefs env_empty in
  let fuel := S (8 * List.length ts + Z.to_nat 256) in
  match k_conditional fuel env ts with
  | POk e [] => COk e
  | POk _ rest => CErr (parse_err_msg "expected the end of the expression" rest)
  | PError m => CErr m
  | PFail => CErr "expected an expression"
  end.
