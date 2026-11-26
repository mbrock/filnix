(** The C preprocessor performs translation phases 2 through 4: line splicing,
    preprocessing tokenization, conditional compilation, macro expansion with
    Dave Prosser's hide sets, `#include` resolution, `#line` remapping, and
    `#pragma` handling (`once`, `push_macro`, `pop_macro`, `pack`, `weak`),
    handing the expanded tokens to CLex. This module is a pure Gallina
    translation of nanofil/src/c_pp.pl together with the `#if` constant
    evaluator (`pp_value`) from nanofil/src/c_types.pl.

    File reads, existence checks, canonical paths, and on-demand feature
    queries suspend through the pure [pp_step] resumption type so the same
    Gallina runs under standard OCaml extraction, the λANF Fil-C arena
    runtime, and pure in-memory tests. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith OrderedTypeEx FMapAVL.
From Frontend Require Import CAst CAttrs CLex CParse.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Preprocessing tokens, macros, and environment

    Each preprocessing token carries its spelling (or retained `#pragma`),
    its physical or `#line`-remapped location, whether whitespace preceded
    it, and its hide set of macros that must not expand it again. *)

Inductive pp_tok_val : Type :=
| PPTText (s : string)
| PPTPragmaWeak (name : string) (target : option string)
| PPTPragmaPack (op : pack_op).

Record pp_tok : Type := mkPpTok {
  ppt_val : pp_tok_val;
  ppt_loc : c_loc;
  ppt_space : bool;
  ppt_hide : list string;
}.

Inductive pp_raw : Type :=
| PPRNl
| PPRTok (t : pp_tok).

Inductive macro_param : Type :=
| MPNamed (name : string)
| MPVariadic (name : string).

Inductive macro_def : Type :=
| MObj (body : list pp_tok)
| MFun (params : list macro_param) (body : list pp_tok).

Inductive include_form : Type :=
| IncQuote
| IncAngle.

(** A hash-bucketed map from strings to values, reusing [CParse.ZMap] and
    [CParse.env_string_hash]. *)
Definition smap (A : Type) : Type := CParse.ZMap.t (list (string * A)).

Definition smap_empty {A : Type} : smap A := CParse.ZMap.empty _.

Definition smap_find {A : Type} (name : string) (m : smap A) : option A :=
  match CParse.ZMap.find (CParse.env_string_hash name 0) m with
  | None => None
  | Some bucket => CLex.assoc_str name bucket
  end.

Definition smap_add {A : Type} (name : string) (v : A) (m : smap A) : smap A :=
  let k := CParse.env_string_hash name 0 in
  let bucket :=
    match CParse.ZMap.find k m with
    | Some b => filter (fun p => negb (String.eqb name (fst p))) b
    | None => []
    end in
  CParse.ZMap.add k ((name, v) :: bucket) m.

Definition smap_remove {A : Type} (name : string) (m : smap A) : smap A :=
  let k := CParse.env_string_hash name 0 in
  match CParse.ZMap.find k m with
  | None => m
  | Some bucket =>
      let bucket' := filter (fun p => negb (String.eqb name (fst p))) bucket in
      match bucket' with
      | [] => CParse.ZMap.remove k m
      | _ => CParse.ZMap.add k bucket' m
      end
  end.

(** A feature answer caches the result of a target operator such as
    `__has_attribute(Name)` or `__has_builtin(Name)`. *)
Record feature_entry : Type := mkFeat {
  feat_op : string;
  feat_name : string;
  feat_val : string;
}.

Record pp_env : Type := mkPpEnv {
  pp_macros : smap macro_def;
  pp_saved : smap (list (option macro_def));
  pp_dirs : list string;
  pp_features : list feature_entry;
  pp_once : list string;
  pp_cache : smap (list pp_raw);
  pp_file : string;
}.

Definition set_macros (e : pp_env) (ms : smap macro_def) : pp_env :=
  mkPpEnv ms (pp_saved e) (pp_dirs e) (pp_features e) (pp_once e) (pp_cache e) (pp_file e).

Definition set_macros_saved (e : pp_env) (ms : smap macro_def)
  (sv : smap (list (option macro_def))) : pp_env :=
  mkPpEnv ms sv (pp_dirs e) (pp_features e) (pp_once e) (pp_cache e) (pp_file e).

Definition add_once (e : pp_env) (id : string) : pp_env :=
  mkPpEnv (pp_macros e) (pp_saved e) (pp_dirs e) (pp_features e)
    (if str_in id (pp_once e) then pp_once e else id :: pp_once e)
    (pp_cache e) (pp_file e).

Definition add_feature (e : pp_env) (op nm val : string) : pp_env :=
  mkPpEnv (pp_macros e) (pp_saved e) (pp_dirs e)
    (mkFeat op nm val :: pp_features e)
    (pp_once e) (pp_cache e) (pp_file e).

Definition add_cache (e : pp_env) (path : string) (raw : list pp_raw) : pp_env :=
  mkPpEnv (pp_macros e) (pp_saved e) (pp_dirs e) (pp_features e) (pp_once e)
    (smap_add path raw (pp_cache e)) (pp_file e).

Definition with_file (e : pp_env) (f : string) : pp_env :=
  mkPpEnv (pp_macros e) (pp_saved e) (pp_dirs e) (pp_features e) (pp_once e) (pp_cache e) f.

(** ## Pure I/O resumption monad

    Every filesystem or target-introspection request suspends cleanly so the
    caller supplies the answer without linking I/O into Gallina. *)

Inductive pp_step (A : Type) : Type :=
| PPDone (res : c_result A)
| PPReadFile (path : string) (k : option (list ascii) -> pp_step A)
| PPFileExists (path : string) (k : bool -> pp_step A)
| PPRealPath (path : string) (k : string -> pp_step A)
| PPQueryFeature (op name : string) (k : string -> pp_step A).

Arguments PPDone {A} res.
Arguments PPReadFile {A} path k.
Arguments PPFileExists {A} path k.
Arguments PPRealPath {A} path k.
Arguments PPQueryFeature {A} op name k.

Fixpoint pp_bind {A B : Type} (m : pp_step A) (f : A -> pp_step B) : pp_step B :=
  match m with
  | PPDone (COk v) => f v
  | PPDone (CErr msg) => PPDone (CErr msg)
  | PPReadFile p k => PPReadFile p (fun r => pp_bind (k r) f)
  | PPFileExists p k => PPFileExists p (fun r => pp_bind (k r) f)
  | PPRealPath p k => PPRealPath p (fun r => pp_bind (k r) f)
  | PPQueryFeature op nm k => PPQueryFeature op nm (fun r => pp_bind (k r) f)
  end.

Definition pp_ok {A : Type} (v : A) : pp_step A := PPDone (COk v).

Definition pp_err {A : Type} (l : c_loc) (msg : string) : pp_step A :=
  PPDone (CErr (loc_to_string l ++ ": " ++ msg)).

(** ## Translation phases 2 and 3: splicing and preprocessing tokens

    Backslash-newline splices preserve physical line numbers for every
    surviving character. When a file has no splices, tokens track a single
    line counter without allocating a parallel location list. *)

Fixpoint splice_rest (cs : list ascii) : option (list ascii) :=
  match cs with
  | c :: rest =>
      if Ascii.eqb c "010"%char then Some rest
      else if Ascii.eqb c "013"%char then
        match rest with
        | c2 :: rest2 => if Ascii.eqb c2 "010"%char then Some rest2 else None
        | [] => None
        end
      else if Ascii.eqb c " "%char || Ascii.eqb c "009"%char ||
              Ascii.eqb c "012"%char || Ascii.eqb c "011"%char then
        splice_rest rest
      else None
  | [] => None
  end.

Fixpoint has_splice (cs : list ascii) : bool :=
  match cs with
  | [] => false
  | c :: rest =>
      if Ascii.eqb c "\"%char then
        match splice_rest rest with
        | Some _ => true
        | None => has_splice rest
        end
      else has_splice rest
  end.

Fixpoint located_splice_loop (fuel : nat) (cs : list ascii) (l : c_loc)
  (cs_acc : list ascii) (ls_acc : list c_loc) : list ascii * list c_loc :=
  match fuel with
  | O => (rev_append cs_acc [], rev_append ls_acc [])
  | S f =>
      match cs with
      | [] => (rev_append cs_acc [], rev_append ls_acc [])
      | c :: rest =>
          if Ascii.eqb c "\"%char then
            match splice_rest rest with
            | Some rest2 =>
                located_splice_loop f rest2 (loc_next_line l) cs_acc ls_acc
            | None =>
                located_splice_loop f rest l (c :: cs_acc) (l :: ls_acc)
            end
          else
            let l1 := if is_nl c then loc_next_line l else l in
            located_splice_loop f rest l1 (c :: cs_acc) (l :: ls_acc)
      end
  end.

Inductive pp_at : Type :=
| AtLine (l : c_loc)
| AtLocs (ls : list c_loc) (fallback : c_loc).

Definition at_loc (a : pp_at) : c_loc :=
  match a with
  | AtLine l => l
  | AtLocs (l :: _) _ => l
  | AtLocs [] fb => fb
  end.

Definition at_skip (c : ascii) (a : pp_at) : pp_at :=
  match a with
  | AtLine l => if is_nl c then AtLine (loc_next_line l) else AtLine l
  | AtLocs (_ :: ls) fb => AtLocs ls fb
  | AtLocs [] fb => AtLocs [] fb
  end.

Fixpoint at_skips (cs : list ascii) (a : pp_at) : pp_at :=
  match cs with
  | [] => a
  | c :: rest => at_skips rest (at_skip c a)
  end.

Definition is_pp_space (c : ascii) : bool :=
  Ascii.eqb c " "%char || Ascii.eqb c "009"%char || Ascii.eqb c "013"%char ||
  Ascii.eqb c "012"%char || Ascii.eqb c "011"%char.

Definition match_digraph (a b : ascii) : option string :=
  if Ascii.eqb a "<"%char && Ascii.eqb b ":"%char then Some "<:"
  else if Ascii.eqb a ":"%char && Ascii.eqb b ">"%char then Some ":>"
  else if Ascii.eqb a "<"%char && Ascii.eqb b "%"%char then Some "<%"
  else if Ascii.eqb a "%"%char && Ascii.eqb b ">"%char then Some "%>"
  else if Ascii.eqb a "%"%char && Ascii.eqb b ":"%char then Some "%:"
  else None.

Fixpoint scan_pp_quoted (fuel : nat) (q : ascii) (cs acc : list ascii)
  : c_result (list ascii * list ascii) :=
  match fuel with
  | O => CErr "unterminated preprocessing literal"
  | S f =>
      match cs with
      | [] => CErr "unterminated preprocessing literal"
      | c :: rest =>
          if Ascii.eqb c "\"%char then
            match rest with
            | c2 :: rest2 => scan_pp_quoted f q rest2 (c2 :: c :: acc)
            | [] => CErr "unterminated preprocessing literal"
            end
          else if Ascii.eqb c q then
            COk (rev_append (q :: acc) [], rest)
          else if is_nl c then
            CErr "unterminated preprocessing literal"
          else
            scan_pp_quoted f q rest (c :: acc)
      end
  end.

Fixpoint take_pp_ident (cs acc : list ascii) : list ascii * list ascii :=
  match cs with
  | c :: rest =>
      if is_ident_char c then take_pp_ident rest (c :: acc)
      else (rev_append acc [], cs)
  | [] => (rev_append acc [], [])
  end.

Definition scan_pp_spelling (fuel : nat) (cs : list ascii)
  : c_result (list ascii * list ascii) :=
  let scan_default (c : ascii) (rest : list ascii) : c_result (list ascii * list ascii) :=
    if is_ident_start c then COk (take_pp_ident rest [c])
    else if is_digit c then COk (scan_pp_number rest [c])
    else
      match cs with
      | a :: b :: c3 :: r3 =>
          if (Ascii.eqb a "."%char && Ascii.eqb b "."%char && Ascii.eqb c3 "."%char) ||
             (Ascii.eqb a "<"%char && Ascii.eqb b "<"%char && Ascii.eqb c3 "="%char) ||
             (Ascii.eqb a ">"%char && Ascii.eqb b ">"%char && Ascii.eqb c3 "="%char)
          then COk ([a; b; c3], r3)
          else
            match match_punct2 a b with
            | Some _ => COk ([a; b], c3 :: r3)
            | None =>
                match match_digraph a b with
                | Some _ => COk ([a; b], c3 :: r3)
                | None => COk ([a], b :: c3 :: r3)
                end
            end
      | a :: b :: r2 =>
          match match_punct2 a b with
          | Some _ => COk ([a; b], r2)
          | None =>
              match match_digraph a b with
              | Some _ => COk ([a; b], r2)
              | None => COk ([a], b :: r2)
              end
          end
      | a :: r1 => COk ([a], r1)
      | [] => CErr "unexpected end of preprocessing token"
      end in
  let scan_wide_q (c : ascii) (rest : list ascii) : c_result (list ascii * list ascii) :=
    match rest with
    | q :: r2 =>
        if Ascii.eqb q """"%char || Ascii.eqb q "'"%char then
          scan_pp_quoted fuel q r2 [q; c]
        else scan_default c rest
    | [] => scan_default c rest
    end in
  match cs with
  | [] => CErr "unexpected end of preprocessing token"
  | c :: rest =>
      if Ascii.eqb c """"%char || Ascii.eqb c "'"%char then
        scan_pp_quoted fuel c rest [c]
      else if Ascii.eqb c "u"%char then
        match rest with
        | d :: q :: r2 =>
            if Ascii.eqb d "8"%char && Ascii.eqb q """"%char then
              scan_pp_quoted fuel """"%char r2 [q; d; c]
            else scan_wide_q c rest
        | _ => scan_wide_q c rest
        end
      else if Ascii.eqb c "L"%char || Ascii.eqb c "U"%char then
        scan_wide_q c rest
      else if Ascii.eqb c "."%char then
        match rest with
        | d :: r2 =>
            if is_digit d then COk (scan_pp_number r2 [d; c])
            else scan_default c rest
        | [] => scan_default c rest
        end
      else scan_default c rest
  end.

Fixpoint skip_pp_line_comment (cs : list ascii) (a : pp_at) : list ascii * pp_at :=
  match cs with
  | [] => ([], a)
  | c :: rest =>
      if is_nl c then (cs, a)
      else skip_pp_line_comment rest (at_skip c a)
  end.

Fixpoint skip_pp_block_comment (cs : list ascii) (a : pp_at)
  : c_result (list ascii * pp_at) :=
  match cs with
  | [] => CErr "unterminated preprocessing comment"
  | c :: rest =>
      if Ascii.eqb c "*"%char then
        match rest with
        | d :: r2 =>
            if Ascii.eqb d "/"%char then
              COk (r2, at_skip d (at_skip c a))
            else skip_pp_block_comment rest (at_skip c a)
        | [] => CErr "unterminated preprocessing comment"
        end
      else skip_pp_block_comment rest (at_skip c a)
  end.

Fixpoint pp_tokenize_loop (fuel : nat) (cs : list ascii) (a : pp_at)
  (space : bool) (acc : list pp_raw) : c_result (list pp_raw) :=
  match fuel with
  | O => CErr "preprocessing lexer fuel exhausted"
  | S f =>
      match cs with
      | [] => COk (rev_append acc [])
      | c :: rest =>
          if is_nl c then
            pp_tokenize_loop f rest (at_skip c a) true (PPRNl :: acc)
          else if is_pp_space c then
            pp_tokenize_loop f rest (at_skip c a) true acc
          else if Ascii.eqb c "/"%char then
            match rest with
            | d :: r2 =>
                if Ascii.eqb d "/"%char then
                  let a1 := at_skip d (at_skip c a) in
                  let '(rem, a2) := skip_pp_line_comment r2 a1 in
                  pp_tokenize_loop f rem a2 true acc
                else if Ascii.eqb d "*"%char then
                  let a1 := at_skip d (at_skip c a) in
                  match skip_pp_block_comment r2 a1 with
                  | COk (rem, a2) => pp_tokenize_loop f rem a2 true acc
                  | CErr m => CErr m
                  end
                else
                  match scan_pp_spelling (S f) cs with
                  | COk (sp_cs, rem) =>
                      let loc := at_loc a in
                      let a1 := at_skips sp_cs a in
                      let tok := mkPpTok (PPTText (string_of_chars sp_cs)) loc space [] in
                      pp_tokenize_loop f rem a1 false (PPRTok tok :: acc)
                  | CErr m => CErr m
                  end
            | [] =>
                let loc := at_loc a in
                let tok := mkPpTok (PPTText "/") loc space [] in
                pp_tokenize_loop f [] (at_skip c a) false (PPRTok tok :: acc)
            end
          else
            match scan_pp_spelling (S f) cs with
            | COk (sp_cs, rem) =>
                let loc := at_loc a in
                let a1 := at_skips sp_cs a in
                let tok := mkPpTok (PPTText (string_of_chars sp_cs)) loc space [] in
                pp_tokenize_loop f rem a1 false (PPRTok tok :: acc)
            | CErr m => CErr m
            end
      end
  end.

(** Run phases 2 and 3 over raw source characters starting at [loc]. *)
Definition source_tokens (cs : list ascii) (loc : c_loc) : c_result (list pp_raw) :=
  let fuel := S (2 * List.length cs + Z.to_nat 16) in
  if has_splice cs then
    let '(spliced, locs) := located_splice_loop fuel cs loc [] [] in
    pp_tokenize_loop fuel spliced (AtLocs locs loc) true []
  else
    pp_tokenize_loop fuel cs (AtLine loc) true [].

(** Split a raw preprocessing token stream at [PPRNl] boundaries. *)
Fixpoint token_lines_acc (raw : list pp_raw) (cur : list pp_tok)
  (acc : list (list pp_tok)) : list (list pp_tok) :=
  match raw with
  | [] =>
      match cur with
      | [] => rev_append acc []
      | _ => rev_append (rev_append cur [] :: acc) []
      end
  | PPRNl :: rest =>
      token_lines_acc rest [] (rev_append cur [] :: acc)
  | PPRTok t :: rest =>
      token_lines_acc rest (t :: cur) acc
  end.

Definition token_lines (raw : list pp_raw) : list (list pp_tok) :=
  token_lines_acc raw [] [].

(** ## Preprocessor `#if` constant evaluator (`pp_value`)

    Every integer constant in `#if` has type `intmax_t` (signed 64-bit) or
    `uintmax_t` (unsigned 64-bit), matching C11 6.10.1p4 and c_types.pl's
    `const_eval(Expr, pp, V, _)`. *)

Inductive pp_val : Type :=
| PVInt (v : Z)
| PVUb.

Definition pow2_63 : Z := 9223372036854775808.
Definition pow2_64 : Z := 18446744073709551616.
Definition mask_64 : Z := 18446744073709551615.
Definition max_int32 : Z := 2147483647.
Definition max_uint32 : Z := 4294967295.
Definition max_int64 : Z := 9223372036854775807.
Definition min_int64 : Z := -9223372036854775808.

Definition convert_int64 (is_unsigned : bool) (v : Z) : Z :=
  let u := Z.land v mask_64 in
  if is_unsigned then u
  else if u >=? pow2_63 then u - pow2_64
  else u.

Definition num_is_unsigned (v : Z) (suf : int_suffix) (rad : int_radix) : bool :=
  match suf with
  | SufU | SufUL | SufULL => true
  | SufNone =>
      match rad with
      | RadDec => v >? max_int64
      | RadOther =>
          if v <=? max_int32 then false
          else if v <=? max_uint32 then true
          else if v <=? max_int64 then false
          else true
      end
  | SufL | SufLL =>
      v >? max_int64
  end.

Definition pv_convert (u : bool) (pv : pp_val) : pp_val :=
  match pv with
  | PVUb => PVUb
  | PVInt v => PVInt (convert_int64 u v)
  end.

Fixpoint eval_pp_expr (e : c_expr) : option (bool * pp_val) :=
  match e with
  | ENum v suf rad =>
      let u := num_is_unsigned v suf rad in
      Some (u, PVInt (convert_int64 u v))
  | EChr v =>
      Some (false, PVInt (convert_int64 false v))
  | EUn op a =>
      match eval_pp_expr a with
      | None => None
      | Some (u, pv) =>
          match op with
          | UNot =>
              match pv with
              | PVUb => Some (false, PVUb)
              | PVInt v => Some (false, PVInt (if Z.eqb v 0 then 1 else 0))
              end
          | UPlus => Some (u, pv)
          | UNeg =>
              match pv with
              | PVUb => Some (u, PVUb)
              | PVInt v => Some (u, PVInt (convert_int64 u (- v)))
              end
          | UBnot =>
              match pv with
              | PVUb => Some (u, PVUb)
              | PVInt v => Some (u, PVInt (convert_int64 u (- v - 1)))
              end
          | _ => None
          end
      end
  | EBin op a b =>
      match eval_pp_expr a, eval_pp_expr b with
      | Some (ua, pva), Some (ub, pvb) =>
          match op with
          | BLand =>
              match pva with
              | PVUb => Some (false, PVUb)
              | PVInt va =>
                  if Z.eqb va 0 then Some (false, PVInt 0)
                  else
                    match pvb with
                    | PVUb => Some (false, PVUb)
                    | PVInt vb => Some (false, PVInt (if Z.eqb vb 0 then 0 else 1))
                    end
              end
          | BLor =>
              match pva with
              | PVUb => Some (false, PVUb)
              | PVInt va =>
                  if negb (Z.eqb va 0) then Some (false, PVInt 1)
                  else
                    match pvb with
                    | PVUb => Some (false, PVUb)
                    | PVInt vb => Some (false, PVInt (if Z.eqb vb 0 then 0 else 1))
                    end
              end
          | BShl | BShr =>
              match pva, pvb with
              | PVInt va, PVInt vb =>
                  if (0 <=? vb) && (vb <? 64) then
                    let va' := convert_int64 ua va in
                    let r :=
                      match op with
                      | BShl => Z.shiftl va' vb
                      | _ => Z.shiftr va' vb
                      end in
                    Some (ua, PVInt (convert_int64 ua r))
                  else Some (ua, PVUb)
              | _, _ => Some (ua, PVUb)
              end
          | BEq | BNe | BLt | BGt | BLe | BGe =>
              let cu := ua || ub in
              match pva, pvb with
              | PVInt va0, PVInt vb0 =>
                  let va := convert_int64 cu va0 in
                  let vb := convert_int64 cu vb0 in
                  let res :=
                    match op with
                    | BEq => Z.eqb va vb
                    | BNe => negb (Z.eqb va vb)
                    | BLt => va <? vb
                    | BGt => vb <? va
                    | BLe => va <=? vb
                    | _ => vb <=? va
                    end in
                  Some (false, PVInt (if res then 1 else 0))
              | _, _ => Some (false, PVUb)
              end
          | BAdd | BSub | BMul | BDiv | BMod | BAnd | BOr | BXor =>
              let cu := ua || ub in
              match pva, pvb with
              | PVInt va0, PVInt vb0 =>
                  let va := convert_int64 cu va0 in
                  let vb := convert_int64 cu vb0 in
                  match op with
                  | BAdd => Some (cu, PVInt (convert_int64 cu (va + vb)))
                  | BSub => Some (cu, PVInt (convert_int64 cu (va - vb)))
                  | BMul => Some (cu, PVInt (convert_int64 cu (va * vb)))
                  | BAnd => Some (cu, PVInt (convert_int64 cu (Z.land va vb)))
                  | BOr => Some (cu, PVInt (convert_int64 cu (Z.lor va vb)))
                  | BXor => Some (cu, PVInt (convert_int64 cu (Z.lxor va vb)))
                  | BDiv =>
                      if Z.eqb vb 0 then Some (cu, PVUb)
                      else if negb cu && Z.eqb va min_int64 && Z.eqb vb (-1) then Some (cu, PVUb)
                      else Some (cu, PVInt (convert_int64 cu (Z.quot va vb)))
                  | BMod =>
                      if Z.eqb vb 0 then Some (cu, PVUb)
                      else if negb cu && Z.eqb va min_int64 && Z.eqb vb (-1) then Some (cu, PVUb)
                      else Some (cu, PVInt (convert_int64 cu (Z.rem va vb)))
                  | _ => None
                  end
              | _, _ => Some (cu, PVUb)
              end
          end
      | _, _ => None
      end
  | ECond c a b =>
      match eval_pp_expr c, eval_pp_expr a, eval_pp_expr b with
      | Some (_, pvc), Some (ua, pva), Some (ub, pvb) =>
          let cu := ua || ub in
          match pvc with
          | PVUb => Some (cu, PVUb)
          | PVInt vc =>
              if negb (Z.eqb vc 0) then Some (cu, pv_convert cu pva)
              else Some (cu, pv_convert cu pvb)
          end
      | _, _, _ => None
      end
  | EGCond c b =>
      match eval_pp_expr c, eval_pp_expr b with
      | Some (uc, pvc), Some (ub, pvb) =>
          let cu := uc || ub in
          match pvc with
          | PVUb => Some (cu, PVUb)
          | PVInt vc =>
              if negb (Z.eqb vc 0) then Some (cu, pv_convert cu pvc)
              else Some (cu, pv_convert cu pvb)
          end
      | _, _ => None
      end
  | EComma a b =>
      match eval_pp_expr a, eval_pp_expr b with
      | Some _, Some res => Some res
      | _, _ => None
      end
  | _ => None
  end.

Definition pp_value (e : c_expr) : option Z :=
  match eval_pp_expr e with
  | Some (_, PVInt v) => Some v
  | _ => None
  end.

(** ## Helpers for token text, hide sets, include names, and paths *)

Definition pp_tok_text (t : pp_tok) : option string :=
  match ppt_val t with
  | PPTText s => Some s
  | _ => None
  end.

Definition hide_intersection (xs ys : list string) : list string :=
  filter (fun s => str_in s ys) xs.

Fixpoint hide_add_list (xs ys : list string) : list string :=
  match xs with
  | [] => ys
  | x :: rest =>
      if str_in x ys then hide_add_list rest ys
      else hide_add_list rest (x :: ys)
  end.

Definition replaced_token (hide : list string) (loc : c_loc) (t : pp_tok) : pp_tok :=
  mkPpTok (ppt_val t) loc (ppt_space t) (hide_add_list hide (ppt_hide t)).

Definition first_spaced (ts : list pp_tok) (sp : bool) : list pp_tok :=
  match ts with
  | [] => []
  | t :: rest => mkPpTok (ppt_val t) (ppt_loc t) sp (ppt_hide t) :: rest
  end.

(** Escape a raw list of characters as a C string literal, as `#` does. *)
Fixpoint escape_pp_string_chars (cs acc : list ascii) : list ascii :=
  match cs with
  | [] => """"%char :: acc
  | c :: rest =>
      if Ascii.eqb c """"%char || Ascii.eqb c "\"%char then
        escape_pp_string_chars rest (c :: "\"%char :: acc)
      else
        escape_pp_string_chars rest (c :: acc)
  end.

Fixpoint tokens_text_chars (ts : list pp_tok) (first : bool) (acc : list ascii)
  : list ascii :=
  match ts with
  | [] => rev_append acc []
  | t :: rest =>
      let acc1 :=
        if ppt_space t && negb first then " "%char :: acc else acc in
      let s := match ppt_val t with PPTText x => x | _ => "" end in
      tokens_text_chars rest false (rev_append (list_ascii_of_string s) acc1)
  end.

Definition tokens_string (ts : list pp_tok) : string :=
  let raw := tokens_text_chars ts true [] in
  string_of_rev (escape_pp_string_chars raw [""""%char]).

Definition parse_positive_dec (s : string) : option Z :=
  let cs := list_ascii_of_string s in
  let '(v, cnt, rem) := take_dec_digits cs 0 O in
  match rem with
  | [] => if negb (Nat.eqb cnt 0) && (v >? 0) then Some v else None
  | _ => None
  end.

Definition parse_nonneg_dec (s : string) : option Z :=
  let cs := list_ascii_of_string s in
  let '(v, cnt, rem) := take_dec_digits cs 0 O in
  match rem with
  | [] => if negb (Nat.eqb cnt 0) then Some v else None
  | _ => None
  end.

Definition parse_include_name (ts : list pp_tok) : option (string * include_form) :=
  match ts with
  | [t] =>
      match ppt_val t with
      | PPTText s =>
          let n := String.length s in
          if (2 <=? n)%nat &&
             String.eqb (String.substring 0 1 s) """" &&
             String.eqb (String.substring (n - 1) 1 s) """"
          then Some (String.substring 1 (n - 2) s, IncQuote)
          else None
      | _ => None
      end
  | t0 :: rest =>
      match ppt_val t0 with
      | PPTText s0 =>
          if String.eqb s0 "<" then
            match rev_append rest [] with
            | t_last :: rmid =>
                match ppt_val t_last with
                | PPTText sl =>
                    if String.eqb sl ">" then
                      let mid := rev_append rmid [] in
                      let parts := map (fun x => match ppt_val x with PPTText a => a | _ => "" end) mid in
                      Some (String.concat "" parts, IncAngle)
                    else None
                | _ => None
                end
            | [] => None
            end
          else None
      | _ => None
      end
  | [] => None
  end.

Definition file_directory (file : string) : string :=
  let fix drop_after_slash (rev_cs : list ascii) : option (list ascii) :=
    match rev_cs with
    | [] => None
    | c :: rest =>
        if Ascii.eqb c "/"%char then Some rest
        else drop_after_slash rest
    end in
  match drop_after_slash (rev_append (list_ascii_of_string file) []) with
  | Some rdir => string_of_rev rdir
  | None => "."
  end.

Definition path_join (dir name : string) : string :=
  dir ++ "/" ++ name.

Definition starts_with (pfx s : string) : bool :=
  let n := String.length pfx in
  (n <=? String.length s)%nat && String.eqb (String.substring 0 n s) pfx.

Definition search_paths (is_next : bool) (file : string) (dirs : list string)
  : list string :=
  if negb is_next then dirs
  else
    let fix find_after (ds : list string) : option (list string) :=
      match ds with
      | [] => None
      | d :: rest =>
          if starts_with (d ++ "/") file then Some rest
          else find_after rest
      end in
    match find_after dirs with
    | Some rest => rest
    | None => dirs
    end.

Fixpoint find_first_existing (cands : list string) : pp_step (option string) :=
  match cands with
  | [] => pp_ok None
  | p :: rest =>
      PPFileExists p (fun ex => if ex then pp_ok (Some p) else find_first_existing rest)
  end.

Definition resolve_include_path (name : string) (form : include_form)
  (file : string) (dirs : list string) : pp_step (option string) :=
  if starts_with "/" name then
    PPFileExists name (fun ex => pp_ok (if ex then Some name else None))
  else
    let dir_cands := map (fun d => path_join d name) dirs in
    let cands :=
      match form with
      | IncQuote => path_join (file_directory file) name :: dir_cands
      | IncAngle => dir_cands
      end in
    find_first_existing cands.

Definition is_feature_op (s : string) : bool :=
  str_in s [ "__has_attribute"; "__has_builtin"; "__has_extension";
             "__has_feature"; "__has_c_attribute"; "__building_module" ].

Definition is_defined_name (name : string) (env : pp_env) : bool :=
  match smap_find name (pp_macros env) with
  | Some _ => true
  | None =>
      String.eqb name "__has_include" || String.eqb name "__has_include_next" ||
      String.eqb name "__LINE__" || String.eqb name "__FILE__" ||
      is_feature_op name
  end.

Fixpoint lookup_feature (op name : string) (fs : list feature_entry)
  : option string :=
  match fs with
  | [] => None
  | f :: rest =>
      if String.eqb (feat_op f) op && String.eqb (feat_name f) name then
        Some (feat_val f)
      else lookup_feature op name rest
  end.

Definition is_valid_ident (s : string) : bool :=
  match list_ascii_of_string s with
  | c :: rest => is_ident_start c && forallb is_ident_char rest
  | [] => false
  end.

(** ## Macro arguments, parameter binding, substitution, and token pasting *)

Fixpoint collect_macro_args (ts : list pp_tok) (depth : nat)
  (rev_cur : list pp_tok) (rev_args : list (list pp_tok))
  : option (list (list pp_tok) * list pp_tok * list string) :=
  match ts with
  | [] => None
  | t :: rest =>
      match ppt_val t with
      | PPTText s =>
          if Nat.eqb depth 0 && String.eqb s ")" then
            let arg := rev_append rev_cur [] in
            Some (rev_append (arg :: rev_args) [], rest, ppt_hide t)
          else if Nat.eqb depth 0 && String.eqb s "," then
            let arg := rev_append rev_cur [] in
            collect_macro_args rest 0 [] (arg :: rev_args)
          else
            let d1 :=
              if String.eqb s "(" then S depth
              else if String.eqb s ")" then pred depth
              else depth in
            collect_macro_args rest d1 (t :: rev_cur) rev_args
      | _ => collect_macro_args rest depth (t :: rev_cur) rev_args
      end
  end.

Fixpoint join_va_args_aux (first : list pp_tok) (rest : list (list pp_tok))
  : list pp_tok :=
  match rest with
  | [] => first
  | a :: more =>
      app first (mkPpTok (PPTText ",") (Loc "<macro>" 0) false [] :: join_va_args_aux a more)
  end.

Definition join_va_args (args : list (list pp_tok)) : list pp_tok :=
  match args with
  | [] => []
  | a :: rest => join_va_args_aux a rest
  end.

Fixpoint bind_macro_params (ps : list macro_param) (args : list (list pp_tok))
  (loc : c_loc) : c_result (list (string * list pp_tok)) :=
  match ps with
  | [] =>
      match args with
      | [] => COk []
      | _ => CErr (loc_to_string loc ++ ": wrong macro argument count")
      end
  | [MPVariadic p] => COk [(p, join_va_args args)]
  | MPNamed p :: ps' =>
      match args with
      | [] => CErr (loc_to_string loc ++ ": wrong macro argument count")
      | a :: args' =>
          match bind_macro_params ps' args' loc with
          | COk bs => COk ((p, a) :: bs)
          | CErr m => CErr m
          end
      end
  | MPVariadic _ :: _ => CErr (loc_to_string loc ++ ": wrong macro argument count")
  end.

(** Apply `##` token pasting and remove empty placemarker tokens. *)
Fixpoint tokens_pasted_loop (fuel : nat) (ts : list pp_tok) (macro_loc : c_loc)
  (acc : list pp_tok) : c_result (list pp_tok) :=
  match fuel with
  | O => CErr (loc_to_string macro_loc ++ ": token paste fuel exhausted")
  | S f =>
      match ts with
      | [] => COk (rev_append acc [])
      | t1 :: t2 :: t3 :: rest =>
          match ppt_val t1, ppt_val t2, ppt_val t3 with
          | PPTText a, PPTText op, PPTText b =>
              if String.eqb op "##" then
                let c := a ++ b in
                let valid :=
                  if String.eqb c "" then true
                  else
                    let cs := list_ascii_of_string c in
                    match scan_pp_spelling (S (List.length cs + 4)) cs with
                    | COk (_, []) => true
                    | _ => false
                    end in
                if valid then
                  let h2 := hide_intersection (ppt_hide t1) (ppt_hide t3) in
                  let pasted := mkPpTok (PPTText c) (ppt_loc t1) (ppt_space t1) h2 in
                  tokens_pasted_loop f (pasted :: rest) macro_loc acc
                else
                  CErr (loc_to_string macro_loc ++ ": invalid_token_paste(" ++ a ++ ", " ++ b ++ ")")
              else if String.eqb a "" then
                tokens_pasted_loop f (t2 :: t3 :: rest) macro_loc acc
              else
                tokens_pasted_loop f (t2 :: t3 :: rest) macro_loc (t1 :: acc)
          | PPTText a, _, _ =>
              if String.eqb a "" then
                tokens_pasted_loop f (t2 :: t3 :: rest) macro_loc acc
              else
                tokens_pasted_loop f (t2 :: t3 :: rest) macro_loc (t1 :: acc)
          | _, _, _ =>
              tokens_pasted_loop f (t2 :: t3 :: rest) macro_loc (t1 :: acc)
          end
      | t1 :: rest =>
          match ppt_val t1 with
          | PPTText a =>
              if String.eqb a "" then tokens_pasted_loop f rest macro_loc acc
              else tokens_pasted_loop f rest macro_loc (t1 :: acc)
          | _ => tokens_pasted_loop f rest macro_loc (t1 :: acc)
          end
      end
  end.

Definition tokens_pasted (ts : list pp_tok) (macro_loc : c_loc) : c_result (list pp_tok) :=
  tokens_pasted_loop (S (2 * List.length ts + 4)) ts macro_loc [].

(** ## Macro expansion engine

    Expansion is a single fuel-bounded loop that returns [pp_step] so
    `__has_include` and on-demand feature queries can suspend cleanly while
    all ordinary token steps stay direct tail calls. *)

Fixpoint expand_tokens_loop (fuel : nat) (ts : list pp_tok) (env : pp_env)
  (acc : list pp_tok) {struct fuel} : pp_step (list pp_tok * pp_env) :=
  match fuel with
  | O => PPDone (CErr "macro expansion fuel exhausted")
  | S f =>
      match ts with
      | [] => pp_ok (rev_append acc [], env)
      | t :: rest =>
          match ppt_val t with
          | PPTText name =>
              let emit_and_cont (_ : unit) :=
                expand_tokens_loop f rest env (t :: acc) in
              let try_builtin (_ : unit) :=
                if String.eqb name "__LINE__" then
                  let ln := match ppt_loc t with Loc _ n => n | LocEof => 0 end in
                  let r := mkPpTok (PPTText (z_to_string ln)) (ppt_loc t) (ppt_space t) (ppt_hide t) in
                  expand_tokens_loop f (r :: rest) env acc
                else if String.eqb name "__FILE__" then
                  let fn := match ppt_loc t with Loc s _ => s | LocEof => "" end in
                  let str_lit := tokens_string [mkPpTok (PPTText fn) (ppt_loc t) false []] in
                  let r := mkPpTok (PPTText str_lit) (ppt_loc t) (ppt_space t) (ppt_hide t) in
                  expand_tokens_loop f (r :: rest) env acc
                else if String.eqb name "__has_include" || String.eqb name "__has_include_next" then
                  match rest with
                  | tlp :: rest1 =>
                      match ppt_val tlp with
                      | PPTText lp =>
                          if String.eqb lp "(" then
                            match collect_macro_args rest1 0 [] [] with
                            | Some ([arg], rest2, _) =>
                                let is_next := String.eqb name "__has_include_next" in
                                let finish_has (hname : string) (hform : include_form) (env1 : pp_env) :=
                                  let dirs := search_paths is_next (pp_file env1) (pp_dirs env1) in
                                  pp_bind (resolve_include_path hname hform (pp_file env1) dirs) (fun found =>
                                    let ans := match found with Some _ => "1" | None => "0" end in
                                    let r := mkPpTok (PPTText ans) (ppt_loc t) (ppt_space t) (ppt_hide t) in
                                    expand_tokens_loop f (r :: rest2) env1 acc) in
                                match parse_include_name arg with
                                | Some (hname, hform) => finish_has hname hform env
                                | None =>
                                    pp_bind (expand_tokens_loop f arg env []) (fun '(earg, env1) =>
                                      match parse_include_name earg with
                                      | Some (hname, hform) => finish_has hname hform env1
                                      | None => emit_and_cont tt
                                      end)
                                end
                            | _ => emit_and_cont tt
                            end
                          else emit_and_cont tt
                      | _ => emit_and_cont tt
                      end
                  | [] => emit_and_cont tt
                  end
                else if is_feature_op name then
                  match rest with
                  | tlp :: tnm :: trp :: rest2 =>
                      match ppt_val tlp, ppt_val tnm, ppt_val trp with
                      | PPTText lp, PPTText fnm, PPTText rp =>
                          if String.eqb lp "(" && String.eqb rp ")" then
                            match lookup_feature name fnm (pp_features env) with
                            | Some ans =>
                                let r := mkPpTok (PPTText ans) (ppt_loc t) (ppt_space t) (ppt_hide t) in
                                expand_tokens_loop f (r :: rest2) env acc
                            | None =>
                                if is_valid_ident fnm then
                                  PPQueryFeature name fnm (fun ans =>
                                    let env1 := add_feature env name fnm ans in
                                    let r := mkPpTok (PPTText ans) (ppt_loc t) (ppt_space t) (ppt_hide t) in
                                    expand_tokens_loop f (r :: rest2) env1 acc)
                                else emit_and_cont tt
                            end
                          else emit_and_cont tt
                      | _, _, _ => emit_and_cont tt
                      end
                  | _ => emit_and_cont tt
                  end
                else emit_and_cont tt in
              if negb (str_in name (ppt_hide t)) then
                match smap_find name (pp_macros env) with
                | Some (MObj body) =>
                    match tokens_pasted body (ppt_loc t) with
                    | CErr msg => PPDone (CErr msg)
                    | COk repl =>
                        let marked := map (replaced_token (name :: ppt_hide t) (ppt_loc t)) repl in
                        let replaced := first_spaced marked (ppt_space t) in
                        expand_tokens_loop f (app replaced rest) env acc
                    end
                | Some (MFun params body) =>
                    match rest with
                    | tlp :: rest1 =>
                        match ppt_val tlp with
                        | PPTText lp =>
                            if String.eqb lp "(" then
                              match collect_macro_args rest1 0 [] [] with
                              | None => try_builtin tt
                              | Some (args0, rest2, end_hide) =>
                                  let args :=
                                    match args0, params with
                                    | [[]], [] => []
                                    | _, _ => args0
                                    end in
                                  match bind_macro_params params args (ppt_loc t) with
                                  | CErr msg => PPDone (CErr msg)
                                  | COk bindings =>
                                      pp_bind (subst_body_loop f body bindings env false [])
                                        (fun '(repl0, env1) =>
                                           match tokens_pasted repl0 (ppt_loc t) with
                                           | CErr msg => PPDone (CErr msg)
                                           | COk repl =>
                                               let base_hide := hide_intersection (ppt_hide t) end_hide in
                                               let marked := map (replaced_token (name :: base_hide) (ppt_loc t)) repl in
                                               let replaced := first_spaced marked (ppt_space t) in
                                               expand_tokens_loop f (app replaced rest2) env1 acc
                                           end)
                                  end
                              end
                            else try_builtin tt
                        | _ => try_builtin tt
                        end
                    | [] => try_builtin tt
                    end
                | None => try_builtin tt
                end
              else try_builtin tt
          | _ => expand_tokens_loop f rest env (t :: acc)
          end
      end
  end

with subst_body_loop (fuel : nat) (body : list pp_tok)
  (bindings : list (string * list pp_tok)) (env : pp_env)
  (after_paste : bool) (acc : list pp_tok) {struct fuel}
  : pp_step (list pp_tok * pp_env) :=
  match fuel with
  | O => PPDone (CErr "macro substitution fuel exhausted")
  | S f =>
      match body with
      | [] => pp_ok (rev_append acc [], env)
      | t1 :: rest1 =>
          let handle_normal (_ : unit) :=
            match ppt_val t1 with
            | PPTText p =>
                let next_paste := String.eqb p "##" in
                match CLex.assoc_str p bindings with
                | Some raw =>
                    let before_paste :=
                      match rest1 with
                      | tnext :: _ =>
                          match ppt_val tnext with
                          | PPTText s => String.eqb s "##"
                          | _ => false
                          end
                      | [] => false
                      end in
                    if after_paste || before_paste then
                      let r :=
                        match raw with
                        | [] => [mkPpTok (PPTText "") (ppt_loc t1) (ppt_space t1) (ppt_hide t1)]
                        | _ => first_spaced raw (ppt_space t1)
                        end in
                      subst_body_loop f rest1 bindings env next_paste (rev_append r acc)
                    else
                      pp_bind (expand_tokens_loop f raw env []) (fun '(use_ts, env1) =>
                        let r :=
                          match use_ts with
                          | [] => [mkPpTok (PPTText "") (ppt_loc t1) (ppt_space t1) (ppt_hide t1)]
                          | _ => first_spaced use_ts (ppt_space t1)
                          end in
                        subst_body_loop f rest1 bindings env1 next_paste (rev_append r acc))
                | None =>
                    subst_body_loop f rest1 bindings env next_paste (t1 :: acc)
                end
            | _ => subst_body_loop f rest1 bindings env false (t1 :: acc)
            end in
          match ppt_val t1, rest1 with
          | PPTText s1, t2 :: rest2 =>
              if String.eqb s1 "#" then
                match ppt_val t2 with
                | PPTText p =>
                    match CLex.assoc_str p bindings with
                    | Some raw =>
                        let st := mkPpTok (PPTText (tokens_string raw)) (ppt_loc t1) (ppt_space t1) (ppt_hide t1) in
                        subst_body_loop f rest2 bindings env false (st :: acc)
                    | None => handle_normal tt
                    end
                | _ => handle_normal tt
                end
              else handle_normal tt
          | _, _ => handle_normal tt
          end
      end
  end.

Definition expand_fuel : nat := Z.to_nat 10000000.

Definition expand_tokens (ts : list pp_tok) (env : pp_env)
  : pp_step (list pp_tok * pp_env) :=
  expand_tokens_loop expand_fuel ts env [].

(** ## Directive parsing: `#define`, `#pragma`, `#line`, and `#if` *)

Fixpoint parse_macro_params (ts : list pp_tok) (acc : list macro_param)
  : option (list macro_param * list pp_tok) :=
  match ts with
  | t1 :: rest1 =>
      match ppt_val t1 with
      | PPTText s1 =>
          if String.eqb s1 ")" then
            match acc with
            | [] => Some ([], rest1)
            | _ => None
            end
          else if String.eqb s1 "..." then
            match rest1 with
            | t2 :: rest2 =>
                match ppt_val t2 with
                | PPTText s2 =>
                    if String.eqb s2 ")" then
                      Some (rev_append (MPVariadic "__VA_ARGS__" :: acc) [], rest2)
                    else None
                | _ => None
                end
            | [] => None
            end
          else
            match rest1 with
            | t2 :: rest2 =>
                match ppt_val t2 with
                | PPTText s2 =>
                    if String.eqb s2 ")" then
                      Some (rev_append (MPNamed s1 :: acc) [], rest2)
                    else if String.eqb s2 "," then
                      parse_macro_params rest2 (MPNamed s1 :: acc)
                    else if String.eqb s2 "..." then
                      match rest2 with
                      | t3 :: rest3 =>
                          match ppt_val t3 with
                          | PPTText s3 =>
                              if String.eqb s3 ")" then
                                Some (rev_append (MPVariadic s1 :: acc) [], rest3)
                              else None
                          | _ => None
                          end
                      | [] => None
                      end
                    else None
                | _ => None
                end
            | [] => None
            end
      | _ => None
      end
  | [] => None
  end.

Definition apply_define (args : list pp_tok) (ms : smap macro_def)
  : option (smap macro_def) :=
  match args with
  | tnm :: rest =>
      match ppt_val tnm with
      | PPTText name =>
          match rest with
          | tlp :: rest1 =>
              match ppt_val tlp with
              | PPTText lp =>
                  if String.eqb lp "(" && negb (ppt_space tlp) then
                    match parse_macro_params rest1 [] with
                    | Some (params, body) => Some (smap_add name (MFun params body) ms)
                    | None => None
                    end
                  else Some (smap_add name (MObj rest) ms)
              | _ => Some (smap_add name (MObj rest) ms)
              end
          | [] => Some (smap_add name (MObj []) ms)
          end
      | _ => None
      end
  | [] => None
  end.

Definition parse_pragma_weak (args : list pp_tok)
  : option (string * option string) :=
  match args with
  | tw :: tn :: rest =>
      match ppt_val tw, ppt_val tn with
      | PPTText w, PPTText nm =>
          if String.eqb w "weak" && is_pack_label nm then
            match rest with
            | [] => Some (nm, None)
            | [teq; ttgt] =>
                match ppt_val teq, ppt_val ttgt with
                | PPTText eqs, PPTText tgts =>
                    if String.eqb eqs "=" && is_pack_label tgts then
                      Some (nm, Some tgts)
                    else None
                | _, _ => None
                end
            | _ => None
            end
          else None
      | _, _ => None
      end
  | _ => None
  end.

Definition parse_pragma_pack (args : list pp_tok) : option pack_op :=
  match args with
  | tp :: tlp :: rest =>
      match ppt_val tp, ppt_val tlp with
      | PPTText p, PPTText lp =>
          if String.eqb p "pack" && String.eqb lp "(" then
            match rev_append rest [] with
            | trp :: rinner =>
                match ppt_val trp with
                | PPTText rp =>
                    if String.eqb rp ")" then
                      let inner := rev_append rinner [] in
                      let to_arg (t : pp_tok) : option pack_arg_val :=
                        match ppt_val t with
                        | PPTText s =>
                            match parse_nonneg_dec s with
                            | Some n => Some (PAInt n)
                            | None => Some (PAAtom s)
                            end
                        | _ => None
                        end in
                      match map_opt to_arg inner with
                      | Some pavs => parse_pack_inner pavs
                      | None => None
                      end
                    else None
                | _ => None
                end
            | [] => None
            end
          else None
      | _, _ => None
      end
  | _ => None
  end.

Definition apply_macro_stack (is_push : bool) (name : string) (env : pp_env)
  : pp_env :=
  let ms := pp_macros env in
  let sv := pp_saved env in
  if is_push then
    let cur := smap_find name ms in
    let stk := match smap_find name sv with Some s => s | None => [] end in
    set_macros_saved env ms (smap_add name (cur :: stk) sv)
  else
    match smap_find name sv with
    | Some (saved :: stk) =>
        let sv1 := smap_add name stk sv in
        let ms1 :=
          match saved with
          | Some def => smap_add name def ms
          | None => smap_remove name ms
          end in
        set_macros_saved env ms1 sv1
    | _ => env
    end.

(** Replace `defined(X)` and `defined X` with `1` or `0` prior to macro
    expansion inside `#if` and `#elif`. *)
Fixpoint replace_defined (ts : list pp_tok) (env : pp_env) (acc : list pp_tok)
  : list pp_tok :=
  match ts with
  | [] => rev_append acc []
  | t0 :: rest0 =>
      match ppt_val t0 with
      | PPTText s0 =>
          if String.eqb s0 "defined" then
            match rest0 with
            | [] => rev_append (t0 :: acc) []
            | t1 :: rest1 =>
                match ppt_val t1 with
                | PPTText s1 =>
                    match rest1 with
                    | t2 :: t3 :: rest3 =>
                        match ppt_val t2, ppt_val t3 with
                        | PPTText nm, PPTText rp =>
                            if String.eqb s1 "(" && String.eqb rp ")" then
                              let v := if is_defined_name nm env then "1" else "0" in
                              let r := mkPpTok (PPTText v) (ppt_loc t0) (ppt_space t0) (ppt_hide t0) in
                              replace_defined rest3 env (r :: acc)
                            else
                              let v := if is_defined_name s1 env then "1" else "0" in
                              let r := mkPpTok (PPTText v) (ppt_loc t0) (ppt_space t0) (ppt_hide t0) in
                              replace_defined rest1 env (r :: acc)
                        | _, _ =>
                            let v := if is_defined_name s1 env then "1" else "0" in
                            let r := mkPpTok (PPTText v) (ppt_loc t0) (ppt_space t0) (ppt_hide t0) in
                            replace_defined rest1 env (r :: acc)
                        end
                    | _ =>
                        let v := if is_defined_name s1 env then "1" else "0" in
                        let r := mkPpTok (PPTText v) (ppt_loc t0) (ppt_space t0) (ppt_hide t0) in
                        replace_defined rest1 env (r :: acc)
                    end
                | _ => replace_defined rest0 env (t0 :: acc)
                end
            end
          else replace_defined rest0 env (t0 :: acc)
      | _ => replace_defined rest0 env (t0 :: acc)
      end
  end.

Definition pp_expr_token (t : pp_tok) : c_result token :=
  let loc := ppt_loc t in
  match ppt_val t with
  | PPTText s =>
      let cs := list_ascii_of_string s in
      match lex_chars "<condition>" cs with
      | COk [mkTok k _] =>
          match k with
          | TId _ | TKw _ => COk (mkTok (TInt 0 SufNone RadDec) loc)
          | _ => COk (mkTok k loc)
          end
      | _ =>
          match cs with
          | c :: _ =>
              if is_ident_start c then COk (mkTok (TInt 0 SufNone RadDec) loc)
              else CErr (loc_to_string loc ++ ": bad_if_token(" ++ s ++ ")")
          | [] => CErr (loc_to_string loc ++ ": bad_if_token()")
          end
      end
  | _ => CErr (loc_to_string loc ++ ": bad_if_token(pragma)")
  end.

Fixpoint map_c_result {A B : Type} (f : A -> c_result B) (xs : list A) (acc : list B)
  : c_result (list B) :=
  match xs with
  | [] => COk (rev_append acc [])
  | x :: rest =>
      match f x with
      | COk y => map_c_result f rest (y :: acc)
      | CErr m => CErr m
      end
  end.

Definition eval_if_condition (args : list pp_tok) (env : pp_env)
  : pp_step (Z * pp_env) :=
  let replaced := replace_defined args env [] in
  pp_bind (expand_tokens replaced env) (fun '(expanded, env1) =>
    match map_c_result pp_expr_token expanded [] with
    | CErr m => PPDone (CErr m)
    | COk toks =>
        match c_constant_expression toks [] with
        | CErr m => PPDone (CErr m)
        | COk expr =>
            match pp_value expr with
            | Some v => pp_ok (v, env1)
            | None =>
                let loc := match toks with mkTok _ l :: _ => l | [] => Loc "<condition>" 0 end in
                pp_err loc "not_constant"
            end
        end
    end).

(** Conditional compilation stack entries. *)
Inductive cond_seen : Type :=
| CSNo
| CSYes
| CSElse.

Record cond_frame : Type := mkCond {
  cf_taken : bool;
  cf_seen : cond_seen;
  cf_parent : bool;
}.

Definition stack_active (st : list cond_frame) : bool :=
  match st with
  | [] => true
  | f :: _ => cf_taken f
  end.

Definition is_cond_directive (name : string) : bool :=
  str_in name [ "if"; "ifdef"; "ifndef"; "elif"; "else"; "endif" ].

Definition eval_cond_kind (name : string) (args : list pp_tok) (env : pp_env)
  : pp_step (Z * pp_env) :=
  if String.eqb name "ifdef" then
    match args with
    | [t] =>
        match ppt_val t with
        | PPTText nm => pp_ok (if is_defined_name nm env then 1 else 0, env)
        | _ => pp_err (ppt_loc t) "expected macro name after #ifdef"
        end
    | _ => PPDone (CErr "expected macro name after #ifdef")
    end
  else if String.eqb name "ifndef" then
    match args with
    | [t] =>
        match ppt_val t with
        | PPTText nm => pp_ok (if is_defined_name nm env then 0 else 1, env)
        | _ => pp_err (ppt_loc t) "expected macro name after #ifndef"
        end
    | _ => PPDone (CErr "expected macro name after #ifndef")
    end
  else eval_if_condition args env.

Definition step_cond_stack (name : string) (loc : c_loc) (args : list pp_tok)
  (env : pp_env) (st : list cond_frame) : pp_step (list cond_frame * pp_env) :=
  if String.eqb name "elif" then
    match st with
    | mkCond _ seen parent :: tail =>
        match seen with
        | CSElse => pp_err loc "unexpected #elif"
        | CSYes => pp_ok (mkCond false CSYes parent :: tail, env)
        | CSNo =>
            if parent then
              pp_bind (eval_if_condition args env) (fun '(v, env1) =>
                let taken := negb (Z.eqb v 0) in
                let seen1 := if taken then CSYes else CSNo in
                pp_ok (mkCond taken seen1 true :: tail, env1))
            else pp_ok (mkCond false CSNo false :: tail, env)
        end
    | [] => pp_err loc "unexpected #elif"
    end
  else if String.eqb name "else" then
    match st with
    | mkCond _ seen parent :: tail =>
        match seen with
        | CSElse => pp_err loc "unexpected #else"
        | CSYes => pp_ok (mkCond false CSElse parent :: tail, env)
        | CSNo => pp_ok (mkCond parent CSElse parent :: tail, env)
        end
    | [] => pp_err loc "unexpected #else"
    end
  else if String.eqb name "endif" then
    match st with
    | _ :: tail => pp_ok (tail, env)
    | [] => pp_err loc "unexpected #endif"
    end
  else
    if stack_active st then
      pp_bind (eval_cond_kind name args env) (fun '(v, env1) =>
        let taken := negb (Z.eqb v 0) in
        let seen := if taken then CSYes else CSNo in
        pp_ok (mkCond taken seen true :: st, env1))
    else
      pp_ok (mkCond false CSNo false :: st, env).

(** Remap token locations after `#line N ["file"]`. *)
Definition remap_loc (old_line : Z) (new_file : string) (new_line : Z) (l : c_loc) : c_loc :=
  match l with
  | Loc _ n => Loc new_file (n - old_line - 1 + new_line)
  | LocEof => LocEof
  end.

Definition remap_lines (old_line : Z) (new_file : string) (new_line : Z)
  (lines : list (list pp_tok)) : list (list pp_tok) :=
  map (map (fun t =>
    mkPpTok (ppt_val t) (remap_loc old_line new_file new_line (ppt_loc t))
      (ppt_space t) (ppt_hide t))) lines.

Definition parse_line_target (marker : list pp_tok) (hash_loc : c_loc)
  : option (string * Z) :=
  let base_file := match hash_loc with Loc f _ => f | LocEof => "" end in
  match marker with
  | tn :: rest =>
      match ppt_val tn with
      | PPTText s =>
          match parse_positive_dec s with
          | Some n =>
              match rest with
              | [] => Some (base_file, n)
              | _ =>
                  match parse_include_name rest with
                  | Some (nf, IncQuote) => Some (nf, n)
                  | _ => None
                  end
              end
          | None => None
          end
      | _ => None
      end
  | [] => None
  end.

(** ## Main file and line preprocessing loop *)

Fixpoint flatten_rev_lines (rev_lines : list (list pp_tok)) (acc : list pp_tok)
  : list pp_tok :=
  match rev_lines with
  | [] => acc
  | ln :: rest => flatten_rev_lines rest (app ln acc)
  end.

Fixpoint pp_lines_loop (fuel : nat) (lines : list (list pp_tok))
  (phys_file : string) (phys_id : string) (st : list cond_frame)
  (pending : list (list pp_tok)) (env : pp_env) (acc : list pp_tok) {struct fuel}
  : pp_step (list pp_tok * pp_env) :=
  match fuel with
  | O => PPDone (CErr "preprocessor line fuel exhausted")
  | S f =>
      let flush_pending (k : list pp_tok -> pp_env -> pp_step (list pp_tok * pp_env)) :=
        match pending with
        | [] => k acc env
        | _ =>
            let flat := flatten_rev_lines pending [] in
            pp_bind (expand_tokens flat env) (fun '(exp, env1) =>
              k (rev_append exp acc) env1)
        end in
      match lines with
      | [] =>
          match st with
          | [] => flush_pending (fun acc1 env1 => pp_ok (rev_append acc1 [], env1))
          | _ => pp_err (Loc phys_file 1) "unterminated #if"
          end
      | line :: more =>
          match line with
          | th :: directive =>
              match ppt_val th with
              | PPTText hs =>
                  if String.eqb hs "#" then
                    flush_pending (fun acc1 env1 =>
                      match directive with
                      | [] => pp_lines_loop f more phys_file phys_id st [] env1 acc1
                      | td :: args =>
                          match ppt_val td with
                          | PPTText dname =>
                              if String.eqb dname "line" && stack_active st then
                                pp_bind (expand_tokens args env1) (fun '(marker, env2) =>
                                  match parse_line_target marker (ppt_loc th) with
                                  | Some (nf, nn) =>
                                      let old_ln := match ppt_loc th with Loc _ l => l | LocEof => 0 end in
                                      let more' := remap_lines old_ln nf nn more in
                                      pp_lines_loop f more' phys_file phys_id st [] env2 acc1
                                  | None => pp_err (ppt_loc td) "bad #line directive"
                                  end)
                              else if is_cond_directive dname then
                                pp_bind (step_cond_stack dname (ppt_loc td) args env1 st)
                                  (fun '(st1, env2) =>
                                     pp_lines_loop f more phys_file phys_id st1 [] env2 acc1)
                              else if negb (stack_active st) then
                                pp_lines_loop f more phys_file phys_id st [] env1 acc1
                              else if String.eqb dname "define" then
                                match apply_define args (pp_macros env1) with
                                | Some ms1 =>
                                    pp_lines_loop f more phys_file phys_id st [] (set_macros env1 ms1) acc1
                                | None => pp_err (ppt_loc td) "bad #define directive"
                                end
                              else if String.eqb dname "undef" then
                                match args with
                                | [tn] =>
                                    match ppt_val tn with
                                    | PPTText nm =>
                                        let ms1 := smap_remove nm (pp_macros env1) in
                                        pp_lines_loop f more phys_file phys_id st [] (set_macros env1 ms1) acc1
                                    | _ => pp_err (ppt_loc td) "bad #undef directive"
                                    end
                                | _ => pp_err (ppt_loc td) "bad #undef directive"
                                end
                              else if String.eqb dname "include" || String.eqb dname "include_next" then
                                let is_next := String.eqb dname "include_next" in
                                let do_include (hname : string) (hform : include_form) (env2 : pp_env) :=
                                  let dirs := search_paths is_next phys_file (pp_dirs env2) in
                                  pp_bind (resolve_include_path hname hform phys_file dirs) (fun opath =>
                                    match opath with
                                    | None => pp_err (ppt_loc td) ("include_not_found(" ++ hname ++ ")")
                                    | Some inc_path =>
                                        pp_bind (pp_file_loop f inc_path env2) (fun '(inc_ts, env3) =>
                                          pp_lines_loop f more phys_file phys_id st [] env3 (rev_append inc_ts acc1))
                                    end) in
                                match parse_include_name args with
                                | Some (hname, hform) => do_include hname hform env1
                                | None =>
                                    pp_bind (expand_tokens args env1) (fun '(eargs, env2) =>
                                      match parse_include_name eargs with
                                      | Some (hname, hform) => do_include hname hform env2
                                      | None => pp_err (ppt_loc td) "bad #include operand"
                                      end)
                                end
                              else if String.eqb dname "pragma" then
                                match parse_pragma_weak args with
                                | Some (wnm, wtgt) =>
                                    let pt := mkPpTok (PPTPragmaWeak wnm wtgt) (ppt_loc td) true [] in
                                    pp_lines_loop f more phys_file phys_id st [] env1 (pt :: acc1)
                                | None =>
                                    match args with
                                    | tp :: _ =>
                                        match ppt_val tp with
                                        | PPTText ps =>
                                            if String.eqb ps "pack" then
                                              match parse_pragma_pack args with
                                              | Some op =>
                                                  let pt := mkPpTok (PPTPragmaPack op) (ppt_loc td) true [] in
                                                  pp_lines_loop f more phys_file phys_id st [] env1 (pt :: acc1)
                                              | None => pp_err (ppt_loc td) "this #pragma pack is not supported"
                                              end
                                            else if String.eqb ps "once" && Nat.eqb (List.length args) 1 then
                                              pp_lines_loop f more phys_file phys_id st [] (add_once env1 phys_id) acc1
                                            else if String.eqb ps "push_macro" || String.eqb ps "pop_macro" then
                                              match args with
                                              | [_; tlp; tstr; trp] =>
                                                  match ppt_val tlp, ppt_val trp, parse_include_name [tstr] with
                                                  | PPTText lp, PPTText rp, Some (mnm, IncQuote) =>
                                                      if String.eqb lp "(" && String.eqb rp ")" then
                                                        let env2 := apply_macro_stack (String.eqb ps "push_macro") mnm env1 in
                                                        pp_lines_loop f more phys_file phys_id st [] env2 acc1
                                                      else pp_lines_loop f more phys_file phys_id st [] env1 acc1
                                                  | _, _, _ => pp_lines_loop f more phys_file phys_id st [] env1 acc1
                                                  end
                                              | _ => pp_lines_loop f more phys_file phys_id st [] env1 acc1
                                              end
                                            else pp_lines_loop f more phys_file phys_id st [] env1 acc1
                                        | _ => pp_lines_loop f more phys_file phys_id st [] env1 acc1
                                        end
                                    | [] => pp_lines_loop f more phys_file phys_id st [] env1 acc1
                                    end
                                end
                              else if String.eqb dname "error" then
                                pp_err (ppt_loc td) "error_directive"
                              else if String.eqb dname "ident" then
                                pp_lines_loop f more phys_file phys_id st [] env1 acc1
                              else
                                pp_err (ppt_loc td) ("unsupported_directive(" ++ dname ++ ")")
                          | _ => pp_lines_loop f more phys_file phys_id st [] env1 acc1
                          end
                      end)
                  else
                    let pending1 := if stack_active st then line :: pending else pending in
                    pp_lines_loop f more phys_file phys_id st pending1 env acc
              | _ =>
                  let pending1 := if stack_active st then line :: pending else pending in
                  pp_lines_loop f more phys_file phys_id st pending1 env acc
              end
          | [] =>
              let pending1 := if stack_active st then line :: pending else pending in
              pp_lines_loop f more phys_file phys_id st pending1 env acc
          end
      end
  end

with pp_file_loop (fuel : nat) (file : string) (env0 : pp_env) {struct fuel}
  : pp_step (list pp_tok * pp_env) :=
  match fuel with
  | O => PPDone (CErr "preprocessor include fuel exhausted")
  | S f =>
      PPRealPath file (fun identity =>
        if str_in identity (pp_once env0) then pp_ok ([], env0)
        else
          let includer := pp_file env0 in
          let run_raw (raw : list pp_raw) (env1 : pp_env) :=
            let lines := token_lines raw in
            pp_bind (pp_lines_loop f lines file identity [] [] (with_file env1 file) [])
              (fun '(ts, env2) => pp_ok (ts, with_file env2 includer)) in
          match smap_find file (pp_cache env0) with
          | Some raw => run_raw raw env0
          | None =>
              PPReadFile file (fun ocs =>
                match ocs with
                | None => pp_err (Loc file 1) "cannot read file"
                | Some cs =>
                    match source_tokens cs (Loc file 1) with
                    | CErr m => PPDone (CErr m)
                    | COk raw => run_raw raw (add_cache env0 file raw)
                    end
                end)
          end)
  end.

(** ## Final lexing from preprocessing tokens to C tokens *)

Fixpoint lex_pp_tokens_loop (ts : list pp_tok) (acc : list token)
  : c_result (list token) :=
  match ts with
  | [] => COk (pack_tokens (rev_append acc []))
  | t :: rest =>
      let loc := ppt_loc t in
      match ppt_val t with
      | PPTPragmaWeak nm tgt =>
          lex_pp_tokens_loop rest (mkTok (TPragmaWeak nm tgt) loc :: acc)
      | PPTPragmaPack op =>
          lex_pp_tokens_loop rest (mkTok (TPragmaPack op) loc :: acc)
      | PPTText s =>
          match lex_chars "<preprocessing token>" (list_ascii_of_string s) with
          | CErr m => CErr m
          | COk lexed =>
              let reloc := map (fun tk => mkTok (tok_val tk) loc) lexed in
              lex_pp_tokens_loop rest (rev_append reloc acc)
          end
      end
  end.

(** ## Target profile helpers

    Parse clang's `-dM -E -x c /dev/null` macro dump and `-E -v -x c /dev/null`
    include search paths in pure Gallina, dropping `__SIZEOF_INT128__` and
    `__BITINT_MAXWIDTH__` to match c_pp.pl. *)

Definition profile_define_line (ms : smap macro_def) (line : list pp_tok)
  : smap macro_def :=
  match line with
  | th :: td :: rest =>
      match ppt_val th, ppt_val td with
      | PPTText hs, PPTText ds =>
          if String.eqb hs "#" && String.eqb ds "define" then
            match rest with
            | tnm :: _ =>
                match ppt_val tnm with
                | PPTText nm =>
                    if String.eqb nm "__SIZEOF_INT128__" ||
                       String.eqb nm "__BITINT_MAXWIDTH__" then ms
                    else
                      match apply_define rest ms with
                      | Some ms1 => ms1
                      | None => ms
                      end
                | _ => ms
                end
            | [] => ms
            end
          else ms
      | _, _ => ms
      end
  | _ => ms
  end.

Definition parse_profile_defs (defs : list ascii) : smap macro_def :=
  match source_tokens defs (Loc "<built-in>" 1) with
  | COk raw => fold_left profile_define_line (token_lines raw) smap_empty
  | CErr _ => smap_empty
  end.

Fixpoint split_text_lines_acc (cs cur : list ascii) (acc : list string)
  : list string :=
  match cs with
  | [] =>
      match cur with
      | [] => rev_append acc []
      | _ => rev_append (string_of_rev cur :: acc) []
      end
  | c :: rest =>
      if is_nl c then split_text_lines_acc rest [] (string_of_rev cur :: acc)
      else split_text_lines_acc rest (c :: cur) acc
  end.

Definition parse_include_dirs (verbose_err : list ascii) : list string :=
  let lines := split_text_lines_acc verbose_err [] [] in
  let fix take_paths (ls acc : list string) : list string :=
    match ls with
    | l :: rest =>
        if starts_with " " l then
          let p := String.substring 1 (String.length l - 1) l in
          take_paths rest (p :: acc)
        else rev_append acc []
    | [] => rev_append acc []
    end in
  let fix find_start (ls : list string) : list string :=
    match ls with
    | [] => []
    | l :: rest =>
        if String.eqb l "#include <...> search starts here:" then take_paths rest []
        else find_start rest
    end in
  find_start lines.

(** Default batch of glibc feature queries matching c_pp.pl's `feature_names`. *)
Definition default_feature_queries : list (string * string) :=
  [ ("__has_attribute", "__nothrow__");
    ("__has_attribute", "__cold__");
    ("__has_attribute", "__malloc__");
    ("__has_attribute", "__alloc_align__");
    ("__has_attribute", "__pure__");
    ("__has_attribute", "__const__");
    ("__has_attribute", "__unused__");
    ("__has_attribute", "__used__");
    ("__has_attribute", "__deprecated__");
    ("__has_attribute", "__format_arg__");
    ("__has_attribute", "__format__");
    ("__has_attribute", "__nonnull__");
    ("__has_attribute", "__returns_nonnull__");
    ("__has_attribute", "__warn_unused_result__");
    ("__has_attribute", "__always_inline__");
    ("__has_attribute", "__artificial__");
    ("__has_attribute", "__indirect_return__");
    ("__has_builtin", "__builtin_expect");
    ("__has_builtin", "__builtin_FILE");
    ("__has_builtin", "__builtin_fclose");
    ("__has_extension", "__attribute_deprecated_with_message__");
    ("__has_extension", "c_generic_selections");
    ("__has_feature", "modules");
    ("__building_module", "_Builtin_stddef") ].

Definition make_pp_env (defs_text : list ascii) (dirs : list string)
  (features : list feature_entry) (file : string) : pp_env :=
  mkPpEnv (parse_profile_defs defs_text) smap_empty dirs features [] smap_empty file.

(** Add a command-line `-D NAME` or `-D NAME=VALUE` definition to [env]. *)
Definition add_cli_define (spec : string) (env : pp_env) : pp_env :=
  let cs := list_ascii_of_string spec in
  let fix split_eq (xs acc : list ascii) : list ascii * list ascii :=
    match xs with
    | [] => (rev_append acc [], ["1"%char])
    | c :: rest =>
        if Ascii.eqb c "="%char then (rev_append acc [], rest)
        else split_eq rest (c :: acc)
    end in
  let '(lhs_cs, val_cs) := split_eq cs [] in
  let line := app (list_ascii_of_string "#define ") (app lhs_cs (" "%char :: val_cs)) in
  match source_tokens line (Loc "<command-line>" 1) with
  | COk raw =>
      let ms := fold_left profile_define_line (token_lines raw) (pp_macros env) in
      set_macros env ms
  | CErr _ => env
  end.

Definition prepend_include_dirs (dirs : list string) (env : pp_env) : pp_env :=
  mkPpEnv (pp_macros env) (pp_saved env) (app dirs (pp_dirs env))
          (pp_features env) (pp_once env) (pp_cache env) (pp_file env).

(** Preprocess [file] under [env] and lex the result into C tokens. *)
Definition preprocess_file (file : string) (env : pp_env) : pp_step (list token) :=
  let fuel := Z.to_nat 1000000 in
  pp_bind (pp_file_loop fuel file env) (fun '(pp_ts, _) =>
    PPDone (lex_pp_tokens_loop pp_ts [])).
