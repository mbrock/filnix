(* Direct-style parser cursor, O(1) backtracking, contextual flags,
   and standard + dynamic operator precedence table. *)

open Ast

exception Fail

type op_table = (string, int * assoc) Hashtbl.t
type fold_table = (string, string) Hashtbl.t

type state = {
  toks : token array;
  len : int;
  mutable pos : int;
  mutable far : int;
  mutable no_at : bool;
  mutable in_if : bool;
  mutable in_pattern : bool;
  mutable in_notation_rhs : bool;
  ops : op_table;
}

let make_state ?(ops = Hashtbl.create 16) (toks : token array) : state =
  {
    toks;
    len = Array.length toks;
    pos = 0;
    far = 0;
    no_at = false;
    in_if = false;
    in_pattern = false;
    in_notation_rhs = false;
    ops;
  }

let clone_sub_state (p : state) (lo_idx : int) (hi_idx : int) : state =
  let sub = Array.sub p.toks lo_idx (hi_idx - lo_idx) in
  {
    toks = sub;
    len = Array.length sub;
    pos = 0;
    far = 0;
    no_at = p.no_at;
    in_if = p.in_if;
    in_pattern = p.in_pattern;
    in_notation_rhs = p.in_notation_rhs;
    ops = p.ops;
  }

let[@inline] at_end p = p.pos >= p.len

let[@inline] peek p = if p.pos < p.len then Some p.toks.(p.pos) else None

let[@inline] peek_kind p = if p.pos < p.len then Some p.toks.(p.pos).kind else None

let[@inline] peek2_kind p =
  if p.pos + 1 < p.len then Some (p.toks.(p.pos).kind, p.toks.(p.pos + 1).kind)
  else None

let[@inline] bump p =
  if p.pos >= p.len then raise Fail;
  let t = p.toks.(p.pos) in
  if t.lo > p.far then p.far <- t.lo;
  p.pos <- p.pos + 1;
  t

let[@inline] expect_tok p f =
  let t = bump p in
  match f t.kind with Some v -> (v, t) | None -> raise Fail

let[@inline] eat_id p s =
  let t = bump p in
  match t.kind with Id x when x = s -> t | _ -> raise Fail

let[@inline] eat_kw p s =
  let t = bump p in
  match t.kind with Kw x when x = s -> t | _ -> raise Fail

let[@inline] eat_sym p s =
  let t = bump p in
  match t.kind with Sym x when x = s -> t | _ -> raise Fail

let[@inline] eat_p p s =
  let t = bump p in
  match t.kind with P x when x = s -> t | _ -> raise Fail

let[@inline] eat_str p =
  let t = bump p in
  match t.kind with Str s -> (s, t) | _ -> raise Fail

let[@inline] eat_num p =
  let t = bump p in
  match t.kind with Num s -> (s, t) | _ -> raise Fail

let[@inline] eat_any_id p =
  let t = bump p in
  match t.kind with Id s -> (s, t) | _ -> raise Fail

let[@inline] eat_any_sym p =
  let t = bump p in
  match t.kind with Sym s -> (s, t) | _ -> raise Fail

(* O(1) zero-allocation backtracking: save and restore integer cursor! *)
let[@inline] try_ p f =
  let saved = p.pos in
  match f p with
  | v -> Some v
  | exception Fail ->
      p.pos <- saved;
      None

let rec first p = function
  | [] -> raise Fail
  | f :: fs ->
      let saved = p.pos in
      (match f p with
      | v -> v
      | exception Fail ->
          p.pos <- saved;
          first p fs)

let with_no_at p v f =
  let old = p.no_at in
  p.no_at <- v;
  Fun.protect ~finally:(fun () -> p.no_at <- old) (fun () -> f p)

let with_in_if p v f =
  let old = p.in_if in
  p.in_if <- v;
  Fun.protect ~finally:(fun () -> p.in_if <- old) (fun () -> f p)

let with_in_pattern p v f =
  let old = p.in_pattern in
  p.in_pattern <- v;
  Fun.protect ~finally:(fun () -> p.in_pattern <- old) (fun () -> f p)

let with_notation_rhs p v f =
  let old = p.in_notation_rhs in
  p.in_notation_rhs <- v;
  Fun.protect ~finally:(fun () -> p.in_notation_rhs <- old) (fun () -> f p)

let is_op_word = function "mod" -> true | _ -> false

let parse_name p =
  let x, t = eat_any_id p in
  if x = "_" then raise Fail;
  { n_span = { lo = t.lo; hi = t.hi }; n_text = x }

let parse_name_or_hole p =
  let x, t = eat_any_id p in
  if is_op_word x then raise Fail;
  { n_span = { lo = t.lo; hi = t.hi }; n_text = x }

let std_op = function
  | "<->" | "↔" -> Some (95, NonAssoc)
  | "⊢" | "-∗" | "==∗" -> Some (99, Right)
  | "⊣⊢" | "∗-∗" -> Some (95, NonAssoc)
  | "∗" -> Some (80, Right)
  | "<$>" -> Some (61, Left)
  | "$" -> Some (65, Right)
  | "∘" -> Some (40, Left)
  | "-d>" -> Some (99, Right)
  | "-n>" -> Some (45, Right)
  | "⋅" | "∪" -> Some (50, Left)
  | "∖" | "∩" -> Some (40, Left)
  | "!!" -> Some (20, NonAssoc)
  | "->" | "→" -> Some (99, Right)
  | "\\/" | "∨" -> Some (85, Right)
  | "/\\" | "∧" -> Some (80, Right)
  | "=" | "<>" | "≠" | "<" | "<=" | ">" | ">=" | "≤" | "≥"
  | "=?" | "<=?" | "<?" | ">=?" | ">?" | "==" | "=?="
  | "≡" | "≡ₚ" | "∈" | "∉" | "⊆" | "⊂" | "⊈" | "##" | "≼" | "~~>" ->
      Some (70, NonAssoc)
  | "::" | "++" -> Some (60, Right)
  | "+" | "-" | "||" -> Some (50, Left)
  | "*" | "/" | "÷" | "mod" | "&&" | "×" -> Some (40, Left)
  | "^" -> Some (30, Right)
  | _ -> None

let lookup_binop p op =
  match Hashtbl.find_opt p.ops op with Some _ as hit -> hit | None -> std_op op

let prefix_op = function
  | "~" | "¬" -> Some 75
  | "-" -> Some 35
  | "▷" | "□" | "◇" | "■" | "↑" | "●" | "◯" | "✓" -> Some 20
  | "!" -> Some 9
  | "£" -> Some 1
  | "⊢" | "|==>" -> Some 200
  | _ -> None

let matching_delim = function
  | "(" -> Some ")"
  | "[" -> Some "]"
  | "{" -> Some "}"
  | _ -> None

(* Forward hook for mutual recursion between terms (ltac:(...)) and tactics. *)
let parse_tactic_ref : (state -> tactic) ref = ref (fun _ -> raise Fail)
