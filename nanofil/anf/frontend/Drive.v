(** The arena driver for the Gallina C frontend mirrors nanofil/anf/backend/Drive.v.
    It reads a file name and source pieces, runs CLex and CParse, and returns a
    chunked stream of canonical Prolog terms followed by an exit code and any
    diagnostic message. *)

From Stdlib Require Import String List Ascii ZArith Arith Bool.
From Frontend Require Import CAst CAttrs CLex CParse CCanon.
Import ListNotations.
Local Open Scope string_scope.

(** A streaming result matching nanofil/anf/backend/driver.c: either [Done]
    with an exit code and error message, or [Chunk] with string parts to print
    before invoking the continuation. *)
Inductive out : Type :=
| Done (code : nat) (why : string)
| Chunk (ps : list string) (next : unit -> out).

(** The command (`0` lex, `1` lex-c23, `2` parse, `3` parse-c23, `4` count),
    source file name for locations, and source text in 1 MB pieces. *)
Record args := mkargs {
  cmd : nat;
  filename : string;
  input : list string;
}.

Definition text_of (l : list string) : list ascii :=
  rev_append (fold_left (fun acc s => rev_append (list_ascii_of_string s) acc) l []) [].

Definition nl_str : string := string_of_rev ["010"%char].

Fixpoint stream_list {A : Type} (f : A -> list string -> list string)
  (first : bool) (xs : list A) : out :=
  match xs with
  | [] => Chunk ["]"; "."; nl_str] (fun _ => Done 0 "")
  | x :: rest =>
      let a0 := if first then ["["] else [","] in
      let ps := rev_append (f x a0) [] in
      Chunk ps (fun _ => stream_list f false rest)
  end.

Definition emit_list_stream {A : Type} (f : A -> list string -> list string)
  (xs : list A) : out :=
  match xs with
  | [] => Chunk ["[]."; nl_str] (fun _ => Done 0 "")
  | _ => stream_list f true xs
  end.

(** Run the selected frontend command on the given source text. *)
Definition run (a : args) : out :=
  let cs := text_of (input a) in
  match lex_chars (filename a) cs with
  | CErr msg => Done 1 ("lex error: " ++ msg)
  | COk ts0 =>
      let c := cmd a in
      let ts := if Nat.eqb c 1 || Nat.eqb c 3 then c23_tokens ts0 else ts0 in
      if Nat.eqb c 0 || Nat.eqb c 1 then
        emit_list_stream emit_token ts
      else
        match c_parse ts with
        | CErr msg => Done 1 ("parse error: " ++ msg)
        | COk items =>
            if Nat.eqb c 4 then
              let nt := z_to_string (Z.of_nat (List.length ts)) in
              let ni := z_to_string (Z.of_nat (List.length items)) in
              Chunk ["ok "; nt; " "; ni; nl_str] (fun _ => Done 0 "")
            else
              emit_list_stream emit_item items
        end
  end.
