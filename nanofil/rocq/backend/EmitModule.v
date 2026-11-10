(** # The lines of a module

    As filc_amd64.pl's `module_emit/4` with every temporary in its
    stack slot: the lines of each item in order, then those of each
    weak thunk, then the end of the file. The gate (emit.sh) holds
    each list to the Prolog compiler's. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Text Asm Plan Abi Layout Emit EmitData EmitThunk.
Import ListNotations.
Local Open Scope list_scope.

(** The lines of an item. Nothing for a function the model keeps
    outside the core subset, or one the backend builds no plan for. *)
Definition item_lines (sy : symbols) (it : item) : option (list line) :=
  match it with
  | IFunc f => option_map function_lines (lower_function sy f)
  | IOutside _ _ => None
  | IData n lk align items => Some (data_lines n lk align items)
  | IAlias n lk target => Some (alias_lines sy n lk target)
  end.

(** The end of the file: the stack is not executable. *)
Definition end_lines : list line := [Dir (DSection SNoteGnuStack)].

(** A module's lists of lines, a piece at a time, in the order
    `module_emit/4` gives them: a piece for each item, one for all
    the weak thunks and one for the end of the file. A driver asks
    for a piece, prints its lists and drops them before it asks for
    the next, so the lines of a whole module are never all alive.
    A piece is nothing if its item or a thunk has no lines. *)
Definition module_pieces (md : module) : list (unit -> option (list (list line))) :=
  let sy := module_symbols md in
  map (fun it _ => option_map (fun ls => [ls]) (item_lines sy it)) md
  ++ [fun _ => option_map (map thunk_lines) (lower_thunks sy md);
      fun _ => Some [end_lines]].

(** The lists of lines of a module: every piece's. Nothing if some
    piece is nothing. *)
Definition module_lines (md : module) : option (list (list line)) :=
  option_map (@concat _) (all_some (fun piece => piece tt) (module_pieces md)).
