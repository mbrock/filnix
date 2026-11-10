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

(** The lists of lines of a module, in the order `module_emit/4`
    gives them. Nothing if some item or thunk has none. *)
Definition module_lines (md : module) : option (list (list line)) :=
  let sy := module_symbols md in
  match all_some (item_lines sy) md, lower_thunks sy md with
  | Some items, Some ts => Some (items ++ map thunk_lines ts ++ [end_lines])
  | _, _ => None
  end.
