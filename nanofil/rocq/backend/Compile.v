(** # From an unchecked module to its lines

    As main.pl's `compile` command for a Fil-C module, without -O:
    the module is pizlonated (Pizlonate.v), read as the model's
    syntax (Transport.v), judged by the model's
    [[validator]] (Validate.v), and its lines are those of
    EmitModule.v. Nothing of Prolog is in the path; the gate
    (tests/compile.sh) holds the printed lines to those of
    `nanofil compile`.

    Two things the Prolog compiler does are not done here, so it
    refuses some modules that [compile] takes:

    - It runs `valid_module/1` on the module as written, before
      pizlonation. Here only the checked module is judged.
    - It checks the `context/2` items (provenance's records), which
      pizlonation drops here.

    The lines of a module both take are the same.

    [compile_promoted] is main.pl's `compile-promoted` command:
    before pizlonation the module is promoted (Promote.v) and its
    copies are propagated (Copy.v), and the emission selects its
    branches (Emit.v). The same gate, with COMMAND=compile-promoted,
    holds its lines to those of `nanofil compile-promoted`. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Validate ValidFast Transport.
From Backend Require Import Text Asm Pizlonate Copy Promote EmitModule Regs.
Import ListNotations.
Local Open Scope string_scope.

(** What becomes of a module. *)
Inductive compiled :=
| Refused (why : string)
    (** Not a valid module: the Prolog compiler refuses it too. *)
| Outside (why : string)
    (** A module this compiler does not take, though it may be
        valid. *)
| Pieces (ps : list (unit -> option (list (list line)))).
    (** Its lines, a piece at a time ([module_pieces]). A piece is
        nothing for a function the backend builds no plan for. *)

(** Whether the item is not a function, or is one named by an atom.
    ir.pl's validator takes any term as a name, and the Prolog
    emission throws at a function whose name is not an atom, since
    the name is also a string of the function's origin. *)
Definition func_named_by_atom (it : term) : bool :=
  match it with
  | TApp f [name; _; _; _; _] =>
      negb (String.eqb f "func") || match name with TAtom _ => true | _ => false end
  | _ => true
  end.

(** The lines of the unchecked Fil-C module m, its branches selected
    or not: pizlonated, read as the model's syntax, judged and
    emitted. Outside if it has a function outside the
    [[core-subset|core subset]], which the validator cannot judge. *)
Definition checked_lines (selected : bool) (m : term) : compiled :=
  match pizlonate_module m with
  | None => Refused "an item is not of the unchecked grammar"
  | Some checked =>
      match decode_module checked with
      | None => Refused "the checked module does not read back"
      | Some md =>
          match valid_fast md with
          | None => Outside "a function is outside the subset"
          | Some false => Refused "the checked module is not valid"
          | Some true => Pieces (module_code selected md)
          end
      end
  end.

(** The module m, as read, compiled. A plain module is outside: its
    backend (amd64.pl) is not ported.

    With promoted, as `optimize(passes([promote, copy]))` and
    `emit(stack, selected, call)`: the module is promoted
    (Promote.v), its copies are propagated (Copy.v), and its
    branches are selected (Emit.v). Whether the module is plain is
    asked of the module as read, as main.pl's `compile` asks it,
    since promotion can remove every pointer. *)
Definition compile_as (promoted : bool) (m : term) : compiled :=
  match m with
  | TApp f [TList items] =>
      if negb (String.eqb f "module") then Refused "not a module"
      else if negb (forallb func_named_by_atom items) then
        Refused "a function's name is not an atom"
      else if negb (module_filc items) then Outside "a plain module"
      else if promoted then
        match promote_module m with
        | None => Refused "promotion refuses the module"
        | Some m1 =>
            match copy_module m1 with
            | None => Refused "copy propagation refuses the module"
            | Some m2 => checked_lines true m2
            end
        end
      else checked_lines false m
  | _ => Refused "not a module"
  end.

(** As `nanofil compile` without -O. *)
Definition compile : term -> compiled := compile_as false.

(** With promotion, copy propagation and selected branches. *)
Definition compile_promoted : term -> compiled := compile_as true.

(** The lines of an unchecked Fil-C module compiled with whole-function
    register allocation and direct register selection (Regs.v). *)
Definition checked_lines_allocated (m : term) : compiled :=
  match pizlonate_module m with
  | None => Refused "an item is not of the unchecked grammar"
  | Some checked =>
      match decode_module checked with
      | None => Refused "the checked module does not read back"
      | Some md =>
          match valid_fast md with
          | None => Outside "a function is outside the subset"
          | Some false => Refused "the checked module is not valid"
          | Some true => Pieces (module_code_allocated md)
          end
      end
  end.

(** With promotion, copy propagation, selected branches and register
    allocation (`nanofil-backend compile-allocated`). *)
Definition compile_allocated (m : term) : compiled :=
  match m with
  | TApp f [TList items] =>
      if negb (String.eqb f "module") then Refused "not a module"
      else if negb (forallb func_named_by_atom items) then
        Refused "a function's name is not an atom"
      else if negb (module_filc items) then Outside "a plain module"
      else
        match promote_module m with
        | None => Refused "promotion refuses the module"
        | Some m1 =>
            match copy_module m1 with
            | None => Refused "copy propagation refuses the module"
            | Some m2 => checked_lines_allocated m2
            end
        end
  | _ => Refused "not a module"
  end.

(** A module of one function that returns its argument is taken, and
    one with no pointer and no outside call is plain. *)
Example compile_identity :
  match compile (TApp "module" [TList [TApp "func" [TAtom "f"; TAtom "export"; TAtom "p";
           TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "a"]]];
           TList [TApp "block" [TAtom "top"; TList []; TList [];
                                TApp "ret" [TApp "tmp" [TAtom "a"]]]]]]]) with
  | Pieces ps => Some (length ps)
  | _ => None
  end = Some 3%nat.
Proof. reflexivity. Qed.

Example compile_plain :
  compile (TApp "module" [TList [TApp "func" [TAtom "f"; TAtom "export"; TAtom "w";
           TList [TApp "param" [TAtom "w"; TApp "tmp" [TAtom "a"]]];
           TList [TApp "block" [TAtom "top"; TList []; TList [];
                                TApp "ret" [TApp "tmp" [TAtom "a"]]]]]]])
  = Outside "a plain module".
Proof. reflexivity. Qed.

(** A use with no definition is refused. *)
Example compile_undefined :
  compile (TApp "module" [TList [TApp "func" [TAtom "f"; TAtom "export"; TAtom "p";
           TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "a"]]];
           TList [TApp "block" [TAtom "top"; TList []; TList [];
                                TApp "ret" [TApp "tmp" [TAtom "b"]]]]]]])
  = Refused "the checked module is not valid".
Proof. reflexivity. Qed.

(** A function named by a term that is not an atom is refused. *)
Example compile_name :
  compile (TApp "module" [TList [TApp "func" [TApp "tmp" [TAtom "a"]; TAtom "export"; TAtom "p";
           TList [TApp "param" [TAtom "p"; TApp "tmp" [TAtom "a"]]];
           TList [TApp "block" [TAtom "top"; TList []; TList [];
                                TApp "ret" [TApp "tmp" [TAtom "a"]]]]]]])
  = Refused "a function's name is not an atom".
Proof. reflexivity. Qed.
