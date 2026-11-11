(** Run-time values, transcribed from interp.pl:
    [[capability|capabilities]], pointers and the [[word|words]] a
    [[temporary]] holds.

    ![[capability]]

    ## Words

    Values are a sum type over [[class|classes]] (formal.md's
    decision): well classedness is a boolean fact about a word, not an
    index of its type.

    | Gallina | interp.pl | Classes |
    |---|---|---|
    | `WInt n` | an integer | `w`, `l`; also `p`, an integer argument with no pointer term |
    | `WPtr p` | `ptr(Addr, Cap)` | `p`, `a`, `f` |
    | `WLimit c size` | `limit(Cap, Size)` | `l`: a limit's opaque snapshot |

    The integer at class `p` is interp.pl's defaulty case for main.pl's
    canonical arguments (`class_arg/2`): the model keeps it, and every
    operation that needs a pointer is stuck on it, as the interpreter
    fails there. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope Z_scope.

(** A [[capability]], what a pointer carries beside its address: which
    object, if any, it may access. An object's is its identity, the
    base of its region, and holds no bounds of its own. *)
Inductive cap : Type :=
| CNone (* `none`: no object, a null or forged pointer *)
| Obj (base : Z) (* `obj(Base)`: the writable object of identity base *)
| Ro (base : Z) (* `ro(Base)`: the read-only object of identity base *)
| Fn (f : name) (* `fn(F)`: the function f of the module *)
| External (n : name). (* `ext(N)`: the symbol n, defined outside the module *)

(** Equality of capabilities. *)
Definition cap_eqb (c c' : cap) : bool :=
  match c, c' with
  | CNone, CNone => true
  | Obj b, Obj b' | Ro b, Ro b' => Z.eqb b b'
  | Fn f, Fn f' | External f, External f' => name_eqb f f'
  | _, _ => false
  end.

(** As `ptr(Addr, Cap)`: a pointer, an address and its capability,
    which move together as one indivisible pair, the pair a [[flight]]
    builds. *)
Record ptr : Type := mkPtr { ptr_addr : Z; ptr_cap : cap }.

(** A [[word]], the value a temporary holds at run time; the table at
    the top of the page gives the classes each form is at. *)
Inductive word : Type :=
| WInt (n : Z) (* an integer, or a float's bit pattern *)
| WPtr (p : ptr) (* a pointer, or a proof of class `a` or `f` *)
| WLimit (c : cap) (size : Z). (* `limit(Cap, Size)`: a [[limit]]'s opaque snapshot *)

(** As `word_at_class(K, X0, X)`: the word x taken at class k. An
    integer is cut to the low 32, 64 or 80 bits of the class (a float
    word is its bit pattern, an integer); a pointer or proof word is
    itself, and a limit stays a limit at `l`. Any other mismatch is the
    interpreter's type error, here no word. *)
Definition word_at_class (k : class) (x : word) : option word :=
  match k, x with
  | W, WInt n => Some (WInt (n mod 2 ^ 32))
  | L, WInt n => Some (WInt (n mod 2 ^ 64))
  | L, WLimit _ _ => Some x
  | Single, WInt n => Some (WInt (n mod 2 ^ 32))
  | Double, WInt n => Some (WInt (n mod 2 ^ 64))
  | Extended, WInt n => Some (WInt (n mod 2 ^ 80))
  | (P | A | F), _ => Some x
  | _, _ => None
  end.

(** As `pointer_address(X, A)`: the address of a pointer word x, or the
    integer held at `p` itself; a limit has none. *)
Definition pointer_address (x : word) : option Z :=
  match x with
  | WPtr p => Some (ptr_addr p)
  | WInt n => Some n
  | WLimit _ _ => None
  end.
