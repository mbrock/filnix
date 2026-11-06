(** Run-time values, transcribed from interp.pl: capabilities,
    pointers and the words a temporary holds.

    A capability is an identity, never bounds: `Obj base` names the
    object whose region has that base, and the region (Memory.v) says
    what its bounds are now. Every alias of an object shares that one
    region, so freeing through one alias empties the bounds the others
    see.

    ## Capabilities

    | Gallina | interp.pl | Names |
    |---|---|---|
    | `CNone` | `none` | no object: a null or forged pointer |
    | `Obj base` | `obj(Base)` | a writable object |
    | `Ro base` | `ro(Base)` | a read-only object |
    | `Fn f` | `fn(F)` | the function f of the module |
    | `External n` | `ext(N)` | the symbol n, defined outside the module |

    ## Words

    Values are a sum type over classes (formal.md's decision): well
    classedness is a boolean fact about a word, not an index of its
    type.

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

Inductive cap : Type :=
| CNone
| Obj (base : Z)
| Ro (base : Z)
| Fn (f : name)
| External (n : name).

Definition cap_eqb (c c' : cap) : bool :=
  match c, c' with
  | CNone, CNone => true
  | Obj b, Obj b' | Ro b, Ro b' => Z.eqb b b'
  | Fn f, Fn f' | External f, External f' => name_eqb f f'
  | _, _ => false
  end.

(** `ptr(Addr, Cap)`: the indivisible flight pair. *)
Record ptr : Type := mkPtr { ptr_addr : Z; ptr_cap : cap }.

Inductive word : Type :=
| WInt (n : Z)
| WPtr (p : ptr)
| WLimit (c : cap) (size : Z).

(** `word_at_class(K, X0, X)`: X is the word X0 taken at class K, its
    low bits(K) bits; a pointer or proof word is itself. A float word
    is its bit pattern, an integer. A limit stays a limit at `l`; any
    other mismatch is the interpreter's type error, here no word. *)
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

(** `pointer_address(X, A)`: a pointer word's address, or the integer
    held at `p` itself. *)
Definition pointer_address (x : word) : option Z :=
  match x with
  | WPtr p => Some (ptr_addr p)
  | WInt n => Some n
  | WLimit _ _ => None
  end.
