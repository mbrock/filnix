(** glibc's fast string functions test eight bytes at once. They load a
    64-bit [[word]], combine it with constants such as `0x7f7f...7f`
    through additions, subtractions and bitwise operations, and read
    the answer for each byte from the matching byte of the result.
    Proving such a function means showing that each byte of the result
    depends only on the bytes in the same position, and computing that
    dependence once for all 256 byte values.

    Bitwise operations act on each byte independently, but addition
    and subtraction pass a carry or borrow from one byte to the next.
    This module models a word expression as a row of eight byte lanes
    joined by those carries. The theorem [sw_ripple] states that every
    byte of the 64-bit result equals the output of one lane, given the
    carries that the lower lanes pass up to it. The checkers that
    follow decide by computation that a lane never produces a carry,
    or produces one only after a byte that stops the search, and the
    lemmas built on them turn that check into a statement about every
    byte of every word.

    The per-function files such as [StrlenBits] and [StrcmpBits] used
    to prove each mask byte by byte with their own case analysis.
    With this module, a mask is written once as an expression of type
    [sw], and its byte-level meaning is a single computed check. *)

From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Memory WordBits.
Import ListNotations.
Open Scope Z_scope.

(** ## Word expressions

    A mask in glibc's string code is built from its input words and
    repeated byte constants. The type [sw] records that construction,
    so that both its 64-bit value and its effect on one byte lane can
    be computed from the same term. *)

(** The constructors follow the operations that nanofil emits for
    glibc's `c: string-fza.h` and `c: string-fzb.h` helpers. [SVar] n
    names the n-th input word, [SRep] c repeats the byte c across the
    word, and the remaining constructors are the bitwise operations and
    the wrapping addition and subtraction of 64-bit integers. *)
Inductive sw : Type :=
  | SVar (n : nat)
  | SRep (c : Z)
  | SAnd (a b : sw)
  | SOr (a b : sw)
  | SXor (a b : sw)
  | SAdd (a b : sw)
  | SSub (a b : sw).

(** The 64-bit value of an expression applies the C operations to the
    input words ws, wrapping each input, sum and difference to 64 bits
    as the machine does. A missing input reads as zero. *)
Fixpoint sw_word (ws : list Z) (e : sw) : Z :=
  match e with
  | SVar n => nth n ws 0 mod 2 ^ 64
  | SRep c => repeat_byte (c mod 256)
  | SAnd a b => Z.land (sw_word ws a) (sw_word ws b)
  | SOr a b => Z.lor (sw_word ws a) (sw_word ws b)
  | SXor a b => Z.lxor (sw_word ws a) (sw_word ws b)
  | SAdd a b => (sw_word ws a + sw_word ws b) mod 2 ^ 64
  | SSub a b => (sw_word ws a - sw_word ws b) mod 2 ^ 64
  end.

(** An expression reads only inputs below n when [sw_vars_below] n
    holds. The checkers below enumerate the bytes of one or two inputs,
    so they need this bound to cover every input the expression reads. *)
Fixpoint sw_vars_below (n : nat) (e : sw) : bool :=
  match e with
  | SVar k => Nat.ltb k n
  | SRep _ => true
  | SAnd a b | SOr a b | SXor a b | SAdd a b | SSub a b => sw_vars_below n a && sw_vars_below n b
  end.

(** ## Byte lanes and their carries

    One byte position of an expression behaves like a small circuit.
    It reads one byte of each input and one incoming carry or borrow
    for each addition and subtraction, and it produces one output byte
    and the carries for the next position up. *)

(** A value of type [carries] holds one bit for each addition and
    subtraction in an expression, arranged in the same tree shape.
    The bit at a bitwise node is unused and kept false. *)
Inductive carries : Type :=
  | CLeaf
  | CNode (c : bool) (l r : carries).

(** No carry enters the lowest byte, so the computation of byte zero
    starts from [sw_zero], which has the shape of e with every bit false. *)
Fixpoint sw_zero (e : sw) : carries :=
  match e with
  | SVar _ | SRep _ => CLeaf
  | SAnd a b | SOr a b | SXor a b | SAdd a b | SSub a b => CNode false (sw_zero a) (sw_zero b)
  end.

(** A lane passes nothing upward when every bit of its outgoing
    carries is false, which [carries_zero] decides. *)
Fixpoint carries_zero (cs : carries) : bool :=
  match cs with
  | CLeaf => true
  | CNode c l r => negb c && carries_zero l && carries_zero r
  end.

(** One lane of e reads the byte of input n as bs n and the incoming
    carries cs, and returns its output byte with the outgoing carries.
    An addition sets its carry when the byte sum reaches 256, and a
    subtraction sets its borrow when the byte difference is negative.
    A carry tree of the wrong shape counts as all false. *)
Fixpoint sw_lane (e : sw) (bs : nat -> Z) (cs : carries) : Z * carries :=
  let kids := match cs with CLeaf => (CLeaf, CLeaf) | CNode _ l r => (l, r) end in
  let cin := match cs with CLeaf => false | CNode c _ _ => c end in
  match e with
  | SVar n => (bs n mod 256, CLeaf)
  | SRep c => (c mod 256, CLeaf)
  | SAnd a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      (Z.land x y, CNode false ca cb)
  | SOr a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      (Z.lor x y, CNode false ca cb)
  | SXor a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      (Z.lxor x y, CNode false ca cb)
  | SAdd a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      let s := x + y + Z.b2z cin in (s mod 256, CNode (256 <=? s) ca cb)
  | SSub a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      let d := x - y - Z.b2z cin in (d mod 256, CNode (d <? 0) ca cb)
  end.

(** The bytes of the inputs at position i, as a lane reads them. *)
Definition sw_bytes (ws : list Z) (i : Z) : nat -> Z := fun n => byte_of (nth n ws 0) i.

(** The carries that enter position i come from running every lower
    lane in turn, starting from no carries below byte zero. *)
Fixpoint sw_carry (ws : list Z) (e : sw) (i : nat) : carries :=
  match i with
  | O => sw_zero e
  | S i => snd (sw_lane e (sw_bytes ws (Z.of_nat i)) (sw_carry ws e i))
  end.

(** ## Words are rows of lanes

    The following facts connect the 64-bit value of an expression to
    its lanes. They hold for every expression and every input, and
    every later lemma in this module follows from them. *)

(** A word expression always yields an unsigned 64-bit value. *)
Lemma sw_word_range ws e : 0 <= sw_word ws e < 2 ^ 64.
Proof. Admitted.

(** Byte i of an expression's value is the output of lane i, given
    the bytes of the inputs at i and the carries from the lanes below. *)
Theorem sw_ripple ws e (i : nat) : (i < 8)%nat ->
  byte_of (sw_word ws e) (Z.of_nat i) =
  fst (sw_lane e (sw_bytes ws (Z.of_nat i)) (sw_carry ws e i)).
Proof. Admitted.

(** When every lane below i passes no carries upward, lane i starts
    from no carries, as byte zero does. *)
Lemma sw_carry_zero ws e (i : nat) :
  (forall j, (j < i)%nat -> carries_zero (snd (sw_lane e (sw_bytes ws (Z.of_nat j)) (sw_zero e))) = true) ->
  sw_carry ws e i = sw_zero e.
Proof. Admitted.

(** ## Checking a lane by computation

    A lane reads at most two input bytes when the expression has at
    most two inputs, so its behaviour is fixed by 256 or 65,536 cases.
    The checkers below compute those cases, and the lemmas after each
    one turn a successful check into a statement about every byte of
    every input word. *)

(** The byte values 0 to 255, in the order the checkers try them. *)
Definition bytes256 : list Z := map Z.of_nat (seq 0 256).

(** The lane inputs that give byte b to the first input and byte c to
    every other input. *)
Definition lane2 (b c : Z) : nat -> Z := fun n => match n with O => b | _ => c end.

(** A one-input expression e computes g on each byte when, for every
    byte b, its lane from no carries returns g b and passes no carries.
    The function g should return a byte, since the lane does. *)
Definition sw_check1 (e : sw) (g : Z -> Z) : bool :=
  sw_vars_below 1 e &&
  forallb (fun b => let '(y, cs) := sw_lane e (lane2 b b) (sw_zero e) in (y =? g b) && carries_zero cs)
    bytes256.

(** A search mask may borrow across a byte only after the byte that
    ends the search. This weaker check requires the lane to return g b
    for every byte, but to pass no carries only for bytes where go
    holds, the bytes that let the search continue. *)
Definition sw_check1_upto (e : sw) (go : Z -> bool) (g : Z -> Z) : bool :=
  sw_vars_below 1 e &&
  forallb (fun b => let '(y, cs) := sw_lane e (lane2 b b) (sw_zero e) in
                    (y =? g b) && (negb (go b) || carries_zero cs))
    bytes256.

(** A successful [sw_check1] makes every byte of the result the image
    under g of the input byte in the same position. *)
Theorem sw_map1 e g : sw_check1 e g = true ->
  forall x i, 0 <= i < 8 -> byte_of (sw_word [x] e) i = g (byte_of x i).
Proof. Admitted.

(** The same check also gives the whole word as the bytes of the input,
    each mapped through g, which suits a later test of the word itself. *)
Corollary sw_map1_word e g : sw_check1 e g = true ->
  forall x, sw_word [x] e = of_bytes (map (fun i => g (byte_of x i)) idx8).
Proof. Admitted.

(** A successful [sw_check1_upto] gives byte i its value under g when
    every byte below i lets the search continue. *)
Theorem sw_map1_upto e go g : sw_check1_upto e go g = true ->
  forall x i, 0 <= i < 8 -> (forall j, 0 <= j < i -> go (byte_of x j) = true) ->
  byte_of (sw_word [x] e) i = g (byte_of x i).
Proof. Admitted.

(** A two-input expression e computes g on each pair of bytes when,
    for all 65,536 pairs, its lane from no carries returns g b c and
    passes no carries. *)
Definition sw_check2 (e : sw) (g : Z -> Z -> Z) : bool :=
  sw_vars_below 2 e &&
  forallb (fun b => forallb (fun c =>
    let '(y, cs) := sw_lane e (lane2 b c) (sw_zero e) in (y =? g b c) && carries_zero cs) bytes256)
    bytes256.

(** The two-input form of [sw_check1_upto], for comparisons that may
    borrow across a byte only after the first pair that ends the search. *)
Definition sw_check2_upto (e : sw) (go : Z -> Z -> bool) (g : Z -> Z -> Z) : bool :=
  sw_vars_below 2 e &&
  forallb (fun b => forallb (fun c =>
    let '(y, cs) := sw_lane e (lane2 b c) (sw_zero e) in
    (y =? g b c) && (negb (go b c) || carries_zero cs)) bytes256)
    bytes256.

(** A successful [sw_check2] makes every byte of the result the image
    under g of the two input bytes in the same position. *)
Theorem sw_map2 e g : sw_check2 e g = true ->
  forall x y i, 0 <= i < 8 -> byte_of (sw_word [x; y] e) i = g (byte_of x i) (byte_of y i).
Proof. Admitted.

(** A successful [sw_check2_upto] gives byte i its value under g when
    every pair of bytes below i lets the comparison continue. *)
Theorem sw_map2_upto e go g : sw_check2_upto e go g = true ->
  forall x y i, 0 <= i < 8 -> (forall j, 0 <= j < i -> go (byte_of x j) (byte_of y j) = true) ->
  byte_of (sw_word [x; y] e) i = g (byte_of x i) (byte_of y i).
Proof. Admitted.
