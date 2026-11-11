(** The programs of M2's gate (docs/lambda-anf.md), each a [Show.out]:
    CertiRocq's standalone programs (its tests/programs/tests.v, over
    its tests/lib), and tests of the Gallina backend's assembly
    printer (rocq/backend/Asm.v) and term order (rocq/backend/Order.v).
    Each is compiled twice: by CertiRocq's λANF and AnfLower.v to the
    arena (Tap.v), and by Rocq's extraction to OCaml (Ref.v). *)

From Stdlib Require Import List ZArith String Ascii Arith.
From Stdlib Require Import Strings.Byte.
From CertiRocq.Tests.lib Require Import vs Binom Color sha256.
From compcert.lib Require Integers.
From Nanofil Require Import Term.
From Backend Require Import Text Asm Order.
From AnfTests Require Import Show.
Import ListNotations.
Import VeriStar.

Local Open Scope nat_scope.

(** ## CertiRocq's tests/programs *)

Definition demo1 := List.app (List.repeat true 500) (List.repeat false 300).

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 := List.map negb (repeat2 true false 100).

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

Definition vs_easy := match vs.main with Valid => true | _ => false end.

Definition vs_hard := match vs.main_h with Valid => true | _ => false end.

Definition binom := Binom.main.

Definition color := Color.main.

Fixpoint loop_add n (f : Datatypes.unit -> nat) : nat :=
  match n with
  | 0 => f tt
  | S n => f tt + loop_add n f
  end.

Definition clos_loop (u : unit) : nat :=
  (fix list_add k1 k2 k3 l : nat :=
     match l with
     | [] => 0
     | x :: xs =>
       let clos z := k1 + k2 + k3 + z in
       (clos x) + list_add k1 k2 k3 xs
     end) 0 0 0 (List.repeat 0 1).

Definition clos := loop_add 1 clos_loop.

Definition addxy (x y w : nat) (l : list nat) :=
  let f := (fix aux l :=
     match l with
     | [] => []
     | z :: zs => (z + x + y + w) :: aux zs
     end) in
  f l.

Definition rec_clos := addxy 1 2 3 (List.repeat 0 (100 * 500)).

Definition intxy (x y w : nat) (l : list nat) :=
  let f := (fix aux l acc :=
     match l with
     | [] => acc
     | z :: zs => aux zs (z :: x :: y :: w :: acc)
     end) in
  f l [].

Definition rec_clos2 := intxy 1 2 3 (List.repeat 0 (100 * 500)).

Definition sha_input : string := ("Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching.")%string.

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes sha_input).

Definition demo1_out := show_list show_bool demo1.
Definition demo2_out := show_list show_bool demo2.
Definition list_sum_out := show_nat list_sum.
Definition vs_easy_out := show_bool vs_easy.
Definition vs_hard_out := show_bool vs_hard.
Definition binom_out := show_nat binom.
Definition color_out := show_pair show_Z show_Z color.
Definition clos_out := show_nat clos.
Definition rec_clos_out := show_list show_nat rec_clos.
Definition rec_clos2_out := show_list show_nat rec_clos2.
Definition sha_fast_out := show_list (fun b => show_Z (Integers.Byte.unsigned b)) sha_fast.

(** ## The Gallina backend's printer and order *)

Local Open Scope Z_scope.

(** The next state of a linear congruential generator. *)
Definition lcg (s : Z) : Z := (s * 1103515245 + 12345) mod 2147483648.

Definition atoms : list string := ["a"; "b"; "[]"; "foo"; "ab"; "Zed"; ""; "a b"]%string.

(** A term of depth at most fuel from the state s, and the next
    state. *)
Fixpoint gen_term (fuel : nat) (s : Z) : term * Z :=
  let s1 := lcg s in
  let k := (s1 / 65536) mod 6 in
  match fuel with
  | O => (TInt ((s1 / 256) mod 2001 - 1000), s1)
  | S f =>
      if k =? 0 then (TInt ((s1 / 256) mod 200001 - 100000), s1)
      else if k =? 1 then (TAtom (nth (Z.to_nat ((s1 / 256) mod 8)) atoms ""%string), s1)
      else if k =? 2 then
        let (a, s2) := gen_term f s1 in
        let (b, s3) := gen_term f s2 in
        (TApp (nth (Z.to_nat ((s1 / 256) mod 8)) atoms "f"%string) [a; b], s3)
      else if k =? 3 then
        let (a, s2) := gen_term f s1 in (TApp "g"%string [a], s2)
      else if k =? 4 then
        let (a, s2) := gen_term f s1 in
        let (b, s3) := gen_term f s2 in (TList [a; b], s3)
      else (TList [], s1)
  end.

(** n terms of depth at most 3 from the state s. *)
Fixpoint gen_terms (n : nat) (s : Z) (acc : list term) : list term :=
  match n with
  | O => acc
  | S n' => let (t, s') := gen_term 3 s in gen_terms n' s' (t :: acc)
  end.

(** A term as Prolog writes it, quotes aside. *)
Fixpoint show_term (t : term) : out :=
  match t with
  | TInt n => show_Z n
  | TAtom a => x27 :: of_string a ++ [x27]
  | TApp f args =>
      of_string f ++ x28 ::
        (fix go (l : list term) (first : bool) : out :=
           match l with
           | [] => [x29]
           | t' :: l' => (if first then [] else [x2c]) ++ show_term t' ++ go l' false
           end) args true
  | TList ts =>
      x5b ::
        (fix go (l : list term) (first : bool) : out :=
           match l with
           | [] => [x5d]
           | t' :: l' => (if first then [] else [x2c]) ++ show_term t' ++ go l' false
           end) ts true
  end.

Definition order_terms := gen_terms 1500 2026 [].

(** The terms in the standard order, as `msort/2` and as `sort/2`. *)
Definition order_out : out :=
  show_list show_term (Order.msort term_compare order_terms)
  ++ [x0a] ++ show_list show_term (Order.sort term_compare order_terms) ++ [x0a].

Section AsmLines.
Local Open Scope string_scope.

(** Some lines of each kind, with the integers of the state s. *)
Definition asm_lines (i : Z) : list line :=
  let s := lcg (lcg i) in
  let n := (s / 7) mod 100000000 - 50000000 in
  let l := LSym ("L" ++ decimal i)%string in
  [Label l;
   Ins "mov" (Some "q") [OMem (LInt n) "rbp"; OReg "rax"];
   Ins "lea" (Some "q") [ORip (EAdd (EAdd (ELit l) (ELit (LInt n))) (ELit (LInt 4))); OReg "rdi"];
   Ins "mov" (Some "l") [OMemIndex (LInt (i * 4)) "rax" "rcx"; OReg "edx"];
   Ins "call" None [OPlt (LSym "memcpy")];
   Ins "jmp" None [OInd (OReg "rax")];
   Ins "mov" (Some "q") [OFs (OGottpoff (LSym "tls")); OReg "r11"];
   Ins "add" (Some "q") [OImm (ELit (LInt n)); OReg "rsp"];
   Ins "mov" (Some "q") [OGotpcrel (LSym "g"); OReg "rax"];
   Ins "jne" None [OSym (ELit l)];
   Fixed (nth (Z.to_nat (i mod 7)) [Cpuid; Xgetbv; Rdtsc; Rdtscp; Lfence; Sfence; Pause] Pause);
   Dir (DSection (nth (Z.to_nat (i mod 8))
                      [SText; SData; SRodata; SBss; STbss; SDataRelRo; SNoteGnuStack;
                       SInit (Z.eqb (i mod 2) 0) (Some (LInt i))] SText));
   Dir (DP2align (LInt 4)); Dir (DGlobl l); Dir (DType l (LSym "function")); Dir (DSize l);
   Dir (DSizeOf l (LInt n)); Dir (DSet l (EAdd (ELit l) (ELit (LInt 8)))); Dir (DQuad (ELit (LInt n)));
   Dir (DLong (LInt n)); Dir (DByte (LInt 1) [LInt 2; LInt (n mod 256)]); Dir (DZero (LInt i));
   Dir (DAscii (app ["a"; """"; "\"; "010"; "200"]%char [Ascii.ascii_of_nat (Z.to_nat (i mod 256))]));
   Dir (DAsciz (LSym "x"))].

(** The text of 300 such groups, as Asm.v prints it. *)
Definition asm_out : out :=
  of_string (String.concat "" (lines_parts (flat_map asm_lines (map Z.of_nat (seq 0 300))))).

End AsmLines.
