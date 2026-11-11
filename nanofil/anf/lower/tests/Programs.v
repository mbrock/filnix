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

(** ## The represented integers, characters and strings

    M3's differential test (docs/lambda-anf.md): Z, N and positive
    operations on values across 2^30, 2^31, 2^32 and 2^64, nat and
    ascii operations, string operations, and Gallina functions that
    match on these types' constructors. The reference is not the OCaml
    extraction of [selftest_out] but [selftest_vm], its value computed
    by [vm_compute] in Rocq (Ref.v). *)

Section SelfTest.
Local Open Scope Z_scope.

Definition zvals : list Z :=
  [0; 1; -1; 2; 3; -7; 2^30 - 1; 2^30; -2^30; -2^30 - 1; 2^31 - 1; 2^31; -2^31; 2^32; 2^32 + 5;
   -2^32; 2^63 - 1; 2^64; -2^64 + 3; 2^64 + 2^32 + 7; 12345678901234567890123; -98765432109876543210].

Definition zops2 : list (Z -> Z -> Z) :=
  [Z.add; Z.sub; Z.mul; Z.max; Z.min; Z.div; Z.modulo; Z.quot; Z.rem; Z.land; Z.lor; Z.lxor].

Definition show_cmp (c : comparison) : out :=
  match c with Eq => [x3d] | Lt => [x3c] | Gt => [x3e] end.

(** Every binary operation on every pair, then the comparisons, a
    line each. *)
Definition z_pairs : list out :=
  flat_map (fun a => map (fun b =>
    show_list show_Z (map (fun f => f a b) zops2)
    ++ show_cmp (Z.compare a b) ++ show_bool (Z.eqb a b) ++ show_bool (Z.ltb a b) ++ show_bool (Z.leb a b)
    ++ show_pair show_Z show_Z (Z.div_eucl a b) ++ [x0a]) zvals) zvals.

Definition shifts : list Z := [-70; -33; -1; 0; 1; 5; 31; 32; 33; 64; 65].
Definition bits : list Z := [-1; 0; 1; 29; 30; 31; 32; 63; 64; 100].

Definition z_unary : list out :=
  map (fun a =>
    show_list show_Z [Z.succ a; Z.pred a; Z.opp a; Z.abs a; Z.of_N (Z.to_N a); Z.of_N (Z.abs_N a)]
    ++ show_list show_Z (map (Z.shiftl a) shifts) ++ show_list show_Z (map (Z.shiftr a) shifts)
    ++ show_list show_bool (map (Z.testbit a) bits) ++ show_bool (Z.even a) ++ show_bool (Z.odd a)
    ++ show_list show_Z (map (Z.pow a) [-1; 0; 1; 2; 3; 5]) ++ [x0a]) zvals.

(** The positive's bits, by matching on its constructors. *)
Fixpoint ones (p : positive) : nat :=
  match p with xI q => S (ones q) | xO q => ones q | xH => 1 end.

Definition sign (z : Z) : Z := match z with Z0 => 0 | Zpos _ => 1 | Zneg _ => -1 end.

(** The magnitude rebuilt from its bits, by constructors. *)
Fixpoint rebuild (p : positive) : positive :=
  match p with xI q => xI (rebuild q) | xO q => xO (rebuild q) | xH => xH end.

Definition z_match : list out :=
  map (fun a =>
    show_Z (sign a) ++ [x20] ++
    match a with
    | Zpos p | Zneg p => show_nat (ones p) ++ [x20] ++ show_Z (Zpos (rebuild p)) ++ [x20]
                          ++ show_Z (Zpos (Pos.add p p)) ++ [x20] ++ show_Z (Zpos (Pos.sub p 1))
                          ++ [x20] ++ show_Z (Zpos (Pos.pred p)) ++ [x20] ++ show_cmp (Pos.compare p 7)
    | Z0 => []
    end ++ [x0a]) zvals.

Definition nvals : list N := map Z.to_N (filter (fun z => 0 <=? z) zvals).

Definition n_pairs : list out :=
  flat_map (fun a => map (fun b =>
    show_list (fun n => show_Z (Z.of_N n))
      [N.add a b; N.sub a b; N.mul a b; N.div a b; N.modulo a b; N.land a b; N.lor a b; N.max a b]
    ++ show_cmp (N.compare a b) ++ show_bool (N.eqb a b) ++ show_bool (N.ltb a b)
    ++ match a with N0 => [x30] | Npos p => show_Z (Zpos p) end ++ [x0a]) nvals) nvals.

Local Open Scope nat_scope.

Definition natvals : list nat := [0; 1; 2; 7; 100; 255; 256; 1000; 4097].

Fixpoint sum_to (n : nat) : nat := match n with O => O | S m => n + sum_to m end.

Definition nat_tests : list out :=
  flat_map (fun a => map (fun b =>
    show_list show_nat [a + b; a - b; a * b; Nat.div a b; Nat.modulo a b; Nat.max a b; Nat.pred a]
    ++ show_bool (Nat.eqb a b) ++ show_bool (Nat.ltb a b) ++ show_cmp (Nat.compare a b) ++ [x0a]) natvals)
    natvals ++ [show_list show_nat (map sum_to natvals) ++ [x0a]].

Definition strs : list string :=
  ["";"a";"ab";"abc";"b";"hello, world";"hello";"hellp";"Zed";"a b";"€"]%string.

(** The string reversed, by its constructors. *)
Fixpoint srev (s acc : string) : string :=
  match s with EmptyString => acc | String c s' => srev s' (String c acc) end.

(** The characters' codes, by matching on the string and the ascii. *)
Fixpoint codes (s : string) : list nat :=
  match s with
  | EmptyString => []
  | String (Ascii b0 b1 _ _ _ _ _ b7 as c) s' =>
      (nat_of_ascii c + (if b0 then 1000 else 0) + (if b1 then 2000 else 0) + (if b7 then 4000 else 0))
        :: codes s'
  end.

(** A string long enough that its tails and substrings are slices of
    its bytes (anf_prims.c's SLICE_MIN), which [slice_tests] gets made
    at run time, so that no lowering folds what it tests. *)
Definition long : string :=
  "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"%string.

Definition slice_tests (l : string) : out :=
  let tl := match l with String _ t => t | EmptyString => l end in
  show_list show_bool [String.eqb (String.substring 1 70 l) (String.substring 1 70 l);
                       String.eqb (String.substring 1 70 l) l;
                       String.eqb tl (String.substring 1 71 l);
                       String.eqb (String.substring 0 64 l) (String.substring 0 64 l);
                       String.eqb (String.substring 1 64 l) (String.substring 2 64 l)]
  ++ show_cmp (String.compare tl l) ++ show_nat (String.length tl)
  ++ of_string (String.substring 60 5 tl) ++ [x0a].

Definition str_tests : list out :=
  flat_map (fun a => map (fun b =>
    of_string (String.append a (String.append "|" b)) ++ show_bool (String.eqb a b)
    ++ show_cmp (String.compare a b) ++ [x0a]) strs) strs
  ++ map (fun a =>
       of_string (srev a "") ++ [x20] ++ show_nat (String.length a) ++ [x20] ++ show_list show_nat (codes a)
       ++ [x20] ++ of_string (String.substring 1 2 a) ++ [x20]
       ++ of_string (string_of_list_ascii (rev (list_ascii_of_string a))) ++ [x0a]) strs
  ++ [of_string (String.concat ", " strs) ++ [x0a]
  ++ show_list (fun n => of_string (String (ascii_of_nat n) EmptyString)) [65; 97; 321; 48]
  ++ show_list show_bool (map (fun n => Ascii.eqb (ascii_of_nat n) "A"%char) [65; 66; 321])
  ++ show_list show_cmp (map (fun n => Ascii.compare (ascii_of_nat n) "M"%char) [65; 77; 200]) ++ [x0a]]
  ++ [slice_tests (srev (srev long "") "")].

(** The lines of the test. Each is short: [vm_compute]'s value of the
    whole output as one list would be a term too deep for Rocq. *)
Definition selftest_lines : list out := z_pairs ++ z_unary ++ z_match ++ n_pairs ++ nat_tests ++ str_tests.

Definition selftest_out : out := List.concat selftest_lines.

End SelfTest.

Definition selftest_vm_lines : list out := Eval vm_compute in selftest_lines.
Definition selftest_vm : out := List.concat selftest_vm_lines.
