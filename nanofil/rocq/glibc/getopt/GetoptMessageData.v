(** The getopt translation unit holds nine diagnostic format strings.
    These lists identify their symbols, bytes and read-only loader pieces. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Values Memory Pieces Heap.
From Glibc Require Import LiteralWords LiteralLogic.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The nine messages

    getopt prints a message when a user gives it an option it does not
    know or leaves out a required argument. Short options use two
    messages and long options use five, and an ambiguous long option also
    prints each candidate and then a newline. The byte lists below spell
    those nine strings without their terminators, as the getopt module's
    data holds them. *)

(** This is message 138, "%s: option '%s%s' is ambiguous\n". *)
Definition t138 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 32; 105; 115; 32;
   97; 109; 98; 105; 103; 117; 111; 117; 115; 10].

(** Message 139 is the heading that getopt prints before it lists the
    candidates of an ambiguous option. *)
Definition t139 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 32; 105; 115; 32;
   97; 109; 98; 105; 103; 117; 111; 117; 115; 59; 32; 112; 111; 115; 115; 105; 98; 105; 108; 105;
   116; 105; 101; 115; 58].

(** This is message 140, " '%s%s'". *)
Definition t140 : list Z :=
  [32; 39; 37; 115; 37; 115; 39].

(** This is message 141, "\n". *)
Definition t141 : list Z :=
  [10].

(** This is message 142, "%s: unrecognized option '%s%s'\n". *)
Definition t142 : list Z :=
  [37; 115; 58; 32; 117; 110; 114; 101; 99; 111; 103; 110; 105; 122; 101; 100; 32; 111; 112; 116;
   105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 10].

(** This is message 143, "%s: option '%s%s' doesn't allow an argument\n". *)
Definition t143 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 32; 100; 111; 101;
   115; 110; 39; 116; 32; 97; 108; 108; 111; 119; 32; 97; 110; 32; 97; 114; 103; 117; 109; 101;
   110; 116; 10].

(** This is message 144, "%s: option '%s%s' requires an argument\n". *)
Definition t144 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 32; 114; 101; 113;
   117; 105; 114; 101; 115; 32; 97; 110; 32; 97; 114; 103; 117; 109; 101; 110; 116; 10].

(** This is message 148, "%s: invalid option -- '%c'\n". *)
Definition t148 : list Z :=
  [37; 115; 58; 32; 105; 110; 118; 97; 108; 105; 100; 32; 111; 112; 116; 105; 111; 110; 32; 45; 45;
   32; 39; 37; 99; 39; 10].

(** This is message 149, "%s: option requires an argument -- '%c'\n". *)
Definition t149 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 114; 101; 113; 117; 105; 114; 101; 115; 32;
   97; 110; 32; 97; 114; 103; 117; 109; 101; 110; 116; 32; 45; 45; 32; 39; 37; 99; 39; 10].

(** These are the symbols of the nine strings, in the order of the texts
    below. *)
Definition dgx_msg_names : list string :=
  ["glibc_getopt#str.138"; "glibc_getopt#str.139"; "glibc_getopt#str.140"; "glibc_getopt#str.141";
   "glibc_getopt#str.142"; "glibc_getopt#str.143"; "glibc_getopt#str.144"; "glibc_getopt#str.148";
   "glibc_getopt#str.149"]%string.

(** These are the nine texts in the same order. *)
Definition dgx_msg_texts : list (list Z) := [t138; t139; t140; t141; t142; t143; t144; t148; t149].

(** Each text has checked words. *)
Lemma dgx_msg_texts_ok : Forall (fun s => lit_ok s = true) dgx_msg_texts.
Proof.
  assert (H : forallb lit_ok dgx_msg_texts = true) by (vm_compute; reflexivity).
  apply List.Forall_forall. intros s Hs. rewrite forallb_forall in H. exact (H s Hs).
Qed.

(** These are the pieces of the nine messages at the objects bs. *)
Definition dgx_msg_ps (bs : list (Z * region)) : list (piece * pval) := lits_ps bs dgx_msg_texts.

(** A symbol table places the messages at bs when each symbol names the
    read-only object at the matching base. *)
Definition dgx_msg_at (gs : list (name * ptr)) (bs : list (Z * region)) : Prop :=
  Forall2 (fun n br => Term.lookup (TAtom n) gs = Some (mkPtr br.1 (Ro br.1))) dgx_msg_names bs.
