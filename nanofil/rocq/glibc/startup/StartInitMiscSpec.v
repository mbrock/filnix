(** A C program can ask for its own name through the variables
    `c: program_invocation_name` and
    `c: program_invocation_short_name`. glibc keeps them in the globals
    `c: __progname_full` and `c: __progname`, and error messages print
    the short one. Before `c: main` runs, the function `c: __init_misc`
    sets both from the first argument of the program. The full name is
    `c: argv[0]` itself. The short name is the part after the last
    slash, or all of `c: argv[0]` when it has no slash.

    This module states what a call of `c: __init_misc` needs and what
    it leaves behind, so that the proof of startup can use the call as
    one step. [StartInitMisc](StartInitMisc.v) proves the contract.

    ## What the call owns

    The call writes the two globals, so it owns them. It only reads
    the argument array and the string of the program name, so a share
    of each is enough, and the call gives the shares back. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic StringLogic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld StrrchrLogic.
From Glibc Require WordString.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L WordString.
Open Scope Z_scope.

(** The short name of a program starts one byte after the last slash
    of the name s at the pointer a. A name without a slash is its own
    short name. The search for the slash covers the terminating zero
    byte too, as `c: strrchr` does, and 47 is the code of the slash. *)
Definition short_name (a : ptr) (s : list Z) : ptr :=
  match last_byte 47 (s ++ [0]) with
  | Some t => ptr_add a (Z.of_nat t + 1)
  | None => a
  end.

(** This record holds the base and the region of each object that the
    call touches, except the string of the program name. *)
Record im_objs := {
  im_pn : Z; im_pnreg : region;   (* __progname *)
  im_pf : Z; im_pfreg : region;   (* __progname_full *)
  im_av : Z; im_avreg : region    (* the argument array *)
}.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The program names the two globals, and each one is an aligned
    pointer cell inside its object. The argument array is not at
    address zero, and its first slot is an aligned pointer cell too. *)
Definition im_ok (o : im_objs) : Prop :=
  lookup (TAtom "__progname") (ge_globals ge) = Some (mkPtr (im_pn o) (Obj (im_pn o))) /\
  lookup (TAtom "__progname_full") (ge_globals ge) = Some (mkPtr (im_pf o) (Obj (im_pf o))) /\
  im_pn o mod 8 = 0 /\ im_pn o + 8 <= r_end (im_pnreg o) /\
  im_pf o mod 8 = 0 /\ im_pf o + 8 <= r_end (im_pfreg o) /\
  0 < im_av o /\ im_av o mod 8 = 0 /\ im_av o + 8 <= r_end (im_avreg o).

(** This assertion owns the two globals. The short name is at x and
    the full name is at y. *)
Definition im_names (o : im_objs) (x y : ptr) : iProp Σ :=
  live (im_pn o) (im_pnreg o) ∗ pcell (im_pn o) 0 x ∗ live (im_pf o) (im_pfreg o) ∗ pcell (im_pf o) 0 y.

(** This assertion holds a share of what the call reads. The first
    slot of the argument array points at a, and the string s lies
    there. *)
Definition im_args (o : im_objs) (dq : dfrac) (a : ptr) (s : list Z) : iProp Σ :=
  liveq dq (im_av o) (im_avreg o) ∗ pcellq dq (im_av o) 0 a ∗ word_string dq a s.

(** A call of `c: __init_misc (argc, argv, envp)` sets the full name to
    `c: argv[0]` and the short name to the part after the last slash.
    It does not look at the count or at the environment. The two
    globals may hold any pointers before the call. *)
Definition init_misc_spec : fspec Σ :=
  FSpec (im_objs * dfrac * Z * ptr * ptr * list Z * ptr * ptr)
    (fun '(o, _, argc, envp, _, _, _, _) => [WInt argc; WPtr (mkPtr (im_av o) (Obj (im_av o))); WPtr envp])
    (fun '(o, dq, _, _, a, s, x, y) => ⌜im_ok o⌝ ∗ im_names o x y ∗ im_args o dq a s)%I
    (fun '(o, dq, _, _, a, s, _, _) r => ⌜r = RetVoid⌝ ∗ im_names o (short_name a s) a ∗ im_args o dq a s)%I.

End spec.
