(** glibc remembers the arguments of the program in three globals.
    The count is in `c: __libc_argc`, the argument array is in
    `c: __libc_argv`, and the environment is in `c: __environ`, which
    `c: getenv` reads. The constructor `c: _init_first` fills the
    three globals in before `c: main` runs. It then calls
    `c: __init_misc`, which sets the two names of the program.

    This module states what a call of the constructor needs and what
    it leaves behind, so that the proof of startup can use the call as
    one step. [StartInitFirst](StartInitFirst.v) proves the contract.

    ## What the call owns

    The call writes the three globals, so it owns them. It also owns
    everything that `c: __init_misc` needs, which
    [StartInitMiscSpec](StartInitMiscSpec.v) lists, and it gives all
    of that back in the state that `c: __init_misc` leaves. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic StringLogic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld StartInitMiscSpec.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv.
Open Scope Z_scope.

(** This record holds the base and the region of each of the three
    globals. *)
Record if_objs := {
  if_ac : Z; if_acreg : region;   (* __libc_argc *)
  if_lv : Z; if_lvreg : region;   (* __libc_argv *)
  if_en : Z; if_enreg : region    (* __environ *)
}.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The program names the three globals. The count has room for four
    bytes, and the other two are aligned pointer cells. *)
Definition if_ok (f : if_objs) : Prop :=
  lookup (TAtom "__libc_argc") (ge_globals ge) = Some (mkPtr (if_ac f) (Obj (if_ac f))) /\
  lookup (TAtom "__libc_argv") (ge_globals ge) = Some (mkPtr (if_lv f) (Obj (if_lv f))) /\
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr (if_en f) (Obj (if_en f))) /\
  if_ac f + 4 <= r_end (if_acreg f) /\
  if_lv f mod 8 = 0 /\ if_lv f + 8 <= r_end (if_lvreg f) /\
  if_en f mod 8 = 0 /\ if_en f + 8 <= r_end (if_enreg f).

(** This assertion owns the lifetimes of the three globals. *)
Definition if_lives (f : if_objs) : iProp Σ :=
  live (if_ac f) (if_acreg f) ∗ live (if_lv f) (if_lvreg f) ∗ live (if_en f) (if_enreg f).

(** A call of `c: _init_first (argc, argv, envp)` stores its three
    arguments in the globals and sets the names of the program. The
    count is an `c: int`, so it must be below 2^32. The globals may
    hold anything before the call. *)
Definition init_first_spec : fspec Σ :=
  FSpec (if_objs * im_objs * dfrac * Z * ptr * ptr * list Z * ptr * ptr * ptr * ptr)
    (fun '(_, o, _, argc, envp, _, _, _, _, _, _) =>
       [WInt argc; WPtr (mkPtr (im_av o) (Obj (im_av o))); WPtr envp])
    (fun '(f, o, dq, argc, _, a, s, x, y, u, v) =>
       ⌜if_ok f /\ 0 <= argc < 2 ^ 32 /\ im_ok o⌝ ∗ if_lives f ∗
       (∃ xs, ⌜length xs = 4%nat⌝ ∗ bytes (if_ac f) 0 xs) ∗ pcell (if_lv f) 0 u ∗ pcell (if_en f) 0 v ∗
       im_names o x y ∗ im_args o dq a s)%I
    (fun '(f, o, dq, argc, envp, a, s, _, _, _, _) r =>
       ⌜r = RetVoid⌝ ∗ if_lives f ∗
       int_cell (if_ac f) 0 argc ∗ pcell (if_lv f) 0 (mkPtr (im_av o) (Obj (im_av o))) ∗ pcell (if_en f) 0 envp ∗
       im_names o (short_name a s) a ∗ im_args o dq a s)%I.

End spec.
