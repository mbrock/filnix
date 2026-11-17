(** The last thing that glibc's startup code does is to call `c: main`.
    It does so in the function `c: __libc_start_call_main`, which
    never returns. The function first records a place for thread
    cancellation to unwind to. It then calls `c: main` with the
    arguments of the program, and it passes the result to `c: exit`.

    This module states what a call of that function needs, so that the
    proof of startup can use the call as its last step.
    [StartCallMain](StartCallMain.v) proves the contract.

    ## The parts that each program supplies

    Every program has its own `c: main`, and the functions that
    `c: exit` runs differ from program to program too. So the contract
    does not fix either of them. It takes a contract for `c: main` and
    a precondition for `c: exit` as parameters, and each program
    supplies its own. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic StringLogic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv.
Open Scope Z_scope.

(** This record holds the address and the region of `c: __environ`,
    and the regions of the argument array and of the environment. *)
Record cm_objs := {
  cm_en : Z; cm_enreg : region;   (* __environ *)
  cm_avreg : region;              (* the argument array *)
  cm_evreg : region               (* the environment array *)
}.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## The end of the process

    A call of `c: exit` does not return. A contract for it therefore
    has a precondition for each status and a postcondition that
    nothing satisfies. *)
Definition exit_never_spec (E : Z -> iProp Σ) : fspec Σ :=
  FSpec Z (fun st => [WInt st]) E (fun _ _ => False)%I.

(** ## The call of main

    The startup code holds `c: main` as a function pointer, and it
    passes three arguments: the count, the argument array and the
    environment. A program may declare `c: main` with fewer
    parameters, and the call then drops the arguments that `c: main`
    does not take. These definitions say which words `c: main`
    receives. *)

(** The function named mn takes the words ys when it is called
    through a pointer with the three arguments of `c: main`. The call
    must not need to convert the result, because the caller reads it
    as the `c: int` that `c: main` returns. *)
Definition main_takes (mn : name) (ys : list word) (argc : Z) (argv envp : ptr) : Prop :=
  forall gf, find_fn ge mn = Some (Defined gf) ->
    variadic_func gf = false /\
    forall d a b c, indirect_call_conv gf (CResult d W) [Arg W a; Arg P b; Arg P c]
                      [WInt argc; WPtr argv; WPtr envp] = Some (Converted ys None).

(** ## What the call owns *)

(** This assertion owns the thread object as startup leaves it. The
    thread has no cleanup handler and no place to unwind to, and the
    four bytes of its cancellation state are zero. *)
Definition tcb_start (self : ptr) : iProp Σ :=
  ∃ tb treg, ⌜self = mkPtr tb (Obj tb) /\ 0 < tb /\ tb mod 8 = 0 /\
              tb + off_cancelhandling + 4 <= r_end treg /\ r_end treg <= 2 ^ 63⌝ ∗
    live tb treg ∗ pcell tb off_cleanup null ∗ pcell tb off_cleanup_jmp null ∗
    bytes tb off_cancelhandling [0; 0; 0; 0].

(** The function reads `c: __environ` to get the third argument of
    `c: main`, and it reloads the argument array's pointer from its
    own frame. This assertion holds a share of the global and of the
    two arrays' lives, which is enough for those loads. *)
Definition cm_reads (o : cm_objs) (dq : dfrac) (argv envp : ptr) : iProp Σ :=
  liveq dq (cm_en o) (cm_enreg o) ∗ pcellq dq (cm_en o) 0 envp ∗
  live_capq dq (ptr_cap argv) (cm_avreg o) ∗ live_capq dq (ptr_cap envp) (cm_evreg o).

(** These are the plain facts that a call needs. The first argument
    points to the function named mn, so the check before the call
    passes. The argument count fits in an `c: int`. The program has a
    global `c: __environ` that is one aligned pointer. The function
    named mn takes the three arguments of `c: main` as the words ys. *)
Definition cm_ok (mn : name) (ys : list word) (o : cm_objs) (mainp : ptr) (argc : Z) (argv envp : ptr) : Prop :=
  ptr_cap mainp = Fn mn /\ function_check_res ge mainp = Some ok /\ 0 <= ptr_addr mainp < 2 ^ 64 /\
  0 <= argc < 2 ^ 32 /\
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr (cm_en o) (Obj (cm_en o))) /\
  cm_en o mod 8 = 0 /\ cm_en o + 8 <= r_end (cm_enreg o) /\
  0 <= ptr_addr argv < 2 ^ 64 /\ 0 <= ptr_addr envp < 2 ^ 64 /\
  main_takes mn ys argc argv envp.

(** ## The contract *)

(** A call of `c: __libc_start_call_main (main, argc, argv)` does not
    return. The caller gives the thread object and the shares that the
    call reads. The caller also shows two things. First, `c: main` may
    be called once the thread has a place to unwind to. Second,
    whatever `c: main` returns is a status with which `c: exit` may be
    called. The status reaches `c: exit` as the `c: int` that
    `c: main` returned. *)
Definition start_call_main_spec (mn : name) (main_spec : fspec Σ) (E : Z -> iProp Σ) : fspec Σ :=
  FSpec (fs_binder main_spec * cm_objs * dfrac * ptr * Z * ptr * ptr)
    (fun '(_, _, _, mainp, argc, argv, _) => [WPtr mainp; WInt argc; WPtr argv])
    (fun '(x, o, dq, mainp, argc, argv, envp) =>
       ⌜cm_ok mn (fs_args main_spec x) o mainp argc argv envp⌝ ∗
       tcb_start (ow_self w0) ∗ cm_reads o dq argv envp ∗
       (tcb_cleanup_inv (ow_self w0) -∗ cm_reads o dq argv envp ==∗ fs_pre main_spec x) ∗
       (∀ r, fs_post main_spec x r -∗ ∃ st, ⌜r = Ret (WInt st) /\ 0 <= st < 2 ^ 32⌝ ∗ E st))%I
    (fun _ _ => False)%I.

End spec.
