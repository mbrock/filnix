(** Before `c: main` runs, startup calls each of the program's
    constructors, and the proof must know what each call does. The
    runner's contract therefore asks for a promise about every
    constructor it calls. This module gives that promise for the three
    constructors of hi_atexit, which are `c: _IO_stdfiles_init`,
    `c: check_stdfiles_vtables` and `c: _init_first`. Each promise comes
    from the constructor's own contract, through a lemma of
    [StartCtorRunner](StartCtorRunner.v).

    ## How the arguments line up

    The runner passes argc, argv and environ to every constructor. The
    first two constructors take no parameters, so the call drops all
    three arguments. `c: _init_first` takes all three, and the call
    passes them unchanged. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv LibioStdfiles StartCode StartCtorRunnerSpec StartCtorRunner
  StartStdfilesInitSpec StartCtorVtablesSpec StartInitMiscSpec StartInitFirstSpec StartInitFirst.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv.
Open Scope Z_scope.

Section calls.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A constructor that takes no parameters and returns nothing accepts
    the runner's three arguments by dropping them. *)
Lemma ctor_call_ok_void g s `{!HasSpec registry (os_wi w0) ge g s} gf x argc argv env Q :
  find_fn ge g = Some (Defined gf) -> fn_params gf = [] -> fn_ret gf = RVoid ->
  variadic_func gf = false -> fs_args s x = [] ->
  (forall v, fs_post s x v ⊢ ⌜v = RetVoid⌝ ∗ Q) ->
  ctor_call_ok g [WInt argc; WPtr argv; WPtr env] (fs_pre s x) Q.
Proof using Type.
  intros Hf Hp Hr Hv Ha HQ. eapply (ctor_call_ok_spec g s x _ gf []); [exact Hf | | | exact HQ].
  - rewrite /indirect_call_conv Hp Hr. reflexivity.
  - rewrite Hv Ha. reflexivity.
Qed.

(** The runner may call `c: _IO_stdfiles_init` with whatever its contract
    asks for, and it gets back what the contract gives, apart from the
    empty return value. *)
Lemma stdfiles_ctor_ok `{!HasSpec registry (os_wi w0) ge (TAtom "glibc_stdfiles#_IO_stdfiles_init") stdfiles_init_spec}
    `{!Defines ge "glibc_stdfiles#_IO_stdfiles_init" glibc_stdfiles_init} x argc argv env :
  ctor_call_ok (TAtom "glibc_stdfiles#_IO_stdfiles_init") [WInt argc; WPtr argv; WPtr env]
    (fs_pre stdfiles_init_spec x)
    (let '(fe, fo, fi, _, _, _, _, _, _) := x in
     io_list_inv ge [fe; fo; fi] ∗ [∗ list] f ∈ [fe; fo; fi], stream_live f)%I.
Proof using Type.
  destruct x as [[[[[[[[fe fo] fi] la] lareg] lk] lkreg] rf] rfreg].
  apply (ctor_call_ok_void _ stdfiles_init_spec glibc_stdfiles_init);
    [apply defines | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros v. reflexivity.
Qed.

(** `c: check_stdfiles_vtables` keeps the promise and gives back the
    shares it read. *)
Lemma vtables_ctor_ok `{!HasSpec registry (os_wi w0) ge (TAtom "glibc_vtables#check_stdfiles_vtables") check_vtables_spec}
    `{!Defines ge "glibc_vtables#check_stdfiles_vtables" start_check_vtables_fn} x argc argv env :
  ctor_call_ok (TAtom "glibc_vtables#check_stdfiles_vtables") [WInt argc; WPtr argv; WPtr env]
    (fs_pre check_vtables_spec x)
    (let '(fi, fireg, fo, foreg, fe, fereg, vb, vreg, dq) := x in
     vt_ok dq fi fireg vb ∗ vt_ok dq fo foreg vb ∗ vt_ok dq fe fereg vb ∗ liveq dq vb vreg)%I.
Proof using Type.
  destruct x as [[[[[[[[fi fireg] fo] foreg] fe] fereg] vb] vreg] dq].
  apply (ctor_call_ok_void _ check_vtables_spec start_check_vtables_fn);
    [apply defines | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros v. reflexivity.
Qed.

(** `c: _init_first` takes the runner's three arguments unchanged. The
    runner's argv must be the writable pointer to the base of the argv
    array that the contract names. *)
Lemma init_first_ctor_ok `{!HasSpec registry (os_wi w0) ge (TAtom "glibc_init_first#_init_first") init_first_spec}
    `{!Defines ge "glibc_init_first#_init_first" start_init_first_fn} x :
  let '(_, o, _, argc, envp, _, _, _, _, _, _) := x in
  ctor_call_ok (TAtom "glibc_init_first#_init_first")
    [WInt argc; WPtr (mkPtr (im_av o) (Obj (im_av o))); WPtr envp]
    (fs_pre init_first_spec x)
    (let '(f, o, dq, argc, envp, a, s, _, _, _, _) := x in
     if_lives f ∗ int_cell (if_ac f) 0 argc ∗ pcell (if_lv f) 0 (mkPtr (im_av o) (Obj (im_av o))) ∗
     pcell (if_en f) 0 envp ∗ im_names o (short_name a s) a ∗ im_args o dq a s)%I.
Proof using Type.
  destruct x as [[[[[[[[[[f o] dq] argc] envp] a] s] u1] u2] u3] u4].
  eapply (ctor_call_ok_spec _ init_first_spec _ _ start_init_first_fn); [apply defines | reflexivity | reflexivity |].
  intros v. reflexivity.
Qed.

End calls.
