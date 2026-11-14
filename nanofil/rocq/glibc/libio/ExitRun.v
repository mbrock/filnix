(** Triples for user glibc's `__run_exit_handlers` and `exit`
    (ExitRunCode.v), over user glibc's OS registry and world, for any
    genv that binds their symbols.

    `exit (status)` is `__run_exit_handlers (status, &__exit_funcs, 1,
    1)`. That takes the recursive `__exit_lock` for the thread whose
    cookie `zthread_self_cookie ()` returns (its count from 0 to 1, its
    owner from null to the cookie), runs `__call_tls_dtors ()`, takes
    `__exit_funcs_lock` (0 to 1) and enters ExitRunLoop.v's handler loop
    at `initial`, which pops the entries of AtexitLogic.v's
    [exit_funcs_inv] from the top, calls each handler, then calls
    `_IO_cleanup ()` and `zsys_exit_soft (status)`, which never
    returns. So both triples prove any postcondition:

    - [wp_glibc_run_exit_handlers]: from the frame of the call;
    - [wp_glibc_exit]: from `exit`'s frame, calling the first.

    `__call_tls_dtors` and `_IO_cleanup` are call rules the caller
    supplies ([dtors_rule], ExitRunTail.v's [cleanup_rule]), and each
    handler a triple ([exit_handler]) between the user resources R
    (S i) and R i. [exit_handler_void] gives that of a function of no
    parameters returning nothing, as `atexit` registers: `close_stdout`
    takes neither the null argument nor the status it is called with. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic MemLogic.
From Glibc Require Import GlibcLogic LeavesLogic AtexitLogic OsWorld OsExit OsThread OsRegistry ExitRunCode
  ExitRunTail ExitRunLoop.
From Glibc Require AtexitLogic ExitRunLoop ExitRunTail LeavesLogic OsExit OsThread OsWorld.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** The frame of a call of `__run_exit_handlers` on the status s, the
    list l and the flags a and d. *)
Lemma run_exit_frame s l a d :
  call_frame glibc___run_exit_handlers [WInt s; WPtr l; WInt a; WInt d] =
  Some (mkFrame glibc___run_exit_handlers [(TAtom "v6", WInt d); (TAtom "v4", WInt a); (TAtom "v2", WPtr l);
          (TAtom "v0", WInt s)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.


Import ExitRunLoop ExitRunTail ExitRunTail.L ExitRunTail.LG AtexitLogic.ML LeavesLogic AtexitLogic OsWorld OsExit OsThread.

Local Opaque glibc___run_exit_handlers glibc_exit.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv).
(** The Iris instance of user glibc's OS registry and world. *)
Local Instance exit_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** A function g of no parameters returning nothing, not variadic,
    whose frame fr runs from P to Q, registered with `atexit` as the
    entry (fn, null, dso): a handler. The call drops both arguments. *)
Lemma exit_handler_void status fnp dsop g gf fr P Q :
  ptr_cap fnp = Fn g -> function_check_res ge fnp = Some ok -> find_fn ge g = Some (Defined gf) ->
  0 <= ptr_addr fnp < 2 ^ 64 -> fn_params gf = [] -> fn_ret gf = RVoid -> variadic_func gf = false ->
  call_frame gf [] = Some fr ->
  (P -∗ WP (ERun fr : gexpr) {{ o, ⌜o = RetVoid⌝ ∗ Q }}) -∗ exit_handler w0 ge status (fnp, null, dsop) P Q.
Proof.
  intros Hc Hf Hg Ha Hp Hr Hv Hfr. iIntros "H". iExists g, gf, [], fr. iFrame "H". iPureIntro. cbn [fst snd].
  split; [exact Hc|]. split; [exact Hf|]. split; [exact Hg|]. split; [exact Ha|]. split; [cbn; lia|].
  split; [intros b; split; discriminate|]. split; [exact (handler_conv_void gf _ _ _ _ Hp Hr)|].
  rewrite Hv. exact Hfr.
Qed.

(** The call rule of `__call_tls_dtors ()` from P to Q: at any call
    site, the rest of the block runs with Q. *)
Definition dtors_rule (P Q : iProp Σ) : iProp Σ :=
  ∀ f e ls lab rest j (Ψ : outcome -> iProp Σ),
    P -∗ ▷ (Q -∗ WP (ERun (mkFrame f e ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
    WP (ERun (mkFrame f e ls None
         (Exec lab (Call CVoid (Global (TAtom "__GI___call_tls_dtors")) [] :: rest) j)) : gexpr) {{ Ψ }}.

(** The recursive lock `__exit_lock` at el, free: its lock word and
    count 0 and its owner null. *)
Definition exit_lock_free (el : Z) (elr : region) : iProp Σ :=
  live el elr ∗ bytes el 0 [0; 0; 0; 0] ∗ bytes el 4 [0; 0; 0; 0] ∗ pcell el 8 null.

(** What the start of `__run_exit_handlers` needs: `__exit_lock` at
    the nonzero, 8-aligned el, holding its 16 bytes, bound in the genv
    and ignored by the world interpretation, and `zthread_self_cookie`
    external with w0's cookie nonzero. *)
Definition exit_lock_env (el : Z) (elr : region) : Prop :=
  0 < el /\ el mod 8 = 0 /\ el + 16 <= r_end elr <= 2 ^ 64 /\
  lookup (TAtom "glibc_exit#__exit_lock") (ge_globals ge) = Some (mkPtr el (Obj el)) /\
  wi_ignores (os_wi w0) el (r_end elr) /\ 0 < ptr_addr (ow_self w0) < 2 ^ 64 /\
  find_fn ge (TAtom "zthread_self_cookie") = None /\ lookup (TAtom "zthread_self_cookie") (ge_globals ge) = None.

(** `__run_exit_handlers (status, &__exit_funcs, 1, 1)`, `initial`
    holding the entries ents and `__exit_lock` free: it runs the
    destructors from P to R (|ents|), each handler from the top, and
    `_IO_cleanup` from R 0, and ends the process: any postcondition. *)
Lemma wp_glibc_run_exit_handlers x el elr ents c status (P : iProp Σ) (R : nat -> iProp Σ) Φ :
  loop_env w0 ge x -> exit_lock_env el elr ->
  exit_funcs_inv x ents c -∗ exit_lock_free el elr -∗ P -∗ dtors_rule P (R (List.length ents)) -∗
  ([∗ list] i ↦ en ∈ ents, exit_handler w0 ge (status mod 2 ^ 32) en (R (S i)) (R i)) -∗
  cleanup_rule w0 ge (R 0%nat) -∗
  WP (ERun (mkFrame glibc___run_exit_handlers [(TAtom "v6", WInt 1); (TAtom "v4", WInt 1);
       (TAtom "v2", WPtr (mkPtr (xo_funcs x) (Obj (xo_funcs x)))); (TAtom "v0", WInt status)] [] None
       (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Henv (He0 & He8 & Hee & Hgel & Hwel & Hself & Hsf & Hsg). pose proof Henv as Henv'.
  destruct x as [lk lkr dn dnr cl clr fs fsr ib ibr].
  destruct Henv' as (Hlay & Hgl & Hwi & Hwdn & Hwfs & Hxf & Hxg).
  destruct Hlay as (Hl0 & Hl4 & Hle & Hd0 & Hde & Hc0 & Hce & Hf0 & Hf8 & Hfe & Hi0 & Hi8 & Hie).
  destruct Hgl as (Hglk & Hgdn & Hgcl & Hgfs). destruct Hwi as (Hwlk & Hwcl & Hwib).
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg]
    in *.
  iIntros "((%Hlen & %Hc) & Hll & Hlb & Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hblk) (Hel & Hek & Hen & Heo)
           HP HD Hhs HK".
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg].
  step.
  iApply wp_zthread_self_cookie; [reflexivity | exact Hsf | exact Hsg | lia |]. iNext.
  step_global Hgel. step.
  rule1 "Hel" ltac:(eapply wp_check_read; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 8 null elr with "Hel Heo []");
    [reflexivity | reflexivity | reflexivity | arith | arith | arith | done |]. nx. iIntros "Hel Heo _".
  step. step. step. (branch_symbolic; LeavesLogic.decide_branch). step.
  (* L13: take the lock word. *)
  step_global Hgel.
  rule1 "Hel" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hel" "Hek" ltac:(eapply wp_raw_cas_w; inst;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwel]). rewrite lock_take.
  step. (branch_symbolic; LeavesLogic.decide_branch). step. step. (branch_symbolic; LeavesLogic.decide_branch). step.
  (* L27: the owner is the cookie. *)
  step_global Hgel. step.
  rule1 "Hel" ltac:(eapply wp_check; inst; [reflexivity | vx | reflexivity | arith | arith | arith]).
  rule2 "Hel" "Heo" ltac:(eapply wp_raw_store_pointer; inst;
    [vx | reflexivity | reflexivity | arith | arith | ign Hwel]).
  step. step.
  (* L15: count one. *)
  step_global Hgel. step.
  rule1 "Hel" ltac:(eapply wp_check_read; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_sub_bytes_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 [0; 0; 0; 0] (WInt 0)
            (DfracOwn 1) (DfracOwn 1) with "Hel Hen");
    [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | arith |]. nx. iIntros "Hel Hen".
  step.
  rule1 "Hel" ltac:(eapply wp_renew; inst; [reflexivity | vx | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hel" "Hen" ltac:(eapply wp_raw_store_w; inst;
    [vx | vx | reflexivity | arith | reflexivity | ign Hwel]).
  step. (branch_symbolic; LeavesLogic.decide_branch). step.
  (* L55: the thread-local destructors. *)
  iApply ("HD" with "HP"). iNext. iIntros "HR". step. step.
  (* L57: take `__exit_funcs_lock`. *)
  step_global Hglk.
  rule1 "Hll" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hll" "Hlb" ltac:(eapply wp_raw_cas_w; inst;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwlk]). rewrite lock_take.
  step. (branch_symbolic; LeavesLogic.decide_branch). step. step. (branch_symbolic; LeavesLogic.decide_branch). step.
  (* L88: `cur` is `initial`. *)
  rule1 "Hfl" ltac:(eapply wp_check_read; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  iDestruct "Hblk" as "(Hil & Hblk)".
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (mkPtr ib (Obj ib)) ibr with "Hfl Hfc Hil");
    [reflexivity | vx | reflexivity | arith | arith | arith |]. nx. iIntros "Hfl Hfc Hil". cbn [live_cap].
  step. step. step. (branch_symbolic; LeavesLogic.decide_branch).
  iApply (exit_loop w0 ge (mkExitObjs lk lkr dn dnr cl clr fs fsr ib ibr) ents c status _ _ R
            with "[-HR Hhs HK] HR Hhs HK"); [exact Henv | |].
  { unfold loop_vars. cbn [xo_funcs xo_init]. repeat split; reflexivity. }
  rewrite /exit_held. cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg
    xo_init xo_init_reg].
  iSplit; [iPureIntro; split; [exact Hlen | exact Hc]|]. iFrame "Hll Hlb Hdl Hdb Hcl Hcc Hfl Hfc".
  rewrite /exit_block. iFrame "Hil Hblk".
Qed.

(** `exit (status)`, as [wp_glibc_run_exit_handlers] with `exit`'s
    call of it: the handlers see the status's 32 bits, and the process
    ends: any postcondition. *)
Lemma wp_glibc_exit x el elr ents c status (P : iProp Σ) (R : nat -> iProp Σ) Φ :
  loop_env w0 ge x -> exit_lock_env el elr ->
  find_fn ge (TAtom "__run_exit_handlers") = Some (Defined glibc___run_exit_handlers) ->
  exit_funcs_inv x ents c -∗ exit_lock_free el elr -∗ P -∗ dtors_rule P (R (List.length ents)) -∗
  ([∗ list] i ↦ en ∈ ents, exit_handler w0 ge (status mod 2 ^ 32) en (R (S i)) (R i)) -∗
  cleanup_rule w0 ge (R 0%nat) -∗
  WP (ERun (mkFrame glibc_exit [(TAtom "v0", WInt status)] [] None (Enter (TAtom "start") None)) : gexpr)
    {{ Φ }}.
Proof.
  intros Henv Hlk Hrun. pose proof Henv as (_ & (_ & _ & _ & Hgfs) & _).
  iIntros "Hinv Hlock HP HD Hhs HK". step. step_global Hgfs.
  eapply step_wand; [eapply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _
    [WInt (status mod 2 ^ 32); WPtr (mkPtr (xo_funcs x) (Obj (xo_funcs x))); WInt 1; WInt 1]); inst;
    [reflexivity | exact Hrun | apply run_exit_frame] |].
  iApply (wp_glibc_run_exit_handlers with "Hinv Hlock HP HD [Hhs] HK"); [exact Henv | exact Hlk |].
  rewrite Zmod_mod. iExact "Hhs".
Qed.

End rules.
