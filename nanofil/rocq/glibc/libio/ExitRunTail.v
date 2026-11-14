From Glibc Require Import GlibcProgram.
(** The definitions of the handler loop of user glibc's
    `__run_exit_handlers` (ExitRunCode.v's [glibc___run_exit_handlers])
    and the end of the function after it ([exit_tail]). ExitRunLoop.v
    proves the loop, and ExitRun.v enters it.

    The loop starts at the block L101 with the lock `__exit_funcs_lock`
    held, `__exit_funcs` holding `initial` (`cur`, v90), and `initial`
    holding the registrations ents of AtexitLogic.v's [exit_block]. Each
    pass pops the last entry: it lowers `idx`, marks the slot `ef_free`
    (0), reads the handler and its argument, releases the lock, calls
    the handler through the pointer as `fn (arg, status)`, takes the
    lock again and, since `__new_exitfn_called` is unchanged (the
    handler does not register; it owns no exit state), goes round. With
    no entry left it sets `__exit_funcs` to `initial`'s null `next`,
    finds the list empty, sets `__exit_funcs_done`, releases the lock,
    calls `_IO_cleanup ()` and ends the process with
    `zsys_exit_soft (status)`, which never returns.

    A handler is any function the pointer names whose call converts to
    a frame ([exit_handler]): a function of no parameters that `atexit`
    registers, such as `close_stdout`, is called with two arguments it
    does not take, which the generic convention drops
    ([handler_conv_void]). Its triple runs
    between the user resources R (S i) and R i, so the i-th handler
    from the top owns what the handlers above it left.
    `_IO_cleanup` is a call rule over R 0 ([cleanup_rule]). *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic MemLogic.
From Glibc Require Import GlibcLogic LeavesLogic AtexitLogic OsWorld OsExit OsRegistry ExitRunCode.
From Glibc Require AtexitLogic LeavesLogic OsExit OsWorld.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** The arguments of the call of an `ef_cxa` handler, at the block
    L279: its argument and the status. *)
Definition handler_args : list arg := [Arg P (Tmp (TAtom "v264")); Arg W (Tmp (TAtom "v0"))].

(** A function of no parameters returning nothing, called through a
    pointer with two arguments and no result, takes none of them: the
    generic convention drops the extra arguments and converts no
    result. *)
Lemma handler_conv_void gf a1 a2 x y :
  fn_params gf = [] -> fn_ret gf = RVoid ->
  indirect_call_conv gf CVoid [a1; a2] [x; y] = Some (Converted [] None).
Proof. intros Hp Hr. unfold indirect_call_conv. rewrite Hp Hr. reflexivity. Qed.

(** A temporary reads as the word the environment holds for it. *)
Lemma value_x_tmp ge e k n x : lookup n e = Some x -> value_x ge e k (Tmp n) = word_at_class k x.
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

(** Read a temporary of the abstract environment below a frame's puts
    by a hypothesis about it there, then compute the rest. *)
Ltac look H := repeat (rewrite lookup_after_put_other; [|reflexivity]); exact H.

(** The value premise of a step: by computation, or through [look]. *)



Module LG := LG0.
Module L := LG.L.
Import L LG AtexitLogic.ML LeavesLogic AtexitLogic OsWorld OsExit.

Local Opaque glibc___run_exit_handlers.

(** Close the instance premise a rule's eapply leaves. *)


(** One step whose premises reduce, by the instruction it runs, values
    read as [vx] does: a pure let, a flight, entering a block, or a
    goto. *)


(** A let copying the global s, bound to p in the genv by Hs. *)


(** A write's world premise, from [wi_ignores] H of its object, as
    AtexitLogic.v's. *)
Ltac ign H :=
  let m := fresh "m" in let wd := fresh "wd" in let h := fresh "h" in let Hw := fresh "Hw" in
  intros m wd h ? Hw;
  first [ refine (proj1 (H m wd h _ _ _ _ CNone _ _ _ Hw)); [lia | lia | ids]
        | refine (proj2 (H m wd h _ _ _ _ _ _ _ _ Hw)); [lia | lia | ids] ].

(** A compare-and-swap's world premise, the same. *)
Ltac cas_ign H := intros _; ign H.

(** A branch, its condition read as [vx] does and simplified. *)


Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv).
(** The Iris instance of user glibc's OS registry and world. *)
Local Instance exitrun_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** The handler en = (fn, arg, dso) of an `ef_cxa` entry, called with
    the status, from P to Q: fn is the exact address of the function
    gf; arg names no object, as `atexit`'s null does; the call through
    the pointer converts the two arguments to gf's frame fr, reading
    no result; and fr runs from P to a return of nothing with Q. *)
Definition exit_handler (status : Z) (en : ptr * ptr * ptr) (P Q : iProp Σ) : iProp Σ :=
  ∃ g gf ys fr,
    ⌜ptr_cap en.1.1 = Fn g /\ function_check_res ge en.1.1 = Some ok /\ find_fn ge g = Some (Defined gf) /\
     0 <= ptr_addr en.1.1 < 2 ^ 64 /\ 0 <= ptr_addr en.1.2 < 2 ^ 64 /\
     (forall b, ptr_cap en.1.2 <> Obj b /\ ptr_cap en.1.2 <> Ro b) /\
     indirect_call_conv gf CVoid handler_args [WPtr en.1.2; WInt status] = Some (Converted ys None) /\
     call_frame gf (ys ++ (if variadic_func gf then skipn (List.length (fn_params gf)) [WPtr en.1.2; WInt status]
                           else [])) = Some fr⌝ ∗
    (P -∗ WP (ERun fr : gexpr) {{ o, ⌜o = RetVoid⌝ ∗ Q }}).

(** The call rule of `_IO_cleanup ()` from P, its result an int: at any
    call site, the rest of the block runs with the result bound. *)
Definition cleanup_rule (P : iProp Σ) : iProp Σ :=
  ∀ f e ls lab d rest j (Ψ : outcome -> iProp Σ),
    P -∗ ▷ (∀ n, WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
    WP (ERun (mkFrame f e ls None
         (Exec lab (Call (CResult d W) (Global (TAtom "_IO_cleanup")) [] :: rest) j)) : gexpr) {{ Ψ }}.

(** The exit handler state while the loop holds the lock: as
    [exit_funcs_inv] with the lock taken (1). *)
Definition exit_held (x : exit_objs) (ents : list (ptr * ptr * ptr)) (c : Z) : iProp Σ :=
  ⌜(List.length ents <= 32)%nat /\ 0 <= c < 2 ^ 64⌝ ∗
  live (xo_lock x) (xo_lock_reg x) ∗ bytes (xo_lock x) 0 [1; 0; 0; 0] ∗
  live (xo_done x) (xo_done_reg x) ∗ ibyte (xo_done x) 0 0 ∗
  live (xo_called x) (xo_called_reg x) ∗ icell (xo_called x) 0 c ∗
  live (xo_funcs x) (xo_funcs_reg x) ∗ pcell (xo_funcs x) 0 (mkPtr (xo_init x) (Obj (xo_init x))) ∗
  exit_block (xo_init x) (xo_init_reg x) ents.

(** What the loop needs of the objects, the genv and the world: the
    exit state's layout, globals and [exit_wi], a world that ignores
    the writes to `__exit_funcs_done` and `__exit_funcs` too, and
    `zsys_exit_soft` external. *)
Definition loop_env (x : exit_objs) : Prop :=
  exit_layout x /\ exit_globals ge x /\ exit_wi (os_wi w0) x /\
  wi_ignores (os_wi w0) (xo_done x) (r_end (xo_done_reg x)) /\
  wi_ignores (os_wi w0) (xo_funcs x) (r_end (xo_funcs_reg x)) /\
  find_fn ge (TAtom "zsys_exit_soft") = None /\ lookup (TAtom "zsys_exit_soft") (ge_globals ge) = None.

(** The lookups the loop makes in the environment it starts with:
    the status v0, `&__exit_funcs` v2 and its check chk6, the flag
    `run_list_atexit` v4 (1), `cur` v90 (`initial`) and null's address
    v96. *)
Definition loop_vars (x : exit_objs) (status : Z) (e : list (name * word)) : Prop :=
  lookup (TAtom "v0") e = Some (WInt status) /\
  lookup (TAtom "v2") e = Some (WPtr (mkPtr (xo_funcs x) (Obj (xo_funcs x)))) /\
  lookup (TAtom "v4") e = Some (WInt 1) /\
  lookup (TAtom "chk6") e = Some (WPtr (mkPtr (xo_funcs x) (Obj (xo_funcs x)))) /\
  lookup (TAtom "v90") e = Some (WPtr (mkPtr (xo_init x) (Obj (xo_init x)))) /\
  lookup (TAtom "v96") e = Some (WInt 0).

(** The end, from L101 with no entry left: `__exit_funcs` becomes null,
    `__exit_funcs_done` 1, the lock is released, `_IO_cleanup ()` runs
    from P, and the process ends: any postcondition. *)
Lemma exit_tail x c status e from P Φ :
  loop_env x -> loop_vars x status e ->
  exit_held x [] c -∗ P -∗ cleanup_rule P -∗
  WP (ERun (mkFrame glibc___run_exit_handlers e [] None (Enter (TAtom "L101") from)) : gexpr) {{ Φ }}.
Proof.
  destruct x as [lk lkr dn dnr cl clr fs fsr ib ibr].
  intros (Hlay & Hgl & Hwi & Hwdn & Hwfs & Hxf & Hxg) (H0 & H2 & H4 & H6 & H90 & H96).
  destruct Hlay as (Hl0 & Hl4 & Hle & Hd0 & Hde & Hc0 & Hce & Hf0 & Hf8 & Hfe & Hi0 & Hi8 & Hie).
  destruct Hgl as (Hglk & Hgdn & Hgcl & Hgfs). destruct Hwi as (Hwlk & Hwcl & Hwib).
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg]
    in *.
  iIntros "((_ & %Hc) & Hll & Hlb & Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hil & Hnext & Hidx & _ & Hspares) HP HK".
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg
    List.length Z.of_nat].
  eapply step_wand; [eapply wp_enter; inst; [reflexivity | destruct from; reflexivity] |]; cbn [b_insts b_jump]. step.
  rule1 "Hil" ltac:(eapply wp_check_read; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hidx" ltac:(eapply wp_raw_load; inst; [reflexivity | reflexivity | reflexivity | arith]).
  step. (branch_symbolic; LeavesLogic.decide_branch). step.
  rule1 "Hil" ltac:(eapply wp_half_check_read; inst;
    [reflexivity | vx | reflexivity | left; reflexivity | arith | arith | arith | arith | arith]).
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 null ibr with "Hil Hnext []");
    [reflexivity | reflexivity | reflexivity | arith | arith | arith | done |]. nx. iIntros "Hil Hnext _".
  rule1 "Hfl" ltac:(eapply wp_renew; inst; [reflexivity | vx | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hfl" "Hfc" ltac:(eapply wp_raw_store_pointer; inst;
    [reflexivity | reflexivity | reflexivity | arith | arith | ign Hwfs]).
  rule1 "Hfl" ltac:(eapply wp_renew; inst; [reflexivity | vx | reflexivity | reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 null fsr with "Hfl Hfc []");
    [reflexivity | reflexivity | reflexivity | arith | arith | arith | done |]. nx. iIntros "Hfl Hfc _".
  step. step. (branch_symbolic; LeavesLogic.decide_branch). step.
  rule1 "Hfl" ltac:(eapply wp_check_read; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 null fsr with "Hfl Hfc []");
    [reflexivity | reflexivity | reflexivity | arith | arith | arith | done |]. nx. iIntros "Hfl Hfc _".
  step. step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step_global Hgdn.
  rule1 "Hdl" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hdl" "Hdb" ltac:(eapply wp_raw_store_byte; inst;
    [reflexivity | reflexivity | reflexivity | arith | ign Hwdn]).
  step_global Hglk.
  rule1 "Hll" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_sub_bytes_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 [1; 0; 0; 0] (WInt 1)
            (DfracOwn 1) (DfracOwn 1) with "Hll Hlb");
    [reflexivity | reflexivity | reflexivity | reflexivity | left; reflexivity | arith |]. nx. iIntros "Hll Hlb".
  step. step.
  rule1 "Hll" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hll" "Hlb" ltac:(eapply wp_raw_cas_w; inst;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwlk]). rewrite lock_release.
  step. (branch_symbolic; LeavesLogic.decide_branch). step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step. (branch_symbolic; LeavesLogic.decide_branch). step.
  iApply ("HK" with "HP"). iNext. iIntros (n). step. step.
  iApply program_call(wp_zsys_exit_soft (glibc_program := program_of w0 glibc_os_registry ge)); [reflexivity | exact Hxf | exact Hxg | vx].
Qed.

End rules.
