From Glibc Require Import GlibcProgram.
(** Before `c: main` runs, glibc's `c: __libc_start_main` and the functions
    it calls make several libpizlo calls that no later code repeats. They
    record the thread descriptor as the thread's cookie, read the thread's
    kernel id and runtime handle, and register the handlers through which
    libpizlo sets `c: errno` and the `c: dlerror` message. This module
    defines their [[external call|contracts]] over [os_world] from
    [OsWorld](OsWorld.v). Their runtime behavior is tested against native
    Fil-C in [zsys-start.c](zsys-start.c).

    ## What libpizlo runs

    The cookie and handler calls store a pointer into a runtime global, as
    the pinned `libpas/src/libpas/filc_runtime.c` shows. Registering a
    handler a second time panics, and so does setting `c: errno` before
    any handler is registered.

    ```c
    void filc_native_zthread_set_self_cookie(filc_thread* my_thread, filc_ptr cookie_ptr)
    {
        filc_flight_ptr_store(my_thread, &my_thread->cookie_ptr, cookie_ptr);
    }

    void filc_native_zregister_sys_errno_handler(filc_thread* my_thread, filc_ptr errno_handler)
    {
        FILC_CHECK(filc_ptr_is_totally_null(filc_pizlonated_errno_handler),
                   NULL, "errno handler already registered.");
        filc_flight_ptr_store(my_thread, &filc_pizlonated_errno_handler, errno_handler);
    }
    ```

    The dlerror registration works the same way and checks on its own that
    it runs only once. The calls `c: zthread_self_id`, `c: zthread_self` and
    `c: zmake_setjmp_save_sigmask` read or set runtime state that the
    program cannot reach through memory. None of these calls writes,
    allocates or frees program memory, and none of them can set
    `c: errno`.

    ## How the world records startup

    Three of the calls change runtime state that later calls depend on,
    so the model records their effect in the OS world. Setting the cookie
    replaces [ow_self], and registering the dlerror handler sets
    [ow_dlerror]. Registering the errno handler sets [ow_errno] to the
    cell [ow_errno_cell], which is the `c: errno` variable that the
    image's handler stores to. The contract identifies that handler,
    `c: errno_handler` in `csu/libc-start.c`, by its function
    [[capability]]. A proof about one image then checks by computation
    that the handler's body stores its argument to that cell. The
    contracts require [ow_errno] and [ow_dlerror] to be unset before
    registration, and that requirement rules out the runtime's panic on a
    second registration. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
From Glibc Require Import OsBlocks OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## World updates

    The three world-changing calls each replace one field of [os_world].
    These functions build the updated world and keep every other field. *)

(** Setting the thread cookie to c replaces [ow_self] with c. *)
Definition with_self (w : os_world) (c : ptr) : os_world :=
  mkOsWorld (ow_errno w) c (ow_log_fd w) (ow_fds w) (ow_facts w) (ow_errno_cell w) (ow_dlerror w).

(** Registering the errno handler makes [ow_errno_cell] the cell that
    later failing system calls write. *)
Definition with_errno (w : os_world) : os_world :=
  mkOsWorld (Some (ow_errno_cell w)) (ow_self w) (ow_log_fd w) (ow_fds w) (ow_facts w) (ow_errno_cell w) (ow_dlerror w).

(** Registering the dlerror handler sets [ow_dlerror]. *)
Definition with_dlerror (w : os_world) : os_world :=
  mkOsWorld (ow_errno w) (ow_self w) (ow_log_fd w) (ow_fds w) (ow_facts w) (ow_errno_cell w) true.

(** ## Calls that only read runtime state

    A call that returns a value without touching memory or the world
    has a simple prefix and postcondition. The helper [quiet_contract]
    states them once for a return type, a call-site shape and a set of
    allowed returned words. *)

(** A quiet call allocates nothing, emits nothing, keeps memory and the
    world, and returns words that satisfy ok. *)
Definition quiet_contract (ret : ret_type) (abi : call_result -> list arg -> Prop)
    (pre : list word -> Prop) (ok : list word -> Prop) : contract os_world :=
  mkContract os_world ret abi (fun xs _ _ => pre xs)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun _ m w born trace ending m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w /\
       exists vs, ending = CallReturn vs /\ ok vs)
    (fun _ => False) (fun why => In why [ArgumentSize; ReturnSize]).

(** A call to `c: unsigned zthread_self_id(void)` returns the calling
    thread's kernel id, which the runtime asserts is nonzero. The contract
    [os_self_id_contract] allows every nonzero 32-bit value, because the
    model does not record the id. *)
Definition os_self_id_contract : contract os_world :=
  quiet_contract (RClass W) (fun r args => (r = CVoid \/ exists d, r = CResult d W) /\ args = [])
    (fun xs => xs = []) (fun vs => exists t, vs = [WInt t] /\ 0 < t < 2 ^ 32).

(** A call to `c: void *zthread_self(void)` returns a pointer to the
    runtime's thread object. That object is special: reading or writing
    a byte through the pointer panics. The contract [os_thread_self_contract]
    therefore returns some nonzero address with no capability, which the
    caller may store and compare but not dereference. *)
Definition os_thread_self_contract : contract os_world :=
  quiet_contract (RClass P) (fun r args => (r = CVoid \/ exists d, r = CResult d P) /\ args = [])
    (fun xs => xs = []) (fun vs => exists a, vs = [WPtr (mkPtr a CNone)] /\ 0 < a < 2 ^ 64).

(** A call to `c: zmake_setjmp_save_sigmask(save)` sets a runtime flag
    that only affects how a later `c: setjmp` saves the signal mask. The
    contract [os_setjmp_sigmask_contract] returns nothing and changes nothing
    the model observes. *)
Definition os_setjmp_sigmask_contract : contract os_world :=
  quiet_contract RVoid (fun r args => r = CVoid /\ exists a, args = [Arg W a])
    (fun xs => exists b, xs = [WInt b]) (fun vs => vs = []).

(** ## Setting the cookie and registering handlers

    Setting the cookie and registering a handler each change one piece of
    runtime state. Such a call keeps memory, allocates nothing and
    returns nothing. The helper [world_contract] states that shape once
    for a precondition and a world update. While such a call is still in
    progress, the world is either the old one or the new one. *)

(** A world-changing call with precondition pre ends in the world
    upd w. *)
Definition world_contract (pre : list word -> os_world -> Prop) (upd : list word -> os_world -> os_world)
    : contract os_world :=
  mkContract os_world RVoid (fun r args => r = CVoid /\ exists a, args = [Arg P a])
    (fun xs _ w => pre xs w)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun xs m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ (w' = w \/ w' = upd xs w))
    (fun xs m w born trace ending m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = upd xs w /\
       ending = CallReturn [])
    (fun _ => False) (fun why => In why [ArgumentSize]).

(** The cookie a call to `c: zthread_set_self_cookie` passes is its only
    argument. Any other argument list leaves the cookie unchanged. *)
Definition cookie_arg (xs : list word) (w : os_world) : ptr :=
  match xs with [WPtr c] => c | _ => ow_self w end.

(** A call to `c: zthread_set_self_cookie(c)` accepts any pointer, null
    included, and makes it the thread cookie. The contract
    [os_set_cookie_contract] replaces [ow_self] with c. *)
Definition os_set_cookie_contract : contract os_world :=
  world_contract (fun xs _ => exists c, xs = [WPtr c]) (fun xs w => with_self w (cookie_arg xs w)).

(** In the linked image, user glibc's `c: errno_handler` from
    `csu/libc-start.c` is the local function [errno_handler_name]. *)
Definition errno_handler_name : name := TAtom "glibc_libc_start#errno_handler".

(** This function is the body that the image must contain for the errno
    handler. It checks that 4 bytes of the global `c: __libc_errno` are
    writable, and it then stores its 32-bit argument at offset 0 of that
    global. A proof about one image checks by computation that the image
    defines [errno_handler_name] as exactly this function. It also checks
    that `c: __libc_errno` is the world's [ow_errno_cell]. Together those
    facts justify letting a failing system call write that cell. *)
Definition errno_handler_fn : func :=
  mkFunc errno_handler_name (TAtom "local") RVoid [(W, TAtom "v0")]
    [mkBlock (TAtom "start") []
       [Let (TAtom "v2") P Copy [Global (TAtom "__libc_errno")];
        Let (TAtom "chk0") A (Check 0 4 Write 1) [Tmp (TAtom "v2")];
        RawStore Ww 0 (Tmp (TAtom "v0")) (Tmp (TAtom "chk0"))]
       JRetVoid].

(** A call to `c: zregister_sys_errno_handler(h)` panics unless it is the
    first one. The contract [os_errno_register_contract] requires that no
    errno cell is registered yet and that h is the image's errno handler,
    and it registers [ow_errno_cell]. *)
Definition os_errno_register_contract : contract os_world :=
  world_contract (fun xs w => exists hp, xs = [WPtr hp] /\ ptr_cap hp = Fn errno_handler_name /\ ow_errno w = None)
    (fun _ w => with_errno w).

(** A call to `c: zregister_sys_dlerror_handler(h)` also panics unless it
    is the first one. The contract [os_dlerror_register_contract] requires
    that no dlerror handler is registered and that h is a function, and it
    sets [ow_dlerror]. *)
Definition os_dlerror_register_contract : contract os_world :=
  world_contract (fun xs w => exists hp n, xs = [WPtr hp] /\ ptr_cap hp = Fn n /\ ow_dlerror w = false)
    (fun _ w => with_dlerror w).

(** A second errno registration is refused, because the world records the
    first one in [ow_errno]. *)
Example errno_register_once xs w e :
  ow_errno w = Some e -> ~ contract_pre os_errno_register_contract xs (Memory.mkMem (fun _ => 0) [] (fun _ => CNone)) w.
Proof. intros He (hp & _ & _ & Hn). congruence. Qed.

(** A contract for a call that can set `c: errno` requires that some
    errno cell is registered. After the errno registration, the world
    records the image's cell in [ow_errno], so that requirement holds. *)
Example errno_register_sets w : ow_errno (with_errno w) = Some (ow_errno_cell w).
Proof. reflexivity. Qed.

(** ## Over a Logic instance

    A proof about a C caller needs a rule for each call, stated in the
    program logic. The three reading calls keep the world, so their rules
    run under the fixed world interpretation [os_wi] of
    [OsWorld](OsWorld.v). The world-changing calls need the startup
    interpretation, so their rules live in [OsStart](OsStart.v). *)

(** The rules below lift the reading contracts into
    [[weakest-precondition|weakest-precondition]] rules. *)
Import OsWorld OsWorld.L OsWorld.LG.

(** A returning quiet call keeps the world and returns words that satisfy
    its ok predicate. *)
Lemma quiet_returns ret abi pre ok r args xs s m w trace values s' m' w' :
  M.E.invoke (quiet_contract ret abi pre ok) r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ ok values.
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & _ & _ & -> & vs & He & Hok). injection He as ->. auto.
Qed.

Import ProgramAbbreviations.
Section rule.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** The model does not know which kernel id a thread gets. A call to
    `c: zthread_self_id` puts some nonzero 32-bit value t into the
    destination register, and the caller's proof must hold for every such
    t. *)
Lemma wp_zthread_self_id f e ls lab d rest j Φ :
  registry (TAtom "zthread_self_id") = Some os_self_id_contract ->
  find_fn ge (TAtom "zthread_self_id") = None ->
  lookup (TAtom "zthread_self_id") (ge_globals ge) = None ->
  ▷ (∀ t, ⌜0 < t < 2 ^ 32⌝ -∗ WP (ERun (mkFrame f (put d (WInt t) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zthread_self_id")) [] :: rest) j)) : zexpr) {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hdata. iIntros "HK".
  iApply (wp_os_call w0 _ _ _ _ _ _ _ _ _ _ _ _ [] [] True%I
            (fun vs => exists t, vs = [WInt t] /\ 0 < t < 2 ^ 32)
            with "[//] [] [HK]"); [done | done | done | exact Hreg | done | | | done | | |].
  - split; [right; eexists; reflexivity | reflexivity].
  - iIntros (σ) "_ _". iPureIntro. split; [reflexivity|]. split; [constructor | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (quiet_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_nil.
  - iNext. iIntros (vs (t & -> & Ht)) "_ _". iExists _. iSplit.
    + iPureIntro. cbn. rewrite Z.mod_small; [reflexivity|lia].
    + iApply ("HK" with "[%]"). exact Ht.
Qed.

(** Reading the runtime thread handle binds the destination to some
    nonzero address a with no capability. *)
Lemma wp_zthread_self f e ls lab d rest j Φ :
  registry (TAtom "zthread_self") = Some os_thread_self_contract ->
  find_fn ge (TAtom "zthread_self") = None ->
  lookup (TAtom "zthread_self") (ge_globals ge) = None ->
  ▷ (∀ a, ⌜0 < a < 2 ^ 64⌝ -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr a CNone)) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "zthread_self")) [] :: rest) j)) : zexpr) {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hdata. iIntros "HK".
  iApply (wp_os_call w0 _ _ _ _ _ _ _ _ _ _ _ _ [] [] True%I
            (fun vs => exists a, vs = [WPtr (mkPtr a CNone)] /\ 0 < a < 2 ^ 64)
            with "[//] [] [HK]"); [done | done | done | exact Hreg | done | | | done | | |].
  - split; [right; eexists; reflexivity | reflexivity].
  - iIntros (σ) "_ _". iPureIntro. split; [reflexivity|]. split; [constructor | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (quiet_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_nil.
  - iNext. iIntros (vs (a & -> & Ha)) "_ _". iExists _. iSplit; [done|].
    iApply ("HK" with "[%]"). exact Ha.
Qed.

(** Setting the setjmp signal-mask flag changes nothing the proof sees,
    so the caller continues with the same environment. *)
Lemma wp_zmake_setjmp_save_sigmask f e ls lab a rest j b Φ :
  registry (TAtom "zmake_setjmp_save_sigmask") = Some os_setjmp_sigmask_contract ->
  find_fn ge (TAtom "zmake_setjmp_save_sigmask") = None ->
  lookup (TAtom "zmake_setjmp_save_sigmask") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a] = Some [WInt b] ->
  ▷ WP (ERun (mkFrame f e ls None (Exec lab rest j)) : zexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zmake_setjmp_save_sigmask")) [Arg W a] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hdata Hx. iIntros "HK".
  iApply (wp_os_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ [] True%I (fun vs => vs = [])
            with "[//] [] [HK]"); [done | done | done | exact Hreg | exact Hx | | | done | | |].
  - split; [reflexivity | eexists; reflexivity].
  - iIntros (σ) "_ _". iPureIntro. split; [eexists; reflexivity|]. split; [constructor | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (quiet_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_nil.
  - iNext. iIntros (vs ->) "_ _". iExists _. iSplit; [done|]. iExact "HK".
Qed.

End rule.
