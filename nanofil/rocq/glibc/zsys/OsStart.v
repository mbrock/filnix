(** The proofs of `c: main` and the glibc code it calls run under the world
    interpretation [os_wi] of [OsWorld](OsWorld.v), which pins the OS world
    to one value for the whole run. Startup cannot be proved that way,
    because `c: __libc_start_main` changes the world three times: it sets
    the thread cookie and registers the errno and dlerror handlers. This
    module defines the startup interpretation [os_wi_start], in which a
    [[ghost-state|ghost]] key decides those three parts of the world, and
    proves the rules for the three calls that change them.

    ## Two interpretations that agree under a key

    Startup passes through four OS worlds, and the proofs of the glibc
    code between the world changes should not have to be written twice.
    The ghost key holds the current cookie and the two registration flags.
    While the key holds fixed values, the startup interpretation accepts
    exactly the states that the fixed interpretation accepts for the
    matching world. For that reason the transport lemma of
    [WiTransport](../../theories/logic/WiTransport.v) runs every existing
    proof under [os_wi], unchanged, as one phase of startup or as the
    phase after it. Only the three world-changing calls need rules of
    their own, and each of them updates the key and the world together. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic WiTransport.
From Glibc Require Import OsBlocks OsWorld OsStartCalls.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The startup world

    A startup world differs from the final one only in the cookie and the
    two registration flags. The definitions below build it from a base
    world w0, whose remaining fields stay fixed for the whole run, and
    store the three varying parts in one ghost value. *)

(** This function builds the world that has cookie c, that has an errno
    handler registered when e is true, and that has a dlerror handler
    registered when d is true. It copies every other field from w0. *)
Definition start_world (w0 : os_world) (c : ptr) (e d : bool) : os_world :=
  mkOsWorld (if e then Some (ow_errno_cell w0) else None) c (ow_log_fd w0) (ow_fds w0) (ow_facts w0)
    (ow_errno_cell w0) d.

(** The ghost value records the cookie and the two flags, each flag as 0
    or 1. *)
Definition start_ghost (c : ptr) (e d : bool) : pval := VName c [Z.b2z e; Z.b2z d].

(** Two ghost values are equal only when their cookies and flags are. *)
Lemma start_ghost_inj c e d c' e' d' :
  start_ghost c e d = start_ghost c' e' d' -> c = c' /\ e = e' /\ d = d'.
Proof.
  intros [= -> He Hd]. split; [reflexivity|].
  split; [destruct e, e'; cbn in He; congruence | destruct d, d'; cbn in Hd; congruence].
Qed.

(** The proofs of `c: main` assume one fixed OS world w for the whole
    run. This lemma shows that startup ends in that world. Once both
    handlers are registered and the cookie is set, the startup world
    built over w equals w. *)
Lemma start_world_done w :
  ow_errno w = Some (ow_errno_cell w) -> ow_dlerror w = true -> start_world w (ow_self w) true true = w.
Proof. destruct w; cbn. intros -> ->. reflexivity. Qed.

(** A proof of startup must know the OS world at every point, but
    `c: __libc_start_main` changes the cookie and both handlers as it
    runs. This definition keeps the current cookie and flags under the
    key k. It accepts a state when [os_wi] accepts that state for the
    world those values describe. *)
Definition os_wi_start (w0 : os_world) (k : Z) (m : mem) (w : os_world) (h : gmap piece pval) : Prop :=
  exists c e d, h !! PName k = Some (start_ghost c e d) /\ os_wi (start_world w0 c e d) m w h.

(** Between two world-changing calls, startup code runs in one fixed
    world. When the key holds the cookie c and the flags e and d, the
    startup interpretation accepts exactly the states that [os_wi]
    accepts for the matching world. *)
Lemma os_wi_start_at w0 k c e d m w h :
  h !! PName k = Some (start_ghost c e d) ->
  os_wi_start w0 k m w h <-> os_wi (start_world w0 c e d) m w h.
Proof.
  intros Hk. split.
  - intros (c' & e' & d' & Hk' & Hw). rewrite Hk in Hk'. assert (Hg : start_ghost c e d = start_ghost c' e' d') by congruence.
    destruct (start_ghost_inj _ _ _ _ _ _ Hg) as (-> & -> & ->). exact Hw.
  - intros Hw. exists c, e, d. auto.
Qed.

(** Updating the key must not break the invariant that ties live objects
    to the ghost heap. Changing a ghost key leaves [os_inv] intact,
    because the invariant reads only liveness entries of the ghost heap. *)
Lemma os_inv_name m w h l v : os_inv m w h -> os_inv m w (<[PName l := v]> h).
Proof.
  intros (He & Hs & Hf). split; [|split; [exact Hs | exact Hf]].
  intros p Hp. destruct (He p Hp) as [Hp' Hg]. split; [exact Hp'|].
  intros reg E. rewrite lookup_insert_ne in E; [exact (Hg reg E) | discriminate].
Qed.

(** ## Over a Logic instance

    The rest of the module connects [os_wi_start] to the program logic.
    It shows that garbage collection preserves it, states the transport
    from [os_wi], and proves the rules for the three world-changing calls. *)

Module LG := LG0.
Module L := LG.L.
Import L LG.
Module WT := WiTransport R LG0.

(** Startup code can reach a garbage-collection [[poll|safepoint]], and
    the interpretation must still hold afterwards. A safepoint changes
    neither the ghost heap nor the world, and [os_wi] survives it, so
    [os_wi_start] survives it too. *)
Instance os_wi_start_stable w0 k : SafepointStable (os_wi_start w0 k).
Proof.
  split. intros s m s' m' w h Hsp (c & e & d & Hk & Hw).
  exists c, e, d. split; [exact Hk | exact (os_wi_safepoint _ _ _ _ _ _ _ Hsp Hw)].
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract os_world)) (ge : genv) (w0 : os_world) (k : Z).

Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation wp_os w := (@wp _ _ _ _ (@wp' _ _ _ (nanofil_irisGS registry (os_wi w) ge)) NotStuck ⊤).
Local Notation wp_start := (@wp _ _ _ _ (@wp' _ _ _ (nanofil_irisGS registry (os_wi_start w0 k) ge)) NotStuck ⊤).

(** This lemma lets a startup proof reuse a proof written for one fixed
    world. A proof under [os_wi] of the startup world for cookie c and
    flags e and d also holds under [os_wi_start], provided the caller
    lends the key holding those values. The key comes back with the
    result. *)
Lemma wp_start_of_os c e d dq (ex : sexpr) Φ :
  pointsto (PName k) dq (start_ghost c e d) -∗ wp_os (start_world w0 c e d) ex Φ -∗
  wp_start ex (fun o => pointsto (PName k) dq (start_ghost c e d) ∗ Φ o)%I.
Proof using Type.
  iApply WT.wp_wi_transport.
  - intros m w h Hk Hw. exact (proj1 (os_wi_start_at _ _ _ _ _ _ _ _ Hk) Hw).
  - intros m w h Hk Hw. exact (proj2 (os_wi_start_at _ _ _ _ _ _ _ _ Hk) Hw).
Qed.

(** Owning the key fixes the machine's current world. *)
Lemma start_heap_world σ c e d dq :
  heap_interp (os_wi_start w0 k) σ -∗ pointsto (PName k) dq (start_ghost c e d) -∗
  ⌜ls_world σ = start_world w0 c e d⌝.
Proof using Type.
  iIntros "Hσ Hk". iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (_ & _ & _ & Hw).
  iDestruct (gen_heap_valid with "Hh Hk") as %Hl.
  apply (os_wi_start_at _ _ _ _ _ _ _ _ Hl) in Hw. destruct Hw as [-> _]. done.
Qed.

Local Instance start_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi_start w0 k) ge.

(** Each of the three startup calls keeps memory, returns nothing and
    changes the world. Suppose the world before the call is the one for
    cookie c and flags e0 and d, and the call ends in the world for c', e1
    and d'. Then this lemma updates the key to match. The caller must show
    that the call's precondition holds and that the new world still
    satisfies [os_inv]. *)
Lemma wp_start_change f e ls lab r g args rest j spec xs c e0 d c' e1 d' (Q : iProp Σ) Φ :
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
  registry g = Some spec -> map_option (arg_x ge e) args = Some xs -> contract_abi spec r args ->
  (forall σ, heap_interp (os_wi_start w0 k) σ -∗ Q -∗
     ⌜contract_pre spec xs (ls_mem σ) (start_world w0 c e0 d)⌝) ->
  (forall s m trace values s' m' w',
     M.E.invoke spec r args xs s m (start_world w0 c e0 d) trace (CallReturn values) s' m' w' ->
     m' = m /\ w' = start_world w0 c' e1 d' /\ values = []) ->
  (forall h m, gen_heap_interp h -∗ Q -∗
     ⌜agrees m h -> os_inv m (start_world w0 c e0 d) h -> os_inv m (start_world w0 c' e1 d') h⌝) ->
  pointsto (PName k) (DfracOwn 1) (start_ghost c e0 d) -∗ Q -∗
  ▷ (pointsto (PName k) (DfracOwn 1) (start_ghost c' e1 d') -∗ Q -∗
       ∃ e', ⌜external_env spec (mkCallSite lab r g args rest j) [] e = Some e'⌝ ∗
         WP (ERun (mkFrame f e' ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfn Hdata Hfree Hreg Hx Habi Hpre Hret Hinv. iIntros "Hk HQ HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ spec xs (pointsto (PName k) (DfracOwn 1) (start_ghost c e0 d) ∗ Q)%I
            with "[$Hk $HQ] [HK]"); [done | done | done | done | exact Hx | exact Habi | |].
  - iIntros (σ) "Hσ [Hk HQ]". iDestruct (start_heap_world with "Hσ Hk") as %->.
    iApply (Hpre with "Hσ HQ").
  - iNext. iIntros (σ trace values s' m' w' Hi) "Hσ [Hk HQ]".
    iDestruct (start_heap_world with "Hσ Hk") as %Hw. rewrite Hw in Hi.
    destruct (Hret _ _ _ _ _ _ _ Hi) as (-> & -> & ->).
    iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (Ha & Hd & Hr & Hwi).
    iDestruct (gen_heap_valid with "Hh Hk") as %Hl.
    iDestruct (Hinv with "Hh HQ") as %Hn.
    apply (os_wi_start_at _ _ _ _ _ _ _ _ Hl) in Hwi. destruct Hwi as [_ Hi0]. rewrite Hw in Hi0.
    pose proof (M.E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ Hi Hr) as [Hr' _].
    iMod (gen_heap_update _ _ _ (start_ghost c' e1 d') with "Hh Hk") as "[Hh Hk]".
    iDestruct ("HK" with "Hk HQ") as (e') "[%He Hwp]".
    iModIntro. iExists e'. iSplit; [done|]. iFrame "Hwp". iExists _. iFrame "Hh". iPureIntro.
    cbn [ls_mem ls_rt ls_world]. split; [|split; [exact Hd | split; [exact Hr'|]]].
    + intros l v E. destruct (decide (l = PName k)) as [->|Hne].
      * rewrite lookup_insert_eq in E. injection E as <-. exact I.
      * rewrite lookup_insert_ne in E; [exact (Ha l v E) | congruence].
    + apply (os_wi_start_at _ _ _ _ _ _ _ _ (lookup_insert_eq _ _ _)).
      split; [reflexivity|]. apply os_inv_name. exact (Hn Ha Hi0).
Qed.

(** A returning world-changing contract keeps memory, returns nothing and
    ends in the updated world. *)
Lemma world_returns pre upd r args xs s m w trace values s' m' w' :
  M.E.invoke (world_contract pre upd) r args xs s m w trace (CallReturn values) s' m' w' ->
  m' = m /\ w' = upd xs w /\ values = [].
Proof using Type*.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & _ & -> & -> & He). injection He as ->. auto.
Qed.

(** Setting the cookie to a pointer into a live object b, or to a pointer
    without a capability, makes it the world's cookie. The caller lends a
    share of b's lifetime, which shows that b stays registered as [os_inv]
    requires. *)
Lemma wp_zthread_set_self_cookie_start f e ls lab a rest j c e0 d c' (Q : iProp Σ) Φ :
  registry (TAtom "zthread_set_self_cookie") = Some os_set_cookie_contract ->
  find_fn ge (TAtom "zthread_set_self_cookie") = None ->
  lookup (TAtom "zthread_set_self_cookie") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg P a] = Some [WPtr c'] ->
  (forall h m, gen_heap_interp h -∗ Q -∗ ⌜agrees m h -> self_registered m c'⌝) ->
  pointsto (PName k) (DfracOwn 1) (start_ghost c e0 d) -∗ Q -∗
  ▷ (pointsto (PName k) (DfracOwn 1) (start_ghost c' e0 d) -∗ Q -∗
       WP (ERun (mkFrame f e ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zthread_set_self_cookie")) [Arg P a] :: rest) j)) : sexpr)
    {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hdata Hx Hself. iIntros "Hk HQ HK".
  iApply (wp_start_change _ _ _ _ _ _ _ _ _ _ _ c e0 d c' e0 d Q with "Hk HQ [HK]");
    [done | done | done | exact Hreg | exact Hx | | | | | ].
  - split; [reflexivity | eexists; reflexivity].
  - iIntros (σ) "_ _". iPureIntro. eexists; reflexivity.
  - intros s m trace values s' m' w' Hi. destruct (world_returns _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (-> & -> & ->).
    auto.
  - iIntros (h m) "Hh HQ". iDestruct (Hself with "Hh HQ") as %Hs. iPureIntro.
    intros Ha (He & _ & Hf). split; [exact He|]. split; [exact (Hs Ha) | exact Hf].
  - iNext. iIntros "Hk HQ". iExists e. iSplit; [done|]. iApply ("HK" with "Hk HQ").
Qed.

(** A pointer into a live object whose lifetime the caller shares is
    registered, which is what [wp_zthread_set_self_cookie_start] asks of
    the new cookie. *)
Lemma self_registered_liveq dq x b reg h m :
  gen_heap_interp h -∗ liveq dq b reg -∗ ⌜agrees m h -> self_registered m (mkPtr x (Obj b))⌝.
Proof using Type.
  iIntros "Hh Hl". iDestruct (ptsq_lookup with "Hh Hl") as %Hl. iPureIntro.
  intros Ha _ b' [[= <-] | [=]]. pose proof (Ha _ _ (Hl _ _ ltac:(by apply list_elem_of_singleton))) as [E _].
  cbn in E. congruence.
Qed.

(** Registering the image's errno handler makes [ow_errno_cell] the errno
    cell. The cell is the base of a global-data object eb, as the C
    variable `c: errno` is, and the caller lends a share of its lifetime so
    that [os_inv] can record it as permanent. *)
Lemma wp_zregister_sys_errno_handler_start f e ls lab a rest j c d hp dq eb reg Φ :
  registry (TAtom "zregister_sys_errno_handler") = Some os_errno_register_contract ->
  find_fn ge (TAtom "zregister_sys_errno_handler") = None ->
  lookup (TAtom "zregister_sys_errno_handler") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg P a] = Some [WPtr hp] -> ptr_cap hp = Fn errno_handler_name ->
  ow_errno_cell w0 = mkPtr eb (Obj eb) -> eb <> 0 -> eb mod 4 = 0 ->
  r_kind reg = GlobalData -> eb + 4 <= r_end reg ->
  pointsto (PName k) (DfracOwn 1) (start_ghost c false d) -∗ liveq dq eb reg -∗
  ▷ (pointsto (PName k) (DfracOwn 1) (start_ghost c true d) -∗ liveq dq eb reg -∗
       WP (ERun (mkFrame f e ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zregister_sys_errno_handler")) [Arg P a] :: rest) j)) : sexpr)
    {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hdata Hx Hh Hcell Hz H4 Hk Hend. iIntros "Hkey Hl HK".
  iApply (wp_start_change _ _ _ _ _ _ _ _ _ _ _ c false d c true d (liveq dq eb reg) with "Hkey Hl [HK]");
    [done | done | done | exact Hreg | exact Hx | | | | | ].
  - split; [reflexivity | eexists; reflexivity].
  - iIntros (σ) "_ _". iPureIntro. exists hp. auto.
  - intros s m trace values s' m' w' Hi. destruct (world_returns _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (-> & -> & ->).
    auto.
  - iIntros (h m) "Hh Hl". iDestruct (ptsq_lookup with "Hh Hl") as %Hl. iPureIntro.
    pose proof (Hl _ _ ltac:(by apply list_elem_of_singleton)) as Hle.
    intros Ha (_ & Hs & Hf). split; [|split; [exact Hs | exact Hf]].
    intros p Hp. cbn in Hp. injection Hp as <-. rewrite Hcell. split.
    + exists eb, reg. pose proof (Ha _ _ Hle) as Hlv. cbn in Hlv. auto 7.
    + intros reg' E. cbn in E. rewrite Hle in E. injection E as <-. exact Hk.
  - iNext. iIntros "Hkey Hl". iExists e. iSplit; [done|]. iApply ("HK" with "Hkey Hl").
Qed.

(** Registering a dlerror handler sets [ow_dlerror] and needs nothing
    else, because no modeled call sets a `c: dlerror` message. *)
Lemma wp_zregister_sys_dlerror_handler_start f e ls lab a rest j c e0 hp n Φ :
  registry (TAtom "zregister_sys_dlerror_handler") = Some os_dlerror_register_contract ->
  find_fn ge (TAtom "zregister_sys_dlerror_handler") = None ->
  lookup (TAtom "zregister_sys_dlerror_handler") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg P a] = Some [WPtr hp] -> ptr_cap hp = Fn n ->
  pointsto (PName k) (DfracOwn 1) (start_ghost c e0 false) -∗
  ▷ (pointsto (PName k) (DfracOwn 1) (start_ghost c e0 true) -∗
       WP (ERun (mkFrame f e ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zregister_sys_dlerror_handler")) [Arg P a] :: rest) j)) : sexpr)
    {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hdata Hx Hh. iIntros "Hkey HK".
  iApply (wp_start_change _ _ _ _ _ _ _ _ _ _ _ c e0 false c e0 true True%I with "Hkey [//] [HK]");
    [done | done | done | exact Hreg | exact Hx | | | | | ].
  - split; [reflexivity | eexists; reflexivity].
  - iIntros (σ) "_ _". iPureIntro. exists hp, n. auto.
  - intros s m trace values s' m' w' Hi. destruct (world_returns _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (-> & -> & ->).
    auto.
  - iIntros (h m) "_ _". iPureIntro. intros _ Hi. exact Hi.
  - iNext. iIntros "Hkey _". iExists e. iSplit; [done|]. iApply ("HK" with "Hkey").
Qed.

End rule.
