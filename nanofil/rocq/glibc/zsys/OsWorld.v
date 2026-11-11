(** Userland glibc makes system calls by calling libpizlo's `zsys_*`
    functions, such as `c: zsys_write`, `c: zsys_fstat`, and
    `c: zsys_close`. Those functions sit at the [[external call|contract]]
    boundary between compiled C code and the Fil-C [[runtime]], and their
    individual contracts are collected in [OsRegistry](OsRegistry.v). This
    module defines the thread and file-descriptor state [os_world] that
    those contracts share, proves that its world interpretation [os_wi]
    survives ordinary memory and runtime steps, and derives the
    [[separation-logic|separation-logic]] rules for calling `zsys_*`
    functions.

    ## The world

    A `zsys_*` wrapper in libpizlo can read or write four pieces of state
    outside the caller's own stack and heap buffers, which we record in
    [os_world]. It can set the calling thread's `c: int errno` variable on
    error, read the thread cookie that points to userland glibc's
    `c: struct pthread`, and check file descriptors against libpizlo's
    internal log descriptor. Every file descriptor that the program passes
    to a system call is distinct from that log descriptor, so
    `c: check_fd(fd)` never panics. Because none of the system-call
    wrappers replace these pointers or descriptor lists, [os_wi] pins the
    world state to a fixed `w0` for the entire run.

    ## Why errno needs no apartness premise

    In userland glibc, `c: __thread int errno` is exported thread-local
    data that [Run](../../theories/core/Run.v) places in a 16-byte-aligned
    global-data [[region]] with a writable [[capability]] at program
    start. In Fil-C, global-data regions are never deallocated: `c: free`
    and external calls only deallocate heap regions, and
    garbage-collection [[poll|safepoints]] do not deallocate any region
    the program can reach.

    Because `c: errno` lives in global data and can never be freed by
    `c: free` or the garbage collector, the world interpretation [os_wi]
    remains valid across every memory store, heap allocation,
    deallocation, and safepoint. Callers never have to prove that ordinary
    heap allocations or deallocations avoid `c: errno`; they only lend the
    4-byte `c: errno` buffer when making a system call that can write an
    error code into it.

    ## Borrowing errno and output buffers

    When a `zsys_*` call can write into caller memory, such as setting
    `c: errno` on failure or filling a `c: struct stat` buffer, the caller
    lends ownership of those memory blocks from [OsBlocks](OsBlocks.v) for
    the duration of the call. When the call returns, [os_call_return]
    updates the borrowed blocks to the bytes and [[aux]] capabilities the
    call wrote into physical memory and hands them back to the caller,
    while every other piece the caller owns remains unchanged. From that
    update, the module derives [wp_os_call] for calls that write output
    buffers, [wp_os_errno_call] for calls that also set `c: errno`, and
    [wp_os_noreturn] for calls that exit the process. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks.
Import ListNotations.
Open Scope Z_scope.

(** ## The world

    Before introducing separation-logic assertions, this first section
    defines the record [os_world] and the invariant [os_inv] that describes
    what a valid world requires of memory. *)

(** The [os_world] record holds the thread and file-descriptor state
    outside a C module that `zsys_*` calls read or check. *)
Record os_world : Type := mkOsWorld {
  ow_errno : option ptr;  (* pointer to the calling thread's `c: int errno` cell, once allocated *)
  ow_self : ptr;          (* the thread cookie returned by `c: zthread_self_cookie()` (userland glibc's `c: struct pthread`) *)
  ow_log_fd : option Z;   (* libpizlo's internal log descriptor, if logging to a file *)
  ow_fds : list Z         (* file descriptors the program uses *)
}.

(** When a system call fails, libpizlo stores the error number into the
    calling thread's `c: errno` variable through `c: filc_set_errno`.
    [errno_spans] returns the 4-byte writable span of that variable when
    one is present. *)
Definition errno_spans (w : os_world) : list span :=
  match ow_errno w with Some p => [mkSpan p 4] | None => [] end.

(** A pointer satisfies [permanent_errno] when it points through a
    writable object capability to the base of a live, non-null,
    4-byte-aligned global-data object of at least 4 bytes. *)
Definition permanent_errno (m : mem) (p : ptr) : Prop :=
  exists eb reg, p = mkPtr eb (Obj eb) /\ eb <> 0 /\ eb mod 4 = 0 /\ live_at m eb reg /\
    r_kind reg = GlobalData /\ eb + 4 <= r_end reg.

(** The thread cookie satisfies [self_registered] when, if non-null, any
    object capability it carries is registered in memory. *)
Definition self_registered (m : mem) (p : ptr) : Prop :=
  ptr_addr p <> 0 -> forall b, (ptr_cap p = Obj b \/ ptr_cap p = Ro b) ->
    object_region b (m_regions m) <> None.

(** Because `c: errno` is allocated in global data rather than on the
    heap, `c: free` can never deallocate it. The predicate
    [errno_life_global] records that any liveness token for the `c: errno`
    object has global-data kind. *)
Definition errno_life_global (h : gmap piece pval) (eb : Z) : Prop :=
  forall reg, h !! PLive eb = Some (VLive reg) -> r_kind reg = GlobalData.

(** Every `zsys_*` wrapper assumes that the calling thread's `c: errno`
    variable is a permanent global-data object, its thread cookie is
    registered, and none of the program's file descriptors collide with
    libpizlo's log file. The invariant [os_inv] combines those three
    conditions. *)
Definition os_inv (m : mem) (w : os_world) (h : gmap piece pval) : Prop :=
  (forall p, ow_errno w = Some p -> permanent_errno m p /\ errno_life_global h (ptr_addr p)) /\
  self_registered m (ow_self w) /\
  Forall (fun fd => ow_log_fd w <> Some fd) (ow_fds w).

(** The world interpretation [os_wi] pins the current world to a fixed
    world `w0` and requires the world invariant [os_inv] to hold. *)
Definition os_wi (w0 : os_world) (m : mem) (w : os_world) (h : gmap piece pval) : Prop :=
  w = w0 /\ os_inv m w h.

(** For a write system call, [os_bytes] reads `k` consecutive bytes
    starting at pointer `p` from physical memory. *)
Definition os_bytes (m : mem) (p : ptr) (k : Z) : list Z :=
  map (fun i => m_bytes m (ptr_addr p + Z.of_nat i)) (seq 0 (Z.to_nat k)).

(** Before reading `n` bytes from a user pointer `p`, libpizlo calls
    `c: filc_check_read(p, n)`. When `n` is zero, `c: filc_check_read`
    returns early (`c: if (!bytes) return;`) without inspecting `p`, so a
    zero-length write such as `c: write(fd, NULL, 0)` succeeds even on a
    null pointer. Otherwise `n` bytes must be readable from `p`. *)
Definition os_readable (m : mem) (p : ptr) (n : Z) : Prop :=
  0 <= n < 2 ^ 64 /\ (n = 0 \/ readable_bytes m p n).

(** Any pointer that satisfies [permanent_errno] is a valid writable
    4-byte `c: int` cell in memory. *)
Lemma permanent_errno_cell m p : permanent_errno m p -> errno_cell m p.
Proof.
  intros (eb & reg & -> & Hz & H4 & [E L] & _ & He). split; [exact Hz|]. split; [|exact H4].
  split; [cbn; lia|]. exists eb, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
  cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** ## What keeps the world interpretation

    In Iris, the [[state-interpretation|state interpretation]] must hold
    before and after every step of the program. Whenever a C function
    stores to memory, allocates a heap object, or calls `c: free`,
    [Logic](../../theories/logic/Logic.v) asks us to show that [os_wi]
    still holds after the step. The lemmas in this section prove that
    [os_wi] survives all of those steps automatically. *)

(** The world invariant checks only that registered objects stay
    registered and that `c: errno` keeps its global-data region and
    liveness kind. Any step that preserves those two facts preserves
    [os_inv]. *)
Lemma os_inv_step m m' w h h' :
  (forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None) ->
  (forall eb reg, ow_errno w = Some (mkPtr eb (Obj eb)) -> live_at m eb reg -> r_kind reg = GlobalData ->
     errno_life_global h eb -> object_region eb (m_regions m') = Some reg /\ errno_life_global h' eb) ->
  os_inv m w h -> os_inv m' w h'.
Proof.
  intros Hreg Herr (He & Hs & Hf). split; [|split; [|exact Hf]].
  - intros p Hp. destruct (He p Hp) as [(eb & reg & -> & Hz & H4 & Hl & Hk & Hend) Hg].
    destruct (Herr eb reg Hp Hl Hk Hg) as [E' Hg']. split; [|exact Hg'].
    exists eb, reg. repeat split; try assumption. exact (proj2 Hl).
  - intros Hz b Hb. exact (Hreg b (Hs Hz b Hb)).
Qed.

(** Because `c: errno` is allocated in global data at program startup,
    updating other entries in the caller's state never changes
    `c: errno`'s allocation kind. *)
Lemma errno_life_overwrite h ps eb :
  (forall reg, (PLive eb, VLive reg) ∈ ps -> r_kind reg = GlobalData) ->
  errno_life_global h eb -> errno_life_global (overwrite ps h) eb.
Proof.
  intros Hps Hg reg E. destruct (lookup_overwrite _ _ _ _ E) as [Hin | [_ Hh]].
  - exact (Hps reg Hin).
  - exact (Hg reg Hh).
Qed.

(** Because [os_wi] only checks object regions and never reads byte
    values, any memory store preserves [os_wi] without requiring the
    stored address to be disjoint from `c: errno`. *)
Lemma os_wi_store w0 m m' w h ps :
  m_regions m' = m_regions m ->
  (forall l v, (l, v) ∈ ps -> match l with PLive _ => h !! l = Some v | _ => True end) ->
  os_wi w0 m w h -> os_wi w0 m' w (overwrite ps h).
Proof.
  intros E Hps [-> Hi]. split; [reflexivity|]. apply (os_inv_step m m' w0 h); [| |exact Hi].
  - intros b. rewrite E. auto.
  - intros eb reg _ [E0 _] _ Hg. rewrite E. split; [exact E0|].
    apply errno_life_overwrite; [|exact Hg]. intros reg' Hin. apply (Hg reg'). exact (Hps _ _ Hin).
Qed.

(** Allocating a new heap object at a [[fresh]] unregistered address
    preserves [os_wi], because the new object cannot be the
    already-registered `c: errno` object. *)
Lemma os_wi_alloc w0 m w h q base :
  fresh m q base -> os_wi w0 m w h -> os_wi w0 (allocated m q base) w (overwrite (obj_ps base q) h).
Proof.
  intros (_ & _ & _ & Hn & _) [-> Hi]. split; [reflexivity|]. apply (os_inv_step m _ w0 h); [| |exact Hi].
  - intros b Hb. rewrite object_region_allocated. destruct (Z.eqb_spec base b); [discriminate|exact Hb].
  - intros eb reg _ [E0 _] _ Hg. rewrite object_region_allocated.
    destruct (Z.eqb_spec base eb) as [<-|Hne]; [congruence|]. split; [exact E0|].
    apply errno_life_overwrite; [|exact Hg]. intros reg' Hin. exfalso.
    unfold obj_ps in Hin. apply elem_of_cons in Hin as [[= ->] | Hin]; [congruence|].
    apply elem_of_app in Hin as [Hin|Hin]; apply list_elem_of_fmap in Hin as (i & [=] & _).
Qed.

(** Freeing a live heap object preserves [os_wi], because `c: errno` lives
    in global data and therefore cannot be the heap object being freed. *)
Lemma os_wi_free w0 m w h b reg rs :
  r_kind reg = Heap -> h !! PLive b = Some (VLive reg) ->
  replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs ->
  os_wi w0 m w h -> os_wi w0 (mkMem (m_bytes m) rs (m_aux m)) w (overwrite [(PLive b, VFreed)] h).
Proof.
  intros Hk Hh Hrs [-> Hi]. split; [reflexivity|].
  pose proof (fun b' => object_region_replace _ _ _ _ b' Hrs eq_refl) as E.
  apply (os_inv_step m _ w0 h); [| |exact Hi].
  - intros b' Hb'. cbn [m_regions]. rewrite E. destruct (Z.eqb_spec b' b); [discriminate|exact Hb'].
  - intros eb reg' _ [E0 _] Hk' Hg. cbn [m_regions]. rewrite E.
    destruct (Z.eqb_spec eb b) as [->|Hne].
    + exfalso. pose proof (Hg reg Hh). congruence.
    + split; [exact E0|]. intros reg0 E1. cbn [overwrite fst snd] in E1.
      rewrite lookup_insert_ne in E1; [exact (Hg reg0 E1) | intros [=]; congruence].
Qed.

(** A runtime deallocation step can only free heap objects and keeps all
    object identities registered, so it preserves [os_wi]. *)
Lemma os_wi_lifetime w0 m m' w h :
  lifetime_step m m' ->
  (forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None) ->
  os_wi w0 m w h -> os_wi w0 m' w h.
Proof.
  intros Hl Hids [-> Hi]. split; [reflexivity|]. apply (os_inv_step m m' w0 h); [exact Hids| |exact Hi].
  intros eb reg _ [E0 _] Hk Hg. split; [|exact Hg].
  destruct (object_region eb (m_regions m')) as [reg'|] eqn:E'; [|exfalso; apply (Hids eb); congruence].
  destruct (Hl eb reg' E') as (reg0 & E1 & [-> | (Hh & _)]); rewrite E0 in E1; injection E1 as <-;
    [reflexivity | congruence].
Qed.

(** ## Over a Logic instance

    The stability lemmas above are pure facts about memory transitions.
    The functor below connects them to a Fil-C [[runtime]] and the program
    logic of [Logic](../../theories/logic/Logic.v), giving the
    [[weakest-precondition|weakest-precondition]] rules for `zsys_*`
    calls. *)

(** The functor [OsWorldOn] instantiates the world-invariant stability
    lemmas and `zsys_*` call rules for a given [[runtime]] and program
    logic. *)
Module OsWorldOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

(** A garbage-collection [[poll|safepoint]] leaves all reachable regions
    and the separation-logic state unchanged, so it preserves [os_wi]. *)
Lemma os_wi_safepoint w0 s m s' m' w h : R.safepoint s m s' m' -> os_wi w0 m w h -> os_wi w0 m' w h.
Proof.
  intros Hsp Hw. pose proof (R.collector_live _ _ _ _ Hsp) as E.
  rewrite <- (overwrite_id [] h) by (intros ? ? Hin; by apply not_elem_of_nil in Hin).
  apply (os_wi_store w0 m m' w h []); [exact E | |exact Hw]. intros l v Hin. by apply not_elem_of_nil in Hin.
Qed.

(** This instance registers [os_wi] as safepoint-stable for the program
    logic. *)
Instance os_wi_stable w0 : SafepointStable (os_wi w0).
Proof. split. intros s m s' m' w h. apply os_wi_safepoint. Qed.

(** If an external call's [effects] path starts from a [[ready]] runtime
    state and frees no existing objects, then every object that was
    already registered before the call keeps its exact region after the
    call. *)
Lemma effects_keep_old sources roots requests s m born0 s' m' born :
  M.E.effects sources roots [] requests s m born0 s' m' born -> R.ready s m ->
  forall b reg, object_region b (m_regions m) = Some reg -> ~ In b born0 ->
    object_region b (m_regions m') = Some reg.
Proof.
  induction 1 as [s m born0 | s m born0 m1 s' m' born Hl H IH
                 | s m born0 align size base s1 s' m' born Hq Hsize Halloc H IH];
    intros Hr b reg E Hb.
  - exact E.
  - apply IH; [exact (R.ready_kept _ _ _ Hr (local_effect_kept _ _ _ _ _ _ Hl)) | | exact Hb].
    destruct Hl as (Hi & Hreg & _). destruct (Hi b reg E) as [reg' E'].
    destruct (Hreg b reg' E') as (reg0 & E0 & [-> | (Hin & _)]); rewrite E in E0; injection E0 as <-;
      [exact E' | contradiction].
  - assert (Hal : 0 < req_align (heap_req align size)) by (cbn; lia).
    assert (He : 0 <= req_extent (heap_req align size)).
    { cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia]. }
    destruct (R.fresh_allocation _ _ _ _ _ Hr Hal He Halloc) as [Hf Hr1].
    pose proof Hf as (_ & _ & _ & Hn & _).
    assert (Hne : base <> b) by (intros <-; congruence).
    apply IH; [exact Hr1 | | intros [Hbb|Hbb]; [exact (Hne Hbb) | exact (Hb Hbb)]].
    rewrite object_region_allocated. destruct (Z.eqb_spec base b); [contradiction | exact E].
Qed.

(** When an external call returns values to its caller, its precondition
    held at entry and its execution trace satisfies the contract's
    postcondition. *)
Lemma os_invoke_returned {world} (spec : contract world) r args xs s m w trace values s' m' w' :
  M.E.invoke spec r args xs s m w trace (CallReturn values) s' m' w' ->
  contract_pre spec xs m w /\ exists born, M.E.prefix spec xs s m w born trace s' m' w' /\
    contract_post spec xs m w born trace (CallReturn values) m' w'.
Proof.
  intros Hi. remember (CallReturn values) as en eqn:Een.
  destruct Hi as [? ? ? ? ? born _ Hpre Hp Hpost | ? ? ? ? ? ? _ _ _ _ _]; [|discriminate Een].
  subst. split; [exact Hpre|]. exists born. auto.
Qed.

(** This section fixes the initial OS world `w0` for a run and proves the
    call-return and weakest-precondition lemmas for `zsys_*` calls. *)
Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** The state interpretation implies that the machine's current world
    equals `w0` and satisfies [os_inv]. *)
Lemma os_heap_world σ :
  heap_interp (os_wi w0) σ -∗ ⌜ls_world σ = w0 /\ exists h, os_inv (ls_mem σ) w0 h⌝.
Proof.
  iIntros "(%h & _ & %Hf)". destruct Hf as (_ & _ & _ & -> & Hi). iPureIntro. eauto.
Qed.

(** When `w0` has an `c: errno` object, the state interpretation guarantees
    that `c: errno` is a valid writable 4-byte `c: int` cell in a live
    object. *)
Lemma os_heap_errno σ eb :
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  heap_interp (os_wi w0) σ -∗ ⌜errno_cell (ls_mem σ) (mkPtr eb (Obj eb)) /\ blk_live (ls_mem σ) (eb, 0, 4)⌝.
Proof.
  intros He. iIntros "Hσ". iDestruct (os_heap_world with "Hσ") as %[_ (h & Hi & _)]. iPureIntro.
  destruct (Hi _ He) as [Hp _]. split; [exact (permanent_errno_cell _ _ Hp)|].
  destruct Hp as (eb' & reg & [= <-] & _ & _ & Hl & _ & Hend). exists reg. cbn. split; [exact Hl|lia].
Qed.

(** Before calling a system-call wrapper that takes a file descriptor, the
    caller must show that the descriptor is not libpizlo's log file and
    that `c: errno` is writable. The lemma [os_heap_ready] extracts both
    facts for any allowed descriptor. *)
Lemma os_heap_ready σ eb fd :
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  heap_interp (os_wi w0) σ -∗
  ⌜ls_world σ = w0 /\ ow_log_fd w0 <> Some fd /\ errno_cell (ls_mem σ) (mkPtr eb (Obj eb))⌝.
Proof.
  intros He Hin. iIntros "Hσ". iDestruct (os_heap_errno with "Hσ") as %[Hc _]; [exact He|].
  iDestruct (os_heap_world with "Hσ") as %[Hw (h & _ & _ & Hfd)]. iPureIntro.
  rewrite Forall_forall in Hfd. auto.
Qed.

(** Adding the thread's 4-byte `c: errno` block to the borrowed block list
    covers all writable spans of a call that writes both `c: errno` and
    those borrowed buffers. *)
Lemma errno_roots_out eb bl (extra : list span) w sp a :
  ow_errno w = Some (mkPtr eb (Obj eb)) ->
  (forall sp a, In sp extra -> span_contains sp a -> blk_out bl a) ->
  In sp (extra ++ errno_spans w) -> span_contains sp a -> blk_out ((eb, 0, 4) :: bl) a.
Proof.
  intros He Hx Hin Hs. unfold errno_spans in Hin. rewrite He in Hin.
  apply in_app_or in Hin as [Hin | [<- | []]].
  - destruct (Hx _ _ Hin Hs) as (b & o & n & Hb & Ha). exists b, o, n. split; [right; exact Hb | exact Ha].
  - exists eb, 0, 4. unfold span_contains in Hs. cbn in Hs. split; [left; reflexivity | lia].
Qed.

(** When an OS contract returns without freeing existing objects and writes
    only inside the borrowed buffers, [os_call_return] refreshes the
    borrowed blocks to their post-call contents and restores the state
    interpretation while leaving all other caller-owned memory unchanged. *)
Lemma os_call_return (spec : contract os_world) r args xs σ trace values s' m' w' bl :
  M.E.invoke spec r args xs (ls_rt σ) (ls_mem σ) (ls_world σ) trace (CallReturn values) s' m' w' ->
  w' = ls_world σ -> contract_releases spec xs (ls_mem σ) (ls_world σ) = [] ->
  (forall sp a, In sp (contract_writes spec xs (ls_mem σ) (ls_world σ)) -> span_contains sp a -> blk_out bl a) ->
  Forall (blk_live (ls_mem σ)) bl ->
  heap_interp (os_wi w0) σ -∗ blks bl ==∗ heap_interp (os_wi w0) (mkLstate m' s' (ls_fuel σ) w') ∗ blks bl.
Proof.
  intros Hinv -> Hrel Hroots Hlive. iIntros "Hσ Hb".
  iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (Ha & Hd & Hr & [Hw Hi]).
  destruct σ as [m s fuel w]. cbn [ls_mem ls_rt ls_world ls_fuel] in *. subst w.
  destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (_ & born & Hp & _).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  assert (Hids : ids_registered h m) by (intros l v Hl Hm; exact (agree_piece_registered _ l v Hm (Ha l v Hl))).
  destruct (prefix_agrees_out _ _ _ _ _ _ _ _ _ _ _ h (blks_keys bl) (blk_out bl) Hp Hr Hd
              (fun l v Hl _ => Ha l v Hl) Hids (fun sp a Hin Hs _ => Hroots sp a Hin Hs)
              (blks_pieces_off _ _ _ Hd Hlive) ltac:(rewrite Hrel; intros ? ? ? []))
    as (Ha' & _ & Hd' & _).
  pose proof Hp as [He' _]. rewrite Hrel in He'.
  pose proof (fun b reg E => effects_keep_old _ _ _ _ _ _ _ _ _ He' Hr b reg E (fun Hin => Hin)) as Hkeep.
  assert (Hlm : forall x, blk_live m x -> blk_live m' x).
  { intros x (reg & [E L] & Hx). exists reg. split; [split; [exact (Hkeep _ _ E) | exact L] | exact Hx]. }
  iMod (blks_return bl h m' [] with "Hh Hb") as (h') "(Hh & Hb & %Ha'' & %Hlv)".
  { rewrite app_nil_r. exact Ha'. }
  { eapply Forall_impl; [exact Hlm | exact Hlive]. }
  iModIntro. iFrame "Hb". iExists h'. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world].
  split; [intros l v Hl; exact (Ha'' l v Hl (not_elem_of_nil _))|].
  split; [exact Hd'|]. split; [exact Hr'|]. split; [reflexivity|].
  apply (os_inv_step m m' w0 h h'); [| |exact Hi].
  - intros b Hb. destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|contradiction].
    rewrite (Hkeep _ _ E). discriminate.
  - intros eb' reg _ [E _] _ Hg. split; [exact (Hkeep _ _ E)|]. intros reg' E'. rewrite Hlv in E'. exact (Hg _ E').
Qed.

(** Finally, we fix a contract `registry` and a [[genv|global environment]]
    `ge` to state the three [[weakest-precondition|weakest-precondition]]
    rules that individual `zsys_*` contract files apply. *)
Section call.
Context (registry : name -> option (contract os_world)) (ge : genv).

(** The instance [os_call_irisGS] configures Iris for the language with the
    OS contract registry and the world interpretation [os_wi]. *)
Local Instance os_call_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** The notation [oexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation oexpr := (language.expr (nanofil_lang registry ge)).

(** When a C function calls an OS contract that leaves the world unchanged,
    frees no objects, and writes only inside borrowed buffers, [wp_os_call]
    lets the caller lend those buffers before the call and receive them
    back for every return value the contract allows. *)
Lemma wp_os_call f e ls lab r g args rest j spec xs bl (Q : iProp Σ) (R : list word -> Prop) Φ :
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
  registry g = Some spec -> map_option (arg_x ge e) args = Some xs -> contract_abi spec r args ->
  (forall σ, heap_interp (os_wi w0) σ -∗ Q -∗
     ⌜contract_pre spec xs (ls_mem σ) (ls_world σ) /\ Forall (blk_live (ls_mem σ)) bl /\
      forall sp a, In sp (contract_writes spec xs (ls_mem σ) w0) -> span_contains sp a -> blk_out bl a⌝) ->
  (forall m, contract_releases spec xs m w0 = []) ->
  (forall σ trace values s' m' w',
     M.E.invoke spec r args xs (ls_rt σ) (ls_mem σ) w0 trace (CallReturn values) s' m' w' ->
     heap_interp (os_wi w0) σ -∗ Q -∗ ⌜w' = w0 /\ R values⌝) ->
  Q -∗ blks bl -∗
  ▷ (∀ values, ⌜R values⌝ -∗ Q -∗ blks bl -∗
       ∃ e', ⌜external_env spec (mkCallSite lab r g args rest j) values e = Some e'⌝ ∗
         WP (ERun (mkFrame f e' ls None (Exec lab rest j)) : oexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : oexpr) {{ Φ }}.
Proof.
  intros Hfn Hdata Hfree Hreg Hx Habi Hpre Hrel Hret. iIntros "HQ Hb HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ spec xs (Q ∗ blks bl)
            with "[$HQ $Hb] [HK]"); [done | done | done | done | exact Hx | exact Habi | |].
  - iIntros (σ) "Hσ (HQ & _)". iDestruct (Hpre with "Hσ HQ") as %[Hp _]. done.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ (HQ & Hb)".
    iDestruct (Hpre with "Hσ HQ") as %(_ & Hl & Hroots'). iDestruct (os_heap_world with "Hσ") as %[Hw _].
    assert (Hrel' := Hrel (ls_mem σ)). rewrite <- Hw in Hrel', Hroots'.
    pose proof Hinv as Hinv0. rewrite Hw in Hinv0.
    iDestruct (Hret _ _ _ _ _ _ Hinv0 with "Hσ HQ") as %[-> HR].
    iMod (os_call_return _ _ _ _ _ _ _ _ _ _ bl Hinv (eq_sym Hw) Hrel' Hroots' Hl with "Hσ Hb") as "(Hσ & Hb)".
    iDestruct ("HK" $! values with "[%] HQ Hb") as (e') "[%He' Hwp]"; [exact HR|].
    iModIntro. iExists e'. iSplit; [done|]. iFrame.
Qed.

(** Most `zsys_*` wrappers can also set the calling thread's `c: errno` on
    failure. [wp_os_errno_call] works like [wp_os_call], except the caller
    also lends [errno_any] before the call and receives it back alongside
    the borrowed buffers when the call returns. *)
Lemma wp_os_errno_call f e ls lab r g args rest j spec xs eb bl (Q : iProp Σ) (R : list word -> Prop) Φ :
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
  registry g = Some spec -> map_option (arg_x ge e) args = Some xs -> contract_abi spec r args ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  (forall σ, heap_interp (os_wi w0) σ -∗ Q -∗
     ⌜contract_pre spec xs (ls_mem σ) (ls_world σ) /\ Forall (blk_live (ls_mem σ)) bl /\
      exists extra, contract_writes spec xs (ls_mem σ) w0 = extra ++ errno_spans w0 /\
        forall sp a, In sp extra -> span_contains sp a -> blk_out bl a⌝) ->
  (forall m, contract_releases spec xs m w0 = []) ->
  (forall σ trace values s' m' w',
     M.E.invoke spec r args xs (ls_rt σ) (ls_mem σ) w0 trace (CallReturn values) s' m' w' ->
     heap_interp (os_wi w0) σ -∗ Q -∗ ⌜w' = w0 /\ R values⌝) ->
  Q -∗ errno_any eb -∗ blks bl -∗
  ▷ (∀ values, ⌜R values⌝ -∗ Q -∗ errno_any eb -∗ blks bl -∗
       ∃ e', ⌜external_env spec (mkCallSite lab r g args rest j) values e = Some e'⌝ ∗
         WP (ERun (mkFrame f e' ls None (Exec lab rest j)) : oexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : oexpr) {{ Φ }}.
Proof.
  intros Hfn Hdata Hfree Hreg Hx Habi He Hpre Hrel Hret. iIntros "HQ Herr Hb HK".
  iApply (wp_os_call _ _ _ _ _ _ _ _ _ _ _ ((eb, 0, 4) :: bl) Q R with "HQ [Herr Hb] [HK]");
    [done | done | done | done | exact Hx | exact Habi | | exact Hrel | exact Hret | |].
  - iIntros (σ) "Hσ HQ". iDestruct (Hpre with "Hσ HQ") as %(Hp & Hl & extra & E & Hx').
    iDestruct (os_heap_errno with "Hσ") as %[_ Hel]; [exact He|]. iPureIntro. split; [exact Hp|].
    split; [constructor; [exact Hel | exact Hl]|]. intros sp a Hin Hs. rewrite E in Hin.
    exact (errno_roots_out eb bl extra w0 sp a He Hx' Hin Hs).
  - iApply big_sepL_cons. iFrame "Hb". iApply errno_any_blk. iExact "Herr".
  - iNext. iIntros (vs HR) "HQ Hb". iDestruct (big_sepL_cons with "Hb") as "[Herr Hb]".
    iApply ("HK" with "[%] HQ [Herr] Hb"); [exact HR | iApply errno_any_blk; iExact "Herr"].
Qed.

(** Some calls, such as `c: zsys_exit_soft` and `c: zsys_exit_hard`,
    terminate the process and never return. Once the caller establishes
    the contract's precondition, [wp_os_noreturn] proves the call for any
    postcondition, because control never reaches the instructions after
    the call. *)
Lemma wp_os_noreturn f e ls lab r g args rest j spec xs (Q : iProp Σ) Φ :
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
  registry g = Some spec -> map_option (arg_x ge e) args = Some xs -> contract_abi spec r args ->
  (forall σ, heap_interp (os_wi w0) σ -∗ Q -∗ ⌜contract_pre spec xs (ls_mem σ) (ls_world σ)⌝) ->
  (forall s m w trace values s' m' w', ~ M.E.invoke spec r args xs s m w trace (CallReturn values) s' m' w') ->
  Q -∗ WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : oexpr) {{ Φ }}.
Proof.
  intros Hfn Hdata Hfree Hreg Hx Habi Hpre Hno. iIntros "HQ".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ spec xs Q with "HQ []");
    [done | done | done | done | exact Hx | exact Habi | exact Hpre |].
  iNext. iIntros (σ trace values s' m' w' Hinv). exfalso. exact (Hno _ _ _ _ _ _ _ _ Hinv).
Qed.

End call.
End rule.
End OsWorldOn.
