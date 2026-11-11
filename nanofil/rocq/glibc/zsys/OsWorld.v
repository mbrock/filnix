(** The OS world of user glibc's calls into libpizlo's `zsys_*`
    functions ([[external call|contracts]] [OsWrite](OsWrite.v) to
    [OsThread](OsThread.v), [OsRegistry](OsRegistry.v)), its world
    interpretation [os_wi], and the lending of `c: errno` to a call.

    ## The world

    [os_world] keeps what no Fil-C code of the module owns: the calling
    thread's `c: errno` cell ([ow_errno]), its thread cookie
    ([ow_self], what `c: zthread_self_cookie()` returns: user glibc's
    `c: struct pthread`), libpizlo's log descriptor ([ow_log_fd]) and
    the descriptors the program uses ([ow_fds], none of them the log
    descriptor, so `c: check_fd(fd)` never fires). The world is fixed
    for a run: no contract here changes it, so [os_wi] w0 pins it to w0
    and a rule can name w0's errno cell and cookie.

    ## A permanent errno

    `c: __thread int errno` (csu/errno.c) is `tls(export)` data, which
    Run.v's [initial_memory] lays out as a 16-aligned [GlobalData]
    region with an [Obj] capability ([permanent_errno]). Nothing frees
    a [GlobalData] object: free ([lifetime_step]) and a call's
    [local_effect] end only live [Heap] objects, and a safepoint ends
    none ([collector_live]). So [os_wi] needs no apartness of the errno
    span from the program's pieces ([roots_apart]), unlike an apartness-based
    world invariant: it reads only regions and the world, and survives stores
    ([os_wi_store]), safepoints ([os_wi_stable]), allocations
    ([os_wi_alloc]), frees ([os_wi_free], [os_wi_lifetime]) and calls
    of these contracts ([os_call_return]). One clause reads the ghost
    heap: a life token of errno's object, if the program owns one, is
    a [GlobalData] one ([errno_life_global]), which is what tells
    [wp_free]'s premise that a freed heap object is not errno's.

    ## Lending errno

    The program owns errno as a block: its 4 bytes and the 4 [[aux]]
    slots at the same offsets ([errno_own], [errno_any]), since
    ContractFrame.v's [pieces_off] asks of every byte and aux piece at
    an address the call may write, and Heap.v's [obj_ps] has an aux
    piece at every offset. A call whose writable roots lie in errno and
    in other owned blocks ([blk_any]; `c: struct stat`, an ioctl
    argument) borrows them and hands them back with whatever the call
    left there ([os_call_return], through Logic.v's
    [prefix_agrees_out] and Heap.v's [pts_update]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks.
Import ListNotations.
Open Scope Z_scope.

(** ## The world *)

(** What a `zsys_*` call reaches outside the module's Fil-C code. *)
Record os_world : Type := mkOsWorld {
  ow_errno : option ptr;  (* the calling thread's `c: int errno` cell, once allocated *)
  ow_self : ptr;          (* the thread's cookie: user glibc's `c: struct pthread` *)
  ow_log_fd : option Z;   (* libpizlo's log descriptor, if it logs to a file *)
  ow_fds : list Z         (* the descriptors the program uses *)
}.

(** The 4-byte span of the thread's `c: errno`, if it has one: the
    writable root every failing call needs (`c: filc_set_errno`). *)
Definition errno_spans (w : os_world) : list span :=
  match ow_errno w with Some p => [mkSpan p 4] | None => [] end.

(** Errno's cell p is the base of a live, never-freed object: a
    nonzero, 4-aligned [GlobalData] object of at least 4 bytes, through
    its [Obj] capability. *)
Definition permanent_errno (m : mem) (p : ptr) : Prop :=
  exists eb reg, p = mkPtr eb (Obj eb) /\ eb <> 0 /\ eb mod 4 = 0 /\ live_at m eb reg /\
    r_kind reg = GlobalData /\ eb + 4 <= r_end reg.

(** The cookie p, if not null, names a registered object. *)
Definition self_registered (m : mem) (p : ptr) : Prop :=
  ptr_addr p <> 0 -> forall b, (ptr_cap p = Obj b \/ ptr_cap p = Ro b) ->
    object_region b (m_regions m) <> None.

(** A life token of the object eb in the ghost heap h, if any, is that
    of a [GlobalData] object. *)
Definition errno_life_global (h : gmap piece pval) (eb : Z) : Prop :=
  forall reg, h !! PLive eb = Some (VLive reg) -> r_kind reg = GlobalData.

(** What the world requires of memory m and ghost heap h. *)
Definition os_inv (m : mem) (w : os_world) (h : gmap piece pval) : Prop :=
  (forall p, ow_errno w = Some p -> permanent_errno m p /\ errno_life_global h (ptr_addr p)) /\
  self_registered m (ow_self w) /\
  Forall (fun fd => ow_log_fd w <> Some fd) (ow_fds w).

(** The world interpretation: the world is w0, and [os_inv] holds. *)
Definition os_wi (w0 : os_world) (m : mem) (w : os_world) (h : gmap piece pval) : Prop :=
  w = w0 /\ os_inv m w h.

(** The first k bytes of memory m from p's address: what a write of k
    bytes from p hands the kernel. *)
Definition os_bytes (m : mem) (p : ptr) (k : Z) : list Z :=
  map (fun i => m_bytes m (ptr_addr p + Z.of_nat i)) (seq 0 (Z.to_nat k)).

(** libpizlo's `c: filc_check_read(p, n)` passes: a canonical `c: size_t`
    n, and n bytes readable from p ([readable_bytes]) unless n is 0,
    which the check skips (`c: if (!bytes) return;`), even for a null
    pointer. *)
Definition os_readable (m : mem) (p : ptr) (n : Z) : Prop :=
  0 <= n < 2 ^ 64 /\ (n = 0 \/ readable_bytes m p n).

(** A permanent errno is a writable `c: int` ([errno_cell]). *)
Lemma permanent_errno_cell m p : permanent_errno m p -> errno_cell m p.
Proof.
  intros (eb & reg & -> & Hz & H4 & [E L] & _ & He). split; [exact Hz|]. split; [|exact H4].
  split; [cbn; lia|]. exists eb, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
  cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** ## What keeps the world interpretation *)

(** [os_inv] survives a change from m to m' and h to h' that keeps
    every registered object registered, and errno's region and the
    [GlobalData] kind of its life token. *)
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

(** Writing pieces ps over h keeps [errno_life_global] when every life
    token of eb among them is a [GlobalData] one. *)
Lemma errno_life_overwrite h ps eb :
  (forall reg, (PLive eb, VLive reg) ∈ ps -> r_kind reg = GlobalData) ->
  errno_life_global h eb -> errno_life_global (overwrite ps h) eb.
Proof.
  intros Hps Hg reg E. destruct (lookup_overwrite _ _ _ _ E) as [Hin | [_ Hh]].
  - exact (Hps reg Hin).
  - exact (Hg reg Hh).
Qed.

(** A store, or anything that keeps every region, keeps [os_wi], when
    the life tokens it writes are those h holds (as Logic.v's store
    rules write them back): no errno span apartness is needed. *)
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

(** An allocation at a [fresh] base keeps [os_wi]: the new object is
    none of errno's, since errno's is registered. *)
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

(** A free of the live heap object b ([wp_free]'s premise) keeps
    [os_wi]: b is not errno's object, whose life token, if owned, is a
    [GlobalData] one. *)
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

(** Any change of the runtime's free kind ([lifetime_step], with every
    identity kept, as Runtime.v's [free_lifetime] and [free_keeps_ids]
    say of every free) keeps [os_wi] with the same ghost heap. *)
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

(** ## Over a Logic instance *)

(** The world interpretation over the [[runtime]] R and [LogicSig]
    LG0: it survives safepoints, and a call of an OS contract hands
    errno and its other blocks back ([os_call_return]). *)
Module OsWorldOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

(** A safepoint keeps [os_wi]: it changes no region
    ([collector_live]) and no ghost heap. *)
Lemma os_wi_safepoint w0 s m s' m' w h : R.safepoint s m s' m' -> os_wi w0 m w h -> os_wi w0 m' w h.
Proof.
  intros Hsp Hw. pose proof (R.collector_live _ _ _ _ Hsp) as E.
  rewrite <- (overwrite_id [] h) by (intros ? ? Hin; by apply not_elem_of_nil in Hin).
  apply (os_wi_store w0 m m' w h []); [exact E | |exact Hw]. intros l v Hin. by apply not_elem_of_nil in Hin.
Qed.

(** [os_wi] is [SafepointStable]. *)
Instance os_wi_stable w0 : SafepointStable (os_wi w0).
Proof. split. intros s m s' m' w h. apply os_wi_safepoint. Qed.

(** Along an [effects] path that releases nothing, from a [[ready]]
    state, every object of m not born in the call keeps its region:
    a [local_effect] ends only released or born objects, and an
    allocation is [fresh]. *)
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

(** A completed call that returned: its precondition held, and a
    [prefix] that its postcondition accepts reached the end state. *)
Lemma os_invoke_returned {world} (spec : contract world) r args xs s m w trace values s' m' w' :
  M.E.invoke spec r args xs s m w trace (CallReturn values) s' m' w' ->
  contract_pre spec xs m w /\ exists born, M.E.prefix spec xs s m w born trace s' m' w' /\
    contract_post spec xs m w born trace (CallReturn values) m' w'.
Proof.
  intros Hi. remember (CallReturn values) as en eqn:Een.
  destruct Hi as [? ? ? ? ? born _ Hpre Hp Hpost | ? ? ? ? ? ? _ _ _ _ _]; [|discriminate Een].
  subst. split; [exact Hpre|]. exists born. auto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** What the state interpretation says of the world: it is w0, and
    [os_inv] holds of the memory. *)
Lemma os_heap_world σ :
  heap_interp (os_wi w0) σ -∗ ⌜ls_world σ = w0 /\ exists h, os_inv (ls_mem σ) w0 h⌝.
Proof.
  iIntros "(%h & _ & %Hf)". destruct Hf as (_ & _ & _ & -> & Hi). iPureIntro. eauto.
Qed.

(** The errno of w0 is a writable `c: int` ([errno_cell]) of the
    memory of σ, and errno's block lies in its live object. *)
Lemma os_heap_errno σ eb :
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  heap_interp (os_wi w0) σ -∗ ⌜errno_cell (ls_mem σ) (mkPtr eb (Obj eb)) /\ blk_live (ls_mem σ) (eb, 0, 4)⌝.
Proof.
  intros He. iIntros "Hσ". iDestruct (os_heap_world with "Hσ") as %[_ (h & Hi & _)]. iPureIntro.
  destruct (Hi _ He) as [Hp _]. split; [exact (permanent_errno_cell _ _ Hp)|].
  destruct Hp as (eb' & reg & [= <-] & _ & _ & Hl & _ & Hend). exists reg. cbn. split; [exact Hl|lia].
Qed.

(** In the state of σ, the world is w0, `c: fd` (one of w0's) is not
    the log descriptor, and w0's errno is a writable `c: int`: what
    every contract's precondition asks of the world. *)
Lemma os_heap_ready σ eb fd :
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  heap_interp (os_wi w0) σ -∗
  ⌜ls_world σ = w0 /\ ow_log_fd w0 <> Some fd /\ errno_cell (ls_mem σ) (mkPtr eb (Obj eb))⌝.
Proof.
  intros He Hin. iIntros "Hσ". iDestruct (os_heap_errno with "Hσ") as %[Hc _]; [exact He|].
  iDestruct (os_heap_world with "Hσ") as %[Hw (h & _ & _ & Hfd)]. iPureIntro.
  rewrite Forall_forall in Hfd. auto.
Qed.

(** The writable roots errno's span and spans inside the blocks bl lie
    in the blocks errno's and bl's. *)
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

(** The lending frame of a returning call of an OS contract spec that
    keeps the world and releases nothing, and whose writable roots lie
    in the owned blocks bl, which lie in live objects: the blocks are
    handed back, whatever the call left in them, and the state
    interpretation holds of the call's end state. Every piece the
    program owns besides them is untouched. *)
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

Section call.
Context (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_call_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation oexpr := (language.expr (nanofil_lang registry ge)).

(** The rule of a call of an OS contract spec that keeps the world,
    releases nothing, and writes only the owned blocks bl: given its
    precondition from Q (with the blocks live), the blocks are lent to
    the call and handed back holding whatever it left, and every return
    the contract allows ([R]) goes on. *)
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

(** The same for a call that also writes w0's errno ([errno_spans]):
    errno is lent with the blocks bl, and comes back holding whatever
    the call left. The writable roots other than errno's lie in bl. *)
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

(** A call whose contract allows no return: any postcondition. *)
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
