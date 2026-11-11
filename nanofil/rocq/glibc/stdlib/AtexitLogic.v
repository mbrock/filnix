(** Triples for user glibc's `atexit` registration (docs/glibc-ir.md):
    `__new_exitfn`, `__internal_atexit`, `__cxa_atexit` and `atexit`,
    over any registry, world and genv that binds their symbols, so a
    program linked with them uses each as a rule at its call.

    glibc keeps the exit handlers in a list of blocks of 32 slots,
    `__exit_funcs`, which starts as the static block `initial`. A
    registration takes `__exit_funcs_lock` by a compare-and-swap from 0
    to 1, takes the slot after the last used one ([wp_new_exitfn]:
    `__exit_funcs_done` must be 0, and the block's `idx` and
    `__new_exitfn_called` go up by one), fills it with the flavor
    `ef_cxa` (4), the function, its argument and its DSO handle, and
    releases the lock by a compare-and-swap from 1 to 0. Single
    threaded, the lock is free, so neither the wait nor the wake runs.

    [exit_funcs_inv] owns that state while `initial` is the only block
    and holds k registered entries ([entry]) and 32 - k spare slots
    ([spare]). For k below 32 and a function pointer at a nonzero
    address (every module function's is, since data starts at
    [data_base]):

    - [wp_glibc_cxa_atexit]: `__cxa_atexit (fn, arg, dso)` appends the
      entry (fn, arg, dso) and returns 0;
    - [wp_glibc_atexit]: `atexit (fn)` is `__cxa_atexit (fn, null,
      null)`.

    The writes are to the lock, the counter and `initial`, which the
    world interpretation must not read ([wi_ignores]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic MemLogic.
From Glibc Require Import StdlibCode GlibcLogic LeavesLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** glibc's `__new_exitfn`. *)
Definition new_exitfn_fn : func := Eval vm_compute in stdlib_fn "__new_exitfn".
(** glibc's `__internal_atexit`. *)
Definition internal_atexit_fn : func := Eval vm_compute in stdlib_fn "__internal_atexit".
(** glibc's `__GI___cxa_atexit`. *)
Definition cxa_atexit_fn : func := Eval vm_compute in stdlib_fn "__GI___cxa_atexit".
(** glibc's `atexit`. *)
Definition atexit_fn : func := Eval vm_compute in stdlib_fn "atexit".

(** The frame of a call of `__new_exitfn` on p. *)
Lemma new_exitfn_frame p :
  call_frame new_exitfn_fn [WPtr p] =
  Some (mkFrame new_exitfn_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** The frame of a call of `__internal_atexit` on f, a, d and l. *)
Lemma internal_atexit_frame f a d l :
  call_frame internal_atexit_fn [WPtr f; WPtr a; WPtr d; WPtr l] =
  Some (mkFrame internal_atexit_fn [(TAtom "v6", WPtr l); (TAtom "v4", WPtr d); (TAtom "v2", WPtr a);
                                    (TAtom "v0", WPtr f)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** The frame of a call of `__cxa_atexit` on f, a and d. *)
Lemma cxa_atexit_frame f a d :
  call_frame cxa_atexit_fn [WPtr f; WPtr a; WPtr d] =
  Some (mkFrame cxa_atexit_fn [(TAtom "v4", WPtr d); (TAtom "v2", WPtr a); (TAtom "v0", WPtr f)] [] None
          (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** The lock's bytes after it is taken. *)
Lemma lock_take : (if of_bytes [0; 0; 0; 0] =? 0 mod 2 ^ 32 then le_bytes 1 4 else [0; 0; 0; 0]) = [1; 0; 0; 0].
Proof. reflexivity. Qed.

(** The lock's bytes after it is released. *)
Lemma lock_release : (if of_bytes [1; 0; 0; 0] =? 1 mod 2 ^ 32 then le_bytes 0 4 else [1; 0; 0; 0]) = [0; 0; 0; 0].
Proof. reflexivity. Qed.

(** The genv defines `__new_exitfn`, `__internal_atexit` and
    `__cxa_atexit` (the alias of `__GI___cxa_atexit`) as these
    functions. *)
Definition exit_fns (ge : genv) : Prop :=
  find_fn ge (TAtom "__new_exitfn") = Some (Defined new_exitfn_fn) /\
  find_fn ge (TAtom "__internal_atexit") = Some (Defined internal_atexit_fn) /\
  find_fn ge (TAtom "__cxa_atexit") = Some (Defined cxa_atexit_fn).

(** The objects of the exit handler state: `__exit_funcs_lock`,
    `__exit_funcs_done`, `__new_exitfn_called`, `__exit_funcs` and
    the block `initial`, each by its identity and region. *)
Record exit_objs : Type := mkExitObjs {
  xo_lock : Z; xo_lock_reg : region;
  xo_done : Z; xo_done_reg : region;
  xo_called : Z; xo_called_reg : region;
  xo_funcs : Z; xo_funcs_reg : region;
  xo_init : Z; xo_init_reg : region
}.

(** The objects lie below 2^64, the lock and `initial` below 2^63 as
    half checks ask, each cell aligned as its accesses check, and
    `initial` holds its 1040 bytes. *)
Definition exit_layout (x : exit_objs) : Prop :=
  0 <= xo_lock x /\ xo_lock x mod 4 = 0 /\ xo_lock x + 4 <= r_end (xo_lock_reg x) <= 2 ^ 63 /\
  0 <= xo_done x /\ xo_done x + 1 <= r_end (xo_done_reg x) <= 2 ^ 64 /\
  0 <= xo_called x /\ xo_called x + 8 <= r_end (xo_called_reg x) <= 2 ^ 64 /\
  0 <= xo_funcs x /\ xo_funcs x mod 8 = 0 /\ xo_funcs x + 8 <= r_end (xo_funcs_reg x) <= 2 ^ 64 /\
  0 < xo_init x /\ xo_init x mod 8 = 0 /\ xo_init x + 1040 <= r_end (xo_init_reg x) <= 2 ^ 63.

(** The genv binds the four globals to the objects, writable. *)
Definition exit_globals (ge : genv) (x : exit_objs) : Prop :=
  lookup (TAtom "__exit_funcs_lock") (ge_globals ge) = Some (mkPtr (xo_lock x) (Obj (xo_lock x))) /\
  lookup (TAtom "__exit_funcs_done") (ge_globals ge) = Some (mkPtr (xo_done x) (Obj (xo_done x))) /\
  lookup (TAtom "__new_exitfn_called") (ge_globals ge) = Some (mkPtr (xo_called x) (Obj (xo_called x))) /\
  lookup (TAtom "__exit_funcs") (ge_globals ge) = Some (mkPtr (xo_funcs x) (Obj (xo_funcs x))).

(** Every piece of ps is a piece of the object b. *)
Lemma ids_of (b : Z) (ps : list (piece * pval)) :
  Forall (fun lv => piece_id lv.1 = b) ps -> forall l, l ∈ ps.*1 -> piece_id l = b.
Proof.
  intros H l Hl. destruct (list_elem_of_fmap_1 _ _ _ Hl) as [[l' v] [E Hin]]. subst l.
  rewrite Forall_forall in H. exact (H (l', v) Hin).
Qed.

(** Show a list of pieces names only one object. *)
Ltac ids := apply ids_of; cbn; repeat constructor.

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
Module AtexitOn (R : Runtime) (LG0 : LogicSig R).
Module GL := GlibcLogicOn R LG0.
Module ML := MemLogicOn R LG0.
Module LV := LeavesOn R LG0.
Module LG := LG0.
Module L := LG.L.
Import L LG GL ML LV.

Local Opaque new_exitfn_fn internal_atexit_fn cxa_atexit_fn atexit_fn.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance atexit_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The world interpretation does not read the object b, ending at e:
    a write of bytes, or of bytes and an aux slot, inside it, with
    pieces of b written over the ghost heap, keeps it. *)
Definition wi_ignores (b e : Z) : Prop :=
  forall m wd h ps a n x c, b <= a -> a + n <= e -> (forall l, l ∈ ps.*1 -> piece_id l = b) -> wi m wd h ->
    wi (store_bytes m a n x) wd (overwrite ps h) /\ wi (store_bytes (store_aux m a c) a n x) wd (overwrite ps h).

(** The world interpretation ignores the lock, the counter and
    `initial`, the objects a registration writes. *)
Definition exit_wi (x : exit_objs) : Prop :=
  wi_ignores (xo_lock x) (r_end (xo_lock_reg x)) /\ wi_ignores (xo_called x) (r_end (xo_called_reg x)) /\
  wi_ignores (xo_init x) (r_end (xo_init_reg x)).

(** A write's world premise, from [wi_ignores] H of its object. *)
Ltac ign H :=
  let m := fresh "m" in let wd := fresh "wd" in let h := fresh "h" in let Hw := fresh "Hw" in
  intros m wd h ? Hw;
  first [ refine (proj1 (H m wd h _ _ _ _ CNone _ _ _ Hw)); [lia | lia | ids]
        | refine (proj2 (H m wd h _ _ _ _ _ _ _ _ Hw)); [lia | lia | ids] ].

(** Close the instance premise a rule's eapply leaves. *)
Ltac inst := lazymatch goal with |- SafepointStable _ => exact _ | _ => idtac end.

(** One step whose premises reduce, by the instruction it runs: a pure
    let, a flight, entering a block, or a goto. *)
Ltac st :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (ERun (mkFrame _ _ _ _ ?pos)) _) =>
      lazymatch pos with
      | Exec _ (Let _ _ _ _ :: _) _ =>
          eapply step_wand;
            [eapply wp_let; inst; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity] |]
      | Exec _ (Flight _ _ _ _ :: _) _ =>
          eapply step_wand; [eapply wp_flight; inst; [reflexivity | reflexivity | reflexivity] |]
      | Enter _ _ =>
          eapply step_wand; [eapply wp_enter; inst; [reflexivity | reflexivity] |]; cbn [b_insts b_jump]
      | Exec _ [] (JGoto _) => eapply step_wand; [eapply wp_goto; inst |]
      end
  end.

(** A let copying the global s, bound to p in the genv by Hs. *)
Ltac st_global Hs :=
  eapply step_wand;
    [eapply wp_let; inst;
       [reflexivity | reflexivity | cbn [map2_option value_x]; rewrite Hs; reflexivity | intros ?; reflexivity] |].

(** A branch, its condition simplified. *)
Ltac br := eapply step_wand; [eapply wp_branch; inst; reflexivity |]; decide_branch.

(** The end of `__new_exitfn` from the block L121, slot k taken:
    marking it `ef_us`, counting the call, returning the slot. *)
Ltac tail58 k c Hc Hgcl Hwib Hwcl :=
  st;
  rule1 "Hil" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]);
  rule2 "Hil" "Hfl0" ltac:(eapply wp_raw_store; inst;
    [reflexivity | reflexivity | reflexivity | arith | ign Hwib]);
  st_global Hgcl;
  rule1 "Hcl" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]);
  rule2 "Hcl" "Hcc" ltac:(eapply wp_raw_load; inst; [reflexivity | reflexivity | reflexivity | arith]);
  rewrite (Z.mod_small c (2 ^ 64)); [|lia]; st;
  rule1 "Hcl" ltac:(eapply wp_renew; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith]);
  rule2 "Hcl" "Hcc" ltac:(eapply wp_raw_store; inst; [reflexivity | reflexivity | reflexivity | arith | ign Hwcl]);
  st; st; iApply wp_ret; [reflexivity | reflexivity |]; nx; simp.

(** A slot of `initial` at offset o: its flavor v, function x,
    argument y and DSO handle z. *)
Definition slot (b o v : Z) (x y z : ptr) : iProp Σ :=
  icell b o v ∗ pcell b (o + 8) x ∗ pcell b (o + 16) y ∗ pcell b (o + 24) z.

(** A registered entry: a slot of flavor `ef_cxa` (4) holding the
    function, argument and DSO handle of e. *)
Definition entry (b o : Z) (e : ptr * ptr * ptr) : iProp Σ := slot b o 4 e.1.1 e.1.2 e.2.

(** A spare slot, holding anything. *)
Definition spare (b o : Z) : iProp Σ := ∃ v x y z, slot b o v x y z.

(** The block `initial` at b, the only block, with the entries ents:
    its life, its null `next`, its `idx` the number of entries, the
    entries in its first slots and the rest spare. *)
Definition exit_block (b : Z) (reg : region) (ents : list (ptr * ptr * ptr)) : iProp Σ :=
  live b reg ∗ pcell b 0 null ∗ icell b 8 (Z.of_nat (List.length ents)) ∗
  ([∗ list] i ↦ e ∈ ents, entry b (16 + 32 * Z.of_nat i) e) ∗
  ([∗ list] i ∈ seqZ (Z.of_nat (List.length ents)) (32 - Z.of_nat (List.length ents)), spare b (16 + 32 * i)).

(** The spare slots from k, below 32, are slot k's and those from
    k + 1. *)
Lemma spares_cons b k :
  0 <= k < 32 ->
  ([∗ list] i ∈ seqZ k (32 - k), spare b (16 + 32 * i)) ⊣⊢
  spare b (16 + 32 * k) ∗ [∗ list] i ∈ seqZ (k + 1) (32 - (k + 1)), spare b (16 + 32 * i).
Proof.
  intros Hk. rewrite (seqZ_cons k (32 - k)); [|lia]. rewrite big_sepL_cons.
  replace (Z.succ k) with (k + 1) by lia. replace (Z.pred (32 - k)) with (32 - (k + 1)) by lia. done.
Qed.

(** `__new_exitfn (&__exit_funcs)`, `__exit_funcs` holding `initial`
    with k = |ents| entries, k below 32, `__exit_funcs_done` 0 and
    `__new_exitfn_called` c: it takes slot k, marking it `ef_us` (1),
    raises `idx` to k + 1 and the counter by one, and returns the
    slot's pointer. *)
Lemma wp_new_exitfn x ents c Φ :
  exit_layout x -> exit_globals ge x -> exit_wi x -> (List.length ents < 32)%nat -> 0 <= c < 2 ^ 64 ->
  live (xo_done x) (xo_done_reg x) ∗ ibyte (xo_done x) 0 0 ∗
  live (xo_called x) (xo_called_reg x) ∗ icell (xo_called x) 0 c ∗
  live (xo_funcs x) (xo_funcs_reg x) ∗ pcell (xo_funcs x) 0 (mkPtr (xo_init x) (Obj (xo_init x))) ∗
  exit_block (xo_init x) (xo_init_reg x) ents -∗
  (live (xo_done x) (xo_done_reg x) ∗ ibyte (xo_done x) 0 0 ∗
   live (xo_called x) (xo_called_reg x) ∗ icell (xo_called x) 0 ((c + 1) mod 2 ^ 64) ∗
   live (xo_funcs x) (xo_funcs_reg x) ∗ pcell (xo_funcs x) 0 (mkPtr (xo_init x) (Obj (xo_init x))) ∗
   live (xo_init x) (xo_init_reg x) ∗ pcell (xo_init x) 0 null ∗
   icell (xo_init x) 8 (Z.of_nat (List.length ents) + 1) ∗
   ([∗ list] i ↦ e ∈ ents, entry (xo_init x) (16 + 32 * Z.of_nat i) e) ∗
   ([∗ list] i ∈ seqZ (Z.of_nat (List.length ents) + 1) (32 - (Z.of_nat (List.length ents) + 1)),
      spare (xo_init x) (16 + 32 * i)) ∗
   (∃ y z w, slot (xo_init x) (16 + 32 * Z.of_nat (List.length ents)) 1 y z w) -∗
   Φ (Ret (WPtr (mkPtr (xo_init x + 16 + 32 * Z.of_nat (List.length ents)) (Obj (xo_init x)))))) -∗
  WP (ERun (mkFrame new_exitfn_fn [(TAtom "v0", WPtr (mkPtr (xo_funcs x) (Obj (xo_funcs x))))] [] None
              (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct x as [lk lkr dn dnr cl clr fs fsr ib ibr]. unfold exit_layout, exit_globals, exit_wi.
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg].
  intros (Hl0 & Hl4 & Hle & Hd0 & Hde & Hc0 & Hce & Hf0 & Hf8 & Hfe & Hi0 & Hi8 & Hie)
    (Hglk & Hgdn & Hgcl & Hgfs) (Hwlk & Hwcl & Hwib) Hk Hc.
  unfold exit_block. remember (Z.of_nat (List.length ents)) as k eqn:Ek. assert (Hk' : 0 <= k < 32) by lia.
  iIntros "(Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hil & Hnext & Hidx & Hents & Hspares) HΦ".
  rewrite (spares_cons ib k Hk'). iDestruct "Hspares" as "[(%v0 & %y & %z & %w & Hfl0 & Hy & Hz & Hw) Hspares]".
  st. st_global Hgdn.
  rule1 "Hdl" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  rule2 "Hdl" "Hdb" ltac:(eapply wp_raw_load_byte; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | left; reflexivity | arith]). br. st.
  rule1 "Hfl" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Hfl Hfc Hil");
    [reflexivity | reflexivity | reflexivity | arith | arith | arith |].
  nx. iIntros "Hfl Hfc Hil". cbn [live_cap]. st. st. st. st. st. br. st. st.
  rule1 "Hil" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hidx" ltac:(eapply wp_raw_load; inst;
    [reflexivity | reflexivity | reflexivity | arith]). st. st. st. br.
  destruct (Z.ltb_spec 0 k) as [Hpos|Hzero]; simp.
  - destruct (lookup_lt_is_Some_2 ents (Z.to_nat (k - 1))) as [e He]; [lia|].
    iDestruct (big_sepL_lookup_acc _ ents _ e He with "Hents") as "[(Hef & Hex) Hents]".
    rewrite Z2Nat.id; [|lia].
    st. st. st. st. st. simp.
    rule1 "Hil" ltac:(eapply wp_check_read; inst;
      [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
    rule2 "Hil" "Hef" ltac:(eapply wp_raw_load; inst;
      [reflexivity | reflexivity | reflexivity | arith]). iDestruct ("Hents" with "[$Hef $Hex]") as "Hents".
    st. br. st. br. st. st. br. st. st. st. st. br.
    st. st. st. st. st. st. simp.
    rule1 "Hil" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
    rule2 "Hil" "Hidx" ltac:(eapply wp_raw_store; inst;
      [reflexivity | reflexivity | reflexivity | arith | ign Hwib]). st. st. st. st. br.
    tail58 k c Hc Hgcl Hwib Hwcl. rewrite Zmod_mod.
    replace (ib + 16 + k * 32) with (ib + 16 + 32 * k) by lia.
    iApply "HΦ". iFrame "Hdl Hdb Hcl Hcc Hfl Hfc Hil Hnext Hidx Hents Hspares". iExists y, z, w.
    iFrame "Hfl0 Hy Hz Hw".
  - assert (k = 0) as -> by lia. st. br. st. st.
    rule1 "Hil" ltac:(eapply wp_renew; inst;
      [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith]).
    rule2 "Hil" "Hidx" ltac:(eapply wp_raw_store; inst;
      [reflexivity | reflexivity | reflexivity | arith | ign Hwib]).
    rule1 "Hil" ltac:(eapply wp_half_check_read; inst;
      [reflexivity | reflexivity | reflexivity | left; reflexivity | arith | arith | arith | arith | arith]).
    iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 null ibr with "Hil Hnext []");
      [reflexivity | reflexivity | reflexivity | arith | arith | arith | done |]. nx. iIntros "Hil Hnext _".
    st. st. st. st. st. br. st. st. br. st. br. st. st. st. br. st. st. st. br. st. st. st.
    rule1 "Hil" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
    rule2 "Hil" "Hidx" ltac:(eapply wp_raw_store; inst;
      [reflexivity | reflexivity | reflexivity | arith | ign Hwib]).
    st. st. st. st. br. tail58 0 c Hc Hgcl Hwib Hwcl. rewrite Zmod_mod Z.mul_0_r !Z.add_0_r.
    iApply "HΦ". iFrame "Hdl Hdb Hcl Hcc Hfl Hfc Hil Hnext Hidx Hents Hspares". iExists y, z, w.
    iFrame "Hfl0 Hy Hz Hw".
Qed.

(** The exit handler state with the entries ents registered and the
    counter `__new_exitfn_called` at c: the lock free (0), the exit not
    begun (`__exit_funcs_done` 0), `__exit_funcs` holding `initial`,
    and `initial` the only block, holding ents. *)
Definition exit_funcs_inv (x : exit_objs) (ents : list (ptr * ptr * ptr)) (c : Z) : iProp Σ :=
  ⌜(List.length ents <= 32)%nat /\ 0 <= c < 2 ^ 64⌝ ∗
  live (xo_lock x) (xo_lock_reg x) ∗ bytes (xo_lock x) 0 [0; 0; 0; 0] ∗
  live (xo_done x) (xo_done_reg x) ∗ ibyte (xo_done x) 0 0 ∗
  live (xo_called x) (xo_called_reg x) ∗ icell (xo_called x) 0 c ∗
  live (xo_funcs x) (xo_funcs_reg x) ∗ pcell (xo_funcs x) 0 (mkPtr (xo_init x) (Obj (xo_init x))) ∗
  exit_block (xo_init x) (xo_init_reg x) ents.

(** `initial` with the entry e filled in after ents. *)
Lemma exit_block_snoc b reg ents e :
  live b reg ∗ pcell b 0 null ∗ icell b 8 (Z.of_nat (List.length ents) + 1) ∗
  ([∗ list] i ↦ e' ∈ ents, entry b (16 + 32 * Z.of_nat i) e') ∗ entry b (16 + 32 * Z.of_nat (List.length ents)) e ∗
  ([∗ list] i ∈ seqZ (Z.of_nat (List.length ents) + 1) (32 - (Z.of_nat (List.length ents) + 1)),
     spare b (16 + 32 * i)) ⊢
  exit_block b reg (ents ++ [e]).
Proof.
  rewrite /exit_block length_app big_sepL_snoc. cbn [List.length].
  replace (Z.of_nat (List.length ents + 1)) with (Z.of_nat (List.length ents) + 1) by lia.
  iIntros "($ & $ & $ & $ & $ & $)".
Qed.

(** A compare-and-swap's world premise, from [wi_ignores] H of its
    object. *)
Ltac cas_ign H := intros _; ign H.

(** `__internal_atexit (fn, arg, dso, &__exit_funcs)`, fn at a nonzero
    address, with k = |ents| below 32: under the lock, it appends the
    entry (fn, arg, dso) and counts the call, and returns 0. *)
Lemma wp_internal_atexit x ents c fnp argp dsop Φ :
  exit_layout x -> exit_globals ge x -> exit_wi x -> (List.length ents < 32)%nat ->
  0 < ptr_addr fnp < 2 ^ 64 -> find_fn ge (TAtom "__new_exitfn") = Some (Defined new_exitfn_fn) ->
  exit_funcs_inv x ents c -∗
  (exit_funcs_inv x (ents ++ [(fnp, argp, dsop)]) ((c + 1) mod 2 ^ 64) -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (mkFrame internal_atexit_fn [(TAtom "v6", WPtr (mkPtr (xo_funcs x) (Obj (xo_funcs x))));
       (TAtom "v4", WPtr dsop); (TAtom "v2", WPtr argp); (TAtom "v0", WPtr fnp)] [] None
       (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct x as [lk lkr dn dnr cl clr fs fsr ib ibr]. intros Hlay Hgl Hwi Hk Hfp Hnf.
  pose proof Hlay as Hl_. destruct Hl_ as (Hl0 & Hl4 & Hle & _ & _ & _ & _ & _ & _ & _ & Hi0 & Hi8 & Hie).
  pose proof Hgl as Hg_. destruct Hg_ as (Hglk & _). pose proof Hwi as Hw_. destruct Hw_ as (Hwlk & _ & Hwib).
  iIntros "((%Hk32 & %Hc) & Hll & Hlb & Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hblk) HΦ".
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg]
    in *.
  st. st. st. st. br. st. st_global Hglk.
  rule1 "Hll" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hll" "Hlb" ltac:(eapply wp_raw_cas_w; inst;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwlk]). rewrite lock_take.
  st. br. st. st. br. st.
  eapply step_wand; [eapply wp_call_bind; inst; [reflexivity | exact Hnf | apply new_exitfn_frame] |].
  iApply (wp_new_exitfn (mkExitObjs lk lkr dn dnr cl clr fs fsr ib ibr) ents c
            with "[$Hdl $Hdb $Hcl $Hcc $Hfl $Hfc $Hblk]");
    [exact Hlay | exact Hgl | exact Hwi | exact Hk | exact Hc |].
  iIntros "(Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hil & Hnext & Hidx & Hents & Hspares &
            (%y & %z & %w & Hf & Hy & Hz & Hw))".
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg].
  remember (Z.of_nat (List.length ents)) as k eqn:Ek. assert (Hk' : 0 <= k < 32) by lia.
  iExists _. iSplit; [iPureIntro; reflexivity|]. nx. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  st. st. br. st. st.
  rule1 "Hil" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hy" ltac:(eapply wp_raw_store_pointer; inst;
    [reflexivity | reflexivity | reflexivity | arith | arith | ign Hwib]).
  st.
  rule1 "Hil" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hil" "Hz" ltac:(eapply wp_raw_store_pointer; inst;
    [reflexivity | reflexivity | reflexivity | arith | arith | ign Hwib]).
  st.
  rule1 "Hil" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hil" "Hw" ltac:(eapply wp_raw_store_pointer; inst;
    [reflexivity | reflexivity | reflexivity | arith | arith | ign Hwib]).
  rule1 "Hil" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hil" "Hf" ltac:(eapply wp_raw_store; inst; [reflexivity | reflexivity | reflexivity | arith | ign Hwib]).
  st_global Hglk.
  rule1 "Hll" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_sub_bytes_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 [1; 0; 0; 0] (WInt 1)
            (DfracOwn 1) (DfracOwn 1) with "Hll Hlb");
    [reflexivity | reflexivity | reflexivity | reflexivity | left; reflexivity | arith |]. nx. iIntros "Hll Hlb".
  st. st.
  rule1 "Hll" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hll" "Hlb" ltac:(eapply wp_raw_cas_w; inst;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwlk]). rewrite lock_release.
  st. br. st. st. br. st.
  iApply wp_ret; [reflexivity | reflexivity |]. nx.
  rewrite (Z.mod_small 4 (2 ^ 64)); [|lia].
  iApply "HΦ". rewrite /exit_funcs_inv.
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg].
  iSplit. { iPureIntro. rewrite length_app /=. split; [lia | apply Z.mod_pos_bound; lia]. }
  iFrame "Hll Hlb Hdl Hdb Hcl Hcc Hfl Hfc". iApply exit_block_snoc. subst k.
  iFrame "Hil Hnext Hidx Hents Hspares". iFrame "Hf Hy Hz Hw".
Qed.

(** `__cxa_atexit (fn, arg, dso)`, fn at a nonzero address, with
    k = |ents| below 32: it appends the entry (fn, arg, dso), counts
    the call, and returns 0. *)
Lemma wp_glibc_cxa_atexit x ents c fnp argp dsop Φ :
  exit_layout x -> exit_globals ge x -> exit_wi x -> exit_fns ge -> (List.length ents < 32)%nat ->
  0 < ptr_addr fnp < 2 ^ 64 ->
  exit_funcs_inv x ents c -∗
  (exit_funcs_inv x (ents ++ [(fnp, argp, dsop)]) ((c + 1) mod 2 ^ 64) -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (mkFrame cxa_atexit_fn [(TAtom "v4", WPtr dsop); (TAtom "v2", WPtr argp); (TAtom "v0", WPtr fnp)]
       [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hlay Hgl Hwi (Hnf & Hia & _) Hk Hfp. pose proof Hgl as Hg_. destruct Hg_ as (_ & _ & _ & Hgfs).
  iIntros "Hinv HΦ". st. st_global Hgfs.
  eapply step_wand; [eapply wp_call_bind; inst; [reflexivity | exact Hia | apply internal_atexit_frame] |].
  iApply (wp_internal_atexit with "Hinv");
    [exact Hlay | exact Hgl | exact Hwi | exact Hk | exact Hfp | exact Hnf |].
  iIntros "Hinv". iExists _. iSplit; [iPureIntro; reflexivity|]. nx. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iApply ("HΦ" with "Hinv").
Qed.

(** `atexit (fn)`, fn at a nonzero address, with k = |ents| below 32:
    `__cxa_atexit (fn, null, null)`, appending the entry (fn, null,
    null) and returning 0. *)
Lemma wp_glibc_atexit x ents c fnp Φ :
  exit_layout x -> exit_globals ge x -> exit_wi x -> exit_fns ge -> (List.length ents < 32)%nat ->
  0 < ptr_addr fnp < 2 ^ 64 ->
  exit_funcs_inv x ents c -∗
  (exit_funcs_inv x (ents ++ [(fnp, null, null)]) ((c + 1) mod 2 ^ 64) -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (mkFrame atexit_fn [(TAtom "v0", WPtr fnp)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hlay Hgl Hwi Hfns Hk Hfp. pose proof Hfns as Hf_. destruct Hf_ as (_ & _ & Hca).
  iIntros "Hinv HΦ". st.
  eapply step_wand; [eapply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ [WPtr fnp; WPtr null; WPtr null]); inst;
    [reflexivity | exact Hca | apply cxa_atexit_frame] |].
  iApply (wp_glibc_cxa_atexit with "Hinv");
    [exact Hlay | exact Hgl | exact Hwi | exact Hfns | exact Hk | exact Hfp |].
  iIntros "Hinv". iExists _. iSplit; [iPureIntro; reflexivity|]. nx. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iApply ("HΦ" with "Hinv").
Qed.

End rules.
End AtexitOn.
