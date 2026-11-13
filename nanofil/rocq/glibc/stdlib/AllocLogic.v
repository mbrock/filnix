(** Userland glibc in Fil-C keeps ptmalloc's tcache fast path at the
    entry of `c: malloc`, while routing actual heap allocation and
    deallocation to the runtime primitives `zgc_alloc` and `zgc_free`.
    This module proves [[hoare-triple|Hoare triples]] for `c: malloc`
    and `c: free` over any [[runtime]] registry, world, and
    [[genv|global environment]] that binds their symbols.

    In `c: malloc`, the prelude rounds the requested byte count up to an
    aligned chunk size and checks whether it fits below the tcache limit
    in `mp_.tcache_max_bytes`. When it fits, `c: malloc` reads the
    corresponding bin through the thread's `tcache` pointer, which
    points to the read-only, zeroed `__tcache_dummy` object. Because
    every bin in that dummy table holds null, every request falls
    through to `__libc_malloc2`, which calls `zgc_alloc`.

    Callers only need shared read access to those tcache globals because
    `c: malloc` never modifies them. Theorem [wp_glibc_malloc]
    preserves that [tcache_idle] invariant and returns a fresh
    16-aligned object for any size below 2^64. Likewise, [wp_glibc_free]
    releases a live heap object, and [wp_glibc_free_null] ignores a null
    pointer. *)

From Stdlib Require Import ZArith Lia.
From Glibc Require Import StrlenBits.
Open Scope Z_scope.

(** Glibc's `c: request2size` rounds a chunk size down to a multiple of
    16 by masking off the low four bits. Lemma [land_align16] proves
    that this bitwise conjunction with `~15` equals a - a mod 16. *)
Lemma land_align16 a : 0 <= a < 2 ^ 64 -> Z.land a 18446744073709551600 = a - a mod 16.
Proof.
  intros Ha. change 18446744073709551600 with (Z.lxor (Z.ones 64) (Z.ones 4)).
  assert (E : Z.land a (Z.lxor (Z.ones 64) (Z.ones 4)) + Z.land a (Z.ones 4) = a).
  { rewrite Z.add_nocarry_lxor.
    - apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, !Z.land_spec, Z.lxor_spec, !Z.testbit_ones by lia.
      rewrite (proj2 (Z.leb_le 0 n) Hn).
      destruct (Z.testbit a n) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec n 4), (Z.ltb_spec n 64); cbn; try reflexivity; try lia.
      rewrite (bits64 a n Ha ltac:(lia)) in E. discriminate.
    - apply Z.bits_inj'. intros n Hn. rewrite Z.bits_0, !Z.land_spec, Z.lxor_spec, !Z.testbit_ones by lia.
      rewrite (proj2 (Z.leb_le 0 n) Hn).
      destruct (Z.testbit a n), (Z.ltb_spec n 4), (Z.ltb_spec n 64); cbn; try reflexivity; lia. }
  rewrite Z.land_ones in E by lia. change (2 ^ 4) with 16 in E. lia.
Qed.

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic MemLogic.
From Glibc Require Import StdlibCode GlibcLogic StrlenBits LeavesLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** [malloc_fn] extracts the decoded IR body of glibc's
    `__GI___libc_malloc`. *)
Definition malloc_fn : func := Eval vm_compute in stdlib_fn "__GI___libc_malloc".
(** [malloc2_fn] extracts the decoded IR body of `__libc_malloc2`,
    which `c: link.pl` renames to `malloc#__libc_malloc2`. *)
Definition malloc2_fn : func := Eval vm_compute in stdlib_fn "malloc#__libc_malloc2".
(** [free_fn] extracts the decoded IR body of glibc's
    `__GI___libc_free`. *)
Definition free_fn : func := Eval vm_compute in stdlib_fn "__GI___libc_free".

(** The module [AllocOn] proves the `c: malloc` and `c: free`
    specifications over an arbitrary [[runtime]] R and logic instance
    LG0. *)
Module AllocOn (R : Runtime) (LG0 : LogicSig R).
Module GL := GlibcLogicOn R LG0.
Module LV := LeavesOn R LG0.
Module LG := LG0.
Module L := LG.L.
Import L LG GL LV.

Local Opaque malloc_fn malloc2_fn free_fn.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** Every Iris proof needs a state interpretation linking memory and
    world state to the operational semantics. [alloc_irisGS] builds that
    instance from [registry], [wi], and [ge]. *)
Local Instance alloc_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** [gexpr] abbreviates the expression type of the parameterized
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Applying a step rule creates a side condition showing that the world
    stays valid across garbage-collection safepoints. The tactic [inst]
    closes that [SafepointStable] obligation by typeclass search. *)
Ltac inst := lazymatch goal with |- SafepointStable _ => exact _ | _ => idtac end.

(** The tactic [st] advances the proof by one symbolic IR step,
    dispatching on whether the frame sits at a let binding, a
    [[flight]], a block entry, or a jump. *)
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

(** Functions in the prelude read global variables such as `mp_` and
    `tcache` before dereferencing them. The tactic [st_global] steps
    past a global pointer load using its binding hypothesis Hs. *)
Ltac st_global Hs :=
  eapply step_wand;
    [eapply wp_let; inst;
       [reflexivity | reflexivity | cbn [map2_option value_x]; rewrite Hs; reflexivity | intros ?; reflexivity] |].

(** The tactic [br] steps across a conditional branch and immediately
    simplifies its boolean condition. *)
Ltac br := eapply step_wand; [eapply wp_branch; inst; reflexivity |]; decide_branch.

(** Allocating a fresh 16-aligned heap object of n bytes must preserve
    the [[state-interpretation|world interpretation]] [wi]. Predicate
    [alloc_keeps] states that preservation condition as required by
    [wp_alloc_any]. *)
Definition alloc_keeps (n : Z) : Prop :=
  forall m wd h base, fresh m (heap_req 16 n) base -> wi m wd h ->
    wi (allocated m (heap_req 16 n) base) wd (overwrite (obj_ps base (heap_req 16 n)) h).

(** Calling `__libc_malloc2` with size n below 2^64 delegates directly
    to `zgc_alloc`. Whenever [alloc_keeps] holds, [wp_libc_malloc2]
    proves that the call either stalls or returns a fresh 16-aligned
    object owning its pieces. *)
Lemma wp_libc_malloc2 n Φ :
  0 <= n < 2 ^ 64 -> alloc_keeps n ->
  (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ -∗
     obj base (heap_req 16 n) -∗ Φ (Ret (WPtr (mkPtr base (Obj base))))) -∗
  WP (ERun (mkFrame malloc2_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hn Hk. iIntros "HΦ". st.
  iApply (wp_alloc_any _ _ _ _ _ _ _ _ _ _ _ _ _ n);
    [cbn; rewrite Z.mod_small; [reflexivity | lia] | lia | exact Hk |].
  nx. iIntros (base) "%Hb Hobj".
  iApply wp_ret; [reflexivity | reflexivity |]. nx.
  iApply ("HΦ" with "[%] Hobj"). exact Hb.
Qed.

(** Calling `c: free` on a non-null pointer to a live heap object b
    delegates to `zgc_free`. Provided the global environment models
    heap deallocation with [frees_heap] and freeing b preserves [wi],
    [wp_glibc_free] consumes b's liveness token and returns void. *)
Lemma wp_glibc_free b reg Φ :
  frees_heap (ge_free ge) -> find_fn ge zgc_free_name = None -> lookup zgc_free_name (ge_globals ge) = None ->
  r_kind reg = Heap -> b <> 0 ->
  (forall m wd h rs, h !! PLive b = Some (VLive reg) ->
     replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs -> wi m wd h ->
     wi (mkMem (m_bytes m) rs (m_aux m)) wd (overwrite [(PLive b, VFreed)] h)) ->
  live b reg -∗ Φ RetVoid -∗
  WP (ERun (mkFrame free_fn [(TAtom "v0", WPtr (mkPtr b (Obj b)))] [] None (Enter (TAtom "start") None))
      : gexpr) {{ Φ }}.
Proof.
  intros Hf Hfn Hdata Hk Hb Hwi. iIntros "Hl HΦ". st.
  iApply (wp_free_sym with "Hl"); [reflexivity | exact Hf | exact Hfn | exact Hdata | reflexivity
                                  | exact Hk | exact Hb | exact Hwi |].
  nx. iApply wp_ret_void. nx. iExact "HΦ".
Qed.

(** Calling `c: free` on a null pointer passes null to `zgc_free`, which
    is a no-op. Lemma [wp_glibc_free_null] proves that the call returns
    void without requiring any heap ownership. *)
Lemma wp_glibc_free_null Φ :
  frees_heap (ge_free ge) -> find_fn ge zgc_free_name = None -> lookup zgc_free_name (ge_globals ge) = None ->
  Φ RetVoid -∗
  WP (ERun (mkFrame free_fn [(TAtom "v0", WPtr null)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hf Hfn Hdata. iIntros "HΦ". st.
  iApply wp_free_null_sym; [reflexivity | exact Hf | exact Hfn | exact Hdata | reflexivity |].
  nx. iApply wp_ret_void. nx. iExact "HΦ".
Qed.

(** Because `c: malloc` only reads the tcache globals, callers can share
    read access to them without giving up exclusive ownership. Predicate
    [tcache_idle] bundles fractional shares of `mp_`, `tcache`, and the
    64 null bins in `__tcache_dummy`. *)
Definition tcache_idle (dq : dfrac) (mp_b tc_b dummy_b : Z) (mp_reg tc_reg dummy_reg : region) : iProp Σ :=
  ⌜0 <= mp_b /\ mp_b + 128 <= r_end mp_reg <= 2 ^ 64 /\ 0 <= tc_b /\ tc_b mod 8 = 0 /\
   tc_b + 8 <= r_end tc_reg <= 2 ^ 64 /\ 0 <= dummy_b /\ dummy_b mod 8 = 0 /\
   dummy_b + 664 <= r_end dummy_reg <= 2 ^ 64⌝ ∗
  liveq dq mp_b mp_reg ∗ icellq dq mp_b 120 1041 ∗
  liveq dq tc_b tc_reg ∗ pcellq dq tc_b 0 (mkPtr dummy_b (Ro dummy_b)) ∗
  liveq dq dummy_b dummy_reg ∗ [∗ list] i ∈ seqZ 0 64, pcellq dq dummy_b (152 + 8 * i) null.

(** [malloc2_frame] states the initial call [[frame]] constructed when
    entering `__libc_malloc2` with request size n. *)
Lemma malloc2_frame n :
  call_frame malloc2_fn [WInt n] =
  Some (mkFrame malloc2_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** Every branch of `c: malloc`'s tcache prelude ends at block `L7`,
    which calls `__libc_malloc2` and returns its result. The tactic
    [l7] steps through that call using [wp_libc_malloc2] and restores
    [tcache_idle] to the caller. *)
Ltac l7 n Hn Hk Hm2 :=
  st;
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ [WInt n] malloc2_fn _);
    [transitivity (Some [WInt (n mod 2 ^ 64)]); [reflexivity | rewrite Z.mod_small; [reflexivity | lia]]
    | exact Hm2 | apply malloc2_frame |];
  nx; iApply (wp_libc_malloc2 with "[-]"); [exact Hn | exact Hk |];
  iIntros (base) "%Hb Hobj"; iExists _; iSplit; [iPureIntro; reflexivity|]; nx;
  iApply wp_ret; [reflexivity | reflexivity |]; nx;
  iApply ("HΦ" with "[%] Hobj [-]"); [assumption | rewrite /tcache_idle; iFrame; iPureIntro; lia].

(** After computing the chunk size, the tcache prelude reads
    `mp_.tcache_max_bytes` and compares it with the request. The tactic
    [join] steps through that global read and its comparison branch. *)
Ltac join Hmp :=
  st; st_global Hmp; st;
  rule1 "Hmpl" ltac:(eapply wp_check_read_dq; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]);
  rule2 "Hmpl" "Hmpc" ltac:(eapply wp_raw_load_read_dq; inst;
    [reflexivity | reflexivity | left; reflexivity | arith]); st; br.

(** [seqZ_bin] confirms that any small-bin index i below 64 appears at
    position i in `seqZ 0 64`. *)
Lemma seqZ_bin i : 0 <= i < 64 -> seqZ 0 64 !! Z.to_nat i = Some i.
Proof. intros Hi. rewrite lookup_seqZ_lt; [f_equal; lia | lia]. Qed.

(** Small allocations check whether a cached chunk is waiting in the
    thread's dummy tcache table before falling back to the runtime
    allocator. The tactic [l26] steps through block `L26` to verify the
    bin bounds check, load the `tcache` pointer, read the null bin
    entry, and restore the remaining bins. *)
Ltac l26 i Htc dq dummy_reg :=
  st; st; st; st; br; st; st_global Htc;
  rule1 "Htcl" ltac:(eapply wp_check_read_dq; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]);
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Htcl Htcc Hdl");
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith |];
  nx; iIntros "Htcl Htcc Hdl"; st; st; st; simp;
  iDestruct (big_sepL_lookup_acc _ _ (Z.to_nat i) i with "Hbins") as "[Hbin Hbins]"; [apply seqZ_bin; lia|];
  rule1 "Hdl" ltac:(eapply wp_check_read_dq; inst;
    [reflexivity | reflexivity | right; reflexivity | arith | arith | arith]);
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (152 + 8 * i) null dummy_reg dq dq dq
            with "Hdl Hbin []");
    [reflexivity | reflexivity | right; reflexivity | arith | arith | arith | by cbn |];
  nx; iIntros "Hdl Hbin _"; iDestruct ("Hbins" with "Hbin") as "Hbins"; st; st; st; br.

(** Calling `c: malloc` with any size n below 2^64 either stalls or
    returns a fresh 16-aligned heap object. Theorem [wp_glibc_malloc]
    proves this specification and restores [tcache_idle] across every
    path through the prelude, provided the global environment binds the
    tcache globals and [alloc_keeps] holds. *)
Lemma wp_glibc_malloc n dq mp_b tc_b dummy_b mp_reg tc_reg dummy_reg Φ :
  0 <= n < 2 ^ 64 -> alloc_keeps n ->
  lookup (TAtom "malloc#mp_") (ge_globals ge) = Some (mkPtr mp_b (Obj mp_b)) ->
  lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc_b (Obj tc_b)) ->
  find_fn ge (TAtom "malloc#__libc_malloc2") = Some (Defined malloc2_fn) ->
  tcache_idle dq mp_b tc_b dummy_b mp_reg tc_reg dummy_reg -∗
  (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ -∗
     obj base (heap_req 16 n) -∗ tcache_idle dq mp_b tc_b dummy_b mp_reg tc_reg dummy_reg -∗
     Φ (Ret (WPtr (mkPtr base (Obj base))))) -∗
  WP (ERun (mkFrame malloc_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hn Hk Hmp Htc Hm2. iIntros "Hidle HΦ".
  iDestruct "Hidle" as "(%Hlay & Hmpl & Hmpc & Htcl & Htcc & Hdl & Hbins)".
  destruct Hlay as (Hm0 & Hmend & Ht0 & Ht8 & Htend & Hd0 & Hd8 & Hdend).
  st. st. br.
  destruct (Z.ltb_spec 9223372036854775807 n) as [Hbig|Hsmall]; simp.
  - join Hmp.
    l7 n Hn Hk Hm2.
  - st. st. st. st. br.
    destruct (Z.ltb_spec (n + 8 + 15) 32) as [Hs32|Hb32]; simp.
    + join Hmp. l26 0 Htc dq dummy_reg. l7 n Hn Hk Hm2.
    + st. st. st. simp. rewrite land_align16; [|lia].
      remember (n + 8 + 15 - (n + 8 + 15) mod 16) as nb eqn:Enb.
      assert (Hnb : 32 <= nb <= n + 23) by (subst nb; Z.div_mod_to_equations; lia).
      clear Enb. join Hmp.
      destruct (Z.ltb_spec nb 1041) as [Hlt|Hge]; simp.
      * assert (Hi : 0 <= (nb - 32) / 16 < 64) by (Z.div_mod_to_equations; lia).
        l26 ((nb - 32) / 16) Htc dq dummy_reg. l7 n Hn Hk Hm2.
      * l7 n Hn Hk Hm2.
Qed.

End rules.
End AllocOn.
