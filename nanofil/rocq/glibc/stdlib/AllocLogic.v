(** Triples for user glibc's `malloc` and `free` (docs/glibc-ir.md),
    over any registry, world and genv that binds their symbols, so a
    program linked with them uses each as a rule at its call.

    Fil-C's glibc keeps ptmalloc's tcache prelude in `malloc` but
    allocates with the runtime: `__libc_malloc2` is `zgc_alloc`, an
    [Alloc] 16 of the request, and `free` is `zgc_free`. The prelude
    rounds the request n to a chunk size nb (2^64 - 1 above 2^63), and
    below `mp_.tcache_max_bytes` (1041, `mp_` + 120) reads the tcache
    bin of index (nb - 32) / 16, always below 64 there, through the
    thread's `tcache`, which points to the read-only, zeroed
    `__tcache_dummy`: the bin, at 152 + 8 index, is null, so every
    request falls through to `__libc_malloc2`. [tcache_idle] owns
    shares of exactly what the prelude reads:

    - [wp_glibc_malloc]: for any n below 2^64, keeping [tcache_idle],
      the call returns a fresh object's own pointer, 16-aligned, owning
      its pieces ([obj] of [heap_req] 16 n), or stalls when the
      runtime refuses ([wp_alloc_any]);
    - [wp_glibc_free] and [wp_glibc_free_null]: `free` of a live heap
      object's own pointer gives up its life; of null, nothing
      ([wp_free_sym], [wp_free_null_sym] for `zgc_free`). *)

From Stdlib Require Import ZArith Lia.
From Glibc Require Import StrlenBits.
Open Scope Z_scope.

(** Rounding a 64-bit size down to a multiple of 16, as malloc's
    `request2size` does: an and with ~15. *)
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

(** glibc's `__GI___libc_malloc`. *)
Definition malloc_fn : func := Eval vm_compute in stdlib_fn "__GI___libc_malloc".
(** malloc.c's `__libc_malloc2`, renamed `malloc#__libc_malloc2` by link.pl. *)
Definition malloc2_fn : func := Eval vm_compute in stdlib_fn "malloc#__libc_malloc2".
(** glibc's `__GI___libc_free`. *)
Definition free_fn : func := Eval vm_compute in stdlib_fn "__GI___libc_free".

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
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
(** The Iris instance of the registry and wi. *)
Local Instance alloc_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

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

(** `malloc`'s requests of a heap object of n bytes, kept in the world
    interpretation: what [wp_alloc_any] asks of each. *)
Definition alloc_keeps (n : Z) : Prop :=
  forall m wd h base, fresh m (heap_req 16 n) base -> wi m wd h ->
    wi (allocated m (heap_req 16 n) base) wd (overwrite (obj_ps base (heap_req 16 n)) h).

(** `__libc_malloc2` of n: `zgc_alloc`, a fresh 16-aligned object of
    n bytes, or a stall. *)
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

(** `free` of the own pointer of the live heap object b: `zgc_free`,
    which the model runs, where the genv's free [frees_heap] and the
    free keeps the world interpretation: b's life is given up. *)
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

(** `free` of null: `zgc_free` of null, which does nothing. *)
Lemma wp_glibc_free_null Φ :
  frees_heap (ge_free ge) -> find_fn ge zgc_free_name = None -> lookup zgc_free_name (ge_globals ge) = None ->
  Φ RetVoid -∗
  WP (ERun (mkFrame free_fn [(TAtom "v0", WPtr null)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hf Hfn Hdata. iIntros "HΦ". st.
  iApply wp_free_null_sym; [reflexivity | exact Hf | exact Hfn | exact Hdata | reflexivity |].
  nx. iApply wp_ret_void. nx. iExact "HΦ".
Qed.

(** The tcache prelude's state while no chunk is cached, owned at the
    share dq: `mp_` (at mp_b, region mp_reg), whose
    `tcache_max_bytes` at 120 is 1041; the thread's `tcache` (at tc_b)
    pointing to the read-only `__tcache_dummy` (at dummy_b); and the
    dummy's 64 small bins from 152 on, all null. The objects lie below
    2^64 and the pointer cells are 8-aligned. *)
Definition tcache_idle (dq : dfrac) (mp_b tc_b dummy_b : Z) (mp_reg tc_reg dummy_reg : region) : iProp Σ :=
  ⌜0 <= mp_b /\ mp_b + 128 <= r_end mp_reg <= 2 ^ 64 /\ 0 <= tc_b /\ tc_b mod 8 = 0 /\
   tc_b + 8 <= r_end tc_reg <= 2 ^ 64 /\ 0 <= dummy_b /\ dummy_b mod 8 = 0 /\
   dummy_b + 664 <= r_end dummy_reg <= 2 ^ 64⌝ ∗
  liveq dq mp_b mp_reg ∗ icellq dq mp_b 120 1041 ∗
  liveq dq tc_b tc_reg ∗ pcellq dq tc_b 0 (mkPtr dummy_b (Ro dummy_b)) ∗
  liveq dq dummy_b dummy_reg ∗ [∗ list] i ∈ seqZ 0 64, pcellq dq dummy_b (152 + 8 * i) null.

(** `__libc_malloc2`'s frame for the request n. *)
Lemma malloc2_frame n :
  call_frame malloc2_fn [WInt n] =
  Some (mkFrame malloc2_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** The call of `__libc_malloc2` that ends the prelude, at the block
    L7, given the share of the tcache state back: its triple, then the
    return of its result. *)
Ltac l7 n Hn Hk Hm2 :=
  st;
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ [WInt n] malloc2_fn _);
    [transitivity (Some [WInt (n mod 2 ^ 64)]); [reflexivity | rewrite Z.mod_small; [reflexivity | lia]]
    | exact Hm2 | apply malloc2_frame |];
  nx; iApply (wp_libc_malloc2 with "[-]"); [exact Hn | exact Hk |];
  iIntros (base) "%Hb Hobj"; iExists _; iSplit; [iPureIntro; reflexivity|]; nx;
  iApply wp_ret; [reflexivity | reflexivity |]; nx;
  iApply ("HΦ" with "[%] Hobj [-]"); [assumption | rewrite /tcache_idle; iFrame; iPureIntro; lia].

(** The prelude's join, where the chunk size is known: the read of
    `mp_.tcache_max_bytes` and the comparison with it. *)
Ltac join Hmp :=
  st; st_global Hmp; st;
  rule1 "Hmpl" ltac:(eapply wp_check_read_dq; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]);
  rule2 "Hmpl" "Hmpc" ltac:(eapply wp_raw_load_read_dq; inst;
    [reflexivity | reflexivity | left; reflexivity | arith]); st; br.

(** The bin i's index is in the 64 small bins. *)
Lemma seqZ_bin i : 0 <= i < 64 -> seqZ 0 64 !! Z.to_nat i = Some i.
Proof. intros Hi. rewrite lookup_seqZ_lt; [f_equal; lia | lia]. Qed.

(** The small bin i's read, from the block L26: the index's bound
    check, `tcache`'s pointer to the dummy, and the bin's null pointer,
    the bins handed back. *)
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

(** `malloc` of any n below 2^64, where the genv binds `malloc#mp_`,
    `tcache` and `malloc#__libc_malloc2` to these objects and
    function, and the allocation keeps the world interpretation: with
    the tcache idle, it returns a fresh 16-aligned object's own
    pointer, owning the object, the tcache handed back. *)
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
