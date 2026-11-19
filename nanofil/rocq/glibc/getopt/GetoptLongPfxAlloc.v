(** When glibc's long-option parser meets an ambiguous word and its
    caller lets it print errors, it allocates a set with one byte per
    table entry. A small set lives in the parser's frame, and a large
    one comes from malloc. The parser clears the set with memset and
    marks the first matching entry. This file states the rules that a
    caller supplies for the three callees that the parser does not
    prove here, and it proves the allocation safe. A failed malloc
    leaves the set null, and the parser then only remembers that the
    word is ambiguous. *)

From Glibc Require Import GetoptTactics Unit_nptl_alloca_cutoff_os GlibcProgram GlibcTactics OsTactics
  GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld WordString StrchrnulLogic StrlenLogic StrlenLoop StrlenWord
  StrcmpLoop StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule
   GetoptReqTail GetoptLongScan
  GetoptLongPfxCmp GetoptLongPfxMark.
From Glibc Require CutoffLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The allocation assigns these names. *)
Definition palloc_names : list name := Eval vm_compute in
  List.map TAtom ["v186"; "iw_1.v3"; "iw_1.v4"; "iw_1.v5"; "iw_1.v11"; "iw_1.v15"; "v190"; "v196"; "v197"; "v199";
    "pr.37"; "pr.28"; "pr.20"; "v204"; "v205"; "v209"; "v212"; "v213"; "chk17"; "pr.35"; "pr.26"; "pr.18"]%string.

(** The marking keeps these names for the caller. *)
Definition palloc_keys : list name := Eval vm_compute in List.map TAtom ["pr.35"; "pr.26"; "pr.18"]%string.

(** The parser tests the allocated set in this block. *)
Definition plo_blk184 : block := Eval vm_compute in plo_blk "L184".


(** The marking module supplies the set, the option table and the tactics. *)
Import GetoptLongPfxMark GetoptLongPfxCmp GetoptLongScan GetoptReqTail Fix.ML0 Fix.LG0 Fix.LG0.L.

Section fresh.
Context `{!gen_heapGS piece pval Σ}.

(** A fresh heap object of n bytes gives its lifetime and its first n
    bytes and capability slots, all of them zero or empty. *)
Lemma obj_set b n :
  0 <= n ->
  obj b (heap_req 16 n) ⊢ live b (mkRegion b (b + req_extent (heap_req 16 n)) Heap Live) ∗
    bytes b 0 (replicate (Z.to_nat n) 0) ∗ auxes b 0 (replicate (Z.to_nat n) CNone).
Proof using Type.
  intros Hn. assert (He : 0 <= req_extent (heap_req 16 n)) by (cbn; Z.div_mod_to_equations; lia).
  rewrite (obj_zero_block b _ He).
  assert (Hd : Z.to_nat (req_extent (heap_req 16 n)) = (Z.to_nat n + (Z.to_nat (req_extent (heap_req 16 n)) - Z.to_nat n))%nat)
    by (cbn; Z.div_mod_to_equations; lia).
  rewrite Hd !replicate_add bytes_app auxes_app. iIntros "(Hl & (Hx & _) & (Hc & _))". iFrame.
Qed.

End fresh.

Import ProgramAbbreviations.
From Glibc Require Export AllocCall.

Section alloc_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance alloc_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Definition getopt_cutoff_rule : Prop :=
  forall f e ls l d args rest j n Φ, map_option (arg_x ge e) args = Some [WInt n] ->
  ⊢ ▷ (∀ x, ⌜0 <= x < 2 ^ 32⌝ -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d W) (Global (TAtom "__GI___libc_alloca_cutoff")) args :: rest) j)) : gexpr) {{ Φ }}.
(** The function reads the thread's stack size, so a caller that can
    supply that memory states the rule with a resource C. The call
    borrows C and gives it back with some 32-bit integer. *)
Definition getopt_cutoff_rule_with (C : iProp Σ) : Prop :=
  forall f e ls l d args rest j n Φ, map_option (arg_x ge e) args = Some [WInt n] ->
  ⊢ C -∗ ▷ (C -∗ ∀ x, ⌜0 <= x < 2 ^ 32⌝ -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d W) (Global (TAtom "__GI___libc_alloca_cutoff")) args :: rest) j)) : gexpr) {{ Φ }}.
Definition getopt_memset_rule : Prop :=
  forall f e ls l d args rest j b reg xs cs nz Φ,
  map_option (arg_x ge e) args = Some [WPtr (mkPtr b (Obj b)); WInt 0; WInt nz] -> nz = Z.of_nat (List.length xs) ->
  nz < 2 ^ 64 -> b mod 8 = 0 -> b + nz <= r_end reg -> List.length cs = List.length xs ->
  ⊢ live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗
    ▷ (∀ cs', live b reg -∗ bytes b 0 (replicate (List.length xs) 0) -∗ auxes b 0 cs' -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr b (Obj b))) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None (Exec l (Call (CResult d P) (Global (TAtom "__GI_memset")) args :: rest) j)) : gexpr)
      {{ Φ }}.

(** The rule without resources serves any C, because C is just carried along. *)
Lemma getopt_cutoff_rule_with_any C : getopt_cutoff_rule -> getopt_cutoff_rule_with C.
Proof using Type.
  intros Hcut f e ls l d args rest j n Φ Hx. iIntros "HC HK".
  iApply Hcut; [exact Hx|]. iNext. iIntros (x Hx32). iApply ("HK" with "HC"). done.
Qed.

(** A cutoff rule for C also holds when the caller carries R beside C. *)
Lemma getopt_cutoff_rule_with_sep R C : getopt_cutoff_rule_with C -> getopt_cutoff_rule_with (R ∗ C).
Proof using Type.
  intros Hcut f e ls l d args rest j n Φ Hx. iIntros "[HR HC] HK".
  iApply (Hcut with "HC"); [exact Hx|]. iNext. iIntros "HC". iApply ("HK" with "[$HR $HC]").
Qed.

(** A malloc rule for M also holds when the caller carries R beside M. *)
Lemma getopt_malloc_rule_sep M R : getopt_malloc_rule w0 registry ge M -> getopt_malloc_rule w0 registry ge (M ∗ R).
Proof using Type.
  intros Hmal f e ls l d v rest j n Φ Hx Hn. iIntros "[HM HR] HK".
  iApply (Hmal with "HM"); [exact Hx | exact Hn|]. iNext. iIntros (p) "HM Hp". iApply ("HK" with "[$HM $HR] Hp").
Qed.
End alloc_values.
Section alloc.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance alloc_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser asks __libc_alloca_cutoff whether a set of a given size
    may live in its frame. The function reads the size of the thread's
    stack. The older rule [getopt_cutoff_rule] takes no resources and
    stays as a recorded dependency. The resource-aware rule
    [getopt_cutoff_rule_with] lends the memory that the function reads,
    and the lemma below proves it from glibc's code. *)

(** The cutoff's rule does not have to be assumed, since glibc's code
    for it is proved. That code reads how big the thread's stack is. So
    whoever can lend that number and the thread's state for one call
    gets the rule, and gets both back. *)
Lemma getopt_cutoff_rule_with_loan (G : iProp Σ) dq :
  registry (TAtom "zthread_self_cookie") = Some OsThread.os_self_contract ->
  find_fn ge (TAtom "zthread_self_cookie") = None ->
  Term.lookup (TAtom "zthread_self_cookie") (ge_globals ge) = None ->
  find_fn ge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff) ->
  (G ⊢ CutoffLogic.cutoff_loan dq ∗ (CutoffLogic.cutoff_loan dq -∗ G)) ->
  getopt_cutoff_rule_with w0 registry ge G.
Proof using Type.
  intros Hs Hsf Hss Hg Hl f e ls l d args rest j n Φ Hx. iIntros "HG HK".
  iDestruct (Hl with "HG") as "[HL Hback]".
  iApply (CutoffLogic.wp_call_alloca_cutoff_loan Hs Hsf Hss with "HL"); [exact Hg | exact Hx |].
  iNext. iIntros "HL" (x Hx32). iApply ("HK" with "[HL Hback]"); [iApply ("Hback" with "HL") | done].
Qed.

(** A caller supplies this rule for malloc. The allocator's own state
    M goes in and comes back. The call returns null, or a fresh heap
    object of the requested size at a positive address aligned to 16
    bytes below 2^48. The rule allows a failed allocation. *)

(** A caller supplies this rule for glibc's memset on the first nz bytes
    xs of a live object b at an eight-byte boundary. The bytes become
    zero, the capability slots stay owned, and the call returns b. *)

(** This tactic replaces the integer that the name holds by v. *)
Local Ltac palloc_int nm v := match goal with |- context [put (TAtom nm) (WInt ?X) _] =>
  replace X with v by (repeat first [rewrite sx_small; [|lia] | rewrite sx_nonneg; [|lia] | rewrite Z.mod_small; [|lia]]; lia) end.

(** This tactic decides a branch on the address of a pointer that is null or an object's base. *)
Local Ltac palloc_brp := iApply wp_branch; [vx | iNext]; close_br.

(** The parser has found the current entry k ambiguous with the first
    match j, it prints errors, and it has no set yet. It asks whether a
    set of n bytes may live in its frame, and it allocates the set there
    or with malloc. It clears the set and marks the entry j. Then it
    marks the entry k and goes on to the next entry. The set may be null
    after a failed malloc, and the parser then records the ambiguity in
    the flag a. When the set came from malloc, the flag m is 1. *)
Lemma wp_pfx_alloc_with ks e (M : iProp Σ) n j k Φ :
  avoids ks palloc_names = true -> avoids ks pmark_names = true ->
  (getopt_cutoff_rule_with w0 registry ge M) -> (getopt_malloc_rule w0 registry ge) M -> (getopt_memset_rule w0 registry ge) ->
  lookup (TAtom "pr.9") e = Some (WInt n) -> lookup (TAtom "pr.39") e = Some (WInt 0) ->
  lookup (TAtom "pr.30") e = Some (WInt 0) -> lookup (TAtom "pr.42") e = Some (WInt (Z.of_nat j)) ->
  lookup (TAtom "pr.13") e = Some (WInt (Z.of_nat k)) -> lookup (TAtom "v90") e = Some (WInt 0) ->
  Z.of_nat j < n -> Z.of_nat k < n -> n < 2 ^ 31 ->
  M -∗
  (∀ e' P a m s, ⌜keeps ks e e' /\ (P = TAtom "L214" \/ P = TAtom "L172") /\
      lookup (TAtom "pr.35") e' = Some (WInt a) /\ lookup (TAtom "pr.26") e' = Some (WInt m) /\
      lookup (TAtom "pr.18") e' = Some (WPtr s) /\ (a = 0 \/ a = 1) /\ (m = 0 \/ (m = 1 /\ s <> null))⌝ -∗
     amb_set n s -∗ M -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L108") (Some P))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L175") (Some (TAtom "L171")))) : gexpr)
    {{ Φ }}.
Proof using Type.
  intros Hks Hksm Hcut Hmal Hset H9 H39 H30 H42 H13 H90 Hj Hk Hn. iIntros "HM HK".
  assert (Hext : n <= req_extent (heap_req 16 n)) by (cbn; Z.div_mod_to_equations; lia).
  assert (Hksk : avoids (palloc_keys ++ ks) pmark_names = true) by (rewrite avoids_app_l Hksm; reflexivity).
  iAssert (∀ e2 p a m, ⌜keeps ks e e2 /\ lookup (TAtom "pr.20") e2 = Some (WPtr p) /\
      lookup (TAtom "pr.37") e2 = Some (WInt a) /\ lookup (TAtom "pr.28") e2 = Some (WInt m) /\
      lookup (TAtom "v186") e2 = Some (WInt n) /\ lookup (TAtom "pr.42") e2 = Some (WInt (Z.of_nat j)) /\
      lookup (TAtom "pr.13") e2 = Some (WInt (Z.of_nat k)) /\ (a = 0 \/ a = 1) /\ (m = 0 \/ (m = 1 /\ p <> null))⌝ -∗
    (⌜p = null⌝ ∨ ∃ base, ⌜p = mkPtr base (Obj base) /\ 0 < base /\ base mod 16 = 0 /\
        base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ ∗ obj base (heap_req 16 n)) -∗ M -∗
    WP (ERun (mkFrame glibc_process_long_option e2 [] None
      (Exec (TAtom "L184") (b_insts plo_blk184) (b_jump plo_blk184))) : gexpr) {{ Φ }})%I with "[HK]" as "H184".
  { iIntros (e2 p a m (Hk2 & H20 & H37 & H28 & H186 & H42' & H13' & Ha & Hm)) "Hp HM".
    assert (Ha32 : 0 <= a < 2 ^ 32) by (destruct Ha as [-> | ->]; lia).
    assert (Hm32 : 0 <= m < 2 ^ 32) by (destruct Hm as [-> | [-> _]]; lia).
    cbn [b_insts b_jump plo_blk184]. step. step.
    iDestruct "Hp" as "[-> | (%base & %Hb & Ho)]".
    - unfold null; cbn [ptr_addr]. change (0 mod 2 ^ 64) with 0. palloc_brp. step.
      rewrite (Z.mod_small a (2 ^ 32)) // (Z.mod_small m (2 ^ 32)) //. pcmp_fold "L172" plo_blk172.
      iApply (wp_pfx_mark (palloc_keys ++ ks)%list _ n null k with "[]"); [exact Hksk | lk_prove | lk_prove | lia | lia | by iLeft |].
      iIntros (e' P (Hk' & HP)) "Hs". apply keeps_app in Hk' as [Hkt Hk'].
      iApply ("HK" $! e' P a m null with "[%] Hs HM").
      split; [eapply keeps_trans; [exact Hk2|]; eapply keeps_trans; [|exact Hk']; xkeep|].
      split; [exact HP|]. repeat split; try viakeep Hkt; tauto.
    - destruct Hb as (-> & Hb0 & Hb16 & Hbe). cbn [ptr_addr].
      rewrite (Z.mod_small base (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
      rewrite (proj2 (Z.eqb_neq base 0)); [|lia]. palloc_brp. step.
      iDestruct (obj_set with "Ho") as "(Hl & Hx & Hcs)"; [lia|].
      iApply (Hset with "Hl Hx Hcs"); [vx | rewrite length_replicate Z2Nat.id; [|lia]; try rewrite Z.mod_small; lia
        | try rewrite Z.mod_small; lia | Z.div_mod_to_equations; lia
        | cbn [r_end]; try rewrite Z.mod_small; lia | rewrite !length_replicate; reflexivity |].
      iNext. iIntros (cs') "Hl Hx _". rewrite length_replicate. step. step. norm.
      rewrite (sx_nonneg (Z.of_nat j)); [|lia].
      match goal with |- context [put (TAtom "v213") (WPtr {| ptr_addr := ?X; ptr_cap := Obj base |})] =>
        replace X with (base + Z.of_nat j) by (rewrite !Z.mod_small; lia) end.
      iApply (wp_amb_mark with "Hl Hx"); [lk_prove | rewrite length_replicate; lia | lia
        | rewrite length_replicate Z2Nat.id; [|lia]; cbn [r_end]; lia | cbn [r_end]; lia |].
      iNext. iIntros "Hl Hx". step. step. rewrite (Z.mod_small a (2 ^ 32)) // (Z.mod_small m (2 ^ 32)) //. pcmp_fold "L172" plo_blk172.
      iApply (wp_pfx_mark (palloc_keys ++ ks)%list _ n (mkPtr base (Obj base)) k with "[Hl Hx]");
        [exact Hksk | lk_prove | lk_prove | lia | lia | | ].
      { iRight. iExists base, _, _. iFrame. iPureIntro. cbn [r_end r_kind]. rewrite length_insert length_replicate Z2Nat.id; [|lia].
        repeat split; try reflexivity; lia. }
      iIntros (e' P (Hk' & HP)) "Hs". apply keeps_app in Hk' as [Hkt Hk'].
      iApply ("HK" $! e' P a m (mkPtr base (Obj base)) with "[%] Hs HM").
      split; [eapply keeps_trans; [exact Hk2|]; eapply keeps_trans; [|exact Hk']; xkeep|].
      split; [exact HP|]. repeat split; try viakeep Hkt; tauto. }
  let T := lazymatch iTypeOf "H184" with Some (_, ?P) => P end in
  iAssert (T -∗ ∀ e2, ⌜keeps ks e e2 /\ lookup (TAtom "v186") e2 = Some (WInt n) /\
      lookup (TAtom "pr.39") e2 = Some (WInt 0) /\ lookup (TAtom "pr.30") e2 = Some (WInt 0) /\
      lookup (TAtom "pr.42") e2 = Some (WInt (Z.of_nat j)) /\ lookup (TAtom "pr.13") e2 = Some (WInt (Z.of_nat k))⌝ -∗ M -∗
    WP (ERun (mkFrame glibc_process_long_option e2 [] None (Enter (TAtom "L182") (Some (TAtom "iw_1.L7")))) : gexpr)
      {{ Φ }})%I as "H182".
  { iIntros "H184" (e2 (Hk2 & H186 & H39' & H30' & H42' & H13')) "HM". step.
    iApply wp_alloc_any; [vx | apply Z.mod_pos_bound; lia | intros mm wd h base Hf Hw; exact (os_wi_alloc w0 mm wd h _ base Hf Hw) |].
    rewrite (Z.mod_small n (2 ^ 64)); [|lia].
    iNext. iIntros (base Hb) "Ho". step. step. pcmp_fold "L184" plo_blk184.
    iApply ("H184" with "[%] [Ho] HM"); [split; [xkeep|]; repeat split; try lk_prove; tauto |].
    iRight. iExists base. iFrame. iPureIntro. destruct Hb as (Hb1 & Hb2 & Hb3).
    split; [reflexivity|]. split; [lia|]. split; [exact Hb2 | exact Hb3]. }
  step. step. palloc_int "v186" n.
  iApply (Hcut with "HM"); [vx |]. iNext. iIntros "HM" (x Hx). step. step. pcmp_br.
  - step. step. step. step. pcmp_br.
    + step. iApply (Hmal with "HM"); [vx | apply Z.mod_pos_bound; lia |]. rewrite (Z.mod_small n (2 ^ 64)); [|lia]. iNext. iIntros (p) "HM Hp". step. step.
      iDestruct "Hp" as "[-> | (%base & %Hb & Ho)]".
      * unfold null; cbn [ptr_addr]. change (0 mod 2 ^ 64) with 0. palloc_brp. step. pcmp_fold "L184" plo_blk184.
        iApply ("H184" with "[%] [] HM"); [split; [xkeep|]; repeat split; try lk_prove; tauto | by iLeft].
      * destruct Hb as (-> & Hb0 & Hb16 & Hbe). cbn [ptr_addr].
        rewrite (Z.mod_small base (2 ^ 64)); [|lia]. rewrite (proj2 (Z.eqb_neq base 0)); [|lia].
        palloc_brp. step. step. step. pcmp_fold "L184" plo_blk184.
        iApply ("H184" with "[%] [Ho] HM"); [split; [xkeep|]; repeat split; try lk_prove; try tauto |].
        { right. split; [reflexivity | discriminate]. }
        iRight. iExists base. iFrame. done.
    + iApply ("H182" with "H184 [%] HM"). split; [xkeep | repeat split; lk_prove].
  - step. iApply wp_branch; [vx | iNext]. close_br.
    iApply ("H182" with "H184 [%] HM"). split; [xkeep | repeat split; lk_prove].
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma wp_pfx_alloc ks e (M : iProp Σ) n j k Φ :
  avoids ks palloc_names = true -> avoids ks pmark_names = true ->
  (getopt_cutoff_rule w0 registry ge) -> (getopt_malloc_rule w0 registry ge) M -> (getopt_memset_rule w0 registry ge) ->
  lookup (TAtom "pr.9") e = Some (WInt n) -> lookup (TAtom "pr.39") e = Some (WInt 0) ->
  lookup (TAtom "pr.30") e = Some (WInt 0) -> lookup (TAtom "pr.42") e = Some (WInt (Z.of_nat j)) ->
  lookup (TAtom "pr.13") e = Some (WInt (Z.of_nat k)) -> lookup (TAtom "v90") e = Some (WInt 0) ->
  Z.of_nat j < n -> Z.of_nat k < n -> n < 2 ^ 31 ->
  M -∗
  (∀ e' P a m s, ⌜keeps ks e e' /\ (P = TAtom "L214" \/ P = TAtom "L172") /\
      lookup (TAtom "pr.35") e' = Some (WInt a) /\ lookup (TAtom "pr.26") e' = Some (WInt m) /\
      lookup (TAtom "pr.18") e' = Some (WPtr s) /\ (a = 0 \/ a = 1) /\ (m = 0 \/ (m = 1 /\ s <> null))⌝ -∗
     amb_set n s -∗ M -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L108") (Some P))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L175") (Some (TAtom "L171")))) : gexpr)
    {{ Φ }}.
Proof using Type.
  intros Hks Hksm Hcut.
  exact (wp_pfx_alloc_with ks e M n j k Φ Hks Hksm (getopt_cutoff_rule_with_any w0 registry ge M Hcut)).
Qed.

(** The same holds when the cutoff borrows a resource G of its own. The
    caller carries G beside the allocator's state M, and gets both back. *)
Lemma wp_pfx_alloc_sep ks e (M G : iProp Σ) n j k Φ :
  avoids ks palloc_names = true -> avoids ks pmark_names = true ->
  (getopt_cutoff_rule_with w0 registry ge G) -> (getopt_malloc_rule w0 registry ge) M -> (getopt_memset_rule w0 registry ge) ->
  lookup (TAtom "pr.9") e = Some (WInt n) -> lookup (TAtom "pr.39") e = Some (WInt 0) ->
  lookup (TAtom "pr.30") e = Some (WInt 0) -> lookup (TAtom "pr.42") e = Some (WInt (Z.of_nat j)) ->
  lookup (TAtom "pr.13") e = Some (WInt (Z.of_nat k)) -> lookup (TAtom "v90") e = Some (WInt 0) ->
  Z.of_nat j < n -> Z.of_nat k < n -> n < 2 ^ 31 ->
  M -∗ G -∗
  (∀ e' P a m s, ⌜keeps ks e e' /\ (P = TAtom "L214" \/ P = TAtom "L172") /\
      lookup (TAtom "pr.35") e' = Some (WInt a) /\ lookup (TAtom "pr.26") e' = Some (WInt m) /\
      lookup (TAtom "pr.18") e' = Some (WPtr s) /\ (a = 0 \/ a = 1) /\ (m = 0 \/ (m = 1 /\ s <> null))⌝ -∗
     amb_set n s -∗ M -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L108") (Some P))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L175") (Some (TAtom "L171")))) : gexpr)
    {{ Φ }}.
Proof using Type.
  intros Hks Hksm Hcut Hmal Hset H9 H39 H30 H42 H13 H90 Hj Hk Hn. iIntros "HM HG HK".
  iApply (wp_pfx_alloc_with ks e (M ∗ G) n j k with "[$HM $HG] [HK]");
    [exact Hks | exact Hksm | apply getopt_cutoff_rule_with_sep, Hcut | apply getopt_malloc_rule_sep, Hmal | exact Hset
    | exact H9 | exact H39 | exact H30 | exact H42 | exact H13 | exact H90 | exact Hj | exact Hk | exact Hn |].
  iIntros (e' P a m s Hp) "Hs [HM HG]". iApply ("HK" with "[//] Hs HM HG").
Qed.

End alloc.
