(** These calling rules use the retained libc string and output contracts.
    They extend the shared string ownership assertions without changing them. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcCalls.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Delegated roots

    Some stateful libc calls, such as `c: stdio` operations, update the
    world's writable spans to include buffers they allocated or touched
    during the call. *)

(** When a call derives new writable world spans from its existing spans
    and newly allocated objects, every address in the new spans is one the
    call already had authority to write, so the new spans remain disjoint
    from the caller's live objects. *)
Lemma delegates_apart : forall roots born m w h,
  stdio_delegates roots born m w -> roots_apart roots h m -> ids_apart born h -> live_disjoint m ->
  roots_apart (stdio_roots w) h m.
Proof.
  intros roots born m w h Hdel Hra Hb Hd s a Hin Hs Ho.
  destruct (Hdel s Hin) as [_ Hw].
  exact (owned_not_authority roots born h m a Hd Hra Hb Ho (Hw a Hs)).
Qed.

(** ## The stdio world

    A puts call may write stream buffers, but it must not overwrite
    the input string or other storage owned by the caller. The following
    world condition separates those writable buffers from the caller's
    objects and requires the stream state to remain ready. *)

(** Stream state must match its representation in memory, be ready for
    output, and keep its writable storage apart from the program's objects.
    The predicate [stdio_wi] combines these requirements using the
    [[ghost-state|ghost heap]] to identify which objects the program owns. *)
Definition stdio_wi (rep : mem -> stdio_world -> Prop) (m : mem) (w : stdio_world)
    (h : gmap piece pval) : Prop :=
  rep m w /\ stdio_ready m w /\ roots_apart (stdio_roots w) h m.

Module LibcStringLogicOn (R : Runtime) (LG0 : LogicSig R).
Include StringLogicOn R LG0.
Module CE := LibcCallsOn R LG0.L.M.
Import L LG.

(** Garbage collection preserves the separation between stream storage
    and program objects because a [[poll|safepoint]] never changes object regions.
    Preserving stream representation and readiness therefore suffices to
    preserve the whole condition, as [stdio_wi_safepoint] proves. *)
Lemma stdio_wi_safepoint (rep : mem -> stdio_world -> Prop) :
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
     rep m' w /\ stdio_ready m' w) ->
  SafepointStable (stdio_wi rep).
Proof.
  intros Hst. split. intros s m s' m' w h Hsp (Hr & Hw & Ha).
  destruct (Hst _ _ _ _ _ Hsp Hr Hw) as [Hr' Hw'].
  split; [exact Hr'|]. split; [exact Hw'|].
  intros sp a Hin Hs (l & v & reg & Hl & Hm & [E Hlive] & Hb). apply (Ha sp a Hin Hs).
  rewrite (R.collector_live _ _ _ _ Hsp) in E. exists l, v, reg. split; [exact Hl|]. split; [exact Hm|].
  split; [|exact Hb].
  split; [exact E | exact Hlive].
Qed.

(** Whenever puts returns normally, its contract supplies exactly one
    integer result, as [puts_returns_int] establishes for the calling rule. *)
Lemma puts_returns_int rep requests r args xs s m w trace values s' m' w' :
  M.E.invoke (puts_contract rep requests) r args xs s m w trace (CallReturn values) s' m' w' ->
  exists n, values = [WInt n].
Proof.
  intros Hi. remember (CallReturn values) as en eqn:Een.
  destruct Hi as [? ? ? ? ? ? _ _ _ Hp | ? ? ? ? ? ? _ _ _ _ _]; [|discriminate Een].
  destruct Hp as (p & bytes & acc & tail & n & _ & _ & _ & _ & _ & Hend & _).
  subst. injection Hend as ->. eauto.
Qed.

(** After puts returns, the caller still owns the same objects and
    bytes, while the stream representation describes the new output state.
    The lemma [puts_return_frame] proves this by restricting stream writes
    to its previous storage and any objects allocated during the call.
    Those locations remain separate from the caller's objects, and the
    runtime remains ready for subsequent execution. *)
Lemma puts_return_frame rep requests r args xs s m w trace values s' m' w' h :
  M.E.invoke (puts_contract rep requests) r args xs s m w trace (CallReturn values) s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> stdio_wi rep m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ stdio_wi rep m' w' h.
Proof.
  intros Hi Ha Hd Hr (Hrep & Hw & Hapart).
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  destruct (prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hp Hr Hd Ha Hapart ltac:(intros ? ? ? []))
    as (Ha' & Hd' & Hb & Hapart').
  destruct Hp as [_ (Hrep' & Hw' & Hdel & _)].
  change (roots_apart (stdio_roots w) h m') in Hapart'.
  split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|]. split; [exact Hrep'|]. split; [exact Hw'|].
  exact (delegates_apart _ _ _ _ h Hdel Hapart' Hb Hd').
Qed.

Section strings.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** ## The calls

    Read-only libc string calls leave the caller's owned bytes and
    the external world unchanged when they return.
    Their rules below turn string ownership into contract preconditions
    and return that ownership alongside the call's result. *)

Section calls.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The instance [string_irisGS] equips these calling rules with the
    chosen contract registry and the interpretation of external state. *)
Local Instance string_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The notation [sexpr] names expressions in this language, keeping
    the contract registry implicit in the calling rules below. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A read-only call leaves the memory and external world unchanged,
    although the runtime's private bookkeeping may change during execution.
    The lemma [pure_return] reestablishes the memory interpretation with
    the same owned pieces because the contract preserves runtime readiness. *)
Lemma pure_return {spec : contract world} r args xs (σ : lstate world) trace ending s' :
  CE.invoke spec r args xs (ls_rt σ) (ls_mem σ) (ls_world σ) trace ending s' (ls_mem σ) (ls_world σ) ->
  heap_interp wi σ -∗ heap_interp wi (mkLstate (ls_mem σ) s' (ls_fuel σ) (ls_world σ)).
Proof.
  intros Hi. iIntros "(%h & Hh & %Hf)". destruct Hf as (Ha & Hd & Hr & Hw).
  destruct (CE.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (CE.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  iExists h. iFrame "Hh". iPureIntro. cbn. auto.
Qed.

(** Calling strlen returns the owned string's length without consuming
    its ownership, as [wp_strlen] derives from the registered [strlen_contract]. *)
Lemma wp_strlen f e ls lab d v rest j p b reg bytes Φ :
  registry (TAtom "strlen") = Some (strlen_contract world) ->
  find_fn ge (TAtom "strlen") = None -> lookup (TAtom "strlen") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) ->
  string p b reg bytes -∗
  ▷ (string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WInt (Z.of_nat (length bytes))) e) ls None (Exec lab rest j)) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "strlen")) [Arg P v] :: rest) j)) : sexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strlen_contract world) [WPtr p] (string p b reg bytes)
            with "Hs [HK]"); [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[Ht _]. iPureIntro.
    exists p, (Z.of_nat (length bytes)). auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ Hs".
    iDestruct (string_facts with "Hσ Hs") as %[Ht _].
    destruct (CE.strlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & k & Hx & Hk & He). injection Hx as <-. injection He as ->.
    rewrite (terminated_length_unique _ _ _ _ Hk Ht).
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w]. iModIntro.
    iExists _. iSplit.
    + iPureIntro. cbn. rewrite Z.mod_small; [reflexivity|]. destruct Ht as [_ ?]. lia.
    + iFrame "Hσ". iApply ("HK" with "Hs").
Qed.

(** Searching for a nonzero character returns its first matching byte
    with the string's capability, or null if no byte matches.
    The predicate [strchr_found] describes this result after reducing
    the character argument to its low byte. *)
Definition strchr_found (p : ptr) (bytes : list Z) (c : Z) (q : ptr) : Prop :=
  (exists i x, bytes !! i = Some x /\ x = c mod 256 /\
     (forall i' x', (i' < i)%nat -> bytes !! i' = Some x' -> x' <> c mod 256) /\
     q = mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) \/
  ((forall i' x', bytes !! i' = Some x' -> x' <> c mod 256) /\ q = mkPtr 0 CNone).

(** Calling strchr preserves string ownership and returns the first
    matching position or null, as [wp_strchr] proves for a nonzero search byte. *)
Lemma wp_strchr f e ls lab d v w rest j p b reg bytes c Φ :
  registry (TAtom "strchr") = Some (strchr_contract world) ->
  find_fn ge (TAtom "strchr") = None -> lookup (TAtom "strchr") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg W w) = Some (WInt c) ->
  0 <= c < 2 ^ 32 -> c mod 256 <> 0 ->
  string p b reg bytes -∗
  ▷ (∀ q, ⌜strchr_found p bytes c q⌝ -∗ string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "strchr")) [Arg P v; Arg W w] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hw Hc Hnz. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strchr_contract world) [WPtr p; WInt c]
            (string p b reg bytes) with "Hs [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv Hw; done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[Ht _]. iPureIntro.
    exists p, c, (Z.of_nat (length bytes)). auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ Hs".
    iDestruct "Hs" as "[%Hok Hs]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _).
    pose proof (string_terminated _ _ _ _ _ Hok Ha) as Ht.
    pose proof (string_bytes _ _ _ _ _ Hok Ha) as Hb.
    destruct (CE.strchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & c' & q & Hx & _ & (k & Hk & Hq) & He). injection Hx as <- <-.
    injection He as ->. rewrite (terminated_length_unique _ _ _ _ Hk Ht) in Hq.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ".
    iApply ("HK" with "[%] [Hs]"); [|by iSplit].
    cbn [ls_mem] in Hb. destruct Hq as [(i & Hi & Hv' & Hbefore & ->) | (Hnone & ->)].
    + assert (Hil : (Z.to_nat i < length bytes)%nat).
      { destruct (decide (Z.to_nat i = length bytes)) as [Heq|Hne]; [|lia]. exfalso. apply Hnz.
        rewrite <- Hv'. rewrite <- (Z2Nat.id i) by lia. rewrite Heq. apply (Hb (length bytes) 0).
        rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity. }
      destruct (lookup_lt_is_Some_2 bytes (Z.to_nat i) Hil) as [x Hx]. left.
      exists (Z.to_nat i), x. split; [exact Hx|]. split.
      * rewrite <- Hv'. rewrite <- (Z2Nat.id i) at 1 by lia. symmetry. apply Hb.
        by apply lookup_app_l_Some.
      * split; [|rewrite Z2Nat.id; [reflexivity | lia]].
        intros i' x' Hlt Hx'. specialize (Hbefore (Z.of_nat i') ltac:(lia)).
        rewrite (Hb i' x') in Hbefore; [exact Hbefore|]. by apply lookup_app_l_Some.
    + right. split; [|reflexivity]. intros i' x' Hx'.
      assert (Hl : (i' < length bytes)%nat) by (apply lookup_lt_Some in Hx'; exact Hx').
      specialize (Hnone (Z.of_nat i') ltac:(lia)).
      rewrite (Hb i' x') in Hnone; [exact Hnone|]. by apply lookup_app_l_Some.
Qed.

(** Calling strcmp preserves both owned strings and returns an integer,
    but [wp_strcmp] deliberately gives no information about its sign or value.
    A caller can use this rule when its safety proof handles every
    result without relying on the strings' relative ordering. *)
Lemma wp_strcmp f e ls lab d v w rest j p b reg xs q b' reg' ys Φ :
  registry (TAtom "strcmp") = Some (strcmp_contract world) ->
  find_fn ge (TAtom "strcmp") = None -> lookup (TAtom "strcmp") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg P w) = Some (WPtr q) ->
  string p b reg xs -∗ string q b' reg' ys -∗
  ▷ (∀ bits, string p b reg xs -∗ string q b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WInt bits) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "strcmp")) [Arg P v; Arg P w] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hw. iIntros "Hs Ht HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strcmp_contract world) [WPtr p; WPtr q]
            (string p b reg xs ∗ string q b' reg' ys) with "[$Hs $Ht] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv Hw; done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ [Hs Ht]". iDestruct (string_facts with "Hσ Hs") as %[Hp _].
    iDestruct (string_facts with "Hσ Ht") as %[Hq _]. iPureIntro.
    exists p, q, (Z.of_nat (length xs)), (Z.of_nat (length ys)). auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ [Hs Ht]".
    destruct (CE.strcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & q' & bits & Hx & _ & He). injection He as ->.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ". iApply ("HK" with "Hs Ht").
Qed.

(** Calling strncmp compares no more than n bytes and preserves both
    strings, while [wp_strncmp] leaves the returned integer unspecified.
    The rule therefore supports safety proofs that do not need the
    comparison's sign or a relation between the string contents. *)
Lemma wp_strncmp f e ls lab d v w u rest j p b reg xs q b' reg' ys n Φ :
  registry (TAtom "strncmp") = Some (strncmp_contract world) ->
  find_fn ge (TAtom "strncmp") = None -> lookup (TAtom "strncmp") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg P w) = Some (WPtr q) ->
  arg_x ge e (Arg L u) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  string p b reg xs -∗ string q b' reg' ys -∗
  ▷ (∀ bits, string p b reg xs -∗ string q b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WInt bits) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "strncmp")) [Arg P v; Arg P w; Arg L u] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hw Hu Hn. iIntros "Hs Ht HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strncmp_contract world) [WPtr p; WPtr q; WInt n]
            (string p b reg xs ∗ string q b' reg' ys) with "[$Hs $Ht] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv Hw Hu; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ [[%Hok Hs] [%Hok' Ht]]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _). iDestruct (pts_facts with "Hσ Ht") as %(Ha' & _).
    iPureIntro. do 5 eexists. split; [reflexivity|].
    split; [exact (string_bounded _ _ _ _ _ _ Hok Ha Hn) | exact (string_bounded _ _ _ _ _ _ Hok' Ha' Hn)].
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ [Hs Ht]".
    destruct (CE.strncmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & q' & n' & bits & Hx & _ & He). injection He as ->.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ". iApply ("HK" with "Hs Ht").
Qed.

(** Searching backward for a nonzero character returns null or a
    pointer before the string's terminator, retaining the original capability.
    The rule [wp_strrchr] preserves string ownership but does not expose
    which byte matched or whether it was the last match. *)
Lemma wp_strrchr f e ls lab d v w rest j p b reg bytes c Φ :
  registry (TAtom "strrchr") = Some (strrchr_contract world) ->
  find_fn ge (TAtom "strrchr") = None -> lookup (TAtom "strrchr") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg W w) = Some (WInt c) ->
  0 <= c < 2 ^ 32 -> c mod 256 <> 0 ->
  string p b reg bytes -∗
  ▷ (∀ q, ⌜q = mkPtr 0 CNone \/
           exists i, (i < length bytes)%nat /\ q = mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)⌝ -∗
     string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "strrchr")) [Arg P v; Arg W w] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hw Hc Hnz. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strrchr_contract world) [WPtr p; WInt c]
            (string p b reg bytes) with "Hs [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv Hw; done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[Ht _]. iPureIntro.
    exists p, c, (Z.of_nat (length bytes)). auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ Hs".
    iDestruct "Hs" as "[%Hok Hs]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _).
    pose proof (string_terminated _ _ _ _ _ Hok Ha) as Ht.
    pose proof (string_bytes _ _ _ _ _ Hok Ha) as Hb.
    destruct (CE.strrchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & c' & q & Hx & _ & (k & Hk & Hq) & He). injection Hx as <- <-.
    injection He as ->. rewrite (terminated_length_unique _ _ _ _ Hk Ht) in Hq.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ".
    iApply ("HK" with "[%] [Hs]"); [|by iSplit].
    cbn [ls_mem] in Hb. destruct Hq as [(i & Hi & Hv' & _ & ->) | (_ & ->)]; [right | left; reflexivity].
    exists (Z.to_nat i). split; [|rewrite Z2Nat.id; [reflexivity | lia]].
    destruct (decide (Z.to_nat i = length bytes)) as [Heq|Hne]; [|lia]. exfalso. apply Hnz.
    rewrite <- Hv'. rewrite <- (Z2Nat.id i) by lia. rewrite Heq. apply (Hb (length bytes) 0).
    rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

End calls.

(** ## puts

    Output changes stream state even though it only reads the caller's
    input string, so its rule uses the separated stdio world.
    The following rule returns string ownership and an integer result
    after accounting for any stream writes and allocations. *)

Section puts.
Context (rep : mem -> stdio_world -> Prop) (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop)
  (registry : name -> option (contract stdio_world)) `{!SafepointStable (stdio_wi rep)} (ge : genv).

(** The instance [puts_irisGS] uses the stdio world condition to keep
    stream writes separate from memory owned by the caller. *)
Local Instance puts_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (stdio_wi rep) ge.

(** The notation [pexpr] names expressions whose external state follows
    the stdio world condition, keeping that choice implicit below. *)
Local Notation pexpr := (language.expr (nanofil_lang registry ge)).

(** Calling puts preserves the input string because all stream writes
    remain separate from its storage under [stdio_wi].
    The rule [wp_puts] returns that ownership and the contract's integer
    result, wrapped to the 32-bit representation of a C int. *)
Lemma wp_puts f e ls lab d v rest j p b reg bytes Φ :
  registry (TAtom "puts") = Some (puts_contract rep requests) ->
  find_fn ge (TAtom "puts") = None -> lookup (TAtom "puts") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) ->
  string p b reg bytes -∗
  ▷ (∀ n, string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WInt (n mod 2 ^ 32)) e) ls None (Exec lab rest j)) : pexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "puts")) [Arg P v] :: rest) j)) : pexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (puts_contract rep requests) [WPtr p]
            (string p b reg bytes) with "Hs [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[_ Hc].
    iDestruct "Hσ" as (h) "[_ %Hf]". destruct Hf as (_ & _ & _ & Hrep & Hw & _).
    iPureIntro. split; [exact Hrep|]. split; [exact Hw|]. exists p, bytes. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hs".
    destruct Hf as (Ha & Hd & Hr & Hwi).
    destruct (puts_return_frame _ _ _ _ _ _ _ _ _ _ _ _ _ h Hinv Ha Hd Hr Hwi)
      as (Ha' & Hd' & Hr' & Hwi').
    destruct (puts_returns_int _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (n & ->).
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh"; [iExists h; iFrame "Hh"; iPureIntro; auto|].
    iApply ("HK" with "Hs").
Qed.

End puts.
End strings.
End LibcStringLogicOn.

Module LibcStringLogic (R : Runtime).
Module LG0 := Logic R.
Include LibcStringLogicOn R LG0.
End LibcStringLogic.
