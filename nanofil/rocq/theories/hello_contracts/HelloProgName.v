(** `set_program_name` preserves strings, not just capabilities. This
    strengthens HelloName's control-flow proofs while reusing its IR
    definitions, literals, cells and store proof. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  HelloModule HelloLeaf HelloName.
Open Scope Z_scope.
Open Scope list_scope.

(** Keep symbolic address arithmetic folded during computation. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** Promotion candidate: a zero bounded comparison implies equal bounded
    lengths, since an earlier NUL would differ from a nonzero byte. *)
Lemma strncmp_zero_lengths m p q n left right :
  bounded_length m p n left -> bounded_length m q n right ->
  strncmp_result m p q n 0 -> left = right.
Proof.
  intros Hl Hr (l & r & Hpl & Hqr & _ & ordering & Horder & Hsign).
  pose proof (bounded_length_unique _ _ _ _ _ Hl Hpl) as <-.
  pose proof (bounded_length_unique _ _ _ _ _ Hr Hqr) as <-.
  change (Datatypes.Eq = ordering) in Hsign. subst ordering.
  assert (Hsame : forall i, 0 <= i < strncmp_window n left right ->
    m_bytes m (ptr_addr p + i) = m_bytes m (ptr_addr q + i)).
  { destruct Horder as [(_ & Hsame) | (k & Hk & Hb & Hne & Heq)]; [exact Hsame|].
    exfalso. apply Hne. apply Z.compare_eq. symmetry. exact Heq. }
  destruct Hl as (Hn & Hl & Hlp & Hap & Hbp & Hnp).
  destruct Hr as (_ & Hr & Hlq & Haq & Hbq & Hnq).
  destruct (Z.lt_trichotomy left right) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
  - specialize (Hsame left ltac:(unfold strncmp_window; lia)).
    rewrite (Hnp ltac:(lia)) in Hsame. specialize (Hbq left ltac:(lia)). lia.
  - specialize (Hsame right ltac:(unfold strncmp_window; lia)).
    rewrite (Hnq ltac:(lia)) in Hsame. specialize (Hbp right ltac:(lia)). lia.
Qed.

(** String-valued program-name reasoning over any [[runtime]]. *)
Module HelloProgNameOn (R : Runtime) (LG0 : LogicSig R).
Module CE := LibcCallsOn R LG0.L.M.
Module HN := HelloNameOn R LG0.
(** Import the existing module paths rather than copying their nested
    signatures into another chain of aliases. *)
Import HN.L HN.LG HN.SL HN.ML HN.HL HN.

Section name.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The linked module and the three external contracts already used by HelloName. *)
Context (Hlinked : hello_linked ge)
  (Hstrrchr : registry (TAtom "strrchr") = Some (strrchr_contract world))
  (Hmemcmp : registry (TAtom "memcmp") = Some (memcmp_contract world))
  (Hstrncmp : registry (TAtom "strncmp") = Some (strncmp_contract world)).

(** Exactly HelloName's global-cell layout and world-preserving store premises. *)
Context (pn nreg sreg : region) (nb sb : Z)
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hpn_end : program_name_b + 8 <= r_end pn)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48)
  (Kpn : store_keeps wi program_name_b pn) (Knb : store_keeps wi nb nreg)
  (Ksb : store_keeps wi sb sreg).

(** The same Iris interpretation as HelloName. *)
Local Instance progname_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** Expressions in the linked language. *)
Local Notation nexpr := (language.expr (nanofil_lang registry ge)).

(** Promotion candidate: expose the length consequence of strncmp's result
    instead of discarding all information about the returned integer. *)
Lemma wp_strncmp_lengths f e ls lab d v w u rest j p b reg xs q b' reg' ys n Φ :
  registry (TAtom "strncmp") = Some (strncmp_contract world) ->
  find_fn ge (TAtom "strncmp") = None -> lookup (TAtom "strncmp") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg P w) = Some (WPtr q) ->
  arg_x ge e (Arg L u) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  string p b reg xs -∗ string q b' reg' ys -∗
  ▷ (∀ bits, ⌜bits mod 2 ^ 32 = 0 -> Z.min (Z.of_nat (length xs)) n = Z.min (Z.of_nat (length ys)) n⌝ -∗
     string p b reg xs -∗ string q b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WInt bits) e) ls None (Exec lab rest j)) : nexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "strncmp")) [Arg P v; Arg P w; Arg L u] :: rest) j))
        : nexpr) {{ Φ }}.
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
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ [[%Hok Hs] [%Hok' Ht]]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _). iDestruct (pts_facts with "Hσ Ht") as %(Ha' & _).
    destruct (CE.strncmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & q' & n' & bits & Hx & Hresult & He).
    injection Hx as <- <- <-. injection He as ->.
    assert (Hlength : bits = 0 -> Z.min (Z.of_nat (length xs)) n = Z.min (Z.of_nat (length ys)) n).
    { intros ->. eapply strncmp_zero_lengths; [| |exact Hresult]; eapply string_bounded; eauto. }
    destruct Hresult as (left & right & _ & _ & Hbits & _).
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ".
    rewrite (Z.mod_small bits (2 ^ 32) Hbits).
    iApply ("HK" with "[%] [Hs] [Ht]").
    + rewrite (Z.mod_small bits (2 ^ 32) Hbits). exact Hlength.
    + by iSplit.
    + by iSplit.
Qed.

(** The cells and the existing store proof specialized to this layout. *)
Local Notation cells := (name_cells pn nreg sreg nb sb).
Local Notation store_names := (spn_L18 registry wi ge Hlinked pn nreg sreg nb sb
  Hnb Hsb Hpn_end Hnb_cell Hsb_cell Kpn Knb Ksb).

(** The lt-prefix test only advances by three when those bytes exist.
    Both the full invocation name and the short name remain suffixes. *)
Lemma spn_L16_suffix e p b reg ys j r3 r4 x0 x1 y0 Φ :
  lookup (TAtom "v15") e = Some (WPtr (mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p))) ->
  (j <= length ys)%nat ->
  string p b reg ys -∗ literals r3 r4 -∗ cells x0 x1 y0 -∗
  ▷ (∀ i k, ⌜(i <= length ys)%nat /\ (k <= length ys)%nat⌝ -∗
     string p b reg ys -∗ literals r3 r4 -∗
     cells (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p))
       (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p))
       (mkPtr (ptr_addr p + Z.of_nat k) (ptr_cap p)) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame set_program_name_fn e [] None (Exec (TAtom "L16") (b_insts s_L16) (b_jump s_L16)))
        : nexpr) {{ Φ }}.
Proof.
  intros Hv15 Hj. destruct (name_lookups ge Hlinked) as (_ & _ & Hlt).
  iIntros "Hs [Hlibs Hlt] Hc HΦ". iDestruct "Hs" as "[%Hok Hps]".
  iAssert (string p b reg ys) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hcap & Hb0 & Hb1 & Hb2 & Hb3 & _). cbn [b_insts b_jump s_L16].
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iDestruct (string_suffix _ _ _ _ j with "Hs") as "[Hsuf Hback]"; [exact Hj|].
  iApply (wp_strncmp_lengths with "Hsuf Hlt");
    [exact Hstrncmp | apply linked_outside; [exact Hlinked | reflexivity] |
     apply linked_unbound; [exact Hlinked | reflexivity] | word_premise | word_premise | word_premise |
     vm_compute; intuition congruence |].
  iNext. iIntros (bits Hlength) "Hsuf Hlt". iDestruct ("Hback" with "Hsuf") as "Hs". gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_branch; [word_premise|]. iNext.
  destruct (Z.eqb (bits mod 2 ^ 32) 0) eqn:E; cbn [edge_label].
  - apply Z.eqb_eq in E. specialize (Hlength E).
    rewrite length_drop in Hlength.
    change (Z.min (Z.of_nat (length ys - j)) 3 = 3) in Hlength.
    assert (Hj3 : (j + 3 <= length ys)%nat) by lia.
    iApply wp_enter; [exact find_s_L35 | reflexivity |]. iNext. cbn [b_insts b_jump s_L35].
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat j + 3));
      [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
    iNext. gen_env. iApply wp_goto. iNext.
    iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
    iApply (store_names with "Hc"); [reflexivity | reflexivity |]. iNext. iIntros "Hc".
    replace (ptr_addr p + Z.of_nat j + 3) with (ptr_addr p + Z.of_nat (j + 3)) by lia.
    iApply ("HΦ" $! (j + 3)%nat (j + 3)%nat with "[%] Hs [$Hlibs $Hlt] Hc"). auto.
  - iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
    iApply (store_names with "Hc"); [reflexivity | reflexivity |]. iNext. iIntros "Hc".
    iApply ("HΦ" $! j j with "[%] Hs [$Hlibs $Hlt] Hc"). auto.
Qed.

(** The directory-prefix comparison keeps the base-name offset; only
    L16 can advance it, using the comparison's length consequence. *)
Lemma spn_L8_suffix e p b reg ys j r3 r4 x0 x1 y0 Φ :
  lookup (TAtom "v15") e = Some (WPtr (mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p))) ->
  lookup (TAtom "v0") e = Some (WPtr p) -> (j <= length ys)%nat ->
  string p b reg ys -∗ literals r3 r4 -∗ cells x0 x1 y0 -∗
  ▷ (∀ i k, ⌜(i <= length ys)%nat /\ (k <= length ys)%nat⌝ -∗
     string p b reg ys -∗ literals r3 r4 -∗
     cells (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p))
       (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p))
       (mkPtr (ptr_addr p + Z.of_nat k) (ptr_cap p)) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame set_program_name_fn e [] None (Exec (TAtom "L8") (b_insts s_L8) (b_jump s_L8)))
        : nexpr) {{ Φ }}.
Proof.
  intros Hv15 Hv0 Hj. destruct (name_lookups ge Hlinked) as (_ & Hlibs & _).
  iIntros "Hs [Hl3 Hl4] Hc HΦ". iDestruct "Hs" as "[%Hok Hps]".
  iAssert (string p b reg ys) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hcap & Hb0 & Hb1 & Hb2 & Hb3 & Hys). cbn [b_insts b_jump s_L8].
  assert (Hjz : Z.of_nat j <= Z.of_nat (length ys)) by lia.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  destruct (Nat.lt_ge_cases j 7) as [Hj7 | Hj7].
  - assert (Hz7 : Z.of_nat j < 7) by lia.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L26 | reflexivity |]. iNext. cbn [b_insts b_jump s_L26]. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
    iApply (store_names with "Hc"); [word_premise | word_premise |]. iNext. iIntros "Hc".
    iApply ("HΦ" $! 0%nat j with "[%] Hs [$Hl3 $Hl4] [Hc]"); [lia|].
    cbn [Z.of_nat]. rewrite Z.add_0_r. destruct p. iExact "Hc".
  - assert (Hz7 : 7 <= Z.of_nat j) by lia.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L25 | reflexivity |]. iNext. cbn [b_insts b_jump s_L25].
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + (ptr_addr p - b + Z.of_nat (j - 7))));
      [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
    iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iDestruct (string_window _ _ _ _ (j - 7) 7 with "Hs") as "(_ & Hl & Hw & Hback)"; [lia|].
    iDestruct (string_window _ _ _ _ 0 7 with "Hl3") as "(%Hok3 & Hl3 & Hw3 & Hback3)"; [cbn; lia|].
    pose proof Hok3 as (_ & _ & _ & H3end & _).
    iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ memeq_fn
              (invocation memeq_fn [WPtr (mkPtr (b + (ptr_addr p - b + Z.of_nat (j - 7))) (ptr_cap p));
                                    WPtr libs_ptr; WInt 7]));
      [word_premise | apply find_memeq; exact (proj1 Hlinked) | reflexivity |].
    iNext.
    iApply (memeq_spec registry wi ge Hlinked b reg (ptr_addr p - b + Z.of_nat (j - 7)) _ (ptr_cap p)
              66112 r3 (ptr_addr libs_ptr - 66112 + Z.of_nat 0) _ (Ro 66112) with "Hl Hw Hl3 Hw3");
      [exact Hmemcmp | rewrite length_take length_drop; lia | exact Hcap | right; reflexivity |
       rewrite !length_take !length_drop; cbn [length libs_bytes]; lia | lia | cbn; lia |
       rewrite length_take length_drop; lia |
       rewrite length_take length_drop; cbn [ptr_addr libs_ptr length libs_bytes] in H3end |- *; lia |
       rewrite length_take length_drop; lia |
       apply Forall_take, Forall_drop; eapply Forall_impl; [exact Hys | intros x Hx; cbn in Hx; lia] |
       vm_compute; repeat constructor; discriminate |].
    iNext. iIntros (k) "Hl Hw Hl3 Hw3". iDestruct ("Hback" with "Hl Hw") as "Hs".
    iDestruct ("Hback3" with "Hl3 Hw3") as "Hl3".
    iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_goto. iNext.
    iApply wp_enter; [exact find_s_L26 | word_premise |]. iNext. cbn [b_insts b_jump s_L26]. gen_env.
    iApply wp_branch; [word_premise|]. iNext.
    repeat match goal with |- context[if ?t then _ else _] => destruct t end; cbn [edge_label].
    + iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
      iApply (store_names with "Hc"); [word_premise | word_premise |]. iNext. iIntros "Hc".
      iApply ("HΦ" $! 0%nat j with "[%] Hs [$Hl3 $Hl4] [Hc]"); [lia|].
      cbn [Z.of_nat]. rewrite Z.add_0_r. destruct p. iExact "Hc".
    + iApply wp_enter; [exact find_s_L16 | reflexivity |]. iNext.
      iApply (spn_L16_suffix with "Hs [$Hl3 $Hl4] Hc"); [word_premise | exact Hj |]. iExact "HΦ".
Qed.

(** The strengthened triple: the first two name cells hold the same
    suffix pointer, the short-name cell another suffix pointer. The
    original string is returned intact, so [string_suffix] lends either
    selected string for printing and restores argv[0] afterwards. *)
Lemma set_program_name_suffix_spec p b reg ys r3 r4 x0 x1 y0 Φ :
  string p b reg ys -∗ literals r3 r4 -∗ cells x0 x1 y0 -∗
  ▷ (∀ i k, ⌜(i <= length ys)%nat /\ (k <= length ys)%nat⌝ -∗
     string p b reg ys -∗ literals r3 r4 -∗
     cells (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p))
       (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p))
       (mkPtr (ptr_addr p + Z.of_nat k) (ptr_cap p)) -∗ Φ RetVoid) -∗
  WP (ERun (invocation set_program_name_fn [WPtr p]) : nexpr) {{ Φ }}.
Proof.
  iIntros "Hs Hlit Hc HΦ". iDestruct "Hs" as "[%Hok Hps]".
  iAssert (string p b reg ys) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hcap & Hb0 & Hb1 & Hb2 & Hb3 & _). rewrite set_program_name_entry.
  iApply wp_enter; [exact find_s_start | reflexivity |]. iNext. cbn [b_insts b_jump s_start].
  iApply (wp_strrchr with "Hs");
    [exact Hstrrchr | apply linked_outside; [exact Hlinked | reflexivity] |
     apply linked_unbound; [exact Hlinked | reflexivity] | reflexivity | reflexivity |
     vm_compute; intuition congruence | vm_compute; intuition congruence |].
  iNext. iIntros (q Hq) "Hs".
  destruct Hq as [-> | (i & Hi & ->)].
  - iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [reflexivity|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L8 | reflexivity |]. iNext.
    iApply (spn_L8_suffix _ _ _ _ _ 0 with "Hs Hlit Hc HΦ");
      [destruct p; cbn; rewrite Z.add_0_r; reflexivity | reflexivity | lia].
  - iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L6 | reflexivity |]. iNext. cbn [b_insts b_jump s_L6].
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat (S i)));
      [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
    iNext. iApply wp_goto. iNext.
    iApply wp_enter; [exact find_s_L8 | reflexivity |]. iNext.
    iApply (spn_L8_suffix _ _ _ _ _ (S i) with "Hs Hlit Hc HΦ"); [reflexivity | reflexivity | lia].
Qed.

(** A printing-ready form of [set_program_name_suffix_spec]: own the
    selected program-name string, with a wand restoring the full argv[0].
    The suffix may be empty, including when argv[0] ends in a slash. *)
Lemma set_program_name_string_spec p b reg ys r3 r4 x0 x1 y0 Φ :
  string p b reg ys -∗ literals r3 r4 -∗ cells x0 x1 y0 -∗
  ▷ (∀ i k, ⌜(i <= length ys)%nat /\ (k <= length ys)%nat⌝ -∗
     string (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i ys) -∗
     (string (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i ys) -∗ string p b reg ys) -∗
     literals r3 r4 -∗
     cells (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p))
       (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p))
       (mkPtr (ptr_addr p + Z.of_nat k) (ptr_cap p)) -∗ Φ RetVoid) -∗
  WP (ERun (invocation set_program_name_fn [WPtr p]) : nexpr) {{ Φ }}.
Proof.
  iIntros "Hs Hlit Hc HΦ".
  iApply (set_program_name_suffix_spec with "Hs Hlit Hc").
  iNext. iIntros (i k [Hi Hk]) "Hs Hlit Hc".
  iDestruct (string_suffix _ _ _ _ i with "Hs") as "[Hs Hback]"; [exact Hi|].
  iApply ("HΦ" $! i k with "[%] Hs Hback Hlit Hc"). auto.
Qed.

End name.
End HelloProgNameOn.

(** [HelloProgNameOn] over a Logic instance of its own. *)
Module HelloProgName (R : Runtime).
Module LG0 := Logic R.
Include HelloProgNameOn R LG0.
End HelloProgName.
