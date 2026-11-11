(** GNU Hello's locale helpers through the program logic of Logic.v
    (docs/logic.md): gnulib's `hard_locale` and the
    `setlocale_null_r` chain beneath it, which `rpl_mbrtowc` calls to
    decide whether a byte may stand for itself.

    `setlocale_null_unlocked(k)` is setlocale's query of the category
    k, whose answer is libc's own name for it: a string the world lends
    (LentLogic.v). `setlocale_null_r_unlocked(k, buf, n)` copies that
    name into buf when it fits, returning 0, or the n - 1 bytes that do
    with a NUL after them, returning ERANGE (34); a name is never NULL,
    so the EINVAL path (22) is dead. `hard_locale(k)` copies the name
    into a 257-byte local and compares it with "C" and "POSIX".

    The triples are generic in the world interpretation wi, given that
    wi keeps every lent string where [lent_at] says, that setlocale's
    query answers with the lent pointer and changes nothing, and that
    wi survives the allocation, the copy and the byte store these
    functions make into memory they own. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic MemLogic
  LentLogic HelloModule HelloLeaf.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
    computed. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The functions *)

(** `setlocale_null_unlocked(category)`. *)
Definition snu_fn : func := Eval vm_compute in hello_fn "setlocale_null_unlocked".
(** Its one block: setlocale's query, returned. *)
Definition u_start : block := Eval vm_compute in hblk snu_fn "start".

(** `setlocale_null_r_unlocked(category, buf, bufsize)`. *)
Definition snru_fn : func := Eval vm_compute in hello_fn "setlocale_null_r_unlocked".
(** Query the name; is it NULL? *)
Definition r_start : block := Eval vm_compute in hblk snru_fn "start".
(** Its length; does it fit? *)
Definition r_L10 : block := Eval vm_compute in hblk snru_fn "L10".
(** It fits: copy it with its NUL, and return 0. *)
Definition r_L27 : block := Eval vm_compute in hblk snru_fn "L27".
(** It does not: is there room for anything? *)
Definition r_L28 : block := Eval vm_compute in hblk snru_fn "L28".
(** Copy what fits, and end it with a NUL. *)
Definition r_L39 : block := Eval vm_compute in hblk snru_fn "L39".
(** Return ERANGE. *)
Definition r_L41 : block := Eval vm_compute in hblk snru_fn "L41".

(** `setlocale_null_r(category, buf, bufsize)`, without a lock. *)
Definition snr_fn : func := Eval vm_compute in hello_fn "setlocale_null_r".
(** Its one block: the unlocked call, returned. *)
Definition n_start : block := Eval vm_compute in hblk snr_fn "start".

(** `hard_locale(category)`. *)
Definition hard_locale_fn : func := Eval vm_compute in hello_fn "hard_locale".
(** A 257-byte buffer, and the name into it. *)
Definition h_start : block := Eval vm_compute in hblk hard_locale_fn "start".
(** The name did not fit: not a hard locale. *)
Definition h_L3 : block := Eval vm_compute in hblk hard_locale_fn "L3".
(** Is it "C"? *)
Definition h_L5 : block := Eval vm_compute in hblk hard_locale_fn "L5".
(** Is it "POSIX"? *)
Definition h_L16 : block := Eval vm_compute in hblk hard_locale_fn "L16".
(** Branch on the answer. *)
Definition h_L17 : block := Eval vm_compute in hblk hard_locale_fn "L17".
(** A hard locale. *)
Definition h_L10 : block := Eval vm_compute in hblk hard_locale_fn "L10".
(** "C" or "POSIX": not a hard locale. *)
Definition h_L12 : block := Eval vm_compute in hblk hard_locale_fn "L12".

(** `setlocale_null_unlocked` has its entry. *)
Lemma find_u_start : find_block (TAtom "start") (fn_blocks snu_fn) = Some u_start.
Proof. vm_compute. reflexivity. Qed.
(** `setlocale_null_r_unlocked` has its entry. *)
Lemma find_r_start : find_block (TAtom "start") (fn_blocks snru_fn) = Some r_start.
Proof. vm_compute. reflexivity. Qed.
(** `setlocale_null_r_unlocked` has L10. *)
Lemma find_r_L10 : find_block (TAtom "L10") (fn_blocks snru_fn) = Some r_L10.
Proof. vm_compute. reflexivity. Qed.
(** `setlocale_null_r_unlocked` has L27. *)
Lemma find_r_L27 : find_block (TAtom "L27") (fn_blocks snru_fn) = Some r_L27.
Proof. vm_compute. reflexivity. Qed.
(** `setlocale_null_r_unlocked` has L28. *)
Lemma find_r_L28 : find_block (TAtom "L28") (fn_blocks snru_fn) = Some r_L28.
Proof. vm_compute. reflexivity. Qed.
(** `setlocale_null_r_unlocked` has L39. *)
Lemma find_r_L39 : find_block (TAtom "L39") (fn_blocks snru_fn) = Some r_L39.
Proof. vm_compute. reflexivity. Qed.
(** `setlocale_null_r_unlocked` has L41. *)
Lemma find_r_L41 : find_block (TAtom "L41") (fn_blocks snru_fn) = Some r_L41.
Proof. vm_compute. reflexivity. Qed.
(** `setlocale_null_r` has its entry. *)
Lemma find_n_start : find_block (TAtom "start") (fn_blocks snr_fn) = Some n_start.
Proof. vm_compute. reflexivity. Qed.
(** `hard_locale` has its entry. *)
Lemma find_h_start : find_block (TAtom "start") (fn_blocks hard_locale_fn) = Some h_start.
Proof. vm_compute. reflexivity. Qed.
(** `hard_locale` has L3. *)
Lemma find_h_L3 : find_block (TAtom "L3") (fn_blocks hard_locale_fn) = Some h_L3.
Proof. vm_compute. reflexivity. Qed.
(** `hard_locale` has L5. *)
Lemma find_h_L5 : find_block (TAtom "L5") (fn_blocks hard_locale_fn) = Some h_L5.
Proof. vm_compute. reflexivity. Qed.
(** `hard_locale` has L16. *)
Lemma find_h_L16 : find_block (TAtom "L16") (fn_blocks hard_locale_fn) = Some h_L16.
Proof. vm_compute. reflexivity. Qed.
(** `hard_locale` has L17. *)
Lemma find_h_L17 : find_block (TAtom "L17") (fn_blocks hard_locale_fn) = Some h_L17.
Proof. vm_compute. reflexivity. Qed.
(** `hard_locale` has L10. *)
Lemma find_h_L10 : find_block (TAtom "L10") (fn_blocks hard_locale_fn) = Some h_L10.
Proof. vm_compute. reflexivity. Qed.
(** `hard_locale` has L12. *)
Lemma find_h_L12 : find_block (TAtom "L12") (fn_blocks hard_locale_fn) = Some h_L12.
Proof. vm_compute. reflexivity. Qed.

(** `setlocale_null_unlocked`'s entry binds its category. *)
Lemma snu_entry k :
  invocation snu_fn [WInt k] = mkFrame snu_fn [(TAtom "v0", WInt k)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.
(** `setlocale_null_r_unlocked`'s entry binds its category, buffer and size. *)
Lemma snru_entry k p n :
  invocation snru_fn [WInt k; WPtr p; WInt n] =
  mkFrame snru_fn [(TAtom "v4", WInt n); (TAtom "v2", WPtr p); (TAtom "v0", WInt k)] []
    None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.
(** `setlocale_null_r`'s entry binds its category, buffer and size. *)
Lemma snr_entry k p n :
  invocation snr_fn [WInt k; WPtr p; WInt n] =
  mkFrame snr_fn [(TAtom "v4", WInt n); (TAtom "v2", WPtr p); (TAtom "v0", WInt k)] []
    None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.
(** `hard_locale`'s entry binds its category. *)
Lemma hard_locale_entry k :
  invocation hard_locale_fn [WInt k] =
  mkFrame hard_locale_fn [(TAtom "v0", WInt k)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The genv's functions, for a genv with Hello's module. *)
Lemma locale_fns ge : ge_module ge = hello_module ->
  find_fn ge (TAtom "setlocale_null_unlocked") = Some (Defined snu_fn) /\
  find_fn ge (TAtom "setlocale_null_r_unlocked") = Some (Defined snru_fn) /\
  find_fn ge (TAtom "setlocale_null_r") = Some (Defined snr_fn).
Proof. intros Hm. unfold find_fn. rewrite Hm. vm_compute. auto. Qed.

(** The literals "C" and "POSIX" of hard-locale.c, read-only. *)
Definition c_ptr : ptr := mkPtr 65824 (Ro 65824).
(** Its bytes. *)
Definition c_bytes : list Z := [67].
(** "POSIX". *)
Definition posix_ptr : ptr := mkPtr 65856 (Ro 65856).
(** Its bytes. *)
Definition posix_bytes : list Z := [80; 79; 83; 73; 88].

(** Hello's symbols put the two literals there. *)
Lemma locale_globals :
  lookup (TAtom "hard-locale#str.31") hello_globals = Some c_ptr /\
  lookup (TAtom "hard-locale#str.32") hello_globals = Some posix_ptr.
Proof. vm_compute. auto. Qed.

(** What `setlocale_null_r_unlocked` leaves in an n-byte buffer for
    the name t: the result r, the string u now at the buffer's start and
    the buffer's bytes ys. A name shorter than the buffer is copied with
    its NUL and r is 0; a longer one is cut to n - 1 bytes and a NUL,
    and r is ERANGE (34). *)
Definition snru_result (t : list Z) (n : nat) (r : Z) (u ys : list Z) : Prop :=
  ((length t < n)%nat /\ r = 0 /\ u = t \/ (n <= length t)%nat /\ r = 34 /\ u = take (n - 1) t) /\
  length ys = n /\ take (S (length u)) ys = u ++ [0].

(** Take every branch of the goal's conditions: each path is safe. *)
Ltac all_cases :=
  repeat match goal with |- context[if ?t then _ else _] => destruct t end; cbn [edge_label].

(** ## The triples *)

(** The locale helpers over any [[runtime]] R. *)
Module HelloLocaleOn (R : Runtime) (LG0 : LogicSig R).
Module HL := HelloLeafOn R LG0.
Module LL := HL.LL.
Module ML := HL.ML.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Import L LG SL ML LL HL.

Section locale.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The genv links Hello, whose world interpretation keeps every lent
    string where [lent_at] says. *)
Context (Hlinked : hello_linked ge)
  (wi_lent : forall m w h k p t, wi m w h -> live_disjoint m -> objects_fit (m_regions m) ->
     freed_empty (m_regions m) -> h !! PName k = Some (VName p t) -> lent_at m h p t).

(** setlocale's contract spec answers a query, of a category whose name
    the world lends, with that name, changing nothing; the query's
    arguments are admitted wherever the name is lent. *)
Context (set_spec : contract world) (Hset : registry (TAtom "setlocale") = Some set_spec)
  (Hset_ret : contract_returns set_spec = RClass P)
  (Hset_abi : forall d c v, contract_abi set_spec (CResult d P) [Arg W c; Arg P v])
  (Hset_pre : forall m w h k p t z, wi m w h -> h !! PName k = Some (VName p t) -> ptr_addr z = 0 ->
     contract_pre set_spec [WInt k; WPtr z] m w)
  (Hset_query : forall r args s m w h k p t z trace ending s' m' w',
     wi m w h -> h !! PName k = Some (VName p t) -> ptr_addr z = 0 ->
     M.E.invoke set_spec r args [WInt k; WPtr z] s m w trace ending s' m' w' ->
     s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr p]).

(** strlen and memcpy have their contracts. *)
Context (Hstrlen : registry (TAtom "strlen") = Some (strlen_contract world))
  (Hmemcpy : registry (TAtom "memcpy") = Some (memcpy_contract world)).

(** The world interpretation survives a copy into a block the program
    owns, whatever bytes it leaves there, and a byte store into one. *)
Context (Kcopy : forall b reg o xs cs s n m m' wd h ys,
     copy_result m (mkPtr (b + o) (Obj b)) s n m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     length ys = length xs ->
     wi m' wd (overwrite (block_ps b reg o ys (slots_after m' b o (length xs))) h))
  (Kbyte : forall b reg o x y m wd h,
     (forall l v, (l, v) ∈ [(PLive b, VLive reg); (PByte b o, VByte x)] -> h !! l = Some v) ->
     wi m wd h ->
     wi (store_bytes m (b + o) 1 y) wd (overwrite [(PLive b, VLive reg); (PByte b o, VByte (y mod 256))] h))
  (Kalloc : forall q m wd h base, fresh m q base -> wi m wd h ->
     wi (allocated m q base) wd (overwrite (obj_ps base q) h)).

(** strcmp has its contract, for `streq`. *)
Context (Hstrcmp : registry (TAtom "strcmp") = Some (strcmp_contract world)).

(** The Iris instance of the registry and wi. *)
Local Instance locale_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation hexpr := (language.expr (nanofil_lang registry ge)).

(** `setlocale_null_unlocked(k)` returns the name the world lends for k. *)
Lemma snu_spec k p t Φ :
  0 <= k < 2 ^ 32 ->
  lent k p t -∗ ▷ Φ (Ret (WPtr p)) -∗ WP (ERun (invocation snu_fn [WInt k]) : hexpr) {{ Φ }}.
Proof.
  intros Hk32. iIntros "#Hk HΦ". rewrite snu_entry.
  iApply wp_enter; [exact find_u_start | reflexivity |]. iNext. cbn [b_insts b_jump u_start].
  iApply (wp_lent_query _ _ _ _ _ _ _ _ _ _ _ _ set_spec [WInt k; WPtr (mkPtr 0 CNone)] k p t with "Hk");
    [exact Hset | exact Hset_ret | apply linked_outside; [exact Hlinked | reflexivity] |
     apply linked_unbound; [exact Hlinked | reflexivity] | reflexivity |
     cbn; rewrite Z.mod_small; [reflexivity | exact Hk32] | apply Hset_abi |
     intros m w h Hw Hl; exact (Hset_pre m w h k p t (mkPtr 0 CNone) Hw Hl eq_refl) |
     intros s m w h tr en s' m' w' Hw Hl Hi; exact (Hset_query _ _ s m w h k p t (mkPtr 0 CNone) tr en s' m' w' Hw Hl eq_refl Hi) |].
  iNext. iApply wp_ret; [reflexivity | reflexivity |]. iNext. iExact "HΦ".
Qed.

(** `setlocale_null_r_unlocked(k, buf, n)`, for the n-byte block of
    the bytes xs and the slots cs at the start of the live object b, at
    a multiple of 8, and the name t the world lends for k: it leaves
    [snru_result] in the block and returns its r. *)
Lemma snru_spec k p t b reg xs cs Φ :
  0 <= k < 2 ^ 32 -> 0 < b -> b mod 8 = 0 -> length cs = length xs -> (0 < length xs)%nat ->
  b + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  lent k p t -∗ live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗
  ▷ (∀ r u ys cs', ⌜snru_result t (length xs) r u ys /\ length cs' = length xs⌝ -∗
       live b reg -∗ bytes b 0 ys -∗ auxes b 0 cs' -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (invocation snru_fn [WInt k; WPtr (mkPtr b (Obj b)); WInt (Z.of_nat (length xs))]) : hexpr)
    {{ Φ }}.
Proof.
  intros Hk32 Hb0 Hb8 Hlc Hn Hend H48. iIntros "#Hk Hl Hx Hcs HΦ".
  iPoseProof "Hk" as "[%Hp _]". destruct Hp as (Hp & Hpt & Ht).
  destruct (locale_fns ge (proj1 Hlinked)) as (Hsnu & _ & _).
  rewrite snru_entry. iApply wp_enter; [exact find_r_start | reflexivity |]. iNext.
  cbn [b_insts b_jump r_start].
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ snu_fn (invocation snu_fn [WInt k]));
    [cbn; rewrite Z.mod_small; [reflexivity | exact Hk32] | exact Hsnu | reflexivity |].
  iNext. iApply (snu_spec with "Hk"); [exact Hk32|]. iNext.
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [exact find_r_L10 | reflexivity |]. iNext. cbn [b_insts b_jump r_L10].
  iApply (wp_strlen_lent with "Hk");
    [exact wi_lent | exact Hstrlen | apply linked_outside; [exact Hlinked | reflexivity] |
     apply linked_unbound; [exact Hlinked | reflexivity] | word_premise |].
  iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  destruct (decide (length t < length xs)%nat) as [Hfit|Hlong].
  - (* The name fits: copy it with its NUL. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_r_L27 | reflexivity |]. iNext. cbn [b_insts b_jump r_L27].
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    set (c := S (length t)).
    iAssert (bytes b 0 (take c xs) ∗ bytes b (0 + Z.of_nat (length (take c xs))) (drop c xs))%I
      with "[Hx]" as "[Hx1 Hx2]"; [rewrite -bytes_app take_drop; iExact "Hx"|].
    iAssert (auxes b 0 (take c cs) ∗ auxes b (0 + Z.of_nat (length (take c cs))) (drop c cs))%I
      with "[Hcs]" as "[Hc1 Hc2]"; [rewrite -auxes_app take_drop; iExact "Hcs"|].
    assert (Hc : length (take c xs) = c) by (rewrite length_take; lia).
    assert (Hcc : length (take c cs) = c) by (rewrite length_take; lia).
    iApply (wp_memcpy_lent with "Hk Hl Hx1 Hc1");
      [exact wi_lent | exact Hmemcpy | apply linked_outside; [exact Hlinked | reflexivity] |
       apply linked_unbound; [exact Hlinked | reflexivity] | cbn; rewrite Z.add_0_r; reflexivity |
       word_premise | rewrite Hc; cbn; do 2 f_equal; unfold c; drop_wraps_goal; lia | rewrite Hc; lia | rewrite Hc Hcc; reflexivity |
       exact Hb8 | reflexivity | lia | rewrite Hc; lia |
       intros m m' wd h Hres Hlk Hw; apply (Kcopy _ _ _ _ _ _ _ _ _ _ _ _ Hres Hlk Hw);
       rewrite length_take length_app Hc; cbn [length]; unfold c; lia |].
    iNext. iIntros (cs1 Hcs1) "Hl Hx1 Hc1".
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    assert (Ec : take (length (take c xs)) (t ++ [0]) = t ++ [0])
      by (rewrite Hc take_ge; [reflexivity | rewrite length_app; cbn [length]; unfold c; lia]).
    rewrite Ec Hc Hcc. rewrite Hc in Hcs1.
    iApply ("HΦ" $! 0 t ((t ++ [0]) ++ drop c xs) (cs1 ++ drop c cs) with "[%] Hl [Hx1 Hx2] [Hc1 Hc2]").
    + split; [|rewrite length_app length_drop; lia]. split; [left; auto|]. split.
      * rewrite !length_app length_drop. cbn [length]. unfold c. lia.
      * replace (S (length t)) with (length (t ++ [0])) by (rewrite length_app; cbn [length]; lia).
        apply take_app_length.
    + iApply bytes_app. rewrite length_app. cbn [length].
      replace (0 + Z.of_nat (length t + 1)) with (0 + Z.of_nat c) by (unfold c; lia). iFrame.
    + iApply auxes_app. rewrite Hcs1. iFrame.
  - (* The name does not fit: copy n - 1 bytes of it and end them with a NUL. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_r_L28 | reflexivity |]. iNext. cbn [b_insts b_jump r_L28].
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_r_L39 | reflexivity |]. iNext. cbn [b_insts b_jump r_L39].
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    set (c := (length xs - 1)%nat).
    assert (Hc : length (take c xs) = c) by (rewrite length_take; lia).
    assert (Hcc : length (take c cs) = c) by (rewrite length_take; lia).
    destruct (drop c xs) as [|x [|x' rest]] eqn:Ed;
      [apply (f_equal length) in Ed; rewrite length_drop in Ed; cbn in Ed; lia| |
       apply (f_equal length) in Ed; rewrite length_drop in Ed; cbn in Ed; lia].
    assert (Eb : forall y, byte_ps b (Z.of_nat c) [y] = [(PByte b (Z.of_nat c), VByte y)])
      by (intros y; rewrite byte_ps_cons; reflexivity).
    iAssert (bytes b 0 (take c xs) ∗ bytes b (0 + Z.of_nat (length (take c xs))) (drop c xs))%I
      with "[Hx]" as "[Hx1 Hx2]"; [rewrite -bytes_app take_drop; iExact "Hx"|].
    rewrite Ed Hc Z.add_0_l /bytes Eb. iEval (rewrite -/(ibyte b (Z.of_nat c) x)) in "Hx2".
    rewrite -/(bytes b 0 (take c xs)).
    iAssert (auxes b 0 (take c cs) ∗ auxes b (0 + Z.of_nat (length (take c cs))) (drop c cs))%I
      with "[Hcs]" as "[Hc1 Hc2]"; [rewrite -auxes_app take_drop; iExact "Hcs"|].
    rewrite Hcc.
    iApply (wp_memcpy_lent with "Hk Hl Hx1 Hc1");
      [exact wi_lent | exact Hmemcpy | apply linked_outside; [exact Hlinked | reflexivity] |
       apply linked_unbound; [exact Hlinked | reflexivity] | cbn; rewrite Z.add_0_r; reflexivity |
       word_premise | rewrite Hc; cbn; do 2 f_equal; unfold c; drop_wraps_goal; lia | rewrite Hc; lia |
       rewrite Hc Hcc; reflexivity | exact Hb8 | reflexivity | lia | rewrite Hc; lia |
       intros m m' wd h Hres Hlk Hw; apply (Kcopy _ _ _ _ _ _ _ _ _ _ _ _ Hres Hlk Hw);
       rewrite length_take length_app Hc; cbn [length]; unfold c; lia |].
    iNext. iIntros (cs1 Hcs1) "Hl Hx1 Hc1". rewrite Hc in Hcs1.
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + Z.of_nat c));
      [word_premise | cbn; f_equal; f_equal; unfold c; addr_premise | word_premise |].
    iNext.
    iApply (wp_check with "Hl");
      [reflexivity | word_premise | reflexivity | unfold c; addr_premise | unfold c; addr_premise |
       addr_premise |].
    iNext. iIntros "Hl".
    iApply (wp_raw_store_byte with "Hl Hx2");
      [word_premise | word_premise | reflexivity | unfold c; addr_premise |
       intros m wd h Hlk Hw; exact (Kbyte _ _ _ _ _ _ _ _ Hlk Hw) |].
    iNext. iIntros "Hl Hx2".
    iApply wp_goto. iNext.
    iApply wp_enter; [exact find_r_L41 | reflexivity |]. iNext. cbn [b_insts b_jump r_L41].
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    assert (Ec : take (length (take c xs)) (t ++ [0]) = take c t)
      by (rewrite Hc take_app_le; [reflexivity | lia]).
    rewrite Ec.
    iApply ("HΦ" $! 34 (take c t) (take c t ++ [0]) (cs1 ++ drop c cs) with "[%] Hl [Hx1 Hx2] [Hc1 Hc2]").
    + split; [|rewrite length_app length_drop; lia]. split; [right; split; [lia|]; split; [reflexivity|]; reflexivity|].
      split.
      * rewrite length_app length_take. cbn [length]. unfold c. lia.
      * apply take_ge. rewrite length_app. cbn [length]. lia.
    + iApply bytes_app. rewrite length_take Nat.min_l; [|unfold c; lia].
      rewrite Z.add_0_l /bytes Eb. iFrame "Hx1". iExact "Hx2".
    + iApply auxes_app. rewrite Hcs1. iFrame.
Qed.

(** `setlocale_null_r(k, buf, n)` is `setlocale_null_r_unlocked`'s
    call ([snru_spec]): this build takes no lock. *)
Lemma snr_spec k p t b reg xs cs Φ :
  0 <= k < 2 ^ 32 -> 0 < b -> b mod 8 = 0 -> length cs = length xs -> (0 < length xs)%nat ->
  b + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  lent k p t -∗ live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗
  ▷ (∀ r u ys cs', ⌜snru_result t (length xs) r u ys /\ length cs' = length xs⌝ -∗
       live b reg -∗ bytes b 0 ys -∗ auxes b 0 cs' -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (invocation snr_fn [WInt k; WPtr (mkPtr b (Obj b)); WInt (Z.of_nat (length xs))]) : hexpr)
    {{ Φ }}.
Proof.
  intros Hk32 Hb0 Hb8 Hlc Hn Hend H48. iIntros "#Hk Hl Hx Hcs HΦ".
  destruct (locale_fns ge (proj1 Hlinked)) as (_ & Hsnru & _).
  rewrite snr_entry. iApply wp_enter; [exact find_n_start | reflexivity |]. iNext.
  cbn [b_insts b_jump n_start].
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ snru_fn
            (invocation snru_fn [WInt k; WPtr (mkPtr b (Obj b)); WInt (Z.of_nat (length xs))]));
    [cbn; rewrite !Z.mod_small; [reflexivity | lia | exact Hk32] | exact Hsnru | reflexivity |].
  iNext. iApply (snru_spec with "Hk Hl Hx Hcs"); [exact Hk32 | exact Hb0 | exact Hb8 | exact Hlc | exact Hn |
                                                  exact Hend | exact H48 |].
  iNext. iIntros (r u ys cs' Hr) "Hl Hx Hcs".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  assert (Hr32 : r = 0 \/ r = 34) by (destruct Hr as (([(_ & -> & _)|(_ & -> & _)] & _) & _); auto).
  destruct Hr32 as [-> | ->];
    (iApply wp_ret; [reflexivity | reflexivity |]; iNext; iApply ("HΦ" with "[%] Hl Hx Hcs"); exact Hr).
Qed.

(** The genv's literals are Hello's, and `streq` and
    `setlocale_null_r` are its functions. *)
Lemma hard_locale_lookups :
  lookup (TAtom "hard-locale#str.31") (ge_globals ge) = Some c_ptr /\
  lookup (TAtom "hard-locale#str.32") (ge_globals ge) = Some posix_ptr /\
  find_fn ge (TAtom "streq") = Some (Defined streq_fn) /\
  find_fn ge (TAtom "setlocale_null_r") = Some (Defined snr_fn).
Proof.
  destruct locale_globals as (H1 & H2). destruct Hlinked as (Hm & Hg & _).
  split; [exact (Hg _ _ H1)|]. split; [exact (Hg _ _ H2)|].
  split; [unfold find_fn; rewrite Hm; vm_compute; reflexivity | exact (proj2 (proj2 (locale_fns ge Hm)))].
Qed.

(** `hard_locale(k)`, for the name t the world lends for k, and the
    literals "C" and "POSIX" owned as strings: it copies the name into
    a fresh 257-byte buffer, compares it with both, and returns. *)
Lemma hard_locale_spec k p t rc rp Φ :
  0 <= k < 2 ^ 32 ->
  lent k p t -∗ string c_ptr 65824 rc c_bytes -∗ string posix_ptr 65856 rp posix_bytes -∗
  ▷ (∀ r, string c_ptr 65824 rc c_bytes -∗ string posix_ptr 65856 rp posix_bytes -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (invocation hard_locale_fn [WInt k]) : hexpr) {{ Φ }}.
Proof.
  intros Hk32. iIntros "#Hk Hc Hposix HΦ".
  iPoseProof "Hk" as "[%Hp _]". destruct Hp as (Hp & Hpt & Ht).
  destruct hard_locale_lookups as (Hlc & Hlp & Hstreq & Hsnr).
  rewrite hard_locale_entry. iApply wp_enter; [exact find_h_start | reflexivity |]. iNext.
  cbn [b_insts b_jump h_start].
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 257);
    [reflexivity | lia | unfold max_allocation_size; lia | intros m wd h base Hf Hw; exact (Kalloc _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (base Hbase) "Hobj". destruct Hbase as (Hb0 & Hb16 & Hb48).
  change (base mod 16 = 0) in Hb16. change (base + 272 <= 2 ^ 48) in Hb48.
  iDestruct (obj_zero_block with "Hobj") as "(Hl & Hx & Hcs)"; [compute; discriminate|].
  assert (Hext : req_extent (heap_req 4 257) = 272) by reflexivity. rewrite Hext in Hb48 |- *.
  match goal with |- context[live base ?r] => set (reg := r) end.
  iAssert (bytes base 0 (replicate 257 0))%I with "[Hx]" as "Hx".
  { rewrite (_ : Z.to_nat 272 = 257 + 15)%nat; [|reflexivity]. rewrite replicate_add bytes_app.
    iDestruct "Hx" as "[$ _]". }
  iAssert (auxes base 0 (replicate 257 CNone))%I with "[Hcs]" as "Hcs".
  { rewrite (_ : Z.to_nat 272 = 257 + 15)%nat; [|reflexivity]. rewrite replicate_add auxes_app.
    iDestruct "Hcs" as "[$ _]". }
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ snr_fn
            (invocation snr_fn [WInt k; WPtr (mkPtr base (Obj base)); WInt (Z.of_nat (length (replicate 257 0)))]));
    [cbn; rewrite Z.mod_small; [reflexivity | exact Hk32] | exact Hsnr | reflexivity |].
  iNext. iApply (snr_spec with "Hk Hl Hx Hcs");
    [exact Hk32 | exact Hb0 |
     pose proof (Z.div_mod base 16 ltac:(lia)); pose proof (Z.div_mod base 8 ltac:(lia));
       pose proof (Z.mod_pos_bound base 8 ltac:(lia)); lia |
     rewrite !length_replicate; reflexivity | rewrite length_replicate; lia |
     rewrite length_replicate; unfold reg; cbn [r_end]; change (Z.of_nat 257) with 257; lia | unfold reg; cbn [r_end]; lia |].
  iNext. iIntros (r u ys cs' [Hr _]) "Hl Hx Hcs".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  rewrite length_replicate in Hr.
  destruct Hr as ([(Hfit & -> & ->)|(Hlong & -> & ->)] & Hys & Htake).
  - (* The name fit: compare it with "C", then "POSIX". *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_h_L5 | reflexivity |]. iNext. cbn [b_insts b_jump h_L5].
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iAssert (bytes base 0 (t ++ [0]) ∗
             bytes base (0 + Z.of_nat (length (take (S (length t)) ys))) (drop (S (length t)) ys))%I
      with "[Hx]" as "[Hx _]"; [rewrite -Htake -bytes_app take_drop; iExact "Hx"|].
    iDestruct (block_string base reg 0 t with "Hl Hx") as "Hs".
    { split; [left; reflexivity|]. unfold reg; cbn [ptr_addr r_end]. split; [exact Hb0|]. split; [lia|].
      split; [lia|]. split; [lia | exact Ht]. }
    rewrite Z.add_0_r.
    iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ streq_fn
              (invocation streq_fn [WPtr (mkPtr base (Obj base)); WPtr c_ptr]));
      [word_premise | exact Hstreq | reflexivity |].
    iNext. iApply (streq_spec registry wi ge Hlinked with "Hs Hc"); [exact Hstrcmp|].
    iNext. iIntros (k1) "Hs Hc". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_branch; [word_premise|]. iNext. all_cases.
    + iApply wp_enter; [exact find_h_L16 | reflexivity |]. iNext. cbn [b_insts b_jump h_L16].
      iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
      iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ streq_fn
                (invocation streq_fn [WPtr (mkPtr base (Obj base)); WPtr posix_ptr]));
        [word_premise | exact Hstreq | reflexivity |].
      iNext. iApply (streq_spec registry wi ge Hlinked with "Hs Hposix"); [exact Hstrcmp|].
      iNext. iIntros (k2) "Hs Hposix". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
      cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
      iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
      iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
      iApply wp_goto. iNext.
      iApply wp_enter; [exact find_h_L17 | word_premise |]. iNext. cbn [b_insts b_jump h_L17].
      iApply wp_branch; [word_premise|]. iNext. all_cases;
        (first [iApply wp_enter; [exact find_h_L10 | reflexivity |] |
                iApply wp_enter; [exact find_h_L12 | reflexivity |]];
         iNext; cbn [b_insts b_jump h_L10 h_L12];
         (iApply wp_ret; [reflexivity | reflexivity |]); iNext; iApply ("HΦ" with "Hc Hposix")).
    + iApply wp_enter; [exact find_h_L17 | word_premise |]. iNext. cbn [b_insts b_jump h_L17].
      iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      iApply wp_enter; [exact find_h_L12 | reflexivity |]. iNext. cbn [b_insts b_jump h_L12].
      iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HΦ" with "Hc Hposix").
  - (* The name did not fit: not a hard locale. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 34); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_h_L3 | reflexivity |]. iNext. cbn [b_insts b_jump h_L3].
    iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HΦ" with "Hc Hposix").
Qed.

End locale.
End HelloLocaleOn.

(** [HelloLocaleOn] over a Logic instance of its own. *)
Module HelloLocale (R : Runtime).
Module LG0 := Logic R.
Include HelloLocaleOn R LG0.
End HelloLocale.
