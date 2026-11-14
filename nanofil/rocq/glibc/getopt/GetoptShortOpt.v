(** A short option that glibc's scanner finds in the option string may
    take an argument. One colon after the character means that it does,
    and two colons make the argument optional. "W;" in the option string
    lets "-W foo" stand for the long option "--foo". This file proves
    the tests that choose among these forms safe: the scanner reads the
    option string only up to two bytes past the character, which stay
    inside it, and it writes only the fields of its own state. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic GetoptModule
  GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptShort GetoptOptArg.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptOptArg GetoptShort GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The optional-argument module supplies the argument vector, its tactics and its step. *)
Import GetoptOptArg GetoptShort GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section opt.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance opt_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance opt_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A read half check of a pointer into a shared object needs only a
    share of that object's lifetime. *)
Lemma wp_half_check_read_dq f e ls l d bd lo hi al args rest j classes p1 p b reg dq Φ :
  op_arg_classes (HalfCheck bd lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (HalfCheck bd lo hi Read al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp1 Hp H1 H2 H3 H4 H5. apply (wp_read_dq registry (os_wi w0) ge dq _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E Lv] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]); [reflexivity | exact Hc | exact Hx |].
  exact (op_half_check_read _ _ _ _ _ _ _ _ _ Hp1 Hp E Lv H1 H2 H3 H4 H5).
Qed.

(** This tactic half-checks and loads byte k of the option string at po, which lies inside it. *)
Ltac rdopt po so k :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  let Hcap := fresh "Hcap" in
  iDestruct (ws_byte po so k with "Hpo") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|];
  destruct Hbb as (Hcap & ? & ? & ? & ?);
  iApply (wp_half_check_read_dq with "Hbl");
    [reflexivity | vx | reflexivity | exact Hcap | rawa | rawa | lia | lia | apply Z.mod_1_r |];
  iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | rawa |];
  iNext; iIntros "_ _"; iClear "Hbl Hbt".

(** After a known option x at index k of the option string, the byte
    after x says whether x takes an argument. A colon means that it does,
    and a second colon makes the argument optional. The scanner reads the
    second colon only after the first, so both reads stay inside the
    option string. An option without a colon keeps the state. An
    optional argument is the rest of the cluster, so the private option
    argument becomes the cursor, or null at the end of the cluster. The
    index steps past the argument and the cursor becomes null. A required
    argument leads on to its own blocks. The names ks keep their values
    from the caller's environment e0. *)
Lemma wp_getopt_argkind ks e0 e fr i cur t po so k a b r Φ :
  avoids ks opt_names = true -> keeps ks e0 e ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v459") e = Some (WPtr (mkPtr (ptr_addr po + Z.of_nat k) (ptr_cap po))) ->
  lookup (TAtom "chk144") e = Some (WPtr (mkPtr (ptr_addr po + Z.of_nat k) (ptr_cap po))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  (k < List.length so)%nat -> 0 <= i < 2 ^ 31 - 1 -> sbyte t 0 <> 0 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗ word_string DfracDiscarded po so -∗
  live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗ pcell b 32 (ptr_add cur 1) -∗
  ((∀ e', ⌜keeps ks e0 e' /\ sbyte so (S k) <> 58⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L510")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e0 e' /\ sbyte so (S k) = 58 /\ sbyte so (S (S k)) = 58⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗
      pcell b 32 null -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L619")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e0 e' /\ sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L611") (Some (TAtom "L603")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L510") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hk0 H12 H459 H144 Hc1 Hc2 Hc20 H137 Hk Hi Ht0 Hb Hal Hend Hr.
  iIntros "#Hws #Hpo Hl Hib Hab Hcur HK".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iDestruct (ws_shape with "Hpo") as %(Hcho & Hpop & Hpoe).
  pose proof (sbyte_range so (S k) Hcho) as Hx1r. pose proof (sbyte_range so (S (S k)) Hcho) as Hx2r.
  step. step. norm. rdopt po so (S k). step. rewrite chr_cmp; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte so (S k)) 58) as [E58 | E58]; close_br.
  2: { iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl Hib Hab Hcur"). split; [xkeep | exact E58]. }
  pose proof (sbyte_in_len so (S k) ltac:(lia)) as Hk1.
  step. step. norm. rdopt po so (S (S k)). step. rewrite chr_cmp; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte so (S (S k))) 58) as [E58' | E58']; close_br.
  2: { iDestruct "HK" as "[_ [_ HK]]". iApply ("HK" with "[%] Hl Hib Hab Hcur"). split; [xkeep|]. split; assumption. }
  iDestruct "HK" as "[_ [HK _]]".
  iApply (wp_getopt_optarg w0 registry ge ks e0 with "Hws Hl Hib Hab Hcur [HK]");
    [exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | exact Hi | exact Ht0 | exact Hb
    | exact Hal | exact Hend | exact Hr |].
  iIntros (e') "%Hk' Hl Hib Hab Hcur". iApply ("HK" with "[%] Hl Hib Hab Hcur"). split; [exact Hk'|]. split; assumption.
Qed.

(** The character x at index k of the option string, which is neither
    a colon nor a semicolon, names a known option. "W;" with a long
    option table leads to the long-option form of the W option. Any other
    option goes on to the colon tests above. *)
Lemma wp_getopt_known ks e i cur t po so k a lo b r Φ :
  avoids ks opt_names = true ->
  lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v80") e = Some (WInt 0) ->
  lookup (TAtom "v459") e = Some (WPtr (ptr_add po (Z.of_nat k))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  (k < List.length so)%nat -> 0 <= i < 2 ^ 31 - 1 -> sbyte t 0 <> 0 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗ word_string DfracDiscarded po so -∗
  live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗ pcell b 32 (ptr_add cur 1) -∗
  ((∀ e', ⌜keeps ks e e' /\ sbyte so k = 87 /\ sbyte so (S k) = 59 /\ ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte so (S k) <> 58⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L510")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte so (S k) = 58 /\ sbyte so (S (S k)) = 58⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗
      pcell b 32 null -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L619")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L611") (Some (TAtom "L603")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L473") (Some (TAtom "L485")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks H6 H12 H80 H459 Hc1 Hc2 Hc20 H137 Hk Hi Ht0 Hb Hal Hend Hr.
  iIntros "#Hws #Hpo Hl Hib Hab Hcur HK".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iDestruct (ws_shape with "Hpo") as %(Hcho & Hpop & Hpoe).
  unfold ptr_add in H459. step.
  iDestruct (ws_byte po so k with "Hpo") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap & ? & ? & ? & ?).
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | rawa | rawa | apply Z.mod_1_r |]; iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | rawa |].
  iNext; iIntros "_ _". iClear "Hbl Hbt".
  pose proof (sbyte_range so k Hcho) as Hxr. pose proof (sbyte_range so (S k) Hcho) as Hx1r.
  step. rewrite chr_cmp; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte so k) 87) as [E87 | E87]; close_br.
  - step. step. norm. rdopt po so (S k). step. rewrite chr_cmp; [|lia|lia]. step. step.
    iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte so (S k)) 59) as [E59 | E59]; close_br.
    + step. step. step. step. step. change (0 mod 2 ^ 64) with 0.
      iApply wp_branch; [vx | iNext]. destruct (ptr_addr lo mod 2 ^ 64 =? 0) eqn:El; close_br.
      * iDestruct "HK" as "[_ HK]". iApply (wp_getopt_argkind ks e with "Hws Hpo Hl Hib Hab Hcur HK");
          [exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | exact Hk | exact Hi
          | exact Ht0 | exact Hb | exact Hal | exact Hend | exact Hr].
      * iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl Hib Hab Hcur").
        split; [xkeep|]. split; [exact E87|]. split; [exact E59|]. apply Z.eqb_neq. exact El.
    + step. iApply wp_branch; [vx | iNext]. close_br. iDestruct "HK" as "[_ HK]". iApply (wp_getopt_argkind ks e with "Hws Hpo Hl Hib Hab Hcur HK");
        [exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | exact Hk | exact Hi
        | exact Ht0 | exact Hb | exact Hal | exact Hend | exact Hr].
  - step. iApply wp_branch; [vx | iNext]. close_br. step. iApply wp_branch; [vx | iNext]. close_br.
    iDestruct "HK" as "[_ HK]". iApply (wp_getopt_argkind ks e with "Hws Hpo Hl Hib Hab Hcur HK");
      [exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | exact Hk | exact Hi
      | exact Ht0 | exact Hb | exact Hal | exact Hend | exact Hr].
Qed.

End opt.
