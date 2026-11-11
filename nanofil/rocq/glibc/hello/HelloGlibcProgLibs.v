(** The "/.libs/" test of GNU Hello's `set_program_name` (HelloName.v's
    [set_program_name_fn]) linked with glibc, for HelloGlibcProgName.v's
    triple over the [os_world] of [OsWorld](../zsys/OsWorld.v): from L8,
    once the base name is found, [spn_L8] compares the seven bytes
    before it with "/.libs/" by Hello's `memeq` over a [memcmp_spec]
    (HelloGlibcProgCells.v's [memeq_call]) and goes on to the "lt-"
    test ([spn_L16]) or to the stores ([spn_L18]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloName.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop OsWorld StrrchrLogic StrncmpCode StrcmpBits
  StrncmpBits HelloGlibcProgCells.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** The test over the [[runtime]] R and the Logic instance LG0. *)
Module HelloGlibcProgLibsOn (R : Runtime) (LG0 : LogicSig R).
(** The cells, the bytes and the memeq call. *)
Module PC := HelloGlibcProgCellsOn R LG0.
(** The world's rules. *)
Module OW := PC.OW.
(** The Logic instance. *)
Module LG := LG0.
(** Its language. *)
Module L := LG.L.
Import L LG.

Section progname.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** Hello's callees: its own memeq, and glibc's strncmp. *)
Context (Hmemeq : find_fn ge (TAtom "memeq") = Some (Defined memeq_fn))
  (Hstrncmp : find_fn ge (TAtom "strncmp") = Some (Defined glibc_strncmp)).
(** The globals: the three cells, each its own 8-aligned object, and
    the literals "/.libs/" and "lt-". *)
Context (pb nb sb : Z) (preg nreg sreg : region) (lp tp : ptr)
  (Hpb : lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr pb (Obj pb)))
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hlp : lookup (TAtom "progname#str.3") (ge_globals ge) = Some lp)
  (Htp : lookup (TAtom "progname#str.4") (ge_globals ge) = Some tp)
  (Hpb_cell : 0 <= pb /\ pb mod 8 = 0 /\ pb + 8 <= r_end preg /\ r_end preg <= 2 ^ 48)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48).

(** [os_wi] w0 survives safepoints. *)
Local Instance pn_stable : SafepointStable (os_wi w0) := OW.os_wi_stable w0.
(** The Iris instance of the registry and [os_wi] w0. *)
Local Instance pn_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry (os_wi w0) ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** HelloGlibcProgCells.v's [memcmp_spec] for this genv. *)
Local Notation memcmp_spec := (PC.memcmp_spec w0 registry ge).
(** The three cells, holding x, y and z. *)
Local Notation name_cells := (PC.name_cells pb nb sb preg nreg sreg).
(** The stores into them. *)
Local Notation spn_L18 := (PC.spn_L18 w0 registry ge pb nb sb preg nreg sreg Hpb Hnb Hsb Hpb_cell Hnb_cell Hsb_cell).
(** Hello's memeq over a [memcmp_spec]. *)
Local Notation memeq_call := (PC.memeq_call w0 registry ge).
(** A string's bytes, as memcmp owns them. *)
Local Notation word_string_bytes := PC.word_string_bytes.
(** The "lt-" test and the stores after it. *)
Local Notation spn_L16 := (PC.spn_L16 w0 registry ge Hstrncmp pb nb sb preg nreg sreg tp Hpb Hnb Hsb Htp
  Hpb_cell Hnb_cell Hsb_cell).

(** From L8, with `v15` reading as the base name, argv[0]'s tail from
    its byte [base_idx], and `v0` as argv[0]: if seven bytes precede the
    base name, Hello's memeq compares them with "/.libs/", and the
    stores follow, after the "lt-" test in a libtool build directory. *)
Lemma spn_L8 (Hcmp : memcmp_spec) dq p s e x0 y0 z0 Φ :
  (dq = DfracDiscarded \/ exists q, dq = DfracOwn q) ->
  lookup (TAtom "v15") e = Some (WPtr (ptr_add p (Z.of_nat (base_idx s)))) -> lookup (TAtom "v0") e = Some (WPtr p) ->
  word_string dq p s -∗ word_string DfracDiscarded lp libs_bytes -∗ word_string DfracDiscarded tp lt_bytes -∗
  name_cells x0 y0 z0 -∗
  ▷ (word_string dq p s -∗ name_cells (ptr_add p (Z.of_nat (name_idx s))) (ptr_add p (Z.of_nat (name_idx s)))
       (ptr_add p (Z.of_nat (short_idx s))) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame set_program_name_fn e [] None (Exec (TAtom "L8") (b_insts s_L8) (b_jump s_L8))) : gexpr)
     {{ Φ }}.
Proof.
  intros Hdq Hv15 Hv0. iIntros "Hs #Hlibs #Hlt Hc HΦ". cbn [b_insts b_jump s_L8].
  iDestruct "Hs" as "(%b & %reg & %ws & %Hs & Hw)". iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hs|].
  pose proof (base_idx_le s) as Hj. destruct (str_shape_addr _ _ _ _ _ Hs) as [Ha0 Ha48].
  pose proof (ss_chars _ _ _ _ _ Hs) as Hch.
  do 4 (iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]; iNext; gen_env).
  destruct (Nat.lt_ge_cases (base_idx s) 7) as [Hj7 | Hj7].
  - (* Fewer than seven bytes precede the base name. *)
    assert (Hl : in_libs s = false).
    { unfold in_libs. replace (7 <=? base_idx s)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. }
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L26 | reflexivity |]. iNext. cbn [b_insts b_jump s_L26]. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
    iApply (spn_L18 with "Hc"); [reflexivity | reflexivity |]. iNext. iIntros "Hc".
    iApply ("HΦ" with "Hs"). unfold name_idx, short_idx. rewrite Hl. cbn [andb].
    change (Z.of_nat 0) with 0. rewrite ptr_add_0. iExact "Hc".
  - (* Compare the seven bytes before it with "/.libs/". *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L25 | reflexivity |]. iNext. cbn [b_insts b_jump s_L25].
    iDestruct (word_string_bytes dq p s (base_idx s - 7) 7 with "Hs")
      as (b1 reg1 (Hc1 & Hb1 & Hst1 & Hend1 & Hr1)) "(Hl1 & Hx1 & Hback1)"; [lia|].
    iDestruct (word_string_bytes DfracDiscarded lp libs_bytes 0 7 with "Hlibs")
      as (b2 reg2 (Hc2 & Hb2 & Hst2 & Hend2 & Hr2)) "(Hl2 & Hx2 & _)"; [cbn; lia|].
    change (take 7 (drop 0 libs_bytes)) with libs_bytes.
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b1 + (ptr_addr p - b1 + Z.of_nat (base_idx s - 7))));
      [word_premise | cbn; do 2 f_equal; rewrite !Z.mod_small; lia | word_premise |].
    iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ memeq_fn
              (invocation memeq_fn [WPtr (mkPtr (b1 + (ptr_addr p - b1 + Z.of_nat (base_idx s - 7))) (ptr_cap p));
                                    WPtr lp; WInt 7])); [word_premise | exact Hmemeq | reflexivity |].
    iNext.
    iApply (memeq_call Hcmp dq DfracDiscarded _ _ 7 b1 reg1 _ _ b2 reg2 _ _ with "Hl1 Hx1 Hl2 Hx2");
      [lia | rewrite length_take; lia | reflexivity | cbn; lia | rewrite length_take length_drop; lia | exact Hc1 | exact Hc2
      | rewrite length_take length_drop; unfold libs_bytes; cbn [length]; lia | lia | lia | rewrite length_take length_drop; lia
      | rewrite length_take length_drop; lia | exact Hr1 | exact Hr2
      | apply Forall_take, Forall_drop; eapply Forall_impl; [exact Hch | intros x Hx; cbn in Hx; lia]
      | apply Forall_forall; intros x Hx; apply list_elem_of_In in Hx; cbn in Hx; lia |].
    iNext. iIntros "Hl1 Hx1 _ _". iDestruct ("Hback1" with "Hl1 Hx1") as "Hs".
    iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
    destruct (decide (take 7 (drop (base_idx s - 7) s) = libs_bytes)) as [D|D].
    + assert (Hl : in_libs s = true).
      { unfold in_libs. replace (7 <=? base_idx s)%nat with true by (symmetry; apply Nat.leb_le; lia).
        rewrite (bool_decide_eq_true_2 _ D). reflexivity. }
      do 2 (iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]; iNext; gen_env).
      iApply wp_goto. iNext. iApply wp_enter; [exact find_s_L26 | word_premise |]. iNext. cbn [b_insts b_jump s_L26].
      gen_env. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      iApply wp_enter; [exact find_s_L16 | reflexivity |]. iNext.
      iApply (spn_L16 with "Hs Hlt Hc"); [exact Hdq | exact Hl | eassumption |].
      iNext. iIntros "Hs Hc". iApply ("HΦ" with "Hs"). unfold name_idx. rewrite Hl. iExact "Hc".
    + assert (Hl : in_libs s = false).
      { unfold in_libs. rewrite (bool_decide_eq_false_2 _ D). apply andb_false_r. }
      do 2 (iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]; iNext; gen_env).
      iApply wp_goto. iNext. iApply wp_enter; [exact find_s_L26 | word_premise |]. iNext. cbn [b_insts b_jump s_L26].
      gen_env. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
      iApply (spn_L18 with "Hc"); [reflexivity | reflexivity |]. iNext. iIntros "Hc".
    iApply ("HΦ" with "Hs"). unfold name_idx, short_idx. rewrite Hl. cbn [andb].
    change (Z.of_nat 0) with 0. rewrite ptr_add_0. iExact "Hc".
Qed.

End progname.
End HelloGlibcProgLibsOn.
