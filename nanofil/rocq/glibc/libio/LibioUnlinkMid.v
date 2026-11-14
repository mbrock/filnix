(** The middle of `c: _IO_un_link` (LibioUnlinkCode.v): the stream
    leaves the list. [chain_split] finds, in [io_list_inv]'s
    [chain_links], the link before a stream, `c: _IO_list_all` or the
    `c: _chain` of the stream before it, and puts the list back
    together without the stream; [wp_unlink_L185] runs block
    `c: L185`, `c: *fp->_prevchain = fp->_chain`, and `c: L199`,
    `c: fp->_chain->_prevchain = fp->_prevchain` when there is a next
    stream ([next_link]), then [wp_unlink_L179] to the return. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioUnlinkCode FileInv LibioLogic
  SysWrappers SysCleanup LibioCloseSteps LibioUnlinkTail.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioUnlinkTail OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioUnlinkTail SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section list.
Context `{!gen_heapGS piece pval Σ}.

(** [next_link] nx p: the stream after an unlinked one, nx, is null,
    or a stream whose life is owned and whose `c: _prevchain` is p. *)
Definition next_link (nx p : ptr) : iProp Σ :=
  ⌜nx = null⌝ ∨ ∃ nb nreg, ⌜nx = mkPtr nb (Obj nb) /\ 0 < nb /\ nb mod 8 = 0 /\ nb + file_size <= r_end nreg /\
                            r_end nreg <= 2 ^ 63⌝ ∗ live nb nreg ∗ pcell nb off_prevchain p.

(** The links of pre ++ f :: post from the cell at offset po of pb:
    the link before f, at offset qo of qb, which is that cell when pre
    is empty and else the `c: _chain` of pre's last stream; f's links;
    and, for the link before f holding post's head and post linked
    from it, the links of pre ++ post. *)
Lemma chain_split pre f post pb po :
  chain_links (mkPtr (pb + po) (Obj pb)) (pre ++ f :: post) -∗ pcell pb po (head_ptr (pre ++ f :: post)) -∗
  ∃ qb qo, ⌜(pre = [] /\ qb = pb /\ qo = po) \/ (exists pre' : list ptr, pre = (pre' ++ [mkPtr qb (Obj qb)])%list /\ qo = off_chain)⌝ ∗
    pcell qb qo f ∗ chain_links (mkPtr (qb + qo) (Obj qb)) (f :: post) ∗
    (pcell qb qo (head_ptr post) -∗ chain_links (mkPtr (qb + qo) (Obj qb)) post -∗
     chain_links (mkPtr (pb + po) (Obj pb)) (pre ++ post) ∗ pcell pb po (head_ptr (pre ++ post))).
Proof.
  revert pb po. induction pre as [|g pre IH]; intros pb po; cbn [app].
  - iIntros "Hc Hp". iExists pb, po. iFrame "Hc Hp". iSplit; [iPureIntro; left; auto|]. iIntros "$ $".
  - cbn [chain_links head_ptr]. iIntros "(%gb & -> & Hgp & Hgc & Hc) Hp".
    iDestruct (IH gb off_chain with "Hc Hgc") as (qb qo Hq) "(Hq & Hf & HW)".
    iExists qb, qo. iFrame "Hq Hf". iSplit.
    { iPureIntro. right. destruct Hq as [(-> & -> & ->) | (pre' & -> & ->)].
      - exists []. split; reflexivity.
      - exists (mkPtr gb (Obj gb) :: pre'). split; reflexivity. }
    iIntros "Hq Hc". iDestruct ("HW" with "Hq Hc") as "[Hc Hgc]". iFrame "Hp". iExists gb. iFrame. done.
Qed.

(** [stream_life] g: the life of the stream g, a 224-byte object, as
    [file_inv] has it: what a load of a pointer to g and a store
    into g's links need. *)
Definition stream_life (g : ptr) : iProp Σ :=
  ∃ gb greg, ⌜g = mkPtr gb (Obj gb) /\ 0 < gb /\ gb mod 8 = 0 /\ gb + file_size <= r_end greg /\
              r_end greg <= 2 ^ 63⌝ ∗ live gb greg.

(** The streams of [io_list_inv] with fb among them, as
    `c: _IO_un_link` sees them: the link before fb, at offset qo of
    qb, with qb's life; fb's links; the next stream ([next_link]); and,
    once the link before fb holds the next stream and the next stream
    links back to it, the list without fb. *)
Lemma unlink_split la lareg pre fb post :
  la mod 8 = 0 -> la + 8 <= r_end lareg ->
  live la lareg -∗ pcell la 0 (head_ptr (pre ++ mkPtr fb (Obj fb) :: post)) -∗
  chain_links (mkPtr la (Obj la)) (pre ++ mkPtr fb (Obj fb) :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ∃ qb qo qreg, ⌜0 <= qo /\ (qb + qo) mod 8 = 0 /\ qb + qo + 8 <= r_end qreg⌝ ∗
    live qb qreg ∗ pcell qb qo (mkPtr fb (Obj fb)) ∗ pcell fb off_prevchain (mkPtr (qb + qo) (Obj qb)) ∗
    pcell fb off_chain (head_ptr post) ∗ next_link (head_ptr post) (mkPtr (fb + off_chain) (Obj fb)) ∗
    (live qb qreg -∗ pcell qb qo (head_ptr post) -∗ next_link (head_ptr post) (mkPtr (qb + qo) (Obj qb)) -∗
     live la lareg ∗ pcell la 0 (head_ptr (pre ++ post)) ∗ chain_links (mkPtr la (Obj la)) (pre ++ post) ∗
     [∗ list] g ∈ pre ++ post, stream_life g).
Proof.
  intros Hal Hend.
  assert (E : mkPtr la (Obj la) = mkPtr (la + 0) (Obj la)) by (rewrite Z.add_0_r; reflexivity). rewrite E.
  iIntros "Hla Hh Hc Hs". iDestruct (big_sepL_app with "Hs") as "[Hpre Hpst]".
  iDestruct (chain_split with "Hc Hh") as (qb qo Hq) "(Hqc & Hf & HW)".
  cbn [chain_links]. iDestruct "Hf" as (fb') "(%Hfb & Hfp & Hfc & Hpost)". injection Hfb as <-.
  iAssert (∃ qreg, ⌜0 <= qo /\ (qb + qo) mod 8 = 0 /\ qb + qo + 8 <= r_end qreg⌝ ∗ live qb qreg ∗
             (live qb qreg -∗ live la lareg ∗ [∗ list] g ∈ pre, stream_life g))%I
    with "[Hla Hpre]" as (qreg Hqb) "[Hql Hback]".
  { destruct Hq as [(-> & -> & ->) | (pre' & -> & ->)].
    - iExists lareg. iFrame "Hla". iSplit; [iPureIntro; rewrite Z.add_0_r; lia|]. iIntros "$". done.
    - iDestruct (big_sepL_app with "Hpre") as "[Hpre [(%gb & %greg & %Hg & Hgl) _]]".
      destruct Hg as (Hg & Hgb & Hgal & Hgend & Hgreg). injection Hg as <-.
      iExists greg. iFrame "Hgl". unfold off_chain, file_size in *.
      iSplit; [iPureIntro; split_and!; [lia | rewrite Z.add_mod; [rewrite Hgal; reflexivity | lia] | lia]|].
      iIntros "Hgl". iFrame "Hla". iApply big_sepL_app. iFrame "Hpre". cbn [big_opL].
      iSplitL; [|done]. iExists qb, greg. iFrame. iPureIntro. unfold file_size. split_and!; done || lia. }
  iExists qb, qo, qreg. iFrame "Hql Hqc Hfp Hfc". iSplit; [iPureIntro; exact Hqb|].
  destruct post as [|n post].
  - cbn [head_ptr chain_links]. iSplitR; [iLeft; done|].
    iIntros "Hql Hqc _". iDestruct ("Hback" with "Hql") as "[$ Hpre]".
    iDestruct ("HW" with "Hqc [//]") as "[$ $]". iApply big_sepL_app. iFrame "Hpre". done.
  - cbn [head_ptr chain_links big_opL]. iDestruct "Hpost" as (nb) "(%Hn & Hnp & Hnc & Hpost)". subst n.
    iDestruct "Hpst" as "[(%nb' & %nreg & %Hn & Hnl) Hpst]". destruct Hn as (Hn & Hnb & Hnal & Hnend & Hnreg).
    injection Hn as <-.
    iSplitL "Hnl Hnp". { iRight. iExists nb, nreg. iFrame. iPureIntro. split_and!; done. }
    iIntros "Hql Hqc [%Hnull | (%nb' & %nreg' & %Hn' & Hnl & Hnp)]"; [discriminate|].
    destruct Hn' as (Hn' & Hnr). injection Hn' as <-.
    iDestruct ("Hback" with "Hql") as "[$ Hpre]".
    iDestruct ("HW" with "Hqc [Hnp Hnc Hpost]") as "[$ $]". { cbn [chain_links]. iExists nb. iFrame. done. }
    iApply big_sepL_app. iFrame "Hpre". cbn [big_opL]. iFrame "Hpst". iExists nb, nreg'. iFrame.
    iPureIntro. split_and!; tauto.
Qed.

End list.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance unlink_mid_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L185` of `c: _IO_un_link` to its return: the link
    before the stream, at offset qo of qb, takes the stream's
    `c: _chain` nx, and the next stream, if any, takes the stream's
    `c: _prevchain`; then [wp_unlink_L179]. *)
Lemma wp_unlink_L185 e from fb freg fl lb lbreg qb qo qreg nx cb creg lk lkreg rf rfreg sb sreg x Φ :
  let qp := mkPtr (qb + qo) (Obj qb) in
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "v0") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) -> lookup (TAtom "v183") e = Some (WInt 0) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 ->
  0 <= qo -> (qb + qo) mod 8 = 0 -> qb + qo + 8 <= r_end qreg ->
  0 < cb -> cb mod 8 = 0 -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 ->
  rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 1 0 (ow_self w0) -∗
  pcell fb off_prevchain qp -∗ pcell fb off_chain nx -∗ live qb qreg -∗ pcell qb qo fp -∗
  next_link nx (mkPtr (fb + off_chain) (Obj fb)) -∗
  live rf rfreg -∗ pcell rf 0 x -∗ lock_state lk lkreg 1 0 (ow_self w0) -∗
  tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (unlinked_flags fl) -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 0 0 null -∗
     pcell fb off_prevchain qp -∗ pcell fb off_chain nx -∗ live qb qreg -∗ pcell qb qo nx -∗ next_link nx qp -∗
     live rf rfreg -∗ pcell rf 0 null -∗ lock_state lk lkreg 0 0 null -∗ tcb_cleanup_inv (ow_self w0) -∗
     live cb creg -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc__IO_un_link e [] None (Enter (TAtom "L185") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros qp fp Hglk Hgrf Hv0 Hc0 Hv10 Hv183 Hfb Hfal Hfend Hfreg Hfl Hul Hqo Hqal Hqend Hcb Hcal Hcend Hcreg
    Hral Hrend.
  iIntros "#Hs Hl Hfl Hlp Hlb Hpc Hch Hql Hqc Hnx Hrl Hrc Hlk Htcb Hcl Hcp Hct HK".
  unfold file_size in Hfend. subst qp fp.
  iApply (wp_live_fit1 w0 registry ge with "Hql"). iIntros ([Hq0 Hq48]) "Hql".
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl". load "Hl" "Hpc" "Hql". step. check "Hl".
  iDestruct "Hnx" as "[-> | (%nb & %nreg & %Hn & Hnl & Hnp)]".
  - load_null "Hl" "Hch". check "Hql". store "Hql" "Hqc". step. step. branch.
    iApply (wp_unlink_L179 with "Hs Hl Hfl Hlp Hlb Hrl Hrc Hlk Htcb Hcl Hcp Hct"); try close_side.
    iNext. iIntros "Hl Hfl Hlp Hlb Hrl Hrc Hlk Htcb Hcl".
    iApply ("HK" with "Hl Hfl Hlp Hlb Hpc Hch Hql Hqc [] Hrl Hrc Hlk Htcb Hcl"). iLeft. done.
  - destruct Hn as (-> & Hnb & Hnal & Hnend & Hnreg). unfold file_size in Hnend.
    iApply (wp_live_fit1 w0 registry ge with "Hnl"). iIntros ([Hn0 Hn48]) "Hnl".
    load "Hl" "Hch" "Hnl". check "Hql". store "Hql" "Hqc". step. step. branch_as false.
    step. step. check "Hnl". store "Hnl" "Hnp". step.
    iApply (wp_unlink_L179 with "Hs Hl Hfl Hlp Hlb Hrl Hrc Hlk Htcb Hcl Hcp Hct"); try close_side.
    iNext. iIntros "Hl Hfl Hlp Hlb Hrl Hrc Hlk Htcb Hcl".
    iApply ("HK" with "Hl Hfl Hlp Hlb Hpc Hch Hql Hqc [Hnl Hnp] Hrl Hrc Hlk Htcb Hcl"). iRight.
    iExists nb, nreg. iFrame. iPureIntro. unfold file_size. split_and!; done || lia.
Qed.

End rules.
