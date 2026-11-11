(** `c: _IO_flush_all ()` (LibioFlushCode.v, libio/genops.c), which
    `c: _IO_cleanup` calls at exit to write out what every open
    stream still buffers.

    The function pushes a cleanup buffer and takes `c: list_all_lock`
    (LibioFlushStart.v). It then walks the streams of
    [io_list_inv]'s list along their `c: _chain` links, one pass per
    stream ([flush_loop], by induction on the list), and releases the
    lock and pops the buffer again (LibioFlushTail.v). Each pass is a
    [flush_body] from P to Q of its stream: [flush_body_exit] for a
    stream with nothing to flush, LibioFlushOver.v's for one whose
    output `c: _IO_new_file_overflow` writes. The result is 0, or EOF
    (-1) if a flush failed ([wp_glibc__IO_flush_all]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean
  LibioFlushStart LibioFlushTail LibioFlushBody.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioFlushOn (R : Runtime) (LG0 : LogicSig R).
Module FB := LibioFlushBodyOn R LG0.
Import FB FB.FT FB.FT.FS FB.FT.FS.FC FB.FT.FS.FC.FU FB.FT.FS.FC.FU.FL FB.FT.FS.FC.FU.FL.CS
  FB.FT.FS.FC.FU.FL.CS.SW FB.FT.FS.FC.FU.FL.CS.SW.FI.ML FB.FT.FS.FC.FU.FL.CS.SW.FI.LG
  FB.FT.FS.FC.FU.FL.CS.SW.FI.L FB.FT.FS.FC.FU.FL.CS.SW.OW FB.FT.FS.FC.FU.FL.CS.SW.FI FB.FT.FS.FC.FU.FL.CS.SW.ST.

Section lives.
Context `{!gen_heapGS piece pval Σ}.

(** The life of the first of the streams fs, each with its
    [stream_life] and P, lent out: what a load of the list's head
    needs; nothing for an empty list, whose head is null. *)
Lemma head_life (P : ptr -> iProp Σ) fs :
  ([∗ list] g ∈ fs, stream_life g ∗ P g) ⊢
  ∃ hreg, ⌜0 <= ptr_addr (head_ptr fs) < 2 ^ 64⌝ ∗ live_cap (ptr_cap (head_ptr fs)) hreg ∗
    (live_cap (ptr_cap (head_ptr fs)) hreg -∗ [∗ list] g ∈ fs, stream_life g ∗ P g).
Proof.
  destruct fs as [|g fs]; cbn [head_ptr].
  - iIntros "H". iExists (mkRegion 0 0 Heap Live). iSplit; [iPureIntro; cbn; lia|]. iSplit; [done|].
    iIntros "_". iExact "H".
  - iIntros "[[(%gb & %greg & %Hg & Hl) HP] Hfs]".
    destruct Hg as (-> & Hgb & Hgal & Hgend & Hgreg). unfold file_size in Hgend.
    iExists greg. cbn [ptr_addr ptr_cap live_cap]. iFrame "Hl". iSplit; [iPureIntro; lia|].
    iIntros "Hl". rewrite big_sepL_cons. iFrame "HP Hfs". iExists gb, greg. iFrame "Hl". iPureIntro.
    unfold file_size. split_and!; auto; lia.
Qed.

End lives.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hpush : find_fn ge (TAtom "__GI___libc_cleanup_push_defer") =
                 Some (Defined glibc___libc_cleanup_push_defer)).
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).
Context (Hpush_spec : push_spec w0 registry ge) (Hpop_spec : pop_spec w0 registry ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance flush_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The loop of `c: _IO_flush_all` from its head `c: L82`, over the
    streams rest still to pass, linked from prev, each with its life
    and P: the head is entered from `c: L15` with rest's first stream
    in `c: v81` and the result 0, or from `c: L329` with it in
    `c: v413` and the result r in `c: pr.1`. Each pass is the
    [flush_body] P Q, and block `c: L414` is entered with each
    stream's Q and the result r or EOF. *)
Lemma flush_loop (P Q : ptr -> iProp Σ) rest prev e from r cb rf rfreg sb sreg Φ :
  flush_body w0 registry ge P Q ->
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  rf mod 8 = 0 -> rf + 8 <= r_end rfreg -> ptr_addr (ow_self w0) <> 0 ->
  (from = TAtom "L15" /\ lookup (TAtom "v81") e = Some (WPtr (head_ptr rest)) /\ r = 0) \/
  (from = TAtom "L329" /\ lookup (TAtom "v413") e = Some (WPtr (head_ptr rest)) /\
   lookup (TAtom "pr.1") e = Some (WInt r)) ->
  lookup (TAtom "v3") e = Some (WPtr cb) -> 0 <= r < 2 ^ 32 ->
  single_ro ge sb sreg -∗ live rf rfreg -∗ pcell rf 0 null -∗ chain_links prev rest -∗
  ([∗ list] g ∈ rest, stream_life g ∗ P g) -∗
  (∀ e' r', ⌜lookup (TAtom "v3") e' = Some (WPtr cb) /\ lookup (TAtom "pr.4") e' = Some (WInt r') /\
             0 <= r' < 2 ^ 32 /\ (r' = r \/ r' = 2 ^ 32 - 1)⌝ -∗
     live rf rfreg -∗ pcell rf 0 null -∗ chain_links prev rest -∗ ([∗ list] g ∈ rest, stream_life g ∗ Q g) -∗
     WP (ERun (mkFrame glibc__IO_flush_all e' [] None (Enter (TAtom "L414") (Some (TAtom "L82")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L82") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hbody Hgrf Hral Hrend Hsz. revert prev e from r.
  induction rest as [|g rest IH]; intros prev e from r Hph Hv3 Hr; cbn [head_ptr] in Hph.
  - iIntros "#Hs Hrl Hrc Hch Hfs HK".
    destruct Hph as [(-> & Hv81 & ->) | (-> & Hv413 & Hp1)].
    + fs. fs. fs. fs. fbr. iApply ("HK" $! _ 0 with "[%] Hrl Hrc Hch Hfs"). split_and!; try lk_prove; lia.
    + fs. fs. fs. fs. fbr. rewrite (Z.mod_small r (2 ^ 32)); [|exact Hr].
      iApply ("HK" $! _ r with "[%] Hrl Hrc Hch Hfs"). split_and!; try lk_prove; lia.
  - iIntros "#Hs Hrl Hrc Hch Hfs HK". cbn [chain_links].
    iDestruct "Hch" as (gb ->) "(Hpv & Hnc & Hch)".
    iDestruct "Hfs" as "[[(%gb' & %greg & %Hg & Hl) HP] Hfs]".
    destruct Hg as (Heq & Hgb & Hgal & Hgend & Hgreg). injection Heq as <-. unfold file_size in Hgend.
    iDestruct (head_life with "Hfs") as (nreg Hnx) "[Hnl Hback]".
    assert (Hr' : (r mod 2 ^ 32) = r) by (apply Z.mod_small; exact Hr).
    destruct Hph as [(-> & Hv81 & Hr0) | (-> & Hv413 & Hp1)].
    all: fs; fs; fs; fs; fbrv false; try rewrite Hr'.
    all: iApply (Hbody _ gb greg rf rfreg sb sreg null r cb (head_ptr rest) nreg with "Hs Hl HP Hrl Hrc Hnc Hnl");
      try lazymatch goal with
      | |- environments.envs_entails _ _ => idtac
      | |- lookup _ _ = _ => first [lk_prove | rewrite Hr0; lk_prove]
      | |- _ => first [exact Hsz | exact Hnx | exact Hral | exact Hrend | lia | unfold file_size; lia]
      end.
    all: iNext; iIntros (e' r' (Hv413' & Hp1' & Hv3' & Hr'' & Hrr')) "Hl HQ Hrl Hrc Hnc Hnl".
    all: iDestruct ("Hback" with "Hnl") as "Hfs".
    all: iApply (IH (mkPtr (gb + off_chain) (Obj gb)) e' (TAtom "L329") r' with "Hs Hrl Hrc Hch Hfs");
      [right; split_and!; auto | exact Hv3' | exact Hr'' |].
    all: iIntros (e'' r''' (Hv3'' & Hp4'' & Hr3 & Hrr'')) "Hrl Hrc Hch Hfs".
    all: iApply ("HK" $! e'' r''' with "[%] Hrl Hrc [Hpv Hnc Hch] [Hl HQ Hfs]");
      [ split_and!; auto; lia
      | iExists gb; iFrame; done
      | rewrite big_sepL_cons; iFrame "HQ Hfs"; iExists gb, greg; iFrame "Hl"; iPureIntro; unfold file_size;
        split_and!; auto; lia ].
Qed.

(** `c: _IO_flush_all ()` over [io_list_inv]'s streams fs, each with
    its life and P, each pass the [flush_body] P Q, the thread's
    cleanup fields as [tcb_cleanup_inv] says and
    `c: __libc_single_threaded` set: the function returns 0 or EOF,
    with the list as it was, each stream's Q, and the cleanup fields
    restored. The cleanup routine's pointer, `c: flush_cleanup`, is
    ge's symbol. *)
Lemma wp_glibc__IO_flush_all fr (P Q : ptr -> iProp Σ) fs sb sreg fcp Φ :
  flush_body w0 registry ge P Q -> call_frame glibc__IO_flush_all [] = Some fr ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
  ([∗ list] g ∈ fs, stream_life g ∗ P g) -∗
  ▷ (∀ r, ⌜r = 0 \/ r = 2 ^ 32 - 1⌝ -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
     ([∗ list] g ∈ fs, stream_life g ∗ Q g) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hbody Hfr Hfc Hfcr.
  iIntros "#Hs Htcb Hio Hfs HK".
  iDestruct "Hio" as (la lareg lk lkreg rf rfreg Hio) "(Hla & Hlah & Hch & Hlk & Hrl & Hrc)".
  destruct Hio as (Hgla & Hglk & Hgrf & Hlaal & Hlaend & Hral & Hrend).
  iDestruct "Htcb" as (tb treg jb Ht) "Htcb". pose proof Ht as (Hself & Htb & _).
  iAssert (tcb_cleanup_inv (ow_self w0)) with "[Htcb]" as "Htcb".
  { iExists tb, treg, jb. iSplit; [iPureIntro; exact Ht | iExact "Htcb"]. }
  assert (Hsz : ptr_addr (ow_self w0) <> 0) by (rewrite Hself; cbn; lia).
  iDestruct (head_life with "Hfs") as (hreg Hh) "[Hhl Hback]".
  iApply (wp_flush_start w0 registry ge Hreg Hext Hpush Hpush_spec with "Hs Htcb Hla Hlah Hhl Hlk");
    try first [exact Hfr | side].
  iNext. iIntros (e cb creg (Hv81 & Hv3 & Hcb & Hcal & Hcend & Hcreg)) "Htcb Hcl Hc24 Hc16 Hla Hlah Hhl Hlk".
  iDestruct ("Hback" with "Hhl") as "Hfs".
  iApply (flush_loop P Q fs (mkPtr la (Obj la)) e (TAtom "L15") 0 with "Hs Hrl Hrc Hch Hfs");
    [exact Hbody | exact Hgrf | exact Hral | exact Hrend | exact Hsz | left; auto | exact Hv3 | lia |].
  iIntros (e' r' (Hv3' & Hp4' & Hr' & Hrr)) "Hrl Hrc Hch Hfs".
  iApply (wp_flush_L414 w0 registry ge Hpop Hpop_spec with "Hs Hlk Htcb Hcl Hc24 Hc16"); try side.
  iNext. iIntros "Hlk Htcb Hcl".
  iApply ("HK" $! r' with "[%] Htcb [Hla Hlah Hch Hlk Hrl Hrc] Hfs"); [lia|].
  iExists la, lareg, lk, lkreg, rf, rfreg. iFrame. iPureIntro. split_and!; assumption.
Qed.

End rules.
End LibioFlushOn.
