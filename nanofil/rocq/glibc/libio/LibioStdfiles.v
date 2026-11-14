From Glibc Require Import GlibcProgram.
(** The triple of `c: _IO_stdfiles_init` (LibioStdfilesCode.v,
    libio/stdfiles.c), the constructor that links glibc's three
    standard streams both ways before `c: main` runs
    ([wp_glibc_stdfiles_init]).

    stdfiles.c builds `c: _IO_2_1_stderr_`, `c: _IO_2_1_stdout_` and
    `c: _IO_2_1_stdin_` statically, each `c: _chain` naming the next
    and the last null, with `c: _IO_list_all` naming stderr. Only the
    back links `c: _prevchain` are left null, since a static
    initializer cannot name a field's address in a way the linker
    keeps. The constructor walks the chain with a pointer f to a link,
    from `c: &_IO_list_all` through each stream's `c: &fp->_chain`
    until the link is null, and sets the `c: _prevchain` of the stream
    each link names to f, the address of that link.

    The loop is proved for any list of streams by Löb induction over
    the head of its block `c: L2` ([wp_stdfiles_loop]). Before it, each
    stream's life is owned and its `c: _chain` names the next one
    ([chain_pre]); after it, the streams are linked both ways as
    FileInv.v's [chain_links] says, and each stream's life is given
    back ([stream_live]). For the three standard streams that is
    FileInv.v's [io_list_inv], which the proofs of `c: puts`,
    `c: fclose` and `c: exit` start from. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  LibioStdfilesCode.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The constructor, by a shorter name. *)
Definition glibc_stdfiles_init : func := glibc_glibc_stdfiles__IO_stdfiles_init.

(** Block `c: L2` of the constructor, the loop's head. *)
Definition sf_L2 : block := Eval vm_compute in
  match find_block (TAtom "L2") (fn_blocks glibc_stdfiles_init) with
  | Some b => b | None => mkBlock (TAtom "L2") [] [] JRetVoid end.


Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}.
Existing Instance gen_heapGS0.
Definition stream_live (f : ptr) : iProp Σ :=
  ∃ fb freg, ⌜f = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\
              r_end freg <= 2 ^ 63⌝ ∗ live fb freg.
Fixpoint chain_pre (fs : list ptr) : iProp Σ :=
  match fs with
  | [] => True
  | f :: fs' => stream_live f ∗ (∃ fb x, ⌜f = mkPtr fb (Obj fb)⌝ ∗ pcell fb off_prevchain x ∗
      pcell fb off_chain (head_ptr fs')) ∗ chain_pre fs'
  end.
Definition stdfile_pre (f next : ptr) : iProp Σ :=
  ∃ fb freg, ⌜f = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\
              r_end freg <= 2 ^ 63⌝ ∗
    live fb freg ∗ pcell fb off_prevchain null ∗ pcell fb off_chain next.
Lemma stdfile_chain_pre f fs : stdfile_pre f (head_ptr fs) -∗ chain_pre fs -∗ chain_pre (f :: fs).
Proof.
  iIntros "(%fb & %freg & %Hf & Hl & Hpc & Hch) Hpre". cbn [chain_pre]. iFrame "Hpre".
  pose proof Hf as (-> & _). iSplitL "Hl"; [iExists fb, freg; iFrame "Hl"; done|].
  iExists fb, null. iFrame. done.
Qed.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [stream_live] f: f is the stream fb's own pointer, a 224-byte
    8-aligned object whose life is owned. *)

(** [chain_pre] fs: each stream of fs, in order, is a [stream_live]
    whose `c: _chain` names the next stream, the last null, and whose
    `c: _prevchain` holds anything: the list before the constructor
    links it back. *)

(** The constructor's loop at its head `c: L2`, `c: pr.1` the address
    of the link at offset o of the live object b that names the first
    of the streams fs: every stream's `c: _prevchain` becomes the
    address of the link before it ([chain_links]), and the function
    returns. *)
Lemma wp_stdfiles_loop Φ :
  ⊢ ∀ fs e b breg o, ⌜lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b + o) (Obj b))) /\ 0 <= o /\
        (b + o) mod 8 = 0 /\ b + o + 8 <= r_end breg /\ r_end breg <= 2 ^ 63⌝ -∗
    live b breg -∗ pcell b o (head_ptr fs) -∗ chain_pre fs -∗
    ▷ (live b breg -∗ pcell b o (head_ptr fs) -∗ chain_links (mkPtr (b + o) (Obj b)) fs -∗
       ([∗ list] f ∈ fs, stream_live f) -∗ Φ RetVoid) -∗
    WP (ERun (mkFrame glibc_stdfiles_init e [] None (Exec (TAtom "L2") (b_insts sf_L2) (b_jump sf_L2)))
          : sexpr) {{ Φ }}.
Proof.
  iLöb as "IH". iIntros (fs e b breg o (Hp & Ho & Hal & Hend & Hreg)) "Hl Hc Hpre HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hb Hb48]) "Hl".
  cbn [sf_L2 b_insts b_jump].
  destruct fs as [|f fs].
  - (* The link is null: the loop ends. *)
    cbn [head_ptr]. check "Hl". load_null "Hl" "Hc". step. step. step. branch.
    step. iApply wp_ret_void. iNext. iApply ("HK" with "Hl Hc [//] [//]").
  - cbn [chain_pre head_ptr]. iDestruct "Hpre" as "(Hsl & (%fb' & %x & %Hf' & Hpc & Hch) & Hpre)".
    iDestruct "Hsl" as (fb freg (Hf & Hfb & Hfal & Hfend & Hfreg)) "Hlf". rewrite Hf in Hf'.
    injection Hf' as <-. subst f. unfold file_size in Hfend.
    (* The link names the stream fb: its _prevchain becomes the link's address. *)
    check "Hl". load "Hl" "Hc" "Hlf". step. step. step. branch_as false.
    step. load "Hl" "Hc" "Hlf". step. check "Hlf". store "Hlf" "Hpc".
    check "Hl". load "Hl" "Hc" "Hlf". step. step. iApply wp_enter; [reflexivity | vx | iNext].
    iApply ("IH" $! fs _ fb freg off_chain with "[%] Hlf Hch Hpre").
    { split_and!; [rewrite Symbolic.lookup_after_put_same; do 3 f_equal; unfold off_chain; cbn [ptr_addr ptr_cap];
                   unwrap2; lia | unfold off_chain; lia | unfold off_chain; Z.div_mod_to_equations; lia
                  | unfold off_chain; lia | lia]. }
    iNext. iIntros "Hlf Hch Hlinks Hlives".
    iApply ("HK" with "Hl Hc [Hpc Hch Hlinks] [Hlf Hlives]").
    + cbn [chain_links]. iExists fb. iSplit; [done|]. iFrame.
    + cbn [big_opL]. iFrame "Hlives". iExists fb, freg. iFrame "Hlf". iPureIntro.
      unfold file_size. repeat split; lia.
Qed.

(** [stdfile_pre] f next: the standard stream f as stdfiles.c builds
    it, its life owned, its `c: _chain` the stream next and its
    `c: _prevchain` null. *)

(** A [stdfile_pre] is the head of a [chain_pre]. *)

(** `c: _IO_stdfiles_init()`, with `c: _IO_list_all` naming stderr fe
    and the static chain fe, stdout fo, stdin fi, null, every
    `c: _prevchain` null: the list of open streams is fe, fo, fi,
    linked both ways ([io_list_inv]), and each stream's life comes
    back. `c: list_all_lock` and `c: run_fp`, which the constructor
    does not touch, are as FileInv.v's [io_list_inv] has them. *)
Lemma wp_glibc_stdfiles_init fr fe fo fi la lareg lk lkreg rf rfreg Φ :
  call_frame glibc_stdfiles_init [] = Some fr ->
  lookup (TAtom "__GI__IO_list_all") (ge_globals ge) = Some (mkPtr la (Obj la)) ->
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  la mod 8 = 0 -> la + 8 <= r_end lareg -> rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  live la lareg -∗ pcell la 0 fe -∗
  stdfile_pre fe fo -∗ stdfile_pre fo fi -∗ stdfile_pre fi null -∗
  lock_state lk lkreg 0 0 null -∗ live rf rfreg -∗ pcell rf 0 null -∗
  ▷ (io_list_inv ge [fe; fo; fi] -∗ ([∗ list] f ∈ [fe; fo; fi], stream_live f) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hgla Hglk Hgrf Hlal Hlaend Hrfal Hrfend. injection Hfr as <-.
  iIntros "Hla Hc He Ho Hi Hlk Hrf Hrfc HK".
  iDestruct (stdfile_chain_pre fi [] with "Hi [//]") as "Hpre".
  iDestruct (stdfile_chain_pre fo [fi] with "Ho Hpre") as "Hpre".
  iDestruct (stdfile_chain_pre fe [fo; fi] with "He Hpre") as "Hpre".
  iApply (wp_live_fit1 with "Hla"). iIntros ([Hla0 Hla48]) "Hla".
  step. step. step. iApply wp_enter; [reflexivity | vx | iNext].
  iApply (wp_stdfiles_loop Φ $! [fe; fo; fi] _ la lareg 0 with "[%] Hla Hc Hpre").
  { split_and!; [rewrite Z.add_0_r; lk_prove | lia | rewrite Z.add_0_r; exact Hlal | lia | lia]. }
  iNext. iIntros "Hla Hc Hlinks Hlives".
  iApply ("HK" with "[Hla Hc Hlinks Hlk Hrf Hrfc] Hlives").
  iExists la, lareg, lk, lkreg, rf, rfreg. rewrite Z.add_0_r. iFrame. iPureIntro. tauto.
Qed.

End rules.
