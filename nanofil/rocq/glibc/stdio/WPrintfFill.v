(** Hello specifies no field width, but the compiled formatter compares
    the low 32 bits of zero minus the wide string length. Those bits
    can represent a positive int for a long greeting, so even this format
    can ask for padding. Each call to wide memset fills part of the
    private array. It writes four characters per iteration and checks the
    count before writing each of the last three. *)

From Glibc Require Import Unit_wcsmbs_wmemset_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld FileInv LibioLogic WPrintfDispatch.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Definition wprintf_fill_fn := Unit_wcsmbs_wmemset_os.fn___GI___wmemset.
Local Definition loop_head := Eval vm_compute in
  default (mkBlock (TAtom "L8") [] [] JUnreachable) (find_block (TAtom "L8") (fn_blocks wprintf_fill_fn)).

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section fill.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** A store replaces one four-byte character without reading it. The old
    bytes can have any value; the new bytes encode the padding character. *)
Local Fixpoint cells b o (n : nat) (v : option Z) : iProp Σ :=
  match n with
  | O => emp
  | S k => (match v with Some c => bytes b o (le_bytes c 4)
                         | None => ∃ bs, ⌜length bs = 4%nat⌝ ∗ bytes b o bs end) ∗ cells b (o+4) k v
  end%I.

Local Lemma lend_cells b o n bs : length bs = (4*n)%nat -> bytes b o bs ⊢ cells b o n None.
Proof using Type.
  revert o bs. induction n as [|n IH]; intros o bs Hlen; [by iIntros "_"|].
  iIntros "H". iDestruct (bytes_take_drop _ _ _ 4 with "H") as "[Hfirst Hrest]"; [lia|].
  iSplitL "Hfirst"; [iExists (take 4 bs); iFrame; iPureIntro; rewrite length_take; lia|].
  iApply (IH with "Hrest"). rewrite length_drop. lia.
Qed.

Local Lemma collect_cells b o n c : cells b o n (Some c) ⊢ bytes b o (stage_bytes (replicate n c)).
Proof using Type.
  revert o. induction n as [|n IH]; intros o; [done|].
  change (cells b o (S n) (Some c) ⊢ bytes b o (le_bytes c 4 ++ stage_bytes (replicate n c))).
  rewrite bytes_app length_le_bytes. iIntros "[$ H]". by iApply IH.
Qed.

(** The unrolled loop retains the original destination for its return
    value. Only its moving cursor and its remaining count change. *)
Local Lemma fill_loop b br ret c Φ :
  0 < b -> r_end br <= 2^63 -> 0 <= c < 2^32 ->
  forall n o e, 0 <= o -> b + o + 4 * Z.of_nat n <= r_end br ->
  lookup (TAtom "v0") e = Some (WPtr ret) -> lookup (TAtom "v2") e = Some (WInt c) ->
  lookup (TAtom "pr.1") e = Some (WInt (Z.of_nat n)) ->
  lookup (TAtom "pr.2") e = Some (WPtr (mkPtr (b+o) (Obj b))) ->
  live b br -∗ cells b o n None -∗
  (live b br -∗ cells b o n (Some c) -∗ Φ (Ret (WPtr ret))) -∗
  WP (ERun (mkFrame wprintf_fill_fn e [] None (Exec (TAtom "L8") (b_insts loop_head) (b_jump loop_head))) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hb Hreg Hc n. induction n as [n IH] using lt_wf_ind.
  intros o e Ho Hend Hret Hc' Hn Hp. iIntros "Hl Hcells HK". cbn [loop_head b_insts b_jump].
  Local Ltac write_one Hnew :=
    let xs := fresh "xs" in let L := fresh "L" in
    iDestruct "Hcells" as "[Hx Hcells]"; iDestruct "Hx" as (xs L) "Hx";
    iApply (wp_raw_store_w with "Hl Hx"); [vx | vx | reflexivity | a2 | exact L | wi_store |];
    iNext; iIntros "Hl Hx"; iRename "Hx" into Hnew;
    lazymatch goal with H : 0 <= ?c < 2^32 |- _ => iEval (rewrite (Z.mod_small c (2^32) H)) in Hnew end;
    clear xs L.
  Local Ltac finish := iApply wp_ret; [reflexivity | vx |]; iNext; iApply ("HK" with "Hl [-]"); cbn [cells]; iFrame.
  destruct n as [|[|[|[|k]]]]; step.
  1-4: branch; step; step; branch; step. 1: finish.
  1-3: check "Hl"; write_one "H0"; step; branch; step. 1: finish.
  1-2: step; check "Hl"; write_one "H1"; step; branch; step. 1: finish.
  1: step; check "Hl"; write_one "H2"; step; step; finish.
  branch_as false. step. check "Hl". write_one "H0".
  step. check "Hl". write_one "H1". step. check "Hl". write_one "H2". step. check "Hl". write_one "H3".
  do 4 step. iApply (IH k ltac:(lia) _ _ with "Hl Hcells [HK H0 H1 H2 H3]"); try lia; try lk_prove.
  1,2: lookups; cbn [ptr_addr ptr_cap]; unwrap2.
  - f_equal; f_equal; lia.
  - replace (b+o+16) with (b+(o+4+4+4+4)) by lia. reflexivity.
  - iIntros "Hl Hcells". iApply ("HK" with "Hl [-]"). cbn [cells]. iFrame.
Qed.

(** Wide memset changes exactly the requested four-byte words. The
    caller keeps the used prefix, the remaining free bytes and every
    shadow slot outside this rule's footprint. *)
Lemma wp_wprintf_fill fr b br o n c bs Φ :
  call_frame wprintf_fill_fn [WPtr (mkPtr (b+o) (Obj b)); WInt c; WInt (Z.of_nat n)] = Some fr ->
  0 < b -> r_end br <= 2^63 -> 0 <= c < 2^32 -> 0 <= o -> b+o+4*Z.of_nat n <= r_end br ->
  length bs = (4*n)%nat -> live b br -∗ bytes b o bs -∗
  ▷ (live b br -∗ bytes b o (stage_bytes (replicate n c)) -∗ Φ (Ret (WPtr (mkPtr (b+o) (Obj b))))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hb Hreg Hc Ho Hend Hbs. injection Hfr as <-. iIntros "Hl Hb HK". do 3 step.
  iApply (fill_loop b br _ c _ Hb Hreg Hc n o _ with "Hl [Hb] [HK]"); try assumption; try reflexivity.
  - lookups. unwrap2. reflexivity.
  - by iApply lend_cells.
  - iIntros "Hl Hcells". iApply ("HK" with "Hl [Hcells]"). by iApply collect_cells.
Qed.
End fill.
