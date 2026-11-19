(** Glibc's transliteration table stores a replacement as a string of wide
    characters followed by a zero word. Before converting the string,
    glibc scans for that word to find the end of the input. The proof
    uses the terminator in the image to bound every read in the scan. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude CLocaleCells CtypeTranslitTables OsWorld
  FileInv LibioLogic LibioDefaultXsputnBuf CBlocks Fix LibioWIdle LibioWConvAscii LibioWConvConsts
  LibioWConvTranslitCmp.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).

(** ## The list of replacements

    The replacement table holds each list of replacements as strings
    that end with a zero word, followed by an empty string. Startup
    checked these facts for every list with [list_okb]. The two lemmas
    below turn that check into the facts that the loop reads. *)

(** A string found by [nul_at] ends with a zero word, and its other words are not zero. *)
Lemma nul_at_spec tbl f : forall p q, nul_at tbl p f = Some q ->
  tbl !! (p + q)%nat = Some 0 /\ forall i, (i < q)%nat -> exists x, tbl !! (p + i)%nat = Some x /\ x <> 0.
Proof using Type.
  induction f as [|f IH]; intros p q H; [discriminate|]. cbn in H.
  destruct (tbl !! p) as [x|] eqn:Ex; [|discriminate].
  destruct x as [|x|x].
  { injection H as <-. rewrite Nat.add_0_r. split; [exact Ex | intros; lia]. }
  all: destruct (nul_at tbl (S p) f) as [qq|] eqn:Eq; [|discriminate]; injection H as <-;
    destruct (IH _ _ Eq) as [Hz Hn]; split; [replace (p + S qq)%nat with (S p + qq)%nat by lia; exact Hz|];
    (intros [|i] Hi; [replace (p + 0)%nat with p by lia; eexists; split; [exact Ex | discriminate]|]);
    destruct (Hn i ltac:(lia)) as (y & Hy & Hy0); exists y;
    replace (p + S i)%nat with (S p + i)%nat by lia; split; [exact Hy | exact Hy0].
Qed.

(** A checked list starts with a string, which the empty string ends or another checked list follows. *)
Lemma list_okb_step tbl p f : list_okb tbl p f = true -> exists q y,
  nul_at tbl p 64 = Some q /\ tbl !! (p + q + 1)%nat = Some y /\
  (y = 0 \/ exists f', list_okb tbl (p + q + 1) f' = true).
Proof using Type.
  destruct f as [|f]; [discriminate|]. cbn [list_okb]. destruct (nul_at tbl p 64) as [q|]; [|discriminate].
  destruct (tbl !! (p + q + 1)%nat) as [y|] eqn:Ey; [|discriminate]. intros H. exists q, y.
  split; [reflexivity|]. split; [exact Ey|]. destruct y; [left; reflexivity | right; eexists; exact H..].
Qed.

Section repl.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## Measuring one replacement

    The loop at block `c: L213` counts the words of the replacement
    that starts at word p of the table, up to its zero word. It reads
    the table through a read-only share and changes only its own
    temporaries. *)

(** These are the temporaries that the counting loop assigns. *)
Definition len_names : list name := Eval vm_compute in
  flat_map (fun b => app (map (fun p => match p with Phi d _ _ => d end) (b_phis b)) (flat_map inst_defs (b_insts b)))
    (filter (fun b => match b_label b with TAtom s => existsb (String.eqb s) ["L213"; "L214"]%string | _ => false end)
      (fn_blocks glibc_translit)).

(** The count starts at i words and stops at the zero word at p + q. *)
Lemma repl_len ls fb reg tbl p q Φ :
  0 < fb -> fb + 4 * Z.of_nat (length tbl) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Z.of_nat (length tbl) < 2 ^ 30 -> Forall (fun x => 0 <= x < 2 ^ 32) tbl ->
  tbl !! (p + q)%nat = Some 0 -> (forall i, (i < q)%nat -> exists x, tbl !! (p + i)%nat = Some x /\ x <> 0) ->
  ⊢ ∀ i e, ⌜(i <= q)%nat /\ lookup (TAtom "pr.7") e = Some (WInt (Z.of_nat p)) /\
      lookup (TAtom "pr.8") e = Some (WInt (Z.of_nat i)) /\ lookup (TAtom "v95") e = Some (WPtr (rop fb))⌝ -∗
    liveq DfracDiscarded fb reg -∗ bytesq DfracDiscarded fb 0 (le_words tbl) -∗
    (∀ e', ⌜same_out len_names e e' /\ lookup (TAtom "pr.8") e' = Some (WInt (Z.of_nat q)) /\
        lookup (TAtom "v222") e' = Some (WPtr (mkPtr (fb + 4 * Z.of_nat (p + q)) (Ro fb)))⌝ -∗
      WP (ERun (mkFrame glibc_translit e' ls None (body_at glibc_translit "L215")) : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame glibc_translit e ls None (body_at glibc_translit "L213")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfb Hend Hreg Hlen Htbl Hz Hnz. pose proof (lookup_lt_Some _ _ _ Hz) as Hpq.
  iLöb as "IH". iIntros (i e (Hi & Hp7 & Hp8 & Hv95)) "Htl Htb HK".
  assert (0 <= Z.of_nat p + Z.of_nat i < Z.of_nat (length tbl)) by lia.
  body_start glibc_translit "L213". do 4 step.
  check_read_dq "Htl" by a4. iNext. iIntros "Htl".
  destruct (lookup_lt_is_Some_2 tbl (p + i)%nat ltac:(lia)) as [x Hx].
  iDestruct (wchar_at _ _ _ _ _ x Hx with "Htb") as "[Hx Hback]".
  assert (Hx32 : 0 <= x < 2 ^ 32) by exact (Forall_lookup_1 _ _ _ _ Htbl Hx).
  load_bytes_dq "Htl Hx" decode (apply load_uw_char; exact Hx32) by a4.
  iNext. iIntros "Htl Hx". iDestruct ("Hback" with "Hx") as "Htb". step.
  destruct (Nat.eq_dec i q) as [->|N].
  - rewrite Hz in Hx. injection Hx as <-. branch_as true. step. iApply ("HK" with "[%]").
    split_and!; [same_tac | vx |]. repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]).
    rewrite Symbolic.lookup_after_put_same. do 3 f_equal. cbn [ptr_addr ptr_cap]. wnorm. lia.
  - destruct (Hnz i ltac:(lia)) as (y & Hy & Ny). rewrite Hx in Hy. injection Hy as <-.
    branch_as false. do 4 step.
    iApply ("IH" $! (S i) with "[%] Htl Htb [HK]").
    + split_and!; try lia; try solve [vx]. rewrite Symbolic.lookup_after_put_same. do 2 f_equal. unwrap2. lia.
    + iIntros (e' (Hs & Hp8' & Hv222)). iApply ("HK" with "[%]").
      split_and!; try assumption. eapply same_out_trans; [|exact Hs]. same_tac.
Qed.
End repl.
