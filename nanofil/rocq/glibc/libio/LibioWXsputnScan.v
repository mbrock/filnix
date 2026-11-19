(** When the line-buffered stream can fit the entire write, it searches
    the staged characters backwards. A newline splits the write just
    after that character and requests a flush. If the search reaches
    the start, the writer keeps the available count and does not flush. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic
  LibioDefaultXsputnBuf CBlocks WideWriteSpec WideBytes.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).

Definition wscan_names := map TAtom ["pr.14"; "v62"; "v63"; "v64"; "v69"; "chk6"; "v70"; "v71";
  "v74"; "v76"; "v77"; "v78"; "pr.10"; "pr.6"].

Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation at_idx b so i := (mkPtr (b+so+4*i) (Obj b)).

(** The cursor starts one past the last character to inspect. The loop
    tests it against the base before stepping back and borrowing four
    bytes, so even a search with no newline stays inside the loan. *)
Lemma wp_wfile_xsputn_scan dq b br so cs capacity :
  0 < b -> 0 <= so -> b+so+4*size cs <= r_end br -> r_end br <= 2^63 ->
  Forall (fun c => 0 <= c < 2^32) cs -> 0 <= capacity < 2^63 ->
  ⊢ ∀ e i Φ, ⌜lookup (TAtom "v2") e = Some (WPtr (mkPtr (b+so) (Obj b))) /\
    lookup (TAtom "pr.14") e = Some (WPtr (at_idx b so i)) /\ lookup (TAtom "v44") e = Some (WInt capacity) /\
    0 <= i <= size cs⌝ -∗ liveq dq b br -∗ bytesq dq b so (stage_bytes cs) -∗
    (∀ e' count flush, ⌜same_out wscan_names e e' /\ lookup (TAtom "pr.10") e' = Some (WInt count) /\
      lookup (TAtom "pr.6") e' = Some (WInt flush) /\ ((flush = 0 /\ count = capacity) \/ (flush = 1 /\ 1 <= count <= i))⌝ -∗
      liveq dq b br -∗ bytesq dq b so (stage_bytes cs) -∗
      WP (ERun (mkFrame wprintf_xsputn_fn e' [] None (body_at wprintf_xsputn_fn "L20")) : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame wprintf_xsputn_fn e [] None (body_at wprintf_xsputn_fn "L56")) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hb Hso He Hr V Hcap. iLöb as "IH". iIntros (e i Φ (Hv2 & Hp & H44 & Hi)) "Hl Hcs HK".
  body_start wprintf_xsputn_fn "L56"%string. do 3 step. destruct (Z.eq_dec i 0) as [->|Hnz].
  - branch_as true. step. iApply ("HK" $! _ capacity 0 with "[%] Hl Hcs"). split; [same_tac|].
    split_and!; [lookups; unwrap2; reflexivity|lookups; reflexivity|left; auto].
  - branch_as false. step. step. set (j := Z.to_nat (i-1)).
    destruct (lookup_lt_is_Some_2 cs j ltac:(lia)) as [x Hx]. pose proof (Forall_lookup_1 _ _ _ _ V Hx) as Vx.
    cbn beta in Vx.
    iDestruct (wchar_at _ _ _ _ _ _ Hx with "Hcs") as "[Hx Hback]".
    check_read_dq "Hl" by (cbn [ptr_addr]; unfold raw_address; unwrap2; lia). iNext. iIntros "Hl".
    load_bytes_dq "Hl Hx" decode (apply load_sw_int; exact Vx) by (cbn [ptr_addr]; unfold raw_address; unwrap2; lia).
    iNext. iIntros "Hl Hx". iDestruct ("Hback" with "Hx") as "Hcs". step.
    destruct (Z.eq_dec x 10) as [->|Hnot].
    + branch_as false. do 7 step. iApply ("HK" $! _ i 1 with "[%] Hl Hcs"). split; [same_tac|].
      split_and!; [|lookups; reflexivity|right; lia]. lookups. do 2 f_equal. cbn [ptr_addr]. unfold raw_address. unwrap2.
      change (sign_extension (2^64) (2^63) 4) with 4. change (4 =? 0) with false. unfold sign_extension. unwrap2.
      replace (b+so+4*i-4-(b+so)) with ((i-1)*4) by lia.
      rewrite (proj2 (Z.leb_gt (2^63) ((i-1)*4)) ltac:(lia)) Z.quot_mul; [|lia]. unwrap2. lia.
    + branch_as true. step. iApply ("IH" $! _ (i-1) with "[%] Hl Hcs [HK]").
      * split_and!; try (lookups; reflexivity); try lia. lookups. do 3 f_equal. cbn [ptr_addr]. unfold raw_address. unwrap2. lia.
      * iIntros (e' count flush (Hs & Hct & Hfl & Hres)) "Hl Hcs".
        iApply ("HK" $! e' count flush with "[%] Hl Hcs"). split; [eapply same_out_trans; [|exact Hs]; same_tac|].
        split; [done|]. split; [done|]. lia.
Qed.
End scan.
