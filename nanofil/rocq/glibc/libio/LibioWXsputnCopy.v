(** Both wide stream writers use wmempcpy when they have more than
    twenty characters to copy. Only a heap buffer has that much room.
    The function copies four bytes per character and returns the address
    just past the last one, which becomes the stream's write pointer. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude HelloImageCode275 Fix OsWorld OsRegistry FileInv
  LibioLogic LibioCloseSteps MemFwdCode LibioDefaultXsputnCopy WPrintfDispatch.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation at_obj b o := (mkPtr (b+o) (Obj b)).
Local Abbreviation size cs := (Z.of_nat (length cs)).
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Definition wmempcpy_fn := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_275])) "__wmempcpy".

Section copy.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hfn : find_fn ge (TAtom "zmemmove") = None) (Hsym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Context `{!Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI_mempcpy" glibc_mempcpy}.

(** The destination may start partway into the stream's buffer. The
    caller gets the whole buffer back at its original size, together
    with the same read-only or shared access to the source. *)
Lemma wp_wmempcpy fr b br off xs caps dq s sr so cs Φ :
  call_frame wmempcpy_fn [WPtr (at_obj b off); WPtr (at_obj s so); WInt (size cs)] = Some fr ->
  0 < b -> b mod 8 = 0 -> b+size xs <= r_end br -> r_end br <= 2^63 ->
  0 <= off -> off+4*size cs <= size xs -> length caps = length xs -> Forall (fun x => 0 <= x < 256) xs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  live b br -∗ bytes b 0 xs -∗ auxes b 0 caps -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  ▷ (live b br -∗ buf_after b (length xs) -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
     Φ (Ret (WPtr (mkPtr (b+off+4*size cs) (Obj b))))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hb Hb8 He Hr Ho Hfit L V Hs Hs8 Hso Hse Hsr. injection Hfr as <-. iIntros "Hl Hx Ha Hs Hcs HK".
  step. step. iApply (wp_call_mempcpy_in Hmove Hfn Hsym _ _ _ _ _ _ _ _ _ b br xs caps off dq s sr so (Obj s) (stage_bytes cs)
    with "Hl Hx Ha Hs Hcs"); try assumption; try apply defines; try reflexivity; try (rewrite ?stage_bytes_length; lia).
  - rewrite stage_bytes_length. cbn [map_option arg_x value_x]. lookups. cbn.
    change (2 ^ ((2 mod 2 ^ 32) mod 64)) with 4. unwrap2. repeat f_equal; lia.
  - left. reflexivity.
  - apply stage_bytes_valid.
  - iNext. iIntros "Hl Hafter Hs Hcs". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. iApply wp_ret; [reflexivity|vx|]. iNext.
    rewrite stage_bytes_length. replace (Z.of_nat (4 * length cs)) with (4*size cs) by lia. by iApply ("HK" with "Hl Hafter Hs Hcs").
Qed.
End copy.
