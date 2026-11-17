(** The formatter appends most characters with the inline function
    `c: __printf_buffer_putc`. It stores the character at the buffer's
    write pointer when the window has a free byte, and it calls
    `c: __printf_buffer_putc_1` to flush when the window is full. This
    module proves that the compiled function meets [putc_spec] of
    [PrintfSpec](PrintfSpec.v).

    The proof follows the shape of the compiled function, which has
    four blocks. It states what holds at the start of each block and
    proves the blocks one at a time, as [CBlocks](../CBlocks.v)
    describes. The statements name the two parameters `c: buf` and
    `c: ch` as the C source does, and they name the buffer's fields as
    the C structure does. The proof assumes a contract for
    `c: __printf_buffer_putc_1`, the one function that is called. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic FormatterCode FormatterSrc
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Module S := FormatterSrc.fn_glibc_vfprintf_internal___printf_buffer_putc.

(** The table [putc_cuts] gives, for each label, the temporaries that
    are live there and the C variable that each one holds. *)
Definition putc_cuts : list (string * cut_sig) :=
  Eval vm_compute in cut_table S.temp_keys S.live_in.

Section putc.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (R : Z * region * Z * Z -> iProp Σ).
Context `{!Callees [(TAtom "__printf_buffer_putc_1", putc_spec R)] }.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The block table *)

(** The two parameters keep their values in every block. *)
Definition putc_vals (bb c : Z) : list (string * word) :=
  [("buf", WPtr (mkPtr bb (Obj bb))); ("ch", WInt c)].

Definition putc_post (bb : Z) (o : outcome) : iProp Σ := (⌜o = RetVoid⌝ ∗ printf_out R bb)%I.

(** The function starts with a usable buffer, and so does the block
    that calls the flushing function. The block that stores the
    character also knows that the window has a free byte. The block
    that returns needs no parameter, so its signature is empty. *)
Definition putc_blocks : list bspec :=
  [BSpec "start" (cut_in putc_cuts "start") (Z * Z) (fun '(bb, c) => putc_vals bb c)
     (fun '(bb, c) => ⌜0 <= c < 2 ^ 32⌝ ∗ printf_out R bb)%I (fun '(bb, _) => putc_post bb);
   BSpec "L4" (cut_in putc_cuts "L4") (Z * Z * region * pwin * Z * Z)
     (fun '(bb, c, _, _, _, _) => putc_vals bb c)
     (fun '(bb, c, breg, w, written, mode) =>
        ⌜0 <= c < 2 ^ 32 /\ pw_ptr w < pw_end w⌝ ∗ printf_buf bb breg w written mode ∗ R (pw_place w))%I
     (fun '(bb, _, _, _, _, _) => putc_post bb);
   BSpec "L5" (cut_in putc_cuts "L5") (Z * Z) (fun '(bb, c) => putc_vals bb c)
     (fun '(bb, c) => ⌜0 <= c < 2 ^ 32⌝ ∗ printf_out R bb)%I (fun '(bb, _) => putc_post bb);
   BSpec "L6" (cut_in putc_cuts "L6") Z (fun bb => putc_vals bb 0)
     (fun bb => printf_out R bb) putc_post].

(** ## The blocks *)

Lemma putc_table : ⊢ blocks_hold glibc_printf_buffer_putc putc_blocks.
Proof using Type*.
  apply blocks_close. iIntros "#IH". repeat iSplit; [| | | | done]; iModIntro.
  - (* start: is the window full? *)
    iIntros ([bb c] e from Φ) "%He [%Hc Hout] HK". cbn [bs_sig bs_vals bs_pre bs_post bs_label] in *.
    c_env_open He. iDestruct "Hout" as (breg w written mode) "[Hbuf HR]". buf_open "Hbuf".
    block_enter. step. check "Hl". load_window "Hl" "Hptr" "Hwl".
    step. check "Hl". load_window "Hl" "Hend" "Hwl". step. step. step. branch_eqn E.
    + goto_block "IH" "HK" 2%nat with (bb, c).
      iSplit; [done|]. out_close "HR" with w. exact Hw.
    + goto_block "IH" "HK" 1%nat with (bb, c, breg, w, written, mode).
      iSplit; [iPureIntro|iSplitR "HR"; [buf_close; exact Hw|iExact "HR"]].
      split; [exact Hc|]. assert (pw_ptr w <> pw_end w); [|unfold pwin_ok in Hw; lia].
      intros Heq. rewrite Heq Z.eqb_refl in E. discriminate E.
  - (* L4: store the character and advance the write pointer. *)
    iIntros ([[[[[bb c] breg] w] written] mode] e from Φ) "%He [[%Hc %Hfree] [Hbuf HR]] HK".
    cbn [bs_sig bs_vals bs_pre bs_post bs_label] in *. c_env_open He. buf_open "Hbuf".
    block_enter. step. load_window "Hl" "Hptr" "Hwl". step. check "Hl". store "Hl" "Hptr". step.
    iDestruct (win_live_acc with "Hl Hwl") as "[Hwo Hback]". iDestruct "Hbytes" as (xs) "[%Hlen Hbytes]".
    iDestruct (window_byte w xs Hw Hfree Hlen with "Hbytes") as (x) "[Hx Hrest]". unfold pwin_ok in Hw.
    check "Hwo". rule2 "Hwo" "Hx" ltac:(eapply wp_raw_store_byte; inst; [vx | vx | reflexivity | a2 | wi_store]).
    iDestruct ("Hback" with "Hwo") as "[Hl Hwl]". iDestruct ("Hrest" with "Hx") as "Hbytes". step.
    goto_block "IH" "HK" 3%nat with bb. cbn [ptr_addr ptr_cap]. unwrap2.
    out_close "HR" with (PWin (pw_obj w) (pw_reg w) (pw_base w) (pw_ptr w + 1) (pw_end w)).
    unfold pwin_ok. cbn [pw_obj pw_reg pw_base pw_ptr pw_end]. lia.
  - (* L5: the window is full, so the out-of-line function flushes and appends. *)
    iIntros ([bb c] e from Φ) "%He [%Hc Hout] HK". cbn [bs_sig bs_vals bs_pre bs_post bs_label] in *.
    c_env_open He. block_enter. step.
    call_callee with (bb, _) giving "Hout".
    { iFrame "Hout". iPureIntro. apply Z.mod_pos_bound. lia. }
    iDestruct "Hpost" as "[-> Hout]". block_resume. step. goto_block "IH" "HK" 3%nat with bb. iExact "Hout".
  - (* L6: return. *)
    iIntros (bb e from Φ) "_ Hout HK". cbn [bs_sig bs_vals bs_pre bs_post bs_label] in *.
    block_enter. iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|iExact "Hout"].
Qed.

(** ## The contract *)

(** The compiled `c: __printf_buffer_putc` meets [putc_spec] in any
    program that defines it. *)
Lemma putc_has_spec `{!Defines ge "glibc_vfprintf_internal#__printf_buffer_putc" glibc_printf_buffer_putc} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_vfprintf_internal#__printf_buffer_putc") (putc_spec R).
Proof using Type*.
  eapply (blocks_has_spec _ _ _ putc_blocks); [exact defines | reflexivity | | exact putc_table].
  intros [bb c]. eexists _, (bb, c). split; [reflexivity|]. split; [c_env_close|].
  cbn [fs_pre fs_post bs_pre bs_post putc_spec]. iIntros "$" (r) "$".
Qed.

End putc.
