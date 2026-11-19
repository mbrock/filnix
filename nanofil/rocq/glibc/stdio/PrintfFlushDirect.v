(** When printf has written straight into a stream, its flush returns
    those bytes to the stream by advancing the stream's write pointer.
    A full window ends that loan. Otherwise printf keeps writing into
    the remaining room and gives back only the prefix it no longer owns. *)

From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Machine ExternalCalls ExternalMachine
  Pieces Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv CStruct PrintfLayout PrintfOut PrintfSpec PrintfFileOut
  PrintfFlush PrintfFlushStage PrintfFlushPublish.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv.
Open Scope Z_scope.

Section direct.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** When printf fills the stream's buffer, it returns the whole buffer
    and keeps the next byte in its own staging array. When room remains,
    printf returns only the complete eight-byte slots before its cursor. *)
Lemma flush_direct_post fr a bb br w written Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr -> pw_obj w <> bb ->
  printf_buf bb br w written 4 -∗ file_R a bb br (pw_place w) -∗
  (fs_post (flush_to_file_spec (file_R a)) bb RetVoid -∗ Φ RetVoid) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hdb. iIntros "Hbuf HR HK". iDestruct "Hbuf" as "[%Hw Hbuf]".
  unfold file_R, pw_place. destruct (Z.eq_dec (pw_obj w) bb) as [Heq|_]; [contradiction|].
  iDestruct "HR" as "(%Hsize & Hfp & Herr & #Hro & #Hm & (%Hroom & %Hapart) & Hstage & Hloan)".
  iDestruct (file_lent_fields with "Hloan") as (freg) "(Hl & Hwc & Hback)".
  iApply (wp_flush_publish _ bb br (fo_fb a) freg w written with "[$Hbuf //] Hfp Hl Hwc"); try assumption.
  iIntros "Hbb Hpv Hfp Hl Hwc Hd Hwin". iDestruct ("Hback" with "[%] Hl Hwc") as "Hloan"; [unfold pwin_ok in Hw; lia|].
  struct_live_open "Hbb" as "[%Hbb Hbb]". iApply "HK".
  set (total := (written+(pw_ptr w-pw_base w)) mod 2^64). assert (Htotal : 0 <= total < 2^64) by (apply Z.mod_pos_bound; lia).
  iExists br, (published_window bb br w), total, 4. iSplit; [iPureIntro; pose proof (published_room bb br w Hw); intuition|].
  unfold published_window. destruct (Z.eq_dec (pw_ptr w) (pw_end w)) as [Hfull|Hroom'].
  - iDestruct (file_lent_tidy with "[$Hloan $Hd $Hwin]") as "HF".
    unfold printf_buf, file_R, pw_place, win_live, pw_lo, staged. cbn [pw_obj pw_reg pw_base pw_end pw_ptr].
    destruct (Z.eq_dec bb bb); [|contradiction]. unfold stage_off, stage_end.
    replace (bb+48-(bb+48) mod 8) with (bb+48) by (destruct Hbb as (_ & Hb8 & _); Z.div_mod_to_equations; lia).
    iDestruct (win_own_join bb (bb+48) (bb+48+1) (bb+176) with "Hstage") as "[Hp Hs]"; [lia|].
    destruct (numbers.Z.eq_dec bb bb); [|contradiction].
    iAssert (pbuf_live bb br) with "[Hbb]" as "Hbb"; [struct_live_close "Hbb"|].
    iFrame "Hbb Hfp Hpv Herr Hro Hm HF Hp Hs". repeat iSplit; iPureIntro; unfold pwin_ok; cbn [pw_obj pw_reg pw_base pw_end pw_ptr]; intuition lia.
  - set (lo := pw_base w - pw_base w mod 8). set (lo' := pw_ptr w - pw_ptr w mod 8).
    assert (Hr : lo <= lo' <= pw_ptr w) by (unfold lo, lo', pwin_ok in *; Z.div_mod_to_equations; lia).
    iDestruct (win_own_join (pw_obj w) lo lo' (pw_end w) with "Hwin") as "[Hp Hs]"; [unfold pwin_ok in Hw; lia|].
    iDestruct (file_lent_shrink _ _ _ lo lo' with "[$Hloan $Hp]") as "Hloan"; [exact Hr|].
    unfold printf_buf, file_R, pw_place, win_live, pw_lo. cbn [pw_obj pw_reg pw_base pw_end pw_ptr].
    destruct (Z.eq_dec (pw_obj w) bb); [contradiction|]. destruct (numbers.Z.eq_dec (pw_obj w) bb); [contradiction|].
    iAssert (pbuf_live bb br) with "[Hbb]" as "Hbb"; [struct_live_close "Hbb"|].
    iFrame "Hbb Hfp Hpv Herr Hro Hm Hd Hs Hstage Hloan". repeat iSplit; iPureIntro; unfold pwin_ok in *; cbn [pw_obj pw_reg pw_base pw_end pw_ptr]; intuition lia.
Qed.
End direct.
