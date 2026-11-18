(** The formatter copies a run of bytes from a string into a buffer's
    window with `c: memcpy`. This module proves three facts that a
    proof of such a copy needs.

    The first fact is that the length of a string fits in a C integer.
    The second fact is that a string lends any run of its bytes to a
    reader and takes the run back. The third fact is that the compiled
    `c: memcpy` meets the contract [win_copy_spec] of
    [PrintfSpec](PrintfSpec.v), which describes a copy into a window.

    An earlier module, [PrintfStagingCopy](PrintfStagingCopy.v),
    already proves that the compiled `c: memcpy` copies bytes into a
    window safely. Its statement lists the bytes of the window one by
    one, and a caller has to supply that list. The contract
    [win_copy_spec] asks only that the caller owns the window, so it is
    easier to use. This module derives it from the earlier statement. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac agree gmap_view.
From iris.base_logic.lib Require Import gen_heap ghost_map own.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic WordString MemFwdLogic LibioDefaultXsputnBuf
  PrintfStagingCopy PrintfOut PrintfSpec.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Section copy.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A string is shorter than the address space of a Fil-C program. *)
Lemma word_string_short dq p s : word_string dq p s ⊢ ⌜Z.of_nat (length s) < 2 ^ 48⌝.
Proof using Type.
  iIntros "(%b & %reg & %ws & %Hs & _)". iPureIntro.
  destruct Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hws Hby Hch]. unfold wstart in Hf.
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia.
Qed.

(** A string lends the m bytes that follow its first d bytes. The
    reader learns the string's object, where that object ends and that
    every lent byte has the value of a byte. *)
Lemma word_string_lend dq p s d m :
  0 <= d -> 0 <= m -> d + m <= Z.of_nat (length s) ->
  word_string dq p s ⊢ ∃ sb sreg ys,
    ⌜Z.of_nat (length ys) = m /\ (ptr_cap p = Obj sb \/ ptr_cap p = Ro sb) /\ sb mod 8 = 0 /\ 0 < sb <= ptr_addr p /\
     ptr_addr p + d + m <= r_end sreg /\ r_end sreg <= 2 ^ 48 /\ Forall (fun y => 0 <= y < 256) ys⌝ ∗
    liveq dq sb sreg ∗ bytesq dq sb (ptr_addr p + d - sb) ys ∗
    (liveq dq sb sreg -∗ bytesq dq sb (ptr_addr p + d - sb) ys -∗ word_string dq p s).
Proof using Type.
  intros Hd Hm Hfit. iIntros "Hs".
  iDestruct (word_string_bytes with "Hs") as (sb sreg ws) "(%Hs & Hsl & Hbytes & Hback)".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hws Hby Hch].
  assert (Hend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end sreg).
  { unfold wstart in Hf. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iDestruct (bytesq_sub dq sb (ptr_addr p - sb) (s ++ [0]) (Z.to_nat d) (Z.to_nat m) with "Hbytes")
    as "[Hys Hrest]"; [rewrite length_app; cbn [length]; lia|].
  replace (ptr_addr p - sb + Z.of_nat (Z.to_nat d)) with (ptr_addr p + d - sb) by lia.
  iExists sb, sreg, (take (Z.to_nat m) (drop (Z.to_nat d) (s ++ [0]))). iFrame "Hsl Hys". iSplit.
  { iPureIntro. split; [rewrite length_take length_drop length_app; cbn [length]; lia|].
    split; [exact Hc|]. split; [exact Hb8|]. split; [lia|]. split; [lia|]. split; [exact Hsp|].
    apply Forall_take, Forall_drop, Forall_app. split; [|apply Forall_singleton; lia].
    eapply List.Forall_impl; [|exact Hch]. cbn. intros; lia. }

  iIntros "Hsl Hys". iApply ("Hback" with "Hsl"). iApply "Hrest". iExact "Hys".
Qed.

(** A run of bytes lends the m bytes that follow its first d bytes,
    in the same way as a string does. *)
Lemma byte_run_lend dq p sb sreg s d m :
  0 <= d -> 0 <= m -> d + m <= Z.of_nat (length s) ->
  byte_run dq p sb sreg s ⊢ ∃ ys,
    ⌜Z.of_nat (length ys) = m /\ (ptr_cap p = Obj sb \/ ptr_cap p = Ro sb) /\ sb mod 8 = 0 /\ 0 < sb <= ptr_addr p /\
     ptr_addr p + d + m <= r_end sreg /\ r_end sreg <= 2 ^ 48 /\ Forall (fun y => 0 <= y < 256) ys⌝ ∗
    liveq dq sb sreg ∗ bytesq dq sb (ptr_addr p + d - sb) ys ∗
    (liveq dq sb sreg -∗ bytesq dq sb (ptr_addr p + d - sb) ys -∗ byte_run dq p sb sreg s).
Proof using Type.
  intros Hd Hm Hfit. iIntros "((%Hc & %Hb8 & %Ha & %Hend & %Hsp & %Hch) & Hsl & Hbytes)".
  iDestruct (bytesq_sub dq sb (ptr_addr p - sb) s (Z.to_nat d) (Z.to_nat m) with "Hbytes") as "[Hys Hrest]"; [lia|].
  replace (ptr_addr p - sb + Z.of_nat (Z.to_nat d)) with (ptr_addr p + d - sb) by lia.
  iExists (take (Z.to_nat m) (drop (Z.to_nat d) s)). iFrame "Hsl Hys". iSplit.
  { iPureIntro. split; [rewrite length_take length_drop; lia|]. split_and!; [exact Hc | exact Hb8 | lia..| exact Hsp |].
    apply Forall_take, Forall_drop. exact Hch. }
  iIntros "Hsl Hys". iFrame "Hsl". iSplit; [done|]. iApply "Hrest". iExact "Hys".
Qed.

(** The first n bytes of a string are a run of bytes, and the string
    comes back when the run is returned. *)
Lemma word_string_run dq p s n :
  0 <= n <= Z.of_nat (length s) ->
  word_string dq p s ⊢ ∃ sb sreg ys,
    ⌜Z.of_nat (length ys) = n⌝ ∗ byte_run dq p sb sreg ys ∗ (byte_run dq p sb sreg ys -∗ word_string dq p s).
Proof using Type.
  intros Hn. iIntros "Hs".
  iDestruct (word_string_lend dq p s 0 n with "Hs")
    as (sb sreg ys) "((%Hlen & %Hc & %Hb8 & %Ha & %Hend & %Hsp & %Hch) & Hsl & Hys & Hback)"; [lia..|].
  replace (ptr_addr p + 0 - sb) with (ptr_addr p - sb) by lia.
  iExists sb, sreg, ys. iSplit; [done|]. iFrame "Hsl Hys". iSplit; [iPureIntro; split_and!; first [assumption | lia]|].
  iIntros "(_ & Hsl & Hys)". iApply ("Hback" with "Hsl Hys").
Qed.

(** A string lends the byte at index i to a reader, and the reader
    learns its value. The index may be the length of the string, and
    the byte there is the terminating NUL. The formatter reads one byte
    of its format in this way to choose what it does next. *)
Lemma word_string_at dq p s (i : nat) x :
  (s ++ [0]) !! i = Some x ->
  word_string dq p s ⊢ ∃ sb sreg,
    ⌜(ptr_cap p = Obj sb \/ ptr_cap p = Ro sb) /\ 0 < sb <= ptr_addr p /\
     ptr_addr p + Z.of_nat i + 1 <= r_end sreg /\ r_end sreg <= 2 ^ 48⌝ ∗
    liveq dq sb sreg ∗ bytesq dq sb (ptr_addr p + Z.of_nat i - sb) [x] ∗
    (liveq dq sb sreg -∗ bytesq dq sb (ptr_addr p + Z.of_nat i - sb) [x] -∗ word_string dq p s).
Proof using Type.
  intros Hx. pose proof (lookup_lt_Some _ _ _ Hx) as Hi. rewrite length_app in Hi. cbn [length] in Hi.
  iIntros "Hs". iDestruct (word_string_bytes with "Hs") as (sb sreg ws) "(%Hs & Hsl & Hbytes & Hback)".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hws Hby Hch].
  assert (Hend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end sreg).
  { unfold wstart in Hf. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iDestruct (bytesq_sub dq sb (ptr_addr p - sb) (s ++ [0]) i 1 with "Hbytes") as "[Hy Hrest]";
    [rewrite length_app; cbn [length]; lia|].
  rewrite (drop_S _ _ _ Hx) /=. replace (ptr_addr p - sb + Z.of_nat i) with (ptr_addr p + Z.of_nat i - sb) by lia.
  iExists sb, sreg. iFrame "Hsl Hy". iSplit; [iPureIntro; split; [exact Hc|]; lia|].
  iIntros "Hsl Hy". iApply ("Hback" with "Hsl"). iApply "Hrest". iExact "Hy".
Qed.

(** ## Lending the rest of a string *)

(** The formatter passes a pointer into the middle of its format to
    the functions that it calls. Such a function has a contract for a
    whole string, so the formatter lends it the rest of the format as
    a string of its own and takes it back afterwards. The lemma
    [word_string_borrow] of [WordString](../string/WordString.v) does
    this for a share that is a fraction, because it keeps half of the
    share to restore the format. A caller of the formatter may hold
    any share, also one that is partly or wholly read-only. The lemmas
    below cover those shares. *)

(** A share that is partly read-only yields a wholly read-only copy
    and stays what it was. *)
Lemma ptsq_both q ps : ptsq (DfracBoth q) ps ⊢ ptsq (DfracBoth q) ps ∗ ptsq DfracDiscarded ps.
Proof using Type.
  rewrite /ptsq -big_sepL_sep. apply big_sepL_mono. intros _ lv _.
  rewrite gen_heap.pointsto_unseal /gen_heap.pointsto_def ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def.
  rewrite -own_op -gmap_view_frag_op agree_idemp. reflexivity.
Qed.

(** A string of any share lends its rest, after the prefix s1, as a
    string at the advanced pointer. The reader gets some share of the
    rest, and giving it back restores the whole string. *)
Lemma word_string_borrow_any dq p s1 s2 :
  word_string dq p (s1 ++ s2) ⊢ ∃ dq',
    word_string dq' (ptr_add p (Z.of_nat (length s1))) s2 ∗
    (word_string dq' (ptr_add p (Z.of_nat (length s1))) s2 -∗ word_string dq p (s1 ++ s2)).
Proof using Type.
  destruct dq as [q| |q].
  - rewrite -(Qp.div_2 q). iIntros "Hs". iExists (DfracOwn (q / 2)). iApply (word_string_borrow with "Hs").
  - iIntros "#Hs". iExists DfracDiscarded. iSplit; [iApply (word_string_suffix with "Hs")|]. iIntros "_". iExact "Hs".
  - iIntros "(%b & %reg & %ws & %Hs & Hl & Hw)". iDestruct (ptsq_both with "Hl") as "[Hl #Hl']".
    iDestruct (ptsq_both with "Hw") as "[Hw #Hw']". iExists DfracDiscarded. iSplitR.
    + iApply word_string_suffix. iExists b, reg, ws. iSplit; [done|]. iFrame "Hl' Hw'".
    + iIntros "_". iExists b, reg, ws. iSplit; [done|]. iFrame "Hl Hw".
Qed.

(** A function that meets the older contract for a copy into a window
    also meets [win_copy_spec]. *)
Lemma win_copy_of_window g :
  HasSpec registry (os_wi w0) ge g window_copy_spec -> HasSpec registry (os_wi w0) ge g win_copy_spec.
Proof using Type.
  intros H [[[[[[[[[b reg] lo] hi] a] dq] sb] sreg] [qa qc]] ys].
  destruct (H (b, reg, lo - b, [], [], a - b, dq, sb, sreg, qa - sb, qc, ys)) as (gf & Hg & Hfr & _).
  cbn [fs_args window_copy_spec win_copy_spec fs_pre fs_post ptr_addr ptr_cap] in *.
  replace (b + (a - b)) with a in Hfr by lia. replace (sb + (qa - sb)) with qa in Hfr by lia.
  exists gf. split; [exact Hg|]. split; [exact Hfr|]. intros fr Φ Hcall.
  iIntros "(%Hp & Hl & Hwin & Hsl & Hs) HK". iDestruct "Hwin" as (xs cs) "((%Hlen & %Hcs & %Hx) & Hx & Hcs)".
  destruct Hp as (Hb8 & Hlo8 & Hlo & Ha & Hhi & Hend & Hc & Hsb8 & Hsa & Hsend & Hn & Hy).
  destruct (H (b, reg, lo - b, xs, cs, a - b, dq, sb, sreg, qa - sb, qc, ys)) as (gf' & Hg' & _ & Ht).
  rewrite Hg in Hg'. injection Hg' as <-. cbn [fs_args window_copy_spec fs_pre fs_post] in Ht.
  replace (b + (a - b)) with a in Ht by lia. replace (sb + (qa - sb)) with qa in Ht by lia.
  iApply (Ht fr Φ Hcall with "[Hl Hx Hcs Hsl Hs]").
  { iFrame "Hl Hx Hcs Hsl Hs". iPureIntro. split; [exact Hc|]. split; [exact Hn|]. split; [exact Hb8|].
    split; [Z.div_mod_to_equations; lia|]. split; [exact Hsb8|]. repeat (split; [lia|]).
    split; [exact Hx | exact Hy]. }
  iIntros (v) "(-> & Hl & Hw & Hsl & Hs)". iApply "HK". iFrame "Hl Hsl Hs". iSplit; [done|].
  iDestruct "Hw" as (xs' cs') "((%Hlen' & %Hcs' & %Hx' & _) & Hx & Hcs)". iExists xs', cs'. iFrame "Hx Hcs".
  iPureIntro. split; [lia|]. split; [lia | exact Hx'].
Qed.

End copy.
