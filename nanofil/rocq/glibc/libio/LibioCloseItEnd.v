From Glibc Require Import GlibcProgram.
(** Closing a descriptor leaves the stream's buffer pointers to reset.
    These final blocks call setb and record the closed flags, descriptor and
    offset. The caller supplies the old buffer's resource contract, so the
    same instruction proof supports heap buffers and in-object short buffers. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioCloseItCode FileInv LibioLogic
  SysWrappers LibioSetb LibioCloseSteps.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Closed flags preserve IO_LINKED and set the remaining bits to 0xFBAD240C. *)
Definition closed_flags (fl : Z) : Z := Z.lor (Z.land fl 128) 4222428172.

(** Setting USER_BUF leaves the IO_LINKED bit unchanged. *)
Lemma land_lor1_128 fl : Z.land (Z.lor fl 1) 128 = Z.land fl 128.
Proof. rewrite Z.land_lor_distr_l. change (Z.land 1 128) with 0. apply Z.lor_0_r. Qed.

(** The closed flags fit in a 32-bit integer. *)
Lemma closed_flags_range fl : 0 <= fl -> 0 <= closed_flags fl < 2 ^ 32.
Proof.
  intros H. unfold closed_flags. assert (0 <= Z.land fl 128 < 2 ^ 32) by (apply land_lt32; lia).
  apply lor_lt32; lia.
Qed.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance close_it_end_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition old_base (fl : Z) (ob : ptr) : iProp Σ :=
  ⌜ob = null⌝ ∨ ∃ bb breg, ⌜ob = mkPtr bb (Obj bb) /\ r_kind breg = Heap /\ 0 < bb /\ bb < 2 ^ 64 /\
                            Z.land fl io_user_buf = 0⌝ ∗ live bb breg.
Definition setb_spec_with (B : Z -> Z -> ptr -> iProp Σ) : Prop := forall fr fb freg fl ob oe nb ne a Φ,
  call_frame glibc__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base ob -∗ pcell fb off_buf_end oe -∗
  B fb fl ob -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Definition setb_spec : Prop := setb_spec_with (fun _ => old_base).
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}.


(** Expressions use the caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The setb rule consumes the supplied buffer resource when replacing its
    pointers. Heap callers supply a buffer lifetime; short-buffer callers
    supply only the pointer shape and USER_BUF fact. *)
Context (B : Z -> Z -> ptr -> iProp Σ) (Hsetb_spec : setb_spec_with w0 registry ge B).

(** The final blocks reset the stream even when descriptor close failed.
    They return that failure if present; otherwise they return the saved
    pending-output result. Buffer disposal follows the supplied setb contract. *)
Lemma wp_close_it_L223_with e from p3 k fb freg fl fd off ob oe p8 p16 p24 p32 p40 p48 Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr fp) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_fileno) (Obj fb))) ->
  lookup (TAtom "chk1") e = Some (WPtr fp) ->
  lookup (TAtom "v2") e = Some (WInt 0) -> lookup (TAtom "pr.3") e = Some (WInt p3) ->
  lookup (TAtom "v220") e = Some (WInt k) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> 0 <= p3 < 2 ^ 32 -> k = 0 \/ k = 2 ^ 32 - 1 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ icell fb off_offset off -∗
  pcell fb 8 p8 -∗ pcell fb 16 p16 -∗ pcell fb 24 p24 -∗ pcell fb 32 p32 -∗ pcell fb 40 p40 -∗ pcell fb 48 p48 -∗
  pcell fb off_buf_base ob -∗ pcell fb off_buf_end oe -∗ B fb fl ob -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (closed_flags fl) -∗ int_cell fb off_fileno (2 ^ 32 - 1) -∗
     icell fb off_offset (2 ^ 64 - 1) -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     Φ (Ret (WInt (if k =? 0 then p3 else k)))) -∗
  WP (ERun (mkFrame glibc__IO_file_close_maybe_unlink e [] None (Enter (TAtom "L223") (Some from))) : sexpr)
    {{ Φ }}.
Proof using Type*.
  intros fp Hv0 Hc0 Hc1 Hv2 Hp3 Hv220 Hfb Hfal Hfend Hfreg Hfl Hp3r Hk. subst fp.
  iIntros "Hl Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe Hob HK".
  unfold file_size in Hfend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl". step.
  iApply wp_call_bind; [vx | exact Hsetb | reflexivity |]. iNext.
  iApply (Hsetb_spec with "Hl Hfl Hbb Hbe Hob"); try close_side.
  iNext. iIntros "Hl Hfl Hbb Hbe". resume.
  step. check "Hl". store "Hl" "H24". step. check "Hl". store "Hl" "H8". step. check "Hl". store "Hl" "H16".
  step. step. check "Hl". store "Hl" "H40". check "Hl". store "Hl" "H32". step. check "Hl". store "Hl" "H48".
  step. branch_as true.
  (* L279: the flags, descriptor and offset of a closed stream. *)
  pose proof (setb_flags_range fl 0 Hfl) as Hsf. iDestruct "Hfl" as "[_ Hfl]".
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. check "Hl".
  assert (E : Z.lor (Z.land (setb_flags fl (0 mod 2 ^ 32) mod 2 ^ 32) (128 mod 2 ^ 32) mod 2 ^ 32)
                (4222428172 mod 2 ^ 32) mod 2 ^ 32 = closed_flags fl).
  { change (0 mod 2 ^ 32) with 0. change (128 mod 2 ^ 32) with 128. change (4222428172 mod 2 ^ 32) with 4222428172.
    rewrite (Z.mod_small (setb_flags fl 0)); [|exact Hsf].
    unfold setb_flags, io_user_buf. cbn [Z.eqb]. rewrite land_lor1_128.
    rewrite (Z.mod_small (Z.land fl 128)); [|apply land_lt32; lia].
    apply Z.mod_small, closed_flags_range; lia. }
  store_int "Hl" "Hfl". iEval (rewrite E) in "Hfl". clear E.
  iDestruct "Hfd" as "[_ Hfd]". step. check "Hl". store_int "Hl" "Hfd". step. check "Hl". store_long "Hl" "Hoff".
  iAssert (int_cell fb off_flags (closed_flags fl)) with "[Hfl]" as "Hfl".
  { iSplit; [iPureIntro; apply closed_flags_range; lia | iExact "Hfl"]. }
  iAssert (int_cell fb off_fileno (2 ^ 32 - 1)) with "[Hfd]" as "Hfd"; [iSplit; [iPureIntro; lia | iExact "Hfd"]|].
  iSpecialize ("HK" with "Hl Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe").
  destruct Hk as [-> | ->].
  - branch. step. step. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    rewrite (Z.mod_small p3 (2 ^ 32)); [|lia]. rewrite (Z.mod_small p3 (2 ^ 32)); [|lia]. iExact "HK".
  - branch. step. iApply wp_ret; [reflexivity | vx |]. iNext. iExact "HK".
Qed.

End rules.

Section legacy.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}.
(** Existing heap-buffer callers retain their original resource contract. *)
Definition wp_close_it_L223 (Hsetb_spec : setb_spec w0 registry ge) :=
  wp_close_it_L223_with (fun _ => old_base) Hsetb_spec.
End legacy.
