(** The last blocks of `c: _IO_file_close_maybe_unlink(fp, 0)`
    (LibioCloseItCode.v), from `c: L223`, the descriptor closed:
    `c: _IO_setb(fp, NULL, NULL, 0)`, the read and write pointers null,
    and the flags, descriptor and offset of a closed stream
    ([wp_close_it_L223]). LibioCloseIt.v runs the blocks before. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioCloseItCode FileInv LibioLogic
  SysWrappers LibioSetb LibioCloseSteps.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The flags of a closed stream: `c: _IO_LINKED` kept, the rest
    `c: _IO_MAGIC | CLOSED_FILEBUF_FLAGS` (`c: 0xFBAD240C`). *)
Definition closed_flags (fl : Z) : Z := Z.lor (Z.land fl 128) 4222428172.

(** `c: _IO_setb`'s `c: _IO_USER_BUF` bit leaves `c: _IO_LINKED` alone. *)
Lemma land_lor1_128 fl : Z.land (Z.lor fl 1) 128 = Z.land fl 128.
Proof. rewrite Z.land_lor_distr_l. change (Z.land 1 128) with 0. apply Z.lor_0_r. Qed.

(** [closed_flags] is an `c: int`'s bits. *)
Lemma closed_flags_range fl : 0 <= fl -> 0 <= closed_flags fl < 2 ^ 32.
Proof.
  intros H. unfold closed_flags. assert (0 <= Z.land fl 128 < 2 ^ 32) by (apply land_lt32; lia).
  apply lor_lt32; lia.
Qed.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioCloseItEndOn (R : Runtime) (LG0 : LogicSig R).
Module CS := LibioCloseStepsOn R LG0.
Import CS CS.SW CS.SW.FI.ML CS.SW.FI.LG CS.SW.FI.L CS.SW.OW CS.SW.FI CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hsetb : find_fn ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance close_it_end_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [old_base] fl ob, as LibioSetb.v's: the old base ob is null, or a
    live heap buffer the stream owns, `c: _IO_USER_BUF` clear in fl. *)
Definition old_base (fl : Z) (ob : ptr) : iProp Σ :=
  ⌜ob = null⌝ ∨ ∃ bb breg, ⌜ob = mkPtr bb (Obj bb) /\ r_kind breg = Heap /\ 0 < bb /\ bb < 2 ^ 64 /\
                            Z.land fl io_user_buf = 0⌝ ∗ live bb breg.

(** `c: _IO_setb`'s triple, LibioSetb.v's [wp_glibc__IO_setb]. *)
Definition setb_spec : Prop := forall fr fb freg fl ob oe nb ne a Φ,
  call_frame glibc__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base ob -∗ pcell fb off_buf_end oe -∗
  old_base fl ob -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

(** [setb_spec] holds. *)
Context (Hsetb_spec : setb_spec).

(** Block `c: L223` of `c: _IO_file_close_maybe_unlink(fp, 0)` to its
    return, `c: pr.3` the result of writing pending output and k that
    of `c: __close`: the stream's buffer is given up ([old_base]),
    its read and write pointers and buffer are null, `c: _flags` is
    [closed_flags], `c: _fileno` and `c: _offset` -1, and the result is
    k if not 0, else `c: pr.3`. *)
Lemma wp_close_it_L223 e from p3 k fb freg fl fd off ob oe p8 p16 p24 p32 p40 p48 Φ :
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
  pcell fb off_buf_base ob -∗ pcell fb off_buf_end oe -∗ old_base fl ob -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (closed_flags fl) -∗ int_cell fb off_fileno (2 ^ 32 - 1) -∗
     icell fb off_offset (2 ^ 64 - 1) -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     Φ (Ret (WInt (if k =? 0 then p3 else k)))) -∗
  WP (ERun (mkFrame glibc__IO_file_close_maybe_unlink e [] None (Enter (TAtom "L223") (Some from))) : sexpr)
    {{ Φ }}.
Proof.
  intros fp Hv0 Hc0 Hc1 Hv2 Hp3 Hv220 Hfb Hfal Hfend Hfreg Hfl Hp3r Hk. subst fp.
  iIntros "Hl Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe Hob HK".
  unfold file_size in Hfend.
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl". fs.
  iApply wp_call_bind; [vx | exact Hsetb | reflexivity |]. iNext.
  iApply (Hsetb_spec with "Hl Hfl Hbb Hbe Hob"); try side.
  iNext. iIntros "Hl Hfl Hbb Hbe". resume.
  fs. fchk "Hl". fstp "Hl" "H24". fs. fchk "Hl". fstp "Hl" "H8". fs. fchk "Hl". fstp "Hl" "H16".
  fs. fs. fchk "Hl". fstp "Hl" "H40". fchk "Hl". fstp "Hl" "H32". fs. fchk "Hl". fstp "Hl" "H48".
  fs. fbrv true.
  (* L279: the flags, descriptor and offset of a closed stream. *)
  pose proof (setb_flags_range fl 0 Hfl) as Hsf. iDestruct "Hfl" as "[_ Hfl]".
  fs. fchk "Hl". fldi "Hl" "Hfl". fs. fs. fchk "Hl".
  assert (E : Z.lor (Z.land (setb_flags fl (0 mod 2 ^ 32) mod 2 ^ 32) (128 mod 2 ^ 32) mod 2 ^ 32)
                (4222428172 mod 2 ^ 32) mod 2 ^ 32 = closed_flags fl).
  { change (0 mod 2 ^ 32) with 0. change (128 mod 2 ^ 32) with 128. change (4222428172 mod 2 ^ 32) with 4222428172.
    rewrite (Z.mod_small (setb_flags fl 0)); [|exact Hsf].
    unfold setb_flags, io_user_buf. cbn [Z.eqb]. rewrite land_lor1_128.
    rewrite (Z.mod_small (Z.land fl 128)); [|apply land_lt32; lia].
    apply Z.mod_small, closed_flags_range; lia. }
  fsti "Hl" "Hfl". iEval (rewrite E) in "Hfl". clear E.
  iDestruct "Hfd" as "[_ Hfd]". fs. fchk "Hl". fsti "Hl" "Hfd". fs. fchk "Hl". fstl "Hl" "Hoff".
  iAssert (int_cell fb off_flags (closed_flags fl)) with "[Hfl]" as "Hfl".
  { iSplit; [iPureIntro; apply closed_flags_range; lia | iExact "Hfl"]. }
  iAssert (int_cell fb off_fileno (2 ^ 32 - 1)) with "[Hfd]" as "Hfd"; [iSplit; [iPureIntro; lia | iExact "Hfd"]|].
  iSpecialize ("HK" with "Hl Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe").
  destruct Hk as [-> | ->].
  - fbr. fs. fs. fs. iApply wp_ret; [reflexivity | vx |]. iNext.
    rewrite (Z.mod_small p3 (2 ^ 32)); [|lia]. rewrite (Z.mod_small p3 (2 ^ 32)); [|lia]. iExact "HK".
  - fbr. fs. iApply wp_ret; [reflexivity | vx |]. iNext. iExact "HK".
Qed.

End rules.
End LibioCloseItEndOn.
