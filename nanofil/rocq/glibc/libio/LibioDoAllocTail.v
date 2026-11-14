From Glibc Require Import GlibcProgram.
(** This file proves the tail blocks of `c: _IO_file_doallocate` (LibioDoAllocBase.v
    describes the function). Block `c: L7` calls `c: malloc` for the
    buffer and installs it with `c: _IO_setb(fp, p, p + size, 1)`;
    block `c: L28` reads `c: st_blksize` and picks the size; block
    `c: L33` sets `c: _IO_LINE_BUF` first.

    The model's `c: malloc` always returns a fresh object, so the
    function's `c: EOF` return for a failed allocation is not reached.
    The `c: malloc` call is the hypothesis [Hmalloc], which
    stdlib/AllocLogic.v's [wp_glibc_malloc] discharges over
    `c: tcache_idle` as Mres. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  LibioSetb LibioDoAllocBase.
From Glibc Require FileInv LibioDoAllocBase LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioDoAllocBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules_values.
Definition da_L7 : block := Eval vm_compute in
  match find_block (TAtom "L7") (fn_blocks glibc__IO_file_doallocate) with
  | Some b => b | None => mkBlock (TAtom "L7") [] [] JRetVoid end.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The registry holds the OS contracts, and the genv's externals
    are the system calls. *)
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
(** The genv defines `c: __gnu_dev_major`. *)
Context `{Hmaj : !Defines ge "__gnu_dev_major" glibc___gnu_dev_major}.
(** The genv defines `c: __isatty_nostatus`. *)
Context `{Hisatty : !Defines ge "__isatty_nostatus" glibc___isatty_nostatus}.

(** The genv defines `c: _IO_setb`. *)
Context `{Hsetbf : !Defines ge "__GI__IO_setb" glibc__IO_setb}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_setb` on a stream with no buffer, as LibioSetb.v's
    [wp_glibc__IO_setb] proves it with the old buffer null. *)
Context (Hsetb_null : forall fr fb freg fl oe nb ne a Φ,
  call_frame glibc__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Φ }}).
(** The allocator's state, which `c: malloc` takes and gives back. *)
Context (Mres : iProp Σ).
(** `c: malloc(n)` returns a fresh object of at least n zero bytes,
    as stdlib/AllocLogic.v's [wp_glibc_malloc] proves over
    `c: tcache_idle`, taken here as Mres. *)
Context (Hmalloc : forall f e ls lab d v rest j n Φ,
  arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  Mres -∗
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ -∗
       obj base (heap_req 16 n) -∗ Mres -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j))
             : language.expr (nanofil_lang registry ge)) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j))
        : language.expr (nanofil_lang registry ge)) {{ Φ }}).


(** Block `c: L7` of `c: _IO_file_doallocate`. *)

(** Block `c: L7`'s instructions, from `c: malloc(size)` to
    `c: _IO_setb(fp, p, p + size, 1)` and the return of 1. *)
Lemma wp_doalloc_malloc fb freg fl oe sz e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 < sz <= 8192 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  ▷ (∀ bb, ⌜0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     live fb freg -∗ int_cell fb off_flags (setb_flags fl 1) -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ Mres -∗ Φ (Ret (WInt 1))) -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate (put (TAtom "pr.2") (WInt sz) e) [] None
              (Exec (TAtom "L7") (b_insts da_L7) (b_jump da_L7))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hsz Hv0. iIntros "Hl Hfl Hb He HM HK". cbn [da_L7 b_insts b_jump].
  iApply (Hmalloc _ _ _ _ _ _ _ _ sz with "HM"); [cbn; rewrite Z.mod_small; [reflexivity | lia] | lia |].
  iNext. iIntros (base (Hb0 & Hb16 & Hbext)) "Ho HM".
  assert (Hx : sz <= req_extent (heap_req 16 sz)) by (cbn; Z.div_mod_to_equations; lia).
  step. step. step. branch_as true. step. step. norm.
  iApply wp_call_bind; [vx | exact Hsetbf | reflexivity |]. iNext.
  iApply (Hsetb_null _ fb freg fl oe _ _ 1 with "Hl Hfl Hb He"); [reflexivity | lia | lia | lia | lia | lia |].
  iNext. iIntros "Hl Hfl Hb He". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply wp_ret; [reflexivity | vx |]. iNext.
  rewrite obj_zero_block; [|lia]. iDestruct "Ho" as "(Hbl & Hxs & Hcs)".
  iDestruct (bytes_take_drop base 0 _ (Z.to_nat sz) with "Hxs") as "[Hxs _]"; [rewrite length_replicate; lia|].
  iDestruct (auxes_take_drop base 0 _ (Z.to_nat sz) with "Hcs") as "[Hcs _]"; [rewrite length_replicate; lia|].
  rewrite !take_replicate. replace (Nat.min (Z.to_nat sz) (Z.to_nat (req_extent (heap_req 16 sz)))) with (Z.to_nat sz) by lia.
  iApply ("HK" with "[%] Hl Hfl Hb He [Hbl Hxs Hcs] HM"); [lia|].
  iExists _. iFrame "Hbl Hxs Hcs". iPureIntro. cbn in Hbext, Hx |- *.
  split; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

(** Block `c: L7`, entered from `c: L59` with the size the stat gave or
    from `c: L66` or `c: L13` with 8192. *)
Lemma wp_doalloc_L7 fb freg fl oe sz from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 < sz <= 8192 ->
  (from = TAtom "L59" /\ (exists v, lookup (TAtom "v73") e = Some (WInt v) /\ v mod 2 ^ 64 = sz)) \/
  ((from = TAtom "L66" \/ from = TAtom "L13") /\ sz = 8192) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  ▷ (∀ bb, ⌜0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     live fb freg -∗ int_cell fb off_flags (setb_flags fl 1) -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ Mres -∗ Φ (Ret (WInt 1))) -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L7") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hsz Hfrom Hv0. iIntros "Hl Hfl Hb He HM HK".
  destruct Hfrom as [[-> (v & Hv & Hvs)] | [[-> | ->] ->]]; step;
    [rewrite Hvs | change (8192 mod 2 ^ 64) with 8192 | change (8192 mod 2 ^ 64) with 8192].
  all: iApply (wp_doalloc_malloc with "Hl Hfl Hb He HM HK"); try libio_side.
Qed.

(** Block `c: L28`, which takes `c: st_blksize` as the size when it is
    between 0 and 8192, and 8192 otherwise. *)
Lemma wp_doalloc_L28 fb freg fl oe sb sreg bs3 from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < sb -> sb mod 16 = 0 -> sb + 144 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> length bs3 = 8%nat ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  lookup (TAtom "chk4") e = Some (WPtr (mkPtr (sb + 24) (Obj sb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  live sb sreg -∗ bytes sb 56 bs3 -∗
  ▷ (∀ bb sz, ⌜0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     live fb freg -∗ int_cell fb off_flags (setb_flags fl 1) -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ Mres -∗ Φ (Ret (WInt 1))) -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L28") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hsb Hsal Hsend Hsreg Hl3 Hv0 Hv4 Hc4.
  iIntros "Hl Hfl Hb He HM Hsl Hb3 HK".
  step. step. norm. check "Hsl".
  iApply (wp_raw_load_bytes8 with "Hsl Hb3"); [reflexivity | vx | exact Hl3 | reflexivity | ar |].
  iNext. iIntros "Hsl Hb3". step. brk E1.
  - step. step. norm.
    iApply (wp_raw_load_bytes8 with "Hsl Hb3"); [reflexivity | vx | exact Hl3 | reflexivity | ar |].
    iNext. iIntros "Hsl Hb3". step. step. step. brk E2.
    + step. step. norm.
      iApply (wp_raw_load_bytes8 with "Hsl Hb3"); [reflexivity | vx | exact Hl3 | reflexivity | ar |].
      iNext. iIntros "Hsl Hb3". step. pose proof (blksize_range _ E1 E2) as Hx.
      iApply (wp_doalloc_L7 _ _ _ _ (of_bytes bs3 mod 2 ^ 64) with "Hl Hfl Hb He HM"); try libio_side.
      * left. split; [reflexivity|]. eexists. split; [lk_prove | reflexivity].
      * iNext. iIntros (bb Hbb). iApply "HK". iPureIntro. lia.
    + iApply (wp_doalloc_L7 _ _ _ _ 8192 with "Hl Hfl Hb He HM"); try libio_side.
      * right. auto.
      * iNext. iIntros (bb Hbb). iApply "HK". iPureIntro. lia.
  - step. branch. iApply (wp_doalloc_L7 _ _ _ _ 8192 with "Hl Hfl Hb He HM"); try libio_side.
    + right. auto.
    + iNext. iIntros (bb Hbb). iApply "HK". iPureIntro. lia.
Qed.

(** Block `c: L33`, which sets `c: _IO_LINE_BUF` and goes on to
    `c: L28`. *)
Lemma wp_doalloc_L33 fb freg fl oe sb sreg bs3 from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < sb -> sb mod 16 = 0 -> sb + 144 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> length bs3 = 8%nat ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_fileno) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  lookup (TAtom "chk4") e = Some (WPtr (mkPtr (sb + 24) (Obj sb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  live sb sreg -∗ bytes sb 56 bs3 -∗
  ▷ (∀ bb sz, ⌜0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     live fb freg -∗ int_cell fb off_flags (setb_flags (Z.lor fl io_line_buf) 1) -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ Mres -∗ Φ (Ret (WInt 1))) -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L33") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hsb Hsal Hsend Hsreg Hl3 Hv0 Hc0 Hv4 Hc4.
  iIntros "Hl [%Hfl Hflb] Hb He HM Hsl Hb3 HK". unfold file_size in Hend.
  step. check "Hl". load_s32_group "Hl Hflb". step. check "Hl".
  store_word "Hl Hflb" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hflb". step.
  iApply (wp_doalloc_L28 _ _ (Z.lor fl io_line_buf) with "Hl [Hflb] Hb He HM Hsl Hb3 HK"); try libio_side.
  assert (Hlo : 0 <= Z.lor fl 512 < 2 ^ 32) by (apply lor_lt32; lia).
  iSplit; [iPureIntro; exact Hlo|]. unfold int_bytes, io_line_buf.
  change (512 mod 2 ^ 32) with 512. rewrite (Z.mod_small fl); [|lia]. rewrite (Z.mod_small (Z.lor fl 512)); [|lia].
  iExact "Hflb".
Qed.

End rules.
