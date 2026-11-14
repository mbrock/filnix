From Glibc Require Import GlibcProgram.
(** What the newline of `c: puts(s)` (LibioPutsCode.v,
    libio/ioputs.c) needs of a stream's narrow buffer: the bounds every
    pointer into it has ([wp_buf_fit]), a load of a read or write
    pointer from the stream ([wp_load_bufptr]), and the store of
    `c: '\n'` through `c: _IO_write_ptr` when it is below
    `c: _IO_write_end` ([wp_buf_putc]).

    Each is proved by cases on the buffer (FileInv.v's [nbuf]): with no
    buffer every pointer is null, so the write pointer is never below
    the end; an unbuffered stream's one byte is `c: _shortbuf`, inside
    the stream at offset 131, among the 8 bytes at 128; a heap buffer's
    bytes are [buf_own]'s. LibioPutsNl.v walks the block that uses
    them. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString LibioGenCode LibioXsputnCode LibioPutsInv LibioPutsLock LibioPutsUnlock LibioPutsCall LibioPutsMode.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** One byte's [bytes] is its [ibyte]. *)
Lemma bytes_one `{!gen_heapGS piece pval Σ} b o x : bytes b o [x] ⊣⊢ ibyte b o x.
Proof. rewrite /bytes /ibyte byte_ps_cons. done. Qed.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Every pointer into the buffer nb of the stream fb, which lies below
    2^63, lies in the address space, before a step. *)
Lemma wp_buf_fit fb nb fr Φ :
  0 <= fb -> fb + 132 <= 2 ^ 63 ->
  buf_own nb -∗ (⌜forall p, in_buf fb nb p -> 0 <= ptr_addr p <= 2 ^ 63⌝ -∗ buf_own nb -∗ WP (ERun fr : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hend. iIntros "Hb HK". destruct nb as [| |bb sz|bb]; cbn [in_buf].
  - iApply ("HK" with "[%] Hb"). intros p ->. cbn. lia.
  - iApply ("HK" with "[%] Hb"). intros p [_ H]. lia.
  - iDestruct "Hb" as (breg xs Hbr) "[Hbl Hxs]".
    iApply (wp_live_fit1 with "Hbl"). iIntros ([Hb0 Hb48]) "Hbl".
    iApply ("HK" with "[%] [Hbl Hxs]"); [intros p [_ H]; lia|]. iExists breg, xs. iFrame. done.
  - iApply ("HK" with "[%] Hb"). intros p ->. cbn. lia.
Qed.

(** A load of the pointer x into the buffer nb of the stream fb, stored
    at offset o of fb: the life it names, the stream's or the heap
    buffer's, is the stream's or [buf_own]'s, and d is bound to x. *)
Lemma wp_load_bufptr f e ls l d off args rest j classes p fb freg o nb x Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj fb -> raw_address (ptr_addr p) off = fb + o -> (fb + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 -> in_buf fb nb x ->
  live fb freg -∗ pcell fb o x -∗ buf_own nb -∗
  ▷ (live fb freg -∗ pcell fb o x -∗ buf_own nb -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
       : sexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hr Hin. iIntros "Hl Hpc Hb HK".
  destruct nb as [| |bb sz|bb]; cbn [in_buf] in Hin.
  - subst x. iApply (wp_raw_load_null with "Hl Hpc"); [exact Hc | exact Hx | exact Hp | exact Ha
      | exact Hal |]. iNext. iIntros "Hl Hpc". iApply ("HK" with "Hl Hpc Hb").
  - destruct Hin as [Hxc _].
    iApply (wp_raw_load_pointer_self with "Hl Hpc");
      [exact Hc | exact Hx | exact Hp | exact Ha | exact Hal | exact Hr | exact Hxc |].
    iNext. iIntros "Hl Hpc". iApply ("HK" with "Hl Hpc Hb").
  - destruct Hin as [Hxc _]. iDestruct "Hb" as (breg xs Hbr) "[Hbl Hxs]".
    iApply (wp_raw_load_pointer with "Hl Hpc [Hbl]");
      [exact Hc | exact Hx | exact Hp | exact Ha | exact Hal | exact Hr | rewrite Hxc; iExact "Hbl" |].
    iNext. iIntros "Hl Hpc Hbl". iApply ("HK" with "Hl Hpc [Hbl Hxs]"). rewrite Hxc.
    iExists breg, xs. iFrame. done.
  - subst x. iApply (wp_raw_load_null with "Hl Hpc"); [exact Hc | exact Hx | exact Hp | exact Ha
      | exact Hal |]. iNext. iIntros "Hl Hpc". iApply ("HK" with "Hl Hpc Hb").
Qed.

(** The store of `c: '\n'` through the write pointer wp of the stream
    fb, below its write end we, both into its buffer nb: a write check
    of wp and a byte store, which change `c: _shortbuf` among the 8
    bytes at 128 or a byte of the heap buffer. *)
Lemma wp_buf_putc f e ls l d v rest j fb freg nb wp we col Φ :
  map2_option (value_x ge e) [P] [v] = Some [WPtr wp] ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  in_buf fb nb wp -> in_buf fb nb we -> ptr_addr wp < ptr_addr we -> length col = 8%nat ->
  live fb freg -∗ bytes fb off_column col -∗ buf_own nb -∗
  ▷ (∀ col', ⌜length col' = 8%nat⌝ -∗ live fb freg -∗ bytes fb off_column col' -∗ buf_own nb -∗
     WP (ERun (mkFrame f (put d (WPtr wp) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d A (Check 0 1 Write 1) [v] :: RawStore Wb 0 (Const 10) (Tmp d) :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hv Hfb Hfal Hfend Hfreg Hw He Hlt Hcl. unfold file_size in Hfend. iIntros "Hl Hcol Hb HK".
  destruct nb as [| |bb sz|bb]; cbn [in_buf] in Hw, He.
  - subst wp we. cbn in Hlt. lia.
  - (* `c: _shortbuf`, the byte at 131. *)
    destruct Hw as [Hwc Hwr]. destruct He as [_ Her].
    destruct col as [|c0 [|c1 [|c2 [|c3 cs]]]]; try discriminate Hcl.
    change (c0 :: c1 :: c2 :: c3 :: cs) with ([c0; c1; c2] ++ [c3] ++ cs)%list. rewrite !bytes_app bytes_one.
    iDestruct "Hcol" as "(H012 & H3 & Hcs)".
    iApply (wp_check with "Hl"); [reflexivity | exact Hv | exact Hwc | a2 | a2 | a2 |]. iNext. iIntros "Hl".
    iApply (wp_raw_store_byte with "Hl H3"); [reflexivity | vx | exact Hwc | cbn [length]; a2 | wi_store |].
    iNext. iIntros "Hl H3".
    iApply ("HK" $! ([c0; c1; c2] ++ [10 mod 256] ++ cs)%list with "[%] Hl [H012 H3 Hcs] Hb").
    + cbn in Hcl |- *. lia.
    + rewrite !bytes_app bytes_one. iFrame.
  - (* A byte of the heap buffer. *)
    destruct Hw as [Hwc Hwr]. destruct He as [_ Her].
    iDestruct "Hb" as (breg xs Hbr) "[Hbl Hxs]". destruct Hbr as (Hk & Hbend & Hbreg & Hsz & Hlen).
    set (i := Z.to_nat (ptr_addr wp - bb)).
    assert (Hi : Z.of_nat i = ptr_addr wp - bb) by (subst i; lia).
    destruct (lookup_lt_is_Some_2 xs i ltac:(subst i; lia)) as [x Hx].
    rewrite (bytes_take_drop bb 0 xs i); [|subst i; lia]. rewrite (drop_S xs x i Hx).
    change (x :: drop (S i) xs) with ([x] ++ drop (S i) xs)%list. rewrite bytes_app bytes_one.
    iDestruct "Hxs" as "(Ht & Hx & Hd)".
    iApply (wp_live_fit1 with "Hbl"). iIntros ([Hb0 Hb48]) "Hbl".
    iApply (wp_check with "Hbl"); [reflexivity | exact Hv | exact Hwc | a2 | a2 | a2 |]. iNext. iIntros "Hbl".
    iApply (wp_raw_store_byte with "Hbl Hx"); [reflexivity | vx | exact Hwc | a2 | wi_store |].
    iNext. iIntros "Hbl Hx".
    iApply ("HK" $! col with "[//] Hl Hcol [Ht Hx Hd Hbl]").
    iExists breg, (take i xs ++ [10 mod 256] ++ drop (S i) xs)%list. iFrame "Hbl".
    iSplitR; [iPureIntro; rewrite !length_app length_take length_drop; cbn [length]; split_and!; try assumption; lia|].
    rewrite (bytes_app bb 0 (take i xs)) (bytes_app _ _ [_]) length_take Nat.min_l; [|lia].
    rewrite bytes_one. iFrame.
  - subst wp we. cbn in Hlt. lia.
Qed.

End rules.
