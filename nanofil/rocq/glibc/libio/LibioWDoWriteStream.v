(** The wide flush `c: _IO_wdo_write` calls the narrow
    `c: _IO_new_do_write` up to once before its loop and once on every
    pass. The two rules of [LibioWDoWriteNarrow](LibioWDoWriteNarrow.v)
    take the stream's fields one cell at a time and need at least one
    byte to send. The flush holds a whole wide stream instead, and the
    count it passes is often zero. This file proves the call for a wide
    stream as a whole and for any count, so that the flush can treat the
    narrow write as one step that hands back a wide stream with the same
    lock. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics GlibcSymFunc.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysCode FileInv FileIdle LibioLogic LibioReadCode
  LibioDoWriteCode LibioDoWrite LibioOverflowBase LibioOverflowShortWrite LibioXsputnHeap LibioWIdle LibioWDoWriteNarrow SysWrappers.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Local Abbreviation objp b := (mkPtr b (Obj b)).

(* Rewinding restores whole FILE cells. Framing them does not need to search
   the byte and capability ownership inside each cell. *)
Local Typeclasses Opaque pcell icell bytes.

(** ## The stream after a write

    After a write that sent at least one byte, glibc points every read
    and write pointer at the start of the narrow buffer and the write
    end at its end. It may set the error bit, and it updates the byte
    count and the file offset. Every other field keeps its value. *)

(** The function [rewound] st fl tw off gives the fields after such a
    write: the flags fl, the twelve pointers rewound to the buffer that
    st names, the byte count tw and the offset off. *)
Definition rewound (st : fstate) (fl tw off : Z) : fstate :=
  let b := fs_ptr st 6 in let e := fs_ptr st 7 in
  mkFstate fl ([b; b; b; b; b; e; b; e] ++ drop 8 (fs_ptrs st)) (fs_fileno st) (fs_flags2 st)
    (fs_old_offset st) (fs_column st) (fs_lock st) off (fs_codecvt st) (fs_wide st) (fs_freeres_list st)
    (fs_freeres_buf st) (fs_mode st) tw (fs_vtable st).

(** A rewound wide stream is still a wide stream between calls, as
    long as it has a narrow buffer and the write added at most the error
    bit to its flags. Rewinding cannot leave pending bytes behind, so
    the putting bit may stay as it was. *)
Lemma wide_ok_rewound ge vb fp fd fb freg st nb wd w tw tm fl n off :
  wide_file_ok ge vb fp fd fb freg st nb wd w tw tm -> length (fs_ptrs st) = 12%nat ->
  (nb = NbShort \/ exists bb sz, nb = NbHeap bb sz) ->
  (fl = fs_flags st \/ fl = Z.lor (fs_flags st) io_err_seen) -> 0 <= fl < 2 ^ 32 ->
  wide_file_ok ge vb fp fd fb freg (rewound st fl n off) nb wd w tw tm.
Proof.
  intros H Hlen Hnb Hfl Hr.
  assert (E : forall m, Z.land io_err_seen m = 0 -> has fl m = has (fs_flags st) m)
    by (intros m Hm; destruct Hfl as [-> | ->]; [reflexivity | apply has_err_other, Hm]).
  assert (Mg : Z.land fl 4294901760 = Z.land (fs_flags st) 4294901760)
    by (destruct Hfl as [-> | ->]; [reflexivity | apply land_lor_const; reflexivity]).
  destruct H as (Hfp & Hal & Hfb & Hend & Hfr & F & I & Hm & Hvt & B & S & U & Hwd & Hcv & Htw & Htm & Hnw).
  unfold wide_file_ok, rewound, wflags_ok, widle_ok, wshort_ok, with_mode0, fs_ptr in *.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps;
    try discriminate Hlen.
  cbn [fs_flags fs_flags2 fs_ptrs fs_fileno fs_mode fs_lock fs_column fs_vtable fs_wide fs_codecvt nth drop app] in *.
  rewrite Mg !E; try reflexivity.
  destruct Hnb as [-> | (bb & sz & ->)]; cbn [buf_ptrs_ok take nth] in B |- *;
    destruct B as (H6 & H7 & Hall); subst p6 p7;
    repeat (apply Forall_cons_1 in Hall; destruct Hall as [? Hall]);
    split_and!; try solve [assumption | reflexivity | lia | tauto]; try (repeat constructor; cbn; lia).
Qed.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__GI___write" glibc___libc_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write).
Context (fd vb fb : Z) (vr freg : region) (eb wd : Z) (w : wbuf) (tw tm : ptr).
Context (Hfd : In fd (ow_fds w0)) (Herr : ow_errno w0 = Some (objp eb)).
Local Abbreviation ok st nb := (wide_file_ok ge vb (objp fb) fd fb freg st nb wd w tw tm).

(** ## A write from a heap buffer

    A stream whose narrow buffer is on the heap writes either the
    buffer's own bytes or the bytes of a separate array. *)

(** This rule sends the n bytes xs from offset o of the object db on a
    wide stream with the heap buffer bb of sz bytes. When db is bb, the
    buffer's own life serves for the write. The stream comes back with
    the same lock whether the write succeeded or failed. *)
Lemma wp_wnarrow_heap fr st bb sz breg db dreg o xs Φ :
  let n := Z.of_nat (length xs) in
  call_frame glibc__IO_new_do_write [WPtr (objp fb); WPtr (mkPtr (db + o) (Obj db)); WInt n] = Some fr ->
  ok st (NbHeap bb sz) -> 0 < bb -> 0 < sz -> bb + sz <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < db -> 0 <= o -> db + o + n <= r_end dreg -> r_end dreg <= 2 ^ 63 -> (db = bb -> dreg = breg) ->
  Forall (fun x => 0 <= x < 256) xs ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ errno_any eb -∗ live fb freg -∗ file_fields fb st -∗
  live bb breg -∗ (if decide (db = bb) then True else live db dreg) -∗ bytes db o xs -∗
  ▷ (∀ r st', ⌜(r = 0 \/ r = 2 ^ 32 - 1) /\ ok st' (NbHeap bb sz) /\ fs_lock st' = fs_lock st⌝ -∗
     errno_any eb -∗ live fb freg -∗ file_fields fb st' -∗ live bb breg -∗
     (if decide (db = bb) then True else live db dreg) -∗ bytes db o xs -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros n Hfr H Hbb Hsz Hbe Hbr Hdb Ho Hde Hdr Hdeq Hxs. iIntros "#Hvt #Hwvt Herr Hl Hfields Hbl Hdl Hxs HK".
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  { rewrite Hn0 in Hfr. iApply (wp_glibc__IO_new_do_write_zero with "[-]"); [exact Hfr|]. iNext.
    iApply ("HK" $! 0 st with "[%] Herr Hl Hfields Hbl Hdl Hxs"). split; [left; reflexivity|]. split; [exact H|reflexivity]. }
  pose proof H as (_ & Hal & Hfb & Hend & Hfreg & F & I & Hm & Hvtb & B & S & U & _).
  iDestruct "Hfields" as "(%L & Hfl & Hps & Hfdc & Hfl2 & Hold & %Lc & Hcol & Hlk & Hoff & Hcv & Hwd & Hfrl & Hfrb & Hmd & Htw & Hvtp)".
  pose proof I as (_ & Hfdeq & _ & _ & _ & _ & Ea & Eb & _ & _ & _ & Happ & _ & Hf2 & _ & Hcol0 & _).
  pose proof S as (_ & _ & Ec & Ed). pose proof B as (H6 & H7 & Hall).
  unfold with_mode0, fs_ptr in *. cbn [fs_flags fs_flags2 fs_fileno fs_column fs_ptrs] in *.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps;
    try discriminate L.
  cbn [nth take] in Ea, Eb, Ec, Ed, H6, H7, Hall. clear Ea. subst p6 p7 p3 p2 p1.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  iEval (rewrite -{1}(take_drop 2 (fs_column st)) Hcol0 bytes_app) in "Hcol". iDestruct "Hcol" as "[Hcol Hct]".
  rewrite Hm Hvtb Hfdeq. iDestruct "Hfl2" as "[%Hf2r Hfl2]".
  iApply (wp_wide_do_write_heap Hreg Hext with "Hvt Hwvt Hl Hfl [$Hfl2 //] Hfdc Htw Hoff Hbl Hdl Hxs Herr P0 P1 P2 P3 P4 P5 P6 P7 Hcol Hmd Hvtp");
    try first [exact Hfr | assumption | lia | apply has_false_land, Happ | reflexivity | cbn; lia].
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hfl Hfl2 Hfdc Htw Hoff Hbl Hdl Hxs Herr P0 P1 P2 P3 P4 P5 P6 P7 Hcol Hmd Hvtp".
  iApply ("HK" $! _ (rewound st fl' tw' off') with "[%] Herr Hl [-Hbl Hdl Hxs] Hbl Hdl Hxs").
  { split; [match goal with |- context [if ?c then _ else _] => destruct c end; [left|right]; reflexivity|]. split; [|reflexivity].
    apply wide_ok_rewound; try assumption; [rewrite Hps; reflexivity|right; eauto|].
    destruct Hpost as [[_ ->] | [_ ->]]; [left|right]; reflexivity. }
  unfold rewound, file_fields, fs_ptr. rewrite Hps. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
    fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable drop app nth big_opL].
  rewrite Hm Hvtb Hfdeq. iFrame. iSplit; [done|]. iSplit; [done|].
  iEval (rewrite -{1}(take_drop 2 (fs_column st)) Hcol0 bytes_app). iFrame.
Qed.

(** ## A write from the short buffer

    A stream that was unbuffered when it became wide keeps a one-byte
    buffer inside the stream object. The flush never converts into it,
    so the bytes always come from a separate array. *)

(** This rule sends the n bytes xs from offset o of the object db on a
    wide stream whose narrow buffer is the one-byte buffer. *)
Lemma wp_wnarrow_short fr st db dreg o xs Φ :
  let n := Z.of_nat (length xs) in
  call_frame glibc__IO_new_do_write [WPtr (objp fb); WPtr (mkPtr (db + o) (Obj db)); WInt n] = Some fr ->
  ok st NbShort -> 0 < db -> 0 <= o -> db + o + n <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ errno_any eb -∗ live fb freg -∗ file_fields fb st -∗
  live db dreg -∗ bytes db o xs -∗
  ▷ (∀ r st', ⌜(r = 0 \/ r = 2 ^ 32 - 1) /\ ok st' NbShort /\ fs_lock st' = fs_lock st⌝ -∗
     errno_any eb -∗ live fb freg -∗ file_fields fb st' -∗ live db dreg -∗ bytes db o xs -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros n Hfr H Hdb Ho Hde Hdr Hxs. iIntros "#Hvt #Hwvt Herr Hl Hfields Hdl Hxs HK".
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  { rewrite Hn0 in Hfr. iApply (wp_glibc__IO_new_do_write_zero with "[-]"); [exact Hfr|]. iNext.
    iApply ("HK" $! 0 st with "[%] Herr Hl Hfields Hdl Hxs"). split; [left; reflexivity|]. split; [exact H|reflexivity]. }
  pose proof H as (_ & Hal & Hfb & Hend & Hfreg & F & I & Hm & Hvtb & B & S & U & _).
  iDestruct "Hfields" as "(%L & Hfl & Hps & Hfdc & Hfl2 & Hold & %Lc & Hcol & Hlk & Hoff & Hcv & Hwd & Hfrl & Hfrb & Hmd & Htw & Hvtp)".
  pose proof I as (_ & Hfdeq & _ & _ & _ & _ & Ea & Eb & _ & _ & _ & Happ & _ & Hf2 & _ & Hcol0 & _).
  pose proof S as (_ & _ & Ec & Ed). pose proof B as (H6 & H7 & Hall).
  unfold with_mode0, fs_ptr in *. cbn [fs_flags fs_flags2 fs_fileno fs_column fs_ptrs] in *.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps;
    try discriminate L.
  cbn [nth take] in Ea, Eb, Ec, Ed, H6, H7, Hall. clear Ea Ec. subst p6 p7 p3 p1.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  iEval (rewrite -{1}(take_drop 2 (fs_column st)) Hcol0 bytes_app) in "Hcol". iDestruct "Hcol" as "[Hcol Hct]".
  rewrite Hm Hvtb Hfdeq. iDestruct "Hfl2" as "[%Hf2r Hfl2]".
  iApply (wp_wide_do_write_short Hreg Hext with "Hvt Hwvt Hl Hfl [$Hfl2 //] Hfdc Htw Hoff Hdl Hxs Herr P0 P1 P2 P3 P4 P5 P6 P7 Hcol Hmd Hvtp");
    try first [exact Hfr | assumption | lia | apply has_false_land, Happ | reflexivity | cbn; lia].
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hfl Hfl2 Hfdc Htw Hoff Hdl Hxs Herr P0 P1 P2 P3 P4 P5 P6 P7 Hcol Hmd Hvtp".
  iApply ("HK" $! _ (rewound st fl' tw' off') with "[%] Herr Hl [-Hdl Hxs] Hdl Hxs").
  { split; [match goal with |- context [if ?c then _ else _] => destruct c end; [left|right]; reflexivity|].
    split; [|reflexivity].
    apply wide_ok_rewound; try assumption; [rewrite Hps; reflexivity|left; reflexivity|].
    destruct Hpost as [[_ ->] | [_ ->]]; [left|right]; reflexivity. }
  unfold rewound, file_fields, fs_ptr. rewrite Hps. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
    fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable drop app nth big_opL].
  rewrite Hm Hvtb Hfdeq. iFrame. iSplit; [done|]. iSplit; [done|].
  iEval (rewrite -{1}(take_drop 2 (fs_column st)) Hcol0 bytes_app). iFrame.
Qed.

End rules.
