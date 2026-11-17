(** The formatter appends bytes to a printf buffer, and every function
    that appends must find the buffer in a usable state and leave it in
    one. This module states that state once, as the invariant
    [printf_out], so the contracts of the appending functions can all
    say the same thing: the invariant holds before and after.

    A buffer has three pointers into one object, which this module
    calls the window's object. The bytes from `c: write_base` to
    `c: write_end` are the window. The window may lie in the buffer's
    own object, as the staging array of a file-backed buffer does, or
    in another object, such as a stream's buffer. Whoever flushes the
    buffer owns more than the window: a stream, a file descriptor. The
    invariant leaves that to a parameter, the backend. The backend may
    depend on where the window lies but not on how full it is, so a
    function that only appends keeps it unchanged. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From iris.program_logic Require Import language weakestpre.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Pieces Heap Language Logic MemLogic.
From Glibc Require Import GlibcProgram Fix OsWorld FileInv LibioPutsInv CStruct PrintfLayout.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** A window is an object with its region and three addresses in it:
    the base, the next free byte and the end. *)
Record pwin : Type := PWin {
  pw_obj : Z;
  pw_reg : region;
  pw_base : Z;
  pw_ptr : Z;
  pw_end : Z
}.

(** The window's place leaves out how full it is. *)
Definition pw_place (w : pwin) : Z * region * Z * Z := (pw_obj w, pw_reg w, pw_base w, pw_end w).

(** The addresses of a window are ordered and lie in its object. *)
Definition pwin_ok (w : pwin) : Prop :=
  0 < pw_obj w /\ pw_obj w <= pw_base w /\ pw_base w <= pw_ptr w /\ pw_ptr w <= pw_end w /\
  pw_end w <= r_end (pw_reg w) /\ r_end (pw_reg w) <= 2 ^ 63.

(** The function [pbuf_vals] lists the values of the five fields of a
    buffer whose window is w. *)
Definition pbuf_vals (w : pwin) (written mode : Z) : list (string * fval) :=
  [("write_base", VPtr (mkPtr (pw_base w) (Obj (pw_obj w))));
   ("write_ptr", VPtr (mkPtr (pw_ptr w) (Obj (pw_obj w))));
   ("write_end", VPtr (mkPtr (pw_end w) (Obj (pw_obj w))));
   ("written", VInt written); ("mode", VInt mode)].

(** The function [pbuf_ptrs] lists the values of the three pointers of
    a buffer whose window is w. *)
Definition pbuf_ptrs (w : pwin) : list (string * fval) :=
  [("write_base", VPtr (mkPtr (pw_base w) (Obj (pw_obj w))));
   ("write_ptr", VPtr (mkPtr (pw_ptr w) (Obj (pw_obj w))));
   ("write_end", VPtr (mkPtr (pw_end w) (Obj (pw_obj w))))].

(** A file-backed buffer has an array of its own for bytes that the
    stream cannot take yet. The window [stage_win] covers that array of
    the buffer at bb, and no byte of it is written. *)
Definition stage_win (bb : Z) (breg : region) : pwin :=
  PWin bb breg (bb + stage_off) (bb + stage_off) (bb + stage_end).

(** The window [data_win] covers the bytes of the object db from the
    offset bo to the offset eo, and no byte of it is written. *)
Definition data_win (db : Z) (dreg : region) (bo eo : Z) : pwin :=
  PWin db dreg (db + bo) (db + bo) (db + eo).

#[global] Hint Unfold pbuf_vals pbuf_ptrs : structs.

Section out.
Context `{!gen_heapGS piece pval Σ}.

(** The window's object is alive. When the window lies in the buffer's
    own object, the buffer's lifetime already says so, and the regions
    agree. *)
Definition win_live (bb : Z) (breg : region) (w : pwin) : iProp Σ :=
  (if Z.eq_dec (pw_obj w) bb then ⌜pw_reg w = breg⌝ else live (pw_obj w) (pw_reg w))%I.

(** The buffer at bb has the window w, and it owns the window's bytes. *)
Definition printf_buf (bb : Z) (breg : region) (w : pwin) (written mode : Z) : iProp Σ :=
  ⌜pwin_ok w⌝ ∗ pbuf_live bb breg ∗ pbuf bb (pbuf_vals w written mode) ∗ win_live bb breg w ∗
  ∃ xs, ⌜Z.of_nat (length xs) = pw_end w - pw_base w⌝ ∗ bytes (pw_obj w) (pw_base w - pw_obj w) xs.

(** Every function that appends to a buffer takes the invariant
    [printf_out] and gives it back. The invariant says that the buffer
    at bb is usable. It also owns what the code that flushes the buffer
    needs, such as the stream. The parameter R states that part, and R
    may depend on where the buffer's window lies. *)
Definition printf_out (R : Z * region * Z * Z -> iProp Σ) (bb : Z) : iProp Σ :=
  ∃ breg w written mode, printf_buf bb breg w written mode ∗ R (pw_place w).

(** A window with a free byte gives that byte up for a store and takes
    it back with any value. *)
Lemma window_byte w xs :
  pwin_ok w -> pw_ptr w < pw_end w -> Z.of_nat (length xs) = pw_end w - pw_base w ->
  bytes (pw_obj w) (pw_base w - pw_obj w) xs ⊢
  ∃ x, ibyte (pw_obj w) (pw_ptr w - pw_obj w) x ∗
    ∀ y, ibyte (pw_obj w) (pw_ptr w - pw_obj w) y -∗
      ∃ ys, ⌜Z.of_nat (length ys) = pw_end w - pw_base w⌝ ∗ bytes (pw_obj w) (pw_base w - pw_obj w) ys.
Proof using Type.
  intros (Hob & Hbase & Hptr & Hend & _) Hfree Hlen.
  set (n := Z.to_nat (pw_ptr w - pw_base w)).
  assert (Hn : (n < length xs)%nat) by lia.
  destruct (lookup_lt_is_Some_2 xs n Hn) as [x Hx].
  rewrite -(take_drop_middle xs n x Hx).
  iIntros "H". iDestruct (bytes_app with "H") as "[Hpre H]".
  change (x :: drop (S n) xs) with ([x] ++ drop (S n) xs).
  iDestruct (bytes_app with "H") as "[Hx Hpost]".
  assert (Htake : Z.of_nat (length (take n xs)) = pw_ptr w - pw_base w) by (rewrite length_take; lia).
  rewrite Htake. replace (pw_base w - pw_obj w + (pw_ptr w - pw_base w)) with (pw_ptr w - pw_obj w) by lia.
  iExists x. iSplitL "Hx".
  { rewrite /bytes /ibyte /=. iExact "Hx". }
  iIntros (y) "Hy". iExists (take n xs ++ [y] ++ drop (S n) xs). iSplit.
  { iPureIntro. rewrite !length_app length_take length_drop. cbn [length]. lia. }
  iApply bytes_app. iFrame "Hpre". rewrite Htake.
  replace (pw_base w - pw_obj w + (pw_ptr w - pw_base w)) with (pw_ptr w - pw_obj w) by lia.
  iApply bytes_app. iFrame "Hpost". rewrite /bytes /ibyte /=. iExact "Hy".
Qed.

(** The window's object is alive whenever the buffer's is. A proof
    borrows the window's lifetime for a check or a store and returns
    it. *)
Lemma win_live_acc bb breg w :
  live bb breg -∗ win_live bb breg w -∗
  live (pw_obj w) (pw_reg w) ∗ (live (pw_obj w) (pw_reg w) -∗ live bb breg ∗ win_live bb breg w).
Proof using Type.
  iIntros "Hl Hw". unfold win_live. destruct (Z.eq_dec (pw_obj w) bb) as [E | N].
  - iDestruct "Hw" as %->. rewrite E. iFrame "Hl". iIntros "Hl". iFrame "Hl". done.
  - iFrame "Hw". iIntros "Hw". iFrame.
Qed.

End out.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Loading one of a buffer's pointers needs the lifetime of the object
    it points into. That object may be the buffer's own, so this rule
    takes the window's lifetime in the form the invariant holds it. *)
Lemma wp_load_window f e ls l d off args rest j classes p bb breg o a w Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj bb -> raw_address (ptr_addr p) off = bb + o -> (bb + o) mod 8 = 0 ->
  0 <= a < 2 ^ 64 ->
  live bb breg -∗ pcell bb o (mkPtr a (Obj (pw_obj w))) -∗ win_live bb breg w -∗
  ▷ (live bb breg -∗ pcell bb o (mkPtr a (Obj (pw_obj w))) -∗ win_live bb breg w -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr a (Obj (pw_obj w)))) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
        (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hc Hx Hp Ha Hal Hr. iIntros "Hl Hc Hw HK". unfold win_live.
  destruct (Z.eq_dec (pw_obj w) bb) as [E | N].
  - iDestruct "Hw" as %Hreg. rewrite E.
    iApply (wp_raw_load_pointer_self with "Hl Hc"); [exact Hc | exact Hx | exact Hp | exact Ha | exact Hal | exact Hr | reflexivity |].
    iNext. iIntros "Hl Hc". iApply ("HK" with "Hl Hc []"). iPureIntro. exact Hreg.
  - iApply (wp_raw_load_pointer with "Hl Hc Hw"); [exact Hc | exact Hx | exact Hp | exact Ha | exact Hal | exact Hr |].
    iNext. iIntros "Hl Hc Hw". iApply ("HK" with "Hl Hc Hw").
Qed.

End rules.

(** The tactic [load_window] loads one of the buffer's three pointers.
    Hl names the buffer's lifetime, Hc the pointer's cell and Hw the
    window's lifetime. *)
Ltac load_window Hl Hc Hw :=
  iRevert Hw; iRevert Hc; iRevert Hl;
  eapply step_res3;
    [eapply wp_load_window; inst;
      [reflexivity | vx | reflexivity | a2 | a2
      | lazymatch goal with H : pwin_ok _ |- _ => unfold pwin_ok in H; cbn [pw_obj pw_reg pw_base pw_ptr pw_end] in *; lia end] |];
  iIntros Hl; iIntros Hc; iIntros Hw.

(** A block that reads or writes the buffer's fields first splits the
    usable buffer into its parts. The tactic [buf_open] does this for
    the buffer in the hypothesis H, and it gives every part a fixed
    name. It names the buffer's lifetime Hl and the five fields Hbase,
    Hptr, Hend, Hwr and Hmode. It names the window's lifetime Hwl and
    the window's bytes Hbytes. It names the facts about the window's
    addresses Hw and the facts about the buffer's address Hbb. *)
Ltac buf_open H :=
  iDestruct H as "(%Hw & Hbl & Hb & Hwl & Hbytes)"; struct_live_open "Hbl" as "[%Hbb Hl]"; struct_open "Hb" as "(Hbase & Hptr & Hend & Hwr & Hmode & _)".

(** The tactic [buf_close] proves a usable buffer from the hypotheses
    that [buf_open] named. It leaves the window's pure facts as the
    goal. *)
Ltac buf_close :=
  iSplit;
    [iPureIntro
    | iSplitL "Hl"; [iEval (struct_sizes); iSplit; [iPureIntro; eassumption | iExact "Hl"]|];
      iSplitR "Hwl Hbytes"; [iEval (struct_cells); iFrame "Hbase Hptr Hend Hwr Hmode" | iFrame "Hwl Hbytes"]].

(** The tactic [out_close] proves the invariant [printf_out] again
    after a block has changed the buffer. The proof gives the buffer's
    new window w and names the hypothesis HR that holds what the
    flushing code owns. *)
Tactic Notation "out_close" constr(HR) "with" uconstr(w) :=
  iExists _, w, _, _; iSplitR HR; [buf_close | iExact HR].
