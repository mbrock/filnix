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
    function that only appends keeps it unchanged.

    A function that copies bytes into the window changes more than
    the window's bytes. Fil-C records, for every eight bytes of an
    object, whether they hold a pointer and what that pointer may
    reach. The record is called a capability slot. A copy writes the
    slot of every eight bytes that it touches, because the copied
    bytes may hold a pointer. The buffer therefore owns the capability
    slots of the window as well as its bytes.

    A slot belongs to eight bytes that start at a multiple of 8, and
    the window may start between two such addresses. The buffer owns
    the bytes and the slots from the last multiple of 8 at or before
    the start of the window, so that it owns every slot that a copy
    into the window can write. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From iris.program_logic Require Import language weakestpre.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Pieces Heap Language Logic MemLogic.
From Glibc Require Import GlibcProgram Fix OsWorld FileInv LibioLogic LibioPutsInv CStruct PrintfLayout.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
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

(** The addresses of a window are ordered and lie in its object, and
    the object is 8-aligned. *)
Definition pwin_ok (w : pwin) : Prop :=
  0 < pw_obj w /\ pw_obj w mod 8 = 0 /\ pw_obj w <= pw_base w /\ pw_base w <= pw_ptr w /\
  pw_ptr w <= pw_end w /\ pw_end w <= r_end (pw_reg w) /\ r_end (pw_reg w) <= 2 ^ 63.

(** The address [pw_lo] is the last 8-aligned address at or below the
    window's base. *)
Definition pw_lo (w : pwin) : Z := pw_base w - pw_base w mod 8.

(** A buffer is in one of several modes. The mode 0 marks a buffer
    whose output has failed, and every other mode says who flushes the
    buffer. *)
Definition mode_failed : Z := 0.

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

(** The predicate [win_own] owns the bytes of the object b from the
    address lo to the address hi, together with their capability
    slots. Every byte has the value of a byte. *)
Definition win_own (b lo hi : Z) : iProp Σ :=
  ∃ xs cs, ⌜Z.of_nat (length xs) = hi - lo /\ length cs = length xs /\ Forall (fun x => 0 <= x < 256) xs⌝ ∗
    bytes b (lo - b) xs ∗ auxes b (lo - b) cs.

(** The buffer at bb has the window w, and it owns the window's bytes
    and capability slots. *)
Definition printf_buf (bb : Z) (breg : region) (w : pwin) (written mode : Z) : iProp Σ :=
  ⌜pwin_ok w⌝ ∗ pbuf_live bb breg ∗ pbuf bb (pbuf_vals w written mode) ∗ win_live bb breg w ∗
  win_own (pw_obj w) (pw_lo w) (pw_end w).

(** Every function that appends to a buffer takes the invariant
    [printf_out] and gives it back. The invariant says that the buffer
    at bb is usable. A usable buffer has either failed or it is in the
    mode k. The mode decides which function flushes the buffer, so k
    names that function. The invariant also owns what that function
    needs, such as the stream. The parameter R states this part of the
    invariant. R takes the buffer, the region of the buffer's object
    and the place of the buffer's window, because what the function
    needs may depend on all three. A file-backed buffer, for example,
    is a larger object than a plain buffer, and its part R says how
    far the object reaches. *)
Definition printf_out (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ) (bb : Z) : iProp Σ :=
  ∃ breg w written mode, ⌜mode = mode_failed \/ mode = k⌝ ∗ printf_buf bb breg w written mode ∗ R bb breg (pw_place w).

(** A window with a free byte gives that byte up for a store and takes
    it back with the value of any byte. *)
Lemma window_byte w :
  pwin_ok w -> pw_ptr w < pw_end w ->
  win_own (pw_obj w) (pw_lo w) (pw_end w) ⊢
  ∃ x, ibyte (pw_obj w) (pw_ptr w - pw_obj w) x ∗
    ∀ y, ⌜0 <= y < 256⌝ -∗ ibyte (pw_obj w) (pw_ptr w - pw_obj w) y -∗ win_own (pw_obj w) (pw_lo w) (pw_end w).
Proof using Type.
  intros (Hob & Hal & Hbase & Hptr & Hend & _) Hfree. unfold pw_lo.
  pose proof (Z.mod_pos_bound (pw_base w) 8 ltac:(lia)) as Hm.
  set (lo := pw_base w - pw_base w mod 8) in *.
  iIntros "(%xs & %cs & (%Hlen & %Hcs & %Hx) & H & Hcs)".
  set (n := Z.to_nat (pw_ptr w - lo)).
  assert (Hn : (n < length xs)%nat) by lia.
  destruct (lookup_lt_is_Some_2 xs n Hn) as [x Hxn].
  rewrite -{1}(take_drop_middle xs n x Hxn).
  iDestruct (bytes_app with "H") as "[Hpre H]".
  change (x :: drop (S n) xs) with ([x] ++ drop (S n) xs).
  iDestruct (bytes_app with "H") as "[Hx Hpost]".
  assert (Htake : Z.of_nat (length (take n xs)) = pw_ptr w - lo) by (rewrite length_take; lia).
  rewrite Htake. replace (lo - pw_obj w + (pw_ptr w - lo)) with (pw_ptr w - pw_obj w) by lia.
  iExists x. iSplitL "Hx".
  { rewrite /bytes /ibyte /=. iExact "Hx". }
  iIntros (y) "%Hy Hy". iExists (take n xs ++ [y] ++ drop (S n) xs), cs. iSplit.
  { iPureIntro. split; [|split].
    - rewrite !length_app length_take length_drop. cbn [length]. lia.
    - rewrite !length_app length_take length_drop. cbn [length]. lia.
    - apply Forall_app. split; [apply Forall_take; exact Hx|].
      apply Forall_app. split; [apply Forall_singleton; exact Hy | apply Forall_drop; exact Hx]. }
  iFrame "Hcs". iApply bytes_app. iFrame "Hpre". rewrite Htake.
  replace (lo - pw_obj w + (pw_ptr w - lo)) with (pw_ptr w - pw_obj w) by lia.
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
      | try lazymatch goal with H : pwin_ok _ |- _ => unfold pwin_ok in H end;
        cbn [pw_obj pw_reg pw_base pw_ptr pw_end] in *; lia] |];
  iIntros Hl; iIntros Hc; iIntros Hw.

(** The compiled code reads the buffer's mode as an unsigned 4-byte
    integer, and the load gives the field's value. *)
Lemma load_mode_int x : 0 <= x < 2 ^ 32 -> extended Uw W (of_bytes (le_bytes x 4)) = Some (WInt x).
Proof. intros Hx. rewrite of_bytes_int; [|exact Hx]. cbn. by rewrite !(Z.mod_small x (2 ^ 32)). Qed.

(** The tactic [load_mode] loads the buffer's mode. Hl names the
    buffer's lifetime and Hb the field. *)
Ltac load_mode Hl Hb :=
  iDestruct Hb as "[%Hmode_range Hmode_bytes]";
  rule2 Hl "Hmode_bytes" ltac:(eapply wp_raw_load_sub_bytes_dq; inst;
    [reflexivity | vx | reflexivity | apply load_mode_int; assumption | left; reflexivity | a2]);
  iAssert (int_cell _ _ _) with "[Hmode_bytes]" as Hb; [iSplit; [iPureIntro; eassumption | iExact "Hmode_bytes"]|].

(** A block that reads or writes the buffer's fields first splits the
    usable buffer into its parts. The tactic [buf_open] does this for
    the buffer in the hypothesis H, and it gives every part a fixed
    name. It names the buffer's lifetime Hl and the five fields Hbase,
    Hptr, Hend, Hwr and Hmode. It names the window's lifetime Hwl and
    the window's bytes and slots Hwin. It names the facts about the
    window's addresses Hw and the facts about the buffer's address Hbb. *)
Ltac buf_open H :=
  iDestruct H as "(%Hw & Hbl & Hb & Hwl & Hwin)"; struct_live_open "Hbl" as "[%Hbb Hl]"; struct_open "Hb" as "(Hbase & Hptr & Hend & Hwr & Hmode & _)".

(** The tactic [buf_close] proves a usable buffer from the hypotheses
    that [buf_open] named. It leaves the window's pure facts as the
    goal. *)
Ltac buf_close :=
  iSplit;
    [iPureIntro
    | iSplitL "Hl"; [iEval (struct_sizes); iSplit; [iPureIntro; eassumption | iExact "Hl"]|];
      iSplitR "Hwl Hwin"; [iEval (struct_cells); iFrame "Hbase Hptr Hend Hwr Hmode" | iFrame "Hwl Hwin"]].

(** The tactic [out_close] proves the invariant [printf_out] again
    after a block has changed the buffer. The proof gives the buffer's
    new window w and names the hypothesis HR that holds what the
    flushing code owns. The tactic takes the fact about the buffer's
    mode from the hypothesis Hmd, and it leaves the window's pure
    facts as the goal. *)
Tactic Notation "out_close" constr(HR) "with" uconstr(w) :=
  iExists _, w, _, _; iSplit; [iPureIntro; eassumption|]; iSplitR HR; [buf_close | iExact HR].
