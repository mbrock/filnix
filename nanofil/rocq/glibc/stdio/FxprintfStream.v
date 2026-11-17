(** glibc prints getopt's diagnostics with __fxprintf_nocancel. That
    wrapper takes the stream's recursive lock, sets bit 2 of the
    `c: _flags2` bitfield while the formatter runs, and puts back both on
    return. This module states what the wrapper needs from the stream and
    from the formatter it calls, so that FxprintfCall.v can prove the
    wrapper's own instructions.

    The wrapper does not format anything itself; it calls glibc's
    formatter to do that, and this module does not prove the formatter.
    A caller must instead supply a rule for that call. The rule receives
    the stream with the temporary flags and the held lock, together with
    the argument cursor and the read-only [[snapshot]] of the arguments.
    It must give the stream back at the same flags and lock count, but it
    may change the stream's orientation, as glibc's formatter does when it
    first writes to a stream. *)
From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Pieces Heap
  Language Logic Identity VariadicLogic.
From Glibc Require Import GlibcProgram OsWorld FileInv LibioLogic PrintfStreamInv.
From Glibc Require FileInv LibioPutsInv PrintfStreamInv.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import PrintfStreamInv FileInv FileInv.ML FileInv.LG FileInv.L.

(** ## The flags2 bitfield

    The wrapper reads `c: _flags2` as a 24-bit signed bitfield of a 32-bit
    word whose top byte belongs to the next field. Shifting left by 8 and
    arithmetically right by 8 recovers the bitfield's value. Only its low
    24 bits reach memory again, so these lemmas reduce the stores to
    ordinary bit operations on the whole word. *)

(** The wrapper saves this signed value of the bitfield. *)
Definition fx_field (x : Z) : Z :=
  (sign_extension (2 ^ 32) (2 ^ 31) ((x * 2 ^ 8) mod 2 ^ 32) / 2 ^ 8) mod 2 ^ 32.

(** Sign extension keeps the bitfield's low 24 bits. *)
Lemma fx_field_low x : 0 <= x < 2 ^ 32 -> Z.land (fx_field x) 16777215 = Z.land x 16777215.
Proof.
  intros Hx. change 16777215 with (Z.ones 24).
  rewrite (Z.land_ones _ 24); [|lia]. rewrite (Z.land_ones _ 24); [|lia].
  unfold fx_field, sign_extension.
  pose proof (Z.mod_pos_bound x (2 ^ 24)) as Hb.
  assert (Hr : (x * 2 ^ 8) mod 2 ^ 32 = (x mod 2 ^ 24) * 2 ^ 8).
  { change (2 ^ 32) with (2 ^ 24 * 2 ^ 8). rewrite Z.mul_mod_distr_r; lia. }
  rewrite Hr. rewrite (Z.mod_small (x mod 2 ^ 24 * 2 ^ 8)); [|lia].
  destruct (Z.leb_spec (2 ^ 31) (x mod 2 ^ 24 * 2 ^ 8)).
  - replace (x mod 2 ^ 24 * 2 ^ 8 - 2 ^ 32) with ((x mod 2 ^ 24 - 2 ^ 24) * 2 ^ 8) by lia.
    rewrite Z.div_mul; [|lia].
    rewrite <- (Z.mod_unique (x mod 2 ^ 24 - 2 ^ 24) (2 ^ 32) (-1) (x mod 2 ^ 24 - 2 ^ 24 + 2 ^ 32));
      [|lia|lia].
    symmetry. apply (Z.mod_unique _ _ 255); lia.
  - rewrite Z.div_mul; [|lia]. rewrite (Z.mod_small (x mod 2 ^ 24)); [|lia].
    rewrite Z.mod_mod; lia.
Qed.

(** Both 32-bit words are equal when their high byte and low 24 bits are. *)
Lemma fx_split x : 0 <= x < 2 ^ 32 ->
  Z.lor (Z.land x 4278190080) (Z.land x 16777215) = x.
Proof.
  intros Hx. rewrite <- Z.land_lor_distr_r. change (Z.lor 4278190080 16777215) with (Z.ones 32).
  rewrite Z.land_ones; [|lia]. apply Z.mod_small. lia.
Qed.

(** The temporary store sets bit 2 of the bitfield and keeps the high byte. *)
Lemma fx_set x : 0 <= x < 2 ^ 32 ->
  Z.lor (Z.land x 4278190080) (Z.land (Z.lor (fx_field x) 2) 16777215) = Z.lor x 2.
Proof.
  intros Hx. rewrite Z.land_lor_distr_l (fx_field_low x Hx).
  change (Z.land 2 16777215) with 2. rewrite Z.lor_assoc (fx_split x Hx). reflexivity.
Qed.

(** The restoring store puts back the saved bitfield under the current high
    byte, which the formatter leaves as it found it. *)
Lemma fx_restore x : 0 <= x < 2 ^ 32 ->
  Z.lor (Z.land (Z.lor x 2) 4278190080) (Z.land (fx_field x) 16777215) = x.
Proof.
  intros Hx. rewrite Z.land_lor_distr_l (fx_field_low x Hx).
  change (Z.land 2 4278190080) with 0. rewrite Z.lor_0_r. apply fx_split. exact Hx.
Qed.

(** Bit 2 is not the need-lock bit, so the temporary flags keep the stream's restriction. *)
Lemma fx_need_lock x : Z.land x io_need_lock = 0 -> Z.land (Z.lor x 2) io_need_lock = 0.
Proof. intros H. rewrite Z.land_lor_distr_l H. reflexivity. Qed.

(** The wrapper computes the bitfield with a left shift and an arithmetic
    right shift, each reduced to 32 bits. The result is [fx_field]. *)
Lemma fx_shift_field x y z : 0 <= x < 2 ^ 32 ->
  y = (x mod 2 ^ 32 * 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32 ->
  z = (sign_extension (2 ^ 32) (2 ^ 31) (y mod 2 ^ 32) / 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32 ->
  z = fx_field x.
Proof.
  intros Hx -> ->. unfold fx_field. change ((8 mod 2 ^ 32) mod 32) with 8.
  rewrite (Z.mod_small x); [|lia]. rewrite Z.mod_mod; [reflexivity|lia].
Qed.

(** A bitwise and with a mask below 2^32 stays below 2^32. *)
Lemma fx_land_lt32 a b : 0 <= a -> 0 <= b < 2 ^ 32 -> 0 <= Z.land a b < 2 ^ 32.
Proof.
  intros Ha Hb. split; [apply Z.land_nonneg; lia|].
  rewrite Z.land_comm. rewrite <- (Z.mod_small b (2 ^ 32)) at 1; [|lia].
  rewrite <- (Z.land_ones b 32); [|lia].
  rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 32) a), Z.land_assoc.
  rewrite Z.land_ones; [|lia]. apply Z.mod_pos_bound. lia.
Qed.

(** The field value is a 32-bit word. *)
Lemma fx_field_range x : 0 <= fx_field x < 2 ^ 32.
Proof. unfold fx_field. apply Z.mod_pos_bound. lia. Qed.

(** The four operations of the temporary store produce flags2 with bit 2 set. *)
Lemma fx_set_ops x f a b c d : 0 <= x < 2 ^ 32 -> f = fx_field x ->
  a = Z.lor (f mod 2 ^ 32) (2 mod 2 ^ 32) ->
  b = Z.land (x mod 2 ^ 32) (4278190080 mod 2 ^ 32) ->
  c = Z.land (a mod 2 ^ 32) (16777215 mod 2 ^ 32) ->
  d = Z.lor (b mod 2 ^ 32) (c mod 2 ^ 32) -> d = Z.lor x 2.
Proof.
  intros Hx -> -> -> -> ->. pose proof (fx_field_range x) as Hf.
  change (2 mod 2 ^ 32) with 2. change (4278190080 mod 2 ^ 32) with 4278190080.
  change (16777215 mod 2 ^ 32) with 16777215.
  rewrite (Z.mod_small (fx_field x)); [|lia]. rewrite (Z.mod_small x); [|lia].
  assert (Ha : 0 <= Z.lor (fx_field x) 2 < 2 ^ 32) by (apply lor_lt32; lia).
  rewrite (Z.mod_small (Z.lor (fx_field x) 2)); [|lia].
  rewrite (Z.mod_small (Z.land x 4278190080)); [|apply fx_land_lt32; lia].
  rewrite (Z.mod_small (Z.land (Z.lor (fx_field x) 2) 16777215)); [|apply fx_land_lt32; lia].
  apply fx_set. exact Hx.
Qed.

(** The three operations of the restoring store give back the saved flags2. *)
Lemma fx_restore_ops x f b c d : 0 <= x < 2 ^ 32 -> f = fx_field x ->
  b = Z.land (Z.lor x 2 mod 2 ^ 32) (4278190080 mod 2 ^ 32) ->
  c = Z.land (f mod 2 ^ 32) (16777215 mod 2 ^ 32) ->
  d = Z.lor (b mod 2 ^ 32) (c mod 2 ^ 32) -> d = x.
Proof.
  intros Hx -> -> -> ->. pose proof (fx_field_range x) as Hf.
  assert (Ho : 0 <= Z.lor x 2 < 2 ^ 32) by (apply lor_lt32; lia).
  change (4278190080 mod 2 ^ 32) with 4278190080. change (16777215 mod 2 ^ 32) with 16777215.
  rewrite (Z.mod_small (fx_field x)); [|lia]. rewrite (Z.mod_small (Z.lor x 2)); [|lia].
  rewrite (Z.mod_small (Z.land (Z.lor x 2) 4278190080)); [|apply fx_land_lt32; lia].
  rewrite (Z.mod_small (Z.land (fx_field x) 16777215)); [|apply fx_land_lt32; lia].
  apply fx_restore. exact Hx.
Qed.

(** These values separate the real bitfield arithmetic from plausible
    mistakes. The word 8388609 has bit 23, the bitfield's sign bit, set, so
    its saved value is negative and sign-extends into the high byte. The
    restoring store must mask it; restoring the saved value whole would
    give 4286578689. The word 4278190208 has a nonzero high byte that both
    stores must keep, and its need-lock bit is set. *)
Example fx_controls :
  fx_field 8388609 = 4286578689 /\
  Z.lor (Z.land 8388609 4278190080) (Z.land (Z.lor (fx_field 8388609) 2) 16777215) = 8388611 /\
  Z.lor (Z.land 8388611 4278190080) (Z.land (fx_field 8388609) 16777215) = 8388609 /\
  Z.lor (Z.land 8388611 4278190080) (fx_field 8388609) <> 8388609 /\
  fx_field 4278190208 = 128 /\
  Z.lor (Z.land 4278190208 4278190080) (Z.land (Z.lor (fx_field 4278190208) 2) 16777215) = 4278190210 /\
  Z.land 4278190208 io_need_lock <> 0.
Proof. vm_compute. repeat split; discriminate || reflexivity. Qed.

(** ## The variadic snapshot

    Entering the variadic wrapper copies every argument into a fresh
    read-only object. The world interpretation only tracks registered
    objects and the errno object, so the copy preserves it as an
    allocation does. *)
Lemma os_wi_snapshot w0 m w h xs q base :
  fresh m q base -> os_wi w0 m w h ->
  os_wi w0 (snapshot_values xs base (allocated m q base)) w (overwrite (snapshot_ps xs base q) h).
Proof.
  intros (_ & _ & _ & Hn & _) [-> Hi]. split; [reflexivity|]. apply (os_inv_step m _ w0 h); [| |exact Hi].
  - intros b Hb. rewrite snapshot_values_regions object_region_allocated.
    destruct (Z.eqb_spec base b); [discriminate|exact Hb].
  - intros eb reg _ [E0 _] _ Hg. rewrite snapshot_values_regions object_region_allocated.
    destruct (Z.eqb_spec base eb) as [<-|Hne]; [congruence|]. split; [exact E0|].
    apply errno_life_overwrite; [|exact Hg]. intros reg' Hin. exfalso.
    apply Hne. symmetry. exact (snapshot_ps_id _ _ _ _ _ Hin).
Qed.

(** A call with these arguments copies them into an object of this size. *)
Definition fx_req (xs : list word) : alloc_req := heap_req 16 (8 * Z.of_nat (length xs)).

(** The formatter sees this lock count. The wrapper takes a free lock
    once, and it takes a lock that this thread holds once more. *)
Definition fx_cnt (held : option Z) : Z :=
  match held with None => 0 | Some c => c + 1 end.

(** A free lock and a lock held once differ by exactly one acquisition. *)
Example fx_cnt_controls : fx_cnt None = 0 /\ fx_cnt (Some 0) = 1 /\ fx_cnt (Some 4) = 5.
Proof. repeat split. Qed.

Section stream.
Context `{!gen_heapGS piece pval Σ}.

(** The cursor object points 16 bytes into the snapshot, past the two
    named arguments. The formatter reads the other arguments through it. *)
Definition fx_va (ap : ptr) (xs : list word) : iProp Σ :=
  ∃ cb sb, ⌜ap = mkPtr cb (Obj cb) /\ 0 < sb /\ sb mod 16 = 0 /\ sb + req_extent (fx_req xs) <= 2 ^ 48⌝ ∗
    pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + 16) (Ro sb))) ∗
    pts (snapshot_ps xs sb (fx_req xs)).

(** Reloading a held lock's owner reads a pointer to the thread object,
    so that case needs a share of the thread's lifetime. A free lock's
    owner is null and needs nothing. *)
Definition fx_owner (self : ptr) (held : option Z) : iProp Σ :=
  match held with None => True | Some _ => ∃ dq reg, live_capq dq (ptr_cap self) reg end.

(** The wrapper reads and writes these fields of the stream: the flags,
    the flags2 word, the mode and the lock pointer, with the lock itself.
    Closing the view may change only flags2, within the need-lock
    restriction, and the lock's state. *)
Lemma printf_stream_fx vb self fp mode flags2 held :
  printf_stream vb self fp mode flags2 held -∗
  ∃ fb freg fl lp, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ 0 <= fl < 2 ^ 32 /\
     Z.land fl io_user_lock = 0 /\ Z.land flags2 io_need_lock = 0 /\ 0 <= flags2 < 2 ^ 32 /\
     0 <= mode < 2 ^ 32⌝ ∗
    live fb freg ∗ int_cell fb off_flags fl ∗ int_cell fb off_flags2 flags2 ∗ int_cell fb off_mode mode ∗
    pcell fb off_lock lp ∗ lock_inv self lp held ∗
    (∀ flags2' held', ⌜Z.land flags2' io_need_lock = 0⌝ -∗ live fb freg -∗ int_cell fb off_flags fl -∗
       int_cell fb off_flags2 flags2' -∗ int_cell fb off_mode mode -∗ pcell fb off_lock lp -∗
       lock_inv self lp held' -∗ printf_stream vb self fp mode flags2' held').
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
  destruct Hp as (Hfp & Hal & Hfb & Hend & Hreg & Hok & Hm & Hmv & Hvt & Hbok & Hf2).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hflags2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd &
    Hfrl & Hfrb & Hmd & Htot & Hvtp)".
  iDestruct "Hfl" as "[%Hflr Hfl]". iDestruct "Hflags2" as "[%Hf2r Hflags2]".
  iDestruct "Hmd" as "[%Hmdr Hmd]".
  pose proof Hok as (_ & _ & _ & _ & Hul & Hnl & _). unfold has in Hul.
  apply negb_false_iff, Z.eqb_eq in Hul.
  iExists fb, freg, (fs_flags st), (fs_lock st). rewrite -Hf2 -Hm.
  iFrame "Hl Hk Hlp". iSplitR; [iPureIntro; split_and!; tauto|].
  iSplitL "Hfl"; [iSplit; [done|iExact "Hfl"]|].
  iSplitL "Hflags2"; [iSplit; [done|iExact "Hflags2"]|].
  iSplitL "Hmd"; [iSplit; [done|iExact "Hmd"]|].
  iIntros (flags2' held' Hmask) "Hl Hfl Hflags2 Hmd Hlp Hk".
  iExists fb, freg, (fs_with_flags2 st flags2'), nb, vt.
  unfold fs_with_flags2, file_fields.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable].
  iSplitR; [iPureIntro; unfold flags_ok in *; cbn [fs_flags fs_flags2];
    destruct Hok as (? & ? & ? & ? & ? & ? & ?); split_and!; first [reflexivity | assumption | lia | rewrite Hm; assumption]|].
  iFrame "Hl Hk Hb Hfl Hps Hfd Hflags2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp". iSplit; done.
Qed.

End stream.

Import ProgramAbbreviations.
Section rule.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Formatting is the one step of the call that the wrapper's proof does
    not cover. A caller therefore states what it knows about the
    formatter, and this rule is the form of that statement. The formatter
    receives the stream with bit 2 of flags2 set and the lock taken once
    more than before the call, together with the caller's resource R. It
    must return the stream with the same flags and lock count, together
    with the caller's result resource Q, though it may change the stream's
    mode. The caller owes this rule, and nothing in this file proves it. *)
Definition fx_vfprintf_rule (vb : Z) (fp fmt : ptr) (xs : list word) (mode flags2 : Z)
    (held : option Z) (R : iProp Σ) (Q : Z -> iProp Σ) : Prop :=
  forall f e ls l d args rest j ap Φ,
    map_option (arg_x ge e) args = Some [WPtr fp; WPtr fmt; WPtr ap; WInt 0] ->
    ⊢ printf_stream vb (ow_self w0) fp mode (Z.lor flags2 2) (Some (fx_cnt held)) -∗ R -∗ fx_va ap xs -∗
      ▷ (∀ x mode', printf_stream vb (ow_self w0) fp mode' (Z.lor flags2 2) (Some (fx_cnt held)) -∗ Q x -∗
          WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d W) (Global (TAtom "__vfprintf_internal")) args :: rest) j)) : gexpr) {{ Φ }}.

(** A caller that prints more than once must know the orientation the
    formatter leaves behind, because the wrapper accepts only an
    unoriented or narrow stream. This variant lets the result resource Q
    depend on that returned mode as well as on the result. *)
Definition fx_vfprintf_rule_at (vb : Z) (fp fmt : ptr) (xs : list word) (mode flags2 : Z)
    (held : option Z) (R : iProp Σ) (Q : Z -> Z -> iProp Σ) : Prop :=
  forall f e ls l d args rest j ap Φ,
    map_option (arg_x ge e) args = Some [WPtr fp; WPtr fmt; WPtr ap; WInt 0] ->
    ⊢ printf_stream vb (ow_self w0) fp mode (Z.lor flags2 2) (Some (fx_cnt held)) -∗ R -∗ fx_va ap xs -∗
      ▷ (∀ x mode', printf_stream vb (ow_self w0) fp mode' (Z.lor flags2 2) (Some (fx_cnt held)) -∗ Q x mode' -∗
          WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d W) (Global (TAtom "__vfprintf_internal")) args :: rest) j)) : gexpr) {{ Φ }}.

(** A caller that does not care about the stream's orientation can keep
    the older rule, because it says the same thing as this one with a
    result resource that ignores the mode. *)
Lemma fx_vfprintf_rule_at_of vb fp fmt xs mode flags2 held R Q :
  fx_vfprintf_rule vb fp fmt xs mode flags2 held R Q ->
  fx_vfprintf_rule_at vb fp fmt xs mode flags2 held R (fun x _ => Q x).
Proof using Type. intros H. exact H. Qed.

End rule.
