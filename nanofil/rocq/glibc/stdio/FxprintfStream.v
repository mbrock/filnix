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
From Glibc Require Import GlibcProgram OsWorld FileInv LibioLogic FxprintfTidy.
From Glibc Require LibioPutsInv.
From Glibc Require Import Fix.
From Glibc Require Export StreamFlags.
Import ListNotations.
Open Scope Z_scope.

Import FileInv Fix.ML0 Fix.LG0 Fix.LG0.L.

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
    named arguments. The formatter reads the other arguments through it.
    The cursor is a heap object at an 8-aligned address, because the
    formatter loads a pointer from it. *)
Definition fx_va (ap : ptr) (xs : list word) : iProp Σ :=
  ∃ cb sb, ⌜ap = mkPtr cb (Obj cb) /\ 0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= 2 ^ 48 /\
            0 < sb /\ sb mod 16 = 0 /\ sb + req_extent (fx_req xs) <= 2 ^ 48⌝ ∗
    pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + 16) (Ro sb))) ∗
    pts (snapshot_ps xs sb (fx_req xs)).

(** Reloading a held lock's owner reads a pointer to the thread object,
    so that case needs a share of the thread's lifetime. A free lock's
    owner is null and needs nothing. *)
Definition fx_owner (self : ptr) (held : option Z) : iProp Σ :=
  match held with None => True | Some _ => ∃ dq reg, live_capq dq (ptr_cap self) reg end.

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
Definition fx_vfprintf_rule (vb fd : Z) (fp fmt : ptr) (xs : list word) (mode flags2 : Z)
    (held : option Z) (R : iProp Σ) (Q : Z -> iProp Σ) : Prop :=
  forall f e ls l d args rest j ap Φ,
    map_option (arg_x ge e) args = Some [WPtr fp; WPtr fmt; WPtr ap; WInt 0] ->
    ⊢ fx_stream vb (ow_self w0) fp fd mode (Z.lor flags2 2) (Some (fx_cnt held)) -∗ R -∗ fx_va ap xs -∗
      ▷ (∀ x mode', fx_stream vb (ow_self w0) fp fd mode' (Z.lor flags2 2) (Some (fx_cnt held)) -∗ Q x -∗
          WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d W) (Global (TAtom "__vfprintf_internal")) args :: rest) j)) : gexpr) {{ Φ }}.

(** A caller that prints more than once must know the orientation the
    formatter leaves behind, because the wrapper accepts only an
    unoriented or narrow stream. This variant lets the result resource Q
    depend on that returned mode as well as on the result. *)
Definition fx_vfprintf_rule_at (vb fd : Z) (fp fmt : ptr) (xs : list word) (mode flags2 : Z)
    (held : option Z) (R : iProp Σ) (Q : Z -> Z -> iProp Σ) : Prop :=
  forall f e ls l d args rest j ap Φ,
    map_option (arg_x ge e) args = Some [WPtr fp; WPtr fmt; WPtr ap; WInt 0] ->
    ⊢ fx_stream vb (ow_self w0) fp fd mode (Z.lor flags2 2) (Some (fx_cnt held)) -∗ R -∗ fx_va ap xs -∗
      ▷ (∀ x mode', fx_stream vb (ow_self w0) fp fd mode' (Z.lor flags2 2) (Some (fx_cnt held)) -∗ Q x mode' -∗
          WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d W) (Global (TAtom "__vfprintf_internal")) args :: rest) j)) : gexpr) {{ Φ }}.

(** A caller that does not care about the stream's orientation can keep
    the older rule, because it says the same thing as this one with a
    result resource that ignores the mode. *)
Lemma fx_vfprintf_rule_at_of vb fd fp fmt xs mode flags2 held R Q :
  fx_vfprintf_rule vb fd fp fmt xs mode flags2 held R Q ->
  fx_vfprintf_rule_at vb fd fp fmt xs mode flags2 held R (fun x _ => Q x).
Proof using Type. intros H. exact H. Qed.

End rule.
