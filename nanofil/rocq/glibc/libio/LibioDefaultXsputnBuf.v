From Glibc Require Import GlibcProgram.
(** The write side of a stream, as the string output functions
    `c: _IO_default_xsputn`, `c: _IO_new_file_xsputn` and `c: puts`
    see it, and the call of the jump table's overflow they make.

    A stream that only writes keeps its eight buffer pointers as a
    flush leaves them ([wbuf]): the read pointer, read end, read base
    and write base at the buffer's base, the write pointer and write end
    anywhere in the buffer, and the base and end of the buffer. Before
    the first write there is no buffer and every pointer is null. The
    buffer is a heap object at a multiple of 8, owned whole, its life,
    every byte (each below 256) and every aux slot, with any contents
    ([wroom]): the copies of LibioDefaultXsputnCopy.v need the slots,
    and a flush needs the bytes.

    The rest of the stream (its flags, descriptor, lock and the rest)
    is what the overflow reads and writes: [overflow_spec] states the
    call of `c: _IO_new_file_overflow(f, ch)` through the jump table
    over [wbuf] and that rest, any predicate of the stream and its
    buffer. LibioOverflow*.v proves the function; here it is a
    premise.

    | Lemma | Use |
    |---|---|
    | [bytes_at], [bytes_put] | one byte of a buffer, read or written |
    | [bytesq_at] | one byte of a source at a share |
    | [wbuf_room] | the room of a stream with a buffer | *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioDoWriteCode LibioDefaultXsputnCopy.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputnCopy LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.

(** ## Environments *)

(** e' answers every name outside the names S as e does. *)
Definition same_out {A : Type} (S : list name) (e e' : list (name * A)) : Prop :=
  forall x, existsb (name_eqb x) S = false -> lookup x e' = lookup x e.

(** Every environment answers as itself. *)
Lemma same_out_refl {A : Type} S (e : list (name * A)) : same_out S e e.
Proof. intros x _. reflexivity. Qed.

(** A [put] of one of the names S keeps [same_out] S. *)
Lemma same_out_put {A : Type} S k (v : A) e e' :
  existsb (name_eqb k) S = true -> same_out S e e' -> same_out S e (put k v e').
Proof.
  intros Hk H x Hx. rewrite Symbolic.lookup_after_put_other; [apply H; exact Hx|].
  destruct (name_eqb x k) eqn:E; [|reflexivity]. apply term_eqb_eq in E. subst. rewrite Hx in Hk. discriminate.
Qed.

(** [same_out] composes. *)
Lemma same_out_trans {A : Type} S (e1 e2 e3 : list (name * A)) :
  same_out S e1 e2 -> same_out S e2 e3 -> same_out S e1 e3.
Proof. intros H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

(** Prove [same_out] S e e' for e' a run of [put]s of names of S over e. *)
Ltac same_tac :=
  repeat (apply same_out_put; [reflexivity|]); first [apply same_out_refl | eassumption].
Import ListNotations.
Open Scope Z_scope.

(** The base of the buffer nb, the heap object b of sz bytes, or null. *)
Definition nb_base (nb : option (Z * Z)) : ptr :=
  match nb with Some (b, _) => mkPtr b (Obj b) | None => null end.

(** The end of the buffer nb, or null. *)
Definition nb_end (nb : option (Z * Z)) : ptr :=
  match nb with Some (b, sz) => mkPtr (b + sz) (Obj b) | None => null end.

(** p points into the buffer b of sz bytes, or just past it. *)
Definition in_buf (b sz : Z) (p : ptr) : Prop := ptr_cap p = Obj b /\ b <= ptr_addr p <= b + sz.

(** A writable buffer comes from the heap and owns every byte and
    capability slot in its window. Both write pointers lie inside
    that window or at its end. Copying must retain the heap origin
    because closing the stream later frees the buffer. *)
Definition room_ok (b sz : Z) (reg : region) (xs : list Z) (cs : list cap) (wp we : ptr) : Prop :=
  0 < b /\ b mod 8 = 0 /\ 0 < sz /\ b + sz <= r_end reg /\ r_end reg <= 2 ^ 63 /\
  length xs = Z.to_nat sz /\ length cs = Z.to_nat sz /\ Forall (fun x => 0 <= x < 256) xs /\
  in_buf b sz wp /\ in_buf b sz we /\ r_kind reg = Heap.


Import LibioDefaultXsputnCopy LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section buf.
Context `{!gen_heapGS piece pval Σ}.

(** [wroom] nb wp we: no buffer, both pointers null, or the heap
    buffer nb, owned whole as [room_ok] says. *)
Definition wroom (nb : option (Z * Z)) (wp we : ptr) : iProp Σ :=
  match nb with
  | None => ⌜wp = null /\ we = null⌝
  | Some (b, sz) => ∃ reg xs cs, ⌜room_ok b sz reg xs cs wp we⌝ ∗ live b reg ∗ bytes b 0 xs ∗ auxes b 0 cs
  end.

(** [wcells] fb nb: the six buffer pointers of the stream fb other
    than the write pointer and end: the read pointer, read end, read
    base and write base at the buffer's base, and the base and end of
    the buffer. *)
Definition wcells (fb : Z) (nb : option (Z * Z)) : iProp Σ :=
  pcell fb off_read_ptr (nb_base nb) ∗ pcell fb 16 (nb_base nb) ∗ pcell fb 24 (nb_base nb) ∗
  pcell fb off_write_base (nb_base nb) ∗ pcell fb off_buf_base (nb_base nb) ∗ pcell fb off_buf_end (nb_end nb).

(** [wbuf] fb nb wp we: the eight buffer pointers of the stream fb,
    the write pointer wp and end we and the others ([wcells]), and the
    buffer ([wroom]). *)
Definition wbuf (fb : Z) (nb : option (Z * Z)) (wp we : ptr) : iProp Σ :=
  wcells fb nb ∗ pcell fb off_write_ptr wp ∗ pcell fb off_write_end we ∗ wroom nb wp we.

(** Owning one byte of a list of bytes from offset 0 is owning it,
    the bytes before and the bytes after. *)
Lemma bytes_at b xs (k : nat) x : xs !! k = Some x ->
  bytes b 0 xs ⊣⊢ bytes b 0 (take k xs) ∗ ibyte b (Z.of_nat k) x ∗ bytes b (Z.of_nat k + 1) (drop (S k) xs).
Proof.
  intros Hk. rewrite -{1}(take_drop_middle xs k x Hk) bytes_app.
  rewrite length_take_le; [|apply lookup_lt_Some in Hk; lia]. rewrite Z.add_0_l.
  rewrite /bytes byte_ps_cons /ibyte /pts !big_sepL_cons big_sepL_nil.
  iSplit; [iIntros "($ & $ & $)" | iIntros "($ & [$ _] & $)"].
Qed.

(** Writing one byte: the bytes around it and the new byte are the
    list with it replaced. *)
Lemma bytes_put b xs (k : nat) y : (k < length xs)%nat ->
  bytes b 0 (take k xs) ∗ ibyte b (Z.of_nat k) y ∗ bytes b (Z.of_nat k + 1) (drop (S k) xs) ⊢
  bytes b 0 (<[k := y]> xs).
Proof.
  intros Hk. rewrite (bytes_at b (<[k := y]> xs) k y); [|apply list_lookup_insert_eq; lia].
  rewrite take_insert_ge; [|lia]. rewrite drop_insert_lt; [|lia]. done.
Qed.

(** Owning one byte of bytes at a share, and the rest back. *)
Lemma bytesq_at dq b o ys (k : nat) y : ys !! k = Some y ->
  bytesq dq b o ys ⊢ bytesq dq b (o + Z.of_nat k) [y] ∗ (bytesq dq b (o + Z.of_nat k) [y] -∗ bytesq dq b o ys).
Proof.
  intros Hk. rewrite -{1 2}(take_drop_middle ys k y Hk).
  rewrite /bytesq !byte_ps_app !ptsq_app length_take_le; [|apply lookup_lt_Some in Hk; lia].
  rewrite (byte_ps_cons _ _ y (drop (S k) ys)) /byte_ps. cbn [length seqZ].
  iIntros "(Ha & Hb)". rewrite /ptsq !big_sepL_cons. iDestruct "Hb" as "(Hy & Hc)".
  iSplitL "Hy"; [cbn; iFrame; done|]. iIntros "(Hy & _)". iFrame.
Qed.

(** Owning a run of bytes at a share, its middle c bytes from j, and
    the whole back. *)
Lemma bytesq_sub dq b o ys (j c : nat) : (j + c <= length ys)%nat ->
  bytesq dq b o ys ⊢ bytesq dq b (o + Z.of_nat j) (take c (drop j ys)) ∗
    (bytesq dq b (o + Z.of_nat j) (take c (drop j ys)) -∗ bytesq dq b o ys).
Proof.
  intros H. set (zs := take c (drop j ys)).
  assert (E : ys = (take j ys ++ zs ++ drop c (drop j ys))%list) by (unfold zs; rewrite !take_drop; reflexivity).
  assert (Lj : length (take j ys) = j) by (rewrite length_take_le; lia).
  rewrite {1 2}E /bytesq !byte_ps_app !ptsq_app Lj.
  iIntros "(H1 & H2 & H3)". iFrame "H2". iIntros "H2". iFrame.
Qed.

(** A stream with a buffer: its room's pieces, and the buffer back
    from any new contents and write pointer in it. *)
Lemma wroom_some b sz wp we :
  wroom (Some (b, sz)) wp we ⊣⊢
  ∃ reg xs cs, ⌜room_ok b sz reg xs cs wp we⌝ ∗ live b reg ∗ bytes b 0 xs ∗ auxes b 0 cs.
Proof. reflexivity. Qed.

End buf.

Import ProgramAbbreviations.
Section ovf_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance buf_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition ovf_ret (ch r : Z) : Prop := r = 2 ^ 32 - 1 \/ r = (if ch =? 2 ^ 32 - 1 then 0 else ch).
Definition overflow_spec (os : Z -> option (Z * Z) -> iProp Σ) : Prop :=
  forall fr fb freg nb wp we ch vb vreg Φ,
  call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ⊢ vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
    wbuf fb nb wp we -∗ os fb nb -∗
    ▷ (∀ r nb' wp' we', ⌜ovf_ret ch r /\ nb' <> None⌝ -∗
       live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
       wbuf fb nb' wp' we' -∗ os fb nb' -∗ Φ (Ret (WInt r))) -∗
    WP (ERun fr : sexpr) {{ Φ }}.
End ovf_values.
Section ovf.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** What `c: _IO_new_file_overflow(f, ch)` returns: ch, or 0 when ch
    is `c: EOF` and the flush succeeded, or `c: EOF` on failure. *)

(** The call `c: _IO_new_file_overflow(f, ch)` of a byte ch or of
    `c: EOF`, through the jump table of a narrow stream: over the
    stream's life, its jump table pointer, its buffer pointers and
    buffer ([wbuf]) and the rest of it, os fb nb, it returns as
    [ovf_ret] says. It leaves an allocated buffer even when output
    fails, so callers can retain that fact without assuming success. *)

End ovf.
