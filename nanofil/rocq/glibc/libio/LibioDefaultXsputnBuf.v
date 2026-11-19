From Glibc Require Import Unit_libio_fileops_os.
From Glibc Require Import GlibcProgram.
(** Buffered string output owns the stream's buffer pointers and the memory they describe.
    Before allocation, all eight pointers are null.
    After allocation, the read pointers start at the buffer's base and the write pointers stay within its bounds.

    The buffer owns every data byte and hidden capability slot in its heap allocation.
    Copying preserves those slots, and flushing reads the bytes.
    Shared source memory instead supplies an [[separation-logic|ownership share]] that the caller receives back.

    Overflow may change the stream's flags, descriptor and other fields alongside its write buffer.
    Its contract keeps those additional resources separate and guarantees a buffer even when output fails. *)

From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  BufferCopy.
From Glibc Require Import Fix.

(** ## Environments *)

(** Output loops assign temporary names while retaining the caller's other bindings.
    Two environments agree outside a list when every name not in that list has the same lookup result. *)
Definition same_out {A : Type} (S : list name) (e e' : list (name * A)) : Prop :=
  forall x, existsb (name_eqb x) S = false -> lookup x e' = lookup x e.

(** Every environment agrees with itself outside any list of names. *)
Lemma same_out_refl {A : Type} S (e : list (name * A)) : same_out S e e.
Proof. intros x _. reflexivity. Qed.

(** Assigning a listed temporary name preserves every lookup outside the list. *)
Lemma same_out_put {A : Type} S k (v : A) e e' :
  existsb (name_eqb k) S = true -> same_out S e e' -> same_out S e (put k v e').
Proof.
  intros Hk H x Hx. rewrite Symbolic.lookup_after_put_other; [apply H; exact Hx|].
  destruct (name_eqb x k) eqn:E; [|reflexivity]. apply term_eqb_eq in E. subst. rewrite Hx in Hk. discriminate.
Qed.

(** Agreement outside the same list survives two successive environment changes. *)
Lemma same_out_trans {A : Type} S (e1 e2 e3 : list (name * A)) :
  same_out S e1 e2 -> same_out S e2 e3 -> same_out S e1 e3.
Proof. intros H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

(** Repeated assignments to listed names preserve every other environment binding. *)
Ltac same_tac :=
  repeat (apply same_out_put; [reflexivity|]); first [apply same_out_refl | eassumption].
Import ListNotations.
Open Scope Z_scope.

(** A stream's buffer starts at its heap object's base, or is null before allocation. *)
Definition nb_base (nb : option (Z * Z)) : ptr :=
  match nb with Some (b, _) => mkPtr b (Obj b) | None => null end.

(** A stream's buffer ends just past its allocated bytes, or is null before allocation. *)
Definition nb_end (nb : option (Z * Z)) : ptr :=
  match nb with Some (b, sz) => mkPtr (b + sz) (Obj b) | None => null end.

(** A buffer pointer retains its object's capability and lies within the allocation or just past its end. *)
Definition in_buf (b sz : Z) (p : ptr) : Prop := ptr_cap p = Obj b /\ b <= ptr_addr p <= b + sz.

(** A writable buffer comes from the heap and owns every byte and
    capability slot in its window. Both write pointers lie inside
    that window or at its end. Copying must retain the heap origin
    because closing the stream later frees the buffer. *)
Definition room_ok (b sz : Z) (reg : region) (xs : list Z) (cs : list cap) (wp we : ptr) : Prop :=
  0 < b /\ b mod 8 = 0 /\ 0 < sz /\ b + sz <= r_end reg /\ r_end reg <= 2 ^ 63 /\
  length xs = Z.to_nat sz /\ length cs = Z.to_nat sz /\ Forall (fun x => 0 <= x < 256) xs /\
  in_buf b sz wp /\ in_buf b sz we /\ r_kind reg = Heap.


Import BufferCopy SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.

Section buf.
Context `{!gen_heapGS piece pval Σ}.

(** An unallocated buffer has two null write pointers.
    An allocated buffer owns its heap storage and bounds both pointers. *)
Definition wroom (nb : option (Z * Z)) (wp we : ptr) : iProp Σ :=
  match nb with
  | None => ⌜wp = null /\ we = null⌝
  | Some (b, sz) => ∃ reg xs cs, ⌜room_ok b sz reg xs cs wp we⌝ ∗ live b reg ∗ bytes b 0 xs ∗ auxes b 0 cs
  end.

(** Six stream fields identify the buffer's base and end between output calls.
    The three read pointers and write base all point to the buffer's base. *)
Definition wcells (fb : Z) (nb : option (Z * Z)) : iProp Σ :=
  pcell fb off_read_ptr (nb_base nb) ∗ pcell fb 16 (nb_base nb) ∗ pcell fb 24 (nb_base nb) ∗
  pcell fb off_write_base (nb_base nb) ∗ pcell fb off_buf_base (nb_base nb) ∗ pcell fb off_buf_end (nb_end nb).

(** The write-buffer assertion owns all eight buffer-pointer fields and the buffer's storage. *)
Definition wbuf (fb : Z) (nb : option (Z * Z)) (wp we : ptr) : iProp Σ :=
  wcells fb nb ∗ pcell fb off_write_ptr wp ∗ pcell fb off_write_end we ∗ wroom nb wp we.

(** A buffer's pointer fields and storage can be used separately.
    The proof-mode instance exposes them when a proof opens buffer ownership. *)
#[global] Instance wbuf_into_sep fb nb wp we :
  IntoSep (wbuf fb nb wp we) (wcells fb nb)
    (pcell fb off_write_ptr wp ∗ pcell fb off_write_end we ∗ wroom nb wp we).
Proof using Type. unfold wbuf. apply _. Qed.

(** Framing can assemble a buffer from its fields without opening an
    unrelated buffer already owned by the caller. *)
#[global] Instance wbuf_frame p R fb nb wp we Q :
  Frame p R (wcells fb nb ∗ pcell fb off_write_ptr wp ∗
    pcell fb off_write_end we ∗ wroom nb wp we) Q ->
  Frame p R (wbuf fb nb wp we) Q.
Proof using Type. unfold wbuf. intros H. exact H. Qed.

(** Reading a selected byte splits its ownership from the bytes before and after it. *)
Lemma bytes_at b xs (k : nat) x : xs !! k = Some x ->
  bytes b 0 xs ⊣⊢ bytes b 0 (take k xs) ∗ ibyte b (Z.of_nat k) x ∗ bytes b (Z.of_nat k + 1) (drop (S k) xs).
Proof using Type.
  intros Hk. rewrite -{1}(take_drop_middle xs k x Hk) bytes_app.
  rewrite length_take_le; [|apply lookup_lt_Some in Hk; lia]. rewrite Z.add_0_l.
  rewrite /bytes byte_ps_cons /ibyte /pts !big_sepL_cons big_sepL_nil.
  iSplit; [iIntros "($ & $ & $)" | iIntros "($ & [$ _] & $)"].
Qed.

(** Writing a selected byte changes only that entry in the owned byte list. *)
Lemma bytes_put b xs (k : nat) y : (k < length xs)%nat ->
  bytes b 0 (take k xs) ∗ ibyte b (Z.of_nat k) y ∗ bytes b (Z.of_nat k + 1) (drop (S k) xs) ⊢
  bytes b 0 (<[k := y]> xs).
Proof using Type.
  intros Hk. rewrite (bytes_at b (<[k := y]> xs) k y); [|apply list_lookup_insert_eq; lia].
  rewrite take_insert_ge; [|lia]. rewrite drop_insert_lt; [|lia]. done.
Qed.

(** A shared reader can borrow one byte and then return it to recover the whole source. *)
Lemma bytesq_at dq b o ys (k : nat) y : ys !! k = Some y ->
  bytesq dq b o ys ⊢ bytesq dq b (o + Z.of_nat k) [y] ∗ (bytesq dq b (o + Z.of_nat k) [y] -∗ bytesq dq b o ys).
Proof using Type.
  intros Hk. rewrite -{1 2}(take_drop_middle ys k y Hk).
  rewrite /bytesq !byte_ps_app !ptsq_app length_take_le; [|apply lookup_lt_Some in Hk; lia].
  rewrite (byte_ps_cons _ _ y (drop (S k) ys)) /byte_ps. cbn [length seqZ].
  iIntros "(Ha & Hb)". rewrite /ptsq !big_sepL_cons. iDestruct "Hb" as "(Hy & Hc)".
  iSplitL "Hy"; [cbn; iFrame; done|]. iIntros "(Hy & _)". iFrame.
Qed.

(** An allocated buffer exposes its storage and the bounds on its current write pointers. *)
Lemma wroom_some b sz wp we :
  wroom (Some (b, sz)) wp we ⊣⊢
  ∃ reg xs cs, ⌜room_ok b sz reg xs cs wp we⌝ ∗ live b reg ∗ bytes b 0 xs ∗ auxes b 0 cs.
Proof using Type. reflexivity. Qed.

End buf.
(** Automatic framing leaves unrelated owned buffers closed. The structural
    instances above still support deliberate construction and destruction. *)
#[global] Hint Opaque wbuf : typeclass_instances.

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
  call_frame Unit_libio_fileops_os.fn__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
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

(** The expression type uses this caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Successful overflow returns the input byte, or zero when the input requests a flush.
    Failure returns EOF instead. *)

(** Overflow borrows the stream's lifetime, jump-table pointer, write buffer and remaining resources.
    It returns those resources with updated buffer pointers and guarantees a buffer even on failure. *)

End ovf.
