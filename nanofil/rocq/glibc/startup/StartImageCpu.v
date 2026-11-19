(** CPU initialization reads a tunable table and small globals.
    Each program can check its initial bytes and give them to the same startup contract. *)

From Glibc Require Fix.
From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list_numbers.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv
  CpuInitSpec.
From Glibc Require Export ImageObjectPieces.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv.
Open Scope Z_scope.

(** ## The contents of the eighteen objects *)

(** These are the names of the eighteen objects, in the order of the
    record [icf_objs]. *)
Definition icf_names : list string :=
  "_dl_x86_cpu_features"%string :: "glibc_dl_tunables#tunable_list"%string ::
  "glibc_libc_start#intel_02_known"%string :: map fst icf_small_globals.

(** Reading one byte of the full initial memory is slow, because that
    memory is built from every initializer of the program. The checks
    below read a smaller memory instead. It keeps the eighteen objects
    and holds zeros everywhere else. This function says which objects
    it keeps. *)
Definition icf_keep (n : name) : bool := existsb (name_eqb n) (map TAtom icf_names).

(** This function reads n bytes of a memory, starting at the address
    b. *)
Definition bytes_at (m : mem) (b n : Z) : list Z := map (fun i => m_bytes m (b + i)) (seqZ 0 n).

(** This function tests that a number is a byte. *)
Definition is_u8 (x : Z) : bool := (0 <=? x) && (x <? 256).

(** A list that passes the test holds only bytes. *)
Lemma bytes_ok xs : forallb is_u8 xs = true -> Forall (fun x => 0 <= x < 256) xs.
Proof.
  induction xs as [|x xs IH]; cbn [forallb]; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [Ha Hb].
  apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. constructor; [lia | exact (IH H2)].
Qed.

(** This function tests that the list xs holds each byte of l at its
    offset. *)
Definition fixed_in (xs : list Z) (l : list (Z * Z)) : bool :=
  forallb (fun ox => match nth_error xs (Z.to_nat (fst ox)) with Some y => y =? snd ox | None => false end) l.

(** A list that passes the test has the fixed bytes in place. *)
Lemma fixed_in_ok xs l : fixed_in xs l = true -> Forall (fun '(o, x) => nth_error xs (Z.to_nat o) = Some x) l.
Proof.
  unfold fixed_in. induction l as [|[o x] l IH]; cbn [forallb]; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|exact (IH H2)]. cbn [fst snd] in H1.
  destruct (nth_error xs (Z.to_nat o)) as [y|]; [|discriminate]. apply Z.eqb_eq in H1. subst y. reflexivity.
Qed.

(** This function tests the contents of the small globals. Each one
    must be as long as its global and must hold only bytes. *)
Fixpoint smalls_ok (gs : list (string * Z)) (xss : list (list Z)) : bool :=
  match gs, xss with
  | [], [] => true
  | g :: gs', xs :: xss' => (length xs =? Z.to_nat (snd g))%nat && forallb is_u8 xs && smalls_ok gs' xss'
  | _, _ => false
  end.

(** ## From the list to the precondition *)

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).

(** Owning the lists of the small globals gives each one in the form
    that the contract asks for. The contract does not care what a
    small global holds, so the known bytes are given up. *)
Lemma smalls_own ge gs : forall qs xss, smalls_ok gs xss = true -> length qs = length gs ->
  pts (concat (zip_with obj_ps qs xss)) ⊢
  [∗ list] g; q ∈ gs; qs, live (fst q) (snd q) ∗
    blk_u8 (glibc_program := program_of w0 glibc_os_registry ge) (fst q) (snd g).
Proof using Type.
  induction gs as [|g gs IH]; intros [|q qs] [|xs xss] Hok Hlen; cbn in Hok, Hlen; try discriminate.
  - iIntros "_". done.
  - cbn [zip_with concat]. rewrite pts_app obj_ps_own.
    apply andb_prop in Hok as [Hok Hr]. apply andb_prop in Hok as [Hl Hb]. apply Nat.eqb_eq in Hl.
    iIntros "((L & Hx & Ha) & Hr)". rewrite big_sepL2_cons. iFrame "L". iSplitL "Hx Ha".
    + iApply (blk_u8_intro (glibc_program := program_of w0 glibc_os_registry ge) (fst q) (snd g) xs
                (repeat CNone (length xs)) with "Hx Ha");
        [exact Hl | rewrite repeat_length; exact Hl | exact (bytes_ok _ Hb)].
    + iApply (IH with "Hr"); [exact Hr | lia].
Qed.

End image.
