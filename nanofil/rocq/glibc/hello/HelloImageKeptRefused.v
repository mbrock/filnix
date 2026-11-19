(** HelloImageKept.v checks the fifteen constants of the gettext route
    against the erased Hello image and carries the check over to the
    genuine memory. A check that cannot fail would prove nothing, so this
    file feeds it wrong pieces on the same erased memory and shows that
    each is refused, while the correct domain pieces pass. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith Bool.
From Nanofil Require Import Term Syntax Values Memory Run Pieces Heap.
From Glibc Require Import HelloGetoptTable HelloGetoptDiagMsgs HelloGettextDomain HelloImageLoad.
From Glibc Require Import ImagePieces HelloImageKept.
Import ListNotations.
Open Scope Z_scope.

(** ## Refusals

    Each wrong input below would let a proof claim bytes that the image
    does not hold. The check refuses a changed message, a message moved
    by one word and a domain object cut short. It also refuses the right
    domain text once the domain is blanked in the copy, because the copy
    then says nothing about the real bytes. The right domain text still
    passes, and one run of the loader serves all five cases. *)

(** This keep set drops the domain. *)
Local Definition keep_no_domain (n : name) : bool :=
  hello_keep n && negb (name_eqb n (TAtom "__GI__libc_intl_domainname")).

(** This is the first message with its first byte changed to zero. *)
Local Definition changed_ps : list (piece * pval) :=
  lits_ps [(img_ob "glibc_getopt#str.138")] [0 :: tail (hd [] dgx_msg_texts)].

(** This is the first message, read at the second message's object. *)
Local Definition moved_ps : list (piece * pval) := lits_ps [(img_ob "glibc_getopt#str.139")] [hd [] dgx_msg_texts].

(** The domain read with an object that ends where it starts. *)
Local Definition short_ps : list (piece * pval) := libc_domain_ps (img_a "__GI__libc_intl_domainname") (gd (img_a "__GI__libc_intl_domainname") (img_a "__GI__libc_intl_domainname")).

Lemma hello_refused :
  match initial_memory hello_skel with
  | Some (g, m') =>
      negb (pieces_ok hello_keep hello_kept g m' changed_ps) && negb (pieces_ok hello_keep hello_kept g m' moved_ps) &&
      negb (pieces_ok hello_keep hello_kept g m' short_ps) &&
      negb (pieces_ok keep_no_domain hello_kept g m' (libc_domain_ps hello_domain_base.1 hello_domain_base.2)) &&
      pieces_ok hello_keep hello_kept g m' (libc_domain_ps hello_domain_base.1 hello_domain_base.2)
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
