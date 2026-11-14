From T Require Import Lib.
Module Type S. Parameter l0 : 0 = 0. End S.
(* A field supplied by an included library. *)
Module M : S. Include Lib. End M.
(* A field supplied by a sealed functor application. *)
Module Type FS (X : S). Parameter l1 : 0 = 0. End FS.
Module F (X : S) : FS X. Lemma l1 : 0 = 0. Proof. exact X.l0. Qed. End F.
Module A := F M.
Lemma q : 0 = 0 /\ 0 = 0. Proof. exact (conj M.l0 A.l1). Qed.
Print Assumptions q.
