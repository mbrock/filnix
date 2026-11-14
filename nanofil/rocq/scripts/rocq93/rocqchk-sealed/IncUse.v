From T Require Import IncLib.
Module Type S.
Parameter p_ok : forall x, IncLib.p x -> True.
End S.
Module M : S.
Include IncLib.
Lemma p_ok : forall x, p x -> True. Proof. auto. Qed.
End M.
