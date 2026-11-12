(** These libc contracts belong to the earlier contract-based campaign.
    They remain available for the Hello proof and program examples.
    Their call relation comes from [ExternalCalls](../external/ExternalCalls.v),
    which the live glibc campaign uses independently. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine Identity ExternalCalls ExternalMachine.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** strlen returns a size_t (class L) and takes exactly one pointer. *)
Definition strlen_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists p, args = [Arg P p].

(** Pure trusted strlen. Its input names the object life and the byte
    span through the first NUL; no auxiliary slots are read to compute
    the result. Empty sources prohibit capability propagation, not reads.
    All memory, including regions and auxiliary slots, is preserved;
    no allocation, release, observation or resource ending is permitted. *)
Definition strlen_contract (world : Type) : contract world :=
  mkContract world (RClass L) strlen_abi
    (fun xs m _ => exists p k, xs = [WPtr p] /\ terminated_length m p k)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p k, xs = [WPtr p] /\ terminated_length m p k /\ ending = CallReturn [WInt k])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** strnlen returns a size_t (class L) and takes a pointer and size_t.
    Discarding the result does not change the callee's return shape. *)
Definition strnlen_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists p n, args = [Arg P p; Arg L n].

(** A pure, read-only trusted API contract over any logical world.
    Empty sources govern capability propagation, not all byte reads:
    those are justified by [bounded_length]. No writes, releases,
    allocations, events or resource outcomes are authorized. Empty
    prefixes allow no visible progress without promising termination.
    Panic annotations describe violated premises, not native behavior
    for every invalid input (notably zero-count null pointers). *)
Definition strnlen_contract (world : Type) : contract world :=
  mkContract world (RClass L) strnlen_abi
    (fun xs m _ => exists p n k, xs = [WPtr p; WInt n] /\ bounded_length m p n k)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p n k, xs = [WPtr p; WInt n] /\ bounded_length m p n k /\ ending = CallReturn [WInt k])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** memchr reads sequentially through its first matching byte, or the
    whole bound on a miss. The memory-only stop witness does not assume
    an invocation or its returned pointer. Zero count retains the live
    capability requirement of [readable_bytes]. *)
Definition memchr_input (m : mem) (p : ptr) (c n : Z) : Prop :=
  0 <= c < 2 ^ 32 /\ 0 <= n < 2 ^ 64 /\
  exists k, 0 <= k <= n /\
    readable_bytes m p (k + (if k <? n then 1 else 0)) /\
    (forall i, 0 <= i < k -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
    (k < n -> m_bytes m (ptr_addr p + k) = c mod 256).

(** A hit is the first matching byte, with exactly the input capability;
    a miss is null. The int's low byte implements unsigned-char
    conversion, including negative C ints already normalized at class W. *)
Definition memchr_result (m : mem) (p : ptr) (c n : Z) (q : ptr) : Prop :=
  (exists k, 0 <= k < n /\ m_bytes m (ptr_addr p + k) = c mod 256 /\
    (forall i, 0 <= i < k -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
    q = mkPtr (ptr_addr p + k) (ptr_cap p)) \/
  ((forall i, 0 <= i < n -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
    q = mkPtr 0 CNone).

(** Finite first-match existence is constructive and independent of
    invocation existence or memory authority. It is not a libc executor
    or a native termination theorem. Extend the interval on the right. *)
Lemma memchr_result_total : forall m p c n,
  0 <= n -> exists q, memchr_result m p c n q.
Proof.
  intros m p c n Hn.
  assert (Hfinite : forall count : nat, exists q, memchr_result m p c (Z.of_nat count) q).
  { induction count as [|count [q Hq]].
    - exists (mkPtr 0 CNone). right. split; [intros i Hi; lia|reflexivity].
    - destruct Hq as [(k & Hk & Hbyte & Hbefore & ->) | (Hmiss & ->)].
      + exists (mkPtr (ptr_addr p + k) (ptr_cap p)). left. exists k.
        rewrite Nat2Z.inj_succ. repeat split; auto; lia.
      + destruct (Z.eq_dec (m_bytes m (ptr_addr p + Z.of_nat count)) (c mod 256)) as [Heq | Hneq].
        * exists (mkPtr (ptr_addr p + Z.of_nat count) (ptr_cap p)). left.
          exists (Z.of_nat count). rewrite Nat2Z.inj_succ. repeat split; auto; lia.
        * exists (mkPtr 0 CNone). right. split; [|reflexivity].
          intros i Hi. rewrite Nat2Z.inj_succ in Hi.
          destruct (Z_lt_dec i (Z.of_nat count)); [apply Hmiss; lia|].
          replace i with (Z.of_nat count) by lia. exact Hneq. }
  replace n with (Z.of_nat (Z.to_nat n)) by (rewrite Z2Nat.id; lia). apply Hfinite.
Qed.

(** Existing full-span callers remain admitted. Early hits no longer
    require their unused suffix to be inside the object. *)
Lemma memchr_input_full : forall m p c n,
  0 <= c < 2 ^ 32 -> readable_bytes m p n -> memchr_input m p c n.
Proof.
  intros m p c n Hc Hread.
  pose proof (proj1 Hread) as Hn.
  split; [exact Hc|]. split; [exact Hn|].
  destruct (memchr_result_total m p c n ltac:(lia)) as [q [(k & Hk & Hbyte & Hbefore & _) | (Hmiss & _)]].
  - exists k. split; [lia|]. split.
    + rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hk)). eapply readable_bytes_prefix; [exact Hread|lia].
    + auto.
  - exists n. rewrite Z.ltb_irrefl. simpl. rewrite Z.add_0_r.
    split; [lia|]. split; [exact Hread|]. split; [exact Hmiss|intros; lia].
Qed.

(** The admitted stop witness constructs a result without searching an
    inaccessible suffix, even when the maximum is SIZE_MAX. *)
Lemma memchr_input_result : forall m p c n,
  memchr_input m p c n -> exists q, memchr_result m p c n q.
Proof.
  intros m p c n (_ & _ & k & Hk & _ & Hbefore & Hmatch).
  destruct (Z_lt_dec k n) as [Hlt|Hlast].
  - exists (mkPtr (ptr_addr p + k) (ptr_cap p)). left. exists k.
    split; [lia|]. split; [apply Hmatch; exact Hlt|]. auto.
  - exists (mkPtr 0 CNone). right. split; [|reflexivity].
    intros i Hi. apply Hbefore. lia.
Qed.

(** First-match order fixes the entire returned pointer, not only its
    numeric address or an available capability. *)
Lemma memchr_result_unique : forall m p c n left right,
  memchr_result m p c n left -> memchr_result m p c n right -> left = right.
Proof.
  intros m p c n left right Hl Hr.
  destruct Hl as [(l & Hl & Hbl & Hbeforel & ->) | (Hmissl & ->)];
    destruct Hr as [(r & Hr & Hbr & Hbeforer & ->) | (Hmissr & ->)].
  - assert (l = r).
    { destruct (Z.lt_trichotomy l r) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
      - exfalso. apply (Hbeforer l ltac:(lia)). exact Hbl.
      - exfalso. apply (Hbeforel r ltac:(lia)). exact Hbr. }
    subst. reflexivity.
  - exfalso. apply (Hmissr l Hl). exact Hbl.
  - exfalso. apply (Hmissl r Hr). exact Hbr.
  - reflexivity.
Qed.

(** A memchr result has only source-pointer authority, or none for a
    miss. The exact provenance requirement remains [memchr_result]. *)
Lemma memchr_result_authority : forall m p c n q,
  memchr_result m p c n q -> available_cap [mkSpan p n] [] m (ptr_cap q).
Proof.
  intros m p c n q [(k & _ & _ & _ & ->) | (_ & ->)].
  - right. left. exists (mkSpan p n). split; [left; reflexivity|reflexivity].
  - left. reflexivity.
Qed.

(** memchr returns a pointer and takes a pointer, int and size_t. *)
Definition memchr_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\
  exists p c n, args = [Arg P p; Arg W c; Arg L n].

(** Pure trusted search with one capability source and no mutation,
    allocation or resource permission. Admission requires only the
    input domain and first-match prefix, not a supplied result or invocation.
    Its source span is a capability propagation envelope, not the consumed
    byte-read footprint; [memchr_result] allows only the input cap or null. *)
Definition memchr_contract (world : Type) : contract world :=
  mkContract world (RClass P) memchr_abi
    (fun xs m _ => exists p c n, xs = [WPtr p; WInt c; WInt n] /\ memchr_input m p c n)
    (fun xs _ _ => match xs with [WPtr p; WInt _; WInt n] => [mkSpan p n] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p c n q, xs = [WPtr p; WInt c; WInt n] /\ memchr_result m p c n q /\
        ending = CallReturn [WPtr q])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Bounded binary comparisons *)

(** Lexicographic byte order: either every pair is equal, or the first
    differing pair fixes the order. Both pointers refer to the same
    memory; overlap and identical spans are permitted. Readability and
    unsigned-byte domains are separate admission obligations. *)
Definition memcmp_order (m : mem) (p q : ptr) (n : Z) (ordering : comparison) : Prop :=
  (ordering = Datatypes.Eq /\
    forall i, 0 <= i < n -> m_bytes m (ptr_addr p + i) = m_bytes m (ptr_addr q + i)) \/
  (exists k, 0 <= k < n /\
    (forall i, 0 <= i < k -> m_bytes m (ptr_addr p + i) = m_bytes m (ptr_addr q + i)) /\
    m_bytes m (ptr_addr p + k) <> m_bytes m (ptr_addr q + k) /\
    ordering = Z.compare (m_bytes m (ptr_addr p + k)) (m_bytes m (ptr_addr q + k))).

(** A finite interval has a first difference or is equal throughout.
    This constructive existence does not assume invocation coverage. *)
Lemma memcmp_order_total : forall m p q n,
  0 <= n -> exists ordering, memcmp_order m p q n ordering.
Proof.
  intros m p q n Hn.
  assert (Hfinite : forall count : nat, exists ordering, memcmp_order m p q (Z.of_nat count) ordering).
  { induction count as [|count [ordering Horder]].
    - exists Datatypes.Eq. left. split; [reflexivity|intros i Hi; lia].
    - destruct Horder as [(-> & Hsame) | (k & Hk & Hbefore & Hdifferent & ->)].
      + destruct (Z.eq_dec (m_bytes m (ptr_addr p + Z.of_nat count))
          (m_bytes m (ptr_addr q + Z.of_nat count))) as [Heq | Hneq].
        * exists Datatypes.Eq. left. split; [reflexivity|]. intros i Hi.
          rewrite Nat2Z.inj_succ in Hi. destruct (Z_lt_dec i (Z.of_nat count)).
          -- apply Hsame. lia.
          -- replace i with (Z.of_nat count) by lia. exact Heq.
        * eexists. right. exists (Z.of_nat count). rewrite Nat2Z.inj_succ.
          repeat split; auto; lia.
      + eexists. right. exists k. rewrite Nat2Z.inj_succ. repeat split; auto; lia. }
  replace n with (Z.of_nat (Z.to_nat n)) by (rewrite Z2Nat.id; lia). apply Hfinite.
Qed.

(** The first differing pair fixes the order uniquely, not the returned
    int's magnitude. An equal prefix rules out a competing earlier pair. *)
Lemma memcmp_order_unique : forall m p q n left right,
  memcmp_order m p q n left -> memcmp_order m p q n right -> left = right.
Proof.
  intros m p q n left right Hl Hr.
  destruct Hl as [(-> & Hsamel) | (l & Hl & Hbeforel & Hdiffl & ->)];
    destruct Hr as [(-> & Hsamer) | (r & Hr & Hbeforer & Hdiffr & ->)].
  - reflexivity.
  - exfalso. apply Hdiffr. apply Hsamel. exact Hr.
  - exfalso. apply Hdiffl. apply Hsamer. exact Hl.
  - assert (l = r).
    { destruct (Z.lt_trichotomy l r) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
      - exfalso. apply Hdiffl. apply Hbeforer. lia.
      - exfalso. apply Hdiffr. apply Hbeforel. lia. }
    subst. reflexivity.
Qed.

(** A canonical class-W bit pattern whose signed reading has the byte
    order's sign. All representable correct magnitudes are permitted,
    not merely minus/plus one or the first byte difference. *)
Definition memcmp_result (m : mem) (p q : ptr) (n bits : Z) : Prop :=
  0 <= bits < 2 ^ 32 /\ exists ordering, memcmp_order m p q n ordering /\
    Z.compare (sign_extension (2 ^ 32) (2 ^ 31) bits) 0 = ordering.

(** Every finite comparison permits a canonical zero, negative or
    positive witness. Other magnitudes remain permitted by the contract. *)
Lemma memcmp_result_total : forall m p q n,
  0 <= n -> exists bits, memcmp_result m p q n bits.
Proof.
  intros m p q n Hn. destruct (memcmp_order_total m p q n Hn) as [ordering Horder].
  destruct ordering; [exists 0|exists (2 ^ 32 - 1)|exists 1].
  all: split; [vm_compute; split; congruence|]; eexists; split; [exact Horder|reflexivity].
Qed.

(** Permitted result words may differ, but their signed signs agree. *)
Lemma memcmp_result_sign_unique : forall m p q n left right,
  memcmp_result m p q n left -> memcmp_result m p q n right ->
  Z.compare (sign_extension (2 ^ 32) (2 ^ 31) left) 0 =
    Z.compare (sign_extension (2 ^ 32) (2 ^ 31) right) 0.
Proof.
  intros m p q n left right (_ & ol & Hl & El) (_ & or & Hr & Er).
  rewrite El, Er. eapply memcmp_order_unique; eauto.
Qed.

(** memcmp returns an int and takes two pointers and a size_t. *)
Definition memcmp_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\
  exists p q n, args = [Arg P p; Arg P q; Arg L n].

(** Pure trusted binary comparison. Both full spans must be readable,
    even at zero count or an early difference. There is no capability
    propagation, mutation, allocation or resource outcome. *)
Definition memcmp_contract (world : Type) : contract world :=
  mkContract world (RClass W) memcmp_abi
    (fun xs m _ => exists p q n, xs = [WPtr p; WPtr q; WInt n] /\
      readable_bytes m p n /\ readable_bytes m q n)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p q n bits, xs = [WPtr p; WPtr q; WInt n] /\ memcmp_result m p q n bits /\
        ending = CallReturn [WInt bits])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Bounded string comparisons *)

(** A logical comparison window includes an earlier terminator, but
    never byte n. These are mathematical integers: adding one before
    taking the minimum must not wrap at SIZE_MAX. A first difference
    can decide the result earlier than the end of this window. *)
Definition strncmp_window (n left right : Z) : Z :=
  Z.min n (Z.min (left + 1) (right + 1)).

(** The window fits both independently justified consumed intervals. *)
Lemma strncmp_window_bounds : forall n left right,
  0 <= left <= n -> 0 <= right <= n ->
  0 <= strncmp_window n left right /\ strncmp_window n left right <= n /\
  strncmp_window n left right <= left + (if left <? n then 1 else 0) /\
  strncmp_window n left right <= right + (if right <? n then 1 else 0).
Proof.
  intros n left right Hl Hr.
  assert (Hzero : 0 <= strncmp_window n left right).
  { unfold strncmp_window. apply Z.min_glb; [lia|]. apply Z.min_glb; lia. }
  assert (Hn : strncmp_window n left right <= n) by apply Z.le_min_l.
  assert (Hleft : strncmp_window n left right <= left + 1).
  { eapply Z.le_trans; [apply Z.le_min_r|apply Z.le_min_l]. }
  assert (Hright : strncmp_window n left right <= right + 1).
  { eapply Z.le_trans; [apply Z.le_min_r|apply Z.le_min_r]. }
  repeat split; try assumption.
  - destruct (left <? n) eqn:E; [lia|]. apply Z.ltb_ge in E. lia.
  - destruct (right <? n) eqn:E; [lia|]. apply Z.ltb_ge in E. lia.
Qed.

(** Both sides can read every byte on which the comparison depends.
    Total model memory alone would not establish this authority fact. *)
Lemma strncmp_window_readable : forall m p q n left right,
  bounded_length m p n left -> bounded_length m q n right ->
  readable_bytes m p (strncmp_window n left right) /\
  readable_bytes m q (strncmp_window n left right).
Proof.
  intros m p q n left right Hl Hr.
  destruct (strncmp_window_bounds n left right (proj1 (proj2 Hl)) (proj1 (proj2 Hr)))
    as (Hzero & _ & Hleft & Hright).
  split; eapply bounded_prefix_readable; eauto; lia.
Qed.

(** The sign comes from the logical window, using the original memory
    and independently witnessed bounded strings. Magnitudes stay free. *)
Definition strncmp_result (m : mem) (p q : ptr) (n bits : Z) : Prop :=
  exists left right, bounded_length m p n left /\ bounded_length m q n right /\
    memcmp_result m p q (strncmp_window n left right) bits.

(** Result existence follows from input obligations, not call coverage. *)
Lemma strncmp_result_total : forall m p q n left right,
  bounded_length m p n left -> bounded_length m q n right ->
  exists bits, strncmp_result m p q n bits.
Proof.
  intros m p q n left right Hl Hr.
  destruct (strncmp_window_readable m p q n left right Hl Hr) as [Hread _].
  destruct (memcmp_result_total m p q (strncmp_window n left right)
    ltac:(destruct Hread as [Hn _]; lia)) as [bits Hbits].
  exists bits, left, right. auto.
Qed.

(** First-NUL uniqueness fixes the window; only the signed sign of
    permitted return words is unique, not their integer magnitude. *)
Lemma strncmp_result_sign_unique : forall m p q n left right,
  strncmp_result m p q n left -> strncmp_result m p q n right ->
  Z.compare (sign_extension (2 ^ 32) (2 ^ 31) left) 0 =
    Z.compare (sign_extension (2 ^ 32) (2 ^ 31) right) 0.
Proof.
  intros m p q n left right (ll & lr & Hll & Hlr & Hl) (rl & rr & Hrl & Hrr & Hr).
  pose proof (bounded_length_unique _ _ _ _ _ Hll Hrl) as <-.
  pose proof (bounded_length_unique _ _ _ _ _ Hlr Hrr) as <-.
  eapply memcmp_result_sign_unique; eauto.
Qed.

(** Pure trusted strncmp, with memcmp's unchanged P/P/L-to-W ABI.
    The table's independent bounded-string premises are conservative:
    an early difference does not waive an invalid suffix on either side.
    Empty sources mean no capability propagation, not an absence of reads. *)
Definition strncmp_contract (world : Type) : contract world :=
  mkContract world (RClass W) memcmp_abi
    (fun xs m _ => exists p q n left right, xs = [WPtr p; WPtr q; WInt n] /\
      bounded_length m p n left /\ bounded_length m q n right)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p q n bits, xs = [WPtr p; WPtr q; WInt n] /\ strncmp_result m p q n bits /\
        ending = CallReturn [WInt bits])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Unbounded string comparisons *)

(** Both terminated strings authorize the comparison window through the
    earlier NUL. Admission still depends on each complete string through
    its own NUL, including the longer string's tail outside this window. *)
Lemma strcmp_window_readable : forall m p q left right,
  terminated_length m p left -> terminated_length m q right ->
  readable_bytes m p (Z.min (left + 1) (right + 1)) /\
  readable_bytes m q (Z.min (left + 1) (right + 1)).
Proof.
  intros m p q left right [Hl Hleft] [Hr Hright].
  pose proof (strncmp_window_readable m p q (2 ^ 64 - 1) left right Hl Hr) as Hread.
  unfold strncmp_window in Hread. rewrite Z.min_r in Hread; [exact Hread|].
  eapply Z.le_trans; [apply Z.le_min_l|lia].
Qed.

(** strcmp compares unsigned bytes through the earlier terminator.
    Independent complete-string witnesses govern admission; only the
    signed sign of the canonical int result is specified, not magnitude. *)
Definition strcmp_result (m : mem) (p q : ptr) (bits : Z) : Prop :=
  exists left right, terminated_length m p left /\ terminated_length m q right /\
    memcmp_result m p q (Z.min (left + 1) (right + 1)) bits.

(** Terminated inputs construct a result independently of invocation
    existence; window readability is proved before using total memory. *)
Lemma strcmp_result_total : forall m p q left right,
  terminated_length m p left -> terminated_length m q right ->
  exists bits, strcmp_result m p q bits.
Proof.
  intros m p q left right Hl Hr.
  destruct (strcmp_window_readable m p q left right Hl Hr) as [Hread _].
  destruct (memcmp_result_total m p q (Z.min (left + 1) (right + 1))
    ltac:(destruct Hread as [Hn _]; lia)) as [bits Hbits].
  exists bits, left, right. auto.
Qed.

(** Unique first-NUL lengths fix the window, hence the result's signed
    sign. Distinct representable magnitudes of that sign remain legal. *)
Lemma strcmp_result_sign_unique : forall m p q left right,
  strcmp_result m p q left -> strcmp_result m p q right ->
  Z.compare (sign_extension (2 ^ 32) (2 ^ 31) left) 0 =
    Z.compare (sign_extension (2 ^ 32) (2 ^ 31) right) 0.
Proof.
  intros m p q left right (ll & lr & Hll & Hlr & Hl) (rl & rr & Hrl & Hrr & Hr).
  pose proof (terminated_length_unique _ _ _ _ Hll Hrl) as <-.
  pose proof (terminated_length_unique _ _ _ _ Hlr Hrr) as <-.
  eapply memcmp_result_sign_unique; eauto.
Qed.

(** strcmp returns an int and takes exactly two pointer arguments, no count. *)
Definition strcmp_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists p q, args = [Arg P p; Arg P q].

(** Pure trusted strcmp over two independent live terminated strings.
    The input footprint is both referenced identities' regions and each
    string's bytes through its NUL; no auxiliary slots are read. The
    result compares only the minimum window. All memory and world are
    preserved, with no writes, propagation, allocation or release. *)
Definition strcmp_contract (world : Type) : contract world :=
  mkContract world (RClass W) strcmp_abi
    (fun xs m _ => exists p q left right, xs = [WPtr p; WPtr q] /\
      terminated_length m p left /\ terminated_length m q right)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p q bits, xs = [WPtr p; WPtr q] /\ strcmp_result m p q bits /\
        ending = CallReturn [WInt bits])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Unbounded character search *)

(** strchr selects the first low-byte match through the first NUL,
    including that NUL when searched for, with exactly the source's
    capability; a miss is null. Full string admission is independent
    of an early match. The int's canonical domain is checked separately. *)
Definition strchr_result (m : mem) (p : ptr) (c : Z) (q : ptr) : Prop :=
  exists k, terminated_length m p k /\ memchr_result m p c (k + 1) q.

(** Input string authority constructs a first match or miss, after
    proving readability. This is nonvacuity, not native termination. *)
Lemma strchr_result_total : forall m p c k,
  terminated_length m p k -> exists q, strchr_result m p c q.
Proof.
  intros m p c k Hlength.
  pose proof (terminated_length_readable m p k Hlength) as [Hspan _].
  destruct (memchr_result_total m p c (k + 1) ltac:(lia)) as [q Hq].
  exists q, k. auto.
Qed.

(** First-NUL and first-match uniqueness fix the full returned pointer,
    including its capability rather than just its numeric address. *)
Lemma strchr_result_unique : forall m p c left right,
  strchr_result m p c left -> strchr_result m p c right -> left = right.
Proof.
  intros m p c left right (kl & Hl & Hleft) (kr & Hr & Hright).
  pose proof (terminated_length_unique _ _ _ _ Hl Hr) as <-.
  eapply memchr_result_unique; eauto.
Qed.

(** A zero-size source permits p's own capability, not any auxiliary
    slot. This is capability provenance, not the string's read footprint. *)
Lemma strchr_result_authority : forall m p c q,
  strchr_result m p c q -> available_cap [mkSpan p 0] [] m (ptr_cap q).
Proof.
  intros m p c q (k & _ & [(i & _ & _ & _ & ->) | (_ & ->)]).
  - right. left. exists (mkSpan p 0). split; [left; reflexivity|reflexivity].
  - left. reflexivity.
Qed.

(** A low-byte-zero search necessarily returns the readable terminator
    with the source capability; null or a later pointer cannot qualify. *)
Lemma strchr_result_nul : forall m p c q k,
  terminated_length m p k -> strchr_result m p c q -> c mod 256 = 0 ->
  q = mkPtr (ptr_addr p + k) (ptr_cap p).
Proof.
  intros m p c q k Hlength Hresult Hzero.
  eapply strchr_result_unique; [exact Hresult|]. exists k. split; [exact Hlength|].
  destruct Hlength as [(_ & Hk & _ & _ & Hbytes & Hnul) Hmax].
  left. exists k. split; [lia|]. split.
  - rewrite Hzero. apply Hnul. exact Hmax.
  - split; [|reflexivity]. intros i Hi. specialize (Hbytes i Hi). rewrite Hzero. lia.
Qed.

(** strchr returns a pointer and takes exactly a pointer and an int. *)
Definition strchr_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ exists p c, args = [Arg P p; Arg W c].

(** Pure trusted strchr. Read dependencies are the source identity's
    region/life and bytes through its own NUL; auxiliary slots are not
    dependencies. The zero-size capability source permits returning p's
    own authority only, not zero byte reads or pointer-slot imports.
    No ownership transfers: a hit retains the source capability and is
    invalidated when that object's lifetime ends. No memory is changed. *)
Definition strchr_contract (world : Type) : contract world :=
  mkContract world (RClass P) strchr_abi
    (fun xs m _ => exists p c k, xs = [WPtr p; WInt c] /\
      0 <= c < 2 ^ 32 /\ terminated_length m p k)
    (fun xs _ _ => match xs with [WPtr p; WInt _] => [mkSpan p 0] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p c q, xs = [WPtr p; WInt c] /\ 0 <= c < 2 ^ 32 /\ strchr_result m p c q /\
        ending = CallReturn [WPtr q])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** strrchr selects the last low-byte match through the first NUL,
    retaining the exact source capability, or returns canonical null.
    Earlier matches are permitted; later matches in the string are not. *)
Definition strrchr_result (m : mem) (p : ptr) (c : Z) (q : ptr) : Prop :=
  exists k, terminated_length m p k /\
    ((exists i, 0 <= i <= k /\ m_bytes m (ptr_addr p + i) = c mod 256 /\
      (forall j, i < j <= k -> m_bytes m (ptr_addr p + j) <> c mod 256) /\
      q = mkPtr (ptr_addr p + i) (ptr_cap p)) \/
     ((forall i, 0 <= i <= k -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
      q = mkPtr 0 CNone)).

(** Constructive last-match existence uses a local finite-interval
    induction, not an assumption that a shorter prefix is terminated.
    Independent string authority justifies the complete readable span. *)
Lemma strrchr_result_total : forall m p c k,
  terminated_length m p k -> exists q, strrchr_result m p c q.
Proof.
  intros m p c k Hlength.
  pose proof (terminated_length_readable m p k Hlength) as [Hspan _].
  assert (Hfinite : forall count : nat, exists q,
    (exists i, 0 <= i < Z.of_nat count /\ m_bytes m (ptr_addr p + i) = c mod 256 /\
      (forall j, i < j < Z.of_nat count -> m_bytes m (ptr_addr p + j) <> c mod 256) /\
      q = mkPtr (ptr_addr p + i) (ptr_cap p)) \/
    ((forall i, 0 <= i < Z.of_nat count -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
      q = mkPtr 0 CNone)).
  { induction count as [|count [q Hq]].
    - exists (mkPtr 0 CNone). right. split; [intros i Hi; lia|reflexivity].
    - destruct (Z.eq_dec (m_bytes m (ptr_addr p + Z.of_nat count)) (c mod 256)) as [Heq | Hneq].
      + exists (mkPtr (ptr_addr p + Z.of_nat count) (ptr_cap p)). left.
        exists (Z.of_nat count). rewrite Nat2Z.inj_succ.
        split; [lia|]. split; [exact Heq|]. split; [intros j Hj; lia|reflexivity].
      + exists q. destruct Hq as [(i & Hi & Hbyte & Hlater & ->) | (Hmiss & ->)].
        * left. exists i. rewrite Nat2Z.inj_succ. split; [lia|].
          split; [exact Hbyte|]. split; [|reflexivity]. intros j Hj.
          destruct (Z_lt_dec j (Z.of_nat count)); [apply Hlater; lia|].
          replace j with (Z.of_nat count) by lia. exact Hneq.
        * right. split; [|reflexivity]. intros i Hi. rewrite Nat2Z.inj_succ in Hi.
          destruct (Z_lt_dec i (Z.of_nat count)); [apply Hmiss; lia|].
          replace i with (Z.of_nat count) by lia. exact Hneq. }
  destruct (Hfinite (Z.to_nat (k + 1))) as [q Hq].
  rewrite Z2Nat.id in Hq by lia. exists q, k. split; [exact Hlength|].
  destruct Hq as [(i & Hi & Hbyte & Hlater & ->) | (Hmiss & ->)].
  - left. exists i. split; [lia|]. split; [exact Hbyte|].
    split; [intros j Hj; apply Hlater; lia|reflexivity].
  - right. split; [intros i Hi; apply Hmiss; lia|reflexivity].
Qed.

(** The shared first-NUL boundary and last-match exclusion fix the
    full returned pointer, not just its address. *)
Lemma strrchr_result_unique : forall m p c left right,
  strrchr_result m p c left -> strrchr_result m p c right -> left = right.
Proof.
  intros m p c left right (kl & Hl & Hleft) (kr & Hr & Hright).
  pose proof (terminated_length_unique _ _ _ _ Hl Hr) as <-.
  destruct Hleft as [(i & Hi & Hbyte & Hlater & ->) | (Hmiss & ->)];
    destruct Hright as [(j & Hj & Hother & Hafter & ->) | (Hnone & ->)].
  - destruct (Z.lt_trichotomy i j) as [Hij | [-> | Hji]]; [|reflexivity|].
    + exfalso. apply (Hlater j ltac:(lia)). exact Hother.
    + exfalso. apply (Hafter i ltac:(lia)). exact Hbyte.
  - exfalso. apply (Hnone i Hi). exact Hbyte.
  - exfalso. apply (Hmiss j Hj). exact Hother.
  - reflexivity.
Qed.

(** Last-match returns need only the source pointer's capability, not
    any auxiliary slot or capability from a different object. *)
Lemma strrchr_result_authority : forall m p c q,
  strrchr_result m p c q -> available_cap [mkSpan p 0] [] m (ptr_cap q).
Proof.
  intros m p c q (k & _ & [(i & _ & _ & _ & ->) | (_ & ->)]).
  - right. left. exists (mkSpan p 0). split; [left; reflexivity|reflexivity].
  - left. reflexivity.
Qed.

(** The readable NUL is a last match for every low-byte-zero argument,
    since the logical search interval has no later index. *)
Lemma strrchr_result_nul : forall m p c q k,
  terminated_length m p k -> strrchr_result m p c q -> c mod 256 = 0 ->
  q = mkPtr (ptr_addr p + k) (ptr_cap p).
Proof.
  intros m p c q k Hlength Hresult Hzero.
  eapply strrchr_result_unique; [exact Hresult|]. exists k. split; [exact Hlength|].
  destruct Hlength as [(_ & Hk & _ & _ & _ & Hnul) Hmax].
  left. exists k. split; [lia|]. split.
  - rewrite Hzero. apply Hnul. exact Hmax.
  - split; [intros j Hj; lia|reflexivity].
Qed.

(** Pure trusted strrchr shares strchr's ABI and propagation source,
    but selects the last match. Its full read dependencies are the
    referenced identity's region/life and bytes through NUL, not aux.
    The zero-size source is not a read footprint. A hit retains Obj or
    Ro with no ownership transfer or lifetime extension, becoming invalid
    when the source object dies. Memory/world remain exactly unchanged. *)
Definition strrchr_contract (world : Type) : contract world :=
  mkContract world (RClass P) strchr_abi
    (fun xs m _ => exists p c k, xs = [WPtr p; WInt c] /\
      0 <= c < 2 ^ 32 /\ terminated_length m p k)
    (fun xs _ _ => match xs with [WPtr p; WInt _] => [mkSpan p 0] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p c q, xs = [WPtr p; WInt c] /\ 0 <= c < 2 ^ 32 /\ strrchr_result m p c q /\
        ending = CallReturn [WPtr q])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Thread-local errno lookup

    The errno contract returns a pointer to the current thread's error cell.
    Its representation must justify that cell's lifetime and write permission. *)

(** Plain __errno_location takes no arguments and returns P, including
    when the caller discards that result. Tuples are not scalar returns. *)
Definition errno_location_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ args = [].

(** The representation independently ties the selected cell to the
    current thread. Its zero-length source exports that exact capability,
    not arbitrary stored pointers. Looking it up neither writes errno
    nor changes the world, allocates, releases, emits events or fails for
    resources. No cross-thread lifetime/stability theorem is implied. *)
Definition errno_location_contract (world : Type) (cell : world -> ptr)
    (rep : mem -> world -> Prop) : contract world :=
  mkContract world (RClass P) errno_location_abi
    (fun xs m w => xs = [] /\ rep m w /\ errno_cell m (cell w))
    (fun _ _ w => [mkSpan (cell w) 0])
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun _ m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      ending = CallReturn [WPtr (cell w)])
    (fun _ => False)
    (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Fresh allocation *)

(** malloc takes one size_t and returns a pointer, or its result is
    discarded. Width coincidence does not admit a W argument. *)
Definition malloc_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ exists n, args = [Arg L n].

(** The one permitted request shape; this does not count attempts. *)
Definition malloc_request (xs : list word) (align size : Z) : Prop :=
  exists n, xs = [WInt n] /\ align = 16 /\ size = n.

(** One successful allocation, including its independent freshness
    and legal original size. No old byte or auxiliary cell changes. *)
Definition malloc_result (m : mem) (n base : Z) (m' : mem) : Prop :=
  0 <= n <= max_allocation_size /\ fresh m (heap_req 16 n) base /\
  m' = allocated m (heap_req 16 n) base.

(** A logical allocation prefix is either unchanged or one-born.
    The generic resource rule can refuse a further permitted request
    after the one-born prefix. This terminal overapproximation is
    explicit: it is not a native two-request claim, nor a guarantee
    that every failure leaves the region list unchanged. *)
Definition malloc_prefix (m : mem) (n : Z) (born : list Z) (m' : mem) : Prop :=
  (born = [] /\ m' = m) \/
  exists base, born = [base] /\ malloc_result m n base m'.

(** The selected Fil-C malloc calls zgc_alloc, which does not return
    NULL on refusal. Refusal is a resource ending, never a panic.
    Exact endpoint framing is logical; native collector prefixes at
    allocation safepoints remain a correspondence obligation. *)
Definition malloc_contract (world : Type) : contract world :=
  mkContract world (RClass P) malloc_abi
    (fun xs _ _ => exists n, xs = [WInt n] /\ 0 <= n < 2 ^ 64)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun xs _ _ => malloc_request xs)
    (fun xs m w born trace m' w' => trace = [] /\ w' = w /\
      exists n, xs = [WInt n] /\ malloc_prefix m n born m')
    (fun xs m w born trace ending m' w' => trace = [] /\ w' = w /\
      exists n base, xs = [WInt n] /\ born = [base] /\ malloc_result m n base m' /\
        ending = CallReturn [WPtr (mkPtr base (Obj base))])
    resource_reason (fun why => In why [ArgumentSize; ReturnSize]).

(** Rounded capacity covers n, with strictly less than 16 extra
    bytes. Zero has zero modeled extent and grants no byte access. *)
Lemma malloc_extent : forall n, 0 <= n ->
  n <= req_extent (heap_req 16 n) < n + 16.
Proof.
  intros n Hn. change (n <= (n + 15) / 16 * 16 < n + 16).
  pose proof (Z.div_mod (n + 15) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)). lia.
Qed.

(** The exact endpoint frames old objects as well as both cell maps. *)
Lemma malloc_old_cells : forall m n base m', malloc_result m n base m' ->
  (forall a, m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a) /\
  (forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg).
Proof.
  intros m n base m' (_ & (_ & _ & _ & Hnew & _) & ->).
  split; [intros; split; reflexivity|]. intros. eapply allocated_old_region; eauto.
Qed.

(** ## Computing exact string footprints *)

(** A total bounded logical scan, not an implementation of libc.
    Exhaustion returns the bound; admission still requires a NUL. *)
Fixpoint nul_count (bytes : Z -> Z) (a : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if bytes a =? 0 then 0 else 1 + nul_count bytes (a + 1) fuel'
  end.

(** Remaining bytes of the object named by p's own capability.
    Missing/nonobject authority yields no scan capacity. *)
Definition string_capacity (m : mem) (p : ptr) : Z :=
  match ptr_cap p with
  | Obj base | Ro base => match object_region base (m_regions m) with
    | Some reg => Z.max 0 (r_end reg - ptr_addr p)
    | None => 0
    end
  | _ => 0
  end.

(** A concrete length lets a single fixed registry name the exact
    source span for strings of different lengths, without choice or a
    ghost length index. The precondition, not this scan, grants reads. *)
Definition string_length (m : mem) (p : ptr) : Z :=
  nul_count (m_bytes m) (ptr_addr p) (Z.to_nat (string_capacity m p)).

Lemma nul_count_first : forall fuel bytes a k,
  0 <= k < Z.of_nat fuel ->
  (forall i, 0 <= i < k -> bytes (a + i) <> 0) -> bytes (a + k) = 0 ->
  nul_count bytes a fuel = k.
Proof.
  induction fuel as [|fuel IH]; intros bytes a k Hk Hbefore Hnul; [simpl in Hk; lia|].
  cbn -[Z.add]. destruct (Z.eq_dec k 0) as [->|Hpos].
  - rewrite Z.add_0_r in Hnul. rewrite Hnul. reflexivity.
  - assert ((bytes a =? 0) = false) as E.
    { apply Z.eqb_neq. replace a with (a + 0) by lia. apply Hbefore. lia. }
    rewrite E. rewrite (IH bytes (a + 1) (k - 1)).
    + lia.
    + rewrite Nat2Z.inj_succ in Hk. lia.
    + intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hbefore. lia.
    + replace (a + 1 + (k - 1)) with (a + k) by lia. exact Hnul.
Qed.

(** An independently established first NUL determines the computed
    footprint. Invalid inputs need not compute a meaningful length. *)
Lemma terminated_string_length : forall m p k,
  terminated_length m p k -> string_length m p = k.
Proof.
  intros m p k Hlength.
  pose proof (terminated_length_readable _ _ _ Hlength) as
    (Hsize & (base & reg & Hcap & Hr & Hl) & Ha & _).
  destruct Hlength as ((_ & Hk & _ & _ & Hbytes & Hnul) & Hmax).
  assert (Hcapacity : k < string_capacity m p).
  { unfold string_capacity. unfold access_res, cap_access_res in Ha.
    destruct Hcap as [Hcap|Hcap]; rewrite Hcap in Ha |- *; rewrite Hr in Ha |- *.
    all: destruct ((base <=? ptr_addr p) && (ptr_addr p + (k + 1) <=? r_end reg)) eqn:E;
      try discriminate.
    all: apply andb_true_iff in E as [_ He]; apply Z.leb_le in He;
      rewrite Z.max_r by lia; lia. }
  unfold string_length. apply nul_count_first.
  - rewrite Z2Nat.id by lia. lia.
  - intros i Hi. specialize (Hbytes i Hi). lia.
  - apply Hnul. exact Hmax.
Qed.

(** ## Scalar string copies *)

(** Ordinary scalar stores retain destination auxiliary entries; they
    neither clear them nor import source capabilities. No rounded
    shadow footprint or base-alignment premise is needed here. *)
Definition string_copy_frame (m : mem) (d : ptr) (n : Z) (m' : mem) : Prop :=
  m_regions m' = m_regions m /\
  (forall a, m_aux m' a = m_aux m a) /\
  (forall a, ~ span_contains (mkSpan d n) a -> m_bytes m' a = m_bytes m a).

(** Snapshot bytes through NUL with the scalar-store frame. *)
Definition string_copy_result (m : mem) (d src : ptr) (n : Z) (m' : mem) : Prop :=
  string_copy_frame m d n m' /\
  forall a, span_contains (mkSpan d n) a ->
    m_bytes m' a = m_bytes m (ptr_addr src + (a - ptr_addr d)).

(** Admission is independent of the computed footprint: a terminated
    source, writable destination through NUL, and byte nonoverlap. *)
Definition string_copy_domain (m : mem) (d src : ptr) (k : Z) : Prop :=
  terminated_length m src k /\ writable_span m (mkSpan d (k + 1)) /\
  (ptr_addr d + (k + 1) <= ptr_addr src \/ ptr_addr src + (k + 1) <= ptr_addr d).

(** A logical witness, not an implementation or native termination proof. *)
Definition string_copy_memory (m : mem) (d src : ptr) (n : Z) : mem :=
  mkMem (fun a => if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
    then m_bytes m (ptr_addr src + (a - ptr_addr d)) else m_bytes m a)
    (m_regions m) (m_aux m).

Lemma string_copy_memory_result : forall m d src n,
  string_copy_result m d src n (string_copy_memory m d src n).
Proof.
  intros m d src n. split.
  - split; [reflexivity|]. split; [intros; reflexivity|]. intros a Hout.
    change ((if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
      then m_bytes m (ptr_addr src + (a - ptr_addr d)) else m_bytes m a) = m_bytes m a).
    destruct ((ptr_addr d <=? a) && (a <? ptr_addr d + n)) eqn:E; [|reflexivity].
    exfalso. apply Hout. apply andb_true_iff in E as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. exact (conj Hlo Hhi).
  - intros a [Hlo Hhi]. simpl in Hlo, Hhi. unfold string_copy_memory. simpl.
    assert ((ptr_addr d <=? a) && (a <? ptr_addr d + n) = true) as E.
    { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; assumption. }
    rewrite E. reflexivity.
Qed.

(** Any specified completion has these cells, not only the witness. *)
Lemma string_copy_cells : forall m d src n m' a,
  string_copy_result m d src n m' ->
  m_bytes m' a = (if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
    then m_bytes m (ptr_addr src + (a - ptr_addr d)) else m_bytes m a) /\
  m_aux m' a = m_aux m a.
Proof.
  intros m d src n m' a ((Hr & Ha & Hb) & Hcopy). split; [|apply Ha].
  destruct ((ptr_addr d <=? a) && (a <? ptr_addr d + n)) eqn:E.
  - apply Hcopy. apply andb_true_iff in E as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. exact (conj Hlo Hhi).
  - apply Hb. intros [Hlo Hhi]. simpl in Hlo, Hhi.
    apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.

(** Only ordinary destination bytes need write permission; every aux
    entry retains its old authority regardless of new numeric bits. *)
Lemma string_copy_local : forall m d src k m',
  string_copy_domain m d src k -> string_copy_result m d src (k + 1) m' ->
  local_effect [mkSpan src (k + 1); mkSpan d 0] [mkSpan d (k + 1)] [] [] m m'.
Proof.
  intros m d src k m' (_ & Hw & _) ((Hr & Ha & Hb) & Hcopy).
  split; [apply ids_same; exact Hr|]. split.
  - intros b reg Hreg. rewrite Hr in Hreg. exists reg. auto.
  - split.
    + intros a Hout. split; [|apply Ha]. apply Hb. intros Hin.
      apply Hout. left. exists (mkSpan d (k + 1)). split; [left; reflexivity|]. auto.
    + intros a. left. apply Ha.
Qed.

(** P/P to P/discarded. The length is neither a native nor a ghost argument. *)
Definition string_copy_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ exists d src, args = [Arg P d; Arg P src].

(** Conditional contract for the selected scalar strcpy/stpcpy paths.
    Their archive and shared bodies use ordinary stores, not memcpy.
    Internal polls may rewrite freed capabilities: this exact logical
    aux frame does not establish native collector-prefix correspondence,
    wider-load adequacy, universal satisfaction or termination. *)
Definition string_copy_contract (end_return : bool) (world : Type) : contract world :=
  mkContract world (RClass P) string_copy_abi
    (fun xs m _ => exists d src k, xs = [WPtr d; WPtr src] /\ string_copy_domain m d src k)
    (fun xs m _ => match xs with [WPtr d; WPtr src] =>
      [mkSpan src (string_length m src + 1); mkSpan d 0] | _ => [] end)
    (fun xs m _ => match xs with [WPtr d; WPtr src] =>
      [mkSpan d (string_length m src + 1)] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun xs m w born trace m' w' => born = [] /\ trace = [] /\ w' = w /\
      exists d src, xs = [WPtr d; WPtr src] /\ string_copy_frame m d (string_length m src + 1) m')
    (fun xs m w born trace ending m' w' => born = [] /\ trace = [] /\ w' = w /\
      exists d src, xs = [WPtr d; WPtr src] /\
        string_copy_result m d src (string_length m src + 1) m' /\
        ending = CallReturn [WPtr (copy_return end_return d (string_length m src))])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** strcpy returns its original destination capability. *)
Definition strcpy_contract := string_copy_contract false.
(** stpcpy returns the destination's NUL position, not one byte after it. *)
Definition stpcpy_contract := string_copy_contract true.

(** ## Fresh string duplication *)

(** P to P/discarded: the length is not a native or ghost argument. *)
Definition strdup_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ exists p, args = [Arg P p].

(** Conservative source-base domain for the reviewed memcpy metadata
    relation. The source address itself need not be aligned. *)
Definition strdup_domain (m : mem) (p : ptr) (k : Z) : Prop :=
  terminated_length m p k /\
  exists base, (ptr_cap p = Obj base \/ ptr_cap p = Ro base) /\ base mod 8 = 0.

(** strlen plus the NUL, computed from the original memory. *)
Definition strdup_request (xs : list word) (m : mem) (align size : Z) : Prop :=
  exists p, xs = [WPtr p] /\ align = 16 /\ size = string_length m p + 1.

(** Fresh storage first, then the reviewed snapshot copy. The malloc
    endpoint is the intermediate memory, NOT the filled result. *)
Definition strdup_result (m : mem) (p : ptr) (n base : Z) (m' : mem) : Prop :=
  malloc_result m n base (allocated m (heap_req 16 n) base) /\
  copy_result (allocated m (heap_req 16 n) base) (mkPtr base (Obj base)) p n m'.

(** Prefixes preserve old objects and restrict writes to the fresh
    destination. As for malloc, terminal OOM can abandon one allocation. *)
Definition strdup_prefix (m : mem) (p : ptr) (n : Z) (born : list Z) (m' : mem) : Prop :=
  (born = [] /\ m' = m) \/ exists base, born = [base] /\
    malloc_result m n base (allocated m (heap_req 16 n) base) /\
    memset_frame (allocated m (heap_req 16 n) base) (mkPtr base (Obj base)) n m'.

(** Trusted strdup for the selected strlen/malloc/memcpy path. No old
    write root or release, no NULL or exit, and exact source metadata
    only for full in-phase words. Auxiliary allocation, native boxing
    and collector-prefix coverage retain the copying qualifications. *)
Definition strdup_contract (world : Type) : contract world :=
  mkContract world (RClass P) strdup_abi
    (fun xs m _ => exists p k, xs = [WPtr p] /\ strdup_domain m p k)
    (fun xs m _ => match xs with [WPtr p] => [mkSpan p (string_length m p + 1)] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun xs m _ => strdup_request xs m)
    (fun xs m w born trace m' w' => trace = [] /\ w' = w /\ exists p,
      xs = [WPtr p] /\ strdup_prefix m p (string_length m p + 1) born m')
    (fun xs m w born trace ending m' w' => trace = [] /\ w' = w /\ exists p base,
      xs = [WPtr p] /\ born = [base] /\ strdup_result m p (string_length m p + 1) base m' /\
      ending = CallReturn [WPtr (mkPtr base (Obj base))])
    resource_reason (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** Fresh allocation preserves every previously readable byte span. *)
Lemma readable_bytes_allocated : forall m q base p n,
  object_region base (m_regions m) = None -> readable_bytes m p n ->
  readable_bytes (allocated m q base) p n.
Proof.
  intros m q base p n Hnew (Hn & (b & reg & Hcap & Hr & Hl) & Ha & Hbytes).
  split; [exact Hn|]. split.
  - exists b, reg. split; [exact Hcap|]. split; [eapply allocated_old_region; eauto|exact Hl].
  - split; [eapply allocated_old_access; eauto|exact Hbytes].
Qed.

(** A 16-aligned fresh base is also a globally aligned aux-slot start. *)
Lemma fresh_heap_aligned8 : forall m n base,
  fresh m (heap_req 16 n) base -> base mod 8 = 0.
Proof.
  intros m n base (_ & Ha & _). change (base mod 16 = 0) in Ha.
  apply Z.mod_divide in Ha; [|lia]. destruct Ha as [k ->].
  replace (k * 16) with ((k * 2) * 8) by ring. apply Z.mod_mul. lia.
Qed.

(** All changed cells, including shadow slot starts, are within the
    fresh object; no caller write root is needed. Imported capabilities
    still require complete readable original-source slots. *)
Lemma strdup_result_local : forall m p n base m',
  0 < n -> readable_bytes m p n -> strdup_result m p n base m' ->
  local_effect [mkSpan p n] [] [] [base] (allocated m (heap_req 16 n) base) m'.
Proof.
  intros m p n base m' Hpos Hread ((Hlegal & Hfresh & _) & ((Hr & Hb & Ha) & Hbytes & Hslots)).
  pose proof (fresh_heap_aligned8 _ _ _ Hfresh) as Halign.
  destruct Hfresh as (Hbase & Hmod & Hbound & Hnew & Hsep & Hzero).
  pose proof (malloc_extent n ltac:(lia)) as Hextent.
  pose proof (readable_bytes_allocated m (heap_req 16 n) base p n Hnew Hread) as Hread'.
  assert (Hwrite : forall a, base <= a < base + n ->
    write_authority [] [base] (allocated m (heap_req 16 n) base) a).
  { intros a Hin. right. exists base, (mkRegion base (base + req_extent (heap_req 16 n)) Heap Live).
    split; [left; reflexivity|]. split; [simpl; rewrite Z.eqb_refl; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    change (base <= a < base + req_extent (heap_req 16 n)). lia. }
  assert (Htouched : forall a, memset_touched (mkPtr base (Obj base)) n a = true -> base <= a < base + n).
  { intros a H. apply memset_aux_in_root in H. unfold memset_root, span_contains in H.
    assert ((n =? 0) = false) as E by (apply Z.eqb_neq; lia).
    rewrite E in H. simpl in H. rewrite Halign in H. lia. }
  split; [apply ids_same; exact Hr|]. split.
  - intros b reg Hreg. rewrite Hr in Hreg. exists reg. auto.
  - split.
    + intros a Hout. split.
      * apply Hb. intros Hin. apply Hout, Hwrite. exact Hin.
      * apply Ha. destruct (memset_touched (mkPtr base (Obj base)) n a) eqn:E; [|reflexivity].
        exfalso. apply Hout, Hwrite, Htouched. exact E.
    + intros a. destruct (memset_touched (mkPtr base (Obj base)) n a) eqn:E.
      * right. rewrite (Hslots a E). unfold copy_slot.
        destruct (copy_full_slot (mkPtr base (Obj base)) p n a) eqn:Hfull; [|left; reflexivity].
        unfold copy_full_slot in Hfull. repeat rewrite andb_true_iff in Hfull.
        destruct Hfull as [[Hlo Hhi] Hphase]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
        apply Z.eqb_eq in Hphase. right; right; left.
        exists (mkSpan p n), (ptr_addr p + (a - base)).
        split; [left; reflexivity|]. split; [unfold span_contains; simpl in *; lia|].
        split; [simpl in *; lia|]. split; [|reflexivity].
        apply (readable_bytes_slot _ _ n); simpl in *; try assumption; lia.
      * left. apply Ha. exact E.
Qed.

(** Every accepted duplication prefix frames the caller's objects,
    including source bytes and stored capabilities, even on refusal. *)
Lemma strdup_prefix_old : forall m p n born m',
  0 < n -> strdup_prefix m p n born m' ->
  (forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg) /\
  (forall a, in_object m a -> m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a).
Proof.
  intros m p n born m' Hpos [(_ & ->)|(base & _ & (Hlegal & Hfresh & _) & Hr & Hb & Ha)].
  - auto.
  - pose proof (fresh_heap_aligned8 _ _ _ Hfresh) as Halign.
    destruct Hfresh as (_ & _ & _ & Hnew & Hsep & _).
    pose proof (malloc_extent n ltac:(lia)) as Hextent. split.
    + intros b reg Hreg. rewrite Hr. eapply allocated_old_region; eauto.
    + intros a (b & reg & Hreg & Hin).
      assert (Hout : ~ (base <= a < base + n)).
      { intros Hboth. apply (Hsep b reg Hreg). split; lia. }
      split.
      * apply Hb. exact Hout.
      * apply Ha. destruct (memset_touched (mkPtr base (Obj base)) n a) eqn:E; [|reflexivity].
        exfalso. apply Hout. apply memset_aux_in_root in E.
        unfold memset_root, span_contains in E.
        assert ((n =? 0) = false) as En by (apply Z.eqb_neq; lia).
        rewrite En in E. simpl in E. rewrite Halign in E. lia.
Qed.

(** ## Calls over any runtime

    These lemmas instantiate the shared call relation with the retained contracts.
    They describe admitted results without claiming native termination. *)

Module LibcCallsOn (R : Runtime) (M : ExternalMachineSig R).
Include M.E.

(** Independent representation and cell admission construct a real call
    in the logical relation; this is not a native termination theorem. *)
Theorem errno_location_return : forall world cell rep r args s m (w : world),
  errno_location_abi r args -> rep m w -> errno_cell m (cell w) ->
  invoke (errno_location_contract world cell rep) r args [] s m w
    [] (CallReturn [WPtr (cell w)]) s m w.
Proof.
  intros world cell rep r args s m w Habi Hrep Hcell.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - split; [reflexivity|]. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; reflexivity.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr (cell w)). split; reflexivity.
    + constructor; [|constructor]. right. left.
      exists (mkSpan (cell w) 0). split; [left; reflexivity|reflexivity].
  - intros status Hbad. discriminate.
Qed.

(** Every endpoint returns the exact represented cell with its original
    capability. All memory, runtime and world state remain unchanged. *)
Theorem errno_location_invocation : forall world cell rep r args xs s m (w : world)
    trace ending s' m' w',
  invoke (errno_location_contract world cell rep) r args xs s m w
    trace ending s' m' w' ->
  errno_location_abi r args /\ xs = [] /\ rep m w /\ errno_cell m (cell w) /\
  trace = [] /\ s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr (cell w)].
Proof.
  intros world cell rep r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - match goal with
    | Habi : contract_abi _ _ _, Hpre : contract_pre _ _ _ _,
      Hp : prefix _ _ _ _ _ _ _ _ _ _, Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (Hxs & Hrep & Hcell);
      destruct Hpost as (Hb & Htrace & Hmem & Hworld & Hend);
      destruct Hp as [He _];
      assert (Hs : s' = s) by (clear -He; induction He; [reflexivity|exact IHHe|contradiction]);
      exact (conj Habi (conj Hxs (conj Hrep (conj Hcell
        (conj Htrace (conj Hs (conj Hmem (conj Hworld Hend))))))))
    end.
  - contradiction.
Qed.

(** Every admitted scan has a permitted normal invocation via the
    reflexive effect path. This proves nonvacuity, not native termination. *)
Theorem strnlen_return : forall world r args p n k s m (w : world),
  strnlen_abi r args -> bounded_length m p n k ->
  invoke (strnlen_contract world) r args [WPtr p; WInt n] s m w
    [] (CallReturn [WInt k]) s m w.
Proof.
  intros world r args p n k s m w Habi Hlength.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, n, k. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, n, k. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt k). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|destruct Hlength as [Hn [Hk _]]; lia].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Every represented completion is the pure bounded result. There is
    no resource or exit ending; malformed arguments get no invocation. *)
Theorem strnlen_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strnlen_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p n k, xs = [WPtr p; WInt n] /\ bounded_length m p n k /\ ending = CallReturn [WInt k].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** Input-only string authority constructs an actual pure invocation.
    This is specification nonvacuity, not native execution or termination. *)
Theorem strlen_return : forall world r args p k s m (w : world),
  strlen_abi r args -> terminated_length m p k ->
  invoke (strlen_contract world) r args [WPtr p] s m w
    [] (CallReturn [WInt k]) s m w.
Proof.
  intros world r args p k s m w Habi Hlength.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, k. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, k. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt k). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|destruct Hlength as [(_ & Hk & _) Hmax]; lia].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Every represented completion returns the original string's exact
    length, with empty observations and unchanged memory and world.
    There is no resource or process-exit alternative. *)
Theorem strlen_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strlen_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p k, xs = [WPtr p] /\ terminated_length m p k /\ ending = CallReturn [WInt k].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** Any specified first match or miss has a permitted pure invocation. *)
Theorem memchr_return : forall world r args p c n q s m (w : world),
  memchr_abi r args -> memchr_input m p c n -> memchr_result m p c n q ->
  invoke (memchr_contract world) r args [WPtr p; WInt c; WInt n] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c n q s m w Habi Hinput Hresult.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, c, n. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, c, n, q. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr q). split; reflexivity.
    + constructor; [apply memchr_result_authority with (c := c); exact Hresult|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Every admitted input has some permitted result, without requiring
    a returned-pointer witness in its precondition. Not native termination. *)
Theorem memchr_admitted : forall world r args p c n s m (w : world),
  memchr_abi r args -> memchr_input m p c n ->
  exists q, invoke (memchr_contract world) r args [WPtr p; WInt c; WInt n] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c n s m w Habi Hinput.
  destruct (memchr_input_result _ _ _ _ Hinput) as [q Hq].
  exists q. apply memchr_return; assumption.
Qed.

(** Every represented completion is pure and returns exactly the first
    matching pointer with its source capability, or null on a miss. *)
Theorem memchr_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (memchr_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p c n q, xs = [WPtr p; WInt c; WInt n] /\ memchr_result m p c n q /\
    ending = CallReturn [WPtr q].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** Runtime readiness bounds the consumed prefix, NOT the maximum count.
    A first-byte hit with SIZE_MAX need not authorize p + SIZE_MAX. *)
Lemma memchr_input_extent : forall s m p c n,
  R.ready s m -> memchr_input m p c n ->
  exists k, 0 <= k <= n /\
    0 <= ptr_addr p /\ ptr_addr p + k + (if k <? n then 1 else 0) <= 2 ^ 48.
Proof.
  intros s m p c n Hr (_ & _ & k & Hk & Hread & _).
  exists k. split; [exact Hk|].
  pose proof (readable_bytes_extent _ _ _ _ Hr Hread). lia.
Qed.

(** Every legal signed magnitude has a permitted pure invocation, not
    only the three witnesses used in [memcmp_result_total]. *)
Theorem memcmp_return : forall world r args p q n bits s m (w : world),
  memcmp_abi r args -> readable_bytes m p n -> readable_bytes m q n ->
  memcmp_result m p q n bits ->
  invoke (memcmp_contract world) r args [WPtr p; WPtr q; WInt n] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q n bits s m w Habi Hp Hq Hresult.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, q, n. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, q, n, bits. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt bits). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|exact (proj1 Hresult)].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Independently readable arguments admit some permitted result;
    invocation existence is a conclusion, not an admission premise. *)
Theorem memcmp_admitted : forall world r args p q n s m (w : world),
  memcmp_abi r args -> readable_bytes m p n -> readable_bytes m q n ->
  exists bits, invoke (memcmp_contract world) r args [WPtr p; WPtr q; WInt n] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q n s m w Habi Hp Hq.
  destruct (memcmp_result_total m p q n ltac:(destruct Hp as [Hn _]; lia)) as [bits Hbits].
  exists bits. apply memcmp_return; assumption.
Qed.

(** Every represented completion is pure with the specified signed
    byte-order result. Resource and process-exit endings are excluded. *)
Theorem memcmp_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (memcmp_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p q n bits, xs = [WPtr p; WPtr q; WInt n] /\ memcmp_result m p q n bits /\
    ending = CallReturn [WInt bits].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** Any legal strncmp result admits a pure invocation. Its result
    predicate already includes the two independent input witnesses. *)
Theorem strncmp_return : forall world r args p q n bits s m (w : world),
  memcmp_abi r args -> strncmp_result m p q n bits ->
  invoke (strncmp_contract world) r args [WPtr p; WPtr q; WInt n] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q n bits s m w Habi Hresult.
  destruct Hresult as (left & right & Hl & Hr & Hbits).
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, q, n, left, right. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, q, n, bits. split; [reflexivity|].
    split; [exists left, right; auto|reflexivity].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt bits). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|exact (proj1 Hbits)].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Input-only premises construct a permitted return; this is trusted
    specification nonvacuity, not a native termination theorem. *)
Theorem strncmp_admitted : forall world r args p q n left right s m (w : world),
  memcmp_abi r args -> bounded_length m p n left -> bounded_length m q n right ->
  exists bits, invoke (strncmp_contract world) r args [WPtr p; WPtr q; WInt n] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q n left right s m w Habi Hl Hr.
  destruct (strncmp_result_total m p q n left right Hl Hr) as [bits Hbits].
  exists bits. apply strncmp_return; assumption.
Qed.

(** Every represented completion has the signed string-order result
    and exact unchanged endpoint, with no resource or exit alternative. *)
Theorem strncmp_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strncmp_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p q n bits, xs = [WPtr p; WPtr q; WInt n] /\ strncmp_result m p q n bits /\
    ending = CallReturn [WInt bits].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** Every legal sign and magnitude constructs a pure strcmp invocation.
    The result predicate already contains independent input authority. *)
Theorem strcmp_return : forall world r args p q bits s m (w : world),
  strcmp_abi r args -> strcmp_result m p q bits ->
  invoke (strcmp_contract world) r args [WPtr p; WPtr q] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q bits s m w Habi (left & right & Hl & Hr & Hbits).
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, q, left, right. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, q, bits. split; [reflexivity|].
    split; [exists left, right; auto|reflexivity].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt bits). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|exact (proj1 Hbits)].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Independent terminated inputs suffice for some permitted return.
    This is logical nonvacuity, not a native termination theorem. *)
Theorem strcmp_admitted : forall world r args p q left right s m (w : world),
  strcmp_abi r args -> terminated_length m p left -> terminated_length m q right ->
  exists bits, invoke (strcmp_contract world) r args [WPtr p; WPtr q] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q left right s m w Habi Hl Hr.
  destruct (strcmp_result_total m p q left right Hl Hr) as [bits Hbits].
  exists bits. apply strcmp_return; assumption.
Qed.

(** Every represented strcmp completion returns its original-memory
    string-order result, with empty observations and unchanged memory/world.
    No resource or process-exit completion is admitted. *)
Theorem strcmp_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strcmp_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p q bits, xs = [WPtr p; WPtr q] /\ strcmp_result m p q bits /\
    ending = CallReturn [WInt bits].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** A specified first match or miss constructs a pure pointer return
    from the independent ABI and canonical-int admission obligations. *)
Theorem strchr_return : forall world r args p c q s m (w : world),
  strchr_abi r args -> 0 <= c < 2 ^ 32 -> strchr_result m p c q ->
  invoke (strchr_contract world) r args [WPtr p; WInt c] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c q s m w Habi Hc Hresult.
  destruct Hresult as (k & Hlength & Hq).
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, c, k. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, c, q. split; [reflexivity|].
    split; [exact Hc|]. split; [exists k; auto|reflexivity].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr q). split; reflexivity.
    + constructor.
      * apply (strchr_result_authority m p c q). exists k. auto.
      * constructor.
  - intros status Hbad. discriminate.
Qed.

(** Canonical int and terminated-string inputs suffice for some actual
    permitted invocation; native coverage and termination remain trusted. *)
Theorem strchr_admitted : forall world r args p c k s m (w : world),
  strchr_abi r args -> 0 <= c < 2 ^ 32 -> terminated_length m p k ->
  exists q, invoke (strchr_contract world) r args [WPtr p; WInt c] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c k s m w Habi Hc Hlength.
  destruct (strchr_result_total m p c k Hlength) as [q Hq].
  exists q. apply strchr_return; assumption.
Qed.

(** Every represented completion is a first-match pointer or null in
    the original memory, with canonical int admission, empty observations,
    unchanged memory/world, and no resource or process-exit ending. *)
Theorem strchr_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strchr_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p c q, xs = [WPtr p; WInt c] /\ 0 <= c < 2 ^ 32 /\ strchr_result m p c q /\
    ending = CallReturn [WPtr q].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** ABI, canonical int and a specified last match or miss suffice for
    an actual pure invocation, with no borrowed auxiliary authority. *)
Theorem strrchr_return : forall world r args p c q s m (w : world),
  strchr_abi r args -> 0 <= c < 2 ^ 32 -> strrchr_result m p c q ->
  invoke (strrchr_contract world) r args [WPtr p; WInt c] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c q s m w Habi Hc Hresult.
  destruct Hresult as (k & Hlength & Hq).
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, c, k. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, c, q. split; [reflexivity|].
    split; [exact Hc|]. split; [exists k; auto|reflexivity].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr q). split; reflexivity.
    + constructor.
      * apply (strrchr_result_authority m p c q). exists k. auto.
      * constructor.
  - intros status Hbad. discriminate.
Qed.

(** Independent input authority constructs some last-match invocation,
    without a native executor, coverage or termination assumption. *)
Theorem strrchr_admitted : forall world r args p c k s m (w : world),
  strchr_abi r args -> 0 <= c < 2 ^ 32 -> terminated_length m p k ->
  exists q, invoke (strrchr_contract world) r args [WPtr p; WInt c] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c k s m w Habi Hc Hlength.
  destruct (strrchr_result_total m p c k Hlength) as [q Hq].
  exists q. apply strrchr_return; assumption.
Qed.

(** Every completion returns a last match or canonical null from the
    original memory, retaining canonical int admission, exact memory/world
    preservation, empty observations and no resource or exit ending. *)
Theorem strrchr_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strrchr_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p c q, xs = [WPtr p; WInt c] /\ 0 <= c < 2 ^ 32 /\ strrchr_result m p c q /\
    ending = CallReturn [WPtr q].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** A successful runtime answer constructs an actual malloc call;
    readiness supplies freshness, rather than assuming it of callers. *)
Theorem malloc_return : forall world r args n s m (w : world) base s',
  malloc_abi r args -> 0 <= n < 2 ^ 64 -> n <= max_allocation_size ->
  R.ready s m -> R.alloc s (heap_req 16 n) = Some (base, s') ->
  invoke (malloc_contract world) r args [WInt n] s m w []
    (CallReturn [WPtr (mkPtr base (Obj base))]) s' (allocated m (heap_req 16 n) base) w.
Proof.
  intros world r args n s m w base s' Habi Hn Hsize Hr Ha.
  destruct (R.fresh_allocation s m (heap_req 16 n) base s' Hr ltac:(simpl; lia)
    ltac:(pose proof (malloc_extent n ltac:(lia)); lia) Ha) as [Hfresh _].
  assert (Hresult : malloc_result m n base (allocated m (heap_req 16 n) base))
    by (split; [lia|]; auto).
  eapply invoke_normal with (born := [base]).
  - exact Habi.
  - exists n. auto.
  - split.
    + eapply effects_alloc; [exists n; auto|lia|exact Ha|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. exists n. split; [reflexivity|].
      right. exists base. auto.
  - split; [reflexivity|]. split; [reflexivity|]. exists n, base. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [|constructor]. right; right; right. exists base. simpl. auto.
  - intros status Hbad. discriminate.
Qed.

(** Refusal can be observed with no successful allocation at all. *)
Theorem malloc_refused : forall world r args n s m (w : world) why,
  malloc_abi r args -> 0 <= n < 2 ^ 64 ->
  resource_failure (malloc_request [WInt n]) s why ->
  invoke (malloc_contract world) r args [WInt n] s m w [] (CallResource why) s m w.
Proof.
  intros world r args n s m w why Habi Hn Hfail.
  eapply invoke_resource with (born := []).
  - exact Habi.
  - exists n. auto.
  - split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
    exists n. split; [reflexivity|]. left. auto.
  - exact Hfail.
  - change (resource_reason why). destruct Hfail; unfold resource_reason; auto.
Qed.

(** Input-only nonvacuity: a ready runtime either grants the sole
    request shape, refuses it, or rejects the original size as TooBig. *)
Theorem malloc_admitted : forall world r args n s m (w : world),
  malloc_abi r args -> 0 <= n < 2 ^ 64 -> R.ready s m ->
  exists ending s' m', invoke (malloc_contract world) r args [WInt n] s m w
    [] ending s' m' w.
Proof.
  intros world r args n s m w Habi Hn Hr.
  destruct (Z_le_dec n max_allocation_size) as [Hsize|Hbig].
  - destruct (R.alloc s (heap_req 16 n)) as [[base s']|] eqn:Ha.
    + do 3 eexists. eapply malloc_return; eauto.
    + exists (CallResource OutOfMemory), s, m. apply malloc_refused; auto.
      eapply failure_oom; [exists n; auto|lia|exact Ha].
  - exists (CallResource TooBig), s, m. apply malloc_refused; auto.
    eapply failure_big; [exists n; auto|lia].
Qed.

(** Public inversion retains the exact success endpoint or the
    documented terminal-resource prefix, with refusal in its final
    runtime state. There is no NULL return and no exit outcome. *)
Theorem malloc_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (malloc_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ w' = w /\ exists n, xs = [WInt n] /\ 0 <= n < 2 ^ 64 /\
    ((exists base, malloc_result m n base m' /\
       ending = CallReturn [WPtr (mkPtr base (Obj base))]) \/
     (exists why born, ending = CallResource why /\ malloc_prefix m n born m' /\
       resource_failure (malloc_request [WInt n]) s' why)).
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with
    | Hpre : contract_pre _ _ _ _, Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (n & Hxs & Hn);
      destruct Hpost as (Ht & Hw & size & base & Hxs' & Hb & Hresult & Hend)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <-.
    split; [exact Ht|]. split; [exact Hw|]. exists n. split; [exact Hxs|].
    split; [exact Hn|]. left. exists base. auto.
  - match goal with
    | Hpre : contract_pre _ _ _ _, Hp : prefix _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (n & Hxs & Hn);
      destruct Hp as (_ & Ht & Hw & size & Hxs' & Hprefix)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <-.
    split; [exact Ht|]. split; [exact Hw|]. exists n. split; [exact Hxs|].
    split; [exact Hn|]. right. do 2 eexists. split; [reflexivity|].
    split; [exact Hprefix|]. subst xs. assumption.
Qed.

(** Oversize refusal cannot follow the successful prefix: legal-size
    admission of that prefix makes this distinction provable. *)
Theorem malloc_too_big_unchanged : forall world r args n s m (w : world) trace s' m' w',
  invoke (malloc_contract world) r args [WInt n] s m w trace (CallResource TooBig) s' m' w' ->
  max_allocation_size < n /\ m' = m.
Proof.
  intros world r args n s m w trace s' m' w' Hcall.
  destruct (malloc_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & size & Hargs & _ & [(base & _ & Hend)|(why & born & Hend & Hp & Hf)]).
  - discriminate Hend.
  - injection Hargs as <-. injection Hend as <-. inversion Hf; subst.
    match goal with Hreq : malloc_request _ _ _ |- _ =>
      destruct Hreq as (k & Hargs & _ & Hsize); injection Hargs as <-; subst
    end.
    split; [assumption|]. destruct Hp as [(_ & ->)|(base & _ & (Hlegal & _))]; [reflexivity|lia].
Qed.

(** Successful allocation followed by any specified snapshot produces
    an actual strdup invocation. Source length is proved from inputs. *)
Theorem strdup_return : forall world r args p k s m (w : world) base s' m',
  strdup_abi r args -> strdup_domain m p k -> k + 1 <= max_allocation_size ->
  R.ready s m -> R.alloc s (heap_req 16 (k + 1)) = Some (base, s') ->
  copy_result (allocated m (heap_req 16 (k + 1)) base)
    (mkPtr base (Obj base)) p (k + 1) m' ->
  invoke (strdup_contract world) r args [WPtr p] s m w []
    (CallReturn [WPtr (mkPtr base (Obj base))]) s' m' w.
Proof.
  intros world r args p k s m w base s' m' Habi Hdomain Hsize Hr Ha Hcopy.
  pose proof (terminated_string_length _ _ _ (proj1 Hdomain)) as Hlen.
  pose proof (terminated_length_readable _ _ _ (proj1 Hdomain)) as Hread.
  destruct (proj1 Hdomain) as ((_ & Hk & _) & Hmax).
  destruct (R.fresh_allocation s m (heap_req 16 (k + 1)) base s' Hr ltac:(simpl; lia)
    ltac:(pose proof (malloc_extent (k + 1) ltac:(lia)); lia) Ha) as [Hfresh _].
  assert (Hresult : strdup_result m p (k + 1) base m').
  { split; [split; [lia|]; auto|exact Hcopy]. }
  eapply invoke_normal with (born := [base]).
  - exact Habi.
  - exists p, k. auto.
  - split.
    + change (effects [mkSpan p (string_length m p + 1)] [] [] (strdup_request [WPtr p] m)
        s m [] s' m' [base]). rewrite Hlen.
      eapply effects_alloc with (align := 16) (size := k + 1).
      * exists p. split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. reflexivity.
      * lia.
      * exact Ha.
      * eapply effects_local; [eapply strdup_result_local; eauto; lia|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. exists p. split; [reflexivity|].
      rewrite Hlen. right. exists base. split; [reflexivity|].
      split; [exact (proj1 Hresult)|exact (proj1 Hcopy)].
  - split; [reflexivity|]. split; [reflexivity|]. exists p, base.
    split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [|constructor]. right; right; right. exists base. simpl. auto.
  - intros status Hbad. discriminate.
Qed.

(** Allocation refusal is an actual unchanged prefix, not NULL. *)
Theorem strdup_refused : forall world r args p k s m (w : world) why,
  strdup_abi r args -> strdup_domain m p k ->
  resource_failure (strdup_request [WPtr p] m) s why ->
  invoke (strdup_contract world) r args [WPtr p] s m w [] (CallResource why) s m w.
Proof.
  intros world r args p k s m w why Habi Hdomain Hfail.
  eapply invoke_resource with (born := []).
  - exact Habi.
  - exists p, k. auto.
  - split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
    exists p. split; [reflexivity|]. left. auto.
  - exact Hfail.
  - change (resource_reason why). destruct Hfail; unfold resource_reason; auto.
Qed.

(** Every independently admitted string has a modeled success or
    resource invocation, even when the runtime refuses to allocate. *)
Theorem strdup_admitted : forall world r args p k s m (w : world),
  strdup_abi r args -> strdup_domain m p k -> R.ready s m ->
  exists ending s' m', invoke (strdup_contract world) r args [WPtr p] s m w
    [] ending s' m' w.
Proof.
  intros world r args p k s m w Habi Hdomain Hr.
  pose proof (terminated_string_length _ _ _ (proj1 Hdomain)) as Hlen.
  destruct (proj1 Hdomain) as ((_ & Hk & _) & Hmax).
  destruct (Z_le_dec (k + 1) max_allocation_size) as [Hsize|Hbig].
  - destruct (R.alloc s (heap_req 16 (k + 1))) as [[base s']|] eqn:Ha.
    + do 3 eexists. eapply strdup_return; eauto. apply copy_memory_result.
    + exists (CallResource OutOfMemory), s, m. eapply strdup_refused; eauto.
      eapply failure_oom with (align := 16) (size := k + 1).
      * exists p. split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. reflexivity.
      * lia.
      * exact Ha.
  - exists (CallResource TooBig), s, m. eapply strdup_refused; eauto.
    eapply failure_big with (align := 16) (size := k + 1).
    + exists p. split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. reflexivity.
    + lia.
Qed.

(** Extract the independent string witness, exact fresh result, or
    terminal-resource prefix. The computed span equals k+1 for this
    witness, so one fixed contract handles different lengths. *)
Theorem strdup_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strdup_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ w' = w /\ exists p k, xs = [WPtr p] /\ strdup_domain m p k /\
    ((exists base, strdup_result m p (k + 1) base m' /\
       ending = CallReturn [WPtr (mkPtr base (Obj base))]) \/
     (exists why born, ending = CallResource why /\ strdup_prefix m p (k + 1) born m' /\
       resource_failure (strdup_request [WPtr p] m) s' why)).
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with
    | Hpre : contract_pre _ _ _ _, Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (p & k & Hxs & Hd);
      destruct Hpost as (Ht & Hw & q & base & Hxs' & Hb & Hr & Hend)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <-.
    pose proof (terminated_string_length _ _ _ (proj1 Hd)) as Hlen. rewrite Hlen in Hr.
    split; [exact Ht|]. split; [exact Hw|]. exists p, k.
    split; [exact Hxs|]. split; [exact Hd|]. left. exists base. auto.
  - match goal with
    | Hpre : contract_pre _ _ _ _, Hp : prefix _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (p & k & Hxs & Hd);
      destruct Hp as (_ & Ht & Hw & q & Hxs' & Hprefix)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <-.
    pose proof (terminated_string_length _ _ _ (proj1 Hd)) as Hlen. rewrite Hlen in Hprefix.
    split; [exact Ht|]. split; [exact Hw|]. exists p, k.
    split; [exact Hxs|]. split; [exact Hd|]. right. do 2 eexists.
    split; [reflexivity|]. split; [exact Hprefix|]. subst xs. assumption.
Qed.

(** Any specified scalar copy constructs an actual invocation from
    independently admitted inputs. The computed footprint equals k+1. *)
Theorem string_copy_completed : forall end_return world r args d src k s m m' (w : world),
  string_copy_abi r args -> string_copy_domain m d src k ->
  string_copy_result m d src (k + 1) m' ->
  invoke (string_copy_contract end_return world) r args [WPtr d; WPtr src] s m w
    [] (CallReturn [WPtr (copy_return end_return d k)]) s m' w.
Proof.
  intros end_return world r args d src k s m m' w Habi Hdomain Hresult.
  pose proof (terminated_string_length _ _ _ (proj1 Hdomain)) as Hlen.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists d, src, k. auto.
  - split.
    + change (effects [mkSpan src (string_length m src + 1); mkSpan d 0]
        [mkSpan d (string_length m src + 1)] [] (fun _ _ => False) s m [] s m' []).
      rewrite Hlen. eapply effects_local; [eapply string_copy_local; eauto|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists d, src. split; [reflexivity|]. rewrite Hlen. exact (proj1 Hresult).
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists d, src. split; [reflexivity|]. rewrite Hlen. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr (copy_return end_return d k)). split; reflexivity.
    + constructor; [|constructor]. unfold copy_return. destruct end_return; simpl.
      all: right; left; exists (mkSpan d 0); split; [right; left; reflexivity|reflexivity].
  - intros status Hbad. discriminate.
Qed.

(** Input-only nonvacuity, without a native progress or termination claim. *)
Theorem string_copy_admitted : forall end_return world r args d src k s m (w : world),
  string_copy_abi r args -> string_copy_domain m d src k ->
  invoke (string_copy_contract end_return world) r args [WPtr d; WPtr src] s m w
    [] (CallReturn [WPtr (copy_return end_return d k)]) s (string_copy_memory m d src (k + 1)) w.
Proof. intros. apply string_copy_completed; [assumption|assumption|apply string_copy_memory_result]. Qed.

(** Arbitrary completions retain all destination aux, exact bytes/NUL,
    and destination or NUL-position provenance. No resource/exit branch. *)
Theorem string_copy_invocation : forall end_return world r args xs s m (w : world)
    trace ending s' m' w',
  invoke (string_copy_contract end_return world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ w' = w /\ exists d src k, xs = [WPtr d; WPtr src] /\
    string_copy_domain m d src k /\ string_copy_result m d src (k + 1) m' /\
    ending = CallReturn [WPtr (copy_return end_return d k)].
Proof.
  intros end_return world r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - match goal with
    | Hpost : contract_post _ _ _ _ _ _ _ _ _, Hpre : contract_pre _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hworld & d & src & Hxs & Hresult & Hending);
      destruct Hpre as (q & v & k & Hxs' & Hdomain)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <- <-.
    pose proof (terminated_string_length _ _ _ (proj1 Hdomain)) as Hlen.
    rewrite Hlen in Hresult, Hending. split; [exact Htrace|]. split; [exact Hworld|].
    exists d, src, k. auto.
  - contradiction.
Qed.

(** stpcpy's returned NUL is inside the destination, not one-past.
    Readiness bounds its mathematical address without a new runtime axiom. *)
Theorem string_copy_endpoint : forall s m d src k,
  R.ready s m -> string_copy_domain m d src k ->
  exists base reg, ptr_cap d = Obj base /\ object_region base (m_regions m) = Some reg /\
    base <= ptr_addr d + k < r_end reg /\ 0 <= ptr_addr d + k < 2 ^ 64.
Proof.
  intros s m d src k Hready (Hlength & (_ & base & reg & Hcap & Hr & Hl & Ha) & _).
  destruct Hlength as ((_ & Hk & _) & _). simpl in Hcap, Ha.
  unfold access_res, cap_access_res in Ha. rewrite Hr in Ha.
  destruct ((base <=? ptr_addr d) && (ptr_addr d + (k + 1) <=? r_end reg)) eqn:E;
    [|discriminate].
  apply andb_true_iff in E as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (R.address_space _ _ Hready base reg Hr) as (Hb & He).
  exists base, reg. split; [exact Hcap|]. split; [exact Hr|]. split; lia.
Qed.

End LibcCallsOn.

Module LibcCalls (R : Runtime).
Module M := ExternalMachine R.
Include LibcCallsOn R M.
End LibcCalls.

(** The logical libc world of [puts_contract]. This small world records
    only the currently modeled stream's usability (stdout_usable) and
    reachable writable libc roots, stdio_roots (stdout, errno, buffer).
    Establishing those roots at startup remains an entry obligation.
    It does not claim that an arbitrary writable object is a FILE. *)
Record stdio_world : Type := mkStdioWorld {
  stdout_usable : bool;
  stdio_roots : list span
}.

(** In memory m, the world w's stdout is usable and every libc root it
    names is a [writable_span]. *)
Definition stdio_ready (m : mem) (w : stdio_world) : Prop :=
  stdout_usable w = true /\ Forall (writable_span m) (stdio_roots w).

(** The ABI of puts: the result is discarded or read as one word of
    [[class]] [W], and the one argument is passed as a pointer ([P]). *)
Definition puts_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists v, args = [Arg P v].

(** The precondition of puts: the world w is represented in memory m
    (rep), it is [stdio_ready], and the one argument word is a pointer
    to a [c_string]. rep is the trusted relation between the abstract
    stream state and its memory representation, including ownership and
    pointer sources. No concrete FILE representation or startup instance
    is claimed here. *)
Definition puts_pre (rep : mem -> stdio_world -> Prop)
    (xs : list word) (m : mem) (w : stdio_world) : Prop :=
  rep m w /\ stdio_ready m w /\ exists p bytes, xs = [WPtr p] /\ c_string m p bytes.

(** Every libc root of the new world w is backed by the call's own
    authority: its capability is [available_cap] from the old roots and
    the born objects, and the call has [write_authority] over all of its
    bytes. A call may retain newly allocated buffers, but cannot acquire
    write authority to an unrelated old object by changing the logical
    world. *)
Definition stdio_delegates (roots : list span) (born : list Z) (m : mem) (w : stdio_world) : Prop :=
  forall s, In s (stdio_roots w) ->
    available_cap roots born m (ptr_cap (span_ptr s)) /\
    forall a, span_contains s a -> write_authority roots born m a.

(** A world whose roots are exactly the old roots, all writable, is
    delegated: keeping the same roots needs no new authority. *)
Lemma stdio_delegates_refl : forall roots born m w,
  stdio_roots w = roots -> Forall (writable_span m) roots -> stdio_delegates roots born m w.
Proof.
  intros roots born m w <- Hroots s Hin. split.
  - right. left. exists s. auto.
  - intros a Ha. left. exists s. split; auto. split; auto.
    rewrite Forall_forall in Hroots. apply Hroots. exact Hin.
Qed.

(** What any finite prefix of a puts call may observe: the new world w'
    is represented in m', [stdio_ready] and [stdio_delegates] from the
    old roots; and the trace is empty, or one [StreamBytes] event on
    stream 1 (stdout) accepting a prefix of the string followed by its
    newline (byte 10). *)
Definition puts_prefix (rep : mem -> stdio_world -> Prop)
    (xs : list word) (m : mem) (w : stdio_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : stdio_world) : Prop :=
  rep m' w' /\ stdio_ready m' w' /\ stdio_delegates (stdio_roots w) born m' w' /\
  (trace = [] \/ exists p bytes accepted tail,
    xs = [WPtr p] /\ c_string m p bytes /\ bytes ++ [10] = accepted ++ tail /\
    trace = [StreamBytes 1 accepted]).

(** The postcondition of puts: the call accepted a prefix of the string
    and its newline, observed as one [StreamBytes] event on stdout, and
    returned one integer, with the world still [stdio_ready]. Successful
    acceptance is the whole string plus newline, with a nonnegative int
    result. On an I/O error, any prefix may have been accepted
    (including all of it), and the result is EOF: -1 at this glibc pin,
    represented as unsigned bits of [[class]] w, 2^32 - 1. Neither event
    says that the bytes have reached a file descriptor. *)
Definition puts_post (xs : list word) (m : mem) (w : stdio_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : stdio_world) : Prop :=
  exists p bytes accepted tail result,
    xs = [WPtr p] /\ c_string m p bytes /\
    bytes ++ [10] = accepted ++ tail /\
    ((tail = [] /\ 0 <= result < 2 ^ 31) \/ result = 2 ^ 32 - 1) /\
    trace = [StreamBytes 1 accepted] /\ ending = CallReturn [WInt result] /\
    stdio_ready m' w'.

(** The capability checks a puts call outside its contract can reach
    (codes R, W and V of [libc-contracts.md](../../../docs/libc-contracts.md)):
    null capability, out of bounds, misaligned, read-only store, and
    argument or return size mismatch. *)
Definition puts_panic (why : reason) : Prop :=
  In why [NullCapability; OutOfBounds; Misaligned; Readonly; ArgumentSize; ReturnSize].

(** The [[external call|contract]] of puts, given the trusted stream
    representation rep and the allocation requests it may make: a word
    result, [puts_abi], [puts_pre], the world's roots as both sources
    and writable roots, no releases, [puts_prefix], [puts_post], the
    [resource_reason] endings and the [puts_panic] set. *)
Definition puts_contract (rep : mem -> stdio_world -> Prop)
    (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop) : contract stdio_world :=
  mkContract stdio_world (RClass W) puts_abi (puts_pre rep)
    (fun _ _ w => stdio_roots w)
    (fun _ _ w => stdio_roots w) (fun _ _ _ => [])
    requests (puts_prefix rep) puts_post resource_reason puts_panic.

(** ## Contract boundary checks *)

(** No resource ending puts may have is in its panic set: running out of
    memory is not a capability panic. *)
Lemma puts_no_capability_panic : forall rep requests why,
  contract_resource (puts_contract rep requests) why -> ~ puts_panic why.
Proof.
  intros rep requests why [-> | ->]; unfold puts_panic; simpl; intuition discriminate.
Qed.

(** A null pointer is never a [c_string], so puts of null fails the
    precondition rather than having a modeled behavior. *)
Lemma puts_null_not_admissible : forall m bytes,
  ~ c_string m (mkPtr 0 CNone) bytes.
Proof. intros m bytes [H _]. discriminate H. Qed.

(** A puts call that returns anything but EOF accepted exactly its
    whole string followed by a newline on stdout. *)
Lemma puts_success_bytes : forall xs m w born trace m' w' result,
  puts_post xs m w born trace (CallReturn [WInt result]) m' w' ->
  result <> 2 ^ 32 - 1 ->
  exists p bytes, xs = [WPtr p] /\ c_string m p bytes /\ trace = [StreamBytes 1 (bytes ++ [10])].
Proof.
  intros xs m w born trace m' w' result (p & bytes & accepted & tail & n & Hx & Hs & Hb & Hr & Ht & He & _) Hn.
  injection He as <-. destruct Hr as [[-> _] | Hr]; [|contradiction].
  rewrite app_nil_r in Hb. exists p, bytes. split; auto. split; auto. rewrite Hb. exact Ht.
Qed.
