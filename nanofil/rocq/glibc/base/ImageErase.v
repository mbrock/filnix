(** Hello linked with the user glibc it reaches is too large to decode in
    Rocq, yet a proof about it needs the addresses that the loader gives
    its globals. The loader places items in order, and the place of each
    item depends only on its kind, its name, its linkage, its alignment
    and the size of its initializer. This file defines an erasure that
    keeps exactly those facts, replaces function bodies with nothing and
    replaces each unselected initializer with zeros of the same size. It
    proves that the loader's first two passes, which place items and
    resolve aliases, give the erased module the same symbols and regions
    as the original.

    Equal addresses do not give equal memory, so this file claims
    nothing about the bytes that the loader writes afterwards. The loader
    finds where to write each object through the final table of names, so
    a later alias or a repeated name can steer one object's bytes into
    another object. An erased object also cannot fail to load the way its
    original can. The last control builds such a module. Whether the real
    image avoids these cases, and whether the program starts from the
    loader's memory at all, are separate questions. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Run.
Import ListNotations.
Open Scope Z_scope.

(** ## The erasure *)

(** An empty initializer stays empty, because the loader skips an empty
    weak declaration and places every other data item. A nonempty one
    becomes one run of zeros of the same size. *)
Definition erase_items (items : list data_item) : list data_item :=
  match items with [] => [] | _ => [Zero (items_size items)] end.

(** A function keeps its name, linkage and return type and loses its
    parameters and blocks. A data item named by keep stays whole, and any
    other data item keeps its name, linkage and alignment with an erased
    initializer. Aliases and outside functions stay as they are. *)
Definition erase_item (keep : name -> bool) (it : item) : item :=
  match it with
  | IFunc f => IFunc (mkFunc (fn_name f) (fn_linkage f) (fn_ret f) [] [])
  | IData n lk al items => if keep n then it else IData n lk al (erase_items items)
  | IOutside _ _ | IAlias _ _ _ => it
  end.

(** The erased module keeps the original order. *)
Definition erase (keep : name -> bool) (md : module) : module := map (erase_item keep) md.

(** These are the symbols and regions that the loader's first two passes
    compute, before any initializer is written. *)
Definition image_layout (md : module) : option (list (name * ptr) * list region) :=
  match fold_left layout md (Some (data_base, [], [])) with
  | Some (_, g0, rs) =>
      match fold_left alias_global md (Some g0) with Some g => Some (g, rs) | None => None end
  | None => None
  end.

(** ## The first two passes do not see the erasure *)

(** An erased initializer has the size of the original. *)
Lemma items_size_erase items : items_size (erase_items items) = items_size items.
Proof. destruct items as [|d ds]; [reflexivity|]. unfold erase_items, items_size at 1. cbn. lia. Qed.

(** Placing an erased item gives the same next address, symbol and region
    as placing the original. *)
Lemma layout_erase_item keep st it : layout st (erase_item keep it) = layout st it.
Proof.
  destruct it as [f|n t|n lk al items|n lk t]; cbn [erase_item]; try reflexivity.
  destruct (keep n); [reflexivity|].
  destruct items as [|d ds]; [reflexivity|].
  unfold layout. destruct st as [[[a g] rs]|]; [|reflexivity]. cbv beta iota zeta.
  replace (erase_items (d :: ds)) with [Zero (items_size (d :: ds))] by reflexivity.
  destruct lk; rewrite <- (items_size_erase (d :: ds)); reflexivity.
Qed.

(** Resolving aliases looks only at aliases, which the erasure keeps. *)
Lemma alias_global_erase_item keep gs it : alias_global gs (erase_item keep it) = alias_global gs it.
Proof. destruct it as [f|n t|n lk al items|n lk t]; cbn [erase_item]; try reflexivity. destruct (keep n); reflexivity. Qed.

(** The placement pass over the erased module ends where it ends over the
    original. *)
Lemma layout_fold_erase keep md st :
  fold_left layout (erase keep md) st = fold_left layout md st.
Proof.
  unfold erase. revert st. induction md as [|it md IH]; intros st; [reflexivity|].
  cbn [map fold_left]. rewrite layout_erase_item. apply IH.
Qed.

(** The alias pass over the erased module ends where it ends over the
    original. *)
Lemma alias_fold_erase keep md gs :
  fold_left alias_global (erase keep md) gs = fold_left alias_global md gs.
Proof.
  unfold erase. revert gs. induction md as [|it md IH]; intros gs; [reflexivity|].
  cbn [map fold_left]. rewrite alias_global_erase_item. apply IH.
Qed.

(** The erased module has the original's symbols and regions. *)
Theorem image_layout_erase keep md : image_layout (erase keep md) = image_layout md.
Proof.
  unfold image_layout. rewrite layout_fold_erase.
  destruct (fold_left layout md _) as [[[a g0] rs]|]; [|reflexivity]. rewrite alias_fold_erase. reflexivity.
Qed.

(** When the loader succeeds on a module, the symbols it returns are the
    ones that the first two passes compute. *)
Lemma initial_memory_globals md g m :
  initial_memory md = Some (g, m) -> exists rs, image_layout md = Some (g, rs).
Proof.
  unfold initial_memory, image_layout.
  destruct (fold_left layout md _) as [[[a g0] rs]|]; [|discriminate]. cbv beta iota zeta.
  destruct (fold_left alias_global md _) as [g1|]; [|discriminate]. cbv beta iota zeta.
  destruct (fold_left (contents g1) md _); [|discriminate]. intros E. injection E as <- _. eauto.
Qed.

(** ## Controls

    A check that cannot fail proves nothing, so the lemmas below run the
    erasure on a small module and then try three wrong erasures. The
    module has one item of each kind, including an empty weak declaration
    and an alias of a data object. The real erasure keeps its addresses.
    Writing zero bytes into the weak declaration, dropping a size and
    retargeting the alias each change them. *)

Local Definition tx (s : string) : name := TAtom s.

(** This is the small module. *)
Local Definition sample : module :=
  [IData (tx "w") LExternWeak 8 [];
   IData (tx "k") (LRo (tx "local")) 1 [Str [67]; Zero 1];
   IFunc (mkFunc (tx "f") (tx "export") RVoid [] []);
   IData (tx "d") LExport 8 [Sym (tx "k") 0; Item Wl 7; Zero 24];
   IOutside (tx "o") (tx "outside");
   IAlias (tx "a") (tx "export") (tx "d");
   IData (tx "t") (LTls (tx "local")) 4 [Item Ww 1]].

(** Only the constant k is kept. *)
Local Definition keep_k (n : name) : bool := name_eqb n (tx "k").

(** The erasure keeps the symbols and regions, and they exist. *)
Lemma sample_erase :
  image_layout (erase keep_k sample) = image_layout sample /\ image_layout sample <> None.
Proof. split; [vm_compute; reflexivity | vm_compute; discriminate]. Qed.

(** Giving the empty weak declaration a zero run makes it a data object
    that the loader cannot place. *)
Lemma sample_weak_refused :
  image_layout (map (fun it => match it with IData n lk al [] => IData n lk al [Zero 0] | _ => erase_item keep_k it end)
    sample) = None.
Proof. vm_compute. reflexivity. Qed.

(** Dropping the size of d moves every later item. *)
Lemma sample_size_refused :
  image_layout (map (fun it => match it with IData n lk al (_ :: _) => if keep_k n then it else IData n lk al [Zero 0]
    | _ => it end) sample) <> image_layout sample.
Proof. vm_compute. discriminate. Qed.

(** Retargeting the alias changes the symbol it names. *)
Lemma sample_alias_refused :
  image_layout (map (fun it => match it with IAlias n lk _ => IAlias n lk (tx "k") | _ => erase_item keep_k it end)
    sample) <> image_layout sample.
Proof. vm_compute. discriminate. Qed.

(** An alias named y after a data object y sends y's initializer into x,
    the object that the alias names. The erased module has the same
    symbols and regions but writes nothing there, so equal layouts do
    not give equal memory. *)
Local Definition redirect : module :=
  [IData (tx "x") LExport 8 [Zero 8]; IData (tx "y") LExport 8 [Item Wl 7]; IAlias (tx "y") (tx "export") (tx "x")].

Lemma redirect_memory_differs :
  image_layout (erase (fun n => name_eqb n (tx "x")) redirect) = image_layout redirect /\
  option_map (fun gm => m_bytes (snd gm) 65536) (initial_memory redirect) = Some 7 /\
  option_map (fun gm => m_bytes (snd gm) 65536) (initial_memory (erase (fun n => name_eqb n (tx "x")) redirect)) = Some 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
