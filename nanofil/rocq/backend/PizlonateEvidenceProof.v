(** Before the translation [[validator]] can accept a pizlonated module,
    every rewritten memory access and indirect call must satisfy the
    checked-stage rules of [Validate](Validate.v). This module defines
    the typed syntax, ground-term decoder, and well-formedness judgment
    for unchecked Fil-C IR modules, then proves the per-instruction
    simulation, [[evidence-pass|evidence pass]], [[limit]] usage, and
    type-validity lemmas for [Pizlonate](Pizlonate.v).

    An unchecked instruction is either an ordinary core-subset
    instruction that uses no checked-stage construct, or one of the
    twelve unchecked heap, atomic, vector-access, and stack-local
    operations that [Pizlonate.checked_access] expands into a check
    paired with a raw access. For every valid unchecked instruction,
    [step_uinst] gives the exact one- or two-instruction checked
    expansion, and [duinst_checked_access_sim] and
    [duinst_non_access_sim] prove that [Pizlonate.inst_step] produces
    terms decoding to that expansion under
    [Transport.dinst](Transport.v).

    Because every emitted check is consumed immediately by the very
    next instruction, [checked_insts] accepts every pizlonated block
    from any incoming live-fact list. Lifting that step across all
    blocks discharges [Validate.evidence_pass] and
    [Validate.limit_reads] independently of predecessor facts, while
    [step_uinst_valid_inst] shows that every emitted instruction passes
    [Validate.valid_inst] whenever the temporary-class table preserves
    original classes and assigns each fresh proof name its check class. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Ops Semantics Cfg Validate Transport.
From Backend Require Import Text Pizlonate.
From Backend Require IrTerm NfbTransport.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Unset Lia Cache.

(** String equality written as in [Pizlonate](Pizlonate.v) and
    [Transport](Transport.v). *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Unchecked IR syntax and decoding

    Unchecked Fil-C IR shares its functions, blocks, phi nodes, jumps,
    data objects, and aliases with the checked IR of
    [Syntax](Syntax.v), differing only at memory accesses and pure
    pointer operations. This section defines the unchecked instruction
    inductive [uinst], its container records [ublock], [ufunc], and
    [uitem], and the term decoders [duinst] through [decode_umodule]. *)

(** An unchecked instruction [uinst] is either an ordinary core-subset
    instruction [UCore] without checked-stage constructs, or one of the
    twelve unchecked memory and access forms rewritten by
    [Pizlonate.checked_access]. *)
Inductive uinst : Type :=
| UCore (i : inst) (* an ordinary unchecked core-subset instruction *)
| ULoadPtr (d : name) (a : value) (* heap pointer load `let(tmp(d), p, load(p), [a])` *)
| ULoad (d : name) (k : class) (t : load_type) (a : value) (* scalar heap load `let(tmp(d), k, load(t), [a])` *)
| UAtomicLoadPtr (d : name) (a : value) (* atomic heap pointer load *)
| UCas (d : name) (k : class) (t : cas_type) (e n a : value) (* atomic compare-and-swap `[e; n; a]` *)
| UStorePtr (v a : value) (* heap pointer store `store(p, v, a)` *)
| UStore (w : width) (v a : value) (* scalar heap store `store(w, v, a)` for non-pointer width w *)
| UAtomicStorePtr (v a : value) (* atomic heap pointer store *)
| UAccess (r : rights) (a : value) (size align : Z) (* explicit access check `access(r, a, size, align)` *)
| ULocalLoadPtr (d : name) (x : name) (off : Z) (* stack-local pointer load *)
| ULocalLoad (d : name) (k : class) (t : load_type) (x : name) (off : Z) (* stack-local scalar load *)
| ULocalStorePtr (v : value) (x : name) (off : Z) (* stack-local pointer store *)
| ULocalStore (w : width) (v : value) (x : name) (off : Z). (* stack-local scalar store for non-pointer width w *)

(** An unchecked basic block [ublock] pairs its label, entry phi nodes,
    unchecked instructions, and terminating jump. *)
Record ublock : Type := mkUBlock {
  ub_label : name;
  ub_phis : list phi;
  ub_insts : list uinst;
  ub_jump : jump
}.

(** An unchecked function [ufunc] carries the same signature metadata
    as [Syntax.func] over a list of unchecked basic blocks. *)
Record ufunc : Type := mkUFunc {
  ufn_name : name;
  ufn_linkage : term;
  ufn_ret : ret_type;
  ufn_params : list (class * name);
  ufn_blocks : list ublock
}.

(** A top-level unchecked module entry [uitem] is a core-subset
    unchecked function, a global data object, or a symbol alias. *)
Inductive uitem : Type :=
| UIFunc (f : ufunc)
| UIData (n : name) (lk : linkage) (align : Z) (items : list data_item)
| UIAlias (n : name) (lk : term) (target : name).

(** An unchecked module [umodule] is a list of top-level unchecked items. *)
Definition umodule := list uitem.

(** Given a ground Prolog instruction term t, [duinst_core] decodes t as
    an ordinary unchecked core instruction via [Transport.dinst]. *)
Definition duinst_core (t : term) : option uinst :=
  let* i := dinst t in
  if negb (checked_inst i) then Some (UCore i) else None.

(** Given a ground Prolog instruction term t, [duinst] decodes t into
    its typed unchecked instruction [uinst], rejecting checked-stage
    instructions and constructs outside the core subset. *)
Definition duinst (t : term) : option uinst :=
  match t with
  | TApp f xs =>
      if f == "let" then
        match xs with
        | [d; k; o; a] =>
            match o, a with
            | TApp o [ty], TList args =>
                if o == "load" then
                  match args with
                  | [a] =>
                      if is_atom "p" k && is_atom "p" ty then
                        let* d' := dtmp d in let* a' := dvalue a in Some (ULoadPtr d' a')
                      else
                        let* d' := dtmp d in let* k' := dclass k in
                        let* lt := dload_type ty in let* a' := dvalue a in
                        Some (ULoad d' k' lt a')
                  | _ => None
                  end
                else if o == "atomic_load" then
                  match args with
                  | [a] =>
                      if is_atom "p" k && is_atom "p" ty then
                        let* d' := dtmp d in let* a' := dvalue a in Some (UAtomicLoadPtr d' a')
                      else None
                  | _ => None
                  end
                else if o == "cas" then
                  match args with
                  | [e; n; a] =>
                      let* d' := dtmp d in let* k' := dclass k in let* ct := dcas_type ty in
                      let* e' := dvalue e in let* n' := dvalue n in let* a' := dvalue a in
                      Some (UCas d' k' ct e' n' a')
                  | _ => None
                  end
                else duinst_core t
            | _, _ => duinst_core t
            end
        | _ => duinst_core t
        end
      else if f == "store" then
        match xs with
        | [w; v; a] =>
            if is_atom "p" w then
              let* v' := dvalue v in let* a' := dvalue a in Some (UStorePtr v' a')
            else
              let* w' := dwidth w in
              match w' with
              | Wp => None
              | _ => let* v' := dvalue v in let* a' := dvalue a in Some (UStore w' v' a')
              end
        | _ => None
        end
      else if f == "atomic_store" then
        match xs with
        | [w; v; a] =>
            if is_atom "p" w then
              let* v' := dvalue v in let* a' := dvalue a in Some (UAtomicStorePtr v' a')
            else None
        | _ => None
        end
      else if f == "access" then
        match xs with
        | [r; a; TInt sz; TInt al] =>
            let* r' := drights r in let* a' := dvalue a in Some (UAccess r' a' sz al)
        | _ => None
        end
      else if f == "local_load" then
        match xs with
        | [d; k; ty; x; TInt off] =>
            if is_atom "p" ty then
              if is_atom "p" k then let* d' := dtmp d in Some (ULocalLoadPtr d' x off) else None
            else
              let* d' := dtmp d in let* k' := dclass k in let* lt := dload_type ty in
              Some (ULocalLoad d' k' lt x off)
        | _ => None
        end
      else if f == "local_store" then
        match xs with
        | [w; v; x; TInt off] =>
            if is_atom "p" w then
              let* v' := dvalue v in Some (ULocalStorePtr v' x off)
            else
              let* w' := dwidth w in
              match w' with
              | Wp => None
              | _ => let* v' := dvalue v in Some (ULocalStore w' v' x off)
              end
        | _ => None
        end
      else duinst_core t
  | _ => None
  end.

(** Given a ground block term t, [dublock] decodes its phi nodes,
    unchecked instructions, and terminating jump into a [ublock]. *)
Definition dublock (t : term) : option ublock :=
  match t with
  | TApp "block" [l; TList phis; TList insts; j] =>
      let* phis' := map_option dphi phis in
      let* insts' := map_option duinst insts in
      let* j' := djump j in
      Some (mkUBlock l phis' insts' j')
  | _ => None
  end.

(** Given the five subterms of a function declaration, [dufunc] decodes
    its return type, parameter list, and unchecked blocks into a [ufunc]. *)
Definition dufunc (n lk r ps bs : term) : option ufunc :=
  let* r' := dret r in
  let* ps' := let* ts := dlist ps in map_option dparam ts in
  let* bs' := let* ts := dlist bs in map_option dublock ts in
  Some (mkUFunc n lk r' ps' bs').

(** Given a top-level term t, [duitem] decodes a core-subset unchecked
    function, a data object, or an alias, returning `Some None` for
    `context` annotations so [decode_umodule] drops them. *)
Definition duitem (t : term) : option (option uitem) :=
  match t with
  | TApp "func" [n; lk; r; ps; bs] =>
      let* uf := dufunc n lk r ps bs in Some (Some (UIFunc uf))
  | TApp "data" [n; lk; TInt al; TList its] =>
      let* lk' := dlinkage lk in let* its' := map_option ddata_item its in
      Some (Some (UIData n lk' al its'))
  | TApp "alias" [n; lk; tg] => Some (Some (UIAlias n lk tg))
  | TApp "context" [_; _] => Some None
  | _ => None
  end.

(** Given a ground module term t, [decode_umodule] decodes every item
    with [duitem] and drops `context` annotations to produce a [umodule]. *)
Definition decode_umodule (t : term) : option umodule :=
  match t with
  | TApp "module" [TList items] =>
      let* its := map_option duitem items in
      Some (flat_map (fun o => match o with Some i => [i] | None => [] end) its)
  | _ => None
  end.

(** ## Skeleton projection and unchecked well-formedness

    Module-level checks such as [unique_names], [func_sig],
    [init_entry_named], [valid_data], [valid_alias], and
    [block_intervals] inspect only declarations, jumps, and core
    instructions such as `local_alloc`, `va_args`, `setjmp`, and direct
    calls. Projecting an unchecked module to its core skeleton lets
    unchecked well-formedness reuse those exact validator functions
    without duplicating them. *)

(** Given an unchecked basic block ub, [uskel_block] retains only its
    [UCore] instructions while preserving its label, phis, and jump. *)
Definition uskel_block (ub : ublock) : block :=
  mkBlock (ub_label ub) (ub_phis ub)
    (flat_map (fun ui => match ui with UCore i => [i] | _ => [] end) (ub_insts ub))
    (ub_jump ub).

(** Given an unchecked function uf, [uskel_func] maps each block with
    [uskel_block] while preserving the function header identically. *)
Definition uskel_func (uf : ufunc) : func :=
  mkFunc (ufn_name uf) (ufn_linkage uf) (ufn_ret uf) (ufn_params uf)
    (map uskel_block (ufn_blocks uf)).

(** Given an unchecked item it, [uskel_item] converts it into the
    corresponding [Syntax.item] skeleton. *)
Definition uskel_item (it : uitem) : item :=
  match it with
  | UIFunc uf => IFunc (uskel_func uf)
  | UIData n lk al its => IData n lk al its
  | UIAlias n lk tg => IAlias n lk tg
  end.

(** Given an unchecked module umd, [uskel_module] projects every item
    with [uskel_item]. *)
Definition uskel_module (umd : umodule) : module := map uskel_item umd.

(** Predicate [uinst_is_access] identifies the unchecked instructions
    that [Pizlonate.checked_access] expands into a fresh proof check
    followed by a raw access or raw call. *)
Definition uinst_is_access (ui : uinst) : bool :=
  match ui with
  | UCore (Call _ (Tmp _) _) => true
  | UCore _ => false
  | _ => true
  end.

(** Predicate [uinst_is_flight] identifies the pure pointer operations
    that [Pizlonate.flight_inst] rewrites into [Flight] instructions. *)
Definition uinst_is_flight (ui : uinst) : bool :=
  match ui with
  | UCore (Let _ P Add [_; _])
  | UCore (Let _ P Sub [_; _])
  | UCore (Let _ P Itop [_])
  | UCore (Let _ P Copy [Tmp _])
  | UCore (Let _ P Copy [Const _]) => true
  | _ => false
  end.

(** Predicate [uinst_is_loc] returns `true` for a source-location
    marker `loc(File, Line)`. *)
Definition uinst_is_loc (ui : uinst) : bool :=
  match ui with UCore (Loc _ _) => true | _ => false end.

(** Given an unchecked instruction ui, [uinst_temp_defs] returns the
    temporaries it defines paired with their register classes. *)
Definition uinst_temp_defs (ui : uinst) : list (name * class) :=
  match ui with
  | UCore i => inst_temp_defs i
  | ULoadPtr d _ | UAtomicLoadPtr d _ | ULocalLoadPtr d _ _ => [(d, P)]
  | ULoad d k _ _ | UCas d k _ _ _ _ | ULocalLoad d k _ _ _ => [(d, k)]
  | UStorePtr _ _ | UStore _ _ _ | UAtomicStorePtr _ _
  | UAccess _ _ _ _ | ULocalStorePtr _ _ _ | ULocalStore _ _ _ _ => []
  end.

(** Given an unchecked instruction ui, [uinst_uses] returns the
    temporary names that ui reads. *)
Definition uinst_uses (ui : uinst) : list name :=
  match ui with
  | UCore i => inst_uses i
  | ULoadPtr _ a | ULoad _ _ _ a | UAtomicLoadPtr _ a | UAccess _ a _ _ => value_temps [a]
  | UCas _ _ _ e n a => value_temps [a; e; n]
  | UStorePtr v a | UStore _ v a | UAtomicStorePtr v a => value_temps [v; a]
  | ULocalLoadPtr _ _ _ | ULocalLoad _ _ _ _ _ => []
  | ULocalStorePtr v _ _ | ULocalStore _ v _ _ => value_temps [v]
  end.

(** Given an unchecked function uf, [utemp_defs] collects all parameter,
    phi, and instruction temporary definitions in program order. *)
Definition utemp_defs (uf : ufunc) : list (name * class) :=
  map (fun p => (snd p, fst p)) (ufn_params uf) ++
  flat_map (fun ub => map (fun ph => match ph with Phi d k _ => (d, k) end) (ub_phis ub)
                      ++ flat_map uinst_temp_defs (ub_insts ub)) (ufn_blocks uf).

(** Given an unchecked function uf, [utemp_sites] records the definition
    sites of every temporary in uf, mirroring [Validate.temp_sites]. *)
Definition utemp_sites (uf : ufunc) : nmap (list site) :=
  let add (m : nmap (list site)) (n : name) (s : site) :=
    nm_add n (s :: match nm_find n m with Some ss => ss | None => [] end) m in
  let m0 := fold_left (fun m p => add m (snd p) SParam) (ufn_params uf) nm_empty in
  fold_left (fun m ub =>
               let m1 := fold_left (fun m ph => match ph with Phi d _ _ => add m d (SAt (ub_label ub) (-1)) end)
                                   (ub_phis ub) m in
               fst (fold_left (fun (acc : nmap (list site) * Z) ui =>
                                 let (m, j) := acc in
                                 (fold_left (fun m dk => add m (fst dk) (SAt (ub_label ub) j))
                                            (uinst_temp_defs ui) m, j + 1))
                              (ub_insts ub) (m1, 0)))
            (ufn_blocks uf) m0.

(** Given an unchecked function uf and its dominator intervals doms,
    [udefinitions_dominate] checks strict SSA dominance across every
    reachable block of uf, mirroring [Validate.definitions_dominate]. *)
Definition udefinitions_dominate (uf : ufunc) (doms : nmap (Z * Z)) : bool :=
  let sites := utemp_sites uf in
  let ends := nm_of_list (map (fun ub => (ub_label ub, Z.of_nat (length (ub_insts ub)))) (ufn_blocks uf)) in
  let dom_use := dominated_use sites in
  forallb (fun ub =>
             if negb (is_reachable doms (ub_label ub)) then true else
             let l := ub_label ub in
             let fix insts (uis : list uinst) (i : Z) : bool :=
               match uis with
               | [] => forallb (dom_use doms l i) (jump_uses (ub_jump ub))
               | ui :: rest => forallb (dom_use doms l i) (uinst_uses ui)
                               && insts rest (i + 1)
               end in
             insts (ub_insts ub) 0 &&
             forallb (fun ph =>
                        match ph with
                        | Phi _ _ pairs =>
                            forallb (fun pv =>
                                       match snd pv with
                                       | Tmp n =>
                                           if is_reachable doms (fst pv) then
                                             match nm_find (fst pv) ends with
                                             | Some e => dom_use doms (fst pv) e n
                                             | None => true
                                             end
                                           else true
                                       | _ => true
                                       end) pairs
                        end) (ub_phis ub))
          (ufn_blocks uf).

(** Given an unchecked function uf, [ulocal_objects] collects all
    [LocalAlloc] declarations in instruction order. *)
Definition ulocal_objects (uf : ufunc) : list (name * Z) :=
  flat_map (fun ub => flat_map (fun ui => match ui with
                                          | UCore (LocalAlloc x sz) => [(x, sz)]
                                          | _ => []
                                          end) (ub_insts ub))
           (ufn_blocks uf).

(** Given an unchecked instruction ui, [uinst_local_target] returns the
    stack-local name accessed by a local load or store, or `None` for
    any other instruction. *)
Definition uinst_local_target (ui : uinst) : option name :=
  match ui with
  | ULocalLoadPtr _ x _ | ULocalLoad _ _ _ x _
  | ULocalStorePtr _ x _ | ULocalStore _ _ x _ => Some x
  | _ => None
  end.

(** Given an unchecked function uf, [uvalid_locals] mirrors
    [Validate.valid_locals] for unchecked stack-local accesses: every
    local name is unique, locals are disallowed with `setjmp`, every
    [LocalAlloc] sits in the entry block, and every local load or store
    names a local allocated earlier in the entry block. *)
Definition uvalid_locals (uf : ufunc) : bool :=
  let objs := ulocal_objects uf in
  no_dups (map fst objs) &&
  match objs with [] => true | _ :: _ => negb (setjmp_func (uskel_func uf)) end &&
  match ufn_blocks uf with
  | [] => false
  | entry :: _ =>
      let declared := fst (fold_left (fun (acc : list (name * Z) * Z) ui =>
                                        let (ds, j) := acc in
                                        match ui with
                                        | UCore (LocalAlloc x _) => (ds ++ [(x, j)], j + 1)
                                        | _ => (ds, j + 1)
                                        end) (ub_insts entry) ([], 0)) in
      (length declared =? length objs)%nat &&
      forallb (fun ub =>
                 fst (fold_left (fun (acc : bool * Z) ui =>
                                   let (ok, j) := acc in
                                   (ok && match uinst_local_target ui with
                                          | Some x =>
                                              match lookup x declared with
                                              | Some at_ => negb (name_eqb (ub_label ub) (ub_label entry))
                                                            || (at_ <? j)
                                              | None => false
                                              end
                                          | None => true
                                          end, j + 1)) (ub_insts ub) (true, 0)))
              (ufn_blocks uf)
  end.

(** Given the Fil-C mode flag filc, an unchecked module umd, a
    temporary-class table classes, and an unchecked instruction ui,
    [uvalid_inst] checks that ui is well typed in unchecked IR. In
    plain mode (`filc = false`), unchecked Fil-C accesses and pointer
    flights are forbidden because [Pizlonate.pizlonate_module] rewrites
    only jumps in plain mode. *)
Definition uvalid_inst (filc : bool) (umd : umodule) (classes : list (name * class))
    (ui : uinst) : bool :=
  let use := valid_use classes in
  if negb filc then
    match ui with
    | UCore i =>
        negb (checked_inst i) && negb (uinst_is_access ui) && negb (uinst_is_flight ui)
        && valid_inst (uskel_module umd) classes i
    | _ => false
    end
  else
    match ui with
    | UCore i => negb (checked_inst i) && valid_inst (uskel_module umd) classes i
    | ULoadPtr _ a => use P a
    | ULoad _ k lt a => op_result_ok (RawLoad lt 0) k && use P a
    | UAtomicLoadPtr _ a => use P a
    | UCas _ k ct e n a => op_result_ok (RawCas ct 0) k && use k e && use k n && use P a
    | UStorePtr v a => use P v && use P a
    | UStore w v a =>
        match width_value_ok w with
        | Some k => use k v && use P a
        | None => false
        end
    | UAtomicStorePtr v a => use P v && use P a
    | UAccess _ a sz al => check_ok 0 sz al && use P a
    | ULocalLoadPtr _ _ off => local_offset off
    | ULocalLoad _ k lt _ off => op_result_ok (RawLoad lt 0) k && local_offset off
    | ULocalStorePtr v _ off => use P v && local_offset off
    | ULocalStore w v _ off =>
        match width_value_ok w with
        | Some k => use k v && local_offset off
        | None => false
        end
    end.

(** Given mode flag filc, unchecked module umd, function uf, class
    table classes, and block ub, [uvalid_block] checks phis,
    instructions, jump, non-empty predecessors for phi blocks, and the
    absence of poll edges in the unchecked input. *)
Definition uvalid_block (filc : bool) (umd : umodule) (uf : ufunc)
    (classes : list (name * class)) (ub : ublock) : bool :=
  let sk := uskel_func uf in
  let preds := preds_of (fn_blocks sk) (ub_label ub) in
  forallb (valid_phi classes preds) (ub_phis ub)
  && forallb (uvalid_inst filc umd classes) (ub_insts ub)
  && valid_jump sk classes (ub_jump ub)
  && negb (checked_jump (ub_jump ub))
  && (match ub_phis ub, preds with _ :: _, [] => false | _, _ => true end).

(** Given mode flag filc, unchecked module umd, and unchecked function
    uf, [uvalid_func] checks every structural, typing, SSA dominance,
    and stack-local rule required of an unchecked Fil-C function. *)
Definition uvalid_func (filc : bool) (umd : umodule) (uf : ufunc) : bool :=
  let sk := uskel_func uf in
  let bs := fn_blocks sk in
  let defs := utemp_defs uf in
  match bs, block_intervals bs with
  | [], _ | _, None => false
  | entry :: _, Some doms =>
      match ufn_linkage uf with TAtom ("export" | "local" | "weak") => true | _ => false end
      && match ufn_ret uf with
         | RTuple ks =>
             (length ks =? 2)%nat
             && forallb (fun k => existsb (class_eqb k) [L; P; Single; Double]) ks
         | RClass k => any_class k
         | RVoid => true
         end
      && negb (extended_crosses sk)
      && no_dups (map b_label bs)
      && temp_classes_ok defs
      && negb (existsb (fun b => mem (b_label entry) (succ_labels (b_jump b))) bs)
      && proof_class_defs sk
      && udefinitions_dominate uf doms
      && uvalid_locals uf
      && forallb (uvalid_block filc umd uf defs) (ufn_blocks uf)
  end.

(** A ground Prolog module term m satisfies [valid_unchecked_module]
    when it decodes as an unchecked core-subset module whose defined
    names are unique and whose functions, data objects, and aliases all
    pass their unchecked well-formedness checks. *)
Definition valid_unchecked_module (m : term) : Prop :=
  exists items umd,
    m = TApp "module" [TList items] /\
    decode_umodule m = Some umd /\
    let filc := Pizlonate.module_filc items in
    let sk := uskel_module umd in
    unique_names sk = true /\
    Forall (fun it =>
              match it with
              | UIFunc uf => uvalid_func filc umd uf = true
              | UIData n lk al its => valid_data sk n lk al its = true
              | UIAlias n lk tg => valid_alias sk n lk tg = true
              end) umd.

(** ## Abstract checked expansion

    Rather than reasoning directly on raw Prolog term lists inside the
    evidence and typing proofs, we define the typed expansion
    [step_uinst] corresponding to one step of [Pizlonate.inst_step].
    Every unchecked access or indirect call expands to a two-instruction
    check-and-raw pair using the supplied fresh proof name, every pure
    pointer operation expands to a single [Flight], and every other
    instruction stays unchanged. *)

(** Given fresh proof name q and a core-subset instruction i,
    [step_core_inst] rewrites indirect calls into `check_function` plus
    `raw_call`, rewrites pure pointer operations into [Flight]
    instructions, and leaves every other instruction unchanged. *)
Definition step_core_inst (q : name) (i : inst) : list inst :=
  match i with
  | Call r (Tmp p) args => [Let q F CheckFunction [Tmp p]; RawCall r (Tmp q) args]
  | Let d P Add [p; x] => [Flight d Add [FAddress p; FValue x] (LowerOf p)]
  | Let d P Sub [p; x] => [Flight d Sub [FAddress p; FValue x] (LowerOf p)]
  | Let d P Copy [Tmp x] => [Flight d Copy [FAddress (Tmp x)] (LowerOf (Tmp x))]
  | Let d P Copy [Const c] => [Flight d Copy [FAddress (Const c)] (LowerOf (Const c))]
  | Let d P Itop [x] => [Flight d Copy [FValue x] LowerNone]
  | _ => [i]
  end.

(** Given mode flag filc, fresh proof name q, and unchecked instruction
    ui, [step_uinst] returns the checked instruction list emitted for ui. *)
Definition step_uinst (filc : bool) (q : name) (ui : uinst) : list inst :=
  if negb filc then
    match ui with UCore i => [i] | _ => [] end
  else
    match ui with
    | ULoadPtr d a =>
        [Let q A (Check 0 8 Read 8) [a];
         Let d P (RawLoadPointer 0 Syntax.load_effects) [Tmp q]]
    | ULoad d k lt a =>
        let '(sz, al) := access_size_align (XLoad lt) in
        [Let q A (Check 0 sz Read al) [a];
         Let d k (RawLoad lt 0) [Tmp q]]
    | UAtomicLoadPtr d a =>
        [Let q A (Check 0 8 Read 8) [a];
         Let d P (RawLoadPointer 0 atomic_load_effects) [Tmp q]]
    | UCas d k ct e n a =>
        let sz := Syntax.cas_bytes ct in
        [Let q A (Check 0 sz Write sz) [a];
         Let d k (RawCas ct 0) [Tmp q; e; n]]
    | UStorePtr v a =>
        [Let q A (Check 0 8 Write 8) [a];
         RawStorePointer 0 v (Tmp q) Validate.store_effects]
    | UStore w v a =>
        let '(sz, al) := access_size_align (XWidth w) in
        [Let q A (Check 0 sz Write al) [a];
         RawStore w 0 v (Tmp q)]
    | UAtomicStorePtr v a =>
        [Let q A (Check 0 8 Write 8) [a];
         RawStorePointer 0 v (Tmp q) atomic_store_effects]
    | UAccess r a sz al =>
        [Let q A (Check 0 sz r al) [a]; Touch q]
    | ULocalLoadPtr d x off =>
        [Let q A (CheckLocal x off 8 Read 8) [];
         Let d P (RawLoadPointer 0 Syntax.local_load_effects) [Tmp q]]
    | ULocalLoad d k lt x off =>
        let '(sz, al) := access_size_align (XLoad lt) in
        [Let q A (CheckLocal x off sz Read al) [];
         Let d k (RawLoad lt 0) [Tmp q]]
    | ULocalStorePtr v x off =>
        [Let q A (CheckLocal x off 8 Write 8) [];
         RawStorePointer 0 v (Tmp q) Validate.local_store_effects]
    | ULocalStore w v x off =>
        let '(sz, al) := access_size_align (XWidth w) in
        [Let q A (CheckLocal x off sz Write al) [];
         RawStore w 0 v (Tmp q)]
    | UCore i => step_core_inst q i
    end.

(** ## Evidence pass and limit reads

    Because every access emitted by [step_uinst] places its capability
    check immediately before the raw access or call that consumes it,
    [Validate.checked_inst_rest] accepts each expanded piece in a single
    step from any incoming list of live facts. This section proves that
    single-step lemma and lifts it to whole blocks and functions to
    establish [Validate.evidence_pass] and [Validate.limit_reads]. *)

(** Equality on names is reflexive. *)
Lemma name_eqb_refl : forall n : name, name_eqb n n = true.
Proof. intros n. apply term_eqb_refl. Qed.

(** Equality on effect lists is reflexive. *)
Lemma effects_eqb_refl : forall es : list effect, effects_eqb es es = true.
Proof.
  induction es as [|e es IH]; simpl; [reflexivity|].
  destruct e; simpl; exact IH.
Qed.

(** Every load type has a positive transfer size and a valid check
    alignment that divides itself. *)
Lemma load_size_align_ok : forall lt,
  let '(sz, al) := access_size_align (XLoad lt) in
  0 < sz /\ sz <= 2 ^ 31 - 1 /\ check_align al = true /\ al mod al = 0 /\ 0 mod al = 0.
Proof.
  intros [| | | |[| | | | |]]; simpl;
    repeat split; try reflexivity; lia.
Qed.

(** Every non-pointer store width has a positive transfer size and a
    valid check alignment that divides itself. *)
Lemma width_size_align_ok : forall w,
  w <> Wp ->
  let '(sz, al) := access_size_align (XWidth w) in
  0 < sz /\ sz <= 2 ^ 31 - 1 /\ check_align al = true /\ al mod al = 0 /\ 0 mod al = 0.
Proof.
  intros [| | | | | | |] Hw; try contradiction; simpl;
    repeat split; try reflexivity; lia.
Qed.

(** Every compare-and-swap type has a positive transfer size that is a
    valid check alignment and divides itself. *)
Lemma cas_size_ok : forall ct,
  let sz := Syntax.cas_bytes ct in
  0 < sz /\ check_align sz = true /\ sz mod sz = 0 /\ 0 mod sz = 0.
Proof.
  intros [| |[| | | | |]]; simpl;
    repeat split; try reflexivity; lia.
Qed.

(** Access rights always permit the same rights they prove. *)
Lemma rights_allow_refl : forall r, rights_allow r r = true.
Proof. intros [|]; reflexivity. Qed.

(** Any unchecked [Let] instruction that is neither an implicit pointer
    flight nor a checked operation passes [checked_inst_rest] directly
    from any live-fact list. *)
Lemma checked_inst_rest_unchecked_let : forall d k o args s rest live,
  checked_op o = false ->
  (k = P ->
   o <> Add /\ o <> Sub /\ o <> Itop /\
   (o = Copy -> match args with [Tmp _] | [Const _] => False | _ => True end)) ->
  exists live',
    checked_inst_rest s (Let d k o args) rest live = Some (rest, live').
Proof.
  intros d k o args s rest live Hnc Hnf.
  destruct o; simpl in Hnc; try discriminate Hnc.
  all: try (destruct k; eexists; reflexivity).
  - destruct k; try (eexists; reflexivity).
    exfalso. destruct (Hnf eq_refl) as [H _]. exact (H eq_refl).
  - destruct k; try (eexists; reflexivity).
    exfalso. destruct (Hnf eq_refl) as [_ [H _]]. exact (H eq_refl).
  - destruct k; try (eexists; reflexivity).
    destruct (Hnf eq_refl) as (_ & _ & _ & Hc). specialize (Hc eq_refl).
    destruct args as [|[x | c | g] [|]]; try contradiction; eexists; reflexivity.
  - destruct k; try (eexists; reflexivity).
    exfalso. destruct (Hnf eq_refl) as (_ & _ & H & _). exact (H eq_refl).
Qed.

(** Every valid unchecked instruction's [step_uinst] expansion is
    consumed in a single step by [checked_insts], regardless of the
    precomputed reuse tables [s] or the incoming live facts [live]. *)
Lemma step_uinst_checked_insts : forall filc umd classes ui q s fuel rest live,
  uvalid_inst filc umd classes ui = true ->
  exists live',
    checked_insts s (S fuel) (step_uinst filc q ui ++ rest) live =
    checked_insts s fuel rest live'.
Proof.
  intros filc umd classes ui q s fuel rest live Hv.
  destruct filc.
  - (* filc = true *)
    destruct ui as [i | d a | d k lt a | d a | d k ct e n a | v a | w v a | v a | r a sz al
                    | d x off | d k lt x off | v x off | w v x off];
      cbn [step_uinst uvalid_inst negb] in *.
    + (* UCore i *)
      apply andb_true_iff in Hv as [Hnc Hvi].
      apply negb_true_iff in Hnc.
      destruct i as [d k o args | d o args lw | w off v a | off v a es
                     | r cl args | r cl args | x sz | fn ln | tq];
        simpl in Hnc; try discriminate Hnc.
      * (* Let d k o args *)
        destruct k;
          try (cbn [step_core_inst app checked_insts];
               match goal with
               | |- context [checked_inst_rest s (Let d ?k0 o args) rest live] =>
                   destruct (checked_inst_rest_unchecked_let d k0 o args s rest live Hnc
                               ltac:(intro; discriminate)) as [live' Hstep];
                   rewrite Hstep; exists live'; reflexivity
               end).
        (* k = P *)
        destruct o; try discriminate Hnc;
          try (cbn [step_core_inst app checked_insts];
               match goal with
               | |- context [checked_inst_rest s (Let d P ?o0 args) rest live] =>
                   destruct (checked_inst_rest_unchecked_let d P o0 args s rest live Hnc
                               ltac:(intros _; repeat split; try discriminate; intros; discriminate))
                     as [live' Hstep];
                   rewrite Hstep; exists live'; reflexivity
               end).
        -- destruct args as [|p [|x [|]]]; simpl in Hvi;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
             try discriminate.
           eexists; cbn [step_core_inst app checked_insts checked_inst_rest raw_access]; reflexivity.
        -- destruct args as [|p [|x [|]]]; simpl in Hvi;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
             try discriminate.
           eexists; cbn [step_core_inst app checked_insts checked_inst_rest raw_access]; reflexivity.
        -- destruct args as [|[x | c | g] [|]]; simpl in Hvi;
             try (repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
                  discriminate).
           all: eexists; cbn [step_core_inst app checked_insts checked_inst_rest raw_access]; reflexivity.
        -- destruct args as [|x [|]]; simpl in Hvi;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
             try discriminate.
           eexists; cbn [step_core_inst app checked_insts checked_inst_rest raw_access]; reflexivity.
      * (* Call r cl args *)
        destruct cl as [p | c | g].
        -- eexists. cbn [step_core_inst app checked_insts checked_inst_rest].
           rewrite name_eqb_refl. reflexivity.
        -- simpl in Hvi. discriminate Hvi.
        -- eexists. cbn [step_core_inst app checked_insts checked_inst_rest raw_access]. reflexivity.
      * eexists. cbn [step_core_inst app checked_insts checked_inst_rest raw_access]. reflexivity.
      * eexists. cbn [step_core_inst app checked_insts checked_inst_rest raw_access]. reflexivity.
    + (* ULoadPtr *)
      eexists. cbn [app checked_insts checked_inst_rest proof_use covered_access raw_access
                    access_size_align rights_allow storage_effects].
      rewrite name_eqb_refl, effects_eqb_refl. reflexivity.
    + (* ULoad *)
      pose proof (load_size_align_ok lt) as Hsa.
      destruct (access_size_align (XLoad lt)) as [sz al] eqn:Esa.
      destruct Hsa as (Hsz & _ & _ & Haa & H0a).
      eexists. cbn [app checked_insts checked_inst_rest proof_use covered_access raw_access
                    rights_allow storage_effects].
      rewrite Esa, name_eqb_refl.
      assert (Hle1 : (0 <=? 0) = true) by reflexivity.
      assert (Hle2 : (0 + sz <=? sz) = true) by (apply Z.leb_le; lia).
      assert (Hm1 : (al mod al =? 0) = true) by (apply Z.eqb_eq; exact Haa).
      assert (Hm2 : ((0 - 0) mod al =? 0) = true) by (apply Z.eqb_eq; exact H0a).
      rewrite Hle1, Hle2, Hm1, Hm2. destruct k; reflexivity.
    + (* UAtomicLoadPtr *)
      eexists. cbn [app checked_insts checked_inst_rest proof_use covered_access raw_access
                    access_size_align rights_allow storage_effects].
      rewrite name_eqb_refl, effects_eqb_refl, orb_true_r. reflexivity.
    + (* UCas *)
      pose proof (cas_size_ok ct) as (Hsz & _ & Haa & H0a).
      eexists. cbn [app checked_insts checked_inst_rest proof_use covered_access raw_access
                    access_size_align rights_allow storage_effects].
      rewrite name_eqb_refl.
      assert (Hle1 : (0 <=? 0) = true) by reflexivity.
      assert (Hle2 : (0 + Syntax.cas_bytes ct <=? Syntax.cas_bytes ct) = true) by (apply Z.leb_le; lia).
      assert (Hm1 : (Syntax.cas_bytes ct mod Syntax.cas_bytes ct =? 0) = true) by (apply Z.eqb_eq; exact Haa).
      assert (Hm2 : ((0 - 0) mod Syntax.cas_bytes ct =? 0) = true) by (apply Z.eqb_eq; exact H0a).
      rewrite Hle1, Hle2, Hm1, Hm2. destruct k; reflexivity.
    + (* UStorePtr *)
      eexists. cbn [app checked_insts checked_inst_rest proof_use covered_access raw_access
                    access_size_align rights_allow storage_effects].
      rewrite name_eqb_refl, effects_eqb_refl. reflexivity.
    + (* UStore *)
      assert (Hw : w <> Wp) by (intro E; subst w; simpl in Hv; discriminate Hv).
      pose proof (width_size_align_ok w Hw) as Hsa.
      destruct (access_size_align (XWidth w)) as [sz al] eqn:Esa.
      destruct Hsa as (Hsz & _ & _ & Haa & H0a).
      eexists. cbn [app checked_insts checked_inst_rest proof_use covered_access raw_access
                    rights_allow storage_effects].
      rewrite Esa, name_eqb_refl.
      assert (Hle1 : (0 <=? 0) = true) by reflexivity.
      assert (Hle2 : (0 + sz <=? sz) = true) by (apply Z.leb_le; lia).
      assert (Hm1 : (al mod al =? 0) = true) by (apply Z.eqb_eq; exact Haa).
      assert (Hm2 : ((0 - 0) mod al =? 0) = true) by (apply Z.eqb_eq; exact H0a).
      rewrite Hle1, Hle2, Hm1, Hm2. reflexivity.
    + (* UAtomicStorePtr *)
      eexists. cbn [app checked_insts checked_inst_rest proof_use covered_access raw_access
                    access_size_align rights_allow storage_effects].
      rewrite name_eqb_refl, effects_eqb_refl, orb_true_r. reflexivity.
    + (* UAccess *)
      eexists. cbn [app checked_insts checked_inst_rest proof_use].
      rewrite name_eqb_refl. reflexivity.
    + (* ULocalLoadPtr *)
      eexists. cbn [app checked_insts checked_inst_rest covered_access raw_access
                    access_size_align rights_allow storage_effects].
      rewrite name_eqb_refl, effects_eqb_refl. reflexivity.
    + (* ULocalLoad *)
      pose proof (load_size_align_ok lt) as Hsa.
      destruct (access_size_align (XLoad lt)) as [sz al] eqn:Esa.
      destruct Hsa as (Hsz & _ & _ & Haa & H0a).
      eexists. cbn [app checked_insts checked_inst_rest covered_access raw_access
                    rights_allow storage_effects].
      rewrite Esa, name_eqb_refl.
      assert (Hle1 : (0 <=? 0) = true) by reflexivity.
      assert (Hle2 : (0 + sz <=? sz) = true) by (apply Z.leb_le; lia).
      assert (Hm1 : (al mod al =? 0) = true) by (apply Z.eqb_eq; exact Haa).
      assert (Hm2 : ((0 - 0) mod al =? 0) = true) by (apply Z.eqb_eq; exact H0a).
      rewrite Hle1, Hle2, Hm1, Hm2. destruct k; reflexivity.
    + (* ULocalStorePtr *)
      eexists. cbn [app checked_insts checked_inst_rest covered_access raw_access
                    access_size_align rights_allow storage_effects].
      rewrite name_eqb_refl, effects_eqb_refl. reflexivity.
    + (* ULocalStore *)
      assert (Hw : w <> Wp) by (intro E; subst w; simpl in Hv; discriminate Hv).
      pose proof (width_size_align_ok w Hw) as Hsa.
      destruct (access_size_align (XWidth w)) as [sz al] eqn:Esa.
      destruct Hsa as (Hsz & _ & _ & Haa & H0a).
      eexists. cbn [app checked_insts checked_inst_rest covered_access raw_access
                    rights_allow storage_effects].
      rewrite Esa, name_eqb_refl.
      assert (Hle1 : (0 <=? 0) = true) by reflexivity.
      assert (Hle2 : (0 + sz <=? sz) = true) by (apply Z.leb_le; lia).
      assert (Hm1 : (al mod al =? 0) = true) by (apply Z.eqb_eq; exact Haa).
      assert (Hm2 : ((0 - 0) mod al =? 0) = true) by (apply Z.eqb_eq; exact H0a).
      rewrite Hle1, Hle2, Hm1, Hm2. reflexivity.
  - (* filc = false *)
    destruct ui as [i | | | | | | | | | | | |]; cbn [uvalid_inst negb] in Hv; try discriminate Hv.
    repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
    match goal with H : negb (checked_inst i) = true |- _ => apply negb_true_iff in H end.
    match goal with H : negb (uinst_is_access _) = true |- _ => apply negb_true_iff in H end.
    match goal with H : negb (uinst_is_flight _) = true |- _ => apply negb_true_iff in H end.
    destruct i as [d k o args | d o args lw | w off v a | off v a es
                   | r cl args | r cl args | x sz | fn ln | tq];
      cbn [checked_inst uinst_is_access uinst_is_flight] in *; try discriminate.
    + destruct k;
        try (cbn [step_uinst negb app checked_insts];
             match goal with
             | |- context [checked_inst_rest s (Let d ?k0 o args) rest live] =>
                 destruct (checked_inst_rest_unchecked_let d k0 o args s rest live ltac:(assumption)
                             ltac:(intro; discriminate)) as [live' Hstep];
                 rewrite Hstep; exists live'; reflexivity
             end).
      (* k = P *)
      cbn [step_uinst negb app checked_insts].
      destruct (checked_inst_rest_unchecked_let d P o args s rest live ltac:(assumption)) as [live' Hstep].
      * intros _. repeat split; intro Eo; subst o.
        -- destruct args as [|p [|x [|]]]; cbn in *; try discriminate;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end; discriminate.
        -- destruct args as [|p [|x [|]]]; cbn in *; try discriminate;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end; discriminate.
        -- destruct args as [|x [|]]; cbn in *; try discriminate;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end; discriminate.
        -- destruct args as [|[x | c | g] [|]]; cbn in *; try discriminate; exact I.
      * rewrite Hstep. exists live'. reflexivity.
    + destruct cl; [discriminate | cbn in *; discriminate | eexists; cbn [step_uinst negb app checked_insts checked_inst_rest raw_access]; reflexivity].
    + eexists; cbn [step_uinst negb app checked_insts checked_inst_rest raw_access]; reflexivity.
    + eexists; cbn [step_uinst negb app checked_insts checked_inst_rest raw_access]; reflexivity.
Qed.

(** Every core instruction expands to a non-empty list under
    [step_core_inst]. *)
Lemma step_core_inst_nonempty : forall q i, (1 <= length (step_core_inst q i))%nat.
Proof.
  intros q [d k o args | | | | r cl args | | | |]; simpl; try lia.
  - destruct k; try (simpl; lia).
    destruct o; try (simpl; lia);
      destruct args as [|a1 [|a2 [|]]]; try (simpl; lia);
      destruct a1; simpl; lia.
  - destruct cl; simpl; lia.
Qed.

(** Every valid unchecked instruction produces a non-empty checked
    instruction list under [step_uinst]. *)
Lemma step_uinst_nonempty : forall filc umd classes ui q,
  uvalid_inst filc umd classes ui = true ->
  (1 <= length (step_uinst filc q ui))%nat.
Proof.
  intros [] umd classes ui q Hv.
  - destruct ui as [i | | d k lt a | | | | w v a | | | | d k lt x off | | w v x off];
      cbn [step_uinst negb length]; try lia.
    + exact (step_core_inst_nonempty q i).
    + destruct (access_size_align (XLoad lt)); simpl; lia.
    + destruct (access_size_align (XWidth w)); simpl; lia.
    + destruct (access_size_align (XLoad lt)); simpl; lia.
    + destruct (access_size_align (XWidth w)); simpl; lia.
  - destruct ui; cbn [uvalid_inst negb] in Hv; try discriminate Hv. simpl. lia.
Qed.

(** Applying [step_uinst] across a sequence of valid unchecked
    instructions always produces an instruction list accepted by
    [checked_insts] with fuel at least the number of original
    instructions, from any incoming live facts. *)
Lemma step_uinsts_checked_insts : forall filc umd classes qs_uis s fuel live,
  Forall (fun qui => uvalid_inst filc umd classes (snd qui) = true) qs_uis ->
  (length qs_uis <= fuel)%nat ->
  let insts := flat_map (fun qui => step_uinst filc (fst qui) (snd qui)) qs_uis in
  exists out, checked_insts s fuel insts live = Some out.
Proof.
  intros filc umd classes qs_uis s.
  induction qs_uis as [|[q ui] rest IH]; intros fuel live Hval Hfuel.
  - simpl. exists live. destruct fuel; reflexivity.
  - inversion Hval as [|? ? Hv Hrest]; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel. cbn [flat_map fst snd].
    destruct (step_uinst_checked_insts filc umd classes ui q s fuel'
                (flat_map (fun qui => step_uinst filc (fst qui) (snd qui)) rest) live Hv)
      as [live' Heq].
    rewrite Heq.
    apply IH; [exact Hrest | lia].
Qed.

(** Every valid sequence of expanded instructions has at least as many
    checked instructions as original unchecked instructions. *)
Lemma step_uinsts_length_ge : forall filc umd classes qs_uis,
  Forall (fun qui => uvalid_inst filc umd classes (snd qui) = true) qs_uis ->
  (length qs_uis <= length (flat_map (fun qui => step_uinst filc (fst qui) (snd qui)) qs_uis))%nat.
Proof.
  intros filc umd classes qs_uis.
  induction qs_uis as [|[q ui] rest IH]; intros Hval; [simpl; lia|].
  inversion Hval as [|? ? Hv Hrest]; subst.
  simpl. rewrite length_app.
  pose proof (step_uinst_nonempty filc umd classes ui q Hv).
  pose proof (IH Hrest). lia.
Qed.

(** When every block of a checked function f' is obtained by expanding
    valid unchecked instructions via [step_uinst], [Validate.evidence_pass]
    succeeds for any precomputed reuse table [s]. *)
Theorem piz_func_evidence_pass : forall filc umd classes f' s,
  Forall (fun b =>
            exists qs_uis,
              Forall (fun qui => uvalid_inst filc umd classes (snd qui) = true) qs_uis /\
              b_insts b = flat_map (fun qui => step_uinst filc (fst qui) (snd qui)) qs_uis)
         (fn_blocks f') ->
  evidence_pass s f' = true.
Proof.
  intros filc umd classes f' s Hbs.
  unfold evidence_pass.
  match goal with
  | |- match fold_left ?F (fn_blocks f') (Some []) with _ => _ end = true =>
      assert (Hfold : forall bs acc,
        Forall (fun b =>
                  exists qs_uis,
                    Forall (fun qui => uvalid_inst filc umd classes (snd qui) = true) qs_uis /\
                    b_insts b = flat_map (fun qui => step_uinst filc (fst qui) (snd qui)) qs_uis) bs ->
        exists res, fold_left F bs (Some acc) = Some res)
  end.
  { induction bs as [|b bs IH]; intros acc H; [exists acc; reflexivity|].
    inversion H as [|? ? Hb Hrest]; subst.
    destruct Hb as (qs_uis & Hval & Hbi).
    cbn [fold_left].
    set (live1 := fold_left _ (b_phis b) _).
    pose proof (step_uinsts_length_ge filc umd classes qs_uis Hval) as Hlen.
    destruct (step_uinsts_checked_insts filc umd classes qs_uis s (S (length (b_insts b))) live1 Hval
                ltac:(rewrite Hbi; lia)) as [out Hchk].
    rewrite <- Hbi in Hchk. rewrite Hchk.
    apply IH. exact Hrest. }
  destruct (Hfold (fn_blocks f') [] Hbs) as [res Hres].
  rewrite Hres. reflexivity.
Qed.

(** No instruction emitted by [step_uinst] for a valid unchecked
    instruction is a [Limit] instruction. *)
Lemma step_uinst_no_limit : forall filc umd classes ui q i,
  uvalid_inst filc umd classes ui = true ->
  In i (step_uinst filc q ui) ->
  match i with Let _ _ (Limit _) _ => False | _ => True end.
Proof.
  intros [] umd classes ui q i Hv Hin.
  - destruct ui as [i0 | | d k lt a | | | | w v a | | | | d k lt x off | | w v x off];
      cbn [step_uinst uvalid_inst negb] in *.
    + apply andb_true_iff in Hv as [Hnc _]. apply negb_true_iff in Hnc.
      destruct i0 as [d k o args | | | | r cl args | | | |]; simpl in *; try discriminate Hnc.
      * destruct k.
        all: try (destruct Hin as [<- | []]; destruct o; simpl in Hnc; try discriminate Hnc; exact I).
        destruct o; simpl in Hnc; try discriminate Hnc;
          try (destruct Hin as [<- | []]; exact I);
          try (destruct args as [|a1 [|a2 [|]]]; try (destruct Hin as [<- | []]; exact I);
               destruct a1; destruct Hin as [<- | []]; exact I).
      * destruct cl; [destruct Hin as [<- | [<- | []]] | destruct Hin as [<- | []] | destruct Hin as [<- | []]]; exact I.
      * destruct Hin as [<- | []]; exact I.
      * destruct Hin as [<- | []]; exact I.
    + destruct Hin as [<- | [<- | []]]; exact I.
    + destruct (access_size_align (XLoad lt)); destruct Hin as [<- | [<- | []]]; exact I.
    + destruct Hin as [<- | [<- | []]]; exact I.
    + destruct Hin as [<- | [<- | []]]; exact I.
    + destruct Hin as [<- | [<- | []]]; exact I.
    + destruct (access_size_align (XWidth w)); destruct Hin as [<- | [<- | []]]; exact I.
    + destruct Hin as [<- | [<- | []]]; exact I.
    + destruct Hin as [<- | [<- | []]]; exact I.
    + destruct Hin as [<- | [<- | []]]; exact I.
    + destruct (access_size_align (XLoad lt)); destruct Hin as [<- | [<- | []]]; exact I.
    + destruct Hin as [<- | [<- | []]]; exact I.
    + destruct (access_size_align (XWidth w)); destruct Hin as [<- | [<- | []]]; exact I.
  - destruct ui; cbn [uvalid_inst negb] in Hv; try discriminate Hv.
    repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
    match goal with H : negb (checked_inst _) = true |- _ => apply negb_true_iff in H end.
    simpl in Hin. destruct Hin as [<- | []].
    destruct i0 as [d k o args | | | | | | | |]; simpl in *; try exact I.
    destruct o; simpl in *; try exact I; discriminate.
Qed.

(** Consequently, any function built from [step_uinst] expansions has
    no [Limit] instructions and passes [Validate.limit_reads]. *)
Theorem piz_func_limit_reads : forall filc umd classes f',
  Forall (fun b =>
            exists qs_uis,
              Forall (fun qui => uvalid_inst filc umd classes (snd qui) = true) qs_uis /\
              b_insts b = flat_map (fun qui => step_uinst filc (fst qui) (snd qui)) qs_uis)
         (fn_blocks f') ->
  limit_reads f' = true.
Proof.
  intros filc umd classes f' Hbs.
  unfold limit_reads.
  assert (Hempty :
    flat_map (fun b => flat_map (fun i => match i with Let n _ (Limit _) _ => [n] | _ => [] end)
                                (b_insts b)) (fn_blocks f') = []).
  { induction (fn_blocks f') as [|b bs IH]; [reflexivity|].
    inversion Hbs as [|? ? Hb Hrest]; subst.
    simpl. rewrite IH by exact Hrest. rewrite app_nil_r.
    destruct Hb as (qs_uis & Hval & Hbi). rewrite Hbi.
    clear IH Hrest Hbi Hbs.
    induction qs_uis as [|[q ui] rest IHq]; [reflexivity|].
    inversion Hval as [|? ? Hv Hr]; subst.
    simpl. rewrite flat_map_app, IHq by exact Hr. rewrite app_nil_r.
    assert (H1 : flat_map (fun i => match i with Let n _ (Limit _) _ => [n] | _ => [] end)
                          (step_uinst filc q ui) = []).
    { pose proof (step_uinst_no_limit filc umd classes ui q) as Hnl.
      induction (step_uinst filc q ui) as [|i0 is IHi]; [reflexivity|].
      simpl.
      pose proof (Hnl i0 Hv (or_introl eq_refl)) as H0.
      destruct i0 as [d k o args | | | | | | | |];
        try (destruct o; try contradiction); simpl;
        apply IHi; intros i1 Hvi Hin; exact (Hnl i1 Hvi (or_intror Hin)). }
    rewrite H1. reflexivity. }
  rewrite Hempty. reflexivity.
Qed.

(** ## Typing of expanded instructions

    Every checked instruction emitted by [step_uinst] reads only
    operands that were valid in the unchecked instruction plus, for a
    two-instruction access pair, the fresh proof temporary of class [A]
    or [F] defined by its own check. This section proves that
    [Validate.valid_inst] holds for every emitted instruction whenever
    the checked class table preserves all original definitions and
    assigns the fresh proof temporary its expected class. *)

(** Two temporary-class tables agree on all uses that succeed in the
    first table whenever every binding of the first table is preserved
    by the second. *)
Lemma valid_use_mono : forall defs1 defs2 k v,
  (forall n k0, lookup n defs1 = Some k0 -> lookup n defs2 = Some k0) ->
  valid_use defs1 k v = true ->
  valid_use defs2 k v = true.
Proof.
  intros defs1 defs2 k [n | c | g] Hext Hv; simpl in *; [| exact Hv | exact Hv].
  destruct (lookup n defs1) as [k0|] eqn:El; [|discriminate Hv].
  rewrite (Hext n k0 El). exact Hv.
Qed.

(** Helper factoring the uniform argument-typing check of `Let`
    instructions across all classes and operations. *)
Lemma valid_let_body_mono : forall defs1 defs2 k o args,
  (forall n k0, lookup n defs1 = Some k0 -> lookup n defs2 = Some k0) ->
  (valid_op o && op_result_ok o k &&
   match o, args with
   | VaArgs, [Const off] => 0 <=? off
   | VaArgs, _ => false
   | Setjmp SjSig, _ => true
   | Setjmp _, [_; Const Z0] => true
   | Setjmp _, _ => false
   | _, _ => true
   end &&
   match op_arg_classes o k with
   | Some cs => (length cs =? length args)%nat
                && forallb (fun ca => valid_use defs1 (fst ca) (snd ca)) (combine cs args)
   | None => false
   end) = true ->
  (valid_op o && op_result_ok o k &&
   match o, args with
   | VaArgs, [Const off] => 0 <=? off
   | VaArgs, _ => false
   | Setjmp SjSig, _ => true
   | Setjmp _, [_; Const Z0] => true
   | Setjmp _, _ => false
   | _, _ => true
   end &&
   match op_arg_classes o k with
   | Some cs => (length cs =? length args)%nat
                && forallb (fun ca => valid_use defs2 (fst ca) (snd ca)) (combine cs args)
   | None => false
   end) = true.
Proof.
  intros defs1 defs2 k o args Hext Hv.
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
  apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split; assumption | assumption]|].
  destruct (op_arg_classes o k) as [cs|]; [|discriminate].
  apply andb_true_iff in H0 as [Hlen Hfa].
  apply andb_true_iff; split; [exact Hlen|].
  rewrite forallb_forall in *; intros ca Hin.
  exact (valid_use_mono _ _ _ _ Hext (Hfa ca Hin)).
Qed.

(** Updating the module context and class table preserves [valid_inst]
    when [func_sig], [init_entry_named], and every class lookup in
    [defs1] are preserved. *)
Lemma valid_inst_mono : forall md1 md2 defs1 defs2 i,
  (forall n, func_sig n md2 = func_sig n md1) ->
  (forall s, init_entry_named md2 s = init_entry_named md1 s) ->
  (forall n k0, lookup n defs1 = Some k0 -> lookup n defs2 = Some k0) ->
  valid_inst md1 defs1 i = true ->
  valid_inst md2 defs2 i = true.
Proof.
  intros md1 md2 defs1 defs2 i Hsig Hinit Hext Hv.
  destruct i as [d k o args | d o args lw | w off v a | off v a es
                 | r cl args | r cl args | x sz | fn ln | q]; cbn [valid_inst] in *.
  - (* Let *)
    destruct k; try (exact (valid_let_body_mono defs1 defs2 _ o args Hext Hv)).
    destruct o; try (exact (valid_let_body_mono defs1 defs2 P _ args Hext Hv)).
    destruct args as [|[x | c | g] [|]];
      try (exact (valid_let_body_mono defs1 defs2 P Copy _ Hext Hv)).
    rewrite Hinit. exact Hv.
  - (* Flight *)
    repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
    apply andb_true_iff; split; [apply andb_true_iff; split; [assumption|]|].
    + rewrite forallb_forall in *; intros fa Hin.
      specialize (H1 fa Hin). destruct fa; exact (valid_use_mono _ _ _ _ Hext H1).
    + destruct lw; [reflexivity | exact (valid_use_mono _ _ _ _ Hext H0)].
  - (* RawStore *)
    destruct (width_value_ok w) as [k|]; [|discriminate Hv].
    apply andb_true_iff in Hv as [H1 H2].
    apply andb_true_iff; split; [exact (valid_use_mono _ _ _ _ Hext H1) | exact (valid_use_mono _ _ _ _ Hext H2)].
  - (* RawStorePointer *)
    repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
    apply andb_true_iff; split; [apply andb_true_iff; split; [assumption |]|].
    + exact (valid_use_mono _ _ _ _ Hext H1).
    + exact (valid_use_mono _ _ _ _ Hext H0).
  - (* Call *)
    destruct cl as [n | c | g].
    + apply andb_true_iff in Hv as [H1 H2].
      apply andb_true_iff; split; [exact (valid_use_mono _ _ _ _ Hext H1)|].
      rewrite forallb_forall in *; intros a Hin.
      exact (valid_use_mono _ _ _ _ Hext (H2 a Hin)).
    + discriminate Hv.
    + repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
      rewrite Hinit, Hsig.
      apply andb_true_iff; split; [apply andb_true_iff; split; [assumption | assumption]|].
      rewrite forallb_forall in *; intros a Hin.
      exact (valid_use_mono _ _ _ _ Hext (H0 a Hin)).
  - (* RawCall *)
    apply andb_true_iff in Hv as [H1 H2].
    apply andb_true_iff; split; [exact (valid_use_mono _ _ _ _ Hext H1)|].
    rewrite forallb_forall in *; intros a Hin.
    exact (valid_use_mono _ _ _ _ Hext (H2 a Hin)).
  - exact Hv.
  - exact Hv.
  - exact (valid_use_mono _ _ _ _ Hext Hv).
Qed.

(** Given an unchecked instruction ui, [uinst_proof_class] returns the
    class ([A] or [F]) of the fresh proof temporary created for ui when
    `uinst_is_access ui = true`. *)
Definition uinst_proof_class (ui : uinst) : class :=
  match ui with
  | UCore (Call _ (Tmp _) _) => F
  | _ => A
  end.

(** Every checked instruction emitted by [step_uinst] passes
    [Validate.valid_inst] in any target module and class table that
    preserve signatures, init entries, original temporary classes, and
    the fresh proof temporary's class. *)
Theorem step_uinst_valid_inst : forall filc umd md' defs defs' ui q,
  (forall n, func_sig n md' = func_sig n (uskel_module umd)) ->
  (forall s, init_entry_named md' s = init_entry_named (uskel_module umd) s) ->
  (forall n k0, lookup n defs = Some k0 -> lookup n defs' = Some k0) ->
  (filc = true -> uinst_is_access ui = true -> lookup q defs' = Some (uinst_proof_class ui)) ->
  uvalid_inst filc umd defs ui = true ->
  forallb (valid_inst md' defs') (step_uinst filc q ui) = true.
Proof.
  intros filc umd md' defs defs' ui q Hsig Hinit Hext Hq Hv.
  destruct filc.
  - (* filc = true *)
    destruct ui as [i | d a | d k lt a | d a | d k ct e n a | v a | w v a | v a | r a sz al
                    | d x off | d k lt x off | v x off | w v x off];
      cbn [step_uinst uvalid_inst negb] in *.
    + (* UCore i *)
      apply andb_true_iff in Hv as [Hnc Hvi].
      apply negb_true_iff in Hnc.
      destruct i as [d k o args | d o args lw | w off v a | off v a es
                     | r cl args | r cl args | x sz | fn ln | tq];
        simpl in Hnc; try discriminate Hnc.
      * (* Let *)
        destruct k.
        all: try (cbn [step_core_inst forallb]; rewrite andb_true_r;
                  exact (valid_inst_mono _ _ _ _ _ Hsig Hinit Hext Hvi)).
        (* k = P *)
        destruct o; try discriminate Hnc;
          try (cbn [step_core_inst forallb]; rewrite andb_true_r;
               exact (valid_inst_mono _ _ _ _ _ Hsig Hinit Hext Hvi)).
        -- (* Add *)
           destruct args as [|p [|x [|]]];
             cbn [valid_inst op_arg_classes valid_op op_result_ok any_class proof_class length Nat.eqb combine forallb fst snd] in Hvi;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
             try discriminate.
           cbn [step_core_inst forallb valid_inst].
           repeat match goal with Hu : valid_use defs _ _ = true |- _ => rewrite (valid_use_mono _ _ _ _ Hext Hu) end.
           reflexivity.
        -- (* Sub *)
           destruct args as [|p [|x [|]]];
             cbn [valid_inst op_arg_classes valid_op op_result_ok any_class proof_class length Nat.eqb combine forallb fst snd] in Hvi;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
             try discriminate.
           cbn [step_core_inst forallb valid_inst].
           repeat match goal with Hu : valid_use defs _ _ = true |- _ => rewrite (valid_use_mono _ _ _ _ Hext Hu) end.
           reflexivity.
        -- (* Copy *)
           destruct args as [|v [|]].
           ++ cbn [valid_inst op_arg_classes valid_op op_result_ok any_class proof_class length Nat.eqb combine forallb fst snd] in Hvi;
              repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end; discriminate.
           ++ destruct v as [x | c | g];
                cbn [valid_inst op_arg_classes valid_op op_result_ok any_class proof_class length Nat.eqb combine forallb fst snd] in Hvi.
              ** repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
                 cbn [step_core_inst forallb valid_inst].
                 repeat match goal with Hu : valid_use defs _ _ = true |- _ => rewrite (valid_use_mono _ _ _ _ Hext Hu) end.
                 reflexivity.
              ** repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
                 reflexivity.
              ** cbn [step_core_inst forallb valid_inst]. rewrite Hinit, Hvi. reflexivity.
           ++ destruct v; cbn [valid_inst op_arg_classes valid_op op_result_ok any_class proof_class length Nat.eqb combine forallb fst snd] in Hvi;
              repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end; discriminate.
        -- (* Itop *)
           destruct args as [|x [|]];
             cbn [valid_inst op_arg_classes valid_op op_result_ok any_class proof_class length Nat.eqb combine forallb fst snd] in Hvi;
             repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
             try discriminate.
           cbn [step_core_inst forallb valid_inst].
           repeat match goal with Hu : valid_use defs _ _ = true |- _ => rewrite (valid_use_mono _ _ _ _ Hext Hu) end.
           reflexivity.
      * (* Call *)
        destruct cl as [p | c | g].
        -- cbn [valid_inst] in Hvi. apply andb_true_iff in Hvi as [Hp Hargs].
           specialize (Hq eq_refl eq_refl). simpl in Hq.
           cbn [step_core_inst forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
           rewrite (valid_use_mono _ _ _ _ Hext Hp).
           cbn [valid_use andb]. rewrite Hq. simpl. rewrite andb_true_r.
           rewrite forallb_forall in *; intros a Hin.
           exact (valid_use_mono _ _ _ _ Hext (Hargs a Hin)).
        -- simpl in Hvi. discriminate Hvi.
        -- cbn [step_core_inst forallb]. rewrite andb_true_r.
           exact (valid_inst_mono _ _ _ _ _ Hsig Hinit Hext Hvi).
      * cbn [step_core_inst forallb]. rewrite andb_true_r. exact (valid_inst_mono _ _ _ _ _ Hsig Hinit Hext Hvi).
      * cbn [step_core_inst forallb]. rewrite andb_true_r. exact (valid_inst_mono _ _ _ _ _ Hsig Hinit Hext Hvi).
    + (* ULoadPtr *)
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      rewrite (valid_use_mono _ _ _ _ Hext Hv), effects_eqb_refl.
      cbn [valid_use]. rewrite Hq. reflexivity.
    + (* ULoad *)
      apply andb_true_iff in Hv as [Hres Ha].
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      pose proof (load_size_align_ok lt) as Hsa.
      destruct (access_size_align (XLoad lt)) as [sz al].
      destruct Hsa as (Hsz & _ & Hal & _).
      cbn [forallb valid_inst valid_op op_arg_classes combine fst snd length Nat.eqb].
      unfold check_ok.
      assert (Hlt : (0 <? sz) = true) by (apply Z.ltb_lt; lia).
      rewrite Hlt, Hal, (valid_use_mono _ _ _ _ Hext Ha), Hres.
      cbn [valid_use]. rewrite Hq. destruct k; reflexivity.
    + (* UAtomicLoadPtr *)
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      rewrite (valid_use_mono _ _ _ _ Hext Hv), effects_eqb_refl, orb_true_r.
      cbn [valid_use]. rewrite Hq. reflexivity.
    + (* UCas *)
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      pose proof (cas_size_ok ct) as (Hsz & Hal & _).
      cbn [forallb valid_inst valid_op op_arg_classes combine fst snd length Nat.eqb].
      unfold check_ok.
      assert (Hlt : (0 <? Syntax.cas_bytes ct) = true) by (apply Z.ltb_lt; lia).
      rewrite Hlt, Hal.
      repeat match goal with
             | Hr : op_result_ok _ _ = true |- _ => rewrite Hr
             | Hu : valid_use defs _ _ = true |- _ => rewrite (valid_use_mono _ _ _ _ Hext Hu)
             end.
      cbn [valid_use]. rewrite Hq. destruct k; reflexivity.
    + (* UStorePtr *)
      apply andb_true_iff in Hv as [Hv' Ha].
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      rewrite (valid_use_mono _ _ _ _ Hext Ha), (valid_use_mono _ _ _ _ Hext Hv'), effects_eqb_refl.
      cbn [valid_use]. rewrite Hq. reflexivity.
    + (* UStore *)
      destruct (width_value_ok w) as [kw|] eqn:Ew; [|discriminate Hv].
      assert (Hw : w <> Wp) by (intro E; subst w; discriminate Ew).
      apply andb_true_iff in Hv as [Hv' Ha].
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      pose proof (width_size_align_ok w Hw) as Hsa.
      destruct (access_size_align (XWidth w)) as [sz al].
      destruct Hsa as (Hsz & _ & Hal & _).
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      unfold check_ok.
      assert (Hlt : (0 <? sz) = true) by (apply Z.ltb_lt; lia).
      rewrite Hlt, Hal, Ew, (valid_use_mono _ _ _ _ Hext Ha), (valid_use_mono _ _ _ _ Hext Hv').
      cbn [valid_use]. rewrite Hq. reflexivity.
    + (* UAtomicStorePtr *)
      apply andb_true_iff in Hv as [Hv' Ha].
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      rewrite (valid_use_mono _ _ _ _ Hext Ha), (valid_use_mono _ _ _ _ Hext Hv'), effects_eqb_refl, orb_true_r.
      cbn [valid_use]. rewrite Hq. reflexivity.
    + (* UAccess *)
      apply andb_true_iff in Hv as [Hchk Ha].
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      rewrite Hchk, (valid_use_mono _ _ _ _ Hext Ha).
      cbn [valid_use]. rewrite Hq. reflexivity.
    + (* ULocalLoadPtr *)
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      rewrite Hv, effects_eqb_refl, orb_true_r.
      cbn [valid_use]. rewrite Hq. reflexivity.
    + (* ULocalLoad *)
      apply andb_true_iff in Hv as [Hres Hoff].
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      pose proof (load_size_align_ok lt) as Hsa.
      destruct (access_size_align (XLoad lt)) as [sz al].
      destruct Hsa as (Hsz & Hhi & Hal & _).
      cbn [forallb valid_inst valid_op op_arg_classes combine fst snd length Nat.eqb].
      assert (Hlt : (0 <? sz) = true) by (apply Z.ltb_lt; lia).
      assert (Hle : (sz <=? 2 ^ 31 - 1) = true) by (apply Z.leb_le; lia).
      rewrite Hoff, Hlt, Hle, Hal, Hres.
      cbn [valid_use]. rewrite Hq. destruct k; reflexivity.
    + (* ULocalStorePtr *)
      apply andb_true_iff in Hv as [Hv' Hoff].
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      rewrite Hoff, (valid_use_mono _ _ _ _ Hext Hv'), effects_eqb_refl, orb_true_r.
      cbn [valid_use]. rewrite Hq. reflexivity.
    + (* ULocalStore *)
      destruct (width_value_ok w) as [kw|] eqn:Ew; [|discriminate Hv].
      assert (Hw : w <> Wp) by (intro E; subst w; discriminate Ew).
      apply andb_true_iff in Hv as [Hv' Hoff].
      specialize (Hq eq_refl eq_refl). simpl in Hq.
      pose proof (width_size_align_ok w Hw) as Hsa.
      destruct (access_size_align (XWidth w)) as [sz al].
      destruct Hsa as (Hsz & Hhi & Hal & _).
      cbn [forallb valid_inst valid_op op_result_ok op_arg_classes combine fst snd length Nat.eqb].
      assert (Hlt : (0 <? sz) = true) by (apply Z.ltb_lt; lia).
      assert (Hle : (sz <=? 2 ^ 31 - 1) = true) by (apply Z.leb_le; lia).
      rewrite Hoff, Hlt, Hle, Hal, Ew, (valid_use_mono _ _ _ _ Hext Hv').
      cbn [valid_use]. rewrite Hq. reflexivity.
  - (* filc = false *)
    destruct ui; cbn [uvalid_inst negb] in Hv; try discriminate Hv.
    repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
    cbn [step_uinst negb forallb]. rewrite andb_true_r.
    match goal with Hvi : valid_inst _ _ _ = true |- _ => exact (valid_inst_mono _ _ _ _ _ Hsig Hinit Hext Hvi) end.
Qed.

(** ## Term-to-syntax simulation of Pizlonate

    The proofs above reason on the typed expansion [step_uinst]. Using
    the canonical term inversion lemmas from
    [NfbTransport](NfbTransport.v), this section bridges back to the
    ground Prolog terms manipulated by [Pizlonate.checked_access] and
    [Pizlonate.flight_inst], proving that every decodable unchecked
    instruction term expands to terms that [Transport.dinst] decodes to
    [step_uinst]. *)

(** Helper lemma matching [Pizlonate.size_align] against
    [Validate.access_size_align] for every decoded [load_type]. *)
Lemma dload_type_size_align : forall ty lt,
  dload_type ty = Some lt ->
  is_atom "p" ty = false /\ Pizlonate.size_align ty = Some (access_size_align (XLoad lt)).
Proof.
  intros ty lt H.
  pose proof (NfbTransport.dload_type_enc ty lt H) as <-.
  destruct lt as [| | | |[| | | | |]]; split; reflexivity.
Qed.

(** Helper lemma matching [Pizlonate.cas_bytes] against
    [Syntax.cas_bytes] for every decoded [cas_type]. *)
Lemma dcas_type_cas_bytes : forall ty ct,
  dcas_type ty = Some ct ->
  Pizlonate.cas_bytes ty = Some (Syntax.cas_bytes ct).
Proof.
  intros ty ct H.
  pose proof (NfbTransport.dcas_type_enc ty ct H) as <-.
  destruct ct as [| |[| | | | |]]; reflexivity.
Qed.

(** Helper lemma matching [Pizlonate.size_align] against
    [Validate.access_size_align] for every decoded non-pointer [width]. *)
Lemma dwidth_size_align : forall w w',
  dwidth w = Some w' ->
  w' <> Wp ->
  is_atom "p" w = false /\ Pizlonate.size_align w = Some (access_size_align (XWidth w')).
Proof.
  intros w w' H Hne.
  pose proof (NfbTransport.dwidth_enc w w' H) as <-.
  destruct w'; try contradiction; split; reflexivity.
Qed.

(** Decoding [Pizlonate.check_inst] yields a [Check] instruction when
    its rights and pointer operand decode. *)
Lemma dinst_check_inst : forall q sz r r' al a a',
  drights r = Some r' ->
  dvalue a = Some a' ->
  dinst (Pizlonate.check_inst q (TInt sz) r (TInt al) a) =
  Some (Let q A (Check 0 sz r' al) [a']).
Proof.
  intros q sz r r' al a a' Hr Ha.
  unfold Pizlonate.check_inst, Pizlonate.tmp, dinst. simpl.
  rewrite Hr, Ha. reflexivity.
Qed.

(** Any term decoded by [duinst_core] decodes via [Transport.dinst] to
    an unchecked core instruction whose exact syntax is [IrTerm.enc_inst i]. *)
Lemma duinst_core_inv : forall t ui,
  duinst_core t = Some ui ->
  exists i, ui = UCore i /\ checked_inst i = false /\ dinst t = Some i /\ IrTerm.enc_inst i = t.
Proof.
  intros t ui H. unfold duinst_core in H.
  destruct (dinst t) as [i|] eqn:Edi; [|discriminate H].
  destruct (checked_inst i) eqn:Eci; [discriminate H|].
  injection H as <-.
  exists i. split; [reflexivity | split; [exact Eci | split; [reflexivity | exact (NfbTransport.dinst_enc t i Edi)]]].
Qed.

(** Every unchecked core instruction [IrTerm.enc_inst i] with
    `checked_inst i = false` and `uinst_is_access (UCore i) = false`
    returns `None` from [Pizlonate.checked_access]. *)
Lemma enc_inst_checked_access_none : forall i,
  checked_inst i = false ->
  uinst_is_access (UCore i) = false ->
  Pizlonate.checked_access (IrTerm.enc_inst i) = None.
Proof.
  intros [d k o args | | | | r cl args | | x sz | fn ln | tq] Hnc Hna;
    simpl in Hnc; try discriminate Hnc; try reflexivity.
  - destruct o; simpl in Hnc; try discriminate Hnc; try reflexivity;
      repeat match goal with
             | x : class |- _ => destruct x
             | x : signedness |- _ => destruct x
             | x : setjmp_kind |- _ => destruct x
             end; reflexivity.
  - destruct cl; simpl in Hna; try discriminate Hna; reflexivity.
Qed.

(** Every unchecked core instruction [IrTerm.enc_inst i] with
    `checked_inst i = false` and `uinst_is_access (UCore i) = false`
    rewrites under [Pizlonate.flight_inst] to a term decoding to
    [step_core_inst q i]. *)
Lemma enc_inst_flight_sim : forall i q,
  checked_inst i = false ->
  uinst_is_access (UCore i) = false ->
  dinst (IrTerm.enc_inst i) = Some i ->
  map_option dinst [match Pizlonate.flight_inst (IrTerm.enc_inst i) with Some j => j | None => IrTerm.enc_inst i end] =
  Some (step_core_inst q i).
Proof.
  intros [d k o args | | | | r cl args | | x sz | fn ln | tq] q Hnc Hna Edi;
    simpl in Hnc; try discriminate Hnc.
  - destruct k;
      try (match goal with
           | |- context [Let d ?k0 o args] =>
               assert (Hfl : Pizlonate.flight_inst (IrTerm.enc_inst (Let d k0 o args)) = None)
                 by (destruct o; try reflexivity;
                     repeat match goal with
                            | x : class |- _ => destruct x
                            | x : signedness |- _ => destruct x
                            | x : setjmp_kind |- _ => destruct x
                            end; reflexivity);
               rewrite Hfl; cbn [step_core_inst map_option]; rewrite Edi; reflexivity
           end).
    (* k = P *)
    destruct o; simpl in Hnc; try discriminate Hnc;
      try (match goal with
           | |- context [Let d P ?o0 args] =>
               assert (Hfl : Pizlonate.flight_inst (IrTerm.enc_inst (Let d P o0 args)) = None)
                 by (try reflexivity;
                     repeat match goal with
                            | x : class |- _ => destruct x
                            | x : signedness |- _ => destruct x
                            | x : setjmp_kind |- _ => destruct x
                            end; reflexivity);
               rewrite Hfl; cbn [step_core_inst map_option]; rewrite Edi; reflexivity
           end).
    + (* Add *)
      destruct args as [|p [|x [|]]];
        try (match goal with
             | |- context [Let d P Add ?a0] =>
                 assert (Hfl : Pizlonate.flight_inst (IrTerm.enc_inst (Let d P Add a0)) = None) by reflexivity;
                 rewrite Hfl; cbn [step_core_inst map_option]; rewrite Edi; reflexivity
             end).
      cbn [IrTerm.enc_inst Pizlonate.flight_inst step_core_inst map map_option dinst dtmp dapp dop dflight_arg dflight_lower].
      destruct x; destruct p; reflexivity.
    + (* Sub *)
      destruct args as [|p [|x [|]]];
        try (match goal with
             | |- context [Let d P Sub ?a0] =>
                 assert (Hfl : Pizlonate.flight_inst (IrTerm.enc_inst (Let d P Sub a0)) = None) by reflexivity;
                 rewrite Hfl; cbn [step_core_inst map_option]; rewrite Edi; reflexivity
             end).
      cbn [IrTerm.enc_inst Pizlonate.flight_inst step_core_inst map map_option dinst dtmp dapp dop dflight_arg dflight_lower].
      destruct x; destruct p; reflexivity.
    + (* Copy *)
      destruct args as [|v [|]].
      * replace (Pizlonate.flight_inst (IrTerm.enc_inst (Let d P Copy []))) with (@None term) by reflexivity.
        cbn [step_core_inst map_option]; rewrite Edi; reflexivity.
      * destruct v as [x | c | g]; [reflexivity | reflexivity | ].
        replace (Pizlonate.flight_inst (IrTerm.enc_inst (Let d P Copy [Global g]))) with (@None term) by reflexivity.
        cbn [step_core_inst map_option]; rewrite Edi; reflexivity.
      * replace (Pizlonate.flight_inst (IrTerm.enc_inst (Let d P Copy (v :: v0 :: l)))) with (@None term) by (destruct v; reflexivity).
        cbn [step_core_inst map_option]; rewrite Edi; destruct v; reflexivity.
    + (* Itop *)
      destruct args as [|x [|]];
        try (match goal with
             | |- context [Let d P Itop ?a0] =>
                 assert (Hfl : Pizlonate.flight_inst (IrTerm.enc_inst (Let d P Itop a0)) = None) by reflexivity;
                 rewrite Hfl; cbn [step_core_inst map_option]; rewrite Edi; reflexivity
             end).
      destruct x; reflexivity.
  - destruct cl; simpl in Hna; try discriminate Hna;
      match goal with
      | |- context [Call r ?c0 args] =>
          assert (Hfl : Pizlonate.flight_inst (IrTerm.enc_inst (Call r c0 args)) = None) by reflexivity;
          rewrite Hfl; cbn [step_core_inst map_option]; rewrite Edi; reflexivity
      end.
  - cbn [step_core_inst map_option]; replace (Pizlonate.flight_inst (IrTerm.enc_inst (LocalAlloc x sz))) with (@None term) by reflexivity;
      rewrite Edi; reflexivity.
  - cbn [step_core_inst map_option]; replace (Pizlonate.flight_inst (IrTerm.enc_inst (Loc fn ln))) with (@None term) by reflexivity;
      rewrite Edi; reflexivity.
Qed.

(** When an unchecked term t decodes to an access [ui] (meaning
    `uinst_is_access ui = true`), [Pizlonate.checked_access] succeeds on
    t and returns a term generator whose output decodes under
    [Transport.dinst] to [step_uinst true q ui]. *)
Theorem duinst_checked_access_sim : forall t ui,
  duinst t = Some ui ->
  uinst_is_access ui = true ->
  exists gen,
    Pizlonate.checked_access t = Some gen /\
    forall q, map_option dinst (gen q) = Some (step_uinst true q ui).
Proof.
  intros t ui Hdu Hacc.
  destruct t as [| |f xs|]; [discriminate Hdu | discriminate Hdu | | discriminate Hdu].
  unfold duinst in Hdu.
  destruct (f == "let") eqn:Ef_let.
  - apply String.eqb_eq in Ef_let; subst f.
    destruct xs as [|d [|k [|o [|args [|]]]]];
      try (cbn iota in Hdu; destruct (duinst_core_inv _ _ Hdu) as (i & Hui & Hnc & Edi & Henc); subst ui;
           destruct i as [ | | | | r cl args0 | | | | ]; simpl in Hacc; try discriminate Hacc;
           cbn [IrTerm.enc_inst] in Henc; discriminate Henc).
    destruct o as [| |of_ oxs|];
      try (cbn iota in Hdu; destruct (duinst_core_inv _ _ Hdu) as (i & Hui & Hnc & Edi & Henc); subst ui;
           destruct i as [ | | | | r cl args0 | | | | ]; simpl in Hacc; try discriminate Hacc;
           cbn [IrTerm.enc_inst] in Henc; discriminate Henc).
    destruct oxs as [|ty [|]];
      try (cbn iota in Hdu; destruct (duinst_core_inv _ _ Hdu) as (i & Hui & Hnc & Edi & Henc); subst ui;
           destruct i as [ | | | | r cl args0 | | | | ]; simpl in Hacc; try discriminate Hacc;
           cbn [IrTerm.enc_inst] in Henc; discriminate Henc).
    destruct args as [| | |l];
      try (cbn iota in Hdu; destruct (duinst_core_inv _ _ Hdu) as (i & Hui & Hnc & Edi & Henc); subst ui;
           destruct i as [ | | | | r cl args0 | | | | ]; simpl in Hacc; try discriminate Hacc;
           cbn [IrTerm.enc_inst] in Henc; discriminate Henc).
    destruct (of_ == "load") eqn:Eo1.
    + apply String.eqb_eq in Eo1; subst of_.
      destruct l as [|a [|]]; try discriminate Hdu.
      destruct (is_atom "p" k && is_atom "p" ty) eqn:Eptr.
      * destruct (dtmp d) as [d'|] eqn:Ed; [|discriminate Hdu].
        destruct (dvalue a) as [a'|] eqn:Ea; [|discriminate Hdu].
        injection Hdu as <-.
        eexists; split.
        -- unfold Pizlonate.checked_access. simpl. rewrite Eptr. reflexivity.
        -- intro q. simpl. unfold Pizlonate.check_sized, Pizlonate.check_inst,
             Pizlonate.raw_load_pointer, Pizlonate.load_effects, Pizlonate.effects, Pizlonate.tmp.
           simpl. rewrite Ea, Ed. reflexivity.
      * destruct (dtmp d) as [d'|] eqn:Ed; [|discriminate Hdu].
        destruct (dclass k) as [k'|] eqn:Ek; [|discriminate Hdu].
        destruct (dload_type ty) as [lt|] eqn:Elt; [|discriminate Hdu].
        destruct (dvalue a) as [a'|] eqn:Ea; [|discriminate Hdu].
        injection Hdu as <-.
        destruct (dload_type_size_align ty lt Elt) as [_ Hsa].
        destruct (access_size_align (XLoad lt)) as [sz al] eqn:Esa.
        eexists; split.
        -- unfold Pizlonate.checked_access. simpl. rewrite Eptr, Hsa. reflexivity.
        -- intro q. cbn [step_uinst negb]. rewrite Esa.
           unfold Pizlonate.check_sized, Pizlonate.check_inst, Pizlonate.raw_load, Pizlonate.tmp.
           simpl. rewrite Ea, Ed, Ek, Elt. reflexivity.
    + destruct (of_ == "atomic_load") eqn:Eo2.
      * apply String.eqb_eq in Eo2; subst of_.
        destruct l as [|a [|]]; try discriminate Hdu.
        destruct (is_atom "p" k && is_atom "p" ty) eqn:Eptr; [|discriminate Hdu].
        destruct (dtmp d) as [d'|] eqn:Ed; [|discriminate Hdu].
        destruct (dvalue a) as [a'|] eqn:Ea; [|discriminate Hdu].
        injection Hdu as <-.
        eexists; split.
        -- unfold Pizlonate.checked_access. simpl. rewrite Eptr. reflexivity.
        -- intro q. simpl. unfold Pizlonate.check_sized, Pizlonate.check_inst,
             Pizlonate.raw_load_pointer, Pizlonate.effects, Pizlonate.tmp.
           simpl. rewrite Ea, Ed. reflexivity.
      * destruct (of_ == "cas") eqn:Eo3.
        -- apply String.eqb_eq in Eo3; subst of_.
           destruct l as [|e [|n [|a [|]]]]; try discriminate Hdu.
           destruct (dtmp d) as [d'|] eqn:Ed; [|discriminate Hdu].
           destruct (dclass k) as [k'|] eqn:Ek; [|discriminate Hdu].
           destruct (dcas_type ty) as [ct|] eqn:Ect; [|discriminate Hdu].
           destruct (dvalue e) as [e'|] eqn:Ee; [|discriminate Hdu].
           destruct (dvalue n) as [n'|] eqn:En; [|discriminate Hdu].
           destruct (dvalue a) as [a'|] eqn:Ea; [|discriminate Hdu].
           injection Hdu as <-.
           pose proof (dcas_type_cas_bytes ty ct Ect) as Hcb.
           eexists; split.
           ++ unfold Pizlonate.checked_access. simpl. rewrite Hcb. reflexivity.
           ++ intro q. simpl. unfold Pizlonate.check_sized, Pizlonate.check_inst, Pizlonate.tmp.
              simpl. rewrite Ea, Ed, Ek, Ect, Ee, En. reflexivity.
        -- destruct (duinst_core_inv _ _ Hdu) as (i & Hui & Hnc & Edi & Henc); subst ui.
           destruct i as [ | | | | r cl args0 | | | | ]; simpl in Hacc; try discriminate Hacc;
             cbn [IrTerm.enc_inst] in Henc; discriminate Henc.
  - destruct (f == "store") eqn:Ef_store.
    + apply String.eqb_eq in Ef_store; subst f.
      destruct xs as [|w [|v [|a [|]]]]; try discriminate Hdu.
      destruct (is_atom "p" w) eqn:Epw.
      * destruct (dvalue v) as [v'|] eqn:Ev; [|discriminate Hdu].
        destruct (dvalue a) as [a'|] eqn:Ea; [|discriminate Hdu].
        injection Hdu as <-.
        eexists; split.
        -- unfold Pizlonate.checked_access. simpl. rewrite Epw. reflexivity.
        -- intro q. simpl. unfold Pizlonate.check_sized, Pizlonate.check_inst,
             Pizlonate.raw_store_pointer, Pizlonate.store_effects, Pizlonate.effects, Pizlonate.tmp.
           simpl. rewrite Ea, Ev. reflexivity.
      * destruct (dwidth w) as [w'|] eqn:Ew; [|discriminate Hdu].
        destruct w'; try discriminate Hdu;
          destruct (dvalue v) as [v'|] eqn:Ev; try discriminate Hdu;
          destruct (dvalue a) as [a'|] eqn:Ea; try discriminate Hdu;
          injection Hdu as <-;
          destruct (dwidth_size_align w _ Ew ltac:(discriminate)) as [_ Hsa];
          eexists; (split;
            [unfold Pizlonate.checked_access; simpl; rewrite Epw, Hsa; reflexivity
            | intro q; simpl; unfold Pizlonate.check_sized, Pizlonate.check_inst,
                Pizlonate.raw_store, Pizlonate.tmp; simpl; rewrite Ea, Ew, Ev; reflexivity]).
    + destruct (f == "atomic_store") eqn:Ef_astore.
      * apply String.eqb_eq in Ef_astore; subst f.
        destruct xs as [|w [|v [|a [|]]]]; try discriminate Hdu.
        destruct (is_atom "p" w) eqn:Epw; [|discriminate Hdu].
        destruct (dvalue v) as [v'|] eqn:Ev; [|discriminate Hdu].
        destruct (dvalue a) as [a'|] eqn:Ea; [|discriminate Hdu].
        injection Hdu as <-.
        eexists; split.
        -- unfold Pizlonate.checked_access. simpl. rewrite Epw. reflexivity.
        -- intro q. simpl. unfold Pizlonate.check_sized, Pizlonate.check_inst,
             Pizlonate.raw_store_pointer, Pizlonate.effects, Pizlonate.tmp.
           simpl. rewrite Ea, Ev. reflexivity.
      * destruct (f == "access") eqn:Ef_acc.
        -- apply String.eqb_eq in Ef_acc; subst f.
           destruct xs as [|r [|a [|[sz| | |][|[al| | |][|]]]]]; try discriminate Hdu.
           destruct (drights r) as [r'|] eqn:Er; [|discriminate Hdu].
           destruct (dvalue a) as [a'|] eqn:Ea; [|discriminate Hdu].
           injection Hdu as <-.
           eexists; split.
           ++ unfold Pizlonate.checked_access. simpl. reflexivity.
           ++ intro q. cbn [map_option step_uinst negb]. rewrite (dinst_check_inst q sz r r' al a a' Er Ea). reflexivity.
        -- destruct (f == "local_load") eqn:Ef_ll.
           ++ apply String.eqb_eq in Ef_ll; subst f.
              destruct xs as [|d [|k [|ty [|x [|[off| | |][|]]]]]]; try discriminate Hdu.
              destruct (is_atom "p" ty) eqn:Epty.
              ** destruct (is_atom "p" k) eqn:Epk; [|discriminate Hdu].
                 destruct (dtmp d) as [d'|] eqn:Ed; [|discriminate Hdu].
                 injection Hdu as <-.
                 destruct ty as [|ta| |]; unfold is_atom in Epty; try discriminate Epty.
                 apply String.eqb_eq in Epty; subst ta.
                 eexists; split.
                 --- unfold Pizlonate.checked_access. simpl. reflexivity.
                 --- intro q. simpl. unfold Pizlonate.check_local_inst, Pizlonate.raw_load_pointer,
                       Pizlonate.local_load_effects, Pizlonate.effects, Pizlonate.tmp.
                     simpl. rewrite Ed. reflexivity.
              ** destruct (dtmp d) as [d'|] eqn:Ed; [|discriminate Hdu].
                 destruct (dclass k) as [k'|] eqn:Ek; [|discriminate Hdu].
                 destruct (dload_type ty) as [lt|] eqn:Elt; [|discriminate Hdu].
                 injection Hdu as <-.
                 destruct (dload_type_size_align ty lt Elt) as [_ Hsa].
                 destruct (access_size_align (XLoad lt)) as [sz al] eqn:Esa.
                 eexists; split.
                 --- unfold Pizlonate.checked_access. simpl. rewrite Hsa. reflexivity.
                 --- intro q. cbn [step_uinst negb]. rewrite Esa, Epty.
                     unfold Pizlonate.check_local_inst, Pizlonate.raw_load, Pizlonate.tmp.
                     simpl. rewrite Ed, Ek, Elt. reflexivity.
           ++ destruct (f == "local_store") eqn:Ef_ls.
              ** apply String.eqb_eq in Ef_ls; subst f.
                 destruct xs as [|w [|v [|x [|[off| | |][|]]]]]; try discriminate Hdu.
                 destruct (is_atom "p" w) eqn:Epw.
                 --- destruct (dvalue v) as [v'|] eqn:Ev; [|discriminate Hdu].
                     injection Hdu as <-.
                     destruct w as [|wa| |]; unfold is_atom in Epw; try discriminate Epw.
                     apply String.eqb_eq in Epw; subst wa.
                     eexists; split.
                     +++ unfold Pizlonate.checked_access. simpl. reflexivity.
                     +++ intro q. simpl. unfold Pizlonate.check_local_inst, Pizlonate.raw_store_pointer,
                           Pizlonate.local_store_effects, Pizlonate.effects, Pizlonate.tmp.
                         simpl. rewrite Ev. reflexivity.
                 --- destruct (dwidth w) as [w'|] eqn:Ew; [|discriminate Hdu].
                     destruct w'; try discriminate Hdu;
                       destruct (dvalue v) as [v'|] eqn:Ev; try discriminate Hdu;
                       injection Hdu as <-;
                       destruct (dwidth_size_align w _ Ew ltac:(discriminate)) as [_ Hsa];
                       eexists; (split;
                         [unfold Pizlonate.checked_access; simpl; rewrite Hsa; reflexivity
                         | intro q; simpl; rewrite Epw; unfold Pizlonate.check_local_inst,
                             Pizlonate.raw_store, Pizlonate.tmp; simpl; rewrite Ew, Ev; reflexivity]).
              ** (* duinst_core: must be indirect Call *)
                 destruct (duinst_core_inv _ _ Hdu) as (i & Hui & Hnc & Edi & Henc); subst ui.
                 destruct i as [ | | | | r cl args0 | | | | ]; simpl in Hacc; try discriminate Hacc.
                 destruct cl as [p | |]; try discriminate Hacc.
                 rewrite <- Henc in *.
                 cbn [IrTerm.enc_inst dinst] in Edi.
                 destruct (dcall_result (IrTerm.enc_call_result r)) as [r'|] eqn:Er; [|discriminate Edi].
                 destruct (dargs (IrTerm.enc_args args0)) as [args'|] eqn:Eargs; [|discriminate Edi].
                 injection Edi as <- <-.
                 eexists; split.
                 --- unfold Pizlonate.checked_access. simpl. reflexivity.
                 --- intro q. simpl. unfold Pizlonate.tmp. simpl. rewrite Er, Eargs. reflexivity.
Qed.

(** Any term decoded by [duinst] to a non-access instruction [ui]
    comes from [duinst_core], giving its exact [dinst] witness. *)
Lemma duinst_non_access_core : forall t ui,
  duinst t = Some ui ->
  uinst_is_access ui = false ->
  exists i, ui = UCore i /\ checked_inst i = false /\ dinst t = Some i /\ IrTerm.enc_inst i = t.
Proof.
  intros t ui Hdu Hna.
  destruct t as [| |f xs|]; [discriminate Hdu | discriminate Hdu | | discriminate Hdu].
  unfold duinst in Hdu.
  destruct (f == "let") eqn:E1.
  - destruct xs as [|d [|k [|o [|args [|]]]]]; try exact (duinst_core_inv _ _ Hdu).
    destruct o as [| |of_ oxs|]; try exact (duinst_core_inv _ _ Hdu).
    destruct oxs as [|ty [|]]; try exact (duinst_core_inv _ _ Hdu).
    destruct args as [| | |l]; try exact (duinst_core_inv _ _ Hdu).
    destruct (of_ == "load");
      [destruct l as [|a [|]]; try discriminate Hdu;
       destruct (is_atom "p" k && is_atom "p" ty);
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; discriminate Hna|].
    destruct (of_ == "atomic_load");
      [destruct l as [|a [|]]; try discriminate Hdu;
       destruct (is_atom "p" k && is_atom "p" ty); try discriminate Hdu;
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; discriminate Hna|].
    destruct (of_ == "cas");
      [destruct l as [|e [|n [|a [|]]]]; try discriminate Hdu;
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; discriminate Hna|].
    exact (duinst_core_inv _ _ Hdu).
  - destruct (f == "store");
      [destruct xs as [|w [|v [|a [|]]]]; try discriminate Hdu;
       destruct (is_atom "p" w);
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; discriminate Hna|].
    destruct (f == "atomic_store");
      [destruct xs as [|w [|v [|a [|]]]]; try discriminate Hdu;
       destruct (is_atom "p" w); try discriminate Hdu;
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; discriminate Hna|].
    destruct (f == "access");
      [destruct xs as [|r [|a [|[sz| | |][|[al| | |][|]]]]]; try discriminate Hdu;
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; discriminate Hna|].
    destruct (f == "local_load");
      [destruct xs as [|d [|k [|ty [|x [|[off| | |][|]]]]]]; try discriminate Hdu;
       destruct (is_atom "p" ty);
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; discriminate Hna|].
    destruct (f == "local_store");
      [destruct xs as [|w [|v [|x [|[off| | |][|]]]]]; try discriminate Hdu;
       destruct (is_atom "p" w);
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; discriminate Hna|].
    exact (duinst_core_inv _ _ Hdu).
Qed.

(** When an unchecked term t decodes to a non-access instruction [ui]
    (meaning `uinst_is_access ui = false`), [Pizlonate.checked_access]
    returns `None` and the optional [Pizlonate.flight_inst] rewrite
    decodes under [Transport.dinst] to the singleton list
    [step_uinst true q ui]. *)
Theorem duinst_non_access_sim : forall t ui q,
  duinst t = Some ui ->
  uinst_is_access ui = false ->
  Pizlonate.checked_access t = None /\
  map_option dinst [match Pizlonate.flight_inst t with Some j => j | None => t end] =
  Some (step_uinst true q ui).
Proof.
  intros t ui q Hdu Hna.
  destruct (duinst_non_access_core t ui Hdu Hna) as (i & -> & Hnc & Edi & Henc).
  subst t.
  split.
  - exact (enc_inst_checked_access_none i Hnc Hna).
  - exact (enc_inst_flight_sim i q Hnc Hna Edi).
Qed.

(** When `filc = false`, every valid unchecked instruction decodes
    directly under [Transport.dinst] to [step_uinst false q ui]. *)
Lemma duinst_plain_sim : forall t umd defs ui q,
  duinst t = Some ui ->
  uvalid_inst false umd defs ui = true ->
  map_option dinst [t] = Some (step_uinst false q ui).
Proof.
  intros t umd defs ui q Hdu Hv.
  destruct ui as [i | | | | | | | | | | | |]; cbn [uvalid_inst negb] in Hv; try discriminate Hv.
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
  match goal with H : negb (uinst_is_access _) = true |- _ => apply negb_true_iff in H end.
  destruct (duinst_non_access_core t (UCore i) Hdu ltac:(assumption)) as (i' & Heq & _ & Edi & _).
  injection Heq as <-. simpl. rewrite Edi. reflexivity.
Qed.

(** ## Structural preservation helpers for [step_uinst]

    To assemble the full [valid_func] proof in
    [PizlonateProof](PizlonateProof.v), we record how [step_uinst]
    relates temporary definitions, temporary uses, `loc` markers,
    `local_alloc`, `va_args`, `setjmp`, and direct global calls between
    an unchecked instruction and its checked expansion. *)

(** The `is_loc` term test agrees with [uinst_is_loc] on every decoded
    unchecked instruction. *)
Lemma is_loc_duinst : forall t ui,
  duinst t = Some ui ->
  Pizlonate.is_loc t = uinst_is_loc ui.
Proof.
  intros t ui Hdu.
  destruct (uinst_is_access ui) eqn:Hacc.
  - assert (Hnotloc : uinst_is_loc ui = false) by (destruct ui; try reflexivity; destruct i; try reflexivity; discriminate Hacc).
    rewrite Hnotloc.
    destruct (duinst_checked_access_sim t ui Hdu Hacc) as (gen & Hca & _).
    destruct t as [| |f xs|]; [discriminate Hca | discriminate Hca | | discriminate Hca].
    unfold Pizlonate.is_loc. destruct xs as [|x1 [|x2 [|]]]; try reflexivity.
    destruct (f == "loc") eqn:Ef; [|reflexivity].
    apply String.eqb_eq in Ef; subst f. discriminate Hca.
  - destruct (duinst_non_access_core t ui Hdu Hacc) as (i & -> & Hnc & _ & <-).
    destruct i; try reflexivity.
Qed.

(** The temporary definitions of [step_core_inst q i] are those of [i],
    preceded by `(q, F)` for an indirect call. *)
Lemma step_core_inst_temp_defs : forall q i,
  flat_map inst_temp_defs (step_core_inst q i) =
  (if uinst_is_access (UCore i) then [(q, F)] else []) ++ inst_temp_defs i.
Proof.
  intros q [d k o args | | | | r cl args | r cl args | | | ]; simpl; try reflexivity.
  - destruct k; try reflexivity.
    destruct o; try reflexivity;
      destruct args as [|a1 [|a2 [|]]]; try reflexivity; destruct a1; reflexivity.
  - destruct cl; simpl; rewrite app_nil_r; reflexivity.
  - rewrite app_nil_r; reflexivity.
Qed.

(** The temporary definitions of [step_uinst filc q ui] are the
    original definitions of [ui], preceded by `(q, uinst_proof_class ui)`
    when `filc = true` and `uinst_is_access ui = true`. *)
Lemma step_uinst_temp_defs : forall filc umd defs ui q,
  uvalid_inst filc umd defs ui = true ->
  flat_map inst_temp_defs (step_uinst filc q ui) =
  (if filc && uinst_is_access ui then [(q, uinst_proof_class ui)] else [])
  ++ uinst_temp_defs ui.
Proof.
  intros [] umd defs ui q Hv.
  - destruct ui as [i | | d k lt a | | | | w v a | | | | d k lt x off | | w v x off];
      cbn [step_uinst negb uinst_is_access uinst_proof_class uinst_temp_defs andb app];
      try reflexivity.
    + rewrite step_core_inst_temp_defs. destruct i as [| | | |r [| |] | | | |]; reflexivity.
    + destruct (access_size_align (XLoad lt)); reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
    + destruct (access_size_align (XLoad lt)); reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
  - destruct ui; cbn [uvalid_inst negb] in Hv; try discriminate Hv.
    simpl. rewrite app_nil_r. reflexivity.
Qed.

(** Every temporary defined by a decoded core instruction [enc_inst i]
    appears in [Pizlonate.inst_defs (enc_inst i)]. *)
Lemma enc_inst_defs_cover : forall i d k,
  In (d, k) (inst_temp_defs i) ->
  In d (Pizlonate.inst_defs (IrTerm.enc_inst i)).
Proof.
  intros [d0 k0 o args | d0 o args lw | | | r cl args | r cl args | | | ] d k Hin;
    simpl in Hin; try contradiction.
  - destruct Hin as [H | []]. injection H as -> _. left. reflexivity.
  - destruct Hin as [H | []]. injection H as -> _. left. reflexivity.
  - destruct r as [|d0 k0|rs]; simpl in Hin.
    + contradiction.
    + destruct Hin as [H | []]. injection H as -> _. left. reflexivity.
    + unfold Pizlonate.inst_defs. simpl.
      induction rs as [|[d1 k1] rs IH]; [contradiction|].
      simpl. destruct Hin as [H | Hin].
      * injection H as -> _. left. reflexivity.
      * right. exact (IH Hin).
  - destruct r as [|d0 k0|rs]; simpl in Hin.
    + contradiction.
    + destruct Hin as [H | []]. injection H as -> _. left. reflexivity.
    + unfold Pizlonate.inst_defs. simpl.
      induction rs as [|[d1 k1] rs IH]; [contradiction|].
      simpl. destruct Hin as [H | Hin].
      * injection H as -> _. left. reflexivity.
      * right. exact (IH Hin).
Qed.

(** Every temporary defined by a decoded unchecked instruction term t
    with name `TAtom a` starting with `"chk"` appears in
    `flat_map Pizlonate.chk_name (Pizlonate.inst_defs t)`. *)
Lemma duinst_defined_chks : forall t ui d k a,
  duinst t = Some ui ->
  In (d, k) (uinst_temp_defs ui) ->
  d = TAtom a ->
  String.prefix "chk" a = true ->
  In a (flat_map Pizlonate.chk_name (Pizlonate.inst_defs t)).
Proof.
  intros t ui d k a Hdu Hin -> Hpre.
  apply in_flat_map. exists (TAtom a). split; [| simpl; rewrite Hpre; left; reflexivity].
  destruct t as [| |f xs|]; [discriminate Hdu | discriminate Hdu | | discriminate Hdu].
  unfold duinst in Hdu.
  destruct (f == "let") eqn:Elet.
  - apply String.eqb_eq in Elet; subst f.
    destruct xs as [|dt [|kt [|ot [|args [|]]]]];
      try (cbn iota in Hdu; destruct (duinst_core_inv _ _ Hdu) as (i & Hui & _ & _ & Henc); subst ui; rewrite <- Henc; exact (enc_inst_defs_cover _ _ _ Hin)).
    destruct ot as [| |of_ oxs|];
      try (cbn iota in Hdu; destruct (duinst_core_inv _ _ Hdu) as (i & Hui & _ & _ & Henc); subst ui; rewrite <- Henc; exact (enc_inst_defs_cover _ _ _ Hin)).
    destruct oxs as [|ty [|]];
      try (cbn iota in Hdu; destruct (duinst_core_inv _ _ Hdu) as (i & Hui & _ & _ & Henc); subst ui; rewrite <- Henc; exact (enc_inst_defs_cover _ _ _ Hin)).
    destruct args as [| | |l];
      try (cbn iota in Hdu; destruct (duinst_core_inv _ _ Hdu) as (i & Hui & _ & _ & Henc); subst ui; rewrite <- Henc; exact (enc_inst_defs_cover _ _ _ Hin)).
    destruct (of_ == "load").
    + destruct l as [|a0 [|]]; try discriminate Hdu.
      destruct (is_atom "p" kt && is_atom "p" ty).
      * destruct (dtmp dt) as [d'|] eqn:Ed; [|discriminate Hdu].
        destruct (dvalue a0); [|discriminate Hdu].
        injection Hdu as <-. simpl in Hin. destruct Hin as [H1 | []]. injection H1 as -> _.
        pose proof (NfbTransport.dtmp_enc dt (TAtom a) Ed) as <-. left. reflexivity.
      * destruct (dtmp dt) as [d'|] eqn:Ed; [|discriminate Hdu].
        destruct (dclass kt); [|discriminate Hdu].
        destruct (dload_type ty); [|discriminate Hdu].
        destruct (dvalue a0); [|discriminate Hdu].
        injection Hdu as <-. simpl in Hin. destruct Hin as [H1 | []]. injection H1 as -> _.
        pose proof (NfbTransport.dtmp_enc dt (TAtom a) Ed) as <-. left. reflexivity.
    + destruct (of_ == "atomic_load").
      * destruct l as [|a0 [|]]; try discriminate Hdu.
        destruct (is_atom "p" kt && is_atom "p" ty); [|discriminate Hdu].
        destruct (dtmp dt) as [d'|] eqn:Ed; [|discriminate Hdu].
        destruct (dvalue a0); [|discriminate Hdu].
        injection Hdu as <-. simpl in Hin. destruct Hin as [H1 | []]. injection H1 as -> _.
        pose proof (NfbTransport.dtmp_enc dt (TAtom a) Ed) as <-. left. reflexivity.
      * destruct (of_ == "cas").
        -- destruct l as [|e0 [|n0 [|a0 [|]]]]; try discriminate Hdu.
           destruct (dtmp dt) as [d'|] eqn:Ed; [|discriminate Hdu].
           destruct (dclass kt); [|discriminate Hdu].
           destruct (dcas_type ty); [|discriminate Hdu].
           destruct (dvalue e0); [|discriminate Hdu].
           destruct (dvalue n0); [|discriminate Hdu].
           destruct (dvalue a0); [|discriminate Hdu].
           injection Hdu as <-. simpl in Hin. destruct Hin as [H1 | []]. injection H1 as -> _.
           pose proof (NfbTransport.dtmp_enc dt (TAtom a) Ed) as <-. left. reflexivity.
        -- destruct (duinst_core_inv _ _ Hdu) as (i & Hui & _ & _ & Henc); subst ui; rewrite <- Henc.
           exact (enc_inst_defs_cover _ _ _ Hin).
  - destruct (f == "store");
      [destruct xs as [|w [|v [|a0 [|]]]]; try discriminate Hdu;
       destruct (is_atom "p" w);
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; destruct Hin|].
    destruct (f == "atomic_store");
      [destruct xs as [|w [|v [|a0 [|]]]]; try discriminate Hdu;
       destruct (is_atom "p" w); try discriminate Hdu;
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; destruct Hin|].
    destruct (f == "access");
      [destruct xs as [|r [|a0 [|[sz| | |][|[al| | |][|]]]]]; try discriminate Hdu;
       repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
       injection Hdu as <-; destruct Hin|].
    destruct (f == "local_load") eqn:Ef_ll.
    + apply String.eqb_eq in Ef_ll; subst f.
      destruct xs as [|dt [|kt [|ty [|x [|[off| | |][|]]]]]]; try discriminate Hdu.
      destruct (is_atom "p" ty).
      * destruct (is_atom "p" kt); [|discriminate Hdu].
        destruct (dtmp dt) as [d'|] eqn:Ed; [|discriminate Hdu].
        injection Hdu as <-. simpl in Hin. destruct Hin as [H1 | []]. injection H1 as -> _.
        pose proof (NfbTransport.dtmp_enc dt (TAtom a) Ed) as <-. left. reflexivity.
      * destruct (dtmp dt) as [d'|] eqn:Ed; [|discriminate Hdu].
        destruct (dclass kt); [|discriminate Hdu].
        destruct (dload_type ty); [|discriminate Hdu].
        injection Hdu as <-. simpl in Hin. destruct Hin as [H1 | []]. injection H1 as -> _.
        pose proof (NfbTransport.dtmp_enc dt (TAtom a) Ed) as <-. left. reflexivity.
    + destruct (f == "local_store");
        [destruct xs as [|w [|v [|x [|[off| | |][|]]]]]; try discriminate Hdu;
         destruct (is_atom "p" w);
         repeat match type of Hdu with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hdu end;
         injection Hdu as <-; destruct Hin|].
      destruct (duinst_core_inv _ _ Hdu) as (i & Hui & _ & _ & Henc); subst ui; rewrite <- Henc.
      exact (enc_inst_defs_cover _ _ _ Hin).
Qed.

(** Every [step_uinst] expansion preserves `LocalAlloc` entries
    identically. *)
Lemma step_uinst_local_objects : forall filc ui q,
  flat_map (fun i => match i with LocalAlloc x sz => [(x, sz)] | _ => [] end)
           (step_uinst filc q ui) =
  match ui with UCore (LocalAlloc x sz) => [(x, sz)] | _ => [] end.
Proof.
  intros [] ui q.
  - destruct ui as [i | | d k lt a | | | | w v a | | | | d k lt x off | | w v x off];
      cbn [step_uinst negb flat_map]; try reflexivity.
    + destruct i as [d k o args | | | | r cl args | | | |]; simpl; try reflexivity.
      * destruct k; try reflexivity.
        destruct o; simpl; try reflexivity;
          destruct args as [|a1 [|a2 [|]]]; simpl; try reflexivity; destruct a1; reflexivity.
      * destruct cl; reflexivity.
    + destruct (access_size_align (XLoad lt)); reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
    + destruct (access_size_align (XLoad lt)); reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
  - destruct ui as [i | | | | | | | | | | | |]; simpl; try reflexivity.
    destruct i; reflexivity.
Qed.

(** Every [step_uinst] expansion preserves `VaArgs` presence
    identically. *)
Lemma step_uinst_va_args : forall filc ui q,
  existsb (fun i => match i with Let _ P VaArgs _ => true | _ => false end)
          (step_uinst filc q ui) =
  match ui with UCore (Let _ P VaArgs _) => true | _ => false end.
Proof.
  intros [] ui q.
  - destruct ui as [i | | d k lt a | | d k ct e n a | | w v a | | | | d k lt x off | | w v x off];
      cbn [step_uinst negb existsb]; try reflexivity.
    + destruct i as [d k o args | | | | r cl args | | | |]; simpl; try reflexivity.
      * destruct k; try reflexivity.
        destruct o; simpl; try reflexivity;
          destruct args as [|a1 [|a2 [|]]]; simpl; try reflexivity; destruct a1; reflexivity.
      * destruct cl; reflexivity.
    + destruct (access_size_align (XLoad lt)); simpl; destruct k; reflexivity.
    + destruct k; reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
    + destruct (access_size_align (XLoad lt)); simpl; destruct k; reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
  - destruct ui as [i | | | | | | | | | | | |]; simpl; try reflexivity.
    destruct i as [d k o args | | | | | | | |]; simpl; try reflexivity.
    destruct k; try reflexivity; destruct o; reflexivity.
Qed.

(** Every [step_uinst] expansion preserves `Setjmp` presence
    identically. *)
Lemma step_uinst_setjmp : forall filc ui q,
  existsb (fun i => match i with Let _ _ (Setjmp _) _ => true | _ => false end)
          (step_uinst filc q ui) =
  match ui with UCore (Let _ _ (Setjmp _) _) => true | _ => false end.
Proof.
  intros [] ui q.
  - destruct ui as [i | | d k lt a | | | | w v a | | | | d k lt x off | | w v x off];
      cbn [step_uinst negb existsb]; try reflexivity.
    + destruct i as [d k o args | | | | r cl args | | | |]; simpl; try reflexivity.
      * destruct k; try (destruct o; simpl; reflexivity).
        destruct o; simpl; try reflexivity;
          destruct args as [|a1 [|a2 [|]]]; simpl; try reflexivity; destruct a1; reflexivity.
      * destruct cl; reflexivity.
    + destruct (access_size_align (XLoad lt)); reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
    + destruct (access_size_align (XLoad lt)); reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
  - destruct ui as [i | | | | | | | | | | | |]; simpl; try reflexivity.
    destruct i as [d k o args | | | | | | | |]; simpl; try reflexivity.
    destruct o; reflexivity.
Qed.

(** Every [step_uinst] expansion preserves direct global calls
    identically. *)
Lemma step_uinst_calls_global : forall filc ui q n,
  existsb (fun i => match i with Call _ (Global g) _ => name_eqb g n | _ => false end)
          (step_uinst filc q ui) =
  match ui with UCore (Call _ (Global g) _) => name_eqb g n | _ => false end.
Proof.
  intros [] ui q n.
  - destruct ui as [i | | d k lt a | | | | w v a | | | | d k lt x off | | w v x off];
      cbn [step_uinst negb existsb]; try reflexivity.
    + destruct i as [d k o args | | | | r cl args | | | |]; simpl; try reflexivity.
      * destruct k; try reflexivity.
        destruct o; simpl; try reflexivity;
          destruct args as [|a1 [|a2 [|]]]; simpl; try reflexivity; destruct a1; reflexivity.
      * destruct cl; simpl; [reflexivity | reflexivity | rewrite orb_false_r; reflexivity].
    + destruct (access_size_align (XLoad lt)); reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
    + destruct (access_size_align (XLoad lt)); reflexivity.
    + destruct (access_size_align (XWidth w)); reflexivity.
  - destruct ui as [i | | | | | | | | | | | |]; simpl; try reflexivity.
    destruct i as [ | | | | r cl args | | | | ]; simpl; try reflexivity.
    destruct cl; simpl; [reflexivity | reflexivity | rewrite orb_false_r; reflexivity].
Qed.
