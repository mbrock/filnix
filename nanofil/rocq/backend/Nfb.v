(** NFB (docs/nfb.md) for the modules of Syntax.v: [encode] writes a
    module's words and [decode] reads them back, in place of the term
    the Prolog compiler prints and Transport.v's [decode_module] reads.

    A module of Syntax.v is written as the term ir.pl would print for
    it ([enc_module], from IrTerm.v's encoders of instructions), and
    that term as words by NfbTerm.v. A function outside the [[core
    subset]] is already its term ([IOutside]), so it is written the
    same way. Reading is the converse: NfbTerm.v's reader gives the
    module term, [decode_module] the module, and the words are taken
    only if they are what [encode] writes for that module. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Validate Transport Cfg.
From Backend Require Import IrTerm NfbTerm.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** ## A module as its term *)

(** As ir.pl writes a data object's Linkage. *)
Definition enc_linkage (lk : linkage) : term :=
  match lk with
  | LExport => TAtom "export"
  | LLocal => TAtom "local"
  | LWeak => TAtom "weak"
  | LRo l => TApp "ro" [l]
  | LTls l => TApp "tls" [l]
  | LInit w p => TApp "init" [w; p]
  | LExternWeak => TApp "extern" [TAtom "weak"]
  | LOther t => t
  end.

(** As ir.pl writes a data item; a string's bytes as the term reader
    makes their characters. *)
Definition enc_data_item (it : data_item) : term :=
  match it with
  | Item w n => TApp "item" [enc_width w; TApp "const" [TInt n]]
  | Str codes => TApp "item" [TAtom "b"; TApp "str" [TList (map code_char codes)]]
  | Sym s off => TApp "item" [TAtom "p"; TApp "sym" [s; TInt off]]
  | Zero n => TApp "zero" [TInt n]
  | ItemOther t => t
  end.

(** As ir.pl writes a function's Ret. *)
Definition enc_ret (r : ret_type) : term :=
  match r with
  | RClass k => eclass k
  | RVoid => TAtom "void"
  | RTuple ks => TApp "tuple" [TList (map eclass ks)]
  end.

(** As ir.pl writes a [[block]]. *)
Definition enc_block (b : block) : term :=
  TApp "block" [b_label b; TList (map enc_phi (b_phis b)); TList (map enc_inst (b_insts b));
                enc_jump (b_jump b)].

(** As ir.pl writes a function. *)
Definition enc_func (f : func) : term :=
  TApp "func" [fn_name f; fn_linkage f; enc_ret (fn_ret f);
               TList (map (fun p => TApp "param" [eclass (fst p); TApp "tmp" [snd p]]) (fn_params f));
               TList (map enc_block (fn_blocks f))].

(** As ir.pl writes an item; a function outside the core subset is its
    term. *)
Definition enc_item (it : item) : term :=
  match it with
  | IFunc f => enc_func f
  | IOutside _ t => t
  | IData n lk al its => TApp "data" [n; enc_linkage lk; TInt al; TList (map enc_data_item its)]
  | IAlias n lk tg => TApp "alias" [n; lk; tg]
  end.

(** The module as the term `module(Items)`. *)
Definition enc_module (m : module) : term := TApp "module" [TList (map enc_item m)].

(** ## Words *)

(** The NFB of the module m, with its NAMES section when names is
    true; none for a module that has no encoding, such as one whose
    symbol is not an atom. *)
Definition encode_with (names : bool) (m : module) : option (list Z) :=
  encode_term names (enc_module m).

(** The NFB of the module m, NAMES included. *)
Definition encode (m : module) : option (list Z) := encode_with true m.

(** The module the NFB ws encode: the words must be what [encode_with]
    writes for it, NAMES if ws have it, CONTEXT and tools' sections
    aside. *)
Definition decode (ws : list Z) : option module :=
  let* p := read_term ws in
  let* m := decode_module (fst p) in
  let* ws1 := encode_with (snd p) m in
  let* ws2 := module_words ws in
  if words_eqb ws1 ws2 then Some m else None.
