(** Several glibc proofs check the transport decoder on the original input.
    This notation builds that input one [term] at a time. A function can
    therefore include an instruction outside the typed core and still
    preserve the bytes, names and operand order that the decoder sees. *)

From Stdlib Require Import List String ZArith.
From Nanofil Require Import Term.
Import ListNotations.
Open Scope string_scope.

Declare Custom Entry capture.
Declare Custom Entry capture_inst.
Declare Custom Entry capture_body.
Declare Custom Entry capture_block.
Declare Custom Entry capture_blocks.

Notation "'cap{' x '}'" := x (x custom capture at level 10).
Notation "x" := (TAtom x) (in custom capture at level 0, x constr at level 0).
Notation "'int' n" := (TInt n) (in custom capture at level 1, n constr at level 0).
Notation "'%' d" := (TApp "tmp" [TAtom d]) (in custom capture at level 1, d constr at level 0).
Notation "'$' n" := (TApp "global" [TAtom n]) (in custom capture at level 1, n constr at level 0).
Notation "'#' n" := (TApp "const" [TInt n]) (in custom capture at level 1, n constr at level 0).
Notation "'op' n '(' x , .. , y ')'" := (TApp n (cons x .. (cons y nil) ..))
  (in custom capture at level 0, n constr at level 0, x custom capture at level 10, y custom capture at level 10).
Notation "'[' ']'" := (TList []) (in custom capture at level 0).
Notation "'[' x ; .. ; y ']'" := (TList (cons x .. (cons y nil) ..))
  (in custom capture at level 0, x custom capture at level 10, y custom capture at level 10).
Notation "'term(' t ')'" := t (in custom capture at level 0, t constr).

Notation "'%' d ':' k '=' o" := (TApp "let" [TApp "tmp" [TAtom d]; k; o; TList []])
  (in custom capture_inst at level 90, d constr at level 0, k custom capture at level 10, o custom capture at level 10).
Notation "'%' d ':' k '=' o x , .. , y" :=
  (TApp "let" [TApp "tmp" [TAtom d]; k; o; TList (cons x .. (cons y nil) ..)])
  (in custom capture_inst at level 90, d constr at level 0, k custom capture at level 10,
   o custom capture at level 10, x custom capture at level 10, y custom capture at level 10).
Notation "'%' d '=' base '+p' off" :=
  (TApp "flight" [TApp "tmp" [TAtom d]; TAtom "add"; TList [TApp "address" [base]; off]; TApp "lower" [base]])
  (in custom capture_inst at level 90, d constr at level 0, base custom capture at level 10,
   off custom capture at level 10).
Notation "'store' w '[' a '+' off ']' '<-' v" := (TApp "raw_store" [w; TInt off; v; a])
  (in custom capture_inst at level 90, w custom capture at level 10, a custom capture at level 10,
   off constr at level 0, v custom capture at level 10).
Notation "'store.ptr' '[' a '+' off ']' '<-' v" :=
  (TApp "raw_store_pointer" [TInt off; v; a; TList [TAtom "aux_ensure"; TAtom "lower_barrier";
     TAtom "rooted_reload"; TAtom "lower_write"; TAtom "address_write"]])
  (in custom capture_inst at level 90, a custom capture at level 10, off constr at level 0, v custom capture at level 10).
Declare Custom Entry capture_actual.
Declare Custom Entry capture_args.
Notation "k v" := (TApp "arg" [k; v])
  (in custom capture_actual at level 10, k custom capture at level 10, v custom capture at level 10).
Notation "'()'" := (TList []) (in custom capture_args at level 0).
Notation "'(' x , .. , y ')'" := (TList (cons x .. (cons y nil) ..))
  (in custom capture_args at level 0, x custom capture_actual at level 10, y custom capture_actual at level 10).
Notation "'call' '%' d ':' k '=' fn args" :=
  (TApp "call" [TApp "result" [TApp "tmp" [TAtom d]; k]; fn; args])
  (in custom capture_inst at level 90, d constr at level 0, k custom capture at level 10,
   fn custom capture at level 10, args custom capture_args at level 0).
Notation "'call' 'void' fn args" := (TApp "call" [TAtom "void"; fn; args])
  (in custom capture_inst at level 90, fn custom capture at level 10, args custom capture_args at level 0).
Notation "'rawcall' '%' d ':' k '=' fn args" :=
  (TApp "raw_call" [TApp "result" [TApp "tmp" [TAtom d]; k]; fn; args])
  (in custom capture_inst at level 90, d constr at level 0, k custom capture at level 10,
   fn custom capture at level 10, args custom capture_args at level 0).
Notation "'rawcall' 'void' fn args" := (TApp "raw_call" [TAtom "void"; fn; args])
  (in custom capture_inst at level 90, fn custom capture at level 10, args custom capture_args at level 0).
Notation "'alloca' d n" := (TApp "local_alloc" [TAtom d; TInt n])
  (in custom capture_inst at level 90, d constr at level 0, n constr at level 0).
Notation "'(' t ')'" := t (in custom capture_inst at level 0, t custom capture at level 10).
Notation "'goto' t" := (TApp "goto" [t]) (in custom capture_inst at level 90, t custom capture at level 10).
Notation "'br' v '?' y ':' n" := (TApp "branch" [v; y; n])
  (in custom capture_inst at level 90, v custom capture at level 10, y custom capture at level 10, n custom capture at level 10).
Notation "'poll' l" := (TApp "poll" [TAtom l]) (in custom capture at level 1, l constr at level 0).
Declare Custom Entry capture_inst_ret.
Notation "x" := (TApp "ret" [x]) (in custom capture_inst_ret at level 0, x custom capture at level 10).
Notation "'void'" := (TAtom "ret") (in custom capture_inst_ret at level 0).
Notation "'ret' r" := r (in custom capture_inst at level 90, r custom capture_inst_ret at level 0).
Notation "'unreachable'" := (TAtom "unreachable") (in custom capture_inst at level 0).

Declare Custom Entry capture_incoming.
Notation "l '=>' v" := (TApp "-" [l; v])
  (in custom capture_incoming at level 10, l custom capture at level 10, v custom capture at level 10).
Notation "'phi' '%' d ':' k '=' '(' x , .. , y ')'" :=
  (TApp "phi" [TApp "tmp" [TAtom d]; k; TList (cons x .. (cons y nil) ..)])
  (in custom capture at level 0, d constr at level 0, k custom capture at level 10,
   x custom capture_incoming at level 10, y custom capture_incoming at level 10).
Notation "'param' k '%' d" := (TApp "param" [k; TApp "tmp" [TAtom d]])
  (in custom capture at level 1, k custom capture at level 10, d constr at level 0).

Notation "'=>'" := (@nil term) (in custom capture_body at level 0).
Notation "x ; .. ; y '=>'" := (cons x .. (cons y nil) ..)
  (in custom capture_body at level 10, x custom capture_inst at level 99, y custom capture_inst at level 99).
Notation "'@' l ':' ins j" := (TApp "block" [l; TList []; TList ins; j])
  (in custom capture_block at level 10, l custom capture at level 10, ins custom capture_body at level 10,
   j custom capture_inst at level 99).
Notation "'@' l '[' p ; .. ; q ']' ':' ins j" :=
  (TApp "block" [l; TList (cons p .. (cons q nil) ..); TList ins; j])
  (in custom capture_block at level 10, l custom capture at level 10, p custom capture at level 10,
   q custom capture at level 10, ins custom capture_body at level 10, j custom capture_inst at level 99).
Notation "'cap_blk{' b '}'" := b (b custom capture_block at level 10).
Notation "'{' x ; .. ; y '}'" := (cons x .. (cons y nil) ..)
  (in custom capture_blocks at level 0, x custom capture_block at level 10, y custom capture_block at level 10).
Notation "'blocks' '(' xs ')'" := xs (in custom capture_blocks at level 0, xs constr, only parsing).
Notation "'cap_fn{' lk n ps '->' r bs '}'" := (TApp "func" [n; lk; r; ps; TList bs])
  (lk custom capture at level 10, n custom capture at level 10, ps custom capture at level 10,
   r custom capture at level 10, bs custom capture_blocks at level 0).
