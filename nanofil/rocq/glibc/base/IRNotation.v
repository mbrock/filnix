(** The glibc fixtures write each captured function as a sequence of labeled
    [[block|blocks]]. A [[phi]] names its incoming edges. The arrow at the
    end of a block separates its instructions from its jump.

    A short pointer addition uses the same operand for its address and
    [[lower]]. An instruction with a different donor retains both operands.
    Parentheses admit a Gallina expression wherever an instruction has no
    short spelling. *)

From Stdlib Require Import String List ZArith.
From Nanofil Require Import Term Syntax.
Import ListNotations.

Declare Custom Entry operand.
Declare Custom Entry ssa.
Notation "'ir{' i '}'" := i (i custom ssa at level 99).
Notation "'%' x" := (Tmp (TAtom x))
  (in custom operand at level 1, x constr at level 0, format "% x").
Notation "'$' x" := (Global (TAtom x))
  (in custom operand at level 1, x constr at level 0, format "$ x").
Notation "'#' x" := (Const x)
  (in custom operand at level 1, x constr at level 0, format "# x").
Notation "'%' dst ':' ty '=' op" := (Let (TAtom dst) ty op [])
  (in custom ssa at level 90, dst constr at level 0, ty constr at level 0,
   op constr at level 0, format "% dst  :  ty  =  op").
Notation "'%' dst ':' ty '=' op x" := (Let (TAtom dst) ty op [x])
  (in custom ssa at level 90, dst constr at level 0, ty constr at level 0,
   op constr at level 0, x custom operand at level 1, format "% dst  :  ty  =  op  x").
Notation "'%' dst ':' ty '=' op x ',' y" := (Let (TAtom dst) ty op [x; y])
  (in custom ssa at level 90, dst constr at level 0, ty constr at level 0,
   op constr at level 0, x custom operand at level 1, y custom operand at level 1,
   format "% dst  :  ty  =  op  x ,  y").
Notation "'%' dst ':' ty '=' op x ',' y ',' z" := (Let (TAtom dst) ty op [x; y; z])
  (in custom ssa at level 90, dst constr at level 0, ty constr at level 0,
   op constr at level 0, x custom operand at level 1, y custom operand at level 1,
   z custom operand at level 1, format "% dst  :  ty  =  op  x ,  y ,  z").
Notation "'%' dst '=' base '+p' offset" :=
  (Flight (TAtom dst) Add [FAddress base; FValue offset] (LowerOf base))
  (in custom ssa at level 90, dst constr at level 0,
   base custom operand at level 1, offset custom operand at level 1,
   format "% dst  =  base  +p  offset").
Notation "'store' sz '[' addr '+' off ']' '<-' src" := (RawStore sz off src addr)
  (in custom ssa at level 90, sz constr at level 0, off constr at level 0,
   src custom operand at level 1, addr custom operand at level 1,
   format "store  sz  [ addr  +  off ]  <-  src").
Declare Custom Entry edge.
Notation "lab" := (To (TAtom lab)) (in custom edge at level 0, lab constr at level 0).
Notation "'poll' lab" := (Poll (TAtom lab)) (in custom edge at level 1, lab constr at level 0).
Declare Custom Entry ssa_ret.
Notation "x" := (JRet x) (in custom ssa_ret at level 0, x custom operand at level 1).
Notation "'void'" := JRetVoid (in custom ssa_ret at level 0).
Notation "'ret' r" := r (in custom ssa at level 90, r custom ssa_ret at level 0).
Notation "'unreachable'" := JUnreachable (in custom ssa at level 0).
Notation "'goto' dst" := (JGoto dst) (in custom ssa at level 90, dst custom edge at level 1).
Notation "'br' x '?' yes ':' no" := (JBranch x yes no)
  (in custom ssa at level 90, x custom operand at level 1,
   yes custom edge at level 1, no custom edge at level 1).
Declare Custom Entry actual.
Notation "ty x" := (Arg ty x)
  (in custom actual at level 10, ty constr at level 0, x custom operand at level 1).
Declare Custom Entry arguments.
Notation "'()'" := (@nil arg) (in custom arguments at level 0).
Notation "'(' x , .. , y ')'" := (cons x .. (cons y nil) ..)
  (in custom arguments at level 0, x custom actual at level 10, y custom actual at level 10).
Notation "'call' '%' dst ':' ty '=' fn args" := (Call (CResult (TAtom dst) ty) fn args)
  (in custom ssa at level 90, dst constr at level 0, ty constr at level 0,
   fn custom operand at level 1, args custom arguments at level 0).
Notation "'call' 'void' fn args" := (Call CVoid fn args)
  (in custom ssa at level 90, fn custom operand at level 1, args custom arguments at level 0).
Notation "'rawcall' '%' dst ':' ty '=' fn args" := (RawCall (CResult (TAtom dst) ty) fn args)
  (in custom ssa at level 90, dst constr at level 0, ty constr at level 0,
   fn custom operand at level 1, args custom arguments at level 0).
Notation "'rawcall' 'void' fn args" := (RawCall CVoid fn args)
  (in custom ssa at level 90, fn custom operand at level 1, args custom arguments at level 0).
Notation "'ir[' x ; .. ; y ']'" := (cons x .. (cons y nil) ..)
  (x custom ssa at level 99, y custom ssa at level 99,
   format "ir[ '[v' x ; '/' .. ; '/' y ']' ]").
Notation "'store.ptr' '[' addr '+' off ']' '<-' src" :=
  (RawStorePointer off src addr [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])
  (in custom ssa at level 90, off constr at level 0, src custom operand at level 1,
   addr custom operand at level 1, format "store.ptr  [ addr  +  off ]  <-  src").
Notation "'alloca' x size" := (LocalAlloc (TAtom x) size)
  (in custom ssa at level 90, x constr at level 0, size constr at level 0).
Notation "'(' x ')'" := x (in custom ssa at level 0, x constr).

Declare Custom Entry incoming.
Declare Custom Entry ir_phi.
Declare Custom Entry phis_end.
Declare Custom Entry insts_end.
Declare Custom Entry ir_block.
Notation "lab '=>' v" := (TAtom lab, v)
  (in custom incoming at level 10, lab constr at level 0, v custom operand at level 1).
Notation "'%' d ':' k '=' 'phi' '(' x , .. , y ')'" :=
  (Phi (TAtom d) k (cons x .. (cons y nil) ..))
  (in custom ir_phi at level 0, d constr at level 0, k constr at level 0,
   x custom incoming at level 10, y custom incoming at level 10).
Notation "'(' x ')'" := x (in custom ir_phi at level 0, x constr).
Notation "':'" := (@nil phi) (in custom phis_end at level 0).
Notation "'[' x ; .. ; y ']' ':'" := (cons x .. (cons y nil) ..)
  (in custom phis_end at level 0, x custom ir_phi at level 0, y custom ir_phi at level 0).
Notation "'=>'" := (@nil inst) (in custom insts_end at level 0).
Notation "x ; .. ; y '=>'" := (cons x .. (cons y nil) ..)
  (in custom insts_end at level 10, x custom ssa at level 99, y custom ssa at level 99,
   format "'[v' x ; '/' .. ; '/' y '/' => ']'").
Notation "'code' '(' xs ')' '=>'" := xs (in custom insts_end at level 0, xs constr, only parsing).
Notation "'@' l ps ins j" := (mkBlock (TAtom l) ps ins j)
  (in custom ir_block at level 10, l constr at level 0, ps custom phis_end at level 0,
   ins custom insts_end at level 10, j custom ssa at level 99,
   format "'[v' @ l ps '/  ' ins  j ']'").
Notation "'(' x ')'" := x (in custom ir_block at level 0, x constr).
Notation "'ir_blk{' b '}'" := b (b custom ir_block at level 10).

Declare Custom Entry formal.
Declare Custom Entry formals.
Declare Custom Entry ir_body.
Notation "k '%' d" := (k, TAtom d)
  (in custom formal at level 10, k constr at level 0, d constr at level 0).
Notation "'()'" := (@nil (class * name)%type) (in custom formals at level 0).
Notation "'(' x , .. , y ')'" := (cons x .. (cons y nil) ..)
  (in custom formals at level 0, x custom formal at level 10, y custom formal at level 10).
Notation "'{' '}'" := (@nil block) (in custom ir_body at level 0).
Notation "'{' x ; .. ; y '}'" := (cons x .. (cons y nil) ..)
  (in custom ir_body at level 0, x custom ir_block at level 10, y custom ir_block at level 10,
   format "'[v' { '/' x ; '/' .. ; '/' y '/' } ']'").
Notation "'blocks' '(' xs ')'" := xs (in custom ir_body at level 0, xs constr, only parsing).
Notation "'ir_fn{' lk n params '->' r bs '}'" :=
  (mkFunc (TAtom n) (TAtom lk) r params bs)
  (lk constr at level 0, n constr at level 0, params custom formals at level 0,
   r constr at level 0, bs custom ir_body at level 0,
   format "'[v' ir_fn{  lk  n params  ->  r '/' bs  } ']'").
Notation "'val(' x ')'" := x (in custom operand at level 0, x constr).
Notation "'edge(' x ')'" := x (in custom edge at level 0, x constr).
