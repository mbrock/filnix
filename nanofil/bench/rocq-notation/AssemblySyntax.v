(** This grammar displays the instructions that allocate a directory buffer
    and compare two locale aliases. A proof can display one instruction on its own
    or the remaining instructions of a block on successive lines. *)

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
Notation "'%' dst ':' ty '=' op x" := (Let (TAtom dst) ty op [x])
  (in custom ssa at level 90, dst constr at level 0, ty constr at level 0,
   op constr at level 0, x custom operand at level 1, format "% dst  :  ty  =  op  x").
Notation "'%' dst ':' ty '=' op x ',' y" := (Let (TAtom dst) ty op [x; y])
  (in custom ssa at level 90, dst constr at level 0, ty constr at level 0,
   op constr at level 0, x custom operand at level 1, y custom operand at level 1,
   format "% dst  :  ty  =  op  x ,  y").
Notation "'%' dst '=' base '+p' offset" :=
  (Flight (TAtom dst) Add [FAddress base; FValue offset] (LowerOf base))
  (in custom ssa at level 90, dst constr at level 0,
   base custom operand at level 1, offset custom operand at level 1,
   format "% dst  =  base  +p  offset").
Notation "'store' sz '[' addr '+' off ']' '<-' src" := (RawStore sz off src addr)
  (in custom ssa at level 90, sz constr at level 0, off constr at level 0,
   src custom operand at level 1, addr custom operand at level 1,
   format "store  sz  [ addr  +  off ]  <-  src").
Notation "'ret' x" := (JRet x)
  (in custom ssa at level 90, x custom operand at level 1).
Notation "'goto' lab" := (JGoto (To (TAtom lab)))
  (in custom ssa at level 90, lab constr at level 0).
Notation "'br' x '?' yes ':' no" := (JBranch x (To (TAtom yes)) (To (TAtom no)))
  (in custom ssa at level 90, x custom operand at level 1,
   yes constr at level 0, no constr at level 0).
Declare Custom Entry actual.
Notation "ty x" := (Arg ty x)
  (in custom actual at level 10, ty constr at level 0, x custom operand at level 1).
Notation "'call' '%' dst ':' ty '=' fn '(' x , .. , y ')'" :=
  (Call (CResult (TAtom dst) ty) fn (cons x .. (cons y nil) ..))
  (in custom ssa at level 0, dst constr at level 0, ty constr at level 0,
   fn custom operand at level 1, x custom actual at level 10, y custom actual at level 10).
Notation "'call' fn '(' x , .. , y ')'" :=
  (Call CVoid fn (cons x .. (cons y nil) ..))
  (in custom ssa at level 0, fn custom operand at level 1,
   x custom actual at level 10, y custom actual at level 10).
Notation "'ir[' x ; .. ; y ']'" := (cons x .. (cons y nil) ..)
  (x custom ssa at level 99, y custom ssa at level 99,
   format "ir[ '[v' x ; '/' .. ; '/' y ']' ]").
