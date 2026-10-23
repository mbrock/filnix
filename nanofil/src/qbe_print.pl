/*  Printer from IR terms to QBE text. Every block ends in an explicit
    jump, so printing is independent of block order.
*/
:- module(qbe_print, [module_chars//1, print_module/1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).

print_module(Module) :-
    phrase(module_chars(Module), Cs),
    format("~s", [Cs]).

module_chars(module(Items)) --> items(Items).

items([]) --> [].
items([Item|Items]) --> item(Item), "\n", items(Items).

item(func(Name, Linkage, Ret, Params, Blocks)) -->
    linkage(Linkage),
    "function ", ret_class(Ret), "$", atom(Name),
    "(", params(Params), ") {\n",
    blocks(Blocks),
    "}\n".
item(data(Name, Linkage, Align, Items)) -->
    linkage(Linkage),
    "data $", atom(Name), " = align ", num(Align),
    " { ", data_items(Items), " }\n".

linkage(export) --> "export ".
linkage(local) --> [].
linkage(ro(Linkage)) --> linkage(Linkage), "section \".rodata\" ".

ret_class(void) --> [].
ret_class(tuple(Ks)) --> !, "{", comma_separated(Ks, atom), "} ".
ret_class(K) --> atom(K), " ".

params([]) --> [].
params([P]) --> !, param(P).
params([P|Ps]) --> param(P), ", ", params(Ps).

param(par(K, V)) --> atom(K), " ", val(V).

blocks([]) --> [].
blocks([blk(Label, Phis, Insts, Jump)|Blocks]) -->
    "@", atom(Label), "\n",
    phis(Phis),
    insts(Insts),
    "\t", jump(Jump), "\n",
    blocks(Blocks).

phis([]) --> [].
phis([phi(D, K, Incoming)|Phis]) -->
    "\t", val(D), " =", atom(K), " phi ", phi_args(Incoming), "\n",
    phis(Phis).

phi_args([Label-V]) --> !, "@", atom(Label), " ", val(V).
phi_args([Label-V|Incoming]) -->
    "@", atom(Label), " ", val(V), ", ",
    phi_args(Incoming).

insts([]) --> [].
insts([Inst|Insts]) --> "\t", inst(Inst), "\n", insts(Insts).

inst(ins(D, K, Op, Args)) -->
    val(D), " =", atom(K), " ", opname(Op), " ", vals(Args).
inst(store(W, V, Addr)) --> "store", atom(W), " ", val(V), ", ", val(Addr).
inst(call(void, F, Args)) --> "call ", val(F), "(", call_args(Args), ")".
inst(call(tuple(Tos), F, Args)) -->
    { findall(D, member(to(D, _), Tos), Ds),
      findall(K, member(to(_, K), Tos), Ks) },
    "{", comma_separated(Ds, val), "} ={", comma_separated(Ks, atom), "}",
    " call ", val(F), "(", call_args(Args), ")".
inst(call(to(D, K), F, Args)) -->
    val(D), " =", atom(K), " call ", val(F), "(", call_args(Args), ")".

call_args([]) --> [].
call_args([A]) --> !, call_arg(A).
call_args([A|As]) --> call_arg(A), ", ", call_args(As).

call_arg(arg(K, V)) --> atom(K), " ", val(V).

opname(cmp(Cond, K)) --> !, "c", atom(Cond), atom(K).
opname(ext(Type)) --> !, "ext", atom(Type).
opname(load(Type)) --> !, "load", atom(Type).
opname(alloc(Align)) --> !, "alloc", num(Align).
opname(Op) --> atom(Op).

jump(jmp(Label)) --> "jmp @", atom(Label).
jump(jnz(V, IfTrue, IfFalse)) -->
    "jnz ", val(V), ", @", atom(IfTrue), ", @", atom(IfFalse).
jump(ret(V)) --> "ret ", val(V).
jump(rets(Vs)) --> "ret {", comma_separated(Vs, val), "}".
jump(ret) --> "ret".
jump(hlt) --> "hlt".

vals([V]) --> !, val(V).
vals([V|Vs]) --> val(V), ", ", vals(Vs).

val(t(N)) --> "%", atom(N).
val(c(N)) --> num(N).
val(glo(N)) --> "$", atom(N).

data_items([Item]) --> !, data_item(Item).
data_items([Item|Items]) --> data_item(Item), ", ", data_items(Items).

data_item(zero(N)) --> "z ", num(N).
data_item(item(W, c(N))) --> atom(W), " ", num(N).
data_item(item(b, str(Cs))) --> "b \"", seq(Cs), "\"".
data_item(item(W, sym(S, 0))) --> !, atom(W), " $", atom(S).
data_item(item(W, sym(S, Off))) --> atom(W), " $", atom(S), " + ", num(Off).

% comma_separated(+Xs, :Print): Print each of the nonempty Xs, separated
% by ", ".
comma_separated([X], Print) --> !, call(Print, X).
comma_separated([X|Xs], Print) -->
    call(Print, X), ", ",
    comma_separated(Xs, Print).

atom(A) --> { atom_chars(A, Cs) }, seq(Cs).
num(N) --> { number_chars(N, Cs) }, seq(Cs).
